"""Local maps whose operands sit in the wrong lane: hoist, compute in place, relayout.

When an output long word's lanes need input words that are not the matching
lanes of one input long word (e.g. a row vector element used by every column
of its row), the plain local map has to fall back to word granularity, which
halves the work done per op. Instead:

1. maximal subexpressions over misplaced operands are hoisted out of the
   output template (``a / b`` is first rewritten to ``a * (1 / b)``) and
   computed at long-word granularity where their operands already are;
2. their results are copied word by word into a buffer laid out like the
   output (four words per copy op);
3. the output template, with the hoisted parts replaced by buffer reads, is
   computed at long-word granularity.
"""

from __future__ import annotations

import itertools
from collections import defaultdict

from .errors import CompileError
from .ir import Node, walk
from .local import analyze
from .machine import Mem
from .select import Constants, GroupGen, lane_type
from .vprog import VOp, VProgram

_names = itertools.count()
GRF_LIMIT = 448  # GRF words below the constant area
LM_WORDS = 4096


def _rewrite_div(graph, node: Node, memo):
    hit = memo.get(node.id)
    if hit is not None:
        return hit
    if not node.args:
        memo[node.id] = node
        return node
    args = [_rewrite_div(graph, a, memo) for a in node.args]
    if node.op == "div" and node.ty == "f" and not (args[0].op == "const" and args[0].value == 1.0):
        recip = graph.make("div", (graph.const(1.0), args[1]), ty="f")
        out = graph.make("mul", tuple(sorted((args[0], recip), key=lambda a: (a.op == "const", a.shape, a.id))), ty="f")
    elif all(a is b for a, b in zip(args, node.args)):
        out = node
    else:
        out = graph.make(node.op, tuple(args), value=node.value, ty=node.ty)
    memo[node.id] = out
    return out


def _bind(template: Node, node: Node, task, mapping: dict, cvals=None):
    if template.op != node.op or len(template.args) != len(node.args):
        raise CompileError("relayout: structure mismatch")
    if template.op == "input":
        leaf = task.leaves[node.id]
        if leaf.src is not None:
            raise CompileError("relayout: operand in another PE")
        word = (leaf.space, 2 * leaf.addr + leaf.lane)
        prev = mapping.get(template.id)
        if prev is not None and prev != word:
            raise CompileError("relayout: sharing mismatch")
        mapping[template.id] = word
        return
    if template.op == "const":
        if cvals is not None and template.ty != "b":
            return  # location-dependent constants are materialized separately
        if template.value != node.value:
            raise CompileError("relayout: constant mismatch")
        return
    for t, n in zip(template.args, node.args):
        _bind(t, n, task, mapping, cvals)


class _Space:
    """Free word ranges of the PE memories not used by inputs and outputs."""

    def __init__(self, contract):
        self.next = {"lm0": 0, "lm1": 0, "grf0": 0, "grf1": 0}
        for spec in list(contract.inputs) + list(contract.outputs):
            if spec.space in ("lm0", "lm1"):
                self.next[spec.space] = max(self.next[spec.space], spec.end)

    def take(self, space, words):
        base = (self.next[space] + 7) // 8 * 8
        limit = GRF_LIMIT if space.startswith("grf") else LM_WORDS
        if base + words > limit:
            return None
        self.next[space] = base + words
        return base


def relayout_strategy(source, contract, outputs, *, variant=None):
    graph = getattr(outputs, "graph", None)
    if graph is None:
        raise CompileError("relayout: no graph")
    if len(contract.outputs) != 1:
        raise CompileError("relayout: one output")
    out_spec = contract.outputs[0]
    if out_spec.space == "dram" or any(s.space == "dram" for s in contract.inputs):
        raise CompileError("relayout: DRAM operand")
    if out_spec.dtype.bits != 32 or any(s.dtype.bits != 32 for s in contract.inputs):
        raise CompileError("relayout: 32-bit lanes only")
    memo = {}
    rewritten = {out_spec.name: {idx: _rewrite_div(graph, n, memo) for idx, n in outputs[out_spec.name].items()}}
    lp = analyze(contract, rewritten, words=False, pe_constants=True, lane_aligned=False)

    from .compiler import _knobs

    knobs = _knobs(rewritten)
    settings = [None]
    if knobs:
        import itertools

        settings = [dict(zip([k for k, _ in knobs], combo)) for combo in itertools.product(*[v for _, v in knobs])]
    results = []
    for var in settings:
        for stage in (False, True):
            try:
                prog = _build(graph, contract, lp, var, stage)
            except CompileError:
                if stage:
                    continue
                raise
            name = "-".join(f"{k}{v}" for k, v in var.items()) if var else "base"
            results.append((name + ("-staged" if stage else ""), prog))
    return results


def _build(graph, contract, lp, variant, stage=False):
    out_spec = contract.outputs[0]
    classes = {}
    for sig, tasks in lp.classes.items():
        items = []
        for t in sorted(tasks, key=lambda t: t.addr):
            if set(t.lanes) != {0, 1}:
                raise CompileError("relayout: partial output long word")
            items.append((t.addr, t, t))
        classes[sig] = items

    from .compiler import _coordinate_constants

    prog = VProgram()
    consts = Constants(prog)
    coord_cache = {}
    lt = lane_type(out_spec.dtype)
    ranges = {s.name: (s.low, s.high) for s in contract.inputs if s.low is not None}
    space = _Space(contract)
    in_spaces = {s.space for s in contract.inputs}
    any_misaligned = False
    copies_all = []  # (src space, src word, dst space, dst word)
    main_groups = []  # (template, dst Mem, operands)
    hoist_groups = []  # (template, dst Mem, operands)
    for sig, items in classes.items():
        template = items[0][1].lanes[0]
        coords = _coordinate_constants(lp, template, [t for _, t, _ in items], prog, consts, lt, coord_cache)
        bindings = []
        for long_addr, t0, t1 in items:
            pair = []
            for lane, t in ((0, t0), (1, t1)):
                m = {}
                _bind(template, t.lanes[lane], t, m, {})
                pair.append(m)
            bindings.append((long_addr, pair))
        positions = [n for n in walk([template]) if n.op == "input"]

        def aligned(p):
            for _, (m0, m1) in bindings:
                (s0, w0), (s1, w1) = m0[p.id], m1[p.id]
                if s0 != s1 or w0 % 2 or w1 != w0 + 1:
                    return False
            return True

        mis = {p.id for p in positions if not aligned(p)}
        if mis:
            any_misaligned = True
        # maximal subtrees over misaligned operands (and constants)
        status = {}
        for n in walk([template]):
            if n.op == "input":
                status[n.id] = "mis" if n.id in mis else "ok"
            elif n.op == "const":
                status[n.id] = "const"
            else:
                kinds = {status[a.id] for a in n.args}
                status[n.id] = "mis" if "mis" in kinds and "ok" not in kinds and "mixed" not in kinds and n.ty != "b" else ("const" if kinds == {"const"} else ("mixed" if "mis" in kinds or "mixed" in kinds else "ok"))
        hoisted = []

        def collect(n):
            if status[n.id] == "mis":
                hoisted.append(n)
                return
            for a in n.args:
                collect(a)

        collect(template)
        hoisted = list({h.id: h for h in hoisted}.values())
        if any(n.id in coords for h in hoisted for n in walk([h])):
            raise CompileError("relayout: location-dependent constant inside a hoisted part")
        # each hoisted subtree: compute at its operands' natural lanes, then relayout to a buffer
        replace_with = {}
        extra_operands = []  # per binding: {placeholder id: (space, long addr)}
        per_binding_extra = [dict() for _ in bindings]
        for k, h in enumerate(hoisted):
            leaves = [n for n in walk([h]) if n.op == "input"]
            source = {}  # binding (tuple of words) -> (space, word) holding h's value
            if h.op == "input":
                for _, pair in bindings:
                    for m in pair:
                        source[(m[h.id],)] = m[h.id]
            else:
                lws = {}
                for _, pair in bindings:
                    for m in pair:
                        words = tuple(m[p.id] for p in leaves)
                        par = {w % 2 for _, w in words}
                        if len(par) != 1:
                            raise CompileError("relayout: hoisted operands in different lanes")
                        lw = tuple((s, w // 2) for s, w in words)
                        lws.setdefault(lw, len(lws))
                        source[words] = (lw, par.pop())
                t1_space = next((s for s in ("grf1", "grf0", "lm1", "lm0") if space.next[s] + 2 * len(lws) <= (GRF_LIMIT if s.startswith("grf") else LM_WORDS)), None)
                base = space.take(t1_space, 2 * ((len(lws) + 3) // 4 * 4))
                if base is None:
                    raise CompileError("relayout: no room for hoisted values")
                order = sorted(lws, key=lws.get)
                for i in range(0, len(order), 4):
                    chunk = order[i:i + 4]
                    while len(chunk) < 4:
                        chunk = chunk + [chunk[-1]]
                    operands = {p.id: Mem(chunk[0][j][0], 2, tuple(2 * c[j][1] for c in chunk)) for j, p in enumerate(leaves)}
                    dst = Mem(t1_space, 2, tuple(base + 2 * lws[c] for c in chunk))
                    hoist_groups.append((h, dst, operands))
                source = {words: (t1_space, base + 2 * lws[lw] + par) for words, (lw, par) in source.items()}
            # buffer slots: (lane-0 source, lane-1 source) per output long word
            slots = {}
            per_task = []
            for _, (m0, m1) in bindings:
                key0 = (m0[h.id],) if h.op == "input" else tuple(m0[p.id] for p in leaves)
                key1 = (m1[h.id],) if h.op == "input" else tuple(m1[p.id] for p in leaves)
                pair = (source[key0], source[key1])
                per_task.append(pair)
                if pair[0][0] == pair[1][0] and pair[0][1] % 2 == 0 and pair[1][1] == pair[0][1] + 1:
                    continue
                slots.setdefault(pair, len(slots))
            placeholder = graph.make("input", value=(f"__relayout{next(_names)}", ()), ty=h.ty)
            replace_with[h.id] = placeholder
            buf = None
            if slots:
                avoid = in_spaces | {out_spec.space}
                buf_space = next((s for s in ("grf0", "grf1", "lm1", "lm0") if s not in avoid and space.next[s] + 2 * len(slots) <= (GRF_LIMIT if s.startswith("grf") else LM_WORDS)), None)
                if buf_space is None:
                    raise CompileError("relayout: no room for the buffer")
                buf = (buf_space, space.take(buf_space, 2 * len(slots)))
                for (a, b), s in slots.items():
                    copies_all.append((a[0], a[1], buf_space, buf[1] + 2 * s))
                    copies_all.append((b[0], b[1], buf_space, buf[1] + 2 * s + 1))
            for i, pair in enumerate(per_task):
                if pair in slots:
                    per_binding_extra[i][placeholder.id] = (buf[0], buf[1] // 2 + slots[pair])
                else:
                    per_binding_extra[i][placeholder.id] = (pair[0][0], pair[0][1] // 2)
        main = _substitute(graph, template, replace_with)
        main_positions = [n for n in walk([main]) if n.op == "input"]
        rows = []
        for i, (long_addr, (m0, _m1)) in enumerate(bindings):
            ops = {}
            for p in main_positions:
                if p.id in per_binding_extra[i]:
                    ops[p.id] = per_binding_extra[i][p.id]
                else:
                    s, w = m0[p.id]
                    ops[p.id] = (s, w // 2)
            rows.append((long_addr, ops))
        for i in range(0, len(rows), 4):
            chunk = rows[i:i + 4]
            while len(chunk) < 4:
                chunk = chunk + [chunk[-1]]
            operands = {pid: Mem(chunk[0][1][pid][0], 2, tuple(2 * r[1][pid][1] for r in chunk)) for pid in chunk[0][1]}
            operands.update(coords)
            dst = Mem(out_spec.space, 2, tuple(2 * r[0] for r in chunk))
            main_groups.append((main, dst, operands))
    if not any_misaligned:
        raise CompileError("relayout: operands already aligned (plain local map)")
    # stage LM operands of the hoisted computations into a GRF (the main ops keep the LM read port)
    if stage:
        hoist_groups = _stage_operands(prog, space, hoist_groups)
    # hoisted computations
    for template, dst, operands in hoist_groups:
        _generate(prog, consts, lt, template, dst, operands, ranges, variant)
    # stage copy sources that live in an LM (whose read port the main ops need) into a GRF
    if stage:
        need = defaultdict(set)
        for s_space, s_word, d_space, d_word in copies_all:
            if s_space in ("lm0", "lm1"):
                need[s_space].add(s_word // 4)
        remap = {}
        for s_space, blocks in need.items():
            blocks = sorted(blocks)
            st_space = next((b for b in ("grf1", "grf0") if space.next[b] + 4 * len(blocks) <= GRF_LIMIT), None)
            if st_space is None:
                raise CompileError("relayout: no room to stage")
            base = space.take(st_space, 4 * ((len(blocks) + 3) // 4 * 4))
            for i in range(0, len(blocks), 4):
                chunk = blocks[i:i + 4]
                while len(chunk) < 4:
                    chunk = chunk + [chunk[-1]]
                prog.add(VOp("lpassa", [Mem(s_space, 4, tuple(4 * b for b in chunk))],
                             dsts=[Mem(st_space, 4, tuple(base + 4 * (i + k if k < len(blocks) - i else len(blocks) - 1 - i) for k in range(4)))], unit="alu", note="relayout stage"))
            for j, b in enumerate(blocks):
                remap[(s_space, b)] = (st_space, base + 4 * j)
        copies_all = [(remap[(s, w // 4)][0], remap[(s, w // 4)][1] + w % 4, d, dw) if (s, w // 4) in remap else (s, w, d, dw) for s, w, d, dw in copies_all]
    # word copies, four per op, grouped by source and destination memory
    by_mem = defaultdict(list)
    for s_space, s_word, d_space, d_word in copies_all:
        by_mem[(s_space, d_space)].append((s_word, d_word))
    copies = []
    for (s_space, d_space), pairs in by_mem.items():
        for i in range(0, len(pairs), 4):
            chunk = pairs[i:i + 4]
            while len(chunk) < 4:
                chunk = chunk + [chunk[-1]]
            src = Mem(s_space, 1, tuple(p[0] for p in chunk))
            dst = Mem(d_space, 1, tuple(p[1] for p in chunk))
            copies.append(prog.add(VOp("lpassa", [src], dsts=[dst], unit="alu", note="relayout copy")))
    for template, dst, operands in main_groups:
        _generate(prog, consts, lt, template, dst, operands, ranges, variant)
    # balance the copies between the ALU and (for float data, where a pass is exact) the MAU
    if out_spec.dtype.is_float and all(s.dtype.is_float for s in contract.inputs):
        load = {"alu": 0, "mau": 0}
        for op in prog.ops:
            if op.unit in load and op not in copies:
                load[op.unit] += 1
        for op in copies:
            unit = min(load, key=lambda u: (load[u], u != "alu"))
            load[unit] += 1
            op.unit = unit
            op.opcode = "lpassa" if unit == "alu" else "fvpassa"
    prog.notes["grf_reserved"] = {b: space.next[b] for b in ("grf0", "grf1")}
    return prog


def _generate(prog, consts, lt, template, dst, operands, ranges, variant):
    uses = {}
    for n in walk([template]):
        for a in n.args:
            uses[a.id] = uses.get(a.id, 0) + 1
    gen = GroupGen(prog, consts, lt, operands, ranges, uses, variant=variant)
    gen.write(template, dst)


def _substitute(graph, node: Node, mapping: dict):
    if node.id in mapping:
        return mapping[node.id]
    if not node.args:
        return node
    args = tuple(_substitute(graph, a, mapping) for a in node.args)
    if all(a is b for a, b in zip(args, node.args)):
        return node
    return graph.make(node.op, args, value=node.value, ty=node.ty)


def _stage_operands(prog, space, groups):
    """Copy the LM long words read by `groups` into a GRF with two-long-word copies; remap the operands."""
    blocks = defaultdict(set)
    for _t, _d, operands in groups:
        for m in operands.values():
            if m.space in ("lm0", "lm1"):
                for a in m.addrs:
                    blocks[m.space].add(a // 4)
    remap = {}
    for s_space, bl in blocks.items():
        bl = sorted(bl)
        st_space = next((b for b in ("grf1", "grf0") if space.next[b] + 4 * len(bl) <= GRF_LIMIT), None)
        if st_space is None:
            raise CompileError("relayout: no room to stage")
        base = space.take(st_space, 4 * ((len(bl) + 3) // 4 * 4))
        for i in range(0, len(bl), 4):
            chunk = bl[i:i + 4]
            idx = list(range(i, i + len(chunk)))
            while len(chunk) < 4:
                chunk.append(chunk[-1])
                idx.append(idx[-1])
            prog.add(VOp("lpassa", [Mem(s_space, 4, tuple(4 * b for b in chunk))],
                         dsts=[Mem(st_space, 4, tuple(base + 4 * j for j in idx))], unit="alu", note="relayout stage"))
        for j, b in enumerate(bl):
            remap[(s_space, b)] = (st_space, base + 4 * j)
    out = []
    for t, d, operands in groups:
        ops = {}
        for k, m in operands.items():
            if m.space in ("lm0", "lm1"):
                sp = remap[(m.space, m.addrs[0] // 4)][0]
                ops[k] = Mem(sp, m.wl, tuple(remap[(m.space, a // 4)][1] + a % 4 for a in m.addrs), neg=m.neg)
            else:
                ops[k] = m
        out.append((t, d, ops))
    return out
