"""Reductions whose terms are all stored in the output's PE (local reductions).

An output word is reduce(op, terms) where every term is the same scalar
function (template) of input lanes held by the output's PE at the output's
lane. Terms are spread over the four cycles of each vector op and accumulated
per cycle; with at least four output words per PE the cycles carry different
outputs instead, so no cross-cycle combine is needed.
"""

from __future__ import annotations

from collections import defaultdict

from .errors import CompileError
from .ir import Node, walk
from .layout import Contract
from .local import analyze, _canon
from .machine import Mem
from .select import Constants, GroupGen, lane_type
from .vprog import FlagUse, Use, Value, VOp, VProgram

REDUCERS = {"sum", "max", "min", "lor", "land"}


def _bind_term(template: Node, node: Node, leaves: dict, mapping: dict):
    if template.op != node.op or len(template.args) != len(node.args):
        raise CompileError("term structure mismatch")
    if template.op == "input":
        leaf = leaves[node.id]
        word = (leaf.space, leaf.addr)
        if mapping.setdefault(template.id, word) != word:
            raise CompileError("term sharing mismatch")
        return
    if template.op == "const":
        if template.value != node.value:
            raise CompileError("term constant mismatch")
        return
    for t, n in zip(template.args, node.args):
        _bind_term(t, n, leaves, mapping)


def local_reduce_strategy(source, contract: Contract, outputs: dict, *, variant=None):
    """Variants: one accumulator chain per cycle slot, two interleaved chains (shorter critical
    path for long reductions), and integer comparisons made on float copies by the MAU."""
    base = _local_reduce(source, contract, outputs, variant=None)
    out = [("base", base)]
    if getattr(base, "chains", False):
        out.append(("split2", _local_reduce(source, contract, outputs, variant={"split": True})))
    for name, var in (("fcmp", {"fcmp": True}), ("fcmp-split4", {"fcmp": True, "split": 4})):
        if "split" in var and not getattr(base, "chains", False):
            continue
        try:
            out.append((name, _local_reduce(source, contract, outputs, variant=var)))
        except CompileError:
            break
    return out[0][1] if len(out) == 1 else out


def _local_reduce(source, contract: Contract, outputs: dict, *, variant=None):
    lp = analyze(contract, outputs, offsets=True)
    prog = VProgram()
    consts = Constants(prog)
    shifted = set()
    if getattr(lp, "shift", None):
        # one input moves by a per-PE amount: T holds its word offset, its leaves read T-indirectly
        if len(lp.shift) != 1:
            raise CompileError("local reduce: several shifted inputs")
        from .compiler import _shift_fit
        from .generate import bitlinear_value

        (tensor, delta), = lp.shift.items()
        coef = _shift_fit(delta, 2)
        bitlinear_value(prog, consts, coef[0], 0, coef[2:], dst=Mem("t", 4))
        shifted = {tensor}
    lt = lane_type(contract.outputs[0].dtype)
    ranges = {s.name: (s.low, s.high) for s in contract.inputs if s.low is not None}
    any_reduce = False
    for sig, tasks in lp.classes.items():
        rep = tasks[0]
        root = rep.lanes[min(rep.lanes)]
        if root.op not in REDUCERS or len(root.args) < 2:
            raise CompileError("local reduce: class is not a reduction")
        any_reduce = True
        op = root.op
        # terms per lane: list of term nodes; all terms share one template
        term_template = root.args[0]
        tshape = term_template.shape
        if any(t.shape != tshape for t in root.args):
            raise CompileError("local reduce: terms have different structure")
        n_terms = len(root.args)
        # bind every term of every task (lanes must agree on words)
        bound = []  # per task: list of {template input id: (space, addr)}
        for task in sorted(tasks, key=lambda t: t.addr):
            per_term = None
            for lane, node in task.lanes.items():
                maps = []
                for t in node.args:
                    m = {}
                    _bind_term(term_template, t, task.leaves, m)
                    maps.append(m)
                if per_term is not None and maps != per_term:
                    raise CompileError("local reduce: lanes read different words")
                per_term = maps
            bound.append((task, per_term))
        uses = {}
        for n in walk([term_template]):
            for a in n.args:
                uses[a.id] = uses.get(a.id, 0) + 1
        tind_ids = frozenset(n.id for n in walk([term_template]) if n.op == "input" and n.value[0] in shifted)
        fl = frozenset()
        if variant and variant.get("fcmp"):
            from .hier import _scratch

            bound, fl = _float_copies(prog, consts, term_template, bound, ranges, lt, _scratch(contract), tind_ids)
        else:
            bound = _stage_shared_memory(prog, term_template, bound, tind_ids)
        for _, per in bound:
            for m in per:
                # a shifted operand read straight from LM0 needs every other operand elsewhere
                if any(t in m and m[t][0] == "lm0" for t in tind_ids) and any(
                        v[0] == "lm0" for k, v in m.items() if k not in tind_ids and isinstance(v, tuple)):
                    raise CompileError("local reduce: shifted operands must be staged")
        if len(bound) >= 4:
            _cycles_are_outputs(prog, consts, lt, ranges, uses, op, term_template, bound, n_terms, fl, tind_ids)
        else:
            prog.chains = True
            for task, per_term in bound:
                _cycles_are_terms(prog, consts, lt, ranges, uses, op, term_template, task, per_term,
                                  chain_split=int(variant.get("split", 0)) if variant else 0, float_inputs=fl, tind_ids=tind_ids)
    if not any_reduce:
        raise CompileError("local reduce: nothing to reduce")
    return prog


def _float_copies(prog, consts, template, bound, ranges, lt, scratch=None, tind_ids=frozenset()):
    """Integer comparison terms of small non-negative inputs: copy every operand position's words
    to GRF as exact floats once (int bits | 2^23 as float, minus 2^23), so the comparisons run on
    the MAU (sign flags) while the ALU only accumulates."""
    from .select import MAGIC23

    if lt.kind not in ("int", "uint") or lt.bits != 32 or template.ty != "b" or template.op not in ("ge", "gt", "le", "lt"):
        raise CompileError("float compare: not a 32-bit integer comparison")
    leaves = [n for n in walk([template]) if n.op == "input"]
    if not leaves or any(n.ty != "i" for n in leaves) or set(template.args) - set(leaves):
        raise CompileError("float compare: operands are not input words")
    for n in leaves:
        r = ranges.get(n.value[0])
        if r is None or r[0] is None or r[0] < 0 or r[1] >= 1 << 23:
            raise CompileError("float compare: operand range")
    magic = consts.word32(MAGIC23)
    out = [(task, [dict(m) for m in per]) for task, per in bound]
    # the two operands of a comparison in different memories (read ports); GRF1 stays free for
    # the accumulators when a free LM area takes the second copy
    banks = ("grf0", scratch[0] if scratch else "grf1")
    next_base = {"grf0": 0, "grf1": 0}
    if scratch:
        next_base[scratch[0]] = 2 * scratch[1]
    for k, n in enumerate(leaves):
        bank = banks[k % 2]
        base = next_base[bank]
        sp = {m[n.id][0] for _, per in bound for m in per}
        if len(sp) != 1:
            raise CompileError("float compare: operand in several memories")
        sp = sp.pop()
        addrs = sorted({m[n.id][1] for _, per in bound for m in per})
        lo, hi = addrs[0], addrs[-1] + 1
        n_long = (hi - lo + 3) // 4 * 4
        if base + 2 * n_long > (448 if bank.startswith("grf") else 4096):
            raise CompileError("float compare: copies do not fit")
        for i in range(0, n_long, 4):
            src = Mem(sp, 2, tuple(2 * (lo + i + c) for c in range(4)), tind=n.id in tind_ids)
            b = VOp("ior", [src, Use(magic)], out=Value(2), unit="alu", note="float copy")
            prog.add(b)
            prog.add(VOp("fvadd", [Use(b.out), Use(magic, neg=True)], dsts=[Mem(bank, 2, tuple(base + 2 * (i + c) for c in range(4)))], unit="mau", note="float copy"))
        for _, per in out:
            for m in per:
                m[n.id] = (bank, base // 2 + m[n.id][1] - lo)
        next_base[bank] = base + 2 * n_long
    res = dict(prog.notes.get("grf_reserved", {}))
    for b, v in next_base.items():
        if b.startswith("grf"):
            res[b] = max(res.get(b, 0), v)
    prog.notes["grf_reserved"] = res
    return out, frozenset(n.id for n in leaves)


def _stage_shared_memory(prog, template, bound, tind_ids=frozenset()):
    """Two operand positions of every term read the same LM: each op would need a copy to
    resolve the read-port conflict. Copy the second position's words to GRF0 once with
    two-long-word copies and read them there (a T-indirect position is always copied)."""
    leaves = [n.id for n in walk([template]) if n.op == "input"]
    if tind_ids:
        targets = [t for t in leaves if t in tind_ids]
        if len(targets) != 1:
            raise CompileError("local reduce: one shifted operand position")
        tgt = targets[0]
        others = [t for t in leaves if t != tgt]

        def span(tid):
            sps = {m[tid][0] for _, per in bound for m in per}
            addrs = sorted({m[tid][1] for _, per in bound for m in per})
            return sps, addrs[-1] + 1 - (addrs[0] - addrs[0] % 2)

        t_sp, t_n = span(tgt)
        if len(others) == 1:
            o_sp, o_n = span(others[0])
            # the unshifted operand copies with aligned two-long-word moves (8 long words per op),
            # the shifted one only long word by long word: stage whichever is cheaper
            if o_sp == t_sp and len(o_sp) == 1 and -(-o_n // 8) < -(-t_n // 4):
                staged = _copy_position(prog, bound, others[0])
                if staged is not bound:
                    return staged
        return _copy_position(prog, bound, tgt, tind=True)
    if len(leaves) < 2:
        return bound
    spaces = {tid: {m[tid][0] for _, per in bound for m in per} for tid in leaves}
    first = {}
    target = None
    for tid in leaves:
        if len(spaces[tid]) != 1:
            return bound
        sp = next(iter(spaces[tid]))
        if sp in ("lm0", "lm1") and sp in first.values():
            target = tid
            break
        first[tid] = sp
    if target is None:
        return bound
    return _copy_position(prog, bound, target)


def _copy_position(prog, bound, target, tind=False):
    spaces = {m[target][0] for _, per in bound for m in per}
    if len(spaces) != 1:
        return bound
    addrs = sorted({m[target][1] for _, per in bound for m in per})
    lo = addrs[0] - addrs[0] % 2
    hi = addrs[-1] + 1
    n_long = (hi - lo + 7) // 8 * 8
    base = prog.notes.get("grf_reserved", {}).get("grf0", 0)
    base = (base + 3) // 4 * 4
    if base + 2 * n_long > 448:
        return bound
    sp = next(iter(spaces))
    # T-indirect offsets may be odd long words: copy long words then (two-long-word access must be aligned)
    wl, step = (2, 4) if tind else (4, 8)
    for i in range(0, n_long, step):
        src = Mem(sp, wl, tuple(2 * (lo + i + (wl // 2) * c) for c in range(4)), tind=tind)
        dst = Mem("grf0", wl, tuple(base + 2 * (i + (wl // 2) * c) for c in range(4)))
        prog.add(VOp("lpassa", [src], dsts=[dst], unit="alu", note="stage operand"))
    res = dict(prog.notes.get("grf_reserved", {}))
    res["grf0"] = base + 2 * n_long
    prog.notes["grf_reserved"] = res
    out = []
    for task, per in bound:
        new = []
        for m in per:
            m = dict(m)
            s_, a = m[target]
            m[target] = ("grf0", base // 2 + a - lo)
            new.append(m)
        out.append((task, new))
    return out


def _accumulate(gen: GroupGen, op, term_template, acc, lt, complement_ok=False):
    """Compute the template (operands bound in gen) and fold it into acc; returns the new acc."""
    t = term_template
    if lt.kind == "float":
        p = lt.fprec
        if op == "sum":
            if t.op == "mul" and len(t.args) == 2 and acc is not None:
                return gen.emit(f"{p}vfma", [gen.operand(t.args[0], "float"), gen.operand(t.args[1], "float"), acc])
            val = gen.operand(t, "float")
            return val if acc is None else gen.emit(f"{p}vadd", [val, acc])
        if op in ("max", "min"):
            val = gen.operand(t, "float")
            return val if acc is None else gen.emit(f"{p}{op}", [val, acc])
    else:
        q = lt.iprec
        u = "u" if lt.unsigned else ""
        if op == "sum":
            if t.ty == "b":
                flags, pol = gen.flags(t)
                if acc is None and (pol or complement_ok):
                    # the first count in one op: 1 where the flag is set, 0 elsewhere (zero flush)
                    vop = gen.op("lpassa", [Use(gen.consts.scalar(1, lt))], "alu", flush=FlagUse(flags))
                    vop.out.complement = not pol
                    return vop.out
                if acc is None:
                    acc = gen.emit("lpassa", [gen.consts.scalar(0, lt)])
                if pol or complement_ok:
                    # with the opposite polarity count where the condition fails; the caller
                    # turns the count into (terms - count) once at the end
                    vop = gen.op(f"{u}{q}inc", [Use(acc)], "alu", write_mask=FlagUse(flags), merge_into=acc)
                    vop.out.complement = not pol
                    return vop.out
                # count the complement: inc everywhere, then undo where the flag is set
                inc = gen.emit(f"{u}{q}inc", [acc])
                vop = gen.op("lpassa", [Use(acc)], "alu", write_mask=FlagUse(flags), merge_into=inc)
                return vop.out
            val = gen.operand(t, "int")
            return val if acc is None else gen.emit(f"{u}{q}add", [val, acc])
        if op in ("max", "min"):
            val = gen.operand(t, "int")
            return val if acc is None else gen.emit(f"{u}{q}{op}", [val, acc])
        if op in ("lor", "land") and t.ty == "b":
            # 0/1 accumulator: set (or clear) where the term's flag says so
            flags, pol = gen.flags(t)
            if acc is None:
                acc = gen.emit("lpassa", [gen.consts.scalar(0 if op == "lor" else 1, lt)])
            if op == "land":
                pol = not pol
            new = gen.consts.scalar(1 if op == "lor" else 0, lt)
            if pol:
                vop = gen.op("lpassa", [Use(new)], "alu", write_mask=FlagUse(flags), merge_into=acc)
                return vop.out
            vop = gen.op("lpassa", [Use(acc)], "alu", write_mask=FlagUse(flags), merge_into=gen.emit("lpassa", [new]))
            return vop.out
    raise CompileError(f"local reduce: no accumulation for {op} on {lt}")


def _final_combine(gen: GroupGen, op, acc: Value, lt):
    """Fold the four cycle slots of acc into one value (valid in every cycle)."""
    if lt.kind == "float":
        p = lt.fprec
        first = f"{p}vpassa"
        name = {"sum": f"{p}vadd", "max": f"{p}max", "min": f"{p}min"}[op]
    else:
        q = lt.iprec
        u = "u" if lt.unsigned else ""
        first = "lpassa"
        name = {"sum": f"{u}{q}add", "max": f"{u}{q}max", "min": f"{u}{q}min"}[op]
    def slot(c):
        if isinstance(acc, Mem):  # an operand read directly: read the cycle's address in every cycle
            return Mem(acc.space, acc.wl, (acc.addrs[c],) * 4, neg=acc.neg, tind=acc.tind)
        return Use(acc, cycle=c)

    cur = gen.emit(first, [slot(0)])
    for c in (1, 2, 3):
        cur = gen.emit(name, [cur, slot(c)])
    return cur


def _cycles_are_outputs(prog, consts, lt, ranges, uses, op, template, bound, n_terms, float_inputs=frozenset(), tind_ids=frozenset()):
    groups = [bound[i:i + 4] for i in range(0, len(bound), 4)]
    for group in groups:
        while len(group) < 4:
            group = group + [group[-1]]
        acc = None
        for k in range(n_terms):
            operands = {tid: Mem(group[0][1][k][tid][0], 2, tuple(per[k][tid][1] * 2 for _, per in group),
                                 tind=tid in tind_ids and group[0][1][k][tid][0] == "lm0") for tid in group[0][1][k]}
            gen = GroupGen(prog, consts, lt, operands, ranges, uses)
            gen.float_inputs = float_inputs
            acc = _accumulate(gen, op, template, acc, lt, complement_ok=True)
        dst = Mem(group[0][0].out.space, 2, tuple(t.addr * 2 for t, _ in group))
        gen = GroupGen(prog, consts, lt, {}, ranges, uses)
        if getattr(acc, "complement", False):
            gen.emit(f"{'u' if lt.unsigned else ''}{lt.iprec}sub", [gen.consts.scalar(n_terms, lt), acc], dst)
        else:
            gen.emit("lpassa", [acc], dst)


def _combine(gen, op, a, b, lt):
    if lt.kind == "float":
        p = lt.fprec
        name = {"sum": f"{p}vadd", "max": f"{p}max", "min": f"{p}min"}[op]
    else:
        q, u = lt.iprec, "u" if lt.unsigned else ""
        name = {"sum": f"{u}{q}add", "max": f"{u}{q}max", "min": f"{u}{q}min", "lor": f"{q}or", "land": f"{q}and"}[op]
    return gen.emit(name, [a, b])


def _cycles_are_terms(prog, consts, lt, ranges, uses, op, template, task, per_term, chain_split=False, float_inputs=frozenset(), tind_ids=frozenset()):
    n = len(per_term)
    chunks = [per_term[i:i + 4] for i in range(0, n, 4)]
    acc = None
    ways = 2 if chain_split in (True, 1) else int(chain_split or 0)
    accs, accs_done = [None] * max(ways, 1), []
    pad_identity = None
    for chunk in chunks:
        live = len(chunk)
        while len(chunk) < 4:
            chunk = chunk + [chunk[-1]]
        operands = {tid: Mem(chunk[0][tid][0], 2, tuple(m[tid][1] * 2 for m in chunk), tind=tid in tind_ids and chunk[0][tid][0] == "lm0")
                    for tid in chunk[0]}
        gen = GroupGen(prog, consts, lt, operands, ranges, uses)
        gen.float_inputs = float_inputs
        if live < 4 and op == "sum":
            # padded cycles would count a term twice: give them their own accumulator slot by
            # computing the chunk separately and masking the padding to the identity
            val = gen.operand(template, "float" if lt.kind == "float" else "int") if template.ty != "b" else None
            if val is None:
                flags, pol = gen.flags(template)
                zero = gen.consts.scalar(0, lt)
                one = gen.consts.scalar(1, lt)
                base = gen.emit("lpassa", [zero if pol else one])
                val = gen.op("lpassa", [gen._use(one if pol else zero)], "alu", write_mask=FlagUse(flags), merge_into=base).out
            from .machine import Mask

            masked = gen.op("lpassa", [gen._use(val)], "alu", flush=Mask(pattern="1" * live + "0" * (4 - live))).out
            p = lt.fprec if lt.kind == "float" else lt.iprec
            add = f"{p}vadd" if lt.kind == "float" else f"{'u' if lt.unsigned else ''}{p}add"
            acc = masked if acc is None else gen.emit(add, [masked, acc])
            continue
        if live < 4 and op in ("max", "min"):
            pass  # duplicates do not change max/min
        if chain_split and live == 4:
            # independent accumulators break the dependency chain of long reductions
            k = len(accs_done) % ways
            accs[k] = _accumulate(gen, op, template, accs[k], lt, complement_ok=n % 4 == 0)
            accs_done.append(k)
            continue
        acc = _accumulate(gen, op, template, acc, lt, complement_ok=n % 4 == 0)
    gen = GroupGen(prog, consts, lt, {}, ranges, uses)
    if chain_split:
        parts = [a for a in accs if a is not None] + ([acc] if acc is not None else [])
        comps = {getattr(a, "complement", False) for a in parts}
        if len(comps) > 1:
            raise CompileError("local reduce: mixed complement accumulators")
        complement = comps.pop()
        acc = parts[0]
        for a in parts[1:]:
            acc = _combine(gen, op, acc, a, lt)
        if complement:
            acc.complement = True
    complement = getattr(acc, "complement", False)
    dst = Mem(task.out.space, 2, (task.addr * 2,) * 4)
    if complement:
        # terms - (c0 + c1 + c2 + c3) as a subtraction chain from the constant (no staging copy)
        sub = f"{'u' if lt.unsigned else ''}{lt.iprec}sub"
        cur = gen.consts.scalar(n, lt)
        for c in range(4):
            cur = gen.emit(sub, [cur, Use(acc, cycle=c)], dst if c == 3 else None)
    else:
        gen.emit("lpassa", [_final_combine(gen, op, acc, lt)], dst)
