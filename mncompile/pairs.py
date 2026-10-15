"""All-pairs reductions: out = sum over j < k of f(x[j], x[k]) along one axis of an input row.

The pairs are grouped by diagonal d = k - j. When the input is broadcast over some
hierarchy axes, every replica unit takes its own diagonals: unit u sums
f(x[j], x[j + d]) over every j of the row for d in its share, reading x[j + d] through
the T register at a per-unit offset (so every unit runs the same program). Positions
past the end of the row read a sentinel S, written beforehand, chosen so that f(x, S) is
zero for every x in the input's domain. The unit partials are then reduced through the
transfer hierarchy (L1BM / L2BM / PDM) back to the output words.
"""

from __future__ import annotations

import math
from collections import defaultdict
from dataclasses import replace as dc_replace

from .errors import CompileError
from .ir import evaluate, walk
from .layout import Dim, Layout, Loc
from .machine import Imm, Mem, Step
from .vprog import VOp, VProgram

HIER = ("L2B", "L1B", "MAB")


def _pair_terms(node, specs):
    """(tensor, row index without the axis, axis, [(j, k, term)]) for a sum of two-leaf terms."""
    if node.op != "sum":
        raise CompileError("pairs: output is not a sum")
    info = None
    pairs = []
    for t in node.args:
        leaves = [n for n in walk([t]) if n.op == "input"]
        if len(leaves) != 2 or leaves[0].value[0] != leaves[1].value[0]:
            raise CompileError("pairs: a term does not read two elements of one tensor")
        (ta, ia), (tb, ib) = leaves[0].value, leaves[1].value
        diff = [a for a in range(len(ia)) if ia[a] != ib[a]]
        if len(diff) != 1:
            raise CompileError("pairs: the two elements differ in more than one index")
        ax = diff[0]
        row = ia[:ax] + ia[ax + 1:]
        key = (ta, row, ax)
        if info not in (None, key):
            raise CompileError("pairs: terms over different rows")
        info = key
        pairs.append((ia[ax], ib[ax], t, leaves))
    return info, pairs


def pairs_strategy(source, contract, outputs, *, variant=None):
    from .compiler import Outputs
    from .hier import ExplicitSpec, plan_chains
    from .reduce import local_reduce_strategy
    from .schedule import schedule
    from .select import Constants
    from .sim import assembler

    graph = outputs.graph
    if len(contract.outputs) != 1:
        raise CompileError("pairs: one output")
    out = contract.outputs[0]
    if out.space == "dram" or out.dtype.is_float:
        raise CompileError("pairs: integer LM output")
    specs = {s.name: s for s in contract.inputs}
    rows = {}
    template = None
    for idx, node in outputs[out.name].items():
        (tensor, row, ax), pairs = _pair_terms(node, specs)
        n = specs[tensor].shape[ax]
        want = {(j, k) for j in range(n) for k in range(j + 1, n)}
        got = {(j, k) for j, k, _t, _l in pairs}
        if got != want or len(pairs) != len(want):
            raise CompileError("pairs: not every pair j < k once")
        t0 = pairs[0][2]
        if template is None:
            template = (t0.shape, tensor, ax, n)
        if (t0.shape, tensor, ax, n) != template or any(t.shape != t0.shape for _j, _k, t, _l in pairs):
            raise CompileError("pairs: terms of different forms")
        # the first leaf of each term must be the j element
        if any(l[0].value[1][ax] != j for j, _k, _t, l in pairs):
            raise CompileError("pairs: leaf order differs from (j, k)")
        rows[idx] = (row, pairs)
    _shape, tensor, ax, n = template
    X = specs[tensor]
    dims = X.layout.axes[ax]
    if len(dims) != 1 or dims[0].axis != "":
        raise CompileError("pairs: the paired axis must be one address dimension")
    stride = dims[0].stride
    # replica units: hierarchy axes the input is broadcast over
    bdims = [d for d in X.layout.broadcast if d.axis in HIER]
    if not bdims:
        raise CompileError("pairs: the input is not replicated over the hierarchy")
    n_units = math.prod(d.size for d in bdims)
    n_diag = n - 1
    per_unit = -(-n_diag // n_units)
    dmax = n_units * per_unit
    # sentinel S: f(x, S) == 0 for the whole input domain
    lo_v, hi_v = X.low, X.high
    if lo_v is None or hi_v is None:
        raise CompileError("pairs: input range needed for a sentinel")
    sample_term = rows[next(iter(rows))][1][0]
    t_node, leaves = sample_term[2], sample_term[3]
    bits = X.dtype.bits
    # all-ones / zero first: one immediate fills them (hi + 1 needs one per distinct 32-bit half)
    cands = [(1 << bits) - 1 if X.dtype.kind == "uint" else (1 << (bits - 1)) - 1, 0, hi_v + 1, lo_v - 1]
    sentinel = None
    for S in cands:
        if X.dtype.kind == "uint" and not 0 <= S < 1 << bits:
            continue
        xs = sorted({lo_v, hi_v, (lo_v + hi_v) // 2})
        try:
            if all(not evaluate([t_node], {leaves[0].value: x, leaves[1].value: S})[0] for x in xs):
                sentinel = S
                break
        except Exception:  # noqa: BLE001 - a candidate the term cannot take
            continue
    if sentinel is None:
        raise CompileError("pairs: no sentinel value")
    # alias of X with the axis extended past the row (the shifted operand and its sentinels)
    ext = n + dmax
    alias_dims = list(X.layout.axes)
    alias_dims[ax] = (Dim(ext, "", stride),)
    alias = dc_replace(X, name=X.name + "~shift", layout=Layout(tuple(alias_dims), X.layout.broadcast, None))
    # unit of each replica coordinate tuple, and the partial expressions
    def unit_coords(u):
        coords = {}
        for d in reversed(bdims):
            u, r = divmod(u, d.size)
            coords[d.axis] = coords.get(d.axis, 0) + r * d.stride
        return coords

    parts = {}
    for idx, (row, pairs) in rows.items():
        loc = out.locations(idx, replicate=False)[0]
        home_pe = loc.pe
        by = {}
        for u in range(n_units):
            c = unit_coords(u)
            pe = home_pe
            # move the home PE to the unit's replica coordinates
            from .layout import pe_coords, pe_index

            hc = pe_coords(pe)
            for a, v in c.items():
                hc[a] = v
            m = pe_index(hc["L2B"], hc["L1B"], hc["MAB"], hc["PE"]) // 4
            terms = []
            for dd in range(per_unit):
                d = 1 + u + dd * n_units
                for j in range(n):
                    a_node = graph.input(tensor, row[:ax] + (j,) + row[ax:], leaves[0].ty)
                    b_node = graph.input(alias.name, row[:ax] + (j + d,) + row[ax:], leaves[1].ty)
                    terms.append(_rebuild(graph, t_node, {leaves[0].id: a_node, leaves[1].id: b_node}))
            by[m] = terms
        parts[(out.name, idx)] = by
    pcontract_inputs = list(contract.inputs) + [alias]
    from .layout import Contract

    space, chains = plan_chains(Contract(pcontract_inputs, contract.outputs), out, "sum", parts)
    asm = assembler()
    results = []
    # sentinel region: the alias addresses past the row, in every PE that holds the row
    base_long = X.base_long
    sent_lo = base_long + stride * n
    sent_hi = base_long + stride * (ext - 1) + 1
    fill_lo = sent_lo - sent_lo % 2
    fill_hi = fill_lo + -(-(sent_hi - fill_lo) // 8) * 8  # the fill writes whole groups of 8 long words
    for s2 in list(contract.inputs) + list(contract.outputs):
        if s2.space == X.space and s2.start < 2 * fill_hi and 2 * fill_lo < s2.end:
            raise CompileError("pairs: the sentinel area is not free")
    if fill_hi * 2 > 4096:
        raise CompileError("pairs: the sentinel area does not fit")
    for cost, name, hops, mreq in chains[:2]:
        locs, nodes = {}, {}
        for (pe, addr), eid in mreq.items():
            for lane, (o, mabs) in eid:
                (m,) = mabs
                ts = parts[o][m]
                k = (len(locs),)
                locs[k] = Loc(pe, addr, lane)
                nodes[k] = graph.make("sum", tuple(sorted(ts, key=lambda a: (a.shape, a.id))), ty=ts[0].ty)
        pspec = ExplicitSpec("__pairs", out.dtype, space, locs, out.atol)
        pc = Contract(pcontract_inputs, [pspec])
        po = Outputs({"__pairs": nodes})
        po.graph = graph
        try:
            res = local_reduce_strategy(source, pc, po)
        except CompileError:
            continue
        prologue = _sentinel_steps(X, sentinel, sent_lo, sent_hi, asm)
        phase_b = []
        for hop in hops:
            if hop:
                phase_b.append(Step(nop=3))
                phase_b += [Step([i]) for i in hop]
        for vname, prog in (res if isinstance(res, list) else [("", res)]):
            try:
                steps = schedule(prog, asm, tries=2)
            except CompileError:
                continue
            results.append((f"{name}+{vname}", prologue + [Step(nop=2)] + steps + phase_b))
    if not results:
        raise CompileError("pairs: no partial program")
    return results


def _rebuild(graph, node, mapping):
    if node.id in mapping:
        return mapping[node.id]
    if not node.args:
        return node
    return graph.make(node.op, tuple(_rebuild(graph, a, mapping) for a in node.args), value=node.value, ty=node.ty)


def _sentinel_steps(X, sentinel, lo, hi, asm):
    """Fill long words [lo, hi) of X's memory with the sentinel in every lane (immediate into a
    GRF word, then two-long-word copies; immediates cannot touch LM0)."""
    from .machine import Instr

    bits = X.dtype.bits
    word = sentinel & ((1 << 32) - 1) if bits <= 32 else sentinel & ((1 << 64) - 1)
    steps = []
    if bits == 64:
        hi_w, lo_w = word >> 32, word & 0xFFFFFFFF
        steps.append(Step([Instr("imm", (Imm("ui", "0x%08X" % hi_w),), (Mem("grf0", 4, (440,) * 4),))]))
        if lo_w != hi_w:
            steps.append(Step([Instr("imm", (Imm("ui", "0x%08X" % lo_w),), (Mem("grf0", 1, (441,) * 4),))]))
            steps.append(Step([Instr("imm", (Imm("ui", "0x%08X" % lo_w),), (Mem("grf0", 1, (443,) * 4),))]))
    else:
        steps.append(Step([Instr("imm", (Imm("ui", "0x%08X" % word),), (Mem("grf0", 4, (440,) * 4),))]))
    steps.append(Step(nop=2))
    a = lo - lo % 2
    while a < hi:
        addrs = tuple(2 * (a + 2 * c) for c in range(4))
        steps.append(Step([Instr("lpassa", (Mem("grf0", 4, (440,) * 4),), (Mem(X.space, 4, addrs),))]))
        a += 8
    return steps
