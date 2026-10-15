"""Reductions across the four PEs of a MAB.

Each output is reduce(op, terms) where every term is an input element held by
one of the PEs of the output's MAB. Every PE first combines its own terms for
four outputs at a time (one output per cycle; word-width reads gather terms
from any lane into lane 0), then the partial results are combined across the
PEs with rotations (msl) so that every PE holds the total, which is written to
the output word.
"""

from __future__ import annotations

from collections import defaultdict

from .errors import CompileError
from .layout import Contract, pe_coords
from .machine import Fixed, Mask, Mem
from .select import Constants, lane_type
from .vprog import Use, Value, VOp, VProgram

REDUCERS = {"sum", "max", "min"}


def pe_reduce_strategy(source, contract: Contract, outputs: dict, *, variant=None):
    if len(contract.outputs) != 1:
        raise CompileError("pe-reduce: one output")
    out = contract.outputs[0]
    if out.space == "dram":
        raise CompileError("pe-reduce: DRAM output")
    specs = {s.name: s for s in contract.inputs}
    dtype = out.dtype
    if any(s.dtype != dtype for s in contract.inputs):
        raise CompileError("pe-reduce: mixed dtypes")
    word_level = dtype.bits == 32
    items = []
    op = None
    for idx, node in outputs[out.name].items():
        if node.op not in REDUCERS:
            raise CompileError("pe-reduce: output is not a reduction")
        if op not in (None, node.op):
            raise CompileError("pe-reduce: mixed reductions")
        op = node.op
        loc = out.locations(idx, replicate=False)[0]
        mab = loc.pe // 4
        per_pe = defaultdict(list)
        for t in node.args:
            if t.op != "input":
                raise CompileError("pe-reduce: terms must be input elements")
            spec = specs[t.value[0]]
            cands = [l for l in spec.locations(t.value[1], replicate=True) if l.pe // 4 == mab]
            if not cands:
                raise CompileError("pe-reduce: term outside the output's MAB")
            l = min(cands, key=lambda l: l.pe)
            if not word_level and l.lane:
                raise CompileError("pe-reduce: 64-bit lanes")
            addr = 2 * l.addr + l.lane if word_level else 2 * l.addr
            per_pe[l.pe % 4].append((spec.space, addr))
        items.append((loc, per_pe))
    counts = {len(v) for _, pp in items for v in pp.values()}
    used = {p for _, pp in items for p in pp}
    if len(counts) != 1:
        raise CompileError("pe-reduce: uneven terms per PE")
    n_t = counts.pop()
    pes = sorted(used)
    # SPMD: every PE reads the same addresses for a given output and term position
    for loc, pp in items:
        lists = [sorted(pp[p]) for p in pes]
        if any(l != lists[0] for l in lists):
            raise CompileError("pe-reduce: PEs hold terms at different addresses")
    if len(pes) not in (1, 2, 4):
        raise CompileError("pe-reduce: unsupported PE set")
    prog = VProgram()
    wl = 1 if word_level else 2
    fl = dtype.is_float
    p = {64: "d", 32: "f", 16: "h"}[dtype.bits] if fl else {64: "l", 32: "i", 16: "s"}[dtype.bits]
    u = "u" if dtype.kind == "uint" else ""
    if fl:
        combine = {"sum": (f"{p}vadd", "mau"), "max": (f"{p}max", "alu"), "min": (f"{p}min", "alu")}[op]
        first = (f"{p}vpassa", "mau") if op == "sum" else ("lpassa", "alu")
    else:
        combine = {"sum": (f"{u}{p}add", "alu"), "max": (f"{u}{p}max", "alu"), "min": (f"{u}{p}min", "alu")}[op]
        first = ("lpassa", "alu")
    order = sorted(items, key=lambda it: (it[0].addr, it[0].lane, it[0].pe))
    out_word = lambda loc: (2 * loc.addr + loc.lane) if word_level else 2 * loc.addr  # noqa: E731
    for g in range(0, len(order), 4):
        chunk = order[g:g + 4]
        live = len(chunk)
        while len(chunk) < 4:
            chunk = chunk + [chunk[-1]]
        terms = [sorted(chunk[c][1][pes[0]]) for c in range(4)]
        acc = None
        for t in range(n_t):
            space = terms[0][t][0]
            mem = Mem(space, wl, tuple(terms[c][t][1] for c in range(4)))
            if acc is None:
                acc = VOp(first[0], [mem], out=Value(2), unit=first[1])
            else:
                acc = VOp(combine[0], [mem, Use(acc.out)], out=Value(2), unit=combine[1])
            prog.add(acc)
        cur = acc.out
        # rotations across PEs
        shifts = {1: [], 2: [1], 4: [1, 2]}[len(pes)]
        dst_words = [out_word(chunk[c][0]) for c in range(4)]
        mask = None if live == 4 else Mask(pattern="1" * live + "0" * (4 - live))
        dst = Mem(out.space, wl, tuple(dst_words), mask=mask)
        if not shifts:
            prog.add(VOp("lpassa", [Use(cur)], dsts=[dst], unit="alu"))
        for n, k in enumerate(shifts):
            rot = cur
            for _ in range(k):
                r = VOp("msl", [Use(rot)], out=Value(2), unit="alu")
                prog.add(r)
                rot = r.out
            last = n == len(shifts) - 1
            c = VOp(combine[0], [Use(cur), Use(rot)], out=None if last else Value(2), dsts=[dst] if last else [], unit=combine[1])
            prog.add(c)
            cur = c.out
    return prog
