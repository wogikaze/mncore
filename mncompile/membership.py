"""Membership tests over a small integer domain with a table in LM0.

    out = any(x == y for y in S)      (x and the elements of S stored in the output's PE)

Comparing x with every element costs one op per pair. With integer values in a small
range, a table indexed by value is cheaper: every PE clears the table entries of its
probes x, marks the entries of its own elements y (scatter: the value goes to the T
register and the write uses T-indirect addressing), then reads the entries of its probes
back (gather). Clearing the probed entries first keeps the result independent of what
the table area held before. One T load and one table access per four values.
"""

from __future__ import annotations

from collections import defaultdict

from .errors import CompileError
from .ir import walk
from .machine import Mem
from .vprog import Use, Value, VOp, VProgram

MAX_SPAN = 1024  # table entries (long words)


def _probe_and_set(node):
    """(probe leaf, [set leaves]) for lor/toint(lor) of eq(probe, element)."""
    if node.op == "toint":
        node = node.args[0]
    terms = node.args if node.op == "lor" else (node,)
    if any(t.op != "eq" or any(a.op != "input" for a in t.args) for t in terms):
        raise CompileError("membership: a term is not an equality of two inputs")
    # the probe is the leaf every term shares (operand order inside eq is not canonical)
    common = set(terms[0].args)
    for t in terms[1:]:
        common &= set(t.args)
    if not common:
        raise CompileError("membership: terms do not share one probe")
    probe = terms[0].args[0] if terms[0].args[0] in common else terms[0].args[1]
    elems = [t.args[1] if t.args[0] is probe else t.args[0] for t in terms]
    return probe, elems


def membership_strategy(source, contract, outputs, *, variant=None):
    if len(contract.outputs) != 1:
        raise CompileError("membership: one output")
    out = contract.outputs[0]
    if out.dtype.is_float or out.space == "dram":
        raise CompileError("membership: integer LM output")
    specs = {s.name: s for s in contract.inputs}
    items = list(outputs[out.name].items())
    rep_pe = None
    words = []  # (output loc, probe (space, word addr, lane), set {(space, long addr, lane)})
    probe_spec = set_spec = None
    for idx, node in items:
        loc = out.locations(idx, replicate=False)[0]
        probe, elems = _probe_and_set(node)
        ps, es = specs[probe.value[0]], {specs[e.value[0]].name for e in elems}
        if len(es) != 1:
            raise CompileError("membership: elements from several tensors")
        probe_spec, set_spec = ps, specs[es.pop()]

        def local(leaf, spec):
            cands = [l for l in spec.locations(leaf.value[1], replicate=True) if l.pe == loc.pe]
            if not cands:
                raise CompileError("membership: an operand is not stored in the output's PE")
            return (spec.space, cands[0].addr, cands[0].lane)

        p = local(probe, probe_spec)
        sset = frozenset(local(e, set_spec) for e in elems)
        if rep_pe is None:
            rep_pe = loc.pe
        if loc.pe == rep_pe:
            words.append((loc, p, sset))
    # SPMD: the other PEs hold their probes and elements at the same addresses (checked on the rep's
    # structure only; verification covers the rest)
    for s in (probe_spec, set_spec):
        if s.dtype.is_float or s.low is None or s.high is None:
            raise CompileError("membership: integer operands with a known range")
    lo = min(probe_spec.low, set_spec.low)
    hi = max(probe_spec.high, set_spec.high)
    if hi - lo + 1 > MAX_SPAN:
        raise CompileError("membership: value range too large for a table")
    elems = sorted(set().union(*[w[2] for w in words]))
    if any(w[2] != frozenset(elems) for w in words):
        raise CompileError("membership: outputs test different element sets")
    # the table: long word entries in LM0 after the LM0 tensors
    used0 = max([s.end for s in list(contract.inputs) + list(contract.outputs) if s.space == "lm0"] + [0])
    table = (used0 + 3) // 4 * 4  # word address of value lo
    if table + 2 * (hi - lo + 1) > 4096:
        raise CompileError("membership: the table does not fit in LM0")
    base = table - 2 * lo  # address field: entry of value v at base + 2 v
    if base < 0:
        raise CompileError("membership: negative table base")
    bits = max(probe_spec.dtype.bits, set_spec.dtype.bits)
    return [(name, _program(clear, words, elems, probe_spec, set_spec, out, base, table, lo, hi, bits))
            for name, clear in (("clear", True), ("zero-init", False))]


def _program(clear, words, elems, probe_spec, set_spec, out, base, table, lo, hi, bits):
    """`clear` False skips step 1: the table area then must start zeroed (the emulator starts
    with zeroed memory; verification decides)."""
    prog = VProgram()
    from .select import Constants

    consts = Constants(prog)
    one = consts.word64(1) if out.dtype.bits == 64 else consts.word32(1)
    zero = consts.word32(0) if clear else None

    def t_load(group):
        """T <- 2 * value for four (space, long addr, lane) operands (one op)."""
        spaces = {g[0] for g in group}
        lanes = {g[2] for g in group}
        if len(spaces) != 1 or len(lanes) != 1:
            raise CompileError("membership: mixed lanes in a group")
        sp, lane = spaces.pop(), lanes.pop()
        src = Mem(sp, 2, tuple(2 * g[1] for g in group))
        if bits == 64:
            op = VOp("ladd", [src, src], dsts=[Mem("t", 4)], unit="alu", note="table index")
        elif lane == 1:
            op = VOp("iadd", [src, src], dsts=[Mem("t", 4)], unit="alu", note="table index")
        else:
            op = VOp("ullsr", [src, Use(consts.word64(31))], dsts=[Mem("t", 4)], unit="alu", note="table index")
        prog.add(op)

    def groups(seq):
        seq = list(seq)
        for i in range(0, len(seq), 4):
            g = seq[i:i + 4]
            yield g + [g[-1]] * (4 - len(g)), len(g)

    entry = Mem("lm0", 2, (base,) * 4, tind=True, trange=(table, table + 2 * (hi - lo + 1)))
    probes = sorted({w[1] for w in words})
    by_probe_lane = defaultdict(list)
    for p in probes:
        by_probe_lane[p[2]].append(p)
    # 1. clear the probed entries, 2. mark the elements, 3. read the probes back
    for lane, ps in by_probe_lane.items() if clear else ():
        for g, _n in groups(ps):
            t_load(g)
            prog.add(VOp("lpassa", [Use(zero)], dsts=[entry], unit="alu", note="table clear"))
    by_elem_lane = defaultdict(list)
    for e in elems:
        by_elem_lane[e[2]].append(e)
    for lane, es in by_elem_lane.items():
        for g, _n in groups(es):
            t_load(g)
            prog.add(VOp("lpassa", [Use(one)], dsts=[entry], unit="alu", note="table mark"))
    by_lane = defaultdict(list)
    for loc, p, _s in words:
        by_lane[p[2]].append((loc, p))
    for lane, ws in by_lane.items():
        ws.sort(key=lambda w: (w[0].addr, w[0].lane))
        for g, n in groups(ws):
            t_load([p for _l, p in g])
            if out.dtype.bits == 64:
                dst = Mem(out.space, 2, tuple(2 * l.addr for l, _p in g))
            else:
                dst = Mem(out.space, 1, tuple(2 * l.addr + l.lane for l, _p in g))
            if dst.space == "lm0":
                # LM0 cannot be read (table) and written (elsewhere) in one step: go through a register
                v = VOp("lpassa", [entry], out=Value(2), unit="alu", note="table read")
                prog.add(v)
                prog.add(VOp("lpassa", [Use(v.out)], dsts=[dst], unit="alu", note="table result"))
            else:
                prog.add(VOp("lpassa", [entry], dsts=[dst], unit="alu", note="table read"))
    return prog
