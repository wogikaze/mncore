"""Split the outputs over replicated MABs, then gather them into the output MAB.

When every input is broadcast over the 16 MABs of an L1B but the outputs live
only in MAB 0, the other MABs would idle. The output long words are dealt out
to the MABs (word a goes to MAB (a - D) % 16), every MAB computes its share
with a PE-level strategy into a staging area (inputs read T-indirectly at a
per-MAB offset, so the program stays SPMD), and the shares are gathered back:
``l1bmd`` collects one staging word per MAB and PE per cycle into the L1BM and
two-long-word ``l1bmm`` broadcasts the L1BM to every MAB at the output
addresses (L1BM index I lands at D + I // 4).
"""

from __future__ import annotations

from .errors import CompileError
from .layout import Contract, Loc
from .machine import Instr, L1, Mem, Step


def split_strategy(source, contract: Contract, outputs: dict, *, variant=None):
    from .compiler import Outputs, local_strategy
    from .hier import ExplicitSpec, _scratch, mab_reduce_strategy
    from .schedule import schedule
    from .sim import assembler

    if len(contract.outputs) != 1:
        raise CompileError("split: one output")
    out = contract.outputs[0]
    if out.space == "dram" or any(s.space == "dram" for s in contract.inputs):
        raise CompileError("split: LM tensors only")
    for s in contract.inputs:
        if not any(d.axis == "MAB" and d.size == 16 for d in s.layout.broadcast):
            raise CompileError("split: an input is not broadcast over the MABs")
    locs = {idx: out.locations(idx, replicate=False)[0] for idx in outputs[out.name]}
    if any(l.pe % 64 // 4 for l in locs.values()):
        raise CompileError("split: outputs outside MAB 0")
    addrs = sorted({l.addr for l in locs.values()})
    D = addrs[0] // 2 * 2
    n_up = (max(a - D for a in addrs) // 16) // 4 + 1
    need = sorted({a - D for a in addrs})  # I // 4 = 16 s + u = a - D for every output word
    # the broadcast writes [D, D + top) of every MAB: it must not touch an input in that memory
    top = (max(need) // 8 + 1) * 8
    for s in contract.inputs:
        if s.space == out.space and s.start < 2 * (D + top) and 2 * D < s.end:
            raise CompileError("split: the gather would overwrite an input")
    space, base = _scratch(contract)
    stage = (base + 3) // 4 * 4
    new_locs, nodes = {}, {}
    for idx, l in locs.items():
        u, s = (l.addr - D) % 16, (l.addr - D) // 16
        pe = (l.pe // 64 * 16 + u) * 4 + l.pe % 4
        new_locs[idx] = Loc(pe, stage + s, l.lane)
        nodes[idx] = outputs[out.name][idx]
    pspec = ExplicitSpec("__split", out.dtype, space, new_locs, out.atol)
    pcontract = Contract(contract.inputs, [pspec])
    pout = Outputs({"__split": nodes})
    pout.graph = outputs.graph
    up = [Instr("l1bmd", (Mem(space, 2, tuple(2 * (stage + 4 * blk + c) for c in range(4))),), (L1(256 * blk, 2),))
          for blk in range(n_up)]
    blocks = sorted({i // 8 for i in need})  # 2-long-word l1bmm moves 32 L1BM words = 8 output words per PE
    down = [Instr("l1bmm", (L1(32 * b, 4),), (Mem(out.space, 4, tuple(2 * (D + 8 * b + 2 * c) for c in range(4))),))
            for b in blocks]
    asm = assembler()
    results = []
    for sname, strat in (("local", local_strategy), ("mab-reduce", mab_reduce_strategy)):
        try:
            res = strat(source, pcontract, pout)
        except CompileError:
            continue
        for vname, prog in (res if isinstance(res, list) else [("", res)]):
            try:
                steps = schedule(prog, asm, tries=2)
            except CompileError:
                continue
            steps = steps + [Step(nop=3)] + [Step([i]) for i in up] + [Step(nop=3)] + [Step([i]) for i in down]
            results.append((f"{sname}{'/' + vname if vname else ''}", steps))
    if not results:
        raise CompileError("split: no PE-level strategy computes the shares")
    return results
