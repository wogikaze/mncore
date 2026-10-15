"""LM -> LM copies across the MABs of an L1B through the L1BM (all-gather).

Every source word is gathered into the L1BM with ``l1bmd`` (all MABs, one
address per cycle), the whole L1BM region is broadcast back to every MAB with
two-long-word ``l1bmm`` into a staging area of LM0, and each MAB picks its own
words with T-indirect reads: the staging address of a target word is a base
that depends only on the PE coordinates (held in T) plus a per-cycle offset
shared by all PEs.
"""

from __future__ import annotations

from collections import defaultdict

from .errors import CompileError
from .layout import Contract
from .machine import Instr, L1, Mem, Step


def allgather_steps(contract: Contract, outputs: dict):
    from .generate import bitlinear_value, fit_bits
    from .hier import _scratch
    from .schedule import schedule
    from .select import Constants
    from .sim import assembler
    from .vprog import VOp, VProgram

    if len(contract.outputs) != 1 or len(contract.inputs) != 1:
        raise CompileError("allgather: one input and one output")
    out, src = contract.outputs[0], contract.inputs[0]
    if out.space == "dram" or src.space == "dram" or out.dtype != src.dtype:
        raise CompileError("allgather: LM to LM copies of one dtype")
    # target long word -> (source MAB, source long address) for the same PE index and L1B
    need = {}
    for idx, node in outputs[out.name].items():
        if node.op != "input":
            raise CompileError("allgather: output is not a copy")
        loc = out.locations(idx, replicate=False)[0]
        cands = [l for l in src.locations(node.value[1], replicate=True)
                 if l.pe // 64 == loc.pe // 64 and l.pe % 4 == loc.pe % 4 and l.lane == loc.lane]
        if not cands:
            raise CompileError("allgather: source not in the target's L1B and PE column")
        s = min(cands, key=lambda l: l.pe)
        key = (loc.pe, loc.addr)
        val = (s.pe % 64 // 4, s.addr)
        if need.setdefault(key, val) != val:
            raise CompileError("allgather: lanes of a word come from different words")
    if all(k[0] // 4 == v[0] + k[0] // 64 * 16 for k, v in need.items()):
        raise CompileError("allgather: nothing crosses MABs")
    addrs = sorted({a for _, a in need.values()})
    n_up = (len(addrs) + 3) // 4
    top = 256 * n_up  # L1BM long words used
    space, _base = _scratch(contract)
    # staging area in LM0 (T-indirect reads are LM0 only), after the LM0 tensors
    used0 = max([s.end for s in (src, out) if s.space == "lm0"] + [0])
    stage = (used0 // 2 + 3) // 4 * 4
    if stage + top // 4 > 2048:
        raise CompileError("allgather: staging area does not fit")
    up = []
    for blk in range(n_up):
        chunk = addrs[4 * blk:4 * blk + 4]
        while len(chunk) < 4:
            chunk = chunk + [chunk[-1]]
        up.append(Instr("l1bmd", (Mem(src.space, 2, tuple(2 * a for a in chunk)),), (L1(256 * blk, 2),)))
    down = []
    for blk in range((top + 31) // 32):
        down.append(Instr("l1bmm", (L1(32 * blk, 4),), (Mem("lm0", 4, tuple(2 * (stage + 8 * blk + 2 * c) for c in range(4))),)))
    # staging long word in PE p holding (MAB mab, source address a): L1BM index 4s + p = 256 blk + 64 c + 4 mab + p
    def staged(mab, a):
        i = addrs.index(a)
        return (256 * (i // 4) + 64 * (i % 4) + 4 * mab) // 4

    by_addr = defaultdict(dict)
    for (pe, addr), (mab, a) in need.items():
        by_addr[addr][pe] = staged(mab, a)
    rep = min(pe for pe, _ in need)
    pes = sorted({pe for pe, _ in need})
    # s(pe, addr) = s(rep, addr) + delta(pe) for every address
    delta = {}
    for addr, per in by_addr.items():
        if rep not in per:
            raise CompileError("allgather: PEs hold different target words")
        for pe, sv in per.items():
            d = sv - per[rep]
            if delta.setdefault(pe, d) != d:
                raise CompileError("allgather: staging offsets are not a per-PE shift")
    coef = fit_bits([(pe, 0, (2 * d) % (1 << 32)) for pe, d in delta.items()])
    if coef is None:
        raise CompileError("allgather: per-PE staging offset is not linear in the coordinate bits")
    prog = VProgram()
    consts = Constants(prog)
    bitlinear_value(prog, consts, coef[0], 0, coef[2:], dst=Mem("t", 4))
    targets = sorted(by_addr)
    for i in range(0, len(targets), 4):
        chunk = targets[i:i + 4]
        live = len(chunk)
        while len(chunk) < 4:
            chunk = chunk + [chunk[-1]]
        srcm = Mem("lm0", 2, tuple(2 * (stage + by_addr[a][rep]) for a in chunk), tind=True)
        dstm = Mem(out.space, 2, tuple(2 * a for a in chunk))
        prog.add(VOp("lpassa", [srcm], dsts=[dstm], unit="alu", note="gather"))
    steps = [Step([ins]) for ins in up] + [Step(nop=3)] + [Step([ins]) for ins in down] + [Step(nop=3)]
    return steps + schedule(prog, assembler(), tries=1)
