"""Data movement: outputs that are copies of inputs stored elsewhere.

Movement is planned at long-word granularity, backwards from the destination.
Each transfer family (MV, L2BM and L1BM instructions) is an affine map between
buffer coordinates; given what the destination buffer must hold, the family's
inverse gives what the previous buffer must hold. Every applicable family is
tried at every hop and the cheapest complete chain is kept. At the source end
the requirement must match where the inputs are; when replicated inputs must
send different words from different PEs, a per-PE address offset is built in
the T register (indirect LM0 addressing).

Paths: DRAM -> L2BM -> L1BM -> PE and PE -> L1BM -> L2BM -> DRAM.
"""

from __future__ import annotations

import itertools
from collections import defaultdict
from dataclasses import dataclass, field

from .errors import CompileError
from .layout import Contract, TensorSpec, pe_coords
from .machine import Dram, Fixed, Imm, Instr, L1, L2, Mask, Mem, Pdm, Step

INF = float("inf")


# ---------------------------------------------------------------- requirements

def word_requirements(contract: Contract, outputs: dict):
    """dst word -> source word identity, and where each source word identity lives."""
    in_specs = {s.name: s for s in contract.inputs}
    req_lanes = defaultdict(dict)
    dst_space = None
    for spec in contract.outputs:
        for idx, node in outputs[spec.name].items():
            if node.op != "input":
                raise CompileError("movement: output is not a copy of an input element")
            loc = spec.locations(idx, replicate=False)[0]
            if in_specs[node.value[0]].dtype != spec.dtype:
                raise CompileError("movement: dtype change")
            req_lanes[(loc.pe, loc.addr)][loc.lane] = node.value
            dst_space = spec.space if dst_space in (None, spec.space) else "mixed"
    src_lanes = defaultdict(dict)
    src_space = None
    for spec in contract.inputs:
        for idx in spec.all_indices():
            for loc in spec.locations(idx, replicate=True):
                src_lanes[(loc.pe, loc.addr)][loc.lane] = (spec.name, idx)
        src_space = spec.space if src_space in (None, spec.space) else "mixed"
    if "mixed" in (dst_space, src_space):
        raise CompileError("movement: several memories on one side")
    src_map = {k: tuple(sorted(v.items())) for k, v in src_lanes.items()}
    req = {k: tuple(sorted(v.items())) for k, v in req_lanes.items()}
    return dst_space, src_space, req, src_map


def satisfies(have, need):
    hd = dict(have)
    return all(hd.get(l) == v for l, v in need)


class Where:
    """Lookup of source locations for a word identity (exact or lane-subset match)."""

    def __init__(self, src_map):
        self.exact = defaultdict(list)
        self.by_lane = defaultdict(set)
        for loc, eid in src_map.items():
            self.exact[eid].append(loc)
            for item in eid:
                self.by_lane[item].add(eid)
        self.cache = {}

    def __call__(self, eid):
        hit = self.cache.get(eid)
        if hit is not None:
            return hit
        if eid in self.exact:
            out = self.exact[eid]
        else:
            cands = None
            for item in eid:
                s = self.by_lane.get(item, set())
                cands = s if cands is None else cands & s
            out = [loc for c in (cands or ()) for loc in self.exact[c] if satisfies(c, eid)]
        self.cache[eid] = out
        return out


def put(req, key, eid):
    old = req.get(key)
    if old is not None and old != eid:
        raise CompileError("slot conflict")
    req[key] = eid


@dataclass
class Plan:
    cost: float
    hops: list = field(default_factory=list)  # list of instruction lists, program order


# ---------------------------------------------------------------- down: L1BM -> PE

def _pairs(addrs):
    return sorted({a // 2 * 2 for a in addrs})


def down_pe_families(req, space):
    """Yield (name, instrs, l1req) for PE <- L1BM."""
    by = defaultdict(dict)  # inst -> {(mab, p, addr): eid}
    for (pe, addr), eid in req.items():
        by[pe // 64][(pe % 64 // 4, pe % 4, addr)] = eid
    addrs = sorted({a for _, a in req})

    def mab_free():
        for r in by.values():
            seen = {}
            for (mab, p, a), e in r.items():
                if seen.setdefault((p, a), e) != e:
                    return False
        return True

    def pe_free():
        for r in by.values():
            seen = {}
            for (mab, p, a), e in r.items():
                if seen.setdefault(a, e) != e:
                    return False
        return True

    mf, pf = mab_free(), pe_free()
    if mf:
        for two in (True, False):
            try:
                yield ("l1bmm" + ("2" if two else "1"),) + _l1bmm_down(by, addrs, space, two)
            except CompileError:
                pass
    if mf and pf:
        for two in (True, False):
            try:
                yield ("l1bmp" + ("2" if two else "1"),) + _l1bmp_down(by, addrs, space, two)
            except CompileError:
                pass
    try:
        yield ("l1bmd",) + _l1bmd_down(by, addrs, space)
    except CompileError:
        pass


def _chunks(seq, n=4):
    out = []
    for i in range(0, len(seq), n):
        c = list(seq[i:i + n])
        while len(c) < n:
            c.append(c[-1])
        out.append(c)
    return out


def _live(seq, n=4):
    """Per chunk, how many leading cycles carry real (non-padding) addresses."""
    return [min(n, len(seq) - i) for i in range(0, len(seq), n)]


def _dst(space, wl, chunk, live):
    mask = None
    if live < 4:
        mask = Mask(pattern="1" * live + "0" * (4 - live), ll=(wl == 4))
    return Mem(space, wl, tuple(a * 2 for a in chunk), mask=mask)


def _l1bmm_down(by, addrs, space, two):
    instrs, l1 = [], {}
    units = _pairs(addrs) if two else addrs
    base = 0
    for chunk, live in zip(_chunks(units), _live(units)):
        wl = 4 if two else 2
        instrs.append(Instr("l1bmm", (L1(base, wl),), (_dst(space, wl, chunk, live),)))
        for c, a in enumerate(chunk[:live]):
            for k in range(2 if two else 1):
                for inst, r in by.items():
                    for p in range(4):
                        e = next((r[(m, p, a + k)] for m in range(16) if (m, p, a + k) in r), None)
                        if e is not None:
                            put(l1, (inst, base + (8 * c + 4 * k + p if two else 4 * c + p)), e)
        base += 32 if two else 16
    return instrs, l1


def _l1bmp_down(by, addrs, space, two):
    instrs, l1 = [], {}
    units = _pairs(addrs) if two else addrs
    base = 0
    for chunk, live in zip(_chunks(units), _live(units)):
        wl = 4 if two else 2
        instrs.append(Instr("l1bmp", (L1(base, wl),), (_dst(space, wl, chunk, live),)))
        for c, a in enumerate(chunk[:live]):
            for k in range(2 if two else 1):
                for inst, r in by.items():
                    e = next((v for (m, p, aa), v in r.items() if aa == a + k), None)
                    if e is not None:
                        put(l1, (inst, base + c + 4 * k), e)
        base += 8 if two else 4
    return instrs, l1


def _l1bmd_down(by, addrs, space):
    instrs, l1 = [], {}
    base = 0
    for chunk, live in zip(_chunks(addrs), _live(addrs)):
        instrs.append(Instr("l1bmd", (L1(base, 2),), (_dst(space, 2, chunk, live),)))
        for c, a in enumerate(chunk[:live]):
            for inst, r in by.items():
                for (m, p, aa), e in r.items():
                    if aa == a:
                        put(l1, (inst, base + 64 * c + 4 * m + p), e)
        base += 256
    return instrs, l1


# ---------------------------------------------------------------- down: L2BM -> L1BM

def down_l1_families(l1req):
    by = defaultdict(lambda: defaultdict(dict))  # l2b -> l1b -> {addr: eid}
    for (inst, a), e in l1req.items():
        by[inst // 8][inst % 8][a] = e
    top = max(a for _, a in l1req) + 1
    used_l1b = sorted({inst % 8 for inst, _ in l1req})
    same = True
    for per in by.values():
        merged = {}
        for r in per.values():
            for a, e in r.items():
                if merged.setdefault(a, e) != e:
                    same = False
    if same:
        instrs, l2 = [], {}
        l1set = _l1set(used_l1b)
        for b in range((top + 63) // 64):
            instrs.append(Instr("l2bmb" + (f"@{l1set}" if l1set else ""), (L2(64 * b),), (L1(64 * b, 2),)))
        for l2b, per in by.items():
            for r in per.values():
                for a, e in r.items():
                    put(l2, (l2b, a), e)
        yield "l2bmb", instrs, l2
    try:
        instrs, l2 = [], {}
        for b in range((top + 31) // 32):
            instrs.append(Instr("l2bmd", (L2(256 * b),), (L1(32 * b, 2),)))
        for l2b, per in by.items():
            for l1b, r in per.items():
                for a, e in r.items():
                    b, off = divmod(a, 32)
                    c, j = divmod(off, 8)
                    put(l2, (l2b, 256 * b + 64 * c + 8 * l1b + j), e)
        yield "l2bmd", instrs, l2
    except CompileError:
        pass


def down_l1_segmented(l1req, where: Where):
    """L1BM <- L2BM <- DRAM in segments: each source run gets its own 64-aligned L2BM block.

    For L1BM contents that are identical across the needed L1Bs. Copies are issued in
    ascending L1BM order; the tail each l2bmb writes beyond its segment is rewritten by
    the next one."""
    by = defaultdict(dict)
    for (inst, a), e in l1req.items():
        by[inst][a] = e
    insts = sorted(by)
    first = by[insts[0]]
    l2bs = sorted({i // 8 for i in insts})
    for inst in insts:
        for a, e in by[inst].items():
            if first.get(a, e) != e:
                raise CompileError("contents differ across L1Bs")
            first[a] = e
    l1bs = sorted({i % 8 for i in insts})
    segs = []
    for a in sorted(first):
        e = first[a]
        cands = where(e)
        if not cands:
            raise CompileError("word not in DRAM")
        if segs:
            s0, n, g0, d0 = segs[-1]
            if a - s0 < 64 and any(g == g0 and d - d0 == a - s0 for g, d in cands):
                segs[-1][1] = a - s0 + 1
                continue
        cands = sorted(cands, key=lambda gd: ((gd[1] - a) % 16 != 0, gd))
        g, d = cands[0]
        segs.append([a, 1, g, d])
    aligned = []
    for s0, n, g, d0 in segs:
        shift = max(s0 % 16, d0 % 16)
        if s0 % 16 != d0 % 16 or d0 - shift < 0:
            # shift both down to a common 16 boundary
            shift = s0 % 16
            if (d0 - shift) % 16 or d0 - shift < 0:
                raise CompileError("cannot align segment")
        aligned.append((s0 - shift, n + shift, g, d0 - shift))
    l1set = _l1set(l1bs)
    mv, l2 = [], []
    for k, (s0, n, g, d0) in enumerate(aligned):
        bc = 64 * k
        for l2b in l2bs:
            mv.append(Instr("mvp/n64", (Dram(d0, g),), (L2(bc, l2b=l2b % 2, group=l2b // 2),)))
        l2.append(Instr("l2bmb" + (f"@{l1set}" if l1set else ""), (L2(bc),), (L1(s0, 2),)))
    if len(l2bs) == 8 and len({(g, d0) for _, _, g, d0 in aligned}) == len(aligned):
        # same data for every L2B: one copy into PDM and a broadcast instead of eight copies
        pdm = []
        for k, (s0, n, g, d0) in enumerate(aligned):
            pdm.append(Instr("mvp/n64", (Dram(d0, g),), (Pdm(64 * k, g),)))
        gs = {g for _, _, g, _ in aligned}
        if len(gs) == 1:
            g = gs.pop()
            pdm.append(Instr(f"mvb/n{64 * len(aligned)}", (Pdm(0, g),), (L2(0),)))
            if len(pdm) < len(mv):
                mv = pdm
    return mv, l2


def _l1set(l1bs):
    """L1B subset syntax for a set of L1B numbers, or '' for all."""
    s = set(l1bs)
    if s == set(range(8)):
        return ""
    for immode in range(8):
        for b0 in range(8):
            m = 7 ^ immode
            members = {b for b in range(8) if b & m == b0 & m}
            if members == s:
                return f"{b0}/{immode}" if immode else f"{b0}"
    # a superset broadcast is harmless for unrequired L1Bs
    return ""


# ---------------------------------------------------------------- down: DRAM -> L2BM

def _runs_for(need: dict, where: Where, groups):
    """Cover needed L2BM addresses {a: eid} with runs (a0, length, src group, d0) copied from DRAM.

    A run maps a0 + i to DRAM d0 + i of one group; unneeded addresses inside a run are free.
    Copies are issued in ascending a0 and rounded up to 64 words, so tails overwritten by a
    copy are rewritten by the following ones."""
    runs = []
    for a in sorted(need):
        e = need[a]
        cands = [(g, d) for g, d in where(e) if g in groups]
        if not cands:
            return None
        if runs:
            a0, n, g0, d0 = runs[-1]
            if any(g == g0 and d - d0 == a - a0 for g, d in cands):
                runs[-1][1] = a - a0 + 1
                continue
        # start a new run: prefer a DRAM address aligned like the L2BM address
        cands.sort(key=lambda gd: ((gd[1] - a) % 16 != 0, gd))
        g, d = cands[0]
        runs.append([a, 1, g, d])
    out = []
    for a0, n, g, d0 in runs:
        # MV needs 64-aligned L2BM and 16-aligned DRAM addresses: extend the run downwards
        shift = a0 % 64
        if (d0 - shift) % 16 != 0 or d0 - shift < 0:
            return None
        out.append((a0 - shift, n + shift, g, d0 - shift))
    return out


def down_mv_families(l2req, where: Where):
    per = defaultdict(dict)  # l2b -> {a: eid}
    for (l2b, a), e in l2req.items():
        per[l2b][a] = e
    # parallel over groups: each column's runs are identical in every group
    try:
        instrs = []
        for c in (0, 1):
            cols = {l2b: need for l2b, need in per.items() if l2b % 2 == c}
            if not cols:
                continue
            plans = []
            for l2b, need in cols.items():
                runs = _runs_for(need, where, {l2b // 2})
                if runs is None:
                    raise CompileError("no runs")
                plans.append([(a0, n, d0) for a0, n, g, d0 in runs])
            # runs must agree on start/offset; take the union of lengths
            ref = plans[0]
            for pl in plans[1:]:
                if [(a, d) for a, _, d in pl] != [(a, d) for a, _, d in ref]:
                    raise CompileError("groups disagree")
            for i, (a0, n, d0) in enumerate(ref):
                n = max(pl[i][1] for pl in plans)
                instrs.append((c, a0, -(-n // 64) * 64, d0))
        # merge columns with identical copies into mvb2
        out = []
        seen = set()
        for c, a0, n, d0 in instrs:
            if (a0, n, d0) in seen:
                continue
            if (1 - c, a0, n, d0) in instrs:
                out.append(Instr(f"mvb2/n{n}", (Dram(d0),), (L2(a0),)))
                seen.add((a0, n, d0))
            else:
                out.append(Instr(f"mvp/n{n}", (Dram(d0),), (L2(a0, l2b=c),)))
        yield "mv-parallel", out, None
    except CompileError:
        pass
    # broadcast through PDM: every needed L2B wants the same content from one group
    try:
        contents = {l2b: need for l2b, need in per.items()}
        first = next(iter(contents.values()))
        if len(contents) > 1 and all(need == first for need in contents.values()):
            runs = None
            for g in range(4):
                runs = _runs_for(first, where, {g})
                if runs is not None:
                    break
            if runs is None:
                raise CompileError("no source group")
            out = []
            for a0, n, g, d0 in runs:
                n64 = -(-n // 64) * 64
                out.append(Instr(f"mvp/n{n64}", (Dram(d0, g),), (Pdm(a0, g),)))
            lo = min(r[0] for r in runs)
            hi = max(r[0] + -(-r[1] // 64) * 64 for r in runs)
            g = runs[0][2]
            out.append(Instr(f"mvb/n{hi - lo}", (Pdm(lo, g),), (L2(lo),)))
            yield "mv-pdm-broadcast", out, None
    except CompileError:
        pass
    # single transfers per L2B, sources from any group
    try:
        out = []
        for l2b, need in sorted(per.items()):
            runs = _runs_for(need, where, {l2b // 2}) or _runs_for(need, where, set(range(4)))
            if runs is None:
                raise CompileError("no runs")
            for a0, n, g, d0 in runs:
                out.append(Instr(f"mvp/n{-(-n // 64) * 64}", (Dram(d0, g),), (L2(a0, l2b=l2b % 2, group=l2b // 2),)))
        yield "mv-single", out, None
    except CompileError:
        pass


PLANS = 4  # cheapest plans kept: latencies decide the line count, not the instruction count


def _cheapest(plans):
    out, seen = [], set()
    for p in sorted(plans, key=lambda p: p.cost):
        key = tuple(tuple(i.text() if hasattr(i, "text") else repr(i) for i in hop) for hop in p.hops)
        if key not in seen:
            seen.add(key)
            out.append(p)
    return out[:PLANS]


def plan_down(req, src_map, space):
    where = Where(src_map)
    plans = []
    for pe_name, pe_instrs, l1req in down_pe_families(req, space):
        try:
            mv_instrs, l1_instrs = down_l1_segmented(l1req, where)
            plans.append(Plan(len(pe_instrs) + len(l1_instrs) + len(mv_instrs), [mv_instrs, l1_instrs, pe_instrs]))
        except CompileError:
            pass
        for l1_name, l1_instrs, l2req in down_l1_families(l1req):
            for mv_name, mv_instrs, _ in down_mv_families(l2req, where):
                plans.append(Plan(len(pe_instrs) + len(l1_instrs) + len(mv_instrs), [mv_instrs, l1_instrs, pe_instrs]))
    if not plans:
        raise CompileError("movement: no download chain")
    return _cheapest(plans)


# ---------------------------------------------------------------- up: PE -> L1BM -> L2BM -> DRAM

def up_mv_families(req, where: Where):
    """DRAM <- L2BM. Yields (name, instrs, l2req)."""
    # candidate source L2Bs per DRAM word
    src_l2b = {}
    for (g, d), e in req.items():
        locs = where(e)
        if not locs:
            raise CompileError("movement: output word not found in inputs")
        src_l2b[(g, d)] = sorted({pe // 512 for pe, _ in locs})
    # parallel: column c of every group supplies a contiguous DRAM range
    for prefer in (0, 1):
        try:
            col_of = {}
            for (g, d), l2bs in src_l2b.items():
                own = [l for l in l2bs if l // 2 == g]
                if not own:
                    raise CompileError("cross-group")
                cs = sorted({l % 2 for l in own}, key=lambda c: c != prefer)
                col_of[(g, d)] = cs[0]
            ranges = defaultdict(list)
            for (g, d), c in col_of.items():
                ranges[c].append(d)
            instrs, l2 = [], {}
            base_l2 = 0
            for c, ds in sorted(ranges.items()):
                lo, hi = min(ds), max(ds)
                lo64 = lo - lo % 64 if lo % 64 else lo
                n = (hi - lo64) // 64 * 64 + 64
                instrs.append(Instr(f"mvp/n{n}", (L2(base_l2, l2b=c),), (Dram(lo64),)))
                for (g, d), cc in col_of.items():
                    if cc == c:
                        put(l2, (2 * g + c, base_l2 + d - lo64), req[(g, d)])
            yield f"mv-parallel{prefer}", instrs, l2
        except CompileError:
            pass
    # per group singles from one L2B (handles outputs in group 0 fed by other groups)
    try:
        by_group = defaultdict(list)
        for (g, d), l2bs in src_l2b.items():
            by_group[g].append(d)
        instrs, l2 = [], {}
        base = 0
        for g, ds in sorted(by_group.items()):
            lo, hi = min(ds), max(ds)
            n = (hi - lo) // 64 * 64 + 64
            choices = set.intersection(*[set(src_l2b[(g, d)]) for d in ds])
            if not choices:
                raise CompileError("no common source L2B")
            l2b = min(choices, key=lambda l: (l // 2 != g, l))
            instrs.append(Instr(f"mvp/n{n}", (L2(base, l2b=l2b % 2, group=l2b // 2),), (Dram(lo, g),)))
            for d in ds:
                put(l2, (l2b, base + d - lo), req[(g, d)])
            base += n
        yield "mv-single", instrs, l2
    except CompileError:
        pass


def up_l2_families(l2req, where: Where):
    """L2BM <- L1BM. Yields (name, instrs, l1req)."""
    top = max(a for _, a in l2req) + 1
    # combine: L2BM[Bc + 64c + 8l + j] <- L1BM[l][Bb + 8c + j]
    try:
        l1 = {}
        instrs = []
        for b in range((top + 255) // 256):
            instrs.append(Instr("l2bmd", (L1(32 * b, 2),), (L2(256 * b),)))
        for (l2b, a), e in l2req.items():
            b, off = divmod(a, 256)
            c, rest = divmod(off, 64)
            l1b, j = divmod(rest, 8)
            inst = l2b * 8 + l1b
            if not any(pe // 64 == inst for pe, _ in where(e)):
                raise CompileError("word not in that L1B")
            put(l1, (inst, 32 * b + 8 * c + j), e)
        yield "l2bmd", instrs, l1
    except CompileError:
        pass
    # individual: L2BM[Bc + 16c + j] <- L1BM[l][Bb + 16c + j], one L1B per 64-block
    try:
        l1 = {}
        instrs = []
        blocks = defaultdict(dict)
        for (l2b, a), e in l2req.items():
            blocks[a // 64][(l2b, a % 64)] = e
        for blk, need in sorted(blocks.items()):
            choice = None
            for (l2b, off), e in need.items():
                cands = {pe // 64 % 8 for pe, _ in where(e) if pe // 512 == l2b}
                choice = cands if choice is None else choice & cands
            if not choice:
                raise CompileError("no single L1B holds the block")
            l1b = min(choice)
            instrs.append(Instr(f"l2bm@{l1b}", (L1(64 * blk, 2),), (L2(64 * blk),)))
            for (l2b, off), e in need.items():
                put(l1, (l2b * 8 + l1b, 64 * blk + off), e)
        yield "l2bm@", instrs, l1
    except CompileError:
        pass


def up_pe_families(l1req, where: Where, src_space):
    """L1BM <- PE. Yields (name, instrs) with any T setup included."""
    # l1bmm@<mab>, two long words per PE per cycle; offset = 8c + 4k + p within 32-blocks
    for two in (True, False):
        size = 32 if two else 16
        try:
            yield ("l1bmm@" + ("2" if two else "1"),) + _up_l1bmm(l1req, where, src_space, two, size)
        except CompileError:
            pass
    try:
        yield ("l1bmd",) + _up_l1bmd(l1req, where, src_space)
    except CompileError:
        try:
            yield ("l1bmd-t",) + _up_l1bmd_offset(l1req, where, src_space)
        except CompileError:
            pass


def _offsets_needed(choices):
    """choices: list of (pe key, set of candidate addresses). Pick a per-cycle base and per-PE offsets."""
    return None


def _up_l1bmm(l1req, where, src_space, two, size):
    blocks = defaultdict(dict)
    for (inst, a), e in l1req.items():
        blocks[a // size][(inst, a % size)] = e
    plain = []
    offset_plan = []
    for blk, need in sorted(blocks.items()):
        per_cycle = defaultdict(lambda: None)
        mabs = None
        cand_by_slot = {}
        for (inst, off), e in need.items():
            c, rest = divmod(off, 8 if two else 4)
            k, p = divmod(rest, 4) if two else (0, rest)
            locs = [(pe, a) for pe, a in where(e) if pe // 64 == inst and pe % 4 == p]
            if not locs:
                raise CompileError("slot cannot be fed from its L1B")
            ms = {pe % 64 // 4 for pe, _ in locs}
            mabs = ms if mabs is None else mabs & ms
            cand_by_slot[(inst, c, k, p)] = {a - k for pe, a in locs}
        if not mabs:
            raise CompileError("no common MAB")
        mab = min(mabs)
        # without per-PE offsets every PE of every L1B reads the same address in a cycle
        cycles = []
        for c in range(4):
            sets = [s for (inst, cc, k, p), s in cand_by_slot.items() if cc == c]
            common = set.intersection(*sets) if sets else {0}
            cycles.append(common)
        if all(cycles):
            addrs = [min(s) for s in cycles]
            if two and any(a % 2 for a in addrs):
                raise CompileError("unaligned pair")
            plain.append((blk, mab, addrs))
            continue
        # per-PE offset o(p, l1b) with address = A_c + o: try o = alpha * p
        found = None
        for alpha in (1, 2, -1, 4, 8):
            ok_cycles = []
            for c in range(4):
                sets = [{a - alpha * p for a in s} for (inst, cc, k, p), s in cand_by_slot.items() if cc == c]
                common = set.intersection(*sets) if sets else {0}
                if not common:
                    break
                ok_cycles.append(min(common))
            else:
                found = (alpha, ok_cycles)
                break
        if found is None:
            raise CompileError("no uniform per-PE offset")
        offset_plan.append((blk, mab, found))
    instrs = []
    wl = 4 if two else 2
    alphas = {f[0] for _, _, f in offset_plan}
    if len(alphas) > 1 or (offset_plan and src_space != "lm0"):
        raise CompileError("per-PE offsets need one stride and an LM0 source")
    if offset_plan:
        alpha = alphas.pop()
        # T = alpha * subpeid long words = 2 * alpha * subpeid words
        instrs += _t_from_subpeid(2 * alpha)
    for blk, mab, addrs in plain:
        instrs.append(Instr(f"l1bmm@{mab}", (Mem(src_space, wl, tuple(a * 2 for a in addrs)),), (L1(size * blk, wl),)))
    for blk, mab, (alpha, addrs) in offset_plan:
        if any(a < 0 for a in addrs):
            raise CompileError("negative base address")
        instrs.append(Instr(f"l1bmm@{mab}", (Mem(src_space, wl, tuple(a * 2 for a in addrs), tind=True),), (L1(size * blk, wl),)))
    return (instrs,)


def _t_from_subpeid(scale):
    """ALU ops leaving scale * subpeid (words) in every cycle of T."""
    if scale == 2:
        return [Instr("ipackbit", (Fixed("subpeid"), Mem("grf1", 2, (480,) * 4)), (Mem("t", 4),))]
    raise CompileError(f"T offset scale {scale} not implemented")


def _up_l1bmd(l1req, where, src_space):
    blocks = defaultdict(dict)
    for (inst, a), e in l1req.items():
        blocks[a // 256][(inst, a % 256)] = e
    instrs = []
    for blk, need in sorted(blocks.items()):
        cycles = [None] * 4
        for (inst, off), e in need.items():
            c, rest = divmod(off, 64)
            mab, p = divmod(rest, 4)
            pe = inst * 64 + mab * 4 + p
            s = {a for q, a in where(e) if q == pe}
            if not s:
                raise CompileError("word not in that PE")
            cycles[c] = s if cycles[c] is None else cycles[c] & s
            if not cycles[c]:
                raise CompileError("PEs disagree on the address")
        addrs = [min(s) if s else 0 for s in cycles]
        instrs.append(Instr("l1bmd", (Mem(src_space, 2, tuple(a * 2 for a in addrs)),), (L1(256 * blk, 2),)))
    return (instrs,)


def _up_l1bmd_offset(l1req, where, src_space):
    """l1bmd where every PE reads its own address: base per cycle + a per-PE offset that is a
    bit-linear function of the PE coordinates, added by T-indirect addressing (LM0 only)."""
    from .generate import bitlinear_value, fit_bits
    from .schedule import schedule
    from .select import Constants
    from .sim import assembler
    from .vprog import VProgram

    if src_space != "lm0":
        raise CompileError("T-indirect reads are LM0 only")
    blocks = defaultdict(dict)
    for (inst, a), e in l1req.items():
        blocks[a // 256][(inst, a % 256)] = e
    base = {}
    delta = {}
    for blk, need in sorted(blocks.items()):
        for (inst, off), e in sorted(need.items()):
            c, rest = divmod(off, 64)
            mab, p = divmod(rest, 4)
            pe = inst * 64 + mab * 4 + p
            s = sorted({a for q, a in where(e) if q == pe})
            if not s:
                raise CompileError("word not in that PE")
            a = s[0]
            if (blk, c) not in base:
                base[(blk, c)] = a - delta.get(pe, 0) if pe in delta else a
                delta.setdefault(pe, 0)
            d = a - base[(blk, c)]
            if delta.setdefault(pe, d) != d:
                raise CompileError("per-PE offsets differ between cycles")
    coef = fit_bits([(pe, 0, (2 * d) % (1 << 32)) for pe, d in delta.items()])
    if coef is None:
        raise CompileError("per-PE offset is not linear in the coordinate bits")
    prog = VProgram()
    bitlinear_value(prog, Constants(prog), coef[0], 0, coef[2:], dst=Mem("t", 4))
    instrs = [i for st in schedule(prog, assembler(), tries=1) for i in st.instrs]
    for blk in sorted(blocks):
        addrs = [base.get((blk, c), base.get((blk, 0), 0)) for c in range(4)]
        if any(a < 0 for a in addrs):
            raise CompileError("negative base address")
        instrs.append(Instr("l1bmd", (Mem(src_space, 2, tuple(a * 2 for a in addrs), tind=True),), (L1(256 * blk, 2),)))
    return (instrs,)


def plan_up(req, src_map, src_space):
    where = Where(src_map)
    plans = []
    for mv_name, mv_instrs, l2req in up_mv_families(req, where):
        for l2_name, l2_instrs, l1req in up_l2_families(l2req, where):
            for pe_name, pe_instrs in up_pe_families(l1req, where, src_space):
                plans.append(Plan(len(mv_instrs) + len(l2_instrs) + len(pe_instrs), [pe_instrs, l2_instrs, mv_instrs]))
    if not plans:
        raise CompileError("movement: no upload chain")
    return _cheapest(plans)


# ---------------------------------------------------------------- driver

def sequence(plan: Plan) -> list[Step]:
    steps = []
    for i, hop in enumerate(plan.hops):
        if not hop:
            continue
        if steps:
            steps.append(Step(nop=3))
        for ins in hop:
            steps.append(Step([ins]))
    return steps


def movement_steps(contract: Contract, outputs: dict):
    dst_space, src_space, req, src_map = word_requirements(contract, outputs)
    if src_space == "dram" and dst_space in ("lm0", "lm1"):
        return [(f"plan{k}", sequence(p)) for k, p in enumerate(plan_down(req, src_map, dst_space))]
    if src_space in ("lm0", "lm1") and dst_space == "dram":
        return [(f"plan{k}", sequence(p)) for k, p in enumerate(plan_up(req, src_map, src_space))]
    raise CompileError(f"movement: path {src_space} -> {dst_space} not implemented")
