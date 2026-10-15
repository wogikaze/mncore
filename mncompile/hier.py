"""Reductions across the hierarchy: per-MAB partials reduced by L1BM/L2BM/MV transfers.

An output element reduce(op, terms) whose terms live in different MABs, L1Bs
or L2Bs is computed in two phases:

A. every MAB computes the partial reduction of the terms it holds with a
   PE-level strategy (local maps, local reductions, PE-group reductions) into
   a scratch LM region, at the words the transfer chain reads;
B. the partials travel to the destination through the transfer hierarchy and
   are reduced on the way where several units contribute: PE -> L1BM (l1bmr
   over the 16 MABs, or a copy from one MAB), L1BM -> L2BM (l2bmr over a set of
   L1Bs, or a copy), L2BM -> DRAM (mvr over all L2Bs, mvr2 over the two L2Bs of
   a group, or a copy). An LM destination is reached back down from the L1BM.

Like plain movement, the chain is planned backwards from the destination words;
every applicable family is tried at every hop and the shortest chain is kept.
"""

from __future__ import annotations

from collections import defaultdict

from .errors import CompileError
from .ir import walk
from .layout import Loc
from .machine import Dram, Instr, L1, L2, Mem, Pdm, Step
from .movement import down_pe_families

REDUCE = {"sum", "max", "min", "lor", "land"}


def rrn_opcode(op, dtype):
    if dtype.is_float:
        p = {64: "d", 32: "f", 16: "h"}[dtype.bits]
        table = {"sum": p + "fadd", "max": p + "max", "min": p + "min"}
    else:
        p = {64: "l", 32: "i", 16: "s"}[dtype.bits]
        table = {"sum": p + "iadd", "lor": p + "or", "land": p + "and"}
    if op not in table:
        raise CompileError(f"hierarchy: no transfer reduction for {op} on {dtype}")
    return table[op]


def _l1set(l1bs):
    l1bs = sorted(l1bs)
    if l1bs == list(range(8)):
        return ""
    return "@[" + ",".join(map(str, l1bs)) + "]"


def _split(eid, unit_of):
    """Split every lane's MAB set by unit: {unit: eid restricted to that unit}."""
    out = defaultdict(dict)
    for lane, (o, mabs) in eid:
        by = defaultdict(set)
        for m in mabs:
            by[unit_of(m)].add(m)
        for u, ms in by.items():
            out[u][lane] = (o, frozenset(ms))
    return {u: tuple(sorted(v.items())) for u, v in out.items()}


def _units(eid, unit_of):
    s = None
    for _lane, (_o, mabs) in eid:
        u = {unit_of(m) for m in mabs}
        s = u if s is None else s
        if u != s:
            return None  # lanes spread differently: a reduction would mix them
    return s


def _put(req, key, eid):
    old = req.get(key)
    if old is not None and old != eid:
        raise CompileError("slot conflict")
    req[key] = eid


L2B_OF = lambda m: m // 128  # noqa: E731  (MAB instance -> L2B)
L1I_OF = lambda m: m // 16  # noqa: E731  (MAB instance -> L1B instance)


# ---------------------------------------------------------------- DRAM <- L2BM

def up_mv(req, rr):
    words = sorted(req)
    # copies: every DRAM word from one L2B (parallel over groups, or one instruction per group)
    for prefer in (0, 1):
        try:
            col = {}
            for (g, d) in words:
                u = _units(req[(g, d)], L2B_OF)
                if u is None or len(u) != 1:
                    raise CompileError("several L2Bs")
                l2b = next(iter(u))
                if l2b // 2 != g:
                    raise CompileError("cross-group")
                col[(g, d)] = l2b % 2
            ranges = defaultdict(list)
            for k, c in col.items():
                ranges[c].append(k[1])
            instrs, l2 = [], {}
            for c, ds in sorted(ranges.items()):
                lo = min(ds) // 64 * 64
                n = (max(ds) - lo) // 64 * 64 + 64
                instrs.append(Instr(f"mvp/n{n}", (L2(0, l2b=c),), (Dram(lo),)))
                for (g, d), cc in col.items():
                    if cc == c:
                        _put(l2, (2 * g + c, d - lo), req[(g, d)])
            yield "mvp", instrs, l2
            break
        except CompileError:
            pass
    # reduction over all eight L2Bs, distributed 16 long words per group
    try:
        lo = min(d for _, d in words) // 16 * 16
        l2 = {}
        top = 0
        for (g, d) in words:
            i, k = divmod(d - lo, 16)
            parts = _split(req[(g, d)], L2B_OF)
            if len(parts) != 8:
                raise CompileError("mvr needs every L2B")
            for l2b, e in parts.items():
                _put(l2, (l2b, 64 * i + 16 * g + k), e)
            top = max(top, i + 1)
        yield "mvr", [Instr(f"mvr{rr}/n{64 * top}", (L2(0),), (Dram(lo),))], l2
    except CompileError:
        pass
    # reduction over all eight L2Bs into one PDM, then a copy to each group's DRAM
    try:
        by_group = defaultdict(list)
        for (g, d) in words:
            by_group[g].append(d)
        chunk = {}
        span = max((max(ds) - min(ds) // 64 * 64) // 64 * 64 + 64 for ds in by_group.values())
        l2 = {}
        instrs = []
        for k, (g, ds) in enumerate(sorted(by_group.items())):
            lo = min(ds) // 64 * 64
            n = (max(ds) - lo) // 64 * 64 + 64
            chunk[g] = (k * span, lo, n)
            for d in ds:
                parts = _split(req[(g, d)], L2B_OF)
                if len(parts) != 8:
                    raise CompileError("PDM reduction needs every L2B")
                for l2b, e in parts.items():
                    _put(l2, (l2b, k * span + d - lo), e)
        total = len(by_group) * span
        instrs.append(Instr(f"mvr{rr}/n{total}", (L2(0),), (Pdm(0, 0),)))
        for g, (base, lo, n) in sorted(chunk.items()):
            instrs.append(Instr(f"mvp/n{n}", (Pdm(base, 0),), (Dram(lo, g),)))
        yield "mvr-pdm", instrs, l2
    except CompileError:
        pass
    # reduction over the two L2Bs of each group
    try:
        lo = min(d for _, d in words) // 64 * 64
        l2 = {}
        top = 0
        for (g, d) in words:
            parts = _split(req[(g, d)], L2B_OF)
            if set(parts) != {2 * g, 2 * g + 1}:
                raise CompileError("mvr2 needs both L2Bs of the group")
            for l2b, e in parts.items():
                _put(l2, (l2b, d - lo), e)
            top = max(top, d - lo + 1)
        n = (top + 63) // 64 * 64
        yield "mvr2", [Instr(f"mvr2{rr}/n{n}", (L2(0),), (Dram(lo),))], l2
    except CompileError:
        pass


# ---------------------------------------------------------------- L2BM <- L1BM

def up_l2(l2req, rr):
    top = max(a for _, a in l2req) + 1
    # copy from one L1B per 64-long-word block
    try:
        blocks = defaultdict(dict)
        for (l2b, a), e in l2req.items():
            blocks[a // 64][(l2b, a)] = e
        instrs, l1 = [], {}
        for blk, need in sorted(blocks.items()):
            common = None
            for (l2b, a), e in need.items():
                u = _units(e, L1I_OF)
                if u is None or len(u) != 1:
                    raise CompileError("several L1Bs")
                inst = next(iter(u))
                common = {inst % 8} if common is None else common & {inst % 8}
            if not common:
                raise CompileError("no common L1B")
            l1b = min(common)
            instrs.append(Instr(f"l2bm@{l1b}", (L1(64 * blk, 2),), (L2(64 * blk),)))
            for (l2b, a), e in need.items():
                _put(l1, (l2b * 8 + l1b, a), e)
        yield "l2bm@", instrs, l1
    except CompileError:
        pass
    # combine: L2BM[256b + 64c + 8l + j] <- L1BM[l][32b + 8c + j]
    try:
        instrs, l1 = [], {}
        for b in range((top + 255) // 256):
            instrs.append(Instr("l2bmd", (L1(32 * b, 2),), (L2(256 * b),)))
        for (l2b, a), e in l2req.items():
            b, off = divmod(a, 256)
            c, rest = divmod(off, 64)
            l1b, j = divmod(rest, 8)
            u = _units(e, L1I_OF)
            if u != {l2b * 8 + l1b}:
                raise CompileError("word not in that L1B")
            _put(l1, (l2b * 8 + l1b, 32 * b + 8 * c + j), e)
        yield "l2bmd", instrs, l1
    except CompileError:
        pass
    # reduction over a set of L1Bs (same addresses)
    try:
        l1 = {}
        sets = set()
        for (l2b, a), e in l2req.items():
            parts = _split(e, L1I_OF)
            sets.add(frozenset(inst % 8 for inst in parts))
            for inst, pe in parts.items():
                _put(l1, (inst, a), pe)
        if len(sets) != 1:
            raise CompileError("words reduce over different L1B sets")
        l1bs = next(iter(sets))
        instrs = [Instr(f"l2bmr{rr}{_l1set(l1bs)}", (L1(64 * b, 2),), (L2(64 * b),)) for b in range((top + 63) // 64)]
        yield "l2bmr", instrs, l1
    except CompileError:
        pass


# ---------------------------------------------------------------- L1BM <- PE (partials)

def up_l1(l1req, rr, base, space, two_ok):
    """Yield (name, instrs, mabreq) with mabreq {(pe, long addr): eid}; partials live from `base` on."""
    top = max(a for _, a in l1req) + 1
    # combine: L1BM[256blk + 64c + 4mab + p] <- PE(mab, p)[src_c] (every MAB, one address per cycle)
    try:
        mreq = {}
        for (inst, a), e in l1req.items():
            blk, off = divmod(a, 256)
            c, rest = divmod(off, 64)
            mab, p = divmod(rest, 4)
            u = _units(e, lambda m: m)
            if u != {inst * 16 + mab}:
                raise CompileError("word not in that MAB")
            _put(mreq, ((inst * 16 + mab) * 4 + p, base + 4 * blk + c), e)
        instrs = [Instr("l1bmd", (Mem(space, 2, tuple(2 * (base + 4 * blk + c) for c in range(4))),), (L1(256 * blk, 2),))
                  for blk in range((top + 255) // 256)]
        yield "l1bmd", instrs, mreq
    except CompileError:
        pass
    for two in ((True, False) if two_ok else (False,)):
        size = 32 if two else 16
        wl = 4 if two else 2

        def pe_addr(a):
            return base + (2 * (a // 8) + (a // 4) % 2 if two else a // 4)

        # copy from one MAB per block
        try:
            blocks = defaultdict(dict)
            for (inst, a), e in l1req.items():
                blocks[a // size][(inst, a)] = e
            instrs, mreq = [], {}
            for blk, need in sorted(blocks.items()):
                common = None
                for (inst, a), e in need.items():
                    u = _units(e, lambda m: m)
                    if u is None or len(u) != 1:
                        raise CompileError("several MABs")
                    m = next(iter(u))
                    if m // 16 != inst:
                        raise CompileError("MAB outside the L1B")
                    common = {m % 16} if common is None else common & {m % 16}
                if not common:
                    raise CompileError("no common MAB")
                mab = min(common)
                first = pe_addr(blk * size)
                addrs = tuple(2 * (first + (2 if two else 1) * c) for c in range(4))
                instrs.append(Instr(f"l1bmm@{mab}", (Mem(space, wl, addrs),), (L1(size * blk, wl),)))
                for (inst, a), e in need.items():
                    _put(mreq, ((inst * 16 + mab) * 4 + a % 4, pe_addr(a)), e)
            yield f"l1bmm@{size}", instrs, mreq
        except CompileError:
            pass
        # reduction over the 16 MABs of each L1B
        if two and not (rr.endswith("fadd") and rr[0] == "f" or rr.endswith("bor")):
            continue
        try:
            mreq = {}
            for (inst, a), e in l1req.items():
                parts = _split(e, lambda m: m)
                if len(parts) != 16:
                    raise CompileError("l1bmr needs every MAB")
                for m, pe in parts.items():
                    _put(mreq, (m * 4 + a % 4, pe_addr(a)), pe)
            instrs = []
            for blk in range((top + size - 1) // size):
                first = pe_addr(blk * size)
                addrs = tuple(2 * (first + (2 if two else 1) * c) for c in range(4))
                instrs.append(Instr(f"l1bmr{rr}", (Mem(space, wl, addrs),), (L1(size * blk, wl),)))
            yield f"l1bmr{size}", instrs, mreq
        except CompileError:
            pass


# ---------------------------------------------------------------- planning

class ExplicitSpec:
    """An LM tensor given by explicit locations (quacks like TensorSpec for PE-level strategies)."""

    def __init__(self, name, dtype, space, locs: dict, atol=0.0):
        self.name, self.dtype, self.space, self.atol = name, dtype, space, atol
        self._locs = locs
        addrs = [l.addr for l in locs.values()]
        self.start, self.end = 2 * min(addrs), 2 * (max(addrs) + 1)
        self.low = self.high = None
        self.group, self.domain, self.allow_inf, self.layout = 0, None, False, None

    def locations(self, idx, *, replicate):
        return [self._locs[idx]]

    def all_indices(self):
        return list(self._locs)


def _scratch(contract):
    """A free LM region (space, first long word) for the partials."""
    used = defaultdict(int)
    for s in list(contract.inputs) + list(contract.outputs):
        if s.space in ("lm0", "lm1"):
            used[s.space] = max(used[s.space], s.end)
    space = min(("lm1", "lm0"), key=lambda sp: used[sp])
    return space, (used[space] // 2 + 7) // 8 * 8


def _coord(m, axis):
    return {"L2B": m // 128, "L1B": m // 16 % 8, "MAB": m % 16}[axis]


def analyze_reductions(contract, outputs, spread=None):
    if len(contract.outputs) != 1:
        raise CompileError("hierarchy: one output")
    out = contract.outputs[0]
    if any(s.space == "dram" for s in contract.inputs):
        raise CompileError("hierarchy: DRAM input")
    specs = {s.name: s for s in contract.inputs}
    leaf_mabs = {}

    def mabs_of(term):
        sets = []
        for n in walk([term]):
            if n.op == "input":
                s = leaf_mabs.get(n.value)
                if s is None:
                    s = frozenset(l.pe // 4 for l in specs[n.value[0]].locations(n.value[1], replicate=True))
                    leaf_mabs[n.value] = s
                sets.append(s)
        return frozenset.intersection(*sets) if sets else None

    op = None
    parts = {}
    budget = [0]
    for idx, node in outputs[out.name].items():
        if node.op == "toint" and node.args[0].op in ("lor", "land") and out.dtype.kind != "float":
            node = node.args[0]  # 0/1 partials reduce with the transfers' logical or/and
        if node.op not in REDUCE or len(node.args) < 2:
            raise CompileError("hierarchy: output is not a reduction")
        if op not in (None, node.op):
            raise CompileError("hierarchy: mixed reductions")
        op = node.op
        per = defaultdict(list)
        if spread:
            # terms held by every replica unit: split them into equal blocks over the units
            sets = [mabs_of(t) for t in node.args]
            if not all(sets):
                raise CompileError("hierarchy: a term's operands are not in one MAB")
            common = frozenset.intersection(*sets)
            if not common:
                raise CompileError("hierarchy: terms have no common units to split over")
            base = min(common)
            units = sorted(m for m in common if all(_coord(m, ax) == _coord(base, ax) for ax in ("L2B", "L1B", "MAB") if ax not in spread))
            n = len(node.args)
            r = len(units)
            while r > 1 and n % r:
                r -= 1
            if r < 2:
                raise CompileError("hierarchy: nothing to split")
            units = units[:r]
            budget[0] += r
            if budget[0] > 65536:
                raise CompileError("hierarchy: too many partials to split")
            for k, t in enumerate(node.args):
                per[units[k * r // n]].append(t)
        else:
            for t in node.args:
                ms = mabs_of(t)
                if not ms:
                    raise CompileError("hierarchy: a term's operands are not in one MAB")
                per[min(ms)].append(t)
        parts[(out.name, idx)] = per
    if all(len(p) == 1 for p in parts.values()):
        raise CompileError("hierarchy: every output reduces within one MAB")
    return out, op, parts


def plan(contract, outputs, spread=None):
    out, op, parts = analyze_reductions(contract, outputs, spread)
    space, chains = plan_chains(contract, out, op, parts)
    return out, op, parts, space, chains


def _pdm_round_trip(l2req, rr):
    """L2BM <- PDM (mvb broadcast to all L2Bs) <- PDM (mvr reduce over all L2Bs): the reduction across
    L2Bs for an LM destination. Yields (instrs, l2req of the partials)."""
    try:
        addrs = sorted({a for _, a in l2req})
        by_addr = {}
        for (l2b, a), e in l2req.items():
            if by_addr.setdefault(a, e) != e:
                raise CompileError("L2Bs need different words at one address")
        lo = addrs[0] // 64 * 64
        n = (addrs[-1] - lo) // 64 * 64 + 64
        up = {}
        for a, e in by_addr.items():
            parts = _split(e, L2B_OF)
            if len(parts) != 8:
                raise CompileError("PDM reduction needs every L2B")
            for l2b, pe in parts.items():
                _put(up, (l2b, a), pe)
        instrs = [Instr(f"mvr{rr}/n{n}", (L2(lo),), (Pdm(lo, 0),)), Instr(f"mvb/n{n}", (Pdm(lo, 0),), (L2(lo),))]
        yield instrs, up
    except CompileError:
        return


def plan_chains(contract, out, op, parts):
    rr = rrn_opcode(op, out.dtype)
    req = defaultdict(dict)
    for (name, idx), per in parts.items():
        loc = out.locations(idx, replicate=False)[0]
        req[(loc.pe, loc.addr)][loc.lane] = ((name, idx), frozenset(per))
    req = {k: tuple(sorted(v.items())) for k, v in req.items()}
    space, base = _scratch(contract)
    two_ok = True
    chains = []
    if out.space == "dram":
        for mv_name, mv, l2req in up_mv(req, rr):
            for l2_name, l2, l1req in up_l2(l2req, rr):
                for l1_name, l1, mreq in up_l1(l1req, rr, base, space, two_ok):
                    chains.append((len(mv) + len(l2) + len(l1), f"{l1_name}/{l2_name}/{mv_name}", [l1, l2, mv], mreq))
    else:
        from .movement import down_l1_families

        for d_name, down, l1req in down_pe_families(req, out.space):
            for l1_name, l1, mreq in up_l1(l1req, rr, base, space, two_ok):
                chains.append((len(down) + len(l1), f"{l1_name}/{d_name}", [l1, down], mreq))
            # through the L2BM: reduce over L1Bs on the way up, broadcast or distribute back down
            for b_name, bdown, l2req in down_l1_families(l1req):
                for l2_name, l2, l1req2 in up_l2(l2req, rr):
                    for l1_name, l1, mreq in up_l1(l1req2, rr, base, space, two_ok):
                        chains.append((len(down) + len(bdown) + len(l2) + len(l1), f"{l1_name}/{l2_name}/{b_name}/{d_name}", [l1, l2, bdown, down], mreq))
                # across L2Bs as well: reduce into the PDM and broadcast back to every L2BM
                for mv, l2req_up in _pdm_round_trip(l2req, rr):
                    for l2_name, l2, l1req2 in up_l2(l2req_up, rr):
                        for l1_name, l1, mreq in up_l1(l1req2, rr, base, space, two_ok):
                            chains.append((len(down) + len(bdown) + len(mv) + len(l2) + len(l1), f"{l1_name}/{l2_name}/pdm/{b_name}/{d_name}", [l1, l2, mv, bdown, down], mreq))
    if not chains:
        raise CompileError("hierarchy: no transfer chain")
    chains.sort(key=lambda c: c[0])
    return space, chains


# ---------------------------------------------------------------- structured partials (for layout-based strategies)

HIER = ("L2B", "L1B", "MAB")


def _digits(k, dims):
    out = []
    for d in reversed(dims):
        k, r = divmod(k, d.size)
        out.append(r)
    return out[::-1]


def _number(digits, dims):
    v = 0
    for r, d in zip(digits, dims):
        v = v * d.size + r
    return v


def split_mixed(spec, name=None):
    """Reinterpret `spec` with every axis mixing hierarchy and local dims split into
    (hierarchy part, local part). Returns (new spec, index remap, {old axis: (hier axis, local axis)})."""
    from dataclasses import replace as dc_replace

    from .layout import Layout

    axes, plan_ = [], []
    where = {}
    for a, dims in enumerate(spec.layout.axes):
        hier_pos = [i for i, d in enumerate(dims) if d.axis in HIER]
        local_pos = [i for i, d in enumerate(dims) if d.axis not in HIER]
        if hier_pos and local_pos:
            where[a] = (len(axes), len(axes) + 1)
            axes += [tuple(dims[i] for i in hier_pos), tuple(dims[i] for i in local_pos)]
            plan_.append((a, dims, hier_pos, local_pos))
        else:
            where[a] = (len(axes), None) if hier_pos else (None, len(axes))
            axes.append(dims)
            plan_.append((a, dims, None, None))
    new = dc_replace(spec, name=name or spec.name + "~", layout=Layout(tuple(axes), spec.layout.broadcast, None))

    def remap(idx):
        out = []
        for (a, dims, hp, lp) in plan_:
            if hp is None:
                out.append(idx[a])
                continue
            dg = _digits(idx[a], dims)
            out.append(_number([dg[i] for i in hp], [dims[i] for i in hp]))
            out.append(_number([dg[i] for i in lp], [dims[i] for i in lp]))
        return tuple(out)

    return new, remap, where


def infer_layout(shape, loc_of):
    """Layout (dims per logical axis) reproducing loc_of(index) -> Loc, or CompileError."""
    import itertools

    from .layout import Dim, Layout, pe_coords

    def coords(idx):
        loc = loc_of(idx)
        if loc is None:
            raise CompileError("hierarchy: partial without a location")
        c = dict(pe_coords(loc.pe))
        c[""] = loc.addr
        c["W"] = loc.lane
        return c

    n = len(shape)
    zero = (0,) * n
    origin = coords(zero)
    if any(origin[a] for a in (*HIER, "PE", "W")):
        raise CompileError("hierarchy: partials do not start at the first PE")
    axes = []
    for ax in range(n):
        dims = []
        block = 1
        while block < shape[ax]:
            idx = list(zero)
            idx[ax] = block
            delta = {k: v - origin[k] for k, v in coords(tuple(idx)).items() if v != origin[k]}
            if len(delta) != 1:
                raise CompileError("hierarchy: partial layout is not separable")
            (hw, stride), = delta.items()
            if stride <= 0:
                raise CompileError("hierarchy: negative stride")
            run = 1
            while block * (run + 1) <= shape[ax] - 0 and shape[ax] % block == 0:
                idx[ax] = block * run
                c = coords(tuple(idx)) if block * run < shape[ax] else None
                if c is None or c[hw] - origin[hw] != stride * run or any(c[k] != origin[k] for k in c if k != hw):
                    break
                run += 1
            rest = shape[ax] // block
            s = max(d for d in range(1, rest + 1) if rest % d == 0 and d <= run)
            if s == 1:
                raise CompileError("hierarchy: partial layout is not mixed-radix")
            dims.insert(0, Dim(s, hw, stride))
            block *= s
        axes.append(tuple(dims) or (Dim(1, "", 1),))
    layout = Layout(tuple(axes), (), None)
    # verify on a sample of indices
    total = 1
    for k in shape:
        total *= k
    step = max(1, total // 4096)
    for i, idx in enumerate(itertools.product(*(range(k) for k in shape))):
        if i % step:
            continue
        want = coords(idx)
        got = dict(origin)
        for a, d_axis in zip(idx, layout.axes):
            for r, d in zip(_digits(a, d_axis), d_axis):
                got[d.axis] += r * d.stride
        if want != got:
            raise CompileError("hierarchy: inferred partial layout does not match")
    return layout, origin[""]


def _unit_index(term, split, specs, hier_axes, rebuild):
    """Hierarchy unit index of one term (from its first input leaf, without rebuilding the term)."""
    for n in walk([term]):
        if n.op == "input":
            new, remap, _w = split[n.value[0]]
            return remap(n.value[1])[hier_axes[new.name]]
    raise CompileError("hierarchy: constant term")


def structured_partials(graph, contract, out, op, parts, mreq, space):
    """Phase-A contract over reinterpreted inputs: P[h][o...] = reduce over the local part."""
    from .compiler import Outputs
    from .layout import Contract, TensorSpec

    specs = {s.name: s for s in contract.inputs}
    used = set()
    for per in parts.values():
        for ts in per.values():
            for t in ts:
                for n in walk([t]):
                    if n.op == "input":
                        used.add(n.value[0])
            break
        break
    split = {name: split_mixed(specs[name]) for name in used}

    def rebuild(node, memo):
        hit = memo.get(node.id)
        if hit is not None:
            return hit
        if node.op == "input":
            new, remap, _w = split[node.value[0]]
            r = graph.make("input", value=(new.name, remap(node.value[1])), ty=node.ty)
        elif not node.args:
            r = node
        else:
            r = graph.make(node.op, tuple(rebuild(a, memo) for a in node.args), value=node.value, ty=node.ty)
        memo[node.id] = r
        return r

    # the hierarchy unit of a term: the hierarchy parts of the axes varying among one output's terms
    first = next(iter(parts.values()))
    memo0 = {}
    sample = [rebuild(t, memo0) for ts in first.values() for t in ts]
    seen = defaultdict(set)
    for t in sample:
        for n in walk([t]):
            if n.op == "input":
                seen[n.value[0]].add(n.value[1])
    hier_axes = hier_axes_cache = {}
    for name, idxs in seen.items():
        orig = name[:-1]
        new, _r, where = split[orig]
        varying = [a for a in range(len(next(iter(idxs)))) if len({i[a] for i in idxs}) > 1]
        hax = [a for a in varying if all(d.axis in HIER for d in new.layout.axes[a])]
        if len(hax) != 1:
            raise CompileError("hierarchy: terms do not vary along one hierarchy axis")
        hier_axes[name] = hax[0]
    where_loc = {}
    for (pe, addr), eid in mreq.items():
        for lane, (o, mabs) in eid:
            where_loc[(o, next(iter(mabs)))] = Loc(pe, addr, lane)
    nodes, locs = {}, {}
    # the layout needs every partial's location; the strategies analyse a sample of the expressions
    keep_every = max(1, len(parts) // 1024)
    for k_o, (o, per) in enumerate(parts.items()):
        if k_o % keep_every:
            for m in per:
                h = _unit_index(per[m][0], split, specs, hier_axes_cache, rebuild)
                locs[(h,) + tuple(o[1])] = where_loc.get((o, m))
            continue
        for m, ts in per.items():
            memo = {}
            rts = [rebuild(t, memo) for t in ts]
            hs = set()
            for t in rts:
                for n in walk([t]):
                    if n.op == "input":
                        hs.add(n.value[1][hier_axes[n.value[0]]])
            if len(hs) != 1:
                raise CompileError("hierarchy: a MAB holds terms of several hierarchy units")
            key = (hs.pop(),) + tuple(o[1])
            nodes[key] = rts[0] if len(rts) == 1 else graph.make(op, tuple(sorted(rts, key=lambda a: (a.shape, a.id))), ty=rts[0].ty)
            locs[key] = where_loc.get((o, m))
    shape = (max(k[0] for k in nodes) + 1,) + tuple(out.shape)
    layout, base = infer_layout(shape, lambda idx: locs.get(idx))
    top = max(l.addr for l in locs.values() if l is not None) + 1
    pspec = TensorSpec(name="__P", dtype=out.dtype, space=space, start=2 * base, end=2 * top, layout=layout, atol=out.atol)
    pspec, premap, _w = split_mixed(pspec, name="__P")
    others = [s for s in contract.inputs if s.name not in split]
    pcontract = Contract(others + [new for new, _r, _w in split.values()], [pspec])
    pout = Outputs({"__P": {premap(k): v for k, v in nodes.items()}})
    pout.graph = graph
    return pcontract, pout


def _per_pe_then_rotate(graph, contract, out, op, parts, mreq, space, dst_space=None, tbase=None):
    """Phase-A variants for partials whose terms are spread over the PEs of a MAB: every PE
    reduces its own terms into a temporary word, then two rotation steps (msl) combine the
    four PEs and every PE writes the MAB partial."""
    from .compiler import Outputs, local_strategy
    from .layout import Contract
    from .reduce import local_reduce_strategy
    from .vprog import FlagUse, Use, Value, VOp, forward_stores

    specs = {s.name: s for s in contract.inputs}
    pe_cache = {}

    def pes_of(term, m):
        sets = []
        for n in walk([term]):
            if n.op == "input":
                k = (n.value, m)
                if k not in pe_cache:
                    pe_cache[k] = frozenset(l.pe % 4 for l in specs[n.value[0]].locations(n.value[1], replicate=True) if l.pe // 4 == m)
                sets.append(pe_cache[k])
        return frozenset.intersection(*sets) if sets else frozenset(range(4))

    amin = min(addr for _, addr in mreq)
    span = max(addr for _, addr in mreq) + 1 - amin
    toff = (max(addr for _, addr in mreq) + 8) // 8 * 8 if tbase is None else tbase  # temporaries
    # region r holds, in every PE of the MAB, that PE's share of the partial PE r must write
    regions = sorted({pe % 4 for pe, _ in mreq})

    def tmp(r, addr):
        return toff + regions.index(r) * span + addr - amin

    locs, nodes = {}, {}
    spread = False
    for (pe, addr), eid in mreq.items():
        m, r = pe // 4, pe % 4
        for lane, (o, mabs) in eid:
            per = defaultdict(list)
            for t in parts[o][next(iter(mabs))]:
                ps = pes_of(t, m)
                if not ps:
                    raise CompileError("hierarchy: a term's operands are not in one PE")
                per[min(ps)].append(t)
            if len(per) > 1:
                spread = True
            for q in range(4):
                ts = per.get(q)
                if not ts:
                    raise CompileError("hierarchy: a PE holds none of a partial's terms")
                k = (len(locs),)
                locs[k] = Loc(m * 4 + q, tmp(r, addr), lane)
                nodes[k] = ts[0] if len(ts) == 1 else graph.make(op, tuple(sorted(ts, key=lambda a: (a.shape, a.id))), ty=ts[0].ty)
    if not spread:
        raise CompileError("hierarchy: partials are PE-local")
    if len(set(locs.values())) != len(locs):
        raise CompileError("hierarchy: temporary words collide")
    tspec = ExplicitSpec("__pepart", out.dtype, space, locs, out.atol)
    tcontract = Contract(contract.inputs, [tspec])
    tout = Outputs({"__pepart": nodes})
    tout.graph = graph
    p = {64: "l", 32: "i", 16: "s"}[out.dtype.bits]
    if out.dtype.is_float:
        f = {64: "d", 32: "f", 16: "h"}[out.dtype.bits]
        combine = {"sum": (f"{f}vadd", "mau"), "max": (f"{f}max", "alu"), "min": (f"{f}min", "alu")}[op]
    else:
        u = "u" if out.dtype.kind == "uint" else ""
        combine = {"sum": (f"{u}{p}add", "alu"), "max": (f"{u}{p}max", "alu"), "min": (f"{u}{p}min", "alu"),
                   "lor": (f"{p}or", "alu"), "land": (f"{p}and", "alu")}[op]
    words = sorted({addr for _, addr in mreq})
    variants = []
    from .membership import membership_strategy

    for sname, strat in (("local", local_strategy), ("local-reduce", local_reduce_strategy), ("membership", membership_strategy)):
        try:
            res = strat(None, tcontract, tout)
        except CompileError:
            continue
        for vname, prog in (res if isinstance(res, list) else [("", res)]):
            flags = {}
            temps = set()
            if len(regions) > 1:
                from .machine import Fixed
                from .select import Constants

                consts = getattr(prog, "constants", None) or Constants(prog, base=480)
                for r in regions:
                    fl = Value(0, "flags")
                    prog.add(VOp("ixor", [Fixed("subpeid"), Use(consts.word32(r))], out=Value(2), flags_out=fl, unit="alu", note="region"))
                    flags[r] = fl
            for i in range(0, len(words), 4):
                chunk = words[i:i + 4]
                while len(chunk) < 4:
                    chunk = chunk + [chunk[-1]]
                dst = Mem(dst_space or space, 2, tuple(2 * a for a in chunk))
                for r in regions:
                    src = Mem(space, 2, tuple(2 * tmp(r, a) for a in chunk))
                    temps.add(src)
                    cur = VOp("lpassa", [src], out=Value(2), unit="alu")
                    prog.add(cur)
                    cur = cur.out
                    for n, k in enumerate((1, 2)):
                        rot = cur
                        for _ in range(k):
                            rr = VOp("msl", [Use(rot)], out=Value(2), unit="alu")
                            prog.add(rr)
                            rot = rr.out
                        last = n == 1
                        c = VOp(combine[0], [Use(cur), Use(rot)], out=Value(2) if not last or flags else None,
                                dsts=[dst] if last and not flags else [], unit=combine[1])
                        prog.add(c)
                        cur = c.out
                    if flags:
                        prog.add(VOp("lpassa", [Use(cur)], dsts=[dst], unit="alu", write_mask=FlagUse(flags[r]), note="region"))
            forward_stores(prog, temps)
            variants.append((f"pe+rot-{sname}{'/' + vname if vname else ''}", _Ready(prog), None, None))
    return variants


class _Ready:
    """A phase-A program computed outside the strategy loop."""

    def __init__(self, prog):
        self.prog = prog

    def __call__(self, source, contract, outputs, **kw):
        return self.prog


def hierarchy_strategy(source, contract, outputs, *, variant=None):
    from .compiler import Outputs, local_strategy
    from .layout import Contract
    from .matmul import contraction_strategy
    from .pereduce import pe_reduce_strategy
    from .reduce import local_reduce_strategy
    from .schedule import schedule, with_hops
    from .sim import assembler

    graph = outputs.graph
    plans = []
    natural = False
    for spread in (None, ("MAB",), ("L1B",), ("MAB", "L1B")):
        if spread is not None and natural:
            break  # the reduction already spans units: splitting replicated work does not apply
        try:
            out, op, parts, space, chains = plan(contract, outputs, spread)
        except CompileError:
            continue
        natural = natural or spread is None
        tag = "" if spread is None else "split-" + "+".join(spread) + ":"
        plans += [(cost, tag + name, hops, mreq, parts) for cost, name, hops, mreq in chains[:2]]
    if not plans:
        raise CompileError("hierarchy: no transfer chain")
    asm = assembler()
    results = []
    for cost, name, hops, mreq, parts in plans:
        # phase A: partial reductions at the words the chain reads
        phase_b = []
        for hop in hops:
            if not hop:
                continue
            phase_b.append(Step(nop=3))
            phase_b += [Step([ins]) for ins in hop]
        phase_a = []
        # partials that are matrix products go to the matrix unit (layout-based)
        try:
            scontract, sout = structured_partials(graph, contract, out, op, parts, mreq, space)
            mm = contraction_strategy(source, scontract, sout)
            phase_a.append(("contraction", _Ready(mm), None, None))
        except CompileError:
            pass
        n_partials = sum(len(eid) for eid in mreq.values())
        if not phase_a and n_partials <= 65536:
            # otherwise every partial at an explicit word, for the PE-level strategies
            locs, nodes = {}, {}
            for (pe, addr), eid in mreq.items():
                for lane, (o, mabs) in eid:
                    (m,) = mabs
                    terms = parts[o][m]
                    node = terms[0] if len(terms) == 1 else graph.make(op, tuple(sorted(terms, key=lambda a: (a.shape, a.id))), ty=terms[0].ty)
                    k = (len(locs),)
                    locs[k] = Loc(pe, addr, lane)
                    nodes[k] = node
            pspec = ExplicitSpec("__partial", out.dtype, space, locs, out.atol)
            pcontract = Contract(contract.inputs, [pspec])
            pout = Outputs({"__partial": nodes})
            pout.graph = graph
            phase_a = [(sname, strat, pcontract, pout) for sname, strat in (("local", local_strategy), ("local-reduce", local_reduce_strategy), ("pe-reduce", pe_reduce_strategy))]
            try:
                phase_a += _per_pe_then_rotate(graph, contract, out, op, parts, mreq, space)
            except CompileError:
                pass
        for sname, strat, pc, po in phase_a:
            try:
                res = strat(source, pc, po)
            except CompileError:
                continue
            for vname, prog in (res if isinstance(res, list) else [("", res)]):
                label = f"{name}+{sname}{'/' + vname if vname else ''}"
                try:
                    steps = schedule(prog, asm, tries=2)
                    results.append((label, steps + phase_b))
                except CompileError:
                    pass
                # the transfer chain scheduled with the computation (overlaps its latencies)
                try:
                    results.append((label + "/fused", schedule(with_hops(prog, hops), asm, tries=2)))
                except CompileError:
                    pass
    if not results:
        raise CompileError("hierarchy: no PE-level strategy computes the partials")
    return results


def mab_reduce_strategy(source, contract, outputs, *, variant=None):
    """Reductions whose terms lie in the output's MAB but in several of its PEs: per-PE partials,
    a rotation tree across the PEs, and every output PE writes its own result."""
    graph = outputs.graph
    if len(contract.outputs) != 1:
        raise CompileError("mab-reduce: one output")
    out = contract.outputs[0]
    if out.space == "dram":
        raise CompileError("mab-reduce: DRAM output")
    specs = {s.name: s for s in contract.inputs}
    op = None
    parts, mreq = {}, defaultdict(dict)
    for idx, node in outputs[out.name].items():
        if node.op == "toint" and node.args[0].op in ("lor", "land") and out.dtype.kind != "float":
            node = node.args[0]
        if node.op not in REDUCE or len(node.args) < 2:
            raise CompileError("mab-reduce: output is not a reduction")
        if op not in (None, node.op):
            raise CompileError("mab-reduce: mixed reductions")
        op = node.op
        loc = out.locations(idx, replicate=False)[0]
        m = loc.pe // 4
        for t in node.args:
            for n in walk([t]):
                if n.op == "input" and not any(l.pe // 4 == m for l in specs[n.value[0]].locations(n.value[1], replicate=True)):
                    raise CompileError("mab-reduce: a term is outside the output's MAB")
        o = (out.name, idx)
        parts[o] = {m: list(node.args)}
        mreq[(loc.pe, loc.addr)][loc.lane] = (o, frozenset({m}))
    mreq = {k: tuple(sorted(v.items())) for k, v in mreq.items()}
    space, base = _scratch(contract)
    variants = _per_pe_then_rotate(graph, contract, out, op, parts, mreq, space, dst_space=out.space, tbase=base)
    if not variants:
        raise CompileError("mab-reduce: no PE-level strategy")
    return [(name, ready.prog) for name, ready, _a, _b in variants]
