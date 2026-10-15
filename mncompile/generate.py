"""Outputs that do not depend on the inputs: generate the words in PEs, then upload them.

The DRAM words are assigned to PE words through an upload chain chosen freely
(no input fixes where a word must come from):

* concentrated: one L2B, one L1B and one MAB carry everything (few words);
* spread: every L2B carries a slice of the DRAM range, every L1B a slice of
  that (``l2bmd``) and every PE of the L1B a few words (``l1bmd``), so each PE
  generates only a handful of words.

A PE word whose value is the same in every PE is written with immediates. When
the values differ between PEs, each 32-bit half must be a constant plus a
function linear in the bits of the PE coordinates; it is built from the fixed
operands (``$peid``, ``$l1bid``, ``$l2bid``) as a sum of shifted fields
(``(F >> s) * a``), once, and every word adds its own constant.
"""

from __future__ import annotations

from collections import defaultdict

from .errors import CompileError
from .layout import pe_coords
from .machine import Dram, Fixed, Imm, Instr, L1, L2, Mem, Pdm, Step
from .values import encode, pack
from .vprog import FlagUse, Use, Value, VOp, VProgram

MASK32 = 0xFFFFFFFF


def _ranges(words):
    by_group = defaultdict(list)
    for g, d in words:
        by_group[g].append(d)
    return {g: (min(ds) // 64 * 64, (max(ds) - min(ds) // 64 * 64) // 64 * 64 + 64) for g, ds in by_group.items()}


def _concentrated(words, base, space):
    """Everything through L2B 0 of group 0, L1B 0 and MAB 0 (two long words per PE per cycle)."""
    ranges = _ranges(words)
    mv, l2pos = [], {}
    top = 0
    for g, (lo, n) in sorted(ranges.items()):
        mv.append(Instr(f"mvp/n{n}", (L2(top, l2b=0, group=0),), (Dram(lo, g),)))
        for (gg, d) in words:
            if gg == g:
                l2pos[(gg, d)] = top + d - lo
        top += n
    l2 = [Instr("l2bm@0", (L1(64 * b, 2),), (L2(64 * b),)) for b in range(top // 64)]
    l1, pereq = [], {}
    for blk in range((top + 31) // 32):
        first = base + 8 * blk
        l1.append(Instr("l1bmm@0", (Mem(space, 4, tuple(2 * (first + 2 * c) for c in range(4))),), (L1(32 * blk, 4),)))
    for key, a in l2pos.items():
        blk, off = divmod(a, 32)
        c, rest = divmod(off, 8)
        k, p = divmod(rest, 4)
        pereq[(p, base + 8 * blk + 2 * c + k)] = words[key]
    return [l1, l2, mv], pereq


def _spread(words, base, space):
    """Every L2B, L1B and PE carries a slice: mvp per L2B, l2bmd, l1bmd."""
    ranges = _ranges(words)
    per_l2b = defaultdict(list)  # l2b -> [(g, dram lo, n)]
    for g, (lo, n) in sorted(ranges.items()):
        units = n // 64
        size = (units + 7) // 8 * 64
        for j in range(8):
            a = lo + j * size
            if a >= lo + n:
                break
            per_l2b[j].append((g, a, min(size, lo + n - a)))
    mv, l2pos = [], {}
    top = 0
    for j, chunks in sorted(per_l2b.items()):
        off = 0
        for g, a, n in chunks:
            mv.append(Instr(f"mvp/n{n}", (L2(off, l2b=j % 2, group=j // 2),), (Dram(a, g),)))
            for (gg, d) in words:
                if gg == g and a <= d < a + n:
                    l2pos[(gg, d)] = (j, off + d - a)
            off += n
        top = max(top, off)
    l1, l2, pereq = _l2_to_pe(words, l2pos, top, base, space)
    return [l1, l2, mv], pereq


def _spread_pdm(words, base, space):
    """Like `_spread`, but the eight L2BM slices are combined into the PDM (mvd, 16 long words
    round robin over the L2Bs) and one mvp writes the whole range."""
    ranges = _ranges(words)
    if len(ranges) != 1:
        raise CompileError("generate: PDM upload for one DRAM group")
    ((g, (lo, n)),) = ranges.items()
    if n % 512:
        raise CompileError("generate: the PDM upload writes whole 512-word blocks")
    total = n
    l2pos = {}
    for (gg, d) in words:
        r = d - lo
        i, rr = divmod(r, 512)
        l2pos[(gg, d)] = ((rr // 16) % 8, 64 * i + 16 * (rr // 128) + rr % 16)
    mv = [Instr(f"mvd/n{total // 8}", (L2(0),), (Pdm(0, 0),))]
    up = [Instr(f"mvp/n{total}", (Pdm(0, 0),), (Dram(lo, g),))]
    l1, l2, pereq = _l2_to_pe(words, l2pos, total // 8, base, space)
    return [l1, l2, mv, up], pereq


def _l2_to_pe(words, l2pos, top, base, space):
    """L1BM -> L2BM (l2bmd) and PE -> L1BM (l1bmd) hops for words at (L2B serial, L2BM address)."""
    l2 = [Instr("l2bmd", (L1(32 * b, 2),), (L2(256 * b),)) for b in range((top + 255) // 256)]
    l1top = 32 * ((top + 255) // 256)
    l1 = [Instr("l1bmd", (Mem(space, 2, tuple(2 * (base + 4 * blk + c) for c in range(4))),), (L1(256 * blk, 2),))
          for blk in range((l1top + 255) // 256)]
    pereq = {}
    for key, (j, a) in l2pos.items():
        b, off = divmod(a, 256)
        c, rest = divmod(off, 64)
        l1b, jj = divmod(rest, 8)
        a1 = 32 * b + 8 * c + jj
        blk, off1 = divmod(a1, 256)
        c1, rest1 = divmod(off1, 64)
        mab, p = divmod(rest1, 4)
        pe = ((j * 8 + l1b) * 16 + mab) * 4 + p
        pereq[(pe, base + 4 * blk + c1)] = words[key]
    return l1, l2, pereq


def _bits_features(pe):
    c = pe_coords(pe)
    f = []
    for axis, n in (("PE", 2), ("MAB", 4), ("L1B", 3), ("L2B", 3)):
        f += [(c[axis] >> i) & 1 for i in range(n)]
    return f


FIELDS = (("peid", 0, 6), ("l1bid", 6, 3), ("l2bid", 9, 3))  # fixed operand, first feature bit, bits


def fit_bits(samples):
    return _fit(samples)


def _fit(samples):
    """samples: [(pe, half, value)] -> (c0, c_half, bit coefficients) or None (exact over the integers
    mod 2^32). Axes are tried from the fewest upwards, so an underdetermined sample still gets the
    simplest integer solution."""
    import itertools

    import numpy as np

    groups = {"PE": range(0, 2), "MAB": range(2, 6), "L1B": range(6, 9), "L2B": range(9, 12)}
    feats = [_bits_features(pe) for pe, _h, _v in samples]
    vals = [v for _, _, v in samples]
    halves = [h for _, h, _ in samples]
    for size in range(0, 5):
        for axes in itertools.combinations(groups, size):
            cols = [i for a in axes for i in groups[a]]
            rows = [[1, h] + [f[i] for i in cols] for f, h in zip(feats, halves)]
            A = np.array(rows, dtype=float)
            for wrap in (False, True):
                b = np.array([float(v - (1 << 32) if wrap and v >= 1 << 31 else v) for v in vals])
                coef, *_ = np.linalg.lstsq(A, b, rcond=None)
                coef = [int(round(x)) for x in coef]
                if all((sum(c * x for c, x in zip(coef, row)) - v) % (1 << 32) == 0 for row, v in zip(rows, vals)):
                    full = [coef[0], coef[1]] + [0] * 12
                    for c, i in zip(coef[2:], cols):
                        full[2 + i] = c
                    return full
    return None


def _times(prog, t, a, consts):
    """t * a with shifts (a = +-2^k or a sum/difference of two powers); returns (value, sign)."""
    sign = 1 if a > 0 else -1
    m = abs(a)
    if m & (m - 1) == 0:
        k = m.bit_length() - 1
        return (t if k == 0 else _op(prog, "ilsl", [Use(t), Use(consts.word32(k))])), sign
    hi = m.bit_length() - 1
    lo_part = m - (1 << hi)
    if lo_part & (lo_part - 1) == 0:
        x = _op(prog, "ilsl", [Use(t), Use(consts.word32(hi))])
        y = t if lo_part == 1 else _op(prog, "ilsl", [Use(t), Use(consts.word32(lo_part.bit_length() - 1))])
        return _op(prog, "iadd", [Use(x), Use(y)]), sign
    up = (1 << (hi + 1)) - m
    if up & (up - 1) == 0:
        x = _op(prog, "ilsl", [Use(t), Use(consts.word32(hi + 1))])
        y = t if up == 1 else _op(prog, "ilsl", [Use(t), Use(consts.word32(up.bit_length() - 1))])
        return _op(prog, "isub", [Use(x), Use(y)]), sign
    raise CompileError(f"generate: coefficient {a} needs too many shifts")


def bitlinear_value(prog, consts, c0, c_half, bits, dst=None):
    """(c0, c0 + c_half) + sum_i bits[i] * (bit i of the PE coordinates) in 32-bit lanes, built from
    the fixed operands as sum of a * (F >> s); the last op also writes `dst` when given."""
    pe_bits, mab_bits = bits[0:2], bits[2:6]
    if not any(pe_bits):
        fields = [("mabid", mab_bits), ("l1bid", bits[6:9]), ("l2bid", bits[9:12])]
    elif not any(mab_bits):
        fields = [("subpeid", pe_bits), ("l1bid", bits[6:9]), ("l2bid", bits[9:12])]
    else:
        fields = [("peid", bits[0:6]), ("l1bid", bits[6:9]), ("l2bid", bits[9:12])]
    terms = []  # (fixed operand, shift right, multiplier)
    for name, cs in fields:
        n = len(cs)
        a_s = [cs[0]] + [cs[i] - 2 * cs[i - 1] for i in range(1, n)]
        terms += [(name, s, a) for s, a in enumerate(a_s) if a]
    acc = None
    for name, s, a in terms:
        t = Fixed(name)
        m = abs(a)
        if m & (m - 1) == 0 and a > 0 and (s == 0 or m == 1):
            # one op: F << k or F >> s
            if s:
                val = _op(prog, "ilsr", [t, Use(consts.word32(s))])
            elif m > 1:
                val = _op(prog, "ilsl", [t, Use(consts.word32(m.bit_length() - 1))])
            else:
                val = _op(prog, "ipassa", [t])
            sign = 1
        else:
            tv = _op(prog, "ilsr", [t, Use(consts.word32(s))]) if s else _op(prog, "ipassa", [t])
            val, sign = _times(prog, tv, a, consts)
        if acc is None:
            if sign > 0:
                acc = val
            else:
                acc = _op(prog, "isub", [Use(consts.word32(0)), Use(val)])
        else:
            acc = _op(prog, "iadd" if sign > 0 else "isub", [Use(acc), Use(val)])
    base = ((c0 & MASK32) << 32) | ((c0 + c_half) & MASK32)
    if acc is None:
        acc = consts.word64(base)
        if dst is not None:
            prog.add(VOp("lpassa", [Use(acc)], dsts=[dst], unit="alu", note="generate"))
        return acc
    if base:
        acc = _op(prog, "iadd", [Use(acc), Use(consts.word64(base))])
    if dst is not None:
        prog.ops[-1].dsts = [dst]
    return acc


def bitgather_value(prog, consts, coef):
    """The bit-linear value when every coordinate bit lands on its own bit (a bit permutation,
    as upload chains produce): bits moved by the same shift are masked, OR-ed and shifted
    together. None when the coefficients are not distinct powers of two or the constant is not 0."""
    import itertools

    c0, ch, bits = coef[0], coef[1], coef[2:]
    if c0 or ch:
        return None
    nz = [c for c in bits if c]
    if any(c < 0 or c & (c - 1) for c in nz) or len(set(nz)) != len(nz):
        return None
    # feature bit -> (fixed operand, bit): peid = MAB * 4 + PE
    src = [("peid", 0), ("peid", 1)] + [("peid", 2 + k) for k in range(4)] + [("l1bid", k) for k in range(3)] + [("l2bid", k) for k in range(3)]
    width = {"peid": 6, "l1bid": 3, "l2bid": 3}
    groups = {}
    for (name, b), c in zip(src, bits):
        if c:
            d = c.bit_length() - 1
            groups.setdefault(d - b, {}).setdefault(name, 0)
            groups[d - b][name] |= 1 << b
    if not groups:
        return None
    best = None
    keys = sorted(groups)
    for post in itertools.product((False, True), repeat=len(keys)):
        plan_ops, used = 0, set()
        for k, pm in zip(keys, post):
            terms = groups[k]
            for name, m in terms.items():
                full = m == (1 << width[name]) - 1
                if not full or pm:
                    if pm and len(terms) == 1:
                        used.add(("mask", (m << k) if k >= 0 else (m >> -k)))
                    else:
                        used.add(("mask", m))
                    plan_ops += 0 if full and pm and len(terms) == 1 else 1
            plan_ops += len(terms) - 1 + (1 if k else 0)
            if k:
                used.add(("shift", abs(k)))
        plan_ops += len(keys) - 1
        cost = plan_ops + len(used)
        if best is None or cost < best[0]:
            best = (cost, post)
    acc = None
    for k, pm in zip(keys, best[1]):
        terms = groups[k]
        one = len(terms) == 1
        t = None
        for name, m in sorted(terms.items()):
            v = Fixed(name)
            full = m == (1 << width[name]) - 1
            if one and pm:
                x = _op(prog, "ilsl" if k > 0 else "ilsr", [v, Use(consts.word32(abs(k)))]) if k else None
                mm = (m << k) if k >= 0 else (m >> -k)
                if x is None:
                    t = _op(prog, "iand", [v, Use(consts.word32(m))]) if not full else _op(prog, "ipassa", [v])
                elif not full or k < 0:
                    t = _op(prog, "iand", [Use(x), Use(consts.word32(mm))]) if not full else x
                else:
                    t = x
                break
            y = Use(_op(prog, "iand", [v, Use(consts.word32(m))])) if not full else v
            t = y if t is None else Use(_op(prog, "ior", [t if isinstance(t, Use) else t, y]))
        if not (one and pm):
            tv = t
            if k:
                t = _op(prog, "ilsl" if k > 0 else "ilsr", [tv, Use(consts.word32(abs(k)))])
            elif isinstance(tv, Use):
                t = tv.value
            else:
                t = _op(prog, "ipassa", [tv])
        acc = t if acc is None else _op(prog, "ior", [Use(acc), Use(t)])
    return acc


def _op(prog, opcode, srcs, unit="alu"):
    op = VOp(opcode, srcs, out=Value(2), unit=unit, note="generate")
    prog.add(op)
    return op.out


def _imm_word(prog, space, a, word, mask):
    hi, lo = word >> 32, word & MASK32
    prog.add(VOp("imm", [Imm("ui", "0x%08X" % hi)], dsts=[Mem(space, 2, (2 * a,) * 4)], unit="alu", write_mask=mask, note="generate"))
    if lo != hi:
        prog.add(VOp("imm", [Imm("ui", "0x%08X" % lo)], dsts=[Mem(space, 1, (2 * a + 1,) * 4)], unit="alu", write_mask=mask, note="generate"))


def _phase_a(pereq, space):
    """Ops writing every required PE word (raw 64-bit values)."""
    from .select import Constants

    prog = VProgram()
    consts = Constants(prog)
    by_addr = defaultdict(dict)
    for (pe, addr), word in pereq.items():
        by_addr[addr][pe] = word
    uniform = {a: next(iter(v.values())) for a, v in by_addr.items() if len(set(v.values())) == 1}
    varying = {a: v for a, v in by_addr.items() if a not in uniform}
    for a, word in sorted(uniform.items()):
        _imm_word(prog, space, a, word, None)
    # words that differ only between the four PEs of a MAB: masked immediates per PE
    for a in list(varying):
        per = varying[a]
        by_sub = defaultdict(set)
        for pe, word in per.items():
            by_sub[pe % 4].add(word)
        if any(len(v) != 1 for v in by_sub.values()):
            continue
        del varying[a]
        values = {p: next(iter(v)) for p, v in by_sub.items()}
        common = max(set(values.values()), key=lambda w: sum(1 for x in values.values() if x == w))
        _imm_word(prog, space, a, common, None)
        for p, word in sorted(values.items()):
            if word == common:
                continue
            flags = Value(0, "flags")
            prog.add(VOp("ixor", [Fixed("subpeid"), Use(consts.word32(p))], out=Value(2), flags_out=flags, unit="alu", note="generate"))
            _imm_word(prog, space, a, word, FlagUse(flags))
    if not varying:
        return prog
    # one bit-linear function of the coordinates shared by all varying words, plus a constant per word
    samples = []
    first = None
    offsets = {}
    for a, per in sorted(varying.items()):
        for pe, word in per.items():
            for h, half in ((0, word >> 32), (1, word & MASK32)):
                samples.append((pe, h, half, a))
    # constant per address: subtract the first PE's value structure later; fit with per-address offsets
    pes = sorted({pe for pe, *_ in samples})
    a0 = min(varying)
    coef = _fit([(pe, h, v) for pe, h, v, a in samples if a == a0])
    if coef is None:
        raise CompileError("generate: values are not linear in the PE coordinate bits")
    c0, ch, bits = coef[0], coef[1], coef[2:]

    def model(pe, h):
        return c0 + ch * h + sum(c * x for c, x in zip(bits, _bits_features(pe)))

    for a, per in varying.items():
        deltas = {((word >> 32) - model(pe, 0)) % (1 << 32) for pe, word in per.items()} | {((word & MASK32) - model(pe, 1)) % (1 << 32) for pe, word in per.items()}
        if len(deltas) != 1:
            raise CompileError("generate: words need different coordinate functions")
        offsets[a] = deltas.pop()
    # V = (0, ch) + sum over fields of shifted terms (a bit permutation: masked fields OR-ed per shift)
    acc = bitgather_value(prog, consts, [0, 0] + list(bits))
    if acc is not None and ch:
        acc = _op(prog, "iadd", [Use(acc), Use(consts.word64(ch & MASK32))])
    if acc is None:
        acc = bitlinear_value(prog, consts, 0, ch, bits)
    for a, off in sorted(offsets.items()):
        total = (off + c0) & MASK32
        dst = Mem(space, 2, (2 * a,) * 4)
        if total:
            prog.add(VOp("iadd", [Use(acc), Use(consts.word32(total))], dsts=[dst], unit="alu", note="generate"))
        else:
            prog.add(VOp("lpassa", [Use(acc)], dsts=[dst], unit="alu", note="generate"))
    return prog


def _table_steps(words, space):
    """Arbitrary words: every PE of MAB 0 holds its own words, written by masked immediates
    (flag = PE index), then l1bmm@0 / l2bm@0 / mvp carry them to the DRAM. One immediate per
    32-bit half and PE: long, but it handles data with no structure the PEs could compute."""
    from .machine import Fixed, Imm, Mask, Omr

    if space == "lm0":
        space = "lm1"  # immediates must not touch LM0
    ranges = _ranges(words)
    mv, l2pos = [], {}
    top = 0
    for g, (lo, n) in sorted(ranges.items()):
        mv.append(Instr(f"mvp/n{n}", (L2(top, l2b=0, group=0),), (Dram(lo, g),)))
        for (gg, d) in words:
            if gg == g:
                l2pos[top + d - lo] = words[(gg, d)]
        top += n
    l2 = [Instr("l2bm@0", (L1(64 * b, 2),), (L2(64 * b),)) for b in range(top // 64)]
    base = 1024 if space == "lm1" else 0  # long words; clear of the small LM1 tensors
    l1 = []
    for blk in range((top + 31) // 32):
        first = base + 8 * blk
        l1.append(Instr("l1bmm@0", (Mem(space, 4, tuple(2 * (first + 2 * c) for c in range(4))),), (L1(32 * blk, 4),)))
    # PE p, long word base + 8 blk + 2 c + k holds L1BM[32 blk + 8 c + 4 k + p]
    per_addr = defaultdict(dict)
    for a, word in l2pos.items():
        blk, off = divmod(a, 32)
        c, rest = divmod(off, 8)
        k, p = divmod(rest, 4)
        per_addr[base + 8 * blk + 2 * c + k][p] = word
    steps = []
    consts = {}
    for p in range(1, 4):
        steps.append(Step([Instr("imm", (Imm("ui", "0x%08X" % p),), (Mem("grf0", 2, (2 * p,) * 4),))]))
    steps.append(Step(nop=2))
    for p in range(1, 4):
        steps.append(Step([Instr("ixor", (Fixed("subpeid"), Mem("grf0", 2, (2 * p,) * 4)), (Omr(p),))]))
    steps.append(Step(nop=2))
    for addr, per in sorted(per_addr.items()):
        for half, (wl, waddr) in enumerate(((2, 2 * addr), (1, 2 * addr + 1))):
            vals = {p: (w >> 32 if half == 0 else w & MASK32) for p, w in per.items()}
            first = vals.get(0, next(iter(vals.values())))
            if half == 1 and all(v == (per[p] >> 32) for p, v in vals.items()) and per.get(0, None) is not None:
                continue  # the long-word write of the high half already put it in both words
            steps.append(Step([Instr("imm", (Imm("ui", "0x%08X" % first),), (Mem(space, wl, (waddr,) * 4),))]))
            for p, v in sorted(vals.items()):
                if p and v != first:
                    steps.append(Step([Instr("imm", (Imm("ui", "0x%08X" % v),), (Mem(space, wl, (waddr,) * 4, mask=Mask(entry=p)),))]))
    for hop in (l1, l2, mv):
        steps.append(Step(nop=3))
        steps += [Step([ins]) for ins in hop]
    return steps


def generate_strategy(source, contract, outputs, *, variant=None):
    from .hier import _scratch
    from .schedule import schedule
    from .sim import assembler

    if len(contract.outputs) != 1:
        raise CompileError("generate: one output")
    out = contract.outputs[0]
    nodes = outputs[out.name]
    if any(n.op != "const" for n in nodes.values()):
        raise CompileError("generate: output depends on the inputs")
    if out.space != "dram":
        raise CompileError("generate: LM constants are local maps")
    lanes = defaultdict(dict)
    for idx, n in nodes.items():
        loc = out.locations(idx, replicate=False)[0]
        lanes[(loc.pe, loc.addr)][loc.lane] = encode(n.value, out.dtype)
    words = {k: pack(v, out.dtype) for k, v in lanes.items()}
    space, base = _scratch(contract)
    asm = assembler()
    results = []
    for name, planner in (("concentrated", _concentrated), ("spread", _spread), ("spread-pdm", _spread_pdm)):
        if planner is _concentrated and len(words) > 256:
            continue  # a handful of PEs would generate everything
        try:
            hops, pereq = planner(words, base, space)
            prog = _phase_a(pereq, space)
            if len(prog.ops) > 4000:
                continue
            steps = schedule(prog, asm, tries=2)
        except CompileError:
            continue
        for hop in hops:
            if hop:
                steps.append(Step(nop=3))
                steps += [Step([ins]) for ins in hop]
        results.append((name, steps))
    if not results:
        results.append(("table", _table_steps(words, space)))
    return results
