"""Constant byte strings that are a formatted counter: tokens T(i) for i = a..b joined by a
one-byte separator, where T(i) is the decimal text of i or a constant chosen by the
divisibility of i (e.g. "1\\n2\\nFizz\\n4\\nBuzz..."). The analysis works on the output bytes
alone (separator, range, period, constants and the divisibility classes are inferred).

Every PE produces one 8-byte window of the string (the upload chain of `generate._spread`
fixes which). The four cycles of a vector op carry four consecutive tokens around the
window start:

* the window's digit-count segment (threshold compares on the byte offset b0) selects the
  segment's constants by masked merges;
* a linear estimate gives the first token i0, so the cycles hold i0 .. i0 + 3;
* the end offset of every token has a closed form in floor(i / m) over the divisibility
  moduli m, so each cycle computes where its token ends and loads it into T;
* the tokens are rendered right-aligned at their ends into LM0 cells (one character per
  word, T-indirect), character position by character position, in increasing position:
  a token's spill to the left is overwritten by the token that owns those cells. Digits come
  from floor(i * 10^-k); constant characters are masked by the divisibility flags;
* the eight cells of the window are packed into the long word the upload chain reads.

Windows the closed forms get wrong (none, or a few at segment boundaries) are patched with
masked immediates.
"""

from __future__ import annotations

import itertools
import math
from dataclasses import dataclass

import numpy as np

from .errors import CompileError
from .machine import Fixed, Imm, Mask, Mem, Step
from .vprog import FlagUse, Use, Value, VOp, VProgram

MAGIC = float(1 << 23)  # 2^23 + c has c in the low mantissa bits
WINDOW = 8
TOKENS = 4  # one per cycle


def f32(x):
    return float(np.float32(x))


def floor32(x):
    return float(math.floor(f32(x)))


@dataclass
class Seq:
    sep: int
    a: int
    b: int
    moduli: tuple  # divisibility flags [m | i]
    texts: dict  # flag tuple -> constant token bytes, or None for the decimal text
    period: int


# ------------------------------------------------------------------ analysis
def analyze(data: bytes) -> Seq:
    cands = sorted({c for c in data if not (48 <= c <= 57)}, key=lambda c: -data.count(bytes([c])))
    for sep in cands[:4]:
        toks = data.split(bytes([sep]))
        first = next((k for k, t in enumerate(toks) if t.isdigit()), None)
        if first is None:
            continue
        a = int(toks[first]) - first
        nums = sum(t == str(a + k).encode() for k, t in enumerate(toks))
        if a < 0 or nums * 4 < len(toks):
            continue
        for period in range(1, 65):
            cls = {}
            if all(cls.setdefault((a + k) % period, None if t == str(a + k).encode() else t) == (None if t == str(a + k).encode() else t)
                   for k, t in enumerate(toks)):
                break
        else:
            continue
        divs = [m for m in range(2, period + 1) if period % m == 0]
        for size in range(0, len(divs) + 1):
            for mods in itertools.combinations(divs, size):
                texts = {}
                ok = True
                for r, t in cls.items():
                    key = tuple(int(r % m == 0) for m in mods)
                    if texts.setdefault(key, t) != t:
                        ok = False
                        break
                if ok:
                    return Seq(sep, a, a + len(toks) - 1, mods, texts, period)
    raise CompileError("fmtseq: not a separator-joined counter with periodic constants")


def _monomials(seq):
    """Class indicators as sums over divisibility products: {class flags: {lcm: coefficient}}."""
    out = {}
    for key in seq.texts:
        poly = {(): 1}
        for m, bit in zip(seq.moduli, key):
            nxt = {}
            for mono, c in poly.items():
                if bit:
                    nxt[mono + (m,)] = nxt.get(mono + (m,), 0) + c
                else:
                    nxt[mono] = nxt.get(mono, 0) + c
                    nxt[mono + (m,)] = nxt.get(mono + (m,), 0) - c
            poly = nxt
        coef = {}
        for mono, c in poly.items():
            l = math.lcm(*mono) if mono else 1
            coef[l] = coef.get(l, 0) + c
        out[key] = {l: c for l, c in coef.items() if c}
    return out


def _weights(seq):
    """len(i) - D = sum over lcm values l of (U_l - V_l D) [l | i]: {l: (U, V)}."""
    mono = _monomials(seq)
    w = {}
    for key, text in seq.texts.items():
        if text is None:
            continue
        for l, c in mono[key].items():
            u, v = w.get(l, (0, 0))
            w[l] = (u + c * len(text), v + c)
    return {l: uv for l, uv in w.items() if uv != (0, 0)}


def _token(seq, i):
    key = tuple(int(i % m == 0) for m in seq.moduli)
    t = seq.texts.get(key)
    return str(i).encode() if t is None else t


# ------------------------------------------------------------------ plan
@dataclass
class Plan:
    seq: Seq
    weights: dict
    segs: list  # (D, first byte, K, R)
    groups: list  # [(U, V, [l...])] lcm values sharing a weight
    c: float
    lmax: int
    dmax: int
    buf: int  # cell offset of the window's first byte (from the T base)
    cell0: int  # LM0 word of cell offset 0
    span: tuple  # cell offsets touched (min, max + 1)
    writes: list  # per position: [(value, modulus or None)], value = ("digit", j) | ("char", byte)
    patches: dict  # b0 -> 8 bytes
    b0_of: dict  # pe -> b0


def _segments(seq, weights, off):
    segs = []
    for D in range(len(str(seq.a)), len(str(seq.b)) + 1):
        s = max(seq.a, 10 ** (D - 1))
        e = min(seq.b, 10 ** D - 1)
        u1, v1 = weights.get(1, (0, 0))
        B = D + 1 + u1 - v1 * D
        K = off[s] - B * s - sum((u - v * D) * ((s - 1) // l) for l, (u, v) in weights.items() if l > 1)
        for i in range(s, e + 1):
            assert off[i + 1] == K + B * (i + 1) + sum((u - v * D) * (i // l) for l, (u, v) in weights.items() if l > 1)
        per = 0
        for k in range(seq.period):
            t = seq.texts.get(tuple(int((s + k) % m == 0) for m in seq.moduli))
            per += (D if t is None else len(t)) + 1
        segs.append((D, off[s], K, f32(seq.period / per)))
    return segs


class Model:
    """The generated program's arithmetic, evaluated on the host (f32 where the PE uses f32)."""

    def __init__(self, seq, weights, segs, groups, c, lmax, dmax, writes):
        self.seq, self.weights, self.segs, self.groups = seq, weights, segs, groups
        self.c, self.lmax, self.dmax, self.writes = c, lmax, dmax, writes
        self.inv = {l: _inv(l) for g in groups for l in g[2]} | {m: _inv(m) for m in seq.moduli}

    def seg(self, b0):
        cur = self.segs[0]
        for s in self.segs[1:]:
            if b0 - s[1] >= 0:
                cur = s
        return cur

    def first(self, b0):
        D, _o, K, R = self.seg(b0)
        X = K - b0
        return math.floor(f32(self.c - f32(X * R))), D, X

    def ends(self, b0, buf):
        """Cell offset (T) of every rendered token: [(i, T)]."""
        i0, D, X = self.first(b0)
        u1, v1 = self.weights.get(1, (0, 0))
        B = D + 1 + u1 - v1 * D
        out = []
        for k in range(TOKENS):
            i = i0 + k
            t = X + (buf - 1 - self.lmax) + B + B * i
            for u, v, ls in self.groups:
                t += (u - v * D) * sum(math.floor(f32(i * self.inv[l])) for l in ls)
            out.append((i, int(t)))
        return out

    def digit(self, i, j):
        """Cell character of digit j (most significant first) as the PE computes it."""
        dmax = self.dmax
        s = {k: scale_val(k) for k in range(1, dmax)}
        F = {0: float(i)}
        for k in range(1, dmax):
            F[k] = float(math.floor(f32(i * s[k])))
        q = dmax - 1 - j
        pre = 48 + (F[q] if q == dmax - 1 else F[q] - 10.0 * F[q + 1])
        return int(pre) if 0 <= pre < 256 else None

    def render(self, b0, buf):
        cells = {}
        toks = self.ends(b0, buf)
        for rel, seqw in enumerate(self.writes):
            for value, mod in seqw:
                for i, t in toks:  # cycles in order
                    if mod is not None:
                        g = math.floor(f32(i * self.inv[mod]))
                        if g * mod - i < 0:
                            continue
                    cells[t + rel] = self.digit(i, value[1]) if value[0] == "digit" else value[1]
        return [cells.get(buf + j) for j in range(WINDOW)], toks


def scale_val(k):
    """f32 10^-k as the PE derives it (0.1 multiplied up), rounded up from the exact value."""
    s = f32(0.1)
    for _ in range(k - 1):
        s = f32(s * f32(0.1))
    return s


def _inv(m):
    """f32 near 1/m, rounded up so floor(i * r) == i // m for the counters used."""
    r = np.float32(1.0 / m)
    while float(r) * m < 1.0:
        r = np.nextafter(r, np.float32(1))
    return float(r)


def _write_sequences(seq, lmax, dmax):
    """For each right-aligned position, the shortest list of (value, modulus) writes leaving
    every class that owns the position with its character."""
    classes = list(seq.texts.items())
    out = []
    for rel in range(lmax + 1):
        want = {}
        for key, text in classes:
            if rel == lmax:
                want[key] = ("char", seq.sep)
            elif text is None:
                j = rel - (lmax - dmax)
                if j >= 0:
                    want[key] = ("digit", j)
            elif rel >= lmax - len(text):
                want[key] = ("char", text[rel - (lmax - len(text))])
        values = sorted(set(want.values()))
        masks = [None] + list(seq.moduli)
        best = None
        for n in range(1, 5):
            for combo in itertools.product(itertools.product(values, masks), repeat=n):
                if combo[0][1] is not None or any(v[0] == "digit" and m is not None for v, m in combo):
                    continue
                ok = True
                for key, w in want.items():
                    got = None
                    for v, m in combo:
                        if m is None or key[seq.moduli.index(m)]:
                            got = v
                    if got != w:
                        ok = False
                        break
                if ok:
                    best = list(combo)
                    break
            if best:
                break
        if best is None:
            raise CompileError("fmtseq: no write sequence for a position")
        out.append(best)
    return out


def plan(seq, b0_of, expect):
    weights = _weights(seq)
    off = {}
    o = 0
    for i in range(seq.a, seq.b + 2):
        off[i] = o
        if i <= seq.b:
            o += len(_token(seq, i)) + 1
    segs = _segments(seq, weights, off)
    lmax = max([len(str(seq.b))] + [len(t) for t in seq.texts.values() if t is not None])
    dmax = len(str(seq.b))
    if lmax > 8 or dmax > 4:
        raise CompileError("fmtseq: tokens longer than 8 characters")
    by_w = {}
    for l, uv in weights.items():
        if l > 1:
            by_w.setdefault(uv, []).append(l)
    groups = [(u, v, ls) for (u, v), ls in sorted(by_w.items())]
    writes = _write_sequences(seq, lmax, dmax)
    # the estimate's offset c: every window's tokens within the four rendered ones
    starts = [off[i] for i in range(seq.a, seq.b + 2)]
    import bisect

    span_tok = {}
    for b0 in set(b0_of.values()):
        want = expect(b0)
        last = max((j for j, w in enumerate(want) if w is not None), default=None)
        if last is None:
            continue
        span_tok[b0] = (seq.a + bisect.bisect_right(starts, b0) - 1, seq.a + bisect.bisect_right(starts, b0 + last) - 1)
    best = None
    for k in range(-128, 129):
        c = k / 32
        m = Model(seq, weights, segs, groups, c, lmax, dmax, writes)
        miss = sum(not (m.first(b0)[0] <= f and m.first(b0)[0] + TOKENS - 1 >= l) for b0, (f, l) in span_tok.items())
        if best is None or miss < best[0]:
            best = (miss, c)
    c = best[1]
    m = Model(seq, weights, segs, groups, c, lmax, dmax, writes)
    bad = {}
    for b0 in span_tok:
        got, _t = m.render(b0, 64)
        want = expect(b0)
        if any(w is not None and g != w for g, w in zip(got, want)):
            bad[b0] = want
    if len(bad) > 16:
        raise CompileError(f"fmtseq: {len(bad)} windows off the closed forms")
    # cell span relative to the window start
    lo = hi = 0
    for b0 in b0_of.values():
        for _i, t in m.ends(b0, 0):
            lo, hi = min(lo, t), max(hi, t + lmax + 1)
    buf = -lo
    return Plan(seq, weights, segs, groups, c, lmax, dmax, buf, 0, (0, hi - lo), writes,
                {b0: [w if w is not None else 0 for w in want] for b0, want in bad.items()}, dict(b0_of))


# ------------------------------------------------------------------ program
def _program(p: Plan, fit, space_out):
    from .generate import bitgather_value, bitlinear_value
    from .select import Constants

    prog = VProgram()
    consts = Constants(prog)

    pool = {}  # f32 constant -> value (immediates and derived)

    def fc(x):
        x = f32(x)
        if x not in pool:
            pool[x] = consts.word32(int(np.float32(x).view(np.uint32)), label=repr(x))
        return pool[x]

    def fd(x):
        """A constant computed on the MAU from constants at hand when exact (a + b, a - b,
        a * b), else an immediate."""
        x = f32(x)
        if x in pool:
            return pool[x]
        items = list(pool.items())
        for a, va in items:
            for b, vb in items:
                for opc, val, srcs in (("fvadd", a + b, [Use(va), Use(vb)]), ("fvadd", a - b, [Use(va), Use(vb, neg=True)]),
                                       ("fvmul", a * b, [Use(va), Use(vb)])):
                    if val == x and f32(val) == x:
                        pool[x] = mau(opc, *srcs)
                        return pool[x]
        return fc(x)  # (no a * b + c: three constants in two GRF banks always clash)

    def op(opcode, srcs, unit, **kw):
        v = VOp(opcode, srcs, out=kw.pop("out", Value(2)), unit=unit, **kw)
        prog.add(v)
        return v.out

    def mau(opcode, *srcs, **kw):
        return op(opcode, list(srcs), "mau", **kw)

    def alu(opcode, *srcs, **kw):
        return op(opcode, list(srcs), "alu", **kw)

    def flagged(opcode, srcs, unit):
        fl = Value(0, "flags")
        prog.add(VOp(opcode, srcs, out=Value(2), unit=unit, flags_out=fl))
        return fl

    def merged(opcode, srcs, flags, base, unit):
        out = Value(2)
        out.nofwd = True
        prog.add(VOp(opcode, srcs, out=out, unit=unit, write_mask=FlagUse(flags), merge_into=base))
        return out

    seq = p.seq
    # window byte offset b0 = sum over the fixed operands F of f_F(F), f_F linear in the bits of F:
    # f_F(F) = sum_b a_b floor(F / 2^b) with a_b = c_b - 2 c_(b-1). In f32 on the (still idle) MAU:
    # F to float by the 2^23 trick, floor(F / 2^b) by a multiply and a floor.
    c0, ch, bits = fit[0], fit[1], fit[2:]
    magic = fc(MAGIC)
    if ch:
        raise CompileError("fmtseq: windows differ between the halves")
    fields = (("peid", bits[0:6]), ("l1bid", bits[6:9]), ("l2bid", bits[9:12]))
    terms = []
    for name, cs in fields:
        a = [cs[0]] + [cs[b] - 2 * cs[b - 1] for b in range(1, len(cs))]
        if not any(a):
            continue
        Ff = mau("fvadd", Use(alu("ior", Fixed(name), Use(magic))), Use(magic, neg=True))
        for b, ab in enumerate(a):
            if ab:
                x = Ff if b == 0 else alu("ffloor", Use(mau("fvmul", Use(Ff), Use(fc(2.0 ** -b)))))
                terms.append((float(ab), x))
    b0f = None
    if c0:
        terms.append((1.0, fc(float(c0))))
    for coef, x in terms:
        if b0f is None:
            b0f = x if coef == 1.0 else mau("fvmul", Use(x), Use(fd(coef)))
        else:
            b0f = mau("fvadd", Use(x if coef == 1.0 else mau("fvmul", Use(x), Use(fd(coef)))), Use(b0f))
    b0i = None
    if p.patches:
        b0i = bitgather_value(prog, consts, fit) or bitlinear_value(prog, consts, c0, ch, bits)
    # segment constants: X = K_seg - b0 and the estimate's argument as masked-merge chains
    D0, _o, K0, R0 = p.segs[0]
    one = fc(1.0)
    flags_seg = [flagged("fvadd", [Use(b0f), Use(fc(float(o)), neg=True)], "mau") for _D, o, _K, _R in p.segs[1:]]
    D = mau("fvpassa", Use(fc(float(D0)))) if len(p.segs) > 1 else fc(float(D0))
    X = mau("fvadd", Use(fc(float(K0))), Use(b0f, neg=True))
    for fl, (_D, _o, Kn, _R) in zip(flags_seg, p.segs[1:]):
        D = merged("fvadd", [Use(D), Use(one)], fl, D, "mau")
        X = merged("fvadd", [Use(fc(float(Kn))), Use(b0f, neg=True)], fl, X, "mau")
    # (two-operand forms throughout: a third GRF operand would clash on a read port)
    P = mau("fvmul", Use(X), Use(fc(R0)))
    for fl, (_D, _o, _K, Rn) in zip(flags_seg, p.segs[1:]):
        P = merged("fvmul", [Use(X), Use(fc(Rn))], fl, P, "mau")
    i0 = alu("ffloor", Use(mau("fvadd", Use(fc(p.c)), Use(P, neg=True))))
    # the four tokens (one per cycle)
    cyc = _cycle_vector(prog, consts, [float(k) for k in range(TOKENS)])
    iv = mau("fvadd", Use(i0), Use(cyc))
    u1, v1 = p.weights.get(1, (0, 0))
    if v1 == 0 and u1 == 0:
        B = mau("fvadd", Use(D), Use(one))
    else:
        B = mau("fvfma", Use(D), Use(fc(float(1 - v1))), Use(fc(float(1 + u1))))
    Y = mau("fvadd", Use(X), Use(fc(float(p.buf - 1 - p.lmax))))
    t = mau("fvadd", Use(Y), Use(B))
    G = {}

    def floor_div(m):
        if m not in G:
            G[m] = alu("ffloor", Use(mau("fvmul", Use(iv), Use(fc(_inv(m))))))
        return G[m]

    for u, v, ls in p.groups:
        s = floor_div(ls[0])
        for l in ls[1:]:
            s = mau("fvadd", Use(s), Use(floor_div(l)))
        if v == 0:
            w = fc(float(u))
        elif v == -1 and u == 0:
            w = D
        elif v == 1:
            w = mau("fvadd", Use(fc(float(u))), Use(D, neg=True))
        else:
            w = mau("fvfma", Use(D), Use(fc(float(-v))), Use(fc(float(u))))
        t = mau("fvfma", Use(w), Use(s), Use(t))  # s fresh, t forwarded
    t = mau("fvfma", Use(B), Use(iv), Use(t))
    trange = (p.cell0, p.cell0 + p.span[1])
    prog.add(VOp("fftoi", [Use(t)], dsts=[Mem("t", 4)], unit="alu", note="token ends"))
    # divisibility flags: m * floor(i / m) - i >= 0 exactly when m | i
    flags = {m: flagged("fvadd", [Use(mau("fvmul", Use(floor_div(m)), Use(fd(float(m))))), Use(iv, neg=True)], "mau") for m in seq.moduli}
    # digits: F_k = floor(i * 10^-k); digit j (most significant first) is F_q - 10 F_(q+1) with
    # q = dmax - 1 - j, and its cell gets that plus 2^23 + '0'
    dmax = p.dmax
    scale = {1: fc(f32(0.1))}
    for k in range(2, dmax):
        scale[k] = mau("fvmul", Use(scale[k - 1]), Use(scale[1]))  # = scale_val(k)
    ten = fd(10.0)
    m48 = fc(MAGIC + 48)
    F = {0: iv}
    for k in range(1, dmax):
        F[k] = alu("ffloor", Use(mau("fvmul", Use(iv), Use(scale[k]))))
    chars = {}

    def char(ch):
        if ch not in chars:
            chars[ch] = fc(MAGIC + ch)
        return chars[ch]

    def cell(rel):
        return Mem("lm0", 1, (p.cell0 + rel,) * 4, tind=True, trange=trange)

    for rel, seqw in enumerate(p.writes):
        for value, mod in seqw:
            wm = FlagUse(flags[mod]) if mod is not None else None
            if value[0] == "digit":
                q = dmax - 1 - value[1]
                pre = F[q] if q == dmax - 1 else mau("fvadd", Use(mau("fvmul", Use(F[q + 1]), Use(ten, neg=True))), Use(F[q]))
                prog.add(VOp("fvadd", [Use(pre), Use(m48)], dsts=[cell(rel)], unit="mau", write_mask=wm, note="digit"))
            else:
                # a bit copy on the ALU (the MAU computes the digits meanwhile)
                prog.add(VOp("fvpassa", [Use(char(value[1]))], dsts=[cell(rel)], unit="mau", write_mask=wm, note="char",
                             alt=("lpassa", "alu")))
    # pack the window (cycle 0: bytes 0-3, cycle 1: bytes 4-7) into the long word of the upload chain
    w0 = p.cell0 + p.buf

    def win(j):
        return Mem("lm0", 1, (w0 + j, w0 + 4 + j, w0 + j, w0 + 4 + j))

    eight = consts.word32(8)
    acc = alu("ilsl", win(0), Use(eight))
    for j in (1, 2):
        acc = alu("ilsl", Use(alu("ior", Use(acc), win(j))), Use(eight))
    low = alu("isub", win(3), Use(magic))  # the last character without the 2^23 exponent bits
    out_mem = Mem(space_out[0], 1, (2 * space_out[1], 2 * space_out[1] + 1) * 2, mask=Mask(pattern="1100"))
    prog.add(VOp("ior", [Use(acc), Use(low)], dsts=[out_mem], unit="alu", note="pack"))
    # windows the closed forms miss
    for b0, data in sorted(p.patches.items()):
        fl = flagged("ixor", [Use(b0i), Use(consts.word32(b0))], "alu")
        word = int.from_bytes(bytes(data), "big")
        for half, val in ((0, word >> 32), (1, word & 0xFFFFFFFF)):
            prog.add(VOp("imm", [Imm("ui", "0x%08X" % val)], dsts=[Mem(space_out[0], 1, (2 * space_out[1] + half,) * 4)],
                         unit="alu", write_mask=FlagUse(fl), note="patch"))
    return prog


def _cycle_vector(prog, consts, values):
    """A GRF vector holding a different f32 constant in each cycle."""
    homes = [consts._home() for _ in values]
    bank, a = homes[0]
    if any(h != (bank, a + 2 * k) for k, h in enumerate(homes)):
        raise CompileError("fmtseq: no consecutive GRF words for a cycle vector")
    v = Value(2, "cycles", home=Mem(bank, 2, tuple(a + 2 * k for k in range(4))))  # not "c:": rebalancing would move one word
    v.nofwd = True
    for k, x in enumerate(values):
        o = VOp("imm", [Imm("f", repr(float(x)))], dsts=[Mem(bank, 2, (a + 2 * k,) * 4)], unit="alu", note="cycle vector")
        if k == len(values) - 1:
            o.out = v
        prog.add(o)
    return v


# ------------------------------------------------------------------ strategy
def fmtseq_strategy(source, contract, outputs, *, variant=None):
    from .generate import _fit, _spread, _spread_pdm
    from .hier import _scratch
    from .schedule import schedule
    from .sim import assembler

    if len(contract.outputs) != 1:
        raise CompileError("fmtseq: one output")
    out = contract.outputs[0]
    if out.space != "dram" or out.dtype.kind != "bytes" or out.dtype.bits != 8:
        raise CompileError("fmtseq: byte string in DRAM")
    nodes = outputs[out.name]
    if any(n.op != "const" for n in nodes.values()):
        raise CompileError("fmtseq: output depends on the inputs")
    by_index = {idx[0]: int(n.value) if not isinstance(n.value, (bytes, str)) else ord(n.value) for idx, n in nodes.items()}
    n = max(by_index) + 1
    if set(by_index) != set(range(n)):
        raise CompileError("fmtseq: holes in the string")
    data = bytes(by_index[i] for i in range(n))
    seq = analyze(data)
    # which PE carries which DRAM long word
    words = {}
    for idx in nodes:
        loc = out.locations(idx, replicate=False)[0]
        words[(loc.pe, loc.addr)] = (loc.pe, loc.addr)
    space, base = _scratch(contract)
    if space != "lm1":
        raise CompileError("fmtseq: LM1 needed for the upload words")

    def expect(b0):
        return [by_index.get(b0 + j) for j in range(WINDOW)]

    asm = assembler()
    results = []
    for cname, planner in (("pdm", _spread_pdm), ("l2b", _spread)):
        try:
            hops, pereq = planner(words, base, space)
        except CompileError:
            continue
        addrs = {a for _pe, a in pereq}
        if len(addrs) != 1:
            continue
        (addr,) = addrs
        b0_of = {}
        for (pe, _a), (g, d) in pereq.items():
            b0_of[pe] = 8 * (d - out.base_long)
        if any(g != 0 for g, _d in pereq.values()):
            continue
        fit = _fit([(pe, h, b0) for pe, b0 in b0_of.items() for h in (0, 1)])
        if fit is None:
            continue
        pl = plan(seq, b0_of, expect)
        if pl.span[1] > 4096:
            continue
        prog = _program(pl, fit, (space, addr))
        steps = schedule(prog, asm, tries=8)
        for hop in hops:
            if hop:
                steps.append(Step(nop=3))
                steps += [Step([ins]) for ins in hop]
        results.append((f"render-{cname}/{len(pl.patches)}p", steps))
    if not results:
        raise CompileError("fmtseq: no upload chain")
    return results
