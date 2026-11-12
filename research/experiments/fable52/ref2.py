#!/usr/bin/env python3
"""Float32-accurate reference of the per-lane pipeline (one lane = block B, role k).

Mirrors the planned instruction sequence; every multiply-add is rounded once to
float32 like the MAU, floors are exact (ALU ffloor).
"""
from fractions import Fraction as Fr
import struct
from ref import NNLE_I, MASK64, want, region
from model import NBLK

def f32r(x):
    """round an exact rational to the nearest float32 (ties to even), returned as Fraction."""
    if x == 0:
        return Fr(0)
    f = struct.unpack(">f", struct.pack(">f", float(x)))[0]
    # float(x) is correctly rounded to double; double->single can double-round only in
    # pathological cases, which we guard against by checking neighbours exactly.
    best = Fr(f)
    bits = struct.unpack(">I", struct.pack(">f", f))[0]
    for b in (bits - 1, bits + 1):
        cand = Fr(struct.unpack(">f", struct.pack(">I", b))[0])
        if abs(cand - x) < abs(best - x):
            best = cand
    return best

def fma(a, b, c):
    return f32r(Fr(a) * Fr(b) + Fr(c))

def fl(x):
    return Fr(x.numerator // x.denominator)

def c32(x):
    return Fr(struct.unpack(">f", struct.pack(">f", x))[0])

# region parameters, index d = 1..4
A_D = {1: Fr(1, 4), 2: Fr(1, 4), 3: c32(16 / 71), 4: c32(16 / 79)}
CST = {1: 4, 2: 9, 3: 62, 4: 595}
E_D = {1: 3, 2: 2, 3: 1, 4: 0}
BIAS = {1: (0x0000, 0x00300A00), 2: (0x0000, 0x30300A00), 3: (0x0030, 0x30300A00), 4: (0x3030, 0x30300A00)}
C10 = Fr(struct.unpack(">f", struct.pack(">I", 0x3DCCCCCD))[0])
C100 = Fr(struct.unpack(">f", struct.pack(">I", 0x3C23D70B))[0])
C1000 = Fr(struct.unpack(">f", struct.pack(">I", 0x3A83126F))[0])
TEXT_I = {}
for i in range(16):
    if i in (3, 6, 9, 12):
        TEXT_I[i] = (0x4669, 0x7A7A0A00)
    elif i == 15:
        TEXT_I[i] = (0x4669, 0x7A7A0000)
    elif i in (0, 5, 10):
        TEXT_I[i] = (0x4275, 0x7A7A0A00)

def lane(B, k, d=None, params=None):
    """64-bit contribution of role k for block B (region d of the block)."""
    d = d or region(B)
    X = Fr(8 * B)
    xt = X + CST[d]
    zf = fma(xt, A_D[d], k)
    m = fl(zf)
    q = fl(fma(m, Fr(1, 16), 0))
    n = m - q
    i = int(m) % 16
    if i in TEXT_I:
        hi, lo = TEXT_I[i]
    else:
        f1 = fl(fma(n, C10, 0)); f2 = fl(fma(n, C100, 0)); f3 = fl(fma(n, C1000, 0))
        bh, bl = BIAS[d]
        hi = int(f2 + 246 * f3 + bh)
        lo = int(65536 * (n + 246 * f1 - 2560 * f2) + bl)
    V = ((hi & 0xffffffff) << 32) | (lo & 0xffffffff)
    e = E_D[d]
    s = 8 * int(5 * m - q - e * (8 * q + NNLE_I[i]) - xt - 3)
    ra = s % 128
    A = (V >> ra) if ra < 64 else 0
    la = (-s) % 128
    Bv = ((V << la) & MASK64) if (la < 64 and s <= 0) else 0
    return A | Bv, int(m)

def block(B):
    out = 0
    for k in range(4):
        v, m = lane(B, k)
        if m >= 1:
            out |= v
    return out

if __name__ == "__main__":
    bad = []
    for B in range(NBLK):
        w, ln = want(B)
        mask = MASK64 if ln == 8 else (MASK64 >> (8 * ln)) ^ MASK64
        if (block(B) & mask) != w:
            bad.append(B)
    print("bad blocks:", len(bad), bad[:30])
