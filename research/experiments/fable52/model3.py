#!/usr/bin/env python3
"""v3 lane model (vectorised, float32-exact for this pipeline).

Every MAU op is emulated as float64 arithmetic followed by one rounding to float32; all the
intermediate sums here fit in 53 bits, so that is exactly the hardware's single rounding.
`run(P)` returns a dict of named intermediates (pairs as (e0, e1) float32 arrays over lanes)
plus the final 64-bit lane words; `check(P)` ORs the 4 candidates and compares with the stream.
"""
import numpy as np
from model import stream, NBLK
from model2 import TXT6

f32 = np.float32
MG = 1.5 * 2.0 ** 23
MASK64 = (1 << 64) - 1

def r32(x):
    return np.asarray(x, dtype=np.float64).astype(np.float32).astype(np.float64)
def fma(a, b, c):
    return r32(np.asarray(a, np.float64) * np.asarray(b, np.float64) + np.asarray(c, np.float64))
def bits(x):
    return np.asarray(x, dtype=np.float32).view(np.uint32).astype(np.uint64)

def c10_default():
    return float(np.array([0x3DCCCCCD], ">u4").view(">f4")[0])

DEFAULT = dict(
    lines=((0.251953125, 1.359375), (0.225341796875, 13.21875), (0.20253394544124603, 119.375)),
    c10=c10_default(),
    D=((-1.0, -65.5), (-2.0, -13.0), (-3.0, -8.5), (0.0, -598.0)),   # (slope, intercept) in u'
    E=6,
)
EZ2 = np.array([(-0.5 if i in (0, 6, 10, 12) else 0.5) if i % 2 == 0 else 0.0 for i in range(16)])

def lanes():
    B = np.repeat(np.arange(NBLK), 4).astype(np.float64)
    k = np.tile(np.arange(4), NBLK).astype(np.float64)
    return B, k

def run(P=DEFAULT):
    B, k = lanes()
    o = {}
    # ---- estimator on B (slopes are 8x the per-byte slopes) ----
    (a2, b2), (a3, b3), (a4, b4) = P["lines"]
    A4 = float(f32(a4)) * 8.0
    l2 = fma(B, a2 * 8.0, b2); l3 = fma(B, a3 * 8.0, b3); l4 = fma(B, A4, b4)
    y = np.minimum(np.minimum(l2, l3), l4)
    o["y"] = y
    yr = r32(y - MG)                      # RNE(y) - MG
    m = r32(yr + (MG + k))
    o["m"] = m
    mq = r32(m * (1.0 / 16.0)); q = np.floor(mq); n = r32(m - q); i = (m - 16 * q).astype(int)
    o["q"] = q; o["n"] = n; o["i"] = i
    u = fma(mq, 8.0, EZ2[i]); o["u"] = u
    # ---- digits ----
    c10 = float(f32(P["c10"])); c100 = float(f32(c10 * c10))
    o["c100"] = c100
    S1 = (np.floor(r32(n * c100)), np.floor(r32(n * c10)))             # [f2, f1]
    S2 = (np.floor(r32(S1[0] * c10)), np.floor(r32(S1[1] * c10)))      # [f3, f2]
    o["S1"] = S1; o["S2"] = S2
    R1 = (r32(n * c100), r32(n * c10))
    F1 = (fma(R1[0], 8.0, -8.0) >= 0, fma(R1[1], 8.0, -8.0) >= 0)       # [g2, g1]
    F2 = (r32(R1[0] - 10.0) >= 0, r32(R1[1] + 5.0) >= 0)                # [g3, 1]
    N1 = (np.full_like(n, 49152.0), r32(n + 48.0625))
    TA = (np.where(F2[0], fma(S2[0], 984.0, N1[0]), 0.0),
          np.where(F2[1], fma(S2[1], -2560.0, N1[1]), 0.0))
    TB = (np.where(F1[0], fma(S1[0], 4.0, 192.0), 0.0),
          np.where(F1[1], fma(S1[1], 246.0, 12288.0), 0.0))
    Ys = (r32(TA[0] + TB[0]), r32(TA[1] + TB[1]))
    Yv = (fma(Ys[0], 0.25, 0.0), fma(Ys[1], 65536.0, -1536.0))
    o["N1"] = N1; o["Ys"] = Ys
    o["TA"] = TA; o["TB"] = TB; o["Yv"] = Yv
    # ---- text ----
    thi = np.zeros(16); tlo = np.zeros(16); istext = np.zeros(16, bool)
    for t, (hi, lo) in TXT6.items():
        thi[t] = hi; tlo[t] = lo; istext[t] = True
    V2 = (np.where(istext[i], thi[i], Yv[0]), np.where(istext[i], tlo[i], Yv[1]))
    o["V2"] = V2
    V = (V2[0].astype(np.uint64) << np.uint64(32)) | V2[1].astype(np.uint64)
    o["V"] = V
    # ---- position ----
    D = [fma(u, sl, ic) for sl, ic in P["D"]]
    Dw = np.maximum(np.maximum(D[0], D[1]), np.maximum(D[2], D[3]))
    R0 = fma(B, -8.0, -q)
    R1 = fma(m, 5.0, R0)
    s = r32(Dw + R1); o["s"] = s
    si = s.astype(np.int64)
    out = np.zeros(len(B), dtype=np.uint64)
    amr = np.where(si >= 0, 8 * si, 0) % 128
    aml = np.where(si <= 0, -8 * si, 0) % 128
    for idx in range(len(B)):
        v = int(V[idx]); a = int(amr[idx]); b = int(aml[idx])
        t = (v >> a) if a < 64 else 0
        t = ((t << b) & MASK64) if b < 64 else 0
        out[idx] = t
    o["F"] = out
    return o

def check(P=DEFAULT, o=None):
    if o is None: o = run(P)
    F = o["F"].reshape(NBLK, 4)
    blk = F[:, 0] | F[:, 1] | F[:, 2] | F[:, 3]
    bad = []
    for b in range(NBLK):
        sb = stream[8 * b: 8 * b + 8].encode("latin-1")
        w = int.from_bytes(sb.ljust(8, b"\0"), "big")
        mask = MASK64 if len(sb) == 8 else MASK64 ^ (MASK64 >> (8 * len(sb)))
        if int(blk[b]) & mask != w: bad.append(b)
    return bad

if __name__ == "__main__":
    o = run()
    b = check(o=o)
    print("bad", len(b), b[:10])
    s = o["s"]; print("s range", s.min(), s.max())
    y = o["y"]; fr = y - np.floor(y)
    print("exact .5 ties in y:", int(np.sum(fr == 0.5)) // 4)
