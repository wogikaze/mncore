#!/usr/bin/env python3
"""v6 lane model: like model3 but (a) the delta lines are slightly perturbed so that the first fmax
yields the digit flags [n>=1000, n>=10], (b) digits are assembled as UA (flags [n>=100, 1]) + UB."""
import numpy as np
from model import stream, NBLK
from model2 import TXT6
import model3
from model3 import r32, fma, MG, MASK64, EZ2, lanes
f32 = np.float32

DEFAULT = dict(
    lines=model3.DEFAULT["lines"],
    c10=float(np.array([0x3DCCCD0C], ">u4").view(">f4")[0]),
    # (slope in u', intercept): l3, l1', l4', l2'
    Y=((-1.0, -65.5), (-3.0, -8.5 + 1 / 32)),
    X=((-(2.0 ** -18), -598.0), (-2.0, -13.0 + 1 / 64)),
)

def run(P=DEFAULT):
    B, k = lanes()
    o = {}
    (a2, b2), (a3, b3), (a4, b4) = P["lines"]
    A4 = float(f32(a4)) * 8.0
    l2 = fma(B, a2 * 8.0, b2); l3 = fma(B, a3 * 8.0, b3); l4 = fma(B, A4, b4)
    y = np.minimum(np.minimum(l2, l3), l4)
    yr = r32(y - MG)
    m = r32(yr + (MG + k)); o["m"] = m
    mq = r32(m * (1.0 / 16.0)); q = np.floor(mq); n = r32(m - q); i = (m - 16 * q).astype(int)
    o["q"] = q; o["n"] = n; o["i"] = i
    u16 = fma(m, 8.0, 16.0 * EZ2[i]); o["u16"] = u16
    # ---- position: Y = [l3, l1'], X = [l4', l2'] as functions of u16 ----
    Yv = [fma(u16, sl / 16.0, ic) for sl, ic in P["Y"]]
    Xv = [fma(u16, sl / 16.0, ic) for sl, ic in P["X"]]
    fl = (Xv[0] >= Yv[0], Xv[1] >= Yv[1])                    # [g3, g1] from fmax(X, Y)
    pq = (np.maximum(Xv[0], Yv[0]), np.maximum(Xv[1], Yv[1]))
    Dw = np.maximum(pq[0], pq[1])
    R0 = fma(B, -8.0, -q); R1 = fma(m, 5.0, R0)
    S = r32(Dw + R1); o["S"] = S
    amr = np.where(S >= 0, fma(S, 8.0, MG), 0.0)
    aml = np.where(S <= 0, fma(S, -8.0, MG), 0.0)
    ar = np.where(amr > 0, amr - MG, 0).astype(np.int64) % 128
    al = np.where(aml > 0, aml - MG, 0).astype(np.int64) % 128
    o["s"] = np.rint(S)
    # ---- digits ----
    c10 = float(f32(P["c10"])); c100 = float(f32(c10 * c10))
    R1d = (r32(n * c100), r32(n * c10))
    S1 = (np.floor(R1d[0]), np.floor(R1d[1]))                 # [f2, f1]
    S2 = (np.floor(r32(S1[0] * c10)), np.floor(r32(S1[1] * c10)))   # [f3, f2]
    FA = (r32(R1d[0] - 1.0) >= 0, r32(R1d[1] + 5.0) >= 0)     # [g2, 1]
    N1 = (np.full_like(n, 192.0), r32(n + 48.0625))
    UA = (np.where(FA[0], fma(S1[0], 4.0, N1[0]), 0.0), np.where(FA[1], fma(S1[1], 246.0, N1[1]), 0.0))
    UB = (np.where(fl[0], fma(S2[0], 984.0, 49152.0), 0.0), np.where(fl[1], fma(S2[1], -2560.0, 12288.0), 0.0))
    Ys = (r32(UA[0] + UB[0]), r32(UA[1] + UB[1]))
    Yv2 = (fma(Ys[0], 0.25, 0.0), fma(Ys[1], 65536.0, -1536.0))
    o["Ys"] = Ys
    thi = np.zeros(16); tlo = np.zeros(16); istext = np.zeros(16, bool)
    for t, (hi, lo) in TXT6.items():
        thi[t] = hi; tlo[t] = lo; istext[t] = True
    V2 = (np.where(istext[i], thi[i], Yv2[0]), np.where(istext[i], tlo[i], Yv2[1]))
    V = (V2[0].astype(np.uint64) << np.uint64(32)) | V2[1].astype(np.uint64)
    o["V"] = V
    out = np.zeros(len(B), dtype=np.uint64)
    for idx in range(len(B)):
        v = int(V[idx]); a = int(ar[idx]); b = int(al[idx])
        t = (v >> a) if a < 64 else 0
        t = ((t << b) & MASK64) if b < 64 else 0
        out[idx] = t
    o["F"] = out
    return o

def check(P=DEFAULT, o=None):
    return model3.check(P, o or run(P))

if __name__ == "__main__":
    o = run(); b = check(o=o)
    print("bad", len(b), b[:10])
    S = o["S"]; print("max |S - rint(S)|:", float(np.max(np.abs(S - np.rint(S)))))
