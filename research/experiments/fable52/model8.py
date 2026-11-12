#!/usr/bin/env python3
"""v8 lane model.  On top of model7:
  * estimator lines are rounded individually (integer intercepts, bias -MG inside the fma): yr = min_d RNE(a_d' B + j_d) - MG
  * digits (variant a): R1' = n*[c100, c10] - [1, -1] -> S1' = [f2-1, f1+1]; R2 = S1'*c10 + [c10, -c10] -> S2 = [f3, f2];
    UA = flush(S1'*[4, 246] + [196, n]) (no separate N1 op); the '0'/newline constant of the low word lives in NL = [0, 12973568]
"""
import numpy as np
from model import stream, NBLK
from model2 import TXT6
import model3
from model3 import r32, fma, MG, MASK64, EZ2, lanes
f32 = np.float32
NLV = 65536.0 * 198.0 - 2560.0            # 12973568

DEFAULT = dict(
    lines=((0.255859375, 1.0), (0.225341796875, 13.0), (0.20254512131214142, 119.0)),
    c10=float(np.array([0x3DCCCD07], ">u4").view(">f4")[0]),
    Y=((-1.0, -65.5), (-3.0, -8.5 + 1 / 32)),
    X=((-(2.0 ** -18), -598.0), (-2.0, -13.0 + 1 / 64)),
)

def run(P=DEFAULT):
    B, k = lanes()
    o = {}
    (a2, b2), (a3, b3), (a4, b4) = P["lines"]
    A4 = float(f32(a4)) * 8.0
    l2 = fma(B, a2 * 8.0, b2 - MG); l3 = fma(B, a3 * 8.0, b3 - MG); l4 = fma(B, A4, b4 - MG)
    yr = np.minimum(np.minimum(l2, l3), l4)
    m = r32(yr + (MG + k)); o["m"] = m
    n = np.floor(fma(m, 15.0 / 16.0, 15.0 / 16.0)); o["n"] = n
    i = (m % 16).astype(int); o["i"] = i
    u16 = fma(m, 8.0, 16.0 * EZ2[i]); o["u16"] = u16
    # ---- position ----
    Yv = [fma(u16, sl / 16.0, ic) for sl, ic in P["Y"]]
    Xv = [fma(u16, sl / 16.0, ic) for sl, ic in P["X"]]
    fl = (Xv[0] >= Yv[0], Xv[1] >= Yv[1])                    # [n>=1000, n>=10]
    pq = (np.maximum(Xv[0], Yv[0]), np.maximum(Xv[1], Yv[1]))
    Dw = np.maximum(pq[0], pq[1]); o["Dw"] = Dw
    W = fma(m, 4.0, -8.0 * B)
    r = r32(n + W); o["r"] = r
    Sp = (r32(-Dw - r), r32(r + Dw)); o["Sp"] = Sp
    am0 = np.where(Sp[0] >= 0, fma(Sp[0], 8.0, MG), 0.0)
    am1 = np.where(Sp[1] >= 0, fma(Sp[1], 8.0, MG), 0.0)
    ar = np.where(am1 > 0, am1 - MG, 0).astype(np.int64) % 128
    al = np.where(am0 > 0, am0 - MG, 0).astype(np.int64) % 128
    o["s"] = np.rint(Sp[1])
    # ---- digits ----
    c10 = float(f32(P["c10"])); c100 = float(f32(c10 * c10))
    R1 = (fma(n, c100, -1.0), fma(n, c10, 1.0))
    FA = (R1[0] >= 0, R1[1] >= 0)                            # [n>=100, 1]
    S1 = (np.floor(R1[0]), np.floor(R1[1]))                  # [f2-1, f1+1]
    XC = (float(f32(c10)), float(f32(-c10)))
    S2 = (np.floor(fma(S1[0], c10, XC[0])), np.floor(fma(S1[1], c10, XC[1])))   # [f3, f2]
    o["S1"] = S1; o["S2"] = S2; o["FA"] = FA; o["fl"] = fl
    UA = (np.where(FA[0], fma(S1[0], 4.0, 196.0), 0.0), np.where(FA[1], fma(S1[1], 246.0, n), 0.0))
    UB = (np.where(fl[0], fma(S2[0], 984.0, 49152.0), 0.0), np.where(fl[1], fma(S2[1], -2560.0, 12288.0), 0.0))
    Ys = (r32(UA[0] + UB[0]), r32(UA[1] + UB[1]))
    Yv2 = (fma(Ys[0], 0.25, 0.0), fma(Ys[1], 65536.0, -NLV))
    o["Ys"] = Ys
    thi = np.zeros(16); tlo = np.zeros(16); istext = np.zeros(16, bool)
    for t, (hi, lo) in TXT6.items():
        thi[t] = hi; tlo[t] = lo; istext[t] = True
        assert float(f32(lo + NLV)) == lo + NLV and float(f32(-(lo + NLV) + NLV)) == -lo
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
    S = o["Sp"][1]; print("max |S - rint(S)|:", float(np.max(np.abs(S - np.rint(S)))))
    n = o["n"]
    f2 = np.floor(n / 100); f1 = np.floor(n / 10); f3 = np.floor(n / 1000)
    print("S1 ok", bool(np.all(o["S1"][0] == f2 - 1) and np.all(o["S1"][1] == f1 + 1)), "S2 ok", bool(np.all(o["S2"][0] == f3) and np.all(o["S2"][1] == f2)),
          "FA ok", bool(np.all(o["FA"][0] == (n >= 100)) and np.all(o["FA"][1])), "n range", float(n.min()), float(n.max()), "m range", float(o["m"].min()), float(o["m"].max()))
