#!/usr/bin/env python3
"""v14 lane model.  On top of model9:
  * digit offsets X = [1, 0]: R1' = n*[c100, c10] - [1, 0] -> S1' = [f2-1, f1]; R2 = S1'*c10 + [c10, 0] -> [f3, f2];
    UA = flush(S1'*[0.25, 246] + [12.25, n]); V2 = (UA + UB)*[4, 65536] + [0, 3148288]
  * text / number selection is an ALU fmax against the table (text chars are larger than any digit chars)
"""
import numpy as np
from model import stream, NBLK
from model2 import TXT6
import model3, model9
from model3 import r32, fma, MG, MASK64, EZ2, lanes
f32 = np.float32
NLP = 65536.0 * 48.0 + 2560.0             # 3148288

DEFAULT = dict(model9.DEFAULT)

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
    fl = (Xv[0] >= Yv[0], Xv[1] >= Yv[1])
    pq = (np.maximum(Xv[0], Yv[0]), np.maximum(Xv[1], Yv[1]))
    Dw = np.maximum(pq[0], pq[1])
    W = fma(m, 4.0, -8.0 * B)
    r = r32(n + W)
    Sp = (r32(-Dw - r), r32(r + Dw)); o["Sp"] = Sp
    am0 = np.where(Sp[0] >= 0, fma(Sp[0], 8.0, MG), 0.0)
    am1 = np.where(Sp[1] >= 0, fma(Sp[1], 8.0, MG), 0.0)
    ar = np.where(am1 > 0, am1 - MG, 0).astype(np.int64) % 128
    al = np.where(am0 > 0, am0 - MG, 0).astype(np.int64) % 128
    # ---- digits ----
    c10 = float(f32(P["c10"])); c100 = float(f32(c10 * c10))
    R1 = (fma(n, c100, -1.0), fma(n, c10, -0.0))
    FA = (R1[0] >= 0, R1[1] >= 0)
    S1 = (np.floor(R1[0]), np.floor(R1[1]))                  # [f2-1, f1]
    XC = (float(f32(c10)), 0.0)
    S2 = (np.floor(fma(S1[0], c10, XC[0])), np.floor(fma(S1[1], c10, XC[1])))   # [f3, f2]
    o["S1"] = S1; o["S2"] = S2; o["FA"] = FA
    UA = (np.where(FA[0], fma(S1[0], 0.25, 12.25), 0.0), np.where(FA[1], fma(S1[1], 246.0, n), 0.0))
    UB = (np.where(fl[0], fma(S2[0], 61.5, 3072.0), 0.0), np.where(fl[1], fma(S2[1], -2560.0, 12288.0), 0.0))
    Ys = (r32(UA[0] + UB[0]), r32(UA[1] + UB[1]))
    V2n = (fma(Ys[0], 4.0, 0.0), fma(Ys[1], 65536.0, NLP))
    thi = np.zeros(16); tlo = np.zeros(16)
    for t, (hi, lo) in TXT6.items():
        thi[t] = hi; tlo[t] = lo
    V2 = (np.maximum(V2n[0], thi[i]), np.maximum(V2n[1], tlo[i]))      # ALU fmax against the table
    o["V2n"] = V2n; o["tsel"] = (thi[i], tlo[i])
    V = (V2[0].astype(np.uint64) << np.uint64(32)) | V2[1].astype(np.uint64)
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
    n = o["n"]; i = o["i"]
    f2 = np.floor(n / 100); f1 = np.floor(n / 10); f3 = np.floor(n / 1000)
    istext = o["tsel"][0] > 0
    print("S1 ok", bool(np.all(o["S1"][0] == f2 - 1) and np.all(o["S1"][1] == f1)), "S2 ok", bool(np.all(o["S2"][0] == f3) and np.all(o["S2"][1] == f2)))
    print("text lanes: number garbage below text:", bool(np.all(o["V2n"][0][istext] < o["tsel"][0][istext]) and np.all(o["V2n"][1][istext] < o["tsel"][1][istext])),
          "| number lanes non-negative:", bool(np.all(o["V2n"][0][~istext] >= 0) and np.all(o["V2n"][1][~istext] > 0)),
          "| max garbage", float(o["V2n"][0][istext].max()), float(o["V2n"][1][istext].max()))
