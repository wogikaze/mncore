#!/usr/bin/env python3
"""brute force: which constants can be produced exactly by one MAU op (fma / mul / add) from the others?"""
import itertools, struct
import numpy as np
import model14
from f32util import hpair
import jopt
def fb(x): return struct.unpack(">I", struct.pack(">f", float(x)))[0]
def f32(b): return struct.unpack(">f", struct.pack(">I", b & 0xffffffff))[0]
def half(h):                                   # MN-Core half: 1 sign, 6 exponent (bias 31), 9 mantissa
    s = -1.0 if h >> 15 else 1.0; e = (h >> 9) & 0x3f; m = h & 0x1ff
    if e == 0 and m == 0: return 0.0 * s
    return s * (1 + m / 512.0) * 2.0 ** (e - 31)
assert half(0x3e00) == 1.0 and half(0x4400) == 8.0 and half(0x4e00) == 256.0
P = dict(model14.DEFAULT)
(a2, b2), (a3, b3), (a4, b4) = P["lines"]
(ys0, yi0), (ys1, yi1) = P["Y"]; (xs0, xi0), (xs1, xi1) = P["X"]
words = dict(MG=jopt.MGB, KBc2=hpair(4, 256), H8=hpair(8, 8), A23=hpair(a3 * 8, a2 * 8), B23=hpair(b3, b2),
             A4=fb(float(np.float32(a4)) * 8), B4=hpair(b4, jopt.BIGV), C10=fb(np.float32(P["c10"])), P_A=hpair(61.5, -2560),
             P_B=hpair(0.25, 246), cUB=hpair(3072, 12288), KBc1=hpair(4, 65536), X=hpair(1, 0), DY=hpair(ys0 / 16, ys1 / 16),
             H1516=hpair(15 / 16, 15 / 16), NLc=fb(model14.NLP), DX=hpair(xs0 / 16, xs1 / 16), IX=hpair(xi0, xi1), IY=hpair(yi0, yi1))
ops = {}                                       # operand name -> (w0, w1) as float32 values
for n, w in words.items():
    ops[n + ":e"] = (half(w >> 16), half(w & 0xffff)); ops[n + ":l"] = (f32(w), f32(w))
ops["A4:w"] = (f32(words["A4"]), 0.0); ops["NLc:w"] = (0.0, f32(words["NLc"]))
c10 = f32(words["C10"]); MG = f32(words["MG"])
ops["CP"] = (float(np.float32(np.float64(c10) * c10)), c10); ops["XC"] = (c10, 0.0)
ops["K1"] = (-73 * MG / 8,) * 2; ops["T9"] = (-9 * MG,) * 2
ops["N23"] = (b3 - MG, b2 - MG); ops["N4"] = (b4 - MG, jopt.BIGV - MG)
def fma(a, b, c): return float(np.float32(np.float64(a) * np.float64(b) + np.float64(c)))   # exact enough for small magnitudes
targets = {"H8": (8.0, 8.0), "H1516": (15 / 16, 15 / 16), "DY": ops["DY:e"], "DX": ops["DX:e"], "IX": ops["IX:e"], "IY": ops["IY:e"],
           "KBc2": (4.0, 256.0), "KBc1": (4.0, 65536.0), "P_A": (61.5, -2560.0), "P_B": (0.25, 246.0), "cUB": (3072.0, 12288.0),
           "B23": ops["B23:e"], "X": (1.0, 0.0), "NLc": (0.0, f32(words["NLc"])), "A4": ops["A4:w"], "C10": (c10, c10),
           "XC": ops["XC"], "CP": ops["CP"], "N23": ops["N23"], "N4": ops["N4"], "K1": ops["K1"], "T9": ops["T9"]}
names = list(ops)
zero = (0.0, 0.0); one = None
for tn, tv in targets.items():
    found = []
    base = [n for n in names if n.split(":")[0] != tn]
    for a in base:
        for b in base:
            if b < a: continue
            pa, pb = ops[a], ops[b]
            for sc in (1, -1):
                prod = [sc * np.float64(pa[i]) * np.float64(pb[i]) for i in (0, 1)]
                if all(float(np.float32(prod[i])) == tv[i] for i in (0, 1)): found.append(f"{'-' if sc < 0 else ''}{a}*{b}")
                for c in base:
                    for s2 in (1, -1):
                        if all(float(np.float32(prod[i] + s2 * np.float64(ops[c][i]))) == tv[i] for i in (0, 1)):
                            found.append(f"{'-' if sc < 0 else ''}{a}*{b}{'+' if s2 > 0 else '-'}{c}")
    for a in base:
        for c in base:
            if c < a: continue
            for s1 in (1, -1):
                for s2 in (1, -1):
                    if all(float(np.float32(s1 * np.float64(ops[a][i]) + s2 * np.float64(ops[c][i]))) == tv[i] for i in (0, 1)):
                        found.append(f"{'+' if s1 > 0 else '-'}{a}{'+' if s2 > 0 else '-'}{c}")
    print(tn, tv, "->", found[:8], f"({len(found)})")
