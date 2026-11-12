#!/usr/bin/env python3
import sys
sys.argv = ["x"]
import gen1
from gen1 import coords, estimator, token, render, ref_m, M23
from chk import dump, lanes
from ref3 import TEXT, Delta, place, Z
import struct
def f2b(x): return struct.unpack(">I", struct.pack(">f", float(x)))[0]
prog = "\n".join(coords() + estimator() + token() + render()) + "\n"
out, words = dump(prog, [("r", 152), ("r", 208), ("r", 160), ("s", 112), ("r", 144), ("r", 192), ("r", 176)])
bad = {"V": 0, "s": 0, "F": 0}
shown = 0
for path, cyc, B, k in lanes():
    m = int(ref_m(B, k) - M23)
    q = m // 16; n = m - q; i = m - 16 * q
    X = 8 * B
    if i in TEXT:
        HI, LO = TEXT[i]
    else:
        f1, f2, f3 = n // 10, n // 100, n // 1000
        D3, D2, D1, D0 = f3, f2 - 10 * f3, f1 - 10 * f2, n - 10 * f1
        t1, t2, t3 = X >= 32, X >= 408, X >= 4672
        HI = 65536 * (D3 + 48 * t3) + 256 * (D2 + 48 * t2) + (D1 + 48 * t1)
        LO = (1 << 24) * (D0 + 48) + 0x0A0000
    V = (HI << 32) | LO
    u = m // 2 + 1 - (1 if i in Z else 0)
    s = 5 * m - q - X - 597 + Delta(u)
    F = place(V, s)
    gV = out[("r", 152)][(path, cyc)]
    gs = struct.unpack(">f", struct.pack(">I", out[("r", 208)][(path, cyc)] >> 32))[0]
    gF = out[("r", 160)][(path, cyc)]
    if gV != V:
        bad["V"] += 1
        if shown < 6:
            print("V", B, k, m, n, i, hex(gV), hex(V), "S", hex(out[("r",144)][(path,cyc)]), "bias", hex(out[("s",112)][(path,cyc)])); shown += 1
    if gs != s:
        bad["s"] += 1
        if shown < 12:
            print("s", B, k, m, i, gs, s, "u", u, "gu", hex(out[("r",176)][(path,cyc)]), "D", hex(out[("r",192)][(path,cyc)])); shown += 1
    if gF != F: bad["F"] += 1
print(bad)
