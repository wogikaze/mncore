#!/usr/bin/env python3
"""find estimator lines (v1 slopes) with tweaked half-exact intercepts such that y=min L_d is never x.5
and round(y)+k reproduces a valid m0 for every block (checked through model2-style rendering)."""
import numpy as np, itertools
from f32util import is_half
from model2 import LINES
from trail import want, NBLK
import model2
f32 = np.float32
B = np.arange(NBLK, dtype=np.float64); X = 8 * B
def lines_y(lines):
    ys = [np.float64(f32(np.float64(f32(a)) * X + np.float64(f32(b)))) for a, b in lines]
    return np.minimum.reduce(ys)
def ok_lines(lines):
    y = lines_y(lines)
    if np.any(np.mod(y, 1.0) == 0.5): return False, "tie"
    m0 = np.round(y).astype(int)
    # verify through model2 lane rendering with given m0 (monkeypatch)
    bad = 0
    for b in range(NBLK):
        out = 0
        for k in range(4):
            out |= lane_m(b, int(m0[b]) + k)
        w, mask = want(b)
        if out & mask != w: bad += 1
        if bad: return False, f"bad block {b}"
    return True, ""
def lane_m(B, m):
    q = m // 16; n = m - q; i = m - 16 * q
    u = m / 2 + model2.EZ[i]
    D = max(-597, -64 - u, -11 - 2 * u, -6 - 3 * u)
    s = 5 * m - q - 8 * B + D - 1
    a, f1 = n // 100, n // 10; f3 = a // 10
    g2, g1, g3 = min(a, 1), min(f1, 1), min(f3, 1)
    HI = a + 246 * f3 + 48 * g2 + 12288 * g3
    LO = 256 * (256 * (246 * f1 - 2560 * a + n + 12288 * g1) + 12298)
    if i in model2.TXT6: HI, LO = model2.TXT6[i]
    return model2.place((int(HI) << 32) | int(LO), int(s))
if __name__ == "__main__":
    y = lines_y(LINES)
    print("ties with v1 lines at blocks:", np.nonzero(np.mod(y, 1.0) == 0.5)[0][:10])
    print("v1 lines ok:", ok_lines(LINES))
    # tweak intercepts by small half-exact offsets
    (a1, b1), (a2, b2), (a3, b3), (a4, b4) = LINES
    cands = []
    for d1 in (0, 1/64, -1/64):
        for d2 in (0, 1/64, -1/64, 1/128, -1/128):
            for d3 in (0, 1/32, -1/32):
                for b4n in (119.375, 119.4375, 119.5, 119.3125):
                    L = ((a1, b1 + d1), (a2, b2 + d2), (a3, b3 + d3), (a4, b4n))
                    if not all(is_half(v) for v in (b1 + d1, b2 + d2, b3 + d3, b4n)): continue
                    r = ok_lines(L)
                    if r[0]:
                        print("FOUND", L); cands.append(L)
                        raise SystemExit
    print("none")

def search2():
    (a1, b1), (a2, b2), (a3, b3), (a4, b4) = LINES
    y = lines_y(LINES)
    for blk in (9, 176, 3273):
        ys = [float(f32(np.float64(f32(a)) * 8 * blk + np.float64(f32(b)))) for a, b in LINES]
        print(blk, ys, "min line", int(np.argmin(ys)))
    for d2 in (1/1024, -1/1024, 1/512, -1/512, 1/256, -1/256, 1/128, -1/128):
        for d3 in (0, 1/1024, -1/1024, 1/256, -1/256):
            for d4 in (0, 2**-10, -2**-10, 2**-8, -2**-8):
                L = ((a1, b1), (a2, b2 + d2), (a3, b3 + d3), (a4, b4 + d4))
                r = ok_lines(L)
                if r[0]:
                    print("FOUND", L, [is_half(v) for v in (b1, b2 + d2, b3 + d3, b4 + d4)]); return L
    print("none2")
