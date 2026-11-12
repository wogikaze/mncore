#!/usr/bin/env python3
"""Lane-level reference for the trailing/end-aligned design (exact ints; float32 effects ignored here)."""
from model import stream, NBLK
MASK64 = (1 << 64) - 1
LINES = [(0.288, 1.174), (0.25206349206349205, 1.9776190476190476),
         (0.22534647887323944, 13.38940281690141), (0.20253113924050634, 119.93358582278480)]
Z = {0, 6, 10, 12}
FIZ = {3, 6, 9, 12}; BUZ = {0, 5, 10}; FH = {15}
TEXT = {i: v for i, v in [(3, (0x46697A, 0x7A0A0000)), (6, (0x46697A, 0x7A0A0000)), (9, (0x46697A, 0x7A0A0000)),
                          (12, (0x46697A, 0x7A0A0000)), (15, (0x46697A, 0x7A000000)),
                          (0, (0x42757A, 0x7A0A0000)), (5, (0x42757A, 0x7A0A0000)), (10, (0x42757A, 0x7A0A0000))]}
def Delta(u): return max(0, 533 - u, 586 - 2 * u, 591 - 3 * u)
def place(v, s):
    a = (8 * s) % 128; b = (-8 * s) % 128
    return ((v >> a) if a < 64 else 0) | (((v << b) & MASK64) if b < 64 else 0)
def lane(B, k, region_mode="block"):
    X = 8 * B
    y = min(a * X + b for a, b in LINES)
    m = int(y // 1) + k
    q = m // 16; n = m - q; i = m - 16 * q
    if i in TEXT:
        HI, LO = TEXT[i]
    else:
        f1, f2, f3 = n // 10, n // 100, n // 1000
        D3, D2, D1, D0 = f3, f2 - 10 * f3, f1 - 10 * f2, n - 10 * f1
        if region_mode == "block":
            t1, t2, t3 = X >= 32, X >= 408, X >= 4672
        else:
            t1, t2, t3 = n >= 10, n >= 100, n >= 1000
        HI = 65536 * (D3 + 48 * t3) + 256 * (D2 + 48 * t2) + (D1 + 48 * t1)
        LO = (1 << 24) * (D0 + 48) + 0x0A0000
    V = (HI << 32) | LO
    u = m // 2 + 1 - (1 if i in Z else 0)
    s = 5 * m - q - X - 597 + Delta(u)
    return place(V, s), s
def check(region_mode="block"):
    bad = []
    srange = [99, -99]
    for B in range(NBLK):
        out = 0
        for k in range(4):
            v, s = lane(B, k, region_mode)
            out |= v
            srange = [min(srange[0], s), max(srange[1], s)]
        sbytes = stream[8 * B: 8 * B + 8].encode("latin-1")
        w = int.from_bytes(sbytes.ljust(8, b"\0"), "big")
        mask = MASK64 if len(sbytes) == 8 else MASK64 ^ (MASK64 >> (8 * len(sbytes)))
        if out & mask != w: bad.append(B)
    return bad, srange
if __name__ == "__main__":
    for mode in ("block", "number"):
        bad, sr = check(mode)
        print(mode, "bad blocks:", len(bad), bad[:10], "s range", sr)
