#!/usr/bin/env python3
"""v2 lane model: E=6 layout, pair digits, g-bias, table text, exact float32 where it matters."""
import numpy as np
from ref3 import MASK64, TEXT, Z
from model import stream, NBLK
f32 = np.float32
LINES = ((0.28125, 0.703125), (0.251953125, 1.359375), (0.225341796875, 13.21875),
         (0.20253221690654755, 119.396484375))
M23 = 2.0 ** 23
C10, C100 = np.frombuffer(np.array([0x3DCCCCCD, 0x3C23D70B], ">u4").tobytes(), ">f4").astype(np.float64)
def fma(a, b, c):  # float32 fma (exact product, single rounding)
    return float(f32(np.float64(f32(a)) * np.float64(f32(b)) + np.float64(f32(c))))
def place(v, s):
    a = (8 * s) % 128; b = (-8 * s) % 128
    return ((v >> a) if a < 64 else 0) | (((v << b) & MASK64) if b < 64 else 0)
TXT6 = {}
for i, (hi, lo) in TEXT.items():
    v6 = ((hi << 32) | lo) >> 8
    TXT6[i] = (v6 >> 32, v6 & 0xffffffff)
EZ = [1 - (1 if i in Z else 0) - (i % 2) / 2 for i in range(16)]
def lane(B, k):
    X = 8.0 * B
    y = min(fma(X, a, b) for a, b in LINES)
    m = int(float(f32(y + M23)) - M23) + k
    q = int(np.floor(f32(m) * f32(1 / 16))); n = m - q; i = m - 16 * q
    u = m / 2 + EZ[i]
    D = max(-597, -64 - u, -11 - 2 * u, -6 - 3 * u)
    s = 5 * m - q - X + D - 1
    a = int(np.floor(f32(n) * f32(C100))); f1 = int(np.floor(f32(n) * f32(C10)))
    f3 = int(np.floor(f32(a) * f32(C10))); a2 = int(np.floor(f32(f1) * f32(C10)))
    assert a2 == a
    g2, g1, g3 = min(a, 1), min(f1, 1), min(f3, 1)
    Phi = a + 246 * f3 + 48 * g2 + 12288 * g3
    Plo = 246 * f1 - 2560 * a + n + 12288 * g1
    HI = Phi; LO = 256 * (256 * Plo + 12298)
    if i in TXT6: HI, LO = TXT6[i]
    return place((int(HI) << 32) | int(LO), int(s))
def check():
    bad = []
    for B in range(NBLK):
        out = 0
        for k in range(4): out |= lane(B, k)
        sb = stream[8 * B: 8 * B + 8].encode("latin-1")
        w = int.from_bytes(sb.ljust(8, b"\0"), "big")
        mask = MASK64 if len(sb) == 8 else MASK64 ^ (MASK64 >> (8 * len(sb)))
        if out & mask != w: bad.append(B)
    return bad
if __name__ == "__main__":
    print({i: (hex(h), hex(l)) for i, (h, l) in TXT6.items()})
    b = check(); print("bad", len(b), b[:10])
