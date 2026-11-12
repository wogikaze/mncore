#!/usr/bin/env python3
"""Estimator tolerance: which (b2, b3, b4) keep the block output correct, for pre-rounded lines
m0 = min_d rint(a_d' * B + b_d)  (exact arithmetic, single rounding)."""
import numpy as np, sys
import model3
from model import NBLK, stream
A2, A3 = 0.251953125 * 8, 0.225341796875 * 8
A4 = float(np.float32(0.20253394544124603)) * 8.0
B = np.arange(NBLK, dtype=np.float64)
# required candidate window per block: tokens overlapping the block -> allowed base range [lo, hi]
import bisect
starts = []; ends = []
# token list (index m from 1): (start, end)
pos = 0; toks = [None]
for n in range(1, 6335):
    if n % 15 == 0: parts = ["Fizz", "Buzz\n"]
    elif n % 3 == 0: parts = ["Fizz\n"]
    elif n % 5 == 0: parts = ["Buzz\n"]
    else: parts = [str(n) + "\n"]
    if n == 6334: parts = [p.rstrip("\n") for p in parts]
    for p in parts:
        toks.append((pos, pos + len(p) - 1)); pos += len(p)
st = [t[0] for t in toks[1:]]; en = [t[1] for t in toks[1:]]
lo = np.zeros(NBLK); hi = np.zeros(NBLK)
for b in range(NBLK):
    x0, x1 = 8 * b, min(8 * b + 7, pos - 1)
    first = bisect.bisect_left(en, x0) + 1          # first token with end >= x0
    last = bisect.bisect_right(st, x1)              # last token with start <= x1
    assert last - first <= 3
    lo[b] = last - 3; hi[b] = first                 # base m0 must satisfy lo <= m0 <= hi
def ok(b2, b3, b4, a4=A4, off=0.0):
    m0 = np.minimum(np.minimum(np.rint(A2 * (B + off) + b2), np.rint(A3 * (B + off) + b3)), np.rint(a4 * (B + off) + b4))
    return bool(np.all((m0 >= lo) & (m0 <= hi)))
if __name__ == "__main__":
    b2, b3, b4 = 1.359375, 13.21875, 119.375
    print("base ok:", ok(b2, b3, b4))
    for name, idx in (("b2", 0), ("b3", 1), ("b4", 2)):
        good = []
        for d in np.arange(-2, 2.0001, 1 / 256):
            v = [b2, b3, b4]; v[idx] += d
            if ok(*v): good.append(v[idx])
        print(name, "window: [%.4f, %.4f]" % (min(good), max(good)), "n", len(good))
