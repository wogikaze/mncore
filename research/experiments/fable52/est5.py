#!/usr/bin/env python3
"""Fit floor(a*X+b) per region for allowed sets in /tmp/allowed_trail.pkl; then check min-of-lines."""
import pickle, sys
from fractions import Fraction as Fr
A = pickle.load(open(sys.argv[1] if len(sys.argv) > 1 else "/tmp/allowed_trail.pkl", "rb"))
REG = {1: range(0, 4), 2: range(4, 51), 3: range(51, 584), 4: range(584, 4096)}
def interval(a, rng):
    lo, hi = Fr(-10**9), Fr(10**9)
    for B in rng:
        al = A[B]; X = 8 * B
        assert al == list(range(al[0], al[-1] + 1))
        lo = max(lo, al[0] - a * X); hi = min(hi, al[-1] + 1 - a * X)
        if lo >= hi: return None
    return lo, hi
for d, rng in REG.items():
    P = 8 * d + 47
    a0 = Fr(16, P)
    best = None
    for num in range(-400, 401):
        a = a0 * (1 + Fr(num, 40000))
        iv = interval(a, rng)
        if iv and (best is None or iv[1] - iv[0] > best[2] - best[1]):
            best = (a, iv[0], iv[1])
    if best:
        print(f"d={d}: a={float(best[0]):.8f} (16/P={float(a0):.8f}) b in [{float(best[1]):.4f},{float(best[2]):.4f}) width {float(best[2]-best[1]):.4f}")
    else:
        print(f"d={d}: infeasible")
    # feasible slope range
    lo_a = hi_a = None
    for num in range(-4000, 4001):
        a = a0 * (1 + Fr(num, 200000))
        if interval(a, rng):
            lo_a = a if lo_a is None else lo_a; hi_a = a
    if lo_a: print(f"     slope range [{float(lo_a):.8f}, {float(hi_a):.8f}] rel width {float((hi_a-lo_a)/a0):.5f}")
