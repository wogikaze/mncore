#!/usr/bin/env python3
"""Search min-of-4-lines estimators y=min_d(a_d X + b_d) with floor(y) in allowed[B] for all B."""
import pickle, sys, itertools
from fractions import Fraction as Fr
A = pickle.load(open(sys.argv[1] if len(sys.argv) > 1 else "/tmp/allowed_trail.pkl", "rb"))
REG = {1: range(0, 4), 2: range(4, 51), 3: range(51, 584), 4: range(584, 4096)}
def interval(a, rng):
    lo, hi = Fr(-10**9), Fr(10**9)
    for B in rng:
        al = A[B]; X = 8 * B
        lo = max(lo, al[0] - a * X); hi = min(hi, al[-1] + 1 - a * X)
        if lo >= hi: return None
    return lo, hi
def ok_all(lines):
    for B in range(len(A)):
        X = 8 * B
        y = min(a * X + b for a, b in lines)
        f = y.numerator // y.denominator
        if f not in A[B]: return False
    return True
cands = {}
for d, rng in REG.items():
    P = 8 * d + 47; a0 = Fr(16, P)
    lst = []
    span = {1: 400, 2: 300, 3: 10, 4: 1}[d]
    for num in range(-span, span + 1, max(1, span // 40)):
        a = a0 * (1 + Fr(num, 40000 if d < 3 else 400000))
        iv = interval(a, rng)
        if iv:
            for t in (Fr(1, 4), Fr(1, 2), Fr(3, 4)):
                lst.append((a, iv[0] + (iv[1] - iv[0]) * t))
    cands[d] = lst
    print(d, len(lst))
found = 0
for l1 in cands[1]:
  for l2 in cands[2]:
    for l3 in cands[3][::3]:
      for l4 in cands[4]:
        if ok_all([l1, l2, l3, l4]):
            print("FOUND", [(float(a), float(b)) for a, b in (l1, l2, l3, l4)])
            found += 1
            if found >= 3: raise SystemExit
print("found", found)
