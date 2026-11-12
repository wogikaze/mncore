#!/usr/bin/env python3
"""Find min-of-4-lines estimator with float32 evaluation: m_b = fl(min_d fl(a_d X + b_d) + 2^23 + k), floor semantics.
Prefer half-exact a1..a3, b1..b3."""
import pickle
from fractions import Fraction as Fr
from f32util import f32, fma, is_half
A = pickle.load(open("/tmp/allowed_trail.pkl", "rb"))
NB = len(A)
M = Fr(2) ** 23
def m0_of(lines, B):
    X = 8 * B
    y = min(fma(a, X, b) for a, b in lines)
    # m_b for k=0: f32(y + 2^23); m = that - 2^23
    return int(f32(y + M) - M)
def ok(lines):
    for B in range(NB):
        if m0_of(lines, B) not in A[B]: return False
    return True
REG = {1: range(0, 4), 2: range(4, 51), 3: range(51, 584), 4: range(584, 4096)}
def ok_reg(line, rng):
    a, b = line
    for B in rng:
        X = 8 * B
        y = fma(a, X, b)
        if int(f32(y + M) - M) not in A[B]: return False
    return True
# candidate half-exact slopes/offsets per region (b already includes the -0.5: floor(aX+b0) = round(aX + b0 - 0.5))
import itertools
def halfgrid(lo, hi, step):
    v = Fr(lo); out = []
    while v <= hi:
        if is_half(v): out.append(v)
        v += step
    return out
cands = {}
cands[1] = [(a, b) for a in halfgrid(Fr(2851, 10000), Fr(2967, 10000), Fr(1, 2048)) for b in halfgrid(Fr(1, 2), Fr(12, 10), Fr(1, 64)) if ok_reg((a, b), REG[1])]
cands[2] = [(a, b) for a in halfgrid(Fr(2489, 10000), Fr(2571, 10000), Fr(1, 4096)) for b in halfgrid(Fr(13, 10), Fr(23, 10), Fr(1, 64)) if ok_reg((a, b), REG[2])]
cands[3] = [(a, b) for a in halfgrid(Fr(225213, 10**6), Fr(225477, 10**6), Fr(1, 2**14)) for b in halfgrid(Fr(127, 10), Fr(133, 10), Fr(1, 128)) if ok_reg((a, b), REG[3])]
print({d: len(c) for d, c in cands.items()})
# region 4: float32 slope & offset
a4s = []
base = Fr(16, 79)
for t in range(-60, 61):
    a = f32(base * (1 + Fr(t, 10**7)))
    for bb in range(-40, 41):
        b = f32(Fr(119886 + 38, 1000) - Fr(1, 2) + Fr(bb, 1000))
        if ok_reg((a, b), REG[4]): a4s.append((a, b))
print("region4 float32 candidates:", len(a4s))
found = []
for l4 in a4s[::max(1, len(a4s)//20)]:
    for l3 in cands[3][::max(1, len(cands[3])//15)]:
        for l2 in cands[2][::max(1, len(cands[2])//10)]:
            for l1 in cands[1][::max(1, len(cands[1])//5)]:
                if ok([l1, l2, l3, l4]):
                    found.append((l1, l2, l3, l4)); break
            if found: break
        if found: break
    if found: break
for f in found:
    print("FOUND", [(str(a), str(b), float(a), float(b)) for a, b in f])
pickle.dump(found, open("/tmp/lines.pkl", "wb"))
