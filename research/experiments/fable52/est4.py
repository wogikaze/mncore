#!/usr/bin/env python3
"""Search common (gamma, c0): m0 = floor(a_d*(X + constd_d + gamma) + c0) allowed for all blocks."""
import pickle, numpy as np
from fractions import Fraction as Fr
A = pickle.load(open("/tmp/allowed.pkl", "rb"))
CONSTD = {1: 0, 2: 5, 3: 58, 4: 591}
regs = {1: range(0, 4), 2: range(4, 51), 3: range(51, 584), 4: range(584, 4096)}
def ok_region(a, d, gamma, c0):
    for B in regs[d]:
        v = a * (8 * B + CONSTD[d] + gamma) + c0
        if int(np.floor(v)) not in A[B]: return False
    return True
import itertools
slopes = {
  1: [Fr(1,4), Fr(33,128), Fr(16,61), Fr(16,55)],
  2: [Fr(1,4), Fr(33,128), Fr(16,63), Fr(16,61)],
  3: [Fr(231,1024), Fr(16,71), Fr(923,4096), Fr(1846,8192)],
  4: [Fr(1659,8192), Fr(16,79), Fr(3318,16384), Fr(6637, 32768), Fr(13274, 65536)],
}
for c0 in [Fr(0), Fr(1,2), Fr(1,4), Fr(3,4), Fr(1), Fr(3,2)]:
    for gamma in range(-12, 13):
        res = {}
        for d in (1, 2, 3, 4):
            res[d] = [s for s in slopes[d] if ok_region(float(s), d, gamma, float(c0))]
        if all(res[d] for d in res):
            print("c0", c0, "gamma", gamma, {d: [str(s) for s in res[d]] for d in res})
