#!/usr/bin/env python3
from est_search import allowed, NBLK
import numpy as np
from fractions import Fraction
def feasible(a, rng):
    lo, hi = -1e18, 1e18
    for b in rng:
        X = 8*b; al = allowed[b]
        lo = max(lo, min(al) - a*X); hi = min(hi, max(al) + 1 - a*X)
        if lo >= hi: return None
    return lo, hi
def slope_range(rng, a0, span):
    lo_a = hi_a = None
    for a in np.linspace(a0*(1-span), a0*(1+span), 4001):
        if feasible(a, rng):
            lo_a = a if lo_a is None else lo_a; hi_a = a
    return lo_a, hi_a
regs = {"d1": range(0,4), "d2": range(4,51), "d3": range(51,584), "d4": range(584,4096), "d12": range(0,51), "d123": range(0,584)}
for name, rng in regs.items():
    a0 = {"d1":16/55,"d2":16/63,"d3":16/71,"d4":16/79,"d12":16/61,"d123":16/70}[name]
    r = slope_range(rng, a0, 0.2 if name in("d1","d12","d123") else 0.05 if name=="d2" else 0.002)
    print(name, r, "rel width", None if r[0] is None else (r[1]-r[0])/a0)
    if r[0] is None: continue
    # best dyadic approximations k/2^j inside the feasible slope range
    for j in range(2, 20):
        k0 = int(np.ceil(r[0]*2**j)); 
        if k0/2**j <= r[1]:
            f = feasible(k0/2**j, rng)
            print(f"   dyadic {k0}/2^{j} = {k0/2**j:.8f}  c window {f}")
            break
