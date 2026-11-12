#!/usr/bin/env python3
"""Per-region linear estimator feasibility for the hardware-semantics allowed sets."""
import pickle, numpy as np, sys
A = pickle.load(open("/tmp/allowed.pkl", "rb"))
def cwin(a, rng):
    """return list of feasible c intervals (union handled by sampling) for floor(a*X+c) in A[B]."""
    # collect constraints as allowed intervals per block; intersect via sweep over candidate c values
    lo, hi = -1e18, 1e18
    ivs = []
    for B in rng:
        X = 8 * B
        al = A[B]
        # contiguous?
        if al != list(range(al[0], al[-1] + 1)):
            ivs.append([(m - a * X, m + 1 - a * X) for m in al])
        else:
            lo = max(lo, al[0] - a * X); hi = min(hi, al[-1] + 1 - a * X)
            if lo >= hi: return None
    # handle non-contiguous by brute force sampling inside [lo,hi)
    if not ivs: return (lo, hi)
    best = None
    for c in np.linspace(lo, hi, 2001)[1:-1]:
        if all(any(l <= c < h for l, h in iv) for iv in ivs):
            best = (c, c) if best is None else (best[0], c)
    return best
regs = {"d1": (range(0, 4), 16/55), "d2": (range(4, 51), 16/63), "d12": (range(0, 51), 16/61), "d3": (range(51, 584), 16/71), "d4": (range(584, 4096), 16/79)}
for name, (rng, a0) in regs.items():
    span = 0.25 if name in ("d1",) else 0.06 if name in ("d2", "d12") else 0.004 if name == "d3" else 0.0008
    feas = []
    for a in np.linspace(a0 * (1 - span), a0 * (1 + span), 2001):
        w = cwin(a, rng)
        if w: feas.append((a, w))
    if not feas: print(name, "INFEASIBLE"); continue
    print(f"{name}: slope range [{feas[0][0]:.7f}, {feas[-1][0]:.7f}]")
    for j in range(2, 16):
        k0 = int(np.ceil(feas[0][0] * 2**j))
        while k0 / 2**j <= feas[-1][0]:
            w = cwin(k0 / 2**j, rng)
            if w:
                print(f"   dyadic {k0}/2^{j} = {k0/2**j:.8f} c window [{w[0]:.4f}, {w[1]:.4f}] width {w[1]-w[0]:.4f}")
                break
            k0 += 1
        else:
            continue
        break
