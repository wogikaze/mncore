#!/usr/bin/env python3
"""For each block, compute the set of allowed first-candidate indices m0 (4 candidates m0..m0+3),
for token variants; then search linear estimators m0 = floor(a*X + c) per region."""
from m_tokens import *
import sys
VAR = sys.argv[1] if len(sys.argv) > 1 else "plain"
# token text variants
T = []
for (p, text, n, kind) in toks:
    if VAR == "numprefix" and kind == 'N' and p > 0:
        T.append((p - 1, "\n" + text))
    else:
        T.append((p, text))
def contrib(m, X):
    s, text = T[m]
    out = [None]*8
    for i, ch in enumerate(text):
        o = s + i - X
        if 0 <= o < 8: out[o] = ch
    return out
allowed = []
for b in range(NBLK):
    X = 8*b
    want = list(stream[X:X+8]) + [None]*(8-len(stream[X:X+8]))
    mf = tok_at(X)
    ok = []
    for m0 in range(mf-4, mf+3):
        got = [None]*8
        good = True
        for m in range(m0, m0+4):
            if m < 0 or m >= len(T): continue
            c = contrib(m, X)
            for o in range(8):
                if c[o] is not None:
                    if got[o] is not None and got[o] != c[o]: good = False
                    got[o] = c[o]
        if good and got == want: ok.append(m0)
    allowed.append(ok)
from collections import Counter
print(VAR, Counter(len(a) for a in allowed))
regions = {1: range(0, 4), 2: range(4, 51), 3: range(51, 584), 4: range(584, 4096)}
import numpy as np
for d, rng in regions.items():
    P = 8*d + 47
    a0 = 16.0 / P
    best = None
    feas = []
    for da in np.linspace(-0.004, 0.004, 161) if d <= 2 else np.linspace(-3e-5, 3e-5, 61):
        a = a0 * (1 + da) if d <= 2 else a0 + da
        # feasible c interval: for each block need floor(a*X + c) in allowed -> c in union of [m0 - aX, m0+1 - aX)
        lo, hi = -1e9, 1e9
        okall = True
        for b in rng:
            X = 8*b
            al = allowed[b]
            if not al: okall = False; break
            # allowed sets are contiguous ranges
            l = min(al) - a*X; h = max(al) + 1 - a*X
            lo = max(lo, l); hi = min(hi, h)
            if lo >= hi: okall = False; break
        if okall: feas.append((a, lo, hi))
    if feas:
        w = max(feas, key=lambda t: t[2]-t[1])
        print(f"d={d}: {len(feas)} feasible slopes; a range [{feas[0][0]:.7f},{feas[-1][0]:.7f}] nominal {a0:.7f}; widest c window at a={w[0]:.7f}: [{w[1]:.4f},{w[2]:.4f}] width {w[2]-w[1]:.4f}")
    else:
        print(f"d={d}: no feasible linear estimator")
