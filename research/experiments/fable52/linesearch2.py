#!/usr/bin/env python3
"""Vectorized search for the min-of-4-lines estimator with exact float32 fma semantics.
m0 = f32(min_d f32(a_d*X + b_d) + 2^23) - 2^23 must lie in allowed[B]."""
import pickle, numpy as np, sys
A = pickle.load(open(sys.argv[1] if len(sys.argv) > 1 else "/tmp/allowed_trail.pkl", "rb"))
NB = len(A)
X = (8 * np.arange(NB)).astype(np.float64)
lo = np.array([a[0] for a in A], dtype=np.float64); hi = np.array([a[-1] for a in A], dtype=np.float64)
M = 2.0 ** 23
def f32(x): return np.asarray(x, dtype=np.float64).astype(np.float32).astype(np.float64)
def line(a, b): return f32(np.float64(np.float32(a)) * X + np.float64(np.float32(b)))
def m0(y): return f32(y + M) - M
REG = {1: (0, 4), 2: (4, 51), 3: (51, 584), 4: (584, NB)}
def ok_mask(y):
    m = m0(y)
    return (m >= lo) & (m <= hi)
def is_half(v):
    v = float(v)
    if v == 0: return True
    a = abs(v); e = np.floor(np.log2(a)); man = a / 2.0 ** e - 1
    return -30 <= e <= 31 and abs(man * 512 - round(man * 512)) < 1e-12
cands = {}
for d, (s, e) in REG.items():
    P = 8 * d + 47; a0 = 16.0 / P
    sl = slice(s, e)
    res = []
    if d < 4:
        step = {1: 2 ** -11, 2: 2 ** -12, 3: 2 ** -14}[d]
        arange = np.arange(np.floor(a0 * 0.95 / step) * step, a0 * 1.05, step)
        brange = np.arange(-5, 30, 1 / 64.0)
    else:
        a32 = np.float32(a0)
        ulp = np.spacing(a32)
        arange = np.array([np.float64(a32) + k * float(ulp) for k in range(-60, 61)])
        brange = np.arange(119.0, 121.0, 1 / 1024.0)
    for a in arange:
        if d < 4 and not is_half(a): continue
        y = f32(np.float64(np.float32(a)) * X[sl][:, None] + brange[None, :].astype(np.float32).astype(np.float64))
        mm = f32(y + M) - M
        good = ((mm >= lo[sl][:, None]) & (mm <= hi[sl][:, None])).all(axis=0)
        for b in brange[good]:
            if d < 4 and not is_half(b): continue
            res.append((float(np.float32(a)), float(np.float32(b))))
    cands[d] = res
    print(d, len(res), res[:3], flush=True)
pickle.dump(cands, open("/tmp/linecands.pkl", "wb"))
# combine: need min over 4 lines to pick correctly everywhere
L = {d: [line(a, b) for a, b in cands[d]] for d in cands}
found = []
import itertools, random
random.seed(1)
c1 = list(range(len(cands[1]))); c2 = list(range(len(cands[2]))); c3 = list(range(len(cands[3]))); c4 = list(range(len(cands[4])))
for tries in range(200000):
    i1, i2, i3, i4 = random.choice(c1), random.choice(c2), random.choice(c3), random.choice(c4)
    y = np.minimum(np.minimum(L[1][i1], L[2][i2]), np.minimum(L[3][i3], L[4][i4]))
    if ok_mask(y).all():
        found.append((cands[1][i1], cands[2][i2], cands[3][i3], cands[4][i4]))
        if len(found) >= 5: break
print("found", len(found))
for f in found: print(f)
pickle.dump(found, open("/tmp/lines.pkl", "wb"))
