#!/usr/bin/env python3
import pickle, numpy as np, random
A = pickle.load(open("/tmp/allowed_trail.pkl", "rb")); NB = len(A)
cands = pickle.load(open("/tmp/linecands.pkl", "rb"))
X = (8 * np.arange(NB)).astype(np.float64)
lo = np.array([a[0] for a in A], float); hi = np.array([a[-1] for a in A], float)
M = 2.0 ** 23
def f32(x): return np.asarray(x, dtype=np.float64).astype(np.float32).astype(np.float64)
def line(a, b): return f32(np.float64(np.float32(a)) * X + np.float64(np.float32(b)))
L = {d: [line(a, b) for a, b in cands[d]] for d in cands}
def full_ok(y):
    m0 = f32(y + M) - M
    if not ((m0 >= lo) & (m0 <= hi)).all(): return False
    for k in range(1, 4):
        if not (f32(y + M + k) - M == m0 + k).all(): return False
    return True
random.seed(7)
found = []
for t in range(400000):
    i = [random.randrange(len(cands[d])) for d in (1, 2, 3, 4)]
    y = np.minimum(np.minimum(L[1][i[0]], L[2][i[1]]), np.minimum(L[3][i[2]], L[4][i[3]]))
    if full_ok(y):
        found.append(tuple(cands[d][i[d - 1]] for d in (1, 2, 3, 4)))
        if len(found) >= 8: break
print(len(found))
for f in found: print(f)
pickle.dump(found, open("/tmp/lines_ok.pkl", "wb"))
