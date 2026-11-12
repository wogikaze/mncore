#!/usr/bin/env python3
"""Search estimator lines with INTEGER intercepts: m0 = min_d rint(a_d' * B + j_d), a2', a3' half-exact.
min >= lo  <=>  every line >= lo ;  min <= hi  <=>  some line <= hi."""
import numpy as np, sys
from est_tol import lo, hi, B, NBLK
A4 = float(np.float32(0.20253394544124603)) * 8.0
def line(a, j): return np.rint(a * B + j)
def cands(avals, jvals):
    out = []
    for a in avals:
        for j in jvals:
            l = line(a, j)
            if np.all(l >= lo): out.append(((a, j), l <= hi))
    return out
c2 = cands([k / 256 for k in range(500, 540)], range(-2, 6))
c3 = cands([k / 512 for k in range(900, 945)], range(6, 22))
a4s = sorted(set(float(np.float32(A4 / 8 + d * 2.0 ** -27)) * 8.0 for d in range(-6000, 6001, 60)))
c4 = cands(a4s, range(110, 130))
print(len(c2), len(c3), len(c4))
# prefix coverage of line2 from block 0, suffix coverage of line4
def prefix(u):
    bad = np.flatnonzero(~u); return int(bad[0]) if len(bad) else NBLK
def suffix(u):
    bad = np.flatnonzero(~u); return int(bad[-1]) + 1 if len(bad) else 0
p2 = [(c, prefix(u)) for c, u in c2]; s4 = [(c, suffix(u)) for c, u in c4]
cs3 = [(c, np.concatenate([[0], np.cumsum(~u)])) for c, u in c3]
sol = []
for a, t2 in p2:
    for d, t4 in s4:
        if t4 <= t2: sol.append((a, None, d)); continue
        for c, cs in cs3:
            if cs[t4] - cs[t2] == 0: sol.append((a, c, d))
print("solutions", len(sol))
two = [s for s in sol if s[1] is None]
print("two-line solutions", len(two))
seen = {}
for s in sol:
    key = (s[0], s[1]); seen.setdefault(key, []).append(s[2])
print("distinct (l2, l3):", len(seen))
for k, v in list(seen.items())[:40]:
    print(k, "n4", len(v), "j4 set", sorted(set(x[1] for x in v)))
if __name__ == "__main__" and len(sys.argv) > 1:
    import struct
    def fbits(x): return struct.unpack(">I", struct.pack(">f", x))[0]
    for key in [((2.046875, 1), (1.802734375, 13))]:
        v = seen[key]
        for j in (119, 120):
            av = sorted(a for a, jj in v if jj == j)
            print("j4", j, "a4' range", av[0], av[-1], "n", len(av), "mid a4 (per byte) bits", hex(fbits(av[len(av)//2] / 8)), av[len(av)//2] / 8)
