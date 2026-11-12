#!/usr/bin/env python3
"""Shortest SIMD ALU chain search (T=16k layout, all PEs read the same row slots).
Units: bit d*4+s = column slot s of PE (p-d).  Value=(M,L); L=-1 garbage.
Sources: aluf, raw word slot j (M={s},L=G), raw long h (M={2h},L={2h+1}),
stored value (long / even word / odd word) from GRF0/GRF1 written >=2 lines ago.
Ops: msl/msr x (both lanes), fmax x y (lane-wise), passa x.  Goal: M == all 16."""
import sys, itertools
from functools import lru_cache
G = -1
FULL = 0xFFFF
def sh(m, k):
    if m == G: return G
    r = 0
    for d in range(4): r |= ((m >> (4*d)) & 15) << (4*((d+k) % 4))
    return r
RAW = [('w%d' % j, (1 << j, G)) for j in range(4)] + [('l%d' % h, (1 << 2*h, 1 << 2*h+1)) for h in range(2)]
MAXD = int(sys.argv[1])
NST = int(sys.argv[2]) if len(sys.argv) > 2 else 2
sys.setrecursionlimit(10000)
found = []
memo = set()
def pc(m): return 0 if m == G else bin(m).count('1')
def dfs(t, aluf, stored, prog):
    # stored: tuple of (mem, tw, M, L)
    if t == MAXD: return
    key = (t, aluf, stored)
    if key in memo: return
    memo.add(key)
    rem = MAXD - t
    # bound: max units of any source (M+L) * 2^rem
    best = max([2] + ([pc(aluf[0]) + pc(aluf[1])] if aluf else []) + [pc(s[2]) + pc(s[3]) for s in stored])
    if best << rem < 16: return
    src = [('aluf', None, aluf)] if aluf else []
    src += [('raw' + n, 'LM0', v) for n, v in RAW]
    for i, (mem, tw, M, L) in enumerate(stored):
        if t - tw >= 2:
            src.append(('%s#%d' % (mem, i), (mem, i, 'l'), (M, L)))
            src.append(('%s#%d.e' % (mem, i), (mem, i, 'e'), (M, G)))
            if L != G: src.append(('%s#%d.o' % (mem, i), (mem, i, 'o'), (L, G)))
    outs = {}
    for n, loc, v in src:
        for op, k in (('msl', 1), ('msr', 3)):
            outs.setdefault((sh(v[0], k), sh(v[1], k)), op + ' ' + n)
        if loc is not None: outs.setdefault(v, 'passa ' + n)
    for (n1, l1, v1), (n2, l2, v2) in itertools.combinations(src, 2):
        if l1 and l2:
            m1 = l1 if l1 == 'LM0' else l1[0]; m2 = l2 if l2 == 'LM0' else l2[0]
            if m1 == m2: continue
        M = v1[0] | v2[0]
        L = G if (v1[1] == G or v2[1] == G) else v1[1] | v2[1]
        outs.setdefault((M, L), 'fmax %s %s' % (n1, n2))
    for v, name in outs.items():
        if v[0] == FULL:
            found.append(prog + [name]); print(t + 1, prog + [name], flush=True); return True
    if t + 1 == MAXD: return
    for v, name in outs.items():
        if v == aluf: continue
        stores = [()]
        if len(stored) < NST:
            stores += [(('GRF0', t, v[0], v[1]),), (('GRF1', t, v[0], v[1]),)]
        for st in stores:
            ns = tuple(sorted(stored + st))
            if dfs(t + 1, v, ns, prog + [name + (' ->' + st[0][0] if st else '')]): return True
dfs(0, None, (), [])
print('done', len(found))
