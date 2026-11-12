#!/usr/bin/env python3
"""Exact search (abstract model) for the shortest ALU op chain giving PE0 the max of all 16 columns.
T=16k layout: every PE reads the same row/slots.  unit bit d*4+s = slot s of PE p-d.
value=(M,L), L=-1 garbage.  Sources: aluf; raw word j -> ({j},G); raw long h -> ({2h},{2h+1});
stored (GRF0/GRF1, readable 2 lines after the write): long, even word (M,G), odd word (L,G).
Ops: msl/msr (both lanes), passa, fmax (lane-wise).  One read location per memory per op.
Pruning: optimistic size DP + 'at least 3 shift ops' rule."""
import sys, itertools
from functools import lru_cache
G = -1; FULL = 0xFFFF
def sh(m, k):
    if m == G: return G
    r = 0
    for d in range(4): r |= ((m >> (4*d)) & 15) << (4*((d+k) % 4))
    return r
def pc(m): return 0 if m == G else bin(m).count('1')
RAW = [('w%d' % j, (1 << j, G)) for j in range(4)] + [('l%d' % h, (1 << 2*h, 1 << 2*h+1)) for h in range(2)]
MAXD = int(sys.argv[1]); NST = int(sys.argv[2])
@lru_cache(maxsize=None)
def bound(al, st, r, kneed):
    # al: size of aluf; st: tuple of (size, age) age = lines since write (readable if age>=2)
    if r == 0: return al
    best = 0
    rd = [s for s, a in st if a >= 2]
    def nxt(v, store):
        nst = tuple(sorted([(s, a + 1) for s, a in st] + ([(v, 1)] if store else [])))
        if len(nst) > NST: nst = tuple(sorted(nst, reverse=True)[:NST])
        return nst
    # shift
    v = max([al, 1] + rd)
    for store in (0, 1):
        best = max(best, bound(v, nxt(v, store), r - 1, max(0, kneed - 1)))
    if r - 1 >= kneed:
        v = max([al + 1, 1] + [al + s for s in rd] + [s + 1 for s in rd] + [x + y for x, y in itertools.combinations(rd, 2)])
        for store in (0, 1):
            best = max(best, bound(v, nxt(v, store), r - 1, kneed))
    return best
def csize(v): return max(pc(v[0]), pc(v[1]))
memo = set(); found = []
def dfs(t, aluf, stored, nshift, prog):
    key = (t, aluf, stored, min(nshift, 3))
    if key in memo: return False
    memo.add(key)
    r = MAXD - t
    b = bound(csize(aluf) if aluf else 0, tuple(sorted((max(pc(M), pc(L)), t - tw) for _, tw, M, L in stored)), r, max(0, 3 - nshift))
    if b < 16: return False
    src = [('aluf', None, aluf)] if aluf else []
    src += [('raw' + n, 'LM0', v) for n, v in RAW]
    for i, (mem, tw, M, L) in enumerate(stored):
        if t - tw >= 2:
            src.append(('%s@%d' % (mem, tw), mem, (M, L)))
            src.append(('%s@%d.e' % (mem, tw), mem, (M, G)))
            if L != G: src.append(('%s@%d.o' % (mem, tw), mem, (L, G)))
    outs = []
    for n, loc, v in src:
        for op, k in (('msl', 1), ('msr', 3)):
            outs.append(((sh(v[0], k), sh(v[1], k)), op + ' ' + n, 1))
        if loc is not None: outs.append((v, 'passa ' + n, 0))
    for (n1, l1, v1), (n2, l2, v2) in itertools.combinations(src, 2):
        if l1 and l2 and l1 == l2: continue
        L = G if (v1[1] == G or v2[1] == G) else v1[1] | v2[1]
        outs.append(((v1[0] | v2[0], L), 'fmax %s %s' % (n1, n2), 0))
    outs.sort(key=lambda o: -(pc(o[0][0]) + pc(o[0][1])))
    seen = set()
    for v, name, isS in outs:
        if v[0] == FULL:
            print(t + 1, prog + [name], flush=True); found.append(1); return True
    if r == 1: return False
    for v, name, isS in outs:
        if v[0] == G or (v, isS) in seen: continue
        seen.add((v, isS))
        opts = [()]
        if len(stored) < NST: opts += [(('GRF0', t, v[0], v[1]),), (('GRF1', t, v[0], v[1]),)]
        for st in opts:
            if dfs(t + 1, v, tuple(sorted(stored + st)), nshift + isS, prog + [name + (' ->' + st[0][0] if st else '')]):
                return True
    return False
dfs(0, None, (), 0, [])
print('done', MAXD, 'found' if found else 'NONE', 'states', len(memo))
