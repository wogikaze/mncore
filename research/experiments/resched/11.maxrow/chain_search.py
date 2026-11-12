#!/usr/bin/env python3
"""Abstract search: shortest SIMD ALU op chain (per-PE, per-cycle) that makes PE0's MSB lane
cover all 16 columns (4 PE offsets x 4 slots) of a row.
Value = (M, L) bitmasks over elements d*4+s (d = PE offset, value at PE p contains column slot s of PE p-d);
G = garbage lane (-1).  Ops: passa/msl/msr x, fmax x y.  Sources: aluf, raw LM0 (word slot j or long h),
stored values (long, even word, odd word).  GRF write->read gap 2 lines, LM0 3 lines.
One read location per memory per line."""
import sys, itertools
G = -1
FULL = (1 << 16) - 1
def sh(m, k):
    if m == G: return G
    r = 0
    for d in range(4):
        r |= ((m >> (4*d)) & 15) << (4*((d+k) % 4))
    return r
def un(a, b):
    return G if a == G or b == G else a | b
RAW = []
for j in range(4): RAW.append((('LM0', 'w%d' % j), (1 << j, G)))
for h in range(2): RAW.append((('LM0', 'l%d' % h), (1 << (2*h), 1 << (2*h+1))))
MAXD = int(sys.argv[1]) if len(sys.argv) > 1 else 8
MEMS = ['GRF0', 'GRF1']
best = [None]
def sources(t, aluf, stored):
    out = []
    if aluf is not None: out.append((None, aluf, 'aluf'))
    for loc, v in RAW: out.append((loc, v, 'raw' + loc[1]))
    for i, (mem, tw, v) in enumerate(stored):
        gap = 3 if mem == 'LM0' else 2
        if t - tw < gap: continue
        out.append(((mem, 'S%dl' % i), v, '%s.S%d' % (mem, i)))
        out.append(((mem, 'S%de' % i), (v[0], G), '%s.S%d.e' % (mem, i)))
        if v[1] != G: out.append(((mem, 'S%do' % i), (v[1], G), '%s.S%d.o' % (mem, i)))
    return out
seen = {}
def dfs(t, aluf, stored, prog):
    if aluf is not None and aluf[0] == FULL:
        if best[0] is None or len(prog) < len(best[0]):
            best[0] = list(prog); print(len(prog), prog, flush=True)
        return
    if t >= MAXD: return
    rem = MAXD - t
    # bound: biggest M obtainable doubles at most per op
    mx = max([bin(v[0]).count('1') for _, v, _ in sources(t + 10, aluf, stored) if v[0] != G] + [0])
    if mx << rem < 16: return
    key = (t, aluf, tuple(sorted((m, v) for m, _, v in stored)))
    if key in seen: return
    seen[key] = 1
    src = sources(t, aluf, stored)
    cands = []
    for a in src:
        for op in ('passa', 'msl', 'msr'):
            if op == 'passa' and a[0] is None: continue
            v = a[1] if op == 'passa' else (sh(a[1][0], 1 if op == 'msl' else 3), sh(a[1][1], 1 if op == 'msl' else 3))
            cands.append((op + ' ' + a[2], v))
    for a, b in itertools.combinations_with_replacement(src, 2):
        if a[0] is not None and b[0] is not None and a[0][0] == b[0][0] and a[0] != b[0]: continue
        if a[0] == b[0] and a[0] is not None: continue  # max(x,x) useless
        v = (un(a[1][0], b[1][0]), un(a[1][1], b[1][1]))
        if v[0] == G: continue
        cands.append(('fmax %s %s' % (a[2], b[2]), v))
    for name, v in cands:
        if v[0] == G: continue
        # store options
        opts = [None] + [m for m in MEMS + ['LM0']] if len(stored) < 3 else [None]
        for m in opts:
            ns = stored + ([(m, t, v)] if m else [])
            dfs(t + 1, v, ns, prog + [name + ((' ->' + m) if m else '')])
dfs(0, None, [], [])
print('best', best[0])
