# which (rot1,mask,rot2) configs admit per-MAB amounts (r1,r2) giving rev64 with no final perm?
import itertools
W = {'s':16,'i':32,'l':64}
def perm_rot(n, r, d):  # position map for rotation of 64-bit by lanes of n
    r %= n
    if d == 'r': r = (n - r) % n
    return [ (b // n) * n + ((b % n) + r) % n for b in range(64)]
maskpos = {'s': {15,31,47,63}, 'i': {31,63}, 'l': {63}}
for p1, d1, mk, p2, d2 in itertools.product('sil', 'lr', 'sil', 'sil', 'lr'):
    good = {}
    for r1 in range(W[p1]):
        P1 = perm_rot(W[p1], r1, d1)
        for r2 in range(W[p2]):
            P2 = perm_rot(W[p2], r2, d2)
            sel = [b for b in range(64) if P1[b] in maskpos[mk]]
            if all(P2[P1[b]] == 63 - b for b in sel):
                good[(r1, r2)] = frozenset(sel)
    full = [k for k, v in good.items() if len(v) == 4]
    if len(set().union(*[good[k] for k in full]) if full else set()) == 64:
        print(p1, d1, mk, p2, d2, 'pairs with 4 bits:', len(full), sorted(full)[:20])
