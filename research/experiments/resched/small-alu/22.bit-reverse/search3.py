import itertools
W = {'s':16,'i':32,'l':64}
def perm_rot(n, r, d):
    r %= n
    if d == 'r': r = (n - r) % n
    return [ (b // n) * n + ((b % n) + r) % n for b in range(64)]
def eff(t, n):  # shift operand low bits t (0..127) for lane width n
    s0 = t % (2*n)
    return s0 - n if s0 >= n else s0
maskpos = {'s': {15,31,47,63}, 'i': {31,63}, 'l': {63}}
for p1, d1, mk, p2, d2 in itertools.product('sil', 'lr', 'sil', 'sil', 'lr'):
    good = {}
    for r1 in range(W[p1]):
        P1 = perm_rot(W[p1], r1, d1)
        for r2 in range(W[p2]):
            P2 = perm_rot(W[p2], r2, d2)
            sel = [b for b in range(64) if P1[b] in maskpos[mk]]
            if len(sel) == 4 and all(P2[P1[b]] == 63 - b for b in sel):
                good[(r1, r2)] = frozenset(sel)
    if not good: continue
    for d in range(16):
        # t values 0..127 ; pair (eff(t[m],p1), eff(t[m+d],p2)) in good, selections disjoint
        sol = None
        def dfs(m, t, used):
            global sol
            if sol: return
            if m == 16:
                # check all pairs
                sets = []
                for k in range(16):
                    key = (eff(t[k], W[p1]), eff(t[(k+d)%16], W[p2]))
                    if key not in good: return
                    sets.append(good[key])
                if len(frozenset().union(*sets)) == 64: sol = list(t)
                return
            for v in range(128):
                t.append(v)
                ok = True
                # check constraints that are fully determined
                for k in range(m+1):
                    j = (k+d) % 16
                    if j <= m:
                        key = (eff(t[k], W[p1]), eff(t[j], W[p2]))
                        if key not in good: ok = False; break
                if ok:
                    k1 = eff(v, W[p1])
                    dfs(m+1, t, used)
                t.pop()
                if sol: return
        dfs(0, [], set())
        if sol: print(p1, d1, mk, p2, d2, 'd', d, sol)
