# brute force: OR_m rot2(mask & rot1(x)) under a final permutation == rev64(x)?
import itertools, random
W = {'s':16,'i':32,'l':64}
M64 = (1<<64)-1
def lanes(v, n): return [(v >> (k*n)) & ((1<<n)-1) for k in range(64//n)]
def join(ls, n): return sum(x << (k*n) for k, x in enumerate(ls))
def rep(val, n): return join([val & ((1<<n)-1)]*(64//n), n)
def rot(x, sh, n, d):
    out = []
    for xv, sv in zip(lanes(x, n), lanes(sh, n)):
        s0 = sv % (2*n)
        if s0 >= n: s0 -= n
        if d == 'r': s0 = (n - s0) % n
        out.append(((xv << s0) | (xv >> (n - s0))) & ((1<<n)-1) if s0 else xv)
    return join(out, n)
def rev64(x): return int(f"{x:064b}"[::-1], 2)
funcs = {
 'pass': lambda m, n: m, 'not': lambda m, n: ~m, 'inc': lambda m, n: m+1, 'dec': lambda m, n: m-1,
 'neg': lambda m, n: -m,
}
masks = {p: rep(1 << (W[p]-1), W[p]) for p in 'sil'}
finals = {'id': lambda y: y, 'sw32': lambda y: rot(y, 32, 64, 'l'), 'rot16': lambda y: rot(y, 16, 64, 'l'),
          'rot48': lambda y: rot(y, 48, 64, 'l'), 'sw16': lambda y: rot(y, rep(16, 32), 32, 'l')}
xs = [random.getrandbits(64) for _ in range(4)] + [1 << b for b in range(64)]
found = 0
if __name__ == "__main__":
 for fn, P1 in itertools.product(funcs, "sil"):
    V = [rep(funcs[fn](m, W[P1]), W[P1]) & M64 for m in range(16)]
    for p1, d1, mk, p2, d2, dd in itertools.product('sil', 'lr', 'sil', 'sil', 'lr', range(16)):
        for fnm, fin in finals.items():
            ok = True
            for x in xs:
                acc = 0
                for m in range(16):
                    y = rot(x, V[m], W[p1], d1) & masks[mk]
                    acc |= rot(y, V[(m+dd) % 16], W[p2], d2)
                if fin(acc) != rev64(x): ok = False; break
            if ok:
                print(fn, P1, 'rot1', p1, d1, 'mask', mk, 'rot2', p2, d2, 'd', dd, 'final', fnm); found += 1
print('found', found)
