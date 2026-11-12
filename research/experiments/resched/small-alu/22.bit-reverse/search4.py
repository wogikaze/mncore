# like search.py but V from mabid or peid (per PE), various unary ops, finals id/sw32
import itertools, random, sys
from search import rot, rep, rev64, masks, W, M64
funcs = {'pass': lambda v: v, 'not': lambda v: ~v, 'inc': lambda v: v+1, 'dec': lambda v: v-1}
xs = [random.getrandbits(64) for _ in range(3)] + [1 << b for b in range(64)]
finals = {'id': lambda y: y}
for src in ['mabid', 'peid']:
  for fn, P1 in itertools.product(funcs, 'sil'):
    for p1, d1, mk, p2, d2, dd in itertools.product('sil', 'lr', 'sil', 'sil', 'lr', range(16)):
        ok = True
        for pe in range(4) if src == 'peid' else [0]:
            val = (lambda m: 4*m+pe) if src == 'peid' else (lambda m: m)
            V = [rep(funcs[fn](val(m)), W[P1]) & M64 for m in range(16)]
            for x in xs:
                acc = 0
                for m in range(16):
                    y = rot(x, V[m], W[p1], d1) & masks[mk]
                    acc |= rot(y, V[(m+dd) % 16], W[p2], d2)
                if acc != rev64(x): ok = False; break
            if not ok: break
        if ok: print(src, fn, P1, p1, d1, mk, p2, d2, dd)
print("end")
