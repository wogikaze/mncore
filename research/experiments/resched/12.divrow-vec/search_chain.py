"""Search 4-op MAU chains (L4..L7) from a magic seed p (aluf at L4) to a2 ~ 1/b.
Constants: c1 available from L5 (aluf) and as register from L6; c2 from L6, c3 from L7.
Values are homogeneous in p: (deg, f(e)), value = p^deg * f(e); b = (deg -1, 1-e).
Only homogeneous fma/mul/add ops are kept (others cannot cancel p)."""
import sympy as sp, itertools
e, c1, c2, c3 = sp.symbols('e c1 c2 c3')
P = ('p', (1, sp.Integer(1))); Bv = ('b', (-1, 1 - e))
def ops(xs, zs):
    out = []
    for (nx, (dx, fx)), (ny, (dy, fy)) in itertools.combinations_with_replacement(xs, 2):
        d = dx + dy
        for sx in (1, -1):
            out.append((f"{'-' if sx<0 else ''}{nx}*{ny}", (d, sp.expand(sx * fx * fy))))
            for nz, (dz, fz) in zs:
                if dz != d: continue
                for sz in (1, -1):
                    out.append((f"{'-' if sx<0 else ''}{nx}*{ny}{'+' if sz>0 else '-'}{nz}", (d, sp.expand(sx * fx * fy + sz * fz))))
    return out
def C(name, sym): return (name, (0, sym))
res = []
for n4, X4 in ops([P, Bv], [P, Bv]):
    v4 = ('X4', X4)
    for n5, X5 in ops([v4, C('c1', c1), P, Bv], [v4, C('c1', c1), P, Bv]):
        v5 = ('X5', X5)
        for n6, X6 in ops([v5, C('c2', c2), P, v4, C('c1', c1), Bv], [v5, C('c2', c2), P, v4, C('c1', c1), Bv]):
            v6 = ('X6', X6)
            for n7, X7 in ops([v6, C('c3', c3), P, v4, v5, C('c1', c1), C('c2', c2), Bv],
                              [v6, C('c3', c3), P, v4, v5, C('c1', c1), C('c2', c2), Bv]):
                if X7[0] != 1 or 'X6' not in n7: continue
                f = X7[1]
                if sp.degree(f, e) < 3: continue
                co = [f.coeff(e, i) for i in range(4)]
                try:
                    sol = sp.solve([co[0] - 1, co[1] - 1, co[2] - 1], [c1, c2, c3], dict=True)
                except Exception:
                    continue
                for s in sol:
                    c3v = sp.simplify(co[3].subs(s))
                    if c3v.free_symbols or not all(complex(v).imag == 0 for v in s.values() if not v.free_symbols): continue
                    if abs(complex(c3v) - 1) < 0.25:
                        print(n4, '|', n5, '|', n6, '|', n7, s, 'e3:', c3v, flush=True)
                        res.append(1)
print('done', len(res))
