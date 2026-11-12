# Enumerate 2-op T (and BAR+T) formulas from two fixed-id inputs (32-bit int model), check target designs.
M = 0xffffffff
def ops():
    yield 'add', lambda x, y: (x + y) & M
    yield 'sub', lambda x, y: (x - y) & M
    yield 'lsl', lambda x, y: (x << (y & 63)) & M if (y & 63) < 32 else 0
    yield 'lsr', lambda x, y: (x >> (y & 63)) if (y & 63) < 32 else 0
    yield 'or', lambda x, y: x | y
    yield 'xor', lambda x, y: x ^ y
    yield 'and', lambda x, y: x & y
    yield 'packbit', lambda x, y: ((x << 1) | (y >> 31)) & M
    yield 'max', lambda x, y: max(x, y)
    yield 'min', lambda x, y: min(x, y)
    yield 'bsl', lambda x, y: ((x << (y % 32)) | (x >> (32 - y % 32))) & M if y % 32 else x
    yield 'passa', lambda x, y: x
    yield 'inc', lambda x, y: (x + 1) & M
    yield 'dec', lambda x, y: (x - 1) & M
    yield 'not', lambda x, y: (~x) & M
    yield 'lnot', lambda x, y: 1 if x == 0 else 0
OPS = list(ops())
def ids(l2b, l1b, mab, pe):
    return {'l2bid': l2b, 'l1bid': l1b, 'mabid': mab, 'peid': 4 * mab + pe, 'subpeid': pe, 'msb1': 0x80000000}
# line1: op1(id1, y1) with y1 in {0, msb1-from-reg? no}: second input is a zero register or an imm constant is not available.
# targets: function (l2b,l1b,mab,pe)->set of acceptable addresses or None (don't care); T+ADDR must hit; ADDR>=0 const multiple of 4
def tgt_D1(l2b, l1b, mab, pe):
    if l2b % 2 or l1b >= 4: return None
    R = 2 * l2b + l1b; return range(4 * R, 4 * R + 4)
def tgt_D2(l2b, l1b, mab, pe):
    R = 4 * (l1b >> 1) + (l1b & 1) + 2 * (l2b & 1); return range(4 * R, 4 * R + 4)
def tgt_D3(l2b, l1b, mab, pe):
    R = 4 * (l1b >> 1) + (l1b & 1); return range(4 * R, 4 * R + 4)
pts = [(a, b, 0, 0) for a in range(8) for b in range(8)]
def check(f, tgt):
    for K in range(0, 64, 4):
        ok = True
        for p in pts:
            t = tgt(*p)
            if t is None: continue
            v = f(*p)
            if v is None or ((v + K) & 0xfff) not in t: ok = False; break
        if ok: return K
    return None
found = 0
for tname, tgt in [('D1', tgt_D1), ('D2', tgt_D2), ('D3', tgt_D3)]:
    # single op
    for n1, o1 in OPS:
        for i1 in ['l2bid', 'l1bid', 'msb1']:
            for y in [0, 0x80000000]:
                f = lambda a, b, m, p: o1(ids(a, b, m, p)[i1], y)
                K = check(f, tgt)
                if K is not None: print(tname, 'single', n1, i1, y, K); found += 1
    for n1, o1 in OPS:
        for i1 in ['l2bid', 'l1bid', 'msb1']:
            for n2, o2 in OPS:
                for i2 in ['l2bid', 'l1bid', 'msb1']:
                    for mode in ['T', 'BAR+T']:
                        def f(a, b, m, p):
                            d = ids(a, b, m, p); A = o1(d[i1], 0); B = o2(d[i2], A)
                            return B if mode == 'T' else (A & 0xfff) + B
                        K = check(f, tgt)
                        if K is not None: print(tname, mode, n1, i1, n2, i2, K); found += 1
print('found', found)
