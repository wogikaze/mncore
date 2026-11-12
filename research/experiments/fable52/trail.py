#!/usr/bin/env python3
"""Trailing-newline, END-aligned token model.

Token m (1-based): number "n\\n" | "Fizz\\n" | "Buzz\\n" | FizzHalf "Fizz" (i=15).
V(m): 64-bit, token's last byte at V byte E (0 = MSB); leading zeros are NUL.
Placement: right shift by s = pos_end(m) - X - E bytes (hardware llsr/llsl semantics).
"""
from model import stream, TOTAL, NBLK, N
MASK64 = (1 << 64) - 1
E = 5
toks = []   # (pos_start, text_bytes, m, n, i)
p = 0; m = 0
for n in range(1, N + 1):
    last = (n == N)
    nl = b"" if last else b"\n"
    if n % 15 == 0:
        m += 1; toks.append((p, b"Fizz", m, n, 15)); p += 4
        m += 1; toks.append((p, b"Buzz" + nl, m, n, 0)); p += 5
    else:
        m += 1
        i = m % 16
        t = b"Fizz" if n % 3 == 0 else b"Buzz" if n % 5 == 0 else str(n).encode()
        toks.append((p, t + nl, m, n, i)); p += len(t) + len(nl)
assert all(t[2] % 16 == t[4] for t in toks)
byM = {t[2]: t for t in toks}
MMAX = m
def V_of(mm):
    if mm not in byM: return 0, None
    s0, txt, *_ = byM[mm]
    v = 0
    for j, ch in enumerate(txt):
        v |= ch << (8 * (7 - (E - len(txt) + 1 + j)))
    return v, s0 + len(txt) - 1     # value, pos_end
def place(v, s):
    a = (8 * s) % 128
    r = (v >> a) if a < 64 else 0
    b = (-8 * s) % 128
    l = ((v << b) & MASK64) if b < 64 else 0
    return r | l
def want(B):
    s = stream[8 * B: 8 * B + 8].encode("latin-1")
    w = int.from_bytes(s.ljust(8, b"\0"), "big")
    mask = MASK64 if len(s) == 8 else MASK64 ^ (MASK64 >> (8 * len(s)))
    return w, mask
def render(B, m0, ncand=4):
    X = 8 * B
    out = 0; ss = []
    for k in range(ncand):
        v, pe = V_of(m0 + k)
        if pe is None: ss.append(None); continue
        s = pe - X - E
        ss.append(s)
        out |= place(v, s)
    return out, ss
import bisect
starts = [t[0] for t in toks]
def first_tok(X):
    return toks[bisect.bisect_right(starts, X) - 1][2]
if __name__ == "__main__":
    from collections import Counter
    import pickle
    A = []
    srng = Counter()
    for B in range(NBLK):
        w, mask = want(B)
        mf = first_tok(8 * B)
        ok = []
        for m0 in range(max(1, mf - 4), mf + 3):
            out, ss = render(B, m0)
            if out & mask == w:
                ok.append(m0)
        A.append(ok)
        srng[len(ok)] += 1
    print("allowed m0 count per block:", dict(srng))
    print("blocks with no m0:", [B for B in range(NBLK) if not A[B]][:20])
    pickle.dump(A, open("/tmp/allowed_trail.pkl", "wb"))
