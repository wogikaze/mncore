#!/usr/bin/env python3
"""Reference model of the token/shift design (exact integer arithmetic).

Token index m (m=1 is "1\\n"); 16 tokens per 15 numbers: q=m//16, i=m%16, n=m-q.
"""
from model import stream, TOTAL, NBLK
NUM_I = {1, 2, 4, 7, 8, 11, 13, 14}
FIZ_I = {3, 6, 9, 12, 15}
BUZ_I = {0, 5, 10}
NNLE_I = [0, 1, 2, 2, 3, 3, 3, 4, 5, 5, 5, 6, 6, 7, 8, 8]
CONSTD = {1: 0, 2: 5, 3: 58, 4: 591}
BIAS = {1: (0x0000, 0x00300A00), 2: (0x0000, 0x30300A00), 3: (0x0030, 0x30300A00), 4: (0x3030, 0x30300A00)}
MASK64 = (1 << 64) - 1

def region(B):
    return 1 if B < 4 else 2 if B < 51 else 3 if B < 584 else 4

def text_lanes(m, d):
    q, i = divmod(m, 16)
    n = m - q
    if i in NUM_I:
        D3, D2, D1, D0 = (n // 1000) % 10, (n // 100) % 10, (n // 10) % 10, n % 10
        bh, bl = BIAS[d]
        return 256 * D3 + D2 + bh, 65536 * (256 * D1 + D0) + bl
    hi = 0x4669 if i in FIZ_I else 0x4275
    lo = 0x7A7A0000 if i == 15 else 0x7A7A0A00
    return hi, lo

def shift_s8(m, d, X):
    q, i = divmod(m, 16)
    e = 4 - d
    return 5 * m - q - e * (8 * q + NNLE_I[i]) - CONSTD[d] - 7 - X   # bytes; >0: right shift

def contrib(m, d, X, hw=True):
    hi, lo = text_lanes(m, d)
    V = ((hi & 0xffffffff) << 32) | (lo & 0xffffffff)
    s = 8 * shift_s8(m, d, X)
    if hw:
        ra = s % 128
        A = (V >> ra) if ra < 64 else 0
        la = (-s) % 128
        Bv = ((V << la) & MASK64) if (la < 64 and s <= 0) else 0   # zero-flushed when s > 0
        return A | Bv
    if s >= 0:
        return V >> s if s < 64 else 0
    return (V << -s) & MASK64 if -s < 64 else 0

def block_from(m0, B, hw=True):
    d = region(B); X = 8 * B
    out = 0
    for k in range(4):
        if m0 + k >= 1:
            out |= contrib(m0 + k, d, X, hw)
    return out

def want(B):
    s = stream[8 * B: 8 * B + 8].encode("latin-1")
    return int.from_bytes(s.ljust(8, b"\0"), "big"), len(s)

def allowed_m0(B, hw=True):
    w, ln = want(B)
    mask = MASK64 if ln == 8 else (MASK64 >> (8 * ln)) ^ MASK64
    ok = []
    approx = None
    from m_tokens import tok_at
    mf = tok_at(8 * B) + 1
    for m0 in range(max(1, mf - 6), mf + 4):
        if (block_from(m0, B, hw) & mask) == w:
            ok.append(m0)
    return ok

if __name__ == "__main__":
    from collections import Counter
    c = Counter(); bad = []
    A = []
    for B in range(NBLK):
        ok = allowed_m0(B)
        A.append(ok)
        c[len(ok)] += 1
        if not ok: bad.append(B)
    print("allowed-set sizes:", dict(c), "blocks with none:", bad[:20])
    import pickle; pickle.dump(A, open("/tmp/allowed.pkl", "wb"))
