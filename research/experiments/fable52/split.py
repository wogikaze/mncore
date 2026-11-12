#!/usr/bin/env python3
"""Lane-type split model: text lanes take v = h0 + k' (k'=0,1), number lanes u = h0 + 1 + k'.
v-th text token (v-1 = 8Q+j) -> m = 16Q + 2j + p(j); u-th number (u-1 = 8Q+j) -> m = 16Q + 2j + 1 - p(j).
Token m rendering/placement as in trail.py (end-aligned E=5, hardware shift semantics)."""
import pickle
from trail import V_of, place, want, E, MASK64, NBLK, byM
def par(j): return bin(j).count("1") & 1
def m_text(v):
    Q, j = divmod(v - 1, 8); return 16 * Q + 2 * j + par(j)
def m_num(u):
    Q, j = divmod(u - 1, 8); return 16 * Q + 2 * j + 1 - par(j)
def render(B, h0):
    X = 8 * B; out = 0
    for m in (m_text(h0), m_text(h0 + 1), m_num(h0 + 1), m_num(h0 + 2)):
        v, pe = V_of(m)
        if pe is None: continue
        out |= place(v, pe - X - E)
    return out
if __name__ == "__main__":
    # sanity: m_num/m_text enumerate the right tokens
    assert all(byM[m_num(u)][1][:1].isdigit() for u in range(1, 3000))
    assert all(not byM[m_text(v)][1][:1].isdigit() for v in range(2, 3000))
    from collections import Counter
    A = []; c = Counter()
    for B in range(NBLK):
        w, mask = want(B)
        guess = (8 * B) // 10
        ok = [h for h in range(max(0, guess - 40), guess + 40) if render(B, h) & mask == w]
        A.append(ok); c[len(ok)] += 1
    print("allowed h0 count per block:", dict(sorted(c.items())))
    print("blocks with none:", [B for B in range(NBLK) if not A[B]][:20])
    print("non-contiguous:", [B for B in range(NBLK) if A[B] and A[B] != list(range(A[B][0], A[B][-1] + 1))][:10])
    pickle.dump(A, open("/tmp/allowed_split.pkl", "wb"))
