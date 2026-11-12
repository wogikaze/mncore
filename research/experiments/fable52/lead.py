#!/usr/bin/env python3
"""Leading-newline token model: each token is "\\n"+text; FizzBuzz = "\\nFizz"+"\\nBuzz" with the Buzz
half starting on the last 'z' of Fizz ('z'|'\\n'=='z'). Token index m=1 is "\\n1" at position -1."""
from model import stream, TOTAL, NBLK, N
toks = []  # (start, bytes, m, n, kind)
p = -1
m = 0
for n in range(1, N + 1):
    if n % 15 == 0:
        m += 1; toks.append((p, b"\nFizz", m, n, 'F')); p += 4
        m += 1; toks.append((p, b"\nBuzz", m, n, 'B')); p += 5
    elif n % 3 == 0:
        m += 1; toks.append((p, b"\nFizz", m, n, 'F')); p += 5
    elif n % 5 == 0:
        m += 1; toks.append((p, b"\nBuzz", m, n, 'B')); p += 5
    else:
        s = b"\n" + str(n).encode()
        m += 1; toks.append((p, s, m, n, 'N')); p += len(s)
# verify OR-rendering reproduces the stream
buf = bytearray(TOTAL + 16)
for (s, t, *_ ) in toks:
    for j, ch in enumerate(t):
        if 0 <= s + j < len(buf):
            buf[s + j] |= ch
assert bytes(buf[:TOTAL]) == stream.encode(), "OR rendering mismatch"
starts = [t[0] for t in toks]
import bisect
def toks_in_block(B):
    X = 8 * B
    out = []
    for idx in range(max(0, bisect.bisect_right(starts, X) - 3), min(len(toks), bisect.bisect_right(starts, X + 7) + 1)):
        s, t = toks[idx][0], toks[idx][1]
        if s < X + 8 and s + len(t) > X:
            out.append(idx)
    return out
if __name__ == "__main__":
    from collections import Counter
    c = Counter(); ex = []
    for B in range(NBLK):
        ids = toks_in_block(B)
        c[len(ids)] += 1
        if len(ids) >= 4: ex.append((B, repr(stream[8*B:8*B+8]), [toks[i][2] for i in ids]))
    print("tokens per block:", dict(sorted(c.items())))
    print("4-token blocks:", ex[:10])
