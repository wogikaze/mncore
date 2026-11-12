#!/usr/bin/env python3
"""m-space token model: FizzBuzz split into "Fizz" + "Buzz\\n"; period = 16 tokens.

Token list for the whole stream; checks tokens-per-block and linear estimators per region.
"""
from model import *
toks = []  # (start, text, n, kind) kind: 'N','F','B','f'(FB fizz half),'b'(FB buzz half)
for n in range(1, N + 1):
    p = pos[n]
    last = (n == N)
    if n % 15 == 0:
        toks.append((p, "Fizz", n, 'f'))
        toks.append((p + 4, "Buzz" + ("" if last else "\n"), n, 'b'))
    elif n % 3 == 0:
        toks.append((p, "Fizz" + ("" if last else "\n"), n, 'F'))
    elif n % 5 == 0:
        toks.append((p, "Buzz" + ("" if last else "\n"), n, 'B'))
    else:
        toks.append((p, str(n) + ("" if last else "\n"), n, 'N'))
tstart = [t[0] for t in toks]
import bisect
def tok_at(X):
    return bisect.bisect_right(tstart, X) - 1
if __name__ == "__main__":
    from collections import Counter
    c = Counter()
    for b in range(NBLK):
        X = 8*b
        mf = tok_at(X); ml = tok_at(min(X+7, TOTAL-1))
        d = len(str(toks[mf][2]))
        c[(d, ml-mf+1)] += 1
        if ml-mf+1 >= 4: print("4tok", b, repr(block(b)), mf, ml)
    for k in sorted(c): print(k, c[k])
    print("ntokens", len(toks))
