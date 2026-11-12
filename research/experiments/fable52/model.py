#!/usr/bin/env python3
"""Stream model helpers for FizzBuzz 1..6334."""
def line(n):
    if n % 15 == 0: return "FizzBuzz"
    if n % 3 == 0: return "Fizz"
    if n % 5 == 0: return "Buzz"
    return str(n)
N = 6334
lines = {n: line(n) + "\n" for n in range(1, N + 1)}
lines[N] = line(N)
pos = {}
p = 0
for n in range(1, N + 1):
    pos[n] = p
    p += len(lines[n])
TOTAL = p
stream = "".join(lines[n] for n in range(1, N + 1))
assert TOTAL == 32766 and len(stream) == TOTAL
NBLK = 4096
def block(b):
    return stream[8*b:8*b+8]
# line containing byte X
import bisect
starts = [pos[n] for n in range(1, N + 1)]
def line_at(X):
    return bisect.bisect_right(starts, X)  # n with pos[n] <= X < pos[n+1]
if __name__ == "__main__":
    from collections import Counter
    c = Counter()
    worst = {}
    for b in range(NBLK):
        X = 8*b
        nf = line_at(X)
        nl = line_at(min(X+7, TOTAL-1))
        cnt = nl - nf + 1
        d = len(str(nf))
        c[(d, cnt)] += 1
    for k in sorted(c): print(k, c[k])
    # half-block counts
    c2 = Counter()
    for h in range(2*NBLK):
        X = 4*h
        if X >= TOTAL: continue
        nf = line_at(X); nl = line_at(min(X+3, TOTAL-1))
        c2[(len(str(nf)), nl-nf+1)] += 1
    print("half-blocks:")
    for k in sorted(c2): print(k, c2[k])
