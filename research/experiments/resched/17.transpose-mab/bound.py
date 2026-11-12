#!/usr/bin/env python3
"""Line bound for the l1bmd gather -> (turnaround | L1BM) -> LM1 scheme (measured rules, see report).
Lines F..N carry gathers (F = first line where T is readable).  For each set R of L1BM-distribution lines:
  - LB at r: no gather at r, no L1BM-writing gather at r-1, r-2, reads 4 cycles gathered (to L1BM) at <= r-3.
  - every other line in F+1..N is a turnaround (TA) distribution: 2 useful cycles from the most recent gather
    (the turnaround register keeps its value across lines without a PE->L1BM transfer).
  - one gather per line (one LM0 read), 4 cycles each.
Need `need` useful slots (30 = 15 off-diagonal deltas x 2 wrap classes).  Greedy flow check."""
import itertools, sys
def feasible(F, N, need):
    lines = range(F, N + 1)
    best = None
    for k in range(0, N - F + 1):
        for R in itertools.combinations(range(F + 3, N + 1), k):
            R = set(R)
            G = [g for g in lines if g not in R and g < N]
            lbok = {g: (g + 1 not in R and g + 2 not in R) for g in G}
            TA = [r for r in range(F + 1, N + 1) if r not in R]
            # cycles left per gather
            left = {g: 4 for g in G}
            slots = 0
            for r in TA:
                src = max([g for g in G if g < r], default=None)
                if src is None or left[src] < 2: continue
                left[src] -= 2; slots += 2
            for r in sorted(R):
                take = 0
                for g in G:
                    if g <= r - 3 and lbok[g] and take < 4:
                        t = min(left[g], 4 - take); left[g] -= t; take += t
                slots += take
            if best is None or slots > best[0]: best = (slots, sorted(R))
    return best
need = int(sys.argv[1]) if len(sys.argv) > 1 else 30
for F in (2, 3):
    for N in range(11, 16):
        print(f"first gather line {F}, last line {N}: max slots {feasible(F, N, need)} (need {need})")

def exhaustive(F, N):
    best = None
    dl = list(range(F + 1, N + 1))
    for R in itertools.chain.from_iterable(itertools.combinations(range(F + 3, N + 1), k) for k in range(0, N - F)):
        R = set(R)
        G = [g for g in range(F, N) if g not in R]
        lbok = {g: (g + 1 not in R and g + 2 not in R) for g in G}
        rest = [r for r in dl if r not in R]
        for mask in range(1 << len(rest)):
            TA = [r for i, r in enumerate(rest) if mask >> i & 1]
            left = {g: 4 for g in G}; slots = 0; ok = True
            for r in TA:
                src = max([g for g in G if g < r], default=None)
                if src is None or left[src] < 2: ok = False; break
                left[src] -= 2; slots += 2
            if not ok: continue
            for r in sorted(R):
                take = 0
                for g in G:
                    if g <= r - 3 and lbok[g] and take < 4:
                        t = min(left[g], 4 - take); left[g] -= t; take += t
                slots += take
            if best is None or slots > best[0]: best = (slots, sorted(R), TA)
    return best
if len(sys.argv) > 2:
    print("exhaustive", sys.argv[2:], exhaustive(int(sys.argv[2]), int(sys.argv[3])))
