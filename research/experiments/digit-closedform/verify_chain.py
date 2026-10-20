#!/usr/bin/env python3
"""Numerically verify the exact semantics of the 93-word solution's T-chain.

The chain occupies source lines 42-48 of problems/challenge/20.fizzbuzz/answer.vsm:
  lsub x6 (ALU) + fvadd x6 (MAU).  It computes
      k = #{ i : r18 >= T_i(w) },   T = 2^23 + 2k,
  with
      w   = s4 = digits(number at byte s0) + 1       in {2,3,4,5}
      n1  = s0 + C_w,  C = {2:8, 3:13, 4:66, 5:599}
      M   = 8w + 39  (period length of the 15-number FizzBuzz pattern)
      r18 = n1 mod M
      T_i = w+8, 2w+8, 3w+13, 4w+23, 5w+33, 6w+33
and the six fvadds add 2.0 to T under the six OMR masks produced by the
lsubs, so T ends as the float whose bit pattern is 0x4b000000 + 2k.

Input: chain_data.csv, produced by collect_chain.py (all 4096 blocks, probes
after L41 and L48).  Run: python3 verify_chain.py
"""
from __future__ import annotations

import csv
import sys
from collections import Counter, defaultdict
from pathlib import Path

HERE = Path(__file__).resolve().parent
DATA = HERE / "chain_data.csv"
BASE = 0x4B000000
C = {2: 8, 3: 13, 4: 66, 5: 599}


def thresholds(w: int) -> list[int]:
    return [w + 8, 2 * w + 8, 3 * w + 13, 4 * w + 23, 5 * w + 33, 6 * w + 33]


def k_of(x: int, w: int) -> int:
    return sum(x >= t for t in thresholds(w))


def main() -> int:
    rows = list(csv.DictReader(DATA.open()))
    if len(rows) != 4096:
        print(f"FAIL: expected 4096 rows, got {len(rows)}")
        return 1
    fails: Counter[str] = Counter()
    examples: dict[str, list] = defaultdict(list)

    def bad(kind, row, detail):
        fails[kind] += 1
        if len(examples[kind]) < 5:
            examples[kind].append((row["b"], detail))

    for r in rows:
        b = int(r["b"])
        s0 = 8 * b
        w = int(r["s4"])
        if w not in C:
            bad("w", r, w)
            continue
        # s-tuple relations
        want = {"s128": w + 3, "s130": w + 5, "s132": w + 8, "s134": w + 10}
        for key, val in want.items():
            if int(r[key]) != val:
                bad("s-tuple", r, (key, r[key], val))
        # n1 and r18
        n1 = s0 + C[w]
        M = 8 * w + 39
        r18 = int(r["r18"])
        if r18 != n1 % M:
            bad("r18=n1%M", r, (r18, n1 % M))
        # k / T
        k = k_of(r18, w)
        t_hi = int(r["t0_hi"])
        # T bit pattern should be BASE + 2k
        if t_hi != BASE + 2 * k:
            bad("T=2^23+2k", r, (hex(t_hi), k))
        # all four cycles identical
        for cyc in range(4):
            if int(r[f"t{cyc}_hi"]) != t_hi or int(r[f"t{cyc}_lo"]) != int(r["t0_lo"]):
                bad("T cycles", r, cyc)

    # k as a function of r18 is w-dependent (32 r18 values differ across w)
    by_x: dict[int, dict[int, int]] = defaultdict(dict)
    for r in rows:
        by_x[int(r["r18"])][int(r["s4"])] = k_of(int(r["r18"]), int(r["s4"]))
    w_dep = {x: m for x, m in by_x.items() if len(set(m.values())) > 1}

    # A table indexed by r18>>3 with the residue table (the tempting closed
    # form) fails on many blocks; quantify it.
    residue_table = [0, 0, 1, 2, 2, 3, 3, 3, 4, 4, 4, 5, 6, 6, 6]
    bad_j = 0
    for r in rows:
        x = int(r["r18"])
        j = x >> 3
        pred = residue_table[j] if j < len(residue_table) else -1
        if pred != k_of(x, int(r["s4"])):
            bad_j += 1

    print(f"rows: {len(rows)}")
    print(f"failures: {dict(fails) if fails else 'none'}")
    for kind, ex in examples.items():
        print(f"  first {kind}: {ex}")
    print(f"r18 values where k depends on w: {len(w_dep)}")
    print("  sample:", dict(list(sorted(w_dep.items()))[:8]))
    print(f"residue-table indexed by r18>>3: {bad_j}/4096 blocks wrong")
    return 0 if not fails else 1


if __name__ == "__main__":
    sys.exit(main())
