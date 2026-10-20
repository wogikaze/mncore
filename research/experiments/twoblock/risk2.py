#!/usr/bin/env python3
"""Risk analysis for a 2-candidate digit stage, done against the official
testcase expectation bytes.

Definitions used here (the ones that decide correctness):

  intersecting numbers of word b = the numbers whose rendering touches bytes
      8b..8b+7  (up to 4 of them, measured: 104/2446/1543/3)
  DIGIT OWNERS of word b = the numbers that own at least one *digit* character
      inside the word.  A renderer that computes k numbers' digits can render
      the word iff k >= #digit owners (letters are phase-determined and can be
      served by a canvas/template, or by the owners' own 5/9-byte renderings).

Outputs:
  risk_digitowners.csv    one row per word (all 4096): owners, offsets, digit
                          positions, digit counts.  2cand_ok=false marks words
                          that a 2-owner renderer cannot serve (there are none).
  summary on stdout.

Run: python3 risk2.py
"""
from __future__ import annotations

import csv
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "offset-inversion"))
import ref  # noqa: E402

pieces, out, L, owner = ref.build()
EXPECT = ref.official_expectation()


def main() -> int:
    # 0) reference is the official expectation, byte for byte
    assert len(out) == len(EXPECT) == 32766
    assert out == EXPECT, "reference diverges from the official testcase"
    print("reference == official testcase expectation: 32766/32766 bytes, 0 mismatches")

    rows = []
    hist_owners = {}
    hist_digits = {}
    hist_gap = {}
    sig = {}
    bad = []
    for b in range(4096):
        lo, hi = 8 * b, min(8 * b + 7, len(owner) - 1)
        first = owner[lo][0]
        owners: dict[int, list[int]] = {}
        ndig = 0
        for i in range(lo, hi + 1):
            n, k = owner[i]
            if 48 <= pieces[n - 1][k] <= 57:
                owners.setdefault(n, []).append(i - lo)
                ndig += 1
        ns = sorted(owners)
        hist_owners[len(ns)] = hist_owners.get(len(ns), 0) + 1
        hist_digits[ndig] = hist_digits.get(ndig, 0) + 1
        gap = tuple(n - first for n in ns)
        hist_gap[gap] = hist_gap.get(gap, 0) + 1
        sig[(gap, tuple(tuple(owners[n]) for n in ns))] = \
            sig.get((gap, tuple(tuple(owners[n]) for n in ns)), 0) + 1
        ok = len(ns) <= 2
        if not ok:
            bad.append(b)
        rows.append(dict(
            word=b,
            block="A" if b < 2048 else "B",
            byte_lo=lo,
            byte_hi=hi,
            n_intersect=len({owner[i][0] for i in range(lo, hi + 1)}),
            n_digit_owners=len(ns),
            owners=" ".join(str(n) for n in ns),
            first_number=first,
            offsets=" ".join(str(n - first) for n in ns),
            digit_positions="|".join(",".join(str(p) for p in owners[n]) for n in ns),
            n_digits=ndig,
            ok_2cand=int(ok),
            text=out[lo:hi + 1].decode("latin-1").encode("unicode_escape").decode(),
        ))

    # naive renderer: candidates = first two *intersecting* numbers (wrong rule).
    # A word is corrupted iff a digit owner is not one of the first two
    # intersecting numbers.
    naive = []
    for r in rows:
        first_two = {r["first_number"], r["first_number"] + 1}
        owners = {int(x) for x in r["owners"].split()} if r["owners"] else set()
        if not owners <= first_two:
            naive.append(r)
    import csv as _csv
    with open(HERE / "risk_naive_first2.csv", "w", newline="") as fh:
        w = _csv.DictWriter(fh, fieldnames=list(rows[0].keys()))
        w.writeheader()
        w.writerows(naive)
    print(f"\nnaive 'first two intersecting numbers' renderer corrupts "
          f"{len(naive)} words ({sum(1 for r in naive if r['block']=='A')} block A, "
          f"{sum(1 for r in naive if r['block']=='B')} block B), "
          f"{sum(r['n_digits'] for r in naive)} digit bytes")
    with open(HERE / "risk_digitowners.csv", "w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=list(rows[0].keys()))
        w.writeheader()
        w.writerows(rows)

    print(f"\ndigit owners per word: {dict(sorted(hist_owners.items()))}")
    print(f"digit chars per word : {dict(sorted(hist_digits.items()))}")
    print(f"words needing >2 digit owners: {len(bad)}  => 2-candidate digit stage is SUFFICIENT"
          if not bad else f"words needing >2 digit owners: {len(bad)}  => NOT sufficient")
    print("\noffset of each digit owner relative to the first intersecting number:")
    for k, v in sorted(hist_gap.items(), key=lambda kv: -kv[1]):
        print(f"  {str(k):16s} {v:5d}")
    print(f"\ndistinct (offsets, digit positions) signatures: {len(sig)}")
    print("words with two non-adjacent digit owners (n, n+2):",
          sum(v for k, v in hist_gap.items() if k == (0, 2)))
    print("\nfirst 8 rows:")
    for r in rows[:8]:
        print(f"  word {r['word']:4d} [{r['block']}] {r['text']:18s} owners={r['owners']:12s} "
              f"offsets={r['offsets']:6s} pos={r['digit_positions']:18s} ndig={r['n_digits']}")
    print("\nwrote risk_digitowners.csv")
    return 0 if not bad else 1


if __name__ == "__main__":
    raise SystemExit(main())
