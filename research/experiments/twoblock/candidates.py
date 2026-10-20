#!/usr/bin/env python3
"""How much of each 8-byte block comes from the 3rd/4th intersecting number?

For every word b, split its 8 bytes by which intersecting number (candidate
index 0..3) owns them, and count digit characters per candidate.  This is the
"2-candidate risk" measure: what a 2-candidate-per-block renderer would miss.

Run: python3 candidates.py
"""
from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "offset-inversion"))
import ref  # noqa: E402

pieces, out, L, owner = ref.build()


def is_digit(n: int, k: int) -> bool:
    """Is character k of number n's rendering a decimal digit?"""
    s = pieces[n - 1]
    return 48 <= s[k] <= 57


def main() -> int:
    hist_digits = {}
    hist_digits_by_cand = [0, 0, 0, 0]
    words_with_cand23_digits = 0
    digits_from_cand23 = 0
    per_block = []
    for b in range(4096):
        lo, hi = 8 * b, 8 * b + 7
        cands = sorted({owner[i][0] for i in range(lo, min(hi + 1, len(owner)))})
        ndig = [0, 0, 0, 0]
        nchar = [0, 0, 0, 0]
        for i in range(lo, hi + 1):
            if i >= len(owner):
                break
            n, k = owner[i]
            ci = cands.index(n)
            nchar[ci] += 1
            if is_digit(n, k):
                ndig[ci] += 1
        tot = sum(ndig)
        hist_digits[tot] = hist_digits.get(tot, 0) + 1
        for c in range(4):
            hist_digits_by_cand[c] += ndig[c]
        if ndig[2] or ndig[3]:
            words_with_cand23_digits += 1
            digits_from_cand23 += ndig[2] + ndig[3]
        per_block.append((b, len(cands), tuple(ndig), tuple(nchar), tot))

    print("digits-per-word histogram:", dict(sorted(hist_digits.items())))
    print("total digit chars per candidate index:", hist_digits_by_cand)
    print(f"words needing digits from candidate 2/3: {words_with_cand23_digits}")
    print(f"digit chars from candidate 2/3: {digits_from_cand23}")
    print()
    print("words (block A only, b<2048) needing cand2 digits:", sum(1 for b, nc, nd, nch, t in per_block if b < 2048 and nd[2]))
    print("words (block A only, b<2048) needing cand3 digits:", sum(1 for b, nc, nd, nch, t in per_block if b < 2048 and nd[3]))
    print("words (block B only, b>=2048) needing cand2 digits:", sum(1 for b, nc, nd, nch, t in per_block if b >= 2048 and nd[2]))
    print("words (block B only, b>=2048) needing cand3 digits:", sum(1 for b, nc, nd, nch, t in per_block if b >= 2048 and nd[3]))
    print()
    # how many *characters* from cand>=2 (letters included)?
    wl = sum(1 for b, nc, nd, nch, t in per_block if nch[2] or nch[3])
    print(f"words with ANY char from candidate 2/3: {wl}")
    hist_cands = {}
    for b, nc, nd, nch, t in per_block:
        hist_cands[nc] = hist_cands.get(nc, 0) + 1
    print("numbers-per-word histogram:", dict(sorted(hist_cands.items())))

    # If block A gets 2 candidates and block B gets 2, which words are wrong?
    print()
    print("example words with cand2 digits (block A):")
    shown = 0
    for b, nc, nd, nch, t in per_block:
        if b < 2048 and nd[2] and shown < 12:
            lo, hi = 8 * b, 8 * b + 7
            cands = sorted({owner[i][0] for i in range(lo, min(hi + 1, len(owner)))})
            print(f"  b={b} bytes={lo} cands={cands} digits_per_cand={nd} text={out[lo:hi+1]!r}")
            shown += 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
