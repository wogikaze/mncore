#!/usr/bin/env python3
"""Build the table-lookup candidate that replaces the 6-ALU/6-MAU T-chain.

Before L42 T = 2^23 in every word.  Four MAU `fvadd $t $const $m[...]` fill
LM0 words 97..112 with 0x4b000000 + 2*k(r); they ride on existing non-imm
ALU lines (L16, L37), or on the two freed chain lines (L42, L43), so they add
no ALU expressions.  The lookup is two ALU:
  llsr   $ls200 $lr6 $t    # T's address word = r18 >> 3
  lpassa $lmt96 $t         # T = table[r]; low word is 0x4b000000 + 2*k
r18 is kept in GRF1 long word 200 (word 201) so the shift can read GRF1 and
GRF0 in one instruction.
"""
from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
SRC = ROOT / "problems/challenge/20.fizzbuzz/answer.vsm"
OUT = Path(__file__).resolve().parent / "cand_table.vsm"
OUT51 = Path(__file__).resolve().parent / "cand_table_keep51.vsm"


def main():
    lines = SRC.read_text().splitlines()
    assert lines[15] == "ior $lr2v $t $nowrite", lines[15]
    assert lines[25] == 'imm f"63" $s3', lines[25]
    assert lines[36] == "fftoi $mauf $r19", lines[36]
    assert lines[76] == "lpassa $lr18 $t", lines[76]

    # r18 -> GRF1 long word 200 (low word 201)
    lines[36] = "fftoi $mauf $s201; fvadd $t $ls[108,112,112,112] $m[101,102,103,104]"
    lines[76] = "lpassa $ls200 $t"

    # Table: entry r at word 97+r, value 0x4b000000 + 2*k(r).
    lines[15] = lines[15] + "; fvadd $t $ls[200,200,104,108] $m[97,98,99,100]"

    # Replace L42-47 with the remaining table groups + gap + lookup.
    lines[41:47] = [
        "fvadd $t $lr[116,116,116,120] $m[105,106,107,108]",
        "fvadd $t $lr[124,124,124,124] $m[109,110,111,112]",
        'imm f"0.001" $lr72',
        "llsr $ls200 $lr6 $t",
        'imm f"0.01" $lr74',
        "lpassa $lmt96 $t",
    ]

    out = list(lines)

    def find(pred, start=0, what=""):
        for i in range(start, len(out)):
            if pred(out[i]):
                return i
        raise SystemExit(f"not found: {what}")

    # original L48 is now the first `fvadd ...; imm 0.01` line; it has been
    # superseded by the moved imm above.  Delete it.
    i = find(lambda s: s.startswith('fvadd $mauf $lr104 $t/$imr1; imm f"0.01"'), what="L48")
    del out[i]
    # original L49 imm 0.001 is now duplicated/moved; delete the old one.
    i = find(lambda s: s == 'imm f"0.001" $lr72', what="L49")
    del out[i]
    # original L51 fftoi to LM0 is dead (overwritten by canvas writes before
    # any read); delete it.
    i = find(lambda s: s == 'fftoi $lmt[18,18,16,16] $t', what="L51")
    del out[i]

    OUT.write_text("\n".join(out) + "\n")
    print(f"wrote {OUT}: {len(out)} lines")
    # Also emit the variant that keeps L51.  L51 is live (deleting it gives
    # 3673 mismatches), so this is the semantically closer broken candidate.
    out51 = list(out)
    for i, s in enumerate(out51):
        if s.startswith("fvfma $s20 $r130"):
            out51.insert(i + 1, "fftoi $lmt[18,18,16,16] $t")
            break
    else:
        raise SystemExit("no L50 line for L51 insertion")
    OUT51.write_text("\n".join(out51) + "\n")
    print(f"wrote {OUT51}: {len(out51)} lines")


if __name__ == "__main__":
    main()
