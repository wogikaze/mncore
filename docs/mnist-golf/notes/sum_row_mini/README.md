# sum_row_mini golf (target: 5 lines, current global top: 6)

Baseline: `problems/9.sumrow-mini/answer.vsm` = 6 lines (score 6 j=6 m=0).

## Current 6-line algorithm (decoded)

```
fvpassa $lm0v4 $nowrite                     # mauf = A[r,0:8]      (one row per cycle)
zero $nowrite; fvadd $lm2v4 $mauf $nowrite  # mauf = A[r,0:8]+A[r,8:16] (8 partials)
gbfn $mauf $nowrite; gmwrite $aluf $lx4     # BF(partials) -> aluf; zero rows 4-7
imm ui"0x3FC00000" $nowrite; gmwrite $aluf $lx0  # ones; write partials as matrix rows 0-3
gmmul $lx $aluf $ln0                        # x=BF(1.0): out[i]=S_i -> PE0=[S0,S1], PE1=[S2,S3]
msr $mauf $ln2                              # shift PE1->PE0: ln2 PE0=[S2,S3]
```

Facts confirmed with assemble3 / gpfn3_package_main:
- `imm ui"0x3FC00000"` is an *integer* immediate (not `immu`); 0x3FC00000 is BF-pseudo 1.0.
- aluf/mauf are previous-step forwarding; a same-step ALU result cannot feed gmwrite/gmmul.
- gmwrite reads the previous step's aluf; gmmul needs the matrix written the step before.
- Two LM0 read operands in one instruction always conflict (`lm0` vs `in_lm0`), also via T-index.
- Two LM1 destinations in one line conflict (`out_lm1` vs `out_lm1`).
- The msr direction is dest[p] = src[p+1]; to get S2,S3 into PE0 a shift line is unavoidable.

## Why 5 lines looks impossible

The minimal chain is strictly serial (each edge is a previous-step forwarding dependency):

read half1 -> add half2 -> BF-convert -> matrix write -> matrix-vector multiply -> PE shift

That is 6 steps. Removing the zero-row gmwrite gives an equivalent 5-instruction,
6-step program (`cand8`, ACCEPTED score=6). Breaking any edge needs an extra
instruction that does not fit in the reduced line budget:
- fold the two LM0 reads: assembler field conflict (cand1, cand7);
- write matrix directly from mauf: BF conversion cannot be skipped (raw floats
  decode as different BF values);
- put msr on gmmul's line: msr would read the stale mauf (cand6, cand9 also hit
  the two-LM1-write conflict);
- two gmmul's / permuted matrix rows: still needs the shift (cand4);
- all-ones matrix + x=data: gives uniform per-cycle sums and only 4 of the 8
  columns are usable in single precision (cand5, cand10).

## Candidates (all verified with run_problem.py)

| file | lines | result |
|---|---|---|
| cand1 | 5 | assemble error: `lm0`/`in_lm0` conflict (two LM0 reads in one fvadd) |
| cand2 | 5 | judge mismatch: ln2 never written (msr dropped) |
| cand3 | 5 | assemble error: gmmul cannot take two dst operands |
| cand4 | 5 | judge mismatch: permuted rows fill ln2 only; ln0 empty |
| cand5 | 4 | judge mismatch: uniform sums; f-precision matvec uses only cols 0,2,4,6 |
| cand6 | 5 | assemble error: `out_lm1`/`out_lm1` conflict (gmmul+msr same step) |
| cand7 | 6 | assemble error: `lm0`/`in_lm0` conflict (T-index second read) |
| cand8 | 6 | **ACCEPTED score=6** (reference-equivalent, cold rows 4-7) |
| cand9 | 5 | assemble error: `out_lm1` conflict |
| cand10 | 5 | judge mismatch: uniform sums |

Best found = 6 lines (no improvement).
