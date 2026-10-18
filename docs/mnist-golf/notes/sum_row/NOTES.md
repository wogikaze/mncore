# sum_row golf: pursuit of a 15-line solution (from 16)

Baseline: `problems/10.sumrow/answer.vsm` = 16 lines, ACCEPTED (score 16).

## What the 16-line answer does
- lines 1-3 setup: `imm 4`, `ilsl $mabid $aluf $lt` (T = 16*mabid), `imm 1.0` (also the T hazard gap)
- lines 4-8: 4 single-precision (f) passes, each 4 columns (word 0/1/2/3 of each row), accumulated
  through `$mauf`; line 8 writes the 4 rows of each MAB to GRF0/GRF1/LM1.
- lines 9-16 gather: 3 M4writes (MABs 1,5,9,13 / 2,6,10,14 / 3,7,11,15) + 3 M4bcasts feed
  MAB0's LM1 words 4-15 and fill the aggregators MAB4/8/12 (GRF0 words 4-15); then
  3 Mwrites (MAB4/8/12, 16 rows each) + 3 Mbcasts deliver rows 16-63. 12 ops, 8 lines.

## Hard constraints found
- T write -> T read (and any GRF write -> read) needs a 7-cycle distance: the read must be
  2 steps after the write. So the compute needs 3 setup lines and can start passes at line 4.
- 4 single-precision passes need 5 lines (fbfn at L4..L7, fma at L5..L8) => 8 compute lines.
- Gather: each broadcast delivers at most 16 words to MAB0's LM1 (4 words/cycle x 4 cycles,
  `ll` destinations). Aggregators need their 12 extra rows from 3 stage-1 broadcasts
  (each stage-1 broadcast gives only 4 rows per recipient). This chain forces 8 gather lines.
- Two L1BM collects cannot share a line; two MAU calc ops cannot share a line;
  static LM0 addresses must be even (odd only via T-indirect).
- `$lbi` vs `$llbi` width must match the turnaround width (transcription trap).

## 15-line attempts (all rejected)
- `imm 0x3F800004` as both shift amount (low 6 bits = 4) and matrix value: the shift works
  (`ilsl` uses b % 64) and BF-single 1.0 is 0x3FC00000, so a near-1.0 trick is possible,
  but the T hazard still needs the gap line: no line saved.
- 3-pass mixed precision (G = pseudo-single, 18-bit, 8 columns; 2 f passes, 8 columns):
  15 lines, assembles, but max |error| ~1.3-1.45e-4 > atol 1e-4 (8-11 of 256 values fail).
  Tried G on words (0,1) vs (2,3), G first/middle/last, and all 16 per-cycle flat-list
  column assignments: best = 8 violations, max 1.45e-4.
- The error is the 18-bit mantissa of the pseudo-single matvec; the exact 4-pass f version
  needs 8 compute lines, and the gather cannot be compressed below 8 lines (dependency
  chain: 3 stage-1 broadcasts -> aggregator complete -> 3 transfers -> 3 broadcasts).

Conclusion: no ACCEPTED solution with score <= 15 was found; best remains 16 lines.

## Verified boundary results
- 15 lines with 3 passes (1 pseudo-single pass of 8 columns + 2 single passes of 4 columns)
  is the only 15-line shape that assembles and computes the right thing; every variant
  exceeds atol=1e-4:
  | variant | G block | max abs err | violations |
  |---|---|---|---|
  | cand15b | words 0,1 | 1.45e-4 | 11/256 |
  | cand15c | words 2,3 | 1.37e-4 | 10/256 |
  | cand15e | words 2,3 (F/G/F order) | 1.37e-4 | 10/256 |
  | cand15f | words 0,1 (F/G/F order) | 1.45e-4 | 11/256 |
  | brute per-cycle best (2,0,2,0) | mixed | 1.45e-4 | 8/256 |
  The 4-pass single-precision version is exact (max err 1.5e-5) but needs 8 compute lines.
- Byte-identical reproduction of the near-miss: `near_miss_15line_gmix.vsm` (15 lines).
