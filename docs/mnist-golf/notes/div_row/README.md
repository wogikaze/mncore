# div_row golf attempts (target j+m <= 28)

Baseline: `problems/12.divrow-vec/answer.vsm` (syttrea) = 29 j lines, official judge ACCEPTED score=29.

All candidates below are <= 28 source lines and were checked with
`python3 problems/run_problem.py 12.divrow-vec --solution <cand>`; none is ACCEPTED.

| file | lines | result |
|---|---|---|
| cand1.vsm | 28 | assemble error: `GRF1 used twice as output` (fvmul dual dst `$ls0v $s1v2`) |
| cand2.vsm | 28 | assemble error: DataRace (LM0 BAR) at first apply fvmul; the dropped fvpassa also served as BAR delay |
| cand3.vsm | 27 | assemble error: DataRace at T (line 3 reads T one step after write) |
| cand4.vsm | 26 | one Newton iteration only: 147/4096 correct (accuracy) |
| cand5.vsm | 28 | early BAR via GRF-stored int 2; odd columns become inf because the LSB lane fix was dropped |
| cand6.vsm | 28 | result-collect chain shifted one line earlier; `Instruction field conflict out_lm1/out_lm1` on line 15 |
| cand7.vsm | 28 | nop after the LSB-fix removed: DataRace LM0 (BAR needs more delay) |
| cand8.vsm | 28 | early BAR + LSB fix, no gap: DataRace GRF1 word 0 at first apply line |

Structure of the 29-line baseline (why 28 is hard):
- 11 prep lines: imm2/shiftT/nop, rsqrt+copy, square, Newton1 x2, BAR shift+Newton2, LSB duplication, GRF1 hazard gap.
- 18 apply lines: 4 fvmul (MAB0 rows 0-7) + 14 l1bmm broadcasts (rows 8-63), with the turnaround collect
  hidden under the fvmul lines.
- LSB lane of the inverse is `inf` because the word-access B load leaves 0 in the second word; the
  `fvpassa $mauf $s1v2` duplication is required and the following gap is required by the GRF1 hazard.
  Moving the BAR write earlier removes the BAR delay but the GRF1 gap remains, so the 11-line prep is unchanged.
- Result broadcasts cannot share a line with fvmul (both write LM1), so the 14-row broadcast chain cannot
  start before the last fvmul line; that forces 4+14 = 18 apply lines.
