# dram_ul_256_16 golf log

- Baseline: `problems/18.dram-ul-256-16/answer.vsm` = 6 lines, `ACCEPTED!! score=6 j=4 m=2 bytes=88`
- Goal: score <= 5 (`j + m`)
- `answer.vsm` and `testcase.vsm` were not modified.

## Candidates and results

| Candidate | Idea | Score if assembled | Result |
|---|---|---|---|
| cand1 | single `mvp/n512 $lc0 $d0` | 5 (j4 m1) | 2048/4096 correct; second L2B half is zero |
| cand2 | `mvnop` instead of two `nop`s | 5 (j2 m3) | rejected: DataRaceError (mvnop adds no delay) |
| cand3 | `l2bmd $lbi` with no delay | 5 (j3 m2) | rejected: DataRaceError (loopback not usable by l2bmd) |
| cand4 | write `$llb256`, read `$lbi` | 5 (j3 m2) | assembled, 0/4096 correct (`$lbi` resolves to address 0) |
| cand5 | `l1bmm4@0` + two `l2bmd` + one `mvp/n512` | 6 (j5 m1) | 512/4096 correct (4x4 MAB copies are duplicated) |
| cand6 | `l1bmd` + two `l2bmd` + one `mvp/n512` | 6 (j5 m1) | 256/4096 correct (16 MAB copies are duplicated) |
| cand7 | two `l1bmm@0` + one `nop` + two `l2bmd` + `mvp/n512` | 6 (j5 m1) | 2048/4096 correct (second LM chunk is empty) |
| cand8 | `mvrlbor/n2048` after one `l2bmd` (NaN trick) | 5 (j4 m1) | assembled, 0/4096; OR gives inf/huge finite values and the upper half is zero |
| cand9 | two `l2bmd` + `mvrlbor/n2048` (NaN trick) | 6 (j5 m1) | 0/4096; OR does not make every lane NaN |
| cand10 | current 6-line answer | 6 | ACCEPTED (reference) |

## Why 5 looks impossible

1. The only practical LM -> DRAM path is `l1bmm@`/`l1bmd` (PE -> L1BM) then
   `l2bmd` (L1BM -> L2BM) then `mvp` (L2BM -> DRAM).
2. Hazard rule 3.6.3.7 requires 10 cycles between the PE -> L1BM write and the
   L1BM -> L2BM read of the same address. With the write at step 0, `l2bmd`
   must be at step 3, so at least two delay words are needed after the write.
   Thus `j >= 4` (write + 2 delays + l2bmd). All shorter schedules are rejected
   by assemble3's hazard checker (`l2bm@`, `l2bmr`, `l2bmr2`, `l2bmd` tested).
3. The two L2B halves hold different data and a single `mvp` reads only one
   half (`n512 $lc0` leaves the second half zero). `mvd` + `mvp` is also two
   MVs, so `m >= 2`.
4. Therefore `j + m >= 6`. The baseline 6-line answer is already at the floor.
