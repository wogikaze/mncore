# dram_ul_256 golf log

- Problem: `problems/31.dram-ul-256` (slug `dram_ul_256`)
- Current best: `answer.vsm` = 7 words (`ACCEPTED!! score=7 j=6 m=1 bytes=86`)
- Target: `j + m <= 6`
- `answer.vsm` / `testcase.vsm` were not modified.

## Result

No 6-word candidate passed. The 10 candidates below were run with
`python3 problems/run_problem.py 31.dram-ul-256 --solution <cand>`.
Only `cand10` (the current answer) is accepted, with score 7.

| Candidate | Idea | Score if assembled | Result |
|---|---|---|---|
| cand1 | drop the T-setup delay word | 6 (j5 m1) | rejected: T data race |
| cand2 | drop one L1BM→L2BM delay word | 6 (j5 m1) | rejected: L1BM data race |
| cand3 | BAR instead of T; flat `$lm[4,4,4,0]` puts the gather in cycle 3; l2bm reads only the late-safe chunks | 6 (j5 m1) | rejected: LM0 port conflict |
| cand4 | BAR instead of T, keep 1 delay word for the LM0 port | 7 (j6 m1) | rejected: LM0 port conflict (needs 2 steps) |
| cand5 | same-step T write and T-indirect gather | 5 (j4 m1) | assembles, but the gather reads the old T (data mismatch) |
| cand6 | same-step T write + cycle-3 gather | 6 (j5 m1) | assembles, old T (data mismatch) |
| cand7 | no per-PE address setup at all | 5 (j4 m1) | assembles, all PEs read word 0 (data mismatch) |
| cand8 | T setup and gather in consecutive steps with a `wait` on a long dummy MV | 7 (j5 m2) | rejected: T data race (the static check ignores the wait) |
| cand9 | flat `$lm[4,4,4,0]` without T (no setup) | 6 (j5 m1) | assembles, but no per-PE address (data mismatch) |
| cand10 | current answer (baseline) | 7 (j6 m1) | ACCEPTED score=7 |

`verify.log` contains the run_problem output for all ten.

## Why 6 is blocked by the static hazard checker

1. Score is `j + m` (one word per PE step, plus one word per MV).
2. The only LM→DRAM path is `l1bmd`/`l1bmm` (PE→L1BM) → `l2bm` (L1BM→L2BM) → `mvp` (L2BM→DRAM).
3. The testcase broadcasts every value to all 64 PEs (`B@[PE,MAB,L1B]`), and the gather writes PE *i* to L1BM word *i*. Therefore every PE must read a different LM word, i.e. a per-PE address is mandatory.
   - `l1bmd` has no per-PE address other than T-indirect or BAR (the `j` modifier only adds one long word for `pe%4 <= madpe`).
   - `$peid` is the linear index `mab*4 + pe` (verified with the emulator), so `ipackbit $peid $lr0 $t` gives exactly the needed `2*peid` word address.
4. T write → T read needs 7 cycles. With the setup at step 0 the first safe `l1bmd` is step 2, i.e. one mandatory delay word.
5. PE→L1BM → L1BM→L2BM needs 11 cycles for the same address. With `l1bmd` at step 2 the first safe `l2bm` is step 5, i.e. two mandatory delay words (a 2-step gap can only surface the 16 words read in cycle 3; the other 16 would be read after 10 cycles and the assembler rejects it).
6. L1BM→L2BM → L2BM-reading MV needs one step, so the MV is one more word.
7. Hence the floor of this schedule is `setup + delay + l1bmd + 2*delay + l2bm + mvp = 7`.

Every attempt to remove one of those words runs into one of:
- the T 7-cycle rule (cand1/cand8/cand9/cand18),
- the LM0 port 2-step rule for a BAR write (cand3/cand4/cand19), or
- the 11-cycle L1BM rule (cand2),
or, when the assembler accepts, the per-PE address is not actually applied (cand5–cand7, cand9), so the values are wrong.

The `wait` instruction can delay execution dynamically but the assembler's static hazard check ignores it, so it cannot replace a delay word (tested: cand14–cand16 in this directory).
