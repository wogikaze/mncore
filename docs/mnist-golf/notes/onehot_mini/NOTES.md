# onehot_mini 6-line attempt (failed)

Baseline: problems/15.onehot-mini/answer.vsm = 7 words (ACCEPTED, score=7).

## Attempts and blockers

1. cand1.vsm (6 words)
   imm ui"0xBF800008" $r1v                     # [0,-v] word0/word1, [v,v] at word2/3
   ipackbit $subpeid $lr0 $nowrite; hvpassa $aluf $omr1; gather A
   iadd/$imr1 $aluf $lr[8,2,8,2] $t; gather B; distribute s0
   ixor $aluf $ls[0,0,2,2] $omr1; distribute s4
   ixor $t $ls[4,4,6,6] $omr2; hvpassar -$lr2 $ln0v/$imr1
   hvpassar -$lr2 $ln8v/$imr2
   -> assembles up to the hazard check, then:
      "racy memory read at GRF0 address 0 ... line 2"
      (imm word-write at word1, packbit reads long word 0 the next step; a
       1-step gap is required, which re-adds the linc instruction.)

2. One instruction cannot write two LM1 destinations:
   "LM1 used twice as output" for `hvpassar ... $ln0v/$imr1 $ln8v/$imr2`.
   The two row-groups therefore need two separate writes.

3. A single 2-long-word write needs 4 independent mask bits/cycle. An ixor
   produces only 2 independent bits (lane0->bits3,2, lane1->bits1,0), so the
   per-row one-hot word can't be encoded; sxor (16-bit lanes) gives 4 bits but
   needs T replicated in all four halfwords, which needs a 16-bit shift or
   equivalent not available within the budget.

4. Issue-group conflicts: the imm cannot share a step with an LM0 read
   ("immediate" vs "lm0"), so the first gather can't share the imm step.

## Result
No 6-word ACCEPTED solution found. answer.vsm untouched; testcase.vsm untouched.
