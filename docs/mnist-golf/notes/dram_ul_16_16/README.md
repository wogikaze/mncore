# dram_ul_16_16 golf (from 9 lines to 8)

## Result

6 verified candidates, all `ACCEPTED!! score=8 (j=7, m=1)`.
Best: `cand1.vsm` (113 bytes).

| file | score | bytes | note |
|---|---|---|---|
| cand1.vsm | 8 | 113 | T=8*l2bid, standard addresses, tagless mvp |
| cand2.vsm | 8 | 121 | flat-mode LM operand `$llmt[0,4,8,12]` |
| cand3.vsm | 8 | 113 | `l1bmm@5` / `l2bm@2` |
| cand4.vsm | 8 | 113 | `l2bm@7` |
| cand5.vsm | 8 | 115 | shifted bank offsets `$llb64/$lc96/$lc128` |
| cand6.vsm | 8 | 114 | `l1bmm@15` / `l2bm@7` |

Verify with:

```bash
python3 problems/run_problem.py 29.dram-ul-16-16 \
  --solution scratch/mnist_golf/dram_ul_16_16/cand1.vsm
```

## Structure (cand1)

```
imm ui"3" $nowrite            # shift amount = 3
llsl $l2bid $aluf $t          # T = 8*l2bid words => group g reads rows 4g..4g+3
nop                           # T write -> LM read needs 1 step
l1bmm@0 $llmt0v $llb32        # LM -> L1BM[32..63] (8 words/cycle x 4)
nop                           # PE->L1BM -> L1BM->L2BM needs 2 steps / 10 cycles
nop
l2bm@0 $lb0 $lc32             # L1BM[32..63] -> L2BM[64..95]
mvp/n64 $lc64@.0 $d0          # L2BM[64..95] -> each group's DRAM d0..d31
```

Because the input is broadcast across MAB/L1B/L2B, the only group-dependent
quantity is `$l2bid` (= 2*group + l2b).  Reading `8*l2bid` words per group makes
group g read rows 4g..4g+3, so one parallel `mvp` can fill all four DRAM groups.

## Why 7 lines (6 PE steps + 1 MV) does not work

The score is `j + m` = PE steps + MV instructions.  The chain needs:
T computation (2) + T hazard gap (1) + l1bmm (1) + L1BM hazard gap (2) + l2bm (1)
= 7 PE steps, plus the mandatory MV = 8.

Attempts that failed (kept in `attempts/`):

- Drop either L1BM gap nop: `DataRaceError` at L1BM (10-cycle rule).
- `llsl ... $t;l1bmm ...` in one step: assembles, but l1bmm reads the old T,
  so every group reads rows 0..3 (wrong for groups 1-3).
- `l1bmm;l2bm` in one step: l2bm reads stale L1BM (all zeros).
- `l2bm;mvp` in one step: parse error ("Non PE operation after separator").
- BAR (`$lmb`) instead of T: BAR->LM read race needs 1 step (same cost), and
  with only 1 nop it still reports a race, so it is not shorter.
- One-instruction shift: fixed operands (`$l1bid`, etc.) are rejected as the
  second ALU input; there is no immediate shift form; testcase LM words all
  have low 13 bits zero, so none can supply shift 3.
- `l1bmm` to L1BM[0..31] with `l2bm` source 0: race at L1BM address 16;
  writing at offset 32 makes the read happen in cycles 2-3 and is race-free.
