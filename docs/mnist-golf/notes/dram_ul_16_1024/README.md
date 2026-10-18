# dram_ul_16_1024 golf attempt

Target: beat the 13-line top (`j+m`), i.e. reach <=12.

## Result

No candidate reached <=12. Best accepted is 13.

| cand | score | result | idea |
|---|---|---|---|
| cand1 | - | assemble error (T race) | drop the T-hazard nop |
| cand2 | - | assemble error (L1BM race) | only one L1BM-gap nop |
| cand3 | - | assemble error (L2BM->MV race) | drop the last nop |
| cand4 | 13 | ACCEPTED j=11 m=2 | BAR+T = 2*l2bid each (`lpackbit ... $lmb $t`), 2 nops |
| cand5 | 11 | wrong data | T computed in the same step as l1bmd (read sees old T) |
| cand6 | - | assemble error (LM0 race) | BAR+T with one nop |
| cand7 | 12 | wrong data | T=2*l2bid (one shift short) |
| cand8 | - | assemble error | `l2bmd $llb` (2-longword L1BM read is illegal) |
| cand9 | 13 | ACCEPTED j=11 m=2 | two-step ALU chain: `lpackbit` -> `lpackbit $aluf` |
| cand10 | 12 | wrong data | single `mvp/n2048` from L2B0 (second half is not in L2B0) |

## Why 13 looks optimal

- 4x `l2bmd` are mandatory: each moves 64 lw/cycle x 4 = 256 lw per L2B,
  and every L2B needs 1024 lw.
- 2x `mvp` are mandatory: an MV L2BM source selects one L2B (`@.0`/`@.1`);
  the no-L2B form defaults to L2B0 (probed with markers).
- 1x `l1bmd` concat is mandatory; PE->L1BM -> L1BM->L2BM needs 10 cycles =
  2 nops (1 nop gives only 8 cycles; address-specific race, probed).
- L1BM->L2BM -> MV needs 1 step (assembly-checked).
- Address setup needs 2 ALU steps + 1 nop:
  the fixed operand `$l2bid` (and `imm` payload) cannot co-issue with an
  LM0 access, `$l2bid` is rejected as the 2nd ALU input, and no 1-instruction
  4x exists. BAR+T can encode 4*l2bid in one ALU step but BAR->LM0 needs 2 nops.
- So j=3+1+2+4+1=11 and m=2 -> 13.

Probes used to establish this are in `probe/` (they use `d set`, which is fine
for probes but never in the candidates).
