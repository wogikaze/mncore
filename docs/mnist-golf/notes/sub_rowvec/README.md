# sub_rowvec golf

- Baseline: `problems/6.subrow-vec/answer.vsm` = 24 lines (score 24, syttrea / current global shortest).
- Best found: **23 lines** — `cand5.vsm`, `cand6.vsm`
  - `python3 problems/run_problem.py 6.subrow-vec --solution scratch/mnist_golf/sub_rowvec/cand5.vsm`
  - `ACCEPTED!! score=23 j=23 m=0 bytes=1199`

## Result

```
lpackbit $mabid $ls0 $t; fvpassa $m[258,258,259,259] $r[8,9,10,11]
imm ui"0x00000002" $nowrite
fvpassa $mt[256,256,257,257] $r[0,1,2,3]; ipassa $aluf $nowrite
fvpassa $mt[288,288,289,289] $r[4,5,6,7]; llsl $t $aluf $t
fvpassa $m[290,290,291,291] $r[12,13,14,15]
fvadd $lmt0v -$lr[0,0,2,2] $ls0v $ln0v
fvadd $lmt128v -$lr[4,4,6,6] $ls8v $ln[128,130,132,134]
fvadd $lm8v -$lr[8,8,10,10] $ln8v
l1bmm@2 $lls0v $llbi; fvadd $lm136v -$lr[12,12,14,14] $ln136v
... (14 more lines: l1bmm@k + l1bmm, flat LM1 destinations)
```

## Techniques

1. `lpackbit $mabid $ls0 $t` gives `T = 2*MAB` in one ALU op (no `imm` needed); `ls0` is zero-initialized.
2. Flat-mode word source `$mt[256,256,257,257]` + flat word destination duplicates a B value
   (`[B0,B0,B1,B1]`) in a single instruction, so the even/odd fill used by the 24-line answer disappears.
3. `ipassa $aluf $nowrite` on the MAU-load line keeps `aluf=2` alive; the next line does
   `llsl $t $aluf $t` to turn `T=2M` into `T=8M` (A rows). This removes the extra `imm 4` line.
4. Each MAB computes 4 rows in two rounds: `{2M,2M+1}` (T=2M for B) and `{2M+32,2M+33}`
   (T=2M, address +32). `T=8M` addresses A rows 2M / 2M+32 with `$lmt0v` / `$lmt128v`.
5. MAB0's own fvadds cover rows 0,1 and 32,33 for free; MABs 2..15 cover the other 56 rows,
   so only rows 2,3 and 34,35 need direct fvadds. They are placed on the T=8M-gap line and on
   the first collect line (the collect does not write LM1, so a MAU calc can share it).
6. The broadcast destination is a flat 2-long-word list `$lln[8M,8M+4,8M+128,8M+132]`, which lets
   each chunk's 4 rows be written to non-contiguous LM1 rows.

## Candidates

| file | lines | result |
|---|---|---|
| cand1 | 23 | assemble error: GRF1 race (collect moved onto the direct-fvadd line) |
| cand2 | 23 | assemble error: T race / aluf timing |
| cand3 | 23 | assemble error: `out_lm1` conflict (broadcast + fvadd same line) |
| cand4 | 23 | emulator error: `aluf` disabled (fixed in cand5 by `ipassa $aluf $nowrite`) |
| cand5 | 23 | **ACCEPTED score=23** |
| cand6 | 23 | **ACCEPTED score=23** (variant: direct rows 34,35 / 2,3 swapped) |
