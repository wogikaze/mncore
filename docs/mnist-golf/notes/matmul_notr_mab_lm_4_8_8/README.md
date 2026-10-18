# matmul_notr_mab_lm_4_8_8 golf log

Current best (answer.vsm): 7 lines, `ACCEPTED!! score=7 j=7 m=0 bytes=207`.
Goal was <= 6 lines. **No 6-line program was found**; all 10 candidates in this
directory fail (wrong values, invalid block float, or assembler rejection).

## Structure of the 7-line answer

```
gmwrite $lm8v $lx0        # B rows 0-3 -> matrix x rows 0-3 (plain floats)
gmwrite $lm16v $lx4       # B rows 4-7 -> matrix x rows 4-7
gmread $lx0 $nowrite      # transposed read cols 0-3 -> mreadf
gbfn $mreadf; gmread $lx4 # BF(transposed cols 0-3) -> aluf ; read cols 4-7
gbfn $mreadf; gmwrite $aluf $lx0   # BF cols 4-7 -> aluf ; write cols 0-3
gbfn $lm0v;  gmwrite $aluf $lx4    # BF(A) -> aluf ; write cols 4-7
gmmul $lx $aluf $ln0v     # C = BF(B^T) . BF(A row)
```

## Limits verified against the official assembler/emulator

* One `mwrite` per step (same issue group; even `$lx0`+`$ly0` is rejected:
  "Instruction field conflict ... mau_port_b"). One `mread` per step.
* A G/`fmwrite` writes only 4 logical rows (one per cycle) -> loading B (8 rows)
  needs 2 steps; writing back the 8 BF rows needs 2 steps.
* A G `gmread` reads 4 columns -> transposing 8 columns needs 2 steps.
* `gmmul u`/`gmmuld` are rejected ("couldn't set `u`/`d` options"); u/d is only
  for double precision (`dmfma` requires it).
* `gmwrite $llm8v ...` *does* assemble (2-long-word source), but only the first
  long word of each cycle lands on G-visible (even) physical rows, so it still
  gives just 4 G rows per instruction. `hmwrite $llm8v` likewise reaches only
  physical rows 0..7 = G rows 0..3.
* `gmwrite`+`gmread` on different faces and `gmwrite`+`gmmul` on different faces
  are legal, but a calc cannot read the face that is written in the same step.
* `imm` is one per step, cannot share a step with any LM0 access, and its address
  must be 4-word aligned (no overlapping-constant trick), so a constants-based
  ALU formulation needs >= 4 imm steps alone.

## Minimum-length argument

Matrix path dependency chain (all steps forced):
load rows 0-3 (1) -> load rows 4-7 (2) -> read cols 0-3 (3) -> read cols 4-7 (4)
-> bfn 0-3 (4) -> bfn 4-7 (5) -> write BF 0-3 (5) -> write BF 4-7 (6) -> gmmul (7).

The last BF write must precede the calc (same matrix operand can appear only once
per step), and the two transpose reads cannot share a step (same issue group), so
the calc cannot be issued earlier than step 7. 6 lines would need a matrix write
of 8 rows in one instruction, or two transpose reads in one instruction, both
rejected by the assembler.

Alternative (non-matmul) formulations were also analysed: the exact closed form is
C[i][j] = 8192*i + 64*i*j + 28*j + 3920 (i = cycle, j = word), e.g.
C = (8i+3.5)(8j+1024)+336 or C = B5*(64i+28)-768i with B5 = 140+j, but every
variant needs several numeric constants (8, 1024, 28, 3920), and the `imm`
constraints above make that >= 4 extra steps.

## Candidates (all 6 lines, all rejected)

| file | idea | result |
|---|---|---|
| cand1 | calc on the other face while writing the last BF rows | invalid block float |
| cand2 | `gmwrite $llm8v` single load | 824 vs 3920 (only B rows 0,2,4,6 reach k=0..3) |
| cand3 | `hmwrite $llm8v` single load | 132 vs 3920 |
| cand4 | skip second BF write (plain B stays in rows 4-7) | 137856 vs 3920 |
| cand5 | BF(A) to GRF on line 3 | all-zero output |
| cand6 | chain partial with `gmfma` | rows 0-3 ok-ish, PEs 2-3 wrong |
| cand7 | write both BF halves to face y | all-zero output |
| cand8 | load B into y, BF into x, calc on y | assembler: invalid output location |
| cand9 | ll-load B into y and x | all-zero output |
| cand10 | reversed read order, calc on y | all-zero output |

`answer.vsm`, `main.vsm`, `testcase.vsm` were not modified.
