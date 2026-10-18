# exp_lowprec 9-line solution (beats the 10-line answer)

## Result
- `cand1.vsm`: **9 lines**, `run_problem.py` → `ACCEPTED!! score=9 j=9 m=0 bytes=446`
- max |Y-exp(x)| over the 4096 test values: **0.00665** (atol = 0.009)
- max |Y-exp(x)| over a 400001-point dense grid on [-2,2]: **0.00861**
  (so the solution is valid on the whole allowed input range, not just the test values)

## Why the previous attempts failed
The 10-line answer and the previous 9-line candidates all used
`Y = E^2` with `E = exp(x/2)`:
- 4 half FMAs for `E` + 4 single-precision instructions for `E = D*y+1` and `E*E`
  = 8 instructions + 2 `imm` lines = 10. There is no slack.
- Dropping the single-precision square (`hvmul` on half-rounded `E`, cand1/2) costs
  ~2*E*eps_half = 0.014 at x=2, so max err stayed at ~0.0107.

The way out is to **not square at all**: a single-precision FMA can produce the final
4096 f32 outputs in 2 instructions if the polynomial is evaluated directly and the last
multiply uses the *exact* x.  That leaves 7 lines for the polynomial and the constants.

## The 9-line program (cand1.vsm)
```
1: hlrelud $msb1 $llm0vr $lt                  # T = h(x)/2          (no imm allowed: reads LM0)
2: imm A3  $llr16/ll1000                      # GRF0 r16 = A3
3: imm A4  $nowrite                           # aluf = A4
4: imm A2  $nowrite; hvfma $alufr $llt $llr16 # S1 = h(A4)*t + A3
5: imm A1  $nowrite; hvfma $maufr $llt $aluf  # S2 = h(S1)*t + A2
6: imm A0  $nowrite; hvfma $maufr $llt $aluf  # S3 = h(S2)*t + A1
7: imm c0 $llr24/ll1000; hvfma $maufr $llt $aluf $lls0v   # S4 = h(S3)*t + A0  (+GRF1 copy)
8: fvfma $mauf  $lm0v4 $aluf  $ln0v4          # Y(even words) = S4*x + c0
9: fvfma $ls2v4 $lm2v4 $llr24 $ln2v4          # Y(odd  words) = S4*x + c0
```
`Y = c0 + x*(A0 + A1 t + A2 t^2 + A3 t^3 + A4 t^4)`, `t = h(x)/2`, i.e. a degree-5
polynomial in x whose last product uses the exact single-precision x.

## Machine facts used (all verified with the official assembler/emulator)
- A half-precision MAU op covers all 16 words/PE = all 4096 elements in **one** instruction;
  a single-precision MAU op covers 8 words/PE, so the final f32 pass costs **2** lines
  (`$lm0v4`/`$ln0v4` = even long words, `$lm2v4`/`$ln2v4` = odd long words).
- One `imm` per line; `imm` and an LM0 access in the same instruction are a
  *field conflict* (`immediate` vs `lm0`), and two ALU expressions on one line
  (`imm` + `hlrelud`) are a field conflict too.
- Only **one GRF0** read per MAU instruction. GRF0+GRF1 are fine together.
- `imm`'s value is also visible as `$aluf` on the next step, so constants can be
  pipelined through `aluf` (1-step) while GRF0 supplies the other (2-step) constant.
- GRF0 and T need 2 steps between write and read. `$mauf` may only be read when the
  immediately preceding step issued a MAU op ("MAU is disabled" otherwise).
- The MAU result is single precision even for `hvfma`; it is read back exactly via
  `$mauf`, so the last Horner value is not half-rounded.
- Writing the last half result to `$lls0v` (GRF1, 2長語) makes the odd 8 words
  reachable as `$ls2v4`.

## Coefficients
Obtained by LP minimax over the exact polynomial terms, then a rounding-aware
pattern search (see `opt3.py`). Values as rounded to f32 by the assembler:
A4 = 0.1759231686592102 (half-rounded to 0.176025390625), A3 = 0.4078565239906311,
A2 = 0.6306540369987488, A1 = 0.9707269668579102, A0 = 1.0076225996017456,
c0 = 1.0020467042922974.

## Files
- `cand1.vsm` — the accepted 9-line solution.
- `evalvsm.py` — fast local evaluator (assembles + runs the official emulator,
  reports words/maxerr/bad; reproduces cand2's 15 mismatches exactly).
- `opt3.py` — model + optimizer for this structure (LP + rounding-aware search).
- `gen.py` — emits `cand1.vsm` from a coefficient vector.
- `t/` — assembler/emulator semantics probes.

## Verification (2026-10-19)
```
$ python3 problems/run_problem.py 13.exp-low-prec --solution scratch/mnist_golf2/exp_lowprec/cand1.vsm
ACCEPTED!! score=9 j=9 m=0 bytes=446
```
- evalvsm.py: `words=9 maxerr=0.00665379 bad=0`
- independent numpy model vs official emulator on all 4096 outputs: max diff 4.8e-7
  (only the f32 rounding of the intermediate MAU results).
- `problems/13.exp-low-prec/answer.vsm` and `testcase.vsm` were not modified
  (`git status` shows only `?? scratch/mnist_golf2/`).

## Note on limits
8 lines does not seem reachable with this instruction set: the final f32 pass needs
2 lines, so 4 half steps + 2 lines leaves only 2 imm lines. A 5-step (degree-6) chain
needs 3 startup lines (T load cannot share a line with `imm`), i.e. 10 lines, and the
E^2 form additionally needs 4 single-precision lines (10 lines total).
