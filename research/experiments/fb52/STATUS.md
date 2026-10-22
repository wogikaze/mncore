# fb52 STATUS — accepted sub-93 not reached; measured cores + remaining build

Date: 2026-10-21. Baseline re-verified: **93 words, ACCEPTED**
(`fbcheck 93/0`, `fbasm ASM-OK`, `fbverify ACCEPTED!! score=93 j=91 m=2 bytes=3054`).
No accepted candidate < 93 was produced in this push.

## What is built and measured (all ASM-OK, native simulator, bit-exact vs numpy)

| file | content | measured cost | validation |
|---|---|---|---|
| `prim_8lanes.vsm` | 8 byte positions in 8 ALU lanes; one `iadd` writes all 8 chars to 8 words; 6-op pack | positions/X 5 ALU, pack 6 ALU + 1 imm | `ABCDEFGH` for every sampled PE |
| `val_x.vsm` | `X = 8b + p` in 8 lanes | 5 ALU | bit-exact for sampled PEs |
| `val_inv.vsm` | d=4 inversion: `(X\|T)-2^23`, `u=X-4668`, `q=floor(u/79)`, `r=u-79q`, `v=r-4[r>=30]`, `j=floor(v/5)`, `o=v-5j`, `n=1000+15q+j` | **4 ALU + 12 MAU** (+10 imm) | **bit-exact** raw patterns for `X,qf,r,jf,o,n`, all 8 lanes, sampled PEs; `f32(u)*f32(1/79)+floor == u//79` for all u≤28099 |
| `val_digit.vsm` | 4-digit extraction + pack `d3d2d1d0` + select by `o` + `+48` | **18 ALU + 6 MAU** (+8 imm) | **25/25** number-field bytes with `o<=3` bit-exact; o=4 newline not handled yet |
| `model.py` | unified 15-token block model: every segment has `n0 ≡ 10 (mod 15)`; prefix = tail (j=6..14) of virtual block `n0=-5`, `S=-25`, `P=55`, `d=1`; `C_d(j)=(d+1)j+(4-d)A(j)+(8-d)[j>5]` | verified over all 32766 bytes | — |

## Exact blocking stages for this push

The build does not fail on a single wall; it stops on three unbuilt stages plus
integration, in this order:

1. **Newline at o = d** (measured-adjacent, ~3 ops). `ind = frelu(o - (d-0.5), 1.0)`
   (1 MAU + 1 ALU), then `char = fma(ind, 10 - char_num, char_num)` (2 MAU).
   Needs the per-lane `d` (already materialised in the segment path) and the `10.0`
   constant. No new machine mechanism.
2. **Class / letter stage (~18-20 ALU/MAU, not yet built).** The class can be derived
   without the 6-entry special list: for every segment `n0 ≡ 10 (mod 15)`, hence
   `n ≡ j+10 (mod 15)`, so
   * Fizz ⇔ `(j+1) mod 3 == 0`; Buzz ⇔ `j mod 5 == 0`; FizzBuzz ⇔ both.
   `j mod 3`, `j mod 5` are 2 × (`fvmul`+`ffloor`+`fvfma`) + 2 × (`frelu`) ≈ 8 ops.
   The letter is a variable 64-bit shift of the packed constant
   `0x46697a7a42757a7a` ("FizzBuzz") — shift amount `8*(7-o-4*buzz)` (1 MAU) and
   `llsr`+`iand 0xff` (2 ALU); the trailing `\n` is one more relu+select.
   ~10 more ops + 3 constants. **This is the largest unbuilt stage.**
3. **Early-segment inversion d=1/2/3 (~12-16 ALU, not yet built).** `j0 = floor(15 r/P)`
   has error in {-1,0,+1}; the correction needs `C_d(j)` i.e. `A(j)` (6-breakpoint
   step). Cheapest measured-ISA construction: 6 `isub`+masked-add pairs
   (12 ALU, 6 constants) using the OMR flag/mask mechanism, then two corrections.
   No per-lane table lookup, no int multiply, no reciprocal in this ISA.
4. **Integration**: wire the measured 6-op output pack to `$s0v/1100` and reuse the
   proven transfer tail (baseline L85-L93 = 4 nops + l1bmd + 2 l2bmd + nop + 2 MV).
   The tail's PE lines can host renderer ALU/MAU; only the 4 nops + 2 MV are fixed.

## Current honest budget (`model.py:per_byte_ops`)

Measured rows: prologue 16 ALU | positions/X 5 | d=4 inversion 4 ALU + 12 MAU |
digit stage 18 ALU + 6 MAU | output pack 6 ALU.
Estimated rows: class/newline ~10 ALU + 4 MAU | early-segment correction ~16 ALU + 6 MAU.

* renderer **71 ALU + 28 MAU + 33 constants**
* constants as `imm`: 104 ALU ⇒ **110 words** (worse than 93)
* all constants MAU-hosted (optimistic, 33 one-op derivations): `max(71,61)+6`
  ⇒ **77 words**; realistic **~80-85** after scheduler gaps and non-derivable
  constants (1/63, 1/71, 1/79, 0.1 must stay `imm`; 0.01/0.001 are exact products).

So the route is real but lands at **~77-85**, not 62. To reach <=70 the two ALU-heavy
measured stages must be cut: the digit stage (18 ALU: 5 `fftoi`, 6-op pack, shift chain)
and the early-segment correction (12-16 ALU).

## Concrete next-step plan (for the next push)

1. Build stages 1 + 2 on top of `val_digit.vsm`; validate the full character stream for
   all d=4 positions (3512 words = 28098 bytes) against the reference text.
2. Build stage 3 (early segments) and validate the remaining 584 words.
3. Wire the output pack + tail, run `fbcheck` / `fbasm` / `fbverify`; target <= 92.
4. Only then optimize: host the constants (measured win 104 -> 71 ALU) and try the
   2-digit ASCII-pair FMA `0x3030 + x + 246*floor(x/10)` (exact in f32 for x<100)
   to halve the digit stage.

## Repro

```sh
python3 tools/fbasm.py research/experiments/fb52/{prim_8lanes,val_x,val_inv,val_digit}.vsm
python3 tools/fbcheck.py solutions/00_baseline_93.vsm
python3 tools/fbverify.py solutions/00_baseline_93.vsm
python3 research/experiments/fb52/model.py
```
