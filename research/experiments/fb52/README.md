# fb52 — independent attack on the FizzBuzz rendering bottleneck

Agent: fb52 (independent track). Baseline: `solutions/00_baseline_93.vsm` = **93 words,
re-verified this session** (`fbcheck` / `fbasm` / `fbverify`).

## Verdict

* **No accepted candidate ≤ 52 was found.** Best verified solution is still the 93-word
  baseline: `ACCEPTED!! score=93 j=91 m=2 bytes=3054`.
* The per-byte renderer route (**b**) is mechanistically viable: I measured a working
  8-lane primitive that writes 8 output bytes with **one ALU expression** and packs them
  with the known 6-op pack. But its full word budget lands at **~62 words with every
  constant hosted in the MAU pipe** (and ~85 with imm constants), not 52. The binding
  costs are the per-lane field-index inversion and the 4-digit extraction, not packing.
* Route (**a**) (MAU/FMA byte generation) cannot beat the same inversion barrier: an
  f32 lane holds at most a 23-bit exact integer payload (2–3 ASCII bytes), and assembling
  8 bytes still needs the measured 6-op shift/or pack.
* Route (**c**) (repeated text) cannot help: 1594/4096 output words are duplicates and
  798 d=4 words equal the word one 79-byte block earlier, but the delivery path
  (`l1bmd → l2bmd → mvd → mvp`) is a fixed gather/permutation with no broadcast or
  DRAM-internal copy, and all 4096 PEs execute the same renderer.

## New results measured in this track

### 1. A verified 8-lane byte renderer primitive (`prim_8lanes.vsm`, 24 words)

The ALU has **4 cycles × 2 int32 lanes = 8 independent results per expression**, and a
long-word destination writes **8 consecutive words** (4 cycles × 2 lanes). I built the
position vector `[0,1],[2,3],[4,5],[6,7]` and computed `char = 'A'+p` in all 8 lanes,
writing all 8 characters with **one** `iadd` (`$ls[48,50,52,54]`). The 6-op pack
(3 × `ilsl` + 3 × `ior`, word reads at `T+0..T+7` equivalents) then produced
`ABCDEFGH` exactly, for every PE sampled:

```
ASM-OK words=24 research/experiments/fb52/prim_8lanes.vsm
GREG0 n1c1b0m0p0   0 4142434445464748 b'ABCDEFGH'
GREG0 n1c1b7m15p3  0 4142434445464748 b'ABCDEFGH'
```

Cost of the output stage (measured): **3 ALU** for the position table, **1 ALU** to
duplicate `B=8b` into both lanes, **1 ALU** for `X=B+p`, **0 ALU** for the 8-word canvas
write (it is the destination of the last character op) and **6 ALU + 1 imm** for the
pack. The caveat: this stage only replaces the baseline's *placement* work (its 8
ALU `ipassa`/`ladd` canvas writes and the 6-ALU pack). The baseline's 14 MAU canvas
writes are the letter overrides, and its character values come from the per-token float
pipeline; a per-byte design must compute 8 characters per instruction instead.
`val_x.vsm` verifies `X = 8b + p` bit-exactly against the Python model for sampled PEs
(`ASM-OK words=27`, dump matches).

### 2. The whole stream is one uniform 15-token block structure (`model.py`)

Verified over all 32766 bytes: every segment is a sequence of 15-token blocks that start
at `n0 == 10 (mod 15)`, including the 9-token prefix, which is the **tail (j=6..14) of the
virtual block `n0 = -5`**:

| segment | n0 | stream start S | period P | d |
|---|---|---|---|---|
| prefix | -5 | **-25** | **55** | 1 |
| d=2 | 10+15q | 30 | 63 | 2 |
| d=3 | 100+15q | 408 | 71 | 3 |
| d=4 | 1000+15q | 4668 | 79 | 4 |

`C_d(j) = (d+1)j + (4-d)A(j) + (8-d)[j>5]`, `A(j)=#{0,2,8,10,11,14}<j`. Because
`n0 ≡ 10 (mod 15)` in every segment, the token class (Buzz at j=0,10; Fizz at
j=2,8,11,14; FizzBuzz at j=5; number otherwise) is a function of `j` alone and is
*identical in all four segments*. P = 8d+47 and n0/P/S are affine in the segment
indicator. This removes the need for separate prefix/segment logic in a redesign.

`python3 research/experiments/fb52/model.py` →
`unified 15-token block model: VERIFIED over 32766 bytes`.

### 3. Float32 division by 79 and the d=4 inversion are exact on the whole domain

`f32(u) * f32(1/79)` then floor reproduces `u//79` for all `u = 0..28099` (0 mismatches),
and `j = floor((r-4[r>=30])*0.2)` is exact for all 79 phases. So the numerical core of a
per-byte renderer is sound; the cost is op count, not precision.

## MEASURED stages (native sim + assemble3, bit-exact against numpy)

Two core stages were built and measured on hardware this session:

### `val_inv.vsm` — d=4 position/inversion chain (ASM-OK, 67 words with a naive schedule)
Prologue (baseline L1-16, 16 ALU) → position table + B duplication + X (5 ALU) →
`f32` conversion, `u = X-4668`, `q = floor(u/79)`, `r = u-79q`, `v = r-4[r>=30]`,
`j = floor(v/5)`, `o = v-5j`, `n = 1000+15q+j`.
**Ops: 4 ALU + 12 MAU** (excluding the 10 imm constants and the prologue).
All 8 lanes for every sampled PE are **bit-exact** against numpy float32
(`X`, `qf`, `r`, `jf`, `o`, `n` compared as raw bit patterns).

### `val_digit.vsm` — 4-digit extraction + pack + select (ASM-OK, 107 words naive)
Given `n` and `o`: three `fvmul`+`ffloor` levels, cross-subtraction with `fvfma`,
4 `fftoi`, a 6-op `ilsl`/`ior` pack into `d3d2d1d0`, `8*(3-o)` via `isub`+`ilsl`,
`ilsr`+`iand`, `iadd 48`.
**Ops: 18 ALU + 6 MAU** (excluding 8 imm constants).
Validated against the reference text: **25/25 number-field bytes with o<=3 match**;
the only remaining mismatches are the o=4 newline slots, which belong to the
not-yet-built class/assembly stage.

The full `val_digit.vsm` is 62 ALU + 18 MAU + 28 nop-words (107 words) because of a
deliberately naive schedule; the op counts above are the ones that matter.

## Revised word budget (`model.py:per_byte_ops`, measured rows marked)

The 62-word projection did **not** survive measurement. Measured ALU counts are
higher than the first estimate: the digit stage costs 18 ALU (5 `fftoi`, a 6-op pack
and the shift chain), and the early-segment `A(j)` correction plus the class/letter
stage are still unbuilt. The current budget is:

* renderer **71 ALU + 28 MAU + 33 constants**
* constants as imm: 104 ALU -> **110 words** (worse than the 93 baseline)
* every constant hosted in the MAU: `max(71, 61) + 6` = **77 words** projected
  (and 61 MAU ops assumes all 33 constants are one-op derivable, which is optimistic)
* remaining unbuilt pieces: newline handling (o=4), Fizz/Buzz/FizzBuzz class and
  letter extraction, the d=1/2/3 inversion correction, and the output pack is measured
  (6 ALU) but not yet wired to the transfer tail.

## Original model budget (superseded by the measured table above)

| stage | ALU | MAU | const |
|---|---|---|---|
| coords `B = 8b` (measured 9-op floor + prologue) | 12 | 0 | 4 |
| 8 byte positions `p = 2c+h` | 3 | 0 | 1 |
| duplicate B + `X = B+p` | 2 | 0 | 0 |
| `X → f32`, `u = X-S` | 1 | 1 | 1 |
| `q = floor(u/P)` | 2 | 1 | 1 |
| `r = u - P q` | 0 | 1 | 1 |
| `v = r - 4[r>=30]` | 1 | 2 | 2 |
| `j = floor(v/5)`, `o` | 2 | 2 | 1 |
| `n = n0 + 15q + j` | 0 | 2 | 2 |
| 4 decimal digits (3 floors + cross-subtract) | 4 | 7 | 4 |
| digit select by o (variable shift + and) | 2 | 1 | 1 |
| class / letter selection | 6 | 4 | 3 |
| character assembly (int) + 8-word write | 3 | 0 | 1 |
| pack 8 words → long word (measured) | 6 | 0 | 1 |
| **total renderer** | **44** | **21** | **23** |
| + mandatory tail (4 nops + 2 MV; transfer lines can host ALU) | | | |

* constants as `imm` (ALU lines): `12+44+23 = 79` ALU → **85 words**
* every constant generated by a hosted MAU op: `max(56 ALU, 44 MAU) + 6` = **62 words**
* target 52 needs **≤ 46 words before the 6 non-hostable tail lines**, i.e. ALU ≤ 46
  with all constants hosted. This design is **10 ALU over**; and the count above is the
  *d=4-only* inversion. Handling d=1/2/3 per lane needs the `extra_d(j)` correction
  (a 16-entry table lookup plus per-lane d selection, ≈ +8 ALU/MAU), which pushes the
  floor further up.

The two irreducible costs are:

1. **Field-index inversion** (`r → j,o`): for d=4 a single correction suffices, but for
   d=1/2/3 the field boundaries differ from `(d+1)j` by up to 25 bytes and the correction
   needs `A(j)` (a 6-breakpoint step function). Estimate-and-correct is exact
   (`j0 = floor(15r/P)`, delta ∈ {-1,0,+1}) but costs ~15 ops for two corrections, and
   the per-lane table lookup is not available in this ISA (T-indirection is per cycle,
   not per lane; the ALU has no int multiply, no reciprocal, no table ops).
2. **4-digit extraction** (~18 ops): the ALU has no integer multiply and the MAU has no
   integer/reciprocal op, so `floor(n/10^k)` must be built from fixed f32 multipliers and
   cross-subtraction for all four digits, then packed with shifts.

## Files

```
model.py               unified block model (verified) + per-byte word budget
prim_8lanes.vsm        measured 8-lane -> 8-word write + 6-op pack primitive (ASM-OK, 24 words)
val_x.vsm              measured X = 8b + p, 8 lanes, checked against Python (ASM-OK, 27 words)
q.py, probe.py         native-simulator probe helpers
```

Repro:

```sh
python3 research/experiments/fb52/model.py
python3 tools/fbasm.py research/experiments/fb52/prim_8lanes.vsm research/experiments/fb52/val_x.vsm
python3 tools/fbcheck.py solutions/00_baseline_93.vsm
python3 tools/fbverify.py solutions/00_baseline_93.vsm
```
