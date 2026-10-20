# Offset→(n, char) inversion: exact solution, error analysis, and line cost

Directory: `research/experiments/offset-inversion/`
Files: `ref.py` (exact reference), `analyze.py` (error analysis), `model.py`
(full byte-generation model), `analysis.out` (analysis log), `REPORT.md`.

## Verdict (short)

1. **The inversion has an exact closed form and it needs zero correction
   steps.** In each digit region the byte offset is a divmod by a constant
   period (`P_d = 8d+47` = 55/63/71/79), followed by a fixed 15-entry slot
   table. Verified over all 32,766 bytes: **0 corrections needed**.
2. **But it is not cheaper than what the 93-word solution already does.**
   The exact divmod inversion costs ≈12–15 lines, while the existing
   approximate estimate + 11-ALU chain costs ≈13. The four candidates are
   *not* a consequence of the approximate inversion: a block of 8 bytes
   intersects up to **4 consecutive numbers** (measured below, 3 blocks do),
   so the four candidate lanes are needed no matter how the inversion is done.
   The digit stage therefore does **not** collapse.
3. **The 41-line gap is not in the inversion.** 93 lines decompose as ALU 66
   = coordinates 12 + constants 24 + est/digits 16 + canvas 8 + pack 6, plus
   27 non-ALU lines. Removing the whole est/digits block (16) and every
   inversion-related constant still leaves ≈77 lines. The two blocks that can
   plausibly yield ~40 lines are **constants (24)** and **coordinates (12)**,
   not the inversion.

Everything below is reproducible: `python3 ref.py`, `python3 analyze.py`,
`python3 model.py`.

## 1. Exact reference (`ref.py`)

Built from the problem statement only, then compared with the official
testcase's own `d getd` expectations (4096 words, 32,766 bytes):

```
length=32766  mismatches=0
L(10)=30  L(100)=408  L(1000)=4668  L(6334)=32762
ok_L=True ok_owner=True ok_inv=True
```

`L(n)` is strictly increasing and `owner[L(n)+k] == (n,k)` for every n and k;
`L(n)+k == B` for every byte. First bytes `1\n2\nFizz`, last bytes `z\n6334`
match the statement.

## 2. The exact inversion

### 2.1 Structure

For d ≥ 2, `N_d = 10^(d-1) ≡ 10 (mod 15)`, so the numbers split into groups of
15 starting at `N_d`, and every group consumes exactly `P_d = 8d + 47` bytes.
Inside a group the piece order is *identical in all regions*:

```
j        :  0  1  2  3  4  5  6  7  8  9 10 11 12 13 14
class    :  B  p  F  p  p FB  p  p  F  p  B  F  p  p  F
len d=4  :  5  5  5  5  5  9  5  5  5  5  5  5  5  5  5   (79)
len d=3  :  5  4  5  4  4  9  4  4  5  4  5  5  4  4  5   (71)
len d=2  :  5  3  5  3  3  9  3  3  5  3  5  5  3  3  5   (63)
cum d=4  :  0  5 10 15 20 25 34 39 44 49 54 59 64 69 74
cum d=3  :  0  5  9 14 18 22 31 35 39 44 48 53 58 62 66
cum d=2  :  0  5  8 13 16 19 28 31 34 39 42 47 52 55 58
```

(Verified: `L(N_d + 15q + j) = B0_d + q*P_d + cum_d[j]` for every q,j of every
region, `B0_d = 0/30/408/4668`.)

### 2.2 The inverse

```
R = B - B0_d;  q = R // P_d;  r = R - q*P_d
j = jtab_d[r];  c = ctab_d[r];  n = N_d + 15q + j
```

* d = 4: because only the j=5 slot is 9 bytes, the whole decode is arithmetic
  (natural tiling):
  `e1=[r>=30]; e2=[r>=34]; j=(r-4*e1)//5; c=r-5j-4*e2`.
* d = 4, **shifted tiling** (groups `[1006+15k, 1020+15k]`, FizzBuzz last):
  for every byte B ≥ 4702 (28,064 of 28,098 bytes of the region) the decode is
  simply `j = min(r//5, 14); c = r - 5j` — verified 0 errors. The 34-byte
  prefix `4668..4701` (`"Buzz\n1001\nFizz\n1003\n1004\nFizzBuzz\n"`) is the only
  irregular part.
* d = 2,3: `cum_d` is not arithmetic; a 15-entry table (or an equivalent
  comparison chain) is required.
* d = 1: 30 bytes, direct map (9 numbers, no period).

### 2.3 Float32 realisation of the divmod (one fma, one floor, one ftoi)

`q = ftoi(ffloor(fma(R, float32(1/P_d), bias)))`, `r = R - P_d*q`.
Verified for every byte of every region:

| d | P | R range | float32(1/P) rel. err | min |frac| (R/P) | biases in [0.0005,0.01] that work | r exact |
|---|---|---|---|---|---|---|
| 2 | 63 | 0..377 | 2.9e-8 | 2.4e-7 | all | yes |
| 3 | 71 | 0..4259 | 2.6e-8 | 1.4e-2 | all | yes |
| 4 | 79 | 0..28097 | 2.3e-8 | 1.3e-2 | all | yes |

The bias is folded into the FMA addend (free). `r` reconstructs `R mod P_d`
exactly for all inputs.

### 2.4 Operation count

| step | ops | unit |
|---|---|---|
| int B → float (2^23 trick) | `ior 0x4b000000`, `fvadd -(2^23)` | 1 ALU + 1 MAU |
| region select (3 thresholds) | `isub` with 3 lanes (mask flags) + 2 masked selects | 3 ALU |
| divmod | `fvfma`, `ffloor`, `fftoi`, `fvfma` | 2 ALU + 2 MAU |
| slot decode d=4 | 2 compares, `*0.2`, `ffloor`, `min`, `fma` | 4 ALU + 2 MAU |
| slot decode d=2/3 | T-set + T-indirect LM0 read + table-base select | 3 ALU |
| n = N+15q+j | 2 × `fvfma` | 2 MAU |

Because ALU and MAU are separate issue groups that can share a line, the
inversion is **≈12–15 lines** (d=4 path 6–7, plus region select 3–4, plus the
d<4 path 3–4).

The 93-word solution's `{0,32,408,4672}` compares + 11-ALU chain is ≈13 lines,
and the chain is **not** a redundant estimate: its constants `{8,13,23,33,33}`
match the `cum` offsets of the irregular regions (`cum_2 = 0,5,8,13,...`), so it
encodes the piece-length/position structure that the d=2/3 slot tables need.
A closed form cannot remove it for those regions. Adding the position step
(4 lines, model stage F) the exact version costs ≈16–17 against ≈14–16 for the
existing path: **line-neutral within ±2**. It cannot save the digit stage.

## 3. Error analysis of affine / quadratic estimates

### 3.1 Global fits (all 32,766 bytes)

| estimate | coefficients | residual min | max | span |
|---|---|---|---|---|
| `n ≈ a*B+b` (least squares) | a=0.191064734911, b=86.465787 | −85.66 | +21.87 | **107.5** |
| `n ≈ c0+c1*B+c2*B²` | c0=59.9785, c1=0.1959152909, c2=−1.4804e−7 | −59.17 | +28.85 | **88.0** |

A global affine or quadratic estimate is off by up to ~60–86 numbers, i.e.
60–107 candidate checks. **Not usable.** The reason is structural: the local
slope is 15/P_d = 0.27/0.24/0.21/0.19 numbers per byte in d=1..4, and a
polynomial cannot track the digit-count breakpoints.

### 3.2 Per-region affine (exact rational slope 15/P_d)

`n_est = N_d + floor(15*(B-B0_d)/P_d)`:

| d | bytes | error histogram (n_true − n_est) |
|---|---|---|
| 1 | 30 | {0:7, +1:22, +2:1} |
| 2 | 378 | {−1:30, 0:318, +1:30} |
| 3 | 4260 | {−1:360, 0:3540, +1:360} |
| 4 | 28098 | {−1:2846, 0:22760, +1:2492} |
| all | 32766 | {−1:3236, 0:26625, +1:2904, +2:1} |

Candidate checks needed (check n_est, then n_est±1):

| checks | bytes |
|---|---|
| 1 | 26,625 (81.3 %) |
| 2 | 6,140 (18.7 %) |
| 3 | 1 (d=1 only) |

With a **rounding bias** instead of a floor (`+0.5`), the error becomes
one-sided:

| d | error histogram |
|---|---|
| 2 | {−1:180, 0:198} |
| 3 | {−1:2100, 0:2160} |
| 4 | {−1:14226, 0:13872} |
| all | {−1:16506, 0:16230} |

so `n = n_est − [B < L(n_est)]` — exactly **one** correction test:

| correction steps | bytes |
|---|---|
| 0 | 16,230 (49.5 %) |
| 1 | 16,506 (50.4 %) |
| 2 | 0 |

But each correction test needs `L(n_est)` (a division by 15 plus two FMAs,
≈5 ops), so the rounded-affine scheme costs ≈2 (estimate) + 5 (L) + 1 (compare)
+ 1 (decrement) = **9 ops and still needs the char index**, versus 4 ops for
the exact divmod. Conclusion: **the exact divmod dominates every affine scheme
— not because the residual is large, but because the exact integer divmod is
already only 4 ops and it also yields the char index for free.**

### 3.3 Exact divmod: correction table

| correction steps | bytes |
|---|---|
| 0 | **32,766 (100 %)** |

## 4. Full byte-generation model (`model.py`) — verified over all 32,766 bytes

The model implements the whole pipeline per PE (4096 PEs, 4 int lanes / 8 float
slots, LM0+T canvas, pack, transfer) and reproduces the official expectation:

```
model bytes: 32768 (last word has 2 don't-care bytes)
byte mismatches: 0     word mismatches: 0
```

The 4096-word output is byte-identical to the official testcase expectations.

### 4.1 Why 4 candidates are mandatory (measured)

For every block, count the numbers whose rendering intersects its 8 bytes
(`max-min+1`): span 1: 104 blocks, 2: 2,446, 3: 1,543, **4: 3 blocks**. The
three 4-candidate blocks are at `B = 120, 144, 168` (blocks 15, 18, 21, all in
the d=2 region). Since SIMD has no branching, the 4-candidate machinery is
required for all PEs; the exact inversion does not remove it.

### 4.2 Instruction budget of this model

| stage | ALU | MAU | imm | other |
|---|---|---|---|---|
| A region select | 3 | 0 | 0 | |
| B int→float | 1 | 1 | 0 | |
| C divmod P_d | 3 | 2 | 0 | |
| D slot decode | 4 | 1 | 0 | |
| E 4 candidates (class, digits, length) | 12 | 8 | 0 | |
| F canvas positions | 4 | 0 | 0 | |
| G digits (2 MAU groups) | 8 | 10 | 0 | |
| H canvas writes | 12 | 0 | 0 | |
| I pack | 6 | 0 | 0 | |
| I transfer | 0 | 0 | 0 | l1b 1, l2b 2, mv 2, nop 3 |
| prologue/consts (inherited) | 12 | 0 | 24 | |
| **total** | **65** | **22** | **24** | 8 |

Line estimate `max(ALU,MAU) + imm + other` = **97** — *worse* than 93. This is
the honest result: a naive "inversion-first" rebuild does not win, because the
rendering (E+G+H+F = 36 ALU here) is larger than the existing est/digits +
canvas (24 ALU), and the inversion (A–D ≈ 13) is not smaller than the existing
chain (≈13).

## 5. Where the 41 lines actually are

93 lines = ALU 66 + non-ALU 27 (from `docs/fizzbuzz-notes/08-redesign-notes.md`):

| block | lines | can the inversion touch it? |
|---|---|---|
| coordinates | 12 | no (9 ALU is the documented lower bound) |
| constants | 24 | partly (the 3 thresholds + 3 reciprocals ≈ 6) |
| est / digits | 16 | exact inversion ≈ 16–17 incl. positions → **−3 at best, ±0 realistic** |
| canvas | 8 | no |
| pack | 6 | no |
| non-ALU (nop 8, MAU-only, L1B/L2B/MV) | 27 | shrinks only when ALU shrinks |

Each ALU instruction is one line (ALU is the binding group at 66 ALU / 41 MAU),
so deleting the whole est/digits block saves **at most 16 lines** → ≥77. The
inversion therefore contributes ≈0–3 lines (→ ≈90). The remaining 25 lines to
52 must come from constants (24, the only block of that size) and coordinates
(12). To reach 52, the two blocks that
matter are **constants (24)** and **coordinates (12)**; a 53-line solution
implies ≈8–10 constants, not 24. (Note the coincidence 93 − 16 − 24 = 53.)

## 6. Obstruction (precise)

* An exact, correction-free inversion exists but is *already* essentially the
  cost of the existing approximate one (≈16–17 vs ≈14–16 lines including
  positions). The obstruction is the machine's line accounting: 4-lane SIMD
  amortises the approximate chain, and the 11-ALU chain is really the irregular
  region slot decoder, so exactness buys nothing.
* The digit stage's 16 ALU is `4 candidates × 4 digit positions`; the 4
  candidates come from the output layout (8 bytes span up to 4 numbers), not
  from the approximation. Hence it does not collapse.
* Global affine/quadratic inverses are off by 60–107 numbers and are useless;
  per-region affine is exact after ≤1 correction but costs more than divmod.
* The remaining gap to 52 is in constants + coordinates, i.e. outside the
  offset-inversion hypothesis.


## 7. If you still want to use it: cheapest exact inversion sequence

For the d=4 region with the shifted tiling (FB last, all pieces 5 bytes) this is
the minimal sequence I can find.  One PE, one lane; `Bf` is `B` as float32
(2^23 trick).  `bias` ≈ 0.002, `14` and `1000` are constants.

```vsm
fvadd  $Bf -4702  $Rf              # R = B - 4702                     (MAU, pairs)
fvfma  $Rf 0.0126582 0.002  $qf    # qf = R/79 + bias                 (MAU)
ffloor $qf  $qf2                   # floor(qf)                        (ALU)
fvfma  $qf2 -79 $Rf  $rf           # rf = R - 79*q                    (MAU)
fvmul  $rf 0.2  $jf                # rf/5                             (MAU)
ffloor $jf  $jf2                   # floor                            (ALU)
fmin   $jf2 14  $j                 # j = min(r//5, 14)                (ALU)
fvfma  $j -5 $rf  $cf              # c = r - 5*j                      (MAU)
fvfma  $j 1 1000  $nf              # 1000 + j                         (MAU)
fvfma  $qf2 15 $nf $n              # n = 1000 + 15*q + j              (MAU)
```

10 ops = 3 ALU + 7 MAU ⇒ **7 lines** when every ALU shares a line with a MAU.
Plus region select (3 ALU), the d=1 prefix override (~2) and the d=2/3 table
path (~3): **≈15 lines**.  The positions needed by the canvas are
`rel0 = -c`, `rel1 = rel0 + len0`, … (4 more ALU in model stage F), i.e. the
total inversion+positions ≈ 17–19 lines versus ≈14–16 for the existing
estimate + 11-ALU chain.  **This is why the digit stage cannot collapse.**

Note the two design constraints found on the way, both useful for any redesign:

* the shifted tiling removes the last irregularity of the d=4 region and makes
  the decode 3 ops shorter, at the cost of a 34-byte prefix override;
* the d=2/3 regions have no arithmetic slot decode (`A_j` is irregular), so a
  comparison chain or a table is unavoidable there; that is what the existing
  11-ALU chain supplies for all regions at once.

## 8. No VSM emitted

The model's line estimate is 97 > 93, so there is nothing worth submitting from
this design. A hand-written VSM was also not attempted because the interface
to the existing canvas/T machinery (T-indirect per-cycle addressing, write
masks, hazard spacing) would have to be re-derived, and the design above is
already line-negative on paper. The positive artifact is the exact inversion
plus the numbers needed to redirect the effort.
