# Over-fit audit of the 25 recorded MN-Core Challenge answers

Date: 2026-10-21 (JST) / 2026-10-20 (UTC).
Scope: every `problems/challenge/*/answer.vsm` (25 problems).
Question: does the recorded answer compute the declared function for **every admissible input**, or only for the values in the official `testcase.vsm`?

**Bottom line: 1 of the 25 answers is testcase-overfitted — `2.plus-two` — and 24 are universal on the evidence below.**
Eleven of the universal ones were checked exhaustively (all values, all pairs, or the single no-input instance); thirteen were checked by sampling plus structural cases because their domains are continuous or too large to enumerate. All 25 reference models reproduced the official expected outputs, and 289 of 300 judge runs were accepted; the 11 failures are all `2.plus-two` variants.

No file under `problems/` was modified. The original problem files, testcases and answers are copied to `problems/` in this directory (and never modified); generated testcases are in `variants/`, judge logs in `logs/`, and the raw machine-readable result is `results.json`.

## Method

1. **Reference semantics.** For every problem, the Python kernel in
   `mncompile/benchmarks/challenge/<slug>.py` was used as the reference model
   (`mncompile.oracle.run_reference`). Before using it, the official testcase
   was reconstructed logically (`mncompile.bench.official.logical_case`) and the
   model output was compared with **every** `d getd ... # expect=[...]` value.
   All 25 models match the official expectations (exactly, or within the
   declared `atol` for the float problems). There were no model mismatches.

2. **Input variants.** Six generic patterns were generated inside the declared
   domain:
   - `zero` — every element 0 (or the nearest admissible value if 0 is outside
     the domain; e.g. `1/512` for `fle`, `1` for `log2`);
   - `max` — declared maximum (for a full-range ULong tensor this is 2^64-1,
     i.e. the all-ones bit pattern);
   - `one` — 1 (or nearest admissible value);
   - `count` — counting / evenly spaced over the declared range;
   - `random` — uniform in-domain sample with a fixed seed (uniform over the
     value set for finite domains, rejection sampling for predicates);
   - `boundary` — low/high/mid/0/1 cycled.

   In addition, where the value domain is enumerable, **exhaustive sweeps** were
   generated:
   - `1.plus-one`: all 51 values in 4 cases (16 positions each, 816 checked outputs);
   - `2.plus-two`: all 100 values in 5 cases (20 positions each);
   - `3.a-plus-b`: **all 101² = 10,201 `(A[i],B[i])` pairs** exactly once, in 80 cases;
   - `4.mul7`: all 1001 values in 1 case (1024 positions);
   - `5.abs`: all 201 values in 1 case (5632 positions);
   - `8.fle`: all 2560 values in 1 case (2560 positions; the official testcase
     also covers every one of them);
   - `13.mod3`: all 256 values in 1 case (2048 positions);
   - `23.fizzbuzz-pe`: all 32,768 values in 1 case (32,768 positions);
   - `24.log2`: all 12 powers of two in 1 case (2048 positions).

   For large/continuous domains, 37 hand-built **structural variants** target the
   semantics instead of random values (e.g. identity/diagonal matrices for
   `mat-sq`, membership sets for `contains`, sorted/reverse/equal arrays for the
   inversion problems, single-bit words for `bit-reverse`, primary hues for
   `hsv2rgb`, a shuffled 1..32768 permutation for `fizzbuzz-pe`).

3. **Testcase generation.** Each variant is a full copy of the official
   `testcase.vsm` in which only the data values are replaced. The
   `mncompile.bench.testcase.parse_entries` entries are used to
   - rewrite every `d set` / `r` payload with the new logical values at the same
     logical indices, and
   - rewrite every `d getd ... # expect=[...]` comment with the reference
     model's output at the same logical indices.
   Addresses, PE/MAB/L1B/L2B selectors, dtypes, replication and `atol` are kept
   unchanged. This is important: the audit is about **value** over-fitting, not
   about using the fixed physical layout (using fixed addresses is legitimate
   because the layout is fixed by the problem).

   **Coverage verification.** After generation, every variant was re-parsed
   with `input_values` and every input element checked against its declared
   `low`/`high`/domain predicate: **0 out-of-domain values in all 275 variants**.
   The sweeps were also re-parsed and confirmed to cover exactly the full value
   sets (51/51, 100/100, 1001/1001, 201/201, 2560/2560, 256/256, 32768/32768,
   12/12) and a-plus-b to cover all 10,201 pairs.

4. **Official judge.** Every variant was run as
   ```
   python3 judge/judge-py/judge.py <variant>.vsm problems/challenge/<problem>/answer.vsm
   ```
   The unmodified recorded `answer.vsm` was used. Accept is `ACCEPTED!! score=...`;
   failures are recorded from the judge's `RESULT MISMATCH: pos=... actual=...
   expected=...` lines. In total there were **300 judge invocations**: 25 official
   testcases + 275 generated variants. 289 accepted; 11 failed, all in
   `2.plus-two`.

## Results table

Coverage key: **E** = exhaustive for the declared domain (all values, all pairs,
or the single no-input instance); **S** = sampled (continuous or too large for
enumeration), with structural cases where they matter. "Variants" counts the
generated variants only; the official testcase always passed.

| # | Problem (score) | Declared input domain | Official | Variants passed | Coverage | Verdict |
|---|---|---|---:|---:|---|---|
| 1 | `1.plus-one` (2) | Int 0..50, 16 elems | PASS | 10/10 | E: all 51 values x 16 positions (4 sweeps) | UNIVERSAL |
| 2 | `2.plus-two` (5) | Long 0..99, 20 elems | PASS | **0/11** | E: all 100 values (5 sweeps); 100/100 outputs wrong | **OVERFITTED** |
| 3 | `3.a-plus-b` (6) | Int 0..100 x2, 128 elems | PASS | 88/88 | E: all 101^2 pairs (80 cases) | UNIVERSAL |
| 4 | `4.mul7` (6) | ULong 0..1000, 1024 elems | PASS | 7/7 | E: all 1001 values | UNIVERSAL |
| 5 | `5.abs` (13) | Int -100..100, 5632 elems | PASS | 7/7 | E: all 201 values | UNIVERSAL |
| 6 | `6.fadd-mul` (14) | Float [0,1], 8192 elems | PASS | 6/6 | S: 6 patterns, incl. 0 and 1 | UNIVERSAL (sampled) |
| 7 | `7.mul2` (9) | Half [-1,1], 12288 elems | PASS | 7/7 | S: 6 patterns + half boundary (+-1, +-0.5, +-2^-14, +-2^-24, 0) | UNIVERSAL (sampled) |
| 8 | `8.fle` (4) | Float k/512, k=1..2560 (2560 elems) | PASS | 7/7 | E: all 2560 values (official also covers all) | UNIVERSAL |
| 9 | `9.transpose-addr` (10) | Double [0,64], 8x8 | PASS | 7/7 | S: 6 patterns + 8x8 ramp with 64 distinct values | UNIVERSAL (sampled) |
| 10 | `10.gather-easy` (6) | Double [0,10000] 16x1024 + ULong [0,1023] 16x16 | PASS | 15/15 | S: I swept over all 1024 values (4 cases) + 5 structural (I=0, I=1023, reverse, strided, X debug ramp) | UNIVERSAL (sampled) |
| 11 | `11.square-sum` (11) | Double [-1,1], 32x128 | PASS | 9/9 | S: 6 patterns + cancel/constant/ramp rows | UNIVERSAL (sampled) |
| 12 | `12.convert-endian` (3) | ULong 0..2^64-1, 4 elems | PASS | 7/7 | S: 6 patterns + byte walk exercising all 8 byte positions | UNIVERSAL (sampled) |
| 13 | `13.mod3` (8) | UInt 0..255, 2048 elems | PASS | 7/7 | E: all 256 values | UNIVERSAL |
| 14 | `14.mat-sq` (10) | Float integers 0..100, 8x16x16 | PASS | 11/11 | S: 6 + identity/diagonal/constant/rank-1 matrices + all 101 values | UNIVERSAL (sampled) |
| 15 | `15.contains` (20) | ULong 0..1000, A and B 1024 each | PASS | 12/12 | S: 6 + B={0..1000}, B={0}, B={0,1}, B={500} + all values | UNIVERSAL (sampled) |
| 16 | `16.count-up` (21) | no inputs; 32768 UInt outputs | PASS | 0 (no input) | E: single admissible input (empty) | UNIVERSAL |
| 17 | `17.transpose-mab` (15) | Double [-1,1], 256 elems | PASS | 7/7 | S: 6 patterns + 256 distinct ramp | UNIVERSAL (sampled) |
| 18 | `18.inversion-small` (9) | ULong 0..10, 64x16 | PASS | 11/11 | S: 6 + ascending/descending/equal/alternating + all 11 values | UNIVERSAL (sampled) |
| 19 | `19.inversion` (31) | UInt 0..100, 128x64 | PASS | 11/11 | S: 6 + ascending/descending/equal/alternating + all 101 values | UNIVERSAL (sampled) |
| 20 | `20.fizzbuzz` (93) | no inputs; 32768-byte String | PASS | 0 (no input) | E: single admissible input (empty); 32766 checked bytes | UNIVERSAL |
| 21 | `21.hello-world` (9) | no inputs; 16-byte String | PASS | 0 (no input) | E: single admissible input (empty); 13 checked bytes | UNIVERSAL |
| 22 | `22.bit-reverse` (10) | ULong 0..2^64-1, 16 elems | PASS | 10/10 | S: 6 + single-bit/walking-bit/alternating/complement | UNIVERSAL (sampled) |
| 23 | `23.fizzbuzz-pe` (9) | UInt 1..32768, 32768 elems | PASS | 8/8 | E: all 32768 values + shuffled permutation | UNIVERSAL |
| 24 | `24.log2` (7) | Int powers of two 1..2048 (12 values) | PASS | 7/7 | E: all 12 values (official also covers all) | UNIVERSAL |
| 25 | `25.hsv2rgb` (12) | Float [0,1), H,V != 1, 32x3 | PASS | 10/10 | S: 6 + six primaries, gray, black, H near 1 | UNIVERSAL (sampled) |

Every non-`2.plus-two` run accepted, including the exhaustive sweeps. The 11
failing runs are `2.plus-two`'s six base patterns and five exhaustive sweeps.

## The overfitted answer: `2.plus-two`

The official testcase has
```
X = [12, 0, 25, 61, 28, 49, 67, 95, 92, 86, 76, 79, 52, 99, 64, 73, 83, 89, 57, 70]
Y = [14, 2, 27, 63, 30, 51, 69, 97, 94, 88, 78, 81, 54, 101, 66, 75, 85, 91, 59, 72]
```
(`Y[i] = X[i] + 2`). The answer is five issue rows, and none of them adds 2:

```
# 88 51 85 72
idec $m[35,25,19,31] $n[19,11,33,39] $r0v
# 27 63 66 69
idec $m[9,29,13,39] $n[5,7,29,13]
# 75 78 91 94
idec $m[21,23,17,15] $n[31,21,35,17]
# 2 14 30 54
ixor $m[11,7,39,27] $r[1,1,0,2] $n[3,1,9,25]
# 59 81 97 101
ixor $m[27,5,37,19] $r[0,3,0,1] $n[37,23,15,27]
```

`idec` decrements a 32-bit lane; `ixor` XORs a 32-bit lane with a GRF value.
The source and destination address lists are a permutation chosen so that the
**official values** satisfy the required relation, not the identity of the
problem. For the first row:

| instruction lane | reads (word) | value | result | writes (word) | official Y |
|---|---|---|---:|---|---:|
| 1 | `$m[35]` = low32(X[17]) | 89 | 88 | `$n[19]` = low32(Y[9]) | 88 |
| 2 | `$m[25]` = low32(X[12]) | 52 | 51 | `$n[11]` = low32(Y[5]) | 51 |
| 3 | `$m[19]` = low32(X[9]) | 86 | 85 | `$n[33]` = low32(Y[16]) | 85 |
| 4 | `$m[31]` = low32(X[15]) | 73 | 72 | `$n[39]` = low32(Y[19]) | 72 |

The first row also writes its four results to `$r0v`; the fourth row then uses
`$r[1,1,0,2]` = `[51, 51, 88, 85]` and synthesizes four more outputs purely by
XOR coincidence:
`49^51=2` (Y[1]), `61^51=14` (Y[0]), `70^88=30` (Y[4]), `99^85=54` (Y[12]).
The fifth row similarly produces `99^88=59`, `25^72=81`, `57^88=97`,
`86^51=101`. This is a lookup table over the official multiset with a small
amount of 32-bit arithmetic; it is not an implementation of `x -> x+2`.

### Failing witnesses

All 11 generated variants fail; the judges' first mismatches are:

| Variant | Input | Expected | Actual |
|---|---|---|---|
| `zero` | every X[i] = 0 | 2 | **4294967295** = `0xFFFFFFFF` (all 20 words) |
| `max` | every X[i] = 99 | 101 | 1 or 98 depending on the word |
| `one` | every X[i] = 1 | 3 | 1 or 0 |
| `count` | X = 0,1,2,... | 2,3,4,... | 8,14,3,... |
| `random` | random 0..99 | x+2 | unrelated |
| `boundary` | low/high/... | x+2 | unrelated |
| `sweep-X-0..4` | all values 0..99, once each | x+2 | **20/20 wrong in every sweep** |

The sweep is value-exhaustive: `2.plus-two` is elementwise and has only 100
admissible values, and the five sweeps place 0..99 once each in the 20 output
positions. Every one of the 100 tested values produces a wrong output word at
the position where the sweep places it, and the zero/max/one variants fail at
all 20 positions. This is more than enough to refute universal correctness; a
full 100 x 20 cross product would be 2000 cases and was not necessary.

The all-zero witness is the cleanest:

```
$ python3 judge/judge-py/judge.py \
    research/experiments/overfit-audit/variants/2.plus-two/zero.vsm \
    problems/challenge/2.plus-two/answer.vsm
...
RESULT MISMATCH: pos=0 actual=4294967295 expected=2 error=4294967293
...
0 value(s) correct, but 20 value(s) mismatch
```

(The judge counts per output word: 0 correct, 20 mismatched.)

### Which instruction relies on the testcase

All five instruction rows do. The three `idec` rows read arbitrary source words
(`$m[35,25,19,31]`, `$m[9,29,13,39]`, `$m[21,23,17,15]`) and decrement them; the
two `ixor` rows read arbitrary source words and XOR them with values produced by
the first `idec` row (`$r[1,1,0,2]`, `$r[0,3,0,1]`). Each destination word list is
a permutation of the 20 output low halves. The specific source/destination
permutation and the `$r[...]` selection are the overfit: they were chosen from
the official testcase's values so that `source-1` or `source XOR saved` equals
the official `Y` at the destination. There is no `ladd`, `linc`, or any 64-bit
add/increment instruction anywhere in the program.

## Universal answers

### Exhaustively covered

- `1.plus-one`: four sweeps cover every value 0..50 at all 16 positions
  (816 outputs); the answer is two `iinc` rows and is lane-local.
- `3.a-plus-b`: 80 pair cases cover all 10,201 `(A[i],B[i])` pairs exactly once
  (10,240 = 80 x 128 slots; the last 39 slots repeat the first pairs); the
  answer is four `iadd` rows plus two `ipassa` and is lane-local.
- `4.mul7`: one sweep covers all 1001 values across 1024 positions; the answer
  is a per-lane `fvfma` with the constant 7.
- `5.abs`: one sweep covers all 201 values across 5632 positions; the answer is
  a sign-based select.
- `8.fle`: one sweep covers all 2560 declared values (the official testcase is
  a shuffle of the same 2560 values); the answer is the sign of `x*x-x` per lane.
- `13.mod3`: one sweep covers all 256 values across 2048 positions; the answer
  is a per-lane magic-reciprocal/FMA computation.
- `23.fizzbuzz-pe`: one sweep covers all 32,768 values and writes all 32,768
  outputs; a second, shuffled permutation of 1..32768 also passes. The answer is
  lane-local (no cross-lane reduction).
- `24.log2`: one sweep covers all 12 powers of two across 2048 positions; the
  official testcase also covers all 12. The answer is lane-local.
- `16.count-up`, `20.fizzbuzz`, `21.hello-world`: there are no inputs, so the
  official testcase is the only admissible input instance. `count-up` checks all
  32,768 outputs; `fizzbuzz` checks 32,766 bytes of the 32,768-byte tensor
  (the remaining bytes are outside the returned string); `hello-world` checks
  the 13 bytes of `"Hello, world!"`.

For `2.plus-two` the same value-exhaustive standard gives the opposite verdict:
all 100 values are covered and all 100 tested words are wrong.

### Sampled, with structural evidence

These domains are continuous or too large to enumerate. The verdict is
"UNIVERSAL (sampled)": every base pattern and every structural case accepts,
and the instruction listing contains no testcase-value lookup, arbitrary
source/destination word permutation, or constant derived from the official
data. This is strong evidence, not a formal proof.

- `6.fadd-mul`: six patterns over 8192 Float lanes, including 0 and 1; the code
  is `(x+8)*8` with vector `iadd`/`fvfma`, no data constants.
- `7.mul2`: six patterns plus the half-precision boundary set
  `{+-1, +-0.5, +-2^-14, +-2^-24, 0}`; `hvaddr` is a per-lane half add.
- `9.transpose-addr`: six patterns plus an 8x8 ramp with 64 distinct values;
  the code is a fixed `lpassa`/`drelu` layout permutation.
- `10.gather-easy`: I swept over all 1024 admissible indices (four cases), plus
  I=0 everywhere, I=1023 everywhere, I row reversal, a strided permutation, and
  the statement's `X[0]=0.1..1023.1` debug ramp (applied to every row in the
  structural variant). The answer uses T-register
  indirect addressing, which is the generic gather mechanism; it does not
  contain 256 index constants.
- `11.square-sum`: six patterns plus rows that must cancel to 0, a constant-row
  case, and a ramp; the code is a MAU reduction.
- `12.convert-endian`: six patterns plus a byte walk containing all byte values
  and all byte positions; the code is a fixed byte permutation with algorithmic
  `imm`/`bsl` constants.
- `14.mat-sq`: six patterns plus identity, diagonal, constant and rank-1
  matrices; the code is a matrix-unit multiply/transpose.
- `15.contains`: six patterns plus B={0..1000}, B={0}, B={0,1}, B={500}; the code
  is a matrix-unit membership computation with no A/B value constants.
- `17.transpose-mab`: six patterns plus a 256-distinct-value ramp; the code is a
  fixed-address layout copy. The hardcoded addresses are the fixed MAB layout,
  not testcase data.
- `18.inversion-small` and `19.inversion`: six patterns plus ascending,
  descending, all-equal and alternating rows, which exercise zero and maximal
  inversion counts; the code implements the inversion count, and the constants
  encode the declared value ranges (0..10 and 0..100), not the official array.
- `22.bit-reverse`: six patterns plus single-bit words at both ends/middle, a
  walking one-bit pattern, alternating `0xAAAA.../0x5555...`, and complements;
  the code is a fixed 1024-bit reversal.
- `25.hsv2rgb`: six patterns plus the six primary/secondary hues with S=1,
  gray (S=0), black (V=0), and H just below 1; the code follows
  `colorsys.hsv_to_rgb`, and the constants are algorithmic.

## Limitations and caveats

- "UNIVERSAL (sampled)" is not a machine-checked proof for the 13 continuous or
  large-domain problems. It is a verdict from (a) six value patterns, (b)
  targeted structural cases, and (c) inspection of the instruction listing.
  A program that is wrong only on a narrow unsampled set would not be caught;
  none of the 13 shows the lookup/permutation signature that `2.plus-two` does.
- The reference models are the Python kernels in
  `mncompile/benchmarks/challenge/`. They reproduce every official expected
  output, but they are models of the problem statements, not the official spec
  itself. `10.gather-easy`'s statement also mentions a debug ramp in `X[0]`;
  our variants deliberately violate that guarantee, and the answer still
  passes, so it does not rely on it.
- Variants keep the official physical layout and addressing. A solution that
  hardcodes layout addresses (e.g. `17.transpose-mab`) is not penalized for
  that; the audit is about **data** over-fitting. The fixed layout is part of
  the problem.
- `20.fizzbuzz` and `21.hello-world` check 32,766 and 13 bytes respectively,
  not the full declared tensor sizes (32,768 and 16). The unchecked trailing
  bytes are outside the string returned by the reference model, so this testcase
  imposes no constraint on them.
- The judge runs were on the bundled emulator (`gpfn3_package_main`) and
  assembler (`assemble3`) via `judge/judge-py/judge.py`, i.e. the same official
  gate that accepted the recorded answers.

## Reproduction

```sh
cd /home/wogikaze/wgkz/mncore

# 1. base patterns + exhaustive sweeps + all-pair a+b cases (238 variants)
python3 research/experiments/overfit-audit/audit.py

# 2. structural variants for the large/continuous domains (37 variants),
#    merged into the same results.json
python3 research/experiments/overfit-audit/audit.py --specials
```

`results.json` is the merged machine-readable record. Every variant file is in
`variants/<problem>/<variant>.vsm`; the corresponding judge output is in
`logs/<problem>/<variant>.log`. The overfit witness can be re-run directly:

```sh
python3 judge/judge-py/judge.py \
  research/experiments/overfit-audit/variants/2.plus-two/zero.vsm \
  problems/challenge/2.plus-two/answer.vsm
```

The harness is `audit.py`; it imports the repo's own
`mncompile.bench.problems`, `mncompile.bench.official`,
`mncompile.bench.testcase`, `mncompile.oracle`, `mncompile.values` and
`mncompile.verify`, and writes only under this directory.
