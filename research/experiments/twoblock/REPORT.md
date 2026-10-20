# Two-block / 2-candidate canvas renderer: measurements, and the constants follow-up

Agent: twoblock. Directory: `research/experiments/twoblock/`.
Baseline: `problems/challenge/20.fizzbuzz/answer.vsm` — re-measured here:
`fbcheck OK words=93 lines=93 mismatches=0`, `fbverify ACCEPTED!! score=93 j=91 m=2 bytes=3054`.

Two deliverables:

1. `REPORT.md` (this file): the 2-block / 2-candidate risk measurement and why the
   2-block restructure cannot pay for itself (§1–§5).
2. `const/REPORT.md`: the follow-up the parent asked for — classification of the 24
   `imm` expressions, the `del_18` diagnosis, ten measured repair attempts, and the
   measured proof that `del_18` cannot be closed with the current schedule (§6).

Reproduce everything: `python3 risk2.py`, `python3 probe_ll3.py`,
`python3 probe_twobase.py`, `python3 const/classify_imm.py`,
`python3 const/diff_dram.py <cand>`; gates `python3 tools/fbasm.py`,
`fbcheck.py`, `fbverify.py`.

---

## 1. What a "candidate" really is (measured)

Reference: `research/experiments/offset-inversion/ref.py`; verified here to be
**byte-identical to the official testcase expectation** (32766/32766 bytes,
0 mismatches), so the tables below are statements about the official data.

For every 8-byte output word `b` (bytes `8b..8b+7`):

| quantity | histogram |
|---|---|
| numbers intersecting the word | 1:104, 2:2446, 3:1543, 4:3 |
| numbers owning >=1 **digit** char in the word | 0:580, 1:2466, **2:1050, >2:0** |
| digit characters in the word | 0:580 .. 7:265 (max **7**) |

**So 2 candidates are sufficient for the digit stage — for all 4096 words — provided
the candidates are the two digit-*owning* numbers, not the first two intersecting
numbers.** The digit owners sit at offsets {0},{1},{2},{0,1},{1,2},{0,2} relative to
the first intersecting number (histogram in `logs/risk2.log`); offset 3 never
occurs, so the 4th est candidate is provably unnecessary. 103 words have two
digit owners that are `n` and `n+2` (non-adjacent), and each owner's digit positions
form a contiguous run (44 distinct signatures).

The "2 candidates" therefore do **not** shrink the renderer: the 93-word answer's
digit stage already computes exactly 2 numbers x 4 digit positions = 8 int32 values
(verified by dumping GRF1 words 20..27 before the canvas writes: e.g. PE b=666 holds
the 8 digits of 1126 and 1127; PE b=15 holds the 4 digits of 31 and 32).

Artefacts: `risk_digitowners.csv` (all 4096 words: owners, offsets, positions,
digit counts), `risk_naive_first2.csv` (the 759 words a "first two intersecting
numbers" renderer would corrupt — a real pitfall, since the first two intersecting
numbers often own no digits at all, e.g. word 2 = `Fizz\n7\n8` intersects 6,7,8 but
only 7 and 8 own digits).

## 2. The ALU is 8 int32 lanes wide, and `ll` does not widen it (measured)

`python3 probe_ll3.py` (log `logs/ll_probe.log`), official assembler ASM-OK for all
rows, native-simulator values:

| instruction | GRF1 words 16..19 | reading |
|---|---|---|
| `iadd $llr0 $lls0 $lls16` | `0b 0b 01 01` | 1+10 in the MSB long word's 2 lanes; the LSB long word is the **first input's LSB passed through** |
| `ilsl $lls0 $llr0 $lls16` | `14 14 0a 0a` | 10<<1; then 10,10 passed through |
| `ipassa $llr0 $lls16` | `01 01 01 01` | both long words copied (4 words/cycle) |

So for every *arithmetic* opcode a 2-long-word operand gives **2 computed int32 lanes
per cycle = 8 per instruction word**; only `passa`/`imm`/`zero`/`bfe`/`bfn` move
4 words/cycle (SDM table 3.9 "2-long-word operation = no" for the rest). One block's
digit stage (2 numbers x 4 positions) already fills all 8 lanes, so two blocks need
two instructions per operation.

## 3. Corrected 2-block budget

Per-block stages are lane-bound and double; only coords, the constants and the pack
amortise:

| stage | 1 block | 2 blocks |
|---|---|---|
| coords | 12 | 12 |
| constants | 24 | 24 (same count, not shareable) |
| est / selection / digits | 16 | **32** |
| canvas writes | 8 | 8 (>=2 possible with `ll` writes, but see §4) |
| pack | 6 | 6 |
| **ALU total** | **66** | **82** |
| transfer tail | 15 j + 2 m = 17 (measured, `p12_final_2block.vsm`, ASM-OK) | |

`architecture.md` §6 gives the 1-block stage costs (coords 12, constants 24,
est/digits 16, canvas 8, pack 6). The 2-block restructure therefore costs **+16 ALU
and +1 tail word** versus the 1-block design: it is a net loss, and
`algo-redesign` §9's 53-word budget counts the per-block stages once.

## 4. Two positive side measurements (useful for any future canvas work)

* One `ipassa` with a 2-long-word **destination** writes 4 canvas words per cycle
  (probe_ll3 `ipassa $llr0 $lls16`), i.e. a whole 8-char block per 2 cycles; and
  p13 (packer) showed 4 arbitrary `(char, position)` pairs per line via per-cycle
  flat addresses. Both are confirmed here.
* Per-cycle T is real (the accepted answer uses T[0]=7, T[1]=5 for two different
  digit-slot bases, measured), but I could **not** get 4 independent T cycle bases
  with the available idioms (`fftoi $lmt[...] $t`, `lpassa $lm0v $lt`,
  `lpassa $lrN $t`); `probe_twobase.py` reports what each idiom actually writes.
  Any plan that needs block A and block B to have different canvas bases in one
  instruction must measure this first.

## 5. Verdict on the 2-block direction

* 2 candidates/block is **sufficient** (measured) but does not reduce instructions.
* 3+3 candidates do not fit 8 lanes, and `ll` does not help (§2).
* The 2-block tail is +1 word (§3).
* Net: **the 2-block restructure cannot beat the 93-word baseline**, and the
  53-word target is ~20 words away regardless of the block layout. The productive
  direction is the 1-block design with fewer ALU expressions (constants and
  coordinates), not the block layout.

## 6. Constants follow-up (parent request)

See `const/REPORT.md`. Headline: **10 of the 24 `imm`s own their word**
(L14, L18, L19, L20, L26, L30, L31, L49, L56, L78); the other 14 are free but also
load-bearing. `del_18` (the 92-word candidate with only 3 wrong words, bytes 0..23)
is **not closable by constant substitution**: the 32 is needed in GRF0 w25, the only
free ALU slots before its consumer L24 are the MAU-only L17/L21 (measured ASM-OK for
an `imm` there), but those lines already write GRF0+GRF1+LM1, `imm` is barred from
LM0, and T (the only free destination) is consumed *before* those lines. Ten
candidates were built and measured; the closest still has 580 wrong words. Freeing
an ALU word before L24 (a 2-destination ALU fusion) is the prerequisite, i.e. the
same problem as 93→52.

## 7. Files

```
risk2.py                     2-candidate risk tables (verified vs the official bytes)
risk_digitowners.csv         one row per word: digit owners, offsets, positions
risk_naive_first2.csv        the 759 words a "first 2 intersecting numbers" renderer breaks
probe_ll3.py, logs/ll_probe.log       2-long-word lane-width measurements
probe_twobase.py             per-cycle-T and 4-words/cycle write probes
logs/risk2.log
const/                       the constants classification + all measured del_18 repairs
```
