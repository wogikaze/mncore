# Constants: which `imm`s cost a word, and can `del_18` be closed?

Agent: twoblock (redirected by parent to the constants question).
Baseline for every number below: `problems/challenge/20.fizzbuzz/answer.vsm`,
`fbcheck` = `OK words=93 lines=93 mismatches=0`,
`fbverify` = `ACCEPTED!! score=93 j=91 m=2 bytes=3054`.
Candidates are in `const/`; logs in `const/classify_imm.log`.

Reproduce:

```sh
python3 const/classify_imm.py                  # the 24-imm classification
python3 const/dump_regs.py ../../../problems/challenge/20.fizzbuzz/answer.vsm --after 23
python3 const/diff_dram.py <candidate.vsm>     # per-word DRAM diff vs the official expectation
python3 tools/fbasm.py <cand> && python3 tools/fbverify.py research/experiments/twoblock/<cand>
```

## 1. Classification of the 24 `imm` expressions (measured)

Method: delete only the `imm` expression (keep the rest of its line; drop the line
if it becomes empty), then `fbcheck` gives the assembled word count and the number
of wrong DRAM words. An imm whose deletion drops the count to 92 **occupies its own
word**.

| line | imm | words | wrong words | class |
|---|---|---|---|---|
| 14 | `imm ui"0x4b000000" $t` | 92 | 4096 | **own-word** |
| 18 | `imm i"32" $r25` | 92 | **3** | **own-word** |
| 19 | `imm i"408" $r26` | 92 | 50 | **own-word** |
| 20 | `imm i"4672" $r27` | 92 | 581 | **own-word** |
| 26 | `imm f"63" $s3` | 92 | 4089 | **own-word** |
| 30 | `imm f"0.0140846" $s[8,8,7,8]/$imr1` | 92 | 532 | **own-word** |
| 31 | `imm f"0.0126583" $s[8,8,8,7]/$imr1` | 92 | 3512 | **own-word** |
| 49 | `imm f"0.001" $lr72` | 92 | 2669 | **own-word** |
| 56 | `imm ui"0x4b000075" $r68` | 92 | 1266 | **own-word** |
| 78 | `imm i"8" $r8` | 92 | 4096 | **own-word** |
| 2 | `imm i"56" $r16/1000` | 93 | 3576 | attached |
| 3 | `imm i"599" $s31` | 93 | 3512 | attached |
| 15 | `imm i"8" $r[16,17,28,0]/1110 $s28` | 93 | 2897 | attached |
| 22 | `imm i"13" $s29` | 93 | 47 | attached |
| 23 | `imm i"66" $s30` | 93 | 533 | attached |
| 27 | `imm ui"0x4b000030" $lr12` | 93 | 3516 | attached |
| 28 | `imm ui"0x4b00000a" $r71` | 93 | 4044 | attached |
| 29 | `imm f"0.0158731" $s[8,7,8,8]/$imr1` | 93 | 44 | attached |
| 34 | `imm f"0.1" $lr76` | 93 | 3132 | attached |
| 36 | `imm ui"0x4b00007a" $r[65,66,69,70]` | 93 | 3113 | attached |
| 48 | `imm f"0.01" $lr74` | 93 | 3098 | attached |
| 52 | `imm ui"0x4b000046" $r63` | 93 | 2111 | attached |
| 54 | `imm ui"0x4b000069" $r64` | 93 | 2111 | attached |
| 55 | `imm ui"0x4b000042" $r67` | 93 | 1266 | attached |

**10 own-word, 14 attached** (matches the parent's ~10 estimate and
`architecture.md` §6's imm-only list, with the boundary cases resolved).

Important: *attached* imms are free but also **not removable** (their deletion saves
no word and breaks 44..4044 words). So the only word wins available are the 10
own-word ones, and each of those carries a load-bearing value.

### Per own-word imm: value, location, consumer

| line | value | where | consumer |
|---|---|---|---|
| 14 | `0x4b000000` (float 2^23) | T (all 4 cycles) | `$t` in L16 `ior $lr2v $t` (constants 1..4), L17 `fvadd -$t`, L27.. L34 float chain, L50/L51 `$mt` T-indirect addressing |
| 18 | 32 | GRF0 w25 | L24 `isub $s0 $r24v $omr1`, cycle 1 only |
| 19 | 408 | GRF0 w26 | L24, cycle 2 only |
| 20 | 4672 | GRF0 w27 | L24, cycle 3 only |
| 26 | 63.0 | GRF1 w3 | L36 `fvfma $s3 -$aluf $n1 $nowrite` |
| 30 | 1/71 | GRF1 w7 (cycle 2, `/$imr1`) | L34 `fvmul $mauf $s7 $nowrite` |
| 31 | 1/79 | GRF1 w7 (cycle 3, `/$imr1`) | L34 (same read, cycle 3) |
| 49 | 0.001 | GRF0 lw72 | L52 `fvmul $lr72v $ls48 $nowrite` |
| 56 | `0x4b000075` ('u') | GRF0 w68 | L76 `fvpassa/$imr15 $r67v $mt42v` (cycle 1 of `$r67v`) |
| 78 | 8 | GRF0 w8 | L81/L83 `ilsl $aluf $r8` (pack shift amount) |

Measured register state just before L24 (which is what the L18 constant feeds;
`const/dump_regs.py --after 23`, identical for all PEs):
GRF0 w2..17 = 1,1,2,2,3,3,4,4,5,5,6,6,7,7,8,8; **w24 = 0 (never written)**,
w25 = 0x20 (32), w26 = 0x198 (408), w27 = 0x1240 (4672), w28 = 8;
GRF1 w28..31 = 8, 13, 66, 599.

## 2. `del_18` (92 words, 3 wrong words): exact diagnosis

`research/experiments/constants/del_18.vsm` measured here:

```
ASM-OK words=92
wrong bytes=22  wrong words=3  (DRAM words 0,1,2 = bytes 0..23)
  word 0  exp "1\n2\nFizz"  got "\nFizz\n04"
  word 1  exp "\n4\nBuzz\n" got "\nBuzz\nFi"
  word 2  exp "Fizz\n7\n8"  got "zz\n07\n8"
```

The rendered text is the **d=2 template with zero-padded 2-digit numbers**
(`07`, `08`) instead of the d=1 template. So the missing constant is exactly the
`(8b >= 32)` flag of mask entry 1: cycle 0 of `isub $s0 $r24v $omr1` compares the
block's first byte `8b` (GRF1 w0) against GRF0 w24..w27 = 0, **32**, 408, 4672.
With w25 = 0 the flag is 1 for every block, so blocks 0..3 (bytes 0..29 = the
1-digit region) take the d≥2 path. Only blocks 0..2 show it because block 3
straddles the boundary.

Any threshold `T` with `8b` a multiple of 8 needs `T ∈ (24, 32]`; 32 is the only
value in the machine, so it must be materialised.

## 3. Measured repair attempts for `del_18` (all fail)

| # | change | asm | wrong words | why it fails |
|---|---|---|---|---|
| v5 | `const/del_18b_fold32_at_L2.vsm`: L2's `imm i"56" $r16` retargeted to `imm i"32" $r25` + del L18 | OK, 92 | 3576 | the 56 at GRF0 **w16 is load-bearing** (see v4) |
| v4 | keep L18, L2's imm 56 → 32 | OK, 93 | 3069 | so 56 cannot be retargeted at all |
| v1 | L2 imm = `imm i"32" $r[16,25,25,25]/1000` + del L18 | OK, 92 | 3072 | same 56 damage |
| v2 | L2 imm = `imm i"56" $r25/1000` + del L18 | OK, 92 | 3579 | w25 = 56 (> 32) |
| v3 | L2 imm = `imm i"32" $r16/1000` + del L18 | OK, 92 | 3072 | w25 = 0 |
| t2 | del L18 + `imax $s0 $r[25,26,27,28] $omr1` (rotates the threshold window, keeps w26/w27) | OK, 92 | 580 | flag order becomes [f32,f408,f4672,f8], the consumers need [1,f32,f408,f4672] |
| t3 | del L18 + `imin $s0 $r24v $omr1` (inverted sense) | OK, 92 | 4048 | sense inverted, thresholds unchanged |
| t4 | del L18 + L15's imm gains a 4th cycle writing w25 = 8 (`$r[16,17,28,25]/1111`) | OK, 92 | 4096 (all zero) | an `imm` with all 4 cycles enabled breaks the program outright (side effect of the 4th flat address) |
| t1 | `imm i"0" $t` co-issued on L17 | **ASM-OK** | 4044 | the slot exists but only T is writable there, and T is load-bearing |
| t1b | `imm i"0" $t` co-issued on L21 | **ASM-OK** | 4044 | same |

## 4. Why the 32 has no free home (measured obstruction)

The only lines before the consumer L24 that have a **free ALU slot** are the two
MAU-only lines **L17 and L21** (all other lines before L24 already carry an ALU
expression; `nop` cannot co-issue). Measured (t1/t1b): an `imm` *does* assemble on
both. But:

* L17 writes **GRF0 + GRF1 + LM1** and L21 writes **GRF0 + GRF1 + LM1**, so an
  `imm` there cannot write any of those three files (two writes to the same PE
  operand in one step is rejected — and the parent's host matrix shows the same:
  `out_grf0` / `out_grf1` conflicts).
* `imm` is barred from **LM0** unconditionally ("immop can't output to LM0").
* Therefore the only legal destination on L17/L21 is **T** — and T = `0x4b000000`
  from L14 is consumed at L16 (`ior $lr2v $t`) and L17 (`fvadd -$t`), i.e. *before*
  those lines: it cannot be moved there. L14 is itself an own-word imm (4096 wrong
  words if deleted), and there is no free ALU slot before L16 either.
* L24 itself already reads GRF0 (`$r24v`) and GRF1 (`$s0`), so a constant placed in
  either file needs the *other* file switched, which re-introduces the same problem
  one step earlier.

Conclusion: **`del_18` cannot be closed with the current instruction schedule.**
The value 32 is needed in GRF0 w25, in a slot that is already occupied by another
expression whose value is load-bearing, and no other slot before the consumer can
write GRF0/GRF1/LM1.

## 5. What would actually close it (recommendation)

The blocker is not the constant, it is that **every ALU slot before L24 is taken**.
Closing `del_18` therefore requires freeing one ALU word before L24, i.e. the same
operation as the 93→52 problem, not a constant substitution. The cheapest concrete
candidates (in the order I would try them):

1. **Fuse two of the coordinate ALU lines into one expression with two destinations.**
   `ilsl $aluf $r4 $s0/1000 $r0/1000` (L13) already demonstrates a 2-destination
   ALU expression; L5/L7 (`iand`) and L6/L8 (`ilsl`) are the same shape with
   `$nowrite` outputs and are the natural candidates.
2. **Re-derive one threshold from another in the consumer**: `408 = 8·51` and
   `4672 = 8·584` are not usefully reachable, but `32 = 8·4` is: if L24's cycle-1
   operand were `$r[24,17,26,27]` (i.e. read GRF0 w17 = 8) an *alsl* would be
   needed — impossible in one ALU expression, so this needs the freed slot anyway.
3. Do not spend more effort on the other nine own-word constants: their deletion
   damage is 50..4096 wrong words, and each has the same "no free slot between
   producer and consumer" obstruction (e.g. L49's 0.001 = 0.01·0.1 needs the
   multiply after L48 and before L52, where the only ALU-only line is L49 itself;
   L50 is MAU-only, L51 is ALU-only; and the two GRF0 operands 0.01/0.1 cannot be
   read by one MAU expression — "GRF0 is read at two different addresses").

## 6. Files

```
const/classify_imm.py     classification of all 24 imms (this report §1)
const/classify_imm.log
const/dump_regs.py        GRF0/GRF1/T word dump after any line (PE-selectable)
const/diff_dram.py        per-word DRAM diff vs the official expectation
const/del_18b_fold32_at_L2.vsm, v1..v5, t1..t4*.vsm   every candidate measured above
research/experiments/constants/del_18.vsm             the parent's 92-word candidate
```
