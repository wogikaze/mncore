# Constants block: can the 10 imm-only lines be synthesised? — measured report

Scope: the 10 imm-only lines of `problems/challenge/20.fizzbuzz/answer.vsm`
(93 words, `fbverify` ACCEPTED), lines **14, 18, 19, 20, 26, 30, 31, 49, 56, 78**.
Question: can any of them be deleted (or its constant produced elsewhere for free)
using mechanisms that already work in this ISA?

Baseline (re-verified this session):

```
python3 tools/fbasm.py    base.vsm   -> ASM-OK words=93
python3 tools/fbcheck.py  base.vsm   -> OK words=93 lines=93 mismatches=0
python3 tools/fbverify.py base.vsm   -> ACCEPTED!! score=93 j=91 m=2 bytes=3054
```

Verdict: **no word was removed with `mismatches=0`. The best verified candidate is
`del_18.vsm` = 92 words, assembles cleanly, and is wrong in 22 bytes** (official judge:
`32744 value(s) correct, but 22 value(s) mismatch`, positions 0..23 = long words 0,1,2).
Everything below is measured with `assemble3 --instruction-mode flat`, the native
simulator (`fbcheck`), and the official judge (`fbverify`) where marked.

All scripts and logs are in this directory (`probe_*.py`, `host_*.py`, `del_sweep.py`,
`census.py`, `state.py`, `build.py`, `logs/`).

---

## 0. ISA facts measured this session (all reused below)

| # | fact | evidence |
|---|---|---|
| F1 | `imm` is an ALU-group expression that **clobbers the ALU forwarding register `aluf`** with its own output (so an imm between a producer and a consumer of `$aluf` is semantically live) | `imm i"5"` then `iadd $aluf $aluf $s4` → `s4 = 10` |
| F2 | an `imm`'s output is 1 value replicated 4× (or `x,0,x,0` with the `u` option), one **word per cycle**, to the addresses of the flat list; the mask selects cycles | `imm ui"32" $r[24,25,26,27]/1111` → words 24,26 = 0x20, words 25,27 = 0 |
| F3 | `T`-relative LM0 addressing adds `T mod 4096` words (LM0/LM1 are 2048 long words): `T=5` and `T=0x4b000005` address LM0 word 5 | `probe_t2.py`: both produce the same reads |
| F4 | the `dmwrite`/`dmread` pair is a **per-PE rotation of the 4 cycle values** (4×4 transpose inside the MAB); it cannot create values. `dmread $lx0 $lr0v4` stored `aluf` = `{0,2,4,6}` at words 0,4,8,12 and `iinc $mreadf $lr2v4` stored `{1,3,5,7}` at words 2,6,10,14, so the net table is 1..7 at words 2..14 | `probe_write.py`, `probe_sem.py` |
| F5 | GRF write→read minimum gaps: **MAU read = 0 steps**, **ALU read = 3 steps** (read at write+3; 2 is rejected), **T write→T read = 2 steps** | `probe_gap.py`, `del_sweep.py` |
| F6 | MAU has **no immediate/float-literal operand** (`fvadd $r0 63.0 $r16` → `Invalid location : 63.0`) and MAU sources are one PE operand per bank (two GRF0 reads = `in_grf0`/`in_grf0`) | `probe_mau.py` |
| F7 | the canvas write mask `$imr15` is the constant **5 = 0b0101 per cycle** (half-word pattern of the negated `u`-imm `x,0,x,0`); a *fixed* mask literal `/0101` is **not** equivalent (4096 mismatches) | `state.py`; `cand_m1_masklit.vsm` |
| F8 | `$r16 = 56` (written by L2's "dead" imm) is **not dead**: L7 `iand $peid $r[14,16,0,0]` uses it as the bit mask 0x38 (peid bits 3..5). Replacing it with 32 shifts the whole output by 512 long words | `cand_c4_32atL2.vsm` (3567 wrong long words, first wrong = 512) |
| F9 | `$r68` (L56) is written and never read (true dead value), and `$s31 = 599` (L3) *is* read through `$s28v` at L25 | grep + `state.py` |
| F10 | `aluf`-produced omr15 can be regenerated at any ALU-only line whose *previous* step is a `u`-imm; **L56 works** (measured mask = 5) | `hvpassa -$aluf $omr15` appended to L56 → `omr15 = {5,5,5,5}` |

### Co-issue host matrix (mechanism 2)
`host_matrix.py` / `logs/host_matrix.log`: for each of the 33 ALU-only lines, adding one
MAU expression. 11 lines accept `GRF0→GRF0`, 6 more accept `GRF1→GRF0`, 13 accept
`GRF0→GRF1`, and 12 accept `GRF0→T`. The 17 MAU-only lines accept no ALU (L17/L21
write GRF0+GRF1, the canvas lines L40/L41/L50/L60..L76 touch LM0, which is a hard
`immediate`+`lm0` field conflict).

---

## 1. Per-line verdicts

### L14 `imm ui"0x4b000000" $t` — NOT removable (3 roles, no free slot)
Measured roles: (a) `T = 2^23`; (b) its `x,0,x,0` forwarding pattern is what makes
`omr15 = 5` at L15 (F7); (c) it seeds the float table 1.0..4.0 built by L17.
Relocation attempts:
* T imm → L2 (the `i"56"` slot): assembles and `T` is right (`cand_c1`), but the 56
  bit mask disappears → **all PE coordinates shift** (F8).
* omr15 can be produced at L56 instead (F10), so L15's `hvpassa` is movable — but that
  frees an MAU slot, not an ALU slot, and L15's own `imm i"8"` is still needed.
* literal-mask replacement of `$imr15` is invalid (F7): `cand_m1_masklit.vsm`, 4096
  mismatches.
* No MAU can make `2^23` earlier: the float table (1..16) only exists from L17/L21/L23.

### L18 `imm i"32" $r25` — closest; NOT removable (measured exhaustive)
* Deleting it alone: `del_18.vsm` = **92 words, ASM-OK, 22 bytes wrong** (long words 0,1,2).
  Cause: with word 25 = 0 the mask thresholds become `{0,0,408,4672}`, so the
  cumulative "last written cycle wins" mask merges regions 0 and 1; blocks b=0,1,2
  then use region 1's constants (T offset 13 instead of 8, reciprocal 1/71 instead of
  the region-0 one).
* Exhaustive host sweep (`host18.py`, `logs/host18.log`): for every one of the 92 other
  lines, put `imm i"32" $r25` on that line and delete L18. **Only L86, L89, L90
  assemble — and all three are after the consumer L24**, so the value arrives too late
  (still 3 long words wrong). No line at or before L23 can host it.
  Why: L17/L21 (the only MAU-only lines before L24) write GRF0+GRF1
  (`out_grf0`/`out_grf1`), L40/L41/L50/L60+ touch LM0 (imm+LM0 is a hard field
  conflict), and all 24 pre-L24 ALU expressions are live.
* MAU route: the largest float reachable with the two free MAU slots at L19/L20 is
  `4*4+4 = 20.0` (only 1.0..4.0 exist there; word 108 reads are racy at L19, F5).
  `32.0 = 8*4` would need L20's `mauf` chain (8.0 at L19), and the integer conversion
  needs `fftoi` — a third MAU slot that does not exist before L24 (L21/L22/L23 are
  MAU-busy; L24 already has `fvpassa $ln102 $lr78`; L25 is the consumer).
* Imm-value reuse was measured and fails: `s29=8` (merging 0/1 with offset 8) →
  51 mismatches; `s28=13` → 4096 mismatches.
* No other existing imm can carry 32: L2 (56 bit mask, F8), L3 (599 → `$s31` is part of
  `$s28v`, F9), L15 (8 → `$s28`), L22/L23 (13/66 → `$s29/$s30`), L27 (`0x4b000030` →
  `$lr12`, consumed at L54).

### L19 `imm i"408" $r26`, L20 `imm i"4672" $r27` — NOT removable
Deletion costs 50 resp. 581 mismatches (`del_19.vsm`, `del_20.vsm`). Same slot scarcity
as L18 (no free ALU slot before L24) and, worse, 408 and 4672 have no cheap MAU
factorisation from the floats that exist at L19/L20 (1..4): 408 = 8·51, 4672 = 64·73.

### L26 `imm f"63" $s3` — NOT removable
Deletion costs 4089 mismatches. It has two roles: `$s3` itself (but note L27 overwrites
word 3, so the *live* role is) **`aluf = 63.0` for L27** (`fvadd $aluf $r116` = 63+8 =
71.0) plus the value for the `63 → 71 → 79` addition chain (L27/L28).
Synthesis would need `63.0 = 4*4*4 − 1`: three chained MAU ops. Before L27 only L19 and
L20 accept a MAU expression (`cand_v1/v2_63mau.vsm`: L18 rejects any read of words
102..108 as racy, "A racy memory read at GRF0 address 108 ... at line 18"; L21..L25
reject `mau`/`mau` or `in_grf*`). And even with the value, `aluf` at L27 must be the
63.0 pattern, which only an ALU expression can supply.

### L30 `imm f"0.0140846"` (1/71), L31 `imm f"0.0126583"` (1/79) — NOT removable
Deletion costs 532 / 3512 mismatches. Blocked by arithmetic, not by slots: the MAU has
fvadd/fvfma/fvmul/fvpassa/fftoi/ffloor/bfe/bfn/rsqrt only — **no reciprocal**, and these
two are per-PE conditional constants (dynamic `$imr1` mask, destinations `[8,8,7,8]` and
`[8,8,8,7]`), so they cannot be merged with each other either.

### L49 `imm f"0.001" $lr72` — NOT removable
`0.001 = 0.1 * 0.01` is a single realizable MAU op (0.1 at L34, 0.01 at L48; the
`fvmul` would write the same `$lr72v`, and float32 rounding must be checked), but the
only ALU-only line between L48 and the consumer L52 is L49 itself, and **L49 is a
mandatory T-write→T-read spacer** (F5): deleting it gives
`A racy memory read at T is detected at line 49`.

### L56 `imm ui"0x4b000075" $r68` — NOT removable (dead value, load-bearing step)
`$r68` is never read (F9), yet the line is a mandatory GRF1 spacer between L55's write
of `$ls20v` and L57's read of `$s[20,22,21,23]`: deleting it yields
`A racy memory read at GRF1 address 20 ... at line 56`. It cannot be turned into a
no-op either (`nop` costs the same word), and moving the canvas write that would fill
it fails: `cand_e1/e2/e3` (merge `fvpassa $r67v $mt42v` into L77) all fail — GRF0/GRF1
read conflicts or `A LM0 memory port is unavailable at line 78`.

### L78 `imm i"8" $r8` — NOT removable (value is reusable, step is not)
The value 8 already exists as GRF1 word 28 (`$s28`, written by L15), so the pack's
`ilsl $aluf $s28` works — but the line is the mandatory T-write→T-read spacer:
L77 `lpassa $lr18 $t` → L79 `$mt[0,4,0,4]`. Measured:
`A racy memory read at T is detected at line 78` for every variant
(`$r8→$s28` + delete, + deleting L85, + deleting tail nops). Reordering the pack is
impossible (L79's `ilsl` needs `aluf = 8` from L78 and every later pack op is a
forwarding-chain link), and moving the T write earlier is impossible (L76, the last
canvas write, still needs the old T).

---

## 2. Summary table

| line | constant | deletion cost (fbcheck) | verdict | blocking mechanism |
|---|---|---|---|---|
| 14 | `T=2^23` (0x4b000000) | 4096 | removable only with the mask rewrite | T + omr15 pattern + float seed; L2 slot needed for 56 |
| 18 | 32 | **3 long words (22 bytes)** | not without a new slot | no ALU slot ≤ L23; MAU cannot make int 32 |
| 19 | 408 | 50 | not removed | same, plus no cheap MAU factorisation |
| 20 | 4672 | 581 | not removed | same |
| 26 | 63.0 | 4089 | not removed | 3-op MAU chain + aluf role; only 2 hosts |
| 30 | 1/71 | 532 | not removed | no reciprocal op; per-PE dynamic mask |
| 31 | 1/79 | 3512 | not removed | no reciprocal op |
| 49 | 0.001 | (racy T) | not removed | mandatory T spacer; no host between L48 and L52 |
| 56 | 2^23+117 (dead) | (racy GRF1) | not removed | mandatory GRF1 spacer |
| 78 | 8 | (racy T) | not removed | mandatory T spacer |

Official gate results for the candidates kept:

```
python3 tools/fbverify.py base.vsm          -> ACCEPTED!! score=93 j=91 m=2 bytes=3054
python3 tools/fbverify.py del_18.vsm        -> 32744 correct, 22 mismatch  (92 words)
python3 tools/fbverify.py cand_c3_maskL56   -> RESULT MISMATCH pos=32765
python3 tools/fbverify.py cand_c4_32atL2    -> RESULT MISMATCH pos=32765
```

## 3. Reusable findings for a redesign

1. `omr15` (the canvas write mask) is `5 = 0b0101` for every cycle and every PE, and it
   is **regenerable for free** at any ALU-only line whose previous step is a `u`-option
   imm (measured at L56). So the `hvpassa` that produces it is movable; a fixed mask
   literal is *not* equivalent (F7).
2. Any ALU-only line with a free MAU slot can carry one extra MAU expression at zero
   word cost, subject to: same-precision only (`dmread` is double, `hvpassa` is half),
   no GRF0/GRF1 out-conflict with the ALU, no LM0 access on the same line, and
   same-address GRF reads if the ALU also reads that bank.
3. `T`-relative LM0 addresses only use `T mod 4096`, so the `0x4b0000XX` canvas
   constants are really the integers 48/70/105/66/117/122/10; they could be written as
   plain integer imms (`imm i"117" $t`) — same word cost, but it removes the 2^23
   float encoding trick from any redesign.
4. `$r16 = 56` is **not** dead (it is the peid bit mask used by L7); the only genuinely
   dead constant writes are `$r68` (L56) and the dead halves of the prologue table.

---

## 4. Addenda measured after the first write-up

* **`0.001 = 0.1 * 0.01` is exact in float32** (`fvmul` of the two imm values gives
  `0x3A83126F`, identical to `imm f"0.001"`), so mechanism 3 (folding a constant into a
  co-issued MAU op) is real; only L49's missing host slot blocks it (`probe` output
  reproduced in §1). The two sources must be in different banks (`$s76 $r74`): two GRF1
  reads in one MAU expression is an `in_grf1`/`in_grf1` conflict.
* **The transfer tail is provably locked** (tried `cand_f1`, `cand_f2`):
  - moving `lpassa $lr18 $t` onto L76 (`fvpassa ... $mt42v; lpassa $lr18 $t`) →
    `GRF0 is read at two different addresses` ($r67 in the MAU, $lr18 in the ALU);
  - deleting L78 with the pack reading `$s28` instead of `$r8` → `racy memory read at T`;
  - L76→L79 needs 3 steps (LM0 port) and L77→L79 needs 2 steps (T). Since L76 is the last
    canvas write and L79 the first pack read, **L77 and L78 are both mandatory steps**,
    and the only values that can occupy them are an instruction that does not touch
    LM0/GRF (L78's imm does exactly that). Same argument for L49 (L48 writes T, L50 reads
    T through `$mt[43,41,0,0]`) and L56 (L55 writes `$ls20v`, L57 reads it).
* The exhaustive `host18.py` sweep is the definitive statement for L18: **no line at or
  before L23 can carry `imm i"32" $r25`**, and lines after L23 are too late. Any future
  attempt at del_18 needs a redesign that either removes the region-0 threshold
  (unified field-width formula) or moves the `$r24v` consumer itself.
