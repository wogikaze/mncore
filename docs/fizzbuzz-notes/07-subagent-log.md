# 07 — subagent log: structural shortening of FizzBuzz (round 4)

Baseline: `problems/challenge/20.fizzbuzz/main.vsm` = 93 lines, ACCEPTED
(`ACCEPTED!! score=93 j=91 m=2 bytes=3054`), re-verified before/after this session.
No candidate below 93 could be verified; best verified score remains **93**.

All candidates are in `attempts/`. Every candidate was run through
`assemble3 --instruction-mode flat` first, then `fastsim.py` (native sim, DRAM
word-for-word), and winners would go to `problems/run_problem.py`.

## Machine facts nailed down in this session (beyond 03/04/06 notes)

1. **`$mt[...]` = LM0 with T-indirect addressing**, and it *reads* the T register.
   T has 4 entries (one per cycle), each a 64-bit value (`d get $t` shows
   0x000..0x003). The address is `(T[cycle] + flat_addr) mod 4096` in **word**
   units. A MAU/fvpassa accesses 2 words (1 longword) per cycle and the `v`
   suffix advances 2 words/cycle; ALU word access advances 1 word/cycle.
   Runtime T addresses may be odd (the assembler cannot check them); a
   **static** absolute LM0 operand with `v` must be longword-aligned (multiple
   of 2) — this kills the "use `$lm<odd>` instead of `$mt<odd>`" rewrite.
2. **T after the canvas prologue is NOT PE-independent.**
   After line 59 (`ladd $ls4 $ls4 $t $ls6`) T is 2*ls4, which depends on the
   MAB/PE: measured 4 (m0), 6 (m1), 8 (m3), 10 (m5), and it then grows by the
   per-PE item lengths (4/8…): m3: 8→12→20→24→32; m1p1: 6→9→15→18→24. So the
   canvas chunk positions are genuinely data-dependent; they cannot be replaced
   by absolute constants. (Earlier note "T after 77 = lr18" is still right;
   T *before* 77 is per-PE.)
3. **Canvas layout**: LM0 words, one ASCII char per 32-bit word. The PE's final
   window is `LM0[T_final .. T_final+7]` where `T_final = lr18` (line 42/77,
   written to word 19 by `fftoi $mauf $r19` at line 37 — r19 is *not* dead, it
   is the low word of longword 18!). Region A (cycles 0/1, T_hi) and region B
   (cycles 2/3, T_lo) are written interleaved by lines 57/58 from s20..s27.
4. MAU single-precision ops process **2 words/cycle** (1 longword), can write
   multiple destinations, and a masked op can restrict which cycles commit
   (that is how `fvpassa/$imr15 $r63v $mt8v` writes exactly "Fizz" over 2 cycles).
5. **A MAU instruction cannot read two different GRF0 addresses**
   (`fvmul $lr0 $lr8 $lr16` → `Instruction field conflict ... in_grf0`), and
   cannot read GRF0+GRF1? (GRF0+GRF1 is fine: `fvmul $lr76 $ls0 $lr74` OK).
   Same address twice is fine. So "0.001 = 0.01*0.1" with both operands in GRF0
   is impossible without a copy.
6. **`imm` + LM0 in the same line is forbidden** (known), but `imm` writing
   **GRF1 while another command on the line reads GRF1 is accepted**
   (`imm ... $s63` next to `fvmul $lr72v $ls48` assembles).
7. **LM0 write→read needs 2 empty steps** (PortConflictError otherwise);
   T write→read needs 1 empty step (DataRaceError otherwise).
   Consequence: lines 60 (fvpassa $lm0v) and 78 (imm 8) are *load-bearing
   fillers*, not removable.

## Concrete structural attempts and why each failed

### A. Merge lines 57+58 (two `ipassa` into one) — assembles, 3329 mismatches
One ALU `ipassa` can write at most 4 words (1 word/cycle); the two lines write
8 words (two digit windows A/B). Merging always loses one half; the deletion
test shows every half is needed by some PEs. File: `attempts/merge57-58.vsm`.

### B. Absolute-address canvas (drop T ladds + 4 nops) — assembler rejects
`$lm16v` etc. must be even-aligned; the needed positions 25/43/… are odd.
Flat `$lm[25,26,27,28]` is rejected for the same reason. Files:
`attempts/abs-canvas.vsm`, `attempts/abs-canvas2.vsm`.

### C. Constant-T canvas (keep T=8 after line 59, fold offsets, delete 4 nops)
Assembles (89 lines) but 2660 mismatches: T after 59 = 2*ls4 is MAB-dependent
(4/6/8/10…), so the offsets are not constant. Canvas *content* was verified
identical for MAB3 but not for other MABs. File: `attempts/tconst-canvas.vsm`.

### D. Move `lpassa $lr18 $t` into line 76 and delete line 77
- Direct merge conflicts: `fvpassa $r67v` (GRF0) + `lpassa $lr18` (GRF0) =
  two GRF0 reads at different addresses. `attempts/move-t-set.vsm`.
- Fix: move the *Fizz* constant to GRF1 (`imm ... $s63` at line 52, all Fizz
  canvas sources become `$s63v`) and swap the last two writes so the final
  line writes Fizz from GRF1. This assembles through the merge
  (`attempts/fizz-grf1.vsm`) but then **LM0 port conflict at the pack**: with
  line 77 deleted, the last canvas write (line 76) is only 1 empty step before
  the pack's first `$mt` read; the port needs 2. Keeping any filler line makes
  the deletion a wash.
- Buzz-to-GRF1 variant blocked: `imm ... $s67` cannot live on line 55 (it also
  writes `$ls20v` → two GRF1 writes) nor on lines 40/41/50/60 (LM0 access +
  imm forbidden, or GRF1 write). `attempts/buzz-grf1.vsm`.

### E. Generate 0.001 by MAU (`fvmul 0.01*0.1`) and delete line 49
Floating point check: `0.01f*0.1f == 0.001f` exactly (0x3a83126f), so the value
is right. Blocked because the only ALU-free line before the first use (line 52)
is line 51 (`fftoi $lmt... $t`), and adding a GRF0+GRF0 MAU read there is
rejected (`in_grf0` conflict). Line 50 has LM0 access (imm forbidden).
File: `attempts/gen-0.001.vsm`.

### F. Move `imm f"63" $s3` (line 26) into a dead imm slot
The apparent dead imms `i"13" $s29` / `i"66" $s30` (lines 22/23) are **not
dead**: `$s28v`/longword reads use the adjacent word, so s29 is the low word of
longword 28. Also line 26's imm output is consumed by line 27 through `$aluf`
(63.0), so it must stay adjacent to line 27; and `$ls3` is not longword-aligned.
File: `attempts/move-63.vsm`.

### G. Full single-line deletion sweep re-run (93 candidates)
Reproduced the prior result: no deletion survives. Deletions that assemble
give mismatches (e.g. L18→3, L19→50, L20→581, L21/27/36/43/52→runtime error,
L60/63/67/71/74/78/85…→DataRace/PortConflict). `del_test.py`.

## Useful leads for a future round

- The pack chain (lines 79–84) needs exactly 6 ALU (3 shifts + 3 ORs) for the
  two 32-bit halves because the canvas is char-per-word. Any real reduction
  requires storing ≥2 chars per word in LM0, which the MAU cannot do directly
  (it writes 2 words/cycle, no bit packing).
- The biggest realistic win would be generating the 6 character-constant imms
  (lines 28,36,52,54,55,56) with 1–2 `fvfma` instructions that compute
  `t + code` per lane. Factorizations exist that respect the "one operand per
  register file" rule for 4 of the 6 constants (70=14×5, 105=15×7, 66=6×11,
  10=2×5; 117=13×9; 122 needs 8×15+2), using GRF1 1..16 at longwords
  102..132, LM1 1..8 at 102..116, LM0 {8,11,13,14} at 48/50/52/54, and `$llt`
  (=2^23) as the addend. Blocked only by where such an op can be placed: the
  ALU-free lines before line 59 are 21, 40, 41, 50 (all LM0 or GRF1-writing)
  and 60; an `imm` cannot share a line with LM0, and two writes to the same
  register file on one line are rejected. If the scheduler allowed one such op
  on line 26/30/31/35/53 (each has a free MAU slot) the 6 imm lines could
  collapse to ~2, which is the shortest path to ~89–90.

## Addendum: the two "dead" imms s29/s30 are alive

`imm i"13" $s29` (line 22) and `imm i"66" $s30` (line 23) looked dead from a
plain register grep, but each is the **LSB word of a longword** consumed by a
strided read (`$s28v`, …). Moving the same value to another GRF1 address:
- `imm i"13" $s100` → 47 DRAM words differ,
- `imm i"66" $s100` → 533 DRAM words differ.
So neither slot is free; they must keep their exact (address, value).
This also means the "move 63.0 onto a free imm slot" plan (which would have
been a clean −1) is impossible: L22/L23 can only host a *GRF1* imm (their MAU
op writes GRF0), and both GRF1 slots are load-bearing.

Best related candidate: `attempts/move-63-v2.vsm` / `-v3.vsm` (92 lines,
47 / 577 mismatches) — assembled cleanly, and proved that
`imm f"63" $ls100` + `fvadd $ls100 $r116 …` at line 27 is a valid replacement
for the aluf-carried 63.0 (source can be an *aligned* GRF1 longword).
Remaining blocker: no line before 27 can host the 63.0 imm.

## Parent follow-up note (round 6/7)

Subagent finished; no score < 93. Baseline intact (`main.vsm`, 93, re-ACCEPTED).

Next concrete attempt (not yet run): merge the last two canvas writes
`fvpassa/$imr15 $s63v $mt38v` and `fvpassa/$imr15 $r67v $mt42v` into one flat
vector write, by moving `'B'` (r67) and `'z'` (r69) into GRF1 slots (s67/s69).
Payoff: -1 line (92) and it also restores the 2-step LM0 port gap that
`fizz-grf1.vsm` misses.

## Parent round-7 experiments (constant generation)

- `63.0` via `fvmul $ln114 $ls118 $s3` (7.0*9.0, LM1+GRF1 -> GRF1):
  host line 20 assembles, but GRF1 118 (9.0) is only written at L21-23,
  so the value is 0 -> 4089/4096 words wrong (`attempts/move-63-v3.vsm`, 92 lines).
  Hosts after L23 are all rejected: L25/L35/L42 read or write GRF1,
  L30/L31/L49 are GRF1-writing imms (out_grf1 conflict), L37 conflicts on in_grf1.
- `'u'` (117) via `fvfma $ls118 $ls126 $llt $r68` (9*13): both factors GRF1 ->
  `in_grf1` twice, rejected. 13 is in LM0 (lm52, written at L38), but every
  ALU-only host between L38 and the T overwrite (L43) touches GRF1.
- Confirmed rule: one operand per register file per MAU instruction/host line.
