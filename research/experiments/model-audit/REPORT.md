# `$aluf` as a source, OMR/`$imr1` write masks, and the `4.mul7` datapath

**Status:** delivered. Every claim below is backed by a probe under
`research/experiments/model-audit/probes/` run against the official assembler +
emulator (`judge/judge-py/mncore2_emuenv/`), or by a Lean `#eval` under
`research/experiments/model-audit/lean/`. All probes run in
`--instruction-mode flat`, the mode the judge uses for device `noto`.

**Bottom line.**

1. `$aluf` is the ALU's **2-long-word output bus from the previous step**, one
   value per cycle. A consumer with long-word access reads its **high long
   word**. It is readable in the step after an ALU-producing step; `nop`,
   `noforward`, and control (mask) lines do **not** update it; a step with no
   ALU producer makes it *invalid* (`IALU is disabled`), and `noforward`
   suppresses the update even when an ALU actually executed. The ALU and MAU of
   one step both read the **pre-step** value. ProofsLean models all of this
   correctly.
2. The OMR entry is 16 bits = 4 cycles x 4 flags. For a long-word mask, the
   four bits are the four half-words of the **high long word**, bit 0 = LSB
   half-word. Write mask: flag 1 writes, 0 skips. Zero flush: flag 1 keeps, 0
   zeros. `max` sets the flag when its **first** input `x` is selected (ties
   select `x`). A flag written by an ALU in step *t* is visible **from step
   t+1**, never to a write in step *t*.
3. ProofsLean and the emulator disagree in **one semantic place**: the Lean
   executor makes an OMR entry written by the ALU in a line visible to the
   float-MAU write mask of the **same** line (`WholeMachineStep.lean`,
   `executeIntegerProducerLineAtPECore` -> `executeParsedFloatMAUsAtPE`), and
   `prepareParsedIntegerMaskInputThenMemoryALUWritesWithForwarding`
   (`ParsedIntegerStep.lean:4393`) does the same for one destination order of a
   single ALU instruction. The emulator uses the pre-step entry. The
   disagreement does not change `4.mul7` because every `smax` in that answer
   produces the same mask (5).
4. The published `4.mul7` answer **is correct**, and its datapath is
   `smax`-half-word-embed + OMR write mask + `fvfma`, not `f(memory word)*7`.
   `SingleFMA` reproduces the emulator's FMA values exactly on the answer's
   (normal) operands, and its FTZ matches the emulator's FTZ. The premise of
   `Mul7FloatGap` ("the answer cannot be stated against `SingleFMA`") is a
   non-sequitur, and adding subnormal support would be *wrong* — the emulator is
   flush-to-zero.
5. `3.a-plus-b`, `2.plus-two`, `12.convert-endian` are **unaffected** by the
   disagreement. `12.convert-endian` does use `$aluf`, but only in the
   correctly-modelled "previous step" role and without OMR.

A separate spec defect was found while checking the lower bound:
`4.mul7`'s shipped testcase puts `X` in the **odd** 32-bit word of each 64-bit
element, while `ProofsLean/Mul7Spec.lean` puts it in the **even** word and
requires the even word to become `7*X`. The counting argument is parity-
symmetric, but the formal spec is the byte-swapped relation, not the judge's
(§4.4, §5.3).

---

## 1. Method and harness

* Emulator: `judge/judge-py/mncore2_emuenv/gpfn3_package_main`
* Assembler: `judge/judge-py/mncore2_emuenv/assemble3 --instruction-mode flat`
* Judge: `python3 judge/judge-py/judge.py <testcase> <answer>`; the judge
  concatenates the **raw** testcase prefix (`d set`), the **assembled** main
  program, and the **raw** testcase suffix (`d get`). It also sets
  `OMP_THREAD_LIMIT=1`.
* Probe runner: `research/experiments/model-audit/probe.sh` (flat by default,
  `OMP_THREAD_LIMIT=1`). Probe log: `logs/probes.log`.

Two harness facts that matter for reproduction:

* **Use flat mode.** The judge assembles the solution with
  `--instruction-mode flat`. In the default (non-flat) mode the packing of a
  multi-instruction line can change, and a parallel ALU+MAU line stops reading
  the same step alignment. Example: the three-line convert-endian answer gives
  `0x0000000000000000` in default mode and `0xB33DEACB66DCE15F` (correct) in
  flat mode. Every probe cited here is flat.
* **Do not blindly assemble `d set` with a timing-sensitive program.** In flat
  mode `assemble3` emits the `d set`/`d get` lines verbatim and leaves the
  `j` lines unchanged, so the usual "everything in one .vsm" probe is fine, but
  a probe that re-assembles an already-assembled file is not. `probe.sh` always
  assembles a source `.vsm`.

Lean side: `lake env lean` from `proofs_lean/`, importing
`ProofsLean.SingleFMA`, `ProofsLean.IntegerALU`, `ProofsLean.Masks`,
`ProofsLean.ConvertEndian`, `ProofsLean.WholeMachineStep`. Transcripts in
`lean/*.lean` (run with `lake env lean <file>`).

---

## 2. `$aluf` as a source operand

### 2.1 The rule

`$aluf` is a read-only forwarding operand (SDM 3.6.1.16; parser:
`ProofsLean/PEParser.lean:71` -> `.forward .aluf`). It carries the ALU's
**2-long-word output bus** for each of the four cycles. Concretely:

1. **Producer.** Any ALU instruction updates it: `imm`, `zero`, and every
   `*max`, `*add`, `passa`, ... op, including when the only destination is
   `$nowrite`. Its high long word is the computed 64-bit result (two 32-bit
   words); its low long word is the first input's low long word for non-2-long-
   word ops (0 when the first source is a long-word access), and the copied
   value for `passa`/`imm`/`zero`.
2. **When readable.** In step *t+1*, cycle *i* reads what the ALU produced in
   step *t*, cycle *i*. It is **not** readable earlier: an ALU and a MAU in the
   same step both see the pre-step value; the new value is committed at the end
   of the step.
3. **What a consumer reads.** A long-word consumer (ALU lane, `fvfma` source)
   reads the **high** long word (two words). The low long word is not used by
   single-precision/long-word consumers; a 2-long-word consumer
   (`$ll...`) sees both.
4. **Lifecycle.**
   * `nop`: value retained.
   * `noforward` (alone or beside an ALU op): value retained; an ALU in the
     same step still writes its memory destination but does **not** update
     `$aluf`.
   * A control line (`mask ...`, `d get`, ...) is not a step: value retained.
   * A step with **no ALU producer** (e.g. a line containing only a MAU op)
     makes the register *invalid*: the next read aborts with
     `Accessing to IALU forwarding register failed. The error on the previous
     step is: IALU is disabled`. There is no "stale value" fallback.
   * Reading `$aluf` is a source-only role; the assembler rejects a negated or
     extended ALU operand (`signa couldn't specified ALU`), so ALU source
     negation is not a legal-program case.

### 2.2 Probe evidence

| probe | program (after LM0 setup) | result |
|---|---|---|
| `p11_line2_aluf` | `imm i"1088421888" $ls64v`<br>`smax $lm0v $aluf $omr1; fvfma -$aluf $aluf $aluf $lr72v`<br>`lpassa $aluf $lr0v` | `lr0 = 0x40E0000540E00005`; the ALU that produced it is the `smax` (`max([0,5],[0x40E0,0]) = [0x40E0,5]`), read in the **next** step |
| `p12_line2_mauf` | same line 2, then `lpassa $mauf $lr16v` | `lr16 = 0xC2280000C2280000 = -42.0f`; the `fvfma(-7*7+7)` used the **pre-step** `$aluf` = the `imm` value 7.0f |
| `p7_smax_full` | `imm 7.0; smax $lm0v $aluf $nowrite; lpassa $aluf $llr0v` | aluf = `{high=0x40E0000540E00005, low=0}`; low long word is 0 for a long-word source |
| `g6_alu_aluf_lw` | `ipassa $llm0v $nowrite` (source high `0x0001000200030004`, low `0x0005000600070008`); `smax $ls0v $aluf $lr0v`; `lpassa $aluf $lr16v` | result `0x0001000200030004`: the ALU source reads the **high** long word |
| `g1_aluf_mauonly` | `imm i"7" $ls0v` / `fvpassa $lr0v $ln0v` / `lpassa $aluf $lr8v` | runtime abort: `IALU is disabled` (rc 134) |
| `g2_aluf_nop` | `imm i"7" $ls0v` / `nop` / `lpassa $aluf $lr8v` | `lr8 = 0x0000000700000007` (retained) |
| `g3_aluf_noforward` | `imm i"7" $ls0v` / `noforward` / `lpassa $aluf $lr8v` | `lr8 = 0x0000000700000007` (retained) |
| `g4_aluf_maskline` | `imm i"7" $ls0v` / `mask 1` / `lpassa $aluf $lr8v` | `lr8 = 0x0000000700000007` (control lines do not disturb it) |
| `g5_noforward_alu` | `imm i"7" $ls0v` / `nop` / `noforward; iadd $lm0v $ls0v $lr8v` / `lpassa $aluf $lr16v` | `lr8 = 0x1800000029...` (iadd ran: 0x11+7, 0x22+7, ...), but `lr16 = 0x0000000700000007`: the iadd result was **not** forwarded |

### 2.3 What this means for the prior blocking note

`research/experiments/mul7-proof/BLOCKED.md` says the `$aluf` reading of the
answer is "not what the repository's parser assumes". That is **not** the case:
the parser and the model's forwarding lifecycle match the emulator. The
input-independent `0x4241999A4241999A` observed there is not reproducible from
the documented `p1.vsm` (`p13_prior_p1`: with input words `0x3F800000`,
`0x40000000`, `5`, the results are `0x42440000`, `0x42440000`, `0x42440004`, and
with `1000` `0x4244036B`). The value depends on the accumulator: with
`z = 0` the FMA is `7 * 0x40E0XXXX = 49 + 7X*2^-21` and rounds on the
**49-exponent grid** (ulp `2^-18`), so the low half-word is `round(7X/8)`; with
`z = -42` (the answer) the result is `7 + 7X*2^-21` on the **7-exponent grid**
(ulp `2^-21`), so the low 16 bits are exactly `7X` for `X <= 1000`. The
`0x4241999A` figure is not reproducible from the documented probe and is
accumulator-dependent; it is not evidence about operand roles.

---

## 3. OMR / `$imr1` write-mask rule

### 3.1 The rule

* **Entries.** 32 entries (SDM 3.6.2, `ProofsLean/Masks.lean`):
  * entry 0: all ones;
  * entries 1..15: variable, one 16-bit entry = 4 cycles x 4 flags; written by
    ALU/MAU mask-flag generation (`$omrN` destination);
  * entries 16..31: fixed pattern from the low 4 bits, cycle 0 = MSB of the
    4-bit value, all words equal.
  * `$imrN` selects entry `N` (the answer uses `$imr1` = variable entry 1).
* **Write mask vs zero flush.** `/...` on a **destination** operand is a write
  mask: flag 1 writes the corresponding unit, flag 0 leaves the old value
  (`$ln0v/$imr1`). `/...` on the **opcode** (`fvfma/$imr1 ...`) is a zero flush:
  flag 1 keeps, flag 0 zeroes the value before the write.
* **Word length.** Default = long word. The 4 flags are the 4 half-words of the
  **high** long word of the cycle's 2-long-word datapath; bit 0 = **LSB**
  half-word. The low long word is unaffected (all-ones enable). With `ll` the 4
  flags are the 4 words of the 2-long-word datapath; bit 0 = LSB word, bit 3 =
  MSB word. Destination and mask word lengths must match, otherwise the
  assembler errors (`conflict of word length between location and mask`).
* **Cycle indexing.** The 4 flags of an entry apply per cycle: cycle *c* uses
  the 4-bit group of cycle *c*. A `smax` writes one 4-bit group per cycle from
  the 4 half-word results of that cycle.
* **Visibility.** A written entry is usable **from the next step** (SDM:
  「書き込んだマスクフラグは直後のステップから利用可能」). A write in the same
  step uses the pre-step entry, for both write masks and zero flushes, and for
  both an ALU+MAU line and a single ALU instruction with an OMR destination.
* **Flag generation for `max`/`min`.** For `max`, flag = 1 iff the first input
  `x` is selected, including `x = y` (tie selects `x`). `smax` is the
  **half-word** (16-bit) signed max (`s` = 半), 4 lanes per long word; `imax`
  would be 32-bit.
* A single-line mask on one destination cancels the multiline `mask` directive
  for that step; the answer uses only single-line masks, so the directive path
  is not exercised here.

### 3.2 Probe evidence

| probe | program | result |
|---|---|---|
| `m11_tie` | LM0 = all 0; `smax $lm0v $ls64v $omr1` (y = 7.0f pattern) | `Mask{5}` per cycle: low half `0 vs 0` ties in favour of `x` -> flag 1; high half `0 vs 0x40E0` -> flag 0 |
| `b3b_omr` | LM0 words 1..8; `smax $lm0v $ls64v $omr1` | `Mask{5}` for every cycle |
| `m1_bits` | LM0 cycle1 half-words `[0, 0, 0x7FFF, 0x8000]` | `Mask{6}`; confirms bit 0 = LSB half-word (the `[0,1,1,0]` flags) |
| `m10_cyclemask` | four different LM0 long words -> flags 5,10,5,10; `d get $omr1`; `fvpassa $lr0v $ln0v/$imr1` | OMR `5,10,5,10`; LM1 long words `0x0000567800005678`, `0x1234000012340000`, `0x0000567800005678`, `0x1234000012340000`: bit 1 positions write, cycle-indexed |
| `m4_mask5` / `m5_mask10` | entry = 5 (resp. 10); `fvpassa $lr0v $ln0v/$imr1` with `0x1234567812345678` | `0x0000567800005678` (mask 5: LSB half-words) / `0x1234000012340000` (mask 10: the other half-words) |
| `m8_llalu` | `smax` produces 5; `lpassa $llr0v $lln0v/$llimr1` | words 1 and 3 written (`bit2`, `bit0`): `ll` = 4 words, bit 0 = LSB word |
| `m13_fixed_entry` | `fvpassa $lr0v $ln0v/$imr17` | only cycle 3 writes (words 6,7); fixed entry 17 = `0b0001`, cycle 0 = bit 3 |
| `m6_zeroflush` | step 2 entry = 5; step 3 `smax B $omr1; fvpassa/$imr1 $lr0v $ln0v` with entry 10 written in the same step | LM1 `0x0000567800005678` = **old** mask 5 kept; `d get $omr1` = 10 |
| `m12_alu_omr_mem` / `m12b_omr_first` | `smax $lm0v $ls64v $lr8v/$imr1 $omr1` (both destination orders), with entry 1 initially 0 | `lr8` stays 0: the memory write used the **old** entry 0; the instruction's own OMR write (5/10) is not visible to it |

The key timing probe is `m2_timing`:

```vsm
d set $lm0n0c0b0m0p0 8 <A: words 0..7 = 1,2,...; B: words 8..15 = 0x7FFF8000...>
d set $lr0n0c0b0m0p0 4 <0x1234567812345678 x4>
imm i"1088421888" $ls64v
smax $lm0v $aluf $omr1                                  # step 2: entry 1 = 5
smax $lm8v $ls64v $omr1; fvpassa $lr0v $ln0v/$imr1      # step 3: entry 1 = 10; write
fvpassa $lr0v $ln8v/$imr1                                # step 4: write with entry 10
d get $ln0n0c0b0m0p0 8
d get $omr1n0c0b0m0p0 1
```

Observed (flat): `ln0..ln7 = 0x0000567800005678` (mask **5**, the pre-step
entry) even though `d get $omr1` shows `Mask{10}` afterwards; `ln8..ln15 =
0x1234000012340000` (mask 10, now the pre-step entry for step 4).

---

## 4. Where ProofsLean and the emulator disagree

### 4.1 D1 — same-step OMR visibility (the only semantic disagreement found)

**Module and definitions.**
`ProofsLean/WholeMachineStep.lean`
`executeIntegerProducerLineAtPECore` (line 7160) runs the integer ALU stage
first; `commitParsedMaskedWrites` (`ProofsLean/ParsedIntegerStep.lean:5202`)
commits the ALU's `$omr` destination into `registers.maskRegisters`; the
executor then passes those **post-ALU** files to the float MAU stage:

```lean
match executeParsedFloatMAUsAtPE (state.peRegisters pe) registers oldSlots ...
```

`executeParsedFloatMAUsAtPE` (line 1174) / `executeParsedFloatMAUCyclesAtPE`
(line 1149) resolve the MAU destination's write mask from
`files.maskRegisters` (lines 1162 and 1166), i.e. the **new** entry.

Second manifestation, in `ProofsLean/ParsedIntegerStep.lean`,
`prepareParsedIntegerMaskInputThenMemoryALUWritesWithForwarding` (line 4393):
when the destinations are `[$omr, $mem/$imr]`, the memory write's selection is
resolved from

```lean
let nextMaskRegisters := Masks.writeRegister files.maskRegisters ...
... resolveMemoryWriteSelection? ... nextMaskRegisters ...
```

i.e. the same instruction's OMR write is visible to its own second destination.
The sibling `prepareParsedIntegerMaskMemoryThenInputALUWritesWithForwarding`
(the `[$mem, $omr]` order) uses the pre-step `files.maskRegisters` — so the
Lean model's behaviour depends on destination order, which the emulator's does
not.

**Emulator result.** `m2_timing`: step 3 writes
`0x0000567800005678` = the **old** mask 5; the entry is observed as 10 only
afterwards. `m12`/`m12b`: a single ALU instruction that writes `$omr1` and a
masked memory destination uses the **old** entry (0 here) in both destination
orders.

**Lean result.** `lean/ModelSupport.lean`:
`Masks.readEntry` of the entry after the ALU write = `5` on the old file,
`10` on the post-ALU file; `Masks.writeBus .long 5` =
`0x0000567800005678`, `.long 10` = `0x1234000012340000`. Since the executor
feeds the post-ALU file to the MAU stage, the Lean transition for `m2_timing`
step 3 is `0x1234000012340000` (new 10), not the emulator's
`0x0000567800005678`.

**Impact.** None on `4.mul7`: every `smax` in the answer yields mask 5 for all
admissible inputs (`x` low half `>= 0 = y`, high half `0 < 0x40E0`), so the
old and new entries coincide on every line. It *is* a real general-semantics
bug and should be fixed before using the model for programs whose OMR entry
changes within a line. Note that the model's own comment
(`WholeMachineStep.lean:163-166`) states the correct pre-issue rule for the
L1-to-PE path ("its mask and flush selection therefore read the pre-issue OMR
state"); the MAU path contradicts that stated intent.

### 4.2 What agrees (checked, not assumed)

| item | emulator | ProofsLean | evidence |
|---|---|---|---|
| `aluf` = previous step's ALU bus, per cycle | yes | `Forwarding.Slots`/`advance`, `readWithForwarding` | `p11`, `p12`, convert-endian |
| `aluf` poisoning when the previous step has no ALU producer | runtime abort `IALU is disabled` | `.alu => .poison`, read = `.failure` (`Forwarding.advanceReference`, `ParsedIntegerInput.readWithForwarding`) | `g1` |
| `nop` / `noforward` / control line retain `aluf` | yes | `.nop => old`, `.issue true => old` | `g2`, `g3`, `g4` |
| `noforward` suppresses a same-line ALU update | yes (memory write still happens) | `updateSupportedPELineForwarding ... noForward = .ok old` | `g5` |
| ALU/MAU in one step read the pre-step `aluf`/`mauf` | yes | reads use `oldSlots`, writes advance at end | `p12`, convert-endian |
| consumer reads the high long word | yes | `IntegerALU.lane ... x.high`, `prepareSingleMAUSource ... bus.high` | `g6` |
| ALU low long word = first input's low LW (0 for long-word source) | yes | `evaluateBus` `low := x.low` / `0` when reduced | `p6`, `p7`, `p14` |
| MAU output low long word = 0 | yes | `executeParsedFloatMAUCycleAtPE` returns `⟨output, 0⟩` | `m7b` |
| mask bit 0 = LSB half-word of high LW; 1 = write | yes | `Masks.halfMask`, `selectedWordMask` | `m4`, `m5`, `m10` |
| `ll` mask = 4 words, bit 0 = LSB word | yes | `Masks.doubleMask` | `m8` |
| fixed entries 16..31, cycle 0 = MSB | yes | `Masks.readEntry` | `m13` |
| `max` flag = x selected incl. tie; half precision = 16-bit | yes | `IntegerALU.evaluateLane .maximum`, `.half` | `m11`, `b3b`, `m1` |
| `imm` produces the literal four times (xxxx) | yes | `evaluateParsedExecutionRequest .immediate` -> `⟨word, word⟩` | `p11`, answer probes |
| FTZ on subnormal input and output | yes (see §4.3) | `decode` exponent 0 -> zero; `roundPack` biased <= 0 -> 0 | `f1`-`f4` |

### 4.3 `Mul7FloatGap` — the theorem is true, the inference is not

`ProofsLean/Mul7FloatGap.lean` proves
`singleFma (BitVec.ofNat 32 m) seven 0 = 0` for `m < 2^23`. That theorem is
true and its two ingredients are both real:

* `SingleFMA.decode` (line 23; the exponent-zero return is line 28) flushes exponent-zero words to `.zero`;
* `roundPack` (line 50) flushes outputs that would be subnormal
  (`biased <= 0 -> 0`).

The emulator does the same on the tested MAU ops, **independently of any
`$aluf`/OMR effect** — these probes contain no ALU/OMR at all:

| probe | computation (no aluf, no mask) | emulator | `SingleFMA` |
|---|---|---|---|
| `f1_ftz` | `fvmul` of subnormal `0x00000005` (= 5*2^-149) by 7.0f | `0` | `0` |
| `f2_ftz` | `fvfma 0x00000005 * 7.0f + 0` | `0` | `0` |
| `f3_sub_norm` | subnormal `0x00400000` (2^-127) * 2.0 -> exact 2^-126 (normal) | `0` (input flushed) | `0` |
| `f4_underflow` | normal `2^-100 * 2^-30` -> subnormal `2^-130` | `0` (output flushed) | `0` |

So the emulator is **flush-to-zero** on these ops, and `SingleFMA` is faithful
to it. The invalid step in `Mul7FloatGap` is the claim that this prevents the
published answer from being stated: the answer **never multiplies an admissible
memory word as a float**. Its `smax` first packs `X` into the low 16 bits of a
*normal* 7.0f bit pattern, and the subsequent FMA has three normal operands:

```
smax_half([0,X], [0x40E0,0]) = [0x40E0,X] = 0x40E0XXXX  (float 7 + X*2^-21)
fvfma 0x40E0XXXX * 7.0f + (-42.0f) = 7 + 7X*2^-21        (exactly representable for X<=1000)
```

and `0x40E0XXXX` is a normal number (`exponent = 0x81`), not a subnormal.
`SingleFMA.singleFma 0x40E005E8 ...` style probes (§5.1) reproduce the
emulator bit-for-bit, including the `-42` intermediate. Adding subnormal
support (the `BLOCKED.md` "resolution 2") would move the model *away* from the
emulator and is the wrong fix.

### 4.4 `Mul7Spec` — even/odd word inversion (spec-fidelity defect, not an executor disagreement)

The shipped testcase stores each 64-bit element big-endian in its long word:

```
d set $lm0m0p0 1 000000000000020D      # values=[525]
DEBUG-LM0(n0c0b0m0p0,0): v:0x000000000000020D   # word 0 = 0, word 1 = 0x20D
```

and expects `3675 = 0xE5B` in the same word order:

```
DEBUG-LM1(n0c0b0m0p0,0): v:0x0000000000000E5B   # word 0 = 0, word 1 = 0xE5B
```

`ProofsLean/Mul7Spec.lean` instead installs the input at `mul7Low w = 2*w`
(the **even** word, `mul7InitialPERegisters`, line 125) and its postcondition
(`mul7Spec.post`, line 210) requires `lm1 (mul7Low w) = 7 * X` with
`lm1 (mul7High w) = 0` — i.e. the 64-bit value `7X * 2^32`, not `7X`. This is
the byte-swapped (little-endian word order) relation, while the judge's
relation is the numeric 64-bit value (big-endian word order).

The published answer satisfies both layouts (probes `a2_answer_5`,
`a3_even_layout`), so the answer is not in question. The lower-bound
*counting* argument is parity-symmetric: a 4-word schedule contains at most two
even and at most two odd words, so the bound transfers after restating the spec
with the odd word. But the current theorem is about a different relation and
cannot be cited for the official problem as-is. This is independent of D1.

### 4.5 Not established / not probed

* Mask-on-mask (`writeRegister ... newFlags selection = newFlags &&& selection`)
  is modelled but was not probed.
* Multiline `mask` directive cancellation, `ll` interactions with directives,
  and L1-to-PE mask timing were not probed; the answer uses neither.
* `-0` preservation: `SingleFMA.encode .zero _ = 0` loses the sign of zero.
  The answer only produces `+0`; no discrepancy was established.
* The `0x4241999A4241999A` figure in `BLOCKED.md` was not reproduced; see
  §2.3.

---

## 5. Verdict: `4.mul7`

### 5.1 The answer is correct under the true semantics

The datapath, line by line (all steps are one `;`-line = one issue step):

| step | instructions | effect |
|---|---|---|
| 1 | `imm i"1088421888" $ls64v` | GRF1[64..71] = `0x40E00000`; `aluf` = `0x40E00000` x4 (4 words) |
| 2 | `smax $lm0v $aluf $omr1`; `fvfma -$aluf $aluf $aluf $lr72v` | `aluf` := half-word max of `[0,X]` and `[0x40E0,0]` = `[0x40E0,X]` (per 32-bit word); OMR1 := flags `...0101` = 5; MAU computes `-7*7+7 = -42` -> `lr72`, `mauf` |
| 3 | `smax $lm8v $ls64v $omr1`; `fvfma $aluf $ls64v $mauf $ln0v/$imr1` | ALU: `[0x40E0,X]` for the next block, OMR1 := 5; MAU: `x = aluf(step 2) = 0x40E0XXXX`, `y = 7.0f`, `z = mauf(step 2) = -42` -> `7 + 7X*2^-21` = `0x40E(0x600000+7X)`; write mask 5 (pre-step entry = 5) writes only the LSB half-word `7X`, leaving the high half-word 0 |
| 4,5 | same shape with `$lm16v`, `$lm24v`, `z = lr72 = -42` | same |
| 6 | `fvfma $aluf $ls64v $lr72v $ln24v/$imr1` | same, using the step-5 `aluf` and the step-5 mask 5 |

Key value checks (flat probes):

| probe | input | emulator output |
|---|---|---|
| `a2_answer_5` | all 32 words = 5 | every LM1 long word `0x0000002300000023` (each 32-bit word 35) |
| `a4_answer_1000` | all 32 words = 1000 | every LM1 long word `0x1B5800001B58` (each 32-bit word 7000) |
| `a1_answer_asc` | words 1..32 | `7,14,...,224` (7X) |
| `x0` / `x1000` (isolated `z=0` variant) | 0 / 1000 | `0` / `0x36B = round(7000/8)` — shows why the answer needs `z=-42` |
| `p11_line2_aluf` | X=5 | `aluf` after step 2 = `0x40E0000540E00005` |
| `p12_line2_mauf` | X=5 | `mauf` after step 2 = `0xC2280000C2280000` (-42) |
| `p10_line3_mauf` | X=5 | `mauf` after step 3 = `0x40E0002340E00023` |
| `p8_line3` | X=5 | LM1 = `0x0000002300000023`; OMR1 = `Mask{5}` |
| `x1000_a` | X=1000 | `aluf` = `0x40E003E840E003E8`; mask 5 |
| `x1000_b` | X=1000 | `mauf` = `0x4244036B...` for `z=0`; with `z=-42` the answer gives `0x40E01B58` (low half `0x1B58 = 7000`) |

Official judge (shipped testcase, 1024 lanes):

```
$ python3 judge/judge-py/judge.py \
    problems/challenge/4.mul7/testcase.vsm \
    problems/challenge/4.mul7/answer.vsm
ACCEPTED!! score=6 j=6 m=0 bytes=310
```

The shipped testcase's lane 0 input `525` / output `3675` were also checked at
the word level (§4.4). The `7X` values fit in 16 bits because `X <= 1000` ->
`7X <= 7000 < 2^16`; the FMA result `7 + 7X*2^-21` is exactly representable
(mantissa `0x600000 + 7X`), and the mask writes exactly the low half-word.

### 5.2 Is `SingleFMA` usable after the fix?

* **For the float values: yes.** `SingleFMA` reproduces the answer's FMA values
  bit-for-bit on the tested operands (all boundaries and mid-range values),
  including the `-42` intermediate and the final `0x40E00023` / `0x40E01B58`;
  the exactness argument in §5.1 shows the result has a single rounding and is
  exactly representable for every admissible `X`:

  ```
  #eval singleFma 0xC0E00000 0x40E00000 0x40E00000 = 0xC2280000
  #eval singleFma 0x40E00005 0x40E00000 0xC2280000 = 0x40E00023
  #eval singleFma 0x40E003E8 0x40E00000 0xC2280000 = 0x40E01B58
  #eval singleFma 0x40E00001 0x40E00000 0xC2280000 = 0x40E00007
  ```

  The dropped-partial-product correction is inert here: the multiplier
  `0x40E00000` has `significand % 32 = 0`, so `dropped = 0`.
* **For a correctness proof of the answer: not by itself.** `SingleFMA` says
  nothing about `smax` (16-bit integer max), the OMR flag write, or the
  half-word write mask. Those are in `IntegerALU` (`evaluateBus`), `Masks`
  (`writeBus`/`halfMask`), and the parsed executor, and they agree with the
  emulator (modulo D1). A model-level correctness proof would compose
  `IntegerALU.evaluateBus .half (.maximum false)`, `Masks.writeBus .long 5`,
  and `SingleFMA.singleFma`.
* **The correct fix is not "add subnormals".** The emulator is FTZ (§4.3);
  adding subnormal support would break agreement. The fix is (i) keep FTZ,
  (ii) correct the same-line OMR visibility (D1), (iii) state the answer's
  datapath with the ALU/OMR pieces, and (iv) retract the `Mul7FloatGap` use as
  a "gap".

### 5.3 The lower bound

`ProofsLean/Mul7LowerBound.lean` proves the one-line refutation from
`Mul7OneLineLm1Footprint`, a statement about **addresses only** (at most 8 of
the 16 lane words per PE per line). It does **not** use `SingleFMA`, the mask
datapath, or the answer's values, so D1 and the FTZ question do not affect it.
The `.pe` residual (inverting the four-cycle destination schedule) is likewise
address-only; the mask timing is irrelevant to it.

Two caveats before citing it for the official problem:

1. **Spec parity (§4.4).** `mul7Spec` requires the even word of each lane to
   become `7X`; the judge requires the odd word. The counting argument is
   parity-symmetric, but the formal theorem must be restated for the judge's
   layout (or a bijection proved). As written, `LowerBound mul7SealedMachine
   mul7Spec 2` is a bound for the byte-swapped relation.
2. **Do not infer "no float datapath can do it" from `SingleFMA`.** The answer
   is a counterexample to the naive statement `f(memory word)*7`; any
   value-level lower bound must include `smax` and the OMR write mask, not just
   `SingleFMA`.

With those two caveats, the answer is compatible with the bound: the bound
says no *one* line suffices; the accepted answer uses six.

---

## 6. Verdict: the integer-only problems

| problem | uses `$aluf`? | uses `$mauf`? | uses OMR / `$imr`? | affected by D1? | judge |
|---|---|---|---|---|---|
| `3.a-plus-b` | no | no | no | **no** | `ACCEPTED!! score=6` |
| `2.plus-two` | no | no | no | **no** | `ACCEPTED!! score=5` |
| `12.convert-endian` | yes (ALU+MAU line 2, ALU line 3) | yes (line 3) | no | **no** | `ACCEPTED!! score=3` |

* **`3.a-plus-b`** (`iadd` + `ipassa $llr0v $llm32v`): only integer ALU ops with
  direct memory sources and memory destinations. `IntegerALU.evaluateBus`
  models `add`; `passa`'s low-long-word copy (`evaluateBus` `low := x.low`) is
  confirmed by `p14_llpassa` (a 2-long-word `ipassa` copies all four words).
  No forwarding, no mask, so neither D1 nor the `$aluf` question applies.
* **`2.plus-two`** (`idec`/`ixor` with flat-mode addresses): same story; the
  answer uses only ALU ops and direct memory; no masks, no forwarding.
* **`12.convert-endian`**: line 2 is a *parallel* ALU+MAU line
  (`ibsl $m0v $aluf $r8v; fvfma $aluf $aluf $aluf $s0v`) that relies exactly on
  the "both units read the pre-step `$aluf`" rule, and line 3 consumes the
  step-2 `$aluf`/`$mauf`. There is no OMR write, so D1 cannot apply. The
  emulator confirms the pre-step reading:
  * `fvfma` with `aluf = imm 0x34F80010` gives `s0 = 0x34F80018` =
    `singleFma 0x34F80010 0x34F80010 0x34F80010` (Lean: `888668184`);
  * the full answer on `X = 0x5FE1DC66CBEA3DB3` gives
    `LM1 = 0xB33DEACB66DCE15F`, byte-swapped;
  * `proofs_lean`'s `ConvertEndian.answerProgram 0x5FE1DC66CBEA3DB3` =
    `12915737465693462879` = `0xB33DEACB66DCE15F` — exact model/emulator
    agreement.
  So `12.convert-endian` is unaffected by the *discrepancy*, and is positive
  evidence that the model's `$aluf` role is right.

---

## 7. Reproduction

```sh
cd research/experiments/model-audit
./probe.sh probes/m2_timing.vsm          # OMR timing: old mask 5, then 10
./probe.sh probes/m12_alu_omr_mem.vsm    # same-instruction OMR+masked dst: no write
./probe.sh probes/g1_aluf_mauonly.vsm    # aluf invalid after a MAU-only step
./probe.sh probes/g6_alu_aluf_lw.vsm     # ALU aluf source = high long word
./probe.sh probes/a2_answer_5.vsm        # answer, all-5 -> 35 per word
./probe.sh probes/a1_answer_asc.vsm      # answer, 1..32 -> 7X
./probe.sh probes/a3_even_layout.vsm     # answer under the even-word layout
./probe.sh probes/ce3.vsm                # convert-endian end-to-end
./probe.sh probes/f3_sub_norm.vsm        # FTZ on a subnormal input
./probe.sh probes/f4_underflow.vsm       # FTZ on a subnormal result

# official judge, all four answers
cd ../../..
for p in 3.a-plus-b 2.plus-two 12.convert-endian 4.mul7; do
  python3 judge/judge-py/judge.py problems/challenge/$p/testcase.vsm \
    problems/challenge/$p/answer.vsm
done

# Lean probes
cd proofs_lean
lake env lean ../research/experiments/model-audit/lean/SingleFMAProbe.lean
lake env lean ../research/experiments/model-audit/lean/ModelProbe.lean
lake env lean ../research/experiments/model-audit/lean/ModelSupport.lean
lake env lean ../research/experiments/model-audit/lean/ConvertEndianProbe.lean
```

`logs/probes.log` contains the raw output of every probe cited above.

---

## Appendix A — probe index

| file | purpose |
|---|---|
| `p5_smax_half`, `p7_smax_full`, `p11_line2_aluf`, `p12_line2_mauf`, `p10_line3_mauf` | `smax` half-word semantics, aluf/mauf after lines 2/3 |
| `p6_fullwidth`, `p14_llpassa` | 2-long-word bus contents, `passa` low copy |
| `p8_line3` | answer lines 1-3, LM1 + OMR |
| `p13_prior_p1` | reproduction attempt of the prior `0x4241999A` probe |
| `b3_omr`, `b3b_omr`, `m1_bits`, `m11_tie` | OMR flag generation, bit order, tie |
| `m2_timing`, `m3_timing_clean`, `m4_mask5`, `m5_mask10`, `m6_zeroflush` | write mask / zero flush, visibility timing |
| `m7b_llmask`, `m8_llalu`, `m13_fixed_entry` | `ll` word mask, fixed entry 17 |
| `m10_cyclemask` | per-cycle entry + application |
| `m12_alu_omr_mem`, `m12b_omr_first` | same-instruction OMR + masked destination, both orders |
| `g1_aluf_mauonly`, `g2_aluf_nop`, `g3_aluf_noforward`, `g4_aluf_maskline`, `g5_noforward_alu`, `g6_alu_aluf_lw`, `g7_alu_neg` | `$aluf` lifecycle and operand roles |
| `f1_ftz`, `f2_ftz`, `f3_sub_norm`, `f4_underflow` | FTZ (no aluf/OMR) |
| `a1_answer_asc`, `a2_answer_5`, `a3_even_layout`, `a4_answer_1000`, `x0`, `x1000`, `x1000_a`, `x1000_b` | `4.mul7` datapath / output range |
| `ce3` | `12.convert-endian` end-to-end |

## Appendix B — Lean transcript (selected; `lean/SingleFMAProbe.lean`, `lean/ModelProbe.lean`, `lean/ModelSupport.lean`, `lean/ConvertEndianProbe.lean`)

```
-- SingleFMAProbe.lean (SingleFMA.singleFma)
singleFma 0x00000005 0x40E00000 0                    = 0x00000000
singleFma 0x00400000 0x40000000 0                    = 0x00000000
singleFma 0x0D800000 0x30800000 0                    = 0x00000000
singleFma 0xC0E00000 0x40E00000 0x40E00000           = 0xC2280000
singleFma 0x40E00005 0x40E00000 0xC2280000           = 0x40E00023
singleFma 0x40E003E8 0x40E00000 0xC2280000           = 0x40E01B58
singleFma 0x40E00001 0x40E00000 0xC2280000           = 0x40E00007
singleFma 0x40E00000 0x40E00000 0                   = 0x42440000

-- IntegerALU / Masks
evaluateBus .half (.maximum false) ⟨0x0000000500000005,0⟩
   ⟨0x40E0000040E00000,0x40E0000040E00000⟩ false
   .value = ⟨0x40E0000540E00005, 0⟩
   .flags 0..3 = (true,false,true,false)      -- bit pattern 0b0101 = 5
evaluateBus .half (.maximum false) ⟨0x000003E8000003E8,0⟩ ... = ⟨0x40E003E840E003E8,0⟩
readEntry regs(entry1:=5) 1 0 = 5
readEntry regs(post-ALU entry1:=10) 1 0 = 10
writeBus .long 5  ⟨0,0⟩ ⟨0x1234567812345678,0⟩ = 0x0000567800005678
writeBus .long 10 ⟨0,0⟩ ⟨0x1234567812345678,0⟩ = 0x1234000012340000

-- ConvertEndian
answerProgram 0x5FE1DC66CBEA3DB3 = 12915737465693462879 = 0xB33DEACB66DCE15F
singleFma 0x34F80010 0x34F80010 0x34F80010 = 888668184 = 0x34F80018
```
