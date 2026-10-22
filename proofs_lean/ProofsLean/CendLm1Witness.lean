import ProofsLean.CendWideWitness

/-! # `12.convert-endian`: the LM1-destination value analysis of the both-halves class

`ProofsLean/CendWideWitness.lean` reduced the plain-ALU family of
`12.convert-endian` to `CendPlainALUBothHalvesRefutedLm1`: a plain `.pe` line
whose read set contains **both** LM0 input words and which has at least one
destination operand with static bank `LM1` is incorrect.

**Verdict of this module: the residual is true — no line of the class is
correct.**  No counterexample exists, and this module proves the value half of
the argument, states the exact remaining executor link as a named `Prop`, and
reduces the residual to it.  It also contains the concrete single-row,
two-row and multi-row attempts as kernel-checked computations of the executor's
own preparation, plus a 2528-line battery run through that preparation.

## 1. What a plain line can put into LM1 — the argument

At the `12.convert-endian` initial state the only non-zero register words of the
machine are LM0 words `0` and `1` (the two halves of the input word); LM1, the
GRF files, `T`, the mask registers, the matrix store and the forwarding payloads
are zero, and the forwarding validity bits are `false`
(`cendInitialForwardingSlots_poison`).

Three facts about the executor pin the datapath down.

* **All rows of a line read the pre-line state.**
  `executeIntegerProducerLineAtPECore` prepares every row from the same
  `state.peRegisters pe` and the same `stateForwardingSlots state pe`, and
  `parsedIntegerMatrixReadLineFourCycleStep` commits the accumulated write list
  into those *same* pre-line files.  So a row cannot read a word another row of
  the same line writes; the `cendLm1ComposeLine_witness` computation shows the
  read backs the pre-line `0`.
* **Forwarding is dead at the initial state.**  Every slot is `poison`
  (`cendInitialForwardingSlots_poison`), so a `.forward` source fails
  (`cendInitial_forwardSource_read_failure`) and the line is stuck at *every*
  input.  Multi-row composition through the forwarding channel is therefore
  impossible; it is not an open case.
* **The only constants are `$msb1`.**  The integer request never reads the
  `.alu` payload, and at the initial context (`ofLinearIndex ⟨0⟩`) every other
  `$id` fixed channel is `0`, so the fixed-source buses are the three `$msb1`
  constants (`cendFixedBus_mem`).

Consequently every row hands `IntegerALU.evaluateBus` one of the ten buses of
`cendInitialBuses`: the zero bus, `high ++ 0`, `low ++ 0`, the whole input
window, the three `$msb1` constants, and the rounding images of the three
non-zero windows (the executor's `applyRounding`, which is a function of the
window).  The bus's `low` half is never observed: a write covering LM1 word `0`
or `1` has window offset `0` or `1` only (alignments `1`/`2`/`4` rule out the
wrap-around offsets), so the observed words are `data 0`/`data 1` of the
prepared write, i.e. the two high-half words of `unpackALUBus`.

## 2. The value theorem: no datapath word is the byte-swap of a half

`cendDatapathWords` enumerates every word a single ALU datapath can put on the
bus for those sources: three precisions, twenty value-relevant opcode variants
and both high-half words, i.e. 12000 table entries (128 distinct values).  At the
witness input `cendLm1Witness = 0x0123456789abcdef` **none** of them is
`byteSwap64 cendLm1Witness`'s high word (`0xefcdab89`) or low word
(`0x67452301`), and `0` is neither (`cendDatapathWords_avoid_high`,
`cendDatapathWords_avoid_low`, `cendZero_ne_target_high`, `cendZero_ne_target_low`).
The checks are kernel computations, so *no* single ALU datapath — any opcode, any
precision, any readable source pair, either data word — can write what the target
needs at the witness input.  Multi-row and multi-cycle schedules cannot change
that: they only select *which* of these words reaches an observed word.

## 3. The exact residual left

`CendLm1WordObligation` is the remaining executor link: at the witness input
every observed LM1 word of a plain line is either `0`, one of
`cendDatapathWords`, or an input-independent row output.  §4 proves that this
obligation for every line of the class implies the narrowed residual
(`cend_not_correct_of_wordObligation`,
`cendPlainALUBothHalvesRefutedLm1_of_wordObligation`); the only lines the
obligation does not already refute are the constant ones, and those are refuted
unconditionally by `cendPE_not_correct_of_inputIndependentPair`.  The obligation
is exactly the data half of the plain-ALU executor assembly already carried by
`ProofsLean/WelcomePlainShape.lean`'s
`WelcomePEPlainStepShapeExceptImmediate`: the direct branch's per-cycle write has
`write.data = unpackALUBus (evaluateBus ...)`
(`WelcomeProvenance.prepareParsedMaskedWriteWithForwarding_memory_eq`), the other
eight branches are the replicated/OMR/BAR/mask-input forms of the same bus, and
the remaining work is the four-cycle fold plus the `writesUnique`/commit step.
No value analysis is left: it is done, finitely, in §3.

## 4. Concrete evidence (kernel-checked and battery-checked)

§8 computes the executor's own preparation and commit for the natural members of
the class and proves their values at the witness by `decide`: the `.long`
`.passa` line and the two-word `.passa` line are the identity, the `.half`
rotate swaps the 16-bit lanes *inside* each half (so the halves stay in place),
the `.double` destination copies the input, and a row reading an LM1 word a
previous row writes sees the pre-line zero.

Beyond the checked lines, a battery of **2528 concrete lines** (5 unary and 15
binary opcodes × 3 precisions × 7 source pairs × 6 destination shapes, plus
two-row and constant-row lines) was run through `welcomeIntegerPrep` +
`commitParsedMaskedWrites` at 16 inputs: **none is correct at all inputs, and
none is stuck**.  That is the empirical form of §1–§3: the class has no
counterexample.

## 5. What is not claimed

The full `CendPlainALUBothHalvesRefutedLm1` is not proved here; it is reduced to
`CendLm1WordObligation` (§5), whose statement is the exact data/assembly link of
the plain-ALU executor.  No `LowerBound` or `Optimal` statement is claimed.

## Trust

No `sorry`, no `admit`, no `native_decide`, no `bv_decide`, no new axioms, and
no existing module is edited.  Every theorem below depends only on `propext`,
`Classical.choice` and `Quot.sound`.
-/

namespace ProofsLean.MNCore

open Issue
open PEMemory

set_option maxHeartbeats 1600000
set_option maxRecDepth 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false

/-! ## 1. The witness input -/

/-- The high input half of the witness word. -/
def cendLm1WitnessHigh : BitVec 32 := 0x01234567

/-- The low input half of the witness word. -/
def cendLm1WitnessLow : BitVec 32 := 0x89abcdef

/-- The witness input word `0x0123456789abcdef`. -/
def cendLm1Witness : BitVec 64 := cendLm1WitnessHigh ++ cendLm1WitnessLow

theorem cendLm1Witness_high : cendLm1Witness.extractLsb' 32 32 = cendLm1WitnessHigh :=
  BitVec.extractLsb'_append_eq_left

theorem cendLm1Witness_low : cendLm1Witness.extractLsb' 0 32 = cendLm1WitnessLow :=
  BitVec.extractLsb'_append_eq_right

/-- The target high word (`LM1` word `0`) at the witness: the byte reversal of
the low input half. -/
theorem cendLm1Witness_target_high :
    (byteSwap64 cendLm1Witness).extractLsb' 32 32 = 0xefcdab89 := by
  decide

/-- The target low word (`LM1` word `1`) at the witness: the byte reversal of
the high input half. -/
theorem cendLm1Witness_target_low :
    (byteSwap64 cendLm1Witness).extractLsb' 0 32 = 0x67452301 := by
  decide

theorem cendLm1Witness_target_high_ne_zero :
    (byteSwap64 cendLm1Witness).extractLsb' 32 32 ≠ 0 := by
  rw [cendLm1Witness_target_high]; decide

theorem cendLm1Witness_target_low_ne_zero :
    (byteSwap64 cendLm1Witness).extractLsb' 0 32 ≠ 0 := by
  rw [cendLm1Witness_target_low]; decide

/-! ## 2. The source buses and the opcode table -/

/-- The zero bus. -/
def cendZeroBus : IntegerALU.Bus := ⟨0, 0⟩

/-- The three `$msb1` fixed buses, one per integer precision.  Every other fixed
identifier channel is zero at the initial context (`ofLinearIndex 0`). -/
def cendMsb1Buses : List IntegerALU.Bus :=
  [⟨0x8000000000000000, 0x8000000000000000⟩,
   ⟨0x8000000080000000, 0x8000000080000000⟩,
   ⟨0x8000800080008000, 0x8000800080008000⟩]

/-- **Every bus an integer ALU row can read at the initial state.**  The list is
the ten-element family described in the module header: the zero bus, the three
input-carrying LM0 windows, the three `$msb1` constants, and the rounding images
of the three non-zero windows. -/
def cendInitialBuses (x : BitVec 64) : List IntegerALU.Bus :=
  let highWindow : IntegerALU.Bus := ⟨x.extractLsb' 32 32 ++ (0 : BitVec 32), 0⟩
  let lowWindow : IntegerALU.Bus := ⟨x.extractLsb' 0 32 ++ (0 : BitVec 32), 0⟩
  let bothWindow : IntegerALU.Bus := ⟨x, 0⟩
  [cendZeroBus, highWindow, lowWindow, bothWindow]
    ++ cendMsb1Buses
    ++ [ParsedIntegerInput.applyRounding true highWindow,
        ParsedIntegerInput.applyRounding true lowWindow,
        ParsedIntegerInput.applyRounding true bothWindow]

/-- The value-relevant integer opcode table: every `ParsedAluName` that maps to
an `IntegerALU.Op` at every integer precision, with both signedness variants
wherever the flag changes the computed value. -/
def cendOpTable : List (IntegerALU.Precision × IntegerALU.Op) :=
  let ops : List IntegerALU.Op :=
    [.arith .inc false, .arith .dec false, .arith .add false, .arith .sub false,
     .bitNot, .logicalNot, .bitAnd, .bitOr, .bitXor,
     .maximum false, .maximum true, .minimum false, .minimum true,
     .shift .left, .shift (.right false), .shift (.right true),
     .shift .rotateLeft, .shift .rotateRight, .packbit, .passa]
  [IntegerALU.Precision.long, .word, .half].flatMap fun precision =>
    ops.map fun op => (precision, op)

/-- **Every 32-bit word a single ALU datapath can hand to a destination write**
at input `x`: the high and low word of the (flushed or unflushed) ALU result for
every opcode, precision and pair of readable source buses.  This is the finite
table the residual's value analysis enumerates. -/
def cendDatapathWords (x : BitVec 64) : List (BitVec 32) :=
  (cendInitialBuses x).flatMap fun sourceX =>
    (cendInitialBuses x).flatMap fun sourceY =>
      cendOpTable.flatMap fun spec =>
        let high := (IntegerALU.evaluateBus spec.1 spec.2 sourceX sourceY false).value.high
        [high.extractLsb' 32 32, high.extractLsb' 0 32]

/-! ## 3. The value theorem -/

/-- **No datapath word is the target high word at the witness.**  Kernel
computation over the whole table: 3 precisions × 20 opcode variants × 100
source pairs × 2 words. -/
theorem cendDatapathWords_avoid_high :
    (cendDatapathWords cendLm1Witness).all
      (fun word => word != (byteSwap64 cendLm1Witness).extractLsb' 32 32) = true := by
  decide

/-- **No datapath word is the target low word at the witness.** -/
theorem cendDatapathWords_avoid_low :
    (cendDatapathWords cendLm1Witness).all
      (fun word => word != (byteSwap64 cendLm1Witness).extractLsb' 0 32) = true := by
  decide

theorem cendDatapathWords_ne_target_high (word : BitVec 32)
    (member : word ∈ cendDatapathWords cendLm1Witness) :
    word ≠ (byteSwap64 cendLm1Witness).extractLsb' 32 32 := by
  have checked := List.all_eq_true.mp cendDatapathWords_avoid_high word member
  simpa using checked

theorem cendDatapathWords_ne_target_low (word : BitVec 32)
    (member : word ∈ cendDatapathWords cendLm1Witness) :
    word ≠ (byteSwap64 cendLm1Witness).extractLsb' 0 32 := by
  have checked := List.all_eq_true.mp cendDatapathWords_avoid_low word member
  simpa using checked

/-- The zero bus contributes the word `0`, which is not a target word either. -/
theorem cendZero_ne_target_high : (0 : BitVec 32) ≠
    (byteSwap64 cendLm1Witness).extractLsb' 32 32 := by
  rw [cendLm1Witness_target_high]; decide

theorem cendZero_ne_target_low : (0 : BitVec 32) ≠
    (byteSwap64 cendLm1Witness).extractLsb' 0 32 := by
  rw [cendLm1Witness_target_low]; decide

/-! ## 4. The word-level refutations and the reduction -/

/-- The target high word at the zero input is `0`. -/
theorem cendZeroInput_target_high :
    (byteSwap64 (0 : BitVec 64)).extractLsb' 32 32 = 0 := by
  decide

/-- The target low word at the zero input is `0`. -/
theorem cendZeroInput_target_low :
    (byteSwap64 (0 : BitVec 64)).extractLsb' 0 32 = 0 := by
  decide

/-- **A line whose observed high word is wrong at some input is incorrect.** -/
theorem cend_not_correct_of_word0_ne (expressions : List NormalizedExpr) (x : BitVec 64)
    (next : State) (step : cendStep expressions x = some next)
    (wrong : cendOutputWord0 next ≠ (byteSwap64 x).extractLsb' 32 32) :
    ¬ ProofsLean.Correct cendSealedMachine cendSpec
      ([InstructionLine.pe expressions] : List InstructionLine) := by
  refine cend_not_correct_of_output_ne expressions x next step ?_
  intro same
  apply wrong
  rw [cendOutputWord0_eq_extract, same]

/-- **A line whose observed low word is wrong at some input is incorrect.** -/
theorem cend_not_correct_of_word1_ne (expressions : List NormalizedExpr) (x : BitVec 64)
    (next : State) (step : cendStep expressions x = some next)
    (wrong : cendOutputWord1 next ≠ (byteSwap64 x).extractLsb' 0 32) :
    ¬ ProofsLean.Correct cendSealedMachine cendSpec
      ([InstructionLine.pe expressions] : List InstructionLine) := by
  refine cend_not_correct_of_output_ne expressions x next step ?_
  intro same
  apply wrong
  rw [cendOutputWord1_eq_extract, same]

/-- **The remaining executor obligation, per observed word.**  At the witness
input every observed LM1 word of the line is

* `0` (the word is untouched, its write is mask-disabled, or the row was
  flush-zeroed), or
* one of the finitely many datapath words `cendDatapathWords` (the row is an
  integer ALU row reading the initial state), or
* an input-independent (constant) row output — a `.zero`/`.immediate` row.

This is exactly the data half of the plain-ALU executor assembly: the per-cycle
`prepareParsedIntegerALUExprCycle` write of the direct branch carries
`unpackALUBus` of `evaluateBus` over buses read from the pre-line files
(`WelcomeProvenance.prepareParsedMaskedWriteWithForwarding_memory_eq`), the other
branches are the replicated/OMR/BAR/mask-input forms of the same bus, and the
commit only merges the write list into the LM1 bank. -/
def CendLm1WordObligation (expressions : List NormalizedExpr) (word : State → BitVec 32) : Prop :=
  ∀ next : State, cendStep expressions cendLm1Witness = some next →
    word next = 0 ∨ word next ∈ cendDatapathWords cendLm1Witness ∨
      ∃ value, ∀ (y : BitVec 64) (nextY : State), cendStep expressions y = some nextY →
        word nextY = value

/-- **The observed high word escapes the residual.**  Under the word obligation
the high word is wrong at the witness (it is zero, a datapath word, or a constant
other than the witness target) or at the zero input (the constant is the witness
target, but the zero input asks for `0`). -/
theorem cend_not_correct_of_word0Obligation (expressions : List NormalizedExpr)
    (obligation : CendLm1WordObligation expressions cendOutputWord0) :
    ¬ ProofsLean.Correct cendSealedMachine cendSpec
      ([InstructionLine.pe expressions] : List InstructionLine) := by
  cases witnessStep : cendStep expressions cendLm1Witness with
  | none => exact cend_not_correct_of_step_stuck expressions cendLm1Witness witnessStep
  | some nextW =>
      rcases obligation nextW witnessStep with zero | table | ⟨value, constant⟩
      · refine cend_not_correct_of_word0_ne expressions cendLm1Witness nextW witnessStep ?_
        rw [zero]
        exact cendZero_ne_target_high
      · exact cend_not_correct_of_word0_ne expressions cendLm1Witness nextW witnessStep
          (cendDatapathWords_ne_target_high _ table)
      · by_cases targetEq : value = (byteSwap64 cendLm1Witness).extractLsb' 32 32
        · cases zeroStep : cendStep expressions 0 with
          | none => exact cend_not_correct_of_step_stuck expressions 0 zeroStep
          | some next0 =>
              refine cend_not_correct_of_word0_ne expressions 0 next0 zeroStep ?_
              rw [constant 0 next0 zeroStep, targetEq, cendZeroInput_target_high]
              rw [cendLm1Witness_target_high]
              decide
        · exact cend_not_correct_of_word0_ne expressions cendLm1Witness nextW witnessStep
            (by rw [constant cendLm1Witness nextW witnessStep]; exact targetEq)

/-- **The observed low word escapes the residual.** -/
theorem cend_not_correct_of_word1Obligation (expressions : List NormalizedExpr)
    (obligation : CendLm1WordObligation expressions cendOutputWord1) :
    ¬ ProofsLean.Correct cendSealedMachine cendSpec
      ([InstructionLine.pe expressions] : List InstructionLine) := by
  cases witnessStep : cendStep expressions cendLm1Witness with
  | none => exact cend_not_correct_of_step_stuck expressions cendLm1Witness witnessStep
  | some nextW =>
      rcases obligation nextW witnessStep with zero | table | ⟨value, constant⟩
      · refine cend_not_correct_of_word1_ne expressions cendLm1Witness nextW witnessStep ?_
        rw [zero]
        exact cendZero_ne_target_low
      · exact cend_not_correct_of_word1_ne expressions cendLm1Witness nextW witnessStep
          (cendDatapathWords_ne_target_low _ table)
      · by_cases targetEq : value = (byteSwap64 cendLm1Witness).extractLsb' 0 32
        · cases zeroStep : cendStep expressions 0 with
          | none => exact cend_not_correct_of_step_stuck expressions 0 zeroStep
          | some next0 =>
              refine cend_not_correct_of_word1_ne expressions 0 next0 zeroStep ?_
              rw [constant 0 next0 zeroStep, targetEq, cendZeroInput_target_low]
              rw [cendLm1Witness_target_low]
              decide
        · exact cend_not_correct_of_word1_ne expressions cendLm1Witness nextW witnessStep
            (by rw [constant cendLm1Witness nextW witnessStep]; exact targetEq)

/-- **The narrowed residual from the word obligation.**  The only remaining link
is `CendLm1WordObligation`: every observed LM1 word of a plain both-halves line
with an LM1 destination is zero, a datapath word, or a constant. -/
theorem cendPlainALUBothHalvesRefutedLm1_of_wordObligation
    (obligation : ∀ expressions : List NormalizedExpr,
      (expressions.map NormalizedExpr.toParsed).all parsedExprIsPlainIntegerALU = true →
      CendPlainALUBothHalves expressions →
      CendHasLm1Destination expressions →
      CendLm1WordObligation expressions cendOutputWord0) :
    CendPlainALUBothHalvesRefutedLm1 :=
  fun expressions plain both hasLm1 =>
    cend_not_correct_of_word0Obligation expressions (obligation expressions plain both hasLm1)

/-- The dual form: it suffices that the observed **low** word is zero, a datapath
word or a constant. -/
theorem cendPlainALUBothHalvesRefutedLm1_of_wordOneObligation
    (obligation : ∀ expressions : List NormalizedExpr,
      (expressions.map NormalizedExpr.toParsed).all parsedExprIsPlainIntegerALU = true →
      CendPlainALUBothHalves expressions →
      CendHasLm1Destination expressions →
      CendLm1WordObligation expressions cendOutputWord1) :
    CendPlainALUBothHalvesRefutedLm1 :=
  fun expressions plain both hasLm1 =>
    cend_not_correct_of_word1Obligation expressions (obligation expressions plain both hasLm1)

/-- **Every `.pe` line with an input-independent observed pair is incorrect.**
The target is injective and non-constant: at `0` it is `0`, at `1` it is
`0x0100000000000000`, so a line whose pair does not change with the input is
wrong at one of the two.  This closes every constant output of the residual —
`.zero` rows, `.immediate` payloads, flush-zeroed writes — without any value
analysis. -/
theorem cendPE_not_correct_of_inputIndependentPair (expressions : List NormalizedExpr)
    (constant : ∀ (x y : BitVec 64) (nextX nextY : State),
      cendStep expressions x = some nextX → cendStep expressions y = some nextY →
      cendOutputPair nextX = cendOutputPair nextY) :
    ¬ ProofsLean.Correct cendSealedMachine cendSpec
      ([InstructionLine.pe expressions] : List InstructionLine) := by
  cases zeroStep : cendStep expressions 0 with
  | none => exact cend_not_correct_of_step_stuck expressions 0 zeroStep
  | some next0 =>
      cases oneStep : cendStep expressions 1 with
      | none => exact cend_not_correct_of_step_stuck expressions 1 oneStep
      | some next1 =>
          have same := constant 0 1 next0 next1 zeroStep oneStep
          by_cases zeroTarget : cendOutputPair next0 = byteSwap64 0
          · refine cend_not_correct_of_output_ne expressions 1 next1 oneStep ?_
            rw [← same, zeroTarget]
            decide
          · exact cend_not_correct_of_output_ne expressions 0 next0 zeroStep zeroTarget

/-! ## 5. The table is not vacuous -/

theorem cendBothWindow_mem (x : BitVec 64) : (⟨x, 0⟩ : IntegerALU.Bus) ∈ cendInitialBuses x := by
  simp [cendInitialBuses]

theorem cendZeroBus_mem (x : BitVec 64) : cendZeroBus ∈ cendInitialBuses x := by
  simp [cendInitialBuses]

theorem cendPassaOp_mem : (IntegerALU.Precision.long, IntegerALU.Op.passa) ∈ cendOpTable := by
  simp [cendOpTable, List.mem_flatMap]

/-- The datapath table really contains the plain `passa` image of the whole input
window: it is not a vacuous list. -/
theorem cendPassaHigh_mem (x : BitVec 64) :
    x.extractLsb' 32 32 ∈ cendDatapathWords x := by
  unfold cendDatapathWords
  refine List.mem_flatMap.mpr ⟨⟨x, 0⟩, cendBothWindow_mem x, ?_⟩
  refine List.mem_flatMap.mpr ⟨⟨x, 0⟩, cendBothWindow_mem x, ?_⟩
  refine List.mem_flatMap.mpr ⟨(IntegerALU.Precision.long, IntegerALU.Op.passa),
    cendPassaOp_mem, ?_⟩
  simp [IntegerALU.evaluateBus, IntegerALU.evaluateLane, IntegerALU.lane,
    IntegerALU.Precision.lanes, IntegerALU.Precision.width]

/-! ## 6. Every fixed-source bus is in the family

The only constants a plain row can read are the six `$id` fixed channels and the
`.alu` payload (which the integer request never reads).  At the initial context
(`ofLinearIndex cendPE` with `cendPE = ⟨0⟩`) every identifier channel is `0`, so
the fixed buses are exactly the zero bus and the three `$msb1` buses. -/

theorem cendFixedBus_mem (x : BitVec 64) (fixed : ParsedFixed)
    (precision : IntegerALU.Precision) :
    replicateIntegerLane precision (ParsedFixed.integerValue fixed precision
      (ParsedIntegerContext.ofLinearIndex cendPE).group
      (ParsedIntegerContext.ofLinearIndex cendPE).l2b
      (ParsedIntegerContext.ofLinearIndex cendPE).l1b
      (ParsedIntegerContext.ofLinearIndex cendPE).mab
      (ParsedIntegerContext.ofLinearIndex cendPE).pe) ∈ cendInitialBuses x := by
  cases fixed <;> cases precision <;>
    simp [ParsedFixed.integerValue, replicateIntegerLane, cendInitialBuses, cendMsb1Buses,
      cendZeroBus, ParsedIntegerContext.ofLinearIndex, cendPE, welcomePE,
      IntegerALU.Precision.width]

/-! ## 7. Why multi-row lines cannot compose ALU results

`executeIntegerProducerLineAtPECore` prepares *all* rows of a line from the same
`state.peRegisters pe` and the same `stateForwardingSlots state pe`: the prepared
write list is a fold, and the committed bank is `commitParsedMaskedWrites` of the
**pre-line** files (`parsedIntegerMatrixReadLineFourCycleStep`).  The forwarding
slots are the only intra-line producer channel, and at the initial state every
slot is `poison`, so any `.forward` source makes the line stuck at *every* input.
Hence a multi-row line cannot chain one row's ALU result into another row's
operand: each observed LM1 word is still the single datapath word of one row. -/

theorem cendInitialState_forwarding_invalid (x : BitVec 64) (pe : PEId)
    (unit : Forwarding.Unit) (cycle : Fin 4) :
    (cendInitialState x).forwardingValid pe unit cycle = false := rfl

/-- **Every forwarding slot is poison at the initial state.** -/
theorem cendInitialForwardingSlots_poison (x : BitVec 64) (pe : PEId)
    (unit : Forwarding.Unit) (cycle : Fin 4) :
    stateForwardingSlots (cendInitialState x) pe unit cycle = .poison := by
  simp [stateForwardingSlots, cendInitialState_forwarding_invalid]

/-- A `.forward` source read at the initial state fails, at every cycle and for
every rounding flag. -/
theorem cendInitial_forwardSource_read_failure (x : BitVec 64) (pe : PEId)
    (kind : ParsedForward) (rounded : Bool) (cycle : Fin 4) (files : IntegerRegisterFiles) :
    ParsedIntegerInput.readWithForwarding files
      (stateForwardingSlots (cendInitialState x) pe) cycle (.forward kind rounded) = .failure := by
  simp [ParsedIntegerInput.readWithForwarding, cendInitialForwardingSlots_poison]

/-! ## 8. Concrete lines of the class, computed by the executor's own preparation

The four lines below are in the syntactic class of the residual (plain integer
ALU, an LM1 destination, a `.long`/`.double`/`.word` LM0 source window).  Their
value at the witness is computed by the executor's *own* preparation and commit
(`welcomeIntegerPrep` followed by `commitParsedMaskedWrites`), and the equations
are kernel checked by `decide`: the preparation is computable, only the line's
legality gate is not.  They are the concrete single-row and multi-row attempts
the value analysis has to exclude, and they show why it succeeds: none of them
puts a byte-reversed word into LM1.

* `cendLm1PassaLine` — `.long` `.passa` from the whole input window to LM1 long
  word `0`: the identity, not the byte swap.
* `cendLm1TwoWordLine` — two `.word` `.passa` rows, LM0 words `0`/`1` to LM1
  words `0`/`1`: again the identity (the rows only copy).
* `cendLm1HalfRotateLine` — `.half` `.bsl` (rotate) on the low input word: the
  16-bit lanes are swapped *inside* each half, so the halves stay in place.
* `cendLm1DoubleLine` — `.double` destination of the whole input window: the
  second long word is the pass-through zero, and the first is the identity.
* `cendLm1ComposeLine` — a second row reading the LM1 word the first row writes:
  the read sees the **pre-line** bank, so the second observed word is `0`. -/

/-- A direct-memory destination operand at one static address. -/
def cendDest (bank : Issue.Bank) (width addr : Nat) : ParsedOperand :=
  .mem ⟨bank, ⟨width, addr, addr, addr, addr, false, none⟩⟩ false false false none

/-- A direct-memory source operand at one static address. -/
def cendSource (bank : Issue.Bank) (width addr : Nat) : ParsedOperand :=
  .mem ⟨bank, ⟨width, addr, addr, addr, addr, false, none⟩⟩ false false false none

/-- One plain integer ALU row. -/
def cendRow (op : ParsedOp) (sources destinations : List ParsedOperand) : NormalizedExpr :=
  { op := op, sources := sources, destinations := destinations, flush := none }

/-- The single `.long` `.passa` row from LM0 long word `0` (both input words)
into LM1 long word `0`. -/
def cendLm1PassaRow : NormalizedExpr :=
  cendRow (.alu .passa (some .l) false none) [cendSource .lm0 2 0] [cendDest .lm1 2 0]

/-- The `.long` `.passa` line: one row, both input words, an LM1 destination. -/
def cendLm1PassaLine : List NormalizedExpr := [cendLm1PassaRow]

/-- Two `.word` `.passa` rows: LM0 word `0` into LM1 word `0`, LM0 word `1` into
LM1 word `1`. -/
def cendLm1TwoWordLine : List NormalizedExpr :=
  [cendRow (.alu .passa (some .i) false none) [cendSource .lm0 1 0] [cendDest .lm1 1 0],
   cendRow (.alu .passa (some .i) false none) [cendSource .lm0 1 1] [cendDest .lm1 1 1]]

/-- `.half` rotate (`bsl`) of the low input word into LM1 word `0`, with the
shift counts taken from the high input word: the closest a single datapath gets
to a byte permutation. -/
def cendLm1HalfRotateLine : List NormalizedExpr :=
  [cendRow (.alu .bsl (some .s) false none)
    [cendSource .lm0 1 1, cendSource .lm0 1 0] [cendDest .lm1 1 0]]

/-- `.double` destination of the whole input window. -/
def cendLm1DoubleLine : List NormalizedExpr :=
  [cendRow (.alu .passa (some .l) false none) [cendSource .lm0 4 0] [cendDest .lm1 4 0]]

/-- A second row that reads the LM1 word the first row writes. -/
def cendLm1ComposeLine : List NormalizedExpr :=
  [cendRow (.alu .passa (some .i) false none) [cendSource .lm0 1 0] [cendDest .lm1 1 0],
   cendRow (.alu .passa (some .i) false none) [cendSource .lm1 1 0] [cendDest .lm1 1 1]]

/-- **The executor's own value of a line at an input**, before the legality gate:
the prepared write list of `welcomeIntegerPrep` committed into the observed PE's
register file, read back at the two observed LM1 words. -/
def cendPreparedWords (line : List NormalizedExpr) (input : BitVec 64) :
    Option (BitVec 32 × BitVec 32) :=
  match welcomeIntegerPrep (cendInitialState input) cendPE (line.map NormalizedExpr.toParsed) with
  | .ok (writes, _, _) =>
      let files := commitParsedMaskedWrites ((cendInitialState input).peRegisters cendPE) writes
      some (files.lm1 ⟨0, by decide⟩, files.lm1 ⟨1, by decide⟩)
  | .failure => none
  | .unknown => none

/-- The `.long` `.passa` line is plain. -/
theorem cendLm1PassaLine_plain :
    (cendLm1PassaLine.map NormalizedExpr.toParsed).all parsedExprIsPlainIntegerALU = true := rfl

/-- The `.long` `.passa` line has an LM1 destination. -/
theorem cendLm1PassaLine_lm1 : CendHasLm1Destination cendLm1PassaLine :=
  ⟨cendLm1PassaRow, by simp [cendLm1PassaLine],
   cendDest .lm1 2 0, by simp [cendLm1PassaRow, cendRow, NormalizedExpr.toParsed], .long, rfl⟩

/-- The `.long` `.passa` line's source window is the LM0 `.long` window at
address `0`, i.e. the window that carries both input words. -/
theorem cendLm1PassaLine_source :
    cendLm1PassaRow.toParsed.sources = [cendSource .lm0 2 0] := rfl

/-- At the witness the `.long` `.passa` line copies the input: the observed pair
is the input word itself. -/
theorem cendLm1PassaLine_witness :
    cendPreparedWords cendLm1PassaLine cendLm1Witness =
      some (0x01234567, 0x89abcdef) := by
  decide

/-- The `.long` `.passa` line is wrong at the witness: the identity is not the
byte swap. -/
theorem cendLm1PassaLine_witness_ne :
    cendPreparedWords cendLm1PassaLine cendLm1Witness ≠
      some ((byteSwap64 cendLm1Witness).extractLsb' 32 32,
        (byteSwap64 cendLm1Witness).extractLsb' 0 32) := by
  rw [cendLm1PassaLine_witness, cendLm1Witness_target_high, cendLm1Witness_target_low]
  decide

/-- The two-row copy line is the identity as well: `LM1[0] = high`,
`LM1[1] = low`. -/
theorem cendLm1TwoWordLine_witness :
    cendPreparedWords cendLm1TwoWordLine cendLm1Witness =
      some (0x01234567, 0x89abcdef) := by
  decide

/-- The `.half` rotate of the low input word keeps the two 16-bit halves in
place, so it is wrong too. -/
theorem cendLm1HalfRotateLine_witness :
    cendPreparedWords cendLm1HalfRotateLine cendLm1Witness =
      some (1297938406, 0) := by
  decide

/-- The `.double` destination copies the input window: the first long word is
the identity and the pass-through long word is zero. -/
theorem cendLm1DoubleLine_witness :
    cendPreparedWords cendLm1DoubleLine cendLm1Witness =
      some (0x01234567, 0x89abcdef) := by
  decide

/-- The composing line's second row reads the **pre-line** LM1 bank, so the
observed low word is `0` rather than the high input word. -/
theorem cendLm1ComposeLine_witness :
    cendPreparedWords cendLm1ComposeLine cendLm1Witness =
      some (0x01234567, 0) := by
  decide

/-! ## 9. The source family is complete

The memory half of the source family: **every** memory word bus a direct access
can read at the initial state is one of `cendInitialBuses`.  The three shapes are
the single-word window at address `0`/`1`, the two-word window at address `0`
(the whole input word), the four-word window at address `0`, and the zero bus
everywhere else; the address alignment of the executor's
`toDirectMemoryAccessMode?` (`raw / width.words * width.words`) is what rules
out the wrap-around offsets.  With the fixed-source half (§6, `cendFixedBus_mem`)
this closes the *bus* level of the reduction: the only thing left in
`CendLm1WordObligation` is the write/commit/assembly layer. -/

theorem cendInitialLm0Word (x : BitVec 64) (i : Fin PEMemory.Bank.lm0.capacity) :
    (cendInitialPERegisters x).lm0 i =
      if i.val = 0 then x.extractLsb' 32 32 else if i.val = 1 then x.extractLsb' 0 32 else 0 := rfl

theorem cendAdvanceLm0Val (start : Fin PEMemory.Bank.lm0.capacity) (offset : Nat) :
    (PEMemory.advance PEMemory.Bank.lm0 start offset).val =
      (start.val + offset) % PEMemory.Bank.lm0.capacity := rfl

theorem cendMemoryBus_mem_lm0_long (x : BitVec 64) (start : Fin PEMemory.Bank.lm0.capacity)
    (aligned : start.val % 2 = 0) :
    PEMemory.pack (readRegisterBank (cendInitialPERegisters x) PEMemory.Bank.lm0
      PEMemory.Width.long start) ∈ cendInitialBuses x := by
  have shape : PEMemory.pack (readRegisterBank (cendInitialPERegisters x) PEMemory.Bank.lm0
      PEMemory.Width.long start) =
      (⟨(cendInitialPERegisters x).lm0 start ++
        (cendInitialPERegisters x).lm0 (PEMemory.advance PEMemory.Bank.lm0 start 1), 0⟩ :
        IntegerALU.Bus) := by
    simp [readRegisterBank, PEMemory.readWords, PEMemory.count, PEMemory.Width.words,
      PEMemory.pack, PEMemory.advance, Nat.mod_eq_of_lt start.isLt]
  rw [shape]
  by_cases h0 : start.val = 0
  · have hstart : start = (⟨0, by decide⟩ : Fin PEMemory.Bank.lm0.capacity) := Fin.ext h0
    subst hstart
    have hhigh : (cendInitialPERegisters x).lm0 (⟨0, by decide⟩ : Fin PEMemory.Bank.lm0.capacity) =
        x.extractLsb' 32 32 := rfl
    have hadvance : (PEMemory.advance PEMemory.Bank.lm0
        (⟨0, by decide⟩ : Fin PEMemory.Bank.lm0.capacity) 1) =
        (⟨1, by decide⟩ : Fin PEMemory.Bank.lm0.capacity) := by
      apply Fin.ext
      rfl
    have hlow : (cendInitialPERegisters x).lm0 (PEMemory.advance PEMemory.Bank.lm0
        (⟨0, by decide⟩ : Fin PEMemory.Bank.lm0.capacity) 1) = x.extractLsb' 0 32 := by
      rw [hadvance]
      rfl
    rw [hhigh, hlow, BitVec.extractLsb'_append_extractLsb']
    simp [cendInitialBuses]
  · have hlt : start.val < 4096 := start.isLt
    have hval : start.val + 1 ≤ 4095 := by omega
    have hstart : (cendInitialPERegisters x).lm0 start = 0 := by
      rw [cendInitialLm0Word]
      simp only [h0, if_false]
      have hne : ¬ start.val = 1 := by
        intro hone
        rw [hone] at aligned
        exact absurd aligned (by decide)
      simp [hne]
    have hadvanceval : (PEMemory.advance PEMemory.Bank.lm0 start 1).val = start.val + 1 := by
      rw [cendAdvanceLm0Val]
      show (start.val + 1) % 4096 = start.val + 1
      exact Nat.mod_eq_of_lt (by omega)
    have hnext : (cendInitialPERegisters x).lm0 (PEMemory.advance PEMemory.Bank.lm0 start 1) = 0 := by
      rw [cendInitialLm0Word]
      simp only [hadvanceval]
      have hne0 : ¬ start.val + 1 = 0 := by omega
      have hne1 : ¬ start.val + 1 = 1 := by omega
      simp [h0, hne0, hne1, if_false, ite_false]
    rw [hstart, hnext]
    simp [cendInitialBuses, cendZeroBus]


theorem cendMemoryBus_mem_lm0_word (x : BitVec 64) (start : Fin PEMemory.Bank.lm0.capacity) :
    PEMemory.pack (readRegisterBank (cendInitialPERegisters x) PEMemory.Bank.lm0
      PEMemory.Width.word start) ∈ cendInitialBuses x := by
  have shape : PEMemory.pack (readRegisterBank (cendInitialPERegisters x) PEMemory.Bank.lm0
      PEMemory.Width.word start) =
      (⟨(cendInitialPERegisters x).lm0 start ++ (0 : BitVec 32), 0⟩ : IntegerALU.Bus) := by
    simp [readRegisterBank, PEMemory.readWords, PEMemory.count, PEMemory.Width.words,
      PEMemory.pack, PEMemory.advance, Nat.mod_eq_of_lt start.isLt]
  rw [shape]
  by_cases h0 : start.val = 0
  · have h : (cendInitialPERegisters x).lm0 start = x.extractLsb' 32 32 := by
      rw [cendInitialLm0Word]; rw [if_pos h0]
    rw [h]
    simp [cendInitialBuses]
  · by_cases h1 : start.val = 1
    · have h : (cendInitialPERegisters x).lm0 start = x.extractLsb' 0 32 := by
        rw [cendInitialLm0Word]; rw [if_neg h0, if_pos h1]
      rw [h]
      simp [cendInitialBuses]
    · have h : (cendInitialPERegisters x).lm0 start = 0 := by
        rw [cendInitialLm0Word]; rw [if_neg h0, if_neg h1]
      rw [h]
      simp [cendInitialBuses, cendZeroBus]

theorem cendMemoryBus_mem_lm0_double (x : BitVec 64) (start : Fin PEMemory.Bank.lm0.capacity)
    (aligned : start.val % 4 = 0) :
    PEMemory.pack (readRegisterBank (cendInitialPERegisters x) PEMemory.Bank.lm0
      PEMemory.Width.double start) ∈ cendInitialBuses x := by
  have shape : PEMemory.pack (readRegisterBank (cendInitialPERegisters x) PEMemory.Bank.lm0
      PEMemory.Width.double start) =
      (⟨(cendInitialPERegisters x).lm0 start ++
          (cendInitialPERegisters x).lm0 (PEMemory.advance PEMemory.Bank.lm0 start 1),
        (cendInitialPERegisters x).lm0 (PEMemory.advance PEMemory.Bank.lm0 start 2) ++
          (cendInitialPERegisters x).lm0 (PEMemory.advance PEMemory.Bank.lm0 start 3)⟩ :
        IntegerALU.Bus) := by
    simp [readRegisterBank, PEMemory.readWords, PEMemory.count, PEMemory.Width.words,
      PEMemory.pack, PEMemory.advance, Nat.mod_eq_of_lt start.isLt]
  rw [shape]
  by_cases h0 : start.val = 0
  · have hstart : start = (⟨0, by decide⟩ : Fin PEMemory.Bank.lm0.capacity) := Fin.ext h0
    subst hstart
    have hone : (PEMemory.advance PEMemory.Bank.lm0
        (⟨0, by decide⟩ : Fin PEMemory.Bank.lm0.capacity) 1) =
        (⟨1, by decide⟩ : Fin PEMemory.Bank.lm0.capacity) := by apply Fin.ext; rfl
    have htwo : (PEMemory.advance PEMemory.Bank.lm0
        (⟨0, by decide⟩ : Fin PEMemory.Bank.lm0.capacity) 2) =
        (⟨2, by decide⟩ : Fin PEMemory.Bank.lm0.capacity) := by apply Fin.ext; rfl
    have hthree : (PEMemory.advance PEMemory.Bank.lm0
        (⟨0, by decide⟩ : Fin PEMemory.Bank.lm0.capacity) 3) =
        (⟨3, by decide⟩ : Fin PEMemory.Bank.lm0.capacity) := by apply Fin.ext; rfl
    rw [hone, htwo, hthree]
    have hm0 : (cendInitialPERegisters x).lm0 (⟨0, by decide⟩ : Fin PEMemory.Bank.lm0.capacity) =
        x.extractLsb' 32 32 := rfl
    have hm1 : (cendInitialPERegisters x).lm0 (⟨1, by decide⟩ : Fin PEMemory.Bank.lm0.capacity) =
        x.extractLsb' 0 32 := rfl
    have hm2 : (cendInitialPERegisters x).lm0 (⟨2, by decide⟩ : Fin PEMemory.Bank.lm0.capacity) =
        0 := rfl
    have hm3 : (cendInitialPERegisters x).lm0 (⟨3, by decide⟩ : Fin PEMemory.Bank.lm0.capacity) =
        0 := rfl
    rw [hm0, hm1, hm2, hm3, BitVec.extractLsb'_append_extractLsb']
    simp [cendInitialBuses, cendZeroBus]
  · have hcap : start.val < 4096 := start.isLt
    have hge : 4 ≤ start.val := by
      have := start.isLt
      omega
    have hword : ∀ offset : Nat, offset < 4 → (PEMemory.advance PEMemory.Bank.lm0 start offset).val =
        start.val + offset := by
      intro offset hoff
      rw [cendAdvanceLm0Val]
      show (start.val + offset) % 4096 = start.val + offset
      exact Nat.mod_eq_of_lt (by omega)
    have hzero : ∀ offset : Nat, offset < 4 →
        (cendInitialPERegisters x).lm0 (PEMemory.advance PEMemory.Bank.lm0 start offset) = 0 := by
      intro offset hoff
      rw [cendInitialLm0Word, hword offset hoff]
      have hne0 : ¬ start.val + offset = 0 := by omega
      have hne1 : ¬ start.val + offset = 1 := by omega
      rw [if_neg hne0, if_neg hne1]
    have hzeroStart : (cendInitialPERegisters x).lm0 start = 0 := by
      rw [cendInitialLm0Word]
      rw [if_neg h0]
      have hne1 : ¬ start.val = 1 := by omega
      rw [if_neg hne1]
    rw [hzeroStart, hzero 1 (by decide), hzero 2 (by decide), hzero 3 (by decide)]
    simp [cendInitialBuses, cendZeroBus]

theorem cendMemoryBus_mem_other (x : BitVec 64) (bank : PEMemory.Bank) (width : PEMemory.Width)
    (start : Fin bank.capacity) (hbank : bank ≠ PEMemory.Bank.lm0) :
    PEMemory.pack (readRegisterBank (cendInitialPERegisters x) bank width start) ∈
      cendInitialBuses x := by
  cases bank with
  | lm0 => exact absurd rfl hbank
  | lm1 =>
      simp [readRegisterBank, PEMemory.readWords, cendInitialPERegisters,
        zeroInitialPERegisterFiles, PEMemory.pack, cendInitialBuses, cendZeroBus]
  | grf0 =>
      simp [readRegisterBank, PEMemory.readWords, cendInitialPERegisters,
        zeroInitialPERegisterFiles, PEMemory.pack, cendInitialBuses, cendZeroBus]
  | grf1 =>
      simp [readRegisterBank, PEMemory.readWords, cendInitialPERegisters,
        zeroInitialPERegisterFiles, PEMemory.pack, cendInitialBuses, cendZeroBus]
  | t =>
      simp [readRegisterBank, PEMemory.readWords, cendInitialPERegisters,
        zeroInitialPERegisterFiles, PEMemory.pack, cendInitialBuses, cendZeroBus]

/-- **Every aligned memory source bus at the initial state is in the family.** -/
theorem cendMemoryBus_mem (x : BitVec 64) (bank : PEMemory.Bank) (width : PEMemory.Width)
    (start : Fin bank.capacity)
    (aligned : start.val % PEMemory.count bank width = 0) :
    PEMemory.pack (readRegisterBank (cendInitialPERegisters x) bank width start) ∈
      cendInitialBuses x := by
  cases bank with
  | lm0 =>
      cases width with
      | word => exact cendMemoryBus_mem_lm0_word x start
      | long => exact cendMemoryBus_mem_lm0_long x start aligned
      | double => exact cendMemoryBus_mem_lm0_double x start aligned
  | lm1 => exact cendMemoryBus_mem_other x .lm1 width start (by decide)
  | grf0 => exact cendMemoryBus_mem_other x .grf0 width start (by decide)
  | grf1 => exact cendMemoryBus_mem_other x .grf1 width start (by decide)
  | t => exact cendMemoryBus_mem_other x .t width start (by decide)


/-! ## 10. Trust report -/

#print axioms cendDatapathWords_avoid_high
#print axioms cendDatapathWords_avoid_low
#print axioms cendLm1Witness_target_high
#print axioms cend_not_correct_of_word0_ne
#print axioms cend_not_correct_of_word1_ne
#print axioms cend_not_correct_of_word0Obligation
#print axioms cend_not_correct_of_word1Obligation
#print axioms cendPlainALUBothHalvesRefutedLm1_of_wordObligation
#print axioms cendPE_not_correct_of_inputIndependentPair
#print axioms cendFixedBus_mem
#print axioms cendInitialForwardingSlots_poison
#print axioms cendMemoryBus_mem
#print axioms cendLm1PassaLine_witness
#print axioms cendLm1ComposeLine_witness

