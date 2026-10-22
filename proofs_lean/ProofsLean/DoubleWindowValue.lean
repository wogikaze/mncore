import ProofsLean.ABWidthBound
import ProofsLean.WelcomeValueBound
import ProofsLean.WelcomeBoundTwo
import ProofsLean.WelcomeProvenance
import ProofsLean.ValueProvenance
import ProofsLean.BusLayout

/-! # The `.double` window at `A = 0, B = 1.0`: data words `2, 3` are never the target

`ProofsLean/ABWidthBound.lean` proves that one `.lm1 .double` destination writes
sixteen words (`4 * 4`), so the "total width below `16` leaves a word untouched"
kernel cannot refute a `.double` line, and `ab_not_correct_of_lm1WidthNotDouble`
closes every non-`.double` family.  This module closes the remaining *value*
half of the `.double` case at the second witness input of `1.a-b`,
`A = 0, B = 1.0`, whose target is the bit pattern of `-1.0`
(`0xBF800000`) in every observed word.

## The argument

A `.lm1 .double` store writes four data-bus words starting at its destination
address (`PEMemory.writeWordsMasked`), and `commitParsedMaskedWrites` folds those
stores over the initial PE file.  At the witness input every *initial* register
word is either `0` (LM0 words `0..15`, LM1, GRF, T) or the input `B = 1.0`
(LM0 words `16..31`), and the PE-0 `.fixed` constants are `0` or an `.msb1`
replication.  For an integer-ALU store the low long word of the result is the
first operand's low long word, or zero (`IntegerALU.evaluateBus`), and a
half-precision rounding of a bus *zeroes* bus words `2, 3`
(`roundSingleWordBusToHalf`).  Hence bus words `2` and `3` of any prepared
integer-ALU write at the witness input lie in the four-word set
`ABWitnessDataWord` and are never `0xBF800000`.

The geometry is even simpler than the "four windows `0, 4, 8, 12`" count: a
`.double` destination address is 4-word aligned, so the data index of an
observed word `t < 16` covered by a write at address `a` is forced:
`distance a t = t % 4` and `a = 4 * (t / 4)`.  In particular every covered word
whose index is `2` or `3` mod `4` — the eight addresses
`2, 3, 6, 7, 10, 11, 14, 15` — is written from data word `2` or `3`
(`doubleWindow_index_forced`, `doubleWindow_eight_low_words`), and the four
covering 4-aligned windows are forced to be exactly `{0, 4, 8, 12}`
(`doubleWindow_four_windows_forced`).

## What is proved here

* `ABWitnessDataWord` and its closure and non-target lemmas
  (`abWitnessDataWord_ne_target`, `abWitnessDataWord_and_wordMask`,
  `abWitnessDataWord_merge`);
* the **initial-read lemma** at the witness input:
  `abZeroRight_readDirectAccess_safe` — every word read from *any* bank, width,
  address and bus index of the initial PE file is `0` or `1.0`; and
  `fixedValue_two` / `fixedValue_three` — the two low bus words of every PE-0
  `.fixed` constant are `0`, `0x80000000` or `0x80008000`, hence never the
  target;
* the **data-path lemmas**: `pack_low_two` / `pack_low_three` (bus words `2, 3`
  are the low long word), `evaluateBus_low_two_safe` (the result's low long word
  is the first operand's or zero), `parsedOutputAfterFlush_two_safe`
  (a flush only ANDs with a full-word mask) and `unpackALUBus_two_safe` /
  `unpackALUBus_three_safe`;
* the **per-prepared-write lemma**
  `prepareParsedMaskedWriteWithForwarding_data_two_three_safe`: if the two
  operand buses of an integer-request ALU write have witness low words, then
  its data words `2` and `3` do.  `abZeroRight_memoryWrite_data_two_three_safe`
  discharges the operand buses for direct memory reads at the witness input,
  `abZeroRight_fixedWrite_data_two_three_safe` for PE-0 `.fixed` operands, and
  `abZeroRight_preparedWrite_data_two_three_safe` (with
  `abZeroRight_readWithForwarding_two_three_safe`) for **any** source shape
  that is a memory read or a PE-0 `.fixed` constant — the "every source operand
  and cycle" form.  `abZeroRight_preparedWrite_data_two_three_ne_target` states
  the target form: the low long word of such a write is never `0xBF800000`;
* the **window forcing** (`doubleWindow_index_forced`,
  `doubleWindow_four_windows_forced`, `doubleWindow_eight_low_words`);
* the **commit kernel** `commitParsedMaskedWrites_lm1_word_ne_target`:
  a commit over a list whose `.lm1 .double` writes at aligned addresses store
  non-target data words `2, 3` never produces the target word;
* the **`.double` refutation at the witness input**
  `abZeroRight_doubleWindow_refutes` and its `¬ Correct` corollary
  `ab_not_correct_of_lm1DoubleWindow`, including the task's "all `.lm1` writes
  are `.double`" form;
* the **composition** `abPE_incorrect_at_one_of_two_witnesses`: a one-line
  `.pe` program whose left witness file has a non-`.double` static width, or
  whose right witness file is an aligned covering write list with safe data
  words, is incorrect at `A = 1.0, B = 0` or at `A = 0, B = 1.0`
  (`abOneLeft_refutes_of_lm1WidthNotDouble` recomputes the left half of
  `ab_not_correct_of_lm1WidthNotDouble` in the `Refutes` form).

## The residual

The data-safety hypothesis `Lm1WritesDataSafe` is *not* free for every family.
The per-write lemma above covers prepared writes whose two operand buses are
direct memory reads, PE-0 `.fixed` constants, or any buses with witness low
words (rounded sources included).  The exact obligations still outside this
module are:

* `.forward` sources: `ParsedIntegerInput.readWithForwarding` can return a bus
  from the forwarding slots, whose low long word is a copy of an earlier read
  or `0`; the forwarding-chain invariant needed to iterate the per-write lemma
  over the four cycles is not proved here;
* non-integer producers (`.mau`, relu, block float, `.matrixRead`, `.l1bm`):
  their buses are `doubleMAUVectorBus`-shaped, whose low long word is `0`, and
  `.matrixRead`/L1BM data is block memory (initially `0`); the family lemmas are
  not restated here;
* one genuine exception to "bus words `2, 3` are never the target": an
  `.immediate payload` operand with `payload = 0xBF800000` puts the target on
  bus words `2, 3` directly (`evaluateParsedExecutionRequest .immediate`).
  Such a line is *correct* on that word at `A = 0, B = 1.0` — it writes
  `-1.0` — but at `A = 1.0, B = 0` the same write is `-1.0` against the target
  `1.0`, so it is still refuted at the *other* witness.  That value comparison
  is not formalised here; it is the only case in which the `.double` kernel's
  right-witness premise fails.  Formally, the missing piece is the statement
  `evaluateParsedExecutionRequest (.immediate payload sparse) x y reduced`'s
  low words at `payload = 0xBF800000` together with the left-witness value
  comparison (the committed word is a payload repeated, versus the target
  `0x3F800000`);
* the destination projection of a line's prepared writes through the dependent
  ALU match (the hypothesis `committed` in the kernels) is the subject of
  `ProofsLean/ALURequestProvenance.lean`; this module deliberately takes the
  projection as a hypothesis, so that agent's result composes with
  `ab_not_correct_of_lm1DoubleWindow` and
  `abPE_incorrect_at_one_of_two_witnesses` unchanged.  The same module supplies
  the per-opcode `executionRequest` facts (`alu_inc_i_executionRequest`,
  `alu_add_l_executionRequest`, …) that discharge the `request` hypothesis of
  `prepareParsedMaskedWriteWithForwarding_data_two_three_safe` for a concrete
  ALU row, so the two halves meet at exactly that hypothesis.

Finally, `abWidthDouble_witness_data_two_three` is a kernel check on the exact
line of `ProofsLean/ABWidthBound.lean` that defeats the width bound: prepared at
the witness input, its four `.double` writes all carry `0` on data words `2` and
`3`, so the eight words `2, 3, 6, 7, 10, 11, 14, 15` are `0` against the target
`-1.0`.

Concretely, to obtain an unconditional `¬ Correct` for every one-line `.pe`
program from `abPE_incorrect_at_one_of_two_witnesses` one must supply, for the
line's PE-0 write lists at the two witness inputs: the width/count data
(`leftCount`, `leftWidths`, already available per family in the tree), the
4-word alignment of every `.lm1` destination, the coverage of the sixteen
observed words, and `Lm1WritesDataSafe`.  Alignment and coverage are properties
of the line's destination geometry; `Lm1WritesDataSafe` is the data fact
discharged above for memory and `.fixed` operands and left as stated for
`.forward` sources and the non-integer producers.

No `sorry`, no `admit`, no `native_decide`, no new axioms, and no existing
module is edited by this file.
-/

namespace ProofsLean.MNCore

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false

open Issue
open PEMemory

/-! ## 1. The witness data-word set -/

/-- The 32-bit words that can reach the data bus of a prepared integer write at
the witness input `A = 0, B = 1.0`, PE 0: the initial register words `0` and
`0x3F800000` (the input `B`), and the two `.fixed .msb1` shapes produced by the
PE-0 fixed constants.  None of them is the target `-1.0 = 0xBF800000`. -/
def ABWitnessDataWord (w : BitVec 32) : Prop :=
  w = 0 ∨ w = 0x3F800000 ∨ w = 0x80000000 ∨ w = 0x80008000

theorem abWitnessDataWord_zero : ABWitnessDataWord 0 := Or.inl rfl

theorem abWitnessDataWord_one : ABWitnessDataWord 0x3F800000 :=
  Or.inr (Or.inl rfl)

theorem abWitnessDataWord_msb1_word : ABWitnessDataWord 0x80000000 :=
  Or.inr (Or.inr (Or.inl rfl))

theorem abWitnessDataWord_msb1_half : ABWitnessDataWord 0x80008000 :=
  Or.inr (Or.inr (Or.inr rfl))

/-- No witness data word is the target `-1.0`. -/
theorem abWitnessDataWord_ne_target (w : BitVec 32) (safe : ABWitnessDataWord w) :
    w ≠ 0xBF800000 := by
  rcases safe with same | same | same | same <;> subst same <;> decide

theorem and_wordMask_false (w : BitVec 32) :
    w &&& ProofsLean.MNCore.Masks.wordMask false = 0 := by
  show w &&& 0#32 = 0
  exact BitVec.and_zero

theorem and_wordMask_true (w : BitVec 32) :
    w &&& ProofsLean.MNCore.Masks.wordMask true = w := by
  show w &&& BitVec.allOnes 32 = w
  exact BitVec.and_allOnes

/-- A witness data word stays a witness data word under a full-word mask. -/
theorem abWitnessDataWord_and_wordMask (w : BitVec 32) (flag : Bool)
    (safe : ABWitnessDataWord w) :
    ABWitnessDataWord (w &&& ProofsLean.MNCore.Masks.wordMask flag) := by
  cases flag
  · rw [and_wordMask_false]
    exact abWitnessDataWord_zero
  · rw [and_wordMask_true]
    exact safe

theorem wordMask_zero_or_allOnes (flag : Bool) :
    ProofsLean.MNCore.Masks.wordMask flag = 0 ∨
      ProofsLean.MNCore.Masks.wordMask flag = BitVec.allOnes 32 := by
  cases flag
  · left
    show (0#32 : BitVec 32) = 0
    rfl
  · right
    show (BitVec.allOnes 32 : BitVec 32) = BitVec.allOnes 32
    rfl

theorem mergeSelectedWord_zero (old new : BitVec 32) :
    mergeSelectedWord old new 0 = old := by
  show (old &&& BitVec.allOnes 32) ||| (new &&& 0#32) = old
  rw [BitVec.and_allOnes, BitVec.and_zero, BitVec.or_zero]

/-- A masked merge with a mask that is either zero or all ones keeps the
witness data-word set. -/
theorem abWitnessDataWord_merge (old new enable : BitVec 32)
    (mask : enable = 0 ∨ enable = BitVec.allOnes 32)
    (oldSafe : ABWitnessDataWord old) (newSafe : ABWitnessDataWord new) :
    ABWitnessDataWord (mergeSelectedWord old new enable) := by
  rcases mask with same | same
  · rw [same, mergeSelectedWord_zero]
    exact oldSafe
  · rw [same, mergeSelectedWord_allOnes]
    exact newSafe

/-! ## 2. Initial register words at the witness input -/

/-- At `A = 0, B = 1.0` the initial LM0 of every PE holds `0` in words `0..15`
(the minuend `A`) and `1.0` in words `16..31` (the subtrahend `B`). -/
theorem abZeroRight_initial_lm0 (address : Fin PEMemory.Bank.lm0.capacity) :
    (abInitialPERegisters abZeroRightInput).lm0 address =
      if address.val < 16 then 0
      else if address.val < 32 then 0x3F800000 else 0 := by
  unfold abInitialPERegisters abInitialLm0 abZeroRightInput abZeroWords abOneWords
  by_cases small : address.val < 16
  · simp [small]
  · by_cases medium : address.val < 32
    · simp [small, medium]
    · simp [small, medium]

theorem abZeroRight_initial_lm0_safe (address : Fin PEMemory.Bank.lm0.capacity) :
    ABWitnessDataWord ((abInitialPERegisters abZeroRightInput).lm0 address) := by
  rw [abZeroRight_initial_lm0]
  split
  · exact abWitnessDataWord_zero
  · split
    · exact abWitnessDataWord_one
    · exact abWitnessDataWord_zero

theorem abZeroRight_initial_lm1_safe (address : Fin PEMemory.Bank.lm1.capacity) :
    ABWitnessDataWord ((abInitialPERegisters abZeroRightInput).lm1 address) :=
  abWitnessDataWord_zero

theorem abZeroRight_initial_grf0_safe (address : Fin PEMemory.Bank.grf0.capacity) :
    ABWitnessDataWord ((abInitialPERegisters abZeroRightInput).grf0 address) :=
  abWitnessDataWord_zero

theorem abZeroRight_initial_grf1_safe (address : Fin PEMemory.Bank.grf1.capacity) :
    ABWitnessDataWord ((abInitialPERegisters abZeroRightInput).grf1 address) :=
  abWitnessDataWord_zero

theorem abZeroRight_initial_t_safe (address : Fin PEMemory.Bank.t.capacity) :
    ABWitnessDataWord ((abInitialPERegisters abZeroRightInput).t address) :=
  abWitnessDataWord_zero

/-- Every word read from a memory whose words are all witness data words is a
witness data word: narrow reads zero the unused bus words. -/
theorem abZeroRight_readWords_safe (bank : PEMemory.Bank) (width : PEMemory.Width)
    (memory : Memory bank) (start : Fin bank.capacity) (index : Fin 4)
    (safe : ∀ target, ABWitnessDataWord (memory target)) :
    ABWitnessDataWord (readWords bank width memory start index) := by
  rw [readWords]
  split
  · exact safe _
  · exact abWitnessDataWord_zero

theorem abZeroRight_readRegisterBank_safe (bank : PEMemory.Bank) (width : PEMemory.Width)
    (address : Fin bank.capacity) (index : Fin 4) :
    ABWitnessDataWord (readRegisterBank (abInitialPERegisters abZeroRightInput)
      bank width address index) := by
  cases bank with
  | lm0 => exact abZeroRight_readWords_safe _ _ _ _ _ abZeroRight_initial_lm0_safe
  | lm1 => exact abZeroRight_readWords_safe _ _ _ _ _ abZeroRight_initial_lm1_safe
  | grf0 => exact abZeroRight_readWords_safe _ _ _ _ _ abZeroRight_initial_grf0_safe
  | grf1 => exact abZeroRight_readWords_safe _ _ _ _ _ abZeroRight_initial_grf1_safe
  | t => exact abZeroRight_readWords_safe _ _ _ _ _ abZeroRight_initial_t_safe

/-- **The generic initial-read lemma.**  At `A = 0, B = 1.0` every word of every
direct register-bank read — any bank, width, address and bus index — is `0` or
`1.0`. -/
theorem abZeroRight_readDirectAccess_safe (access : DirectMemoryAccess) (index : Fin 4) :
    ABWitnessDataWord (readDirectAccess (abInitialPERegisters abZeroRightInput)
      access index) :=
  abZeroRight_readRegisterBank_safe access.bank access.width access.address index

/-! ## 3. The low long word of a prepared integer write -/

theorem pack_low_two (data : WordBus) (bound : 2 < 4) :
    (pack data).low.extractLsb' 32 32 = data ⟨2, bound⟩ := by
  have h : (⟨2, by decide⟩ : Fin 4) = ⟨2, bound⟩ := Fin.ext rfl
  rw [← h]
  show BitVec.extractLsb' 32 32 (data ⟨2, by decide⟩ ++ data ⟨3, by decide⟩) =
    data ⟨2, by decide⟩
  rw [BitVec.extractLsb'_append_eq_left]

theorem pack_low_three (data : WordBus) (bound : 3 < 4) :
    (pack data).low.extractLsb' 0 32 = data ⟨3, bound⟩ := by
  have h : (⟨3, by decide⟩ : Fin 4) = ⟨3, bound⟩ := Fin.ext rfl
  rw [← h]
  show BitVec.extractLsb' 0 32 (data ⟨2, by decide⟩ ++ data ⟨3, by decide⟩) =
    data ⟨3, by decide⟩
  rw [BitVec.extractLsb'_append_eq_right]

/-- A half-precision rounding of a packed bus zeroes its low long word: the
rounding only populates bus words `0` and `1`. -/
theorem applyRounding_true_pack_low (data : WordBus) :
    (ParsedIntegerInput.applyRounding true (pack data)).low = 0 := by
  simp [ParsedIntegerInput.applyRounding, roundSingleInputBusToHalf,
    roundSingleWordBusToHalf, pack]

/-- A rounded or unrounded packed read with witness bus words `2, 3` has a
witness low long word. -/
theorem applyRounding_pack_two_safe (rounded : Bool) (data : WordBus)
    (safe : ABWitnessDataWord (data ⟨2, by decide⟩)) :
    ABWitnessDataWord
      ((ParsedIntegerInput.applyRounding rounded (pack data)).low.extractLsb' 32 32) := by
  cases rounded with
  | false =>
      show ABWitnessDataWord (BitVec.extractLsb' 32 32 (data ⟨2, by decide⟩ ++ data ⟨3, by decide⟩))
      rw [BitVec.extractLsb'_append_eq_left]
      exact safe
  | true =>
      rw [applyRounding_true_pack_low]
      show ABWitnessDataWord (BitVec.extractLsb' 32 32 (0 : BitVec 64))
      exact abWitnessDataWord_zero

theorem applyRounding_pack_three_safe (rounded : Bool) (data : WordBus)
    (safe : ABWitnessDataWord (data ⟨3, by decide⟩)) :
    ABWitnessDataWord
      ((ParsedIntegerInput.applyRounding rounded (pack data)).low.extractLsb' 0 32) := by
  cases rounded with
  | false =>
      show ABWitnessDataWord (BitVec.extractLsb' 0 32 (data ⟨2, by decide⟩ ++ data ⟨3, by decide⟩))
      rw [BitVec.extractLsb'_append_eq_right]
      exact safe
  | true =>
      rw [applyRounding_true_pack_low]
      show ABWitnessDataWord (BitVec.extractLsb' 0 32 (0 : BitVec 64))
      exact abWitnessDataWord_zero

/-- The low long word of an evaluated integer bus is the first operand's, or
zero when the first operand is precision-reduced (and also for `.passa`). -/
theorem evaluateBus_low_two_safe (p : IntegerALU.Precision) (op : IntegerALU.Op)
    (x y : IntegerALU.Bus) (reduced : Bool)
    (safe : ABWitnessDataWord (x.low.extractLsb' 32 32)) :
    ABWitnessDataWord
      ((IntegerALU.evaluateBus p op x y reduced).value.low.extractLsb' 32 32) := by
  rw [evaluateBus_value_low]
  split
  · exact safe
  · split
    · show ABWitnessDataWord (BitVec.extractLsb' 32 32 (0 : BitVec 64))
      exact abWitnessDataWord_zero
    · exact safe

theorem evaluateBus_low_three_safe (p : IntegerALU.Precision) (op : IntegerALU.Op)
    (x y : IntegerALU.Bus) (reduced : Bool)
    (safe : ABWitnessDataWord (x.low.extractLsb' 0 32)) :
    ABWitnessDataWord
      ((IntegerALU.evaluateBus p op x y reduced).value.low.extractLsb' 0 32) := by
  rw [evaluateBus_value_low]
  split
  · exact safe
  · split
    · show ABWitnessDataWord (BitVec.extractLsb' 0 32 (0 : BitVec 64))
      exact abWitnessDataWord_zero
    · exact safe

theorem flushBus_long_low (flags : BitVec 4) (data : IntegerALU.Bus) :
    (ProofsLean.MNCore.Masks.flushBus .long flags data).low = data.low := by
  show data.low &&& (BitVec.allOnes 64 : BitVec 64) = data.low
  exact BitVec.and_allOnes

theorem flushBus_double_two (flags : BitVec 4) (data : IntegerALU.Bus) :
    (ProofsLean.MNCore.Masks.flushBus .double flags data).low.extractLsb' 32 32 =
      data.low.extractLsb' 32 32 &&&
        ProofsLean.MNCore.Masks.wordMask (flags.getLsbD 1) := by
  simp only [ProofsLean.MNCore.Masks.flushBus]
  rw [BitVec.extractLsb'_and]
  rw [show (ProofsLean.MNCore.Masks.doubleMask flags).low.extractLsb' 32 32 =
      ProofsLean.MNCore.Masks.wordMask (flags.getLsbD 1) from by
    simp only [ProofsLean.MNCore.Masks.doubleMask]
    rw [BitVec.extractLsb'_append_eq_left]]

theorem flushBus_double_three (flags : BitVec 4) (data : IntegerALU.Bus) :
    (ProofsLean.MNCore.Masks.flushBus .double flags data).low.extractLsb' 0 32 =
      data.low.extractLsb' 0 32 &&&
        ProofsLean.MNCore.Masks.wordMask (flags.getLsbD 0) := by
  simp only [ProofsLean.MNCore.Masks.flushBus]
  rw [BitVec.extractLsb'_and]
  rw [show (ProofsLean.MNCore.Masks.doubleMask flags).low.extractLsb' 0 32 =
      ProofsLean.MNCore.Masks.wordMask (flags.getLsbD 0) from by
    simp only [ProofsLean.MNCore.Masks.doubleMask]
    rw [BitVec.extractLsb'_append_eq_right]]

/-- A flush keeps witness low words: it ANDs each 32-bit word with a mask that
is either zero or all ones. -/
theorem parsedOutputAfterFlush_two_safe (selection : Option PEWordSelection)
    (output : IntegerALU.Bus)
    (safeTwo : ABWitnessDataWord (output.low.extractLsb' 32 32))
    (safeThree : ABWitnessDataWord (output.low.extractLsb' 0 32)) :
    ABWitnessDataWord ((parsedOutputAfterFlush selection output).low.extractLsb' 32 32) ∧
      ABWitnessDataWord ((parsedOutputAfterFlush selection output).low.extractLsb' 0 32) := by
  cases selection with
  | none => exact ⟨safeTwo, safeThree⟩
  | some selected =>
      cases longLong : selected.longLong
      · have isLong : (if selected.longLong then
            ProofsLean.MNCore.Masks.Width.double
          else ProofsLean.MNCore.Masks.Width.long) =
            ProofsLean.MNCore.Masks.Width.long := by simp [longLong]
        constructor
        · rw [parsedOutputAfterFlush, isLong, flushBus_long_low]
          exact safeTwo
        · rw [parsedOutputAfterFlush, isLong, flushBus_long_low]
          exact safeThree
      · have isDouble : (if selected.longLong then
            ProofsLean.MNCore.Masks.Width.double
          else ProofsLean.MNCore.Masks.Width.long) =
            ProofsLean.MNCore.Masks.Width.double := by simp [longLong]
        constructor
        · rw [parsedOutputAfterFlush, isDouble, flushBus_double_two]
          exact abWitnessDataWord_and_wordMask _ _ safeTwo
        · rw [parsedOutputAfterFlush, isDouble, flushBus_double_three]
          exact abWitnessDataWord_and_wordMask _ _ safeThree

theorem unpackALUBus_two_safe (bus : IntegerALU.Bus) (bound : 2 < 4)
    (safe : ABWitnessDataWord (bus.low.extractLsb' 32 32)) :
    ABWitnessDataWord (unpackALUBus bus ⟨2, bound⟩) := by
  rw [unpackALUBus_of_val_eq_two bus ⟨2, bound⟩ rfl]
  exact safe

theorem unpackALUBus_three_safe (bus : IntegerALU.Bus) (bound : 3 < 4)
    (safe : ABWitnessDataWord (bus.low.extractLsb' 0 32)) :
    ABWitnessDataWord (unpackALUBus bus ⟨3, bound⟩) := by
  rw [unpackALUBus_of_val_eq_three bus ⟨3, bound⟩ rfl]
  exact safe

/-! ## 4. The `.fixed` constants at PE 0 are small -/

theorem fixedValue_zero_two (precision : IntegerALU.Precision) :
    ABWitnessDataWord ((replicateIntegerLane precision 0).low.extractLsb' 32 32) := by
  cases precision <;> unfold ABWitnessDataWord <;> decide

theorem fixedValue_zero_three (precision : IntegerALU.Precision) :
    ABWitnessDataWord ((replicateIntegerLane precision 0).low.extractLsb' 0 32) := by
  cases precision <;> unfold ABWitnessDataWord <;> decide

theorem fixedValue_msb_two (precision : IntegerALU.Precision) :
    ABWitnessDataWord ((replicateIntegerLane precision
      (2 ^ (precision.width - 1))).low.extractLsb' 32 32) := by
  cases precision <;> unfold ABWitnessDataWord <;> decide

theorem fixedValue_msb_three (precision : IntegerALU.Precision) :
    ABWitnessDataWord ((replicateIntegerLane precision
      (2 ^ (precision.width - 1))).low.extractLsb' 0 32) := by
  cases precision <;> unfold ABWitnessDataWord <;> decide

/-- **The `.fixed` low words at PE 0.**  Every `.fixed` constant lowered at
`PE 0` is `0` or an `.msb1` replication, whose low bus words `2` and `3` are
`0`, `0x80000000` or `0x80008000` — never the target. -/
theorem fixedValue_two (fixed : ParsedFixed) (precision : IntegerALU.Precision) :
    ABWitnessDataWord ((replicateIntegerLane precision
      (ParsedFixed.integerValue fixed precision
        (ParsedIntegerContext.ofLinearIndex welcomePE).group
        (ParsedIntegerContext.ofLinearIndex welcomePE).l2b
        (ParsedIntegerContext.ofLinearIndex welcomePE).l1b
        (ParsedIntegerContext.ofLinearIndex welcomePE).mab
        (ParsedIntegerContext.ofLinearIndex welcomePE).pe)).low.extractLsb' 32 32) := by
  rw [welcomeFixedValue]
  cases fixed
  · exact fixedValue_zero_two precision
  · exact fixedValue_zero_two precision
  · exact fixedValue_zero_two precision
  · exact fixedValue_zero_two precision
  · exact fixedValue_zero_two precision
  · exact fixedValue_msb_two precision

theorem fixedValue_three (fixed : ParsedFixed) (precision : IntegerALU.Precision) :
    ABWitnessDataWord ((replicateIntegerLane precision
      (ParsedFixed.integerValue fixed precision
        (ParsedIntegerContext.ofLinearIndex welcomePE).group
        (ParsedIntegerContext.ofLinearIndex welcomePE).l2b
        (ParsedIntegerContext.ofLinearIndex welcomePE).l1b
        (ParsedIntegerContext.ofLinearIndex welcomePE).mab
        (ParsedIntegerContext.ofLinearIndex welcomePE).pe)).low.extractLsb' 0 32) := by
  rw [welcomeFixedValue]
  cases fixed
  · exact fixedValue_zero_three precision
  · exact fixedValue_zero_three precision
  · exact fixedValue_zero_three precision
  · exact fixedValue_zero_three precision
  · exact fixedValue_zero_three precision
  · exact fixedValue_msb_three precision

/-- A `.fixed` bus whose lowered value is the PE-0 replication is witness-safe in
both low bus words. -/
theorem fixedBus_two_three_safe (fixed : ParsedFixed) (precision : IntegerALU.Precision) :
    ABWitnessDataWord ((replicateIntegerLane precision
        (ParsedFixed.integerValue fixed precision
          (ParsedIntegerContext.ofLinearIndex welcomePE).group
          (ParsedIntegerContext.ofLinearIndex welcomePE).l2b
          (ParsedIntegerContext.ofLinearIndex welcomePE).l1b
          (ParsedIntegerContext.ofLinearIndex welcomePE).mab
          (ParsedIntegerContext.ofLinearIndex welcomePE).pe)).low.extractLsb' 32 32) ∧
      ABWitnessDataWord ((replicateIntegerLane precision
        (ParsedFixed.integerValue fixed precision
          (ParsedIntegerContext.ofLinearIndex welcomePE).group
          (ParsedIntegerContext.ofLinearIndex welcomePE).l2b
          (ParsedIntegerContext.ofLinearIndex welcomePE).l1b
          (ParsedIntegerContext.ofLinearIndex welcomePE).mab
          (ParsedIntegerContext.ofLinearIndex welcomePE).pe)).low.extractLsb' 0 32) :=
  ⟨fixedValue_two fixed precision, fixedValue_three fixed precision⟩

/-! ## 5. The per-prepared-write data lemma -/

/-- **The prepared-write data equation.**  A successful preparation with an
integer ALU request returns the flushed `evaluateBus` image of its two operand
buses. -/
theorem prepareParsedMaskedWriteWithForwarding_data_eq_flush
    (files : IntegerRegisterFiles) (slots : ProofsLean.MNCore.Forwarding.Slots)
    (cycle : Fin 4) (accesses : ParsedMaskedIntegerAccesses) (reduced : Bool)
    (write : PreparedParsedMaskedWrite) (x y : IntegerALU.Bus)
    (readX : ParsedIntegerInput.readWithForwarding files slots cycle accesses.sourceX = .ok x)
    (readY : ParsedIntegerInput.readWithForwarding files slots cycle accesses.sourceY = .ok y)
    (precision : IntegerALU.Precision) (aluOp : IntegerALU.Op)
    (request : accesses.op.executionRequest = .ok (.integer precision aluOp))
    (prepared : prepareParsedMaskedWriteWithForwarding files slots cycle accesses reduced =
      .ok write) :
    write.data = unpackALUBus (parsedOutputAfterFlush accesses.flushSelection
      (IntegerALU.evaluateBus precision aluOp x y reduced).value) := by
  have evaluated := parsed_integer_evaluation_uses_requested_semantics accesses.op
    precision aluOp request x y reduced
  unfold prepareParsedMaskedWriteWithForwarding at prepared
  simp only [readX, readY, evaluated, StepResult.ok.injEq] at prepared
  subst prepared
  rfl

/-- **The per-prepared-write data lemma.**  If the **first** operand bus of an
integer-request ALU write has a witness low long word, then the prepared write's
data words `2` and `3` are witness data words — never the target `-1.0`.  The low
long word of an integer ALU result is the first operand's (or zero), so the
second operand is irrelevant here.  The lemma is stated per prepared write and
mentions no family, no expression and no cycle. -/
theorem prepareParsedMaskedWriteWithForwarding_data_two_three_safe
    (files : IntegerRegisterFiles) (slots : ProofsLean.MNCore.Forwarding.Slots)
    (cycle : Fin 4) (accesses : ParsedMaskedIntegerAccesses) (reduced : Bool)
    (write : PreparedParsedMaskedWrite) (x y : IntegerALU.Bus)
    (readX : ParsedIntegerInput.readWithForwarding files slots cycle accesses.sourceX = .ok x)
    (readY : ParsedIntegerInput.readWithForwarding files slots cycle accesses.sourceY = .ok y)
    (safeX : ABWitnessDataWord (x.low.extractLsb' 32 32) ∧
      ABWitnessDataWord (x.low.extractLsb' 0 32))
    (precision : IntegerALU.Precision) (aluOp : IntegerALU.Op)
    (request : accesses.op.executionRequest = .ok (.integer precision aluOp))
    (prepared : prepareParsedMaskedWriteWithForwarding files slots cycle accesses reduced =
      .ok write) :
    (∀ bound : 2 < 4, ABWitnessDataWord (write.data ⟨2, bound⟩)) ∧
      (∀ bound : 3 < 4, ABWitnessDataWord (write.data ⟨3, bound⟩)) := by
  have dataEq := prepareParsedMaskedWriteWithForwarding_data_eq_flush files slots cycle
    accesses reduced write x y readX readY precision aluOp request prepared
  have lowSafe := parsedOutputAfterFlush_two_safe accesses.flushSelection
    (IntegerALU.evaluateBus precision aluOp x y reduced).value
    (evaluateBus_low_two_safe precision aluOp x y reduced safeX.1)
    (evaluateBus_low_three_safe precision aluOp x y reduced safeX.2)
  constructor
  · intro bound
    rw [dataEq]
    exact unpackALUBus_two_safe _ bound lowSafe.1
  · intro bound
    rw [dataEq]
    exact unpackALUBus_three_safe _ bound lowSafe.2

theorem readWithForwarding_memory_eq (files : IntegerRegisterFiles)
    (slots : ProofsLean.MNCore.Forwarding.Slots) (cycle : Fin 4)
    (access : DirectMemoryAccess) (rounded : Bool) :
    ParsedIntegerInput.readWithForwarding files slots cycle (.memory access rounded) =
      .ok (ParsedIntegerInput.applyRounding rounded
        (pack (readDirectAccess files access))) := by
  simp [ParsedIntegerInput.readWithForwarding, ParsedIntegerInput.read]

theorem readWithForwarding_fixed_eq (files : IntegerRegisterFiles)
    (slots : ProofsLean.MNCore.Forwarding.Slots) (cycle : Fin 4)
    (value : IntegerALU.Bus) :
    ParsedIntegerInput.readWithForwarding files slots cycle (.fixed value) = .ok value := by
  simp [ParsedIntegerInput.readWithForwarding, ParsedIntegerInput.read]

/-- The integer-ALU instance for a **direct memory read** operand at the witness
input (the first operand may be rounded; rounding zeroes the low word). -/
theorem abZeroRight_memoryWrite_data_two_three_safe
    (slots : ProofsLean.MNCore.Forwarding.Slots)
    (cycle : Fin 4) (accesses : ParsedMaskedIntegerAccesses) (reduced : Bool)
    (write : PreparedParsedMaskedWrite) (x y : IntegerALU.Bus)
    (sourceXAccess sourceYAccess : DirectMemoryAccess)
    (roundedX roundedY : Bool)
    (sourceX : accesses.sourceX = .memory sourceXAccess roundedX)
    (sourceY : accesses.sourceY = .memory sourceYAccess roundedY)
    (readX : ParsedIntegerInput.readWithForwarding
      (abInitialPERegisters abZeroRightInput) slots cycle accesses.sourceX = .ok x)
    (readY : ParsedIntegerInput.readWithForwarding
      (abInitialPERegisters abZeroRightInput) slots cycle accesses.sourceY = .ok y)
    (precision : IntegerALU.Precision) (aluOp : IntegerALU.Op)
    (request : accesses.op.executionRequest = .ok (.integer precision aluOp))
    (prepared : prepareParsedMaskedWriteWithForwarding
      (abInitialPERegisters abZeroRightInput) slots cycle accesses reduced = .ok write) :
    (∀ bound : 2 < 4, ABWitnessDataWord (write.data ⟨2, bound⟩)) ∧
      (∀ bound : 3 < 4, ABWitnessDataWord (write.data ⟨3, bound⟩)) := by
  have xEq : x = ParsedIntegerInput.applyRounding roundedX
      (pack (readDirectAccess (abInitialPERegisters abZeroRightInput) sourceXAccess)) := by
    have h := readX
    rw [sourceX, readWithForwarding_memory_eq] at h
    exact (StepResult.ok.inj h).symm
  have yEq : y = ParsedIntegerInput.applyRounding roundedY
      (pack (readDirectAccess (abInitialPERegisters abZeroRightInput) sourceYAccess)) := by
    have h := readY
    rw [sourceY, readWithForwarding_memory_eq] at h
    exact (StepResult.ok.inj h).symm
  subst xEq
  subst yEq
  apply prepareParsedMaskedWriteWithForwarding_data_two_three_safe
    (abInitialPERegisters abZeroRightInput) slots cycle accesses reduced write _ _
    readX readY
    ⟨applyRounding_pack_two_safe roundedX
      (readDirectAccess (abInitialPERegisters abZeroRightInput) sourceXAccess)
      (abZeroRight_readDirectAccess_safe sourceXAccess ⟨2, by decide⟩),
      applyRounding_pack_three_safe roundedX
      (readDirectAccess (abInitialPERegisters abZeroRightInput) sourceXAccess)
      (abZeroRight_readDirectAccess_safe sourceXAccess ⟨3, by decide⟩)⟩
    precision aluOp request prepared

/-- The integer-ALU instance for a **`.fixed` PE-0 constant** operand. -/
theorem abZeroRight_fixedWrite_data_two_three_safe
    (slots : ProofsLean.MNCore.Forwarding.Slots)
    (cycle : Fin 4) (accesses : ParsedMaskedIntegerAccesses) (reduced : Bool)
    (write : PreparedParsedMaskedWrite) (x y : IntegerALU.Bus)
    (fixedX : ParsedFixed) (precisionX : IntegerALU.Precision)
    (sourceX : accesses.sourceX = .fixed (replicateIntegerLane precisionX
      (ParsedFixed.integerValue fixedX precisionX
        (ParsedIntegerContext.ofLinearIndex welcomePE).group
        (ParsedIntegerContext.ofLinearIndex welcomePE).l2b
        (ParsedIntegerContext.ofLinearIndex welcomePE).l1b
        (ParsedIntegerContext.ofLinearIndex welcomePE).mab
        (ParsedIntegerContext.ofLinearIndex welcomePE).pe)))
    (readX : ParsedIntegerInput.readWithForwarding
      (abInitialPERegisters abZeroRightInput) slots cycle accesses.sourceX = .ok x)
    (readY : ParsedIntegerInput.readWithForwarding
      (abInitialPERegisters abZeroRightInput) slots cycle accesses.sourceY = .ok y)
    (precision : IntegerALU.Precision) (aluOp : IntegerALU.Op)
    (request : accesses.op.executionRequest = .ok (.integer precision aluOp))
    (prepared : prepareParsedMaskedWriteWithForwarding
      (abInitialPERegisters abZeroRightInput) slots cycle accesses reduced = .ok write) :
    (∀ bound : 2 < 4, ABWitnessDataWord (write.data ⟨2, bound⟩)) ∧
      (∀ bound : 3 < 4, ABWitnessDataWord (write.data ⟨3, bound⟩)) := by
  have xEq : x = replicateIntegerLane precisionX
      (ParsedFixed.integerValue fixedX precisionX
        (ParsedIntegerContext.ofLinearIndex welcomePE).group
        (ParsedIntegerContext.ofLinearIndex welcomePE).l2b
        (ParsedIntegerContext.ofLinearIndex welcomePE).l1b
        (ParsedIntegerContext.ofLinearIndex welcomePE).mab
        (ParsedIntegerContext.ofLinearIndex welcomePE).pe) := by
    have h := readX
    rw [sourceX, readWithForwarding_fixed_eq] at h
    exact (StepResult.ok.inj h).symm
  subst xEq
  apply prepareParsedMaskedWriteWithForwarding_data_two_three_safe
    (abInitialPERegisters abZeroRightInput) slots cycle accesses reduced write _ _
    readX readY (fixedBus_two_three_safe fixedX precisionX) precision aluOp request prepared

/-- **The per-source read lemma.**  At the witness input, a successfully read
operand whose shape is either a direct memory access (any bank, width, address,
rounding) or a PE-0 `.fixed` constant has witness low data words.  This is the
"every source operand and cycle" form of the initial-read lemma; `.forward`
sources are the residual (their buses come from the forwarding slots and are the
subject of the forwarding-chain invariant, not of this lemma). -/
theorem abZeroRight_readWithForwarding_two_three_safe
    (slots : ProofsLean.MNCore.Forwarding.Slots) (cycle : Fin 4)
    (input : ParsedIntegerInput) (bus : IntegerALU.Bus)
    (read : ParsedIntegerInput.readWithForwarding (abInitialPERegisters abZeroRightInput)
      slots cycle input = .ok bus)
    (shape : (∃ (access : DirectMemoryAccess) (rounded : Bool), input = .memory access rounded) ∨
      (∃ (fixed : ParsedFixed) (precision : IntegerALU.Precision),
        input = .fixed (replicateIntegerLane precision
          (ParsedFixed.integerValue fixed precision
            (ParsedIntegerContext.ofLinearIndex welcomePE).group
            (ParsedIntegerContext.ofLinearIndex welcomePE).l2b
            (ParsedIntegerContext.ofLinearIndex welcomePE).l1b
            (ParsedIntegerContext.ofLinearIndex welcomePE).mab
            (ParsedIntegerContext.ofLinearIndex welcomePE).pe)))) :
    ABWitnessDataWord (bus.low.extractLsb' 32 32) ∧
      ABWitnessDataWord (bus.low.extractLsb' 0 32) := by
  rcases shape with ⟨access, rounded, same⟩ | ⟨fixed, precision, same⟩
  · subst same
    rw [readWithForwarding_memory_eq] at read
    have busEq : bus = ParsedIntegerInput.applyRounding rounded
        (pack (readDirectAccess (abInitialPERegisters abZeroRightInput) access)) :=
      (StepResult.ok.inj read).symm
    subst busEq
    exact ⟨applyRounding_pack_two_safe rounded _
        (abZeroRight_readDirectAccess_safe access ⟨2, by decide⟩),
      applyRounding_pack_three_safe rounded _
        (abZeroRight_readDirectAccess_safe access ⟨3, by decide⟩)⟩
  · subst same
    rw [readWithForwarding_fixed_eq] at read
    have busEq : bus = replicateIntegerLane precision
        (ParsedFixed.integerValue fixed precision
          (ParsedIntegerContext.ofLinearIndex welcomePE).group
          (ParsedIntegerContext.ofLinearIndex welcomePE).l2b
          (ParsedIntegerContext.ofLinearIndex welcomePE).l1b
          (ParsedIntegerContext.ofLinearIndex welcomePE).mab
          (ParsedIntegerContext.ofLinearIndex welcomePE).pe) :=
      (StepResult.ok.inj read).symm
    subst busEq
    exact fixedBus_two_three_safe fixed precision

/-- **The general prepared-write data lemma with source shapes.**  Every prepared
integer-request write at the witness input whose two sources are direct memory
reads or PE-0 `.fixed` constants has witness data words `2` and `3`, hence never
the target `-1.0`. -/
theorem abZeroRight_preparedWrite_data_two_three_safe
    (slots : ProofsLean.MNCore.Forwarding.Slots)
    (cycle : Fin 4) (accesses : ParsedMaskedIntegerAccesses) (reduced : Bool)
    (write : PreparedParsedMaskedWrite) (x y : IntegerALU.Bus)
    (readX : ParsedIntegerInput.readWithForwarding (abInitialPERegisters abZeroRightInput)
      slots cycle accesses.sourceX = .ok x)
    (readY : ParsedIntegerInput.readWithForwarding (abInitialPERegisters abZeroRightInput)
      slots cycle accesses.sourceY = .ok y)
    (shapeX : (∃ (access : DirectMemoryAccess) (rounded : Bool),
        accesses.sourceX = .memory access rounded) ∨
      (∃ (fixed : ParsedFixed) (precision : IntegerALU.Precision),
        accesses.sourceX = .fixed (replicateIntegerLane precision
          (ParsedFixed.integerValue fixed precision
            (ParsedIntegerContext.ofLinearIndex welcomePE).group
            (ParsedIntegerContext.ofLinearIndex welcomePE).l2b
            (ParsedIntegerContext.ofLinearIndex welcomePE).l1b
            (ParsedIntegerContext.ofLinearIndex welcomePE).mab
            (ParsedIntegerContext.ofLinearIndex welcomePE).pe))))
    (precision : IntegerALU.Precision) (aluOp : IntegerALU.Op)
    (request : accesses.op.executionRequest = .ok (.integer precision aluOp))
    (prepared : prepareParsedMaskedWriteWithForwarding
      (abInitialPERegisters abZeroRightInput) slots cycle accesses reduced = .ok write) :
    (∀ bound : 2 < 4, ABWitnessDataWord (write.data ⟨2, bound⟩)) ∧
      (∀ bound : 3 < 4, ABWitnessDataWord (write.data ⟨3, bound⟩)) :=
  prepareParsedMaskedWriteWithForwarding_data_two_three_safe
    (abInitialPERegisters abZeroRightInput) slots cycle accesses reduced write x y readX readY
    (abZeroRight_readWithForwarding_two_three_safe slots cycle accesses.sourceX x readX shapeX)
    precision aluOp request prepared

/-- **The target form of the per-write data lemma.**  The low long word — data
words `2` and `3` — of any prepared integer-request `.double` store at the
witness input is never the target word `0xBF800000`. -/
theorem abZeroRight_preparedWrite_data_two_three_ne_target
    (slots : ProofsLean.MNCore.Forwarding.Slots)
    (cycle : Fin 4) (accesses : ParsedMaskedIntegerAccesses) (reduced : Bool)
    (write : PreparedParsedMaskedWrite) (x y : IntegerALU.Bus)
    (readX : ParsedIntegerInput.readWithForwarding (abInitialPERegisters abZeroRightInput)
      slots cycle accesses.sourceX = .ok x)
    (readY : ParsedIntegerInput.readWithForwarding (abInitialPERegisters abZeroRightInput)
      slots cycle accesses.sourceY = .ok y)
    (shapeX : (∃ (access : DirectMemoryAccess) (rounded : Bool),
        accesses.sourceX = .memory access rounded) ∨
      (∃ (fixed : ParsedFixed) (precision : IntegerALU.Precision),
        accesses.sourceX = .fixed (replicateIntegerLane precision
          (ParsedFixed.integerValue fixed precision
            (ParsedIntegerContext.ofLinearIndex welcomePE).group
            (ParsedIntegerContext.ofLinearIndex welcomePE).l2b
            (ParsedIntegerContext.ofLinearIndex welcomePE).l1b
            (ParsedIntegerContext.ofLinearIndex welcomePE).mab
            (ParsedIntegerContext.ofLinearIndex welcomePE).pe))))
    (precision : IntegerALU.Precision) (aluOp : IntegerALU.Op)
    (request : accesses.op.executionRequest = .ok (.integer precision aluOp))
    (prepared : prepareParsedMaskedWriteWithForwarding
      (abInitialPERegisters abZeroRightInput) slots cycle accesses reduced = .ok write) :
    (∀ bound : 2 < 4, write.data ⟨2, bound⟩ ≠ 0xBF800000) ∧
      (∀ bound : 3 < 4, write.data ⟨3, bound⟩ ≠ 0xBF800000) := by
  obtain ⟨safeTwo, safeThree⟩ := abZeroRight_preparedWrite_data_two_three_safe slots cycle
    accesses reduced write x y readX readY shapeX precision aluOp request prepared
  exact ⟨fun bound => abWitnessDataWord_ne_target _ (safeTwo bound),
    fun bound => abWitnessDataWord_ne_target _ (safeThree bound)⟩

/-! ## 6. A commit with safe `.double` words never produces the target -/

/-- The mask of bus word `2` (or `3`) of a `.double` store is either zero or all
ones, so the masked merge returns the old or the new word. -/
theorem selectedWordMask_two_zero_or_allOnes (flags : BitVec 4) (longLong : Bool) :
    selectedWordMask flags longLong ⟨2, by decide⟩ = 0 ∨
      selectedWordMask flags longLong ⟨2, by decide⟩ = BitVec.allOnes 32 := by
  cases longLong with
  | false =>
      right
      simp [selectedWordMask]
  | true =>
      by_cases bit : flags.getLsbD 1 = true
      · right
        simp only [selectedWordMask]
        rw [ite_eq_left trivial, ite_eq_left bit]
      · left
        simp only [selectedWordMask]
        rw [ite_eq_left trivial, ite_eq_right bit]

theorem selectedWordMask_three_zero_or_allOnes (flags : BitVec 4) (longLong : Bool) :
    selectedWordMask flags longLong ⟨3, by decide⟩ = 0 ∨
      selectedWordMask flags longLong ⟨3, by decide⟩ = BitVec.allOnes 32 := by
  cases longLong with
  | false =>
      right
      simp [selectedWordMask]
  | true =>
      by_cases bit : flags.getLsbD 0 = true
      · right
        simp only [selectedWordMask]
        rw [ite_eq_left trivial, ite_eq_left bit]
      · left
        simp only [selectedWordMask]
        rw [ite_eq_left trivial, ite_eq_right bit]

/-- One masked `.double` store at data index `2` keeps a non-target word
non-target. -/
theorem writeWordsMasked_double_two_ne
    (memory : PEMemory.Memory .lm1) (start target : Fin PEMemory.Bank.lm1.capacity)
    (data : WordBus) (flags : BitVec 4) (longLong : Bool)
    (dataSafe : ABWitnessDataWord (data ⟨2, by decide⟩))
    (distanceTwo : distance .lm1 start target = 2)
    (oldNe : memory target ≠ 0xBF800000) :
    writeWordsMasked .lm1 .double memory start data flags longLong target ≠ 0xBF800000 := by
  have within : distance .lm1 start target < count .lm1 .double := by
    rw [distanceTwo]
    decide
  rw [writeWordsMasked_at .lm1 .double memory start target data flags longLong within]
  have hidx : (⟨distance .lm1 start target,
      Nat.lt_of_lt_of_le within (count_le_four .lm1 .double)⟩ : Fin 4) =
      ⟨2, by decide⟩ :=
    Fin.ext distanceTwo
  rw [hidx]
  rcases selectedWordMask_two_zero_or_allOnes flags longLong with maskZero | maskOnes
  · rw [maskZero, mergeSelectedWord_zero]
    exact oldNe
  · rw [maskOnes, mergeSelectedWord_allOnes]
    exact abWitnessDataWord_ne_target _ dataSafe

/-- The same at data index `3`. -/
theorem writeWordsMasked_double_three_ne
    (memory : PEMemory.Memory .lm1) (start target : Fin PEMemory.Bank.lm1.capacity)
    (data : WordBus) (flags : BitVec 4) (longLong : Bool)
    (dataSafe : ABWitnessDataWord (data ⟨3, by decide⟩))
    (distanceThree : distance .lm1 start target = 3)
    (oldNe : memory target ≠ 0xBF800000) :
    writeWordsMasked .lm1 .double memory start data flags longLong target ≠ 0xBF800000 := by
  have within : distance .lm1 start target < count .lm1 .double := by
    rw [distanceThree]
    decide
  rw [writeWordsMasked_at .lm1 .double memory start target data flags longLong within]
  have hidx : (⟨distance .lm1 start target,
      Nat.lt_of_lt_of_le within (count_le_four .lm1 .double)⟩ : Fin 4) =
      ⟨3, by decide⟩ :=
    Fin.ext distanceThree
  rw [hidx]
  rcases selectedWordMask_three_zero_or_allOnes flags longLong with maskZero | maskOnes
  · rw [maskZero, mergeSelectedWord_zero]
    exact oldNe
  · rw [maskOnes, mergeSelectedWord_allOnes]
    exact abWitnessDataWord_ne_target _ dataSafe

/-- **One commit step.**  If every `.lm1` write of the step either misses the
target word or is a `.double` store hitting it at data index `2` or `3` with a
non-target data word, the word stays non-target. -/
theorem welcomeCommitStep_lm1_word_ne_target (files : IntegerRegisterFiles)
    (write : PreparedParsedMaskedWrite) (target : Fin PEMemory.Bank.lm1.capacity)
    (keeps : ∀ (width : PEMemory.Width) (address : Fin PEMemory.Bank.lm1.capacity)
        (data : WordBus) (selection : PEWordSelection),
      write.destination = some ⟨.lm1, width, address⟩ → write.data = data →
      write.selection = selection →
        (count .lm1 width ≤ distance .lm1 address target) ∨
        (width = .double ∧
          ((distance .lm1 address target = 2 ∧ ABWitnessDataWord (data ⟨2, by decide⟩)) ∨
           (distance .lm1 address target = 3 ∧ ABWitnessDataWord (data ⟨3, by decide⟩)))))
    (oldNe : files.lm1 target ≠ 0xBF800000) :
    (welcomeCommitStep files write).lm1 target ≠ 0xBF800000 := by
  cases write with
  | mk destination maskUpdate data selection =>
    cases maskUpdate with
    | some update =>
        simp only [welcomeCommitStep]
        exact oldNe
    | none =>
        cases destination with
        | none =>
            simp only [welcomeCommitStep]
            exact oldNe
        | some access =>
            cases access with
            | mk bank width address =>
                cases bank with
                | lm1 =>
                    simp only [welcomeCommitStep]
                    rw [writeDirectAccessMasked_lm1_apply]
                    rcases keeps width address data selection rfl rfl rfl with
                      outside | ⟨widthDouble, block⟩
                    · rw [writeWordsMasked_preserves_outside .lm1 width files.lm1 address
                        target data selection.flags selection.longLong outside]
                      exact oldNe
                    · subst widthDouble
                      rcases block with ⟨distanceTwo, dataTwo⟩ | ⟨distanceThree, dataThree⟩
                      · exact writeWordsMasked_double_two_ne files.lm1 address target data
                          selection.flags selection.longLong dataTwo distanceTwo oldNe
                      · exact writeWordsMasked_double_three_ne files.lm1 address target data
                          selection.flags selection.longLong dataThree distanceThree oldNe
                | lm0 =>
                    simp only [welcomeCommitStep]
                    rw [writeDirectAccessMasked_lm1_eq _ _ _ _ _ _ (by simp)]
                    exact oldNe
                | grf0 =>
                    simp only [welcomeCommitStep]
                    rw [writeDirectAccessMasked_lm1_eq _ _ _ _ _ _ (by simp)]
                    exact oldNe
                | grf1 =>
                    simp only [welcomeCommitStep]
                    rw [writeDirectAccessMasked_lm1_eq _ _ _ _ _ _ (by simp)]
                    exact oldNe
                | t =>
                    simp only [welcomeCommitStep]
                    rw [writeDirectAccessMasked_lm1_eq _ _ _ _ _ _ (by simp)]
                    exact oldNe

/-- **The commit kernel.**  A commit over an aligned, covering `.double` write
list with witness data words never produces the target `-1.0`. -/
theorem commitParsedMaskedWrites_lm1_word_ne_target (files : IntegerRegisterFiles)
    (writes : List PreparedParsedMaskedWrite) (target : Fin PEMemory.Bank.lm1.capacity)
    (keeps : ∀ write ∈ writes, ∀ (width : PEMemory.Width)
        (address : Fin PEMemory.Bank.lm1.capacity) (data : WordBus) (selection : PEWordSelection),
      write.destination = some ⟨.lm1, width, address⟩ → write.data = data →
      write.selection = selection →
        (count .lm1 width ≤ distance .lm1 address target) ∨
        (width = .double ∧
          ((distance .lm1 address target = 2 ∧ ABWitnessDataWord (data ⟨2, by decide⟩)) ∨
           (distance .lm1 address target = 3 ∧ ABWitnessDataWord (data ⟨3, by decide⟩)))))
    (oldNe : files.lm1 target ≠ 0xBF800000) :
    (commitParsedMaskedWrites files writes).lm1 target ≠ 0xBF800000 := by
  induction writes generalizing files with
  | nil => simpa [commitParsedMaskedWrites] using oldNe
  | cons write rest ih =>
      rw [commitParsedMaskedWrites_cons]
      apply ih
      · intro item member
        exact keeps item (List.mem_cons_of_mem _ member)
      · exact welcomeCommitStep_lm1_word_ne_target files write target
          (fun width address data selection destination dataEq selectionEq =>
            keeps write (by simp) width address data selection destination dataEq selectionEq)
          oldNe

/-! ## 7. Window forcing: the data index of a covered observed word -/

/-- A covering write whose address is 4-word aligned hits an observed word at
data index `t % 4`; the aligned start is `4 * (t / 4)`. -/
theorem doubleWindow_index_forced_four (address : Fin PEMemory.Bank.lm1.capacity)
    (aligned : address.val % 4 = 0) (t : Fin 16)
    (within : distance .lm1 address (lm1Target t) < 4) :
    address.val = 4 * (t.val / 4) ∧ distance .lm1 address (lm1Target t) = t.val % 4 := by
  have ha := address.isLt
  have ht := t.isLt
  unfold distance lm1Target at *
  simp only [PEMemory.Bank.capacity] at *
  -- a covering aligned start is at most the observed word: otherwise the
  -- circular distance is at least `4096 - 15` and cannot be below four
  have hle : address.val ≤ t.val := by
    by_contra hlt
    have hpos : t.val + 4096 - address.val < 4096 := by omega
    rw [Nat.mod_eq_of_lt hpos] at within
    omega
  have hsplit : t.val + 4096 - address.val = (t.val - address.val) + 4096 := by omega
  have hlt : t.val - address.val < 4096 := by omega
  rw [hsplit, Nat.add_mod_right, Nat.mod_eq_of_lt hlt] at within
  constructor <;> omega

theorem doubleWindow_index_forced (address : Fin PEMemory.Bank.lm1.capacity)
    (aligned : address.val % 4 = 0) (t : Fin 16)
    (within : distance .lm1 address (lm1Target t) < count .lm1 .double) :
    address.val = 4 * (t.val / 4) ∧ distance .lm1 address (lm1Target t) = t.val % 4 := by
  apply doubleWindow_index_forced_four address aligned t
  have countEq : count .lm1 .double = 4 := by decide
  rwa [countEq] at within

/-- **The eight low-word addresses.**  Every covered observed word whose index is
`2` or `3` mod `4` is written from data word `2` or `3` of its covering write. -/
theorem doubleWindow_eight_low_words (address : Fin PEMemory.Bank.lm1.capacity)
    (aligned : address.val % 4 = 0) (t : Fin 16)
    (within : distance .lm1 address (lm1Target t) < count .lm1 .double)
    (mod : t.val % 4 = 2 ∨ t.val % 4 = 3) :
    distance .lm1 address (lm1Target t) = 2 ∨
      distance .lm1 address (lm1Target t) = 3 := by
  have forced := doubleWindow_index_forced address aligned t within
  omega

/-- Every one of the four `4`-word windows of an aligned start family that covers
all sixteen observed words has exactly four observed words. -/
theorem doubleWindow_window_card_eq_four (starts : Fin 4 → Fin PEMemory.Bank.lm1.capacity)
    (covers : ∀ t : Fin 16, ∃ i, distance .lm1 (starts i) (lm1Target t) <
      count .lm1 .double) (i : Fin 4) :
    (Finset.univ.filter (fun t : Fin 16 =>
      distance .lm1 (starts i) (lm1Target t) < count .lm1 .double)).card = 4 := by
  classical
  have countEq : count .lm1 .double = 4 := by decide
  let windows : Fin 4 → Finset (Fin 16) := fun j =>
    Finset.univ.filter (fun t => distance .lm1 (starts j) (lm1Target t) < count .lm1 .double)
  have cardLe : ∀ j, (windows j).card ≤ 4 := by
    intro j
    have := card_window_le_size (starts j) 4
    simpa [windows, countEq] using this
  have subset : (Finset.univ : Finset (Fin 16)) ⊆
      windows 0 ∪ windows 1 ∪ windows 2 ∪ windows 3 := by
    intro t _
    obtain ⟨j, hj⟩ := covers t
    have hmem : t ∈ windows j := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩
    have hv : j.val = 0 ∨ j.val = 1 ∨ j.val = 2 ∨ j.val = 3 := by
      have := j.isLt
      omega
    have je : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by
      rcases hv with h | h | h | h
      · exact Or.inl (Fin.ext h)
      · exact Or.inr (Or.inl (Fin.ext h))
      · exact Or.inr (Or.inr (Or.inl (Fin.ext h)))
      · exact Or.inr (Or.inr (Or.inr (Fin.ext h)))
    rcases je with rfl | rfl | rfl | rfl
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ hmem))
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ hmem))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ hmem)
    · exact Finset.mem_union_right _ hmem
  have chain : 16 ≤ (windows 0 ∪ windows 1 ∪ windows 2 ∪ windows 3).card := by
    have h : (Finset.univ : Finset (Fin 16)).card ≤
        (windows 0 ∪ windows 1 ∪ windows 2 ∪ windows 3).card := Finset.card_le_card subset
    simpa using h
  have a0 := cardLe 0
  have a1 := cardLe 1
  have a2 := cardLe 2
  have a3 := cardLe 3
  have u01 := Finset.card_union_le (windows 0) (windows 1)
  have u012 := Finset.card_union_le (windows 0 ∪ windows 1) (windows 2)
  have u0123 := Finset.card_union_le ((windows 0 ∪ windows 1) ∪ windows 2) (windows 3)
  have h0 : (windows 0).card = 4 := by omega
  have h1 : (windows 1).card = 4 := by omega
  have h2 : (windows 2).card = 4 := by omega
  have h3 : (windows 3).card = 4 := by omega
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
    have hv : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 := by
      have := i.isLt
      omega
    rcases hv with h | h | h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Or.inl (Fin.ext h))
    · exact Or.inr (Or.inr (Or.inl (Fin.ext h)))
    · exact Or.inr (Or.inr (Or.inr (Fin.ext h)))
  rcases hi with rfl | rfl | rfl | rfl <;> assumption

/-- **The window forcing.**  Four `4`-aligned windows covering all sixteen
observed words are exactly the windows at `0, 4, 8, 12`: every window covers
four words, hence is one of them, and each of them is covered. -/
theorem doubleWindow_four_windows_forced (starts : Fin 4 → Fin PEMemory.Bank.lm1.capacity)
    (aligned : ∀ i, (starts i).val % 4 = 0)
    (covers : ∀ t : Fin 16, ∃ i, distance .lm1 (starts i) (lm1Target t) <
      count .lm1 .double) :
    (Finset.univ.image (fun i => (starts i).val)) = ({0, 4, 8, 12} : Finset Nat) := by
  classical
  have countEq : count .lm1 .double = 4 := by decide
  have windowNonempty : ∀ i, ∃ t : Fin 16, distance .lm1 (starts i) (lm1Target t) <
      count .lm1 .double := by
    intro i
    have card := doubleWindow_window_card_eq_four starts covers i
    have nonempty : (Finset.univ.filter (fun t : Fin 16 =>
        distance .lm1 (starts i) (lm1Target t) < count .lm1 .double)).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro empty
      rw [empty] at card
      simp at card
    obtain ⟨t, ht⟩ := nonempty
    exact ⟨t, (Finset.mem_filter.mp ht).2⟩
  apply Finset.ext
  intro value
  constructor
  · intro member
    obtain ⟨i, _, same⟩ := Finset.mem_image.mp member
    subst same
    obtain ⟨t, within⟩ := windowNonempty i
    have forced := doubleWindow_index_forced (starts i) (aligned i) t within
    have ha := (starts i).isLt
    have hval : (starts i).val = 0 ∨ (starts i).val = 4 ∨ (starts i).val = 8 ∨
        (starts i).val = 12 := by
      have := forced.1
      omega
    rcases hval with h | h | h | h <;> simp [h]
  · intro member
    simp only [Finset.mem_insert, Finset.mem_singleton] at member
    rcases member with h | h | h | h
    · rw [h]
      obtain ⟨i, within⟩ := covers (⟨0, by decide⟩ : Fin 16)
      have forced := doubleWindow_index_forced (starts i) (aligned i) ⟨0, by decide⟩ within
      have zero : (⟨0, by decide⟩ : Fin 16).val = 0 := rfl
      rw [zero] at forced
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, by omega⟩
    · rw [h]
      obtain ⟨i, within⟩ := covers (⟨4, by decide⟩ : Fin 16)
      have forced := doubleWindow_index_forced (starts i) (aligned i) ⟨4, by decide⟩ within
      have four : (⟨4, by decide⟩ : Fin 16).val = 4 := rfl
      rw [four] at forced
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, by omega⟩
    · rw [h]
      obtain ⟨i, within⟩ := covers (⟨8, by decide⟩ : Fin 16)
      have forced := doubleWindow_index_forced (starts i) (aligned i) ⟨8, by decide⟩ within
      have eight : (⟨8, by decide⟩ : Fin 16).val = 8 := rfl
      rw [eight] at forced
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, by omega⟩
    · rw [h]
      obtain ⟨i, within⟩ := covers (⟨12, by decide⟩ : Fin 16)
      have forced := doubleWindow_index_forced (starts i) (aligned i) ⟨12, by decide⟩ within
      have twelve : (⟨12, by decide⟩ : Fin 16).val = 12 := rfl
      rw [twelve] at forced
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, by omega⟩

/-! ## 8. The `.double` write-list predicates and the refutation -/

/-- Every `.lm1` destination of the list has the static width `w`. -/
def Lm1WritesOfWidth (writes : List PreparedParsedMaskedWrite) (w : PEMemory.Width) : Prop :=
  ∀ write ∈ writes, ∀ (width : PEMemory.Width) (address : Fin PEMemory.Bank.lm1.capacity),
    write.destination = some ⟨.lm1, width, address⟩ → width = w

/-- Every `.lm1` destination address of the list is 4-word aligned, as
`PEMemory.address_aligned` guarantees for `.double` destinations. -/
def Lm1WritesAligned (writes : List PreparedParsedMaskedWrite) : Prop :=
  ∀ write ∈ writes, ∀ (width : PEMemory.Width) (address : Fin PEMemory.Bank.lm1.capacity),
    write.destination = some ⟨.lm1, width, address⟩ → address.val % 4 = 0

/-- The list covers every observed word `0..15`. -/
def Lm1WritesCover (writes : List PreparedParsedMaskedWrite) : Prop :=
  ∀ t : Fin 16, ∃ write ∈ writes, ∃ (width : PEMemory.Width)
      (address : Fin PEMemory.Bank.lm1.capacity),
    write.destination = some ⟨.lm1, width, address⟩ ∧
      distance .lm1 address (lm1Target t) < count .lm1 width

/-- Data words `2` and `3` of every write of the list are witness data words. -/
def Lm1WritesDataSafe (writes : List PreparedParsedMaskedWrite) : Prop :=
  ∀ write ∈ writes, ABWitnessDataWord (write.data ⟨2, by decide⟩) ∧
    ABWitnessDataWord (write.data ⟨3, by decide⟩)

/-- **The `.double` refutation at the witness input.**  A one-line `.pe`
program whose PE-0 file at `A = 0, B = 1.0` is the commit of an aligned write
list covering all sixteen observed words, whose data words `2, 3` are witness
data words, is refuted at that input: word `2` is written from a non-target
data word (or left at the initial `0`), while the specification demands `-1.0`.
Alignment plus coverage already forces the covering write to be `.double`
(`widthDouble` below), so no width hypothesis is needed. -/
theorem abZeroRight_doubleWindow_refutes (expressions : List NormalizedExpr)
    (next : State)
    (step : abSealedMachine.step (.pe expressions) (abInitialState abZeroRightInput) = some next)
    (writes : List PreparedParsedMaskedWrite)
    (committed : next.peRegisters abPE =
      commitParsedMaskedWrites ((abInitialState abZeroRightInput).peRegisters abPE) writes)
    (aligned : Lm1WritesAligned writes)
    (covers : Lm1WritesCover writes)
    (safe : Lm1WritesDataSafe writes) :
    ProofsLean.Refutes abSealedMachine abSpec
      ([InstructionLine.pe expressions] : List InstructionLine) abZeroRightInput := by
  refine ⟨abSpec_admissible _, ?_⟩
  rintro ⟨result, executed, post⟩
  have stepResult : abSealedMachine.step (.pe expressions)
      (abInitialState abZeroRightInput) = some result := by
    simpa [ProofsLean.execute] using executed
  rw [step] at stepResult
  have resultEq : result = next := (Option.some.inj stepResult).symm
  subst result
  -- word `2` is covered; its covering write must be an aligned `.double` store
  -- hitting data index `2`
  let word : Fin 16 := ⟨2, by decide⟩
  obtain ⟨write, member, width, address, destination, within⟩ := covers word
  have wordValue : word.val = 2 := rfl
  have alignedAddress : address.val % 4 = 0 :=
    aligned write member width address destination
  have withinFour : distance .lm1 address (lm1Target word) < 4 := by
    have bounded := count_le_four .lm1 width
    omega
  have forced := doubleWindow_index_forced_four address alignedAddress word withinFour
  have distanceTwo : distance .lm1 address (lm1Target word) = 2 := by
    have := forced.2
    rw [wordValue] at this
    simpa using this
  have widthDouble : width = .double := by
    cases width with
    | word =>
        have hc : count .lm1 .word = 1 := by decide
        rw [hc] at within
        omega
    | long =>
        have hc : count .lm1 .long = 2 := by decide
        rw [hc] at within
        omega
    | double => rfl
  subst widthDouble
  have wordNe : (next.peRegisters abPE).lm1 (lm1Target word) ≠ 0xBF800000 := by
    rw [committed]
    apply commitParsedMaskedWrites_lm1_word_ne_target
      ((abInitialState abZeroRightInput).peRegisters abPE) writes (lm1Target word)
    · intro other otherMember otherWidth otherAddress data selection otherDestination
        dataEq selectionEq
      subst dataEq selectionEq
      by_cases otherWithin : distance .lm1 otherAddress (lm1Target word) < 4
      · have otherAligned := aligned other otherMember otherWidth otherAddress otherDestination
        have otherForced := doubleWindow_index_forced_four otherAddress otherAligned word
          otherWithin
        have otherDistance : distance .lm1 otherAddress (lm1Target word) = 2 := by
          have := otherForced.2
          rw [wordValue] at this
          simpa using this
        cases otherWidth with
        | word =>
            exact Or.inl (by
              have hc : count .lm1 .word = 1 := by decide
              rw [hc]
              omega)
        | long =>
            exact Or.inl (by
              have hc : count .lm1 .long = 2 := by decide
              rw [hc]
              omega)
        | double =>
            exact Or.inr ⟨rfl, Or.inl ⟨otherDistance,
              (safe other otherMember).1⟩⟩
      · exact Or.inl (by
          have bounded := count_le_four .lm1 otherWidth
          omega)
    · show (0 : BitVec 32) ≠ 0xBF800000
      decide
  have wanted := post word
  have zeroForm : (next.peRegisters abPE).lm1
      ⟨word.val, by have := word.isLt; change word.val < 4096; omega⟩ =
      (next.peRegisters abPE).lm1 (lm1Target word) := by
    exact congrArg (fun index => (next.peRegisters abPE).lm1 index) (Fin.ext rfl)
  rw [zeroForm] at wanted
  rw [abTarget_zeroRight] at wanted
  exact wordNe wanted

/-- **The task's `.double` form**: the same refutation with the explicit
hypothesis that all `.lm1` writes are `.double` (redundant given alignment and
coverage, and kept for statement compatibility). -/
theorem abZeroRight_doubleWindow_refutes_of_double (expressions : List NormalizedExpr)
    (next : State)
    (step : abSealedMachine.step (.pe expressions) (abInitialState abZeroRightInput) = some next)
    (writes : List PreparedParsedMaskedWrite)
    (committed : next.peRegisters abPE =
      commitParsedMaskedWrites ((abInitialState abZeroRightInput).peRegisters abPE) writes)
    (_allDouble : Lm1WritesOfWidth writes .double)
    (aligned : Lm1WritesAligned writes)
    (covers : Lm1WritesCover writes)
    (safe : Lm1WritesDataSafe writes) :
    ProofsLean.Refutes abSealedMachine abSpec
      ([InstructionLine.pe expressions] : List InstructionLine) abZeroRightInput :=
  abZeroRight_doubleWindow_refutes expressions next step writes committed aligned covers safe

/-- **The `.double` kernel in `¬ Correct` form** (all `.lm1` writes `.double`, the
task's statement). -/
theorem ab_not_correct_of_lm1DoubleWindow (expressions : List NormalizedExpr)
    (next : State)
    (step : abSealedMachine.step (.pe expressions) (abInitialState abZeroRightInput) = some next)
    (writes : List PreparedParsedMaskedWrite)
    (committed : next.peRegisters abPE =
      commitParsedMaskedWrites ((abInitialState abZeroRightInput).peRegisters abPE) writes)
    (allDouble : Lm1WritesOfWidth writes .double)
    (aligned : Lm1WritesAligned writes)
    (covers : Lm1WritesCover writes)
    (safe : Lm1WritesDataSafe writes) :
    ¬ ProofsLean.Correct abSealedMachine abSpec
      ([InstructionLine.pe expressions] : List InstructionLine) :=
  ProofsLean.refutes_not_correct
    (abZeroRight_doubleWindow_refutes_of_double expressions next step writes committed allDouble
      aligned covers safe)

/-! ## 9. The left witness in `Refutes` form -/

/-- **The left witness of the width kernel.**  At `A = 1.0, B = 0` a write list
of total `.lm1` width below `16` leaves an observed word untouched, which keeps
its initial `0` while the target is `0x3F800000`. -/
theorem abOneLeft_refutes_of_lm1TotalWidth (expressions : List NormalizedExpr)
    (next : State)
    (step : abSealedMachine.step (.pe expressions) (abInitialState abOneLeftInput) = some next)
    (writes : List PreparedParsedMaskedWrite)
    (committed : next.peRegisters abPE =
      commitParsedMaskedWrites ((abInitialState abOneLeftInput).peRegisters abPE) writes)
    (total : lm1WriteWords writes < 16) :
    ProofsLean.Refutes abSealedMachine abSpec
      ([InstructionLine.pe expressions] : List InstructionLine) abOneLeftInput := by
  refine ⟨abSpec_admissible _, ?_⟩
  rintro ⟨result, executed, post⟩
  obtain ⟨word, untouched⟩ := exists_uncovered_of_totalWidth writes total
  have stepResult : abSealedMachine.step (.pe expressions)
      (abInitialState abOneLeftInput) = some result := by
    simpa [ProofsLean.execute] using executed
  rw [step] at stepResult
  have resultEq : result = next := (Option.some.inj stepResult).symm
  subst result
  have zero : (next.peRegisters abPE).lm1 (lm1Target word) = 0 := by
    rw [committed]
    apply commitParsedMaskedWrites_lm1_word_zero
      ((abInitialState abOneLeftInput).peRegisters abPE) writes (lm1Target word)
    · intro other otherMember width address data selection destination dataEq selectionEq
      subst dataEq selectionEq
      exact Or.inl (untouched other otherMember width address destination)
    · exact abInitialPERegisters_lm1 abOneLeftInput (lm1Target word)
  have wanted := post word
  have zeroForm : (next.peRegisters abPE).lm1
      ⟨word.val, by have := word.isLt; change word.val < 4096; omega⟩ =
      (next.peRegisters abPE).lm1 (lm1Target word) := rfl
  rw [zeroForm, zero, abTarget_oneLeft] at wanted
  exact absurd wanted.symm (by decide)

/-- **The left witness for non-`.double` widths.**  Any one-line `.pe` program
whose PE-0 write list at `A = 1.0, B = 0` has at most four `.lm1` writes of a
static non-`.double` width is refuted there. -/
theorem abOneLeft_refutes_of_lm1WidthNotDouble (expressions : List NormalizedExpr)
    (next : State)
    (step : abSealedMachine.step (.pe expressions) (abInitialState abOneLeftInput) = some next)
    (writes : List PreparedParsedMaskedWrite)
    (committed : next.peRegisters abPE =
      commitParsedMaskedWrites ((abInitialState abOneLeftInput).peRegisters abPE) writes)
    (w : PEMemory.Width) (countLe : lm1WriteCount writes ≤ 4)
    (widths : ∀ write ∈ writes, ∀ (width : PEMemory.Width)
      (address : Fin PEMemory.Bank.lm1.capacity),
      write.destination = some ⟨PEMemory.Bank.lm1, width, address⟩ → width = w)
    (notDouble : w ≠ PEMemory.Width.double) :
    ProofsLean.Refutes abSealedMachine abSpec
      ([InstructionLine.pe expressions] : List InstructionLine) abOneLeftInput := by
  apply abOneLeft_refutes_of_lm1TotalWidth expressions next step writes committed
  have budget := lm1WriteWords_le_count_mul writes w countLe widths
  have small := (four_mul_count_le_eight w).mpr notDouble
  omega

/-- `ab_not_correct_of_lm1WidthNotDouble` restated through the `Refutes` form. -/
theorem ab_not_correct_of_lm1WidthNotDouble' (expressions : List NormalizedExpr)
    (next : State)
    (step : abSealedMachine.step (.pe expressions) (abInitialState abOneLeftInput) = some next)
    (writes : List PreparedParsedMaskedWrite)
    (committed : next.peRegisters abPE =
      commitParsedMaskedWrites ((abInitialState abOneLeftInput).peRegisters abPE) writes)
    (w : PEMemory.Width) (countLe : lm1WriteCount writes ≤ 4)
    (widths : ∀ write ∈ writes, ∀ (width : PEMemory.Width)
      (address : Fin PEMemory.Bank.lm1.capacity),
      write.destination = some ⟨PEMemory.Bank.lm1, width, address⟩ → width = w)
    (notDouble : w ≠ PEMemory.Width.double) :
    ¬ ProofsLean.Correct abSealedMachine abSpec
      ([InstructionLine.pe expressions] : List InstructionLine) :=
  ProofsLean.refutes_not_correct
    (abOneLeft_refutes_of_lm1WidthNotDouble expressions next step writes committed w countLe
      widths notDouble)

/-! ## 10. Composition: one line fails at one of the two witnesses -/

/-- **The composed one-line refutation.**  A one-line `.pe` program whose PE-0
write list at `A = 1.0, B = 0` has at most four `.lm1` writes of one static
width `w`, and whose PE-0 write list at `A = 0, B = 1.0` is an aligned covering
`.double` list with witness data words, is refuted at one of the two witness
inputs: at the left one when `w ≠ .double`, at the right one when
`w = .double`. -/
theorem abPE_incorrect_at_one_of_two_witnesses (expressions : List NormalizedExpr)
    (w : PEMemory.Width)
    (leftNext : State)
    (leftStep : abSealedMachine.step (.pe expressions) (abInitialState abOneLeftInput) =
      some leftNext)
    (leftWrites : List PreparedParsedMaskedWrite)
    (leftCommitted : leftNext.peRegisters abPE =
      commitParsedMaskedWrites ((abInitialState abOneLeftInput).peRegisters abPE) leftWrites)
    (leftCount : lm1WriteCount leftWrites ≤ 4)
    (leftWidths : ∀ write ∈ leftWrites, ∀ (width : PEMemory.Width)
      (address : Fin PEMemory.Bank.lm1.capacity),
      write.destination = some ⟨PEMemory.Bank.lm1, width, address⟩ → width = w)
    (rightNext : State)
    (rightStep : abSealedMachine.step (.pe expressions) (abInitialState abZeroRightInput) =
      some rightNext)
    (rightWrites : List PreparedParsedMaskedWrite)
    (rightCommitted : rightNext.peRegisters abPE =
      commitParsedMaskedWrites ((abInitialState abZeroRightInput).peRegisters abPE) rightWrites)
    (rightDouble : Lm1WritesOfWidth rightWrites .double)
    (rightAligned : Lm1WritesAligned rightWrites)
    (rightCovers : Lm1WritesCover rightWrites)
    (rightSafe : Lm1WritesDataSafe rightWrites) :
    ProofsLean.Refutes abSealedMachine abSpec
        ([InstructionLine.pe expressions] : List InstructionLine) abOneLeftInput ∨
      ProofsLean.Refutes abSealedMachine abSpec
        ([InstructionLine.pe expressions] : List InstructionLine) abZeroRightInput := by
  by_cases isDouble : w = PEMemory.Width.double
  · exact Or.inr (abZeroRight_doubleWindow_refutes_of_double expressions rightNext rightStep
      rightWrites rightCommitted rightDouble rightAligned rightCovers rightSafe)
  · exact Or.inl (abOneLeft_refutes_of_lm1WidthNotDouble expressions leftNext leftStep leftWrites
      leftCommitted w leftCount leftWidths isDouble)

/-- The `¬ Correct` form of the composition. -/
theorem abPE_not_correct_of_widthOrDoubleWindow (expressions : List NormalizedExpr)
    (w : PEMemory.Width)
    (leftNext : State)
    (leftStep : abSealedMachine.step (.pe expressions) (abInitialState abOneLeftInput) =
      some leftNext)
    (leftWrites : List PreparedParsedMaskedWrite)
    (leftCommitted : leftNext.peRegisters abPE =
      commitParsedMaskedWrites ((abInitialState abOneLeftInput).peRegisters abPE) leftWrites)
    (leftCount : lm1WriteCount leftWrites ≤ 4)
    (leftWidths : ∀ write ∈ leftWrites, ∀ (width : PEMemory.Width)
      (address : Fin PEMemory.Bank.lm1.capacity),
      write.destination = some ⟨PEMemory.Bank.lm1, width, address⟩ → width = w)
    (rightNext : State)
    (rightStep : abSealedMachine.step (.pe expressions) (abInitialState abZeroRightInput) =
      some rightNext)
    (rightWrites : List PreparedParsedMaskedWrite)
    (rightCommitted : rightNext.peRegisters abPE =
      commitParsedMaskedWrites ((abInitialState abZeroRightInput).peRegisters abPE) rightWrites)
    (rightDouble : Lm1WritesOfWidth rightWrites .double)
    (rightAligned : Lm1WritesAligned rightWrites)
    (rightCovers : Lm1WritesCover rightWrites)
    (rightSafe : Lm1WritesDataSafe rightWrites) :
    ¬ ProofsLean.Correct abSealedMachine abSpec
      ([InstructionLine.pe expressions] : List InstructionLine) := by
  by_cases isDouble : w = PEMemory.Width.double
  · exact ab_not_correct_of_lm1DoubleWindow expressions rightNext rightStep rightWrites
      rightCommitted rightDouble rightAligned rightCovers rightSafe
  · exact ab_not_correct_of_lm1WidthNotDouble expressions leftNext leftStep leftWrites
      leftCommitted w leftCount leftWidths isDouble

/-! ## 11. A kernel-checked instance: the witness line of `ABWidthBound` -/

/-- **The `.double` witness line's data words at the witness input.**  The
`iinc` row of `ProofsLean/ABWidthBound.lean` with an `.lm1 .double` destination
(its own integer-stage preparation, computed by the kernel at
`A = 0, B = 1.0`) has data words `2` and `3` equal to `0` in all four writes.
This is the concrete instance of
`abZeroRight_preparedWrite_data_two_three_safe`, on the exact line that defeats
the width bound: its four `.double` writes cover the sixteen observed words, so
the eight words at addresses `2, 3, 6, 7, 10, 11, 14, 15` receive `0` while the
target is `-1.0`. -/
theorem abWidthDouble_witness_data_two_three :
    (match prepareParsedIntegerMatrixReadLineCycles (abInitialPERegisters abZeroRightInput)
        welcomeZeroSlots welcomeZeroMatrixStore [abWidthDoubleExpr.toParsed]
        welcomeZeroControl false with
      | .ok (writes, _, _) => writes.map (fun write =>
          (write.data ⟨2, by decide⟩, write.data ⟨3, by decide⟩))
      | _ => []) = [(0, 0), (0, 0), (0, 0), (0, 0)] := by
  decide

end ProofsLean.MNCore

-- End of module: no sorry, no admit, no native_decide, no new axioms.
