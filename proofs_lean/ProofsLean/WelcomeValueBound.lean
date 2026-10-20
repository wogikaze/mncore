import ProofsLean.WelcomeShapes

/-! # Direct value lower bound for the sealed Welcome machine

`WelcomeShapes.lean` established that the ten write-shape `Prop`s of
`WelcomeProvenance.lean` are **unsound** as stated: they hypothesise the residual
class they are meant to refute, and their `data₂ = 0` conclusion is false for a
`.fixed .msb1` first operand.  This module abandons that decomposition and
attacks `LowerBound welcomeSealedMachine welcomeSpec 2` by a **direct value
argument** on the all-zero input.

## The value argument

The specification forces every one of the sixteen PE 0 `LM1` words to be `1` on
the all-zero input.  Three ways produce a refutation:

* **Narrow writes.**  A `.word`/`.long` `LM1` destination covers at most two
  words per cycle, so the four cycles of the (unique, by `writesUnique`) `LM1`
  access cover at most eight words: some observed word is untouched and keeps
  its initial value `0`.
* **Copied `.double` writes.**  The third bus word of a `.double` block is a
  *copy* of the first operand's low half (`evaluateBus_value_low`), never a
  computed word.  At PE 0 the copies are `0` or a submask of `0x80008000` (the
  `.fixed` lane replication), and the masked store merges submasks of that mask,
  so word `2` of the commit can never be `1`.
* **Input-independent output.**  Constant producers (`.zero`, `.immediate`,
  and every `.l1bm`/`.l2bm` broadcast whose data is the zero block memory) give
  the same PE 0 `LM1` file for the all-zero and the all-five input, while the
  specification demands `1` and `6` (`welcome_not_correct_of_inputIndependentLM1`).

The first two halves are proved here at the level of the *commit list*
`commitParsedMaskedWrites`, which is where `WelcomeProvenance.lean` connects the
executor for the plain integer-ALU subclass (`WelcomeWriteProvenance`).  The
third is `WelcomePEInputIndependent`, already refuted in `WelcomeBoundTwo.lean`.

## What is proved, unconditionally

* `welcome_not_correct_of_word_ne_one` — one non-`1` PE 0 `LM1` word refutes the
  line (the sharpening of `welcome_not_correct_of_word_zero` used below).
* `IsWelcomeCopy` / `mergeSelectedWord_isWelcomeCopy` /
  `writeWordsMasked_double_target_isWelcomeCopy` /
  `commitParsedMaskedWrites_lm1_target_isWelcomeCopy` — the masked-store algebra:
  a masked merge of copies is a copy.
* `commitParsedMaskedWrites_lm1_word_two_isWelcomeCopy` — a commit whose `LM1`
  writes are all 4-aligned `.double` blocks with copied third data words leaves
  word 2 a copy (so `≠ 1`).
* `card_covered_le` / `exists_uncovered_of_windows` /
  `welcome_not_correct_of_lm1Narrow` — the counting half: at most four narrow
  `LM1` writes cover at most eight of the sixteen observed words, so one of them
  is untouched and keeps its initial `0`.
* `prepareParsedMaskedWriteWithForwarding_data_two_isWelcomeCopy_of_memory_low_zero`
  and `..._of_fixed` — the prepared-write data half: for a direct-memory source
  with a zero low half, and for a `.fixed` source whose lane replication is a
  copy, the prepared write's third data word is a copy.  At PE 0 every `.fixed`
  value is a copy (`welcomeFixedBus_isWelcomeCopy`).
* `prepareParsedIntegerALUExprCycle_alu_direct_double_copy_of_fixed` — the
  per-cycle `.double` shape for a `.fixed` first operand, i.e. the case that
  falsifies the round-28 `data₂ = 0` shape.
* `welcomeLm1Writer_unique` — the issue checker's `writesUnique` really does
  allow at most one `LM1`-writing expression per line.
* `welcomeLowerBound_two_of_lm1WriteShapes` and
  `welcomeAnswer_optimal_of_lm1WriteShapes` — the lower bound (hence `Optimal`)
  from the exact per-line write-shape statement that is still open.

## What is not proved here

The remaining gap is the executor link from a successful `.pe` step to the three
shapes above, stated as `WelcomePELm1WriteShapeObligation` and specialised per
producer family in section 7 (`WelcomePEPlainShapeObligation`,
`WelcomePEOtherShapeObligation`, and the six per-family `Prop`s).  Each such
`Prop` is stated *without* the residual-class hypothesis, so it is not vacuous;
and its conclusion is the sound one (a copy or a window bound or
input-independence, never `data₂ = 0`).  Nothing in this module assumes any of
them, so `LowerBound welcomeSealedMachine welcomeSpec 2` and
`Optimal welcomeSealedMachine welcomeSpec welcomeAnswer` are still **not**
proved.

No `sorry`, no `admit`, no `native_decide`, no new axioms.
-/

namespace ProofsLean.MNCore

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

open Issue
open PEMemory

/-! ## 1. A PE 0 `LM1` word that is not `1` refutes the line -/

/-- **The `≠ 1` refutation.** If the all-zero step of a one-line program leaves
some observed PE 0 `LM1` word different from `1`, the specification fails there
(it demands `input i + 1 = 1` on the all-zero input). -/
theorem welcome_not_correct_of_word_ne_one (line : InstructionLine) (next : State)
    (step : welcomeSealedMachine.step line (welcomeInitialState welcomeZeroWords) = some next)
    (i : Fin 16)
    (ne : (next.peRegisters welcomePE).lm1
      ⟨i.val, by have := i.isLt; change i.val < 4096; omega⟩ ≠ 1) :
    ¬ ProofsLean.Correct welcomeSealedMachine welcomeSpec
      (([line] : List InstructionLine)) := by
  intro correct
  obtain ⟨result, executed, post⟩ := correct.2 welcomeZeroWords welcomeZeroWords_admissible
  rw [welcomeSpec_initial] at executed
  simp only [welcomeSpec] at post
  have stepResult : welcomeSealedMachine.step line (welcomeInitialState welcomeZeroWords) =
      some result := by
    simpa [ProofsLean.execute] using executed
  rw [step] at stepResult
  have resultEq : result = next := (Option.some.inj stepResult).symm
  subst result
  have word := post i
  simp [welcomeZeroWords] at word
  exact ne word


/-! ## 2. Copies and the masked-store algebra -/

/-- The bit mask of every `.fixed` copy at PE 0.  A `.word` or `.long`
replication of `.msb1` contributes `0x80000000`, a `.half` replication
contributes `0x80008000`; every other `.fixed` value at PE 0 is zero. -/
def welcomeCopyMask : BitVec 32 := 0x80008000

/-- A 32-bit word all of whose set bits are also set in `welcomeCopyMask`. -/
def IsWelcomeCopy (w : BitVec 32) : Prop := w &&& welcomeCopyMask = w

theorem isWelcomeCopy_zero : IsWelcomeCopy 0 := by
  unfold IsWelcomeCopy
  simp

theorem isWelcomeCopy_msb1_word : IsWelcomeCopy 0x80000000 := by
  unfold IsWelcomeCopy
  decide

theorem isWelcomeCopy_msb1_half : IsWelcomeCopy 0x80008000 := by
  unfold IsWelcomeCopy
  decide

/-- `1` is not a copy: its low bit is outside the mask. -/
theorem isWelcomeCopy_ne_one {w : BitVec 32} (copy : IsWelcomeCopy w) : w ≠ 1 := by
  intro one
  unfold IsWelcomeCopy at copy
  rw [one] at copy
  have zero : (1 : BitVec 32) &&& welcomeCopyMask = 0 := by decide
  rw [zero] at copy
  exact absurd copy.symm (by decide)

theorem and_or_distrib_copy (a b c : BitVec 32) :
    (a ||| b) &&& c = (a &&& c) ||| (b &&& c) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_or]
  revert hi
  generalize a.getLsbD i = x
  generalize b.getLsbD i = y
  generalize c.getLsbD i = z
  intro _
  cases x <;> cases y <;> cases z <;> simp

/-- A sub-word of a copy is a copy. -/
theorem isWelcomeCopy_and (w e : BitVec 32) (copy : IsWelcomeCopy w) :
    IsWelcomeCopy (w &&& e) := by
  unfold IsWelcomeCopy at copy ⊢
  rw [BitVec.and_assoc, BitVec.and_comm e welcomeCopyMask, ← BitVec.and_assoc, copy]

/-- The union of two copies is a copy. -/
theorem isWelcomeCopy_or (a b : BitVec 32) (ha : IsWelcomeCopy a) (hb : IsWelcomeCopy b) :
    IsWelcomeCopy (a ||| b) := by
  unfold IsWelcomeCopy at ha hb ⊢
  rw [and_or_distrib_copy, ha, hb]

/-- A masked merge of two copies is a copy: the mask only selects bits. -/
theorem mergeSelectedWord_isWelcomeCopy (old new enable : BitVec 32)
    (oldCopy : IsWelcomeCopy old) (newCopy : IsWelcomeCopy new) :
    IsWelcomeCopy (mergeSelectedWord old new enable) := by
  unfold mergeSelectedWord
  exact isWelcomeCopy_or _ _ (isWelcomeCopy_and _ _ oldCopy) (isWelcomeCopy_and _ _ newCopy)

/-- A 4-aligned `.double` store whose third bus word is a copy leaves the target
word a copy (the only way word 2 of the block is hit is at bus index 2). -/
theorem writeWordsMasked_double_target_isWelcomeCopy (memory : PEMemory.Memory .lm1)
    (start target : Fin Bank.lm1.capacity) (data : WordBus) (flags : BitVec 4)
    (longLong : Bool)
    (dataCopy : ∀ bound : 2 < 4, IsWelcomeCopy (data ⟨2, bound⟩))
    (distanceTwo : distance .lm1 start target = 2)
    (oldCopy : IsWelcomeCopy (memory target)) :
    IsWelcomeCopy (writeWordsMasked .lm1 .double memory start data flags longLong target) := by
  have within : distance .lm1 start target < count .lm1 .double := by
    rw [distanceTwo]
    decide
  rw [writeWordsMasked_at .lm1 .double memory start target data flags longLong within]
  have hidx : (⟨distance .lm1 start target,
      Nat.lt_of_lt_of_le within (count_le_four .lm1 .double)⟩ : Fin 4) =
      ⟨2, by decide⟩ :=
    Fin.ext distanceTwo
  rw [hidx]
  exact mergeSelectedWord_isWelcomeCopy _ _ _ oldCopy (dataCopy _)

/-- One commit step keeps a copy a copy when the target is either outside the
write window or hit at bus index 2 of a `.double` store with copied data. -/
theorem welcomeCommitStep_lm1_target_isWelcomeCopy (files : IntegerRegisterFiles)
    (write : PreparedParsedMaskedWrite) (target : Fin Bank.lm1.capacity)
    (keeps : ∀ (width : PEMemory.Width) (address : Fin Bank.lm1.capacity)
        (d : WordBus) (s : PEWordSelection),
      write.destination = some ⟨.lm1, width, address⟩ → write.data = d →
      write.selection = s →
        (count .lm1 width ≤ distance .lm1 address target) ∨
        (width = .double ∧ distance .lm1 address target = 2 ∧
          IsWelcomeCopy (d ⟨2, by decide⟩)))
    (oldCopy : IsWelcomeCopy (files.lm1 target)) :
    IsWelcomeCopy ((welcomeCommitStep files write).lm1 target) := by
  cases write with
  | mk destination maskUpdate data selection =>
    cases maskUpdate with
    | some update =>
        simp only [welcomeCommitStep]
        exact oldCopy
    | none =>
        cases destination with
        | none =>
            simp only [welcomeCommitStep]
            exact oldCopy
        | some access =>
            cases access with
            | mk bank width address =>
                cases bank with
                | lm1 =>
                    simp only [welcomeCommitStep]
                    rw [writeDirectAccessMasked_lm1_apply]
                    rcases keeps width address data selection rfl rfl rfl with
                      outside | block
                    · rw [writeWordsMasked_preserves_outside .lm1 width files.lm1 address
                        target data selection.flags selection.longLong outside]
                      exact oldCopy
                    · obtain ⟨widthDouble, distanceTwo, dataCopy⟩ := block
                      subst widthDouble
                      exact writeWordsMasked_double_target_isWelcomeCopy files.lm1 address target
                        data selection.flags selection.longLong (fun _ => dataCopy) distanceTwo
                        oldCopy
                | lm0 =>
                    simp only [welcomeCommitStep]
                    rw [writeDirectAccessMasked_lm1_eq _ _ _ _ _ _ (by simp)]
                    exact oldCopy
                | grf0 =>
                    simp only [welcomeCommitStep]
                    rw [writeDirectAccessMasked_lm1_eq _ _ _ _ _ _ (by simp)]
                    exact oldCopy
                | grf1 =>
                    simp only [welcomeCommitStep]
                    rw [writeDirectAccessMasked_lm1_eq _ _ _ _ _ _ (by simp)]
                    exact oldCopy
                | t =>
                    simp only [welcomeCommitStep]
                    rw [writeDirectAccessMasked_lm1_eq _ _ _ _ _ _ (by simp)]
                    exact oldCopy

/-- **The copy fold.**  A commit list whose `.lm1` writes avoid the target or hit
it at bus index 2 of a `.double` store with copied data leaves a copy a copy. -/
theorem commitParsedMaskedWrites_lm1_target_isWelcomeCopy (files : IntegerRegisterFiles)
    (writes : List PreparedParsedMaskedWrite) (target : Fin Bank.lm1.capacity)
    (keeps : ∀ write ∈ writes, ∀ (width : PEMemory.Width)
        (address : Fin Bank.lm1.capacity) (data : WordBus) (selection : PEWordSelection),
      write.destination = some ⟨.lm1, width, address⟩ → write.data = data →
      write.selection = selection →
        (count .lm1 width ≤ distance .lm1 address target) ∨
        (width = .double ∧ distance .lm1 address target = 2 ∧
          IsWelcomeCopy (data ⟨2, by decide⟩)))
    (oldCopy : IsWelcomeCopy (files.lm1 target)) :
    IsWelcomeCopy ((commitParsedMaskedWrites files writes).lm1 target) := by
  induction writes generalizing files with
  | nil => simpa [commitParsedMaskedWrites] using oldCopy
  | cons write rest ih =>
      rw [commitParsedMaskedWrites_cons]
      apply ih
      · intro item member
        exact keeps item (List.mem_cons_of_mem _ member)
      · exact welcomeCommitStep_lm1_target_isWelcomeCopy files write target
          (fun width address data selection destination dataEq selectionEq =>
            keeps write (by simp) width address data selection destination dataEq
              selectionEq)
          oldCopy

/-- **The `.double` copy shape.**  If every `.lm1` destination among the
committed writes is a 4-aligned `.double` block whose third data word is a copy,
then an observed word `t` with `t % 4 = 2` stays a copy. -/
theorem commitParsedMaskedWrites_lm1_word_two_isWelcomeCopy
    (files : IntegerRegisterFiles) (writes : List PreparedParsedMaskedWrite)
    (target : Fin Bank.lm1.capacity) (targetMod : target.val % 4 = 2)
    (allDouble : ∀ write ∈ writes, ∀ (width : PEMemory.Width)
      (address : Fin Bank.lm1.capacity) (data : WordBus) (selection : PEWordSelection),
        write.destination = some ⟨.lm1, width, address⟩ → write.data = data →
        write.selection = selection → width = .double ∧ address.val % 4 = 0 ∧
          (∀ bound : 2 < 4, IsWelcomeCopy (data ⟨2, bound⟩)))
    (oldCopy : IsWelcomeCopy (files.lm1 target)) :
    IsWelcomeCopy ((commitParsedMaskedWrites files writes).lm1 target) := by
  apply commitParsedMaskedWrites_lm1_target_isWelcomeCopy files writes target _ oldCopy
  intro write mem width address data selection destination dataEq selectionEq
  obtain ⟨widthEq, aligned, dataCopy⟩ :=
    allDouble write mem width address data selection destination dataEq selectionEq
  subst widthEq
  have distanceMod : distance .lm1 address target % 4 = 2 := by
    have h := welcomeDistance_mod_four address.val target.val address.isLt aligned targetMod
    simpa [distance, Bank.capacity] using h
  by_cases atTwo : distance .lm1 address target = 2
  · exact Or.inr ⟨rfl, atTwo, dataCopy _⟩
  · left
    show 4 ≤ distance .lm1 address target
    rcases Nat.lt_or_ge (distance .lm1 address target) 4 with small | large
    · rw [Nat.mod_eq_of_lt small] at distanceMod
      omega
    · exact large


/-! ## 3. The prepared-write third data word is a copy -/

/-- The third bus word of an unpacked bus is the high word of its low half. -/
theorem unpackALUBus_word_two (bus : IntegerALU.Bus) (bound : 2 < 4) :
    unpackALUBus bus ⟨2, bound⟩ = bus.low.extractLsb' 32 32 :=
  unpackALUBus_of_val_eq_two bus _ rfl

/-- A flush only ANDs the bus, so it preserves a copy. -/
theorem flushBus_word_two_isWelcomeCopy (width : ProofsLean.MNCore.Masks.Width)
    (flags : BitVec 4) (data : IntegerALU.Bus)
    (copy : IsWelcomeCopy (data.low.extractLsb' 32 32)) :
    IsWelcomeCopy
      ((ProofsLean.MNCore.Masks.flushBus width flags data).low.extractLsb' 32 32) := by
  cases width with
  | long =>
      rw [ProofsLean.MNCore.Masks.long_flush_preserves_low]
      exact copy
  | double =>
      rw [show (ProofsLean.MNCore.Masks.flushBus .double flags data).low =
          data.low &&& (ProofsLean.MNCore.Masks.doubleMask flags).low from rfl]
      rw [BitVec.extractLsb'_and]
      exact isWelcomeCopy_and _ _ copy

/-- The flush-adjusted bus output of an integer ALU keeps a copy. -/
theorem parsedOutputAfterFlush_word_two_isWelcomeCopy (selection : Option PEWordSelection)
    (output : IntegerALU.Bus) (copy : IsWelcomeCopy (output.low.extractLsb' 32 32)) :
    IsWelcomeCopy ((parsedOutputAfterFlush selection output).low.extractLsb' 32 32) := by
  cases selection with
  | none => exact copy
  | some selected =>
      unfold parsedOutputAfterFlush
      exact flushBus_word_two_isWelcomeCopy _ _ _ copy

/-- **Prepared-write third data word, memory source.**  With both sources direct
memory reads and a zero low half of the first read, the prepared write's third
data word is zero, hence a copy. -/
theorem prepareParsedMaskedWriteWithForwarding_data_two_isWelcomeCopy_of_memory_low_zero
    (files : IntegerRegisterFiles) (slots : ProofsLean.MNCore.Forwarding.Slots)
    (cycle : Fin 4) (accesses : ParsedMaskedIntegerAccesses) (reduced : Bool)
    (write : PreparedParsedMaskedWrite)
    (sourceXAccess sourceYAccess : DirectMemoryAccess) (roundedX roundedY : Bool)
    (sourceX : accesses.sourceX = .memory sourceXAccess roundedX)
    (sourceY : accesses.sourceY = .memory sourceYAccess roundedY)
    (readX : (ParsedIntegerInput.applyRounding roundedX
      (pack (readDirectAccess files sourceXAccess))).low = 0)
    (precision : IntegerALU.Precision) (aluOp : IntegerALU.Op)
    (request : accesses.op.executionRequest = .ok (.integer precision aluOp))
    (prepared : prepareParsedMaskedWriteWithForwarding files slots cycle accesses reduced
      = .ok write) :
    ∀ bound : 2 < 4, IsWelcomeCopy (write.data ⟨2, bound⟩) := by
  intro bound
  obtain ⟨two, _⟩ :=
    prepareParsedMaskedWriteWithForwarding_data_two_three_zero_of_low_zero files slots cycle
      accesses reduced write sourceXAccess sourceYAccess roundedX roundedY sourceX sourceY
      readX precision aluOp request prepared
  rw [two bound]
  exact isWelcomeCopy_zero

/-- The fixed-source form of the prepared-write equation, with the second
source a direct memory read and the flush selection kept symbolic. -/
theorem prepareParsedMaskedWriteWithForwarding_fixed_eq_flush_general
    (files : IntegerRegisterFiles) (slots : ProofsLean.MNCore.Forwarding.Slots)
    (cycle : Fin 4) (accesses : ParsedMaskedIntegerAccesses) (reduced : Bool)
    (value : IntegerALU.Bus) (sourceX : accesses.sourceX = .fixed value)
    (sourceYAccess : DirectMemoryAccess) (roundedY : Bool)
    (sourceY : accesses.sourceY = .memory sourceYAccess roundedY)
    (precision : IntegerALU.Precision) (aluOp : IntegerALU.Op)
    (request : accesses.op.executionRequest = .ok (.integer precision aluOp)) :
    prepareParsedMaskedWriteWithForwarding files slots cycle accesses reduced =
      .ok { destination := some accesses.destination
            maskUpdate := none
            data := unpackALUBus (parsedOutputAfterFlush accesses.flushSelection
              (IntegerALU.evaluateBus precision aluOp value
                (ParsedIntegerInput.applyRounding roundedY
                  (pack (readDirectAccess files sourceYAccess))) reduced).value)
            selection := accesses.writeSelection } := by
  unfold prepareParsedMaskedWriteWithForwarding
  rw [sourceX, sourceY]
  simp [ParsedIntegerInput.readWithForwarding, ParsedIntegerInput.read,
    evaluateParsedIntegerAlu, request, evaluateParsedExecutionRequest]

/-- **Prepared-write third data word, `.fixed` source.**  If the first source is
a constant bus whose low-half high word is a copy, the prepared write's third
data word is a copy: the low half of `evaluateBus` is that constant (or zero). -/
theorem prepareParsedMaskedWriteWithForwarding_data_two_isWelcomeCopy_of_fixed
    (files : IntegerRegisterFiles) (slots : ProofsLean.MNCore.Forwarding.Slots)
    (cycle : Fin 4) (accesses : ParsedMaskedIntegerAccesses) (reduced : Bool)
    (write : PreparedParsedMaskedWrite) (value : IntegerALU.Bus)
    (sourceX : accesses.sourceX = .fixed value)
    (copy : IsWelcomeCopy (value.low.extractLsb' 32 32))
    (sourceYAccess : DirectMemoryAccess) (roundedY : Bool)
    (sourceY : accesses.sourceY = .memory sourceYAccess roundedY)
    (precision : IntegerALU.Precision) (aluOp : IntegerALU.Op)
    (request : accesses.op.executionRequest = .ok (.integer precision aluOp))
    (prepared : prepareParsedMaskedWriteWithForwarding files slots cycle accesses reduced
      = .ok write) :
    ∀ bound : 2 < 4, IsWelcomeCopy (write.data ⟨2, bound⟩) := by
  intro bound
  rw [prepareParsedMaskedWriteWithForwarding_fixed_eq_flush_general files slots cycle accesses
    reduced value sourceX sourceYAccess roundedY sourceY precision aluOp request] at prepared
  simp only [StepResult.ok.injEq] at prepared
  rw [← prepared]
  dsimp only
  rw [unpackALUBus_word_two]
  have lowCopy : IsWelcomeCopy
      ((IntegerALU.evaluateBus precision aluOp value
        (ParsedIntegerInput.applyRounding roundedY
          (pack (readDirectAccess files sourceYAccess))) reduced).value.low.extractLsb'
        32 32) := by
    rw [evaluateBus_value_low]
    split
    · exact copy
    · split
      · have zero : BitVec.extractLsb' 32 32 (0 : BitVec 64) = (0 : BitVec 32) := by
          decide
        rw [zero]
        exact isWelcomeCopy_zero
      · exact copy
  exact parsedOutputAfterFlush_word_two_isWelcomeCopy _ _ lowCopy


/-! ## 4. Narrow `LM1` writes leave an observed word untouched -/

theorem nat_advance_distance (start target : Nat) (hs : start < 4096) (ht : target < 4096) :
    (start + (target + 4096 - start) % 4096) % 4096 = target := by
  rcases Nat.lt_or_ge target start with hlt | hge
  · have h1 : target + 4096 - start < 4096 := by omega
    rw [Nat.mod_eq_of_lt h1]
    have h2 : start + (target + 4096 - start) = target + 4096 := by omega
    rw [h2, Nat.add_mod_right]
    exact Nat.mod_eq_of_lt ht
  · have h1 : target + 4096 - start = (target - start) + 4096 := by omega
    have h2 : target - start < 4096 := by omega
    have h3 : (target - start + 4096) % 4096 = target - start := by
      rw [Nat.add_mod_right, Nat.mod_eq_of_lt h2]
    rw [h1, h3]
    have h4 : start + (target - start) = target := by omega
    rw [h4, Nat.mod_eq_of_lt ht]

/-- `advance` inverts `distance`: the word at distance `d` from `start` is the
unique such word. -/
theorem advance_distance (start target : Fin Bank.lm1.capacity) :
    advance .lm1 start (distance .lm1 start target) = target := by
  apply Fin.ext
  have ht : target.val < 4096 := target.isLt
  have hs : start.val < 4096 := start.isLt
  change (start.val + distance .lm1 start target) % 4096 = target.val
  unfold distance
  change (start.val + (target.val + 4096 - start.val) % 4096) % 4096 = target.val
  exact nat_advance_distance start.val target.val hs ht

/-- An observed `LM1` word `0..15`, as a `Bank.lm1` address. -/
def lm1Target (word : Fin 16) : Fin Bank.lm1.capacity :=
  ⟨word.val, by have := word.isLt; change word.val < 4096; omega⟩

theorem lm1Target_injective {a b : Fin 16} (same : lm1Target a = lm1Target b) : a = b := by
  have values := congrArg Fin.val same
  exact Fin.ext (by simpa [lm1Target] using values)

/-- A window of at most two observed words has at most two members. -/
theorem card_window_le (start : Fin Bank.lm1.capacity) (size : Nat) (sizeTwo : size ≤ 2) :
    ((Finset.univ : Finset (Fin 16)).filter
      (fun t => distance .lm1 start (lm1Target t) < size)).card ≤ 2 := by
  classical
  let windowSet := (Finset.univ : Finset (Fin 16)).filter
    (fun t => distance .lm1 start (lm1Target t) < size)
  change windowSet.card ≤ 2
  rw [← Fintype.card_coe windowSet]
  calc Fintype.card ↥windowSet ≤ Fintype.card (Fin 2) := by
        apply Fintype.card_le_of_injective
          (fun t : ↥windowSet =>
            (⟨distance .lm1 start (lm1Target t.1), by
              have member := t.2
              simp only [windowSet, Finset.mem_filter, Finset.mem_univ, true_and] at member
              omega⟩ : Fin 2))
        intro a b same
        apply Subtype.ext
        have hd : distance .lm1 start (lm1Target a.1) =
            distance .lm1 start (lm1Target b.1) := by
          simpa using same
        have ea := advance_distance start (lm1Target a.1)
        have eb := advance_distance start (lm1Target b.1)
        exact lm1Target_injective (by rw [← ea, ← eb, hd])
    _ = 2 := by simp

/-- The union of the observed words covered by a list of narrow windows has at
most two words per window. -/
theorem card_covered_le : ∀ (windows : List (Fin Bank.lm1.capacity × Nat)),
    (∀ p ∈ windows, p.2 ≤ 2) →
    ((Finset.univ : Finset (Fin 16)).filter
      (fun t => ∃ p ∈ windows, distance .lm1 p.1 (lm1Target t) < p.2)).card ≤
      2 * windows.length := by
  classical
  intro windows
  induction windows with
  | nil => intro _; simp
  | cons p rest ih =>
      intro sizes
      have hsub : (Finset.univ.filter
            (fun t => ∃ q ∈ p :: rest, distance .lm1 q.1 (lm1Target t) < q.2)) ⊆
          (Finset.univ.filter (fun t => distance .lm1 p.1 (lm1Target t) < p.2)) ∪
          (Finset.univ.filter
            (fun t => ∃ q ∈ rest, distance .lm1 q.1 (lm1Target t) < q.2)) := by
        intro t member
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at member
        obtain ⟨q, qMem, covered⟩ := member
        rcases List.mem_cons.mp qMem with same | qMem
        · subst same
          exact Finset.mem_union_left _
            (Finset.mem_filter.mpr ⟨Finset.mem_univ _, covered⟩)
        · exact Finset.mem_union_right _
            (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨q, qMem, covered⟩⟩)
      calc (Finset.univ.filter
              (fun t => ∃ q ∈ p :: rest, distance .lm1 q.1 (lm1Target t) < q.2)).card
          ≤ ((Finset.univ.filter (fun t => distance .lm1 p.1 (lm1Target t) < p.2)) ∪
              (Finset.univ.filter
                (fun t => ∃ q ∈ rest, distance .lm1 q.1 (lm1Target t) < q.2))).card :=
            Finset.card_le_card hsub
        _ ≤ (Finset.univ.filter (fun t => distance .lm1 p.1 (lm1Target t) < p.2)).card +
              (Finset.univ.filter
                (fun t => ∃ q ∈ rest, distance .lm1 q.1 (lm1Target t) < q.2)).card :=
            Finset.card_union_le _ _
        _ ≤ 2 + 2 * rest.length := by
            apply Nat.add_le_add
            · exact card_window_le p.1 p.2 (sizes p (by simp))
            · exact ih (fun q qMem => sizes q (List.mem_cons_of_mem _ qMem))
        _ = 2 * (p :: rest).length := by
            rw [List.length_cons]
            omega

/-- **The counting half.**  At most four windows of at most two words each cover
at most eight of the sixteen observed words, so one observed word is untouched. -/
theorem exists_uncovered_of_windows (windows : List (Fin Bank.lm1.capacity × Nat))
    (bound : windows.length ≤ 4) (sizes : ∀ p ∈ windows, p.2 ≤ 2) :
    ∃ t : Fin 16, ∀ p ∈ windows, ¬ distance .lm1 p.1 (lm1Target t) < p.2 := by
  classical
  let covered := (Finset.univ : Finset (Fin 16)).filter
    (fun t => ∃ p ∈ windows, distance .lm1 p.1 (lm1Target t) < p.2)
  have bounds : covered.card ≤ 8 := by
    have small : covered.card ≤ 2 * windows.length := card_covered_le windows sizes
    have cap : 2 * windows.length ≤ 2 * 4 := Nat.mul_le_mul_left 2 bound
    omega
  have universeCard : (Finset.univ : Finset (Fin 16)).card = 16 := by simp
  have strict : covered.card < (Finset.univ : Finset (Fin 16)).card := by
    omega
  obtain ⟨t, _, untouched⟩ := Finset.exists_mem_notMem_of_card_lt_card strict
  refine ⟨t, ?_⟩
  intro p pMem covers
  exact untouched (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨p, pMem, covers⟩⟩)

/-- The initial PE 0 `LM1` word is zero on the all-zero input. -/
theorem welcomeZero_initial_lm1 (target : Fin Bank.lm1.capacity) :
    ((welcomeInitialState welcomeZeroWords).peRegisters welcomePE).lm1 target = 0 := by
  show (welcomeInitialPERegisters welcomeZeroWords).lm1 target = 0
  rw [welcomeInitialPERegisters_lm1]

/-- **The narrow refutation.**  If the all-zero PE 0 `LM1` file of the line is
the commit of a write list whose `.lm1` destinations are all covered by at most
four narrow windows, then some observed word keeps its initial `0`, so the line
cannot be correct. -/
theorem welcome_not_correct_of_lm1Narrow (line : InstructionLine) (next : State)
    (step : welcomeSealedMachine.step line (welcomeInitialState welcomeZeroWords) = some next)
    (writes : List PreparedParsedMaskedWrite)
    (committed : next.peRegisters welcomePE =
      commitParsedMaskedWrites ((welcomeInitialState welcomeZeroWords).peRegisters welcomePE)
        writes)
    (windows : List (Fin Bank.lm1.capacity × Nat))
    (covers : ∀ write ∈ writes, ∀ (width : PEMemory.Width)
        (address : Fin Bank.lm1.capacity),
      write.destination = some ⟨.lm1, width, address⟩ →
        (address, count .lm1 width) ∈ windows)
    (bound : windows.length ≤ 4) (sizes : ∀ p ∈ windows, p.2 ≤ 2) :
    ¬ ProofsLean.Correct welcomeSealedMachine welcomeSpec
      (([line] : List InstructionLine)) := by
  obtain ⟨t, uncovered⟩ := exists_uncovered_of_windows windows bound sizes
  have zero : (next.peRegisters welcomePE).lm1 (lm1Target t) = 0 := by
    rw [committed]
    apply commitParsedMaskedWrites_lm1_word_zero
      ((welcomeInitialState welcomeZeroWords).peRegisters welcomePE) writes (lm1Target t)
    · intro write writeMem width address data selection destination dataEq selectionEq
      subst dataEq selectionEq
      have member := covers write writeMem width address destination
      by_cases within : distance .lm1 address (lm1Target t) < count .lm1 width
      · exact absurd within (uncovered (address, count .lm1 width) member)
      · exact Or.inl (Nat.le_of_not_lt within)
    · exact welcomeZero_initial_lm1 (lm1Target t)
  exact welcome_not_correct_of_word_zero line next step t (by simpa [lm1Target] using zero)


/-! ## 5. The two sound write shapes and the reduction -/

/-- **The `.double` copy shape** of a line's all-zero PE 0 write list: every
`.lm1` destination is a 4-aligned `.double` block whose third bus word is a copy
(`0` or a submask of `0x80008000` at PE 0).  This is the sound replacement for
the `data₂ = 0` shape of `WelcomeProvenance.lean`, which a `.fixed .msb1` first
operand falsifies. -/
def WelcomePEDoubleCopyShape (expressions : List NormalizedExpr) : Prop :=
  ∀ next, welcomeSealedMachine.step (.pe expressions)
      (welcomeInitialState welcomeZeroWords) = some next →
    ∃ writes, next.peRegisters welcomePE =
        commitParsedMaskedWrites
          ((welcomeInitialState welcomeZeroWords).peRegisters welcomePE) writes ∧
      ∀ write ∈ writes, ∀ (width : PEMemory.Width)
        (address : Fin Bank.lm1.capacity) (data : WordBus)
        (selection : PEWordSelection),
          write.destination = some ⟨.lm1, width, address⟩ → write.data = data →
          write.selection = selection → width = .double ∧ address.val % 4 = 0 ∧
            (∀ bound : 2 < 4, IsWelcomeCopy (data ⟨2, bound⟩))

/-- **The narrow shape** of a line's all-zero PE 0 write list: every `.lm1`
destination lies in one of at most four windows of at most two words.  Four
cycles of a `.word`/`.long` destination cover at most eight words, which is the
counting half of the value argument. -/
def WelcomePENarrowShape (expressions : List NormalizedExpr) : Prop :=
  ∀ next, welcomeSealedMachine.step (.pe expressions)
      (welcomeInitialState welcomeZeroWords) = some next →
    ∃ (writes : List PreparedParsedMaskedWrite)
      (windows : List (Fin Bank.lm1.capacity × Nat)),
      next.peRegisters welcomePE =
        commitParsedMaskedWrites
          ((welcomeInitialState welcomeZeroWords).peRegisters welcomePE) writes ∧
      (∀ write ∈ writes, ∀ (width : PEMemory.Width)
        (address : Fin Bank.lm1.capacity),
          write.destination = some ⟨.lm1, width, address⟩ →
            (address, count .lm1 width) ∈ windows) ∧
      windows.length ≤ 4 ∧ (∀ window ∈ windows, window.2 ≤ 2)

/-- **The `.double` copy case is closed.**  A line whose all-zero PE 0 write list
is all copied `.double` blocks leaves word 2 a copy, hence not `1`. -/
theorem welcome_not_correct_of_doubleCopyShape (expressions : List NormalizedExpr)
    (shape : WelcomePEDoubleCopyShape expressions) :
    ¬ ProofsLean.Correct welcomeSealedMachine welcomeSpec
      (([InstructionLine.pe expressions] : List InstructionLine)) := by
  cases step : welcomeSealedMachine.step (.pe expressions)
      (welcomeInitialState welcomeZeroWords) with
  | none => exact welcome_not_correct_of_step_none _ step
  | some next =>
      obtain ⟨writes, committed, allDouble⟩ := shape next step
      have copy : IsWelcomeCopy
          ((next.peRegisters welcomePE).lm1 (lm1Target ⟨2, by decide⟩)) := by
        rw [committed]
        apply commitParsedMaskedWrites_lm1_word_two_isWelcomeCopy _ writes
          (lm1Target ⟨2, by decide⟩) (by decide) allDouble
        rw [welcomeZero_initial_lm1]
        exact isWelcomeCopy_zero
      exact welcome_not_correct_of_word_ne_one (.pe expressions) next step
        ⟨2, by decide⟩ (by simpa [lm1Target] using isWelcomeCopy_ne_one copy)

/-- **The narrow case is closed.**  A line whose all-zero PE 0 write list is
covered by at most four narrow windows leaves some observed word at `0`. -/
theorem welcome_not_correct_of_narrowShape (expressions : List NormalizedExpr)
    (shape : WelcomePENarrowShape expressions) :
    ¬ ProofsLean.Correct welcomeSealedMachine welcomeSpec
      (([InstructionLine.pe expressions] : List InstructionLine)) := by
  cases step : welcomeSealedMachine.step (.pe expressions)
      (welcomeInitialState welcomeZeroWords) with
  | none => exact welcome_not_correct_of_step_none _ step
  | some next =>
      obtain ⟨writes, windows, committed, covers, bound, sizes⟩ := shape next step
      exact welcome_not_correct_of_lm1Narrow (.pe expressions) next step writes committed
        windows covers bound sizes

/-- **The exact remaining per-line statement.**  Every unrefuted one-line `.pe`
program satisfies one of the three value shapes that the refutations of this
module consume:

* `WelcomePEDoubleCopyShape` — all `LM1` writes are copied `.double` blocks;
* `WelcomePENarrowShape` — the `LM1` writes fit in four windows of two words;
* `WelcomePEInputIndependent` — the `PE 0 LM1` output does not depend on the
  input (the constant-producer case, refuted on the all-five input).

This is **not** implied by the residual class of `WelcomeBoundTwo.lean`; it is
the executor link that remains.  It is not vacuous, because `WelcomePEUnrefuted`
is inhabited (`welcomePEUnrefuted_inhabited`), and the third disjunct is the
already-proved `WelcomePEInputIndependent`, not an assumption about it. -/
def WelcomePELm1WriteShapeObligation : Prop :=
  ∀ expressions : List NormalizedExpr, WelcomePEUnrefuted expressions →
    WelcomePEDoubleCopyShape expressions ∨ WelcomePENarrowShape expressions ∨
      WelcomePEInputIndependent expressions

/-- **Lower bound two from the three sound write shapes.** -/
theorem welcomeLowerBound_two_of_lm1WriteShapes
    (open_ : WelcomePELm1WriteShapeObligation) :
    ProofsLean.LowerBound welcomeSealedMachine welcomeSpec 2 := by
  apply welcomeLowerBound_two_of_unrefuted
  intro expressions unrefuted
  rcases open_ expressions unrefuted with shape | shape | shape
  · exact welcome_not_correct_of_doubleCopyShape expressions shape
  · exact welcome_not_correct_of_narrowShape expressions shape
  · exact welcome_not_correct_of_inputIndependentLM1 (.pe expressions) shape

/-- **`Optimal` from the three sound write shapes.**  `welcomeAnswer_correct` is
already proved, so the lower bound gives `Optimal` immediately. -/
theorem welcomeAnswer_optimal_of_lm1WriteShapes
    (open_ : WelcomePELm1WriteShapeObligation) :
    ProofsLean.Optimal welcomeSealedMachine welcomeSpec welcomeAnswer :=
  welcomeAnswer_optimal_of_lowerBound (welcomeLowerBound_two_of_lm1WriteShapes open_)


/-! ## 6. The write-list forms of the shapes

The two shapes are stated at the step level above because that is what
`WelcomeWriteProvenance` produces.  The corresponding *write-list* predicates
below are the form in which the per-cycle analysis of
`prepareParsedIntegerALUExprCycles` and of the MAU / L1BM / L2BM stages has to
be carried out. -/

/-- Every `.lm1` destination of the write list is a 4-aligned `.double` block
with a copied third data word. -/
def Lm1WritesDoubleCopy (writes : List PreparedParsedMaskedWrite) : Prop :=
  ∀ write ∈ writes, ∀ (width : PEMemory.Width)
    (address : Fin Bank.lm1.capacity) (data : WordBus) (selection : PEWordSelection),
      write.destination = some ⟨.lm1, width, address⟩ → write.data = data →
      write.selection = selection → width = .double ∧ address.val % 4 = 0 ∧
        (∀ bound : 2 < 4, IsWelcomeCopy (data ⟨2, bound⟩))

/-- The `.lm1` destinations of the write list lie in at most four windows of at
most two words. -/
def Lm1WritesNarrow (writes : List PreparedParsedMaskedWrite) : Prop :=
  ∃ windows : List (Fin Bank.lm1.capacity × Nat),
    (∀ write ∈ writes, ∀ (width : PEMemory.Width) (address : Fin Bank.lm1.capacity),
      write.destination = some ⟨.lm1, width, address⟩ →
        (address, count .lm1 width) ∈ windows) ∧
    windows.length ≤ 4 ∧ (∀ window ∈ windows, window.2 ≤ 2)

theorem lm1WritesDoubleCopy_word_two_isWelcomeCopy
    (writes : List PreparedParsedMaskedWrite) (shape : Lm1WritesDoubleCopy writes) :
    IsWelcomeCopy
      ((commitParsedMaskedWrites
        ((welcomeInitialState welcomeZeroWords).peRegisters welcomePE) writes).lm1
        (lm1Target ⟨2, by decide⟩)) :=
  commitParsedMaskedWrites_lm1_word_two_isWelcomeCopy _ writes
    (lm1Target ⟨2, by decide⟩) (by decide) shape
    (by rw [welcomeZero_initial_lm1]; exact isWelcomeCopy_zero)

theorem lm1WritesNarrow_exists_uncovered (writes : List PreparedParsedMaskedWrite)
    (shape : Lm1WritesNarrow writes) :
    ∃ t : Fin 16, ∀ write ∈ writes, ∀ (width : PEMemory.Width)
      (address : Fin Bank.lm1.capacity),
        write.destination = some ⟨.lm1, width, address⟩ →
          count .lm1 width ≤ distance .lm1 address (lm1Target t) := by
  obtain ⟨windows, covers, bound, sizes⟩ := shape
  obtain ⟨t, uncovered⟩ := exists_uncovered_of_windows windows bound sizes
  refine ⟨t, ?_⟩
  intro write writeMem width address destination
  have member := covers write writeMem width address destination
  by_cases within : distance .lm1 address (lm1Target t) < count .lm1 width
  · exact absurd within (uncovered (address, count .lm1 width) member)
  · exact Nat.le_of_not_lt within

/-! ## 7. The remaining per-producer-family obligations

Each `Prop` below is the exact statement still missing for one producer family.
None is assumed anywhere in this module, and each is stated **without** the
residual-class hypothesis that made the round-28 obligations vacuous.  The
common body `WelcomePEWriteShape` is `double-copy ∨ narrow ∨ input-independent`.

The `WelcomePEInputIndependent` disjunct is already refuted
(`welcome_not_correct_of_inputIndependentLM1`); it is the case of the
constant producers `.zero` and `.immediate`, whose outputs ignore both operand
buses (`Issue.zero_execution_ignores_inputs`,
`Issue.immediate_execution_ignores_inputs`). -/

/-- The common shape body consumed by the reduction. -/
def WelcomePEWriteShape (expressions : List NormalizedExpr) : Prop :=
  WelcomePEDoubleCopyShape expressions ∨ WelcomePENarrowShape expressions ∨
    WelcomePEInputIndependent expressions

/-- **Obligation (plain integer-ALU lines).**  Every unrefuted line whose rows are
all `.alu` / `.zero` / `.immediate` has one of the three value shapes.

What is already available for this family:

* the commit form of the shape is proved (`WelcomeWriteProvenance` through
  `welcomeWriteProvenance_of_plainIntegerALU`);
* the *third data word* half of the `.double` shape is proved per cycle for the
  direct-access branch, for both source kinds: `memory` sources through
  `prepareParsedIntegerALUExprCycle_alu_direct_double_zero` (zero low half at
  PE 0) and `.fixed` sources through
  `prepareParsedIntegerALUExprCycle_alu_direct_double_copy_of_fixed` (which
  covers the `.fixed .msb1` case that falsifies the round-28 `data₂ = 0` shape);
* the narrow counting half is proved (`lm1WritesNarrow_exists_uncovered`).

What is missing: the per-cycle *destination* analysis of
`prepareParsedIntegerALUExprCycles` for the branches other than the direct one
(`toDirectMaskedIntegerWritesInLine?`, `parsedIntegerMaskExprAccessesInLine?`,
`parsedIntegerNoWriteExprAccessesInLine?`, `parsedIntegerBarExprAccessesInLine?`,
`parsedIntegerMaskInputExprAccessesInLine?`,
`parsedIntegerMaskMemoryThenInputExprAccessesInLine?`,
`parsedIntegerMaskInputThenMemoryExprAccessesInLine?`, and the constant branch
`prepareParsedMaskedConstantWrites`), together with the `writesUnique` link that
makes the whole line's `.lm1` writes the four cycles of the single `.lm1`
access.  `.alu` rows with `.double` destinations need the double-copy or
input-independent branch; `.alu` rows with `.word`/`.long` destinations need the
narrow branch; `.immediate` rows need input-independence
(`immediateExcludesLm0`); `.zero` rows write the zero bus, so their third data
word is zero (double-copy) and their first two words are `0` as well. -/
def WelcomePEPlainShapeObligation : Prop :=
  ∀ expressions : List NormalizedExpr, WelcomePEUnrefuted expressions →
    (expressions.map NormalizedExpr.toParsed).all parsedExprIsPlainIntegerALU = true →
    WelcomePEWriteShape expressions

/-- **Obligation (lines with a non-plain row).**  The counterpart of
`WelcomePEPlainShapeObligation` for lines that contain at least one row outside
the plain integer-ALU class: `.matrixRead`, a `.mau` family (matrix MAU, float
MAU, float relu, block float), `.matrixWrite`, an L1BM producer (including
`.distrib`) or an L2BM producer.  These rows bypass
`prepareParsedIntegerALUExprCycle` and are prepared by
`prepareParsedMatrixReadExprCycles`, `executeParsedFloatMAUsAtPE`,
`executeParsedMatrixMAUAndWrites`, `executeParsedSharedBlockProducers`,
`executeParsedL1ToPEProducers` and the L2BM stage.  None of those stages has a
write-shape lemma yet, and their `.lm1` data words are not covered by the
`evaluateBus` copy fact. -/
def WelcomePEOtherShapeObligation : Prop :=
  ∀ expressions : List NormalizedExpr, WelcomePEUnrefuted expressions →
    (expressions.map NormalizedExpr.toParsed).all parsedExprIsPlainIntegerALU = false →
    WelcomePEWriteShape expressions

/-- The aggregate obligation follows from its plain and non-plain halves. -/
theorem welcomePELm1WriteShapeObligation_of_two (plain : WelcomePEPlainShapeObligation)
    (other : WelcomePEOtherShapeObligation) : WelcomePELm1WriteShapeObligation := by
  intro expressions unrefuted
  by_cases allPlain : (expressions.map NormalizedExpr.toParsed).all
      parsedExprIsPlainIntegerALU = true
  · exact plain expressions unrefuted allPlain
  · have notPlain : (expressions.map NormalizedExpr.toParsed).all
        parsedExprIsPlainIntegerALU = false := by
      cases h : (expressions.map NormalizedExpr.toParsed).all
          parsedExprIsPlainIntegerALU <;> simp_all
    exact other expressions unrefuted notPlain

/-! ### Per-family specialisations of the non-plain obligation

These record exactly which producer families the aggregate non-plain obligation
still contains.  Each is the same shape statement restricted to lines containing
that producer. -/

/-- Obligation (`.matrixRead` rows): `prepareParsedMatrixReadExprCycles` writes
`.double` blocks whose third data word is a copy, or narrow writes, or the matrix
read is input-independent. -/
def WelcomePEMatrixReadShapeObligation : Prop :=
  ∀ expressions : List NormalizedExpr, WelcomePEUnrefuted expressions →
    (expressions.map NormalizedExpr.toParsed).any parsedExprIsMatrixReadProducer = true →
    WelcomePEWriteShape expressions

/-- Obligation (`.mau` matrix family): `executeParsedMatrixMAUProducer` and
`executeParsedMatrixWritesAtMABs`. -/
def WelcomePEMatrixMAUShapeObligation : Prop :=
  ∀ expressions : List NormalizedExpr, WelcomePEUnrefuted expressions →
    (expressions.map NormalizedExpr.toParsed).any parsedExprIsMatrixMAUProducer = true →
    WelcomePEWriteShape expressions

/-- Obligation (`.mau` float family): `executeParsedFloatMAUsAtPE`. -/
def WelcomePEFloatMAUShapeObligation : Prop :=
  ∀ expressions : List NormalizedExpr, WelcomePEUnrefuted expressions →
    (expressions.map NormalizedExpr.toParsed).any parsedExprIsSupportedFloatMAUProducer = true →
    WelcomePEWriteShape expressions

/-- Obligation (`.matrixWrite` rows): `executeParsedMatrixWritesAtMABs`. -/
def WelcomePEMatrixWriteShapeObligation : Prop :=
  ∀ expressions : List NormalizedExpr, WelcomePEUnrefuted expressions →
    (expressions.map NormalizedExpr.toParsed).any parsedExprIsMatrixWriteProducer = true →
    WelcomePEWriteShape expressions

/-- Obligation (`.l1bm` rows, including `.distrib`): the L1BM-to-PE producer
stage. -/
def WelcomePEL1ToPEShapeObligation : Prop :=
  ∀ expressions : List NormalizedExpr, WelcomePEUnrefuted expressions →
    (expressions.map NormalizedExpr.toParsed).any parsedExprIsL1ToPEProducer = true →
    WelcomePEWriteShape expressions

/-- Obligation (`.l2bm` rows): the L2BM producer stage. -/
def WelcomePEL2BMShapeObligation : Prop :=
  ∀ expressions : List NormalizedExpr, WelcomePEUnrefuted expressions →
    (expressions.map NormalizedExpr.toParsed).any parsedExprIsL2BMProducer = true →
    WelcomePEWriteShape expressions


/-! ## 8. The `.fixed` constants at PE 0 are copies, and the per-cycle `.double`
write shape for a `.fixed` first operand -/

theorem replicateIntegerLane_zero_copy (precision : IntegerALU.Precision) :
    IsWelcomeCopy ((replicateIntegerLane precision 0).low.extractLsb' 32 32) := by
  cases precision <;> unfold IsWelcomeCopy <;> decide

theorem replicateIntegerLane_msb1_copy (precision : IntegerALU.Precision) :
    IsWelcomeCopy
      ((replicateIntegerLane precision (2 ^ (precision.width - 1))).low.extractLsb' 32 32) := by
  cases precision <;> unfold IsWelcomeCopy <;> decide

/-- Every `.fixed` value at PE 0 is zero except `.msb1`, whose lane replication
is `2 ^ (width - 1)`. -/
theorem welcomeFixedValue (fixed : ParsedFixed) (precision : IntegerALU.Precision) :
    ParsedFixed.integerValue fixed precision
      (ParsedIntegerContext.ofLinearIndex welcomePE).group
      (ParsedIntegerContext.ofLinearIndex welcomePE).l2b
      (ParsedIntegerContext.ofLinearIndex welcomePE).l1b
      (ParsedIntegerContext.ofLinearIndex welcomePE).mab
      (ParsedIntegerContext.ofLinearIndex welcomePE).pe =
      match fixed with
      | .msb1 => 2 ^ (precision.width - 1)
      | _ => 0 := by
  rw [parsed_fixed_integerValue_ofLinearIndex]
  cases fixed <;> simp [welcomePE]

/-- **Every `.fixed` bus at PE 0 is a copy.** -/
theorem welcomeFixedBus_isWelcomeCopy (fixed : ParsedFixed)
    (precision : IntegerALU.Precision) :
    IsWelcomeCopy
      ((replicateIntegerLane precision
        (ParsedFixed.integerValue fixed precision
          (ParsedIntegerContext.ofLinearIndex welcomePE).group
          (ParsedIntegerContext.ofLinearIndex welcomePE).l2b
          (ParsedIntegerContext.ofLinearIndex welcomePE).l1b
          (ParsedIntegerContext.ofLinearIndex welcomePE).mab
          (ParsedIntegerContext.ofLinearIndex welcomePE).pe)).low.extractLsb' 32 32) := by
  rw [welcomeFixedValue]
  cases fixed
  · exact replicateIntegerLane_zero_copy precision
  · exact replicateIntegerLane_zero_copy precision
  · exact replicateIntegerLane_zero_copy precision
  · exact replicateIntegerLane_zero_copy precision
  · exact replicateIntegerLane_zero_copy precision
  · exact replicateIntegerLane_msb1_copy precision

/-- **The per-cycle `.double` shape for a `.fixed` first operand.**  A direct
access integer ALU cycle whose lowered destination is an `.lm1` `.double` block
prepares exactly one write to that block, and its third data word is a copy even
when the first operand is `.fixed .msb1` — the counterexample that refuted the
`data₂ = 0` shape of `WelcomeProvenance.lean`. -/
theorem prepareParsedIntegerALUExprCycle_alu_direct_double_copy_of_fixed
    (files : IntegerRegisterFiles) (oldSlots nextSlots : ProofsLean.MNCore.Forwarding.Slots)
    (expression : ParsedExpr) (control : ParsedMaskExecutionControl)
    (hasSingleLineMask noForward reduced : Bool) (cycle : Fin 4)
    (accesses : ParsedMaskedIntegerAccesses) (write : PreparedParsedMaskedWrite)
    (address : Fin Bank.lm1.capacity) (value : IntegerALU.Bus)
    (isAlu : ∃ name precision unsigned arg, expression.op = .alu name precision unsigned arg)
    (lowered : ParsedExpr.toDirectMaskedIntegerAccessesInLine? expression files.maskRegisters
      control.directive hasSingleLineMask control.context.group control.context.l2b
      control.context.l1b control.context.mab control.context.pe cycle control.context.bar0
      control.context.bar1 control.context.tWord = some accesses)
    (sourceX : accesses.sourceX = .fixed value)
    (copy : IsWelcomeCopy (value.low.extractLsb' 32 32))
    (sourceYAccess : DirectMemoryAccess) (roundedY : Bool)
    (sourceY : accesses.sourceY = .memory sourceYAccess roundedY)
    (precision : IntegerALU.Precision) (aluOp : IntegerALU.Op)
    (request : accesses.op.executionRequest = .ok (.integer precision aluOp))
    (destination : accesses.destination = ⟨.lm1, .double, address⟩)
    (prepared : prepareParsedMaskedWriteWithForwarding files oldSlots cycle accesses reduced
      = .ok write) :
    ∃ slots,
      prepareParsedIntegerALUExprCycle files oldSlots nextSlots expression control
          hasSingleLineMask noForward reduced cycle = .ok ([write], slots) ∧
      write.destination = some ⟨.lm1, .double, address⟩ ∧
      (∀ bound : 2 < 4, IsWelcomeCopy (write.data ⟨2, bound⟩)) := by
  have dataCopy :=
    prepareParsedMaskedWriteWithForwarding_data_two_isWelcomeCopy_of_fixed files oldSlots cycle
      accesses reduced write value sourceX copy sourceYAccess roundedY sourceY precision aluOp
      request prepared
  have destinationEq : write.destination = some ⟨.lm1, .double, address⟩ := by
    rw [prepareParsedMaskedWriteWithForwarding_fixed_eq_flush_general files oldSlots cycle
      accesses reduced value sourceX sourceYAccess roundedY sourceY precision aluOp request]
      at prepared
    simp only [StepResult.ok.injEq] at prepared
    rw [← prepared, destination]
  have updated : ∃ slots,
      updateParsedIntegerALUForwardingCycle nextSlots cycle (.ok write) noForward = .ok slots := by
    cases noForward <;> simp [updateParsedIntegerALUForwardingCycle]
  obtain ⟨slots, updatedEq⟩ := updated
  exact ⟨slots,
    prepareParsedIntegerALUExprCycle_alu_direct files oldSlots nextSlots expression control
      hasSingleLineMask noForward reduced cycle accesses write slots isAlu lowered prepared
      updatedEq,
    destinationEq, dataCopy⟩


/-! ## 9. The issue checker allows at most one `LM1` writer per line -/

theorem welcomeWritesUnique (expressions : List NormalizedExpr)
    (legal : LegalParsedLine (expressions.map NormalizedExpr.toParsed)) :
    writesUnique (projectLine (expressions.map NormalizedExpr.toParsed)) := by
  unfold LegalParsedLine at legal
  exact legal.2.2.2.2.2.2.1

/-- The accepted issue checker gives the legality record of the line. -/
theorem welcomePEUnrefuted_legal (expressions : List NormalizedExpr)
    (unrefuted : WelcomePEUnrefuted expressions) :
    LegalParsedLine (expressions.map NormalizedExpr.toParsed) :=
  parsed_topline_check_sound (.pe (expressions.map NormalizedExpr.toParsed)) unrefuted.1.1

/-- Each expression's own `LM1` write list is duplicate free. -/
theorem welcomeLm1WritesNodup (expressions : List NormalizedExpr)
    (legal : LegalParsedLine (expressions.map NormalizedExpr.toParsed)) :
    ∀ expression ∈ projectLine (expressions.map NormalizedExpr.toParsed),
      expression.writeBanks.Nodup :=
  (welcomeWritesUnique expressions legal).1

/-- **At most one expression of an accepted line writes PE bank `LM1`.**  This is
the `writesUnique` half of the issue checker, extracted for the value argument:
the four cycles of the single `LM1` destination are the whole line's `LM1` write
list. -/
theorem welcomeLm1Writer_unique (expressions : List NormalizedExpr)
    (legal : LegalParsedLine (expressions.map NormalizedExpr.toParsed)) :
    ∀ expression ∈ projectLine (expressions.map NormalizedExpr.toParsed),
      ∀ other ∈ projectLine (expressions.map NormalizedExpr.toParsed),
        Issue.Bank.lm1 ∈ expression.writeBanks → Issue.Bank.lm1 ∈ other.writeBanks →
          expression = other := by
  have unique := welcomeWritesUnique expressions legal
  have ids := projectLine_idsUnique (expressions.map NormalizedExpr.toParsed)
  intro expression member other otherMember first second
  by_contra different
  exact unique.2 expression member other otherMember Issue.Bank.lm1 first Issue.Bank.lm1 second
    (fun same => different (ids expression member other otherMember same)) rfl


/-! ## 10. The write-list-level target for the plain integer-ALU class

For plain lines the commit form is already proved (`WelcomeWriteProvenance`
through `welcomeWriteProvenance_of_plainIntegerALU`), so the only missing
content is the shape of the executor's own prepared write list.  The target
below states exactly that: the same existential carries the commit equation and
one of the two write-list shapes, and the input-independent case is kept as a
separate disjunct for the constant producers. -/

/-- **The plain-class target, at the write-list level.**  For every unrefuted
plain line, either the PE 0 `LM1` output is input-independent, or the executor's
all-zero write list is committed and is all copied `.double` blocks or fits in
four narrow windows. -/
def WelcomePEPlainShapeTarget : Prop :=
  ∀ expressions : List NormalizedExpr, WelcomePEUnrefuted expressions →
    (expressions.map NormalizedExpr.toParsed).all parsedExprIsPlainIntegerALU = true →
    WelcomePEInputIndependent expressions ∨
      ∀ next, welcomeSealedMachine.step (.pe expressions)
          (welcomeInitialState welcomeZeroWords) = some next →
        ∃ writes, next.peRegisters welcomePE =
            commitParsedMaskedWrites
              ((welcomeInitialState welcomeZeroWords).peRegisters welcomePE) writes ∧
          (Lm1WritesDoubleCopy writes ∨ Lm1WritesNarrow writes)

/-- **The plain-class target implies the plain-class shape obligation.** -/
theorem welcomePEPlainShapeObligation_of_target (target : WelcomePEPlainShapeTarget) :
    WelcomePEPlainShapeObligation := by
  intro expressions unrefuted plain
  rcases target expressions unrefuted plain with independent | shape
  · exact Or.inr (Or.inr independent)
  · cases step : welcomeSealedMachine.step (.pe expressions)
        (welcomeInitialState welcomeZeroWords) with
    | none =>
        exact Or.inl (fun next step' => by rw [step] at step'; simp at step')
    | some next =>
        obtain ⟨writes, committed, double | narrow⟩ := shape next step
        · refine Or.inl ?_
          intro next' step'
          rw [step] at step'
          obtain rfl : next' = next := (Option.some.inj step').symm
          exact ⟨writes, committed, double⟩
        · refine Or.inr (Or.inl ?_)
          obtain ⟨windows, covers, bound, sizes⟩ := narrow
          intro next' step'
          rw [step] at step'
          obtain rfl : next' = next := (Option.some.inj step').symm
          exact ⟨writes, windows, committed, covers, bound, sizes⟩

end ProofsLean.MNCore

