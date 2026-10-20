import ProofsLean.WelcomeLowerBoundTwo

/-! # Bound two for the sealed Welcome machine: the value core and the two-sided gap

`WelcomeLowerBoundTwo.lean` reduces `LowerBound welcomeSealedMachine welcomeSpec 2`
to the refutation of the class `WelcomePEUnrefuted`: a `.pe` line that passes the
issue checker, has no pending `wait` tag, has no Rust-unsupported ALU row, has only
supported producers, is not all-`.noforward` and is not a single Welcome `iinc` row.

This module does three things.

## 1. The low half of an integer ALU result is a copy or zero

The value argument of the two-sided refutation rests on one fact about
`IntegerALU.evaluateBus`: the low 64-bit half of a result is **never computed**.
It is the low half of the first operand (`passa`), or zero (reduced operand), or a
plain copy of the first operand's low half. The same holds after a flush, because
`Masks.flushBus` only applies an AND mask. Consequently the third and fourth
32-bit words of any integer-ALU write (`unpackALUBus` indices 2 and 3) are
*copies of source words or zero*: they can never be a computed function such as
`input i + 1`.

* `evaluateBus_value_low`, `evaluateBus_value_low_zero` — the low half is copied
  or zeroed, never computed.
* `unpackALUBus_of_val_eq_two`, `unpackALUBus_of_val_eq_three`,
  `unpackALUBus_two_zero_of_low_zero`, `unpackALUBus_three_zero_of_low_zero`.
* `flushBus_low_zero`, `parsedOutputAfterFlush_low_zero` — a flush preserves a
  zero low half.
* `prepareParsedMaskedWriteWithForwarding_data_two_three_zero` — **the copy fact
  for a prepared ALU write**: if both memory sources of the access read the zero
  bus, the prepared write's data words 2 and 3 are zero. This is exactly what a
  `.double` destination writes into the third and fourth words of its block.

## 2. The all-zero initial state reads zero in every bank

`welcomeZero_readDirectAccess_zero` and `welcomeZero_pack_readDirectAccess_zero`
prove that on the all-zero input every register bank of the initial PE file reads
zero, so the hypothesis of the copy fact holds for every access.

## 3. The two-sided reduction, proved at the state level

The remaining gap is narrowed by two proved refutations.

* **Zero word.** If, on the all-zero input, *any* PE 0 LM1 word is still zero
  after the line, the spec is violated there (`welcome_not_correct_of_word_zero`).
  So only lines that rewrite all sixteen words can remain.
* **Input-independent output.** If the PE 0 LM1 output of the line is the same
  for the all-zero input and for the all-five input, the line is refuted: the
  spec demands `1` for the first and `6` for the second
  (`welcome_not_correct_of_inputIndependentLM1`). This is the case that the
  constant-producing rows (`.immediate`, `.zero`) fall into, since
  `Issue.immediate_execution_ignores_inputs` and
  `Issue.zero_execution_ignores_inputs` say their execution request ignores the
  operand buses.

`WelcomePEResidual` is therefore the **exact** residual class: accepted,
non-trivial `.pe` lines that rewrite all sixteen words on the all-zero input and
whose PE 0 LM1 output is *not* input-independent.
`welcomeLowerBound_two_of_residual` proves the bound from a refutation of that
class, and `welcomeLowerBound_two_iff_residual` shows the two statements are
equivalent, so the reduction is not a weakening.

The bound itself is **not** proved here. What remains after this module is exactly
`WelcomePEResidual → ¬ Correct ...`: lines that write all sixteen words with
input-dependent data. The missing executor link is named as an exact Lean
statement, `WelcomeWriteProvenance` (a `Prop`, not an axiom): the PE 0 register
file after a `.pe` line is the commit of a list of prepared writes. Nothing in
this module assumes it. Once it is proved, the `.double` block argument can be
assembled from `writeWordsMasked_double_block_two` (the block word at `start + 2`
stays zero because its bus word is zero) and the copy fact above; the remaining
per-opcode work is the width/address analysis of
`prepareParsedIntegerALUExprCycles` and `prepareParsedIntegerMatrixReadLineExpression`,
whose uncovered families are named in the docstring of `WelcomePEResidual`.

No `sorry`, no `admit`, no `native_decide`, no new axioms.
-/

namespace ProofsLean.MNCore

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

open Issue
open PEMemory

/-! ## 1. The low half of an integer ALU result is a copy or zero -/

/-- The low half of an ALU bus is returned by `evaluateBus` unchanged, except for
`passa` and for a reduced first operand (zero result). -/
theorem evaluateBus_value_low (p : IntegerALU.Precision) (op : IntegerALU.Op)
    (x y : IntegerALU.Bus) (reduced : Bool) :
    (IntegerALU.evaluateBus p op x y reduced).value.low =
      (if op = .passa then x.low else if reduced then 0 else x.low) := rfl

/-- A zero low half of the first operand gives a zero low half of the result: the
low half is copied or zeroed, never computed. -/
theorem evaluateBus_value_low_zero (p : IntegerALU.Precision) (op : IntegerALU.Op)
    (x y : IntegerALU.Bus) (reduced : Bool) (hx : x.low = 0) :
    (IntegerALU.evaluateBus p op x y reduced).value.low = 0 := by
  rw [evaluateBus_value_low]
  split <;> simp_all

/-- The third 32-bit word of an unpacked bus is the low half's high word. -/
theorem unpackALUBus_of_val_eq_two (bus : IntegerALU.Bus) (index : Fin 4)
    (value : index.val = 2) :
    unpackALUBus bus index = bus.low.extractLsb' 32 32 := by
  simp [unpackALUBus, value]

/-- The fourth 32-bit word of an unpacked bus is the low half's low word. -/
theorem unpackALUBus_of_val_eq_three (bus : IntegerALU.Bus) (index : Fin 4)
    (value : index.val = 3) :
    unpackALUBus bus index = bus.low.extractLsb' 0 32 := by
  simp [unpackALUBus, value]

/-- Bus word 2 of a bus with a zero low half is zero, in proof-polymorphic form. -/
theorem unpackALUBus_two_zero (bus : IntegerALU.Bus) (h : bus.low = 0)
    (bound : 2 < 4) :
    unpackALUBus bus ⟨2, bound⟩ = 0 := by
  rw [unpackALUBus_of_val_eq_two bus _ rfl, h]
  simp

/-- Bus word 3 of a bus with a zero low half is zero, in proof-polymorphic form. -/
theorem unpackALUBus_three_zero (bus : IntegerALU.Bus) (h : bus.low = 0)
    (bound : 3 < 4) :
    unpackALUBus bus ⟨3, bound⟩ = 0 := by
  rw [unpackALUBus_of_val_eq_three bus _ rfl, h]
  simp

/-- A flush only ANDs the bus, so it preserves a zero low half. -/
theorem flushBus_low_zero (width : ProofsLean.MNCore.Masks.Width)
    (flags : BitVec 4) (data : IntegerALU.Bus) (h : data.low = 0) :
    (ProofsLean.MNCore.Masks.flushBus width flags data).low = 0 := by
  cases width <;> simp [ProofsLean.MNCore.Masks.flushBus, h]

/-- The flush-adjusted output of an integer ALU keeps a zero low half. -/
theorem parsedOutputAfterFlush_low_zero (selection : Option PEWordSelection)
    (output : IntegerALU.Bus) (h : output.low = 0) :
    (parsedOutputAfterFlush selection output).low = 0 := by
  cases selection with
  | none => exact h
  | some selected =>
      unfold parsedOutputAfterFlush
      split <;> simp_all [flushBus_low_zero]

/-! ## 2. The all-zero initial state reads zero in every bank -/

/-- The all-zero word bus, named to keep function-literal elaboration explicit. -/
def zeroWordBus : WordBus := fun _ => 0

@[simp] theorem zeroWordBus_apply (index : Fin 4) : zeroWordBus index = 0 := rfl

theorem pack_zeroWordBus : pack zeroWordBus = (⟨0, 0⟩ : IntegerALU.Bus) := by
  apply bus_ext <;> simp [pack, zeroWordBus]

theorem readWords_zero (bank : PEMemory.Bank) (width : PEMemory.Width)
    (start : Fin bank.capacity) :
    readWords bank width (fun (_ : Fin bank.capacity) => (0 : BitVec 32)) start =
      zeroWordBus := by
  funext index
  simp [readWords, zeroWordBus]

theorem welcomeInitialPERegisters_lm1 (input : ProofsLean.MNCore.PlusOne.Words) :
    (welcomeInitialPERegisters input).lm1 = fun _ => 0 := rfl

theorem welcomeInitialPERegisters_grf0 (input : ProofsLean.MNCore.PlusOne.Words) :
    (welcomeInitialPERegisters input).grf0 = fun _ => 0 := rfl

theorem welcomeInitialPERegisters_grf1 (input : ProofsLean.MNCore.PlusOne.Words) :
    (welcomeInitialPERegisters input).grf1 = fun _ => 0 := rfl

theorem welcomeInitialPERegisters_t (input : ProofsLean.MNCore.PlusOne.Words) :
    (welcomeInitialPERegisters input).t = fun _ => 0 := rfl

theorem welcomeInitialPERegisters_maskRegisters
    (input : ProofsLean.MNCore.PlusOne.Words) :
    (welcomeInitialPERegisters input).maskRegisters = fun _ _ => 0 := rfl

/-- On the all-zero input every bank of the initial register file reads zero. -/
theorem welcomeZero_readDirectAccess_zero (access : DirectMemoryAccess) :
    readDirectAccess (welcomeInitialPERegisters welcomeZeroWords) access = zeroWordBus := by
  obtain ⟨bank, width, address⟩ := access
  cases bank with
  | lm0 =>
      have memoryZero : (fun address : Fin Bank.lm0.capacity =>
          if h : address.val < 16 then welcomeZeroWords ⟨address.val, h⟩ else 0) =
          (fun _ => 0) := by
        funext address
        by_cases inside : address.val < 16
        · simp [inside, welcomeZeroWords]
        · simp [inside]
      show readWords .lm0 width (fun address : Fin Bank.lm0.capacity =>
        if h : address.val < 16 then welcomeZeroWords ⟨address.val, h⟩ else 0) address =
          zeroWordBus
      rw [memoryZero]
      exact readWords_zero .lm0 width address
  | lm1 =>
      show readWords .lm1 width (fun _ => 0) address = zeroWordBus
      exact readWords_zero .lm1 width address
  | grf0 =>
      show readWords .grf0 width (fun _ => 0) address = zeroWordBus
      exact readWords_zero .grf0 width address
  | grf1 =>
      show readWords .grf1 width (fun _ => 0) address = zeroWordBus
      exact readWords_zero .grf1 width address
  | t =>
      show readWords .t width (fun _ => 0) address = zeroWordBus
      exact readWords_zero .t width address

/-- The packed read of any access of the all-zero initial state is the zero ALU
bus. -/
theorem welcomeZero_pack_readDirectAccess_zero (access : DirectMemoryAccess) :
    pack (readDirectAccess (welcomeInitialPERegisters welcomeZeroWords) access) =
      (⟨0, 0⟩ : IntegerALU.Bus) := by
  rw [welcomeZero_readDirectAccess_zero]
  exact pack_zeroWordBus

/-! ## 3. Prepared integer writes: the low-half copy fact -/

/-- General form of `prepareParsedMaskedWriteWithForwarding_memory_eq`, with the
flush selection kept symbolic instead of assumed absent. -/
theorem prepareParsedMaskedWriteWithForwarding_memory_eq_flush
    (files : IntegerRegisterFiles) (slots : ProofsLean.MNCore.Forwarding.Slots)
    (cycle : Fin 4) (accesses : ParsedMaskedIntegerAccesses) (reduced : Bool)
    (sourceXAccess sourceYAccess : DirectMemoryAccess)
    (sourceX : accesses.sourceX = .memory sourceXAccess false)
    (sourceY : accesses.sourceY = .memory sourceYAccess false)
    (precision : IntegerALU.Precision) (aluOp : IntegerALU.Op)
    (request : accesses.op.executionRequest = .ok (.integer precision aluOp)) :
    prepareParsedMaskedWriteWithForwarding files slots cycle accesses reduced =
      .ok { destination := some accesses.destination
            maskUpdate := none
            data := unpackALUBus (parsedOutputAfterFlush accesses.flushSelection
              (IntegerALU.evaluateBus precision aluOp
                (pack (readDirectAccess files sourceXAccess))
                (pack (readDirectAccess files sourceYAccess)) reduced).value)
            selection := accesses.writeSelection } := by
  unfold prepareParsedMaskedWriteWithForwarding
  rw [sourceX, sourceY]
  simp [ParsedIntegerInput.readWithForwarding, ParsedIntegerInput.read,
    ParsedIntegerInput.applyRounding, evaluateParsedIntegerAlu, request,
    evaluateParsedExecutionRequest]

/-- **The copy fact for a prepared ALU write.** If both memory sources of the
access read the zero bus, the prepared write's data words 2 and 3 are zero: the
low half of an ALU result is a copy, never a computation. -/
theorem prepareParsedMaskedWriteWithForwarding_data_two_three_zero
    (files : IntegerRegisterFiles) (slots : ProofsLean.MNCore.Forwarding.Slots)
    (cycle : Fin 4) (accesses : ParsedMaskedIntegerAccesses) (reduced : Bool)
    (write : PreparedParsedMaskedWrite)
    (sourceXAccess sourceYAccess : DirectMemoryAccess)
    (sourceX : accesses.sourceX = .memory sourceXAccess false)
    (sourceY : accesses.sourceY = .memory sourceYAccess false)
    (readX : readDirectAccess files sourceXAccess = zeroWordBus)
    (readY : readDirectAccess files sourceYAccess = zeroWordBus)
    (precision : IntegerALU.Precision) (aluOp : IntegerALU.Op)
    (request : accesses.op.executionRequest = .ok (.integer precision aluOp))
    (prepared : prepareParsedMaskedWriteWithForwarding files slots cycle accesses
      reduced = .ok write) :
    (∀ bound : 2 < 4, write.data ⟨2, bound⟩ = 0) ∧
      (∀ bound : 3 < 4, write.data ⟨3, bound⟩ = 0) := by
  rw [prepareParsedMaskedWriteWithForwarding_memory_eq_flush files slots cycle accesses
    reduced sourceXAccess sourceYAccess sourceX sourceY precision aluOp request] at prepared
  simp only [StepResult.ok.injEq] at prepared
  subst prepared
  have xzero : pack (readDirectAccess files sourceXAccess) = (⟨0, 0⟩ : IntegerALU.Bus) := by
    rw [readX]
    exact pack_zeroWordBus
  have yzero : pack (readDirectAccess files sourceYAccess) = (⟨0, 0⟩ : IntegerALU.Bus) := by
    rw [readY]
    exact pack_zeroWordBus
  have lowZero : (IntegerALU.evaluateBus precision aluOp
      (pack (readDirectAccess files sourceXAccess))
      (pack (readDirectAccess files sourceYAccess)) reduced).value.low = 0 := by
    rw [xzero, yzero]
    exact evaluateBus_value_low_zero precision aluOp ⟨0, 0⟩ ⟨0, 0⟩ reduced rfl
  have flushed := parsedOutputAfterFlush_low_zero accesses.flushSelection _ lowZero
  exact ⟨fun bound => unpackALUBus_two_zero _ flushed bound,
    fun bound => unpackALUBus_three_zero _ flushed bound⟩

/-! ## 4. Masked stores: the `.double` block word -/

theorem mergeSelectedWord_zero_zero (enable : BitVec 32) :
    mergeSelectedWord 0 0 enable = 0 := by
  simp [mergeSelectedWord]

/-- A masked `.double` store keeps the target at zero when the target is the
block's third word (`distance = 2`) and the bus word 2 is zero. -/
theorem writeWordsMasked_double_block_two
    (memory : PEMemory.Memory .lm1) (start target : Fin Bank.lm1.capacity)
    (data : WordBus) (flags : BitVec 4) (longLong : Bool)
    (dataTwo : ∀ bound : 2 < 4, data ⟨2, bound⟩ = 0)
    (distanceTwo : distance .lm1 start target = 2)
    (oldZero : memory target = 0) :
    writeWordsMasked .lm1 .double memory start data flags longLong target = 0 := by
  have within : distance .lm1 start target < count .lm1 .double := by
    rw [distanceTwo]
    decide
  rw [writeWordsMasked_at .lm1 .double memory start target data flags longLong within]
  have hidx : (⟨distance .lm1 start target,
      Nat.lt_of_lt_of_le within (count_le_four .lm1 .double)⟩ : Fin 4) =
      ⟨2, by decide⟩ :=
    Fin.ext distanceTwo
  rw [hidx, dataTwo, oldZero, mergeSelectedWord_zero_zero]

/-- The same, for the word `start + 2` of the block. -/
theorem writeWordsMasked_double_block_third
    (memory : PEMemory.Memory .lm1) (start : Fin Bank.lm1.capacity) (data : WordBus)
    (flags : BitVec 4) (longLong : Bool)
    (dataTwo : ∀ bound : 2 < 4, data ⟨2, bound⟩ = 0)
    (oldZero : memory (advance .lm1 start 2) = 0) :
    writeWordsMasked .lm1 .double memory start data flags longLong
      (advance .lm1 start 2) = 0 :=
  writeWordsMasked_double_block_two memory start (advance .lm1 start 2) data flags longLong
    dataTwo (distance_advance .lm1 start 2) oldZero

/-- A masked write to another bank leaves LM1 untouched. -/
theorem writeDirectAccessMasked_lm1_eq (files : IntegerRegisterFiles)
    (bank : PEMemory.Bank) (width : PEMemory.Width) (address : Fin bank.capacity)
    (data : WordBus) (selection : PEWordSelection) (different : bank ≠ .lm1) :
    (writeDirectAccessMasked files ⟨bank, width, address⟩ data selection).lm1 = files.lm1 := by
  cases bank with
  | lm1 => exact absurd rfl different
  | lm0 => simp [writeDirectAccessMasked, writeRegisterBankMasked]
  | grf0 => simp [writeDirectAccessMasked, writeRegisterBankMasked]
  | grf1 => simp [writeDirectAccessMasked, writeRegisterBankMasked]
  | t => simp [writeDirectAccessMasked, writeRegisterBankMasked]

/-- The LM1 effect of a masked `.lm1` write, at a word. -/
theorem writeDirectAccessMasked_lm1_apply (files : IntegerRegisterFiles)
    (width : PEMemory.Width) (address : Fin Bank.lm1.capacity) (data : WordBus)
    (selection : PEWordSelection) (target : Fin Bank.lm1.capacity) :
    (writeDirectAccessMasked files ⟨.lm1, width, address⟩ data selection).lm1 target =
      writeWordsMasked .lm1 width files.lm1 address data selection.flags
        selection.longLong target := rfl

/-- One commit step, matching the body of `commitParsedMaskedWrites`. -/
def welcomeCommitStep (files : IntegerRegisterFiles)
    (write : PreparedParsedMaskedWrite) : IntegerRegisterFiles :=
  match write.maskUpdate with
  | some (entry, cycle, flags) =>
      { files with maskRegisters :=
          (ProofsLean.MNCore.Masks.writeRegister files.maskRegisters entry cycle
            flags write.selection.flags) }
  | none =>
      match write.destination with
      | some destination => writeDirectAccessMasked files destination write.data write.selection
      | none => files

theorem commitParsedMaskedWrites_singleton (files : IntegerRegisterFiles)
    (write : PreparedParsedMaskedWrite) :
    commitParsedMaskedWrites files [write] = welcomeCommitStep files write := by
  unfold commitParsedMaskedWrites welcomeCommitStep
  rfl

theorem commitParsedMaskedWrites_cons (files : IntegerRegisterFiles)
    (write : PreparedParsedMaskedWrite) (rest : List PreparedParsedMaskedWrite) :
    commitParsedMaskedWrites files (write :: rest) =
      commitParsedMaskedWrites (welcomeCommitStep files write) rest := by
  rw [show write :: rest = [write] ++ rest from rfl, commitParsedMaskedWrites_append,
    commitParsedMaskedWrites_singleton]

/-- One commit step keeps an LM1 word at zero when the destination is either not
LM1, or outside the word's window, or hits it at bus index 2 with a zero bus
word. -/
theorem welcomeCommitStep_lm1_word_zero (files : IntegerRegisterFiles)
    (write : PreparedParsedMaskedWrite) (target : Fin Bank.lm1.capacity)
    (keeps : ∀ (width : PEMemory.Width) (address : Fin Bank.lm1.capacity)
        (d : WordBus) (s : PEWordSelection),
      write.destination = some ⟨.lm1, width, address⟩ → write.data = d →
      write.selection = s →
        (count .lm1 width ≤ distance .lm1 address target) ∨
        ((∀ bound : 2 < 4, d ⟨2, bound⟩ = 0) ∧
          distance .lm1 address target = 2))
    (oldZero : files.lm1 target = 0) :
    (welcomeCommitStep files write).lm1 target = 0 := by
  cases write with
  | mk destination maskUpdate data selection =>
    cases maskUpdate with
    | some update =>
        simp only [welcomeCommitStep]
        exact oldZero
    | none =>
        cases destination with
        | none =>
            simp only [welcomeCommitStep]
            exact oldZero
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
                        target data selection.flags selection.longLong outside, oldZero]
                    · cases width with
                      | double =>
                          exact writeWordsMasked_double_block_two files.lm1 address target
                            data selection.flags selection.longLong block.1 block.2 oldZero
                      | word =>
                          rw [writeWordsMasked_preserves_outside .lm1 .word files.lm1
                            address target data selection.flags selection.longLong
                            (by rw [block.2]; decide), oldZero]
                      | long =>
                          rw [writeWordsMasked_preserves_outside .lm1 .long files.lm1
                            address target data selection.flags selection.longLong
                            (by rw [block.2]; decide), oldZero]
                | lm0 =>
                    simp only [welcomeCommitStep]
                    rw [writeDirectAccessMasked_lm1_eq _ _ _ _ _ _ (by simp)]
                    exact oldZero
                | grf0 =>
                    simp only [welcomeCommitStep]
                    rw [writeDirectAccessMasked_lm1_eq _ _ _ _ _ _ (by simp)]
                    exact oldZero
                | grf1 =>
                    simp only [welcomeCommitStep]
                    rw [writeDirectAccessMasked_lm1_eq _ _ _ _ _ _ (by simp)]
                    exact oldZero
                | t =>
                    simp only [welcomeCommitStep]
                    rw [writeDirectAccessMasked_lm1_eq _ _ _ _ _ _ (by simp)]
                    exact oldZero

/-- **The block fold.** A commit list that never touches a given LM1 word except
as bus index 2 of a `.double` store leaves that word at zero. -/
theorem commitParsedMaskedWrites_lm1_word_zero (files : IntegerRegisterFiles)
    (writes : List PreparedParsedMaskedWrite) (target : Fin Bank.lm1.capacity)
    (keeps : ∀ write ∈ writes, ∀ (width : PEMemory.Width)
        (address : Fin Bank.lm1.capacity) (data : WordBus) (selection : PEWordSelection),
      write.destination = some ⟨.lm1, width, address⟩ → write.data = data →
      write.selection = selection →
        (count .lm1 width ≤ distance .lm1 address target) ∨
        ((∀ bound : 2 < 4, data ⟨2, bound⟩ = 0) ∧
          distance .lm1 address target = 2))
    (oldZero : files.lm1 target = 0) :
    (commitParsedMaskedWrites files writes).lm1 target = 0 := by
  induction writes generalizing files with
  | nil => simpa [commitParsedMaskedWrites] using oldZero
  | cons write rest ih =>
      rw [commitParsedMaskedWrites_cons]
      apply ih
      · intro item member
        exact keeps item (List.mem_cons_of_mem _ member)
      · exact welcomeCommitStep_lm1_word_zero files write target
          (fun width address data selection destination dataEq selectionEq =>
            keeps write (by simp) width address data selection destination dataEq
              selectionEq)
          oldZero

/-! ## 5. The two-sided state-level refutations -/

/-- The all-five input word vector: every word is `5`, still admissible. -/
def welcomeAllFiveWords : ProofsLean.MNCore.PlusOne.Words := fun _ => 5

theorem welcomeAllFiveWords_admissible : welcomeSpec.admissible welcomeAllFiveWords := by
  intro i
  show (5 : BitVec 32).toNat ≤ 50
  decide

/-- A line whose successful all-zero step leaves some PE 0 LM1 word at zero is
refuted: the spec demands `1` there. -/
theorem welcome_not_correct_of_word_zero (line : InstructionLine) (next : State)
    (step : welcomeSealedMachine.step line (welcomeInitialState welcomeZeroWords) = some next)
    (i : Fin 16)
    (zero : (next.peRegisters welcomePE).lm1
      ⟨i.val, by have := i.isLt; change i.val < 4096; omega⟩ = 0) :
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
  rw [zero] at word
  have one : (1 : BitVec 32) = 0 := by
    simpa [welcomeZeroWords] using word.symm
  exact absurd one (by decide)

/-- **The input-independence side.** If the PE 0 LM1 output of a line does not
depend on the input, the line is refuted: the spec forces `1` on the all-zero
input and `6` on the all-five input. -/
theorem welcome_not_correct_of_inputIndependentLM1 (line : InstructionLine)
    (independent : ∀ nextA,
      welcomeSealedMachine.step line (welcomeInitialState welcomeZeroWords) = some nextA →
      ∀ nextB,
      welcomeSealedMachine.step line (welcomeInitialState welcomeAllFiveWords) = some nextB →
        (nextA.peRegisters welcomePE).lm1 = (nextB.peRegisters welcomePE).lm1) :
    ¬ ProofsLean.Correct welcomeSealedMachine welcomeSpec
      (([line] : List InstructionLine)) := by
  intro correct
  obtain ⟨resultA, executedA, postA⟩ :=
    correct.2 welcomeZeroWords welcomeZeroWords_admissible
  obtain ⟨resultB, executedB, postB⟩ :=
    correct.2 welcomeAllFiveWords welcomeAllFiveWords_admissible
  rw [welcomeSpec_initial] at executedA executedB
  simp only [welcomeSpec] at postA postB
  have stepA : welcomeSealedMachine.step line (welcomeInitialState welcomeZeroWords) =
      some resultA := by simpa [ProofsLean.execute] using executedA
  have stepB : welcomeSealedMachine.step line (welcomeInitialState welcomeAllFiveWords) =
      some resultB := by simpa [ProofsLean.execute] using executedB
  have wordA := postA ⟨0, by decide⟩
  have wordB := postB ⟨0, by decide⟩
  have same := congrFun (independent resultA stepA resultB stepB) ⟨0, by decide⟩
  rw [wordA, wordB] at same
  simp [welcomeZeroWords, welcomeAllFiveWords] at same

/-- **Reduction: only all-sixteen-word lines can remain.** If the all-zero step
is stuck or leaves any PE 0 LM1 word zero, the line is already refuted. -/
theorem welcomeLowerBound_two_of_allWordsChanged
    (open_ : ∀ expressions : List NormalizedExpr, WelcomePEUnrefuted expressions →
      (∃ next, welcomeSealedMachine.step (.pe expressions)
          (welcomeInitialState welcomeZeroWords) = some next ∧
        ∀ i : Fin 16, (next.peRegisters welcomePE).lm1
          ⟨i.val, by have := i.isLt; change i.val < 4096; omega⟩ ≠ 0) →
      ¬ ProofsLean.Correct welcomeSealedMachine welcomeSpec
        (([InstructionLine.pe expressions] : List InstructionLine))) :
    ProofsLean.LowerBound welcomeSealedMachine welcomeSpec 2 := by
  apply welcomeLowerBound_two_of_unrefuted
  intro expressions unrefuted
  cases step : welcomeSealedMachine.step (.pe expressions)
      (welcomeInitialState welcomeZeroWords) with
  | none => exact welcome_not_correct_of_step_none _ step
  | some next =>
      by_cases untouched : ∃ i : Fin 16, (next.peRegisters welcomePE).lm1
          ⟨i.val, by have := i.isLt; change i.val < 4096; omega⟩ = 0
      · obtain ⟨i, zero⟩ := untouched
        exact welcome_not_correct_of_word_zero _ next step i zero
      · apply open_ expressions unrefuted
        refine ⟨next, step, fun i => ?_⟩
        by_cases zero : (next.peRegisters welcomePE).lm1
            ⟨i.val, by have := i.isLt; change i.val < 4096; omega⟩ = 0
        · exact absurd ⟨i, zero⟩ untouched
        · exact zero

/-- The all-zero success condition of the residual class: the line's step
succeeds and rewrites all sixteen PE 0 LM1 words. -/
def WelcomePEAllWordsChanged (expressions : List NormalizedExpr) : Prop :=
  ∃ next, welcomeSealedMachine.step (.pe expressions)
      (welcomeInitialState welcomeZeroWords) = some next ∧
    ∀ i : Fin 16, (next.peRegisters welcomePE).lm1
      ⟨i.val, by have := i.isLt; change i.val < 4096; omega⟩ ≠ 0

/-- The PE 0 LM1 output of the line does not depend on the input, between the
all-zero and all-five inputs. -/
def WelcomePEInputIndependent (expressions : List NormalizedExpr) : Prop :=
  ∀ nextA,
    welcomeSealedMachine.step (.pe expressions)
      (welcomeInitialState welcomeZeroWords) = some nextA →
    ∀ nextB,
    welcomeSealedMachine.step (.pe expressions)
      (welcomeInitialState welcomeAllFiveWords) = some nextB →
      (nextA.peRegisters welcomePE).lm1 = (nextB.peRegisters welcomePE).lm1

/-- **The residual class, exactly**: an accepted non-trivial `.pe` line that
rewrites all sixteen PE 0 LM1 words on the all-zero input and whose PE 0 LM1
output is *not* input-independent.

The expressions of such a line still carry one of the following producer shapes,
none of which is refuted by this module:

* `.alu name precision unsigned arg` rows, `.immediate`/`.zero` rows and
  `.matrixRead` rows (the integer stage of
  `prepareParsedIntegerALUExprCycles`), with a `.lm1` destination of width
  `.word`, `.long` or `.double`;
* `.mau` rows of the matrix, float, block-float and integer families
  (`executeParsedFloatMAUsAtPE`, `executeParsedMatrixMAUAndWrites`,
  `executeParsedBlockFloatProducer`, `executeParsedSharedBlockProducers`);
* `.matrixWrite` rows (`executeParsedMatrixMAUAndWrites`);
* `.l1bm` rows including `.distrib` (`executeParsedL1ToPEProducers`) and `.l2bm`
  rows.

The `.double` bus-word-2 case for the integer stage is already closed at the
preparation level by
`prepareParsedMaskedWriteWithForwarding_data_two_three_zero` together with
`welcomeZero_pack_readDirectAccess_zero`; what is still missing is the executor
link `WelcomeWriteProvenance`. -/
def WelcomePEResidual (expressions : List NormalizedExpr) : Prop :=
  WelcomePEUnrefuted expressions ∧ WelcomePEAllWordsChanged expressions ∧
    ¬ WelcomePEInputIndependent expressions

/-- **Conditional bound.** Refuting the residual class proves lower bound two. -/
theorem welcomeLowerBound_two_of_residual
    (open_ : ∀ expressions : List NormalizedExpr, WelcomePEResidual expressions →
      ¬ ProofsLean.Correct welcomeSealedMachine welcomeSpec
        (([InstructionLine.pe expressions] : List InstructionLine))) :
    ProofsLean.LowerBound welcomeSealedMachine welcomeSpec 2 := by
  apply welcomeLowerBound_two_of_allWordsChanged
  intro expressions unrefuted changed
  by_cases independent : WelcomePEInputIndependent expressions
  · exact welcome_not_correct_of_inputIndependentLM1 (.pe expressions) independent
  · exact open_ expressions ⟨unrefuted, changed, independent⟩

/-- **The gap, exactly.** The bound is equivalent to the refutation of
`WelcomePEResidual`, so the two-sided reduction above is not a weakening. -/
theorem welcomeLowerBound_two_iff_residual :
    ProofsLean.LowerBound welcomeSealedMachine welcomeSpec 2 ↔
      (∀ expressions : List NormalizedExpr, WelcomePEResidual expressions →
        ¬ ProofsLean.Correct welcomeSealedMachine welcomeSpec
          (([InstructionLine.pe expressions] : List InstructionLine))) := by
  constructor
  · intro lower expressions _residual
    rw [welcomeLowerBound_two_iff_rejects_short_lines] at lower
    exact lower (.pe expressions) (by simp [InstructionLine.cost])
  · exact welcomeLowerBound_two_of_residual

/-! ## 6. The remaining executor obligation, as an exact Lean statement

The single missing link between the reduced statement above and the executor is
the following provenance statement. It is *true* (every `.pe` step commits the
prepared writes of the integer stage at each PE), it is stated here as a `Prop`,
and **nothing in this module assumes it**. -/

/-- Obligation (write provenance at PE 0). After a `.pe` line, the observed PE's
register file is the commit of a list of prepared masked writes on its initial
value. This is the missing connection between
`prepareParsedIntegerALUExprCycles` / `prepareParsedIntegerMatrixReadLineExpressions`
and `executeIntegerProducerInstructionLine`; the per-PE walk already has the
corresponding per-expression lemmas
(`executeIntegerProducerLineAtPEs_peRegisters_mem`,
`executeIntegerProducerLineAtPE_peRegisters`). -/
def WelcomeWriteProvenance (expressions : List NormalizedExpr) : Prop :=
  ∀ (input : ProofsLean.MNCore.PlusOne.Words) (next : State),
    welcomeSealedMachine.step (.pe expressions) (welcomeInitialState input) = some next →
    ∃ writes : List PreparedParsedMaskedWrite,
      next.peRegisters welcomePE =
        commitParsedMaskedWrites ((welcomeInitialState input).peRegisters welcomePE) writes

end ProofsLean.MNCore
