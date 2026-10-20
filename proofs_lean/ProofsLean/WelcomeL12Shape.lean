import ProofsLean.WelcomePlainStep

/-! # The L1BM-to-PE and L2BM producer families: value facts and stage frames

This module starts the analysis of the two non-plain producer families
`WelcomePEL1ToPEShapeObligation` (`.l1bm .pbcast` / `.mbcast` / `.m4bcast` /
`.distrib`) and `WelcomePEL2BMShapeObligation` (`.l2bm`) of
`WelcomeValueBound.lean` §7.

The two families are structurally very different:

* an `.l2bm` row is executed by the **shared-block stage**
  (`executeParsedSharedBlockProducers`).  That stage only ever rewrites
  `l1bm`, `l1bmTurnaround`, `blockMemory` and the DAR registers; it never
  touches `peRegisters` (§4 below).  An `.l2bm` row therefore contributes
  *nothing* to the PE 0 `LM1` file, and the family obligation can only be
  discharged together with the analysis of the line's other rows;
* an `.l1bm` broadcast row is executed by the **L1BM-to-PE stage**
  (`executeParsedL1ToPEProducers`), the last stage of the `.pe` pipeline.  Its
  data bus `l1ToPEBusAt` reads `readState.l1bm` / `readState.l1bmTurnaround`,
  where `readState` is the state *before* the line.  At the Welcome initial
  state both memories are zero, so the bus is the **zero bus for every
  expression, access, PE and cycle and for every input** (§2).  This is the
  value half of the family: the `.lm1` `.double` blocks a broadcast writes at
  PE 0 carry a copied third data word (`0`), independent of the input.

What this module does **not** do: it does not close either `Prop`.  The exact
missing executor facts are recorded in §6.

No `sorry`, no `admit`, no `native_decide`, no new axioms.
-/

namespace ProofsLean.MNCore

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

open Issue
open PEMemory

/-! ## 1. The initial state's block memories are zero for every input

`welcomeInitialState` only replaces `peRegisters`; every block memory of
`rustSimulatorInitialState` is the constant zero function. -/

theorem welcomeInitialState_l1bm (input : ProofsLean.MNCore.PlusOne.Words)
    (bank : Fin 64) : (welcomeInitialState input).l1bm bank = fun _ => 0 := rfl

theorem welcomeInitialState_l1bm_apply (input : ProofsLean.MNCore.PlusOne.Words)
    (bank : Fin 64) (address : Fin L1Transfer.l1bmLongWords) :
    (welcomeInitialState input).l1bm bank address = 0 := rfl

theorem welcomeInitialState_l1bmTurnaround (input : ProofsLean.MNCore.PlusOne.Words) :
    (welcomeInitialState input).l1bmTurnaround = fun _ _ _ => 0 := rfl

theorem welcomeInitialState_l1bmTurnaround_apply
    (input : ProofsLean.MNCore.PlusOne.Words) (bank : Fin 64) (cycle : Fin 4)
    (index : Fin 64) : (welcomeInitialState input).l1bmTurnaround bank cycle index = 0 := rfl

theorem welcomeInitialState_l1bmTurnaroundValid
    (input : ProofsLean.MNCore.PlusOne.Words) :
    (welcomeInitialState input).l1bmTurnaroundValid = false := rfl

theorem welcomeInitialState_blockMemory (input : ProofsLean.MNCore.PlusOne.Words) :
    (welcomeInitialState input).blockMemory = fun _ => 0 := rfl

theorem welcomeInitialState_l1bm_eq_rust :
    ∀ (input : ProofsLean.MNCore.PlusOne.Words) (bank : Fin 64),
      (welcomeInitialState input).l1bm bank = rustSimulatorInitialState.l1bm bank :=
  fun _ _ => rfl

/-! ## 2. The L1BM-to-PE broadcast bus is the zero bus at the initial state -/

/-- The zero turnaround register, with its type made explicit. -/
abbrev zeroTurnaround : L1Transfer.L1Turnaround := fun _ _ => (0 : BitVec 64)

/-- The zero L1 bank, with its type made explicit. -/
abbrev zeroL1Bank : L1Transfer.L1Bank := fun _ => (0 : BitVec 64)

theorem pbcast_zero (base : Fin L1Transfer.l1bmLongWords) (twoLongWords : Bool)
    (cycle : Fin 4) :
    L1Transfer.pbcast zeroL1Bank base twoLongWords cycle = ⟨0, 0⟩ := by
  cases twoLongWords <;> rfl

theorem pbcastTurnaround_zero (twoLongWords : Bool) (cycle : Fin 4) :
    L1Transfer.pbcastTurnaround zeroTurnaround twoLongWords cycle = ⟨0, 0⟩ := by
  cases twoLongWords <;> rfl

theorem mbcast_zero_addressed (base : Fin L1Transfer.l1bmLongWords)
    (twoLongWords : Bool) (pe cycle : Fin 4) :
    L1Transfer.mbcast zeroL1Bank (.addressed base) twoLongWords pe cycle = ⟨0, 0⟩ := by
  cases twoLongWords <;> rfl

theorem mbcast_zero_turnaround (twoLongWords : Bool) (pe cycle : Fin 4) :
    L1Transfer.mbcast zeroL1Bank (.turnaround zeroTurnaround) twoLongWords pe cycle =
      ⟨0, 0⟩ := by
  cases twoLongWords <;> rfl

theorem m4bcast_zero_addressed (base : Fin L1Transfer.l1bmLongWords)
    (twoLongWords : Bool) (mabGroup pe cycle : Fin 4) :
    L1Transfer.m4bcast zeroL1Bank (.addressed base) twoLongWords mabGroup pe cycle =
      ⟨0, 0⟩ := by
  cases twoLongWords <;> rfl

theorem m4bcast_zero_turnaround (twoLongWords : Bool) (mabGroup pe cycle : Fin 4) :
    L1Transfer.m4bcast zeroL1Bank (.turnaround zeroTurnaround) twoLongWords mabGroup pe cycle =
      ⟨0, 0⟩ := by
  cases twoLongWords <;> rfl

theorem distrib_zero_addressed (base : Fin L1Transfer.l1bmLongWords) (mabDiff : Int)
    (mab : Fin 16) (pe cycle : Fin 4) :
    L1Transfer.distrib zeroL1Bank (.addressed base) mabDiff mab pe cycle = ⟨0, 0⟩ := by
  have words := L1Transfer.distrib_addressed_words zeroL1Bank base mabDiff mab pe cycle
  have high : (L1Transfer.distrib zeroL1Bank (.addressed base) mabDiff mab pe cycle).high = 0 :=
    words.1
  have low : (L1Transfer.distrib zeroL1Bank (.addressed base) mabDiff mab pe cycle).low = 0 :=
    words.2
  cases bus : L1Transfer.distrib zeroL1Bank (.addressed base) mabDiff mab pe cycle with
  | mk h l => rw [bus] at high low; simp_all

theorem distrib_zero_turnaround (mabDiff : Int) (mab : Fin 16) (pe cycle : Fin 4) :
    L1Transfer.distrib zeroL1Bank (.turnaround zeroTurnaround) mabDiff mab pe cycle =
      ⟨0, 0⟩ := by
  simp [L1Transfer.distrib, L1Transfer.readL1Long, zeroTurnaround]

/-- **The broadcast bus is the zero bus at the Welcome initial state.**  This
holds for every operation (`.pbcast`, `.mbcast`, `.m4bcast`, `.distrib`), for
both source kinds (addressed and turnaround), and for every PE, cycle and
input: the data a broadcast reads does not depend on the PE input at all. -/
theorem l1ToPEBusAt_welcomeInitialState (input : ProofsLean.MNCore.PlusOne.Words)
    (expression : ParsedExpr) (access : ParsedL1ToPEAccess) (pe : PEId) (cycle : Fin 4) :
    l1ToPEBusAt (welcomeInitialState input) expression access pe cycle = ⟨0, 0⟩ := by
  cases operation : expression.op with
  | l1bm l1op =>
      cases l1op <;>
        cases source : access.sourceBase <;>
        simp [l1ToPEBusAt, operation, welcomeInitialState, rustSimulatorInitialState,
          L1Transfer.pbcast, L1Transfer.pbcastTurnaround, L1Transfer.mbcast,
          L1Transfer.m4bcast, L1Transfer.distrib, L1Transfer.readL1Long, source]
  | alu name precision unsigned arg =>
      simp [l1ToPEBusAt, operation, welcomeInitialState, rustSimulatorInitialState]
  | immediate value unsigned =>
      simp [l1ToPEBusAt, operation, welcomeInitialState, rustSimulatorInitialState]
  | zero =>
      simp [l1ToPEBusAt, operation, welcomeInitialState, rustSimulatorInitialState]
  | mau precision matrix kind half round =>
      simp [l1ToPEBusAt, operation, welcomeInitialState, rustSimulatorInitialState]
  | matrixWrite precision =>
      simp [l1ToPEBusAt, operation, welcomeInitialState, rustSimulatorInitialState]
  | matrixRead precision =>
      simp [l1ToPEBusAt, operation, welcomeInitialState, rustSimulatorInitialState]
  | wait tag =>
      simp [l1ToPEBusAt, operation, welcomeInitialState, rustSimulatorInitialState]
  | noforward =>
      simp [l1ToPEBusAt, operation, welcomeInitialState, rustSimulatorInitialState]
  | l2bm l2op =>
      simp [l1ToPEBusAt, operation, welcomeInitialState, rustSimulatorInitialState]

/-- The `.pbcast` case of `l1ToPEBusAt_welcomeInitialState`, recorded separately
because `.pbcast` reads the memory directly and not through `readL1Long`. -/
theorem l1ToPEBusAt_welcomeInitialState_pbcast
    (input : ProofsLean.MNCore.PlusOne.Words) (expression : ParsedExpr)
    (access : ParsedL1ToPEAccess) (pe : PEId) (cycle : Fin 4)
    (operation : expression.op = .l1bm .pbcast) :
    l1ToPEBusAt (welcomeInitialState input) expression access pe cycle = ⟨0, 0⟩ :=
  l1ToPEBusAt_welcomeInitialState input expression access pe cycle

/-! ## 3. The broadcast's flushed output and its written data are zero -/

/-- The zero bus is fixed by `unpackALUBus`. -/
theorem unpackALUBus_zero : unpackALUBus (⟨0, 0⟩ : IntegerALU.Bus) = fun _ => 0 := by
  funext index
  simp only [unpackALUBus]
  split
  · decide
  · split
    · decide
    · split
      · decide
      · decide

/-- Flushing the zero bus leaves the zero bus. -/
theorem parsedOutputAfterFlush_zero (selection : Option PEWordSelection) :
    parsedOutputAfterFlush selection (⟨0, 0⟩ : IntegerALU.Bus) = ⟨0, 0⟩ := by
  cases selection with
  | none => rfl
  | some selected =>
      obtain ⟨flags, longLong⟩ := selected
      cases longLong <;>
        simp [parsedOutputAfterFlush, ProofsLean.MNCore.Masks.flushBus,
          ProofsLean.MNCore.Masks.doubleMask, ProofsLean.MNCore.Masks.halfMask]

/-- **Every flush selection of the broadcast bus is the zero bus.**  This is
the data half of the L1BM family: whatever flush selection and mask the line
resolves, the data written at PE 0 is zero. -/
theorem parsedOutputAfterFlush_l1ToPEBusAt_zero
    (input : ProofsLean.MNCore.PlusOne.Words) (expression : ParsedExpr)
    (access : ParsedL1ToPEAccess) (pe : PEId) (cycle : Fin 4)
    (selection : Option PEWordSelection) :
    parsedOutputAfterFlush selection
      (l1ToPEBusAt (welcomeInitialState input) expression access pe cycle) = ⟨0, 0⟩ := by
  rw [l1ToPEBusAt_welcomeInitialState]
  exact parsedOutputAfterFlush_zero selection

/-- The written data of a broadcast at the initial state is the zero word bus,
so in particular its third word is a copy.  This is the fact the `.double`
copy shape consumes. -/
theorem unpackALUBus_l1ToPEBusAt_zero
    (input : ProofsLean.MNCore.PlusOne.Words) (expression : ParsedExpr)
    (access : ParsedL1ToPEAccess) (pe : PEId) (cycle : Fin 4)
    (selection : Option PEWordSelection) :
    unpackALUBus (parsedOutputAfterFlush selection
      (l1ToPEBusAt (welcomeInitialState input) expression access pe cycle)) = fun _ => 0 := by
  rw [parsedOutputAfterFlush_l1ToPEBusAt_zero, unpackALUBus_zero]

/-- The third data word of a broadcast write at PE 0 is a copy. -/
theorem l1ToPE_data_word_two_isWelcomeCopy
    (input : ProofsLean.MNCore.PlusOne.Words) (expression : ParsedExpr)
    (access : ParsedL1ToPEAccess) (pe : PEId) (cycle : Fin 4)
    (selection : Option PEWordSelection) (bound : 2 < 4) :
    IsWelcomeCopy
      ((unpackALUBus (parsedOutputAfterFlush selection
        (l1ToPEBusAt (welcomeInitialState input) expression access pe cycle))) ⟨2, bound⟩) := by
  rw [unpackALUBus_l1ToPEBusAt_zero]
  exact isWelcomeCopy_zero


/-! ## 4. Bank frames for the masked store primitives

A masked store into one bank leaves every other bank of the register file
untouched, and the commit of a write list with no `.lm1` destination leaves
`lm1` untouched.  These are the generic facts every non-`LM1` producer stage
needs in order to be invisible to the `.lm1` value shape. -/

theorem writeRegisterBankMasked_lm1 (files : IntegerRegisterFiles)
    (bank : PEMemory.Bank) (width : Width) (address : Fin bank.capacity)
    (data : WordBus) (selection : PEWordSelection) :
    (writeRegisterBankMasked files bank width address data selection).lm1 =
      match bank with
      | .lm1 => writeWordsMasked .lm1 width files.lm1 address data selection.flags
          selection.longLong
      | _ => files.lm1 := by
  cases bank <;> rfl

theorem writeRegisterBankMasked_lm1_of_ne (files : IntegerRegisterFiles)
    (bank : PEMemory.Bank) (width : Width) (address : Fin bank.capacity)
    (data : WordBus) (selection : PEWordSelection) (ne : bank ≠ PEMemory.Bank.lm1) :
    (writeRegisterBankMasked files bank width address data selection).lm1 = files.lm1 := by
  cases bank <;> simp_all [writeRegisterBankMasked]

theorem writeRegisterBankMasked_maskRegisters (files : IntegerRegisterFiles)
    (bank : PEMemory.Bank) (width : Width) (address : Fin bank.capacity)
    (data : WordBus) (selection : PEWordSelection) :
    (writeRegisterBankMasked files bank width address data selection).maskRegisters =
      files.maskRegisters := by
  cases bank <;> rfl

theorem writeDirectAccessMasked_lm1_of_ne (files : IntegerRegisterFiles)
    (access : DirectMemoryAccess) (data : WordBus) (selection : PEWordSelection)
    (ne : access.bank ≠ PEMemory.Bank.lm1) :
    (writeDirectAccessMasked files access data selection).lm1 = files.lm1 := by
  cases access with
  | mk bank width address =>
      exact writeRegisterBankMasked_lm1_of_ne files bank width address data selection ne

/-- A single commit step with no `.lm1` destination preserves `lm1`. -/
theorem welcomeCommitStep_lm1_of_ne (files : IntegerRegisterFiles)
    (write : PreparedParsedMaskedWrite)
    (h : ∀ access : DirectMemoryAccess, write.destination = some access →
      access.bank ≠ PEMemory.Bank.lm1) :
    (welcomeCommitStep files write).lm1 = files.lm1 := by
  unfold welcomeCommitStep
  split
  · rfl
  · split
    · rename_i destination hdest
      exact writeDirectAccessMasked_lm1_of_ne files destination write.data write.selection
        (h destination hdest)
    · rfl

/-- A commit whose write list has no `.lm1` destination preserves the whole
`.lm1` bank. -/
theorem commitParsedMaskedWrites_lm1_of_no_lm1 (writes : List PreparedParsedMaskedWrite)
    (files : IntegerRegisterFiles)
    (h : ∀ write ∈ writes, ∀ access : DirectMemoryAccess,
      write.destination = some access → access.bank ≠ PEMemory.Bank.lm1) :
    (commitParsedMaskedWrites files writes).lm1 = files.lm1 := by
  induction writes generalizing files with
  | nil => rfl
  | cons write rest ih =>
      rw [commitParsedMaskedWrites_cons,
        ih _ (fun item member access hitem =>
          h item (List.mem_cons_of_mem _ member) access hitem)]
      exact welcomeCommitStep_lm1_of_ne files write (fun access haccess =>
        h write (by simp) access haccess)

/-! ## 5. The shared-block stage never touches the PE register files

The shared-block stage executes the `.l1bm` `.mwrite`/`.m4write`/`.gather`/
`.reduce`/`.reduce4` transfers and the `.l2bm` producers.  All of them rewrite
only `l1bm`, `l1bmTurnaround`, `blockMemory` and the DAR registers, so every
one of them preserves `peRegisters` at every PE.  In particular an `.l2bm` row
contributes nothing to the PE 0 `LM1` value. -/

theorem executeL1MwriteBankList_peRegisters (readState : State)
    (access : ParsedL1MwriteAccess) (updateTurnaround : Bool) :
    ∀ (banks : List (Fin 64)) (state next : State),
      executeL1MwriteBankList readState access updateTurnaround banks state = .ok next →
      next.peRegisters = state.peRegisters := by
  intro banks
  induction banks with
  | nil =>
      intro state next executed
      simp only [executeL1MwriteBankList, StepResult.ok.injEq] at executed
      rw [executed]
  | cons bank rest ih =>
      intro state next executed
      simp only [executeL1MwriteBankList] at executed
      split at executed
      · simp at executed
      · simp at executed
      · rename_i memory turnaround step
        rw [ih _ _ executed]

theorem executeParsedL1MwriteAtAllBanks_peRegisters (readState currentState next : State)
    (expression : ParsedExpr) (updateTurnaround : Bool)
    (executed : executeParsedL1MwriteAtAllBanks readState currentState expression
      updateTurnaround = .ok next) :
    next.peRegisters = currentState.peRegisters := by
  unfold executeParsedL1MwriteAtAllBanks at executed
  split at executed
  · simp at executed
  · exact executeL1MwriteBankList_peRegisters readState _ updateTurnaround
      (List.finRange 64) currentState next executed

theorem executeL1GatherBankList_peRegisters (readState : State)
    (access : ParsedL1GatherAccess) (updateTurnaround : Bool) :
    ∀ (banks : List (Fin 64)) (state next : State),
      executeL1GatherBankList readState access updateTurnaround banks state = .ok next →
      next.peRegisters = state.peRegisters := by
  intro banks
  induction banks with
  | nil =>
      intro state next executed
      simp only [executeL1GatherBankList, StepResult.ok.injEq] at executed
      rw [executed]
  | cons bank rest ih =>
      intro state next executed
      simp only [executeL1GatherBankList] at executed
      split at executed
      · simp at executed
      · simp at executed
      · rename_i memory turnaround step
        rw [ih _ _ executed]

theorem executeParsedL1GatherAtAllBanks_peRegisters (readState currentState next : State)
    (expression : ParsedExpr) (updateTurnaround : Bool)
    (executed : executeParsedL1GatherAtAllBanks readState currentState expression
      updateTurnaround = .ok next) :
    next.peRegisters = currentState.peRegisters := by
  unfold executeParsedL1GatherAtAllBanks at executed
  split at executed
  · simp at executed
  · exact executeL1GatherBankList_peRegisters readState _ updateTurnaround
      (List.finRange 64) currentState next executed

theorem executeL1ReduceBankList_peRegisters (readState : State)
    (access : ParsedL1ReduceAccess) (updateTurnaround : Bool) :
    ∀ (banks : List (Fin 64)) (state next : State),
      executeL1ReduceBankList readState access updateTurnaround banks state = .ok next →
      next.peRegisters = state.peRegisters := by
  intro banks
  induction banks with
  | nil =>
      intro state next executed
      simp only [executeL1ReduceBankList, StepResult.ok.injEq] at executed
      rw [executed]
  | cons bank rest ih =>
      intro state next executed
      simp only [executeL1ReduceBankList] at executed
      split at executed
      · simp at executed
      · simp at executed
      · rename_i memory turnaround step
        rw [ih _ _ executed]

theorem executeParsedL1ReduceAtAllBanks_peRegisters (readState currentState next : State)
    (expression : ParsedExpr) (updateTurnaround : Bool)
    (executed : executeParsedL1ReduceAtAllBanks readState currentState expression
      updateTurnaround = .ok next) :
    next.peRegisters = currentState.peRegisters := by
  unfold executeParsedL1ReduceAtAllBanks at executed
  split at executed
  · simp at executed
  · exact executeL1ReduceBankList_peRegisters readState _ updateTurnaround
      (List.finRange 64) currentState next executed

theorem executeParsedL1PEToL1Expression_peRegisters (readState currentState next : State)
    (expression : ParsedExpr) (updateTurnaround : Bool)
    (executed : executeParsedL1PEToL1Expression readState currentState expression
      updateTurnaround = .ok next) :
    next.peRegisters = currentState.peRegisters := by
  cases operation : expression.op with
  | l1bm l1op =>
      cases l1op with
      | mwrite mab =>
          simp only [executeParsedL1PEToL1Expression, operation] at executed
          exact executeParsedL1MwriteAtAllBanks_peRegisters readState currentState next expression
            updateTurnaround executed
      | m4write mab =>
          simp only [executeParsedL1PEToL1Expression, operation] at executed
          exact executeParsedL1MwriteAtAllBanks_peRegisters readState currentState next expression
            updateTurnaround executed
      | gather mabDiff =>
          simp only [executeParsedL1PEToL1Expression, operation] at executed
          exact executeParsedL1GatherAtAllBanks_peRegisters readState currentState next expression
            updateTurnaround executed
      | reduce rrn round =>
          simp only [executeParsedL1PEToL1Expression, operation] at executed
          exact executeParsedL1ReduceAtAllBanks_peRegisters readState currentState next expression
            updateTurnaround executed
      | reduce4 rrn round =>
          simp only [executeParsedL1PEToL1Expression, operation] at executed
          exact executeParsedL1ReduceAtAllBanks_peRegisters readState currentState next expression
            updateTurnaround executed
      | pbcast =>
          simp only [executeParsedL1PEToL1Expression, operation] at executed
          simp only [StepResult.ok.injEq] at executed
          rw [executed]
      | mbcast =>
          simp only [executeParsedL1PEToL1Expression, operation] at executed
          simp only [StepResult.ok.injEq] at executed
          rw [executed]
      | m4bcast =>
          simp only [executeParsedL1PEToL1Expression, operation] at executed
          simp only [StepResult.ok.injEq] at executed
          rw [executed]
      | distrib mabdiff =>
          simp only [executeParsedL1PEToL1Expression, operation] at executed
          simp only [StepResult.ok.injEq] at executed
          rw [executed]
  | alu name precision unsigned arg =>
      simp only [executeParsedL1PEToL1Expression, operation] at executed
      simp only [StepResult.ok.injEq] at executed
      rw [executed]
  | immediate value unsigned =>
      simp only [executeParsedL1PEToL1Expression, operation] at executed
      simp only [StepResult.ok.injEq] at executed
      rw [executed]
  | zero =>
      simp only [executeParsedL1PEToL1Expression, operation] at executed
      simp only [StepResult.ok.injEq] at executed
      rw [executed]
  | mau precision matrix kind half round =>
      simp only [executeParsedL1PEToL1Expression, operation] at executed
      simp only [StepResult.ok.injEq] at executed
      rw [executed]
  | matrixWrite precision =>
      simp only [executeParsedL1PEToL1Expression, operation] at executed
      simp only [StepResult.ok.injEq] at executed
      rw [executed]
  | matrixRead precision =>
      simp only [executeParsedL1PEToL1Expression, operation] at executed
      simp only [StepResult.ok.injEq] at executed
      rw [executed]
  | wait tag =>
      simp only [executeParsedL1PEToL1Expression, operation] at executed
      simp only [StepResult.ok.injEq] at executed
      rw [executed]
  | noforward =>
      simp only [executeParsedL1PEToL1Expression, operation] at executed
      simp only [StepResult.ok.injEq] at executed
      rw [executed]
  | l2bm l2op =>
      simp only [executeParsedL1PEToL1Expression, operation] at executed
      simp only [StepResult.ok.injEq] at executed
      rw [executed]

theorem executeParsedDars_peRegisters (state next : State) (expression : ParsedExpr)
    (executed : executeParsedDars state expression = .ok next) :
    next.peRegisters = state.peRegisters := by
  unfold executeParsedDars at executed
  cases hs : parsedDarsSource? expression with
  | none => simp [hs] at executed
  | some value =>
      obtain ⟨a, b, c⟩ := value
      simp only [hs] at executed
      injection executed with hnext
      rw [← hnext]

theorem executeParsedDarw_peRegisters (state : State) :
    (executeParsedDarw state).peRegisters = state.peRegisters := rfl

theorem executeParsedL2BlockExpression_peRegisters (readState currentState next : State)
    (expression : ParsedExpr)
    (executed : executeParsedL2BlockExpression readState currentState expression = .ok next) :
    next.peRegisters = currentState.peRegisters := by
  cases operation : expression.op with
  | l1bm l1op => simp [executeParsedL2BlockExpression, operation] at executed
  | l2bm l2op =>
      cases l2op with
      | dars =>
          simp only [executeParsedL2BlockExpression, operation] at executed
          exact executeParsedDars_peRegisters currentState next expression executed
      | darw =>
          simp only [executeParsedL2BlockExpression, operation] at executed
          split at executed
          · simp only [StepResult.ok.injEq] at executed
            rw [← executed]
            exact executeParsedDarw_peRegisters currentState
          · simp at executed
      | bcast set =>
          simp only [executeParsedL2BlockExpression, operation] at executed
          split at executed
          · simp at executed
          · split at executed
            · simp at executed
            · simp only [StepResult.ok.injEq] at executed
              rw [← executed]
      | bcast2 set =>
          simp only [executeParsedL2BlockExpression, operation] at executed
          split at executed
          · simp at executed
          · split at executed
            · simp at executed
            · simp only [StepResult.ok.injEq] at executed
              rw [← executed]
      | distrib mabDiff =>
          simp only [executeParsedL2BlockExpression, operation] at executed
          split at executed
          · simp at executed
          · split at executed
            · simp at executed
            · simp only [StepResult.ok.injEq] at executed
              rw [← executed]
      | fromL1b l1b =>
          simp only [executeParsedL2BlockExpression, operation] at executed
          split at executed
          · simp at executed
          · split at executed
            · simp at executed
            · simp only [StepResult.ok.injEq] at executed
              rw [← executed]
      | reduce rrn round =>
          simp only [executeParsedL2BlockExpression, operation] at executed
          split at executed
          · simp at executed
          · split at executed
            · simp at executed
            · simp only [StepResult.ok.injEq] at executed
              rw [← executed]
      | reduce2 rrn =>
          simp only [executeParsedL2BlockExpression, operation] at executed
          split at executed
          · simp at executed
          · split at executed
            · simp at executed
            · simp only [StepResult.ok.injEq] at executed
              rw [← executed]
      | gather =>
          simp only [executeParsedL2BlockExpression, operation] at executed
          split at executed
          · simp at executed
          · split at executed
            · simp at executed
            · simp only [StepResult.ok.injEq] at executed
              rw [← executed]
      | imcast set =>
          simp only [executeParsedL2BlockExpression, operation] at executed
          split at executed
          · simp at executed
          · split at executed
            · simp at executed
            · simp only [StepResult.ok.injEq] at executed
              rw [← executed]
  | alu name precision unsigned arg => simp [executeParsedL2BlockExpression, operation] at executed
  | immediate value unsigned => simp [executeParsedL2BlockExpression, operation] at executed
  | zero => simp [executeParsedL2BlockExpression, operation] at executed
  | mau precision matrix kind half round =>
      simp [executeParsedL2BlockExpression, operation] at executed
  | matrixWrite precision => simp [executeParsedL2BlockExpression, operation] at executed
  | matrixRead precision => simp [executeParsedL2BlockExpression, operation] at executed
  | wait tag => simp [executeParsedL2BlockExpression, operation] at executed
  | noforward => simp [executeParsedL2BlockExpression, operation] at executed

theorem executeParsedSharedBlockExpression_peRegisters (readState currentState next : State)
    (expression : ParsedExpr) (updateTurnaround : Bool)
    (executed : executeParsedSharedBlockExpression readState currentState expression
      updateTurnaround = .ok next) :
    next.peRegisters = currentState.peRegisters := by
  cases operation : expression.op with
  | l1bm l1op =>
      cases l1op with
      | mwrite mab =>
          simp only [executeParsedSharedBlockExpression, operation] at executed
          exact executeParsedL1PEToL1Expression_peRegisters readState currentState next expression
            updateTurnaround executed
      | m4write mab =>
          simp only [executeParsedSharedBlockExpression, operation] at executed
          exact executeParsedL1PEToL1Expression_peRegisters readState currentState next expression
            updateTurnaround executed
      | gather mabDiff =>
          simp only [executeParsedSharedBlockExpression, operation] at executed
          exact executeParsedL1PEToL1Expression_peRegisters readState currentState next expression
            updateTurnaround executed
      | reduce rrn round =>
          simp only [executeParsedSharedBlockExpression, operation] at executed
          exact executeParsedL1PEToL1Expression_peRegisters readState currentState next expression
            updateTurnaround executed
      | reduce4 rrn round =>
          simp only [executeParsedSharedBlockExpression, operation] at executed
          exact executeParsedL1PEToL1Expression_peRegisters readState currentState next expression
            updateTurnaround executed
      | pbcast =>
          simp only [executeParsedSharedBlockExpression, operation] at executed
          simp only [StepResult.ok.injEq] at executed
          rw [executed]
      | mbcast =>
          simp only [executeParsedSharedBlockExpression, operation] at executed
          simp only [StepResult.ok.injEq] at executed
          rw [executed]
      | m4bcast =>
          simp only [executeParsedSharedBlockExpression, operation] at executed
          simp only [StepResult.ok.injEq] at executed
          rw [executed]
      | distrib mabdiff =>
          simp only [executeParsedSharedBlockExpression, operation] at executed
          simp only [StepResult.ok.injEq] at executed
          rw [executed]
  | l2bm l2op =>
      simp only [executeParsedSharedBlockExpression, operation] at executed
      exact executeParsedL2BlockExpression_peRegisters readState currentState next expression
        executed
  | alu name precision unsigned arg =>
      simp only [executeParsedSharedBlockExpression, operation] at executed
      simp only [StepResult.ok.injEq] at executed
      rw [executed]
  | immediate value unsigned =>
      simp only [executeParsedSharedBlockExpression, operation] at executed
      simp only [StepResult.ok.injEq] at executed
      rw [executed]
  | zero =>
      simp only [executeParsedSharedBlockExpression, operation] at executed
      simp only [StepResult.ok.injEq] at executed
      rw [executed]
  | mau precision matrix kind half round =>
      simp only [executeParsedSharedBlockExpression, operation] at executed
      simp only [StepResult.ok.injEq] at executed
      rw [executed]
  | matrixWrite precision =>
      simp only [executeParsedSharedBlockExpression, operation] at executed
      simp only [StepResult.ok.injEq] at executed
      rw [executed]
  | matrixRead precision =>
      simp only [executeParsedSharedBlockExpression, operation] at executed
      simp only [StepResult.ok.injEq] at executed
      rw [executed]
  | wait tag =>
      simp only [executeParsedSharedBlockExpression, operation] at executed
      simp only [StepResult.ok.injEq] at executed
      rw [executed]
  | noforward =>
      simp only [executeParsedSharedBlockExpression, operation] at executed
      simp only [StepResult.ok.injEq] at executed
      rw [executed]

theorem executeParsedSharedBlockProducerList_peRegisters (readState : State)
    (updateTurnaround : Bool) (expressions : List ParsedExpr) :
    ∀ (state next : State),
      executeParsedSharedBlockProducerList readState updateTurnaround expressions state =
        .ok next →
      next.peRegisters = state.peRegisters := by
  induction expressions with
  | nil =>
      intro state next executed
      simp only [executeParsedSharedBlockProducerList, StepResult.ok.injEq] at executed
      rw [executed]
  | cons expression rest ih =>
      intro state next executed
      simp only [executeParsedSharedBlockProducerList] at executed
      split at executed
      · simp at executed
      · simp at executed
      · rename_i middle step
        rw [ih _ _ executed]
        exact executeParsedSharedBlockExpression_peRegisters readState state middle expression
          updateTurnaround step

/-- **The shared-block stage preserves the PE register files at every PE.** -/
theorem executeParsedSharedBlockProducers_peRegisters (readState currentState next : State)
    (expressions : List ParsedExpr) (updateTurnaround : Bool)
    (executed : executeParsedSharedBlockProducers readState currentState expressions
      updateTurnaround = .ok next) :
    next.peRegisters = currentState.peRegisters :=
  executeParsedSharedBlockProducerList_peRegisters readState updateTurnaround expressions
    currentState next executed


/-! ## 6. The L1BM-to-PE destination write is a masked store of the zero bus

`writeParsedL1ToPEDestination?` on a `.mem` destination lowers to exactly one
`writeDirectAccessMasked` of the unpacked broadcast bus.  Combined with §3 the
stored data is zero, and a zero-bus store cannot turn the all-zero `lm1` file
into anything but zero. -/

theorem writeParsedL1ToPEDestination_mem (files : IntegerRegisterFiles)
    (maskRegisters : ProofsLean.MNCore.Masks.RegisterFile)
    (operandAccess : Access) (negated extended rounded : Bool)
    (mask : Option ParsedMask) (context : ParsedIntegerContext)
    (output : IntegerALU.Bus) (cycle : Fin 4) (directive : ParsedMaskDirective)
    (hasSingleLineMask : Bool) (access : DirectMemoryAccess)
    (selection : PEWordSelection)
    (lowered : ParsedOperand.toDirectMemoryDestination?
      (.mem operandAccess negated extended rounded mask) context.pe cycle
      context.bar0 context.bar1 context.tWord = some access)
    (resolved : ParsedOperand.resolveMemoryWriteSelection?
      (.mem operandAccess negated extended rounded mask) access.bank maskRegisters cycle
      directive hasSingleLineMask = some selection) :
    writeParsedL1ToPEDestination? files maskRegisters
        (.mem operandAccess negated extended rounded mask) context output cycle directive
        hasSingleLineMask =
      some (writeDirectAccessMasked files access (unpackALUBus output) selection, none) := by
  simp [writeParsedL1ToPEDestination?, lowered, resolved]

theorem writeParsedL1ToPEDestination_nowrite (files : IntegerRegisterFiles)
    (maskRegisters : ProofsLean.MNCore.Masks.RegisterFile) (context : ParsedIntegerContext)
    (output : IntegerALU.Bus) (cycle : Fin 4) (directive : ParsedMaskDirective)
    (hasSingleLineMask : Bool) :
    writeParsedL1ToPEDestination? files maskRegisters .nowrite context output cycle directive
        hasSingleLineMask = some (files, none) := by
  simp [writeParsedL1ToPEDestination?]

/-- A masked store of the zero bus into a zero bank keeps the bank zero. -/
theorem writeWordsMasked_zero_bus (bank : PEMemory.Bank) (width : Width)
    (start : Fin bank.capacity) (flags : BitVec 4) (longLong : Bool) :
    writeWordsMasked bank width (fun _ => 0) start (fun _ => 0) flags longLong =
      fun _ => 0 := by
  funext target
  by_cases within : distance bank start target < count bank width
  · rw [writeWordsMasked_at bank width (fun _ => 0) start target (fun _ => 0) flags
      longLong within]
    simp [mergeSelectedWord]
  · rw [writeWordsMasked_preserves_outside bank width (fun _ => 0) start target
      (fun _ => 0) flags longLong (Nat.le_of_not_lt within)]

/-- A zero-bus masked `.lm1` store into the all-zero `lm1` file leaves it zero. -/
theorem writeDirectAccessMasked_lm1_zero (files : IntegerRegisterFiles) (width : Width)
    (address : Fin PEMemory.Bank.lm1.capacity) (selection : PEWordSelection)
    (zero : files.lm1 = fun _ => 0) :
    (writeDirectAccessMasked files ⟨PEMemory.Bank.lm1, width, address⟩ (fun _ => 0)
      selection).lm1 = fun _ => 0 := by
  funext target
  rw [show (writeDirectAccessMasked files ⟨PEMemory.Bank.lm1, width, address⟩ (fun _ => 0)
      selection).lm1 target =
      writeWordsMasked PEMemory.Bank.lm1 width files.lm1 address (fun _ => 0)
        selection.flags selection.longLong target from rfl]
  rw [zero]
  exact congrFun (writeWordsMasked_zero_bus PEMemory.Bank.lm1 width address
    selection.flags selection.longLong) target

/-- **A broadcast write at PE 0 cannot make an `lm1` word nonzero.**  The written
data is the zero bus, and the all-zero initial `lm1` file is a fixed point of
every such masked store. -/
theorem commitParsedMaskedWrites_lm1_zero_of_zero (writes : List PreparedParsedMaskedWrite)
    (files : IntegerRegisterFiles) (zero : files.lm1 = fun _ => 0)
    (h : ∀ write ∈ writes, ∀ (width : Width) (address : Fin PEMemory.Bank.lm1.capacity),
      write.destination = some ⟨PEMemory.Bank.lm1, width, address⟩ →
        write.data = fun _ => 0) :
    (commitParsedMaskedWrites files writes).lm1 = fun _ => 0 := by
  induction writes generalizing files with
  | nil => exact zero
  | cons write rest ih =>
      rw [commitParsedMaskedWrites_cons]
      apply ih
      · unfold welcomeCommitStep
        split
        · exact zero
        · split
          · rename_i destination hdest
            cases destination with
            | mk bank width address =>
                cases bank with
                | lm1 =>
                    rw [h write (by simp) width address hdest]
                    exact writeDirectAccessMasked_lm1_zero files width address write.selection zero
                | lm0 =>
                    rw [writeDirectAccessMasked_lm1_of_ne files _ write.data write.selection
                      (by simp)]
                    exact zero
                | grf0 =>
                    rw [writeDirectAccessMasked_lm1_of_ne files _ write.data write.selection
                      (by simp)]
                    exact zero
                | grf1 =>
                    rw [writeDirectAccessMasked_lm1_of_ne files _ write.data write.selection
                      (by simp)]
                    exact zero
                | t =>
                    rw [writeDirectAccessMasked_lm1_of_ne files _ write.data write.selection
                      (by simp)]
                    exact zero
          · exact zero
      · intro item member width address hitem
        exact h item (List.mem_cons_of_mem _ member) width address hitem


/-! ## 7. The four cycle writes of a broadcast already have the two shapes

The L1BM-to-PE stage resolves one destination operand per cycle and performs one
masked store per cycle, so at PE 0 the broadcast contributes at most four `.lm1`
writes, each at the cycle-dependent destination address and each carrying the
zero data bus of §3.  With that data the two shapes reduce to the *static*
width of the destination operand:

* width `.double`: `PEMemory.address_aligned` gives a 4-aligned address and the
  zero third data word is a copy, so the four writes are `Lm1WritesDoubleCopy`;
* width `.word`/`.long`: each write covers one or two words, so the four writes
  are `Lm1WritesNarrow`.

This is the value half of `WelcomePEL1ToPEShapeObligation` in the form the
commit decomposition consumes. -/

/-- The four cycle writes a broadcast performs at PE 0, as far as the `.lm1`
value shape is concerned: the destination operand's static width, the
cycle-resolved addresses and selections, and the zero data bus of §3. -/
def l1ToPEWrites (width : Width) (addresses : Fin 4 → Fin PEMemory.Bank.lm1.capacity)
    (selections : Fin 4 → PEWordSelection) : List PreparedParsedMaskedWrite :=
  (List.finRange 4).map fun cycle =>
    ⟨some ⟨PEMemory.Bank.lm1, width, addresses cycle⟩, none, fun _ => 0, selections cycle⟩

theorem l1ToPEWrites_length (width : Width)
    (addresses : Fin 4 → Fin PEMemory.Bank.lm1.capacity)
    (selections : Fin 4 → PEWordSelection) :
    (l1ToPEWrites width addresses selections).length = 4 := by
  simp [l1ToPEWrites]

theorem l1ToPEWrites_mem (width : Width)
    (addresses : Fin 4 → Fin PEMemory.Bank.lm1.capacity)
    (selections : Fin 4 → PEWordSelection) (write : PreparedParsedMaskedWrite)
    (member : write ∈ l1ToPEWrites width addresses selections) :
    ∃ cycle : Fin 4, write.destination = some ⟨PEMemory.Bank.lm1, width, addresses cycle⟩ ∧
      write.data = (fun _ => 0) ∧ write.selection = selections cycle := by
  simp only [l1ToPEWrites, List.mem_map, List.mem_finRange] at member
  obtain ⟨cycle, _, rfl⟩ := member
  exact ⟨cycle, rfl, rfl, rfl⟩

/-- **The `.double` case**: four 4-aligned `.double` writes with zero data are a
`Lm1WritesDoubleCopy` list. -/
theorem l1ToPEWrites_doubleCopy (addresses : Fin 4 → Fin PEMemory.Bank.lm1.capacity)
    (selections : Fin 4 → PEWordSelection)
    (aligned : ∀ cycle, (addresses cycle).val % 4 = 0) :
    Lm1WritesDoubleCopy (l1ToPEWrites .double addresses selections) := by
  intro write member width address data selection destination dataEq selectionEq
  simp only [l1ToPEWrites, List.mem_map, List.mem_finRange] at member
  obtain ⟨cycle, _, rfl⟩ := member
  simp only [Option.some.injEq] at destination
  injection destination with hbank hwidth haddress
  subst hwidth
  subst haddress
  refine ⟨rfl, aligned cycle, ?_⟩
  intro bound
  rw [← dataEq]
  exact isWelcomeCopy_zero

/-- The `.lm1` word count of a `.word`/`.long` destination is at most two. -/
theorem count_lm1_le_two_of_ne_double (width : Width) (notDouble : width ≠ .double) :
    count PEMemory.Bank.lm1 width ≤ 2 := by
  cases width with
  | word => decide
  | long => decide
  | double => exact absurd rfl notDouble

/-- **The non-`.double` case**: four `.word`/`.long` writes fit four narrow
windows. -/
theorem l1ToPEWrites_narrow (width : Width)
    (addresses : Fin 4 → Fin PEMemory.Bank.lm1.capacity)
    (selections : Fin 4 → PEWordSelection) (notDouble : width ≠ .double) :
    Lm1WritesNarrow (l1ToPEWrites width addresses selections) := by
  refine ⟨(List.finRange 4).map fun cycle =>
    (addresses cycle, count PEMemory.Bank.lm1 width), ?_, ?_, ?_⟩
  · intro write member writeWidth address destination
    simp only [l1ToPEWrites, List.mem_map, List.mem_finRange] at member
    obtain ⟨cycle, _, rfl⟩ := member
    simp only [Option.some.injEq] at destination
    injection destination with hbank hwidth haddress
    subst hwidth
    subst haddress
    exact List.mem_map_of_mem (List.mem_finRange cycle)
  · simp
  · intro window member
    simp only [List.mem_map, List.mem_finRange] at member
    obtain ⟨cycle, _, rfl⟩ := member
    exact count_lm1_le_two_of_ne_double width notDouble


/-! ## 8. The L1BM-to-PE walk only rewrites the register file of the PE it visits

`executeParsedL1ToPEAtPEs` walks the PE list; each step rewrites `peRegisters`,
`forwarding`, `forwardingValid` and `peContext` of the visited PE only.  Hence
a PE that is not in the list keeps its register file.  This is the per-PE frame
the PE 0 extraction consumes. -/

theorem executeParsedL1ToPEAtPEs_peRegisters_not_mem (readState : State)
    (expression : ParsedExpr) (access : ParsedL1ToPEAccess)
    (noForward hasSingleLineMask usePreIssueMask : Bool) :
    ∀ (pes : List PEId) (state next : State) (p : PEId),
      executeParsedL1ToPEAtPEs readState state expression access pes noForward hasSingleLineMask
        usePreIssueMask = .ok next →
      p ∉ pes → next.peRegisters p = state.peRegisters p := by
  intro pes
  induction pes with
  | nil =>
      intro state next p executed _
      simp only [executeParsedL1ToPEAtPEs, StepResult.ok.injEq] at executed
      rw [executed]
  | cons pe rest ih =>
      intro state next p executed notMem
      have hne : p ≠ pe := by intro h; subst h; exact notMem (by simp)
      have hnotRest : p ∉ rest := by
        intro h; exact notMem (List.mem_cons_of_mem _ h)
      simp only [executeParsedL1ToPEAtPEs] at executed
      split at executed
      · cases executed
      · split at executed
        · cases executed
        · cases executed
        · rename_i files bar0 bar1 wrote
          rw [ih _ _ p executed hnotRest]
          simp [hne]

/-! ## 9. Unfolding the L1BM-to-PE cycle loops

`executeParsedL1ToPEAtPEs` uses two local loops: `writeCycles` over the four
cycles and `writeDestinations` over the destination operands.  Lean lifts both
to stable auxiliary declarations, so their equations can be named.  The lemmas
below expose exactly the interface the line-level assembly needs:

* `writeDestinations_nil` / `writeDestinations_mem_singleton`: the destination
  loop of one cycle is a single masked store of the bus;
* `writeCycles_cons`: one cycle of the cycle loop is the destination loop
  followed by the rest of the cycles;
* `writeCycles_four`: given the four per-cycle destination results, the cycle
  loop returns their composition. -/

theorem writeDestinations_nil (currentState : State) (hasSingleLineMask : Bool)
    (maskRegisters : ProofsLean.MNCore.Masks.RegisterFile) (cycle : Fin 4)
    (context : ParsedIntegerContext) (output : IntegerALU.Bus)
    (files : IntegerRegisterFiles) (bar0 bar1 : BitVec 12) :
    executeParsedL1ToPEAtPEs.writeCycles.writeDestinations currentState hasSingleLineMask
        maskRegisters cycle context output [] files bar0 bar1 = some (files, bar0, bar1) := by
  rw [executeParsedL1ToPEAtPEs.writeCycles.writeDestinations]

/-- One destination cycle of the `.mem` form is exactly one masked store of the
flushed broadcast bus. -/
theorem writeDestinations_mem_singleton (currentState : State) (hasSingleLineMask : Bool)
    (maskRegisters : ProofsLean.MNCore.Masks.RegisterFile) (cycle : Fin 4)
    (context : ParsedIntegerContext) (output : IntegerALU.Bus) (access : Access)
    (negated extended rounded : Bool) (mask : Option ParsedMask)
    (files : IntegerRegisterFiles) (bar0 bar1 : BitVec 12)
    (access' : DirectMemoryAccess) (selection : PEWordSelection)
    (lowered : ParsedOperand.toDirectMemoryDestination?
      (.mem access negated extended rounded mask) context.pe cycle bar0 bar1
      context.tWord = some access')
    (resolved : ParsedOperand.resolveMemoryWriteSelection?
      (.mem access negated extended rounded mask) access'.bank maskRegisters cycle
      currentState.maskDirective hasSingleLineMask = some selection) :
    executeParsedL1ToPEAtPEs.writeCycles.writeDestinations currentState hasSingleLineMask
        maskRegisters cycle context output [.mem access negated extended rounded mask] files
        bar0 bar1 =
      some (writeDirectAccessMasked files access' (PEMemory.unpackALUBus output) selection,
        bar0, bar1) := by
  rw [executeParsedL1ToPEAtPEs.writeCycles.writeDestinations]
  simp only [writeParsedL1ToPEDestination?]
  simp [lowered, resolved]
  rw [executeParsedL1ToPEAtPEs.writeCycles.writeDestinations]

/-- The `.nowrite` destination leaves the file and the BARs untouched. -/
theorem writeDestinations_nowrite_singleton (currentState : State)
    (hasSingleLineMask : Bool) (maskRegisters : ProofsLean.MNCore.Masks.RegisterFile)
    (cycle : Fin 4) (context : ParsedIntegerContext) (output : IntegerALU.Bus)
    (files : IntegerRegisterFiles) (bar0 bar1 : BitVec 12) :
    executeParsedL1ToPEAtPEs.writeCycles.writeDestinations currentState hasSingleLineMask
        maskRegisters cycle context output [.nowrite] files bar0 bar1 =
      some (files, bar0, bar1) := by
  rw [executeParsedL1ToPEAtPEs.writeCycles.writeDestinations]
  simp [writeParsedL1ToPEDestination?]
  rw [executeParsedL1ToPEAtPEs.writeCycles.writeDestinations]

/-- **One cycle of the L1BM-to-PE cycle loop.**  The cycle resolves its flush
selection, computes the broadcast bus, runs the destination loop, and continues
with the remaining cycles from the resulting register file and BARs. -/
theorem writeCycles_cons (readState currentState : State) (expression : ParsedExpr)
    (access : ParsedL1ToPEAccess) (hasSingleLineMask : Bool) (pe : PEId)
    (coordinates readContext : ParsedIntegerContext) (maskRegisters : Masks.RegisterFile)
    (cycle : Fin 4) (cycles : List (Fin 4))
    (files nextFiles : IntegerRegisterFiles) (bar0 bar1 nextBar0 nextBar1 : BitVec 12)
    (selection : Option PEWordSelection)
    (flushed : resolveFlushSelection? expression.flush maskRegisters cycle = some selection)
    (wrote : executeParsedL1ToPEAtPEs.writeCycles.writeDestinations currentState hasSingleLineMask
        maskRegisters cycle
        { coordinates with cycle := cycle, bar0 := bar0, bar1 := bar1, tWord := readContext.tWord }
        (parsedOutputAfterFlush selection (l1ToPEBusAt readState expression access pe cycle))
        access.destinations files bar0 bar1 = some (nextFiles, nextBar0, nextBar1)) :
    executeParsedL1ToPEAtPEs.writeCycles readState currentState expression access hasSingleLineMask pe
        coordinates readContext maskRegisters (cycle :: cycles) files bar0 bar1 =
      executeParsedL1ToPEAtPEs.writeCycles readState currentState expression access hasSingleLineMask pe
        coordinates readContext maskRegisters cycles nextFiles nextBar0 nextBar1 := by
  rw [executeParsedL1ToPEAtPEs.writeCycles]
  simp only []
  rw [flushed]
  simp only []
  rw [wrote]

/-- The empty cycle list is the identity. -/
theorem writeCycles_nil (readState currentState : State) (expression : ParsedExpr)
    (access : ParsedL1ToPEAccess) (hasSingleLineMask : Bool) (pe : PEId)
    (coordinates readContext : ParsedIntegerContext) (maskRegisters : Masks.RegisterFile)
    (files : IntegerRegisterFiles) (bar0 bar1 : BitVec 12) :
    executeParsedL1ToPEAtPEs.writeCycles readState currentState expression access hasSingleLineMask pe
        coordinates readContext maskRegisters [] files bar0 bar1 = .ok (files, bar0, bar1) := by
  rw [executeParsedL1ToPEAtPEs.writeCycles]

/-- **The four cycles.**  Given the four per-cycle destination results, the
cycle loop returns their composition.  The `.mem` destination leaves the BARs
unchanged, which is the case the broadcast uses. -/
theorem writeCycles_four (readState currentState : State) (expression : ParsedExpr)
    (access : ParsedL1ToPEAccess) (hasSingleLineMask : Bool) (pe : PEId)
    (coordinates readContext : ParsedIntegerContext) (maskRegisters : Masks.RegisterFile)
    (files0 files1 files2 files3 files4 : IntegerRegisterFiles)
    (b0 b1 b2 b3 : BitVec 12)
    (selection0 selection1 selection2 selection3 : Option PEWordSelection)
    (flushed0 : resolveFlushSelection? expression.flush maskRegisters 0 = some selection0)
    (flushed1 : resolveFlushSelection? expression.flush maskRegisters 1 = some selection1)
    (flushed2 : resolveFlushSelection? expression.flush maskRegisters 2 = some selection2)
    (flushed3 : resolveFlushSelection? expression.flush maskRegisters 3 = some selection3)
    (wrote0 : executeParsedL1ToPEAtPEs.writeCycles.writeDestinations currentState hasSingleLineMask
        maskRegisters 0
        { coordinates with cycle := 0, bar0 := b0, bar1 := b1, tWord := readContext.tWord }
        (parsedOutputAfterFlush selection0 (l1ToPEBusAt readState expression access pe 0))
        access.destinations files0 b0 b1 = some (files1, b0, b1))
    (wrote1 : executeParsedL1ToPEAtPEs.writeCycles.writeDestinations currentState hasSingleLineMask
        maskRegisters 1
        { coordinates with cycle := 1, bar0 := b0, bar1 := b1, tWord := readContext.tWord }
        (parsedOutputAfterFlush selection1 (l1ToPEBusAt readState expression access pe 1))
        access.destinations files1 b0 b1 = some (files2, b0, b1))
    (wrote2 : executeParsedL1ToPEAtPEs.writeCycles.writeDestinations currentState hasSingleLineMask
        maskRegisters 2
        { coordinates with cycle := 2, bar0 := b0, bar1 := b1, tWord := readContext.tWord }
        (parsedOutputAfterFlush selection2 (l1ToPEBusAt readState expression access pe 2))
        access.destinations files2 b0 b1 = some (files3, b0, b1))
    (wrote3 : executeParsedL1ToPEAtPEs.writeCycles.writeDestinations currentState hasSingleLineMask
        maskRegisters 3
        { coordinates with cycle := 3, bar0 := b0, bar1 := b1, tWord := readContext.tWord }
        (parsedOutputAfterFlush selection3 (l1ToPEBusAt readState expression access pe 3))
        access.destinations files3 b0 b1 = some (files4, b0, b1)) :
    executeParsedL1ToPEAtPEs.writeCycles readState currentState expression access hasSingleLineMask pe
        coordinates readContext maskRegisters [0, 1, 2, 3] files0 b0 b1 =
      .ok (files4, b0, b1) := by
  rw [writeCycles_cons readState currentState expression access hasSingleLineMask pe coordinates
    readContext maskRegisters 0 [1, 2, 3] files0 files1 b0 b1 b0 b1 selection0 flushed0 wrote0]
  rw [writeCycles_cons readState currentState expression access hasSingleLineMask pe coordinates
    readContext maskRegisters 1 [2, 3] files1 files2 b0 b1 b0 b1 selection1 flushed1 wrote1]
  rw [writeCycles_cons readState currentState expression access hasSingleLineMask pe coordinates
    readContext maskRegisters 2 [3] files2 files3 b0 b1 b0 b1 selection2 flushed2 wrote2]
  rw [writeCycles_cons readState currentState expression access hasSingleLineMask pe coordinates
    readContext maskRegisters 3 [] files3 files4 b0 b1 b0 b1 selection3 flushed3 wrote3]
  exact writeCycles_nil readState currentState expression access hasSingleLineMask pe coordinates
    readContext maskRegisters files4 b0 b1

/-! ## 10. What is still missing for the two family obligations

### The two `Prop`s (verbatim from `WelcomeValueBound.lean` §7)

```
def WelcomePEL1ToPEShapeObligation : Prop :=
  ∀ expressions : List NormalizedExpr, WelcomePEUnrefuted expressions →
    (expressions.map NormalizedExpr.toParsed).any parsedExprIsL1ToPEProducer = true →
    WelcomePEWriteShape expressions

def WelcomePEL2BMShapeObligation : Prop :=
  ∀ expressions : List NormalizedExpr, WelcomePEUnrefuted expressions →
    (expressions.map NormalizedExpr.toParsed).any parsedExprIsL2BMProducer = true →
    WelcomePEWriteShape expressions
```

Neither is proved here.

### Structural obstruction: the family row need not be the `LM1` writer

An `.l2bm` row never writes `lm0`/`lm1`: `executeParsedL2BlockExpression` rewrites
only `l1bm`, `blockMemory`, `dar`, `darBuffer`, `darBufferReadAddress` and
`darWriteAddress` (§5 proves the `peRegisters` half), and its destinations are
`.l1bm`/`.l2bm`/`.dar` operands, which `ParsedOperand.accesses` does not turn
into `Access`es, so the row's `Expr.writeBanks` contains no `lm0`/`lm1`.

An addressed `.l1bm` broadcast *can* write `lm1` (its destinations are `.mem`
operands of any bank, or `.bar`), but it can just as well write only `lm0`; in
that case the line's `LM1` writer is another row.

Consequently both family `Prop`s quantify over lines whose shape is decided by a
*different* row (a plain `.alu` row, an `.immediate` row, a `.matrixRead`/`.mau`/
`.matrixWrite` row, or another `.l1bm` broadcast), so neither can be closed from
its own family's stage.  The sound specialisation for the `L1BM` family is "the
`L1ToPE` row is the unique `LM1` writer"; for `.l2bm` the family row is
value-irrelevant and the `Prop` is exactly as hard as the aggregate over the
line's other rows.

### Interface delivered for the unified single-`LM1`-writer reduction

For the row-level predicate "this row writes the PE `lm1` file", the assembly
can use:

* `.l2bm` rows: **false**, by `executeParsedSharedBlockProducers_peRegisters`;
* `.l1bm` broadcast rows: a destination operand of the `.mem` form resolves a
  `DirectMemoryAccess` whose bank is static per operand; when that bank is `lm1`
  the row is an `lm1` writer.  In that case
  * the data bus is the zero bus at the initial state for every input
    (`l1ToPEBusAt_welcomeInitialState`), so word 2 of the write is a copy
    (`l1ToPE_data_word_two_isWelcomeCopy`);
  * the write is a masked store of that bus
    (`writeParsedL1ToPEDestination_mem`, `writeDestinations_mem_singleton`);
  * a masked store of the zero bus cannot make an all-zero `lm1` file nonzero
    (`commitParsedMaskedWrites_lm1_zero_of_zero`);
  * the four cycle writes are `Lm1WritesDoubleCopy` when the destination width is
    `.double` and `Lm1WritesNarrow` otherwise (`l1ToPEWrites_doubleCopy`,
    `l1ToPEWrites_narrow`).

Frames available for the assembly:

* `executeParsedSharedBlockProducers_peRegisters` — the shared-block stage
  (`.l1bm` `.mwrite`/`.m4write`/`.gather`/`.reduce`/`.reduce4`, all `.l2bm`
  producers, `.dars`, `.darw`) preserves every PE register file;
* `executeParsedL1ToPEAtPEs_peRegisters_not_mem` — the L1BM-to-PE walk preserves
  the register file of every PE it does not visit;
* `commitParsedMaskedWrites_lm1_of_no_lm1` and `welcomeCommitStep_lm1_of_ne` —
  a commit with no `.lm1` destination preserves `lm1`.

### Missing executor facts

1. **`LM1` frames of the four middle stages** (`executeParsedMslMsrProducers`,
   `executeParsedFloatReluProducers`, `executeParsedBlockFloatProducer`,
   `executeParsedMatrixMAUAndWrites`): *if no expression of the line has an
   `.lm1` destination operand (`.mem` bank `lm1`, or `.bar true`), these stages
   preserve `lm1` at every PE.*  Their destination writers all funnel into
   `writeDirectAccessMasked`, and §4 supplies the bank frame; the work is the
   per-PE walk and the `let rec writeDestinations` loops.
2. **Integer-stage list-level provenance.**  `prepareParsedIntegerALUExprCycle_lm1_facts`
   gives the per-cycle provenance, and
   `executeIntegerProducerLineAtPEs_prepared` gives the commit form; what is
   missing is the list-level statement that a prepared write list generated from
   expressions with no `.lm1` destination operand has no `.lm1` destination
   (then `commitParsedMaskedWrites_lm1_of_no_lm1` applies).  The integer stage's
   `peExpressions` filter removes the `L1ToPE` row
   (`parsedExprIsIntegerMatrixReadStageInput` mentions
   `parsedExprIsL1ToPEProducer`).
3. **Outer one-step unfolding of `executeParsedL1ToPEAtPEs`.**  The cycle loops
   are now named equations (§9: `writeCycles_cons`, `writeCycles_four`,
   `writeDestinations_mem_singleton`), so what remains is: unfold
   `executeParsedL1ToPEAtPEs` once for the head PE and show that the head's
   register file is the `writeCycles [0,1,2,3]` result (the tail frame is §8).

With 1–3 and the `writesUnique` bridge the "the `L1ToPE` row is the `LM1`
writer" case closes.  The remaining case is the other families' work by the
obstruction above.  No `LM1` frame, provenance or unfolding fact is needed for
the `.l2bm` family beyond what §5 already gives.

-/

end ProofsLean.MNCore
