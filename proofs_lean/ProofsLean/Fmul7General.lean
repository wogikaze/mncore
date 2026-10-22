import ProofsLean.Fmul7Optimal
import ProofsLean.FamilyDestinationCongruence
import ProofsLean.PlusTwoLowerBound

/-! # `2.fmul7` — the general line layer and the BAR caveat

`ProofsLean/Fmul7Optimal.lean` fixes the specification, the five-line answer,
the issue-level rejection of a 16-word product line, and the counting skeleton
`fmul7_shape_score_five`.  Its `Fmul7LineShapeResidual` is stated for an
**arbitrary** state.  That is too strong for the `LM1` destination of `fvmul`:

* the effective `.lm1` address is
  `(bar1 + regionAddressAt cycle) / width.words * width.words % capacity`
  (`ParsedOperand.toDirectMemoryAccessMode?`), so a non-zero `bar1` shifts the
  write window;
* with `bar1 = 2`, the four cycles write addresses `2, 4, 6, 8` instead of
  `0, 2, 4, 6` (proved below by `decide`).  Address `8` is outside
  `fmul7Window 0`, and window word `0` is not written at all;
* therefore `Fmul7LineShapeResidual.productZero`, which claims that *every*
  window word becomes zero for an arbitrary zero-`t` state, is false: a state
  with `bar1 = 2`, `t = 0`, and `lm1[0] = 5` ends with `lm1[0] = 5`, not `0`.

The shape program of the answer starts from `fmul7InitialState`, whose `bar1`
is zero, and neither shape line writes `bar1`.  The correct residual therefore
carries `(state.peContext 0).bar1 = 0` (and a preservation field for it).  The
corrected residual is `Fmul7LineShapeResidualZeroBar` below.

What is proved in this module:

* the exact `.lm1` destination of one `fvmul` cycle (`fmul7Lm1Destination_exists`);
* the destination membership of `parsedStepDestinations` for that operand;
* the flat-map form over the four cycles;
* a commit frame: committing a list of `.lm1` writes leaves the `t` bank
  unchanged (`commitParsedMaskedWrites_t_of_all_lm1`);
* the wrapper-to-run extraction for the float-MAU stage
  (`fmul7FloatRun`).

The remaining proof obligation is named, not hidden: the corrected residual
fields and the general (non-shape) line refutation.

No `sorry`, no `admit`, no `native_decide`, no new axioms.
-/

namespace ProofsLean.MNCore

open Issue
open PEMemory

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

/-! ## 1. The `.lm1` destination of one `fvmul` cycle -/

/-- A single `fvmul` cycle has a `.lm1` destination of width `.long`; the
address depends on `bar1`. -/
theorem fmul7Lm1Destination_exists (base : Nat) (cycle : Fin 4) (bar0 bar1 : BitVec 12)
    (tWord : BitVec 32) :
    ∃ addr : Fin PEMemory.Bank.lm1.capacity,
      ParsedOperand.toDirectMemoryDestination? (fmul7Lm1Long base) 0 cycle bar0 bar1 tWord =
        some ⟨.lm1, .long, addr⟩ := by
  simp (config := { decide := true }) [ParsedOperand.toDirectMemoryDestination?,
    ParsedOperand.toDirectMemoryAccessMode?, fmul7Lm1Long, fmul7LongRegion,
    parsedRegionAddressAt, parsedWidth?,
    issueBankToRegisterBank, PEMemory.Bank.capacity]
  all_goals
    have hcycle : cycle.val = 0 ∨ cycle.val = 1 ∨ cycle.val = 2 ∨ cycle.val = 3 := by
      have := cycle.isLt; omega
    rcases hcycle with h | h | h | h <;> simp [h, PEMemory.Width.words] <;> exact ⟨_, rfl⟩

/-- **The BAR caveat, concretely.**  With `bar1 = 2`, cycle `3` of the first
product writes `LM1` address `8`, not `6`.  This is the arithmetic reason why
`Fmul7LineShapeResidual.productZero` cannot hold for arbitrary states. -/
theorem fmul7_bar1_shifts_cycle3 :
    ParsedOperand.toDirectMemoryDestination? (fmul7Lm1Long 0) 0 3 0 2 0 =
      some ⟨.lm1, .long, ⟨8, by decide⟩⟩ := by
  decide

/-- With `bar1 = 2`, cycle `0` writes address `2`, so window word `0` is not
written by any cycle (`2, 4, 6, 8`). -/
theorem fmul7_bar1_shifts_cycle0 :
    ParsedOperand.toDirectMemoryDestination? (fmul7Lm1Long 0) 0 0 0 2 0 =
      some ⟨.lm1, .long, ⟨2, by decide⟩⟩ := by
  decide

/-- With `bar1 = 0` (the initial state of the answer), cycle `c` writes
`base + 2c`. -/
theorem fmul7_zeroBar_destination (slot : Fin 4) (cycle : Fin 4) (bar0 : BitVec 12)
    (tWord : BitVec 32) :
    ParsedOperand.toDirectMemoryDestination?
        (fmul7Lm1Long (8 * slot.val)) 0 cycle bar0 0 tWord =
      some ⟨.lm1, .long, ⟨8 * slot.val + 2 * cycle.val, by
        have hcap : PEMemory.Bank.lm1.capacity = 4096 := rfl
        have := slot.isLt; have := cycle.isLt; omega⟩⟩ := by
  simp (config := { decide := true }) [ParsedOperand.toDirectMemoryDestination?,
    ParsedOperand.toDirectMemoryAccessMode?, fmul7Lm1Long, fmul7LongRegion,
    parsedRegionAddressAt, parsedWidth?,
    issueBankToRegisterBank, PEMemory.Bank.capacity]
  all_goals
    have hcycle : cycle.val = 0 ∨ cycle.val = 1 ∨ cycle.val = 2 ∨ cycle.val = 3 := by
      have := cycle.isLt; omega
    rcases hcycle with h | h | h | h <;> simp [h, PEMemory.Width.words] <;>
      congr 1 <;> apply Fin.ext <;> simp only [Fin.val_mk] <;> omega

/-! ## 2. Destination membership of the four-cycle flat map -/

/-- Every destination produced by `parsedStepDestinations` for one product
cycle is a `.lm1` `.long` write. -/
theorem fmul7StepDestinations_mem_lm1 (base : Nat) (cycle : Fin 4) (bar0 bar1 : BitVec 12)
    (tWord : BitVec 32) :
    ∀ d ∈ parsedStepDestinations (fmul7Lm1Long base) 0 cycle bar0 bar1 tWord,
      ∃ addr, d = some ⟨.lm1, .long, addr⟩ := by
  intro d hd
  obtain ⟨addr, h⟩ := fmul7Lm1Destination_exists base cycle bar0 bar1 tWord
  simp only [fmul7Lm1Long] at hd h
  rw [parsedStepDestinations_mem] at hd
  rw [h] at hd
  simp only [List.mem_singleton] at hd
  exact ⟨addr, hd⟩

/-- The four-cycle flat map has only `.lm1` `.long` destinations. -/
theorem fmul7FlatMap_lm1 (base : Nat) (bar0 bar1 : BitVec 12) (tWord : BitVec 32) :
    ∀ d ∈ ([0, 1, 2, 3].flatMap (fun cycle : Fin 4 =>
      parsedStepDestinations (fmul7Lm1Long base) 0 cycle bar0 bar1 tWord)),
      ∃ addr, d = some ⟨.lm1, .long, addr⟩ := by
  intro d hd
  simp only [List.mem_flatMap, List.mem_cons, List.not_mem_nil] at hd
  obtain ⟨cycle, _, hd⟩ := hd
  exact fmul7StepDestinations_mem_lm1 base cycle bar0 bar1 tWord d hd

/-! ## 3. Commit frames for `.lm1`-only write lists -/

/-- Committing only `.lm1` writes leaves the `t` bank unchanged. -/
theorem commitParsedMaskedWrites_t_of_all_lm1
    (files : IntegerRegisterFiles) (writes : List PreparedParsedMaskedWrite)
    (allLm1 : ∀ write ∈ writes, ∀ (bank : PEMemory.Bank) (width : PEMemory.Width)
        (address : Fin bank.capacity),
      write.destination = some ⟨bank, width, address⟩ → bank = .lm1) :
    (commitParsedMaskedWrites files writes).t = files.t := by
  induction writes generalizing files with
  | nil => rfl
  | cons write rest ih =>
      rw [show commitParsedMaskedWrites files (write :: rest) =
          commitParsedMaskedWrites
            (commitParsedMaskedWrites files [write]) rest from rfl]
      rw [ih (commitParsedMaskedWrites files [write])
        (fun w mem => allLm1 w (List.mem_cons_of_mem _ mem))]
      unfold commitParsedMaskedWrites
      simp only [List.foldl_cons, List.foldl_nil]
      split
      · rfl
      · split
        · rename_i destination hdest
          rcases destination with ⟨bank, width, address⟩
          have bankEq := allLm1 write (by simp) bank width address hdest
          subst bankEq
          rfl
        · rfl

/-! ## 4. Wrapper-to-run extraction for the float-MAU stage -/

/-- The wrapper `executeParsedFloatMAUsAtPE` is the filtered `run`; expose the
run equation at the singleton product list. -/
theorem fmul7FloatRun (state : State) (pe : PEId) (slot : Fin 4)
    (currentFiles : IntegerRegisterFiles)
    (floatFiles : IntegerRegisterFiles) (a b : BitVec 12)
    (outputs : Fin 4 → IntegerALU.Bus) (has : Bool)
    (floatEq : executeParsedFloatMAUsAtPE (state.peRegisters pe) currentFiles
      (stateForwardingSlots state pe)
      { (ParsedIntegerContext.ofLinearIndex pe) with
        bar0 := (state.peContext pe).bar0
        bar1 := (state.peContext pe).bar1
        tWord := (state.peContext pe).tWord }
      [(fmul7MulExpr (8 * slot.val)).toParsed] state.maskDirective
      (([(fmul7MulExpr (8 * slot.val)).toParsed].any parsedExprHasSingleLineWriteMask)) =
      .ok (floatFiles, a, b, outputs, has)) :
    ∃ (nextBar0 nextBar1 : BitVec 12) (nextOutputs : Fin 4 → IntegerALU.Bus),
      executeParsedFloatMAUsAtPE.run (state.peRegisters pe) (stateForwardingSlots state pe)
        { (ParsedIntegerContext.ofLinearIndex pe) with
          bar0 := (state.peContext pe).bar0
          bar1 := (state.peContext pe).bar1
          tWord := (state.peContext pe).tWord }
        state.maskDirective
        (([(fmul7MulExpr (8 * slot.val)).toParsed].any parsedExprHasSingleLineWriteMask))
        [(fmul7MulExpr (8 * slot.val)).toParsed] currentFiles
        (state.peContext pe).bar0 (state.peContext pe).bar1 (fun _ => ⟨0, 0⟩) =
        .ok (floatFiles, nextBar0, nextBar1, nextOutputs) := by
  unfold executeParsedFloatMAUsAtPE at floatEq
  simp only [List.filter_cons, List.filter_nil, List.any_cons, List.any_nil] at floatEq
  split at floatEq
  · simp at floatEq
  · simp at floatEq
  · rename_i fb fa fbb fo
    injection floatEq with hTuple
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hTuple
    have supported :
        parsedExprIsSupportedFloatMAUProducer (fmul7MulExpr (8 * slot.val)).toParsed = true := rfl
    simp only [supported, ite_true, List.any_cons, List.any_nil, Bool.or_false] at fo ⊢
    exact ⟨a, b, outputs, fo⟩

/-! ## 5. The corrected shape residual (BAR-zero) -/

/-- `ProofsLean/Fmul7Optimal.lean`'s `Fmul7LineShapeResidual` with the `bar1`
hypotheses that its `LM1` frame/zero fields actually need, plus the BAR
preservation fields that carry `bar1 = 0` through a shape program. -/
structure Fmul7LineShapeResidualZeroBar : Prop where
  constFrame : ∀ (state next : State),
    executeNormalizedLine (.pe [fmul7ImmExpr]) state = .ok next →
    ∀ index : Fin 32,
      (next.peRegisters 0).lm1 (fmul7Lm1Index index) =
        (state.peRegisters 0).lm1 (fmul7Lm1Index index)
  constBar : ∀ (state next : State),
    executeNormalizedLine (.pe [fmul7ImmExpr]) state = .ok next →
    (next.peContext 0).bar1 = (state.peContext 0).bar1
  productFrame : ∀ (slot : Fin 4) (state next : State),
    (state.peContext 0).bar1 = 0 →
    executeNormalizedLine (.pe [fmul7MulExpr (8 * slot.val)]) state = .ok next →
    ∀ index : Fin 32, index ∉ fmul7Window slot →
      (next.peRegisters 0).lm1 (fmul7Lm1Index index) =
        (state.peRegisters 0).lm1 (fmul7Lm1Index index)
  productBar : ∀ (slot : Fin 4) (state next : State),
    executeNormalizedLine (.pe [fmul7MulExpr (8 * slot.val)]) state = .ok next →
    (next.peContext 0).bar1 = (state.peContext 0).bar1
  productTFrame : ∀ (slot : Fin 4) (state next : State),
    executeNormalizedLine (.pe [fmul7MulExpr (8 * slot.val)]) state = .ok next →
    ∀ address, (next.peRegisters 0).t address = (state.peRegisters 0).t address
  productZero : ∀ (slot : Fin 4) (state next : State),
    (state.peContext 0).bar1 = 0 →
    (∀ address, (state.peRegisters 0).t address = 0) →
    executeNormalizedLine (.pe [fmul7MulExpr (8 * slot.val)]) state = .ok next →
    ∀ index : Fin 32, index ∈ fmul7Window slot →
      (next.peRegisters 0).lm1 (fmul7Lm1Index index) = 0

/-! ## 6. The general (non-shape) residual -/

/-- Every correct program of at most four lines consists of shape lines.  This
is the general line analysis: a non-product line cannot write a correct
`7 * x` output word, a non-constant line cannot supply `7.0`, and the
`imm`/product split is the only way to cover the 32 words with four lines. -/
def Fmul7ShortProgramsAreShape : Prop :=
  ∀ (program : List InstructionLine),
    program.length ≤ 4 →
    ProofsLean.Correct fmul7SealedMachine fmul7Spec program →
    ∀ line ∈ program, Fmul7ShapeLine line

/-- The two remaining obligations for the unconditional `LowerBound 5`: the
corrected per-line shape residual and the general short-program shape
analysis. -/
def Fmul7GeneralResidual : Prop :=
  Fmul7LineShapeResidualZeroBar ∧ Fmul7ShortProgramsAreShape

/-! ## 7. Trust report -/

#print axioms fmul7Lm1Destination_exists
#print axioms fmul7_bar1_shifts_cycle3
#print axioms fmul7_bar1_shifts_cycle0
#print axioms fmul7_zeroBar_destination
#print axioms fmul7StepDestinations_mem_lm1
#print axioms fmul7FlatMap_lm1
#print axioms commitParsedMaskedWrites_t_of_all_lm1
#print axioms fmul7FloatRun




theorem fmul7InitialState_bar1_zero (input : Fmul7Input) :
    ((fmul7InitialState input).peContext 0).bar1 = 0 := by
  simp [fmul7InitialState, rustSimulatorInitialState, ParsedIntegerContext.ofLinearIndex]


/-! ## 5b. The shape invariants with the BAR-zero invariant -/

/-- A shape program starting with `bar1 = 0` leaves every output word outside
the product windows unchanged and keeps `bar1 = 0`. -/
theorem fmul7_shape_frame_zeroBar
    (residual : Fmul7LineShapeResidualZeroBar)
    (program : List InstructionLine)
    (shape : ∀ line ∈ program, Fmul7ShapeLine line)
    (index : Fin 32)
    (outside : ∀ line ∈ program, ∀ slot : Fin 4,
      line = .pe [fmul7MulExpr (8 * slot.val)] → index ∉ fmul7Window slot)
    (state next : State)
    (barZero : (state.peContext 0).bar1 = 0)
    (executed : ProofsLean.execute fmul7SealedMachine program state = some next) :
    (next.peRegisters 0).lm1 (fmul7Lm1Index index) =
      (state.peRegisters 0).lm1 (fmul7Lm1Index index) ∧
      (next.peContext 0).bar1 = 0 := by
  induction program generalizing state with
  | nil =>
      simp only [ProofsLean.execute] at executed
      injection executed with equal
      subst equal
      exact ⟨rfl, barZero⟩
  | cons line rest ih =>
      simp only [ProofsLean.execute] at executed
      cases step : fmul7SealedMachine.step line state with
      | none => simp [step] at executed
      | some mid =>
          simp [step] at executed
          have lineFrame : (mid.peRegisters 0).lm1 (fmul7Lm1Index index) =
              (state.peRegisters 0).lm1 (fmul7Lm1Index index) := by
            rcases shape line (by simp) with const | ⟨slot, product⟩
            · rw [const] at step
              exact residual.constFrame state mid (fmul7_step_ok step) index
            · rw [product] at step
              exact residual.productFrame slot state mid barZero (fmul7_step_ok step) index
                (outside line (by simp) slot product)
          have midBar : (mid.peContext 0).bar1 = 0 := by
            rcases shape line (by simp) with const | ⟨slot, product⟩
            · rw [const] at step
              rw [residual.constBar state mid (fmul7_step_ok step)]
              exact barZero
            · rw [product] at step
              rw [residual.productBar slot state mid (fmul7_step_ok step)]
              exact barZero
          obtain ⟨tailFrame, tailBar⟩ := ih
            (fun l mem => shape l (List.mem_cons_of_mem _ mem))
            (fun l mem slot product => outside l (List.mem_cons_of_mem _ mem) slot product)
            mid midBar executed
          exact ⟨by rw [tailFrame, lineFrame], tailBar⟩

/-- A shape program of product lines, started with a zero `LM1`, a zero `t`
bank and `bar1 = 0`, ends with all three invariants. -/
theorem fmul7_products_zero_zeroBar
    (residual : Fmul7LineShapeResidualZeroBar)
    (program : List InstructionLine)
    (allProducts : ∀ line ∈ program, Fmul7ProductLine line)
    (state next : State)
    (lm1Zero : ∀ index : Fin 32, (state.peRegisters 0).lm1 (fmul7Lm1Index index) = 0)
    (tZero : ∀ address, (state.peRegisters 0).t address = 0)
    (barZero : (state.peContext 0).bar1 = 0)
    (executed : ProofsLean.execute fmul7SealedMachine program state = some next) :
    (∀ index : Fin 32, (next.peRegisters 0).lm1 (fmul7Lm1Index index) = 0) ∧
      (∀ address, (next.peRegisters 0).t address = 0) ∧
      (next.peContext 0).bar1 = 0 := by
  induction program generalizing state with
  | nil =>
      simp only [ProofsLean.execute] at executed
      injection executed with equal
      subst equal
      exact ⟨lm1Zero, tZero, barZero⟩
  | cons line rest ih =>
      simp only [ProofsLean.execute] at executed
      cases step : fmul7SealedMachine.step line state with
      | none => simp [step] at executed
      | some mid =>
          simp [step] at executed
          obtain ⟨slot, product⟩ := allProducts line (by simp)
          have normEq : line.toNormalizedLine =
              .pe [fmul7MulExpr (8 * slot.val)] := by
            rw [product]
            rfl
          have ok : executeNormalizedLine (.pe [fmul7MulExpr (8 * slot.val)]) state = .ok mid := by
            rw [← normEq]
            exact fmul7_step_ok step
          have midT : ∀ address, (mid.peRegisters 0).t address = 0 := by
            intro address
            rw [residual.productTFrame slot state mid ok address]
            exact tZero address
          have midLm1 : ∀ index : Fin 32, (mid.peRegisters 0).lm1 (fmul7Lm1Index index) = 0 := by
            intro index
            by_cases within : index ∈ fmul7Window slot
            · exact residual.productZero slot state mid barZero tZero ok index within
            · rw [residual.productFrame slot state mid barZero ok index within]
              exact lm1Zero index
          have midBar : (mid.peContext 0).bar1 = 0 := by
            rw [residual.productBar slot state mid ok]
            exact barZero
          obtain ⟨tailLm1, tailT, tailBar⟩ := ih
            (fun l mem => allProducts l (List.mem_cons_of_mem _ mem))
            mid midLm1 midT midBar executed
          exact ⟨tailLm1, tailT, tailBar⟩

/-- `score ≥ 5` for every correct shape program, from the corrected BAR-zero
residual and the finite coverage obligation.  This is the BAR-corrected version
of `Fmul7Optimal.fmul7_shape_score_five`. -/
theorem fmul7_shape_score_five_zeroBar
    (residual : Fmul7LineShapeResidualZeroBar)
    (coverage : ∀ program : List InstructionLine, program.length ≤ 4 →
      (∀ line ∈ program, Fmul7ShapeLine line) → Fmul7ShapeCoverage program)
    (program : List InstructionLine)
    (shape : ∀ line ∈ program, Fmul7ShapeLine line)
    (correct : ProofsLean.Correct fmul7SealedMachine fmul7Spec program) :
    5 ≤ ProofsLean.score fmul7SealedMachine program := by
  rw [fmul7_shape_score_eq_length program shape]
  by_cases short : program.length ≤ 4
  · obtain ⟨result, executed, post⟩ := correct.2 fmul7AllOnes trivial
    have barZero := fmul7InitialState_bar1_zero fmul7AllOnes
    rcases coverage program short shape with uncovered | allProducts
    · obtain ⟨index, outside⟩ := uncovered
      obtain ⟨frame, _⟩ := fmul7_shape_frame_zeroBar residual program shape index outside
        (fmul7InitialState fmul7AllOnes) result barZero executed
      have initialZero := fmul7InitialState_lm1_zero fmul7AllOnes index
      have zero : (result.peRegisters 0).lm1 (fmul7Lm1Index index) = 0 := by
        rw [frame, initialZero]
      have targetNe : fmul7Target fmul7AllOnes index ≠ 0 :=
        fmul7Target_allOnes_ne_zero index
      have postZero' : (result.peRegisters 0).lm1 (fmul7Lm1Index index) =
          fmul7Target fmul7AllOnes index := post index
      exact False.elim (targetNe (by rw [← postZero', zero]))
    · obtain ⟨zeroAll, _, _⟩ := fmul7_products_zero_zeroBar residual program allProducts
        (fmul7InitialState fmul7AllOnes) result
        (fun index => fmul7InitialState_lm1_zero fmul7AllOnes index)
        (fun address => fmul7InitialState_t_zero fmul7AllOnes address)
        barZero executed
      have targetNe : fmul7Target fmul7AllOnes 0 ≠ 0 :=
        fmul7Target_allOnes_ne_zero 0
      have zeroZero : (result.peRegisters 0).lm1 (fmul7Lm1Index 0) = 0 := zeroAll 0
      have postZero' : (result.peRegisters 0).lm1 (fmul7Lm1Index 0) =
          fmul7Target fmul7AllOnes 0 := post 0
      exact False.elim (targetNe (by rw [← postZero', zeroZero]))
  · omega



/-! ## 8. Trust report for the BAR-zero layer -/

#print axioms fmul7InitialState_bar1_zero
#print axioms fmul7_shape_frame_zeroBar
#print axioms fmul7_products_zero_zeroBar
#print axioms fmul7_shape_score_five_zeroBar



end ProofsLean.MNCore
