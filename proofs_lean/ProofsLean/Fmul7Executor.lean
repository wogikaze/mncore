import ProofsLean.Fmul7Optimal
import ProofsLean.WelcomeAssembly
import ProofsLean.WelcomeFrameFix
import ProofsLean.WelcomeLm1FrameResidual
import ProofsLean.CendAnswerExec

/-! # `2.fmul7` — executor-side shape lemmas

This module is the executor half of the five-line optimality proof.  It imports
`ProofsLean.Fmul7Optimal` (the specification, the answer, and the shape
interfaces) and proves the parts assigned to it:

* the imm line's `LM1` frame (`constFrame`),
* the finite shape coverage (`Fmul7ShapeCoverage`),
* the five-line executor link (`Fmul7AnswerExecutorLink`).

No `sorry`, no `admit`, no `native_decide`, no new axioms.
-/

namespace ProofsLean.MNCore

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

open Issue
open PEMemory

/-! ## 1. A computable product-slot test -/

/-- The four canonical product forms `fvmul $lm<8s>v $t $ln<8s>v`, as a
computable optional slot. -/
def fmul7ProductSlot? (line : InstructionLine) : Option (Fin 4) :=
  if line = .pe [fmul7MulExpr 0] then some 0
  else if line = .pe [fmul7MulExpr 8] then some 1
  else if line = .pe [fmul7MulExpr 16] then some 2
  else if line = .pe [fmul7MulExpr 24] then some 3
  else none

theorem fmul7MulExpr_base_injective {a b : Nat}
    (equal : fmul7MulExpr a = fmul7MulExpr b) : a = b := by
  have sources := congrArg NormalizedExpr.sources equal
  simp [fmul7MulExpr, fmul7Lm0Long, fmul7LongRegion] at sources
  omega

theorem fmul7MulExpr_base_ne {a b : Nat} (different : a ≠ b) :
    fmul7MulExpr a ≠ fmul7MulExpr b :=
  fun equal => different (fmul7MulExpr_base_injective equal)

theorem fmul7ProductSlot?_isSome_iff (line : InstructionLine) :
    (fmul7ProductSlot? line).isSome ↔ Fmul7ProductLine line := by
  constructor
  · intro some
    unfold fmul7ProductSlot? at some
    split at some
    · exact ⟨0, by assumption⟩
    · split at some
      · exact ⟨1, by assumption⟩
      · split at some
        · exact ⟨2, by assumption⟩
        · split at some
          · exact ⟨3, by assumption⟩
          · simp at some
  · rintro ⟨slot, rfl⟩
    have bound := slot.isLt
    have cases : slot.val = 0 ∨ slot.val = 1 ∨ slot.val = 2 ∨ slot.val = 3 := by omega
    rcases cases with h | h | h | h
    · have slotEq : slot = 0 := Fin.ext (by simpa using h)
      subst slotEq
      simp [fmul7ProductSlot?]
    · have slotEq : slot = 1 := Fin.ext (by simpa using h)
      subst slotEq
      have h10 : fmul7MulExpr 8 ≠ fmul7MulExpr 0 := fmul7MulExpr_base_ne (by omega)
      simp [fmul7ProductSlot?, h10]
    · have slotEq : slot = 2 := Fin.ext (by simpa using h)
      subst slotEq
      have h20 : fmul7MulExpr 16 ≠ fmul7MulExpr 0 := fmul7MulExpr_base_ne (by omega)
      have h21 : fmul7MulExpr 16 ≠ fmul7MulExpr 8 := fmul7MulExpr_base_ne (by omega)
      simp [fmul7ProductSlot?, h20, h21]
    · have slotEq : slot = 3 := Fin.ext (by simpa using h)
      subst slotEq
      have h30 : fmul7MulExpr 24 ≠ fmul7MulExpr 0 := fmul7MulExpr_base_ne (by omega)
      have h31 : fmul7MulExpr 24 ≠ fmul7MulExpr 8 := fmul7MulExpr_base_ne (by omega)
      have h32 : fmul7MulExpr 24 ≠ fmul7MulExpr 16 := fmul7MulExpr_base_ne (by omega)
      simp [fmul7ProductSlot?, h30, h31, h32]

/-! ## 2. The product-window list and its counting facts -/

/-- The windows of the canonical product lines of a program, in order. -/
def fmul7ProductWindows (program : List InstructionLine) : List (Finset (Fin 32)) :=
  program.filterMap fun line => (fmul7ProductSlot? line).map fmul7Window

theorem fmul7ProductWindows_cons (head : InstructionLine) (rest : List InstructionLine) :
    fmul7ProductWindows (head :: rest) =
      match Option.map fmul7Window (fmul7ProductSlot? head) with
      | none => fmul7ProductWindows rest
      | some window => window :: fmul7ProductWindows rest := by
  unfold fmul7ProductWindows
  rw [List.filterMap_cons]
  cases Option.map fmul7Window (fmul7ProductSlot? head) <;> rfl

theorem fmul7ProductSlot?_eq_some {line : InstructionLine} {slot : Fin 4}
    (product : line = .pe [fmul7MulExpr (8 * slot.val)]) :
    fmul7ProductSlot? line = some slot := by
  subst product
  have bound := slot.isLt
  have cases : slot.val = 0 ∨ slot.val = 1 ∨ slot.val = 2 ∨ slot.val = 3 := by omega
  rcases cases with h | h | h | h
  · have slotEq : slot = 0 := Fin.ext (by simpa using h)
    subst slotEq
    simp [fmul7ProductSlot?]
  · have slotEq : slot = 1 := Fin.ext (by simpa using h)
    subst slotEq
    have h10 : fmul7MulExpr 8 ≠ fmul7MulExpr 0 := fmul7MulExpr_base_ne (by omega)
    simp [fmul7ProductSlot?, h10]
  · have slotEq : slot = 2 := Fin.ext (by simpa using h)
    subst slotEq
    have h20 : fmul7MulExpr 16 ≠ fmul7MulExpr 0 := fmul7MulExpr_base_ne (by omega)
    have h21 : fmul7MulExpr 16 ≠ fmul7MulExpr 8 := fmul7MulExpr_base_ne (by omega)
    simp [fmul7ProductSlot?, h20, h21]
  · have slotEq : slot = 3 := Fin.ext (by simpa using h)
    subst slotEq
    have h30 : fmul7MulExpr 24 ≠ fmul7MulExpr 0 := fmul7MulExpr_base_ne (by omega)
    have h31 : fmul7MulExpr 24 ≠ fmul7MulExpr 8 := fmul7MulExpr_base_ne (by omega)
    have h32 : fmul7MulExpr 24 ≠ fmul7MulExpr 16 := fmul7MulExpr_base_ne (by omega)
    simp [fmul7ProductSlot?, h30, h31, h32]

theorem fmul7ProductWindows_mem {program : List InstructionLine} {line : InstructionLine}
    (member : line ∈ program) {slot : Fin 4}
    (product : line = .pe [fmul7MulExpr (8 * slot.val)]) :
    fmul7Window slot ∈ fmul7ProductWindows program := by
  induction program with
  | nil => simp at member
  | cons head rest ih =>
      rw [fmul7ProductWindows_cons]
      rcases List.mem_cons.mp member with headEq | tail
      · subst headEq
        rw [fmul7ProductSlot?_eq_some product]
        simp
      · cases slotEq : fmul7ProductSlot? head with
        | none =>
            simp only [slotEq, Option.map_none]
            exact ih tail
        | some found =>
            simp only [slotEq, Option.map_some]
            exact List.mem_cons_of_mem _ (ih tail)

theorem fmul7ProductWindows_length_le (program : List InstructionLine) :
    (fmul7ProductWindows program).length ≤ program.length :=
  List.length_filterMap_le _ _

/-! ## 3. The finite coverage, from the window-count bound -/

/-- The union of a list of windows. -/
def fmul7WindowUnion (windows : List (Finset (Fin 32))) : Finset (Fin 32) :=
  windows.foldr (· ∪ ·) ∅

theorem fmul7WindowUnion_cons (head : Finset (Fin 32)) (rest : List (Finset (Fin 32))) :
    fmul7WindowUnion (head :: rest) = head ∪ fmul7WindowUnion rest := rfl

theorem fmul7WindowUnion_mem {windows : List (Finset (Fin 32))} {window : Finset (Fin 32)}
    (member : window ∈ windows) {index : Fin 32} (inside : index ∈ window) :
    index ∈ fmul7WindowUnion windows := by
  induction windows with
  | nil => simp at member
  | cons head rest ih =>
      simp only [fmul7WindowUnion, List.foldr_cons]
      rcases List.mem_cons.mp member with headEq | tail
      · subst headEq
        exact Finset.mem_union_left _ inside
      · exact Finset.mem_union_right _ (ih tail)

theorem fmul7WindowUnion_card_le (windows : List (Finset (Fin 32)))
    (sizes : ∀ window ∈ windows, window.card ≤ 8) :
    (fmul7WindowUnion windows).card ≤ 8 * windows.length := by
  induction windows with
  | nil => simp [fmul7WindowUnion]
  | cons head rest ih =>
      have headCard := sizes head (by simp)
      have restSizes : ∀ window ∈ rest, window.card ≤ 8 :=
        fun window member => sizes window (List.mem_cons_of_mem _ member)
      have restCard := ih restSizes
      have unionCard := Finset.card_union_le head (fmul7WindowUnion rest)
      rw [fmul7WindowUnion_cons, List.length_cons]
      omega

theorem fmul7ProductWindows_length_lt {program : List InstructionLine}
    (notAll : ¬ ∀ line ∈ program, Fmul7ProductLine line) :
    (fmul7ProductWindows program).length < program.length := by
  induction program with
  | nil => exact False.elim (notAll (by simp))
  | cons head rest ih =>
      rw [fmul7ProductWindows_cons]
      cases mapped : Option.map fmul7Window (fmul7ProductSlot? head) with
      | none =>
          have le := fmul7ProductWindows_length_le rest
          simp only [List.length_cons]
          omega
      | some found =>
          have headProduct : Fmul7ProductLine head := by
            apply (fmul7ProductSlot?_isSome_iff head).mp
            cases slotEq : fmul7ProductSlot? head with
            | none => rw [slotEq] at mapped; simp at mapped
            | some slot => simp [slotEq]
          have notAllTail : ¬ ∀ line ∈ rest, Fmul7ProductLine line := by
            intro all
            apply notAll
            intro line member
            rcases List.mem_cons.mp member with headEq | tail
            · subst headEq
              exact headProduct
            · exact all line tail
          have tailShort := ih notAllTail
          simp only [List.length_cons]
          omega

/-- Every window in the product-window list has eight words. -/
theorem fmul7ProductWindows_card_le (program : List InstructionLine) :
    ∀ window ∈ fmul7ProductWindows program, window.card ≤ 8 := by
  induction program with
  | nil => simp [fmul7ProductWindows]
  | cons head rest ih =>
      rw [fmul7ProductWindows_cons]
      cases mapped : Option.map fmul7Window (fmul7ProductSlot? head) with
      | none =>
          exact ih
      | some found =>
          intro window member
          rcases List.mem_cons.mp member with headEq | tail
          · subst headEq
            cases slotEq : fmul7ProductSlot? head with
            | none => rw [slotEq] at mapped; simp at mapped
            | some slot =>
                rw [slotEq] at mapped
                simp only [Option.map_some, Option.some.injEq] at mapped
                subst mapped
                exact le_of_eq (fmul7Window_card slot)
          · exact ih window tail

/-- **The finite coverage obligation, from the window-count bound.** -/
theorem fmul7ShapeCoverage_of_windows (program : List InstructionLine)
    (windowsBound : (fmul7ProductWindows program).length ≤ 3) :
    Fmul7ShapeCoverage program := by
  left
  have sizes := fmul7ProductWindows_card_le program
  have unionCard := fmul7WindowUnion_card_le (fmul7ProductWindows program) sizes
  have universeCard : (Finset.univ : Finset (Fin 32)).card = 32 := by decide
  have small : (fmul7WindowUnion (fmul7ProductWindows program)).card <
      (Finset.univ : Finset (Fin 32)).card := by
    omega
  obtain ⟨index, _, outside⟩ := Finset.exists_mem_notMem_of_card_lt_card small
  refine ⟨index, ?_⟩
  intro line member slot product inside
  have windowMember : fmul7Window slot ∈ fmul7ProductWindows program :=
    fmul7ProductWindows_mem member product
  exact outside (fmul7WindowUnion_mem windowMember inside)

/-- **The finite coverage obligation is closed.**  A shape program of length at
most four either is all products, or has one output word outside every product
window. -/
theorem fmul7ShapeCoverage (program : List InstructionLine) (short : program.length ≤ 4) :
    Fmul7ShapeCoverage program := by
  by_cases allProducts : ∀ line ∈ program, Fmul7ProductLine line
  · exact Or.inr allProducts
  · apply fmul7ShapeCoverage_of_windows
    have strict := fmul7ProductWindows_length_lt allProducts
    omega

/-- **The shape lower bound with the coverage residual discharged.**  Only the
per-line `Fmul7LineShapeResidual` remains. -/
theorem fmul7_shape_score_five_of_residual
    (residual : Fmul7LineShapeResidual)
    (program : List InstructionLine)
    (shape : ∀ line ∈ program, Fmul7ShapeLine line)
    (correct : ProofsLean.Correct fmul7SealedMachine fmul7Spec program) :
    5 ≤ ProofsLean.score fmul7SealedMachine program :=
  fmul7_shape_score_five residual
    (fun program short _shape => fmul7ShapeCoverage program short)
    program shape correct

/-! ## 4. The imm line's `$t` write list -/

def tAccess : Access := ⟨.t, fmul7LongRegion 0⟩
def tResolved (cycle : Fin 4) : DirectMemoryAccess :=
  ⟨.t, .long, ⟨cycle.val * 4, by have := cycle.isLt; change cycle.val * 4 < 16; omega⟩⟩

def tImmAccesses (cycle : Fin 4) : ParsedMaskedIntegerAccesses where
  op := .immediate 0x40E00000 false
  sourceX := .memory (tResolved cycle) false
  sourceY := .memory (tResolved cycle) false
  destination := tResolved cycle
  writeSelection := ⟨BitVec.allOnes 4, true⟩
  flushSelection := none
  hasRequest := ⟨.immediate 0x40E00000 false, rfl⟩

def tImmTargets (cycle : Fin 4) : List ParsedConstantDestination :=
  [.memory (tImmAccesses cycle)]

theorem tDestination (cycle : Fin 4) :
    ParsedOperand.toDirectMemoryDestination? (.mem tAccess false false false none)
      (0 : Fin 4) cycle 0 0 0 = some (tResolved cycle) := by
  simp [ParsedOperand.toDirectMemoryDestination?, ParsedOperand.toDirectMemoryAccessMode?,
    tAccess, tResolved, fmul7LongRegion, parsedWidth?, parsedRegionAddressAt,
    issueBankToRegisterBank]

theorem tSelection (input : Fmul7Input) (cycle : Fin 4) :
    ParsedOperand.resolveMemoryWriteSelection? (.mem tAccess false false false none) .t
      ((fmul7InitialState input).peRegisters 0).maskRegisters cycle
      (fmul7InitialState input).maskDirective false = some ⟨BitVec.allOnes 4, true⟩ := by
  simp [ParsedOperand.resolveMemoryWriteSelection?, resolveMemoryDirectiveSelection?,
    fmul7InitialState, rustSimulatorInitialState]

theorem fmul7Imm_lowered (input : Fmul7Input) (cycle : Fin 4) :
    ParsedExpr.toDirectMaskedConstantWrites? fmul7ImmExpr.toParsed
      ((fmul7InitialState input).peRegisters 0).maskRegisters
      (fmul7InitialState input).maskDirective false 0 0 0 0 0 cycle 0 0 0 =
      some (tImmTargets cycle) := by
  have h := toDirectMaskedConstantWrites?_immediate_single 0x40E00000 false none ""
    tAccess false false false none _ _ false 0 0 0 0 0 cycle 0 0 0
    (tResolved cycle) ⟨BitVec.allOnes 4, true⟩ none
    (tDestination cycle) (tSelection input cycle) rfl
  simpa [NormalizedExpr.toParsed, fmul7ImmExpr, fmul7TLong, tAccess, tImmTargets, tImmAccesses] using h

end ProofsLean.MNCore

namespace ProofsLean.MNCore
open Issue PEMemory

def tImmWrite (cycle : Fin 4) : PreparedParsedMaskedWrite where
  destination := some (tResolved cycle)
  maskUpdate := none
  data := fun _ => 0x40E00000
  selection := ⟨BitVec.allOnes 4, true⟩

theorem fmul7Imm_prepared (input : Fmul7Input) (cycle : Fin 4) :
    prepareParsedMaskedConstantWrites ((fmul7InitialState input).peRegisters 0) cycle
        (tImmTargets cycle) = .ok [tImmWrite cycle] := by
  simp only [tImmTargets, tImmAccesses, tImmWrite, tResolved,
    prepareParsedMaskedConstantWrites, prepareParsedConstantTarget,
    prepareParsedMaskedWrite, ParsedIntegerInput.read,
    evaluateParsedIntegerAlu, ParsedOp.executionRequest, evaluateParsedExecutionRequest,
    parsedOutputAfterFlush, Bool.false_eq_true, ite_false]
  rw [unpackALUBus_self]

end ProofsLean.MNCore

namespace ProofsLean.MNCore
open Issue PEMemory

def fmul7Control (input : Fmul7Input) : ParsedMaskExecutionControl where
  directive := (fmul7InitialState input).maskDirective
  context := { (ParsedIntegerContext.ofLinearIndex 0) with
    bar0 := ((fmul7InitialState input).peContext 0).bar0
    bar1 := ((fmul7InitialState input).peContext 0).bar1
    tWord := ((fmul7InitialState input).peContext 0).tWord }
  elapsedWords := (fmul7InitialState input).hazardClock

def fmul7ImmALUWrite : PreparedParsedMaskedWrite :=
  immediateALUWrite 0x40E00000 false false none

theorem fmul7Imm_aluCycles (input : Fmul7Input) :
    prepareParsedIntegerALUExprCycles ((fmul7InitialState input).peRegisters 0)
        (stateForwardingSlots (fmul7InitialState input) 0)
        (stateForwardingSlots (fmul7InitialState input) 0)
        fmul7ImmExpr.toParsed (fmul7Control input) false false false =
      .ok ([tImmWrite 0] ++ [fmul7ImmALUWrite] ++ [tImmWrite 1] ++ [fmul7ImmALUWrite] ++
        [tImmWrite 2] ++ [fmul7ImmALUWrite] ++ [tImmWrite 3] ++ [fmul7ImmALUWrite],
        immediateALUSlots (stateForwardingSlots (fmul7InitialState input) 0)
          0x40E00000 false false (fun _ => none)) := by
  let files := (fmul7InitialState input).peRegisters 0
  let oldSlots := stateForwardingSlots (fmul7InitialState input) 0
  let expression := fmul7ImmExpr.toParsed
  let control := fmul7Control input
  let s0 : ProofsLean.MNCore.Forwarding.Slots := oldSlots
  let s1 : ProofsLean.MNCore.Forwarding.Slots := fun unit cycle =>
    if unit = ProofsLean.MNCore.Forwarding.Unit.alu ∧ cycle = (0 : Fin 4) then
      .known (pack fmul7ImmALUWrite.data)
    else s0 unit cycle
  let s2 : ProofsLean.MNCore.Forwarding.Slots := fun unit cycle =>
    if unit = ProofsLean.MNCore.Forwarding.Unit.alu ∧ cycle = (1 : Fin 4) then
      .known (pack fmul7ImmALUWrite.data)
    else s1 unit cycle
  let s3 : ProofsLean.MNCore.Forwarding.Slots := fun unit cycle =>
    if unit = ProofsLean.MNCore.Forwarding.Unit.alu ∧ cycle = (2 : Fin 4) then
      .known (pack fmul7ImmALUWrite.data)
    else s2 unit cycle
  let s4 : ProofsLean.MNCore.Forwarding.Slots := fun unit cycle =>
    if unit = ProofsLean.MNCore.Forwarding.Unit.alu ∧ cycle = (3 : Fin 4) then
      .known (pack fmul7ImmALUWrite.data)
    else s3 unit cycle
  have isImmediate : expression.op = .immediate 0x40E00000 false := rfl
  have lowered : ∀ cycle, ParsedExpr.toDirectMaskedConstantWrites? expression
      files.maskRegisters control.directive false control.context.group control.context.l2b
      control.context.l1b control.context.mab control.context.pe cycle control.context.bar0
      control.context.bar1 control.context.tWord = some (tImmTargets cycle) := by
    intro cycle
    exact fmul7Imm_lowered input cycle
  have prepared : ∀ cycle, prepareParsedMaskedConstantWrites files cycle (tImmTargets cycle)
      = .ok [tImmWrite cycle] := fun cycle => fmul7Imm_prepared input cycle
  have flushResolved : ∀ cycle, resolveFlushSelection? expression.flush files.maskRegisters
      cycle = some (none : Option PEWordSelection) := by
    intro cycle
    rfl
  have updated : ∀ (cycle : Fin 4) (next : ProofsLean.MNCore.Forwarding.Slots),
      updateParsedIntegerALUForwardingCycle next cycle
        (.ok fmul7ImmALUWrite) false =
        .ok (fun unit slotCycle =>
          if unit = ProofsLean.MNCore.Forwarding.Unit.alu ∧ slotCycle = cycle then
            .known (pack fmul7ImmALUWrite.data)
          else next unit slotCycle) := by
    intro cycle next
    exact updateParsedIntegerALUForwardingCycle_immediate next cycle 0x40E00000 false false none
  have step0 : prepareParsedIntegerALUExprCycle files oldSlots s0 expression control
      false false false 0 = .ok ([tImmWrite 0] ++ [fmul7ImmALUWrite], s1) :=
    prepareParsedIntegerALUExprCycle_immediate files oldSlots s0 expression control
      false false false 0 (tImmTargets 0) [tImmWrite 0] none s1 0x40E00000 false
      isImmediate (lowered 0) (prepared 0) (flushResolved 0) (updated 0 s0)
  have step1 : prepareParsedIntegerALUExprCycle files oldSlots s1 expression control
      false false false 1 = .ok ([tImmWrite 1] ++ [fmul7ImmALUWrite], s2) :=
    prepareParsedIntegerALUExprCycle_immediate files oldSlots s1 expression control
      false false false 1 (tImmTargets 1) [tImmWrite 1] none s2 0x40E00000 false
      isImmediate (lowered 1) (prepared 1) (flushResolved 1) (updated 1 s1)
  have step2 : prepareParsedIntegerALUExprCycle files oldSlots s2 expression control
      false false false 2 = .ok ([tImmWrite 2] ++ [fmul7ImmALUWrite], s3) :=
    prepareParsedIntegerALUExprCycle_immediate files oldSlots s2 expression control
      false false false 2 (tImmTargets 2) [tImmWrite 2] none s3 0x40E00000 false
      isImmediate (lowered 2) (prepared 2) (flushResolved 2) (updated 2 s2)
  have step3 : prepareParsedIntegerALUExprCycle files oldSlots s3 expression control
      false false false 3 = .ok ([tImmWrite 3] ++ [fmul7ImmALUWrite], s4) :=
    prepareParsedIntegerALUExprCycle_immediate files oldSlots s3 expression control
      false false false 3 (tImmTargets 3) [tImmWrite 3] none s4 0x40E00000 false
      isImmediate (lowered 3) (prepared 3) (flushResolved 3) (updated 3 s3)
  unfold prepareParsedIntegerALUExprCycles
  simp only [parsedIntegerALUCycles]
  rw [prepareParsedIntegerALUCycles.eq_2, step0]
  dsimp only
  rw [List.nil_append]
  rw [prepareParsedIntegerALUCycles.eq_2, step1]
  dsimp only
  rw [prepareParsedIntegerALUCycles.eq_2, step2]
  dsimp only
  rw [prepareParsedIntegerALUCycles.eq_2, step3]
  dsimp only
  rw [prepareParsedIntegerALUCycles.eq_1]
  simp only [StepResult.ok.injEq]
  refine Prod.ext rfl ?_
  funext unit cycle
  have hsmall : cycle.val = 0 ∨ cycle.val = 1 ∨ cycle.val = 2 ∨ cycle.val = 3 := by
    have := cycle.isLt; omega
  rcases hsmall with h | h | h | h
  · rw [show cycle = 0 from Fin.ext (by simpa using h)]
    cases unit <;> simp [s0, s1, s2, s3, s4, immediateALUSlots, fmul7ImmALUWrite, oldSlots]
  · rw [show cycle = 1 from Fin.ext (by simpa using h)]
    cases unit <;> simp [s0, s1, s2, s3, s4, immediateALUSlots, fmul7ImmALUWrite, oldSlots]
  · rw [show cycle = 2 from Fin.ext (by simpa using h)]
    cases unit <;> simp [s0, s1, s2, s3, s4, immediateALUSlots, fmul7ImmALUWrite, oldSlots]
  · rw [show cycle = 3 from Fin.ext (by simpa using h)]
    cases unit <;> simp [s0, s1, s2, s3, s4, immediateALUSlots, fmul7ImmALUWrite, oldSlots]

end ProofsLean.MNCore

namespace ProofsLean.MNCore
open Issue PEMemory



/-- The imm line is locally issue-legal. -/
theorem fmul7Imm_legal : LegalParsedLine [fmul7ImmExpr.toParsed] := by
  unfold LegalParsedLine projectLine projectFrom ParsedExpr.toIssueExpr
    ParsedExpr.issueGroup ParsedExpr.issueMau ParsedOperand.accesses
    ParsedOperand.matrixUseCount ParsedExpr.hasTurnaround
    ParsedExpr.maskApplications ParsedOperand.writeMask?
    ParsedExpr.maskRegisterWrites ParsedOperand.maskRegisterWrite?
    ParsedExpr.barWrites ParsedOperand.barWriteBank?
    ParsedExpr.writesLbf ParsedExpr.nowriteOutputValid
  simp [fmul7ImmExpr, fmul7TLong, fmul7LongRegion, Legal, idsUnique, groupsUnique,
    mauCountBounded, mauExpressions, mauPrecisionsAgree, matrixWritePairAgrees,
    matrixRegistersUnique, writesUnique, Expr.writeBanks, barWritesExcludeReads, readsAgree,
    localReadWriteAgree, immediateExcludesLm0, zeroFlushUnique, maskWidthsAgree,
    maskEntriesAgree, nowriteOutputsUnique, lbfWritesUnique, maskRegisterWritesUnique,
    projectFrom, NormalizedExpr.toParsed]

theorem fmul7Imm_accepted :
    checkParsedTopLine (InstructionLine.pe [fmul7ImmExpr]).toParsed = true := by
  have accepted := parsed_topline_check_complete
    (ParsedLine.pe [fmul7ImmExpr.toParsed]) fmul7Imm_legal
  simpa [InstructionLine.toParsed] using accepted


/-! ## 5. Arbitrary-PE versions for the 4096-PE walk -/

/-- The mask execution control at an arbitrary PE. -/
def fmul7ControlAt (input : Fmul7Input) (pe : PEId) : ParsedMaskExecutionControl where
  directive := (fmul7InitialState input).maskDirective
  context := { (ParsedIntegerContext.ofLinearIndex pe) with
    bar0 := ((fmul7InitialState input).peContext pe).bar0
    bar1 := ((fmul7InitialState input).peContext pe).bar1
    tWord := ((fmul7InitialState input).peContext pe).tWord }
  elapsedWords := (fmul7InitialState input).hazardClock

theorem tDestinationAt (subPE : Fin 4) (cycle : Fin 4) :
    ParsedOperand.toDirectMemoryDestination? (.mem tAccess false false false none)
      subPE cycle 0 0 0 = some (tResolved cycle) := by
  simp [ParsedOperand.toDirectMemoryDestination?, ParsedOperand.toDirectMemoryAccessMode?,
    tAccess, tResolved, fmul7LongRegion, parsedWidth?, issueBankToRegisterBank]

theorem tSelectionAt (input : Fmul7Input) (pe : PEId) (cycle : Fin 4) :
    ParsedOperand.resolveMemoryWriteSelection? (.mem tAccess false false false none) .t
      ((fmul7InitialState input).peRegisters pe).maskRegisters cycle
      (fmul7InitialState input).maskDirective false = some ⟨BitVec.allOnes 4, true⟩ := by
  simp [ParsedOperand.resolveMemoryWriteSelection?, resolveMemoryDirectiveSelection?,
    fmul7InitialState, rustSimulatorInitialState]

theorem fmul7Imm_lowered_any (input : Fmul7Input) (pe : PEId) (cycle : Fin 4) :
    ParsedExpr.toDirectMaskedConstantWrites? fmul7ImmExpr.toParsed
      ((fmul7InitialState input).peRegisters pe).maskRegisters
      (fmul7InitialState input).maskDirective false 0 0 0 0 0 cycle 0 0 0 =
      some (tImmTargets cycle) := by
  have h := toDirectMaskedConstantWrites?_immediate_single 0x40E00000 false none ""
    tAccess false false false none _ _ false 0 0 0 0 0 cycle 0 0 0
    (tResolved cycle) ⟨BitVec.allOnes 4, true⟩ none
    (tDestinationAt (ParsedIntegerContext.ofLinearIndex pe).pe cycle)
    (tSelectionAt input pe cycle) rfl
  simpa [NormalizedExpr.toParsed, fmul7ImmExpr, fmul7TLong, tAccess, tImmTargets, tImmAccesses]
    using h

theorem fmul7Imm_prepared_any (files : IntegerRegisterFiles) (cycle : Fin 4) :
    prepareParsedMaskedConstantWrites files cycle (tImmTargets cycle) =
      .ok [tImmWrite cycle] := by
  simp only [tImmTargets, tImmAccesses, tImmWrite, tResolved,
    prepareParsedMaskedConstantWrites, prepareParsedConstantTarget,
    prepareParsedMaskedWrite, ParsedIntegerInput.read,
    evaluateParsedIntegerAlu, ParsedOp.executionRequest, evaluateParsedExecutionRequest,
    parsedOutputAfterFlush, Bool.false_eq_true, ite_false]
  rw [unpackALUBus_self]

theorem fmul7Imm_aluCycles_any (input : Fmul7Input) (pe : PEId) :
    prepareParsedIntegerALUExprCycles ((fmul7InitialState input).peRegisters pe)
        (stateForwardingSlots (fmul7InitialState input) pe)
        (stateForwardingSlots (fmul7InitialState input) pe)
        fmul7ImmExpr.toParsed (fmul7ControlAt input pe) false false false =
      .ok ([tImmWrite 0] ++ [fmul7ImmALUWrite] ++ [tImmWrite 1] ++ [fmul7ImmALUWrite] ++
        [tImmWrite 2] ++ [fmul7ImmALUWrite] ++ [tImmWrite 3] ++ [fmul7ImmALUWrite],
        immediateALUSlots (stateForwardingSlots (fmul7InitialState input) pe)
          0x40E00000 false false (fun _ => none)) := by
  let files := (fmul7InitialState input).peRegisters pe
  let oldSlots := stateForwardingSlots (fmul7InitialState input) pe
  let expression := fmul7ImmExpr.toParsed
  let control := fmul7ControlAt input pe
  let s0 : ProofsLean.MNCore.Forwarding.Slots := oldSlots
  let s1 : ProofsLean.MNCore.Forwarding.Slots := fun unit cycle =>
    if unit = ProofsLean.MNCore.Forwarding.Unit.alu ∧ cycle = (0 : Fin 4) then
      .known (pack fmul7ImmALUWrite.data)
    else s0 unit cycle
  let s2 : ProofsLean.MNCore.Forwarding.Slots := fun unit cycle =>
    if unit = ProofsLean.MNCore.Forwarding.Unit.alu ∧ cycle = (1 : Fin 4) then
      .known (pack fmul7ImmALUWrite.data)
    else s1 unit cycle
  let s3 : ProofsLean.MNCore.Forwarding.Slots := fun unit cycle =>
    if unit = ProofsLean.MNCore.Forwarding.Unit.alu ∧ cycle = (2 : Fin 4) then
      .known (pack fmul7ImmALUWrite.data)
    else s2 unit cycle
  let s4 : ProofsLean.MNCore.Forwarding.Slots := fun unit cycle =>
    if unit = ProofsLean.MNCore.Forwarding.Unit.alu ∧ cycle = (3 : Fin 4) then
      .known (pack fmul7ImmALUWrite.data)
    else s3 unit cycle
  have isImmediate : expression.op = .immediate 0x40E00000 false := rfl
  have lowered : ∀ cycle, ParsedExpr.toDirectMaskedConstantWrites? expression
      files.maskRegisters control.directive false control.context.group control.context.l2b
      control.context.l1b control.context.mab control.context.pe cycle control.context.bar0
      control.context.bar1 control.context.tWord = some (tImmTargets cycle) := by
    intro cycle
    exact fmul7Imm_lowered_any input pe cycle
  have prepared : ∀ cycle, prepareParsedMaskedConstantWrites files cycle (tImmTargets cycle)
      = .ok [tImmWrite cycle] := fun cycle => fmul7Imm_prepared_any ((fmul7InitialState input).peRegisters pe) cycle
  have flushResolved : ∀ cycle, resolveFlushSelection? expression.flush files.maskRegisters
      cycle = some (none : Option PEWordSelection) := by
    intro cycle
    rfl
  have updated : ∀ (cycle : Fin 4) (next : ProofsLean.MNCore.Forwarding.Slots),
      updateParsedIntegerALUForwardingCycle next cycle
        (.ok fmul7ImmALUWrite) false =
        .ok (fun unit slotCycle =>
          if unit = ProofsLean.MNCore.Forwarding.Unit.alu ∧ slotCycle = cycle then
            .known (pack fmul7ImmALUWrite.data)
          else next unit slotCycle) := by
    intro cycle next
    exact updateParsedIntegerALUForwardingCycle_immediate next cycle 0x40E00000 false false none
  have step0 : prepareParsedIntegerALUExprCycle files oldSlots s0 expression control
      false false false 0 = .ok ([tImmWrite 0] ++ [fmul7ImmALUWrite], s1) :=
    prepareParsedIntegerALUExprCycle_immediate files oldSlots s0 expression control
      false false false 0 (tImmTargets 0) [tImmWrite 0] none s1 0x40E00000 false
      isImmediate (lowered 0) (prepared 0) (flushResolved 0) (updated 0 s0)
  have step1 : prepareParsedIntegerALUExprCycle files oldSlots s1 expression control
      false false false 1 = .ok ([tImmWrite 1] ++ [fmul7ImmALUWrite], s2) :=
    prepareParsedIntegerALUExprCycle_immediate files oldSlots s1 expression control
      false false false 1 (tImmTargets 1) [tImmWrite 1] none s2 0x40E00000 false
      isImmediate (lowered 1) (prepared 1) (flushResolved 1) (updated 1 s1)
  have step2 : prepareParsedIntegerALUExprCycle files oldSlots s2 expression control
      false false false 2 = .ok ([tImmWrite 2] ++ [fmul7ImmALUWrite], s3) :=
    prepareParsedIntegerALUExprCycle_immediate files oldSlots s2 expression control
      false false false 2 (tImmTargets 2) [tImmWrite 2] none s3 0x40E00000 false
      isImmediate (lowered 2) (prepared 2) (flushResolved 2) (updated 2 s2)
  have step3 : prepareParsedIntegerALUExprCycle files oldSlots s3 expression control
      false false false 3 = .ok ([tImmWrite 3] ++ [fmul7ImmALUWrite], s4) :=
    prepareParsedIntegerALUExprCycle_immediate files oldSlots s3 expression control
      false false false 3 (tImmTargets 3) [tImmWrite 3] none s4 0x40E00000 false
      isImmediate (lowered 3) (prepared 3) (flushResolved 3) (updated 3 s3)
  unfold prepareParsedIntegerALUExprCycles
  simp only [parsedIntegerALUCycles]
  rw [prepareParsedIntegerALUCycles.eq_2, step0]
  dsimp only
  rw [List.nil_append]
  rw [prepareParsedIntegerALUCycles.eq_2, step1]
  dsimp only
  rw [prepareParsedIntegerALUCycles.eq_2, step2]
  dsimp only
  rw [prepareParsedIntegerALUCycles.eq_2, step3]
  dsimp only
  rw [prepareParsedIntegerALUCycles.eq_1]
  simp only [StepResult.ok.injEq]
  refine Prod.ext rfl ?_
  funext unit cycle
  have hsmall : cycle.val = 0 ∨ cycle.val = 1 ∨ cycle.val = 2 ∨ cycle.val = 3 := by
    have := cycle.isLt; omega
  rcases hsmall with h | h | h | h
  · rw [show cycle = 0 from Fin.ext (by simpa using h)]
    cases unit <;> simp [s0, s1, s2, s3, s4, immediateALUSlots, fmul7ImmALUWrite, oldSlots]
  · rw [show cycle = 1 from Fin.ext (by simpa using h)]
    cases unit <;> simp [s0, s1, s2, s3, s4, immediateALUSlots, fmul7ImmALUWrite, oldSlots]
  · rw [show cycle = 2 from Fin.ext (by simpa using h)]
    cases unit <;> simp [s0, s1, s2, s3, s4, immediateALUSlots, fmul7ImmALUWrite, oldSlots]
  · rw [show cycle = 3 from Fin.ext (by simpa using h)]
    cases unit <;> simp [s0, s1, s2, s3, s4, immediateALUSlots, fmul7ImmALUWrite, oldSlots]

end ProofsLean.MNCore

namespace ProofsLean.MNCore
open Issue PEMemory





/-! ## 5b. The imm row, line cycles, and per-PE core -/

def fmul7ImmWrites : List PreparedParsedMaskedWrite :=
  [tImmWrite 0] ++ [fmul7ImmALUWrite] ++ [tImmWrite 1] ++ [fmul7ImmALUWrite] ++
    [tImmWrite 2] ++ [fmul7ImmALUWrite] ++ [tImmWrite 3] ++ [fmul7ImmALUWrite]

theorem fmul7Imm_op : fmul7ImmExpr.toParsed.op = .immediate 0x40E00000 false := rfl

theorem fmul7Imm_hasNoMask :
    parsedExprHasSingleLineWriteMask fmul7ImmExpr.toParsed = false := by
  decide

theorem fmul7Imm_noMask :
    ([fmul7ImmExpr.toParsed].any parsedExprHasSingleLineWriteMask) = false := by
  rw [List.any_cons, fmul7Imm_hasNoMask]
  simp

theorem fmul7Imm_stageInput :
    parsedExprIsIntegerMatrixReadStageInput fmul7ImmExpr.toParsed = true := by
  decide

theorem fmul7Imm_lineExecRow :
    parsedExprIsLineExecRow fmul7ImmExpr.toParsed = true := by
  decide

theorem fmul7Imm_notFloat :
    parsedExprIsSupportedFloatMAUProducer fmul7ImmExpr.toParsed = false := by
  decide

theorem fmul7Imm_rowExpression (input : Fmul7Input) (pe : PEId)
    (store : ParsedMatrixReadStore) :
    prepareParsedIntegerMatrixReadLineExpression ((fmul7InitialState input).peRegisters pe)
        (stateForwardingSlots (fmul7InitialState input) pe)
        (stateForwardingSlots (fmul7InitialState input) pe) store
        fmul7ImmExpr.toParsed (fmul7ControlAt input pe) false false false =
      .ok (fmul7ImmWrites,
        immediateALUSlots (stateForwardingSlots (fmul7InitialState input) pe)
          0x40E00000 false false (fun _ => none), []) := by
  unfold prepareParsedIntegerMatrixReadLineExpression
  rw [fmul7Imm_op]
  dsimp only
  rw [fmul7Imm_aluCycles_any input pe]
  dsimp only
  simp only [parsedIntegerALUBarUpdates, fmul7ImmExpr, ParsedExpr.normalize,
    NormalizedExpr.toParsed, fmul7TLong, fmul7ImmWrites]

theorem fmul7Imm_lineCycles_any (input : Fmul7Input) (pe : PEId)
    (store : ParsedMatrixReadStore) :
    prepareParsedIntegerMatrixReadLineCycles ((fmul7InitialState input).peRegisters pe)
        (stateForwardingSlots (fmul7InitialState input) pe) store
        [fmul7ImmExpr.toParsed] (fmul7ControlAt input pe) false =
      .ok (fmul7ImmWrites,
        immediateALUSlots (stateForwardingSlots (fmul7InitialState input) pe)
          0x40E00000 false false (fun _ => none), []) := by
  unfold prepareParsedIntegerMatrixReadLineCycles
  dsimp only
  simp only [fmul7Imm_noMask]
  refine prepareParsedIntegerMatrixReadLineExpressions_singleton
    ((fmul7InitialState input).peRegisters pe)
    (stateForwardingSlots (fmul7InitialState input) pe) store
    fmul7ImmExpr.toParsed (fmul7ControlAt input pe) false false false fmul7ImmWrites
    (immediateALUSlots (stateForwardingSlots (fmul7InitialState input) pe)
      0x40E00000 false false (fun _ => none)) [] ?_
  exact fmul7Imm_rowExpression input pe store


/-- The `.t` write selection is the all-ones selection for the default directive
and the zero mask-register file. -/
theorem tSelectionGeneral (files : IntegerRegisterFiles)
    (control : ParsedMaskExecutionControl)
    (directiveEq : control.directive = rustSimulatorInitialState.maskDirective)
    (registersEq : files.maskRegisters = zeroInitialPERegisterFiles.maskRegisters)
    (cycle : Fin 4) :
    ParsedOperand.resolveMemoryWriteSelection? (.mem tAccess false false false none) .t
      files.maskRegisters cycle control.directive false = some ⟨BitVec.allOnes 4, true⟩ := by
  rw [registersEq, directiveEq]
  simp [ParsedOperand.resolveMemoryWriteSelection?, resolveMemoryDirectiveSelection?,
    rustSimulatorInitialState, zeroInitialPERegisterFiles]

theorem fmul7Imm_lowered_general (files : IntegerRegisterFiles)
    (control : ParsedMaskExecutionControl)
    (directiveEq : control.directive = rustSimulatorInitialState.maskDirective)
    (registersEq : files.maskRegisters = zeroInitialPERegisterFiles.maskRegisters)
    (cycle : Fin 4) :
    ParsedExpr.toDirectMaskedConstantWrites? fmul7ImmExpr.toParsed
      files.maskRegisters control.directive false 0 0 0 0 0 cycle 0 0 0 =
      some (tImmTargets cycle) := by
  have h := toDirectMaskedConstantWrites?_immediate_single 0x40E00000 false none ""
    tAccess false false false none _ _ false 0 0 0 0 0 cycle 0 0 0
    (tResolved cycle) ⟨BitVec.allOnes 4, true⟩ none
    (tDestinationAt 0 cycle) (tSelectionGeneral files control directiveEq registersEq cycle) rfl
  simpa [NormalizedExpr.toParsed, fmul7ImmExpr, fmul7TLong, tAccess, tImmTargets, tImmAccesses]
    using h

theorem fmul7Imm_aluCycles_general (files : IntegerRegisterFiles)
    (oldSlots : ProofsLean.MNCore.Forwarding.Slots)
    (control : ParsedMaskExecutionControl)
    (directiveEq : control.directive = rustSimulatorInitialState.maskDirective)
    (registersEq : files.maskRegisters = zeroInitialPERegisterFiles.maskRegisters) :
    prepareParsedIntegerALUExprCycles files oldSlots oldSlots
        fmul7ImmExpr.toParsed control false false false =
      .ok ([tImmWrite 0] ++ [fmul7ImmALUWrite] ++ [tImmWrite 1] ++ [fmul7ImmALUWrite] ++
        [tImmWrite 2] ++ [fmul7ImmALUWrite] ++ [tImmWrite 3] ++ [fmul7ImmALUWrite],
        immediateALUSlots oldSlots
          0x40E00000 false false (fun _ => none)) := by
  let expression := fmul7ImmExpr.toParsed
  let s0 : ProofsLean.MNCore.Forwarding.Slots := oldSlots
  let s1 : ProofsLean.MNCore.Forwarding.Slots := fun unit cycle =>
    if unit = ProofsLean.MNCore.Forwarding.Unit.alu ∧ cycle = (0 : Fin 4) then
      .known (pack fmul7ImmALUWrite.data)
    else s0 unit cycle
  let s2 : ProofsLean.MNCore.Forwarding.Slots := fun unit cycle =>
    if unit = ProofsLean.MNCore.Forwarding.Unit.alu ∧ cycle = (1 : Fin 4) then
      .known (pack fmul7ImmALUWrite.data)
    else s1 unit cycle
  let s3 : ProofsLean.MNCore.Forwarding.Slots := fun unit cycle =>
    if unit = ProofsLean.MNCore.Forwarding.Unit.alu ∧ cycle = (2 : Fin 4) then
      .known (pack fmul7ImmALUWrite.data)
    else s2 unit cycle
  let s4 : ProofsLean.MNCore.Forwarding.Slots := fun unit cycle =>
    if unit = ProofsLean.MNCore.Forwarding.Unit.alu ∧ cycle = (3 : Fin 4) then
      .known (pack fmul7ImmALUWrite.data)
    else s3 unit cycle
  have isImmediate : expression.op = .immediate 0x40E00000 false := rfl
  have lowered : ∀ cycle, ParsedExpr.toDirectMaskedConstantWrites? expression
      files.maskRegisters control.directive false control.context.group control.context.l2b
      control.context.l1b control.context.mab control.context.pe cycle control.context.bar0
      control.context.bar1 control.context.tWord = some (tImmTargets cycle) := by
    intro cycle
    exact fmul7Imm_lowered_general files control directiveEq registersEq cycle
  have prepared : ∀ cycle, prepareParsedMaskedConstantWrites files cycle (tImmTargets cycle)
      = .ok [tImmWrite cycle] := fun cycle => fmul7Imm_prepared_any files cycle
  have flushResolved : ∀ cycle, resolveFlushSelection? expression.flush files.maskRegisters
      cycle = some (none : Option PEWordSelection) := by
    intro cycle
    rfl
  have updated : ∀ (cycle : Fin 4) (next : ProofsLean.MNCore.Forwarding.Slots),
      updateParsedIntegerALUForwardingCycle next cycle
        (.ok fmul7ImmALUWrite) false =
        .ok (fun unit slotCycle =>
          if unit = ProofsLean.MNCore.Forwarding.Unit.alu ∧ slotCycle = cycle then
            .known (pack fmul7ImmALUWrite.data)
          else next unit slotCycle) := by
    intro cycle next
    exact updateParsedIntegerALUForwardingCycle_immediate next cycle 0x40E00000 false false none
  have step0 : prepareParsedIntegerALUExprCycle files oldSlots s0 expression control
      false false false 0 = .ok ([tImmWrite 0] ++ [fmul7ImmALUWrite], s1) :=
    prepareParsedIntegerALUExprCycle_immediate files oldSlots s0 expression control
      false false false 0 (tImmTargets 0) [tImmWrite 0] none s1 0x40E00000 false
      isImmediate (lowered 0) (prepared 0) (flushResolved 0) (updated 0 s0)
  have step1 : prepareParsedIntegerALUExprCycle files oldSlots s1 expression control
      false false false 1 = .ok ([tImmWrite 1] ++ [fmul7ImmALUWrite], s2) :=
    prepareParsedIntegerALUExprCycle_immediate files oldSlots s1 expression control
      false false false 1 (tImmTargets 1) [tImmWrite 1] none s2 0x40E00000 false
      isImmediate (lowered 1) (prepared 1) (flushResolved 1) (updated 1 s1)
  have step2 : prepareParsedIntegerALUExprCycle files oldSlots s2 expression control
      false false false 2 = .ok ([tImmWrite 2] ++ [fmul7ImmALUWrite], s3) :=
    prepareParsedIntegerALUExprCycle_immediate files oldSlots s2 expression control
      false false false 2 (tImmTargets 2) [tImmWrite 2] none s3 0x40E00000 false
      isImmediate (lowered 2) (prepared 2) (flushResolved 2) (updated 2 s2)
  have step3 : prepareParsedIntegerALUExprCycle files oldSlots s3 expression control
      false false false 3 = .ok ([tImmWrite 3] ++ [fmul7ImmALUWrite], s4) :=
    prepareParsedIntegerALUExprCycle_immediate files oldSlots s3 expression control
      false false false 3 (tImmTargets 3) [tImmWrite 3] none s4 0x40E00000 false
      isImmediate (lowered 3) (prepared 3) (flushResolved 3) (updated 3 s3)
  unfold prepareParsedIntegerALUExprCycles
  simp only [parsedIntegerALUCycles]
  rw [prepareParsedIntegerALUCycles.eq_2, step0]
  dsimp only
  rw [List.nil_append]
  rw [prepareParsedIntegerALUCycles.eq_2, step1]
  dsimp only
  rw [prepareParsedIntegerALUCycles.eq_2, step2]
  dsimp only
  rw [prepareParsedIntegerALUCycles.eq_2, step3]
  dsimp only
  rw [prepareParsedIntegerALUCycles.eq_1]
  simp only [StepResult.ok.injEq]
  refine Prod.ext rfl ?_
  funext unit cycle
  have hsmall : cycle.val = 0 ∨ cycle.val = 1 ∨ cycle.val = 2 ∨ cycle.val = 3 := by
    have := cycle.isLt; omega
  rcases hsmall with h | h | h | h
  · rw [show cycle = 0 from Fin.ext (by simpa using h)]
    cases unit <;> simp [s0, s1, s2, s3, s4, immediateALUSlots, fmul7ImmALUWrite]
  · rw [show cycle = 1 from Fin.ext (by simpa using h)]
    cases unit <;> simp [s0, s1, s2, s3, s4, immediateALUSlots, fmul7ImmALUWrite]
  · rw [show cycle = 2 from Fin.ext (by simpa using h)]
    cases unit <;> simp [s0, s1, s2, s3, s4, immediateALUSlots, fmul7ImmALUWrite]
  · rw [show cycle = 3 from Fin.ext (by simpa using h)]
    cases unit <;> simp [s0, s1, s2, s3, s4, immediateALUSlots, fmul7ImmALUWrite]


theorem fmul7InitialPERegisters_maskRegisters (input : Fmul7Input) (pe : PEId) :
    (fmul7InitialPERegisters input pe).maskRegisters =
      zeroInitialPERegisterFiles.maskRegisters := by
  unfold fmul7InitialPERegisters
  split <;> rfl

theorem fmul7Imm_rowExpression_general (files : IntegerRegisterFiles)
    (oldSlots : ProofsLean.MNCore.Forwarding.Slots)
    (control : ParsedMaskExecutionControl) (store : ParsedMatrixReadStore)
    (directiveEq : control.directive = rustSimulatorInitialState.maskDirective)
    (registersEq : files.maskRegisters = zeroInitialPERegisterFiles.maskRegisters) :
    prepareParsedIntegerMatrixReadLineExpression files oldSlots oldSlots store
        fmul7ImmExpr.toParsed control false false false =
      .ok (fmul7ImmWrites,
        immediateALUSlots oldSlots 0x40E00000 false false (fun _ => none), []) := by
  unfold prepareParsedIntegerMatrixReadLineExpression
  rw [fmul7Imm_op]
  dsimp only
  rw [fmul7Imm_aluCycles_general files oldSlots control directiveEq registersEq]
  dsimp only
  simp only [parsedIntegerALUBarUpdates, fmul7ImmExpr, NormalizedExpr.toParsed,
    fmul7TLong, fmul7ImmWrites]

theorem fmul7Imm_lineCycles_general (files : IntegerRegisterFiles)
    (oldSlots : ProofsLean.MNCore.Forwarding.Slots)
    (control : ParsedMaskExecutionControl) (store : ParsedMatrixReadStore)
    (directiveEq : control.directive = rustSimulatorInitialState.maskDirective)
    (registersEq : files.maskRegisters = zeroInitialPERegisterFiles.maskRegisters) :
    prepareParsedIntegerMatrixReadLineCycles files oldSlots store
        [fmul7ImmExpr.toParsed] control false =
      .ok (fmul7ImmWrites,
        immediateALUSlots oldSlots 0x40E00000 false false (fun _ => none), []) := by
  unfold prepareParsedIntegerMatrixReadLineCycles
  dsimp only
  simp only [fmul7Imm_noMask]
  refine prepareParsedIntegerMatrixReadLineExpressions_singleton files oldSlots store
    fmul7ImmExpr.toParsed control false false false fmul7ImmWrites
    (immediateALUSlots oldSlots 0x40E00000 false false (fun _ => none)) [] ?_
  exact fmul7Imm_rowExpression_general files oldSlots control store directiveEq registersEq


/-- **The imm line's per-PE core step succeeds and commits the explicit write
list.** -/
theorem fmul7Imm_pecore (input : Fmul7Input) (state : State) (pe : PEId)
    (filesEq : state.peRegisters pe = fmul7InitialPERegisters input pe)
    (_validEq : ∀ (unit : ProofsLean.MNCore.Forwarding.Unit) (cycle : Fin 4),
      state.forwardingValid pe unit cycle = false)
    (_ctxEq : state.peContext pe = ParsedIntegerContext.ofLinearIndex pe)
    (directiveEq : state.maskDirective = rustSimulatorInitialState.maskDirective) :
    ∃ next, executeIntegerProducerLineAtPECore [fmul7ImmExpr.toParsed] state pe = .ok next ∧
      next.peRegisters pe =
        commitParsedMaskedWrites (fmul7InitialPERegisters input pe) fmul7ImmWrites := by
  unfold executeIntegerProducerLineAtPECore
  dsimp only
  rw [filesEq]
  rw [show ([fmul7ImmExpr.toParsed].filter parsedExprIsIntegerMatrixReadStageInput) =
      [fmul7ImmExpr.toParsed] from by simp [fmul7Imm_stageInput]]
  rw [directiveEq]
  unfold parsedIntegerMatrixReadLineFourCycleStep
  rw [fmul7Imm_lineCycles_general (fmul7InitialPERegisters input pe)
    (stateForwardingSlots state pe)
    { directive := rustSimulatorInitialState.maskDirective
      context :=
        { (ParsedIntegerContext.ofLinearIndex pe) with
          bar0 := (state.peContext pe).bar0
          bar1 := (state.peContext pe).bar1
          tWord := (state.peContext pe).tWord }
      elapsedWords := state.hazardClock }
    (state.matrixRegisters (ParsedIntegerContext.ofLinearIndex pe).group
      (ParsedIntegerContext.ofLinearIndex pe).l2b
      (ParsedIntegerContext.ofLinearIndex pe).l1b)
    rfl (fmul7InitialPERegisters_maskRegisters input pe)]
  dsimp only
  rw [executeParsedFloatMAUsAtPE_empty _ _ _ _ _ _ _
    (by simp [fmul7Imm_notFloat])]
  dsimp only
  rw [updateSupportedPELineForwarding_eq]
  dsimp only
  exact ⟨_, rfl, by simp⟩


theorem fmul7Imm_notBar : parsedExprIsIntegerBARWriter fmul7ImmExpr.toParsed = false := by
  decide

/-- The walk invariant: every not-yet-visited PE still has the initial file,
invalid forwarding and the linear-index context; the mask directive is the
default one. -/
structure Fmul7ImmWalkInvariant (input : Fmul7Input) (pes : List PEId) (state : State) : Prop where
  directive : state.maskDirective = rustSimulatorInitialState.maskDirective
  files : ∀ p ∈ pes, state.peRegisters p = fmul7InitialPERegisters input p
  valid : ∀ p ∈ pes, ∀ (unit : ProofsLean.MNCore.Forwarding.Unit) (cycle : Fin 4),
    state.forwardingValid p unit cycle = false
  context : ∀ p ∈ pes, state.peContext p = ParsedIntegerContext.ofLinearIndex p

/-- **The imm line's PE walk succeeds.** -/
theorem fmul7Imm_walk (input : Fmul7Input) (pes : List PEId) (state : State)
    (nodup : pes.Nodup) (inv : Fmul7ImmWalkInvariant input pes state) :
    ∃ next, executeIntegerProducerLineAtPEs [fmul7ImmExpr.toParsed] pes state = .ok next := by
  induction pes generalizing state with
  | nil => exact ⟨state, rfl⟩
  | cons pe rest ih =>
      obtain ⟨mid, coreOk, _⟩ := fmul7Imm_pecore input state pe
        (inv.files pe (by simp)) (inv.valid pe (by simp)) (inv.context pe (by simp))
        inv.directive
      have lineOk : executeIntegerProducerLineAtPE [fmul7ImmExpr.toParsed] state pe = .ok mid := by
        unfold executeIntegerProducerLineAtPE
        simp [fmul7Imm_notBar, coreOk]
      have maskEq : mid.maskDirective = state.maskDirective :=
        (executeIntegerProducerLineAtPECore_maskDirective_hazardClock
          [fmul7ImmExpr.toParsed] state mid pe coreOk).1
      have restInv : Fmul7ImmWalkInvariant input rest mid := by
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [maskEq]; exact inv.directive
        · intro p member
          have different : p ≠ pe := by
            intro same
            subst same
            exact (List.nodup_cons.mp nodup).1 member
          have fields := executeIntegerProducerLineAtPECore_peFields_other
            [fmul7ImmExpr.toParsed] state mid pe p different coreOk
          rw [fields.1]
          exact inv.files p (List.mem_cons_of_mem _ member)
        · intro p member unit cycle
          have different : p ≠ pe := by
            intro same
            subst same
            exact (List.nodup_cons.mp nodup).1 member
          have fields := executeIntegerProducerLineAtPECore_peFields_other
            [fmul7ImmExpr.toParsed] state mid pe p different coreOk
          rw [fields.2.2.1]
          exact inv.valid p (List.mem_cons_of_mem _ member) unit cycle
        · intro p member
          have different : p ≠ pe := by
            intro same
            subst same
            exact (List.nodup_cons.mp nodup).1 member
          have fields := executeIntegerProducerLineAtPECore_peFields_other
            [fmul7ImmExpr.toParsed] state mid pe p different coreOk
          rw [fields.2.2.2]
          exact inv.context p (List.mem_cons_of_mem _ member)
      obtain ⟨next, walked⟩ := ih mid (List.nodup_cons.mp nodup).2 restInv
      refine ⟨next, ?_⟩
      rw [executeIntegerProducerLineAtPEs]
      rw [lineOk]
      dsimp only
      exact walked

/-- **The imm line's step succeeds at the initial state.** -/
theorem fmul7Imm_lineStep (input : Fmul7Input) :
    ∃ next, executeNormalizedLine (.pe [fmul7ImmExpr]) (fmul7InitialState input) = .ok next := by
  have inv : Fmul7ImmWalkInvariant input (List.finRange 4096) (fmul7InitialState input) := by
    refine ⟨rfl, ?_, ?_, ?_⟩
    · intro p member
      unfold fmul7InitialState
      rfl
    · intro p member unit cycle
      unfold fmul7InitialState
      rfl
    · intro p member
      unfold fmul7InitialState
      rfl
  obtain ⟨nextPEs, walked⟩ := fmul7Imm_walk input (List.finRange 4096)
    (fmul7InitialState input) (List.nodup_finRange 4096) inv
  have rows : (([fmul7ImmExpr].map NormalizedExpr.toParsed).all parsedExprIsLineExecRow) = true := by
    simp [fmul7Imm_lineExecRow]
  have step := executeIntegerProducerInstructionLine_pe_lineExec [fmul7ImmExpr]
    (fmul7InitialState input) nextPEs fmul7Imm_accepted rows walked
  refine ⟨{ nextPEs with
    hazardClock := nextPEs.hazardClock + InstructionLine.cost (.pe [fmul7ImmExpr])
    l1bmTurnaroundValid := false }, ?_⟩
  unfold executeNormalizedLine
  simp only [NormalizedLine.toInstruction?]
  exact step


/-! ## 7. The fvmul cycle: value interface -/

theorem prepareSingleMAUSource_false (bus : IntegerALU.Bus) :
    prepareSingleMAUSource bus false false false = bus.high := by
  simp [prepareSingleMAUSource]

theorem multiplyBus_high (left right : BitVec 64) :
    (FloatMultiply.multiplyBus left right).extractLsb' 32 32 =
      FloatMultiply.multiply (left.extractLsb' 32 32) (right.extractLsb' 32 32) := by
  simp only [FloatMultiply.multiplyBus]
  rw [BitVec.extractLsb'_append_eq_left]

theorem multiplyBus_low (left right : BitVec 64) :
    (FloatMultiply.multiplyBus left right).extractLsb' 0 32 =
      FloatMultiply.multiply (left.extractLsb' 0 32) (right.extractLsb' 0 32) := by
  simp only [FloatMultiply.multiplyBus]
  rw [BitVec.extractLsb'_append_eq_right]

/-- **One `fvmul` cycle, prepared form.**  Direct application of
`executeParsedFloatMAUCycleAtPE_mul_success` with the lowered accesses and the
two successful source reads. -/
theorem fmul7Mul_cycle_value_prepared
    (readFiles currentFiles : IntegerRegisterFiles)
    (oldSlots : ProofsLean.MNCore.Forwarding.Slots)
    (slot : Fin 4) (context : ParsedIntegerContext) (cycle : Fin 4)
    (accesses : ParsedFloatMultiplyAccesses) (busA busB : IntegerALU.Bus)
    (isMul : (fmul7MulExpr (8 * slot.val)).toParsed.op = .mau .f false .mul none false)
    (lowered : lowerParsedFloatMultiply? (fmul7MulExpr (8 * slot.val)).toParsed
      { context with cycle := cycle } = some accesses)
    (readA : ParsedIntegerInput.readWithForwarding readFiles oldSlots cycle accesses.sourceA =
      .ok busA)
    (readB : ParsedIntegerInput.readWithForwarding readFiles oldSlots cycle accesses.sourceB =
      .ok busB) :
    executeParsedFloatMAUCycleAtPE readFiles currentFiles oldSlots
        (fmul7MulExpr (8 * slot.val)).toParsed context cycle =
      .ok (currentFiles,
        ⟨FloatMultiply.multiplyBus
          (prepareSingleMAUSource busA accesses.negateA accesses.extendA accesses.roundA)
          (prepareSingleMAUSource busB accesses.negateB accesses.extendB accesses.roundB), 0⟩,
        parsedVectorMAUFlags .single false
          ⟨FloatMultiply.multiplyBus
            (prepareSingleMAUSource busA accesses.negateA accesses.extendA accesses.roundA)
            (prepareSingleMAUSource busB accesses.negateB accesses.extendB accesses.roundB), 0⟩) :=
  executeParsedFloatMAUCycleAtPE_mul_success readFiles currentFiles oldSlots
    (fmul7MulExpr (8 * slot.val)).toParsed context cycle accesses busA busB isMul lowered
    readA readB

/-- **One `fvmul` cycle, high-bus form.**  With the no-negate/no-extend/no-round
attributes (which `fmul7MulExpr` has), the cycle output is the pointwise
`FloatMultiply.multiply` of the two source high buses. -/
theorem fmul7Mul_cycle_value
    (readFiles currentFiles : IntegerRegisterFiles)
    (oldSlots : ProofsLean.MNCore.Forwarding.Slots)
    (slot : Fin 4) (context : ParsedIntegerContext) (cycle : Fin 4)
    (accesses : ParsedFloatMultiplyAccesses) (busA busB : IntegerALU.Bus)
    (isMul : (fmul7MulExpr (8 * slot.val)).toParsed.op = .mau .f false .mul none false)
    (lowered : lowerParsedFloatMultiply? (fmul7MulExpr (8 * slot.val)).toParsed
      { context with cycle := cycle } = some accesses)
    (readA : ParsedIntegerInput.readWithForwarding readFiles oldSlots cycle accesses.sourceA =
      .ok busA)
    (readB : ParsedIntegerInput.readWithForwarding readFiles oldSlots cycle accesses.sourceB =
      .ok busB)
    (negateA : accesses.negateA = false) (extendA : accesses.extendA = false)
    (roundA : accesses.roundA = false)
    (negateB : accesses.negateB = false) (extendB : accesses.extendB = false)
    (roundB : accesses.roundB = false) :
    executeParsedFloatMAUCycleAtPE readFiles currentFiles oldSlots
        (fmul7MulExpr (8 * slot.val)).toParsed context cycle =
      .ok (currentFiles,
        ⟨FloatMultiply.multiplyBus busA.high busB.high, 0⟩,
        parsedVectorMAUFlags .single false
          ⟨FloatMultiply.multiplyBus busA.high busB.high, 0⟩) := by
  rw [fmul7Mul_cycle_value_prepared readFiles currentFiles oldSlots slot context cycle
    accesses busA busB isMul lowered readA readB]
  simp only [negateA, extendA, roundA, negateB, extendB, roundB,
    prepareSingleMAUSource_false]


/-! ## 9. The fvmul source and lowering interfaces -/

theorem readWithForwarding_memory (files : IntegerRegisterFiles)
    (slots : ProofsLean.MNCore.Forwarding.Slots) (cycle : Fin 4)
    (access : DirectMemoryAccess) (rounded : Bool) :
    ParsedIntegerInput.readWithForwarding files slots cycle (.memory access rounded) =
      .ok (ParsedIntegerInput.applyRounding rounded (pack (readDirectAccess files access))) := by
  simp [ParsedIntegerInput.readWithForwarding, ParsedIntegerInput.read]

theorem fmul7Mul_lm0_read (input : Fmul7Input) (slot : Fin 4) (cycle : Fin 4) :
    ParsedIntegerInput.readWithForwarding (fmul7InitialPERegisters input 0)
      (stateForwardingSlots (fmul7InitialState input) 0) cycle
      (.memory ⟨.lm0, .long, ⟨cycle.val * 2, by
        have := cycle.isLt; change cycle.val * 2 < 4096; omega⟩⟩ false) =
    .ok (pack (readDirectAccess (fmul7InitialPERegisters input 0)
      ⟨.lm0, .long, ⟨cycle.val * 2, by
        have := cycle.isLt; change cycle.val * 2 < 4096; omega⟩⟩)) := by
  rw [readWithForwarding_memory]
  rfl

/-- The lowered accesses of the canonical `fvmul` row, parameterised by the two
resolved source accesses. -/
def fmul7MulAccesses (slot : Fin 4) (context : ParsedIntegerContext) (cycle : Fin 4)
    (sourceA sourceB : DirectMemoryAccess) : ParsedFloatMultiplyAccesses where
  sourceA := .memory sourceA false
  sourceB := .memory sourceB false
  negateA := false
  negateB := false
  extendA := false
  extendB := false
  roundA := false
  roundB := false
  destinations := [fmul7Lm1Long (8 * slot.val)]


theorem fmul7Mul_t_read (files : IntegerRegisterFiles)
    (slots : ProofsLean.MNCore.Forwarding.Slots) (cycle : Fin 4)
    (readValue : readDirectAccess files
      ⟨.t, .long, ⟨cycle.val * 4, by have := cycle.isLt; change cycle.val * 4 < 16; omega⟩⟩ =
      fun k => if k.val < 2 then 0x40E00000 else 0) :
    ParsedIntegerInput.readWithForwarding files slots cycle
      (.memory ⟨.t, .long, ⟨cycle.val * 4, by
        have := cycle.isLt; change cycle.val * 4 < 16; omega⟩⟩ false) =
      .ok ⟨0x40E0000040E00000, 0⟩ := by
  rw [readWithForwarding_memory]
  simp [readValue, pack, ParsedIntegerInput.applyRounding]

/-! ## 10. Trust report -/

#print axioms fmul7ProductSlot?_isSome_iff
#print axioms fmul7ProductWindows_mem
#print axioms fmul7ProductWindows_length_lt
#print axioms fmul7ProductWindows_card_le
#print axioms fmul7WindowUnion_card_le
#print axioms fmul7ShapeCoverage
#print axioms fmul7_shape_score_five_of_residual
#print axioms fmul7Imm_lowered
#print axioms fmul7Imm_prepared
#print axioms fmul7Imm_aluCycles
#print axioms fmul7Imm_legal
#print axioms fmul7Imm_accepted
#print axioms fmul7Imm_aluCycles_any
#print axioms fmul7Imm_aluCycles_general
#print axioms fmul7Imm_rowExpression
#print axioms fmul7Imm_lineCycles_any
#print axioms fmul7Imm_lineCycles_general
#print axioms fmul7Imm_pecore
#print axioms fmul7Imm_walk
#print axioms fmul7Imm_lineStep
#print axioms prepareSingleMAUSource_false
#print axioms multiplyBus_high
#print axioms multiplyBus_low
#print axioms fmul7Mul_cycle_value
#print axioms readWithForwarding_memory
#print axioms fmul7Mul_lm0_read
#print axioms fmul7Mul_t_read
#print axioms fmul7Mul_cycle_value
#print axioms readWithForwarding_memory
#print axioms fmul7Mul_lm0_read
#print axioms fmul7Mul_t_read

end ProofsLean.MNCore
