import ProofsLean.ProgramLegality

/-! Syntactic read/write footprints for every normalized executable row.
Address resolution and value effects remain separate: operands are preserved
as structured locations instead of assuming an incomplete datapath lowering. -/
namespace ProofsLean.MNCore

open Issue

inductive OperandRole where
  | source
  | destinationRead
  | destinationWrite
  deriving DecidableEq, Repr

inductive OperandRef where
  | pe (operand : ParsedOperand)
  | mv (operand : ParsedMvOperand)
  deriving DecidableEq, Repr

inductive UnitResource where
  | alu | mau | matrix | l1bm | l2bm | mv
  | forwarding | issueControl | hazardClock
  deriving DecidableEq, Repr

structure Footprint where
  operandReads : List (OperandRole × OperandRef)
  operandWrites : List (OperandRole × OperandRef)
  unitReads : List UnitResource
  unitWrites : List UnitResource
  deriving DecidableEq, Repr

def emptyFootprint : Footprint := ⟨[], [], [], []⟩

def parsedOpUnitReads : ParsedOp → List UnitResource
  | .alu .. => [.alu]
  | .immediate .. | .zero => []
  | .mau .. => [.mau]
  | .matrixWrite .. | .matrixRead .. => [.matrix]
  | .wait .. => []
  | .noforward => [.forwarding]
  | .l1bm .. => [.l1bm]
  | .l2bm .. => [.l2bm]

def parsedOpUnitWrites : ParsedOp → List UnitResource
  | .alu .. | .immediate .. | .zero => [.alu, .forwarding]
  | .mau .. => [.mau, .forwarding]
  | .matrixWrite .. => [.matrix]
  | .matrixRead .. => [.matrix, .forwarding]
  | .wait .. => []
  | .noforward => [.issueControl]
  | .l1bm .. => [.l1bm, .forwarding]
  | .l2bm .. => [.l2bm, .forwarding]

def parsedExprFootprint (expression : ParsedExpr) : Footprint :=
  { operandReads :=
      expression.sources.map (fun operand => (.source, .pe operand)) ++
        expression.destinations.map (fun operand => (.destinationRead, .pe operand))
    operandWrites := expression.destinations.map
      (fun operand => (.destinationWrite, .pe operand))
    unitReads := parsedOpUnitReads expression.op
    unitWrites := parsedOpUnitWrites expression.op }

def normalizedMvFootprint (transfer : NormalizedMv) : Footprint :=
  { emptyFootprint with
    operandReads := transfer.source.toList.map (fun operand => (.source, .mv operand))
    operandWrites := transfer.destination.toList.map
      (fun operand => (.destinationWrite, .mv operand))
    unitReads := [.mv]
    unitWrites := [.mv] }

def Footprint.combine (left right : Footprint) : Footprint :=
  { operandReads := left.operandReads ++ right.operandReads
    operandWrites := left.operandWrites ++ right.operandWrites
    unitReads := left.unitReads ++ right.unitReads
    unitWrites := left.unitWrites ++ right.unitWrites }

theorem Footprint.foldl_unitWrites_keep {α : Type} (items : List α)
    (effect : α → Footprint) (initial : Footprint) (resource : UnitResource)
    (member : resource ∈ initial.unitWrites) :
    resource ∈ (items.foldl
      (fun result item => Footprint.combine result (effect item)) initial).unitWrites := by
  induction items generalizing initial with
  | nil => exact member
  | cons item rest ih =>
      apply ih
      simp [Footprint.combine, member]

def writeOperand {α : Type} (state : OperandRef → α)
    (target : OperandRef) (value : α) : OperandRef → α :=
  fun location => if location = target then value else state location

def commitOperandWrites {α : Type} (state : OperandRef → α) :
    List (OperandRef × α) → OperandRef → α
  | [], location => state location
  | (target, value) :: rest, location =>
      commitOperandWrites (writeOperand state target value) rest location

theorem commitOperandWrites_preserves_absent {α : Type}
    (state : OperandRef → α) (writes : List (OperandRef × α))
    (location : OperandRef)
    (absent : ∀ target value, (target, value) ∈ writes → target ≠ location) :
    commitOperandWrites state writes location = state location := by
  induction writes generalizing state with
  | nil => rfl
  | cons head rest ih =>
      rcases head with ⟨target, value⟩
      have headDifferent := absent target value List.mem_cons_self
      have tailAbsent : ∀ target value, (target, value) ∈ rest → target ≠ location := by
        intro target value member
        exact absent target value (List.mem_cons_of_mem _ member)
      simp [commitOperandWrites, writeOperand, Ne.symm headDifferent,
        ih (writeOperand state target value) tailAbsent]

def Footprint.containsAllWrites (footprint : Footprint)
    (writes : List (OperandRef × α)) : Prop :=
  ∀ target value, (target, value) ∈ writes →
    (OperandRole.destinationWrite, target) ∈ footprint.operandWrites

theorem commitOperandWrites_frame {α : Type}
    (state : OperandRef → α) (writes : List (OperandRef × α))
    (footprint : Footprint)
    (contained : footprint.containsAllWrites writes)
    (location : OperandRef)
    (outside : (OperandRole.destinationWrite, location) ∉ footprint.operandWrites) :
    commitOperandWrites state writes location = state location := by
  apply commitOperandWrites_preserves_absent
  intro target value member same
  have inFootprint := contained target value member
  rw [same] at inFootprint
  exact outside inFootprint

def instructionLineFootprint : InstructionLine → Footprint
  | .pe expressions =>
      expressions.foldl (fun result expression =>
        Footprint.combine result (parsedExprFootprint expression.toParsed))
        { emptyFootprint with unitWrites := [.hazardClock] }
  | .nop .. => { emptyFootprint with unitWrites := [.hazardClock] }
  | .mv transfer =>
      Footprint.combine (normalizedMvFootprint transfer)
        { emptyFootprint with unitWrites := [.hazardClock] }

theorem ParsedExpr.source_in_footprint (expression : ParsedExpr)
    (operand : ParsedOperand) (member : operand ∈ expression.sources) :
    (OperandRole.source, OperandRef.pe operand) ∈
      (parsedExprFootprint expression).operandReads := by
  simp [parsedExprFootprint, member]

theorem ParsedExpr.destination_in_read_footprint (expression : ParsedExpr)
    (operand : ParsedOperand) (member : operand ∈ expression.destinations) :
    (OperandRole.destinationRead, OperandRef.pe operand) ∈
      (parsedExprFootprint expression).operandReads := by
  simp [parsedExprFootprint, member]

theorem ParsedExpr.destination_in_write_footprint (expression : ParsedExpr)
    (operand : ParsedOperand) (member : operand ∈ expression.destinations) :
    (OperandRole.destinationWrite, OperandRef.pe operand) ∈
      (parsedExprFootprint expression).operandWrites := by
  simp [parsedExprFootprint, member]

theorem InstructionLine.has_hazard_clock_write (line : InstructionLine) :
    UnitResource.hazardClock ∈ (instructionLineFootprint line).unitWrites := by
  cases line with
  | pe expressions =>
      let initial : Footprint :=
        { emptyFootprint with unitWrites := [.hazardClock] }
      have starts : UnitResource.hazardClock ∈ initial.unitWrites := by
        simp [initial]
      simpa [instructionLineFootprint, initial] using
        Footprint.foldl_unitWrites_keep expressions
          (fun expression => parsedExprFootprint expression.toParsed)
          initial UnitResource.hazardClock starts
  | nop count wait => simp [instructionLineFootprint]
  | mv transfer => simp [instructionLineFootprint, Footprint.combine]

end ProofsLean.MNCore
