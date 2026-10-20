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
  | forwarding | issueControl | maskRegisters | maskControl | bar | t | lbf
  | l1bmTurnaround | hazardClock
  deriving DecidableEq, Repr

structure Footprint where
  operandReads : List (OperandRole × OperandRef)
  operandWrites : List (OperandRole × OperandRef)
  unitReads : List UnitResource
  unitWrites : List UnitResource
  deriving DecidableEq, Repr

def emptyFootprint : Footprint := ⟨[], [], [], []⟩

/-- An unmasked writable PE destination can inherit the current multiline mask
directive. The directive can also select the mask used for an unmasked OMR
write. -/
def ParsedOperand.mayReadMaskDirective : ParsedOperand → Bool
  | .mem _ _ _ _ none | .bar _ _ none | .omr _ none => true
  | _ => false

def ParsedOperand.isL1BMTurnaround : ParsedOperand → Bool
  | .l1bm _ none => true
  | _ => false

def ParsedOperand.readsBARContext : ParsedOperand → Bool
  | .mem access .. => access.bank == .lm0 || access.bank == .lm1
  | _ => false

def ParsedOperand.readsTContext : ParsedOperand → Bool
  | .mem access .. => access.region.tIndirect
  | _ => false

theorem ParsedOperand.isL1BMTurnaround_iff_missing_address (width : Fin 5)
    (address : Option (Fin (2 ^ 32))) :
    ParsedOperand.isL1BMTurnaround (.l1bm width address) = address.isNone := by
  cases address <;> rfl

def parsedOpUnitReads : ParsedOp → List UnitResource
  | .alu .. => [.alu]
  | .immediate .. | .zero => []
  | .mau .. => [.mau]
  | .matrixWrite .. | .matrixRead .. => [.matrix]
  | .wait .. => []
  | .noforward => [.forwarding]
  | .l1bm .. => [.l1bm]
  | .l2bm .. => [.l2bm]

-- A `noforward` expression is not a passive issue directive: every visited PE
-- rewrites its forwarding slots with `stateForwardingSlots` (invalid slots
-- become poison), and `executeIntegerProducerLineAtPECore` assigns
-- `forwarding pe := stateForwardingSlots state pe` for it. Naming `.forwarding`
-- here matches that write; the issue-control effect remains named as well.
def parsedOpUnitWrites : ParsedOp → List UnitResource
  | .alu .. | .immediate .. | .zero => [.alu, .forwarding]
  | .mau .. => [.mau, .forwarding]
  | .matrixWrite .. => [.matrix]
  | .matrixRead .. => [.matrix, .forwarding]
  | .wait .. => []
  | .noforward => [.issueControl, .forwarding]
  | .l1bm .. => [.l1bm, .forwarding]
  | .l2bm .. => [.l2bm, .forwarding]

def parsedOpMayWriteL1BMTurnaround : ParsedOp → Bool
  | .l1bm (.mwrite _) => true
  | .l1bm (.m4write _) => true
  | .l1bm (.gather _) => true
  | .l1bm (.reduce ..) => true
  | .l1bm (.reduce4 ..) => true
  | _ => false

def parsedExprMayWriteL1BMTurnaround (expression : ParsedExpr) : Bool :=
  parsedOpMayWriteL1BMTurnaround expression.op

def parsedExprUnitReads (expression : ParsedExpr) : List UnitResource :=
  parsedOpUnitReads expression.op ++
    (if (expression.maskApplications.filterMap ParsedMask.variableEntry?).isEmpty &&
        !(expression.destinations.any ParsedOperand.mayReadMaskDirective) then []
      else [.maskRegisters]) ++
    (if expression.destinations.any ParsedOperand.mayReadMaskDirective then [.maskControl]
      else []) ++
    (if expression.sources.any ParsedOperand.isL1BMTurnaround then [.l1bmTurnaround]
      else []) ++
    (if (expression.sources ++ expression.destinations).any ParsedOperand.readsBARContext
      then [.bar] else []) ++
    (if (expression.sources ++ expression.destinations).any ParsedOperand.readsTContext
      then [.t] else [])

def parsedExprFootprint (expression : ParsedExpr) : Footprint :=
  { operandReads :=
      expression.sources.map (fun operand => (.source, .pe operand)) ++
        expression.destinations.map (fun operand => (.destinationRead, .pe operand))
    operandWrites := expression.destinations.map
      (fun operand => (.destinationWrite, .pe operand))
    unitReads := parsedExprUnitReads expression
    unitWrites := parsedOpUnitWrites expression.op ++
      (if expression.maskRegisterWrites.isEmpty then [] else [.maskRegisters]) ++
      (if expression.barWrites.isEmpty then [] else [.bar]) ++
      (if expression.writesLbf then [.lbf] else []) ++
      (if parsedOpMayWriteL1BMTurnaround expression.op then [.l1bmTurnaround] else []) }

def normalizedMvFootprint (transfer : NormalizedMv) : Footprint :=
  if transfer.kind == .nop then emptyFootprint else
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

theorem Footprint.foldl_unitWrites_contains_effect {α : Type} (items : List α)
    (effect : α → Footprint) (initial : Footprint) (item : α)
    (member : item ∈ items) (resource : UnitResource)
    (writes : resource ∈ (effect item).unitWrites) :
    resource ∈ (items.foldl
      (fun result current => Footprint.combine result (effect current)) initial).unitWrites := by
  induction items generalizing initial with
  | nil => simp at member
  | cons head rest ih =>
      rcases List.mem_cons.mp member with same | later
      · subst item
        have afterHead : resource ∈ (Footprint.combine initial (effect head)).unitWrites := by
          simp [Footprint.combine, writes]
        exact Footprint.foldl_unitWrites_keep rest effect
          (Footprint.combine initial (effect head)) resource afterHead
      · exact ih (Footprint.combine initial (effect head)) later

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

/-- Footprint-local spelling of "this expression is a `noforward` directive".
Kept here so that `Footprint.lean` does not depend on the executor module. -/
def parsedExprIsNoforward (expression : ParsedExpr) : Bool :=
  match expression.op with
  | .noforward => true
  | _ => false

/-- Footprint of a `pe` issue line.

The line-level `unitWrites` seed carries the writes that the executor performs
once per line rather than once per expression:

* **forwarding.** Every successful `pe` line runs
  `updateSupportedPELineForwarding` at every PE. Even a line with no producer
  rewrites the ALU/MAU/matrix-read slots (`Forwarding.advanceReference` turns
  absent ALU/MAU producers into poison and an absent matrix-read producer into
  zero) and recomputes `forwardingValid`. A `noforward` line additionally
  rewrites the payload with `stateForwardingSlots`, but an empty or wait-only
  line is not exempt either, so `.forwarding` is seeded for every `pe` line.
  This is why the per-expression `.noforward` write alone is not sufficient.
* **turnaround.** Every `pe` line without a `noforward` expression assigns
  `l1bmTurnaroundValid`: `executeIntegerProducerInstructionLine` ends with
  `l1bmTurnaroundValid := if noForward then old else hasPEToL1Producer`, and
  `hasPEToL1Producer` is `false` when no expression may write the L1BM
  turnaround. So an ordinary ALU line (and even an empty `pe` line) writes the
  latch to `false`. `machine.rs` models the same latch as `$lbi` plus
  `lbi_error`: a step without a PE-to-L1BM transfer records the "no transfer"
  error, and `if !noforward { ... lbi_error ... }` skips that write for a
  no-forward step. A `noforward` line therefore preserves the latch.

These are line-level writes, not expression-level ones, so the seed is applied
once here; the per-expression composition in `parsedExprFootprint` is
unchanged apart from the `noforward` forwarding write. -/
def peLineFootprint (expressions : List NormalizedExpr) : Footprint :=
  expressions.foldl (fun result expression =>
    Footprint.combine result (parsedExprFootprint expression.toParsed))
    { emptyFootprint with unitWrites :=
        if (expressions.map NormalizedExpr.toParsed).any parsedExprIsNoforward then
          [.hazardClock, .forwarding]
        else [.hazardClock, .forwarding, .l1bmTurnaround] }

theorem peLineFootprint_starts_with_hazardClock (expressions : List NormalizedExpr) :
    UnitResource.hazardClock ∈
      (if (expressions.map NormalizedExpr.toParsed).any parsedExprIsNoforward then
        ([.hazardClock, .forwarding] : List UnitResource)
      else [.hazardClock, .forwarding, .l1bmTurnaround]) := by
  split <;> simp

theorem peLineFootprint_starts_with_forwarding (expressions : List NormalizedExpr) :
    UnitResource.forwarding ∈
      (if (expressions.map NormalizedExpr.toParsed).any parsedExprIsNoforward then
        ([.hazardClock, .forwarding] : List UnitResource)
      else [.hazardClock, .forwarding, .l1bmTurnaround]) := by
  split <;> simp

theorem peLineFootprint_forwarding_in_writes (expressions : List NormalizedExpr) :
    UnitResource.forwarding ∈ (peLineFootprint expressions).unitWrites := by
  simp only [peLineFootprint]
  apply Footprint.foldl_unitWrites_keep
  exact peLineFootprint_starts_with_forwarding expressions

theorem peLineFootprint_l1bmTurnaround_in_writes (expressions : List NormalizedExpr)
    (noNoforward :
      (expressions.map NormalizedExpr.toParsed).any parsedExprIsNoforward = false) :
    UnitResource.l1bmTurnaround ∈ (peLineFootprint expressions).unitWrites := by
  simp only [peLineFootprint, noNoforward, Bool.false_eq_true, if_false]
  apply Footprint.foldl_unitWrites_keep
  simp

def instructionLineFootprint : InstructionLine → Footprint
  | .pe expressions => peLineFootprint expressions
  | .nop .. => { emptyFootprint with unitWrites := [.hazardClock] }
  | .mv transfer => Footprint.combine (normalizedMvFootprint transfer)
      { emptyFootprint with unitWrites := [.hazardClock] }

/-- Footprint of every normalized source line, including zero-cost mask
directives. A directive changes the mask-control context but consumes no issue
word and therefore does not write the hazard clock. -/
def normalizedLineFootprint : NormalizedLine → Footprint
  | .pe expressions => peLineFootprint expressions
  | .nop 0 _ => emptyFootprint
  | .nop (_ + 1) _ => { emptyFootprint with unitWrites := [.hazardClock] }
  | .mv transfer => Footprint.combine (normalizedMvFootprint transfer)
      { emptyFootprint with unitWrites := [.hazardClock] }
  | .maskDirective .. =>
      { emptyFootprint with unitWrites := [.maskControl] }

/-- Every normalized line that emits an instruction word has the same
syntactic footprint as the `InstructionLine` consumed by the execution
transition. Zero-count nops and mask directives are excluded because they do
not produce an instruction line. -/
theorem NormalizedLine.footprint_eq_instructionLineFootprint
    (line : NormalizedLine) (instruction : InstructionLine)
    (emits : line.toInstruction? = some instruction) :
    normalizedLineFootprint line = instructionLineFootprint instruction := by
  cases line with
  | pe expressions =>
      simp only [NormalizedLine.toInstruction?] at emits
      cases emits
      rfl
  | nop count wait =>
      cases count with
      | zero => simp [NormalizedLine.toInstruction?] at emits
      | succ count =>
          simp only [NormalizedLine.toInstruction?] at emits
          cases emits
          rfl
  | mv transfer =>
      simp only [NormalizedLine.toInstruction?] at emits
      cases emits
      rfl
  | maskDirective widthWords targets entry =>
      simp [NormalizedLine.toInstruction?] at emits

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

theorem ParsedExpr.mask_register_write_in_footprint (expression : ParsedExpr)
    (written : expression.maskRegisterWrites ≠ []) :
    UnitResource.maskRegisters ∈ (parsedExprFootprint expression).unitWrites := by
  simp [parsedExprFootprint, written]

theorem ParsedExpr.variable_mask_reads_register_file (expression : ParsedExpr)
    (reads : (expression.maskApplications.filterMap ParsedMask.variableEntry?) ≠ []) :
    UnitResource.maskRegisters ∈ (parsedExprFootprint expression).unitReads := by
  simp [parsedExprFootprint, parsedExprUnitReads, reads]

theorem ParsedExpr.inherited_write_mask_reads_directive (expression : ParsedExpr)
    (reads : expression.destinations.any ParsedOperand.mayReadMaskDirective = true) :
    UnitResource.maskControl ∈ (parsedExprFootprint expression).unitReads := by
  simp [parsedExprFootprint, parsedExprUnitReads, reads]

theorem ParsedExpr.l1bm_turnaround_read_in_footprint (expression : ParsedExpr)
    (reads : expression.sources.any ParsedOperand.isL1BMTurnaround = true) :
    UnitResource.l1bmTurnaround ∈ (parsedExprFootprint expression).unitReads := by
  simp [parsedExprFootprint, parsedExprUnitReads, reads]

theorem ParsedExpr.bar_context_read_in_footprint (expression : ParsedExpr)
    (reads : (expression.sources ++ expression.destinations).any
      ParsedOperand.readsBARContext = true) :
    UnitResource.bar ∈ (parsedExprFootprint expression).unitReads := by
  simp [parsedExprFootprint, parsedExprUnitReads, reads]

theorem ParsedExpr.t_context_read_in_footprint (expression : ParsedExpr)
    (reads : (expression.sources ++ expression.destinations).any
      ParsedOperand.readsTContext = true) :
    UnitResource.t ∈ (parsedExprFootprint expression).unitReads := by
  simp [parsedExprFootprint, parsedExprUnitReads, reads]

theorem ParsedExpr.bar_write_in_footprint (expression : ParsedExpr)
    (written : expression.barWrites ≠ []) :
    UnitResource.bar ∈ (parsedExprFootprint expression).unitWrites := by
  simp [parsedExprFootprint, written]

theorem ParsedExpr.lbf_write_in_footprint (expression : ParsedExpr)
    (written : expression.writesLbf = true) :
    UnitResource.lbf ∈ (parsedExprFootprint expression).unitWrites := by
  simp [parsedExprFootprint, written]

theorem ParsedExpr.l1bm_turnaround_write_in_footprint (expression : ParsedExpr)
    (written : parsedOpMayWriteL1BMTurnaround expression.op = true) :
    UnitResource.l1bmTurnaround ∈ (parsedExprFootprint expression).unitWrites := by
  simp [parsedExprFootprint, written]

theorem NormalizedLine.pe_preserves_l1bm_turnaround_write
    (expressions : List NormalizedExpr) (expression : NormalizedExpr)
    (member : expression ∈ expressions)
    (writes : parsedExprMayWriteL1BMTurnaround expression.toParsed = true) :
    UnitResource.l1bmTurnaround ∈
      (normalizedLineFootprint (.pe expressions)).unitWrites := by
  simp only [normalizedLineFootprint, peLineFootprint]
  exact Footprint.foldl_unitWrites_contains_effect expressions
    (fun current => parsedExprFootprint current.toParsed)
    _ expression member UnitResource.l1bmTurnaround
    (ParsedExpr.l1bm_turnaround_write_in_footprint expression.toParsed writes)

theorem InstructionLine.has_hazard_clock_write (line : InstructionLine) :
    UnitResource.hazardClock ∈ (instructionLineFootprint line).unitWrites := by
  cases line with
  | pe expressions =>
      have starts := peLineFootprint_starts_with_hazardClock expressions
      simpa [instructionLineFootprint, peLineFootprint] using
        Footprint.foldl_unitWrites_keep expressions
          (fun expression => parsedExprFootprint expression.toParsed)
          { emptyFootprint with unitWrites :=
            if (expressions.map NormalizedExpr.toParsed).any parsedExprIsNoforward then
              [.hazardClock, .forwarding]
            else [.hazardClock, .forwarding, .l1bmTurnaround] }
          UnitResource.hazardClock starts
  | nop count wait => simp [instructionLineFootprint]
  | mv transfer => simp [instructionLineFootprint, Footprint.combine]

theorem NormalizedLine.maskDirective_footprint (widthWords : Nat)
    (targets : ParsedMaskTargets) (entry : Fin 256) :
    (UnitResource.maskControl ∈
      (normalizedLineFootprint (.maskDirective widthWords targets entry)).unitWrites) ∧
    (UnitResource.hazardClock ∉
      (normalizedLineFootprint (.maskDirective widthWords targets entry)).unitWrites) := by
  simp [normalizedLineFootprint]

theorem NormalizedLine.zero_nop_has_empty_footprint (wait : Option (Fin 256)) :
    normalizedLineFootprint (.nop 0 wait) = emptyFootprint := rfl

theorem NormalizedLine.positive_nop_writes_hazard_clock
    (count : Nat) (wait : Option (Fin 256)) :
    UnitResource.hazardClock ∈
      (normalizedLineFootprint (.nop (count + 1) wait)).unitWrites := by
  simp [normalizedLineFootprint]

theorem NormalizedMv.nop_has_empty_footprint (transfer : NormalizedMv)
    (isNop : transfer.kind = .nop) :
    normalizedMvFootprint transfer = emptyFootprint := by
  simp [normalizedMvFootprint, isNop]

end ProofsLean.MNCore
