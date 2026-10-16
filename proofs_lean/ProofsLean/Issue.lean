import Std
import ProofsLean.IntegerALU

/- Abstracts the PE-expression issue predicates in viz/core/src/issue.rs
(`check`, corresponding to SDM 3.6.4). This is only the issue checker layer:
the VSM parser must still be proved to produce complete and faithful records,
and execution legality has further rules outside this module. -/
namespace ProofsLean.MNCore.Issue

inductive Group where
  | alu | mauCalc | mauWrite | mauRead
  | l1bm | l1bmTurnaround | l2bm | l2bmDarw | wait | noforward
  deriving DecidableEq, Repr

inductive Bank where
  | grf0 | grf1 | lm0 | lm1 | t | l1bm | l2bm | pdm | dram | omr
  deriving DecidableEq, Repr

structure Region where
  width : Nat
  address0 : Nat
  address1 : Nat
  address2 : Nat
  address3 : Nat
  tIndirect : Bool
  madpe : Option Nat
  deriving DecidableEq, Repr

/-- A finite envelope for PE address regions. The address bound is the largest
single-word PE memory capacity in the checked assemble3 probes (LM0/LM1: 4096;
GRF0/GRF1: 512). Width-specific alignment and bank-specific legality remain
separate. See `evidence/isa-bounds/reference.json`. -/
def Region.inFiniteEnvelope (r : Region) : Prop :=
  r.width < 5 ∧ r.address0 < 4096 ∧ r.address1 < 4096 ∧
  r.address2 < 4096 ∧ r.address3 < 4096 ∧
  ∀ n, r.madpe = some n → n < 4

structure Access where
  bank : Bank
  region : Region
  deriving DecidableEq, Repr

inductive CalcKind where
  | fma | mul | add | passa
  deriving DecidableEq, Repr

inductive MauKind where
  | calc (kind : CalcKind) (matrix : Bool)
  | matrixWrite
  | matrixRead
  deriving DecidableEq, Repr

structure Mau where
  precision : Nat
  kind : MauKind
  deriving DecidableEq, Repr

inductive ParsedForward where
  | aluf | mauf | lbf | mreadf
  deriving DecidableEq, Repr

inductive ParsedFixed where
  | l2bid | l1bid | mabid | peid | subpeid | msb1
  deriving DecidableEq, Repr

inductive ParsedMask where
  | pattern (longLong : Bool) (bits : BitVec 4)
  | entry (longLong : Bool) (index : Nat)
  deriving DecidableEq, Repr

def ParsedMask.isDoubleLong : ParsedMask → Bool
  | .pattern longLong _ | .entry longLong _ => longLong

def ParsedMask.variableEntry? : ParsedMask → Option Nat
  | .entry _ index => some index
  | .pattern .. => none

/-- Structured PE operand syntax. Rust's `Operand::Raw` is a diagnostic parser
fallback for tokens outside the SDM operand productions and is not a candidate
in this legal-instruction syntax. -/
inductive ParsedOperand where
  | mem (access : Access) (neg ext rnd : Bool) (mask : Option ParsedMask)
  | bar (lm1 : Bool) (width : Nat) (mask : Option ParsedMask)
  | forward (kind : ParsedForward) (neg ext rnd : Bool)
  | fixed (kind : ParsedFixed)
  | omr (entry : Nat) (mask : Option ParsedMask)
  | matrix (y : Bool) (width : Nat) (row : Option Nat)
  | nowrite
  | l1bm (width : Nat) (address : Option Nat)
  | l2bm (address : Nat) (l2b : Option Nat)
  | dar (address : Nat)
  deriving DecidableEq, Repr

def ParsedOperand.writeMask? : ParsedOperand → Option ParsedMask
  | .mem _ _ _ _ mask | .bar _ _ mask | .omr _ mask => mask
  | _ => none

structure Expr where
  id : Nat
  group : Option Group
  mau : Option Mau
  /-- Operand identity at source position 1, when this is a calculation. -/
  secondSource : Option ParsedOperand
  /-- Operand identity at source position 0, when this writes a matrix row. -/
  matrixWriteSource : Option ParsedOperand
  reads : List Access
  writes : List Access
  matrixXUses : Nat
  matrixYUses : Nat
  maskApplications : List ParsedMask
  immediate : Bool
  zeroFlush : Bool
  deriving DecidableEq, Repr

def idsUnique (xs : List Expr) : Prop :=
  ∀ e ∈ xs, ∀ f ∈ xs, e.id = f.id → e = f

def groupsUnique (xs : List Expr) : Prop :=
  ∀ e ∈ xs, ∀ f ∈ xs, e.id ≠ f.id →
    ∀ group : Group, e.group = some group → f.group ≠ some group

def mauExpressions (xs : List Expr) : List Expr :=
  xs.filter fun e => e.mau.isSome

def mauCountBounded (xs : List Expr) : Prop :=
  (mauExpressions xs).length ≤ 2

def mauPrecisionsAgree (xs : List Expr) : Prop :=
  ∀ e ∈ mauExpressions xs, ∀ f ∈ mauExpressions xs,
    e.mau.bind (some ·.precision) = f.mau.bind (some ·.precision)

def matrixWriteKind (e : Expr) : Bool :=
  e.mau.map (fun m => m.kind) == some .matrixWrite

def vectorFmaOrMul (e : Expr) : Bool :=
  e.mau.map (fun m => m.kind) == some (.calc .fma false) ||
  e.mau.map (fun m => m.kind) == some (.calc .mul false)

def matrixWritePairAgrees (xs : List Expr) : Prop :=
  match mauExpressions xs with
  | [first, second] =>
      if matrixWriteKind first then
        if vectorFmaOrMul second then
          first.matrixWriteSource = second.secondSource
        else True
      else if matrixWriteKind second && vectorFmaOrMul first then
        first.secondSource = second.matrixWriteSource
      else True
  | _ => True

def matrixRegistersUnique (xs : List Expr) : Prop :=
  (xs.map Expr.matrixXUses).sum ≤ 1 ∧ (xs.map Expr.matrixYUses).sum ≤ 1

def writesUnique (xs : List Expr) : Prop :=
  ∀ e ∈ xs, ∀ f ∈ xs, ∀ a ∈ e.writes, ∀ b ∈ f.writes,
    e.id ≠ f.id → a.bank = b.bank → False

def readsAgree (xs : List Expr) : Prop :=
  ∀ e ∈ xs, ∀ f ∈ xs, ∀ a ∈ e.reads, ∀ b ∈ f.reads,
    a.bank = b.bank → a.region = b.region

def localReadWriteAgree (xs : List Expr) : Prop :=
  ∀ e ∈ xs, ∀ f ∈ xs, ∀ a ∈ e.reads, ∀ b ∈ f.writes,
    (a.bank = .lm0 ∨ a.bank = .lm1) → a.bank = b.bank → a.region = b.region

def immediateExcludesLm0 (xs : List Expr) : Prop :=
  ∀ e ∈ xs, e.immediate →
    (∀ f ∈ xs, ∀ a ∈ f.reads, a.bank ≠ .lm0) ∧
    (∀ f ∈ xs, ∀ a ∈ f.writes, a.bank ≠ .lm0)

def zeroFlushUnique (xs : List Expr) : Prop :=
  (xs.filter Expr.zeroFlush).length ≤ 1

def maskWidthsAgree (xs : List Expr) : Prop :=
  let widths := (xs.flatMap Expr.maskApplications).map ParsedMask.isDoubleLong
  match widths with
  | [] => True
  | first :: rest => ∀ width ∈ rest, width = first

def maskEntriesAgree (xs : List Expr) : Prop :=
  let entries := (xs.flatMap Expr.maskApplications).filterMap ParsedMask.variableEntry?
  match entries with
  | [] => True
  | first :: rest => ∀ entry ∈ rest, entry = first

/-- The explicit constraints enforced in the local PE issue checker. -/
def Legal (xs : List Expr) : Prop :=
  idsUnique xs ∧
  groupsUnique xs ∧
  mauCountBounded xs ∧
  mauPrecisionsAgree xs ∧
  matrixWritePairAgrees xs ∧
  matrixRegistersUnique xs ∧
  writesUnique xs ∧
  readsAgree xs ∧
  localReadWriteAgree xs ∧
  immediateExcludesLm0 xs ∧
  zeroFlushUnique xs ∧
  maskWidthsAgree xs ∧
  maskEntriesAgree xs

/-- Classical decision specification for the abstract rule set. This is not
claimed as executable parser or hardware validation. -/
noncomputable def check (xs : List Expr) : Bool := by
  classical
  exact decide (Legal xs)

theorem check_sound (xs : List Expr) (accepted : check xs = true) : Legal xs := by
  classical
  unfold check at accepted
  exact of_decide_eq_true accepted

theorem check_complete (xs : List Expr) (legal : Legal xs) : check xs = true := by
  classical
  unfold check
  exact decide_eq_true_eq.mpr legal

theorem rejected_not_legal (xs : List Expr) (rejected : check xs = false) : ¬ Legal xs := by
  classical
  intro legal
  have accepted := check_complete xs legal
  simp [rejected] at accepted

def emptyExpr : Expr where
  id := 0
  group := none
  mau := none
  secondSource := none
  matrixWriteSource := none
  reads := []
  writes := []
  matrixXUses := 0
  matrixYUses := 0
  maskApplications := []
  immediate := false
  zeroFlush := false

theorem empty_is_legal : Legal [] := by
  simp [Legal, idsUnique, groupsUnique, mauCountBounded, mauExpressions,
    mauPrecisionsAgree, matrixWritePairAgrees, matrixRegistersUnique,
    writesUnique, readsAgree, localReadWriteAgree, immediateExcludesLm0,
    zeroFlushUnique, maskWidthsAgree, maskEntriesAgree]

theorem empty_check_accepts : check [] = true := check_complete [] empty_is_legal

def aluExpr (id : Nat) : Expr := { emptyExpr with id := id, group := some .alu }

def maskIssueExpr (id : Nat) (group : Group) (mask : ParsedMask) : Expr :=
  { emptyExpr with id := id, group := some group, maskApplications := [mask] }

theorem conflicting_mask_widths_are_illegal :
    ¬ Legal [maskIssueExpr 0 .alu (.entry false 1),
      maskIssueExpr 1 .l1bm (.entry true 1)] := by
  intro legal
  rcases legal with ⟨_, _, _, _, _, _, _, _, _, _, _, widths, _⟩
  simp [maskWidthsAgree, maskIssueExpr, emptyExpr, ParsedMask.isDoubleLong] at widths

theorem conflicting_mask_widths_rejected :
    check [maskIssueExpr 0 .alu (.entry false 1),
      maskIssueExpr 1 .l1bm (.entry true 1)] = false := by
  classical
  apply decide_eq_false_iff_not.mpr
  exact conflicting_mask_widths_are_illegal

theorem conflicting_mask_entries_are_illegal :
    ¬ Legal [maskIssueExpr 0 .alu (.entry false 1),
      maskIssueExpr 1 .l1bm (.entry false 2)] := by
  intro legal
  rcases legal with ⟨_, _, _, _, _, _, _, _, _, _, _, _, entries⟩
  simp [maskEntriesAgree, maskIssueExpr, emptyExpr, ParsedMask.variableEntry?] at entries

theorem conflicting_mask_entries_rejected :
    check [maskIssueExpr 0 .alu (.entry false 1),
      maskIssueExpr 1 .l1bm (.entry false 2)] = false := by
  classical
  apply decide_eq_false_iff_not.mpr
  exact conflicting_mask_entries_are_illegal

theorem duplicate_alu_groups_rejected (a b : Nat) (different : a ≠ b) :
    check [aluExpr a, aluExpr b] = false := by
  classical
  unfold check
  apply decide_eq_false_iff_not.mpr
  intro legal
  have groupRule := legal.2.1
  have h := groupRule (aluExpr a) (by simp) (aluExpr b) (by simp) different .alu rfl
  exact h rfl

end ProofsLean.MNCore.Issue

namespace ProofsLean.MNCore.Issue

inductive ParsedPrecision where
  | d | f | g | h | l | i | s
  deriving DecidableEq, Repr

def ParsedPrecision.code : ParsedPrecision → Nat
  | .d => 0
  | .f => 1
  | .g => 2
  | .h => 3
  | .l => 4
  | .i => 5
  | .s => 6

theorem ParsedPrecision.code_injective : Function.Injective ParsedPrecision.code := by
  intro a b equal
  cases a <;> cases b <;> simp [ParsedPrecision.code] at equal ⊢

def ParsedPrecision.laneWidth : ParsedPrecision → IntegerALU.Precision
  | .d | .l => .long
  | .f | .g | .i => .word
  | .h | .s => .half

inductive ParsedAluName where
  | msl | msr | passa | inc | dec | not | lnot | rsqrt | floor | ftoi
  | bfe | bfn | max | min | packbit | and | or | xor | add | sub
  | lsl | lsr | bsl | bsr | relu | relu0 | relu1 | relu2 | relu3
  | lrelud | lreluo | ilrelud
  deriving DecidableEq, Repr

def ParsedAluName.toIntegerOp (name : ParsedAluName) (unsigned : Bool) :
    Option IntegerALU.Op :=
  match name with
  | .inc => some (.arith .inc unsigned)
  | .dec => some (.arith .dec unsigned)
  | .add => some (.arith .add unsigned)
  | .sub => some (.arith .sub unsigned)
  | .not => some .bitNot
  | .lnot => some .logicalNot
  | .and => some .bitAnd
  | .or => some .bitOr
  | .xor => some .bitXor
  | .max => some (.maximum unsigned)
  | .min => some (.minimum unsigned)
  | .packbit => some .packbit
  | .passa => some .passa
  | .lsl => some (.shift .left)
  | .lsr => some (.shift (.right unsigned))
  | .bsl => some (.shift .rotateLeft)
  | .bsr => some (.shift .rotateRight)
  | .msl | .msr | .rsqrt | .floor | .ftoi | .bfe | .bfn
  | .relu | .relu0 | .relu1 | .relu2 | .relu3 | .lrelud | .lreluo | .ilrelud => none

/-- Number of source operands consumed by each parsed ALU opcode, mirrored from
Rust `AluOp::inputs`. This is syntax metadata; execution support remains separate. -/
def ParsedAluName.inputCount : ParsedAluName → Nat
  | .msl | .msr | .passa | .inc | .dec | .not | .lnot | .rsqrt | .floor
  | .ftoi | .bfe | .bfn => 1
  | .max | .min | .packbit | .and | .or | .xor | .add | .sub | .lsl | .lsr
  | .bsl | .bsr | .relu | .relu0 | .relu1 | .relu2 | .relu3 | .lrelud
  | .lreluo | .ilrelud => 2

theorem ParsedAluName.inputCount_positive (name : ParsedAluName) :
    0 < name.inputCount := by
  cases name <;> decide

def ParsedAluName.supportsIntegerAt
    (name : ParsedAluName) (precision : ParsedPrecision) : Bool :=
  match name with
  | .packbit => precision != .g
  | .passa => precision == .l || precision == .i || precision == .s
  | .inc | .dec | .not | .lnot | .and | .or | .xor | .add | .sub
  | .max | .min | .lsl | .lsr | .bsl | .bsr =>
      precision == .l || precision == .i || precision == .s
  | _ => false

inductive ParsedRrnOp where
  | fadd | max | min | iadd | band | and | bor | or
  deriving DecidableEq, Repr

structure ParsedRrn where
  precision : Char
  op : ParsedRrnOp
  deriving DecidableEq, Repr

structure ParsedL1bSet where
  mask : Nat
  immode : Nat
  deriving DecidableEq, Repr

inductive ParsedL1Op where
  | pbcast | mbcast | mwrite (mab : Nat) | m4bcast | m4write (mab : Nat)
  | reduce (rrn : ParsedRrn) (round : Bool)
  | reduce4 (rrn : ParsedRrn) (round : Bool)
  | distrib (mabdiff : Int) | gather (mabdiff : Int)
  deriving DecidableEq, Repr

inductive ParsedL2Op where
  | bcast (set : ParsedL1bSet) | bcast2 (set : ParsedL1bSet)
  | distrib (set : ParsedL1bSet) | fromL1b (l1b : Nat)
  | reduce (rrn : ParsedRrn) (set : ParsedL1bSet)
  | reduce2 (rrn : ParsedRrn) | gather | imcast (set : ParsedL1bSet)
  | dars | darw
  deriving DecidableEq, Repr

inductive ParsedOp where
  | alu (name : ParsedAluName) (precision : Option ParsedPrecision)
      (unsigned : Bool) (arg : Option Nat)
  | immediate (value : BitVec 32) (unsigned : Bool)
  | zero
  | mau (precision : ParsedPrecision) (matrix : Bool) (kind : CalcKind)
      (half : Option Char) (round : Bool)
  | matrixWrite (precision : ParsedPrecision)
  | matrixRead (precision : ParsedPrecision)
  | wait (tag : Nat)
  | noforward
  | l1bm (op : ParsedL1Op)
  | l2bm (op : ParsedL2Op)
  deriving DecidableEq, Repr

/-- Maximum number of source tokens assigned by Rust `parse_expr` before its
remaining operands are split into destinations. This mirrors the parser's
`n_in` calculation; it is not by itself a theorem that an arbitrary
`ParsedExpr` came from that parser. -/
def ParsedOp.parserSourceLimit : ParsedOp → Nat
  | .alu name .. => name.inputCount
  | .immediate .. | .zero | .wait .. | .noforward => 0
  | .mau _ matrix kind .. =>
      match matrix, kind with
      | _, .fma => 3
      | _, .mul => 2
      | false, .add => 2
      | _, _ => 1
  | .matrixWrite .. | .matrixRead .. => 1
  | .l1bm .. | .l2bm .. => 1

theorem ParsedAluName.inputCount_le_two (name : ParsedAluName) :
    name.inputCount ≤ 2 := by
  cases name <;> decide

theorem ParsedOp.parserSourceLimit_le_three (op : ParsedOp) :
    op.parserSourceLimit ≤ 3 := by
  cases op with
  | alu name _ _ _ =>
      exact Nat.le_trans (ParsedAluName.inputCount_le_two name) (by decide)
  | immediate value unsigned => change 0 ≤ 3; omega
  | zero => change 0 ≤ 3; omega
  | mau precision matrix kind half round =>
      cases matrix <;> cases kind <;> simp [ParsedOp.parserSourceLimit]
  | matrixWrite precision => change 1 ≤ 3; omega
  | matrixRead precision => change 1 ≤ 3; omega
  | wait tag => change 0 ≤ 3; omega
  | noforward => simp [ParsedOp.parserSourceLimit]
  | l1bm operation => change 1 ≤ 3; omega
  | l2bm operation => change 1 ≤ 3; omega

/-- Structural PE-expression AST mirror. Issue and execution interpretations
are separate functions over this syntax. -/
structure ParsedExpr where
  op : ParsedOp
  sources : List ParsedOperand
  destinations : List ParsedOperand
  flush : Option ParsedMask
  text : String
  deriving DecidableEq, Repr

def ParsedExpr.maskApplications (expression : ParsedExpr) : List ParsedMask :=
  (expression.sources ++ expression.destinations).filterMap ParsedOperand.writeMask? ++
    expression.flush.toList

/-- Source-count condition imposed by the Rust parser's fixed source prefix. -/
def ParsedExpr.sourcesMatchParserArity (expression : ParsedExpr) : Prop :=
  expression.sources.length ≤ expression.op.parserSourceLimit

theorem ParsedExpr.sources_length_le_three (expression : ParsedExpr)
    (arity : expression.sourcesMatchParserArity) :
    expression.sources.length ≤ 3 :=
  Nat.le_trans arity expression.op.parserSourceLimit_le_three

/-- Canonical PE expression syntax. Display text is intentionally absent;
source and destination order remains explicit. -/
structure NormalizedExpr where
  op : ParsedOp
  sources : List ParsedOperand
  destinations : List ParsedOperand
  flush : Option ParsedMask
  deriving DecidableEq, Repr

def ParsedExpr.normalize (expression : ParsedExpr) : NormalizedExpr :=
  ⟨expression.op, expression.sources, expression.destinations, expression.flush⟩

def NormalizedExpr.toParsed (expression : NormalizedExpr) : ParsedExpr :=
  ⟨expression.op, expression.sources, expression.destinations, expression.flush, ""⟩

/-- Canonical expressions retain the exact opcode-specific source-prefix bound
imposed by Rust `parse_expr` when display text is erased. -/
def NormalizedExpr.sourcesMatchParserArity (expression : NormalizedExpr) : Prop :=
  expression.sources.length ≤ expression.op.parserSourceLimit

theorem ParsedExpr.normalize_sourcesMatchParserArity
    (expression : ParsedExpr)
    (arity : expression.sourcesMatchParserArity) :
    expression.normalize.sourcesMatchParserArity := by
  exact arity

theorem NormalizedExpr.sources_length_le_three (expression : NormalizedExpr)
    (arity : expression.sourcesMatchParserArity) :
    expression.sources.length ≤ 3 :=
  Nat.le_trans arity expression.op.parserSourceLimit_le_three

/-- Map only the integer ALU subset whose parsed precision is established.
Floating and otherwise unsupported encodings stay unknown. -/
def ParsedOp.integerRequest : ParsedOp → StepResult IntegerALU.Request
  | .alu name (some precision) unsigned _ =>
      if name.supportsIntegerAt precision then
        match name.toIntegerOp unsigned with
        | some op => .ok (.integer precision.laneWidth op)
        | none => .unknown
      else .unknown
  | _ => .unknown

inductive ParsedExecutionRequest where
  | integer (precision : IntegerALU.Precision) (op : IntegerALU.Op)
  | zero
  | immediate (payload : BitVec 32) (sparse : Bool)
  deriving DecidableEq, Repr

def ParsedOp.executionRequest : ParsedOp → StepResult ParsedExecutionRequest
  | .zero => .ok .zero
  | .immediate payload sparse => .ok (.immediate payload sparse)
  | op => match op.integerRequest with
      | .ok (.integer precision aluOp) => .ok (.integer precision aluOp)
      | .ok (.unimplemented _) | .failure | .unknown => .unknown

def evaluateParsedExecutionRequest (request : ParsedExecutionRequest)
    (x y : IntegerALU.Bus) (reduced : Bool) : IntegerALU.BusResult :=
  match request with
  | .integer precision op => IntegerALU.evaluateBus precision op x y reduced
  | .zero => ⟨⟨0, 0⟩, fun _ => false⟩
  | .immediate payload sparse =>
      let word := payload ++ (if sparse then (0 : BitVec 32) else payload)
      ⟨⟨word, word⟩, fun _ => false⟩

theorem zero_has_execution_request :
    (ParsedOp.zero : ParsedOp).executionRequest = .ok .zero := rfl

theorem immediate_has_execution_request (value : BitVec 32) (sparse : Bool) :
    (ParsedOp.immediate value sparse).executionRequest =
      .ok (.immediate value sparse) := rfl

theorem integer_request_is_execution_request (op : ParsedOp)
    (precision : IntegerALU.Precision) (aluOp : IntegerALU.Op)
    (selected : op.integerRequest = .ok (.integer precision aluOp)) :
    op.executionRequest = .ok (.integer precision aluOp) := by
  cases op <;> simp_all [ParsedOp.integerRequest, ParsedOp.executionRequest]

theorem zero_execution_ignores_inputs (x y z w : IntegerALU.Bus)
    (reduced reduced' : Bool) :
    evaluateParsedExecutionRequest .zero x y reduced =
      evaluateParsedExecutionRequest .zero z w reduced' := rfl

theorem immediate_execution_ignores_inputs (value : BitVec 32) (sparse : Bool)
    (x y z w : IntegerALU.Bus) (reduced reduced' : Bool) :
    evaluateParsedExecutionRequest (.immediate value sparse) x y reduced =
      evaluateParsedExecutionRequest (.immediate value sparse) z w reduced' := rfl

theorem supported_integer_opcode_has_mapping (name : ParsedAluName)
    (precision : ParsedPrecision) (unsigned : Bool)
    (supported : name.supportsIntegerAt precision = true) :
    ∃ op, name.toIntegerOp unsigned = some op := by
  cases name <;> cases precision <;>
    simp [ParsedAluName.supportsIntegerAt, ParsedAluName.toIntegerOp] at supported ⊢

def evaluateParsedIntegerAlu (op : ParsedOp) (x y : IntegerALU.Bus)
    (reduced : Bool) : StepResult IntegerALU.BusResult :=
  match op.executionRequest with
  | .ok request => .ok (evaluateParsedExecutionRequest request x y reduced)
  | .failure => .failure
  | .unknown => .unknown

theorem parsed_integer_evaluation_uses_requested_semantics (op : ParsedOp)
    (precision : IntegerALU.Precision) (aluOp : IntegerALU.Op)
    (selected : op.executionRequest = .ok (.integer precision aluOp))
    (x y : IntegerALU.Bus) (reduced : Bool) :
    evaluateParsedIntegerAlu op x y reduced =
      .ok (IntegerALU.evaluateBus precision aluOp x y reduced) := by
  simp [evaluateParsedIntegerAlu, selected, evaluateParsedExecutionRequest]

theorem unsupported_parsed_integer_is_unknown (op : ParsedOp)
    (unsupported : op.executionRequest = .unknown) (x y : IntegerALU.Bus)
    (reduced : Bool) : evaluateParsedIntegerAlu op x y reduced = .unknown := by
  simp [evaluateParsedIntegerAlu, unsupported]

theorem iinc_integer_request :
    (ParsedOp.alu .inc (some .i) false none).integerRequest =
      .ok (.integer .word (.arith .inc false)) := rfl

theorem iinc_evaluation_is_integer_alu (x y : IntegerALU.Bus) (reduced : Bool) :
    evaluateParsedIntegerAlu (.alu .inc (some .i) false none) x y reduced =
      IntegerALU.partialEvaluate (.integer .word (.arith .inc false)) x y reduced := rfl

theorem parsed_float_rsqrt_is_unknown :
    (ParsedOp.alu .rsqrt (some .f) false none).integerRequest = .unknown := rfl


def ParsedExpr.hasTurnaround (e : ParsedExpr) : Bool :=
  (e.sources ++ e.destinations).any fun operand =>
    match operand with
    | .l1bm _ none => true
    | _ => false

def ParsedExpr.issueGroup (e : ParsedExpr) : Option Group :=
  match e.op with
  | .alu .. | .immediate .. | .zero => some .alu
  | .mau .. => some .mauCalc
  | .matrixWrite .. => some .mauWrite
  | .matrixRead .. => some .mauRead
  | .l1bm _ => if e.hasTurnaround then some .l1bmTurnaround else some .l1bm
  | .l2bm .darw => some .l2bmDarw
  | .l2bm _ => some .l2bm
  | .wait _ => some .wait
  | .noforward => some .noforward

def ParsedExpr.issueMau (e : ParsedExpr) : Option Mau :=
  match e.op with
  | .mau precision matrix kind .. => some ⟨precision.code, .calc kind matrix⟩
  | .matrixWrite precision => some ⟨precision.code, .matrixWrite⟩
  | .matrixRead precision => some ⟨precision.code, .matrixRead⟩
  | _ => none

def ParsedOperand.accesses (xs : List ParsedOperand) : List Access :=
  xs.filterMap fun operand =>
    match operand with
    | .mem access .. => some access
    | _ => none

def ParsedOperand.matrixUseCount (xs : List ParsedOperand) (side : Bool) : Nat :=
  xs.filter (fun operand =>
    match operand with
    | .matrix y .. => y == side
    | _ => false) |>.length

def ParsedExpr.toIssueExpr (id : Nat) (e : ParsedExpr) : Expr where
  id := id
  group := e.issueGroup
  mau := e.issueMau
  secondSource := e.sources.drop 1 |>.head?
  matrixWriteSource := e.sources.head?
  reads := ParsedOperand.accesses e.sources
  writes := ParsedOperand.accesses e.destinations
  matrixXUses := ParsedOperand.matrixUseCount e.sources false +
    ParsedOperand.matrixUseCount e.destinations false
  matrixYUses := ParsedOperand.matrixUseCount e.sources true +
    ParsedOperand.matrixUseCount e.destinations true
  maskApplications := e.maskApplications
  immediate := e.op matches .immediate ..
  zeroFlush := e.flush.isSome

theorem projected_reads_are_mem_operands (id : Nat) (e : ParsedExpr) :
    (e.toIssueExpr id).reads = ParsedOperand.accesses e.sources := rfl

theorem projected_writes_are_mem_operands (id : Nat) (e : ParsedExpr) :
    (e.toIssueExpr id).writes = ParsedOperand.accesses e.destinations := rfl

theorem projected_group_is_parser_group (id : Nat) (e : ParsedExpr) :
    (e.toIssueExpr id).group = e.issueGroup := rfl

theorem projected_mau_is_parser_mau (id : Nat) (e : ParsedExpr) :
    (e.toIssueExpr id).mau = e.issueMau := rfl

theorem projected_mask_applications_are_parser_masks (id : Nat) (e : ParsedExpr) :
    (e.toIssueExpr id).maskApplications = e.maskApplications := rfl

theorem normalized_expr_issue_projection (id : Nat) (e : ParsedExpr) :
    (e.normalize.toParsed.toIssueExpr id) = e.toIssueExpr id := by
  cases e
  rfl

theorem normalized_expr_group (e : ParsedExpr) :
    e.normalize.toParsed.issueGroup = e.issueGroup := by
  cases e
  rfl

/-- Preserve parser order and assign the unique list-position identity used by
the abstract issue record. -/
def projectFrom (nextId : Nat) : List ParsedExpr → List Expr
  | [] => []
  | expression :: rest =>
      expression.toIssueExpr nextId :: projectFrom (nextId + 1) rest

def projectLine (expressions : List ParsedExpr) : List Expr := projectFrom 0 expressions

theorem projectFrom_id_lower (nextId : Nat) (expressions : List ParsedExpr)
    (expression : Expr) (member : expression ∈ projectFrom nextId expressions) :
    nextId ≤ expression.id := by
  induction expressions generalizing nextId with
  | nil => simp [projectFrom] at member
  | cons parsed rest ih =>
    simp only [projectFrom, List.mem_cons] at member
    rcases member with head | tail
    · subst expression
      simp [ParsedExpr.toIssueExpr]
    · have lower := ih (nextId + 1) tail
      omega

theorem projectFrom_idsUnique (nextId : Nat) (expressions : List ParsedExpr) :
    idsUnique (projectFrom nextId expressions) := by
  induction expressions generalizing nextId with
  | nil => simp [idsUnique, projectFrom]
  | cons parsed rest ih =>
    intro e he f hf equalIds
    simp only [projectFrom, List.mem_cons] at he hf
    rcases he with eHead | eTail <;> rcases hf with fHead | fTail
    · subst e
      subst f
      rfl
    · subst e
      have lower := projectFrom_id_lower (nextId + 1) rest f fTail
      simp [ParsedExpr.toIssueExpr] at equalIds
      omega
    · subst f
      have lower := projectFrom_id_lower (nextId + 1) rest e eTail
      simp [ParsedExpr.toIssueExpr] at equalIds
      omega
    · exact ih (nextId + 1) e eTail f fTail equalIds

theorem projectLine_idsUnique (expressions : List ParsedExpr) :
    idsUnique (projectLine expressions) := projectFrom_idsUnique 0 expressions

theorem projectFrom_normalized (nextId : Nat) (expressions : List ParsedExpr) :
    projectFrom nextId (expressions.map (fun e => e.normalize.toParsed)) =
      projectFrom nextId expressions := by
  induction expressions generalizing nextId with
  | nil => rfl
  | cons expression rest inductionHypothesis =>
      simp only [List.map_cons, projectFrom]
      rw [normalized_expr_issue_projection]
      rw [inductionHypothesis]

theorem projectLine_normalized (expressions : List ParsedExpr) :
    projectLine (expressions.map (fun e => e.normalize.toParsed)) =
      projectLine expressions :=
  projectFrom_normalized 0 expressions

def LegalParsedLine (expressions : List ParsedExpr) : Prop := Legal (projectLine expressions)

noncomputable def checkParsedLine (expressions : List ParsedExpr) : Bool :=
  check (projectLine expressions)

theorem parsed_check_sound (expressions : List ParsedExpr)
    (accepted : checkParsedLine expressions = true) : LegalParsedLine expressions := by
  exact check_sound (projectLine expressions) accepted

theorem parsed_check_complete (expressions : List ParsedExpr)
    (legal : LegalParsedLine expressions) : checkParsedLine expressions = true := by
  exact check_complete (projectLine expressions) legal

theorem parsed_check_unchanged_by_normalization (expressions : List ParsedExpr) :
    checkParsedLine (expressions.map (fun e => e.normalize.toParsed)) =
      checkParsedLine expressions := by
  rw [checkParsedLine, checkParsedLine, projectLine_normalized]

/-- Line constructors corresponding to the categories in the VSM parser's
top-level `Line` enum. Only `pe` lines enter the PE issue checker. -/
structure ParsedMaskTargets where
  grf0 : Bool := false
  grf1 : Bool := false
  t : Bool := false
  lm0 : Bool := false
  lm1 : Bool := false
  maskRegister : Bool := false
  deriving DecidableEq, Repr

structure ParsedMaskDirective where
  widthWords : Nat := 2
  targets : ParsedMaskTargets := {}
  entry : Nat := 0
  deriving DecidableEq, Repr

inductive ParsedMvKind where
  | nop | copy | broadcast | broadcast2 | broadcast4 | distribute
  | reduce (rrn : ParsedRrn) | reduce2 (rrn : ParsedRrn) | reduce4 (rrn : ParsedRrn)
  deriving DecidableEq, Repr

/-- Parse the RRN suffix used by MV reduction opcodes. The precision selects
the same operation family as `Rrn::parse_prefix` in the Rust parser. -/
def parseParsedMvRrn? (chars : List Char) : Option ParsedRrn := do
  let precision ← chars.head?
  let opChars := chars.drop 1
  let op ← match precision, String.ofList opChars with
    | 'd', "fadd" | 'f', "fadd" | 'h', "fadd" => some .fadd
    | 'd', "max" | 'f', "max" | 'h', "max" => some .max
    | 'd', "min" | 'f', "min" | 'h', "min" => some .min
    | 'l', "iadd" | 'i', "iadd" | 's', "iadd" => some .iadd
    | 'l', "band" | 'i', "band" | 's', "band" => some .band
    | 'l', "and" | 'i', "and" | 's', "and" => some .and
    | 'l', "bor" | 'i', "bor" | 's', "bor" => some .bor
    | 'l', "or" | 'i', "or" | 's', "or" => some .or
    | _, _ => none
  pure ⟨precision, op⟩

/-- Decode the MV opcode mode. RRN modes require an exact RRN spelling. -/
def parseParsedMvKind? (mode : String) : Option ParsedMvKind := do
  if mode == "p" then some .copy
  else if mode == "b" then some .broadcast
  else if mode == "b2" then some .broadcast2
  else if mode == "b4" then some .broadcast4
  else if mode == "d" then some .distribute
  else if mode.startsWith "r2" then
    let rrn ← parseParsedMvRrn? ((mode.drop 2).toString.toList)
    some (.reduce2 rrn)
  else if mode.startsWith "r4" then
    let rrn ← parseParsedMvRrn? ((mode.drop 2).toString.toList)
    some (.reduce4 rrn)
  else if mode.startsWith "r" then
    let rrn ← parseParsedMvRrn? ((mode.drop 1).toString.toList)
    some (.reduce rrn)
  else none

inductive ParsedMvOperand where
  | pdm (address : Fin (2 ^ 64)) (group : Option (Fin 256))
  | dram (address : Fin (2 ^ 64)) (group : Option (Fin 256)) (indirect : Bool)
  | l2bm (address : Fin (2 ^ 64)) (group : Option (Fin 256)) (l2b : Option (Fin 256))
  deriving DecidableEq, Repr

def parsedNatToFin? (n bound : Nat) : Option (Fin bound) :=
  if h : n < bound then some ⟨n, h⟩ else none

def parsedMvDigit? (base : Nat) (c : Char) : Option Nat :=
  let code := c.toNat
  if 48 ≤ code && code ≤ 57 then some (code - 48)
  else if base == 16 && 65 ≤ code && code ≤ 70 then some (code - 55)
  else if base == 16 && 97 ≤ code && code ≤ 102 then some (code - 87)
  else none

def parsedMvDigitsPrefix (base : Nat) : List Char → Nat → Option (Nat × List Char)
  | [], value => some (value, [])
  | char :: rest, value =>
      match parsedMvDigit? base char with
      | none => some (value, char :: rest)
      | some digit => parsedMvDigitsPrefix base rest (value * base + digit)

def parsedMvNumberPrefix (chars : List Char) : Option (Nat × List Char) :=
  match chars with
  | '0' :: 'x' :: digits =>
      match digits with
      | first :: _ =>
          if (parsedMvDigit? 16 first).isSome then parsedMvDigitsPrefix 16 digits 0
          else none
      | [] => none
  | first :: _ =>
      if (parsedMvDigit? 10 first).isSome then parsedMvDigitsPrefix 10 chars 0
      else none
  | [] => none

def parsedMvDecimal? (chars : List Char) : Option Nat := do
  let digits := if chars.head? == some '+' then chars.drop 1 else chars
  if digits.isEmpty then none else
  let (value, rest) ← parsedMvDigitsPrefix 10 digits 0
  if rest.isEmpty then some value else none

structure ParsedMvParams where
  size : Option (Fin (2 ^ 64)) := none
  tag : Option (Fin 256) := none
  nd : Option (Fin (2 ^ 32)) := none
  priority : Fin 256 := ⟨0, by decide⟩
  deriving DecidableEq, Repr

/-- Parse MV's concatenated `nd`, `n`, `i`, and `p` parameters. Integer casts
for `nd` and priority intentionally wrap, matching Rust's `as u32`/`as u8`. -/
def parseParsedMvParamsAux : Nat → List Char → ParsedMvParams → Option ParsedMvParams
  | 0, _, _ => none
  | _ + 1, [], params => some params
  | fuel + 1, 'n' :: 'd' :: rest, params => do
      let (value, tail) ← parsedMvNumberPrefix rest
      if value ≥ 2 ^ 64 then none else
        parseParsedMvParamsAux fuel tail { params with nd := some ⟨value % (2 ^ 32), by omega⟩ }
  | fuel + 1, 'n' :: rest, params => do
      let (value, tail) ← parsedMvNumberPrefix rest
      if value ≥ 2 ^ 64 then none else
        parseParsedMvParamsAux fuel tail { params with size := parsedNatToFin? value (2 ^ 64) }
  | fuel + 1, 'p' :: rest, params => do
      let (value, tail) ← parsedMvNumberPrefix rest
      if value ≥ 2 ^ 64 then none else
        parseParsedMvParamsAux fuel tail { params with priority := ⟨value % 256, by omega⟩ }
  | fuel + 1, 'i' :: '+' :: digit :: rest, params => do
      let value ← parsedMvDigit? 16 digit
      parseParsedMvParamsAux fuel rest { params with tag := some ⟨value % 256, Nat.mod_lt _ (by decide)⟩ }
  | fuel + 1, 'i' :: h1 :: h2 :: rest, params => do
      let d1 ← parsedMvDigit? 16 h1
      let d2 ← parsedMvDigit? 16 h2
      if d1 < 16 && d2 < 16 then
        parseParsedMvParamsAux fuel rest { params with tag := some ⟨(d1 * 16 + d2) % 256, Nat.mod_lt _ (by decide)⟩ }
      else none
  | _ + 1, _, _ => none

def parseParsedMvParams? (text : String) : Option ParsedMvParams :=
  parseParsedMvParamsAux (text.length + 1) text.toList {}

def parsedMvOptionalU8? (chars : List Char) : Option (Option (Fin 256)) := do
  if chars.isEmpty then some none else do
    let value ← parsedMvDecimal? chars
    some <$> parsedNatToFin? value 256

def parsedMvGroupSuffix? (chars : List Char) : Option (Option (Fin 256)) := do
  match chars with
  | [] => some none
  | '@' :: group => do
      let value ← parsedMvDecimal? group
      some <$> parsedNatToFin? value 256
  | _ => none

def parseParsedL2bmOperand? (text : String) : Option ParsedMvOperand := do
  let chars := text.toList
  let rest ← match chars with
    | '$' :: 'l' :: 'c' :: rest => some rest
    | _ => none
  let (addressValue, suffix) ← parsedMvNumberPrefix rest
  let (groupChars, l2bChars) ← match suffix with
    | [] => some ([], [])
    | '@' :: selector =>
      match selector.splitOn '.' with
      | [group] => some (group, [])
      | [group, l2b] => some (group, l2b)
      | _ => none
    | _ => none
  let address ← parsedNatToFin? addressValue (2 ^ 64)
  let group ← parsedMvOptionalU8? groupChars
  let l2b ← parsedMvOptionalU8? l2bChars
  pure (.l2bm address group l2b)

def parseParsedMvOperand? (text : String) : Option ParsedMvOperand := do
  match text.toList with
  | '$' :: 'l' :: 'c' :: _ => parseParsedL2bmOperand? text
  | '$' :: 'd' :: 'i' :: rest => do
      let (addressValue, suffix) ← parsedMvNumberPrefix rest
      let address ← parsedNatToFin? addressValue (2 ^ 64)
      let group ← parsedMvGroupSuffix? suffix
      pure (.dram address group true)
  | '$' :: 'd' :: rest => do
      let (addressValue, suffix) ← parsedMvNumberPrefix rest
      let address ← parsedNatToFin? addressValue (2 ^ 64)
      let group ← parsedMvGroupSuffix? suffix
      pure (.dram address group false)
  | '$' :: 'p' :: rest => do
      let (addressValue, suffix) ← parsedMvNumberPrefix rest
      let address ← parsedNatToFin? addressValue (2 ^ 64)
      let group ← parsedMvGroupSuffix? suffix
      pure (.pdm address group)
  | _ => none

theorem parseParsedL2bmOperand_decimal :
    parseParsedL2bmOperand? "$lc42" =
      some (.l2bm ⟨42, by decide⟩ none none) := by decide

theorem parseParsedL2bmOperand_hex_and_selectors :
    parseParsedL2bmOperand? "$lc0x2a@3.1" =
      some (.l2bm ⟨42, by decide⟩ (some ⟨3, by decide⟩) (some ⟨1, by decide⟩)) := by decide

theorem parseParsedL2bmOperand_empty_group_selector :
    parseParsedL2bmOperand? "$lc5@.1" =
      some (.l2bm ⟨5, by decide⟩ none (some ⟨1, by decide⟩)) := by decide

theorem parseParsedL2bmOperand_matches_rust_operand_fixture :
    parseParsedL2bmOperand? "$lc0@2.1" =
      some (.l2bm ⟨0, by decide⟩ (some ⟨2, by decide⟩) (some ⟨1, by decide⟩)) := by decide

theorem parseParsedL2bmOperand_unselected_bank_fixture :
    parseParsedL2bmOperand? "$lc0" =
      some (.l2bm ⟨0, by decide⟩ none none) := by decide

theorem parseParsedL2bmOperand_rejects_u64_overflow :
    parseParsedL2bmOperand? "$lc18446744073709551616" = none := by decide

theorem parseParsedL2bmOperand_rejects_u8_group_overflow :
    parseParsedL2bmOperand? "$lc1@256.0" = none := by decide

theorem parseParsedMvOperand_pdm_fixture :
    parseParsedMvOperand? "$p0@0" =
      some (.pdm ⟨0, by decide⟩ (some ⟨0, by decide⟩)) := by decide

theorem parseParsedMvOperand_indirect_dram_fixture :
    parseParsedMvOperand? "$di512@2" =
      some (.dram ⟨512, by decide⟩ (some ⟨2, by decide⟩) true) := by decide

theorem parseParsedMvOperand_direct_dram_fixture :
    parseParsedMvOperand? "$d0" =
      some (.dram ⟨0, by decide⟩ none false) := by decide

structure ParsedMv where
  kind : ParsedMvKind
  size : Fin (2 ^ 64)
  tag : Option (Fin 256)
  nd : Option (Fin (2 ^ 32))
  priority : Fin 256
  source : Option ParsedMvOperand
  destination : Option ParsedMvOperand
  text : String
  deriving DecidableEq, Repr

/-- Canonical MV syntax without source spelling or whitespace. -/
structure NormalizedMv where
  kind : ParsedMvKind
  size : Fin (2 ^ 64)
  tag : Option (Fin 256)
  nd : Option (Fin (2 ^ 32))
  priority : Fin 256
  source : Option ParsedMvOperand
  destination : Option ParsedMvOperand
  deriving DecidableEq, Repr

def ParsedMv.normalize (transfer : ParsedMv) : NormalizedMv :=
  ⟨transfer.kind, transfer.size, transfer.tag, transfer.nd, transfer.priority,
    transfer.source, transfer.destination⟩

def NormalizedMv.toParsed (transfer : NormalizedMv) : ParsedMv :=
  ⟨transfer.kind, transfer.size, transfer.tag, transfer.nd, transfer.priority,
    transfer.source, transfer.destination, ""⟩

/-- Construct the parsed MV payload from an already tokenized opcode and its
two operand tokens, matching the Rust `Mv` fields and numeric casts. -/
def parsedMvSplitSlashAux : List Char → List Char → Option (List Char × List Char)
  | [], _ => none
  | '/' :: rest, acc => some (acc.reverse, rest)
  | char :: rest, acc => parsedMvSplitSlashAux rest (char :: acc)

def parseParsedMvTokens? (text opcode : String) (operands : List String) : Option ParsedMv := do
  if opcode == "mvnop" then
    some ⟨.nop, ⟨0, by decide⟩, none, none, ⟨0, by decide⟩, none, none, text⟩
  else do
    let (modeChars, parameterChars) ← parsedMvSplitSlashAux opcode.toList []
    let (modeTail, _) ← match modeChars with
      | 'm' :: 'v' :: tail => some (tail, ())
      | _ => none
    let kind ← parseParsedMvKind? (String.ofList modeTail)
    let params ← parseParsedMvParams? (String.ofList parameterChars)
      let size ← params.size
      let (sourceText, destinationText) ← match operands with
        | [source, destination] => some (source, destination)
        | _ => none
      let source ← parseParsedMvOperand? sourceText
      let destination ← parseParsedMvOperand? destinationText
      some ⟨kind, size, params.tag, params.nd, params.priority,
        some source, some destination, text⟩

def parsedMvWhitespace (char : Char) : Bool :=
  char.toNat == 9 || char.toNat == 10 || char.toNat == 11 ||
    char.toNat == 12 || char.toNat == 13 || char.toNat == 32

def parsedMvSplitWhitespaceAux : List Char → List Char → List String → List String
  | [], current, words =>
      if current.isEmpty then words.reverse
      else (String.ofList current.reverse :: words).reverse
  | char :: rest, current, words =>
      if parsedMvWhitespace char then
        let nextWords := if current.isEmpty then words else String.ofList current.reverse :: words
        parsedMvSplitWhitespaceAux rest [] nextWords
      else parsedMvSplitWhitespaceAux rest (char :: current) words

def parsedMvSplitWhitespace (text : String) : List String :=
  parsedMvSplitWhitespaceAux text.toList [] []

/-- Parse a complete MV line, using Rust-compatible ASCII whitespace tokenization. -/
def parseParsedMvLine? (text : String) : Option ParsedMv := do
  match parsedMvSplitWhitespace text with
  | [] => none
  | opcode :: operands => parseParsedMvTokens? text opcode operands

theorem parseParsedMvParams_cast_fixture :
    (parseParsedMvParams? "nd0x100000001n0x20i0Ap257") =
      some ⟨some ⟨32, by decide⟩, some ⟨10, by decide⟩,
        some ⟨1, by decide⟩, ⟨1, by decide⟩⟩ := by decide

theorem parseParsedMvLine_copy_fixture :
    parseParsedMvLine? "  mvp/n2  $p0\t$d1 " =
      some ⟨.copy, ⟨2, by decide⟩, none, none, ⟨0, by decide⟩,
        some (.pdm ⟨0, by decide⟩ none),
        some (.dram ⟨1, by decide⟩ none false), "  mvp/n2  $p0\t$d1 "⟩ := by decide

theorem parseParsedMvParams_rejects_size_overflow :
    parseParsedMvParams? "n18446744073709551616" = none := by decide

theorem parseParsedMvParams_selector_accepts_explicit_plus :
    parsedMvOptionalU8? ['+', '2', '5', '5'] = some (some ⟨255, by decide⟩) := by decide

theorem parseParsedMvParams_tag_accepts_rust_radix_plus :
    parseParsedMvParams? "i+A" =
      some ⟨none, some ⟨10, by decide⟩, none, ⟨0, by decide⟩⟩ := by decide

theorem parseParsedMvLine_accepts_plus_in_u8_operand_group :
    parseParsedMvLine? "mvp/n1 $p0@+1 $d1@+2" =
      some ⟨.copy, ⟨1, by decide⟩, none, none, ⟨0, by decide⟩,
        some (.pdm ⟨0, by decide⟩ (some ⟨1, by decide⟩)),
        some (.dram ⟨1, by decide⟩ (some ⟨2, by decide⟩) false),
        "mvp/n1 $p0@+1 $d1@+2"⟩ := by decide

theorem parseParsedMvLine_nop_ignores_operands_like_rust :
    (parseParsedMvLine? "mvnop ignored tokens") =
      some ⟨.nop, ⟨0, by decide⟩, none, none, ⟨0, by decide⟩,
        none, none, "mvnop ignored tokens"⟩ := by decide

inductive ParsedLine where
  | pe (expressions : List ParsedExpr)
  | nop (count : Nat) (wait : Option Nat)
  | mv (transfer : ParsedMv)
  | maskDirective (widthWords : Nat) (targets : ParsedMaskTargets) (entry : Nat)
  | debugSet
  | debugGet
  | dramSet
  deriving DecidableEq, Repr

/-- A parsed control line is in the mask-directive envelope when it uses an
assembler-supported width and selector. Other lines leave the mask state
unchanged. -/
def ParsedLine.maskDirectiveInFiniteEnvelope : ParsedLine → Prop
  | .maskDirective widthWords _ entry =>
      (widthWords = 2 ∨ widthWords = 4) ∧ entry < 32
  | _ => True

/-- Candidate instruction lines after removing presentation-only fields and
judge-stripped debug/DRAM records. PE expression order is preserved. -/
inductive NormalizedLine where
  | pe (expressions : List NormalizedExpr)
  | nop (count : Nat) (wait : Option Nat)
  | mv (transfer : NormalizedMv)
  | maskDirective (widthWords : Nat) (targets : ParsedMaskTargets) (entry : Nat)
  deriving DecidableEq, Repr

/-- Executable issue words after zero-cost directives are folded into control
state. Nop counts are strictly positive by construction. -/
inductive InstructionLine where
  | pe (expressions : List NormalizedExpr)
  | nop (count : {n : Nat // 0 < n}) (wait : Option Nat)
  | mv (transfer : NormalizedMv)
  deriving DecidableEq, Repr

def InstructionLine.cost : InstructionLine → Nat
  | .pe _ | .mv _ => 1
  | .nop count _ => count.val

theorem InstructionLine.cost_positive (line : InstructionLine) :
    0 < line.cost := by
  cases line with
  | pe _ => change 0 < 1; decide
  | mv _ => change 0 < 1; decide
  | nop count _ => change 0 < count.val; exact count.property


def NormalizedLine.toInstruction? : NormalizedLine → Option InstructionLine
  | .pe expressions => some (.pe expressions)
  | .nop 0 _ => none
  | .nop (count + 1) wait =>
      some (.nop ⟨count + 1, by omega⟩ wait)
  | .mv transfer => some (.mv transfer)
  | .maskDirective .. => none

theorem nop_zero_not_instruction :
    NormalizedLine.toInstruction? (.nop 0 none) = none := rfl

theorem normalized_positive_nop_cost (count : Nat) (wait : Option Nat) :
    (NormalizedLine.toInstruction? (.nop (count + 1) wait)).map
      InstructionLine.cost = some (count + 1) := rfl

def NormalizedLine.toParsed : NormalizedLine → ParsedLine
  | .pe expressions => .pe (expressions.map NormalizedExpr.toParsed)
  | .nop count wait => .nop count wait
  | .mv transfer => .mv transfer.toParsed
  | .maskDirective widthWords targets entry =>
      .maskDirective widthWords targets entry

/-- Normalize source-only records away and erase display strings. `nop/0`
has no emitted instruction word, while `nop/0; wait ...` is rejected by the
assembler, so the zero-count form maps to an empty line sequence. -/
def ParsedLine.normalizeForSubmission? : ParsedLine → Option (List NormalizedLine)
  | .pe expressions => some [.pe (expressions.map ParsedExpr.normalize)]
  | .nop 0 none => some []
  | .nop 0 (some _) => none
  | .nop count wait => some [.nop count wait]
  | .mv transfer => some [.mv transfer.normalize]
  | .maskDirective widthWords targets entry =>
      some [.maskDirective widthWords targets entry]
  | .debugSet | .debugGet | .dramSet => some []

theorem nop_zero_normalizes_empty :
    ParsedLine.normalizeForSubmission? (.nop 0 none) = some [] := rfl

def ParsedLine.issueLegal : ParsedLine → Prop
  | .pe expressions => LegalParsedLine expressions
  | .nop _ _ | .mv _ | .maskDirective _ _ _ | .debugSet | .debugGet | .dramSet => True

noncomputable def checkParsedTopLine : ParsedLine → Bool
  | .pe expressions => checkParsedLine expressions
  | .nop _ _ | .mv _ | .maskDirective _ _ _ | .debugSet | .debugGet | .dramSet => true

theorem parsed_topline_check_sound (line : ParsedLine)
    (accepted : checkParsedTopLine line = true) : line.issueLegal := by
  cases line with
  | pe expressions => exact parsed_check_sound expressions accepted
  | nop _ _ | mv _ | maskDirective _ _ _ | debugSet | debugGet | dramSet => trivial

theorem parsed_topline_check_complete (line : ParsedLine) (legal : line.issueLegal) :
    checkParsedTopLine line = true := by
  cases line with
  | pe expressions => exact parsed_check_complete expressions legal
  | nop _ _ | mv _ | maskDirective _ _ _ | debugSet | debugGet | dramSet => rfl

/-- Non-directive source lines retain mask state; directive lines replace it,
matching `Sim::exec`'s zero-cost state update. -/
def ParsedLine.updateMaskState (line : ParsedLine) (state : ParsedMaskDirective) :
    ParsedMaskDirective :=
  match line with
  | .maskDirective widthWords targets entry => ⟨widthWords, targets, entry⟩
  | _ => state

theorem mask_directive_replaces_state (widthWords : Nat) (targets : ParsedMaskTargets)
    (entry : Nat) (state : ParsedMaskDirective) :
    ParsedLine.updateMaskState (.maskDirective widthWords targets entry) state =
      ⟨widthWords, targets, entry⟩ := rfl

theorem ordinary_line_preserves_mask_state (state : ParsedMaskDirective) :
    ParsedLine.updateMaskState (.nop 1 none) state = state := rfl

def plusOneRead : ParsedOperand :=
  .mem ⟨.lm0, ⟨2, 0, 0, 0, 0, false, none⟩⟩ false false false none

def plusOneWrite : ParsedOperand :=
  .mem ⟨.lm1, ⟨2, 0, 0, 0, 0, false, none⟩⟩ false false false none

def plusOneParsed : ParsedExpr where
  op := .alu .inc (some .i) false none
  sources := [plusOneRead]
  destinations := [plusOneWrite]
  flush := none
  text := "iinc $lm0v $ln0v"

def parsedVectorFma : ParsedExpr where
  op := .mau .f false .fma none false
  sources := [.fixed .msb1, .fixed .peid]
  destinations := [.nowrite]
  flush := none
  text := "fvfma ..."

def parsedMatrixWrite : ParsedExpr where
  op := .matrixWrite .f
  sources := [.fixed .l1bid]
  destinations := [.matrix false 2 none]
  flush := none
  text := "fmwrite ..."

theorem plusOne_issue_legal : LegalParsedLine [plusOneParsed] := by
  unfold LegalParsedLine projectLine projectFrom ParsedExpr.toIssueExpr
    ParsedExpr.issueGroup ParsedExpr.issueMau ParsedOperand.accesses
    ParsedOperand.matrixUseCount ParsedExpr.hasTurnaround
    ParsedExpr.maskApplications ParsedOperand.writeMask?
    plusOneParsed plusOneRead plusOneWrite
  simp [Legal, idsUnique, groupsUnique, mauCountBounded, mauExpressions,
    mauPrecisionsAgree, matrixWritePairAgrees, matrixRegistersUnique,
    writesUnique, readsAgree, localReadWriteAgree, immediateExcludesLm0,
    zeroFlushUnique, maskWidthsAgree, maskEntriesAgree, projectFrom]

theorem plusOne_issue_accepts : checkParsedLine [plusOneParsed] = true :=
  parsed_check_complete [plusOneParsed] plusOne_issue_legal

theorem mismatched_fma_matrix_write_rejected :
    checkParsedLine [parsedVectorFma, parsedMatrixWrite] = false := by
  classical
  unfold checkParsedLine check
  apply decide_eq_false_iff_not.mpr
  intro legal
  have pairRule := legal.2.2.2.2.1
  simp [matrixWritePairAgrees, mauExpressions, ParsedExpr.toIssueExpr,
    ParsedExpr.issueGroup, ParsedExpr.issueMau, ParsedOperand.accesses,
    ParsedOperand.matrixUseCount, parsedVectorFma,
    parsedMatrixWrite, projectLine, projectFrom, vectorFmaOrMul,
    matrixWriteKind] at pairRule

theorem l1bm_turnaround_group :
    ({ op := ParsedOp.l1bm .pbcast, sources := [.l1bm 2 none], destinations := [],
       flush := none, text := "" } : ParsedExpr).issueGroup = some .l1bmTurnaround := rfl

theorem other_memory_banks_remain_distinct :
    Bank.l1bm ≠ Bank.l2bm ∧ Bank.pdm ≠ Bank.dram := by decide

end ProofsLean.MNCore.Issue
