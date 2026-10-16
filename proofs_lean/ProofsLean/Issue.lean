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

/-- Structural mirror of operand variants in `viz/core/src/vsm.rs`. -/
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
  | raw (text : String)
  deriving DecidableEq, Repr

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
  zeroFlushUnique xs

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
  immediate := false
  zeroFlush := false

theorem empty_is_legal : Legal [] := by
  simp [Legal, idsUnique, groupsUnique, mauCountBounded, mauExpressions,
    mauPrecisionsAgree, matrixWritePairAgrees, matrixRegistersUnique,
    writesUnique, readsAgree, localReadWriteAgree, immediateExcludesLm0,
    zeroFlushUnique]

theorem empty_check_accepts : check [] = true := check_complete [] empty_is_legal

def aluExpr (id : Nat) : Expr := { emptyExpr with id := id, group := some .alu }

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
  | other (text : String)
  deriving DecidableEq, Repr

/-- Structural PE-expression AST mirror. Issue and execution interpretations
are separate functions over this syntax. -/
structure ParsedExpr where
  op : ParsedOp
  sources : List ParsedOperand
  destinations : List ParsedOperand
  flush : Option ParsedMask
  text : String
  deriving DecidableEq, Repr

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
  | .other _ => none

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

def LegalParsedLine (expressions : List ParsedExpr) : Prop := Legal (projectLine expressions)

noncomputable def checkParsedLine (expressions : List ParsedExpr) : Bool :=
  check (projectLine expressions)

theorem parsed_check_sound (expressions : List ParsedExpr)
    (accepted : checkParsedLine expressions = true) : LegalParsedLine expressions := by
  exact check_sound (projectLine expressions) accepted

theorem parsed_check_complete (expressions : List ParsedExpr)
    (legal : LegalParsedLine expressions) : checkParsedLine expressions = true := by
  exact check_complete (projectLine expressions) legal

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
  if chars.isEmpty then none else
  let (value, rest) ← parsedMvDigitsPrefix 10 chars 0
  if rest.isEmpty then some value else none

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

inductive ParsedLine where
  | pe (expressions : List ParsedExpr)
  | nop (count : Nat) (wait : Option Nat)
  | mv (transfer : ParsedMv)
  | maskDirective (widthWords : Nat) (targets : ParsedMaskTargets) (entry : Nat)
  | debugSet
  | debugGet
  | dramSet
  deriving DecidableEq, Repr

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
    plusOneParsed plusOneRead plusOneWrite
  simp [Legal, idsUnique, groupsUnique, mauCountBounded, mauExpressions,
    mauPrecisionsAgree, matrixWritePairAgrees, matrixRegistersUnique,
    writesUnique, readsAgree, localReadWriteAgree, immediateExcludesLm0,
    zeroFlushUnique, projectFrom]

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
