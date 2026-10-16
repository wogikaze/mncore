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

theorem supported_integer_opcode_has_mapping (name : ParsedAluName)
    (precision : ParsedPrecision) (unsigned : Bool)
    (supported : name.supportsIntegerAt precision = true) :
    ∃ op, name.toIntegerOp unsigned = some op := by
  cases name <;> cases precision <;>
    simp [ParsedAluName.supportsIntegerAt, ParsedAluName.toIntegerOp] at supported ⊢

def evaluateParsedIntegerAlu (op : ParsedOp) (x y : IntegerALU.Bus)
    (reduced : Bool) : StepResult IntegerALU.BusResult :=
  match op.integerRequest with
  | .ok request => IntegerALU.partialEvaluate request x y reduced
  | .failure => .failure
  | .unknown => .unknown

theorem parsed_integer_evaluation_uses_requested_semantics (op : ParsedOp)
    (request : IntegerALU.Request) (selected : op.integerRequest = .ok request)
    (x y : IntegerALU.Bus) (reduced : Bool) :
    evaluateParsedIntegerAlu op x y reduced =
      IntegerALU.partialEvaluate request x y reduced := by
  simp [evaluateParsedIntegerAlu, selected]

theorem unsupported_parsed_integer_is_unknown (op : ParsedOp)
    (unsupported : op.integerRequest = .unknown) (x y : IntegerALU.Bus)
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
inductive ParsedLine where
  | pe (expressions : List ParsedExpr)
  | nop (count : Nat) (wait : Option Nat)
  | mv
  | maskDirective
  | debugSet
  | debugGet
  | dramSet
  deriving DecidableEq, Repr

def ParsedLine.issueLegal : ParsedLine → Prop
  | .pe expressions => LegalParsedLine expressions
  | .nop _ _ | .mv | .maskDirective | .debugSet | .debugGet | .dramSet => True

noncomputable def checkParsedTopLine : ParsedLine → Bool
  | .pe expressions => checkParsedLine expressions
  | .nop _ _ | .mv | .maskDirective | .debugSet | .debugGet | .dramSet => true

theorem parsed_topline_check_sound (line : ParsedLine)
    (accepted : checkParsedTopLine line = true) : line.issueLegal := by
  cases line with
  | pe expressions => exact parsed_check_sound expressions accepted
  | nop _ _ | mv | maskDirective | debugSet | debugGet | dramSet => trivial

theorem parsed_topline_check_complete (line : ParsedLine) (legal : line.issueLegal) :
    checkParsedTopLine line = true := by
  cases line with
  | pe expressions => exact parsed_check_complete expressions legal
  | nop _ _ | mv | maskDirective | debugSet | debugGet | dramSet => rfl

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
