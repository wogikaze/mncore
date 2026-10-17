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
  (r.width = 1 ∨ r.width = 2 ∨ r.width = 4) ∧
  r.address0 < 4096 ∧ r.address1 < 4096 ∧
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
  | entry (longLong : Bool) (index : Fin 256)
  deriving DecidableEq, Repr

def ParsedMask.isDoubleLong : ParsedMask → Bool
  | .pattern longLong _ | .entry longLong _ => longLong

def ParsedMask.variableEntry? : ParsedMask → Option Nat
  | .entry _ index => some index.val
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

/-- Fixed identifiers and forwarding values are source-only operand roles.
This coarse screen is necessary, but not sufficient, for destination validity. -/
def ParsedOperand.notKnownSourceOnly : ParsedOperand → Prop
  | .fixed .. | .forward .. => False
  | _ => True

theorem ParsedOperand.fixed_notKnownSourceOnly (kind : ParsedFixed) :
    ¬ ParsedOperand.notKnownSourceOnly (.fixed kind) := by
  simp [notKnownSourceOnly]

theorem ParsedOperand.forward_notKnownSourceOnly (kind : ParsedForward) (neg ext rnd : Bool) :
    ¬ ParsedOperand.notKnownSourceOnly (.forward kind neg ext rnd) := by
  simp [notKnownSourceOnly]

def ParsedOperand.destinationsAvoidKnownSourceOnly (operands : List ParsedOperand) : Prop :=
  ∀ operand ∈ operands, operand.notKnownSourceOnly

def ParsedOperand.scalarPEDestinationRole : ParsedOperand → Prop
  | .mem .. | .bar .. | .omr .. | .nowrite => True
  | _ => False

def ParsedOperand.matrixReadDestinationRole : ParsedOperand → Prop
  | .mem .. | .bar .. | .nowrite => True
  | _ => False

def ParsedOperand.l1bmDestinationRole : ParsedOperand → Prop
  | .l1bm .. => True
  | _ => False

def ParsedOperand.l1bmToPEDestinationRole : ParsedOperand → Prop
  | .mem .. | .bar .. | .nowrite => True
  | _ => False

def ParsedOperand.l2bmDestinationRole : ParsedOperand → Prop
  | .l2bm .. => True
  | _ => False

def ParsedOperand.darDestinationRole : ParsedOperand → Prop
  | .dar .. => True
  | _ => False

def ParsedOperand.l2bmSourceRole : ParsedOperand → Prop
  | .l2bm .. => True
  | _ => False

def ParsedOperand.l1bmSourceRole : ParsedOperand → Prop
  | .l1bm .. => True
  | _ => False

/-- PE memory, forwarding values, accepted as sources of L1BM transfers.
Base-address, mask, matrix, block-memory, fixed-ID, and DAR operands are not
L1BM transfer sources. -/
def ParsedOperand.peSourceRole : ParsedOperand → Prop
  | .mem access .. =>
      access.bank = .grf0 ∨ access.bank = .grf1 ∨ access.bank = .lm0 ∨
        access.bank = .lm1 ∨ access.bank = .t
  | .forward .. => True
  | _ => False

def ParsedOperand.isMreadf : ParsedOperand → Bool
  | .forward .mreadf .. => true
  | _ => false

def ParsedOperand.writeMask? : ParsedOperand → Option ParsedMask
  | .mem _ _ _ _ mask | .bar _ _ mask | .omr _ mask => mask
  | _ => none

def ParsedOperand.maskRegisterWrite? : ParsedOperand → Option Nat
  | .omr entry _ => some entry
  | _ => none

def ParsedOperand.barWriteBank? : ParsedOperand → Option Bank
  | .bar lm1 .. => some (if lm1 then .lm1 else .lm0)
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
  barWrites : List Bank
  omrWrites : List Nat
  lbfWrites : Nat
  nowriteOutputValid : Bool
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

def Expr.writeBanks (e : Expr) : List Bank :=
  e.writes.map Access.bank ++ e.barWrites

def writesUnique (xs : List Expr) : Prop :=
  (∀ e ∈ xs, e.writeBanks.Nodup) ∧
  (∀ e ∈ xs, ∀ f ∈ xs, ∀ bank ∈ e.writeBanks, ∀ other ∈ f.writeBanks,
    e.id ≠ f.id → bank = other → False)

def barWritesExcludeReads (xs : List Expr) : Prop :=
  ∀ e ∈ xs, ∀ f ∈ xs, ∀ bank ∈ e.barWrites, ∀ access ∈ f.reads,
    bank = access.bank → False

def nowriteOutputsUnique (xs : List Expr) : Prop :=
  ∀ e ∈ xs, e.nowriteOutputValid = true

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

/-- Mask-flag reads in one issue step use the same PE read width. -/
def maskWidthsAgree (xs : List Expr) : Prop :=
  let widths := (xs.flatMap Expr.maskApplications).map ParsedMask.isDoubleLong
  match widths with
  | [] => True
  | first :: rest => ∀ width ∈ rest, width = first

/-- Variable mask-flag reads in one issue step use the same OMR entry.
This is the mask-register part of SDM 3.6.4's shared-read-region rule. -/
def maskEntriesAgree (xs : List Expr) : Prop :=
  let entries := (xs.flatMap Expr.maskApplications).filterMap ParsedMask.variableEntry?
  match entries with
  | [] => True
  | first :: rest => ∀ entry ∈ rest, entry = first

def maskRegisterWritesUnique (xs : List Expr) : Prop :=
  (xs.flatMap Expr.omrWrites).length ≤ 1

def lbfWritesUnique (xs : List Expr) : Prop :=
  (xs.map Expr.lbfWrites).sum ≤ 1

/-- The explicit constraints enforced in the local PE issue checker. -/
def Legal (xs : List Expr) : Prop :=
  idsUnique xs ∧
  groupsUnique xs ∧
  mauCountBounded xs ∧
  mauPrecisionsAgree xs ∧
  matrixWritePairAgrees xs ∧
  matrixRegistersUnique xs ∧
  writesUnique xs ∧
  barWritesExcludeReads xs ∧
  readsAgree xs ∧
  localReadWriteAgree xs ∧
  immediateExcludesLm0 xs ∧
  zeroFlushUnique xs ∧
  maskWidthsAgree xs ∧
  maskEntriesAgree xs ∧
  nowriteOutputsUnique xs ∧
  lbfWritesUnique xs ∧
  maskRegisterWritesUnique xs

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
  barWrites := []
  omrWrites := []
  lbfWrites := 0
  nowriteOutputValid := true
  matrixXUses := 0
  matrixYUses := 0
  maskApplications := []
  immediate := false
  zeroFlush := false

theorem empty_is_legal : Legal [] := by
  simp [Legal, idsUnique, groupsUnique, mauCountBounded, mauExpressions,
    mauPrecisionsAgree, matrixWritePairAgrees, matrixRegistersUnique,
    writesUnique, Expr.writeBanks, barWritesExcludeReads, readsAgree, localReadWriteAgree, immediateExcludesLm0,
    zeroFlushUnique, maskWidthsAgree, maskEntriesAgree, nowriteOutputsUnique,
    lbfWritesUnique,
    maskRegisterWritesUnique]

theorem empty_check_accepts : check [] = true := check_complete [] empty_is_legal

def aluExpr (id : Nat) : Expr := { emptyExpr with id := id, group := some .alu }

def maskIssueExpr (id : Nat) (group : Group) (mask : ParsedMask) : Expr :=
  { emptyExpr with id := id, group := some group, maskApplications := [mask] }

theorem conflicting_mask_widths_are_illegal :
    ¬ Legal [maskIssueExpr 0 .alu (.entry false 1),
      maskIssueExpr 1 .l1bm (.entry true 1)] := by
  intro legal
  rcases legal with ⟨_, _, _, _, _, _, _, _, _, _, _, _, widths, _⟩
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
  rcases legal with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, entries⟩
  simp [maskEntriesAgree, maskIssueExpr, emptyExpr, ParsedMask.variableEntry?] at entries

theorem conflicting_mask_entries_rejected :
    check [maskIssueExpr 0 .alu (.entry false 1),
      maskIssueExpr 1 .l1bm (.entry false 2)] = false := by
  classical
  apply decide_eq_false_iff_not.mpr
  exact conflicting_mask_entries_are_illegal

def maskWriteIssueExpr (id : Nat) (group : Group) (entry : Nat) : Expr :=
  { emptyExpr with id := id, group := some group, omrWrites := [entry] }

def barWriteIssueExpr (id : Nat) (group : Group) (bank : Bank) : Expr :=
  { emptyExpr with id := id, group := some group, barWrites := [bank] }

def memoryReadIssueExpr (id : Nat) (group : Group) (bank : Bank) : Expr :=
  { emptyExpr with
    id := id
    group := some group
    reads := [{ bank := bank, region := { width := 1, address0 := 0, address1 := 0, address2 := 0, address3 := 0, tIndirect := false, madpe := none } }] }

theorem base_address_write_conflicts_with_same_bank_read :
    ¬ Legal [barWriteIssueExpr 0 .alu .lm0, memoryReadIssueExpr 1 .mauCalc .lm0] := by
  intro legal
  rcases legal with ⟨_, _, _, _, _, _, _, conflict, _, _, _, _, _, _, _, _, _⟩
  simp [barWritesExcludeReads, barWriteIssueExpr, memoryReadIssueExpr, emptyExpr] at conflict

def lbfWriteIssueExpr (id : Nat) (group : Group) : Expr :=
  { emptyExpr with id := id, group := some group, lbfWrites := 1 }

def invalidNowriteIssueExpr (id : Nat) : Expr :=
  { emptyExpr with id := id, group := some .alu, nowriteOutputValid := false }

theorem nowrite_with_other_destination_is_illegal :
    ¬ Legal [invalidNowriteIssueExpr 0] := by
  intro legal
  rcases legal with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, valid, _, _⟩
  simp [nowriteOutputsUnique, invalidNowriteIssueExpr, emptyExpr] at valid

def duplicateMemWriteIssueExpr : Expr :=
  { emptyExpr with
    id := 0
    group := some .alu
    writes := [⟨.lm0, ⟨1, 0, 0, 0, 0, false, none⟩⟩,
      ⟨.lm0, ⟨1, 2, 2, 2, 2, false, none⟩⟩] }

theorem duplicate_memory_destination_bank_is_illegal :
    ¬ Legal [duplicateMemWriteIssueExpr] := by
  intro legal
  rcases legal with ⟨_, _, _, _, _, _, writes, _, _, _, _, _, _, _, _, _, _⟩
  simp [writesUnique, Expr.writeBanks, duplicateMemWriteIssueExpr, emptyExpr] at writes

theorem duplicate_lbf_writes_are_illegal :
    ¬ Legal [lbfWriteIssueExpr 0 .l1bm, lbfWriteIssueExpr 1 .l1bmTurnaround] := by
  intro legal
  rcases legal with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, writes, _⟩
  simp [lbfWritesUnique, lbfWriteIssueExpr, emptyExpr] at writes

theorem duplicate_lbf_writes_rejected :
    check [lbfWriteIssueExpr 0 .l1bm, lbfWriteIssueExpr 1 .l1bmTurnaround] = false := by
  classical
  apply decide_eq_false_iff_not.mpr
  exact duplicate_lbf_writes_are_illegal

theorem duplicate_mask_register_writes_are_illegal :
    ¬ Legal [maskWriteIssueExpr 0 .mauCalc 1, maskWriteIssueExpr 1 .alu 1] := by
  intro legal
  rcases legal with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, writes⟩
  simp [maskRegisterWritesUnique, maskWriteIssueExpr, emptyExpr] at writes

theorem duplicate_mask_register_writes_rejected :
    check [maskWriteIssueExpr 0 .mauCalc 1, maskWriteIssueExpr 1 .alu 2] = false := by
  classical
  apply decide_eq_false_iff_not.mpr
  intro legal
  rcases legal with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, writes⟩
  simp [maskRegisterWritesUnique, maskWriteIssueExpr, emptyExpr] at writes

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
  precision : {precision : Char // precision.toNat < 128}
  op : ParsedRrnOp
  deriving DecidableEq, Repr

structure ParsedL1bSet where
  mask : Nat
  immode : Nat
  deriving DecidableEq, Repr

/-- Parsed L1B selectors are an 8-bit membership bitmap and a 3-bit mode. -/
def ParsedL1bSet.inFiniteEnvelope (set : ParsedL1bSet) : Prop :=
  set.mask < 256 ∧ set.immode < 8

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
      (unsigned : Bool) (arg : Option (Fin 256))
  | immediate (value : BitVec 32) (unsigned : Bool)
  | zero
  | mau (precision : ParsedPrecision) (matrix : Bool) (kind : CalcKind)
      (half : Option Char) (round : Bool)
  | matrixWrite (precision : ParsedPrecision)
  | matrixRead (precision : ParsedPrecision)
  | wait (tag : Fin 256)
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
  | .l1bm .. | .l2bm .dars => 1
  | .l2bm .darw => 0
  | .l2bm _ => 1

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
  | l2bm operation =>
      cases operation <;> simp [ParsedOp.parserSourceLimit] <;> omega

/-- Opcode-class destination-role screen based on the assembler probes and
Rust operand roles. It is a necessary filter only; block-memory roles and
complete per-opcode acceptance remain to be modeled. -/
def ParsedOp.destinationRoleScreen : ParsedOp → List ParsedOperand → ParsedOperand → Prop
  | .alu .., _, operand => operand.scalarPEDestinationRole
  | .immediate .., _, operand => operand.scalarPEDestinationRole
  | .zero, _, operand => operand.scalarPEDestinationRole
  | .mau .., _, operand => operand.scalarPEDestinationRole
  | .matrixWrite .., _, .matrix .. => True
  | .matrixWrite .., _, _ => False
  | .matrixRead .., _, operand => operand.matrixReadDestinationRole
  | .l1bm operation, sources, operand =>
      match operation with
      | .mwrite _ | .m4write _ | .reduce .. | .reduce4 .. | .gather _ =>
          operand.l1bmDestinationRole
      | .distrib _ => operand.l1bmToPEDestinationRole
      | .pbcast | .mbcast | .m4bcast =>
          match sources with
          | .l1bm .. :: _ => operand.l1bmToPEDestinationRole
          | _ => operand.l1bmDestinationRole
  | .l2bm operation, _, operand =>
      match operation with
      | .bcast .. | .bcast2 .. | .distrib .. | .imcast .. =>
          operand.l1bmDestinationRole
      | .fromL1b .. | .reduce .. | .reduce2 .. | .gather =>
          operand.l2bmDestinationRole
      | .dars => operand.darDestinationRole
      | .darw => False
  | .wait .., _, _ => False
  | .noforward, _, _ => False

theorem ParsedOp.l1bm_broadcast_from_l1bm_to_pe_role :
    ParsedOp.destinationRoleScreen (.l1bm .mbcast)
      [.l1bm 2 (some 0)] (.bar false 1 none) := by
  simp [ParsedOp.destinationRoleScreen, ParsedOperand.l1bmDestinationRole,
    ParsedOperand.l1bmToPEDestinationRole]

theorem ParsedOp.l1bm_mwrite_pe_to_l1bm_role (mab : Nat) :
    ParsedOp.destinationRoleScreen (.l1bm (.mwrite mab))
      [.forward .mauf false false false] (.l1bm 2 (some 0)) := by
  simp [ParsedOp.destinationRoleScreen, ParsedOperand.l1bmDestinationRole]

theorem ParsedOp.l1bm_distrib_l1bm_to_pe_role (mabdiff : Int) :
    ParsedOp.destinationRoleScreen (.l1bm (.distrib mabdiff))
      [.l1bm 2 (some 0)] (.mem ⟨.lm0, ⟨1, 0, 0, 0, 0, false, none⟩⟩
        false false false none) := by
  simp [ParsedOp.destinationRoleScreen, ParsedOperand.l1bmToPEDestinationRole]

theorem ParsedOp.l1bm_gather_pe_to_l1bm_role (mabdiff : Int) :
    ParsedOp.destinationRoleScreen (.l1bm (.gather mabdiff))
      [.mem ⟨.lm0, ⟨1, 0, 0, 0, 0, false, none⟩⟩ false false false none]
      (.l1bm 2 (some 0)) := by
  simp [ParsedOp.destinationRoleScreen, ParsedOperand.l1bmDestinationRole]

theorem ParsedOp.l2bm_broadcast_to_l1bm_role (set : ParsedL1bSet) :
    ParsedOp.destinationRoleScreen (.l2bm (.bcast set))
      [.l2bm 0 none] (.l1bm 2 (some 0)) := by
  simp [ParsedOp.destinationRoleScreen, ParsedOperand.l1bmDestinationRole]

theorem ParsedOp.l2bm_gather_to_l2bm_role :
    ParsedOp.destinationRoleScreen (.l2bm .gather)
      [.l1bm 2 (some 0)] (.l2bm 0 none) := by
  simp [ParsedOp.destinationRoleScreen, ParsedOperand.l2bmDestinationRole]

theorem ParsedOp.l2bm_multicast_l1bm_role (set : ParsedL1bSet) :
    ParsedOp.destinationRoleScreen (.l2bm (.imcast set))
      [.l1bm 2 (some 0)] (.l1bm 2 (some 16)) := by
  simp [ParsedOp.destinationRoleScreen, ParsedOperand.l1bmDestinationRole]

theorem ParsedOp.l2bm_dars_writes_dar_role :
    ParsedOp.destinationRoleScreen (.l2bm .dars) [.l2bm 1024 (some 0)] (.dar 0) := by
  simp [ParsedOp.destinationRoleScreen, ParsedOperand.darDestinationRole]

theorem ParsedOp.l2bm_dars_rejects_l2bm_destination :
    ¬ ParsedOp.destinationRoleScreen (.l2bm .dars) [.l2bm 1024 (some 0)]
      (.l2bm 0 none) := by
  simp [ParsedOp.destinationRoleScreen, ParsedOperand.darDestinationRole]

theorem ParsedOp.l2bm_darw_has_no_destination_role (operand : ParsedOperand) :
    ¬ ParsedOp.destinationRoleScreen (.l2bm .darw) [] operand := by
  simp [ParsedOp.destinationRoleScreen]

def ParsedOp.sourceRoleScreen : ParsedOp → List ParsedOperand → ParsedOperand → Prop
  | .l1bm operation, _, operand =>
      match operation with
      | .pbcast | .mbcast | .m4bcast | .distrib _ => operand.l1bmSourceRole
      | .mwrite _ | .m4write _ | .reduce .. | .reduce4 .. | .gather _ =>
          operand.peSourceRole
  | .l2bm operation, _, operand =>
      match operation with
      | .bcast .. | .bcast2 .. | .distrib .. | .dars => operand.l2bmSourceRole
      | .fromL1b .. | .reduce .. | .reduce2 .. | .gather | .imcast .. =>
          operand.l1bmSourceRole
      | .darw => False
  | _, _, _ => True

/-- SDM 3.6.1.18 permits `$mreadf` only at source position zero of an ALU
expression. Other forwarding operands have no such position restriction. -/
def ParsedOp.forwardingSourcePositionsValid (op : ParsedOp)
    (sources : List ParsedOperand) : Prop :=
  match op with
  | .alu .. => ∀ operand ∈ sources.drop 1, operand.isMreadf = false
  | _ => ∀ operand ∈ sources, operand.isMreadf = false

theorem ParsedOp.mreadf_at_first_alu_source_is_valid :
    ParsedOp.forwardingSourcePositionsValid (.alu .add none false none)
      [.forward .mreadf false false false, .mem ⟨.lm0, ⟨1, 0, 0, 0, 0, false, none⟩⟩ false false false none] := by
  simp [ParsedOp.forwardingSourcePositionsValid, ParsedOperand.isMreadf]

theorem ParsedOp.mreadf_at_second_alu_source_is_invalid :
    ¬ ParsedOp.forwardingSourcePositionsValid (.alu .add none false none)
      [.mem ⟨.lm0, ⟨1, 0, 0, 0, 0, false, none⟩⟩ false false false none,
       .forward .mreadf false false false] := by
  simp [ParsedOp.forwardingSourcePositionsValid, ParsedOperand.isMreadf]

theorem ParsedOp.mreadf_non_alu_source_is_invalid :
    ¬ ParsedOp.forwardingSourcePositionsValid (.l1bm (.reduce
      ⟨⟨'f', by decide⟩, .fadd⟩ false)) [.forward .mreadf false false false] := by
  simp [ParsedOp.forwardingSourcePositionsValid, ParsedOperand.isMreadf]

theorem ParsedOp.l2bm_dars_source_role (operand : ParsedOperand) :
    ParsedOp.sourceRoleScreen (.l2bm .dars) [] operand = operand.l2bmSourceRole := rfl

theorem ParsedOp.l2bm_broadcast_source_role (set : ParsedL1bSet) :
    ParsedOp.sourceRoleScreen (.l2bm (.bcast set)) [] (.l2bm 0 none) := by
  simp [ParsedOp.sourceRoleScreen, ParsedOperand.l2bmSourceRole]

theorem ParsedOp.l2bm_broadcast_rejects_l1bm_source (set : ParsedL1bSet) :
    ¬ ParsedOp.sourceRoleScreen (.l2bm (.bcast set)) [] (.l1bm 2 (some 0)) := by
  simp [ParsedOp.sourceRoleScreen, ParsedOperand.l2bmSourceRole]

theorem ParsedOp.l2bm_from_l1b_source_role (index : Nat) :
    ParsedOp.sourceRoleScreen (.l2bm (.fromL1b index)) [] (.l1bm 2 (some 0)) := by
  simp [ParsedOp.sourceRoleScreen, ParsedOperand.l1bmSourceRole]

theorem ParsedOp.l2bm_from_l1b_rejects_l2bm_source (index : Nat) :
    ¬ ParsedOp.sourceRoleScreen (.l2bm (.fromL1b index)) [] (.l2bm 0 none) := by
  simp [ParsedOp.sourceRoleScreen, ParsedOperand.l1bmSourceRole]

theorem ParsedOp.l2bm_reduce_source_role (rrn : ParsedRrn) (set : ParsedL1bSet) :
    ParsedOp.sourceRoleScreen (.l2bm (.reduce rrn set)) [] (.l1bm 2 (some 0)) := by
  simp [ParsedOp.sourceRoleScreen, ParsedOperand.l1bmSourceRole]

theorem ParsedOp.l2bm_multicast_source_role (set : ParsedL1bSet) :
    ParsedOp.sourceRoleScreen (.l2bm (.imcast set)) [] (.l1bm 2 (some 0)) := by
  simp [ParsedOp.sourceRoleScreen, ParsedOperand.l1bmSourceRole]

theorem ParsedOp.l2bm_multicast_rejects_l2bm_source (set : ParsedL1bSet) :
    ¬ ParsedOp.sourceRoleScreen (.l2bm (.imcast set)) [] (.l2bm 0 none) := by
  simp [ParsedOp.sourceRoleScreen, ParsedOperand.l1bmSourceRole]

theorem ParsedOp.l1bm_mwrite_pe_source (mab : Nat) (operand : ParsedOperand)
    (role : operand.peSourceRole) :
    ParsedOp.sourceRoleScreen (.l1bm (.mwrite mab)) [] operand := by
  exact role

theorem ParsedOp.l1bm_mwrite_rejects_l1bm_source (mab width : Nat)
    (address : Option Nat) :
    ¬ ParsedOp.sourceRoleScreen (.l1bm (.mwrite mab)) [] (.l1bm width address) := by
  simp [ParsedOp.sourceRoleScreen, ParsedOperand.peSourceRole]

theorem ParsedOp.l1bm_mwrite_rejects_base_address_source (mab : Nat)
    (lm1 : Bool) (width : Nat) (mask : Option ParsedMask) :
    ¬ ParsedOp.sourceRoleScreen (.l1bm (.mwrite mab)) [] (.bar lm1 width mask) := by
  simp [ParsedOp.sourceRoleScreen, ParsedOperand.peSourceRole]

theorem ParsedOp.l1bm_distrib_l1bm_source (offset : Int) (width : Nat)
    (address : Option Nat) :
    ParsedOp.sourceRoleScreen (.l1bm (.distrib offset)) [] (.l1bm width address) := by
  simp [ParsedOp.sourceRoleScreen, ParsedOperand.l1bmSourceRole]

theorem ParsedOp.l1bm_distrib_rejects_pe_source (offset : Int)
    (operand : ParsedOperand) (role : ¬ operand.l1bmSourceRole) :
    ¬ ParsedOp.sourceRoleScreen (.l1bm (.distrib offset)) [] operand := by
  simpa [ParsedOp.sourceRoleScreen] using role

theorem ParsedOp.l1bm_broadcast_l1bm_source (operation : ParsedL1Op)
    (isBroadcast : operation = .pbcast ∨ operation = .mbcast ∨ operation = .m4bcast)
    (width : Nat) (address : Option Nat) :
    ParsedOp.sourceRoleScreen (.l1bm operation) [.l1bm width address]
      (.l1bm width address) := by
  rcases isBroadcast with h | h | h <;> simp [ParsedOp.sourceRoleScreen, h,
    ParsedOperand.l1bmSourceRole]

theorem ParsedOp.l1bm_broadcast_rejects_pe_source
    (operation : ParsedL1Op)
    (isBroadcast : operation = .pbcast ∨ operation = .mbcast ∨ operation = .m4bcast)
    (width : Nat) (address : Option Nat) :
    ¬ ParsedOp.sourceRoleScreen (.l1bm operation) [.l1bm width address]
      (.mem ⟨.lm0, ⟨1, 0, 0, 0, 0, false, none⟩⟩ false false false none) := by
  rcases isBroadcast with h | h | h <;> simp [ParsedOp.sourceRoleScreen, h,
    ParsedOperand.l1bmSourceRole]

/-- Structural PE-expression AST mirror. Issue and execution interpretations
are separate functions over this syntax. -/
structure ParsedExpr where
  op : ParsedOp
  sources : List ParsedOperand
  destinations : List ParsedOperand
  flush : Option ParsedMask
  text : String
  deriving DecidableEq, Repr

def ParsedExpr.destinationsPassRoleScreen (expression : ParsedExpr) : Prop :=
  ∀ operand ∈ expression.destinations,
    expression.op.destinationRoleScreen expression.sources operand

def ParsedExpr.sourcesPassRoleScreen (expression : ParsedExpr) : Prop :=
  ∀ operand ∈ expression.sources,
    expression.op.sourceRoleScreen expression.sources operand

def ParsedExpr.forwardingSourcePositionsValid (expression : ParsedExpr) : Prop :=
  expression.op.forwardingSourcePositionsValid expression.sources

def ParsedExpr.maskApplications (expression : ParsedExpr) : List ParsedMask :=
  (expression.sources ++ expression.destinations).filterMap ParsedOperand.writeMask? ++
    expression.flush.toList

def ParsedExpr.maskRegisterWrites (expression : ParsedExpr) : List Nat :=
  expression.destinations.filterMap ParsedOperand.maskRegisterWrite?

def ParsedExpr.barWrites (expression : ParsedExpr) : List Bank :=
  expression.destinations.filterMap ParsedOperand.barWriteBank?

def ParsedExpr.writesLbf (expression : ParsedExpr) : Bool :=
  match expression.op with
  | .l1bm _ => expression.sources.any fun operand =>
      match operand with
      | .l1bm .. => true
      | _ => false
  | _ => false

def ParsedExpr.nowriteOutputValid (expression : ParsedExpr) : Bool :=
  let nowrites := expression.destinations.filter fun operand =>
    match operand with
    | .nowrite => true
    | _ => false
  decide (nowrites.length = 0 ∨
    (nowrites.length = 1 ∧ expression.destinations.length = 1))

/-- Source-count condition imposed by the Rust parser's fixed source prefix. -/
def ParsedExpr.sourcesMatchParserArity (expression : ParsedExpr) : Prop :=
  expression.sources.length ≤ expression.op.parserSourceLimit

/-- The ordinary Rust `parse_expr` path splits a fixed opcode-specific prefix
into sources and rejects a missing input or output. Custom zero-input and
block-memory parser paths retain the weaker upper-bound condition. -/
def ParsedOp.hasFixedParserSourceArity : ParsedOp → Bool
  | .alu .. | .mau .. | .matrixWrite .. | .matrixRead .. => true
  | .l2bm .dars | .l2bm .darw => true
  | .immediate .. | .zero | .wait .. | .noforward | .l1bm .. | .l2bm _ => false

def ParsedExpr.parserSourceArityValid (expression : ParsedExpr) : Prop :=
  if expression.op.hasFixedParserSourceArity then
    expression.sources.length = expression.op.parserSourceLimit
  else expression.sourcesMatchParserArity

/-- DARS has one L2BM source and one DAR output; DARW is a zero-operand
companion instruction. The source count is fixed above and these destination
counts follow the assemble3 role/arity probes. -/
def ParsedExpr.blockDestinationArityValid (expression : ParsedExpr) : Prop :=
  match expression.op with
  | .l2bm .dars => expression.destinations.length = 1
  | .l2bm .darw => expression.destinations.length = 0
  | _ => True

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

def NormalizedExpr.destinationsPassRoleScreen (expression : NormalizedExpr) : Prop :=
  ∀ operand ∈ expression.destinations,
    expression.op.destinationRoleScreen expression.sources operand

def NormalizedExpr.sourcesPassRoleScreen (expression : NormalizedExpr) : Prop :=
  ∀ operand ∈ expression.sources,
    expression.op.sourceRoleScreen expression.sources operand

def NormalizedExpr.forwardingSourcePositionsValid (expression : NormalizedExpr) : Prop :=
  expression.op.forwardingSourcePositionsValid expression.sources

def ParsedExpr.normalize (expression : ParsedExpr) : NormalizedExpr :=
  ⟨expression.op, expression.sources, expression.destinations, expression.flush⟩

def NormalizedExpr.toParsed (expression : NormalizedExpr) : ParsedExpr :=
  ⟨expression.op, expression.sources, expression.destinations, expression.flush, ""⟩

/-- Canonical expressions retain the exact opcode-specific source-prefix bound
imposed by Rust `parse_expr` when display text is erased. -/
def NormalizedExpr.sourcesMatchParserArity (expression : NormalizedExpr) : Prop :=
  expression.sources.length ≤ expression.op.parserSourceLimit

def NormalizedExpr.parserSourceArityValid (expression : NormalizedExpr) : Prop :=
  if expression.op.hasFixedParserSourceArity then
    expression.sources.length = expression.op.parserSourceLimit
  else expression.sourcesMatchParserArity

def NormalizedExpr.blockDestinationArityValid (expression : NormalizedExpr) : Prop :=
  match expression.op with
  | .l2bm .dars => expression.destinations.length = 1
  | .l2bm .darw => expression.destinations.length = 0
  | _ => True

theorem ParsedExpr.normalize_sourcesMatchParserArity
    (expression : ParsedExpr)
    (arity : expression.sourcesMatchParserArity) :
    expression.normalize.sourcesMatchParserArity := by
  exact arity

theorem ParsedExpr.normalize_parserSourceArityValid
    (expression : ParsedExpr)
    (arity : expression.parserSourceArityValid) :
    expression.normalize.parserSourceArityValid := by
  exact arity

theorem ParsedExpr.normalize_blockDestinationArityValid
    (expression : ParsedExpr)
    (arity : expression.blockDestinationArityValid) :
    expression.normalize.blockDestinationArityValid := by
  exact arity

theorem ParsedExpr.normalize_destinationsPassRoleScreen
    (expression : ParsedExpr)
    (roles : expression.destinationsPassRoleScreen) :
    expression.normalize.destinationsPassRoleScreen := by
  exact roles

theorem ParsedExpr.normalize_sourcesPassRoleScreen
    (expression : ParsedExpr)
    (roles : expression.sourcesPassRoleScreen) :
    expression.normalize.sourcesPassRoleScreen := by
  exact roles

theorem ParsedExpr.normalize_forwardingSourcePositionsValid
    (expression : ParsedExpr)
    (positions : expression.forwardingSourcePositionsValid) :
    expression.normalize.forwardingSourcePositionsValid := by
  exact positions

theorem NormalizedExpr.parserSourceArityValid_length_le_three
    (expression : NormalizedExpr)
    (arity : expression.parserSourceArityValid) :
    expression.sources.length ≤ 3 := by
  unfold NormalizedExpr.parserSourceArityValid at arity
  split at arity
  · rw [arity]
    exact expression.op.parserSourceLimit_le_three
  · exact Nat.le_trans arity expression.op.parserSourceLimit_le_three

theorem ParsedExpr.parserSourceArityValid_length_le_three
    (expression : ParsedExpr)
    (arity : expression.parserSourceArityValid) :
    expression.sources.length ≤ 3 := by
  exact expression.normalize.parserSourceArityValid_length_le_three
    (expression.normalize_parserSourceArityValid arity)

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
  barWrites := e.barWrites
  omrWrites := e.maskRegisterWrites
  lbfWrites := if e.writesLbf then 1 else 0
  nowriteOutputValid := e.nowriteOutputValid
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

theorem projected_bar_writes_are_bar_destinations (id : Nat) (e : ParsedExpr) :
    (e.toIssueExpr id).barWrites = e.destinations.filterMap ParsedOperand.barWriteBank? := rfl

theorem projected_mask_register_writes_are_destinations (id : Nat) (e : ParsedExpr) :
    (e.toIssueExpr id).omrWrites =
      e.destinations.filterMap ParsedOperand.maskRegisterWrite? := rfl

theorem projected_lbf_writes_match_transfer_sources (id : Nat) (e : ParsedExpr) :
    (e.toIssueExpr id).lbfWrites = if e.writesLbf then 1 else 0 := rfl

theorem projected_nowrite_output_validity (id : Nat) (e : ParsedExpr) :
    (e.toIssueExpr id).nowriteOutputValid = e.nowriteOutputValid := rfl

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

theorem parsed_check_rejects_invalid_nowrite (expression : ParsedExpr)
    (invalid : expression.nowriteOutputValid = false) :
    checkParsedLine [expression] = false := by
  classical
  cases checked : checkParsedLine [expression] with
  | false => rfl
  | true =>
      have legal := parsed_check_sound [expression] checked
      rcases legal with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, valid, _, _⟩
      have projected : expression.nowriteOutputValid = true := by
        simpa [LegalParsedLine, projectLine, projectFrom, nowriteOutputsUnique,
          ParsedExpr.toIssueExpr] using valid
      cases invalid.symm.trans projected

def duplicateNowriteParsedExpr : ParsedExpr where
  op := .zero
  sources := []
  destinations := [.nowrite, .omr 1 none]
  flush := none
  text := "zero $nowrite $omr1"

theorem parsed_duplicate_nowrite_output_rejected :
    checkParsedLine [duplicateNowriteParsedExpr] = false :=
  parsed_check_rejects_invalid_nowrite duplicateNowriteParsedExpr (by decide)

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
  let rawPrecision ← chars.head?
  let precision ← if h : rawPrecision.toNat < 128 then
    some ⟨rawPrecision, h⟩ else none
  let opChars := chars.drop 1
  let op ← match precision.val, String.ofList opChars with
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

/-- L1B membership bitmap produced by the manual's `<l1badr>/<immode>`
selector form. The 3-bit comparison selects members; the result is represented
as an eight-bit bitmap, matching `ParsedL1bSet.mask`. -/
def parsedL1bAddressModeBitmap (address immode : Fin 8) : BitVec 8 :=
  let keep : BitVec 3 := (7 : BitVec 3) ^^^ BitVec.ofNat 3 immode.val
  let addressBits := BitVec.ofNat 3 address.val
  (List.finRange 8).foldl (fun bits index =>
    let indexBits := BitVec.ofNat 3 index.val
    if indexBits &&& keep == addressBits &&& keep then
      bits ||| ((1 : BitVec 8) <<< index.val)
    else bits) (0 : BitVec 8)

def parsedL1bAddressModeSet (address immode : Fin 8) : ParsedL1bSet :=
  ⟨(parsedL1bAddressModeBitmap address immode).toFin.val, immode.val⟩

theorem parsedL1bAddressModeSet_inFiniteEnvelope (address immode : Fin 8) :
    (parsedL1bAddressModeSet address immode).inFiniteEnvelope := by
  constructor
  · exact (parsedL1bAddressModeBitmap address immode).toFin.isLt
  · exact immode.isLt

def parsedL1bAddressModeSet? (addressValue immodeValue : Nat) :
    Option {set : ParsedL1bSet // set.inFiniteEnvelope} := do
  let address ← parsedNatToFin? addressValue 8
  let immode ← parsedNatToFin? immodeValue 8
  let set := parsedL1bAddressModeSet address immode
  some ⟨set, parsedL1bAddressModeSet_inFiniteEnvelope address immode⟩

/-- Parse the canonical decimal `<l1badr>` or `<l1badr>/<immode>` selector
form. -/
def parseParsedL1bAddressMode? (text : String) :
    Option {set : ParsedL1bSet // set.inFiniteEnvelope} := do
  let (addressChars, immodeChars) ← match text.toList.splitOn '/' with
    | [address] => some (address, ['0'])
    | [address, immode] => some (address, immode)
    | _ => none
  let addressValue ← parsedMvDecimal? addressChars
  let immodeValue ← parsedMvDecimal? immodeChars
  parsedL1bAddressModeSet? addressValue immodeValue

theorem parseParsedL1bAddressMode?_full_set :
    (parseParsedL1bAddressMode? "0/7").map Subtype.val = some ⟨255, 7⟩ := by decide

theorem parseParsedL1bAddressMode?_rejects_address_eight :
    parseParsedL1bAddressMode? "8/0" = none := by decide

theorem parseParsedL1bAddressMode?_rejects_immode_eight :
    parseParsedL1bAddressMode? "0/8" = none := by decide

/-- Trim the ASCII whitespace accepted around entries by Rust's `str::trim`.
The L1B list grammar only needs the whitespace characters used by source files. -/
def parsedL1bTrim (chars : List Char) : List Char :=
  let whitespace : Char → Bool := fun c => c == ' ' || c == '\t' || c == '\n' || c == '\r'
  (chars.dropWhile whitespace).reverse.dropWhile whitespace |>.reverse

def parsedL1bListValues? : List (List Char) → Option (List (Fin 8))
  | [] => none
  | [entry] => do
      let value ← parsedMvDecimal? (parsedL1bTrim entry)
      let bounded ← parsedNatToFin? value 8
      some [bounded]
  | entry :: rest => do
      let value ← parsedMvDecimal? (parsedL1bTrim entry)
      let bounded ← parsedNatToFin? value 8
      let tail ← parsedL1bListValues? rest
      some (bounded :: tail)

def parsedL1bSplitCommaAux : List Char → List Char → List (List Char) → List (List Char)
  | [], current, reversedEntries => (current.reverse :: reversedEntries).reverse
  | ',' :: rest, current, reversedEntries =>
      parsedL1bSplitCommaAux rest [] (current.reverse :: reversedEntries)
  | char :: rest, current, reversedEntries =>
      parsedL1bSplitCommaAux rest (char :: current) reversedEntries

def parsedL1bSplitComma (chars : List Char) : List (List Char) :=
  parsedL1bSplitCommaAux chars [] []

def parsedL1bListMask (values : List (Fin 8)) : BitVec 8 :=
  values.foldl (fun bits value => bits ||| ((1 : BitVec 8) <<< value.val)) 0

def parsedL1bListImmode (values : List (Fin 8)) : Fin 8 :=
  match values with
  | [] => ⟨0, by decide⟩
  | base :: rest =>
      let baseBits : BitVec 3 := BitVec.ofNat 3 base.val
      let difference := rest.foldl (fun bits value =>
        bits ||| (BitVec.ofNat 3 value.val ^^^ baseBits)) (0 : BitVec 3)
      ⟨difference.toNat, difference.isLt⟩

def parsedL1bListSet (values : List (Fin 8)) : ParsedL1bSet :=
  ⟨(parsedL1bListMask values).toFin.val, (parsedL1bListImmode values).val⟩

theorem parsedL1bListSet_inFiniteEnvelope (values : List (Fin 8)) :
    (parsedL1bListSet values).inFiniteEnvelope := by
  constructor
  · exact (parsedL1bListMask values).toFin.isLt
  · exact (parsedL1bListImmode values).isLt

/-- Parse the manual's bracketed L1B list form. Empty lists and malformed or
out-of-range members are rejected, matching `L1bSet::parse`. -/
def parseParsedL1bList? (text : String) :
    Option {set : ParsedL1bSet // set.inFiniteEnvelope} := do
  let chars := text.toList
  let rest ← match chars with
    | '[' :: rest => some rest
    | _ => none
  let reversed ← match rest.reverse with
    | ']' :: inside => some inside.reverse
    | _ => none
  let values ← parsedL1bListValues? (parsedL1bSplitComma reversed)
  let set := parsedL1bListSet values
  some ⟨set, parsedL1bListSet_inFiniteEnvelope values⟩

theorem parseParsedL1bList?_all :
    (parseParsedL1bList? "[0,1,2,3,4,5,6,7]").map Subtype.val = some ⟨255, 7⟩ := by decide

theorem parseParsedL1bList?_singleton :
    (parseParsedL1bList? "[5]").map Subtype.val = some ⟨32, 0⟩ := by decide

theorem parseParsedL1bList?_rejects_empty :
    parseParsedL1bList? "[]" = none := by decide

theorem parseParsedL1bList?_rejects_eight :
    parseParsedL1bList? "[0,8]" = none := by decide

theorem parseParsedL1bList?_trims_entries :
    (parseParsedL1bList? "[ 0, 7 ]").map Subtype.val = some ⟨129, 7⟩ := by decide

/-- Unified L1B selector parser used by the `l2bm` opcode parser. -/
def parseParsedL1bSet? (text : String) :
    Option {set : ParsedL1bSet // set.inFiniteEnvelope} :=
  match text.toList with
  | '[' :: _ => parseParsedL1bList? text
  | _ => parseParsedL1bAddressMode? text

def parsedL1bSetAll : ParsedL1bSet := ⟨255, 7⟩

theorem parsedL1bSetAll_inFiniteEnvelope : parsedL1bSetAll.inFiniteEnvelope := by
  constructor <;> decide

def parsedSplitAt? : List Char → Char → Option (List Char × List Char)
  | [], _ => none
  | separator :: rest, delimiter =>
      if separator == delimiter then some ([], rest) else do
        let (before, suffix) ← parsedSplitAt? rest delimiter
        some (separator :: before, suffix)

def parsedStripChars? : List Char → List Char → Option (List Char)
  | [], input => some input
  | first :: restPrefix, input =>
      match input with
      | char :: restInput =>
          if first == char then parsedStripChars? restPrefix restInput else none
      | [] => none

/-- Mirror the selector-bearing `l2bm` opcode forms in Rust's
`parse_l2_opcode`: broadcast, broadcast2, internal multicast, and the
direction-dependent `d` operation. The final Boolean records whether the
first operand is L2BM, as in the Rust parser. -/
def parseParsedL2SelectorOpcode? (opcode : String) (fromL2 : Bool) :
    Option ParsedL2Op := do
  let (head, selectorText) ← match parsedSplitAt? opcode.toList '@' with
    | none =>
        let rest ← parsedStripChars? ['l', '2', 'b', 'm'] opcode.toList
        some (rest, none)
    | some (whole, selector) => do
        let rest ← parsedStripChars? ['l', '2', 'b', 'm'] whole
        some (rest, some (String.ofList selector))
  let parseSet := do
    match selectorText with
    | none => some parsedL1bSetAll
    | some text => some (← parseParsedL1bSet? text).val
  match head with
  | ['b'] => some (.bcast (← parseSet))
  | ['b', '2'] => some (.bcast2 (← parseSet))
  | ['i'] => some (.imcast (← parseSet))
  | ['d'] => if fromL2 then some (.distrib (← parseSet)) else some .gather
  | [] => do
      let text ← selectorText
      let value ← parsedMvDecimal? text.toList
      let l1b ← parsedNatToFin? value 256
      some (.fromL1b l1b.val)
  | _ => none

theorem parseParsedL2SelectorOpcode_broadcast_list :
    parseParsedL2SelectorOpcode? "l2bmb@[0,2,4,6]" false =
      some (.bcast ⟨85, 6⟩) := by decide

theorem parseParsedL2SelectorOpcode_broadcast_default :
    parseParsedL2SelectorOpcode? "l2bmb" false =
      some (.bcast parsedL1bSetAll) := by decide

theorem parseParsedL2SelectorOpcode_distribution_list :
    parseParsedL2SelectorOpcode? "l2bmd@[1,3,5,7]" true =
      some (.distrib ⟨170, 6⟩) := by decide

theorem parseParsedL2SelectorOpcode_gather_ignores_selector_like_rust :
    parseParsedL2SelectorOpcode? "l2bmd@not-a-selector" false = some .gather := by decide

theorem parseParsedL2SelectorOpcode_from_l1b_parser_u8_range :
    parseParsedL2SelectorOpcode? "l2bm@255" false = some (.fromL1b 255) := by decide

theorem parseParsedL2SelectorOpcode_rejects_l1b_u8_overflow :
    parseParsedL2SelectorOpcode? "l2bm@256" false = none := by decide

/-- Full opcode-level mirror of Rust's `parse_l2_opcode`. Operand-dependent
`fromL2` classification is supplied by the caller, as in the Rust parser. -/
def parseParsedL2Opcode? (opcode : String) (fromL2 : Bool) : Option ParsedL2Op := do
  let (head, selectorText) ← match parsedSplitAt? opcode.toList '@' with
    | none => do
        let rest ← parsedStripChars? ['l', '2', 'b', 'm'] opcode.toList
        some (rest, none)
    | some (whole, selector) => do
        let rest ← parsedStripChars? ['l', '2', 'b', 'm'] whole
        some (rest, some (String.ofList selector))
  let parseSet := do
    match selectorText with
    | none => some parsedL1bSetAll
    | some text => some (← parseParsedL1bSet? text).val
  if head == ['d', 'a', 'r', 's'] then some .dars
  else if head == ['d', 'a', 'r', 'w'] then some .darw
  else if head.take 2 == ['r', '2'] then do
    let rrn ← parseParsedMvRrn? (head.drop 2)
    some (.reduce2 rrn)
  else if head.head? == some 'r' then do
    let rrn ← parseParsedMvRrn? (head.drop 1)
    some (.reduce rrn (← parseSet))
  else parseParsedL2SelectorOpcode? opcode fromL2

theorem parseParsedL2Opcode_reduce_with_list :
    parseParsedL2Opcode? "l2bmrdfadd@[0,4]" false =
      some (.reduce ⟨⟨'d', by decide⟩, .fadd⟩ ⟨17, 4⟩) := by decide

theorem parseParsedL2Opcode_reduce_default_set :
    parseParsedL2Opcode? "l2bmrdfadd" false =
      some (.reduce ⟨⟨'d', by decide⟩, .fadd⟩ parsedL1bSetAll) := by decide

theorem parseParsedL2Opcode_reduce2_ignores_selector_like_rust :
    parseParsedL2Opcode? "l2bmr2dfadd@ignored" false =
      some (.reduce2 ⟨⟨'d', by decide⟩, .fadd⟩) := by decide

theorem parseParsedL2Opcode_dars_ignores_selector_like_rust :
    parseParsedL2Opcode? "l2bmdars@ignored" false = some .dars := by decide

theorem parseParsedL2Opcode_darw :
    parseParsedL2Opcode? "l2bmdarw" false = some .darw := by decide

theorem parseParsedL2Opcode_rejects_bad_rrn :
    parseParsedL2Opcode? "l2bmrdfsub" false = none := by decide

def parsedSignedDecimal? (chars : List Char) : Option Int := do
  match chars with
  | '-' :: magnitude =>
      let value ← parsedMvDecimal? magnitude
      some (-(Int.ofNat value))
  | _ =>
      let value ← parsedMvDecimal? chars
      some (Int.ofNat value)

/-- Parse an L1BM MAB offset directly into its bounded range subtype. -/
def parsedMabdiff? (chars : List Char) :
    Option {offset : Int // -255 ≤ offset ∧ offset ≤ 255} := do
  let offset ← parsedSignedDecimal? chars
  if h : -255 ≤ offset ∧ offset ≤ 255 then some ⟨offset, h⟩ else none

theorem parsedMabdiff?_boundaries :
    parsedMabdiff? ['-','2','5','5'] = some ⟨-255, by omega⟩ ∧
      parsedMabdiff? ['+','2','5','5'] = some ⟨255, by omega⟩ ∧
      parsedMabdiff? ['-','2','5','6'] = none ∧
      parsedMabdiff? ['+','2','5','6'] = none := by decide

def parsedL1RrnRound? (chars : List Char) : Option (ParsedRrn × Bool) := do
  let (rrnChars, round) := if chars.getLast? == some 'r'
    then (chars.dropLast, true) else (chars, false)
  let rrn ← parseParsedMvRrn? rrnChars
  some (rrn, round)

/-- Mirror Rust's `parse_l1_opcode`. The caller supplies `toPE`, which Rust
derives from whether the first parsed operand is an L1BM operand. -/
def parseParsedL1Opcode? (opcode : String) (toPE : Bool) : Option ParsedL1Op := do
  let rest ← parsedStripChars? ['l', '1', 'b', 'm'] opcode.toList
  if rest == ['p'] then some .pbcast
  else if rest.take 2 == ['m', '4'] then
    let suffix := rest.drop 2
    match suffix with
    | '@' :: mabChars => do
        let mab ← parsedMvDecimal? mabChars
        if mab < 256 then some (.m4write mab) else none
    | [] => some .m4bcast
    | _ => none
  else if rest.head? == some 'm' then
    let suffix := rest.drop 1
    match suffix with
    | '@' :: mabChars => do
        let mab ← parsedMvDecimal? mabChars
        if mab < 256 then some (.mwrite mab) else none
    | [] => some .mbcast
    | _ => none
  else if rest.head? == some 'd' then
    let offsetChars := rest.drop 1
    let offset ← if offsetChars.isEmpty then some ⟨0, by omega⟩
      else parsedMabdiff? offsetChars
    some (if toPE then .distrib offset.val else .gather offset.val)
  else if rest.take 2 == ['r', '4'] then do
    let (rrn, round) ← parsedL1RrnRound? (rest.drop 2)
    some (.reduce4 rrn round)
  else if rest.head? == some 'r' then do
    let (rrn, round) ← parsedL1RrnRound? (rest.drop 1)
    some (.reduce rrn round)
  else none

/-- Derive the `to_pe` argument exactly as `parse_expr` does: only a first
operand classified as L1BM makes `l1bmd` a distribution. -/
def parseParsedL1OpcodeForOperands? (opcode : String) (operands : List ParsedOperand) :
    Option ParsedL1Op :=
  parseParsedL1Opcode? opcode (match operands with
    | .l1bm .. :: _ => true
    | _ => false)

/-- Derive `from_l2` from Rust's first-operand test before parsing an L2BM
opcode. -/
def parseParsedL2OpcodeForOperands? (opcode : String) (operands : List ParsedOperand) :
    Option ParsedL2Op :=
  parseParsedL2Opcode? opcode (match operands with
    | .l2bm .. :: _ => true
    | _ => false)

theorem parseParsedL1OpcodeForOperands_l1bm_source_distributes :
    parseParsedL1OpcodeForOperands? "l1bmd+3" [.l1bm 2 (some 0)] =
      some (.distrib 3) := by decide

theorem parseParsedL1OpcodeForOperands_non_l1bm_source_gathers :
    parseParsedL1OpcodeForOperands? "l1bmd+3" [.nowrite] =
      some (.gather 3) := by decide

theorem parseParsedL1OpcodeForOperands_empty_sources_gathers :
    parseParsedL1OpcodeForOperands? "l1bmd" [] = some (.gather 0) := by decide

theorem parseParsedL2OpcodeForOperands_l2bm_source_distributes :
    parseParsedL2OpcodeForOperands? "l2bmd@[0,4]" [.l2bm 0 none] =
      some (.distrib ⟨17, 4⟩) := by decide

theorem parseParsedL2OpcodeForOperands_non_l2bm_source_gathers :
    parseParsedL2OpcodeForOperands? "l2bmd@[invalid]" [.nowrite] =
      some .gather := by decide

theorem parseParsedL1Opcode_pbcast :
    parseParsedL1Opcode? "l1bmp" false = some .pbcast := by decide

theorem parseParsedL1Opcode_mab_writes_parse_u8_range :
    parseParsedL1Opcode? "l1bmm@255" false = some (.mwrite 255) := by decide

theorem parseParsedL1Opcode_m4write_valid_selector :
    parseParsedL1Opcode? "l1bmm4@15" true = some (.m4write 15) := by decide

theorem parseParsedL1Opcode_mab_write_rejects_u8_overflow :
    parseParsedL1Opcode? "l1bmm4@256" false = none := by decide

theorem parseParsedL1Opcode_broadcast_forms :
    parseParsedL1Opcode? "l1bmm" false = some .mbcast ∧
      parseParsedL1Opcode? "l1bmm4" false = some .m4bcast := by decide

theorem parseParsedL1Opcode_distribution_direction :
    parseParsedL1Opcode? "l1bmd-255" true = some (.distrib (-255)) ∧
      parseParsedL1Opcode? "l1bmd+255" false = some (.gather 255) := by decide

theorem parseParsedL1Opcode_zero_offset_default :
    parseParsedL1Opcode? "l1bmd" true = some (.distrib 0) := by decide

theorem parseParsedL1Opcode_mabdiff_rejects_outside_assembler_range :
    parseParsedL1Opcode? "l1bmd-256" true = none ∧
      parseParsedL1Opcode? "l1bmd+256" false = none := by decide

theorem parseParsedL1Opcode_reduce_rounding :
    parseParsedL1Opcode? "l1bmr4dfaddr" false =
      some (.reduce4 ⟨⟨'d', by decide⟩, .fadd⟩ true) := by decide

theorem parseParsedL1Opcode_reduce_unrounded :
    parseParsedL1Opcode? "l1bmriband" true =
      some (.reduce ⟨⟨'i', by decide⟩, .band⟩ false) := by decide

theorem parseParsedL1Opcode_rejects_invalid_round_suffix :
    parseParsedL1Opcode? "l1bmrdfaddrr" false = none := by decide

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

def parsedHexDigit? (digit : Char) : Option Nat :=
  let value := digit.toNat
  if 48 ≤ value ∧ value ≤ 57 then some (value - 48)
  else if 65 ≤ value ∧ value ≤ 70 then some (value - 55)
  else if 97 ≤ value ∧ value ≤ 102 then some (value - 87)
  else none

def parsedHexValueAux : List Char → Nat → Option Nat
  | [], value => some value
  | digit :: rest, value => do
      let nibble ← parsedHexDigit? digit
      parsedHexValueAux rest (value * 16 + nibble)

/-- Parse Rust's `i<hex-u8>` wait-tag spelling. Zero is syntactically parsed;
the assembler rejects it, which remains a separate legality condition. -/
def parseParsedWaitTag? (text : String) : Option (Fin 256) := do
  match text.toList with
  | 'i' :: digits =>
      if digits.isEmpty then none else do
        let value ← parsedHexValueAux digits 0
        parsedNatToFin? value 256
  | _ => none

theorem parseParsedWaitTag_i01 :
    parseParsedWaitTag? "i01" = some ⟨1, by decide⟩ := by decide

theorem parseParsedWaitTag_iFF :
    parseParsedWaitTag? "iFF" = some ⟨255, by decide⟩ := by decide

theorem parseParsedWaitTag_i00_is_syntactic :
    parseParsedWaitTag? "i00" = some ⟨0, by decide⟩ := by decide

theorem parseParsedWaitTag_rejects_overflow :
    parseParsedWaitTag? "i100" = none := by decide

theorem parseParsedWaitTag_value_bounded (text : String) (tag : Fin 256)
    (_parsed : parseParsedWaitTag? text = some tag) : tag.val < 256 := tag.isLt

inductive ParsedLine where
  | pe (expressions : List ParsedExpr)
  | nop (count : Nat) (wait : Option (Fin 256))
  | mv (transfer : ParsedMv)
  | maskDirective (widthWords : Nat) (targets : ParsedMaskTargets) (entry : Nat)
  | debugSet
  | debugGet
  | dramSet
  deriving DecidableEq, Repr

def parseParsedNopOpcode? (opcode : String) : Option Nat :=
  match opcode.toList with
  | ['n', 'o', 'p'] => some 1
  | 'n' :: 'o' :: 'p' :: '/' :: countChars => do
      let count ← parsedMvDecimal? countChars
      if count < 2 ^ 32 then some count else none
  | _ => none

/-- Parse the canonical single-nop/single-wait spelling. This deliberately
keeps the source syntax separate from legality: `i00` parses, then the
top-line checker rejects it, matching the assembler boundary probes. -/
def parseParsedNopLine? (text : String) : Option ParsedLine := do
  let (nopChars, waitChars) ← match parsedSplitAt? text.toList ';' with
    | none => some (text.toList, none)
    | some (before, after) => some (before, some after)
  let opcode ← match parsedMvSplitWhitespace (String.ofList nopChars) with
    | [opcode] => some opcode
    | _ => none
  let count ← parseParsedNopOpcode? opcode
  let wait ← match waitChars with
    | none => some none
    | some chars => do
        match parsedMvSplitWhitespace (String.ofList chars) with
        | ["wait", tagText] => do
            let tag ← parseParsedWaitTag? tagText
            some (some tag)
        | _ => none
  some (.nop count wait)

theorem parseParsedNopLine_plain :
    parseParsedNopLine? "nop" = some (.nop 1 none) := by decide

theorem parseParsedNopLine_with_wait :
    parseParsedNopLine? "nop/7; wait iFF" =
      some (.nop 7 (some ⟨255, by decide⟩)) := by decide

theorem parseParsedNopLine_rejects_wait_overflow :
    parseParsedNopLine? "nop; wait i100" = none := by decide

theorem parseParsedNopLine_rejects_nop_u32_overflow :
    parseParsedNopLine? "nop/4294967296" = none := by decide

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
  | nop (count : Nat) (wait : Option (Fin 256))
  | mv (transfer : NormalizedMv)
  | maskDirective (widthWords : Nat) (targets : ParsedMaskTargets) (entry : Nat)
  deriving DecidableEq, Repr

/-- Executable issue words after zero-cost directives are folded into control
state. Nop counts are strictly positive by construction. -/
inductive InstructionLine where
  | pe (expressions : List NormalizedExpr)
  | nop (count : {n : Nat // 0 < n}) (wait : Option (Fin 256))
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

theorem normalized_positive_nop_cost (count : Nat) (wait : Option (Fin 256)) :
    (NormalizedLine.toInstruction? (.nop (count + 1) wait)).map
      InstructionLine.cost = some (count + 1) := rfl

/-- Scored instruction words contributed by a normalized executable line.
Control directives have zero cost and are handled by the control trace. -/
def NormalizedLine.instructionCost : NormalizedLine → Nat
  | .pe _ | .mv _ => 1
  | .nop count _ => count
  | .maskDirective .. => 0

theorem NormalizedLine.instructionCost_eq_toInstruction_cost
    (line : NormalizedLine) :
    line.toInstruction?.map InstructionLine.cost =
      if line.instructionCost = 0 then none else some line.instructionCost := by
  cases line with
  | pe expressions => rfl
  | nop count wait =>
      cases count with
      | zero => rfl
      | succ count => rfl
  | mv transfer => rfl
  | maskDirective widthWords targets entry => rfl

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

/-- Cost after the judge's solution sanitization. A zero-count nop with a wait
is rejected by the assembler; source/debug records and control directives do
not contribute scored instruction words. -/
def ParsedLine.submissionCost? : ParsedLine → Option Nat
  | .pe _ | .mv _ => some 1
  | .nop 0 (some _) => none
  | .nop count _ => some count
  | .maskDirective .. | .debugSet | .debugGet | .dramSet => some 0

theorem ParsedLine.normalizeForSubmission_cost (line : ParsedLine)
    (normalized : List NormalizedLine)
    (result : line.normalizeForSubmission? = some normalized) :
    (normalized.map NormalizedLine.instructionCost).sum = line.submissionCost?.getD 0 := by
  cases line with
  | pe expressions =>
      simp [ParsedLine.normalizeForSubmission?] at result
      subst normalized
      simp [ParsedLine.submissionCost?, NormalizedLine.instructionCost]
  | nop count wait =>
      cases count with
      | zero =>
          cases wait with
          | none =>
              simp [ParsedLine.normalizeForSubmission?] at result
              subst normalized
              simp [ParsedLine.submissionCost?]
          | some tag => simp [ParsedLine.normalizeForSubmission?] at result
      | succ count =>
          simp [ParsedLine.normalizeForSubmission?] at result
          subst normalized
          simp [ParsedLine.submissionCost?, NormalizedLine.instructionCost]
  | mv transfer =>
      simp [ParsedLine.normalizeForSubmission?] at result
      subst normalized
      simp [ParsedLine.submissionCost?, NormalizedLine.instructionCost]
  | maskDirective widthWords targets entry =>
      simp [ParsedLine.normalizeForSubmission?] at result
      subst normalized
      simp [ParsedLine.submissionCost?, NormalizedLine.instructionCost]
  | debugSet | debugGet | dramSet =>
      simp [ParsedLine.normalizeForSubmission?] at result
      subst normalized
      simp [ParsedLine.submissionCost?]

theorem nop_zero_normalizes_empty :
    ParsedLine.normalizeForSubmission? (.nop 0 none) = some [] := rfl

/-- The standard judge strips source/debug records before running and scoring
the submitted instruction stream. These records therefore contribute no
instruction line to the normalized submission. -/
theorem source_records_normalize_empty :
    ParsedLine.normalizeForSubmission? .debugSet = some [] ∧
    ParsedLine.normalizeForSubmission? .debugGet = some [] ∧
    ParsedLine.normalizeForSubmission? .dramSet = some [] ∧
    ParsedLine.normalizeForSubmission? (.nop 0 none) = some [] := by
  exact ⟨rfl, rfl, rfl, rfl⟩

def ParsedLine.nopIssueLegalB (count : Nat) (wait : Option (Fin 256)) : Bool :=
  match count, wait with
  | 0, some _ => false
  | _, some tag => decide (0 < tag.val)
  | _, none => true

def ParsedLine.nopIssueLegal (count : Nat) (wait : Option (Fin 256)) : Prop :=
  ParsedLine.nopIssueLegalB count wait = true

def ParsedLine.issueLegal : ParsedLine → Prop
  | .pe expressions => LegalParsedLine expressions
  | .nop count wait => ParsedLine.nopIssueLegal count wait
  | .mv _ | .maskDirective _ _ _ | .debugSet | .debugGet | .dramSet => True

noncomputable def checkParsedTopLine : ParsedLine → Bool
  | .pe expressions => checkParsedLine expressions
  | .nop count wait => ParsedLine.nopIssueLegalB count wait
  | .mv _ | .maskDirective _ _ _ | .debugSet | .debugGet | .dramSet => true

theorem parsed_topline_check_sound (line : ParsedLine)
    (accepted : checkParsedTopLine line = true) : line.issueLegal := by
  cases line with
  | pe expressions => exact parsed_check_sound expressions accepted
  | nop count wait =>
      change ParsedLine.nopIssueLegalB count wait = true
      exact accepted
  | mv _ | maskDirective _ _ _ | debugSet | debugGet | dramSet => trivial

theorem ParsedLine.checked_nop_wait_positive (count : Nat) (tag : Fin 256)
    (checked : checkParsedTopLine (.nop count (some tag)) = true) :
    0 < tag.val := by
  have legal := parsed_topline_check_sound (.nop count (some tag)) checked
  change ParsedLine.nopIssueLegalB count (some tag) = true at legal
  cases count with
  | zero => simp [ParsedLine.nopIssueLegalB] at legal
  | succ count =>
      have positive : decide (0 < tag.val) = true := by
        simpa [ParsedLine.nopIssueLegalB] using legal
      exact of_decide_eq_true positive

theorem parseParsedNopLine_checked_wait_positive (text : String)
    (count : Nat) (tag : Fin 256)
    (_parsed : parseParsedNopLine? text = some (.nop count (some tag)))
    (checked : checkParsedTopLine (.nop count (some tag)) = true) :
    0 < tag.val :=
  ParsedLine.checked_nop_wait_positive count tag checked

theorem parsed_topline_check_complete (line : ParsedLine) (legal : line.issueLegal) :
    checkParsedTopLine line = true := by
  cases line with
  | pe expressions => exact parsed_check_complete expressions legal
  | nop count wait =>
      change ParsedLine.nopIssueLegal count wait at legal
      exact legal
  | mv _ | maskDirective _ _ _ | debugSet | debugGet | dramSet => rfl

theorem parsed_topline_rejects_zero_wait_tag :
    checkParsedTopLine (.nop 1 (some ⟨0, by decide⟩)) = false := by decide

theorem parsed_topline_rejects_zero_nop_with_wait :
    checkParsedTopLine (.nop 0 (some ⟨1, by decide⟩)) = false := by decide

theorem parsed_topline_accepts_zero_nop_without_wait :
    checkParsedTopLine (.nop 0 none) = true := by decide

theorem parseParsedNopLine_zero_tag_parses_but_checker_rejects :
    ∃ line, parseParsedNopLine? "nop; wait i00" = some line ∧
      checkParsedTopLine line = false := by
  exact ⟨.nop 1 (some ⟨0, by decide⟩), by decide, rfl⟩

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
    ParsedExpr.maskRegisterWrites ParsedOperand.maskRegisterWrite?
    ParsedExpr.barWrites ParsedOperand.barWriteBank?
    ParsedExpr.writesLbf ParsedExpr.nowriteOutputValid
    plusOneParsed plusOneRead plusOneWrite
  simp [Legal, idsUnique, groupsUnique, mauCountBounded, mauExpressions,
    mauPrecisionsAgree, matrixWritePairAgrees, matrixRegistersUnique,
    writesUnique, Expr.writeBanks, barWritesExcludeReads, readsAgree, localReadWriteAgree, immediateExcludesLm0,
    zeroFlushUnique, maskWidthsAgree, maskEntriesAgree, nowriteOutputsUnique,
    lbfWritesUnique, maskRegisterWritesUnique,
    projectFrom]

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
