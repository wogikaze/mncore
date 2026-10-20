import ProofsLean.WelcomeWriterDispatch
import ProofsLean.WelcomeValueBound
import ProofsLean.WelcomeWriterShape
import ProofsLean.WelcomeGapShape
-- `WelcomeMixedStructure` supplies the two list bookkeeping lemmas used below:
-- `projectFrom_getElem_toIssueExpr` (the `i`-th projected row is the `i`-th
-- source row at id `i`) and `welcomeMixed_writer_writeBanks_nodup_of_mem` (a
-- row's own write banks are duplicate free, from its membership alone).
import ProofsLean.WelcomeMixedStructure

/-! # The final write-shape assembly: from the unique `.lm1` writer's kind to the line

`WelcomeWriterDispatch.lean` (round 45) proves five **unique-writer dispatch**
theorems: if the line's unique `.lm1` row `e` is plain / `.matrixRead` /
float-MAU / matrix-MAU / `.l1bm`, and the line's other integer-stage rows are
`.noforward` / `.wait` companions, then the line's write shape is `e`'s row
shape.  Those theorems take the row-local hypothesis

```
rows : ∀ expression ∈ line, expression ≠ e → WelcomeRowHasNoLm1Destination expression
```

while the issue checker only provides `welcomeLm1Writer_unique`, stated about
`Expr.writeBanks` and expression ids.  This module closes that gap and performs
the assembly.

* **§1 the bridge (unconditional).**  `WelcomeRowHasNoLm1Destination` is about
  destination operands; `Expr.writeBanks` is `bankList destinations ++ barWrites`
  (`writeBanks_eq_bankList`).  A direct destination resolving to bank `.lm1` is
  an `.lm1` memory destination (`directDestinationBankWidth_isLm1`), hence
  contributes `Issue.Bank.lm1` to `bankList`, hence to `writeBanks`:
  `welcomeRowHasNoLm1Destination_of_writeBanks_not_mem`.  Two `.lm1`-writing rows
  of an accepted line are equal — `welcomeLm1Writer_eq_of_two`, from
  `welcomeLm1Writer_unique` plus the id component of `Expr` — so
  `welcomeLm1Writer_rows` gives exactly the `rows` hypothesis above, and
  `welcomeLm1Writer_nodup` gives the writer's own `writeBanks.Nodup`.
* **§2 the writer-kind data, per line.**  Each dispatch theorem also needs
  line-level data that uniqueness does not supply: the split of the integer-stage
  filter into `.noforward` / `.wait` companions around `e`, the singleton
  middle-stage filter for the writer's own stage, the mask-flag agreement and the
  immediate-double exclusion for a plain writer (packaged as
  "flag agreement and no immediate-double, **or** input independence"), and
  "no float-MAU companion" where the integer stage's list must be
  `welcomeIntegerPrep`'s.  Each package is the per-line `Prop`
  `WelcomePEPlainWriterDataFor`, `WelcomePEMatrixReadWriterDataFor`,
  `WelcomePEFloatMAUWriterDataFor`, `WelcomePEMatrixMAUWriterDataFor`,
  `WelcomePEL1BMWriterDataFor`, with global forms (`WelcomePEPlainWriterData`, …)
  for the aggregate.  Each `welcomePEWriteShape_of_*Writer_data` theorem turns
  one package plus the §1 bridge into the line shape.
* **§3 the cases with no dispatchable writer.**  If every `.lm1`-writing row is
  `.noforward`, `.wait`, a shared-block `.l1bm` row, a `.matrixWrite` row or an
  `.l2bm` row (or there is no `.lm1` writer at all), no stage writes an `.lm1`
  word.  The value content of the case is `WelcomePELm1FreeStageCommit` ("the
  line's stage commit list is `.lm1`-free"), which gives the shape vacuously
  (`welcomePEWriteShape_of_freeStageCommit`).  The provenance statement is the
  global `WelcomePELm1PhantomWriterProvenance`; its proof reduces to the
  float-MAU list-level provenance plus the integer-stage provenance refined at
  `.noforward` / `.wait` rows.  The special-ALU writer is the one shape-level
  residual, `WelcomePESpecialALUWriterShapeObligation`, split in §5 into its three
  stages.
* **§4 the per-line aggregate.**  `WelcomePELm1LineDispatchData` is the
  seven-way disjunction of §2/§3 cases *for one line*, and
  `welcomePEWriteShape_of_lineData` turns it plus the special-ALU case into the
  line's shape.  The exhaustive `supportedProducer_partition`
  (plain / six families / three special-ALU families / PE-inert /
  Rust-unsupported) proves the per-line data from the global packages
  (`welcomePELm1LineDispatchData_of_components`), so
  `WelcomePEDispatchResiduals` (the special-ALU case plus the per-line data for
  every unrefuted line) yields `WelcomePELm1WriteShapeObligation`, and with it
  `LowerBound welcomeSealedMachine welcomeSpec 2` and
  `Optimal welcomeSealedMachine welcomeSpec welcomeAnswer`
  (`welcomePELm1WriteShapeObligation_of_dispatch`,
  `welcomeLowerBound_two_of_dispatch`, `welcomeAnswer_optimal_of_dispatch`).

## What is proved unconditionally here

* the §1 bridge, `welcomeLm1Writer_rows` and `welcomeLm1Writer_nodup`;
* the five per-line writer-kind theorems modulo their data packages;
* `welcomePEWriteShape_of_freeStageCommit` (an `.lm1`-free stage list gives the
  shape) and `welcomePEWriteShape_of_noWriter_of_integerOrInert` (the no-writer
  case on integer-or-inert lines, through `welcomePEWriteShape_of_noLm1Rows`);
* the per-line aggregate `welcomePEWriteShape_of_lineData` and the
  classification `welcomePELm1LineDispatchData_of_components`.

## What is **not** proved here

`WelcomePELm1WriteShapeObligation`, `LowerBound welcomeSealedMachine welcomeSpec 2`
and `Optimal welcomeSealedMachine welcomeSpec welcomeAnswer` are **not** proved
unconditionally: the three theorems above take `WelcomePEDispatchResiduals` as a
hypothesis, and that bundle is open.  Its content is exactly the syntactic
remainder, and the five writer-kind data packages are *restrictions* of the
current row-shape lemmas, not consequences of the issue checker:

* the **companion split** is a genuine locality condition:
  `plainRow_lm1_shape` / `matrixReadRow_lm1_shape` are stated at the initial
  forwarding slots, so a line whose integer stage has a second preparing row
  (e.g. a `.matrixRead` row without an `.lm1` destination followed by a plain
  `.lm1` writer) is outside the reduction.  Closing it needs a slot-independent
  (or concatenation) form of the row shapes.
* the **singleton middle-stage filters** (`floatFilter = [e]`, `mauFilter = [e]`,
  `l1Filter = [e]`) exclude lines with two rows of the writer's own stage.
* the **mask-flag agreement** is false in general
  (`welcomePEMixedPlainInertFlagAgreement_false`, round 45), which is why the
  plain package carries the `… ∨ WelcomePEInputIndependent expressions` branch
  (mirroring `WelcomePEMixedPlainInertStructureReduced`); the flag-`true`
  lowering of a plain row with no masked destination of its own is still open.
* the **float-MAU list-level provenance** (the phantom case) and the
  **special-ALU stage fold** are the two provenance/shape residuals.

No `sorry`, no `admit`, no `native_decide`, no new axioms, and no existing
module is edited by this file.
-/

namespace ProofsLean.MNCore

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open Issue
open PEMemory

/-! ## 1. The syntactic bridge: from `writeBanks` uniqueness to row-local freeness -/

/-- `writeBanks` does not depend on the projection's id. -/
theorem writeBanks_toIssueExpr_eq (e : ParsedExpr) (id : Nat) :
    (e.toIssueExpr 0).writeBanks = (e.toIssueExpr id).writeBanks := by
  rw [writeBanks_eq_bankList, writeBanks_eq_bankList]

/-- The bank part of a one-element destination list, as an append. -/
theorem bankList_cons (d : ParsedOperand) (rest : List ParsedOperand) :
    ParsedOperand.bankList (d :: rest) =
      (match d with
        | .mem access _ _ _ _ => [access.bank]
        | _ => []) ++ ParsedOperand.bankList rest := by
  cases d <;> rfl

/-- The bank list of a one-element destination list. -/
theorem bankList_singleton (d : ParsedOperand) :
    ParsedOperand.bankList [d] =
      (match d with
        | .mem access _ _ _ _ => [access.bank]
        | _ => []) := by
  cases d <;> rfl

/-- A bank of a destination's own bank list is a bank of the whole list. -/
theorem mem_bankList_of_mem : ∀ (l : List ParsedOperand) (d : ParsedOperand), d ∈ l →
    ∀ (b : Issue.Bank), b ∈ ParsedOperand.bankList [d] →
      b ∈ ParsedOperand.bankList l := by
  intro l
  induction l with
  | nil => intro d hd; simp at hd
  | cons x xs ih =>
      intro d hd b hb
      rcases List.mem_cons.mp hd with rfl | hd
      · rw [bankList_cons]
        exact List.mem_append_left _ (by rw [bankList_singleton] at hb; exact hb)
      · rw [bankList_cons]
        exact List.mem_append_right _ (ih d hd b hb)

/-- **A destination resolving to bank `.lm1` is an `.lm1` memory destination.** -/
theorem isLm1MemoryDestination_of_bankList (destination : ParsedOperand)
    (width : PEMemory.Width)
    (resolved : ParsedOperand.directDestinationBankWidth? destination =
      some (PEMemory.Bank.lm1, width)) :
    Issue.Bank.lm1 ∈ ParsedOperand.bankList [destination] := by
  have lm1Dest := directDestinationBankWidth_isLm1 destination width resolved
  cases destination with
  | mem access negated extended rounded mask =>
      simp only [ParsedOperand.isLm1MemoryDestination] at lm1Dest
      have bankEq : access.bank = Issue.Bank.lm1 := beq_iff_eq.mp lm1Dest
      simp [ParsedOperand.bankList, bankEq]
  | bar bar width mask => simp [ParsedOperand.isLm1MemoryDestination] at lm1Dest
  | forward kind negated extended rounded => simp [ParsedOperand.isLm1MemoryDestination] at lm1Dest
  | fixed kind => simp [ParsedOperand.isLm1MemoryDestination] at lm1Dest
  | omr entry mask => simp [ParsedOperand.isLm1MemoryDestination] at lm1Dest
  | matrix y width row => simp [ParsedOperand.isLm1MemoryDestination] at lm1Dest
  | nowrite => simp [ParsedOperand.isLm1MemoryDestination] at lm1Dest
  | l1bm width address => simp [ParsedOperand.isLm1MemoryDestination] at lm1Dest
  | l2bm address l2b => simp [ParsedOperand.isLm1MemoryDestination] at lm1Dest
  | dar address => simp [ParsedOperand.isLm1MemoryDestination] at lm1Dest

/-- **No `.lm1` in a row's write banks: no `.lm1` destination operand.**
`Expr.writeBanks` is `bankList destinations ++ barWrites`, and a `.lm1` direct
destination contributes `Issue.Bank.lm1` to the bank list. -/
theorem welcomeRowHasNoLm1Destination_of_writeBanks_not_mem
    (expression : ParsedExpr) (id : Nat)
    (notMem : Issue.Bank.lm1 ∉ (expression.toIssueExpr id).writeBanks) :
    WelcomeRowHasNoLm1Destination expression := by
  intro destination destinationMem bank width resolved sameBank
  apply notMem
  rw [writeBanks_eq_bankList]
  apply List.mem_append_left
  have resolvedLm1 : ParsedOperand.directDestinationBankWidth? destination =
      some (PEMemory.Bank.lm1, width) := by
    rw [← sameBank]
    exact resolved
  exact mem_bankList_of_mem expression.destinations destination destinationMem Issue.Bank.lm1
    (isLm1MemoryDestination_of_bankList destination width resolvedLm1)

/-- **Two `.lm1`-writing rows of an accepted line are the same row.**  This is
`welcomeLm1Writer_unique` read through the id component of the projected
`Expr`: two projected rows with `.lm1` in their write banks are equal, hence
their list positions are equal. -/
theorem welcomeLm1Writer_eq_of_two (expressions : List NormalizedExpr)
    (unrefuted : WelcomePEUnrefuted expressions) {x e : ParsedExpr}
    (xMem : x ∈ expressions.map NormalizedExpr.toParsed)
    (eMem : e ∈ expressions.map NormalizedExpr.toParsed)
    (xWriter : Issue.Bank.lm1 ∈ (x.toIssueExpr 0).writeBanks)
    (eWriter : Issue.Bank.lm1 ∈ (e.toIssueExpr 0).writeBanks) :
    x = e := by
  let line := expressions.map NormalizedExpr.toParsed
  have legal : LegalParsedLine line := welcomePEUnrefuted_legal expressions unrefuted
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp xMem
  obtain ⟨j, hj, he⟩ := List.mem_iff_getElem.mp eMem
  subst he
  have projLength : (projectLine line).length = line.length := projectFrom_length 0 line
  have iLt : i < (projectLine line).length := by rw [projLength]; exact hi
  have jLt : j < (projectLine line).length := by rw [projLength]; exact hj
  have gi : (projectLine line)[i]'iLt = (line[i]'hi).toIssueExpr i := by
    show (projectFrom 0 line)[i]'iLt = (line[i]'hi).toIssueExpr i
    simpa using projectFrom_getElem_toIssueExpr 0 line i iLt hi
  have gj : (projectLine line)[j]'jLt = (line[j]'hj).toIssueExpr j := by
    show (projectFrom 0 line)[j]'jLt = (line[j]'hj).toIssueExpr j
    simpa using projectFrom_getElem_toIssueExpr 0 line j jLt hj
  have writerI : Issue.Bank.lm1 ∈ ((projectLine line)[i]'iLt).writeBanks := by
    rw [gi, ← writeBanks_toIssueExpr_eq (line[i]'hi) i]
    exact xWriter
  have writerJ : Issue.Bank.lm1 ∈ ((projectLine line)[j]'jLt).writeBanks := by
    rw [gj, ← writeBanks_toIssueExpr_eq (line[j]'hj) j]
    exact eWriter
  have same := welcomeLm1Writer_unique expressions legal ((projectLine line)[i]'iLt)
    (List.getElem_mem iLt) ((projectLine line)[j]'jLt) (List.getElem_mem jLt)
    writerI writerJ
  have ids : i = j := by
    have idEq := congrArg Expr.id same
    rw [gi, gj] at idEq
    exact idEq
  subst ids
  rfl

/-- **The bridge.**  For the unique `.lm1` writer `e` of an accepted line, every
*other* row of the line has no `.lm1` destination operand — the row-local
hypothesis `rows` of the five unique-writer dispatch corollaries. -/
theorem welcomeLm1Writer_rows (expressions : List NormalizedExpr)
    (unrefuted : WelcomePEUnrefuted expressions) (e : ParsedExpr)
    (eMem : e ∈ expressions.map NormalizedExpr.toParsed)
    (eWriter : Issue.Bank.lm1 ∈ (e.toIssueExpr 0).writeBanks) :
    ∀ x ∈ expressions.map NormalizedExpr.toParsed, x ≠ e →
      WelcomeRowHasNoLm1Destination x := by
  intro x xMem ne
  apply welcomeRowHasNoLm1Destination_of_writeBanks_not_mem x 0
  intro xWriter
  exact ne (welcomeLm1Writer_eq_of_two expressions unrefuted xMem eMem xWriter eWriter)

/-- The writer's own write banks are duplicate free (the `nodup` input of the
row-shape lemmas), from its membership alone. -/
theorem welcomeLm1Writer_nodup (expressions : List NormalizedExpr)
    (unrefuted : WelcomePEUnrefuted expressions) (e : ParsedExpr)
    (eMem : e ∈ expressions.map NormalizedExpr.toParsed) :
    (e.toIssueExpr 0).writeBanks.Nodup :=
  welcomeMixed_writer_writeBanks_nodup_of_mem expressions unrefuted e eMem

/-! ## 2. The writer-kind data packages, per line

Each `Prop` below states, *for one line*, the line-level data that the
corresponding dispatch theorem needs when the line's `.lm1` writer is of that
kind.  None of them concludes a write shape: they are the syntactic remainder
(companion split, singleton filters, mask-flag agreement, immediate-double
exclusion).  The global forms (`WelcomePEPlainWriterData`, …) quantify over all
unrefuted lines and are used only by the aggregate of §4.

The companion-split component is a genuine restriction of the current row-shape
lemmas, not bookkeeping: `plainRow_lm1_shape` and `matrixReadRow_lm1_shape` are
stated at the *initial* forwarding slots, so a companion row that prepares a
write *before* the writer changes the slots the writer sees.  Lines whose
integer stage has more than one preparing row (e.g. a `.matrixRead` row without
an `.lm1` destination followed by a plain `.lm1` writer) are therefore outside
the scope of this module's reduction; they need a slot-independent or
concatenation form of the row shapes. -/

/-- **The plain-writer data of one line.**  The line's integer-stage filter
splits as `.noforward` / `.wait` companions around the plain writer `e`, the line
has no float-MAU row, and either the line's mask flag is `e`'s own flag and `e` is
not an `.immediate` row with an `.lm1 .double` destination, or the line is
input-independent.

The trailing disjunction mirrors `WelcomePEMixedPlainInertStructureReduced`:
both components of the first branch are refutable in general (the mask-flag
agreement fails when an inert companion carries a masked `.mem` / `.bar` / `.omr`
destination, `welcomePEMixedPlainInertFlagAgreement_false`; an `.immediate`
writer with an `.lm1 .double` destination is input-independent rather than
double-copy, `welcomePEMixedPlainInertStructure_forbids_immediateDouble`), while
the second branch is exactly the third disjunct of `WelcomePEWriteShape`. -/
def WelcomePEPlainWriterDataFor (expressions : List NormalizedExpr) : Prop :=
  ∀ (e : ParsedExpr),
    e ∈ expressions.map NormalizedExpr.toParsed →
      parsedExprIsPlainIntegerALU e = true →
      Issue.Bank.lm1 ∈ (e.toIssueExpr 0).writeBanks →
      ∃ before after : List ParsedExpr,
        (expressions.map NormalizedExpr.toParsed).filter
            parsedExprIsIntegerMatrixReadStageInput = before ++ e :: after ∧
          (∀ expression ∈ before, expression.op = .noforward ∨
            ∃ tag : Fin 256, expression.op = .wait tag) ∧
          (∀ expression ∈ after, expression.op = .noforward ∨
            ∃ tag : Fin 256, expression.op = .wait tag) ∧
          (expressions.map NormalizedExpr.toParsed).filter
            parsedExprIsSupportedFloatMAUProducer = [] ∧
          (((((expressions.map NormalizedExpr.toParsed).filter
                  parsedExprIsIntegerMatrixReadStageInput).any
                parsedExprHasSingleLineWriteMask =
              parsedExprHasSingleLineWriteMask e) ∧
            (∀ (payload : BitVec 32) (sparse : Bool), e.op = .immediate payload sparse →
              ∀ destination ∈ e.destinations,
                ParsedOperand.directDestinationBankWidth? destination ≠
                  some (PEMemory.Bank.lm1, PEMemory.Width.double))) ∨
            WelcomePEInputIndependent expressions)

/-- **The `.matrixRead`-writer data of one line.**  Same companion split, plus the
row's static `.lm1` width and the line's lack of float-MAU rows.  The mask flag is
not needed: the matrix-read row shape is uniform in it. -/
def WelcomePEMatrixReadWriterDataFor (expressions : List NormalizedExpr) : Prop :=
  ∀ (e : ParsedExpr),
    e ∈ expressions.map NormalizedExpr.toParsed →
      parsedExprIsMatrixReadProducer e = true →
      Issue.Bank.lm1 ∈ (e.toIssueExpr 0).writeBanks →
      ∃ (before after : List ParsedExpr) (precision : ParsedPrecision) (sideY : Bool)
        (width : Fin 5) (row : Fin (2 ^ 32)) (staticW : PEMemory.Width),
        (expressions.map NormalizedExpr.toParsed).filter
            parsedExprIsIntegerMatrixReadStageInput = before ++ e :: after ∧
          (∀ expression ∈ before, expression.op = .noforward ∨
            ∃ tag : Fin 256, expression.op = .wait tag) ∧
          (∀ expression ∈ after, expression.op = .noforward ∨
            ∃ tag : Fin 256, expression.op = .wait tag) ∧
          e.op = .matrixRead precision ∧
          e.sources = [.matrix sideY width (some row)] ∧
          (∀ destination ∈ e.destinations, ∀ v : PEMemory.Width,
            ParsedOperand.directDestinationBankWidth? destination =
              some (PEMemory.Bank.lm1, v) → v = staticW) ∧
          (expressions.map NormalizedExpr.toParsed).filter
            parsedExprIsSupportedFloatMAUProducer = []

/-- **The float-MAU-writer data of one line.**  The float-MAU filter is the writer
alone and every integer-stage row is `.noforward`: float-MAU rows execute *inside*
the integer stage, and its write list is only
`executeIntegerProducerLineAtPEs_floatWriter`'s when no other row prepares
anything. -/
def WelcomePEFloatMAUWriterDataFor (expressions : List NormalizedExpr) : Prop :=
  ∀ (e : ParsedExpr),
    e ∈ expressions.map NormalizedExpr.toParsed →
      parsedExprIsSupportedFloatMAUProducer e = true →
      Issue.Bank.lm1 ∈ (e.toIssueExpr 0).writeBanks →
      (expressions.map NormalizedExpr.toParsed).filter
          parsedExprIsSupportedFloatMAUProducer = [e] ∧
        (∀ expression ∈ (expressions.map NormalizedExpr.toParsed).filter
          parsedExprIsIntegerMatrixReadStageInput, expression.op = .noforward)

/-- **The matrix-MAU-writer data of one line.**  The matrix-MAU filter is the
writer alone and the line has no float-MAU row. -/
def WelcomePEMatrixMAUWriterDataFor (expressions : List NormalizedExpr) : Prop :=
  ∀ (e : ParsedExpr),
    e ∈ expressions.map NormalizedExpr.toParsed →
      parsedExprIsMatrixMAUProducer e = true →
      Issue.Bank.lm1 ∈ (e.toIssueExpr 0).writeBanks →
      (expressions.map NormalizedExpr.toParsed).filter
          parsedExprIsMatrixMAUProducer = [e] ∧
        (expressions.map NormalizedExpr.toParsed).filter
          parsedExprIsSupportedFloatMAUProducer = []

/-- **The `.l1bm`-broadcast-writer data of one line.**  The row lowers to a single
masked `.mem .lm1` destination of static width `w`, the L1BM-to-PE filter is the
writer alone, and the line has no float-MAU row. -/
def WelcomePEL1BMWriterDataFor (expressions : List NormalizedExpr) : Prop :=
  ∀ (e : ParsedExpr),
    e ∈ expressions.map NormalizedExpr.toParsed →
      parsedExprIsL1ToPEProducer e = true →
      Issue.Bank.lm1 ∈ (e.toIssueExpr 0).writeBanks →
      ∃ (access : ParsedL1ToPEAccess) (memoryAccess : Access)
        (negated extended rounded : Bool) (mask : Option ParsedMask) (w : PEMemory.Width),
        lowerParsedL1ToPE? e = some access ∧
          access.destinations =
            [ParsedOperand.mem memoryAccess negated extended rounded mask] ∧
          ParsedOperand.directDestinationBankWidth?
              (ParsedOperand.mem memoryAccess negated extended rounded mask) =
            some (PEMemory.Bank.lm1, w) ∧
          (expressions.map NormalizedExpr.toParsed).filter
            parsedExprIsL1ToPEProducer = [e] ∧
          (expressions.map NormalizedExpr.toParsed).filter
            parsedExprIsSupportedFloatMAUProducer = []

/-- The global plain-writer data package. -/
def WelcomePEPlainWriterData : Prop :=
  ∀ expressions, WelcomePEUnrefuted expressions → WelcomePEPlainWriterDataFor expressions

/-- The global `.matrixRead`-writer data package. -/
def WelcomePEMatrixReadWriterData : Prop :=
  ∀ expressions, WelcomePEUnrefuted expressions → WelcomePEMatrixReadWriterDataFor expressions

/-- The global float-MAU-writer data package. -/
def WelcomePEFloatMAUWriterData : Prop :=
  ∀ expressions, WelcomePEUnrefuted expressions → WelcomePEFloatMAUWriterDataFor expressions

/-- The global matrix-MAU-writer data package. -/
def WelcomePEMatrixMAUWriterData : Prop :=
  ∀ expressions, WelcomePEUnrefuted expressions → WelcomePEMatrixMAUWriterDataFor expressions

/-- The global `.l1bm`-writer data package. -/
def WelcomePEL1BMWriterData : Prop :=
  ∀ expressions, WelcomePEUnrefuted expressions → WelcomePEL1BMWriterDataFor expressions

/-- **The plain-writer line shape, from the line's writer-kind data.** -/
theorem welcomePEWriteShape_of_plainWriter_data (expressions : List NormalizedExpr)
    (data : WelcomePEPlainWriterDataFor expressions)
    (unrefuted : WelcomePEUnrefuted expressions) (e : ParsedExpr)
    (eMem : e ∈ expressions.map NormalizedExpr.toParsed)
    (plain : parsedExprIsPlainIntegerALU e = true)
    (writer : Issue.Bank.lm1 ∈ (e.toIssueExpr 0).writeBanks) :
    WelcomePEWriteShape expressions := by
  obtain ⟨before, after, split, skipBefore, skipAfter, floatEmpty, flagAndDouble | indep⟩ :=
    data e eMem plain writer
  · exact welcomePEWriteShape_of_plainWriter_unique expressions before after e split
      skipBefore skipAfter flagAndDouble.1 flagAndDouble.2
      (welcomeLm1Writer_nodup expressions unrefuted e eMem) plain floatEmpty
      (welcomeLm1Writer_rows expressions unrefuted e eMem writer)
  · exact Or.inr (Or.inr indep)

/-- **The `.matrixRead`-writer line shape, from the line's writer-kind data.** -/
theorem welcomePEWriteShape_of_matrixReadWriter_data (expressions : List NormalizedExpr)
    (data : WelcomePEMatrixReadWriterDataFor expressions)
    (unrefuted : WelcomePEUnrefuted expressions) (e : ParsedExpr)
    (eMem : e ∈ expressions.map NormalizedExpr.toParsed)
    (read : parsedExprIsMatrixReadProducer e = true)
    (writer : Issue.Bank.lm1 ∈ (e.toIssueExpr 0).writeBanks) :
    WelcomePEWriteShape expressions := by
  obtain ⟨before, after, precision, sideY, width, row, staticW, split, skipBefore, skipAfter,
    op, sources, staticWidth, floatEmpty⟩ := data e eMem read writer
  exact welcomePEWriteShape_of_matrixReadWriter_unique expressions before after e split
    skipBefore skipAfter precision sideY width row op sources staticW
    (welcomeLm1Writer_nodup expressions unrefuted e eMem) staticWidth floatEmpty
    (welcomeLm1Writer_rows expressions unrefuted e eMem writer)

/-- **The float-MAU-writer line shape, from the line's writer-kind data.** -/
theorem welcomePEWriteShape_of_floatMAUWriter_data (expressions : List NormalizedExpr)
    (data : WelcomePEFloatMAUWriterDataFor expressions)
    (unrefuted : WelcomePEUnrefuted expressions) (e : ParsedExpr)
    (eMem : e ∈ expressions.map NormalizedExpr.toParsed)
    (float : parsedExprIsSupportedFloatMAUProducer e = true)
    (writer : Issue.Bank.lm1 ∈ (e.toIssueExpr 0).writeBanks) :
    WelcomePEWriteShape expressions := by
  obtain ⟨floatFilter, intAll⟩ := data e eMem float writer
  exact welcomePEWriteShape_of_floatMAUWriter_unique expressions e float
    (welcomeLm1Writer_nodup expressions unrefuted e eMem) floatFilter intAll
    (welcomeLm1Writer_rows expressions unrefuted e eMem writer)

/-- **The matrix-MAU-writer line shape, from the line's writer-kind data.** -/
theorem welcomePEWriteShape_of_matrixMAUWriter_data (expressions : List NormalizedExpr)
    (data : WelcomePEMatrixMAUWriterDataFor expressions)
    (unrefuted : WelcomePEUnrefuted expressions) (e : ParsedExpr)
    (eMem : e ∈ expressions.map NormalizedExpr.toParsed)
    (mau : parsedExprIsMatrixMAUProducer e = true)
    (writer : Issue.Bank.lm1 ∈ (e.toIssueExpr 0).writeBanks) :
    WelcomePEWriteShape expressions := by
  obtain ⟨mauFilter, floatEmpty⟩ := data e eMem mau writer
  exact welcomePEWriteShape_of_matrixMAUWriter_unique expressions e mau
    (welcomeLm1Writer_nodup expressions unrefuted e eMem) mauFilter floatEmpty
    (welcomeLm1Writer_rows expressions unrefuted e eMem writer)

/-- **The `.l1bm`-writer line shape, from the line's writer-kind data.** -/
theorem welcomePEWriteShape_of_l1bmWriter_data (expressions : List NormalizedExpr)
    (data : WelcomePEL1BMWriterDataFor expressions)
    (unrefuted : WelcomePEUnrefuted expressions) (e : ParsedExpr)
    (eMem : e ∈ expressions.map NormalizedExpr.toParsed)
    (l1 : parsedExprIsL1ToPEProducer e = true)
    (writer : Issue.Bank.lm1 ∈ (e.toIssueExpr 0).writeBanks) :
    WelcomePEWriteShape expressions := by
  obtain ⟨access, memoryAccess, negated, extended, rounded, mask, w, lowered, destinations,
    static, l1Filter, floatEmpty⟩ := data e eMem l1 writer
  exact welcomePEWriteShape_of_l1bmWriter_unique expressions e access memoryAccess negated
    extended rounded mask w lowered destinations static l1Filter floatEmpty
    (welcomeLm1Writer_rows expressions unrefuted e eMem writer)

/-! ## 3. The cases with no dispatchable writer

If the unique `.lm1`-writing row is `.noforward`, `.wait`, a shared-block
`.l1bm` row, a `.matrixWrite` row or an `.l2bm` row, no stage writes an `.lm1`
word: `.noforward` / `.wait` rows prepare nothing, the shared-block stage is a
frame for every PE register file (`executeParsedSharedBlockProducers_peRegisters`),
and the matrix-write / L2BM stages never write a PE register file.  The same holds
when no row is a `.lm1` writer at all.  The value content of this case is exactly
"the line's stage commit list is `.lm1`-free", from which the write shape is
vacuous. -/

/-- **The line's stage commit list is `.lm1`-free.**  This is the provenance
statement of the "no `.lm1` word is written" case; it implies the write shape
(`welcomePEWriteShape_of_freeStageCommit`) but says nothing about the shape of any
`.double` block or window.  It is the per-line form used by
`WelcomePELm1LineDispatchData`. -/
def WelcomePELm1FreeStageCommit (expressions : List NormalizedExpr) : Prop :=
  ∀ next, welcomeSealedMachine.step (.pe expressions)
      (welcomeInitialState welcomeZeroWords) = some next →
    ∃ writes : List PreparedParsedMaskedWrite,
      next.peRegisters welcomePE =
        commitParsedMaskedWrites
          ((welcomeInitialState welcomeZeroWords).peRegisters welcomePE) writes ∧
      Lm1FreePreparedWrites writes

/-- **An `.lm1`-free stage list gives the line shape.**  Both `Lm1Writes*`
predicates hold vacuously: the list has no `.lm1` destination to inspect. -/
theorem welcomePEWriteShape_of_freeStageCommit (expressions : List NormalizedExpr)
    (free : WelcomePELm1FreeStageCommit expressions) :
    WelcomePEWriteShape expressions := by
  apply welcomePEWriteShape_of_commit_shape
  intro next step
  obtain ⟨writes, committed, freeWrites⟩ := free next step
  refine ⟨writes, committed, Or.inl ?_⟩
  intro write member width address data selection destination dataEq selectionEq
  exact absurd rfl (isLm1Write_false_bank write (freeWrites write member)
    ⟨PEMemory.Bank.lm1, width, address⟩ destination)

/-- The phantom-writer kind of a row: a row whose stage writes no PE register file
at all. -/
def welcomePhantomWriterKind (expression : ParsedExpr) : Prop :=
  expression.op = .noforward ∨ (∃ tag : Fin 256, expression.op = .wait tag) ∨
    parsedExprIsL1SharedBlockProducer expression = true ∨
    parsedExprIsMatrixWriteProducer expression = true ∨
    parsedExprIsL2BMProducer expression = true

/-- **The phantom/no-writer provenance (global form).**  If every `.lm1`-writing
row of an unrefuted line is a phantom row, then the line's stage commit list is
`.lm1`-free.

The statement is true; it is not proved here.  Its proof reduces to two
ingredients that are not available in the imported modules:

* the **float-MAU list-level provenance** — only the bank frame
  `executeParsedFloatMAUsAtPE_lm1_free` exists, and the integer stage commits the
  prepared integer list followed by the float list.  (`WelcomeFloatProvenance.lean`
  in the working tree, not imported here, targets exactly this provenance.)
* the integer-stage provenance refined at `.noforward` / `.wait` rows — those rows
  contribute no write even when their destination operands name bank `.lm1`,
  while `WelcomePEIntegerStageLm1Provenance` demands `.lm1`-free destinations of
  every integer-stage row.

The four middle stages' list-level provenance *is* available
(`WelcomePEStageLm1ProvenanceForm`), and the shared-block frame is unconditional. -/
def WelcomePELm1PhantomWriterProvenance : Prop :=
  ∀ (expressions : List NormalizedExpr), WelcomePEUnrefuted expressions →
    (∀ e ∈ expressions.map NormalizedExpr.toParsed,
      Issue.Bank.lm1 ∈ (e.toIssueExpr 0).writeBanks →
        welcomePhantomWriterKind e) →
    WelcomePELm1FreeStageCommit expressions

/-- **The special-ALU writer case.**  When the line's unique `.lm1` writer is an
`msl`/`msr`, float-relu or block-float row, the line satisfies the write shape.

The row shapes exist (`welcomePEMslMsrCyclesShape` is proved,
`welcomePEFloatReluCyclesShape` is proved, and the block-float shapes are
`welcomePEBlockFloatMabShape_of_precision_low_zero`), but assembling a row shape
into the line shape needs the stage fold over coordinates / cycles, exactly as the
five dispatch theorems do for their stages.  That assembly is the content of this
`Prop`; it is the only shape-level residual of this module. -/
def WelcomePESpecialALUWriterShapeObligation : Prop :=
  ∀ (expressions : List NormalizedExpr), WelcomePEUnrefuted expressions →
    (∃ e ∈ expressions.map NormalizedExpr.toParsed,
      Issue.Bank.lm1 ∈ (e.toIssueExpr 0).writeBanks ∧
        parsedExprIsSpecialALUProducer e = true) →
    WelcomePEWriteShape expressions

/-- **The no-writer case on integer-or-inert lines is unconditional.**  If no row
is a `.lm1` writer and every row is an integer-stage input or PE-inert, then no
row has an `.lm1` destination operand (§1), so the integer stage's list is
`.lm1`-free (`welcomePEWriteShape_of_noLm1Rows`). -/
theorem welcomePEWriteShape_of_noWriter_of_integerOrInert
    (expressions : List NormalizedExpr) (unrefuted : WelcomePEUnrefuted expressions)
    (intOrInert : (expressions.map NormalizedExpr.toParsed).all
      welcomeIntegerOrInertLine = true)
    (noWriter : ∀ e ∈ expressions.map NormalizedExpr.toParsed,
      Issue.Bank.lm1 ∉ (e.toIssueExpr 0).writeBanks) :
    WelcomePEWriteShape expressions :=
  welcomePEWriteShape_of_noLm1Rows expressions unrefuted intOrInert
    (fun expression member =>
      welcomeRowHasNoLm1Destination_of_writeBanks_not_mem expression 0
        (noWriter expression (List.mem_of_mem_filter member)))

/-! ## 4. The per-line dispatch data and the aggregate -/

/-- **The per-line dispatch data.**  For one unrefuted line, one of the following
holds:

* the line's `.lm1` writer is a special-ALU row (the shape then comes from
  `WelcomePESpecialALUWriterShapeObligation`);
* the line's `.lm1` writer is plain / `.matrixRead` / float-MAU / matrix-MAU /
  `.l1bm` and the corresponding writer-kind data of §2 is available;
* every `.lm1`-writing row is a phantom row and the line's stage commit list is
  `.lm1`-free.

This is the exact form in which the assembly consumes the syntactic remainder:
`welcomePEWriteShape_of_lineData` turns it into the line's write shape. -/
def WelcomePELm1LineDispatchData (expressions : List NormalizedExpr) : Prop :=
  (∃ e ∈ expressions.map NormalizedExpr.toParsed,
      Issue.Bank.lm1 ∈ (e.toIssueExpr 0).writeBanks ∧
        parsedExprIsSpecialALUProducer e = true) ∨
    (WelcomePEPlainWriterDataFor expressions ∧
      ∃ e ∈ expressions.map NormalizedExpr.toParsed,
        Issue.Bank.lm1 ∈ (e.toIssueExpr 0).writeBanks ∧
          parsedExprIsPlainIntegerALU e = true) ∨
    (WelcomePEMatrixReadWriterDataFor expressions ∧
      ∃ e ∈ expressions.map NormalizedExpr.toParsed,
        Issue.Bank.lm1 ∈ (e.toIssueExpr 0).writeBanks ∧
          parsedExprIsMatrixReadProducer e = true) ∨
    (WelcomePEFloatMAUWriterDataFor expressions ∧
      ∃ e ∈ expressions.map NormalizedExpr.toParsed,
        Issue.Bank.lm1 ∈ (e.toIssueExpr 0).writeBanks ∧
          parsedExprIsSupportedFloatMAUProducer e = true) ∨
    (WelcomePEMatrixMAUWriterDataFor expressions ∧
      ∃ e ∈ expressions.map NormalizedExpr.toParsed,
        Issue.Bank.lm1 ∈ (e.toIssueExpr 0).writeBanks ∧
          parsedExprIsMatrixMAUProducer e = true) ∨
    (WelcomePEL1BMWriterDataFor expressions ∧
      ∃ e ∈ expressions.map NormalizedExpr.toParsed,
        Issue.Bank.lm1 ∈ (e.toIssueExpr 0).writeBanks ∧
          parsedExprIsL1ToPEProducer e = true) ∨
    ((∀ e ∈ expressions.map NormalizedExpr.toParsed,
        Issue.Bank.lm1 ∈ (e.toIssueExpr 0).writeBanks → welcomePhantomWriterKind e) ∧
      WelcomePELm1FreeStageCommit expressions)

/-- **The per-line write shape from the per-line dispatch data.**  This is the
usable form of the assembly: for each line, once its dispatch data (§4) and the
special-ALU writer case are available, the line's shape follows. -/
theorem welcomePEWriteShape_of_lineData (expressions : List NormalizedExpr)
    (unrefuted : WelcomePEUnrefuted expressions)
    (special : WelcomePESpecialALUWriterShapeObligation)
    (data : WelcomePELm1LineDispatchData expressions) :
    WelcomePEWriteShape expressions := by
  rcases data with ⟨e, eMem, eWriter, kind⟩ | ⟨plainData, e, eMem, eWriter, kind⟩ |
    ⟨readData, e, eMem, eWriter, kind⟩ | ⟨floatData, e, eMem, eWriter, kind⟩ |
    ⟨mauData, e, eMem, eWriter, kind⟩ | ⟨l1Data, e, eMem, eWriter, kind⟩ |
    ⟨-, free⟩
  · exact special expressions unrefuted ⟨e, eMem, eWriter, kind⟩
  · exact welcomePEWriteShape_of_plainWriter_data expressions plainData unrefuted e eMem
      kind eWriter
  · exact welcomePEWriteShape_of_matrixReadWriter_data expressions readData unrefuted e eMem
      kind eWriter
  · exact welcomePEWriteShape_of_floatMAUWriter_data expressions floatData unrefuted e eMem
      kind eWriter
  · exact welcomePEWriteShape_of_matrixMAUWriter_data expressions mauData unrefuted e eMem
      kind eWriter
  · exact welcomePEWriteShape_of_l1bmWriter_data expressions l1Data unrefuted e eMem
      kind eWriter
  · exact welcomePEWriteShape_of_freeStageCommit expressions free

/-- The special-ALU writer selects the first disjunct of the per-line data. -/
theorem welcomePELm1LineDispatchData_special (expressions : List NormalizedExpr)
    (e : ParsedExpr) (eMem : e ∈ expressions.map NormalizedExpr.toParsed)
    (eWriter : Issue.Bank.lm1 ∈ (e.toIssueExpr 0).writeBanks)
    (special : parsedExprIsSpecialALUProducer e = true) :
    WelcomePELm1LineDispatchData expressions :=
  Or.inl ⟨e, eMem, eWriter, special⟩

/-- A plain writer with its line data selects the second disjunct. -/
theorem welcomePELm1LineDispatchData_plain (expressions : List NormalizedExpr)
    (data : WelcomePEPlainWriterDataFor expressions) (e : ParsedExpr)
    (eMem : e ∈ expressions.map NormalizedExpr.toParsed)
    (eWriter : Issue.Bank.lm1 ∈ (e.toIssueExpr 0).writeBanks)
    (plain : parsedExprIsPlainIntegerALU e = true) :
    WelcomePELm1LineDispatchData expressions :=
  Or.inr (Or.inl ⟨data, e, eMem, eWriter, plain⟩)

/-- A `.matrixRead` writer with its line data selects the third disjunct. -/
theorem welcomePELm1LineDispatchData_matrixRead (expressions : List NormalizedExpr)
    (data : WelcomePEMatrixReadWriterDataFor expressions) (e : ParsedExpr)
    (eMem : e ∈ expressions.map NormalizedExpr.toParsed)
    (eWriter : Issue.Bank.lm1 ∈ (e.toIssueExpr 0).writeBanks)
    (read : parsedExprIsMatrixReadProducer e = true) :
    WelcomePELm1LineDispatchData expressions :=
  Or.inr (Or.inr (Or.inl ⟨data, e, eMem, eWriter, read⟩))

/-- A float-MAU writer with its line data selects the fourth disjunct. -/
theorem welcomePELm1LineDispatchData_floatMAU (expressions : List NormalizedExpr)
    (data : WelcomePEFloatMAUWriterDataFor expressions) (e : ParsedExpr)
    (eMem : e ∈ expressions.map NormalizedExpr.toParsed)
    (eWriter : Issue.Bank.lm1 ∈ (e.toIssueExpr 0).writeBanks)
    (float : parsedExprIsSupportedFloatMAUProducer e = true) :
    WelcomePELm1LineDispatchData expressions :=
  Or.inr (Or.inr (Or.inr (Or.inl ⟨data, e, eMem, eWriter, float⟩)))

/-- A matrix-MAU writer with its line data selects the fifth disjunct. -/
theorem welcomePELm1LineDispatchData_matrixMAU (expressions : List NormalizedExpr)
    (data : WelcomePEMatrixMAUWriterDataFor expressions) (e : ParsedExpr)
    (eMem : e ∈ expressions.map NormalizedExpr.toParsed)
    (eWriter : Issue.Bank.lm1 ∈ (e.toIssueExpr 0).writeBanks)
    (mau : parsedExprIsMatrixMAUProducer e = true) :
    WelcomePELm1LineDispatchData expressions :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨data, e, eMem, eWriter, mau⟩))))

/-- A `.l1bm` writer with its line data selects the sixth disjunct. -/
theorem welcomePELm1LineDispatchData_l1bm (expressions : List NormalizedExpr)
    (data : WelcomePEL1BMWriterDataFor expressions) (e : ParsedExpr)
    (eMem : e ∈ expressions.map NormalizedExpr.toParsed)
    (eWriter : Issue.Bank.lm1 ∈ (e.toIssueExpr 0).writeBanks)
    (l1 : parsedExprIsL1ToPEProducer e = true) :
    WelcomePELm1LineDispatchData expressions :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨data, e, eMem, eWriter, l1⟩)))))

/-- The phantom/no-writer case selects the seventh disjunct. -/
theorem welcomePELm1LineDispatchData_phantom (expressions : List NormalizedExpr)
    (h : ∀ e ∈ expressions.map NormalizedExpr.toParsed,
      Issue.Bank.lm1 ∈ (e.toIssueExpr 0).writeBanks → welcomePhantomWriterKind e)
    (free : WelcomePELm1FreeStageCommit expressions) :
    WelcomePELm1LineDispatchData expressions :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h, free⟩)))))

/-- **The per-line dispatch data from the global packages.**  The case split is
the exhaustive `supportedProducer_partition` of the line's `.lm1` writer: plain,
one of the six families, one of the three special-ALU families, PE-inert, or
Rust-unsupported.  The unsupported case contradicts acceptance; the six families
and the three special-ALU families select the corresponding disjunct; the
PE-inert, `.matrixWrite` and `.l2bm` writers are the phantom case; with no writer
the phantom case is vacuous. -/
theorem welcomePELm1LineDispatchData_of_components
    (phantom : WelcomePELm1PhantomWriterProvenance)
    (plain : WelcomePEPlainWriterData) (read : WelcomePEMatrixReadWriterData)
    (float : WelcomePEFloatMAUWriterData) (mau : WelcomePEMatrixMAUWriterData)
    (l1 : WelcomePEL1BMWriterData)
    (expressions : List NormalizedExpr) (unrefuted : WelcomePEUnrefuted expressions) :
    WelcomePELm1LineDispatchData expressions := by
  by_cases hasWriter : ∃ e ∈ expressions.map NormalizedExpr.toParsed,
      Issue.Bank.lm1 ∈ (e.toIssueExpr 0).writeBanks
  · obtain ⟨e, eMem, eWriter⟩ := hasWriter
    have supported := List.all_eq_true.mp unrefuted.1.2.2.2 e eMem
    have notUnsupported : parsedExprIsUnsupportedRustAlu e = false := by
      simpa using (List.any_eq_false.mp unrefuted.1.2.2.1) e eMem
    rcases supportedProducer_partition e supported with
      isPlain | isFamily | isSpecial | isInert | isUnsupported
    · exact welcomePELm1LineDispatchData_plain expressions (plain expressions unrefuted) e
        eMem eWriter isPlain
    · rcases parsedExprIsFamilyProducer_cases e isFamily with
        readKind | mauKind | floatKind | writeKind | toPEKind | l2Kind
      · exact welcomePELm1LineDispatchData_matrixRead expressions (read expressions unrefuted) e
          eMem eWriter readKind
      · exact welcomePELm1LineDispatchData_matrixMAU expressions (mau expressions unrefuted) e
          eMem eWriter mauKind
      · exact welcomePELm1LineDispatchData_floatMAU expressions (float expressions unrefuted) e
          eMem eWriter floatKind
      · have hphantom : ∀ x ∈ expressions.map NormalizedExpr.toParsed,
            Issue.Bank.lm1 ∈ (x.toIssueExpr 0).writeBanks → welcomePhantomWriterKind x := by
          intro x xMem xWriter
          have same : x = e :=
            welcomeLm1Writer_eq_of_two expressions unrefuted xMem eMem xWriter eWriter
          rw [same]
          exact Or.inr (Or.inr (Or.inr (Or.inl writeKind)))
        exact welcomePELm1LineDispatchData_phantom expressions hphantom
          (phantom expressions unrefuted hphantom)
      · exact welcomePELm1LineDispatchData_l1bm expressions (l1 expressions unrefuted) e
          eMem eWriter toPEKind
      · have hphantom : ∀ x ∈ expressions.map NormalizedExpr.toParsed,
            Issue.Bank.lm1 ∈ (x.toIssueExpr 0).writeBanks → welcomePhantomWriterKind x := by
          intro x xMem xWriter
          have same : x = e :=
            welcomeLm1Writer_eq_of_two expressions unrefuted xMem eMem xWriter eWriter
          rw [same]
          exact Or.inr (Or.inr (Or.inr (Or.inr l2Kind)))
        exact welcomePELm1LineDispatchData_phantom expressions hphantom
          (phantom expressions unrefuted hphantom)
    · exact welcomePELm1LineDispatchData_special expressions e eMem eWriter isSpecial
    · have hphantom : ∀ x ∈ expressions.map NormalizedExpr.toParsed,
          Issue.Bank.lm1 ∈ (x.toIssueExpr 0).writeBanks → welcomePhantomWriterKind x := by
        intro x xMem xWriter
        have same : x = e :=
          welcomeLm1Writer_eq_of_two expressions unrefuted xMem eMem xWriter eWriter
        rw [same]
        rcases parsedExprIsPEInertProducer_cases e isInert with forward | wait | shared
        · exact Or.inl forward
        · exact Or.inr (Or.inl wait)
        · exact Or.inr (Or.inr (Or.inl shared))
      exact welcomePELm1LineDispatchData_phantom expressions hphantom
        (phantom expressions unrefuted hphantom)
    · rw [notUnsupported] at isUnsupported
      cases isUnsupported
  · have hphantom : ∀ x ∈ expressions.map NormalizedExpr.toParsed,
        Issue.Bank.lm1 ∈ (x.toIssueExpr 0).writeBanks → welcomePhantomWriterKind x := by
      intro x xMem xWriter
      exact absurd ⟨x, xMem, xWriter⟩ hasWriter
    exact welcomePELm1LineDispatchData_phantom expressions hphantom
      (phantom expressions unrefuted hphantom)

/-- **The global residual bundle.**  The special-ALU writer case, and the per-line
dispatch data for every unrefuted line. -/
def WelcomePEDispatchResiduals : Prop :=
  WelcomePESpecialALUWriterShapeObligation ∧
    ∀ expressions, WelcomePEUnrefuted expressions →
      WelcomePELm1LineDispatchData expressions

/-- **`WelcomePELm1WriteShapeObligation` from the residual bundle.** -/
theorem welcomePELm1WriteShapeObligation_of_dispatch
    (residuals : WelcomePEDispatchResiduals) :
    WelcomePELm1WriteShapeObligation := by
  obtain ⟨special, data⟩ := residuals
  intro expressions unrefuted
  exact welcomePEWriteShape_of_lineData expressions unrefuted special
    (data expressions unrefuted)

/-- **The lower bound from the residual bundle** (through
`welcomeLowerBound_two_of_lm1WriteShapes`). -/
theorem welcomeLowerBound_two_of_dispatch (residuals : WelcomePEDispatchResiduals) :
    ProofsLean.LowerBound welcomeSealedMachine welcomeSpec 2 :=
  welcomeLowerBound_two_of_lm1WriteShapes
    (welcomePELm1WriteShapeObligation_of_dispatch residuals)

/-- **`Optimal` from the residual bundle** (through
`welcomeAnswer_optimal_of_lm1WriteShapes`; `welcomeAnswer_correct` is already
proved, so the lower bound gives optimality). -/
theorem welcomeAnswer_optimal_of_dispatch (residuals : WelcomePEDispatchResiduals) :
    ProofsLean.Optimal welcomeSealedMachine welcomeSpec welcomeAnswer :=
  welcomeAnswer_optimal_of_lm1WriteShapes
    (welcomePELm1WriteShapeObligation_of_dispatch residuals)

/-! ## 5. Splitting the special-ALU writer case, and the component forms

The special-ALU case of §3 is the only shape-level residual.  It splits into the
three stages that execute such rows, so each can be closed independently (the
`msl`/`msr` row shape `welcomePEMslMsrCyclesShape` is already proved, the
float-relu one `welcomePEFloatReluCyclesShape` is already proved, and the
block-float per-coordinate shape is
`welcomePEBlockFloatMabShape_of_precision_low_zero`; what each still needs is the
stage fold from the row shape to the line shape). -/

/-- The `msl`/`msr` writer case. -/
def WelcomePEMslMsrWriterShapeObligation : Prop :=
  ∀ (expressions : List NormalizedExpr), WelcomePEUnrefuted expressions →
    (∃ e ∈ expressions.map NormalizedExpr.toParsed,
      Issue.Bank.lm1 ∈ (e.toIssueExpr 0).writeBanks ∧
        parsedExprIsMslMsrProducer e = true) →
    WelcomePEWriteShape expressions

/-- The float-relu writer case. -/
def WelcomePEFloatReluWriterShapeObligation : Prop :=
  ∀ (expressions : List NormalizedExpr), WelcomePEUnrefuted expressions →
    (∃ e ∈ expressions.map NormalizedExpr.toParsed,
      Issue.Bank.lm1 ∈ (e.toIssueExpr 0).writeBanks ∧
        parsedExprIsFloatReluProducer e = true) →
    WelcomePEWriteShape expressions

/-- The block-float writer case. -/
def WelcomePEBlockFloatWriterShapeObligation : Prop :=
  ∀ (expressions : List NormalizedExpr), WelcomePEUnrefuted expressions →
    (∃ e ∈ expressions.map NormalizedExpr.toParsed,
      Issue.Bank.lm1 ∈ (e.toIssueExpr 0).writeBanks ∧
        parsedExprIsBlockFloatProducer e = true) →
    WelcomePEWriteShape expressions

/-- **The special-ALU writer case is weaker than the family-wide special-ALU
obligation.**  `WelcomePESpecialALUShapeObligation` quantifies over every line
*containing* a special-ALU row; the writer case only concerns the lines whose
`.lm1` writer is that row, so progress on the existing residual gives this one. -/
theorem welcomePESpecialALUWriterShapeObligation_of_special
    (special : WelcomePESpecialALUShapeObligation) :
    WelcomePESpecialALUWriterShapeObligation := by
  intro expressions unrefuted ⟨e, eMem, eWriter, kind⟩
  exact special expressions unrefuted (List.any_eq_true.mpr ⟨e, eMem, kind⟩)

/-- **The special-ALU writer case from its three stages.** -/
theorem welcomePESpecialALUWriterShapeObligation_of_three
    (msl : WelcomePEMslMsrWriterShapeObligation)
    (relu : WelcomePEFloatReluWriterShapeObligation)
    (block : WelcomePEBlockFloatWriterShapeObligation) :
    WelcomePESpecialALUWriterShapeObligation := by
  intro expressions unrefuted ⟨e, eMem, eWriter, special⟩
  rcases parsedExprIsSpecialALUProducer_cases e special with isMsl | isRelu | isBlock
  · exact msl expressions unrefuted ⟨e, eMem, eWriter, isMsl⟩
  · exact relu expressions unrefuted ⟨e, eMem, eWriter, isRelu⟩
  · exact block expressions unrefuted ⟨e, eMem, eWriter, isBlock⟩

/-- **The per-line write-shape obligation from the nine components.**  This is the
component form of `welcomePELm1WriteShapeObligation_of_dispatch`: the phantom
provenance, the five writer-kind data packages, and the three special-ALU writer
cases. -/
theorem welcomePELm1WriteShapeObligation_of_components
    (phantom : WelcomePELm1PhantomWriterProvenance)
    (plain : WelcomePEPlainWriterData)
    (read : WelcomePEMatrixReadWriterData)
    (float : WelcomePEFloatMAUWriterData)
    (mau : WelcomePEMatrixMAUWriterData)
    (l1 : WelcomePEL1BMWriterData)
    (msl : WelcomePEMslMsrWriterShapeObligation)
    (relu : WelcomePEFloatReluWriterShapeObligation)
    (block : WelcomePEBlockFloatWriterShapeObligation) :
    WelcomePELm1WriteShapeObligation :=
  welcomePELm1WriteShapeObligation_of_dispatch
    ⟨welcomePESpecialALUWriterShapeObligation_of_three msl relu block,
      fun expressions unrefuted =>
        welcomePELm1LineDispatchData_of_components phantom plain read float mau l1
          expressions unrefuted⟩

/-- **`LowerBound 2` from the nine components.** -/
theorem welcomeLowerBound_two_of_components
    (phantom : WelcomePELm1PhantomWriterProvenance)
    (plain : WelcomePEPlainWriterData)
    (read : WelcomePEMatrixReadWriterData)
    (float : WelcomePEFloatMAUWriterData)
    (mau : WelcomePEMatrixMAUWriterData)
    (l1 : WelcomePEL1BMWriterData)
    (msl : WelcomePEMslMsrWriterShapeObligation)
    (relu : WelcomePEFloatReluWriterShapeObligation)
    (block : WelcomePEBlockFloatWriterShapeObligation) :
    ProofsLean.LowerBound welcomeSealedMachine welcomeSpec 2 :=
  welcomeLowerBound_two_of_lm1WriteShapes
    (welcomePELm1WriteShapeObligation_of_components phantom plain read float mau l1
      msl relu block)

/-- **`Optimal` from the nine components.** -/
theorem welcomeAnswer_optimal_of_components
    (phantom : WelcomePELm1PhantomWriterProvenance)
    (plain : WelcomePEPlainWriterData)
    (read : WelcomePEMatrixReadWriterData)
    (float : WelcomePEFloatMAUWriterData)
    (mau : WelcomePEMatrixMAUWriterData)
    (l1 : WelcomePEL1BMWriterData)
    (msl : WelcomePEMslMsrWriterShapeObligation)
    (relu : WelcomePEFloatReluWriterShapeObligation)
    (block : WelcomePEBlockFloatWriterShapeObligation) :
    ProofsLean.Optimal welcomeSealedMachine welcomeSpec welcomeAnswer :=
  welcomeAnswer_optimal_of_lm1WriteShapes
    (welcomePELm1WriteShapeObligation_of_components phantom plain read float mau l1
      msl relu block)

end ProofsLean.MNCore

