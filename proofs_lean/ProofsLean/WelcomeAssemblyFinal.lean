import ProofsLean.WelcomeHalfBlockFloat
import ProofsLean.WelcomeResiduals
import ProofsLean.WelcomeFlagFreePlain
import ProofsLean.WelcomeSlotFree

/-! # The final Welcome assembly: the exact writer-kind data that is still needed

This module assembles `WelcomePELm1WriteShapeObligation` from the strongest
available pieces of rounds 46–48 and records precisely which per-line writer-kind
data packages remain as hypotheses.

## What is unconditional

The global residual bundle `WelcomePEDispatchResiduals` of
`WelcomeFinalShape.lean` had nine components.  After rounds 47–48 four of them
are theorems and the module below proves a fifth:

* **the phantom provenance** `WelcomePELm1PhantomWriterProvenance`
  (`welcomePELm1PhantomWriterProvenance`, `WelcomeResiduals.lean`): a line whose
  every `.lm1`-writing row is `.noforward`, an incomplete `.wait`, a shared-block
  `.l1bm` row, a `.matrixWrite` row or an `.l2bm` row (or which has no `.lm1`
  writer at all) commits an `.lm1`-free stage list;
* **the special-ALU writer obligation**
  `WelcomePESpecialALUWriterShapeObligation`
  (`welcomePESpecialALUWriterShapeObligation`, `WelcomeHalfBlockFloat.lean`),
  through its three unconditional stages `welcomePEMslMsrWriterShapeObligation`,
  `welcomePEFloatReluWriterShapeObligation` (`WelcomeResiduals.lean`) and
  `welcomePEBlockFloatWriterShapeObligation` (`WelcomeHalfBlockFloat.lean`, the
  `.h` half-precision case included);
* **the matrix-MAU writer data** `WelcomePEMatrixMAUWriterData`
  (`welcomePEMatrixMAUWriterData`, §2 below).  A matrix-MAU row is a `.mau` row,
  and `groupsUnique` — the second conjunct of the issue checker's `Legal` —
  forbids two rows of the same issue group in an accepted line, so an unrefuted
  line has **at most one** `.mau` row.  The matrix-MAU family filter is therefore
  the writer alone, and the float-MAU filter (whose rows are `.mau` rows too, in a
  disjoint family) is empty.  The two side conditions of
  `WelcomePEMatrixMAUWriterDataFor` are exactly those two facts.

The **plain** writer additionally has an unconditional *row shape* in the
strongest form available: `plainRow_lm1_shape_of_linePrep_anyFlag`
(`WelcomeFlagFreePlain.lean`) holds at arbitrary forwarding slots and at
arbitrary mask flag, so the round-46 flag equation and the round-46 companion
restriction are gone.  What the plain *data package* still carries is not the row
shape but the line-level side conditions listed below.

## What is still a hypothesis

After substituting the three unconditional components, the aggregate
`welcomePELm1WriteShapeObligation_of_componentsFlagFree` of
`WelcomeFlagFreePlain.lean` needs four per-line data packages (each a `Prop`):

1. `WelcomePEPlainWriterDataFlagFree`: for the line's plain `.lm1` writer `e`,
   the split of the integer-stage filter at `e` with `e` occurring once,
   **no float-MAU row in the line** (`filter … = []`), and the immediate-`.double`
   exclusion `notDouble` **or** `WelcomePEInputIndependent`.
2. `WelcomePEMatrixReadWriterDataSlotFree`: the same split for a `.matrixRead`
   writer, plus `e.op = .matrixRead _`, `e.sources = [.matrix sideY width (some row)]`,
   a static `.lm1` width, and no float-MAU row in the line.
3. `WelcomePEFloatMAUWriterData`: the float-MAU filter is the writer alone and
   every integer-stage row of the line is `.noforward`.
4. `WelcomePEL1BMWriterData`: the `.l1bm` writer lowers to a single masked
   `.lm1` destination of static width, the L1-to-PE filter is the writer alone,
   and the line has no float-MAU row.

Each of the four is a restriction of a row-shape theorem that *is* proved (the
row shapes are `plainRow_lm1_shape_of_linePrep_anyFlag`,
`matrixReadRow_lm1_shape_of_startSlots`, the float-MAU writer row shape and the
`.l1bm` writer row shape of rounds 41–44); the restriction is the line-level
bookkeeping, not the per-row value argument.  The components that remain
genuinely open are

* the **absence of float-MAU companions** in packages 1, 2 and 4 — a float-MAU
  row that is not the `.lm1` writer is not covered by the float-MAU dispatch,
  and the plain / matrix-read / `.l1bm` line shapes currently demand an empty
  float filter rather than the (derivable) `.lm1`-freeness of the float stage;
* the **immediate-`.double` case** of package 1, whose only available value
  theorem (`welcomePEPlainImmediateDoubleObligation`) is stated for all-plain
  lines, and whose mixed-line form
  (`welcomePEMixedImmediateDouble_inputIndependent`) requires the other rows to
  be `.noforward` / `.wait` inert rows;
* the **all-`.noforward` integer stage** of package 3 and the **singleton L1
  filter** of package 4, which exclude lines whose writer shares its stage with
  another preparing row.

The per-line split-at-`e` components are syntactic: §1 proves that an accepted
line has no duplicate rows (`welcomeLine_nodup`), so a row occurs at most once in
any filter, and `welcomeLm1Writer_unique` gives `.lm1`-writer uniqueness.  §2
below uses the same "at most one row per issue group" tool for the matrix-MAU
family.

No `sorry`, no `admit`, no `native_decide`, no new axioms, and no existing module
is edited by this file.
-/

namespace ProofsLean.MNCore

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open Issue
open PEMemory

/-! ## 1. Issue groups, row injectivity, and singleton family filters

The issue checker's `groupsUnique` says that two projected rows with different ids
have different issue groups.  `projectLine` numbers rows by position, so no two
positions can carry rows of the same group.  This gives the "at most one row per
group" tool used in §2. -/

/-- Every expression carries an issue group. -/
theorem issueGroup_exists (expression : ParsedExpr) :
    ∃ group : Issue.Group, expression.issueGroup = some group := by
  rcases expression with ⟨op, sources, destinations, flush, text⟩
  cases op with
  | l1bm operation =>
      by_cases h : (⟨.l1bm operation, sources, destinations, flush, text⟩ :
        ParsedExpr).hasTurnaround = true
      · exact ⟨Issue.Group.l1bmTurnaround, by simp [ParsedExpr.issueGroup, h]⟩
      · exact ⟨Issue.Group.l1bm, by simp [ParsedExpr.issueGroup, h]⟩
  | l2bm operation => cases operation <;> exact ⟨_, rfl⟩
  | alu name precision unsigned arg => exact ⟨_, rfl⟩
  | immediate value unsigned => exact ⟨_, rfl⟩
  | zero => exact ⟨_, rfl⟩
  | mau precision matrix kind half round => exact ⟨_, rfl⟩
  | matrixWrite precision => exact ⟨_, rfl⟩
  | matrixRead precision => exact ⟨_, rfl⟩
  | wait tag => exact ⟨_, rfl⟩
  | noforward => exact ⟨_, rfl⟩

/-- **An accepted line has no duplicate rows.**  `projectLine` numbers the rows
by position, so two equal rows at distinct positions would be two projected rows
with distinct ids and the same issue group, which `groupsUnique` forbids. -/
theorem welcomeLine_nodup (line : List ParsedExpr) (legal : LegalParsedLine line) :
    line.Nodup := by
  rw [List.nodup_iff_injective_getElem]
  intro i j hij
  by_contra hne
  have hij' : line[i.1] = line[j.1] := hij
  have hval : i.1 ≠ j.1 := fun h => hne (Fin.ext h)
  obtain ⟨g, hg⟩ := issueGroup_exists (line[i.1]'i.isLt)
  have hgj : (line[j.1]'j.isLt).issueGroup = some g := by
    rw [← hij']
    exact hg
  have projLength : (projectLine line).length = line.length := projectFrom_length 0 line
  have iLt : i.1 < (projectLine line).length := by rw [projLength]; exact i.isLt
  have jLt : j.1 < (projectLine line).length := by rw [projLength]; exact j.isLt
  have gi : (projectLine line)[i.1]'iLt = (line[i.1]'i.isLt).toIssueExpr i.1 := by
    show (projectFrom 0 line)[i.1]'iLt = _
    simpa using projectFrom_getElem_toIssueExpr 0 line i.1 iLt i.isLt
  have gj : (projectLine line)[j.1]'jLt = (line[j.1]'j.isLt).toIssueExpr j.1 := by
    show (projectFrom 0 line)[j.1]'jLt = _
    simpa using projectFrom_getElem_toIssueExpr 0 line j.1 jLt j.isLt
  have idNe : ((projectLine line)[i.1]'iLt).id ≠ ((projectLine line)[j.1]'jLt).id := by
    rw [gi, gj]
    exact hval
  have groupI : ((projectLine line)[i.1]'iLt).group = some g := by
    rw [gi]; exact hg
  have groupJ : ((projectLine line)[j.1]'jLt).group = some g := by
    rw [gj]; exact hgj
  exact legal.2.1 ((projectLine line)[i.1]'iLt) (List.getElem_mem iLt)
    ((projectLine line)[j.1]'jLt) (List.getElem_mem jLt) idNe g groupI
    (by simp [groupJ])

/-- **Two rows of the same issue group are equal.** -/
theorem welcomeLine_eq_of_group (line : List ParsedExpr) (legal : LegalParsedLine line)
    {x y : ParsedExpr} (hx : x ∈ line) (hy : y ∈ line) (group : Issue.Group)
    (xg : x.issueGroup = some group) (yg : y.issueGroup = some group) : x = y := by
  by_contra hxy
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hy
  have hij : i ≠ j := by
    intro same
    subst same
    exact hxy rfl
  have projLength : (projectLine line).length = line.length := projectFrom_length 0 line
  have iLt : i < (projectLine line).length := by rw [projLength]; exact hi
  have jLt : j < (projectLine line).length := by rw [projLength]; exact hj
  have gi : (projectLine line)[i]'iLt = (line[i]'hi).toIssueExpr i := by
    show (projectFrom 0 line)[i]'iLt = _
    simpa using projectFrom_getElem_toIssueExpr 0 line i iLt hi
  have gj : (projectLine line)[j]'jLt = (line[j]'hj).toIssueExpr j := by
    show (projectFrom 0 line)[j]'jLt = _
    simpa using projectFrom_getElem_toIssueExpr 0 line j jLt hj
  have idNe : ((projectLine line)[i]'iLt).id ≠ ((projectLine line)[j]'jLt).id := by
    rw [gi, gj]
    exact hij
  have groupI : ((projectLine line)[i]'iLt).group = some group := by
    rw [gi]; exact xg
  have groupJ : ((projectLine line)[j]'jLt).group = some group := by
    rw [gj]; exact yg
  exact legal.2.1 ((projectLine line)[i]'iLt) (List.getElem_mem iLt)
    ((projectLine line)[j]'jLt) (List.getElem_mem jLt) idNe group groupI
    (by simp [groupJ])

/-- **At most one row of a given issue group.**  A filter whose predicate selects
only rows of one group has length at most one. -/
theorem welcomeLine_filter_length_le_one_of_group
    (expressions : List NormalizedExpr) (unrefuted : WelcomePEUnrefuted expressions)
    (q : ParsedExpr → Bool) (group : Issue.Group)
    (selects : ∀ x ∈ expressions.map NormalizedExpr.toParsed, q x = true →
      x.issueGroup = some group) :
    ((expressions.map NormalizedExpr.toParsed).filter q).length ≤ 1 := by
  let line := expressions.map NormalizedExpr.toParsed
  have legal : LegalParsedLine line := welcomePEUnrefuted_legal expressions unrefuted
  have filterNodup : (line.filter q).Nodup := (welcomeLine_nodup line legal).filter q
  have hall : ∀ x ∈ line.filter q, ∀ y ∈ line.filter q, x = y := by
    intro x hx y hy
    exact welcomeLine_eq_of_group line legal (List.mem_of_mem_filter hx)
      (List.mem_of_mem_filter hy) group
      (selects x (List.mem_of_mem_filter hx) (List.mem_filter.mp hx).2)
      (selects y (List.mem_of_mem_filter hy) (List.mem_filter.mp hy).2)
  cases hf : line.filter q with
  | nil => simp
  | cons a rest =>
      have hrest : rest = [] := by
        rcases rest with _ | ⟨b, rest'⟩
        · rfl
        · exfalso
          have hb : b ∈ line.filter q := by rw [hf]; simp
          have ha : a ∈ line.filter q := by rw [hf]; simp
          have hba : b = a := hall b hb a ha
          rw [hf] at filterNodup
          subst hba
          exact (List.nodup_cons.mp filterNodup).1 List.mem_cons_self
      rw [hrest]
      simp

/-! ## 2. The matrix-MAU writer data, unconditionally

Both conjuncts of `WelcomePEMatrixMAUWriterDataFor` follow from "at most one
`.mau` row per accepted line": the matrix-MAU filter is the writer alone, and the
float-MAU filter is empty because its rows are `.mau` rows of a disjoint family. -/

/-- A matrix-MAU row has issue group `.mauCalc`. -/
theorem matrixMAU_issueGroup (expression : ParsedExpr)
    (mau : parsedExprIsMatrixMAUProducer expression = true) :
    expression.issueGroup = some Issue.Group.mauCalc := by
  rcases expression with ⟨op, sources, destinations, flush, text⟩
  cases op <;> simp_all [parsedExprIsMatrixMAUProducer, ParsedExpr.issueGroup]

/-- A supported float-MAU row has issue group `.mauCalc`. -/
theorem floatMAU_issueGroup (expression : ParsedExpr)
    (float : parsedExprIsSupportedFloatMAUProducer expression = true) :
    expression.issueGroup = some Issue.Group.mauCalc := by
  rcases expression with ⟨op, sources, destinations, flush, text⟩
  cases op <;> simp_all [parsedExprIsSupportedFloatMAUProducer, ParsedExpr.issueGroup]

/-- A matrix-MAU row is not a float-MAU row. -/
theorem matrixMAU_not_floatMAU (expression : ParsedExpr)
    (mau : parsedExprIsMatrixMAUProducer expression = true) :
    parsedExprIsSupportedFloatMAUProducer expression = false :=
  (matrixMAU_parsedExpr_predicates expression mau).2.2.2.2.2.2.1

/-- **The matrix-MAU filter of an unrefuted line is the writer alone.** -/
theorem welcomeLine_matrixMAU_filter_singleton
    (expressions : List NormalizedExpr) (unrefuted : WelcomePEUnrefuted expressions)
    (e : ParsedExpr) (eMem : e ∈ expressions.map NormalizedExpr.toParsed)
    (mau : parsedExprIsMatrixMAUProducer e = true) :
    (expressions.map NormalizedExpr.toParsed).filter
      parsedExprIsMatrixMAUProducer = [e] := by
  have member : e ∈ (expressions.map NormalizedExpr.toParsed).filter
      parsedExprIsMatrixMAUProducer := List.mem_filter.mpr ⟨eMem, mau⟩
  exact filter_singleton_of_length_le_one _ _ e member
    (welcomeLine_filter_length_le_one_of_group expressions unrefuted
      parsedExprIsMatrixMAUProducer Issue.Group.mauCalc
      (fun x _ hx => matrixMAU_issueGroup x hx))

/-- **The float-MAU filter of an unrefuted line with a matrix-MAU writer is
empty**: every float-MAU row has group `.mauCalc` and so equals the writer, which
is not a float-MAU row. -/
theorem welcomeLine_floatMAU_filter_empty_of_matrixMAU
    (expressions : List NormalizedExpr) (unrefuted : WelcomePEUnrefuted expressions)
    (e : ParsedExpr) (eMem : e ∈ expressions.map NormalizedExpr.toParsed)
    (mau : parsedExprIsMatrixMAUProducer e = true) :
    (expressions.map NormalizedExpr.toParsed).filter
      parsedExprIsSupportedFloatMAUProducer = [] := by
  rw [List.eq_nil_iff_forall_not_mem]
  intro x hx
  have hxLine : x ∈ expressions.map NormalizedExpr.toParsed := List.mem_of_mem_filter hx
  have hxGroup : x.issueGroup = some Issue.Group.mauCalc :=
    floatMAU_issueGroup x (List.mem_filter.mp hx).2
  have heGroup : e.issueGroup = some Issue.Group.mauCalc := matrixMAU_issueGroup e mau
  have same : x = e :=
    welcomeLine_eq_of_group (expressions.map NormalizedExpr.toParsed)
      (welcomePEUnrefuted_legal expressions unrefuted) hxLine eMem Issue.Group.mauCalc
      hxGroup heGroup
  have produced : parsedExprIsSupportedFloatMAUProducer x = true :=
    (List.mem_filter.mp hx).2
  rw [same, matrixMAU_not_floatMAU e mau] at produced
  exact absurd produced (by simp)

/-- **The matrix-MAU writer-kind data package holds unconditionally.** -/
theorem welcomePEMatrixMAUWriterData : WelcomePEMatrixMAUWriterData := by
  intro expressions unrefuted e eMem mau writer
  exact ⟨welcomeLine_matrixMAU_filter_singleton expressions unrefuted e eMem mau,
    welcomeLine_floatMAU_filter_empty_of_matrixMAU expressions unrefuted e eMem mau⟩

/-- **The matrix-MAU writer's line shape, with no hypothesis.** -/
theorem welcomePEWriteShape_of_matrixMAUWriter
    (expressions : List NormalizedExpr) (unrefuted : WelcomePEUnrefuted expressions)
    (e : ParsedExpr) (eMem : e ∈ expressions.map NormalizedExpr.toParsed)
    (mau : parsedExprIsMatrixMAUProducer e = true)
    (writer : Issue.Bank.lm1 ∈ (e.toIssueExpr 0).writeBanks) :
    WelcomePEWriteShape expressions :=
  welcomePEWriteShape_of_matrixMAUWriter_data expressions
    (welcomePEMatrixMAUWriterData expressions unrefuted) unrefuted e eMem mau writer

/-! ## 3. The four remaining writer-kind data packages -/

/-- **The writer-kind data that the assembly still needs.**  The conjunction of
the four per-line packages of `WelcomeSlotFree.lean` and
`WelcomeFlagFreePlain.lean`.  The phantom provenance, the special-ALU writer
obligation and the matrix-MAU writer data are *not* components: all three are now
theorems.

The plain component is the flag-free, slot-free one (no mask-flag equation, no
`.noforward` / `.wait` companion restriction), and the `.matrixRead` component is
the slot-free one, so this bundle is strictly weaker than the round-46
`WelcomePEDispatchResiduals` bundle minus its now-proved components. -/
def WelcomePEWriterKindDataResiduals : Prop :=
  WelcomePEPlainWriterDataFlagFree ∧
    WelcomePEMatrixReadWriterDataSlotFree ∧
      WelcomePEFloatMAUWriterData ∧ WelcomePEL1BMWriterData

/-- **The flag-free dispatch bundle from the four writer-kind packages.**  The
special-ALU component is the unconditional theorem, the matrix-MAU component is
`welcomePEMatrixMAUWriterData`, and the per-line dispatch data is
`welcomePELm1LineDispatchDataFlagFree_of_components`. -/
theorem welcomePEDispatchResidualsFlagFree_of_writerKindData
    (plain : WelcomePEPlainWriterDataFlagFree)
    (read : WelcomePEMatrixReadWriterDataSlotFree)
    (float : WelcomePEFloatMAUWriterData) (l1 : WelcomePEL1BMWriterData) :
    WelcomePEDispatchResidualsFlagFree :=
  ⟨welcomePESpecialALUWriterShapeObligation,
    fun expressions unrefuted =>
      welcomePELm1LineDispatchDataFlagFree_of_components
        welcomePELm1PhantomWriterProvenance plain read float welcomePEMatrixMAUWriterData l1
        expressions unrefuted⟩

/-! ## 4. The assembly

With the phantom provenance, the special-ALU writer case and the matrix-MAU writer
data substituted, the per-line write-shape obligation follows from the four
packages only. -/

/-- **`WelcomePELm1WriteShapeObligation` from the four writer-kind packages.**
This is the strongest unconditional reduction available: the phantom,
special-ALU and matrix-MAU components are discharged, so every line whose unique
`.lm1` writer is a phantom row, a special-ALU row or a matrix-MAU row is already
covered without hypotheses. -/
theorem welcomePELm1WriteShapeObligation_of_writerKindData
    (plain : WelcomePEPlainWriterDataFlagFree)
    (read : WelcomePEMatrixReadWriterDataSlotFree)
    (float : WelcomePEFloatMAUWriterData) (l1 : WelcomePEL1BMWriterData) :
    WelcomePELm1WriteShapeObligation :=
  welcomePELm1WriteShapeObligation_of_dispatchFlagFree
    (welcomePEDispatchResidualsFlagFree_of_writerKindData plain read float l1)

/-- **The bundle form** of `welcomePELm1WriteShapeObligation_of_writerKindData`. -/
theorem welcomePELm1WriteShapeObligation_of_writerKindDataResiduals
    (residuals : WelcomePEWriterKindDataResiduals) :
    WelcomePELm1WriteShapeObligation := by
  obtain ⟨plain, read, float, l1⟩ := residuals
  exact welcomePELm1WriteShapeObligation_of_writerKindData plain read float l1

/-- **`LowerBound welcomeSealedMachine welcomeSpec 2` from the four packages**
(through `welcomeLowerBound_two_of_lm1WriteShapes`). -/
theorem welcomeLowerBound_two_of_writerKindData
    (plain : WelcomePEPlainWriterDataFlagFree)
    (read : WelcomePEMatrixReadWriterDataSlotFree)
    (float : WelcomePEFloatMAUWriterData) (l1 : WelcomePEL1BMWriterData) :
    ProofsLean.LowerBound welcomeSealedMachine welcomeSpec 2 :=
  welcomeLowerBound_two_of_lm1WriteShapes
    (welcomePELm1WriteShapeObligation_of_writerKindData plain read float l1)

/-- **The bundle form** of `welcomeLowerBound_two_of_writerKindData`. -/
theorem welcomeLowerBound_two_of_writerKindDataResiduals
    (residuals : WelcomePEWriterKindDataResiduals) :
    ProofsLean.LowerBound welcomeSealedMachine welcomeSpec 2 := by
  obtain ⟨plain, read, float, l1⟩ := residuals
  exact welcomeLowerBound_two_of_writerKindData plain read float l1

/-- **`Optimal welcomeSealedMachine welcomeSpec welcomeAnswer` from the four
packages.**  `welcomeAnswer_correct` is already proved, so the lower bound gives
optimality. -/
theorem welcomeAnswer_optimal_of_writerKindData
    (plain : WelcomePEPlainWriterDataFlagFree)
    (read : WelcomePEMatrixReadWriterDataSlotFree)
    (float : WelcomePEFloatMAUWriterData) (l1 : WelcomePEL1BMWriterData) :
    ProofsLean.Optimal welcomeSealedMachine welcomeSpec welcomeAnswer :=
  welcomeAnswer_optimal_of_lm1WriteShapes
    (welcomePELm1WriteShapeObligation_of_writerKindData plain read float l1)

/-- **The bundle form** of `welcomeAnswer_optimal_of_writerKindData`. -/
theorem welcomeAnswer_optimal_of_writerKindDataResiduals
    (residuals : WelcomePEWriterKindDataResiduals) :
    ProofsLean.Optimal welcomeSealedMachine welcomeSpec welcomeAnswer := by
  obtain ⟨plain, read, float, l1⟩ := residuals
  exact welcomeAnswer_optimal_of_writerKindData plain read float l1

/-! ## 5. Which writer kinds are unconditional

The dispatch of one line reads the kind of its unique `.lm1` writer (the
partition is `supportedProducer_partition`).  The table below records, for every
kind, whether the line shape follows without a data package.

| writer kind | covered unconditionally | theorem / package |
|---|---|---|
| no `.lm1` writer at all | yes | phantom case of `welcomePELm1PhantomWriterProvenance` |
| `.noforward`, `.wait`, shared-block `.l1bm`, `.matrixWrite`, `.l2bm` | yes | `welcomePELm1PhantomWriterProvenance` |
| `msl` / `msr` | yes | `welcomePEMslMsrWriterShapeObligation` |
| float-relu | yes | `welcomePEFloatReluWriterShapeObligation` |
| block-float (`.d` / `.f` / `.g` / `.h`) | yes | `welcomePEBlockFloatWriterShapeObligation` |
| matrix-MAU | yes | `welcomePEMatrixMAUWriterData` (§2) |
| plain (`.alu` / `.zero` / `.immediate`) | **no** | `WelcomePEPlainWriterDataFlagFree` |
| `.matrixRead` | **no** | `WelcomePEMatrixReadWriterDataSlotFree` |
| float-MAU | **no** | `WelcomePEFloatMAUWriterData` |
| `.l1bm` broadcast (`.pbcast` / `.mbcast` / `.m4bcast` / `.distrib`) | **no** | `WelcomePEL1BMWriterData` |

The plain row shape itself is unconditional; only the line-level side conditions
of package 1 remain.  Consequently a line whose unique `.lm1` writer is plain is
*partially* covered: the shape follows whenever the line additionally has no
float-MAU row and either the writer is not an `.immediate` row with an
`.lm1 .double` destination or the line is input-independent.

## What would close the remaining gap

Discharging packages 1, 2 and 4 needs one of:

* a plain / matrix-read / `.l1bm` line shape that tolerates a float-MAU
  companion, i.e. one stated with `.lm1`-freeness of the float stage
  (`executeIntegerProducerLineAtPEs_zero_prepared_float_clean_of_line_split`
  supplies exactly that pair of `.lm1`-free lists) instead of an empty float
  filter — the special-ALU proofs of `WelcomeHalfBlockFloat.lean` already use the
  `.lm1`-free form;
* for package 3, a float-MAU line shape with arbitrary `.lm1`-free integer-stage
  companions;
* for package 1, a version of `welcomePEPlainImmediateDoubleObligation` for lines
  with float-MAU companions (the all-plain version is proved, and
  `welcomePEMixedImmediateDouble_inputIndependent` covers inertial companions).

The per-line split-at-`e` components are syntactic: §1 proves that an accepted
line has no duplicate rows (`welcomeLine_nodup`), and `welcomeLm1Writer_unique`
gives `.lm1`-writer uniqueness.
-/

end ProofsLean.MNCore

-- End of module: no sorry, no admit, no native_decide, no new axioms.
