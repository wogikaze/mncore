import ProofsLean.WelcomeFrameFix
import ProofsLean.WelcomeGapShape

/-! # The `.lm1` writer reduction: per-row shapes plus the line assembly

`WelcomeMatrixMAUCommit.lean` proves the line assembly unconditionally
(`welcomePE_line_stage_commit_unconditional`): for an unrefuted `.pe` line the
PE 0 register file after the step is

```
commitParsedMaskedWrites initial (intWrites ++ mslWrites ++ reluWrites ++
  blockWrites ++ matrixWrites ++ l1Writes)
```

`WelcomeGapShape.lean` reduces the per-line write shape to nine named `Prop`s,
one of which is the *mixed plain/inert* obligation
`WelcomePEMixedPlainInertShapeObligation`: a line with a plain row, no six-family
row and no special-ALU row.  This module supplies the missing bridge that turns a
per-row shape plus the assembly into the line-level shape, and instantiates it for
the row kinds whose shapes are already proved:

* **§1 the `.lm1` algebra**: a block of writes with no `.lm1` write can be
  appended to (or prepended to) a shaped block without changing the shape
  (`lm1WritesDoubleCopy_append_of_only`, `lm1WritesNarrow_append_of_only`).
* **§2 from a write list to the line shape**: the two `WelcomePE*Shape`
  predicates are the commit equation plus `Lm1Writes*` of one write list
  (`welcomePEDoubleCopyShape_of_commit`, `welcomePENarrowShape_of_commit`,
  `welcomePEWriteShape_of_commit_shape`).
* **§3 the assembly for integer-or-inert lines**: if every row is an
  integer/matrix-read stage input or a PE-inert producer (`.noforward`, a
  non-pending `.wait`, or one of the five shared-block `.l1bm` operations), the
  whole line is the commit of the integer stage's prepared list
  (`executeIntegerProducerInstructionLine_pe_commit_of_integerOrInert` and its
  sealed-machine form).  This generalises `welcomePE_line_commit_of_clean` from
  `.matrixWrite` rows to `.noforward` / `.wait` / shared `.l1bm` rows.
* **§4 the single-writer characterisation of the integer stage**: a stage list
  that consists of one row plus `.noforward` / `.wait` rows produces exactly
  that row's prepared writes (`..._single_writer`).  The `.noforward` and
  `.wait` rows prepare nothing at all, and they leave the forwarding slots
  unchanged, so the writer row sees the initial slots.
* **§5 the three row shapes**: plain (`plainRow_lm1_shape`, built from
  `prepareParsedIntegerALUExprCycles_four` and the per-cycle `Lm1ChunkFacts` of
  `WelcomePlainStep.lean`), `.matrixRead`
  (`matrixReadRow_lm1_shape`, from
  `prepareParsedIntegerMatrixReadLineExpression_matrixRead_shape`), and inert
  rows, which prepare no write
  (`prepareParsedIntegerMatrixReadLineExpression_skip`).
* **§6 the unique-writer line shape** (`welcomePEWriteShape_of_integerStageWriter`)
  and its instantiations: a plain writer (`welcomePEWriteShape_of_plainWriter`),
  a `.matrixRead` writer (`welcomePEWriteShape_of_matrixReadWriter`), a line with
  no `.lm1` destination in any prepared row
  (`welcomePEWriteShape_of_noLm1Rows`), and an all-inert line
  (`welcomePEWriteShape_of_allInert`).
* **§7 the mixed plain/inert class**: every row of such a line is
  integer-or-inert (`welcomeMixed_rows_integerOrInert`), a legal line has at most
  one plain row (`plain_rows_at_most_one_eq`), and the mixed obligation follows
  from the syntactic structure statement `WelcomePEMixedPlainInertStructure`
  (`welcomePEMixedPlainInertShapeObligation_of_structure`,
  `welcomePELm1WriteShapeObligation_of_eight_and_structure`).  Two components of
  that statement are *not* proved here and are described in §8: the mask-flag
  agreement and the immediate-double exclusion.

No `sorry`, no `admit`, no `native_decide`, no new axioms.  Nothing here assumes
the obligations it names, and it does not claim `LowerBound 2` or `Optimal`.
-/

namespace ProofsLean.MNCore

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

open Issue
open PEMemory

/-! ## 1. The `.lm1` algebra of concatenated stage lists

The commit only sees the `.lm1` bank through the `.lm1` writes of the list
(`commitParsedMaskedWrites_lm1_filter`).  Consequently a block that writes no
`.lm1` word at all is invisible to the shape of the concatenation. -/

theorem isLm1Write_false_bank_ne (write : PreparedParsedMaskedWrite)
    (notLm1 : PreparedParsedMaskedWrite.isLm1Write write = false) :
    ∀ access : DirectMemoryAccess, write.destination = some access →
      access.bank ≠ PEMemory.Bank.lm1 :=
  isLm1Write_false_bank write notLm1

/-- A shaped block followed by an `.lm1`-free block is shaped. -/
theorem lm1WritesDoubleCopy_append_of_only (first second : List PreparedParsedMaskedWrite)
    (shape : Lm1WritesDoubleCopy first)
    (only : ∀ write ∈ second, PreparedParsedMaskedWrite.isLm1Write write = false) :
    Lm1WritesDoubleCopy (first ++ second) := by
  intro write member width address data selection destination dataEq selectionEq
  rcases List.mem_append.mp member with head | tail
  · exact shape write head width address data selection destination dataEq selectionEq
  · have bankNe := isLm1Write_false_bank write (only write tail)
      ⟨PEMemory.Bank.lm1, width, address⟩ destination
    exact absurd rfl bankNe

/-- A shaped block followed by an `.lm1`-free block is narrow. -/
theorem lm1WritesNarrow_append_of_only (first second : List PreparedParsedMaskedWrite)
    (shape : Lm1WritesNarrow first)
    (only : ∀ write ∈ second, PreparedParsedMaskedWrite.isLm1Write write = false) :
    Lm1WritesNarrow (first ++ second) := by
  obtain ⟨windows, covers, bound, sizes⟩ := shape
  refine ⟨windows, ?_, bound, sizes⟩
  intro write member width address destination
  rcases List.mem_append.mp member with head | tail
  · exact covers write head width address destination
  · have bankNe := isLm1Write_false_bank write (only write tail)
      ⟨PEMemory.Bank.lm1, width, address⟩ destination
    exact absurd rfl bankNe

/-- An `.lm1`-free block followed by a shaped block is shaped. -/
theorem lm1WritesDoubleCopy_append_of_only_right (first second : List PreparedParsedMaskedWrite)
    (shape : Lm1WritesDoubleCopy second)
    (only : ∀ write ∈ first, PreparedParsedMaskedWrite.isLm1Write write = false) :
    Lm1WritesDoubleCopy (first ++ second) := by
  intro write member width address data selection destination dataEq selectionEq
  rcases List.mem_append.mp member with head | tail
  · have bankNe := isLm1Write_false_bank write (only write head)
      ⟨PEMemory.Bank.lm1, width, address⟩ destination
    exact absurd rfl bankNe
  · exact shape write tail width address data selection destination dataEq selectionEq

/-- An `.lm1`-free block followed by a shaped block is narrow. -/
theorem lm1WritesNarrow_append_of_only_right (first second : List PreparedParsedMaskedWrite)
    (shape : Lm1WritesNarrow second)
    (only : ∀ write ∈ first, PreparedParsedMaskedWrite.isLm1Write write = false) :
    Lm1WritesNarrow (first ++ second) := by
  obtain ⟨windows, covers, bound, sizes⟩ := shape
  refine ⟨windows, ?_, bound, sizes⟩
  intro write member width address destination
  rcases List.mem_append.mp member with head | tail
  · have bankNe := isLm1Write_false_bank write (only write head)
      ⟨PEMemory.Bank.lm1, width, address⟩ destination
    exact absurd rfl bankNe
  · exact covers write tail width address destination

/-- The shape disjunction is stable under appending `.lm1`-free blocks. -/
theorem lm1WritesShape_append_of_only (first second : List PreparedParsedMaskedWrite)
    (only : ∀ write ∈ second, PreparedParsedMaskedWrite.isLm1Write write = false)
    (shape : Lm1WritesDoubleCopy first ∨ Lm1WritesNarrow first) :
    Lm1WritesDoubleCopy (first ++ second) ∨ Lm1WritesNarrow (first ++ second) := by
  rcases shape with double | narrow
  · exact Or.inl (lm1WritesDoubleCopy_append_of_only first second double only)
  · exact Or.inr (lm1WritesNarrow_append_of_only first second narrow only)

/-- The shape disjunction is stable under prepending `.lm1`-free blocks. -/
theorem lm1WritesShape_append_of_only_right (first second : List PreparedParsedMaskedWrite)
    (only : ∀ write ∈ first, PreparedParsedMaskedWrite.isLm1Write write = false)
    (shape : Lm1WritesDoubleCopy second ∨ Lm1WritesNarrow second) :
    Lm1WritesDoubleCopy (first ++ second) ∨ Lm1WritesNarrow (first ++ second) := by
  rcases shape with double | narrow
  · exact Or.inl (lm1WritesDoubleCopy_append_of_only_right first second double only)
  · exact Or.inr (lm1WritesNarrow_append_of_only_right first second narrow only)

/-! ## 2. From one write list to the line-level shape

The two `WelcomePE*Shape` predicates are literally the commit equation for one
write list plus the corresponding `Lm1Writes*` predicate, so a producer that
exhibits such a list has already proved the predicate. -/

theorem welcomePEDoubleCopyShape_of_commit (expressions : List NormalizedExpr)
    (committed : ∀ next, welcomeSealedMachine.step (.pe expressions)
        (welcomeInitialState welcomeZeroWords) = some next →
      ∃ writes, next.peRegisters welcomePE =
          commitParsedMaskedWrites
            ((welcomeInitialState welcomeZeroWords).peRegisters welcomePE) writes ∧
        Lm1WritesDoubleCopy writes) :
    WelcomePEDoubleCopyShape expressions := by
  intro next step
  exact committed next step

theorem welcomePENarrowShape_of_commit (expressions : List NormalizedExpr)
    (committed : ∀ next, welcomeSealedMachine.step (.pe expressions)
        (welcomeInitialState welcomeZeroWords) = some next →
      ∃ writes, next.peRegisters welcomePE =
          commitParsedMaskedWrites
            ((welcomeInitialState welcomeZeroWords).peRegisters welcomePE) writes ∧
        Lm1WritesNarrow writes) :
    WelcomePENarrowShape expressions := by
  intro next step
  obtain ⟨writes, commitEq, windows, covers, bound, sizes⟩ := committed next step
  exact ⟨writes, windows, commitEq, covers, bound, sizes⟩

/-- **The line-level shape from one write list.** -/
theorem welcomePEWriteShape_of_commit_shape (expressions : List NormalizedExpr)
    (committed : ∀ next, welcomeSealedMachine.step (.pe expressions)
        (welcomeInitialState welcomeZeroWords) = some next →
      ∃ writes, next.peRegisters welcomePE =
          commitParsedMaskedWrites
            ((welcomeInitialState welcomeZeroWords).peRegisters welcomePE) writes ∧
        (Lm1WritesDoubleCopy writes ∨ Lm1WritesNarrow writes)) :
    WelcomePEWriteShape expressions := by
  rcases Classical.em (∃ next, welcomeSealedMachine.step (.pe expressions)
      (welcomeInitialState welcomeZeroWords) = some next) with ⟨next, stepEq⟩ | none
  · obtain ⟨writes, commitEq, shape⟩ := committed next stepEq
    have unique : ∀ next' : State, welcomeSealedMachine.step (.pe expressions)
        (welcomeInitialState welcomeZeroWords) = some next' → next' = next := by
      intro next' step'
      rw [stepEq] at step'
      exact (Option.some.inj step').symm
    rcases shape with double | narrow
    · left
      intro next' step'
      obtain rfl : next' = next := unique next' step'
      exact ⟨writes, commitEq, double⟩
    · right; left
      intro next' step'
      obtain rfl : next' = next := unique next' step'
      obtain ⟨windows, covers, bound, sizes⟩ := narrow
      exact ⟨writes, windows, commitEq, covers, bound, sizes⟩
  · left
    intro next step'
    exact absurd ⟨next, step'⟩ none

/-! ## 3. The line assembly for integer-or-inert lines

The clean class of `WelcomeAssembly.lean` is "integer/matrix-read stage input or
`.matrixWrite`".  The mixed plain/inert class needs the same assembly with the
`.matrixWrite` rows replaced by the PE-inert rows of `WelcomeGapShape.lean`
(`.noforward`, a non-pending `.wait`, and the five shared-block `.l1bm`
operations).  The shared-block stage is a frame for *every* row, so nothing has
to be assumed about those rows beyond their inertness. -/

/-- A row the line assembly handles outside the four middle stages and the
L1BM-to-PE stage: an integer/matrix-read stage input, or a PE-inert producer. -/
def welcomeIntegerOrInertLine (expression : ParsedExpr) : Bool :=
  parsedExprIsIntegerMatrixReadStageInput expression ||
    parsedExprIsPEInertProducer expression

/-- An integer-or-inert row is executed by none of the four middle stages and by
no L1BM-to-PE stage, and it carries no float-MAU producer. -/
theorem welcomeIntegerOrInertLine_stageFacts (expression : ParsedExpr)
    (intOrInert : welcomeIntegerOrInertLine expression = true) :
    parsedExprIsL2BMProducer expression = false ∧
    parsedExprIsMslMsrProducer expression = false ∧
    parsedExprIsMatrixMAUProducer expression = false ∧
    parsedExprIsBlockFloatProducer expression = false ∧
    parsedExprIsFloatReluProducer expression = false ∧
    parsedExprIsL1ToPEProducer expression = false ∧
    parsedExprIsSupportedFloatMAUProducer expression = false := by
  unfold welcomeIntegerOrInertLine at intOrInert
  rcases Bool.or_eq_true_iff.mp intOrInert with input | inert
  · obtain ⟨_, l2bm, _, _, _, _, l1tope, mmau, float, msl, block, relu⟩ :=
      (parsedExprIsIntegerMatrixReadStageInput_spec expression).mp input
    exact ⟨l2bm, msl, mmau, block, relu, l1tope, float⟩
  · rcases parsedExprIsPEInertProducer_cases expression inert with
      forward | wait | shared
    · simp [forward, parsedExprIsL2BMProducer, parsedExprIsMslMsrProducer,
        parsedExprIsMatrixMAUProducer, parsedExprIsBlockFloatProducer,
        parsedExprIsFloatReluProducer, parsedExprIsL1ToPEProducer,
        parsedExprIsSupportedFloatMAUProducer]
    · obtain ⟨tag, tagEq⟩ := wait
      simp [tagEq, parsedExprIsL2BMProducer, parsedExprIsMslMsrProducer,
        parsedExprIsMatrixMAUProducer, parsedExprIsBlockFloatProducer,
        parsedExprIsFloatReluProducer, parsedExprIsL1ToPEProducer,
        parsedExprIsSupportedFloatMAUProducer]
    · rcases parsedExprIsL1SharedBlockProducer_cases expression shared with
        mw | m4w | gather | reduce | reduce4
      · obtain ⟨mab, mabEq⟩ := mw
        simp [mabEq, parsedExprIsL2BMProducer, parsedExprIsMslMsrProducer,
          parsedExprIsMatrixMAUProducer, parsedExprIsBlockFloatProducer,
          parsedExprIsFloatReluProducer, parsedExprIsL1ToPEProducer,
          parsedExprIsSupportedFloatMAUProducer]
      · obtain ⟨mab, mabEq⟩ := m4w
        simp [mabEq, parsedExprIsL2BMProducer, parsedExprIsMslMsrProducer,
          parsedExprIsMatrixMAUProducer, parsedExprIsBlockFloatProducer,
          parsedExprIsFloatReluProducer, parsedExprIsL1ToPEProducer,
          parsedExprIsSupportedFloatMAUProducer]
      · obtain ⟨mabdiff, diffEq⟩ := gather
        simp [diffEq, parsedExprIsL2BMProducer, parsedExprIsMslMsrProducer,
          parsedExprIsMatrixMAUProducer, parsedExprIsBlockFloatProducer,
          parsedExprIsFloatReluProducer, parsedExprIsL1ToPEProducer,
          parsedExprIsSupportedFloatMAUProducer]
      · obtain ⟨rrn, round, reduceEq⟩ := reduce
        simp [reduceEq, parsedExprIsL2BMProducer, parsedExprIsMslMsrProducer,
          parsedExprIsMatrixMAUProducer, parsedExprIsBlockFloatProducer,
          parsedExprIsFloatReluProducer, parsedExprIsL1ToPEProducer,
          parsedExprIsSupportedFloatMAUProducer]
      · obtain ⟨rrn, round, reduceEq⟩ := reduce4
        simp [reduceEq, parsedExprIsL2BMProducer, parsedExprIsMslMsrProducer,
          parsedExprIsMatrixMAUProducer, parsedExprIsBlockFloatProducer,
          parsedExprIsFloatReluProducer, parsedExprIsL1ToPEProducer,
          parsedExprIsSupportedFloatMAUProducer]

/-- An integer-or-inert row survives the outer filter of the integer stage. -/
theorem welcomeIntegerOrInertLine_outerFilter (expression : ParsedExpr)
    (intOrInert : welcomeIntegerOrInertLine expression = true) :
    (!parsedExprIsL2BMProducer expression && !parsedExprIsMslMsrProducer expression &&
      !parsedExprIsMatrixMAUProducer expression && !parsedExprIsBlockFloatProducer expression &&
      !parsedExprIsFloatReluProducer expression) = true := by
  obtain ⟨l2bm, msl, mmau, block, relu, _⟩ :=
    welcomeIntegerOrInertLine_stageFacts expression intOrInert
  rw [l2bm, msl, mmau, block, relu]
  rfl

theorem welcomeIntegerOrInertLine_filter_eq_self (expressions : List ParsedExpr)
    (intOrInert : expressions.all welcomeIntegerOrInertLine = true) :
    expressions.filter (fun expression =>
      !parsedExprIsL2BMProducer expression && !parsedExprIsMslMsrProducer expression &&
        !parsedExprIsMatrixMAUProducer expression && !parsedExprIsBlockFloatProducer expression &&
        !parsedExprIsFloatReluProducer expression) = expressions := by
  rw [List.filter_eq_self]
  intro expression member
  exact welcomeIntegerOrInertLine_outerFilter expression
    (List.all_eq_true.mp intOrInert expression member)

theorem welcomeIntegerOrInertLine_filter_nil (expressions : List ParsedExpr)
    (predicate : ParsedExpr → Bool)
    (absent : ∀ expression ∈ expressions, welcomeIntegerOrInertLine expression = true →
      predicate expression = false)
    (intOrInert : expressions.all welcomeIntegerOrInertLine = true) :
    expressions.filter predicate = [] :=
  List.filter_eq_nil_iff.mpr fun expression member => by
    rw [absent expression member (List.all_eq_true.mp intOrInert expression member)]
    simp

theorem welcomeIntegerOrInertLine_floatFilter_nil (expressions : List ParsedExpr)
    (intOrInert : expressions.all welcomeIntegerOrInertLine = true) :
    expressions.filter parsedExprIsSupportedFloatMAUProducer = [] :=
  welcomeIntegerOrInertLine_filter_nil expressions _ (fun expression _ intOrInert =>
    (welcomeIntegerOrInertLine_stageFacts expression intOrInert).2.2.2.2.2.2) intOrInert

theorem welcomeIntegerOrInertLine_mslFilter_nil (expressions : List ParsedExpr)
    (intOrInert : expressions.all welcomeIntegerOrInertLine = true) :
    expressions.filter parsedExprIsMslMsrProducer = [] :=
  welcomeIntegerOrInertLine_filter_nil expressions _ (fun expression _ intOrInert =>
    (welcomeIntegerOrInertLine_stageFacts expression intOrInert).2.1) intOrInert

theorem welcomeIntegerOrInertLine_reluFilter_nil (expressions : List ParsedExpr)
    (intOrInert : expressions.all welcomeIntegerOrInertLine = true) :
    expressions.filter parsedExprIsFloatReluProducer = [] :=
  welcomeIntegerOrInertLine_filter_nil expressions _ (fun expression _ intOrInert =>
    (welcomeIntegerOrInertLine_stageFacts expression intOrInert).2.2.2.2.1) intOrInert

theorem welcomeIntegerOrInertLine_blockFilter_nil (expressions : List ParsedExpr)
    (intOrInert : expressions.all welcomeIntegerOrInertLine = true) :
    expressions.filter parsedExprIsBlockFloatProducer = [] :=
  welcomeIntegerOrInertLine_filter_nil expressions _ (fun expression _ intOrInert =>
    (welcomeIntegerOrInertLine_stageFacts expression intOrInert).2.2.2.1) intOrInert

theorem welcomeIntegerOrInertLine_matrixMAUFilter_nil (expressions : List ParsedExpr)
    (intOrInert : expressions.all welcomeIntegerOrInertLine = true) :
    expressions.filter parsedExprIsMatrixMAUProducer = [] :=
  welcomeIntegerOrInertLine_filter_nil expressions _ (fun expression _ intOrInert =>
    (welcomeIntegerOrInertLine_stageFacts expression intOrInert).2.2.1) intOrInert

theorem welcomeIntegerOrInertLine_l1ToPEFilter_nil (expressions : List ParsedExpr)
    (intOrInert : expressions.all welcomeIntegerOrInertLine = true) :
    expressions.filter parsedExprIsL1ToPEProducer = [] :=
  welcomeIntegerOrInertLine_filter_nil expressions _ (fun expression _ intOrInert =>
    (welcomeIntegerOrInertLine_stageFacts expression intOrInert).2.2.2.2.2.1) intOrInert

theorem welcomeIntegerOrInertLine_l2BMFilter_nil (expressions : List ParsedExpr)
    (intOrInert : expressions.all welcomeIntegerOrInertLine = true) :
    expressions.filter parsedExprIsL2BMProducer = [] :=
  welcomeIntegerOrInertLine_filter_nil expressions _ (fun expression _ intOrInert =>
    (welcomeIntegerOrInertLine_stageFacts expression intOrInert).1) intOrInert

/-- **The line assembly for integer-or-inert lines.**  If every row is an
integer/matrix-read stage input or a PE-inert producer, a successful `.pe` line
leaves PE 0's register file equal to the commit of the integer stage's prepared
write list.  The four middle stages and the L1BM-to-PE stage are the identity
(their producer filters are empty), the matrix-MAU/write stage preserves every
PE register file (there is no matrix-MAU row), and the shared-block stage is a
frame for every row. -/
theorem executeIntegerProducerInstructionLine_pe_commit_of_integerOrInert
    (expressions : List NormalizedExpr) (state next : State)
    (accepted : checkParsedTopLine (InstructionLine.pe expressions).toParsed = true)
    (waits : (expressions.map NormalizedExpr.toParsed).any
      (parsedExprWaitPending state) = false)
    (unsupported : (expressions.map NormalizedExpr.toParsed).any
      parsedExprIsUnsupportedRustAlu = false)
    (supported : (expressions.map NormalizedExpr.toParsed).all
      parsedExprIsSupportedPELineProducer = true)
    (intOrInert : (expressions.map NormalizedExpr.toParsed).all
      welcomeIntegerOrInertLine = true)
    (step : executeIntegerProducerInstructionLine (.pe expressions) state = .ok next) :
    ∃ writes slots bars,
      welcomeIntegerPrep state welcomePE (expressions.map NormalizedExpr.toParsed) =
        .ok (writes, slots, bars) ∧
      next.peRegisters welcomePE =
        commitParsedMaskedWrites (state.peRegisters welcomePE) writes := by
  obtain ⟨nextPEs, nextMsl, nextRelu, nextBlockFloat, afterMatrix, nextShared,
    nextBroadcast, walkExecuted, mslExecuted, reluExecuted, blockExecuted, matrixExecuted,
    sharedExecuted, l1Executed, nextEq⟩ :=
    executeIntegerProducerInstructionLine_pe_stages_exists expressions state next accepted
      waits unsupported supported step
  have filterEq := welcomeIntegerOrInertLine_filter_eq_self
    (expressions.map NormalizedExpr.toParsed) intOrInert
  rw [filterEq] at walkExecuted
  obtain ⟨writes, slots, bars, prep, committed⟩ :=
    executeIntegerProducerLineAtPEs_prepared (expressions.map NormalizedExpr.toParsed)
      (List.finRange 4096) state nextPEs
      (welcomeIntegerOrInertLine_floatFilter_nil _ intOrInert) walkExecuted
      (List.nodup_finRange 4096) welcomePE (List.mem_finRange welcomePE)
  have mslId : executeParsedMslMsrProducers state nextPEs
      (expressions.map NormalizedExpr.toParsed)
      (expressions.any (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed))
      (expressions.any (parsedExprHasSingleLineWriteMask ∘ NormalizedExpr.toParsed)) =
      .ok nextPEs :=
    executeParsedMslMsrProducers_eq_self state nextPEs _ _ _
      (welcomeIntegerOrInertLine_mslFilter_nil _ intOrInert)
  have nextMslEq : nextMsl = nextPEs := by
    rw [mslId] at mslExecuted
    exact (StepResult.ok.inj mslExecuted).symm
  have reluId : executeParsedFloatReluProducers state nextPEs
      (expressions.map NormalizedExpr.toParsed)
      (expressions.any (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed))
      (expressions.any (parsedExprHasSingleLineWriteMask ∘ NormalizedExpr.toParsed)) =
      .ok nextPEs :=
    executeParsedFloatReluProducers_eq_self state nextPEs _ _ _
      (welcomeIntegerOrInertLine_reluFilter_nil _ intOrInert)
  have nextReluEq : nextRelu = nextPEs := by
    rw [nextMslEq, reluId] at reluExecuted
    exact (StepResult.ok.inj reluExecuted).symm
  have blockId : executeParsedBlockFloatProducer state nextPEs
      (expressions.map NormalizedExpr.toParsed)
      (expressions.any (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed))
      (expressions.any (parsedExprHasSingleLineWriteMask ∘ NormalizedExpr.toParsed)) =
      .ok nextPEs :=
    executeParsedBlockFloatProducer_eq_self state nextPEs _ _ _
      (welcomeIntegerOrInertLine_blockFilter_nil _ intOrInert)
  have nextBlockFloatEq : nextBlockFloat = nextPEs := by
    rw [nextReluEq, blockId] at blockExecuted
    exact (StepResult.ok.inj blockExecuted).symm
  have matrixFrame : ∀ pe : PEId,
      afterMatrix.peRegisters pe = nextBlockFloat.peRegisters pe :=
    executeParsedMatrixMAUAndWrites_peRegisters_frame_of_noMatrixMAU state nextBlockFloat
      afterMatrix (expressions.map NormalizedExpr.toParsed)
      (expressions.any (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed))
      (expressions.any (parsedExprHasSingleLineWriteMask ∘ NormalizedExpr.toParsed))
      (welcomeIntegerOrInertLine_matrixMAUFilter_nil _ intOrInert) matrixExecuted
  have sharedFrame : nextShared.peRegisters = afterMatrix.peRegisters :=
    executeParsedSharedBlockProducers_peRegisters state afterMatrix nextShared
      (expressions.map NormalizedExpr.toParsed)
      (!(expressions.any (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed)))
      sharedExecuted
  have l1Id : executeParsedL1ToPEProducers state nextShared
      (expressions.map NormalizedExpr.toParsed)
      (expressions.any (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed))
      (expressions.any (parsedExprHasSingleLineWriteMask ∘ NormalizedExpr.toParsed))
      (parsedL1ToPEPrecedesOMRWriter (expressions.map NormalizedExpr.toParsed)) =
      .ok nextShared :=
    executeParsedL1ToPEProducers_eq_self state nextShared _ _ _ _
      (welcomeIntegerOrInertLine_l1ToPEFilter_nil _ intOrInert)
  have nextBroadcastEq : nextBroadcast = nextShared := by
    rw [l1Id] at l1Executed
    exact (StepResult.ok.inj l1Executed).symm
  refine ⟨writes, slots, bars, prep, ?_⟩
  rw [nextEq, nextBroadcastEq]
  simp only [sharedFrame, matrixFrame welcomePE, nextBlockFloatEq, committed]

/-- **The line assembly for integer-or-inert lines at the sealed machine.** -/
theorem welcomePE_line_commit_of_integerOrInert
    (expressions : List NormalizedExpr) (input : ProofsLean.MNCore.PlusOne.Words)
    (next : State) (unrefuted : WelcomePEUnrefuted expressions)
    (intOrInert : (expressions.map NormalizedExpr.toParsed).all
      welcomeIntegerOrInertLine = true)
    (step : welcomeSealedMachine.step (.pe expressions)
      (welcomeInitialState input) = some next) :
    ∃ writes slots bars,
      welcomeIntegerPrep (welcomeInitialState input) welcomePE
        (expressions.map NormalizedExpr.toParsed) = .ok (writes, slots, bars) ∧
      next.peRegisters welcomePE =
        commitParsedMaskedWrites
          ((welcomeInitialState input).peRegisters welcomePE) writes := by
  have executed := welcomeSealed_step_ok step
  simp only [executeNormalizedLine, NormalizedLine.toInstruction?,
    Issue.InstructionLine.toNormalizedLine] at executed
  refine executeIntegerProducerInstructionLine_pe_commit_of_integerOrInert expressions
    (welcomeInitialState input) next unrefuted.1.1 ?_ unrefuted.1.2.2.1 unrefuted.1.2.2.2
    intOrInert executed
  have waits := unrefuted.1.2.1
  have same : (expressions.map NormalizedExpr.toParsed).any
      (parsedExprWaitPending (welcomeInitialState input)) =
      (expressions.map NormalizedExpr.toParsed).any
        (parsedExprWaitPending (welcomeInitialState welcomeZeroWords)) := by
    apply List.any_congr rfl
    intro expression
    exact parsedExprWaitPending_welcomeInitialState input expression
  exact same ▸ waits

/-! ## 4. The single-writer characterisation of the integer stage

`welcomeIntegerPrep` folds `prepareParsedIntegerMatrixReadLineExpression` over the
integer/matrix-read stage rows.  A `.noforward` or `.wait` row prepares the empty
write list and leaves the forwarding slots untouched, so a stage list that
consists of one row plus such rows produces exactly the writes of that row, and
that row is prepared at the initial slots.  These are the lemmas that turn the
`writesUnique` reduction into a statement about a single row. -/

theorem prepareParsedIntegerMatrixReadLineExpression_skip
    (files : IntegerRegisterFiles) (oldSlots nextSlots : ProofsLean.MNCore.Forwarding.Slots)
    (store : ParsedMatrixReadStore) (expression : ParsedExpr)
    (control : ParsedMaskExecutionControl) (hasSingleLineMask noForward reduced : Bool)
    (skip : expression.op = .noforward ∨ ∃ tag : Fin 256, expression.op = .wait tag) :
    prepareParsedIntegerMatrixReadLineExpression files oldSlots nextSlots store expression
      control hasSingleLineMask noForward reduced = .ok ([], nextSlots, []) := by
  rcases skip with forward | ⟨tag, waitEq⟩
  · simp [prepareParsedIntegerMatrixReadLineExpression, forward]
  · simp [prepareParsedIntegerMatrixReadLineExpression, waitEq]

/-- The fold over a concatenation: the first block's result is the second block's
starting accumulator. -/
theorem prepareParsedIntegerMatrixReadLineExpressions_append
    (files : IntegerRegisterFiles) (oldSlots : ProofsLean.MNCore.Forwarding.Slots)
    (store : ParsedMatrixReadStore) (control : ParsedMaskExecutionControl)
    (hasSingleLineMask noForward reduced : Bool) (second : List ParsedExpr) :
    ∀ (first : List ParsedExpr) (writes : List PreparedParsedMaskedWrite)
      (slots : ProofsLean.MNCore.Forwarding.Slots) (bars : List (Bool × BitVec 12))
      (writes1 : List PreparedParsedMaskedWrite)
      (slots1 : ProofsLean.MNCore.Forwarding.Slots) (bars1 : List (Bool × BitVec 12)),
      prepareParsedIntegerMatrixReadLineExpressions files oldSlots store control
        hasSingleLineMask noForward reduced first writes slots bars = .ok (writes1, slots1, bars1) →
      prepareParsedIntegerMatrixReadLineExpressions files oldSlots store control
        hasSingleLineMask noForward reduced (first ++ second) writes slots bars =
        prepareParsedIntegerMatrixReadLineExpressions files oldSlots store control
          hasSingleLineMask noForward reduced second writes1 slots1 bars1 := by
  intro first
  induction first with
  | nil =>
      intro writes slots bars writes1 slots1 bars1 executed
      simp only [prepareParsedIntegerMatrixReadLineExpressions,
        StepResult.ok.injEq, Prod.mk.injEq] at executed
      obtain ⟨rfl, rfl, rfl⟩ := executed
      rfl
  | cons expression rest ih =>
      intro writes slots bars writes1 slots1 bars1 executed
      rw [show (expression :: rest) ++ second = expression :: (rest ++ second) from rfl]
      simp only [prepareParsedIntegerMatrixReadLineExpressions] at executed ⊢
      cases result : prepareParsedIntegerMatrixReadLineExpression files oldSlots slots store
          expression control hasSingleLineMask noForward reduced with
      | failure => rw [result] at executed; simp at executed
      | unknown => rw [result] at executed; simp at executed
      | ok row =>
          rw [result] at executed
          dsimp only at executed
          obtain ⟨rowWrites, rowSlots, rowBars⟩ := row
          exact ih (writes ++ rowWrites) rowSlots (bars ++ rowBars) writes1 slots1 bars1 executed

/-- A prefix of `.noforward` / `.wait` rows can be dropped from the fold. -/
theorem prepareParsedIntegerMatrixReadLineExpressions_skip
    (files : IntegerRegisterFiles) (oldSlots : ProofsLean.MNCore.Forwarding.Slots)
    (store : ParsedMatrixReadStore) (control : ParsedMaskExecutionControl)
    (hasSingleLineMask noForward reduced : Bool) (rest : List ParsedExpr) :
    ∀ (first : List ParsedExpr),
      (∀ expression ∈ first,
        expression.op = .noforward ∨ ∃ tag : Fin 256, expression.op = .wait tag) →
      ∀ (writes : List PreparedParsedMaskedWrite)
        (slots : ProofsLean.MNCore.Forwarding.Slots) (bars : List (Bool × BitVec 12)),
      prepareParsedIntegerMatrixReadLineExpressions files oldSlots store control
        hasSingleLineMask noForward reduced (first ++ rest) writes slots bars =
        prepareParsedIntegerMatrixReadLineExpressions files oldSlots store control
          hasSingleLineMask noForward reduced rest writes slots bars := by
  intro first
  induction first with
  | nil => intro _ writes slots bars; rw [List.nil_append]
  | cons expression tail ih =>
      intro skips writes slots bars
      rw [List.cons_append]
      simp only [prepareParsedIntegerMatrixReadLineExpressions]
      rw [prepareParsedIntegerMatrixReadLineExpression_skip files oldSlots slots store expression
        control hasSingleLineMask noForward reduced (skips expression (by simp))]
      dsimp only
      rw [List.append_nil, List.append_nil]
      exact ih (fun item member => skips item (List.mem_cons_of_mem _ member)) writes slots bars

/-- **The fold over one row and skippable rows.**  If the stage list is
`before ++ e :: after` with `before` and `after` made of `.noforward` / `.wait`
rows, the result is the write list of `e` prepared at the initial slots. -/
theorem prepareParsedIntegerMatrixReadLineExpressions_single
    (files : IntegerRegisterFiles) (oldSlots : ProofsLean.MNCore.Forwarding.Slots)
    (store : ParsedMatrixReadStore) (control : ParsedMaskExecutionControl)
    (hasSingleLineMask noForward reduced : Bool)
    (before after : List ParsedExpr) (e : ParsedExpr)
    (skipBefore : ∀ expression ∈ before,
      expression.op = .noforward ∨ ∃ tag : Fin 256, expression.op = .wait tag)
    (skipAfter : ∀ expression ∈ after,
      expression.op = .noforward ∨ ∃ tag : Fin 256, expression.op = .wait tag)
    (writes : List PreparedParsedMaskedWrite) (slots : ProofsLean.MNCore.Forwarding.Slots)
    (bars : List (Bool × BitVec 12))
    (prep : prepareParsedIntegerMatrixReadLineExpressions files oldSlots store control
      hasSingleLineMask noForward reduced (before ++ e :: after) [] oldSlots [] =
      .ok (writes, slots, bars)) :
    ∃ rowWrites rowSlots rowBars,
      prepareParsedIntegerMatrixReadLineExpression files oldSlots oldSlots store e control
        hasSingleLineMask noForward reduced = .ok (rowWrites, rowSlots, rowBars) ∧
      writes = rowWrites := by
  rw [prepareParsedIntegerMatrixReadLineExpressions_skip files oldSlots store control
    hasSingleLineMask noForward reduced (e :: after) before skipBefore [] oldSlots []] at prep
  simp only [prepareParsedIntegerMatrixReadLineExpressions] at prep
  cases result : prepareParsedIntegerMatrixReadLineExpression files oldSlots oldSlots store e
      control hasSingleLineMask noForward reduced with
  | failure => rw [result] at prep; simp at prep
  | unknown => rw [result] at prep; simp at prep
  | ok row =>
      obtain ⟨rowWrites, rowSlots, rowBars⟩ := row
      rw [result] at prep
      dsimp only at prep
      simp only [List.nil_append] at prep
      have tail := prepareParsedIntegerMatrixReadLineExpressions_skip files oldSlots store control
        hasSingleLineMask noForward reduced [] after skipAfter rowWrites rowSlots rowBars
      have afterEq : prepareParsedIntegerMatrixReadLineExpressions files oldSlots store control
          hasSingleLineMask noForward reduced after rowWrites rowSlots rowBars =
          .ok (rowWrites, rowSlots, rowBars) := by
        rw [List.append_nil] at tail
        simpa only [prepareParsedIntegerMatrixReadLineExpressions] using tail
      rw [afterEq] at prep
      simp only [StepResult.ok.injEq, Prod.mk.injEq] at prep
      exact ⟨rowWrites, rowSlots, rowBars, rfl, prep.1.symm⟩

/-- **The single-writer form at the integer stage.**  The rows of the line other
than `e` are `.noforward` / `.wait` rows, so the prepared list is `e`'s own
prepared list at the initial forwarding slots. -/
theorem welcomeIntegerPrep_single_writer (state : State) (expressions : List ParsedExpr)
    (before after : List ParsedExpr) (e : ParsedExpr)
    (split : expressions.filter parsedExprIsIntegerMatrixReadStageInput = before ++ e :: after)
    (skipBefore : ∀ expression ∈ before,
      expression.op = .noforward ∨ ∃ tag : Fin 256, expression.op = .wait tag)
    (skipAfter : ∀ expression ∈ after,
      expression.op = .noforward ∨ ∃ tag : Fin 256, expression.op = .wait tag)
    (writes : List PreparedParsedMaskedWrite) (slots : ProofsLean.MNCore.Forwarding.Slots)
    (bars : List (Bool × BitVec 12))
    (prep : welcomeIntegerPrep state welcomePE expressions = .ok (writes, slots, bars)) :
    ∃ rowWrites rowSlots rowBars,
      prepareParsedIntegerMatrixReadLineExpression (state.peRegisters welcomePE)
        (stateForwardingSlots state welcomePE) (stateForwardingSlots state welcomePE)
        (state.matrixRegisters (ParsedIntegerContext.ofLinearIndex welcomePE).group
          (ParsedIntegerContext.ofLinearIndex welcomePE).l2b
          (ParsedIntegerContext.ofLinearIndex welcomePE).l1b)
        e (parsedPEHazardControl state welcomePE)
        ((expressions.filter parsedExprIsIntegerMatrixReadStageInput).any
          parsedExprHasSingleLineWriteMask)
        ((expressions.filter parsedExprIsIntegerMatrixReadStageInput).any fun expression =>
          match expression.op with
          | ParsedOp.noforward => true
          | _ => false)
        false = .ok (rowWrites, rowSlots, rowBars) ∧
      writes = rowWrites := by
  unfold welcomeIntegerPrep prepareParsedIntegerMatrixReadLineCycles at prep
  dsimp only at prep
  rw [split] at prep
  rw [split]
  exact prepareParsedIntegerMatrixReadLineExpressions_single _ _ _ _ _ _ _ _ _ _
    skipBefore skipAfter _ _ _ prep

/-! ## 5. The three row shapes

The plain row shape is the four-cycle fold of `WelcomePlainStep.lean` restated as
a *row* fact: it takes the line's own mask flag and no-forward flag as inputs, so
it applies to a plain row inside a mixed line.  The `.matrixRead` row shape is
`prepareParsedIntegerMatrixReadLineExpression_matrixRead_shape`, which is
uniform in both flags.  Inert rows prepare no write at all. -/

/-- **The plain row's `.lm1` shape.**  Four cycles of
`prepareParsedIntegerALUExprCycle`, each satisfying `Lm1ChunkFacts`, give the
double-copy or narrow shape of the row's whole write list. -/
theorem plainRow_lm1_shape (e : ParsedExpr)
    (notDouble : ∀ payload sparse, e.op = .immediate payload sparse →
      ∀ destination ∈ e.destinations,
        ParsedOperand.directDestinationBankWidth? destination ≠
          some (PEMemory.Bank.lm1, PEMemory.Width.double))
    (nodup : (e.toIssueExpr 0).writeBanks.Nodup)
    (noForward : Bool)
    (writes : List PreparedParsedMaskedWrite)
    (slots : ProofsLean.MNCore.Forwarding.Slots)
    (prep : prepareParsedIntegerALUExprCycles welcomeZeroFiles welcomeZeroSlots welcomeZeroSlots e
      welcomeZeroControl (parsedExprHasSingleLineWriteMask e) noForward false =
      .ok (writes, slots)) :
    Lm1WritesDoubleCopy writes ∨ Lm1WritesNarrow writes := by
  cases e with
  | mk op sources destinations flush text =>
      obtain ⟨w0, w1, w2, w3, s1, s2, s3, h0, h1, h2, h3, writesEq⟩ :=
        prepareParsedIntegerALUExprCycles_four welcomeZeroFiles welcomeZeroSlots
          ⟨op, sources, destinations, flush, text⟩ welcomeZeroControl
          (parsedExprHasSingleLineWriteMask ⟨op, sources, destinations, flush, text⟩)
          noForward false writes slots prep
      have f0 := prepareParsedIntegerALUExprCycle_lm1_facts op sources destinations flush text
        noForward 0 welcomeZeroSlots w0 s1 notDouble nodup h0
      have f1 := prepareParsedIntegerALUExprCycle_lm1_facts op sources destinations flush text
        noForward 1 s1 w1 s2 notDouble nodup h1
      have f2 := prepareParsedIntegerALUExprCycle_lm1_facts op sources destinations flush text
        noForward 2 s2 w2 s3 notDouble nodup h2
      have f3 := prepareParsedIntegerALUExprCycle_lm1_facts op sources destinations flush text
        noForward 3 s3 w3 slots notDouble nodup h3
      rw [writesEq]
      exact lm1WritesShape_of_chunks ⟨op, sources, destinations, flush, text⟩ nodup
        w0 w1 w2 w3 f0 f1 f2 f3

/-- **The plain row's `.lm1` shape, in the line-expression form** produced by the
integer stage: the row is prepared by
`prepareParsedIntegerMatrixReadLineExpression`, which for a plain op is the
four-cycle preparation plus a bar-update component. -/
theorem plainRow_lm1_shape_of_linePrep (e : ParsedExpr)
    (plain : parsedExprIsPlainIntegerALU e = true)
    (notDouble : ∀ payload sparse, e.op = .immediate payload sparse →
      ∀ destination ∈ e.destinations,
        ParsedOperand.directDestinationBankWidth? destination ≠
          some (PEMemory.Bank.lm1, PEMemory.Width.double))
    (nodup : (e.toIssueExpr 0).writeBanks.Nodup)
    (noForward : Bool)
    (writes : List PreparedParsedMaskedWrite)
    (slots : ProofsLean.MNCore.Forwarding.Slots) (bars : List (Bool × BitVec 12))
    (prep : prepareParsedIntegerMatrixReadLineExpression welcomeZeroFiles welcomeZeroSlots
      welcomeZeroSlots welcomeZeroMatrixStore e welcomeZeroControl
      (parsedExprHasSingleLineWriteMask e) noForward false = .ok (writes, slots, bars)) :
    Lm1WritesDoubleCopy writes ∨ Lm1WritesNarrow writes := by
  cases e with
  | mk op sources destinations flush text =>
      cases op with
      | alu name precision unsigned arg =>
          simp only [prepareParsedIntegerMatrixReadLineExpression] at prep
          cases cycles : prepareParsedIntegerALUExprCycles welcomeZeroFiles welcomeZeroSlots
              welcomeZeroSlots ⟨.alu name precision unsigned arg, sources, destinations, flush,
                text⟩ welcomeZeroControl
              (parsedExprHasSingleLineWriteMask
                ⟨.alu name precision unsigned arg, sources, destinations, flush, text⟩)
              noForward false with
          | failure => rw [cycles] at prep; simp at prep
          | unknown => rw [cycles] at prep; simp at prep
          | ok result =>
              obtain ⟨rowWrites, rowSlots⟩ := result
              rw [cycles] at prep
              simp only [StepResult.ok.injEq, Prod.mk.injEq] at prep
              rw [← prep.1]
              exact plainRow_lm1_shape _ notDouble nodup noForward rowWrites rowSlots cycles
      | zero =>
          simp only [prepareParsedIntegerMatrixReadLineExpression] at prep
          cases cycles : prepareParsedIntegerALUExprCycles welcomeZeroFiles welcomeZeroSlots
              welcomeZeroSlots ⟨.zero, sources, destinations, flush, text⟩ welcomeZeroControl
              (parsedExprHasSingleLineWriteMask ⟨.zero, sources, destinations, flush, text⟩)
              noForward false with
          | failure => rw [cycles] at prep; simp at prep
          | unknown => rw [cycles] at prep; simp at prep
          | ok result =>
              obtain ⟨rowWrites, rowSlots⟩ := result
              rw [cycles] at prep
              simp only [StepResult.ok.injEq, Prod.mk.injEq] at prep
              rw [← prep.1]
              exact plainRow_lm1_shape _ notDouble nodup noForward rowWrites rowSlots cycles
      | immediate value unsigned =>
          simp only [prepareParsedIntegerMatrixReadLineExpression] at prep
          cases cycles : prepareParsedIntegerALUExprCycles welcomeZeroFiles welcomeZeroSlots
              welcomeZeroSlots ⟨.immediate value unsigned, sources, destinations, flush, text⟩
              welcomeZeroControl
              (parsedExprHasSingleLineWriteMask
                ⟨.immediate value unsigned, sources, destinations, flush, text⟩)
              noForward false with
          | failure => rw [cycles] at prep; simp at prep
          | unknown => rw [cycles] at prep; simp at prep
          | ok result =>
              obtain ⟨rowWrites, rowSlots⟩ := result
              rw [cycles] at prep
              simp only [StepResult.ok.injEq, Prod.mk.injEq] at prep
              rw [← prep.1]
              exact plainRow_lm1_shape _ notDouble nodup noForward rowWrites rowSlots cycles
      | noforward =>
          simp [parsedExprIsPlainIntegerALU, parsedExprIsIntegerProducer,
            parsedExprIsUnsupportedRustAlu, parsedExprIsMslMsrProducer,
            parsedExprIsFloatReluProducer, parsedExprIsBlockFloatProducer] at plain
      | «wait» tag =>
          simp [parsedExprIsPlainIntegerALU, parsedExprIsIntegerProducer,
            parsedExprIsUnsupportedRustAlu, parsedExprIsMslMsrProducer,
            parsedExprIsFloatReluProducer, parsedExprIsBlockFloatProducer] at plain
      | mau precision matrix kind half round =>
          simp [parsedExprIsPlainIntegerALU, parsedExprIsIntegerProducer,
            parsedExprIsUnsupportedRustAlu, parsedExprIsMslMsrProducer,
            parsedExprIsFloatReluProducer, parsedExprIsBlockFloatProducer] at plain
      | matrixWrite precision =>
          simp [parsedExprIsPlainIntegerALU, parsedExprIsIntegerProducer,
            parsedExprIsUnsupportedRustAlu, parsedExprIsMslMsrProducer,
            parsedExprIsFloatReluProducer, parsedExprIsBlockFloatProducer] at plain
      | matrixRead precision =>
          simp [parsedExprIsPlainIntegerALU, parsedExprIsIntegerProducer,
            parsedExprIsUnsupportedRustAlu, parsedExprIsMslMsrProducer,
            parsedExprIsFloatReluProducer, parsedExprIsBlockFloatProducer] at plain
      | l1bm l1op =>
          simp [parsedExprIsPlainIntegerALU, parsedExprIsIntegerProducer,
            parsedExprIsUnsupportedRustAlu, parsedExprIsMslMsrProducer,
            parsedExprIsFloatReluProducer, parsedExprIsBlockFloatProducer] at plain
      | l2bm l2op =>
          simp [parsedExprIsPlainIntegerALU, parsedExprIsIntegerProducer,
            parsedExprIsUnsupportedRustAlu, parsedExprIsMslMsrProducer,
            parsedExprIsFloatReluProducer, parsedExprIsBlockFloatProducer] at plain

/-- **The `.matrixRead` row's `.lm1` shape**, uniformly in the line's mask and
no-forward flags. -/
theorem matrixReadRow_lm1_shape (e : ParsedExpr) (precision : ParsedPrecision)
    (sideY : Bool) (width : Fin 5) (row : Fin (2 ^ 32))
    (op : e.op = .matrixRead precision)
    (sources : e.sources = [.matrix sideY width (some row)])
    (control : ParsedMaskExecutionControl) (hasSingleLineMask noForward reduced : Bool)
    (w : PEMemory.Width)
    (nodup : (e.toIssueExpr 0).writeBanks.Nodup)
    (staticWidth : ∀ destination ∈ e.destinations, ∀ v : PEMemory.Width,
      ParsedOperand.directDestinationBankWidth? destination =
        some (PEMemory.Bank.lm1, v) → v = w)
    (writes : List PreparedParsedMaskedWrite)
    (slots : ProofsLean.MNCore.Forwarding.Slots) (bars : List (Bool × BitVec 12))
    (prep : prepareParsedIntegerMatrixReadLineExpression welcomeZeroFiles welcomeZeroSlots
      welcomeZeroSlots welcomeZeroMatrixStore e control hasSingleLineMask noForward reduced =
      .ok (writes, slots, bars)) :
    Lm1WritesDoubleCopy writes ∨ Lm1WritesNarrow writes :=
  prepareParsedIntegerMatrixReadLineExpression_matrixRead_shape e precision sideY width row op
    sources welcomeZeroSlots control hasSingleLineMask noForward reduced w nodup staticWidth
    writes slots bars prep

/-! ## 6. The unique-writer line shape

`welcomeLm1Writer_unique` says at most one row of an accepted line writes bank
`.lm1`.  The assembly (§3) makes the line's PE 0 file the commit of the integer
stage's list, and §4 shows that list is the writer row's own list.  Hence the
line's shape is the writer row's shape.  The stage blocks that write no `.lm1`
(the four middle stages and the L1BM-to-PE stage — all empty here) contribute
nothing. -/

/-- **The line shape from a writer row.**  If every row of the line is an
integer/matrix-read stage input or PE-inert, and the integer stage's list is one
row `e` plus `.noforward` / `.wait` rows, then the line's shape is `e`'s row
shape. -/
theorem welcomePEWriteShape_of_integerStageWriter
    (expressions : List NormalizedExpr) (unrefuted : WelcomePEUnrefuted expressions)
    (intOrInert : (expressions.map NormalizedExpr.toParsed).all
      welcomeIntegerOrInertLine = true)
    (before after : List ParsedExpr) (e : ParsedExpr)
    (split : (expressions.map NormalizedExpr.toParsed).filter
        parsedExprIsIntegerMatrixReadStageInput = before ++ e :: after)
    (skipBefore : ∀ expression ∈ before,
      expression.op = .noforward ∨ ∃ tag : Fin 256, expression.op = .wait tag)
    (skipAfter : ∀ expression ∈ after,
      expression.op = .noforward ∨ ∃ tag : Fin 256, expression.op = .wait tag)
    (rowShape : ∀ (writes : List PreparedParsedMaskedWrite)
      (slots : ProofsLean.MNCore.Forwarding.Slots) (bars : List (Bool × BitVec 12)),
      prepareParsedIntegerMatrixReadLineExpression welcomeZeroFiles welcomeZeroSlots
        welcomeZeroSlots welcomeZeroMatrixStore e welcomeZeroControl
        (((expressions.map NormalizedExpr.toParsed).filter
          parsedExprIsIntegerMatrixReadStageInput).any parsedExprHasSingleLineWriteMask)
        (((expressions.map NormalizedExpr.toParsed).filter
          parsedExprIsIntegerMatrixReadStageInput).any fun expression =>
          match expression.op with
          | ParsedOp.noforward => true
          | _ => false)
        false = .ok (writes, slots, bars) →
      Lm1WritesDoubleCopy writes ∨ Lm1WritesNarrow writes) :
    WelcomePEWriteShape expressions := by
  apply welcomePEWriteShape_of_commit_shape
  intro next step
  have executed := welcomeSealed_step_ok step
  simp only [executeNormalizedLine, NormalizedLine.toInstruction?,
    Issue.InstructionLine.toNormalizedLine] at executed
  obtain ⟨writes, slots, bars, prep, committed⟩ :=
    executeIntegerProducerInstructionLine_pe_commit_of_integerOrInert expressions
      (welcomeInitialState welcomeZeroWords) next unrefuted.1.1 unrefuted.1.2.1
      unrefuted.1.2.2.1 unrefuted.1.2.2.2 intOrInert executed
  obtain ⟨rowWrites, rowSlots, rowBars, rowPrep, writesEq⟩ :=
    welcomeIntegerPrep_single_writer (welcomeInitialState welcomeZeroWords)
      ((expressions.map NormalizedExpr.toParsed)) before after e split skipBefore skipAfter
      writes slots bars prep
  refine ⟨writes, committed, ?_⟩
  rw [writesEq]
  exact rowShape rowWrites rowSlots rowBars rowPrep

/-- **The plain-writer line shape.**  When the writer row is plain (`alu`,
`zero` or `immediate`), its row shape is `plainRow_lm1_shape`.  The only extra
inputs are the row's own write-bank nodup (the `writesUnique` half of the issue
checker), the exclusion of an `.lm1 .double` destination on an `.immediate` row
(that case is input-independent, not double-copy), and the agreement of the
line's mask flag with the row's own flag. -/
theorem welcomePEWriteShape_of_plainWriter
    (expressions : List NormalizedExpr) (unrefuted : WelcomePEUnrefuted expressions)
    (intOrInert : (expressions.map NormalizedExpr.toParsed).all
      welcomeIntegerOrInertLine = true)
    (before after : List ParsedExpr) (e : ParsedExpr)
    (split : (expressions.map NormalizedExpr.toParsed).filter
        parsedExprIsIntegerMatrixReadStageInput = before ++ e :: after)
    (skipBefore : ∀ expression ∈ before,
      expression.op = .noforward ∨ ∃ tag : Fin 256, expression.op = .wait tag)
    (skipAfter : ∀ expression ∈ after,
      expression.op = .noforward ∨ ∃ tag : Fin 256, expression.op = .wait tag)
    (flagEq : ((expressions.map NormalizedExpr.toParsed).filter
        parsedExprIsIntegerMatrixReadStageInput).any parsedExprHasSingleLineWriteMask =
        parsedExprHasSingleLineWriteMask e)
    (notDouble : ∀ payload sparse, e.op = .immediate payload sparse →
      ∀ destination ∈ e.destinations,
        ParsedOperand.directDestinationBankWidth? destination ≠
          some (PEMemory.Bank.lm1, PEMemory.Width.double))
    (nodup : (e.toIssueExpr 0).writeBanks.Nodup)
    (plain : parsedExprIsPlainIntegerALU e = true) :
    WelcomePEWriteShape expressions := by
  apply welcomePEWriteShape_of_integerStageWriter expressions unrefuted intOrInert before after e
    split skipBefore skipAfter
  intro writes slots bars prep
  rw [flagEq] at prep
  exact plainRow_lm1_shape_of_linePrep e plain notDouble nodup _ writes slots bars prep

/-- **The `.matrixRead`-writer line shape.**  The matrix-read row shape is
uniform in the mask and no-forward flags, so no flag agreement is needed. -/
theorem welcomePEWriteShape_of_matrixReadWriter
    (expressions : List NormalizedExpr) (unrefuted : WelcomePEUnrefuted expressions)
    (intOrInert : (expressions.map NormalizedExpr.toParsed).all
      welcomeIntegerOrInertLine = true)
    (before after : List ParsedExpr) (e : ParsedExpr)
    (split : (expressions.map NormalizedExpr.toParsed).filter
        parsedExprIsIntegerMatrixReadStageInput = before ++ e :: after)
    (skipBefore : ∀ expression ∈ before,
      expression.op = .noforward ∨ ∃ tag : Fin 256, expression.op = .wait tag)
    (skipAfter : ∀ expression ∈ after,
      expression.op = .noforward ∨ ∃ tag : Fin 256, expression.op = .wait tag)
    (precision : ParsedPrecision) (sideY : Bool) (width : Fin 5) (row : Fin (2 ^ 32))
    (op : e.op = .matrixRead precision)
    (sources : e.sources = [.matrix sideY width (some row)])
    (staticW : PEMemory.Width)
    (nodup : (e.toIssueExpr 0).writeBanks.Nodup)
    (staticWidth : ∀ destination ∈ e.destinations, ∀ v : PEMemory.Width,
      ParsedOperand.directDestinationBankWidth? destination =
        some (PEMemory.Bank.lm1, v) → v = staticW) :
    WelcomePEWriteShape expressions := by
  apply welcomePEWriteShape_of_integerStageWriter expressions unrefuted intOrInert before after e
    split skipBefore skipAfter
  intro writes slots bars prep
  exact matrixReadRow_lm1_shape e precision sideY width row op sources welcomeZeroControl _ _ _
    staticW nodup staticWidth writes slots bars prep

/-- **The no-`.lm1`-writer line shape.**  If no row the integer stage prepares
names bank `.lm1`, the prepared write list carries no `.lm1` write at all
(`WelcomePEIntegerStageLm1Provenance`), so both write shapes hold vacuously: the
commit cannot change the `.lm1` bank, and neither the double-copy nor the narrow
predicate has a `.lm1` destination to inspect. -/
theorem welcomePEWriteShape_of_noLm1Rows (expressions : List NormalizedExpr)
    (unrefuted : WelcomePEUnrefuted expressions)
    (intOrInert : (expressions.map NormalizedExpr.toParsed).all
      welcomeIntegerOrInertLine = true)
    (noLm1 : ∀ expression ∈ (expressions.map NormalizedExpr.toParsed).filter
      parsedExprIsIntegerMatrixReadStageInput, WelcomeRowHasNoLm1Destination expression) :
    WelcomePEWriteShape expressions := by
  apply welcomePEWriteShape_of_commit_shape
  intro next step
  have executed := welcomeSealed_step_ok step
  simp only [executeNormalizedLine, NormalizedLine.toInstruction?,
    Issue.InstructionLine.toNormalizedLine] at executed
  obtain ⟨writes, slots, bars, prep, committed⟩ :=
    executeIntegerProducerInstructionLine_pe_commit_of_integerOrInert expressions
      (welcomeInitialState welcomeZeroWords) next unrefuted.1.1 unrefuted.1.2.1
      unrefuted.1.2.2.1 unrefuted.1.2.2.2 intOrInert executed
  have free := welcomePEIntegerStageLm1Provenance
    ((expressions.map NormalizedExpr.toParsed)) (welcomeInitialState welcomeZeroWords)
    welcomePE writes slots bars prep noLm1
  refine ⟨writes, committed, Or.inl ?_⟩
  intro write member width address data selection destination dataEq selectionEq
  exact absurd rfl (isLm1Write_false_bank write (free write member)
    ⟨PEMemory.Bank.lm1, width, address⟩ destination)

/-- **The inert line shape.**  A line all of whose rows are PE-inert writes no PE
register at all, so its `.lm1` commit list is empty and both write shapes hold.
This is the "inert rows contribute no `.lm1` write" instantiation; the underlying
fact is `welcomePEInertLine_shape` of `WelcomeGapShape.lean`. -/
theorem welcomePEWriteShape_of_allInert (expressions : List NormalizedExpr)
    (all : ∀ expression ∈ expressions.map NormalizedExpr.toParsed,
      parsedExprIsPEInertProducer expression = true) :
    WelcomePEWriteShape expressions :=
  welcomePEInertLine_shape expressions all

/-! ## 7. The mixed plain/inert class and the precise remainder

The mixed obligation `WelcomePEMixedPlainInertShapeObligation` of
`WelcomeGapShape.lean` is the class "a plain row, no six-family row, no
special-ALU row".  By `supportedProducer_partition` every such row is plain or
PE-inert, so the integer stage's row list is the plain writer plus `.noforward`
rows, and §6 gives the line shape from the writer row's shape.  What is left is
a single **syntactic structure statement** about the line, which is isolated as
`WelcomePEMixedPlainInertStructure`.  Two of its components are residuals that
this module does not prove:

* the **mask-flag agreement**: the integer stage prepares its rows with the
  *line* mask flag `(filter).any parsedExprHasSingleLineWriteMask`, while the
  plain row's shape lemma (`plainRow_lm1_shape`) is stated at the row's own flag
  `parsedExprHasSingleLineWriteMask e`.  The two agree unless an inert row
  carries a masked `.mem` / `.bar` / `.omr` destination operand, which flips the
  line flag to `true` (`parsedOperandHasSingleLineWriteMask`).  Nothing in the
  issue checker forbids such a row, and the flag changes which masked lowering
  of the plain row fires, so the row-shape lemma cannot simply be reused; a
  proof of the flag-`true` case is missing.
* the **immediate-double exclusion**: an `.immediate` writer row with an
  `.lm1 .double` destination is *input-independent*, not double-copy
  (`WelcomePEPlainImmediateDoubleObligation` in `WelcomePlainClose.lean` proves
  exactly that for all-plain lines).  For the mixed class the same two-run
  comparison has to be carried out with the inert rows present; it is not done
  here.

The remaining components — every row is integer-or-inert, the filtered list
splits as `noforward* ++ [writer] ++ noforward*`, and the writer's write banks
are duplicate free — are list bookkeeping; `plain_rows_at_most_one_eq` below is
the part of it that is proved. -/

/-- **A legal line has at most one plain row.**  Every plain row has issue group
`.alu`, `projectLine` numbers its rows consecutively, and `groupsUnique` forbids
two different ids in the same group. -/
theorem plain_rows_at_most_one_eq (line : List ParsedExpr)
    (legal : LegalParsedLine line)
    (i j : Nat) (hi : i < line.length) (hj : j < line.length)
    (plainI : parsedExprIsPlainIntegerALU (line[i]'hi) = true)
    (plainJ : parsedExprIsPlainIntegerALU (line[j]'hj) = true) :
    i = j := by
  have lengthEq : (projectLine line).length = line.length := projectFrom_length 0 line
  have iLt : i < (projectLine line).length := by omega
  have jLt : j < (projectLine line).length := by omega
  have groupI : ((projectLine line)[i]'iLt).group = some Issue.Group.alu :=
    projectLine_getElem_group line i iLt hi Issue.Group.alu (plainExpr_issueGroup _ plainI)
  have groupJ : ((projectLine line)[j]'jLt).group = some Issue.Group.alu :=
    projectLine_getElem_group line j jLt hj Issue.Group.alu (plainExpr_issueGroup _ plainJ)
  have idI : ((projectLine line)[i]'iLt).id = i := projectLine_getElem_id line i iLt
  have idJ : ((projectLine line)[j]'jLt).id = j := projectLine_getElem_id line j jLt
  by_contra different
  have distinctIds : ((projectLine line)[i]'iLt).id ≠ ((projectLine line)[j]'jLt).id := by
    rw [idI, idJ]
    exact different
  exact legal.2.1 ((projectLine line)[i]'iLt) (List.getElem_mem iLt)
    ((projectLine line)[j]'jLt) (List.getElem_mem jLt) distinctIds Issue.Group.alu groupI
    (by rw [groupJ])

/-- **Every row of a mixed line is integer-or-inert.**  This is the "no family,
no special ALU" half of the partition: the remaining supported rows are plain
(hence integer-stage inputs, `plain_stageInput`) or PE-inert. -/
theorem welcomeMixed_rows_integerOrInert (expressions : List NormalizedExpr)
    (unrefuted : WelcomePEUnrefuted expressions)
    (noFamily : (expressions.map NormalizedExpr.toParsed).any
      parsedExprIsFamilyProducer = false)
    (noSpecial : (expressions.map NormalizedExpr.toParsed).any
      parsedExprIsSpecialALUProducer = false) :
    (expressions.map NormalizedExpr.toParsed).all welcomeIntegerOrInertLine = true := by
  rw [List.all_eq_true]
  intro expression member
  have supported := List.all_eq_true.mp unrefuted.1.2.2.2 expression member
  have notUnsupported : parsedExprIsUnsupportedRustAlu expression = false := by
    simpa using (List.any_eq_false.mp unrefuted.1.2.2.1) expression member
  have notFamily : parsedExprIsFamilyProducer expression = false := by
    simpa using (List.any_eq_false.mp noFamily) expression member
  have notSpecial : parsedExprIsSpecialALUProducer expression = false := by
    simpa using (List.any_eq_false.mp noSpecial) expression member
  rcases supportedProducer_partition expression supported with
    plain | family | special | inert | unsupported
  · simp [welcomeIntegerOrInertLine, plain_stageInput expression plain]
  · rw [notFamily] at family
    cases family
  · rw [notSpecial] at special
    cases special
  · simp [welcomeIntegerOrInertLine, inert]
  · rw [notUnsupported] at unsupported
    cases unsupported

/-- **The structure of a mixed plain/inert line**, as consumed by §6.  The
integer stage's row list is `.noforward` rows around the unique plain writer; the
writer's write banks are duplicate free; the line mask flag agrees with the
writer's own flag; and the writer is not an `.immediate` row with an `.lm1
.double` destination.  The last two components are the residuals described
above. -/
def WelcomePEMixedPlainInertStructure : Prop :=
  ∀ expressions : List NormalizedExpr, WelcomePEUnrefuted expressions →
    (expressions.map NormalizedExpr.toParsed).all parsedExprIsPlainIntegerALU = false →
    (expressions.map NormalizedExpr.toParsed).any parsedExprIsPlainIntegerALU = true →
    (expressions.map NormalizedExpr.toParsed).any parsedExprIsFamilyProducer = false →
    (expressions.map NormalizedExpr.toParsed).any parsedExprIsSpecialALUProducer = false →
    ∃ (before after : List ParsedExpr) (e : ParsedExpr),
      (expressions.map NormalizedExpr.toParsed).filter
          parsedExprIsIntegerMatrixReadStageInput = before ++ e :: after ∧
      (∀ expression ∈ before, expression.op = ParsedOp.noforward) ∧
      (∀ expression ∈ after, expression.op = ParsedOp.noforward) ∧
      parsedExprIsPlainIntegerALU e = true ∧
      (e.toIssueExpr 0).writeBanks.Nodup ∧
      (((expressions.map NormalizedExpr.toParsed).filter
            parsedExprIsIntegerMatrixReadStageInput).any parsedExprHasSingleLineWriteMask =
        parsedExprHasSingleLineWriteMask e) ∧
      (∀ (payload : BitVec 32) (sparse : Bool), e.op = .immediate payload sparse →
        ∀ destination ∈ e.destinations,
          ParsedOperand.directDestinationBankWidth? destination ≠
            some (PEMemory.Bank.lm1, PEMemory.Width.double))

/-- **The mixed obligation from the structure statement.**  The value content is
entirely §6; nothing about the executor or the commit is assumed. -/
theorem welcomePEMixedPlainInertShapeObligation_of_structure
    (skeleton : WelcomePEMixedPlainInertStructure) :
    WelcomePEMixedPlainInertShapeObligation := by
  intro expressions unrefuted notPlain plainAny noFamily noSpecial
  obtain ⟨before, after, e, split, skipBefore, skipAfter, ePlain, nodup,
    flagEq, notDouble⟩ :=
    skeleton expressions unrefuted notPlain plainAny noFamily noSpecial
  have intOrInert := welcomeMixed_rows_integerOrInert expressions unrefuted noFamily noSpecial
  exact welcomePEWriteShape_of_plainWriter expressions unrefuted intOrInert before after e
    split (fun expression member => Or.inl (skipBefore expression member))
    (fun expression member => Or.inl (skipAfter expression member))
    flagEq notDouble nodup ePlain

/-- **The aggregate, with the mixed obligation replaced by the structure
statement.**  This is the exact position of the aggregate after this module:
eight `Prop`s plus `WelcomePEMixedPlainInertStructure` imply the per-line shape
obligation. -/
theorem welcomePELm1WriteShapeObligation_of_eight_and_structure
    (plain : WelcomePEPlainShapeObligation)
    (read : WelcomePEMatrixReadShapeObligation)
    (mau : WelcomePEMatrixMAUShapeObligation)
    (float : WelcomePEFloatMAUShapeObligation)
    (write : WelcomePEMatrixWriteShapeObligation)
    (l1 : WelcomePEL1ToPEShapeObligation)
    (l2 : WelcomePEL2BMShapeObligation)
    (special : WelcomePESpecialALUShapeObligation)
    (skeleton : WelcomePEMixedPlainInertStructure) :
    WelcomePELm1WriteShapeObligation :=
  welcomePELm1WriteShapeObligation_of_nine plain read mau float write l1 l2 special
    (welcomePEMixedPlainInertShapeObligation_of_structure skeleton)

/-- **The mixed obligation, from the writer-row data alone.**  This is the
low-level form of the reduction: any producer of the syntactic decomposition and
of the two flag facts yields the mixed obligation. -/
theorem welcomePEMixedPlainInertShapeObligation_of_writer
    (data : ∀ expressions : List NormalizedExpr, WelcomePEUnrefuted expressions →
      (expressions.map NormalizedExpr.toParsed).all parsedExprIsPlainIntegerALU = false →
      (expressions.map NormalizedExpr.toParsed).any parsedExprIsPlainIntegerALU = true →
      (expressions.map NormalizedExpr.toParsed).any parsedExprIsFamilyProducer = false →
      (expressions.map NormalizedExpr.toParsed).any parsedExprIsSpecialALUProducer = false →
      ∃ (before after : List ParsedExpr) (e : ParsedExpr),
        (expressions.map NormalizedExpr.toParsed).filter
            parsedExprIsIntegerMatrixReadStageInput = before ++ e :: after ∧
        (∀ expression ∈ before, expression.op = ParsedOp.noforward) ∧
        (∀ expression ∈ after, expression.op = ParsedOp.noforward) ∧
        parsedExprIsPlainIntegerALU e = true ∧
        (e.toIssueExpr 0).writeBanks.Nodup ∧
        (((expressions.map NormalizedExpr.toParsed).filter
              parsedExprIsIntegerMatrixReadStageInput).any parsedExprHasSingleLineWriteMask =
          parsedExprHasSingleLineWriteMask e) ∧
        (∀ (payload : BitVec 32) (sparse : Bool), e.op = .immediate payload sparse →
          ∀ destination ∈ e.destinations,
            ParsedOperand.directDestinationBankWidth? destination ≠
              some (PEMemory.Bank.lm1, PEMemory.Width.double))) :
    WelcomePEMixedPlainInertShapeObligation :=
  welcomePEMixedPlainInertShapeObligation_of_structure data

/-! ## 8. What remains

The per-line write-shape obligation `WelcomePELm1WriteShapeObligation` is, after
this module,

* `WelcomePEPlainShapeObligation` — **proved** (`WelcomePlainStep.lean`);
* `WelcomePEMixedPlainInertShapeObligation` — **reduced** to
  `WelcomePEMixedPlainInertStructure` (§7), whose remaining components are the
  mask-flag agreement and the immediate-double exclusion below, plus list
  bookkeeping (`welcomeMixed_rows_integerOrInert` is the first piece of it);
* `WelcomePEMatrixReadShapeObligation` — the **writer-row half is proved**:
  `matrixReadRow_lm1_shape` (uniform in both flags) plus
  `welcomePEWriteShape_of_matrixReadWriter`.  The obligation is *not*
  discharged, because a line containing a matrix-read row may have a different
  unique writer (the issue checker only forbids two `.lm1` writers, not a
  matrix-read row that does not write `.lm1`), and because the line
  decomposition is not formalised;
* `WelcomePEMatrixWriteShapeObligation`, `WelcomePEL2BMShapeObligation` — these
  rows never write a PE register file, so a line whose rows are such rows plus
  the writer is handled by the reduction; but the obligations allow arbitrary
  other rows (any family may be the writer), so they are not discharged either;
* `WelcomePEFloatMAUShapeObligation` — **unproved**: the writes prepared by
  `executeParsedFloatMAUsAtPE` have no `.lm1` shape lemma at all;
* `WelcomePEMatrixMAUShapeObligation` — **unproved**: `commitParsedMatrixMAUPEState`
  writes four PE register files per MAB coordinate, so a matrix-MAU row *can* be
  the unique `.lm1` writer and needs its own row shape;
* `WelcomePEL1ToPEShapeObligation` — **unproved**: an `.l1bm` row with a
  `.mem lm1` destination (`pbcast` / `mbcast` / `m4bcast` / `distrib`) writes PE
  bank `.lm1`; the required facts are `l1ToPEWrites_doubleCopy` and
  `l1ToPEWrites_narrow` of `WelcomeL12Shape.lean`, and the `.double` case still
  lacks the **4-alignment divisibility lemma** that derives `address.val % 4 = 0`
  from `toDirectMemoryAccessMode?` (the shape requires it, `WelcomeL12Shape` does
  not derive it);
* `WelcomePESpecialALUShapeObligation` — the msl/msr row shape is proved
  (`welcomePEMslMsrCyclesShape`), the float-relu and block-float row shapes only
  in their corrected forms, and the writer-row line assembly is again §6.

The two residuals inside `WelcomePEMixedPlainInertStructure`:

* **mask-flag agreement** — `(filter).any parsedExprHasSingleLineWriteMask =
  parsedExprHasSingleLineWriteMask e`.  It fails only when an inert row carries a
  masked `.mem` / `.bar` / `.omr` destination operand
  (`parsedOperandHasSingleLineWriteMask`).  The flag decides whether an
  *unmasked* `.mem` destination of the plain row resolves as a masked write
  (`parsed_issue_line_mask_cancels_unmasked_memory_target`), so it changes which
  lowering branch fires.  The row-shape lemma `plainRow_lm1_shape` is stated at
  the row's own flag, so it cannot be reused for the line flag; the flag-`true`
  case would need the whole per-branch analysis of `WelcomePlainStep.lean`
  repeated with a free flag;
* **immediate-double exclusion** — an `.immediate` writer with an `.lm1 .double`
  destination is input-independent; `WelcomePEPlainImmediateDoubleObligation`
  proves that for all-plain lines, the mixed-line two-run comparison is missing.

No `LowerBound 2` and no `Optimal` is claimed. -/

end ProofsLean.MNCore
