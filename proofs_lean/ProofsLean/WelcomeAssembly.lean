import ProofsLean.WelcomeMAUShape
import ProofsLean.WelcomeL12Shape

/-! # F1: the line-level stage assembly for a `.pe` line

`WelcomeValueBound.lean` reduces `LowerBound welcomeSealedMachine welcomeSpec 2`
to the per-line write shape `WelcomePELm1WriteShapeObligation`; `WelcomeMAUShape`
and `WelcomeL12Shape` analyse the individual producer families.  What is missing
between them is the **line-level assembly**: a `.pe` line runs seven stages
(`executeIntegerProducerInstructionLine`), and each of them may contribute
prepared masked writes to PE 0's register file.  The line's `LM1` output is the
`LM1` part of the concatenation of the stage write lists, and the issue checker
allows only one row to write `LM1` (`welcomeLm1Writer_unique`), so at most one
stage's list can carry `LM1` destinations.

## What is proved here

* **Stage peeling** (§2, `executeIntegerProducerInstructionLine_pe_stages_exists`):
  a successful `.pe` step exposes the six intermediate states, each stage's
  `.ok` equation, and the final clock/turnaround update.
* **Absent-stage identities** (§1): a stage whose producer filter is empty is the
  identity (`executeParsedMslMsrProducers_eq_self`, `..._FloatRelu...`,
  `..._BlockFloat...`, `executeParsedL1ToPEProducers_eq_self`,
  `executeParsedMatrixMAUAndWrites_eq_self`, and the shared-block list form).
* **The clean line class** (§3): rows of the integer/matrix-read stage plus
  `.matrixWrite` rows.  For such a line the whole PE 0 register file is the
  commit of the integer stage's prepared write list —
  `executeIntegerProducerInstructionLine_pe_commit_of_clean`, and at the sealed
  machine `welcomePE_line_commit_of_clean` (which carries the exact
  `welcomeIntegerPrep` list).  The plain integer-ALU class is a subclass
  (`welcomeStageClean_of_plain`, `welcomePE_line_commit_of_plain`), so the result
  is not vacuous.
* **The general assembly** (§4, `executeIntegerProducerInstructionLine_pe_stage_commit`
  and its sealed-machine form `welcomePE_line_stage_commit`): from the six
  per-stage commit obligations — bundled as `WelcomePEStageCommitForm` — the line
  leaves PE 0's register file equal to the commit of
  integer ++ MSL/MSR ++ float-relu ++ block-float ++ matrix-MAU/write ++
  L1BM-to-PE.  The composition itself is proved; only the six per-stage commit
  facts are hypotheses.
* **The `.lm1` algebra** (§5): the `.lm1` bank of a commit is the commit of its
  `.lm1` writes (`commitParsedMaskedWrites_lm1_filter`), and a list with no
  `.lm1` write can be dropped from a concatenation without changing the `.lm1`
  bank (`commitParsedMaskedWrites_lm1_concat_of_only`).  Together these say that
  the `.lm1` part of the line's concatenation is the unique writer's `.lm1` part.
* **The line-level `.lm1` frame** (§6, `executeIntegerProducerInstructionLine_pe_lm1_frame`
  and `welcomePE_line_lm1_frame`): a line none of whose rows names bank `.lm1`
  leaves PE 0's `.lm1` bank unchanged, from the two `.lm1` frame obligations.
  Its value consequence is proved: such a line is refuted
  (`welcomePE_not_correct_of_noLm1Destination`).

## What is NOT proved here

None of the following is assumed anywhere; each is a named `Prop`:

* `WelcomePEIntegerFloatStageCommit` / `WelcomePEIntegerStageCommit` — the
  integer stage commits at PE 0 even when the line carries **float-MAU** rows
  (those are executed inside the integer stage, at `executeParsedFloatMAUsAtPE`;
  the proved `executeIntegerProducerLineAtPEs_prepared` needs the float filter to
  be empty);
* `WelcomePEMslMsrStageCommit`, `WelcomePEFloatReluStageCommit`,
  `WelcomePEBlockFloatStageCommit`, `WelcomePEMatrixMAUStageCommit`,
  `WelcomePEL1ToPEStageCommit` — the four middle stages and the L1BM-to-PE stage
  each commit a prepared write list at PE 0 (proved only when the stage's
  producer filter is empty, i.e. as the empty list);
* `WelcomePEIntegerStageLm1Provenance` / `WelcomePEIntegerStageLm1Frame` — the
  integer stage's prepared list writes `.lm1` only when a row it prepares names
  bank `.lm1`;
* `WelcomePEStageLm1Frame` — the four middle stages and the L1BM-to-PE stage
  preserve PE 0's `.lm1` bank when no row names bank `.lm1`.

Consequently this module does **not** prove `LowerBound welcomeSealedMachine
welcomeSpec 2` and does not prove `Optimal welcomeSealedMachine welcomeSpec
welcomeAnswer`.  No `sorry`, no `admit`, no `native_decide`, no new axioms.
-/

namespace ProofsLean.MNCore

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

open Issue
open PEMemory

/-! ## 1. The absent-stage identities

Each of the six non-integer stages of `executeIntegerProducerInstructionLine`
returns the state unchanged when the line contains no row of that stage's
producer family. -/

/-- **MSL/MSR stage.** With no MSL/MSR row the stage is the identity. -/
theorem executeParsedMslMsrProducers_eq_self
    (readState currentState : State) (expressions : List ParsedExpr)
    (noForward hasSingleLineMask : Bool)
    (absent : expressions.filter parsedExprIsMslMsrProducer = []) :
    executeParsedMslMsrProducers readState currentState expressions noForward
      hasSingleLineMask = .ok currentState := by
  simp [executeParsedMslMsrProducers, absent]

/-- **Float-relu stage.** With no float-relu row the stage is the identity. -/
theorem executeParsedFloatReluProducers_eq_self
    (readState currentState : State) (expressions : List ParsedExpr)
    (noForward hasSingleLineMask : Bool)
    (absent : expressions.filter parsedExprIsFloatReluProducer = []) :
    executeParsedFloatReluProducers readState currentState expressions noForward
      hasSingleLineMask = .ok currentState := by
  simp [executeParsedFloatReluProducers, absent]

/-- **Block-float stage.** With no block-float row the stage is the identity. -/
theorem executeParsedBlockFloatProducer_eq_self
    (readState currentState : State) (expressions : List ParsedExpr)
    (noForward hasSingleLineMask : Bool)
    (absent : expressions.filter parsedExprIsBlockFloatProducer = []) :
    executeParsedBlockFloatProducer readState currentState expressions noForward
      hasSingleLineMask = .ok currentState := by
  simp [executeParsedBlockFloatProducer, absent]

/-- **L1BM-to-PE stage.** With no L1BM-to-PE row the stage is the identity. -/
theorem executeParsedL1ToPEProducers_eq_self
    (readState currentState : State) (expressions : List ParsedExpr)
    (noForward hasSingleLineMask usePreIssueMask : Bool)
    (absent : expressions.filter parsedExprIsL1ToPEProducer = []) :
    executeParsedL1ToPEProducers readState currentState expressions noForward
      hasSingleLineMask usePreIssueMask = .ok currentState := by
  simp [executeParsedL1ToPEProducers, absent]

/-- **Matrix-MAU/write stage.** With no matrix-MAU row and no `.matrixWrite` row
the stage is the identity. -/
theorem executeParsedMatrixMAUAndWrites_eq_self
    (readState currentState : State) (expressions : List ParsedExpr)
    (noForward hasSingleLineMask : Bool)
    (noMatrixMAU : expressions.filter parsedExprIsMatrixMAUProducer = [])
    (noMatrixWrite : expressions.any parsedExprIsMatrixWriteProducer = false) :
    executeParsedMatrixMAUAndWrites readState currentState expressions noForward
      hasSingleLineMask = .ok currentState := by
  unfold executeParsedMatrixMAUAndWrites executeParsedMatrixWritesAtMABs
  rw [executeParsedMatrixMAUProducer]
  simp [noMatrixMAU, noMatrixWrite]

/-- **Shared-block stage.** The stage is the identity on a state whose rows are
all non-block-producer rows. -/
theorem executeParsedSharedBlockProducerList_eq_self
    (readState : State) (updateTurnaround : Bool) :
    ∀ (expressions : List ParsedExpr) (state : State),
      (∀ expression ∈ expressions,
        executeParsedSharedBlockExpression readState state expression updateTurnaround =
          .ok state) →
      executeParsedSharedBlockProducers readState state expressions updateTurnaround =
        .ok state := by
  intro expressions
  induction expressions with
  | nil => intro state _; simp [executeParsedSharedBlockProducers,
      executeParsedSharedBlockProducerList]
  | cons expression rest ih =>
      intro state identity
      have head := identity expression (by simp)
      simp only [executeParsedSharedBlockProducers, executeParsedSharedBlockProducerList,
        head]
      exact ih state (fun item member => identity item (List.mem_cons_of_mem _ member))

/-! ## 2. Peeling a successful `.pe` line into its seven stages

`executeIntegerProducerInstructionLine` runs the seven stages in sequence.  A
successful `.pe` step therefore yields the six intermediate states of the
non-integer stages, each stage's `.ok` equation, and the final clock/turnaround
update.  This is the shape every assembly proof below consumes. -/

/-- **Stage peeling.**  A successful `.pe` step exposes the seven stage results. -/
theorem executeIntegerProducerInstructionLine_pe_stages_exists
    (expressions : List NormalizedExpr) (state next : State)
    (accepted : checkParsedTopLine (InstructionLine.pe expressions).toParsed = true)
    (waits : (expressions.map NormalizedExpr.toParsed).any (parsedExprWaitPending state) = false)
    (unsupported : (expressions.map NormalizedExpr.toParsed).any
      parsedExprIsUnsupportedRustAlu = false)
    (supported : (expressions.map NormalizedExpr.toParsed).all
      parsedExprIsSupportedPELineProducer = true)
    (step : executeIntegerProducerInstructionLine (.pe expressions) state = .ok next) :
    ∃ nextPEs nextMsl nextRelu nextBlockFloat afterMatrix nextShared nextBroadcast,
      executeIntegerProducerLineAtPEs
        ((expressions.map NormalizedExpr.toParsed).filter (fun expression =>
          !parsedExprIsL2BMProducer expression && !parsedExprIsMslMsrProducer expression &&
            !parsedExprIsMatrixMAUProducer expression &&
            !parsedExprIsBlockFloatProducer expression &&
            !parsedExprIsFloatReluProducer expression))
        (List.finRange 4096) state = .ok nextPEs ∧
      executeParsedMslMsrProducers state nextPEs
        (expressions.map NormalizedExpr.toParsed)
        (expressions.any (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed))
        (expressions.any (parsedExprHasSingleLineWriteMask ∘ NormalizedExpr.toParsed)) =
        .ok nextMsl ∧
      executeParsedFloatReluProducers state nextMsl
        (expressions.map NormalizedExpr.toParsed)
        (expressions.any (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed))
        (expressions.any (parsedExprHasSingleLineWriteMask ∘ NormalizedExpr.toParsed)) =
        .ok nextRelu ∧
      executeParsedBlockFloatProducer state nextRelu
        (expressions.map NormalizedExpr.toParsed)
        (expressions.any (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed))
        (expressions.any (parsedExprHasSingleLineWriteMask ∘ NormalizedExpr.toParsed)) =
        .ok nextBlockFloat ∧
      executeParsedMatrixMAUAndWrites state nextBlockFloat
        (expressions.map NormalizedExpr.toParsed)
        (expressions.any (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed))
        (expressions.any (parsedExprHasSingleLineWriteMask ∘ NormalizedExpr.toParsed)) =
        .ok afterMatrix ∧
      executeParsedSharedBlockProducers state afterMatrix
        (expressions.map NormalizedExpr.toParsed)
        (!(expressions.any (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed))) =
        .ok nextShared ∧
      executeParsedL1ToPEProducers state nextShared
        (expressions.map NormalizedExpr.toParsed)
        (expressions.any (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed))
        (expressions.any (parsedExprHasSingleLineWriteMask ∘ NormalizedExpr.toParsed))
        (parsedL1ToPEPrecedesOMRWriter (expressions.map NormalizedExpr.toParsed)) =
        .ok nextBroadcast ∧
      next = { nextBroadcast with
        hazardClock := nextBroadcast.hazardClock + InstructionLine.cost (.pe expressions)
        l1bmTurnaroundValid :=
          if expressions.any (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed)
          then nextBroadcast.l1bmTurnaroundValid
          else expressions.any (fun expression =>
            parsedExprMayWriteL1BMTurnaround expression.toParsed) } := by
  unfold executeIntegerProducerInstructionLine at step
  simp only [accepted, waits, unsupported, supported, List.any_map, Bool.not_true,
    Bool.false_eq_true, ite_true, ite_false] at step
  split at step
  · simp at step
  · simp at step
  · rename_i nextPEs walkExecuted
    split at step
    · simp at step
    · simp at step
    · rename_i nextMsl mslExecuted
      split at step
      · simp at step
      · simp at step
      · rename_i nextRelu reluExecuted
        split at step
        · simp at step
        · simp at step
        · rename_i nextBlockFloat blockExecuted
          split at step
          · simp at step
          · simp at step
          · rename_i afterMatrix matrixExecuted
            split at step
            · simp at step
            · simp at step
            · rename_i nextShared sharedExecuted
              split at step
              · simp at step
              · simp at step
              · rename_i nextBroadcast l1Executed
                simp only [StepResult.ok.injEq] at step
                exact ⟨nextPEs, nextMsl, nextRelu, nextBlockFloat, afterMatrix, nextShared,
                  nextBroadcast, walkExecuted, mslExecuted, reluExecuted, blockExecuted,
                  matrixExecuted, sharedExecuted, l1Executed, step.symm⟩

/-! ## 3. The clean line class: rows of the integer/matrix-read stage and `.matrixWrite`

The seven-stage line degenerates whenever every row belongs to the integer /
matrix-read stage or is a `.matrixWrite` row: the four middle stages and the
L1BM-to-PE stage are then the identity, the matrix-MAU/write stage only rewrites
the matrix registers, and the shared-block stage dispatches each of these rows to
the identity.  For this class the whole line's PE 0 file is the commit of the
integer stage's prepared write list. -/

/-- The rows for which the line assembly is the identity outside the integer
stage: the integer/matrix-read stage inputs and the `.matrixWrite` rows. -/
def welcomeStageCleanExpression (expression : ParsedExpr) : Bool :=
  parsedExprIsIntegerMatrixReadStageInput expression ||
    parsedExprIsMatrixWriteProducer expression

/-- **The family predicates of a clean row.**  A clean row is not an MSL/MSR,
float-relu, block-float, matrix-MAU, L1BM-to-PE, L2BM or float-MAU producer. -/
theorem welcomeStageCleanExpression_notFamilies (expression : ParsedExpr)
    (clean : welcomeStageCleanExpression expression = true) :
    parsedExprIsL2BMProducer expression = false ∧
    parsedExprIsMslMsrProducer expression = false ∧
    parsedExprIsMatrixMAUProducer expression = false ∧
    parsedExprIsBlockFloatProducer expression = false ∧
    parsedExprIsFloatReluProducer expression = false ∧
    parsedExprIsL1ToPEProducer expression = false ∧
    parsedExprIsSupportedFloatMAUProducer expression = false := by
  rcases expression with ⟨op, sources, destinations, flush, text⟩
  simp only [welcomeStageCleanExpression, Bool.or_eq_true,
    parsedExprIsMatrixWriteProducer] at clean
  rcases clean with input | mwrite
  · obtain ⟨_, notL2BM, _, _, _, _, notL1ToPE, notMatrixMAU, notFloatMAU, notMslMsr,
      notBlockFloat, notFloatRelu⟩ :=
      (parsedExprIsIntegerMatrixReadStageInput_spec _).mp input
    exact ⟨notL2BM, notMslMsr, notMatrixMAU, notBlockFloat, notFloatRelu, notL1ToPE,
      notFloatMAU⟩
  · cases op <;>
      simp_all [parsedExprIsL2BMProducer, parsedExprIsMslMsrProducer,
        parsedExprIsMatrixMAUProducer, parsedExprIsBlockFloatProducer,
        parsedExprIsFloatReluProducer, parsedExprIsL1ToPEProducer,
        parsedExprIsSupportedFloatMAUProducer]

/-- **A supported integer-stage input row is an integer-line candidate.** -/
theorem parsedExpr_stageInput_candidate (expression : ParsedExpr)
    (input : parsedExprIsIntegerMatrixReadStageInput expression = true)
    (supported : parsedExprIsSupportedPELineProducer expression = true) :
    parsedExprIsIntegerMatrixReadLineCandidate expression = true :=
  parsedExpr_supported_stage_input_is_candidate expression [expression] supported
    (by simpa using input)

/-- The shared-block stage dispatches every integer-line candidate row to the
identity. -/
theorem candidate_sharedBlockExpression_eq_self
    (readState currentState : State) (expression : ParsedExpr) (updateTurnaround : Bool)
    (candidate : parsedExprIsIntegerMatrixReadLineCandidate expression = true) :
    executeParsedSharedBlockExpression readState currentState expression updateTurnaround =
      .ok currentState := by
  rcases expression with ⟨op, sources, destinations, flush, text⟩
  cases op <;> simp_all [parsedExprIsIntegerMatrixReadLineCandidate,
    executeParsedSharedBlockExpression]

/-- The shared-block stage dispatches every `.matrixWrite` row to the identity. -/
theorem matrixWrite_sharedBlockExpression_eq_self
    (readState currentState : State) (expression : ParsedExpr) (updateTurnaround : Bool)
    (mwrite : parsedExprIsMatrixWriteProducer expression = true) :
    executeParsedSharedBlockExpression readState currentState expression updateTurnaround =
      .ok currentState := by
  rcases expression with ⟨op, sources, destinations, flush, text⟩
  simp only [parsedExprIsMatrixWriteProducer] at mwrite
  cases op <;> simp_all [executeParsedSharedBlockExpression]

/-- **A clean row is dispatched to the identity by the shared-block stage.** -/
theorem welcomeStageCleanExpression_sharedBlock_eq_self
    (readState currentState : State) (expression : ParsedExpr) (updateTurnaround : Bool)
    (clean : welcomeStageCleanExpression expression = true)
    (supported : parsedExprIsSupportedPELineProducer expression = true) :
    executeParsedSharedBlockExpression readState currentState expression updateTurnaround =
      .ok currentState := by
  rcases expression with ⟨op, sources, destinations, flush, text⟩
  simp only [welcomeStageCleanExpression, Bool.or_eq_true,
    parsedExprIsMatrixWriteProducer] at clean
  rcases clean with input | mwrite
  · exact candidate_sharedBlockExpression_eq_self readState currentState _ updateTurnaround
      (parsedExpr_stageInput_candidate _ input supported)
  · cases op <;> simp_all [executeParsedSharedBlockExpression]

/-- **The shared-block stage is the identity on a clean line.** -/
theorem welcomeStageClean_sharedBlockProducers_eq_self
    (readState currentState : State) (expressions : List ParsedExpr)
    (updateTurnaround : Bool)
    (clean : expressions.all welcomeStageCleanExpression = true)
    (supported : expressions.all parsedExprIsSupportedPELineProducer = true) :
    executeParsedSharedBlockProducers readState currentState expressions updateTurnaround =
      .ok currentState :=
  executeParsedSharedBlockProducerList_eq_self readState updateTurnaround expressions
    currentState (fun expression member =>
      welcomeStageCleanExpression_sharedBlock_eq_self readState currentState expression
        updateTurnaround (List.all_eq_true.mp clean expression member)
        (List.all_eq_true.mp supported expression member))

/-- **The integer-stage filter of a clean line is the identity** (the five
excluded families are all absent). -/
theorem welcomeStageClean_peFilter_eq_self (expressions : List ParsedExpr)
    (clean : expressions.all welcomeStageCleanExpression = true) :
    expressions.filter (fun expression =>
      !parsedExprIsL2BMProducer expression && !parsedExprIsMslMsrProducer expression &&
        !parsedExprIsMatrixMAUProducer expression &&
        !parsedExprIsBlockFloatProducer expression &&
        !parsedExprIsFloatReluProducer expression) = expressions := by
  apply List.filter_eq_self.mpr
  intro expression member
  obtain ⟨notL2BM, notMsl, notMatrixMAU, notBlock, notRelu, _, _⟩ :=
    welcomeStageCleanExpression_notFamilies expression
      (List.all_eq_true.mp clean expression member)
  simp [notL2BM, notMsl, notMatrixMAU, notBlock, notRelu]

/-- A clean line has no MSL/MSR row. -/
theorem welcomeStageClean_mslFilter_nil (expressions : List ParsedExpr)
    (clean : expressions.all welcomeStageCleanExpression = true) :
    expressions.filter parsedExprIsMslMsrProducer = [] :=
  List.filter_eq_nil_iff.mpr fun expression member =>
    by simpa using (welcomeStageCleanExpression_notFamilies expression
      (List.all_eq_true.mp clean expression member)).2.1

/-- A clean line has no float-relu row. -/
theorem welcomeStageClean_reluFilter_nil (expressions : List ParsedExpr)
    (clean : expressions.all welcomeStageCleanExpression = true) :
    expressions.filter parsedExprIsFloatReluProducer = [] :=
  List.filter_eq_nil_iff.mpr fun expression member =>
    by simpa using (welcomeStageCleanExpression_notFamilies expression
      (List.all_eq_true.mp clean expression member)).2.2.2.2.1

/-- A clean line has no block-float row. -/
theorem welcomeStageClean_blockFilter_nil (expressions : List ParsedExpr)
    (clean : expressions.all welcomeStageCleanExpression = true) :
    expressions.filter parsedExprIsBlockFloatProducer = [] :=
  List.filter_eq_nil_iff.mpr fun expression member =>
    by simpa using (welcomeStageCleanExpression_notFamilies expression
      (List.all_eq_true.mp clean expression member)).2.2.2.1

/-- A clean line has no matrix-MAU row. -/
theorem welcomeStageClean_matrixMAUFilter_nil (expressions : List ParsedExpr)
    (clean : expressions.all welcomeStageCleanExpression = true) :
    expressions.filter parsedExprIsMatrixMAUProducer = [] :=
  List.filter_eq_nil_iff.mpr fun expression member =>
    by simpa using (welcomeStageCleanExpression_notFamilies expression
      (List.all_eq_true.mp clean expression member)).2.2.1

/-- A clean line has no L1BM-to-PE row. -/
theorem welcomeStageClean_l1ToPEFilter_nil (expressions : List ParsedExpr)
    (clean : expressions.all welcomeStageCleanExpression = true) :
    expressions.filter parsedExprIsL1ToPEProducer = [] :=
  List.filter_eq_nil_iff.mpr fun expression member =>
    by simpa using (welcomeStageCleanExpression_notFamilies expression
      (List.all_eq_true.mp clean expression member)).2.2.2.2.2.1

/-- A clean line has no float-MAU row. -/
theorem welcomeStageClean_floatFilter_nil (expressions : List ParsedExpr)
    (clean : expressions.all welcomeStageCleanExpression = true) :
    expressions.filter parsedExprIsSupportedFloatMAUProducer = [] :=
  List.filter_eq_nil_iff.mpr fun expression member =>
    by simpa using (welcomeStageCleanExpression_notFamilies expression
      (List.all_eq_true.mp clean expression member)).2.2.2.2.2.2

/-- **The clean-line assembly.**  If every row of a successful `.pe` line is an
integer/matrix-read stage input or a `.matrixWrite` row, then the whole line's
PE 0 register file is the commit of the integer stage's prepared write list: the
four middle stages, the shared-block stage and the L1BM-to-PE stage are all the
identity, and the matrix-write stage preserves every PE register file. -/
theorem executeIntegerProducerInstructionLine_pe_commit_of_clean
    (expressions : List NormalizedExpr) (state next : State)
    (accepted : checkParsedTopLine (InstructionLine.pe expressions).toParsed = true)
    (waits : (expressions.map NormalizedExpr.toParsed).any
      (parsedExprWaitPending state) = false)
    (unsupported : (expressions.map NormalizedExpr.toParsed).any
      parsedExprIsUnsupportedRustAlu = false)
    (supported : (expressions.map NormalizedExpr.toParsed).all
      parsedExprIsSupportedPELineProducer = true)
    (clean : (expressions.map NormalizedExpr.toParsed).all
      welcomeStageCleanExpression = true)
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
  have filterEq := welcomeStageClean_peFilter_eq_self
    (expressions.map NormalizedExpr.toParsed) clean
  rw [filterEq] at walkExecuted
  obtain ⟨writes, slots, bars, prep, committed⟩ :=
    executeIntegerProducerLineAtPEs_prepared (expressions.map NormalizedExpr.toParsed)
      (List.finRange 4096) state nextPEs
      (welcomeStageClean_floatFilter_nil _ clean) walkExecuted
      (List.nodup_finRange 4096) welcomePE (List.mem_finRange welcomePE)
  -- the MSL/MSR stage is the identity
  have mslId : executeParsedMslMsrProducers state nextPEs
      (expressions.map NormalizedExpr.toParsed)
      (expressions.any (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed))
      (expressions.any (parsedExprHasSingleLineWriteMask ∘ NormalizedExpr.toParsed)) =
      .ok nextPEs :=
    executeParsedMslMsrProducers_eq_self state nextPEs _ _ _
      (welcomeStageClean_mslFilter_nil _ clean)
  have nextMslEq : nextMsl = nextPEs := by
    rw [mslId] at mslExecuted
    exact (StepResult.ok.inj mslExecuted).symm
  -- the float-relu stage is the identity
  have reluId : executeParsedFloatReluProducers state nextPEs
      (expressions.map NormalizedExpr.toParsed)
      (expressions.any (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed))
      (expressions.any (parsedExprHasSingleLineWriteMask ∘ NormalizedExpr.toParsed)) =
      .ok nextPEs :=
    executeParsedFloatReluProducers_eq_self state nextPEs _ _ _
      (welcomeStageClean_reluFilter_nil _ clean)
  have nextReluEq : nextRelu = nextPEs := by
    rw [nextMslEq, reluId] at reluExecuted
    exact (StepResult.ok.inj reluExecuted).symm
  -- the block-float stage is the identity
  have blockId : executeParsedBlockFloatProducer state nextPEs
      (expressions.map NormalizedExpr.toParsed)
      (expressions.any (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed))
      (expressions.any (parsedExprHasSingleLineWriteMask ∘ NormalizedExpr.toParsed)) =
      .ok nextPEs :=
    executeParsedBlockFloatProducer_eq_self state nextPEs _ _ _
      (welcomeStageClean_blockFilter_nil _ clean)
  have nextBlockFloatEq : nextBlockFloat = nextPEs := by
    rw [nextReluEq, blockId] at blockExecuted
    exact (StepResult.ok.inj blockExecuted).symm
  -- the matrix-MAU/write stage preserves every PE register file
  have matrixFrame : ∀ pe : PEId,
      afterMatrix.peRegisters pe = nextBlockFloat.peRegisters pe :=
    executeParsedMatrixMAUAndWrites_peRegisters_frame_of_noMatrixMAU state nextBlockFloat
      afterMatrix (expressions.map NormalizedExpr.toParsed)
      (expressions.any (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed))
      (expressions.any (parsedExprHasSingleLineWriteMask ∘ NormalizedExpr.toParsed))
      (welcomeStageClean_matrixMAUFilter_nil _ clean) matrixExecuted
  -- the shared-block stage preserves every PE register file
  have sharedFrame : nextShared.peRegisters = afterMatrix.peRegisters :=
    executeParsedSharedBlockProducers_peRegisters state afterMatrix nextShared
      (expressions.map NormalizedExpr.toParsed)
      (!(expressions.any (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed)))
      sharedExecuted
  -- the L1BM-to-PE stage is the identity
  have l1Id : executeParsedL1ToPEProducers state nextShared
      (expressions.map NormalizedExpr.toParsed)
      (expressions.any (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed))
      (expressions.any (parsedExprHasSingleLineWriteMask ∘ NormalizedExpr.toParsed))
      (parsedL1ToPEPrecedesOMRWriter (expressions.map NormalizedExpr.toParsed)) =
      .ok nextShared :=
    executeParsedL1ToPEProducers_eq_self state nextShared _ _ _ _
      (welcomeStageClean_l1ToPEFilter_nil _ clean)
  have nextBroadcastEq : nextBroadcast = nextShared := by
    rw [l1Id] at l1Executed
    exact (StepResult.ok.inj l1Executed).symm
  refine ⟨writes, slots, bars, prep, ?_⟩
  rw [nextEq, nextBroadcastEq]
  simp only [sharedFrame, matrixFrame welcomePE, nextBlockFloatEq, committed]

/-- The wait-tag pending test only reads the completed-tag table, so it is the
same at the initial state of every input. -/
theorem parsedExprWaitPending_welcomeInitialState
    (input : ProofsLean.MNCore.PlusOne.Words) (expression : ParsedExpr) :
    parsedExprWaitPending (welcomeInitialState input) expression =
      parsedExprWaitPending (welcomeInitialState welcomeZeroWords) expression := rfl

/-- **F1 for the clean class, at the level of the sealed machine.**  For an
unrefuted `.pe` line whose rows are all integer/matrix-read stage inputs or
`.matrixWrite` rows, the state after the line is the commit of the integer
stage's prepared writes on the initial register file. -/
theorem welcomePE_line_commit_of_clean
    (expressions : List NormalizedExpr) (input : ProofsLean.MNCore.PlusOne.Words)
    (next : State) (unrefuted : WelcomePEUnrefuted expressions)
    (clean : (expressions.map NormalizedExpr.toParsed).all
      welcomeStageCleanExpression = true)
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
  refine executeIntegerProducerInstructionLine_pe_commit_of_clean expressions
    (welcomeInitialState input) next unrefuted.1.1 ?_ unrefuted.1.2.2.1 unrefuted.1.2.2.2
    clean executed
  have waits := unrefuted.1.2.1
  have same : (expressions.map NormalizedExpr.toParsed).any
      (parsedExprWaitPending (welcomeInitialState input)) =
      (expressions.map NormalizedExpr.toParsed).any
        (parsedExprWaitPending (welcomeInitialState welcomeZeroWords)) := by
    apply List.any_congr rfl
    intro expression
    exact parsedExprWaitPending_welcomeInitialState input expression
  exact same ▸ waits

/-! ## 4. The general assembly and its six residual obligations

The clean class of §3 covers every line whose non-plain rows are `.matrixWrite`
rows.  A general `.pe` line also runs the four middle stages and the L1BM-to-PE
stage, and each of those may contribute prepared masked writes to PE 0's register
file.  The assembly below composes whatever write lists those stages produce, so
the line-level statement holds as soon as **each stage is a commit of a prepared
write list**.  The five `Prop`s below are exactly those per-stage statements;
nothing assumes them.

For reference the already-proved cases are:

* the integer stage with no float-MAU row
  (`executeIntegerProducerLineAtPEs_prepared` — an explicit write list and its
  `welcomeIntegerPrep`);
* the matrix-MAU/write stage with no matrix-MAU row
  (`executeParsedMatrixMAUAndWrites_peRegisters_frame_of_noMatrixMAU` — the empty
  list);
* the shared-block stage, unconditionally
  (`executeParsedSharedBlockProducers_peRegisters` — the empty list);
* every stage with an empty producer filter (§1 — the empty list). -/

/-- **Residual obligation (integer stage, float-MAU row present).**  A successful
per-PE integer-stage step commits a prepared write list at the visited PE even
when the line carries a float-MAU producer.  The float-MAU writes happen inside
this stage (`executeParsedFloatMAUsAtPE`), which is why
`executeIntegerProducerLineAtPECore_peRegisters_commit` needs
`expressions.filter parsedExprIsSupportedFloatMAUProducer = []`. -/
def WelcomePEIntegerFloatStageCommit : Prop :=
  ∀ (expressions : List ParsedExpr) (state next : State) (pe : PEId),
    executeIntegerProducerLineAtPECore expressions state pe = .ok next →
    ∃ writes, next.peRegisters pe =
      commitParsedMaskedWrites (state.peRegisters pe) writes

/-- **Residual obligation (integer stage, walk level).**  The per-PE walk of the
integer stage commits a prepared write list at every visited PE.  It is derived
below from `WelcomePEIntegerFloatStageCommit`. -/
def WelcomePEIntegerStageCommit : Prop :=
  ∀ (expressions : List ParsedExpr) (pes : List PEId) (state next : State),
    pes.Nodup → welcomePE ∈ pes →
      executeIntegerProducerLineAtPEs expressions pes state = .ok next →
    ∃ writes, next.peRegisters welcomePE =
      commitParsedMaskedWrites (state.peRegisters welcomePE) writes

/-- **Residual obligation (MSL/MSR stage).** -/
def WelcomePEMslMsrStageCommit : Prop :=
  ∀ (readState currentState next : State) (expressions : List ParsedExpr)
    (noForward hasSingleLineMask : Bool),
    executeParsedMslMsrProducers readState currentState expressions noForward
      hasSingleLineMask = .ok next →
    ∃ writes, next.peRegisters welcomePE =
      commitParsedMaskedWrites (currentState.peRegisters welcomePE) writes

/-- **Residual obligation (float-relu stage).** -/
def WelcomePEFloatReluStageCommit : Prop :=
  ∀ (readState currentState next : State) (expressions : List ParsedExpr)
    (noForward hasSingleLineMask : Bool),
    executeParsedFloatReluProducers readState currentState expressions noForward
      hasSingleLineMask = .ok next →
    ∃ writes, next.peRegisters welcomePE =
      commitParsedMaskedWrites (currentState.peRegisters welcomePE) writes

/-- **Residual obligation (block-float stage).** -/
def WelcomePEBlockFloatStageCommit : Prop :=
  ∀ (readState currentState next : State) (expressions : List ParsedExpr)
    (noForward hasSingleLineMask : Bool),
    executeParsedBlockFloatProducer readState currentState expressions noForward
      hasSingleLineMask = .ok next →
    ∃ writes, next.peRegisters welcomePE =
      commitParsedMaskedWrites (currentState.peRegisters welcomePE) writes

/-- **Residual obligation (matrix-MAU/write stage with a matrix-MAU row).** -/
def WelcomePEMatrixMAUStageCommit : Prop :=
  ∀ (readState currentState next : State) (expressions : List ParsedExpr)
    (noForward hasSingleLineMask : Bool),
    executeParsedMatrixMAUAndWrites readState currentState expressions noForward
      hasSingleLineMask = .ok next →
    ∃ writes, next.peRegisters welcomePE =
      commitParsedMaskedWrites (currentState.peRegisters welcomePE) writes

/-- **Residual obligation (L1BM-to-PE stage).**  The broadcast writes are masked
stores of the broadcast bus at the destination operands' banks; each PE it
visits ends as the commit of those stores on its incoming register file. -/
def WelcomePEL1ToPEStageCommit : Prop :=
  ∀ (readState currentState next : State) (expressions : List ParsedExpr)
    (noForward hasSingleLineMask usePreIssueMask : Bool),
    executeParsedL1ToPEProducers readState currentState expressions noForward
      hasSingleLineMask usePreIssueMask = .ok next →
    ∃ writes, next.peRegisters welcomePE =
      commitParsedMaskedWrites (currentState.peRegisters welcomePE) writes

/-- **The six per-stage commit obligations, bundled.** -/
def WelcomePEStageCommitForm : Prop :=
  WelcomePEIntegerStageCommit ∧ WelcomePEMslMsrStageCommit ∧
    WelcomePEFloatReluStageCommit ∧ WelcomePEBlockFloatStageCommit ∧
      WelcomePEMatrixMAUStageCommit ∧ WelcomePEL1ToPEStageCommit

/-! ### Deriving the walk-level integer obligation from the per-PE one -/

theorem executeIntegerProducerLineAtPE_pe_commit_of_core
    (core : ∀ (expressions : List ParsedExpr) (state next : State) (pe : PEId),
      executeIntegerProducerLineAtPECore expressions state pe = .ok next →
      ∃ writes, next.peRegisters pe =
        commitParsedMaskedWrites (state.peRegisters pe) writes)
    (expressions : List ParsedExpr) (state next : State) (pe : PEId)
    (executed : executeIntegerProducerLineAtPE expressions state pe = .ok next) :
    ∃ writes, next.peRegisters pe =
      commitParsedMaskedWrites (state.peRegisters pe) writes := by
  unfold executeIntegerProducerLineAtPE at executed
  split at executed
  · simp at executed
  · exact core expressions state next pe executed

theorem executeIntegerProducerLineAtPEs_pe_commit_of_core
    (core : ∀ (expressions : List ParsedExpr) (state next : State) (pe : PEId),
      executeIntegerProducerLineAtPECore expressions state pe = .ok next →
      ∃ writes, next.peRegisters pe =
        commitParsedMaskedWrites (state.peRegisters pe) writes)
    (expressions : List ParsedExpr) (pes : List PEId) (state next : State)
    (executed : executeIntegerProducerLineAtPEs expressions pes state = .ok next)
    (nodup : pes.Nodup) (p : PEId) (mem : p ∈ pes) :
    ∃ writes, next.peRegisters p =
      commitParsedMaskedWrites (state.peRegisters p) writes := by
  induction pes generalizing state with
  | nil => simp at mem
  | cons pe rest ih =>
      obtain ⟨peNotRest, restNodup⟩ := List.nodup_cons.mp nodup
      simp only [executeIntegerProducerLineAtPEs] at executed
      split at executed
      · simp at executed
      · simp at executed
      · rename_i middle headExecuted
        by_cases same : p = pe
        · subst p
          obtain ⟨writes, headCommit⟩ :=
            executeIntegerProducerLineAtPE_pe_commit_of_core core expressions state middle pe
              headExecuted
          have tailFrame := executeIntegerProducerLineAtPEs_peRegisters_not_mem expressions rest
            middle next executed
            (fun pe other s n he different =>
              executeIntegerProducerLineAtPE_peRegisters_other expressions s n pe other
                different he)
            pe peNotRest
          refine ⟨writes, ?_⟩
          rw [tailFrame, headCommit]
        · have pMem : p ∈ rest := by
            rcases List.mem_cons.mp mem with h | h
            · exact False.elim (same h)
            · exact h
          obtain ⟨writes, tailCommit⟩ := ih middle executed restNodup pMem
          have headFrame := executeIntegerProducerLineAtPE_peRegisters_other expressions state
            middle pe p same headExecuted
          exact ⟨writes, by rw [tailCommit, headFrame]⟩

/-- **The per-PE integer obligation gives the walk-level one.** -/
theorem welcomePEIntegerStageCommit_of_float
    (float : WelcomePEIntegerFloatStageCommit) : WelcomePEIntegerStageCommit :=
  fun expressions pes state next nodup mem executed =>
    executeIntegerProducerLineAtPEs_pe_commit_of_core float expressions pes state next
      executed nodup welcomePE mem

/-! ### The general line-level assembly -/

/-- **F1: the line-level stage assembly.**  Given the six per-stage commit
obligations, a successful `.pe` line leaves PE 0's register file equal to the
commit of the concatenation of the stage write lists:
integer ++ MSL/MSR ++ float-relu ++ block-float ++ matrix-MAU/write ++
L1BM-to-PE.  The shared-block stage contributes nothing because it preserves
every PE register file unconditionally. -/
theorem executeIntegerProducerInstructionLine_pe_stage_commit
    (stages : WelcomePEStageCommitForm)
    (expressions : List NormalizedExpr) (state next : State)
    (accepted : checkParsedTopLine (InstructionLine.pe expressions).toParsed = true)
    (waits : (expressions.map NormalizedExpr.toParsed).any
      (parsedExprWaitPending state) = false)
    (unsupported : (expressions.map NormalizedExpr.toParsed).any
      parsedExprIsUnsupportedRustAlu = false)
    (supported : (expressions.map NormalizedExpr.toParsed).all
      parsedExprIsSupportedPELineProducer = true)
    (step : executeIntegerProducerInstructionLine (.pe expressions) state = .ok next) :
    ∃ intWrites mslWrites reluWrites blockWrites matrixWrites l1Writes,
      next.peRegisters welcomePE =
        commitParsedMaskedWrites (state.peRegisters welcomePE)
          (intWrites ++ mslWrites ++ reluWrites ++ blockWrites ++ matrixWrites ++
            l1Writes) := by
  obtain ⟨integerCommit, mslCommit, reluCommit, blockCommit, matrixCommit, l1Commit⟩ :=
    stages
  obtain ⟨nextPEs, nextMsl, nextRelu, nextBlockFloat, afterMatrix, nextShared,
    nextBroadcast, walkExecuted, mslExecuted, reluExecuted, blockExecuted, matrixExecuted,
    sharedExecuted, l1Executed, nextEq⟩ :=
    executeIntegerProducerInstructionLine_pe_stages_exists expressions state next accepted
      waits unsupported supported step
  obtain ⟨intWrites, intCommit⟩ :=
    integerCommit ((expressions.map NormalizedExpr.toParsed).filter (fun expression =>
      !parsedExprIsL2BMProducer expression && !parsedExprIsMslMsrProducer expression &&
        !parsedExprIsMatrixMAUProducer expression &&
        !parsedExprIsBlockFloatProducer expression &&
        !parsedExprIsFloatReluProducer expression))
      (List.finRange 4096) state nextPEs (List.nodup_finRange 4096)
      (List.mem_finRange welcomePE) walkExecuted
  obtain ⟨mslWrites, mslCommitEq⟩ :=
    mslCommit state nextPEs nextMsl (expressions.map NormalizedExpr.toParsed)
      (expressions.any (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed))
      (expressions.any (parsedExprHasSingleLineWriteMask ∘ NormalizedExpr.toParsed))
      mslExecuted
  obtain ⟨reluWrites, reluCommitEq⟩ :=
    reluCommit state nextMsl nextRelu (expressions.map NormalizedExpr.toParsed)
      (expressions.any (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed))
      (expressions.any (parsedExprHasSingleLineWriteMask ∘ NormalizedExpr.toParsed))
      reluExecuted
  obtain ⟨blockWrites, blockCommitEq⟩ :=
    blockCommit state nextRelu nextBlockFloat (expressions.map NormalizedExpr.toParsed)
      (expressions.any (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed))
      (expressions.any (parsedExprHasSingleLineWriteMask ∘ NormalizedExpr.toParsed))
      blockExecuted
  obtain ⟨matrixWrites, matrixCommitEq⟩ :=
    matrixCommit state nextBlockFloat afterMatrix (expressions.map NormalizedExpr.toParsed)
      (expressions.any (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed))
      (expressions.any (parsedExprHasSingleLineWriteMask ∘ NormalizedExpr.toParsed))
      matrixExecuted
  obtain ⟨l1Writes, l1CommitEq⟩ :=
    l1Commit state nextShared nextBroadcast (expressions.map NormalizedExpr.toParsed)
      (expressions.any (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed))
      (expressions.any (parsedExprHasSingleLineWriteMask ∘ NormalizedExpr.toParsed))
      (parsedL1ToPEPrecedesOMRWriter (expressions.map NormalizedExpr.toParsed))
      l1Executed
  have sharedFrame : nextShared.peRegisters welcomePE = afterMatrix.peRegisters welcomePE :=
    congrFun (executeParsedSharedBlockProducers_peRegisters state afterMatrix nextShared
      (expressions.map NormalizedExpr.toParsed)
      (!(expressions.any (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed)))
      sharedExecuted) welcomePE
  have peNext : next.peRegisters welcomePE = nextBroadcast.peRegisters welcomePE := by
    rw [nextEq]
  refine ⟨intWrites, mslWrites, reluWrites, blockWrites, matrixWrites, l1Writes, ?_⟩
  rw [peNext, l1CommitEq, sharedFrame, matrixCommitEq, blockCommitEq, reluCommitEq,
    mslCommitEq, intCommit]
  simp only [← commitParsedMaskedWrites_append]

/-! ## 5. The `.lm1` part of the concatenation

The value argument only looks at PE 0's `lm1` bank.  Two algebraic facts make the
stage concatenation transparent there:

* the `.lm1` bank of a commit is the commit of the `.lm1` writes alone
  (`commitParsedMaskedWrites_lm1_filter`);
* a block of writes with no `.lm1` write can be dropped from the concatenation
  without changing the `.lm1` bank
  (`commitParsedMaskedWrites_lm1_concat_of_only`).

Hence the `.lm1` bank after the line is the `.lm1` bank of the unique `.lm1`
writer's own write list, provided every other stage's list avoids `.lm1` — which
is the residual provenance obligation `WelcomePEIntegerStageLm1Provenance` and
its stage analogues. -/

theorem isLm1Write_false_bank (write : PreparedParsedMaskedWrite)
    (notLm1 : ProofsLean.MNCore.PreparedParsedMaskedWrite.isLm1Write write = false) :
    ∀ access : DirectMemoryAccess, write.destination = some access →
      access.bank ≠ PEMemory.Bank.lm1 := by
  intro access haccess
  rcases write with ⟨destination, update, data, selection⟩
  cases destination with
  | none => simp at haccess
  | some found =>
      obtain rfl := Option.some.inj haccess
      simpa [ProofsLean.MNCore.PreparedParsedMaskedWrite.isLm1Write,
        beq_eq_false_iff_ne] using notLm1

theorem isLm1Write_true_bank (write : PreparedParsedMaskedWrite)
    (yesLm1 : ProofsLean.MNCore.PreparedParsedMaskedWrite.isLm1Write write = true) :
    ∃ access : DirectMemoryAccess, write.destination = some access ∧
      access.bank = PEMemory.Bank.lm1 := by
  rcases write with ⟨destination, update, data, selection⟩
  cases destination with
  | none =>
      simp [ProofsLean.MNCore.PreparedParsedMaskedWrite.isLm1Write] at yesLm1
  | some access =>
      exact ⟨access, rfl, by
        simpa [ProofsLean.MNCore.PreparedParsedMaskedWrite.isLm1Write,
          beq_iff_eq] using yesLm1⟩

/-- **The `.lm1` bank of a commit is the commit of its `.lm1` writes.** -/
theorem commitParsedMaskedWrites_lm1_filter (files : IntegerRegisterFiles)
    (writes : List PreparedParsedMaskedWrite) :
    (commitParsedMaskedWrites files writes).lm1 =
      (commitParsedMaskedWrites files
        (writes.filter ProofsLean.MNCore.PreparedParsedMaskedWrite.isLm1Write)).lm1 := by
  induction writes generalizing files with
  | nil => rfl
  | cons write rest ih =>
      rw [commitParsedMaskedWrites_cons]
      by_cases lm1 : ProofsLean.MNCore.PreparedParsedMaskedWrite.isLm1Write write = true
      · rw [List.filter_cons_of_pos lm1, commitParsedMaskedWrites_cons]
        exact ih _
      · have notLm1 :
            ProofsLean.MNCore.PreparedParsedMaskedWrite.isLm1Write write = false := by
          cases h : ProofsLean.MNCore.PreparedParsedMaskedWrite.isLm1Write write <;> simp_all
        rw [List.filter_cons_of_neg (by simpa using notLm1)]
        rw [commitParsedMaskedWrites_lm1_congr (welcomeCommitStep files write) files
          rest rest (welcomeCommitStep_lm1_of_ne files write
            (isLm1Write_false_bank write notLm1)) rfl]
        exact ih files

/-- **A block of writes with no `.lm1` write does not change the `.lm1` bank.** -/
theorem commitParsedMaskedWrites_lm1_concat_of_only (files : IntegerRegisterFiles)
    (intWrites rest : List PreparedParsedMaskedWrite)
    (only : ∀ write ∈ rest,
      ProofsLean.MNCore.PreparedParsedMaskedWrite.isLm1Write write = false) :
    (commitParsedMaskedWrites files (intWrites ++ rest)).lm1 =
      (commitParsedMaskedWrites files intWrites).lm1 := by
  rw [commitParsedMaskedWrites_append]
  exact commitParsedMaskedWrites_lm1_of_no_lm1 rest
    (commitParsedMaskedWrites files intWrites)
    (fun write member access haccess =>
      isLm1Write_false_bank write (only write member) access haccess)

/-! ## 6. The `.lm1` provenance still missing

The single fact that turns the assembly into "the line's `.lm1` bank is the
unique writer's" is that a prepared write list carries an `.lm1` destination
only when the row it was prepared from has an `.lm1` destination operand.
`welcomeLm1Writer_unique` then says at most one row can be such a writer. -/

/-- The row-level "no `.lm1` destination operand" test: every direct-memory
destination operand of the row lowers to a bank other than `.lm1`, at every
cycle. -/
def WelcomeRowHasNoLm1Destination (expression : ParsedExpr) : Prop :=
  ∀ destination ∈ expression.destinations,
    ∀ (bank : PEMemory.Bank) (width : PEMemory.Width),
      ParsedOperand.directDestinationBankWidth? destination = some (bank, width) →
        bank ≠ PEMemory.Bank.lm1

/-- **Residual obligation (integer-stage `.lm1` provenance).**  If none of the
rows the integer stage prepares has an `.lm1` destination operand, the prepared
write list has no `.lm1` write.  This is the positive companion of the
integer-stage provenance gap: it is the list-level statement that
`prepareParsedIntegerMatrixReadLineExpressions` only writes the banks its rows
name. -/
def WelcomePEIntegerStageLm1Provenance : Prop :=
  ∀ (expressions : List ParsedExpr) (state : State) (pe : PEId)
    (writes : List PreparedParsedMaskedWrite) (slots : ProofsLean.MNCore.Forwarding.Slots)
    (bars : List (Bool × BitVec 12)),
    welcomeIntegerPrep state pe expressions = .ok (writes, slots, bars) →
    (∀ expression ∈ expressions.filter parsedExprIsIntegerMatrixReadStageInput,
      WelcomeRowHasNoLm1Destination expression) →
    ∀ write ∈ writes,
      ProofsLean.MNCore.PreparedParsedMaskedWrite.isLm1Write write = false

/-- **Residual obligation (middle-stage `.lm1` frames).**  The four middle stages
and the L1BM-to-PE stage preserve PE 0's `.lm1` bank when every row avoids bank
`.lm1`.  With the stage commit forms of §4 these also give the corresponding
stage write lists with no `.lm1` write. -/
def WelcomePEStageLm1Frame : Prop :=
  (∀ (readState currentState next : State) (expressions : List ParsedExpr)
      (noForward hasSingleLineMask : Bool),
      (∀ expression ∈ expressions, WelcomeRowHasNoLm1Destination expression) →
      executeParsedMslMsrProducers readState currentState expressions noForward
        hasSingleLineMask = .ok next →
      (next.peRegisters welcomePE).lm1 = (currentState.peRegisters welcomePE).lm1) ∧
  (∀ (readState currentState next : State) (expressions : List ParsedExpr)
      (noForward hasSingleLineMask : Bool),
      (∀ expression ∈ expressions, WelcomeRowHasNoLm1Destination expression) →
      executeParsedFloatReluProducers readState currentState expressions noForward
        hasSingleLineMask = .ok next →
      (next.peRegisters welcomePE).lm1 = (currentState.peRegisters welcomePE).lm1) ∧
  (∀ (readState currentState next : State) (expressions : List ParsedExpr)
      (noForward hasSingleLineMask : Bool),
      (∀ expression ∈ expressions, WelcomeRowHasNoLm1Destination expression) →
      executeParsedBlockFloatProducer readState currentState expressions noForward
        hasSingleLineMask = .ok next →
      (next.peRegisters welcomePE).lm1 = (currentState.peRegisters welcomePE).lm1) ∧
  (∀ (readState currentState next : State) (expressions : List ParsedExpr)
      (noForward hasSingleLineMask : Bool),
      (∀ expression ∈ expressions, WelcomeRowHasNoLm1Destination expression) →
      executeParsedMatrixMAUAndWrites readState currentState expressions noForward
        hasSingleLineMask = .ok next →
      (next.peRegisters welcomePE).lm1 = (currentState.peRegisters welcomePE).lm1) ∧
  (∀ (readState currentState next : State) (expressions : List ParsedExpr)
      (noForward hasSingleLineMask usePreIssueMask : Bool),
      (∀ expression ∈ expressions, WelcomeRowHasNoLm1Destination expression) →
      executeParsedL1ToPEProducers readState currentState expressions noForward
        hasSingleLineMask usePreIssueMask = .ok next →
      (next.peRegisters welcomePE).lm1 = (currentState.peRegisters welcomePE).lm1)

/-- The shared-block stage is *unconditionally* `.lm1`-preserving: it preserves
every PE register file. -/
theorem executeParsedSharedBlockProducers_lm1_frame
    (readState currentState next : State) (expressions : List ParsedExpr)
    (updateTurnaround : Bool)
    (executed : executeParsedSharedBlockProducers readState currentState expressions
      updateTurnaround = .ok next) :
    (next.peRegisters welcomePE).lm1 = (currentState.peRegisters welcomePE).lm1 := by
  rw [executeParsedSharedBlockProducers_peRegisters readState currentState next expressions
    updateTurnaround executed]

/-- **Residual obligation (integer-stage `.lm1` frame).**  The integer stage
leaves PE 0's `.lm1` bank unchanged when no row it prepares has an `.lm1`
destination operand.  This is the commit-level counterpart of
`WelcomePEIntegerStageLm1Provenance` for lines that also carry float-MAU rows
(whose writes happen inside this stage). -/
def WelcomePEIntegerStageLm1Frame : Prop :=
  ∀ (expressions : List ParsedExpr) (pes : List PEId) (state next : State),
    pes.Nodup → welcomePE ∈ pes →
    (∀ expression ∈ expressions.filter parsedExprIsIntegerMatrixReadStageInput,
      WelcomeRowHasNoLm1Destination expression) →
    executeIntegerProducerLineAtPEs expressions pes state = .ok next →
    (next.peRegisters welcomePE).lm1 = (state.peRegisters welcomePE).lm1

/-- **The line-level `.lm1` frame.**  If no row of the line has an `.lm1`
destination operand, a successful `.pe` line leaves PE 0's `.lm1` bank exactly as
it was.  This is the form in which the six family obligations consume the
assembly: a line that never names bank `.lm1` cannot produce the observed
output. -/
theorem executeIntegerProducerInstructionLine_pe_lm1_frame
    (integerFrame : WelcomePEIntegerStageLm1Frame)
    (stageFrame : WelcomePEStageLm1Frame)
    (expressions : List NormalizedExpr) (state next : State)
    (accepted : checkParsedTopLine (InstructionLine.pe expressions).toParsed = true)
    (waits : (expressions.map NormalizedExpr.toParsed).any
      (parsedExprWaitPending state) = false)
    (unsupported : (expressions.map NormalizedExpr.toParsed).any
      parsedExprIsUnsupportedRustAlu = false)
    (supported : (expressions.map NormalizedExpr.toParsed).all
      parsedExprIsSupportedPELineProducer = true)
    (noLm1 : ∀ expression ∈ expressions.map NormalizedExpr.toParsed,
      WelcomeRowHasNoLm1Destination expression)
    (step : executeIntegerProducerInstructionLine (.pe expressions) state = .ok next) :
    (next.peRegisters welcomePE).lm1 = (state.peRegisters welcomePE).lm1 := by
  obtain ⟨mslF, reluF, blockF, matrixF, l1F⟩ := stageFrame
  obtain ⟨nextPEs, nextMsl, nextRelu, nextBlockFloat, afterMatrix, nextShared,
    nextBroadcast, walkExecuted, mslExecuted, reluExecuted, blockExecuted, matrixExecuted,
    sharedExecuted, l1Executed, nextEq⟩ :=
    executeIntegerProducerInstructionLine_pe_stages_exists expressions state next accepted
      waits unsupported supported step
  have intFrame := integerFrame _ (List.finRange 4096) state nextPEs
    (List.nodup_finRange 4096) (List.mem_finRange welcomePE)
    (fun expression member => noLm1 expression (List.mem_filter.mp
      (List.mem_filter.mp member).1).1) walkExecuted
  have mslFrame := mslF state nextPEs nextMsl _ _ _ noLm1 mslExecuted
  have reluFrame := reluF state nextMsl nextRelu _ _ _ noLm1 reluExecuted
  have blockFrame := blockF state nextRelu nextBlockFloat _ _ _ noLm1 blockExecuted
  have matrixFrame := matrixF state nextBlockFloat afterMatrix _ _ _ noLm1 matrixExecuted
  have sharedFrame := executeParsedSharedBlockProducers_lm1_frame state afterMatrix
    nextShared _ _ sharedExecuted
  have l1Frame := l1F state nextShared nextBroadcast _ _ _ _ noLm1 l1Executed
  have peNext : next.peRegisters welcomePE = nextBroadcast.peRegisters welcomePE := by
    rw [nextEq]
  rw [peNext, l1Frame, sharedFrame, matrixFrame, blockFrame, reluFrame, mslFrame, intFrame]

/-! ## 7. The sealed-machine forms

`welcomeSealedMachine.step` is `executeNormalizedLine` with non-`.ok` results
mapped to `none`, so the line equations above lift to it directly. -/

/-- **F1 at the sealed machine (general form).**  Given the six per-stage commit
obligations, the state after an unrefuted `.pe` line is the commit of the
concatenation of the stage write lists on the *initial* register file. -/
theorem welcomePE_line_stage_commit
    (stages : WelcomePEStageCommitForm)
    (expressions : List NormalizedExpr) (input : ProofsLean.MNCore.PlusOne.Words)
    (next : State) (unrefuted : WelcomePEUnrefuted expressions)
    (step : welcomeSealedMachine.step (.pe expressions)
      (welcomeInitialState input) = some next) :
    ∃ intWrites mslWrites reluWrites blockWrites matrixWrites l1Writes,
      next.peRegisters welcomePE =
        commitParsedMaskedWrites
          ((welcomeInitialState input).peRegisters welcomePE)
          (intWrites ++ mslWrites ++ reluWrites ++ blockWrites ++ matrixWrites ++
            l1Writes) := by
  have executed := welcomeSealed_step_ok step
  simp only [executeNormalizedLine, NormalizedLine.toInstruction?,
    Issue.InstructionLine.toNormalizedLine] at executed
  refine executeIntegerProducerInstructionLine_pe_stage_commit stages expressions
    (welcomeInitialState input) next unrefuted.1.1 ?_ unrefuted.1.2.2.1 unrefuted.1.2.2.2
    executed
  have waits := unrefuted.1.2.1
  have same : (expressions.map NormalizedExpr.toParsed).any
      (parsedExprWaitPending (welcomeInitialState input)) =
      (expressions.map NormalizedExpr.toParsed).any
        (parsedExprWaitPending (welcomeInitialState welcomeZeroWords)) := by
    apply List.any_congr rfl
    intro expression
    exact parsedExprWaitPending_welcomeInitialState input expression
  exact same ▸ waits

/-- **The line-level `.lm1` frame at the sealed machine.**  A line none of whose
rows names bank `.lm1` leaves PE 0's `.lm1` bank unchanged, at every input. -/
theorem welcomePE_line_lm1_frame
    (integerFrame : WelcomePEIntegerStageLm1Frame)
    (stageFrame : WelcomePEStageLm1Frame)
    (expressions : List NormalizedExpr) (input : ProofsLean.MNCore.PlusOne.Words)
    (next : State) (unrefuted : WelcomePEUnrefuted expressions)
    (noLm1 : ∀ expression ∈ expressions.map NormalizedExpr.toParsed,
      WelcomeRowHasNoLm1Destination expression)
    (step : welcomeSealedMachine.step (.pe expressions)
      (welcomeInitialState input) = some next) :
    (next.peRegisters welcomePE).lm1 =
      ((welcomeInitialState input).peRegisters welcomePE).lm1 := by
  have executed := welcomeSealed_step_ok step
  simp only [executeNormalizedLine, NormalizedLine.toInstruction?,
    Issue.InstructionLine.toNormalizedLine] at executed
  refine executeIntegerProducerInstructionLine_pe_lm1_frame integerFrame stageFrame
    expressions (welcomeInitialState input) next unrefuted.1.1 ?_ unrefuted.1.2.2.1
    unrefuted.1.2.2.2 noLm1 executed
  have waits := unrefuted.1.2.1
  have same : (expressions.map NormalizedExpr.toParsed).any
      (parsedExprWaitPending (welcomeInitialState input)) =
      (expressions.map NormalizedExpr.toParsed).any
        (parsedExprWaitPending (welcomeInitialState welcomeZeroWords)) := by
    apply List.any_congr rfl
    intro expression
    exact parsedExprWaitPending_welcomeInitialState input expression
  exact same ▸ waits

/-- **The `.lm1`-free class is refuted.**  An unrefuted line that never names
bank `.lm1` cannot produce the required output: every observed word keeps its
initial value `0`, while the specification demands `1` on the all-zero input.
This is the value argument's use of the assembly, conditional only on the two
`.lm1` frames. -/
theorem welcomePE_not_correct_of_noLm1Destination
    (integerFrame : WelcomePEIntegerStageLm1Frame)
    (stageFrame : WelcomePEStageLm1Frame)
    (expressions : List NormalizedExpr)
    (unrefuted : WelcomePEUnrefuted expressions)
    (noLm1 : ∀ expression ∈ expressions.map NormalizedExpr.toParsed,
      WelcomeRowHasNoLm1Destination expression) :
    ¬ ProofsLean.Correct welcomeSealedMachine welcomeSpec
      (([InstructionLine.pe expressions] : List InstructionLine)) := by
  cases step : welcomeSealedMachine.step (.pe expressions)
      (welcomeInitialState welcomeZeroWords) with
  | none => exact welcome_not_correct_of_step_none _ step
  | some next =>
      refine welcome_not_correct_of_word_zero (.pe expressions) next step ⟨0, by decide⟩ ?_
      have frame := welcomePE_line_lm1_frame integerFrame stageFrame expressions
        welcomeZeroWords next unrefuted noLm1 step
      rw [frame]
      exact welcomeZero_initial_lm1 _

/-! ## 8. Non-vacuity: the plain integer-ALU class is clean

Every plain `.alu` / `.zero` / `.immediate` row is an integer-stage input (no
wait tag, no producer family), so the clean class of §3 contains the whole plain
class — in particular the two lines of the Welcome answer.  This instantiates the
assembly on a genuinely inhabited class. -/

theorem welcomeStageClean_of_plain (expressions : List ParsedExpr)
    (plain : expressions.all parsedExprIsPlainIntegerALU = true) :
    expressions.all welcomeStageCleanExpression = true := by
  apply List.all_eq_true.mpr
  intro expression member
  have h := List.all_eq_true.mp plain expression member
  obtain ⟨producer, unsupported, msl, relu, block, supported, waitTag, mmau, mwrite,
    l1tope, l2bm, nofwd, turn⟩ := parsedExprIsPlainIntegerALU_facts expression h
  have floatMau := parsedExprIsPlainIntegerALU_notFloatMAU expression h
  obtain ⟨l1m, l1g, l1r⟩ := plain_l1Predicates expression h
  have input : parsedExprIsIntegerMatrixReadStageInput expression = true := by
    rw [parsedExprIsIntegerMatrixReadStageInput_spec]
    exact ⟨waitTag, l2bm, mwrite, l1m, l1g, l1r, l1tope, mmau, floatMau, msl, block, relu⟩
  simp [welcomeStageCleanExpression, input]

/-- **The clean assembly on the plain class.**  A specialisation of
`welcomePE_line_commit_of_clean` that recovers the plain-class commit form from
`executeIntegerProducerInstructionLine_pe_commit_of_clean` rather than from the
plain-specific stage identities. -/
theorem welcomePE_line_commit_of_plain
    (expressions : List NormalizedExpr) (input : ProofsLean.MNCore.PlusOne.Words)
    (next : State) (unrefuted : WelcomePEUnrefuted expressions)
    (plain : (expressions.map NormalizedExpr.toParsed).all
      parsedExprIsPlainIntegerALU = true)
    (step : welcomeSealedMachine.step (.pe expressions)
      (welcomeInitialState input) = some next) :
    ∃ writes slots bars,
      welcomeIntegerPrep (welcomeInitialState input) welcomePE
        (expressions.map NormalizedExpr.toParsed) = .ok (writes, slots, bars) ∧
      next.peRegisters welcomePE =
        commitParsedMaskedWrites
          ((welcomeInitialState input).peRegisters welcomePE) writes :=
  welcomePE_line_commit_of_clean expressions input next unrefuted
    (welcomeStageClean_of_plain _ plain) step

/-! ## 9. A building block for the stage frames

The per-destination half of `WelcomePEStageLm1Frame`: `writeParsedMslMsrDestination?`
(the single destination writer shared by the MSL/MSR, float-relu and float-MAU
stages) leaves the `.lm1` bank alone when the destination operand lowers to a
bank other than `.lm1`.  The remaining work for the stage frames is the
induction over the local `writeDestinations` / `runCycles` loops and the per-PE
walk, using this lemma at each write. -/

theorem writeParsedMslMsrDestination?_lm1_of_ne
    (files : IntegerRegisterFiles) (destination : ParsedOperand)
    (context : ParsedIntegerContext) (output : IntegerALU.Bus) (flags : BitVec 4)
    (cycle : Fin 4) (directive : ParsedMaskDirective) (hasSingleLineMask : Bool)
    (noLm1 : ∀ (bank : PEMemory.Bank) (width : PEMemory.Width),
      ParsedOperand.directDestinationBankWidth? destination = some (bank, width) →
        bank ≠ PEMemory.Bank.lm1)
    (write : ParsedMslMsrDestinationWrite)
    (lowered : writeParsedMslMsrDestination? files destination context output flags cycle
      directive hasSingleLineMask = some write) :
    write.files.lm1 = files.lm1 := by
  cases destination with
  | mem access negated extended rounded mask =>
      simp only [writeParsedMslMsrDestination?] at lowered
      cases h : ParsedOperand.toDirectMemoryDestination?
        (ParsedOperand.mem access negated extended rounded mask) context.pe cycle
        context.bar0 context.bar1 context.tWord with
      | none => simp [h] at lowered
      | some found =>
          cases h2 : ParsedOperand.resolveMemoryWriteSelection?
            (ParsedOperand.mem access negated extended rounded mask) found.bank
            files.maskRegisters cycle directive hasSingleLineMask with
          | none => simp [h, h2] at lowered
          | some selection =>
              simp [h, h2] at lowered
              subst lowered
              have static := ParsedOperand.toDirectMemoryDestination?_bankWidth
                (ParsedOperand.mem access negated extended rounded mask) context.pe cycle
                context.bar0 context.bar1 context.tWord
              rw [h] at static
              exact writeDirectAccessMasked_lm1_of_ne files found _ _
                (noLm1 found.bank found.width static.symm)
  | omr entry mask =>
      simp only [writeParsedMslMsrDestination?] at lowered
      cases h : ParsedOperand.toMaskRegisterEntry? (ParsedOperand.omr entry mask) with
      | none => simp [h] at lowered
      | some found =>
          cases h2 : ParsedOperand.resolveOmrWriteSelection? (ParsedOperand.omr entry mask)
            files.maskRegisters cycle directive hasSingleLineMask with
          | none => simp [h, h2] at lowered
          | some selection =>
              simp [h, h2] at lowered
              subst lowered
              rfl
  | bar lm1 width mask =>
      simp only [writeParsedMslMsrDestination?] at lowered
      cases h : ParsedOperand.resolveMemoryWriteSelection? (ParsedOperand.bar lm1 width mask)
        (if lm1 = true then PEMemory.Bank.lm1 else PEMemory.Bank.lm0) files.maskRegisters
        cycle directive hasSingleLineMask with
      | none => simp [h] at lowered
      | some selection =>
          simp [h] at lowered
          subst lowered
          rfl
  | nowrite =>
      simp only [writeParsedMslMsrDestination?] at lowered
      obtain rfl := Option.some.inj lowered
      rfl
  | forward kind neg ext rnd => simp [writeParsedMslMsrDestination?] at lowered
  | fixed value => simp [writeParsedMslMsrDestination?] at lowered
  | matrix side width row => simp [writeParsedMslMsrDestination?] at lowered
  | l1bm width address => simp [writeParsedMslMsrDestination?] at lowered
  | l2bm address l2b => simp [writeParsedMslMsrDestination?] at lowered
  | dar value => simp [writeParsedMslMsrDestination?] at lowered

end ProofsLean.MNCore
