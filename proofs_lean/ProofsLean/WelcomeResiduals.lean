import ProofsLean.WelcomeFinalShape
import ProofsLean.WelcomeFloatProvenance

/-! # The two provenance/shape residuals of the final assembly

`WelcomeFinalShape.lean` (round 46) reduces `WelcomePELm1WriteShapeObligation` to
the bundle `WelcomePEDispatchResiduals`, whose two open components are

* `WelcomePELm1PhantomWriterProvenance` — if every `.lm1`-writing row of an
  unrefuted line is a *phantom* row (`.noforward`, a non-pending `.wait`, one of
  the five shared-block `.l1bm` forms, a `.matrixWrite` row or an `.l2bm` row), or
  if there is no `.lm1` writer at all, the line's stage commit list is
  `.lm1`-free;
* `WelcomePESpecialALUWriterShapeObligation` — if the line's unique `.lm1` writer
  is an `msl`/`msr`, float-relu or block-float row, the line satisfies
  `WelcomePEWriteShape`.

This module discharges the first residual unconditionally and reduces the second
to named Prop remainders, recording the exact missing facts.

## Plan

* **§1 the phantom classes.**  A phantom row is not a producer of any of the five
  executed stages (`welcomePhantomWriterKind_stagePredicates`), hence no row of a
  stage filter names bank `.lm1` (`..._of_phantomFilter`): a row that names an
  `.lm1` destination is an `.lm1` writer (`lm1_mem_writeBanks_of_destination`),
  and the phantom hypothesis would then contradict the stage predicate.
* **§2 the integer stage refined at `.noforward` / `.wait`.**  The existing
  integer-stage provenance
  (`prepareParsedIntegerMatrixReadLineExpressions_lm1_free`) demands that *every*
  row the integer stage prepares avoids bank `.lm1`.  A `.noforward` / `.wait`
  row prepares nothing (`prepareParsedIntegerMatrixReadLineExpression_skip`), so
  its destinations are irrelevant:
  `prepareParsedIntegerMatrixReadLineExpressions_clean_of_skip_or_noLm1`.
* **§3 the float-MAU list.**  `executeParsedFloatMAUsAtPE_clean_commit`
  (round 46) supplies the float half of the integer stage's commit list.
  Combining the two gives
  `executeIntegerProducerLineAtPEs_zero_prepared_float_clean_of_line_split`:
  the PE 0 walk over the integer stage's filter commits
  `intWrites ++ floatWrites` with both halves `.lm1`-free, where `intWrites` is
  `welcomeIntegerPrep`'s own list.
* **§4 the phantom provenance.**  The five middle stages commit `.lm1`-free
  lists by the round-46 stage provenance; the shared-block stage is an
  unconditional PE frame; the stage chain gives the line's commit list, and the
  concatenation of six `.lm1`-free lists is `.lm1`-free:
  `welcomePELm1PhantomWriterProvenance`.
* **§5 the special-ALU writer.**  The writer's own stage (its filter is the
  singleton `[e]`, since the executor fails on two rows) supplies the shaped
  list, all other stages are `.lm1`-free, and the shape transports across the
  `.lm1`-free prefix and suffix.  The `msl`/`msr` case is assembled from
  `welcomePEMslMsrCyclesShape` (the previously named
  `WelcomePEMslMsrExecutorExposure` is proved here), the float-relu case from
  `welcomePEFloatReluCyclesShape` plus the zero-state read-copy
  `welcomeZero_executeParsedFloatRelu_read_copy`, and the block-float `.d`/`.f`/`.g`
  case from `welcomePEBlockFloatMabShape_of_precision_low_zero` plus the new fold
  over `allMABCoordinates`.  Only the `.h`-precision (`non-low`) block-float
  writer remains, as `WelcomePEBlockFloatNonLowWriterShapeObligation`.

No `sorry`, no `admit`, no `native_decide`, no new axioms, and no existing module
is edited by this file.  Neither `LowerBound 2` nor `Optimal` is claimed.
-/

namespace ProofsLean.MNCore

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open Issue
open PEMemory

/-! ## 1. The phantom classes

A phantom row's operation is one of the non-executed forms, so it is not a
producer of any of the five executed stages.  This is the only syntactic input of
the phantom provenance: it converts "stage filter row that names `.lm1`" into
"`.lm1` writer of the line", which the phantom hypothesis then contradicts. -/

/-- **A phantom row is not a producer of any executed stage.**  All six stage
producer predicates are `false` for a `.noforward` / `.wait` / shared-block
`.l1bm` / `.matrixWrite` / `.l2bm` row. -/
theorem welcomePhantomWriterKind_stagePredicates (expression : ParsedExpr)
    (phantom : welcomePhantomWriterKind expression) :
    parsedExprIsMslMsrProducer expression = false ∧
      parsedExprIsFloatReluProducer expression = false ∧
      parsedExprIsBlockFloatProducer expression = false ∧
      parsedExprIsMatrixMAUProducer expression = false ∧
      parsedExprIsL1ToPEProducer expression = false ∧
      parsedExprIsSupportedFloatMAUProducer expression = false := by
  rcases expression with ⟨op, sources, destinations, flush, text⟩
  rcases phantom with opEq | ⟨tag, opEq⟩ | shared | mwrite | l2
  · have h : op = .noforward := opEq
    subst h
    simp [parsedExprIsMslMsrProducer, parsedExprIsFloatReluProducer,
      parsedExprIsBlockFloatProducer, parsedExprIsMatrixMAUProducer,
      parsedExprIsL1ToPEProducer, parsedExprIsSupportedFloatMAUProducer]
  · have h : op = .wait tag := opEq
    subst h
    simp [parsedExprIsMslMsrProducer, parsedExprIsFloatReluProducer,
      parsedExprIsBlockFloatProducer, parsedExprIsMatrixMAUProducer,
      parsedExprIsL1ToPEProducer, parsedExprIsSupportedFloatMAUProducer]
  · rcases parsedExprIsL1SharedBlockProducer_cases _ shared with
      ⟨mab, opEq⟩ | ⟨mab, opEq⟩ | ⟨difference, opEq⟩ | ⟨rrn, round, opEq⟩ |
        ⟨rrn, round, opEq⟩
    · have h : op = .l1bm (.mwrite mab) := opEq
      subst h
      simp [parsedExprIsMslMsrProducer, parsedExprIsFloatReluProducer,
        parsedExprIsBlockFloatProducer, parsedExprIsMatrixMAUProducer,
        parsedExprIsL1ToPEProducer, parsedExprIsSupportedFloatMAUProducer]
    · have h : op = .l1bm (.m4write mab) := opEq
      subst h
      simp [parsedExprIsMslMsrProducer, parsedExprIsFloatReluProducer,
        parsedExprIsBlockFloatProducer, parsedExprIsMatrixMAUProducer,
        parsedExprIsL1ToPEProducer, parsedExprIsSupportedFloatMAUProducer]
    · have h : op = .l1bm (.gather difference) := opEq
      subst h
      simp [parsedExprIsMslMsrProducer, parsedExprIsFloatReluProducer,
        parsedExprIsBlockFloatProducer, parsedExprIsMatrixMAUProducer,
        parsedExprIsL1ToPEProducer, parsedExprIsSupportedFloatMAUProducer]
    · have h : op = .l1bm (.reduce rrn round) := opEq
      subst h
      simp [parsedExprIsMslMsrProducer, parsedExprIsFloatReluProducer,
        parsedExprIsBlockFloatProducer, parsedExprIsMatrixMAUProducer,
        parsedExprIsL1ToPEProducer, parsedExprIsSupportedFloatMAUProducer]
    · have h : op = .l1bm (.reduce4 rrn round) := opEq
      subst h
      simp [parsedExprIsMslMsrProducer, parsedExprIsFloatReluProducer,
        parsedExprIsBlockFloatProducer, parsedExprIsMatrixMAUProducer,
        parsedExprIsL1ToPEProducer, parsedExprIsSupportedFloatMAUProducer]
  · cases op <;> simp_all [parsedExprIsMatrixWriteProducer, parsedExprIsMslMsrProducer,
      parsedExprIsFloatReluProducer, parsedExprIsBlockFloatProducer,
      parsedExprIsMatrixMAUProducer, parsedExprIsL1ToPEProducer,
      parsedExprIsSupportedFloatMAUProducer]
  · cases op <;> simp_all [parsedExprIsL2BMProducer, parsedExprIsMslMsrProducer,
      parsedExprIsFloatReluProducer, parsedExprIsBlockFloatProducer,
      parsedExprIsMatrixMAUProducer, parsedExprIsL1ToPEProducer,
      parsedExprIsSupportedFloatMAUProducer]

/-- **An `.lm1` direct destination is an `.lm1` write bank.**  The converse of
`welcomeRowHasNoLm1Destination_of_writeBanks_not_mem`: a destination operand that
resolves to bank `.lm1` contributes `Issue.Bank.lm1` to the row's `writeBanks`. -/
theorem lm1_mem_writeBanks_of_destination (expression : ParsedExpr)
    (destination : ParsedOperand) (width : PEMemory.Width)
    (member : destination ∈ expression.destinations)
    (resolved : ParsedOperand.directDestinationBankWidth? destination =
      some (PEMemory.Bank.lm1, width)) :
    Issue.Bank.lm1 ∈ (expression.toIssueExpr 0).writeBanks := by
  rw [writeBanks_eq_bankList]
  exact List.mem_append_left _
    (mem_bankList_of_mem expression.destinations destination member Issue.Bank.lm1
      (isLm1MemoryDestination_of_bankList destination width resolved))

/-- **A non-phantom row of a phantom line has no `.lm1` destination operand.** -/
theorem welcomeRowHasNoLm1Destination_of_phantom (line : List ParsedExpr)
    (phantomRows : ∀ e ∈ line, Issue.Bank.lm1 ∈ (e.toIssueExpr 0).writeBanks →
      welcomePhantomWriterKind e)
    (expression : ParsedExpr) (member : expression ∈ line)
    (notPhantom : ¬ welcomePhantomWriterKind expression) :
    WelcomeRowHasNoLm1Destination expression := by
  apply welcomeRowHasNoLm1Destination_of_writeBanks_not_mem expression 0
  intro writer
  exact notPhantom (phantomRows expression member writer)

/-- **Every row of a stage filter of a phantom line has no `.lm1` destination.**
The stage predicate excludes the phantom classes, so no row of the filter may be
an `.lm1` writer. -/
theorem welcomeRowHasNoLm1Destination_of_phantomFilter
    (line : List ParsedExpr)
    (phantomRows : ∀ e ∈ line, Issue.Bank.lm1 ∈ (e.toIssueExpr 0).writeBanks →
      welcomePhantomWriterKind e)
    (producer : ParsedExpr → Bool)
    (excludes : ∀ e, welcomePhantomWriterKind e → producer e = false)
    (expression : ParsedExpr) (member : expression ∈ line.filter producer) :
    WelcomeRowHasNoLm1Destination expression := by
  have lineMember : expression ∈ line := List.mem_of_mem_filter member
  have keeps : producer expression = true := (List.mem_filter.mp member).2
  refine welcomeRowHasNoLm1Destination_of_phantom line phantomRows expression lineMember ?_
  intro phantom
  have excluded := excludes expression phantom
  rw [keeps] at excluded
  simp at excluded

/-! ## 2. The integer stage refined at `.noforward` / `.wait`

The round-46 integer-stage provenance is stated at the integer-stage filter and
demands `WelcomeRowHasNoLm1Destination` of every prepared row.  A `.noforward` or
`.wait` row is prepared to the empty write list and leaves the forwarding slots
untouched (`prepareParsedIntegerMatrixReadLineExpression_skip`), so its
destinations never reach the commit list. -/

/-- **The integer-stage fold is `.lm1`-free when every prepared row either is
skipped or names no `.lm1` bank.** -/
theorem prepareParsedIntegerMatrixReadLineExpressions_clean_of_skip_or_noLm1
    (files : IntegerRegisterFiles) (oldSlots : ProofsLean.MNCore.Forwarding.Slots)
    (store : ParsedMatrixReadStore) (control : ParsedMaskExecutionControl)
    (hasSingleLineMask noForward reduced : Bool) :
    ∀ (expressions : List ParsedExpr),
      (∀ expression ∈ expressions,
        expression.op = .noforward ∨ (∃ tag : Fin 256, expression.op = .wait tag) ∨
          WelcomeRowHasNoLm1Destination expression) →
      ∀ (writes : List PreparedParsedMaskedWrite)
        (slots : ProofsLean.MNCore.Forwarding.Slots)
        (bars : List (Bool × BitVec 12))
        (finalWrites : List PreparedParsedMaskedWrite)
        (finalSlots : ProofsLean.MNCore.Forwarding.Slots)
        (finalBars : List (Bool × BitVec 12)),
        prepareParsedIntegerMatrixReadLineExpressions files oldSlots store control
          hasSingleLineMask noForward reduced expressions writes slots bars =
            .ok (finalWrites, finalSlots, finalBars) →
        Lm1FreePreparedWrites writes → Lm1FreePreparedWrites finalWrites := by
  intro expressions
  induction expressions with
  | nil =>
      intro rows writes slots bars finalWrites finalSlots finalBars executed prior
      simp only [prepareParsedIntegerMatrixReadLineExpressions, StepResult.ok.injEq,
        Prod.mk.injEq] at executed
      obtain ⟨rfl, rfl, rfl⟩ := executed
      exact prior
  | cons expression rest ih =>
      intro rows writes slots bars finalWrites finalSlots finalBars executed prior
      simp only [prepareParsedIntegerMatrixReadLineExpressions] at executed
      rcases rows expression (by simp) with skip | ⟨tag, tagEq⟩ | noLm1
      · have skipped := prepareParsedIntegerMatrixReadLineExpression_skip files oldSlots slots
          store expression control hasSingleLineMask noForward reduced (Or.inl skip)
        rw [skipped] at executed
        dsimp only at executed
        simp only [List.append_nil] at executed
        exact ih (fun item member => rows item (List.mem_cons_of_mem _ member))
          writes slots bars finalWrites finalSlots finalBars executed prior
      · have skipped := prepareParsedIntegerMatrixReadLineExpression_skip files oldSlots slots
          store expression control hasSingleLineMask noForward reduced (Or.inr ⟨tag, tagEq⟩)
        rw [skipped] at executed
        dsimp only at executed
        simp only [List.append_nil] at executed
        exact ih (fun item member => rows item (List.mem_cons_of_mem _ member))
          writes slots bars finalWrites finalSlots finalBars executed prior
      · cases result : prepareParsedIntegerMatrixReadLineExpression files oldSlots slots store
            expression control hasSingleLineMask noForward reduced with
        | failure => rw [result] at executed; simp at executed
        | unknown => rw [result] at executed; simp at executed
        | ok expressionResult =>
            rw [result] at executed
            dsimp only at executed
            obtain ⟨expressionWrites, expressionSlots, expressionBars⟩ := expressionResult
            have headFree := prepareParsedIntegerMatrixReadLineExpression_lm1_free files
              oldSlots slots store expression control hasSingleLineMask noForward reduced
              expressionWrites expressionSlots expressionBars noLm1 result
            exact ih (fun item member => rows item (List.mem_cons_of_mem _ member))
              (writes ++ expressionWrites) expressionSlots (bars ++ expressionBars)
              finalWrites finalSlots finalBars executed
              (lm1FreePreparedWrites_append prior headFree)

/-- **The integer-stage cycle fold, refined.** -/
theorem prepareParsedIntegerMatrixReadLineCycles_clean_of_skip_or_noLm1
    (files : IntegerRegisterFiles) (oldSlots : ProofsLean.MNCore.Forwarding.Slots)
    (store : ParsedMatrixReadStore) (expressions : List ParsedExpr)
    (control : ParsedMaskExecutionControl) (reduced : Bool)
    (rows : ∀ expression ∈ expressions,
      expression.op = .noforward ∨ (∃ tag : Fin 256, expression.op = .wait tag) ∨
        WelcomeRowHasNoLm1Destination expression)
    (writes : List PreparedParsedMaskedWrite)
    (nextSlots : ProofsLean.MNCore.Forwarding.Slots)
    (bars : List (Bool × BitVec 12))
    (prepared : prepareParsedIntegerMatrixReadLineCycles files oldSlots store expressions
      control reduced = .ok (writes, nextSlots, bars)) :
    Lm1FreePreparedWrites writes := by
  unfold prepareParsedIntegerMatrixReadLineCycles at prepared
  exact prepareParsedIntegerMatrixReadLineExpressions_clean_of_skip_or_noLm1 files oldSlots
    store control _ _ reduced expressions rows [] oldSlots [] writes nextSlots bars prepared
    lm1FreePreparedWrites_nil

/-- **`welcomeIntegerPrep`'s list is `.lm1`-free, refined.**  A `.noforward` or
`.wait` integer-stage row is skipped, so it need not avoid bank `.lm1`; every
prepared row must. -/
theorem welcomeIntegerPrep_lm1_free_of_skip_or_noLm1
    (state : State) (pe : PEId) (expressions : List ParsedExpr)
    (rows : ∀ expression ∈ expressions.filter parsedExprIsIntegerMatrixReadStageInput,
      expression.op = .noforward ∨ (∃ tag : Fin 256, expression.op = .wait tag) ∨
        WelcomeRowHasNoLm1Destination expression)
    (writes : List PreparedParsedMaskedWrite)
    (slots : ProofsLean.MNCore.Forwarding.Slots)
    (bars : List (Bool × BitVec 12))
    (prepared : welcomeIntegerPrep state pe expressions = .ok (writes, slots, bars)) :
    Lm1FreePreparedWrites writes := by
  unfold welcomeIntegerPrep at prepared
  exact prepareParsedIntegerMatrixReadLineCycles_clean_of_skip_or_noLm1
    (state.peRegisters pe) (stateForwardingSlots state pe)
    (state.matrixRegisters (ParsedIntegerContext.ofLinearIndex pe).group
      (ParsedIntegerContext.ofLinearIndex pe).l2b
      (ParsedIntegerContext.ofLinearIndex pe).l1b)
    (expressions.filter parsedExprIsIntegerMatrixReadStageInput)
    (parsedPEHazardControl state pe) false rows writes slots bars prepared

/-! ## 3. The PE-0 walk of the integer stage, refined

The round-46 walk statement `executeIntegerProducerLineAtPEs_zero_prepared_float_clean`
demands `.lm1`-freeness of every line row; the refined integer-stage provenance of
§2 only demands it of the prepared rows, and the float-MAU list is covered by
`executeParsedFloatMAUsAtPE_clean_commit`.  Both halves of the committed list come
out `.lm1`-free. -/

/-- **The integer stage's PE 0 commit list, both halves `.lm1`-free.** -/
theorem executeIntegerProducerLineAtPEs_zero_prepared_float_clean_of_line_split
    (expressions : List NormalizedExpr) (next : State)
    (intRows : ∀ expression ∈ (expressions.map NormalizedExpr.toParsed).filter
        parsedExprIsIntegerMatrixReadStageInput,
      expression.op = .noforward ∨ (∃ tag : Fin 256, expression.op = .wait tag) ∨
        WelcomeRowHasNoLm1Destination expression)
    (floatRows : ∀ expression ∈ (expressions.map NormalizedExpr.toParsed).filter
        parsedExprIsSupportedFloatMAUProducer, WelcomeRowHasNoLm1Destination expression)
    (executed : executeIntegerProducerLineAtPEs (welcomePEWalkFilter expressions)
      (List.finRange 4096) (welcomeInitialState welcomeZeroWords) = .ok next) :
    ∃ intWrites floatWrites slots bars,
      welcomeIntegerPrep (welcomeInitialState welcomeZeroWords) welcomePE
        (welcomePEWalkFilter expressions) = .ok (intWrites, slots, bars) ∧
      next.peRegisters welcomePE =
        commitParsedMaskedWrites welcomeZeroFiles (intWrites ++ floatWrites) ∧
      Lm1FreePreparedWrites intWrites ∧ Lm1FreePreparedWrites floatWrites := by
  have hrange : List.finRange 4096 =
      welcomePE :: (List.finRange 4095).map Fin.succ := by
    have h := @List.finRange_succ 4095
    simpa [welcomePE] using h
  rw [hrange] at executed
  simp only [executeIntegerProducerLineAtPEs] at executed
  split at executed
  · simp at executed
  · simp at executed
  · rename_i nextPEs headExecuted
    have coreExecuted : executeIntegerProducerLineAtPECore (welcomePEWalkFilter expressions)
        (welcomeInitialState welcomeZeroWords) welcomePE = .ok nextPEs := by
      unfold executeIntegerProducerLineAtPE at headExecuted
      split at headExecuted
      · simp at headExecuted
      · exact headExecuted
    have floatRowsWalk : ∀ expression ∈
        (welcomePEWalkFilter expressions).filter parsedExprIsSupportedFloatMAUProducer,
        WelcomeRowHasNoLm1Destination expression := by
      intro expression member
      rw [welcomePEWalkFilter_float] at member
      exact floatRows expression member
    obtain ⟨intWrites, floatWrites, slots, bars, intPrep, intCommit, floatFree⟩ :=
      executeIntegerProducerLineAtPECore_prepared_float_clean (welcomePEWalkFilter expressions)
        (welcomeInitialState welcomeZeroWords) nextPEs welcomePE floatRowsWalk coreExecuted
    have intFree : Lm1FreePreparedWrites intWrites := by
      refine welcomeIntegerPrep_lm1_free_of_skip_or_noLm1 (welcomeInitialState welcomeZeroWords)
        welcomePE (welcomePEWalkFilter expressions) ?_ intWrites slots bars intPrep
      intro expression member
      rw [welcomePEWalkFilter_integer] at member
      exact intRows expression member
    have notMem : welcomePE ∉ (List.finRange 4095).map Fin.succ := by
      intro hmem
      simp only [List.mem_map] at hmem
      obtain ⟨i, -, hi⟩ := hmem
      have := congrArg Fin.val hi
      simp [welcomePE] at this
    have tailFrame := executeIntegerProducerLineAtPEs_peRegisters_not_mem
      (welcomePEWalkFilter expressions) ((List.finRange 4095).map Fin.succ) nextPEs next
      executed
      (fun pe p s n he different =>
        executeIntegerProducerLineAtPE_peRegisters_other (welcomePEWalkFilter expressions) s n
          pe p different he)
      welcomePE notMem
    refine ⟨intWrites, floatWrites, slots, bars, intPrep, ?_, intFree, floatFree⟩
    rw [tailFrame]
    exact intCommit

/-! ## 4. The phantom provenance

The line's PE 0 register file is the commit of the six stage lists
(`executeIntegerProducerInstructionLine_pe_commit_split`).  The integer stage's
list is `intWrites ++ floatWrites`, both `.lm1`-free by §3; the five middle stages'
lists are `.lm1`-free by the round-46 stage provenance applied to the stage
filters of a phantom line (§1); the shared-block stage is an unconditional PE
frame.  Six `.lm1`-free lists concatenate to an `.lm1`-free list. -/

/-- **Freeness of a left-associated six-block concatenation.** -/
theorem lm1FreePreparedWrites_six (a b c d e f : List PreparedParsedMaskedWrite)
    (ha : Lm1FreePreparedWrites a) (hb : Lm1FreePreparedWrites b)
    (hc : Lm1FreePreparedWrites c) (hd : Lm1FreePreparedWrites d)
    (he : Lm1FreePreparedWrites e) (hf : Lm1FreePreparedWrites f) :
    Lm1FreePreparedWrites (a ++ b ++ c ++ d ++ e ++ f) := by
  intro write member
  rcases List.mem_append.mp member with first | last
  · rcases List.mem_append.mp first with second | fifth
    · rcases List.mem_append.mp second with third | fourth
      · rcases List.mem_append.mp third with fourth' | third'
        · rcases List.mem_append.mp fourth' with first' | second'
          · exact ha write first'
          · exact hb write second'
        · exact hc write third'
      · exact hd write fourth
    · exact he write fifth
  · exact hf write last

/-- **The phantom/no-writer provenance holds.**  A line all of whose `.lm1`
writers are phantom rows commits an `.lm1`-free stage list at PE 0. -/
theorem welcomePELm1PhantomWriterProvenance : WelcomePELm1PhantomWriterProvenance := by
  intro expressions unrefuted phantomRows next step
  have executed := welcomeSealed_step_ok step
  simp only [executeNormalizedLine, NormalizedLine.toInstruction?,
    Issue.InstructionLine.toNormalizedLine] at executed
  obtain ⟨accepted, waits, unsupported, supported⟩ :=
    executeIntegerProducerInstructionLine_pe_conditions expressions
      (welcomeInitialState welcomeZeroWords) next executed
  obtain ⟨nextPEs, nextMsl, nextRelu, nextBlockFloat, afterMatrix, nextShared, nextBroadcast,
    walkExecuted, mslExecuted, reluExecuted, blockExecuted, matrixExecuted, sharedExecuted,
    l1Executed, nextEq⟩ :=
    executeIntegerProducerInstructionLine_pe_stages_exists expressions
      (welcomeInitialState welcomeZeroWords) next accepted waits unsupported supported executed
  -- the integer-stage split: skipped rows or `.lm1`-free rows
  have intRows : ∀ expression ∈ (expressions.map NormalizedExpr.toParsed).filter
      parsedExprIsIntegerMatrixReadStageInput,
      expression.op = .noforward ∨ (∃ tag : Fin 256, expression.op = .wait tag) ∨
        WelcomeRowHasNoLm1Destination expression := by
    intro expression member
    have lineMember : expression ∈ expressions.map NormalizedExpr.toParsed :=
      List.mem_of_mem_filter member
    have keeps : parsedExprIsIntegerMatrixReadStageInput expression = true :=
      (List.mem_filter.mp member).2
    obtain ⟨waitNone, l2bm, mwrite, l1mwrite, l1gather, l1reduce, l1, mmau, float, msl,
      block, relu⟩ := (parsedExprIsIntegerMatrixReadStageInput_spec expression).mp keeps
    by_cases forward : expression.op = .noforward
    · exact Or.inl forward
    by_cases wait : ∃ tag : Fin 256, expression.op = .wait tag
    · exact Or.inr (Or.inl wait)
    refine Or.inr (Or.inr ?_)
    refine welcomeRowHasNoLm1Destination_of_phantom _ phantomRows expression lineMember ?_
    intro phantom
    rcases phantom with opEq | ⟨tag, opEq⟩ | shared | mwriteEq | l2
    · exact forward opEq
    · exact wait ⟨tag, opEq⟩
    · rcases parsedExprIsL1SharedBlockProducer_cases expression shared with
        ⟨mab, opEq⟩ | ⟨mab, opEq⟩ | ⟨difference, opEq⟩ | ⟨rrn, round, opEq⟩ |
          ⟨rrn, round, opEq⟩
      · have trueEq : parsedExprIsL1MwriteProducer expression = true := by
          simp [parsedExprIsL1MwriteProducer, opEq]
        rw [trueEq] at l1mwrite
        simp at l1mwrite
      · have trueEq : parsedExprIsL1MwriteProducer expression = true := by
          simp [parsedExprIsL1MwriteProducer, opEq]
        rw [trueEq] at l1mwrite
        simp at l1mwrite
      · have trueEq : parsedExprIsL1GatherProducer expression = true := by
          simp [parsedExprIsL1GatherProducer, opEq]
        rw [trueEq] at l1gather
        simp at l1gather
      · have trueEq : parsedExprIsL1ReduceProducer expression = true := by
          simp [parsedExprIsL1ReduceProducer, opEq]
        rw [trueEq] at l1reduce
        simp at l1reduce
      · have trueEq : parsedExprIsL1ReduceProducer expression = true := by
          simp [parsedExprIsL1ReduceProducer, opEq]
        rw [trueEq] at l1reduce
        simp at l1reduce
    · rw [mwriteEq] at mwrite
      simp at mwrite
    · rw [l2] at l2bm
      simp at l2bm
  -- the float-MAU filter of a phantom line
  have floatRows : ∀ expression ∈ (expressions.map NormalizedExpr.toParsed).filter
      parsedExprIsSupportedFloatMAUProducer, WelcomeRowHasNoLm1Destination expression :=
    fun expression member => welcomeRowHasNoLm1Destination_of_phantomFilter _
      phantomRows parsedExprIsSupportedFloatMAUProducer
      (fun x h => (welcomePhantomWriterKind_stagePredicates x h).2.2.2.2.2) expression member
  obtain ⟨intWrites, floatWrites, slots, bars, intPrep, intCommit, intFree, floatFree⟩ :=
    executeIntegerProducerLineAtPEs_zero_prepared_float_clean_of_line_split expressions nextPEs
      intRows floatRows walkExecuted
  -- the five middle stages
  obtain ⟨mslWrites, mslCommit, mslFree⟩ :=
    executeParsedMslMsrProducers_clean_commit (welcomeInitialState welcomeZeroWords) nextPEs
      nextMsl (expressions.map NormalizedExpr.toParsed) _ _
      (fun expression member => welcomeRowHasNoLm1Destination_of_phantomFilter _
        phantomRows parsedExprIsMslMsrProducer
        (fun x h => (welcomePhantomWriterKind_stagePredicates x h).1) expression member)
      mslExecuted
  obtain ⟨reluWrites, reluCommit, reluFree⟩ :=
    executeParsedFloatReluProducers_clean_commit (welcomeInitialState welcomeZeroWords)
      nextMsl nextRelu (expressions.map NormalizedExpr.toParsed) _ _
      (fun expression member => welcomeRowHasNoLm1Destination_of_phantomFilter _
        phantomRows parsedExprIsFloatReluProducer
        (fun x h => (welcomePhantomWriterKind_stagePredicates x h).2.1) expression member)
      reluExecuted
  obtain ⟨blockWrites, blockCommit, blockFree⟩ :=
    executeParsedBlockFloatProducer_clean_commit (welcomeInitialState welcomeZeroWords)
      nextRelu nextBlockFloat (expressions.map NormalizedExpr.toParsed) _ _
      (fun expression member => welcomeRowHasNoLm1Destination_of_phantomFilter _
        phantomRows parsedExprIsBlockFloatProducer
        (fun x h => (welcomePhantomWriterKind_stagePredicates x h).2.2.1) expression member)
      blockExecuted
  obtain ⟨matrixWrites, matrixCommit, matrixFree⟩ :=
    executeParsedMatrixMAUAndWrites_clean_commit (welcomeInitialState welcomeZeroWords)
      nextBlockFloat afterMatrix (expressions.map NormalizedExpr.toParsed) _ _
      (fun expression member => welcomeRowHasNoLm1Destination_of_phantomFilter _
        phantomRows parsedExprIsMatrixMAUProducer
        (fun x h => (welcomePhantomWriterKind_stagePredicates x h).2.2.2.1) expression member)
      matrixExecuted
  obtain ⟨l1Writes, l1Commit, l1Free⟩ :=
    executeParsedL1ToPEProducers_clean_commit (welcomeInitialState welcomeZeroWords)
      nextShared nextBroadcast (expressions.map NormalizedExpr.toParsed) _ _ _
      (fun expression member => welcomeRowHasNoLm1Destination_of_phantomFilter _
        phantomRows parsedExprIsL1ToPEProducer
        (fun x h => (welcomePhantomWriterKind_stagePredicates x h).2.2.2.2.1) expression member)
      l1Executed
  have sharedFrame : nextShared.peRegisters welcomePE = afterMatrix.peRegisters welcomePE :=
    congrFun (executeParsedSharedBlockProducers_peRegisters (welcomeInitialState welcomeZeroWords)
      afterMatrix nextShared (expressions.map NormalizedExpr.toParsed)
      (!(expressions.any (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed)))
      sharedExecuted) welcomePE
  have commitEq := executeIntegerProducerInstructionLine_pe_commit_split nextPEs nextMsl
    nextRelu nextBlockFloat afterMatrix nextShared nextBroadcast next (by rw [nextEq])
    (intWrites ++ floatWrites) mslWrites reluWrites blockWrites matrixWrites l1Writes
    intCommit mslCommit reluCommit blockCommit matrixCommit sharedFrame l1Commit
  refine ⟨(intWrites ++ floatWrites) ++ mslWrites ++ reluWrites ++ blockWrites ++
    matrixWrites ++ l1Writes, ?_, ?_⟩
  · rw [commitEq]
  · exact lm1FreePreparedWrites_six (intWrites ++ floatWrites) mslWrites reluWrites blockWrites
      matrixWrites l1Writes (lm1FreePreparedWrites_append intFree floatFree) mslFree reluFree
      blockFree matrixFree l1Free

/-! ## 5. The special-ALU writer

The line's unique `.lm1` writer `e` is an `msl`/`msr`, float-relu or block-float
row.  For each family the argument is the same:

1. the family's stage filter is the singleton `[e]` (the executor returns
   `.failure` on two rows, so a successful stage has at most one row, and `e` is
   in it);
2. every *other* stage's write list is `.lm1`-free, because `e` is the unique
   `.lm1` writer and is not a producer of the other stages;
3. the writer's stage list carries the family's row shape at PE 0;
4. the six-block concatenation of the stage lists is shaped by
   `lm1WritesShape_of_six_*`.

The `msl`/`msr`, float-relu and low-precision block-float families are discharged
below.  The remaining block-float family is exactly
`WelcomePEBlockFloatWriterShapeObligation` of `WelcomeFinalShape.lean`; its
non-low (`.h`-precision) coordinate needs the third-word copy of
`parsedBlockFloatMab .h`, which is *false* for arbitrary input buses
(`parsedBlockFloatMab_h_third_word_not_copy`) and would have to be derived from
the all-zero state's reads. -/

/-! ### 5.1 The `.lm1`-free case of a write list -/

/-- The narrow shape of the empty list (no window has to cover anything). -/
theorem lm1WritesShape_nil : Lm1WritesShape [] :=
  Or.inr ⟨[], by intro write member; simp at member, by simp, by simp⟩

/-! ### 5.2 The stage profile of an `msl`/`msr` row

An `msl`/`msr` row is an `.alu .msl none …` / `.alu .msr none …` row, so it is
not a producer of any other stage and not an integer-stage input. -/

theorem parsedExprIsMslMsrProducer_cases (expression : ParsedExpr)
    (msl : parsedExprIsMslMsrProducer expression = true) :
    (∃ (unsigned : Bool) (arg : Option (Fin 256)),
      expression.op = .alu .msl none unsigned arg) ∨
    (∃ (unsigned : Bool) (arg : Option (Fin 256)),
      expression.op = .alu .msr none unsigned arg) := by
  rcases expression with ⟨op, sources, destinations, flush, text⟩
  cases op with
  | alu name precision unsigned arg =>
      cases name <;> cases precision <;> simp_all [parsedExprIsMslMsrProducer]
  | immediate value unsigned => simp [parsedExprIsMslMsrProducer] at msl
  | zero => simp [parsedExprIsMslMsrProducer] at msl
  | mau precision matrix kind half round => simp [parsedExprIsMslMsrProducer] at msl
  | matrixWrite precision => simp [parsedExprIsMslMsrProducer] at msl
  | matrixRead precision => simp [parsedExprIsMslMsrProducer] at msl
  | wait tag => simp [parsedExprIsMslMsrProducer] at msl
  | noforward => simp [parsedExprIsMslMsrProducer] at msl
  | l1bm operation => simp [parsedExprIsMslMsrProducer] at msl
  | l2bm operation => simp [parsedExprIsMslMsrProducer] at msl

theorem welcomeMslMsr_stageProfile (expression : ParsedExpr)
    (msl : parsedExprIsMslMsrProducer expression = true) :
    parsedExprIsFloatReluProducer expression = false ∧
      parsedExprIsBlockFloatProducer expression = false ∧
      parsedExprIsMatrixMAUProducer expression = false ∧
      parsedExprIsL1ToPEProducer expression = false ∧
      parsedExprIsSupportedFloatMAUProducer expression = false ∧
      parsedExprIsIntegerMatrixReadStageInput expression = false ∧
      parsedExprIsMatrixWriteProducer expression = false ∧
      parsedExprIsL2BMProducer expression = false := by
  rcases parsedExprIsMslMsrProducer_cases expression msl with
    ⟨unsigned, arg, op⟩ | ⟨unsigned, arg, op⟩ <;>
    simp [op, msl, parsedExprIsFloatReluProducer, parsedExprIsBlockFloatProducer,
      parsedExprIsMatrixMAUProducer, parsedExprIsL1ToPEProducer,
      parsedExprIsSupportedFloatMAUProducer, parsedExprIsIntegerMatrixReadStageInput,
      parsedExprIsMatrixWriteProducer, parsedExprIsL2BMProducer]

/-! ### 5.3 The `msl`/`msr` executor exposure and row shape -/

/-- **The `msl`/`msr` executor exposes its cycle fold.**  The previously named
residual `WelcomePEMslMsrExecutorExposure` holds definitionally: the executor's
local `runCycles` call is exactly the one of the statement, with the cycle fold's
arguments built from `ofLinearIndex pe` and `readState.peContext pe`. -/
theorem welcomePEMslMsrExecutorExposure : WelcomePEMslMsrExecutorExposure := by
  intro readState currentState expression pe noForward hasSingleLineMask next isMsl
    destinations lowered executed
  rw [executeParsedMslMsrAtPE.eq_1] at executed
  rw [lowered] at executed
  dsimp only at executed
  split at executed
  · simp at executed
  · simp at executed
  · rename_i registers bar0 bar1 outputs ran
    rw [Id.run_pure] at executed
    simp only [StepResult.ok.injEq] at executed
    refine ⟨registers, bar0, bar1, outputs, ?_, ?_⟩
    · have sameSource : mslMsrSourceAt expression readState isMsl
          (mslMsrSourcePE pe isMsl) =
          (fun cycle =>
            match expression.sources with
            | [source] =>
              ParsedOperand.toParsedIntegerInput? source IntegerALU.Precision.long
                (ParsedIntegerContext.ofLinearIndex (mslMsrSourcePE pe isMsl)).group
                (ParsedIntegerContext.ofLinearIndex (mslMsrSourcePE pe isMsl)).l2b
                (ParsedIntegerContext.ofLinearIndex (mslMsrSourcePE pe isMsl)).l1b
                (ParsedIntegerContext.ofLinearIndex (mslMsrSourcePE pe isMsl)).mab
                (ParsedIntegerContext.ofLinearIndex (mslMsrSourcePE pe isMsl)).pe cycle
                (readState.peContext (mslMsrSourcePE pe isMsl)).bar0
                (readState.peContext (mslMsrSourcePE pe isMsl)).bar1
                (readState.peContext (mslMsrSourcePE pe isMsl)).tWord
            | _ => none) := rfl
      rw [sameSource]
      exact ran
    · subst executed
      simp

/-- **The `msl`/`msr` row shape at its visited PE.**  The row's commit list at
`pe` is the cycle-fold list of `welcomePEMslMsrCyclesShape`; the static `.lm1`
width and the "at most one `.lm1` destination" bound come from the row's
no-duplicate-write condition. -/
theorem executeParsedMslMsrAtPE_pe_shape
    (readState currentState next : State) (expression : ParsedExpr) (pe : PEId)
    (noForward hasSingleLineMask : Bool)
    (nodup : (expression.toIssueExpr 0).writeBanks.Nodup)
    (executed : executeParsedMslMsrAtPE readState currentState expression pe noForward
      hasSingleLineMask = .ok next) :
    ∃ writes, next.peRegisters pe =
      commitParsedMaskedWrites (currentState.peRegisters pe) writes ∧
      Lm1WritesShape writes := by
  cases lowered : lowerParsedMslMsr? expression with
  | none =>
      rw [executeParsedMslMsrAtPE_lowering_failure readState currentState expression pe
        noForward hasSingleLineMask lowered] at executed
      simp at executed
  | some pair =>
      obtain ⟨isMsl, destinations⟩ := pair
      have destinationsEq : destinations = expression.destinations :=
        lowerParsedMslMsr?_destinations expression isMsl destinations lowered
      have staticWidth : ∀ destination ∈ destinations,
          ∀ (bank : PEMemory.Bank) (width : PEMemory.Width),
            ParsedOperand.directDestinationBankWidth? destination = some (bank, width) →
              bank = PEMemory.Bank.lm1 →
                width = (lm1StaticWidth expression).getD PEMemory.Width.word := by
        intro destination member bank width resolved bankEq
        rw [destinationsEq] at member
        rw [bankEq] at resolved
        exact lm1StaticWidth_spec expression nodup destination member width resolved
      have countBound : (destinations.filter ParsedOperand.isLm1MemoryDestination).length ≤ 1 := by
        rw [destinationsEq]
        exact lm1Destinations_count_le_one expression 0 nodup
      obtain ⟨writes, committed, shape⟩ :=
        welcomePEMslMsrExecutorRowShape_of_exposure welcomePEMslMsrExecutorExposure
          readState currentState expression pe noForward hasSingleLineMask next isMsl
          destinations ((lm1StaticWidth expression).getD PEMemory.Width.word) lowered
          staticWidth countBound executed
      exact ⟨writes, committed, shape⟩

/-- **An `msl`/`msr` walk leaves every unvisited PE untouched.** -/
theorem executeParsedMslMsrAtPEs_peRegisters_not_mem
    (readState : State) (expression : ParsedExpr) (noForward hasSingleLineMask : Bool) :
    ∀ (pes : List PEId) (state next : State) (target : PEId), target ∉ pes →
      executeParsedMslMsrAtPEs readState state expression pes noForward hasSingleLineMask =
        .ok next →
      next.peRegisters target = state.peRegisters target := by
  intro pes
  induction pes with
  | nil =>
      intro state next target absent executed
      simp only [executeParsedMslMsrAtPEs, StepResult.ok.injEq] at executed
      subst executed
      rfl
  | cons pe rest ih =>
      intro state next target absent executed
      simp only [executeParsedMslMsrAtPEs] at executed
      split at executed
      · simp at executed
      · simp at executed
      · rename_i middle headExecuted
        have different : target ≠ pe := by
          intro same
          exact absent (same ▸ List.mem_cons_self ..)
        have headFrame := executeParsedMslMsrAtPE_peRegisters_frame' readState state middle
          expression pe target different noForward hasSingleLineMask headExecuted
        have tailAbsent : target ∉ rest := fun member =>
          absent (List.mem_cons_of_mem _ member)
        rw [ih middle next target tailAbsent executed, headFrame]

/-- **The `msl`/`msr` walk shape at a visited PE.**  The walk is over a
duplicate-free PE list, so the target's own step is its only write step into the
target's file; that step's list carries the row shape. -/
theorem executeParsedMslMsrAtPEs_shape
    (readState : State) (expression : ParsedExpr) (noForward hasSingleLineMask : Bool)
    (nodup : (expression.toIssueExpr 0).writeBanks.Nodup) :
    ∀ (pes : List PEId) (pesNodup : pes.Nodup) (state next : State) (target : PEId),
      target ∈ pes →
      executeParsedMslMsrAtPEs readState state expression pes noForward hasSingleLineMask =
        .ok next →
      ∃ writes, next.peRegisters target =
        commitParsedMaskedWrites (state.peRegisters target) writes ∧
        Lm1WritesShape writes := by
  intro pes
  induction pes with
  | nil => intro _ state next target member; simp at member
  | cons pe rest ih =>
      intro pesNodup state next target member executed
      obtain ⟨peNotRest, restNodup⟩ := List.nodup_cons.mp pesNodup
      simp only [executeParsedMslMsrAtPEs] at executed
      split at executed
      · simp at executed
      · simp at executed
      · rename_i middle headExecuted
        by_cases same : target = pe
        · subst target
          obtain ⟨headWrites, headCommit, headShape⟩ :=
            executeParsedMslMsrAtPE_pe_shape readState state middle expression pe noForward
              hasSingleLineMask nodup headExecuted
          have absent : pe ∉ rest := peNotRest
          have tailFrame := executeParsedMslMsrAtPEs_peRegisters_not_mem readState expression
            noForward hasSingleLineMask rest middle next pe absent executed
          refine ⟨headWrites, ?_, headShape⟩
          rw [tailFrame]
          exact headCommit
        · have memberRest : target ∈ rest := by
            rcases List.mem_cons.mp member with same' | member
            · exact absurd same' same
            · exact member
          obtain ⟨tailWrites, tailCommit, tailShape⟩ :=
            ih restNodup middle next target memberRest executed
          have headFrame := executeParsedMslMsrAtPE_peRegisters_frame' readState state middle
            expression pe target same noForward hasSingleLineMask headExecuted
          exact ⟨tailWrites, by rw [tailCommit, headFrame], tailShape⟩

/-- **A successful `msl`/`msr` stage has a singleton producer filter.** -/
theorem mslMsrFilter_length_le_one
    (readState currentState next : State) (expressions : List ParsedExpr)
    (noForward hasSingleLineMask : Bool)
    (executed : executeParsedMslMsrProducers readState currentState expressions noForward
      hasSingleLineMask = .ok next) :
    (expressions.filter parsedExprIsMslMsrProducer).length ≤ 1 := by
  cases filtered : expressions.filter parsedExprIsMslMsrProducer with
  | nil => simp
  | cons expression rest =>
      cases rest with
      | nil => simp
      | cons second remaining =>
          simp only [executeParsedMslMsrProducers, filtered] at executed
          simp at executed

/-- The producer filter is the writer's singleton. -/
theorem mslMsrFilter_singleton (expressions : List ParsedExpr) (e : ParsedExpr)
    (member : e ∈ expressions.filter parsedExprIsMslMsrProducer)
    (short : (expressions.filter parsedExprIsMslMsrProducer).length ≤ 1) :
    expressions.filter parsedExprIsMslMsrProducer = [e] := by
  cases filtered : expressions.filter parsedExprIsMslMsrProducer with
  | nil => rw [filtered] at member; simp at member
  | cons expression rest =>
      cases rest with
      | nil =>
          rw [filtered] at member
          simp only [List.mem_singleton] at member
          rw [member]
      | cons second remaining =>
          rw [filtered] at short
          simp at short

/-- **The `msl`/`msr` producer stage's PE 0 shape, from the singleton filter.** -/
theorem executeParsedMslMsrProducers_shape_of_singleton
    (readState currentState next : State) (expressions : List ParsedExpr) (e : ParsedExpr)
    (noForward hasSingleLineMask : Bool)
    (filtered : expressions.filter parsedExprIsMslMsrProducer = [e])
    (nodup : (e.toIssueExpr 0).writeBanks.Nodup)
    (executed : executeParsedMslMsrProducers readState currentState expressions noForward
      hasSingleLineMask = .ok next) :
    ∃ writes, next.peRegisters welcomePE =
      commitParsedMaskedWrites (currentState.peRegisters welcomePE) writes ∧
      Lm1WritesShape writes := by
  simp only [executeParsedMslMsrProducers, filtered] at executed
  exact executeParsedMslMsrAtPEs_shape readState e noForward hasSingleLineMask nodup
    (List.finRange 4096) (List.nodup_finRange 4096) currentState next welcomePE
    (List.mem_finRange welcomePE) executed

/-! ### 5.4 The uniqueness bridge on a stage filter -/

/-- **A stage filter of a line with one `.lm1` writer is `.lm1`-free**, provided
the writer is not a producer of that stage. -/
theorem stageFilter_noLm1_of_rows (line : List ParsedExpr) (e : ParsedExpr)
    (rows : ∀ x ∈ line, x ≠ e → WelcomeRowHasNoLm1Destination x)
    (producer : ParsedExpr → Bool) (excludes : producer e = false)
    (x : ParsedExpr) (member : x ∈ line.filter producer) :
    WelcomeRowHasNoLm1Destination x := by
  refine rows x (List.mem_of_mem_filter member) ?_
  intro same
  rw [same] at member
  have keeps : producer e = true := (List.mem_filter.mp member).2
  rw [excludes] at keeps
  simp at keeps

/-! ### 5.5 The `msl`/`msr` writer case -/

/-- **The `msl`/`msr` writer obligation holds.**  The writer's stage list is the
row's own shaped list (`welcomePEMslMsrCyclesShape` through the exposure), and
every other stage list is `.lm1`-free by the writer's uniqueness. -/
theorem welcomePEMslMsrWriterShapeObligation : WelcomePEMslMsrWriterShapeObligation := by
  intro expressions unrefuted ⟨e, eMem, eWriter, isMsl⟩
  apply welcomePEWriteShape_of_commit_shape
  intro next step
  have executed := welcomeSealed_step_ok step
  simp only [executeNormalizedLine, NormalizedLine.toInstruction?,
    Issue.InstructionLine.toNormalizedLine] at executed
  obtain ⟨accepted, waits, unsupported, supported⟩ :=
    executeIntegerProducerInstructionLine_pe_conditions expressions
      (welcomeInitialState welcomeZeroWords) next executed
  obtain ⟨nextPEs, nextMsl, nextRelu, nextBlockFloat, afterMatrix, nextShared, nextBroadcast,
    walkExecuted, mslExecuted, reluExecuted, blockExecuted, matrixExecuted, sharedExecuted,
    l1Executed, nextEq⟩ :=
    executeIntegerProducerInstructionLine_pe_stages_exists expressions
      (welcomeInitialState welcomeZeroWords) next accepted waits unsupported supported executed
  have rows := welcomeLm1Writer_rows expressions unrefuted e eMem eWriter
  have eNodup := welcomeLm1Writer_nodup expressions unrefuted e eMem
  obtain ⟨eReluFalse, eBlockFalse, eMatrixFalse, eL1False, eFloatFalse, eIntFalse,
    eMwriteFalse, eL2False⟩ := welcomeMslMsr_stageProfile e isMsl
  have eFilterMem : e ∈ (expressions.map NormalizedExpr.toParsed).filter
      parsedExprIsMslMsrProducer :=
    List.mem_filter.mpr ⟨eMem, isMsl⟩
  have mslFilter : (expressions.map NormalizedExpr.toParsed).filter
      parsedExprIsMslMsrProducer = [e] :=
    mslMsrFilter_singleton _ e eFilterMem
      (mslMsrFilter_length_le_one (welcomeInitialState welcomeZeroWords) nextPEs nextMsl
        (expressions.map NormalizedExpr.toParsed) _ _ mslExecuted)
  obtain ⟨mslWrites, mslCommit, mslShape⟩ :=
    executeParsedMslMsrProducers_shape_of_singleton (welcomeInitialState welcomeZeroWords)
      nextPEs nextMsl (expressions.map NormalizedExpr.toParsed) e _ _ mslFilter eNodup
      mslExecuted
  have intRows : ∀ expression ∈ (expressions.map NormalizedExpr.toParsed).filter
      parsedExprIsIntegerMatrixReadStageInput,
      expression.op = .noforward ∨ (∃ tag : Fin 256, expression.op = .wait tag) ∨
        WelcomeRowHasNoLm1Destination expression := by
    intro expression member
    refine Or.inr (Or.inr ?_)
    refine rows expression (List.mem_of_mem_filter member) ?_
    intro same
    rw [same] at member
    have keeps := (List.mem_filter.mp member).2
    rw [eIntFalse] at keeps
    simp at keeps
  have floatRows : ∀ expression ∈ (expressions.map NormalizedExpr.toParsed).filter
      parsedExprIsSupportedFloatMAUProducer, WelcomeRowHasNoLm1Destination expression :=
    fun expression member => stageFilter_noLm1_of_rows _ e rows
      parsedExprIsSupportedFloatMAUProducer eFloatFalse expression member
  obtain ⟨intWrites, floatWrites, slots, bars, intPrep, intCommit, intFree, floatFree⟩ :=
    executeIntegerProducerLineAtPEs_zero_prepared_float_clean_of_line_split expressions nextPEs
      intRows floatRows walkExecuted
  obtain ⟨reluWrites, reluCommit, reluFree⟩ :=
    executeParsedFloatReluProducers_clean_commit (welcomeInitialState welcomeZeroWords)
      nextMsl nextRelu (expressions.map NormalizedExpr.toParsed) _ _
      (fun expression member => stageFilter_noLm1_of_rows _ e rows
        parsedExprIsFloatReluProducer eReluFalse expression member) reluExecuted
  obtain ⟨blockWrites, blockCommit, blockFree⟩ :=
    executeParsedBlockFloatProducer_clean_commit (welcomeInitialState welcomeZeroWords)
      nextRelu nextBlockFloat (expressions.map NormalizedExpr.toParsed) _ _
      (fun expression member => stageFilter_noLm1_of_rows _ e rows
        parsedExprIsBlockFloatProducer eBlockFalse expression member) blockExecuted
  obtain ⟨matrixWrites, matrixCommit, matrixFree⟩ :=
    executeParsedMatrixMAUAndWrites_clean_commit (welcomeInitialState welcomeZeroWords)
      nextBlockFloat afterMatrix (expressions.map NormalizedExpr.toParsed) _ _
      (fun expression member => stageFilter_noLm1_of_rows _ e rows
        parsedExprIsMatrixMAUProducer eMatrixFalse expression member) matrixExecuted
  obtain ⟨l1Writes, l1Commit, l1Free⟩ :=
    executeParsedL1ToPEProducers_clean_commit (welcomeInitialState welcomeZeroWords)
      nextShared nextBroadcast (expressions.map NormalizedExpr.toParsed) _ _ _
      (fun expression member => stageFilter_noLm1_of_rows _ e rows
        parsedExprIsL1ToPEProducer eL1False expression member) l1Executed
  have sharedFrame : nextShared.peRegisters welcomePE = afterMatrix.peRegisters welcomePE :=
    congrFun (executeParsedSharedBlockProducers_peRegisters (welcomeInitialState welcomeZeroWords)
      afterMatrix nextShared (expressions.map NormalizedExpr.toParsed)
      (!(expressions.any (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed)))
      sharedExecuted) welcomePE
  have commitEq := executeIntegerProducerInstructionLine_pe_commit_split nextPEs nextMsl
    nextRelu nextBlockFloat afterMatrix nextShared nextBroadcast next (by rw [nextEq])
    (intWrites ++ floatWrites) mslWrites reluWrites blockWrites matrixWrites l1Writes
    intCommit mslCommit reluCommit blockCommit matrixCommit sharedFrame l1Commit
  exact ⟨(intWrites ++ floatWrites) ++ mslWrites ++ reluWrites ++ blockWrites ++
    matrixWrites ++ l1Writes, commitEq,
    lm1WritesShape_of_six_second (intWrites ++ floatWrites) mslWrites reluWrites blockWrites
      matrixWrites l1Writes (lm1FreePreparedWrites_append intFree floatFree) mslShape reluFree
      blockFree matrixFree l1Free⟩

/-- **A length-one filter containing `e` is `[e]`.** -/
theorem filter_singleton_of_length_le_one {α : Type} (producer : α → Bool)
    (items : List α) (e : α) (member : e ∈ items.filter producer)
    (short : (items.filter producer).length ≤ 1) :
    items.filter producer = [e] := by
  cases filtered : items.filter producer with
  | nil => rw [filtered] at member; simp at member
  | cons expression rest =>
      cases rest with
      | nil =>
          rw [filtered] at member
          simp only [List.mem_singleton] at member
          rw [member]
      | cons second remaining =>
          rw [filtered] at short
          simp at short

/-! ### 5.6 The float-relu writer case

The float-relu row shape is `welcomePEFloatReluCyclesShape` (proved in
`WelcomeReluBlockShape.lean`).  Its third-word (`dataCopy`) hypothesis is exactly
the zero-state read-copy fact `welcomeZero_executeParsedFloatRelu_read_copy` of
`WelcomeFrameFix.lean`: at PE 0 with the all-zero state's register file and
forwarding slots, every successful read of the lowered first source has a copied
high word.  The static `.lm1` width and the destination count again come from the
row's no-duplicate-write condition. -/

theorem parsedExprIsFloatReluProducer_cases (expression : ParsedExpr)
    (relu : parsedExprIsFloatReluProducer expression = true) :
    ∃ (name : ParsedAluName) (precision : ParsedPrecision) (unsigned : Bool)
      (arg : Option (Fin 256)), expression.op = .alu name (some precision) unsigned arg := by
  rcases expression with ⟨op, sources, destinations, flush, text⟩
  cases op with
  | alu name precision unsigned arg =>
      cases precision with
      | none => simp [parsedExprIsFloatReluProducer] at relu
      | some precision => exact ⟨name, precision, unsigned, arg, rfl⟩
  | immediate value unsigned => simp [parsedExprIsFloatReluProducer] at relu
  | zero => simp [parsedExprIsFloatReluProducer] at relu
  | mau precision matrix kind half round => simp [parsedExprIsFloatReluProducer] at relu
  | matrixWrite precision => simp [parsedExprIsFloatReluProducer] at relu
  | matrixRead precision => simp [parsedExprIsFloatReluProducer] at relu
  | wait tag => simp [parsedExprIsFloatReluProducer] at relu
  | noforward => simp [parsedExprIsFloatReluProducer] at relu
  | l1bm operation => simp [parsedExprIsFloatReluProducer] at relu
  | l2bm operation => simp [parsedExprIsFloatReluProducer] at relu

theorem welcomeFloatRelu_stageProfile (expression : ParsedExpr)
    (relu : parsedExprIsFloatReluProducer expression = true) :
    parsedExprIsMslMsrProducer expression = false ∧
      parsedExprIsBlockFloatProducer expression = false ∧
      parsedExprIsMatrixMAUProducer expression = false ∧
      parsedExprIsL1ToPEProducer expression = false ∧
      parsedExprIsSupportedFloatMAUProducer expression = false ∧
      parsedExprIsIntegerMatrixReadStageInput expression = false ∧
      parsedExprIsMatrixWriteProducer expression = false ∧
      parsedExprIsL2BMProducer expression = false := by
  have intFalse : parsedExprIsIntegerMatrixReadStageInput expression = false := by
    unfold parsedExprIsIntegerMatrixReadStageInput
    rw [relu]
    simp
  rcases expression with ⟨op, sources, destinations, flush, text⟩
  cases op with
  | alu name precision unsigned arg =>
      cases precision with
      | none => simp [parsedExprIsFloatReluProducer] at relu
      | some precision =>
          cases name <;>
            simp_all [relu, parsedExprIsFloatReluProducer, parsedExprIsMslMsrProducer,
              parsedExprIsBlockFloatProducer, parsedExprIsMatrixMAUProducer,
              parsedExprIsL1ToPEProducer, parsedExprIsSupportedFloatMAUProducer,
              parsedExprIsMatrixWriteProducer, parsedExprIsL2BMProducer, intFalse]
  | immediate value unsigned =>
      simp [parsedExprIsFloatReluProducer] at relu
  | zero => simp [parsedExprIsFloatReluProducer] at relu
  | mau precision matrix kind half round =>
      simp [parsedExprIsFloatReluProducer] at relu
  | matrixWrite precision => simp [parsedExprIsFloatReluProducer] at relu
  | matrixRead precision => simp [parsedExprIsFloatReluProducer] at relu
  | wait tag => simp [parsedExprIsFloatReluProducer] at relu
  | noforward => simp [parsedExprIsFloatReluProducer] at relu
  | l1bm operation => simp [parsedExprIsFloatReluProducer] at relu
  | l2bm operation => simp [parsedExprIsFloatReluProducer] at relu

/-- **The float-relu executor exposes its cycle fold.** -/
theorem executeParsedFloatReluAtPE_runCycles_exists
    (readState currentState : State) (expression : ParsedExpr) (pe : PEId)
    (noForward hasSingleLineMask : Bool) (next : State)
    (executed : executeParsedFloatReluAtPE readState currentState expression pe noForward
      hasSingleLineMask = .ok next) :
    ∃ (registers : IntegerRegisterFiles) (bar0 bar1 : BitVec 12)
      (outputs : Fin 4 → IntegerALU.Bus),
      executeParsedFloatReluAtPE.runCycles readState currentState expression pe
        hasSingleLineMask (ParsedIntegerContext.ofLinearIndex pe)
        { ParsedIntegerContext.ofLinearIndex pe with
          bar0 := (readState.peContext pe).bar0
          bar1 := (readState.peContext pe).bar1
          tWord := (readState.peContext pe).tWord }
        [0, 1, 2, 3] (currentState.peRegisters pe) (readState.peContext pe).bar0
        (readState.peContext pe).bar1 (fun _ => (⟨0, 0⟩ : IntegerALU.Bus)) =
          .ok (registers, bar0, bar1, outputs) ∧
      next.peRegisters pe = registers := by
  rw [executeParsedFloatReluAtPE.eq_1] at executed
  dsimp only at executed
  split at executed
  · simp at executed
  · simp at executed
  · rename_i registers bar0 bar1 outputs ran
    rw [Id.run_pure] at executed
    simp only [StepResult.ok.injEq] at executed
    exact ⟨registers, bar0, bar1, outputs, ran, by subst executed; simp⟩

/-- **The float-relu row shape at PE 0 from the all-zero read state.** -/
theorem executeParsedFloatReluAtPE_pe_shape_at_zero
    (state next : State) (expression : ParsedExpr) (noForward hasSingleLineMask : Bool)
    (nodup : (expression.toIssueExpr 0).writeBanks.Nodup)
    (executed : executeParsedFloatReluAtPE (welcomeInitialState welcomeZeroWords) state
      expression welcomePE noForward hasSingleLineMask = .ok next) :
    ∃ writes, next.peRegisters welcomePE =
      commitParsedMaskedWrites (state.peRegisters welcomePE) writes ∧
      Lm1WritesShape writes := by
  obtain ⟨registers, bar0, bar1, outputs, ran, finalEq⟩ :=
    executeParsedFloatReluAtPE_runCycles_exists (welcomeInitialState welcomeZeroWords) state
      expression welcomePE noForward hasSingleLineMask next executed
  have staticWidth : ∀ cycle ∈ List.finRange 4, ∀ accesses : ParsedFloatReluAccesses,
      lowerParsedFloatRelu? expression
        { ({ ParsedIntegerContext.ofLinearIndex welcomePE with
            bar0 := ((welcomeInitialState welcomeZeroWords).peContext welcomePE).bar0
            bar1 := ((welcomeInitialState welcomeZeroWords).peContext welcomePE).bar1
            tWord := ((welcomeInitialState welcomeZeroWords).peContext welcomePE).tWord } :
              ParsedIntegerContext) with cycle := cycle } = some accesses →
      ∀ destination ∈ accesses.destinations,
        ∀ (bank : PEMemory.Bank) (width : PEMemory.Width),
          ParsedOperand.directDestinationBankWidth? destination = some (bank, width) →
            bank = PEMemory.Bank.lm1 →
              width = (lm1StaticWidth expression).getD PEMemory.Width.word := by
    intro cycle _ accesses lowered destination member bank width resolved bankEq
    have destinationsEq := lowerParsedFloatRelu?_destinations expression
      { ({ ParsedIntegerContext.ofLinearIndex welcomePE with
          bar0 := ((welcomeInitialState welcomeZeroWords).peContext welcomePE).bar0
          bar1 := ((welcomeInitialState welcomeZeroWords).peContext welcomePE).bar1
          tWord := ((welcomeInitialState welcomeZeroWords).peContext welcomePE).tWord } :
            ParsedIntegerContext) with cycle := cycle } accesses lowered
    rw [destinationsEq] at member
    rw [bankEq] at resolved
    exact lm1StaticWidth_spec expression nodup destination member width resolved
  have countBound : ∀ cycle ∈ List.finRange 4, ∀ accesses : ParsedFloatReluAccesses,
      lowerParsedFloatRelu? expression
        { ({ ParsedIntegerContext.ofLinearIndex welcomePE with
            bar0 := ((welcomeInitialState welcomeZeroWords).peContext welcomePE).bar0
            bar1 := ((welcomeInitialState welcomeZeroWords).peContext welcomePE).bar1
            tWord := ((welcomeInitialState welcomeZeroWords).peContext welcomePE).tWord } :
              ParsedIntegerContext) with cycle := cycle } = some accesses →
      (accesses.destinations.filter ParsedOperand.isLm1MemoryDestination).length ≤ 1 := by
    intro cycle _ accesses lowered
    rw [lowerParsedFloatRelu?_destinations expression
      { ({ ParsedIntegerContext.ofLinearIndex welcomePE with
          bar0 := ((welcomeInitialState welcomeZeroWords).peContext welcomePE).bar0
          bar1 := ((welcomeInitialState welcomeZeroWords).peContext welcomePE).bar1
          tWord := ((welcomeInitialState welcomeZeroWords).peContext welcomePE).tWord } :
            ParsedIntegerContext) with cycle := cycle } accesses lowered]
    exact lm1Destinations_count_le_one expression 0 nodup
  have dataCopy : ∀ cycle ∈ List.finRange 4, ∀ accesses : ParsedFloatReluAccesses,
      lowerParsedFloatRelu? expression
        { ({ ParsedIntegerContext.ofLinearIndex welcomePE with
            bar0 := ((welcomeInitialState welcomeZeroWords).peContext welcomePE).bar0
            bar1 := ((welcomeInitialState welcomeZeroWords).peContext welcomePE).bar1
            tWord := ((welcomeInitialState welcomeZeroWords).peContext welcomePE).tWord } :
              ParsedIntegerContext) with cycle := cycle } = some accesses →
      ∀ sourceA : IntegerALU.Bus,
        ParsedIntegerInput.readWithForwarding
          ((welcomeInitialState welcomeZeroWords).peRegisters welcomePE)
          (stateForwardingSlots (welcomeInitialState welcomeZeroWords) welcomePE) cycle
          accesses.sourceA = .ok sourceA →
        IsWelcomeCopy (sourceA.low.extractLsb' 32 32) := by
    intro cycle _ accesses lowered sourceA read
    exact welcomeZero_executeParsedFloatRelu_read_copy cycle expression accesses lowered sourceA read
  obtain ⟨writes, committed, shape⟩ :=
    welcomePEFloatReluCyclesShape (welcomeInitialState welcomeZeroWords) state expression
      welcomePE hasSingleLineMask (ParsedIntegerContext.ofLinearIndex welcomePE)
      { ParsedIntegerContext.ofLinearIndex welcomePE with
        bar0 := ((welcomeInitialState welcomeZeroWords).peContext welcomePE).bar0
        bar1 := ((welcomeInitialState welcomeZeroWords).peContext welcomePE).bar1
        tWord := ((welcomeInitialState welcomeZeroWords).peContext welcomePE).tWord }
      ((lm1StaticWidth expression).getD PEMemory.Width.word) staticWidth countBound dataCopy
      (state.peRegisters welcomePE) ((welcomeInitialState welcomeZeroWords).peContext welcomePE).bar0
      ((welcomeInitialState welcomeZeroWords).peContext welcomePE).bar1
      (fun _ => ⟨0, 0⟩) registers bar0 bar1 outputs ran
  exact ⟨writes, by rw [finalEq]; exact committed, shape⟩

/-- **A float-relu walk leaves every unvisited PE untouched.** -/
theorem executeParsedFloatReluAtPEs_peRegisters_not_mem
    (readState : State) (expression : ParsedExpr) (noForward hasSingleLineMask : Bool) :
    ∀ (pes : List PEId) (state next : State) (target : PEId), target ∉ pes →
      executeParsedFloatReluAtPEs readState state expression pes noForward hasSingleLineMask =
        .ok next →
      next.peRegisters target = state.peRegisters target := by
  intro pes
  induction pes with
  | nil =>
      intro state next target absent executed
      simp only [executeParsedFloatReluAtPEs, StepResult.ok.injEq] at executed
      subst executed
      rfl
  | cons pe rest ih =>
      intro state next target absent executed
      simp only [executeParsedFloatReluAtPEs] at executed
      split at executed
      · simp at executed
      · simp at executed
      · rename_i middle headExecuted
        have different : target ≠ pe := by
          intro same
          exact absent (same ▸ List.mem_cons_self ..)
        have headFrame := executeParsedFloatReluAtPE_peRegisters_other readState state middle
          expression pe target different noForward hasSingleLineMask headExecuted
        have tailAbsent : target ∉ rest := fun member =>
          absent (List.mem_cons_of_mem _ member)
        rw [ih middle next target tailAbsent executed, headFrame]

/-- **The float-relu walk shape at a visited PE**, from the row shape at that PE
only.  The walk is duplicate-free, so the target's own step is the only one that
writes into the target's file. -/
theorem executeParsedFloatReluAtPEs_shape
    (readState : State) (expression : ParsedExpr) (target : PEId)
    (noForward hasSingleLineMask : Bool)
    (rowShape : ∀ (state nextState : State),
      executeParsedFloatReluAtPE readState state expression target noForward
        hasSingleLineMask = .ok nextState →
      ∃ writes, nextState.peRegisters target =
        commitParsedMaskedWrites (state.peRegisters target) writes ∧
        Lm1WritesShape writes) :
    ∀ (pes : List PEId) (pesNodup : pes.Nodup) (state next : State), target ∈ pes →
      executeParsedFloatReluAtPEs readState state expression pes noForward hasSingleLineMask =
        .ok next →
      ∃ writes, next.peRegisters target =
        commitParsedMaskedWrites (state.peRegisters target) writes ∧
        Lm1WritesShape writes := by
  intro pes
  induction pes with
  | nil => intro _ state next member; simp at member
  | cons pe rest ih =>
      intro pesNodup state next member executed
      obtain ⟨peNotRest, restNodup⟩ := List.nodup_cons.mp pesNodup
      simp only [executeParsedFloatReluAtPEs] at executed
      split at executed
      · simp at executed
      · simp at executed
      · rename_i middle headExecuted
        by_cases same : target = pe
        · subst target
          obtain ⟨headWrites, headCommit, headShape⟩ :=
            rowShape state middle headExecuted
          have absent : pe ∉ rest := peNotRest
          have tailFrame := executeParsedFloatReluAtPEs_peRegisters_not_mem readState expression
            noForward hasSingleLineMask rest middle next pe absent executed
          refine ⟨headWrites, ?_, headShape⟩
          rw [tailFrame]
          exact headCommit
        · have memberRest : target ∈ rest := by
            rcases List.mem_cons.mp member with same' | member
            · exact absurd same' same
            · exact member
          obtain ⟨tailWrites, tailCommit, tailShape⟩ :=
            ih restNodup middle next memberRest executed
          have headFrame := executeParsedFloatReluAtPE_peRegisters_other readState state middle
            expression pe target same noForward hasSingleLineMask headExecuted
          exact ⟨tailWrites, by rw [tailCommit, headFrame], tailShape⟩

/-- **A successful float-relu stage has a singleton producer filter.** -/
theorem floatReluFilter_length_le_one
    (readState currentState next : State) (expressions : List ParsedExpr)
    (noForward hasSingleLineMask : Bool)
    (executed : executeParsedFloatReluProducers readState currentState expressions noForward
      hasSingleLineMask = .ok next) :
    (expressions.filter parsedExprIsFloatReluProducer).length ≤ 1 := by
  cases filtered : expressions.filter parsedExprIsFloatReluProducer with
  | nil => simp
  | cons expression rest =>
      cases rest with
      | nil => simp
      | cons second remaining =>
          simp only [executeParsedFloatReluProducers, filtered] at executed
          simp at executed

/-- **The float-relu producer stage's PE 0 shape, from the singleton filter.** -/
theorem executeParsedFloatReluProducers_shape_of_singleton
    (currentState next : State) (expressions : List ParsedExpr) (e : ParsedExpr)
    (noForward hasSingleLineMask : Bool)
    (filtered : expressions.filter parsedExprIsFloatReluProducer = [e])
    (nodup : (e.toIssueExpr 0).writeBanks.Nodup)
    (executed : executeParsedFloatReluProducers (welcomeInitialState welcomeZeroWords)
      currentState expressions noForward hasSingleLineMask = .ok next) :
    ∃ writes, next.peRegisters welcomePE =
      commitParsedMaskedWrites (currentState.peRegisters welcomePE) writes ∧
      Lm1WritesShape writes := by
  simp only [executeParsedFloatReluProducers, filtered] at executed
  exact executeParsedFloatReluAtPEs_shape (welcomeInitialState welcomeZeroWords) e welcomePE
    noForward hasSingleLineMask
    (fun state nextState executed =>
      executeParsedFloatReluAtPE_pe_shape_at_zero state nextState e noForward hasSingleLineMask
        nodup executed)
    (List.finRange 4096) (List.nodup_finRange 4096) currentState next
    (List.mem_finRange welcomePE) executed

/-- **The float-relu writer obligation holds.** -/
theorem welcomePEFloatReluWriterShapeObligation : WelcomePEFloatReluWriterShapeObligation := by
  intro expressions unrefuted ⟨e, eMem, eWriter, isRelu⟩
  apply welcomePEWriteShape_of_commit_shape
  intro next step
  have executed := welcomeSealed_step_ok step
  simp only [executeNormalizedLine, NormalizedLine.toInstruction?,
    Issue.InstructionLine.toNormalizedLine] at executed
  obtain ⟨accepted, waits, unsupported, supported⟩ :=
    executeIntegerProducerInstructionLine_pe_conditions expressions
      (welcomeInitialState welcomeZeroWords) next executed
  obtain ⟨nextPEs, nextMsl, nextRelu, nextBlockFloat, afterMatrix, nextShared, nextBroadcast,
    walkExecuted, mslExecuted, reluExecuted, blockExecuted, matrixExecuted, sharedExecuted,
    l1Executed, nextEq⟩ :=
    executeIntegerProducerInstructionLine_pe_stages_exists expressions
      (welcomeInitialState welcomeZeroWords) next accepted waits unsupported supported executed
  have rows := welcomeLm1Writer_rows expressions unrefuted e eMem eWriter
  have eNodup := welcomeLm1Writer_nodup expressions unrefuted e eMem
  obtain ⟨eMslFalse, eBlockFalse, eMatrixFalse, eL1False, eFloatFalse, eIntFalse,
    eMwriteFalse, eL2False⟩ := welcomeFloatRelu_stageProfile e isRelu
  have eFilterMem : e ∈ (expressions.map NormalizedExpr.toParsed).filter
      parsedExprIsFloatReluProducer :=
    List.mem_filter.mpr ⟨eMem, isRelu⟩
  have reluFilter : (expressions.map NormalizedExpr.toParsed).filter
      parsedExprIsFloatReluProducer = [e] :=
    filter_singleton_of_length_le_one parsedExprIsFloatReluProducer _ e eFilterMem
      (floatReluFilter_length_le_one (welcomeInitialState welcomeZeroWords) nextMsl nextRelu
        (expressions.map NormalizedExpr.toParsed) _ _ reluExecuted)
  obtain ⟨reluWrites, reluCommit, reluShape⟩ :=
    executeParsedFloatReluProducers_shape_of_singleton nextMsl nextRelu
      (expressions.map NormalizedExpr.toParsed) e _ _ reluFilter eNodup reluExecuted
  have intRows : ∀ expression ∈ (expressions.map NormalizedExpr.toParsed).filter
      parsedExprIsIntegerMatrixReadStageInput,
      expression.op = .noforward ∨ (∃ tag : Fin 256, expression.op = .wait tag) ∨
        WelcomeRowHasNoLm1Destination expression := by
    intro expression member
    refine Or.inr (Or.inr ?_)
    refine rows expression (List.mem_of_mem_filter member) ?_
    intro same
    rw [same] at member
    have keeps := (List.mem_filter.mp member).2
    rw [eIntFalse] at keeps
    simp at keeps
  have floatRows : ∀ expression ∈ (expressions.map NormalizedExpr.toParsed).filter
      parsedExprIsSupportedFloatMAUProducer, WelcomeRowHasNoLm1Destination expression :=
    fun expression member => stageFilter_noLm1_of_rows _ e rows
      parsedExprIsSupportedFloatMAUProducer eFloatFalse expression member
  obtain ⟨intWrites, floatWrites, slots, bars, intPrep, intCommit, intFree, floatFree⟩ :=
    executeIntegerProducerLineAtPEs_zero_prepared_float_clean_of_line_split expressions nextPEs
      intRows floatRows walkExecuted
  obtain ⟨mslWrites, mslCommit, mslFree⟩ :=
    executeParsedMslMsrProducers_clean_commit (welcomeInitialState welcomeZeroWords)
      nextPEs nextMsl (expressions.map NormalizedExpr.toParsed) _ _
      (fun expression member => stageFilter_noLm1_of_rows _ e rows
        parsedExprIsMslMsrProducer eMslFalse expression member) mslExecuted
  obtain ⟨blockWrites, blockCommit, blockFree⟩ :=
    executeParsedBlockFloatProducer_clean_commit (welcomeInitialState welcomeZeroWords)
      nextRelu nextBlockFloat (expressions.map NormalizedExpr.toParsed) _ _
      (fun expression member => stageFilter_noLm1_of_rows _ e rows
        parsedExprIsBlockFloatProducer eBlockFalse expression member) blockExecuted
  obtain ⟨matrixWrites, matrixCommit, matrixFree⟩ :=
    executeParsedMatrixMAUAndWrites_clean_commit (welcomeInitialState welcomeZeroWords)
      nextBlockFloat afterMatrix (expressions.map NormalizedExpr.toParsed) _ _
      (fun expression member => stageFilter_noLm1_of_rows _ e rows
        parsedExprIsMatrixMAUProducer eMatrixFalse expression member) matrixExecuted
  obtain ⟨l1Writes, l1Commit, l1Free⟩ :=
    executeParsedL1ToPEProducers_clean_commit (welcomeInitialState welcomeZeroWords)
      nextShared nextBroadcast (expressions.map NormalizedExpr.toParsed) _ _ _
      (fun expression member => stageFilter_noLm1_of_rows _ e rows
        parsedExprIsL1ToPEProducer eL1False expression member) l1Executed
  have sharedFrame : nextShared.peRegisters welcomePE = afterMatrix.peRegisters welcomePE :=
    congrFun (executeParsedSharedBlockProducers_peRegisters (welcomeInitialState welcomeZeroWords)
      afterMatrix nextShared (expressions.map NormalizedExpr.toParsed)
      (!(expressions.any (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed)))
      sharedExecuted) welcomePE
  have commitEq := executeIntegerProducerInstructionLine_pe_commit_split nextPEs nextMsl
    nextRelu nextBlockFloat afterMatrix nextShared nextBroadcast next (by rw [nextEq])
    (intWrites ++ floatWrites) mslWrites reluWrites blockWrites matrixWrites l1Writes
    intCommit mslCommit reluCommit blockCommit matrixCommit sharedFrame l1Commit
  exact ⟨(intWrites ++ floatWrites) ++ mslWrites ++ reluWrites ++ blockWrites ++
    matrixWrites ++ l1Writes, commitEq,
    lm1WritesShape_of_six_third (intWrites ++ floatWrites) mslWrites reluWrites blockWrites
      matrixWrites l1Writes (lm1FreePreparedWrites_append intFree floatFree) mslFree reluShape
      blockFree matrixFree l1Free⟩

/-! ### 5.7 The special-ALU writer case from the block-float remainder -/

/-- **The special-ALU writer obligation holds modulo the block-float family.**
The `msl`/`msr` and float-relu writer families are proved above, so
`WelcomePESpecialALUWriterShapeObligation` follows from the block-float writer
obligation alone. -/
theorem welcomePESpecialALUWriterShapeObligation_of_block
    (block : WelcomePEBlockFloatWriterShapeObligation) :
    WelcomePESpecialALUWriterShapeObligation :=
  welcomePESpecialALUWriterShapeObligation_of_three welcomePEMslMsrWriterShapeObligation
    welcomePEFloatReluWriterShapeObligation block

/-! ### 5.8 The block-float fold at PE 0

`executeParsedBlockFloatProducer` (with a singleton filter) walks
`allMABCoordinates`.  The coordinate `⟨0,0,0,0⟩` is the head of that list and the
only coordinate one of whose four PEs is PE 0 (`physicalPEId_welcomePE_eq`), so
the PE 0 file is the commit of the row's coordinate shape and the rest of the
walk is a frame. -/

theorem allMABCoordinates_eq_zero_cons :
    allMABCoordinates = (⟨0, 0, 0, 0⟩ : MABCoordinate) :: allMABCoordinates.drop 1 := rfl

theorem zero_not_mem_allMABCoordinates_drop :
    (⟨0, 0, 0, 0⟩ : MABCoordinate) ∉ allMABCoordinates.drop 1 := by
  set_option maxRecDepth 100000 in
  set_option maxHeartbeats 2000000 in
  decide

/-- **The block-float walk leaves every untouched PE alone.** -/
theorem executeParsedBlockFloatAtMABs_peRegisters_not_mem
    (readState : State) (expression : ParsedExpr) (noForward hasSingleLineMask : Bool)
    (p : PEId) :
    ∀ (coordinates : List MABCoordinate) (state next : State),
      (∀ coordinate ∈ coordinates, ∀ pe : Fin 4, physicalPEId coordinate pe ≠ p) →
      executeParsedBlockFloatAtMABs readState state expression coordinates noForward
        hasSingleLineMask = .ok next →
      next.peRegisters p = state.peRegisters p := by
  intro coordinates
  induction coordinates with
  | nil =>
      intro state next untouched executed
      simp only [executeParsedBlockFloatAtMABs.eq_1, StepResult.ok.injEq] at executed
      subst executed
      rfl
  | cons coordinate rest ih =>
      intro state next untouched executed
      rw [executeParsedBlockFloatAtMABs.eq_2] at executed
      split at executed
      · simp at executed
      · simp at executed
      · rename_i middle ran
        have headFrame := executeParsedBlockFloatAtMAB_peRegisters_frame readState state
          expression coordinate noForward hasSingleLineMask p
          (fun pe => Ne.symm (untouched coordinate (by simp) pe)) middle ran
        exact (ih middle next
          (fun item member => untouched item (List.mem_cons_of_mem _ member)) executed).trans
          headFrame

/-- **The block-float walk shape at PE 0.**  The head coordinate `⟨0,0,0,0⟩` is
the only one that touches PE 0; the rest of the walk is a frame. -/
theorem executeParsedBlockFloatAtMABs_shape_at_zero
    (readState : State) (expression : ParsedExpr) (noForward hasSingleLineMask : Bool)
    (rest : List MABCoordinate) (currentState next : State)
    (rowShape : ∀ (state' next' : State),
      executeParsedBlockFloatAtMAB readState state' expression ⟨0, 0, 0, 0⟩ noForward
        hasSingleLineMask = .ok next' →
      ∃ writes, next'.peRegisters welcomePE =
        commitParsedMaskedWrites (state'.peRegisters welcomePE) writes ∧
        Lm1WritesShape writes)
    (restUntouched : ∀ coordinate ∈ rest, ∀ pe : Fin 4,
      physicalPEId coordinate pe ≠ welcomePE)
    (executed : executeParsedBlockFloatAtMABs readState currentState expression
      (⟨0, 0, 0, 0⟩ :: rest) noForward hasSingleLineMask = .ok next) :
    ∃ writes, next.peRegisters welcomePE =
      commitParsedMaskedWrites (currentState.peRegisters welcomePE) writes ∧
      Lm1WritesShape writes := by
  rw [executeParsedBlockFloatAtMABs.eq_2] at executed
  split at executed
  · simp at executed
  · simp at executed
  · rename_i middle ran
    obtain ⟨writes, committed, shape⟩ := rowShape currentState middle ran
    have tailFrame := executeParsedBlockFloatAtMABs_peRegisters_not_mem readState expression
      noForward hasSingleLineMask welcomePE rest middle next restUntouched executed
    exact ⟨writes, by rw [tailFrame]; exact committed, shape⟩

/-- **The block-float coordinate `⟨0,0,0,0⟩` shape at PE 0.** -/
theorem executeParsedBlockFloatAtMAB_zero_shape
    (readState state next : State) (expression : ParsedExpr)
    (noForward hasSingleLineMask : Bool)
    (accesses : ParsedBlockFloatAccesses) (w : PEMemory.Width)
    (lowered : lowerParsedBlockFloat? expression = some accesses)
    (staticWidth : ∀ destination ∈ accesses.destinations,
      ∀ (bank : PEMemory.Bank) (width : PEMemory.Width),
        ParsedOperand.directDestinationBankWidth? destination = some (bank, width) →
          bank = PEMemory.Bank.lm1 → width = w)
    (countBound : (accesses.destinations.filter ParsedOperand.isLm1MemoryDestination).length ≤ 1)
    (lowPrecision : accesses.precision = .d ∨ accesses.precision = .f ∨ accesses.precision = .g)
    (executed : executeParsedBlockFloatAtMAB readState state expression ⟨0, 0, 0, 0⟩
      noForward hasSingleLineMask = .ok next) :
    ∃ writes, next.peRegisters welcomePE =
      commitParsedMaskedWrites (state.peRegisters welcomePE) writes ∧
      Lm1WritesShape writes := by
  obtain ⟨writes, committed, shape⟩ :=
    welcomePEBlockFloatMabShape_of_precision_low_zero readState state expression ⟨0, 0, 0, 0⟩
      noForward hasSingleLineMask next accesses w lowered staticWidth countBound lowPrecision
      executed 0
  rw [physicalPEId_zero_zero] at committed
  exact ⟨writes, committed, shape⟩

/-- **The block-float producer's accesses come from its lowering.** -/
theorem executeParsedBlockFloatProducer_lowering_exists
    (readState currentState next : State) (expressions : List ParsedExpr) (e : ParsedExpr)
    (noForward hasSingleLineMask : Bool)
    (filtered : expressions.filter parsedExprIsBlockFloatProducer = [e])
    (executed : executeParsedBlockFloatProducer readState currentState expressions noForward
      hasSingleLineMask = .ok next) :
    ∃ accesses, lowerParsedBlockFloat? e = some accesses := by
  cases lowered : lowerParsedBlockFloat? e with
  | none =>
      simp only [executeParsedBlockFloatProducer, filtered] at executed
      rw [allMABCoordinates_eq_zero_cons, executeParsedBlockFloatAtMABs.eq_2] at executed
      rw [executeParsedBlockFloatAtMAB_lowering_failure readState currentState e
        ⟨0, 0, 0, 0⟩ noForward hasSingleLineMask lowered] at executed
      simp at executed
  | some accesses => exact ⟨accesses, rfl⟩

/-- **The block-float stage's PE 0 shape for the low precisions.** -/
theorem executeParsedBlockFloatProducer_shape_of_singleton_low
    (currentState next : State) (expressions : List ParsedExpr) (e : ParsedExpr)
    (noForward hasSingleLineMask : Bool)
    (filtered : expressions.filter parsedExprIsBlockFloatProducer = [e])
    (accesses : ParsedBlockFloatAccesses)
    (lowered : lowerParsedBlockFloat? e = some accesses)
    (lowPrecision : accesses.precision = .d ∨ accesses.precision = .f ∨ accesses.precision = .g)
    (nodup : (e.toIssueExpr 0).writeBanks.Nodup)
    (executed : executeParsedBlockFloatProducer (welcomeInitialState welcomeZeroWords)
      currentState expressions noForward hasSingleLineMask = .ok next) :
    ∃ writes, next.peRegisters welcomePE =
      commitParsedMaskedWrites (currentState.peRegisters welcomePE) writes ∧
      Lm1WritesShape writes := by
  have staticWidth : ∀ destination ∈ accesses.destinations,
      ∀ (bank : PEMemory.Bank) (width : PEMemory.Width),
        ParsedOperand.directDestinationBankWidth? destination = some (bank, width) →
          bank = PEMemory.Bank.lm1 → width = (lm1StaticWidth e).getD PEMemory.Width.word := by
    intro destination member bank width resolved bankEq
    rw [lowerParsedBlockFloat?_destinations e accesses lowered] at member
    rw [bankEq] at resolved
    exact lm1StaticWidth_spec e nodup destination member width resolved
  have countBound : (accesses.destinations.filter ParsedOperand.isLm1MemoryDestination).length ≤ 1 := by
    rw [lowerParsedBlockFloat?_destinations e accesses lowered]
    exact lm1Destinations_count_le_one e 0 nodup
  simp only [executeParsedBlockFloatProducer, filtered] at executed
  rw [allMABCoordinates_eq_zero_cons] at executed
  refine executeParsedBlockFloatAtMABs_shape_at_zero (welcomeInitialState welcomeZeroWords) e
    noForward hasSingleLineMask (allMABCoordinates.drop 1) currentState next ?_ ?_ executed
  · intro state' next' ran
    exact executeParsedBlockFloatAtMAB_zero_shape (welcomeInitialState welcomeZeroWords) state'
      next' e noForward hasSingleLineMask accesses
      ((lm1StaticWidth e).getD PEMemory.Width.word) lowered staticWidth countBound lowPrecision ran
  · intro coordinate member pe same
    exact zero_not_mem_allMABCoordinates_drop
      (by rw [physicalPEId_welcomePE_eq coordinate pe same] at member; exact member)

/-- **A successful block-float stage has a singleton producer filter.** -/
theorem blockFloatFilter_length_le_one
    (readState currentState next : State) (expressions : List ParsedExpr)
    (noForward hasSingleLineMask : Bool)
    (executed : executeParsedBlockFloatProducer readState currentState expressions noForward
      hasSingleLineMask = .ok next) :
    (expressions.filter parsedExprIsBlockFloatProducer).length ≤ 1 := by
  cases filtered : expressions.filter parsedExprIsBlockFloatProducer with
  | nil => simp
  | cons expression rest =>
      cases rest with
      | nil => simp
      | cons second remaining =>
          simp only [executeParsedBlockFloatProducer, filtered] at executed
          simp at executed

/-- **The stage profile of a block-float row.** -/
theorem welcomeBlockFloat_stageProfile (expression : ParsedExpr)
    (block : parsedExprIsBlockFloatProducer expression = true) :
    parsedExprIsMslMsrProducer expression = false ∧
      parsedExprIsFloatReluProducer expression = false ∧
      parsedExprIsMatrixMAUProducer expression = false ∧
      parsedExprIsL1ToPEProducer expression = false ∧
      parsedExprIsSupportedFloatMAUProducer expression = false ∧
      parsedExprIsIntegerMatrixReadStageInput expression = false := by
  have intFalse : parsedExprIsIntegerMatrixReadStageInput expression = false := by
    unfold parsedExprIsIntegerMatrixReadStageInput
    rw [block]
    simp
  rcases expression with ⟨op, sources, destinations, flush, text⟩
  cases op with
  | alu name precision unsigned arg =>
      cases precision with
      | none => simp [parsedExprIsBlockFloatProducer] at block
      | some precision =>
          cases name <;>
            simp_all [block, parsedExprIsBlockFloatProducer, parsedExprIsMslMsrProducer,
              parsedExprIsFloatReluProducer, parsedExprIsMatrixMAUProducer,
              parsedExprIsL1ToPEProducer, parsedExprIsSupportedFloatMAUProducer, intFalse]
  | immediate value unsigned => simp [parsedExprIsBlockFloatProducer] at block
  | zero => simp [parsedExprIsBlockFloatProducer] at block
  | mau precision matrix kind half round =>
      simp [parsedExprIsBlockFloatProducer] at block
  | matrixWrite precision => simp [parsedExprIsBlockFloatProducer] at block
  | matrixRead precision => simp [parsedExprIsBlockFloatProducer] at block
  | wait tag => simp [parsedExprIsBlockFloatProducer] at block
  | noforward => simp [parsedExprIsBlockFloatProducer] at block
  | l1bm operation => simp [parsedExprIsBlockFloatProducer] at block
  | l2bm operation => simp [parsedExprIsBlockFloatProducer] at block

/-- **The block-float low-precision writer case.** -/
def WelcomePEBlockFloatLowPrecisionWriterShapeObligation : Prop :=
  ∀ (expressions : List NormalizedExpr), WelcomePEUnrefuted expressions →
    (∃ e ∈ expressions.map NormalizedExpr.toParsed,
      Issue.Bank.lm1 ∈ (e.toIssueExpr 0).writeBanks ∧
        parsedExprIsBlockFloatProducer e = true ∧
          ∀ (accesses : ParsedBlockFloatAccesses), lowerParsedBlockFloat? e = some accesses →
            accesses.precision = .d ∨ accesses.precision = .f ∨ accesses.precision = .g) →
    WelcomePEWriteShape expressions

/-- **The block-float low-precision writer obligation holds.** -/
theorem welcomePEBlockFloatLowPrecisionWriterShapeObligation :
    WelcomePEBlockFloatLowPrecisionWriterShapeObligation := by
  intro expressions unrefuted ⟨e, eMem, eWriter, isBlock, lowPrecision⟩
  apply welcomePEWriteShape_of_commit_shape
  intro next step
  have executed := welcomeSealed_step_ok step
  simp only [executeNormalizedLine, NormalizedLine.toInstruction?,
    Issue.InstructionLine.toNormalizedLine] at executed
  obtain ⟨accepted, waits, unsupported, supported⟩ :=
    executeIntegerProducerInstructionLine_pe_conditions expressions
      (welcomeInitialState welcomeZeroWords) next executed
  obtain ⟨nextPEs, nextMsl, nextRelu, nextBlockFloat, afterMatrix, nextShared, nextBroadcast,
    walkExecuted, mslExecuted, reluExecuted, blockExecuted, matrixExecuted, sharedExecuted,
    l1Executed, nextEq⟩ :=
    executeIntegerProducerInstructionLine_pe_stages_exists expressions
      (welcomeInitialState welcomeZeroWords) next accepted waits unsupported supported executed
  have rows := welcomeLm1Writer_rows expressions unrefuted e eMem eWriter
  have eNodup := welcomeLm1Writer_nodup expressions unrefuted e eMem
  obtain ⟨eMslFalse, eReluFalse, eMatrixFalse, eL1False, eFloatFalse, eIntFalse⟩ :=
    welcomeBlockFloat_stageProfile e isBlock
  have eFilterMem : e ∈ (expressions.map NormalizedExpr.toParsed).filter
      parsedExprIsBlockFloatProducer :=
    List.mem_filter.mpr ⟨eMem, isBlock⟩
  have blockFilter : (expressions.map NormalizedExpr.toParsed).filter
      parsedExprIsBlockFloatProducer = [e] :=
    filter_singleton_of_length_le_one parsedExprIsBlockFloatProducer _ e eFilterMem
      (blockFloatFilter_length_le_one (welcomeInitialState welcomeZeroWords) nextRelu
        nextBlockFloat (expressions.map NormalizedExpr.toParsed) _ _ blockExecuted)
  obtain ⟨accesses, lowered⟩ :=
    executeParsedBlockFloatProducer_lowering_exists (welcomeInitialState welcomeZeroWords)
      nextRelu nextBlockFloat (expressions.map NormalizedExpr.toParsed) e _ _ blockFilter
      blockExecuted
  obtain ⟨blockWrites, blockCommit, blockShape⟩ :=
    executeParsedBlockFloatProducer_shape_of_singleton_low nextRelu nextBlockFloat
      (expressions.map NormalizedExpr.toParsed) e _ _ blockFilter accesses lowered
      (lowPrecision accesses lowered) eNodup blockExecuted
  have intRows : ∀ expression ∈ (expressions.map NormalizedExpr.toParsed).filter
      parsedExprIsIntegerMatrixReadStageInput,
      expression.op = .noforward ∨ (∃ tag : Fin 256, expression.op = .wait tag) ∨
        WelcomeRowHasNoLm1Destination expression := by
    intro expression member
    refine Or.inr (Or.inr ?_)
    refine rows expression (List.mem_of_mem_filter member) ?_
    intro same
    rw [same] at member
    have keeps := (List.mem_filter.mp member).2
    rw [eIntFalse] at keeps
    simp at keeps
  have floatRows : ∀ expression ∈ (expressions.map NormalizedExpr.toParsed).filter
      parsedExprIsSupportedFloatMAUProducer, WelcomeRowHasNoLm1Destination expression :=
    fun expression member => stageFilter_noLm1_of_rows _ e rows
      parsedExprIsSupportedFloatMAUProducer eFloatFalse expression member
  obtain ⟨intWrites, floatWrites, slots, bars, intPrep, intCommit, intFree, floatFree⟩ :=
    executeIntegerProducerLineAtPEs_zero_prepared_float_clean_of_line_split expressions nextPEs
      intRows floatRows walkExecuted
  obtain ⟨mslWrites, mslCommit, mslFree⟩ :=
    executeParsedMslMsrProducers_clean_commit (welcomeInitialState welcomeZeroWords)
      nextPEs nextMsl (expressions.map NormalizedExpr.toParsed) _ _
      (fun expression member => stageFilter_noLm1_of_rows _ e rows
        parsedExprIsMslMsrProducer eMslFalse expression member) mslExecuted
  obtain ⟨reluWrites, reluCommit, reluFree⟩ :=
    executeParsedFloatReluProducers_clean_commit (welcomeInitialState welcomeZeroWords)
      nextMsl nextRelu (expressions.map NormalizedExpr.toParsed) _ _
      (fun expression member => stageFilter_noLm1_of_rows _ e rows
        parsedExprIsFloatReluProducer eReluFalse expression member) reluExecuted
  obtain ⟨matrixWrites, matrixCommit, matrixFree⟩ :=
    executeParsedMatrixMAUAndWrites_clean_commit (welcomeInitialState welcomeZeroWords)
      nextBlockFloat afterMatrix (expressions.map NormalizedExpr.toParsed) _ _
      (fun expression member => stageFilter_noLm1_of_rows _ e rows
        parsedExprIsMatrixMAUProducer eMatrixFalse expression member) matrixExecuted
  obtain ⟨l1Writes, l1Commit, l1Free⟩ :=
    executeParsedL1ToPEProducers_clean_commit (welcomeInitialState welcomeZeroWords)
      nextShared nextBroadcast (expressions.map NormalizedExpr.toParsed) _ _ _
      (fun expression member => stageFilter_noLm1_of_rows _ e rows
        parsedExprIsL1ToPEProducer eL1False expression member) l1Executed
  have sharedFrame : nextShared.peRegisters welcomePE = afterMatrix.peRegisters welcomePE :=
    congrFun (executeParsedSharedBlockProducers_peRegisters (welcomeInitialState welcomeZeroWords)
      afterMatrix nextShared (expressions.map NormalizedExpr.toParsed)
      (!(expressions.any (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed)))
      sharedExecuted) welcomePE
  have commitEq := executeIntegerProducerInstructionLine_pe_commit_split nextPEs nextMsl
    nextRelu nextBlockFloat afterMatrix nextShared nextBroadcast next (by rw [nextEq])
    (intWrites ++ floatWrites) mslWrites reluWrites blockWrites matrixWrites l1Writes
    intCommit mslCommit reluCommit blockCommit matrixCommit sharedFrame l1Commit
  exact ⟨(intWrites ++ floatWrites) ++ mslWrites ++ reluWrites ++ blockWrites ++
    matrixWrites ++ l1Writes, commitEq,
    lm1WritesShape_of_six_fourth (intWrites ++ floatWrites) mslWrites reluWrites blockWrites
      matrixWrites l1Writes (lm1FreePreparedWrites_append intFree floatFree) mslFree reluFree
      blockShape matrixFree l1Free⟩

/-- **The block-float writer case outside the low precisions.**  This is the
exact remainder of the block-float family.  For a block-float row
`parsedExprIsBlockFloatProducer` admits only the precisions `.d`, `.f`, `.g` and
`.h`, and the lowering preserves the row's precision; so this case is precisely
the `.h`-precision (half) writer. -/
def WelcomePEBlockFloatNonLowWriterShapeObligation : Prop :=
  ∀ (expressions : List NormalizedExpr), WelcomePEUnrefuted expressions →
    (∃ e ∈ expressions.map NormalizedExpr.toParsed,
      Issue.Bank.lm1 ∈ (e.toIssueExpr 0).writeBanks ∧
        parsedExprIsBlockFloatProducer e = true ∧
          ¬ (∀ (accesses : ParsedBlockFloatAccesses), lowerParsedBlockFloat? e = some accesses →
              accesses.precision = .d ∨ accesses.precision = .f ∨ accesses.precision = .g)) →
    WelcomePEWriteShape expressions

/-- **The block-float writer obligation from its low and non-low cases.** -/
theorem welcomePEBlockFloatWriterShapeObligation_of_low_and_nonLow
    (low : WelcomePEBlockFloatLowPrecisionWriterShapeObligation)
    (nonLow : WelcomePEBlockFloatNonLowWriterShapeObligation) :
    WelcomePEBlockFloatWriterShapeObligation := by
  intro expressions unrefuted ⟨e, eMem, eWriter, isBlock⟩
  by_cases lowPrecision : ∀ (accesses : ParsedBlockFloatAccesses),
      lowerParsedBlockFloat? e = some accesses →
        accesses.precision = .d ∨ accesses.precision = .f ∨ accesses.precision = .g
  · exact low expressions unrefuted ⟨e, eMem, eWriter, isBlock, lowPrecision⟩
  · exact nonLow expressions unrefuted ⟨e, eMem, eWriter, isBlock, lowPrecision⟩

/-! ## 6. Status

* `welcomePELm1PhantomWriterProvenance` is proved **unconditionally**: the
  phantom/no-writer case no longer depends on the float-MAU provenance or on an
  integer-stage refinement, both of which are used as lemmas above.
* `welcomePEMslMsrWriterShapeObligation`, `welcomePEFloatReluWriterShapeObligation`
  and `welcomePEBlockFloatLowPrecisionWriterShapeObligation` are proved
  **unconditionally**.  The previously named residual
  `WelcomePEMslMsrExecutorExposure` is discharged
  (`welcomePEMslMsrExecutorExposure`).
* `welcomePESpecialALUWriterShapeObligation_of_block` reduces
  `WelcomePESpecialALUWriterShapeObligation` to the block-float writer obligation,
  and `welcomePEBlockFloatWriterShapeObligation_of_low_and_nonLow` splits that
  obligation into the low-precision case (proved) and the non-low case
  (`WelcomePEBlockFloatNonLowWriterShapeObligation`).
* `WelcomePEBlockFloatNonLowWriterShapeObligation` is the one remaining
  shape-level residual.  For a block-float row the precision is one of `.d`,
  `.f`, `.g`, `.h` (the predicate `parsedExprIsBlockFloatProducer`), so this is
  precisely the `.h`-precision (half) writer: the third-word copy of
  `parsedBlockFloatMab .h` fails for arbitrary input buses
  (`parsedBlockFloatMab_h_third_word_not_copy`), and the line-level proof would
  have to derive the copy from the all-zero state at which the block-float stage
  reads its inputs.  That read analysis is not formalised here.

No `sorry`, no `admit`, no `native_decide`, and no new axioms.  No existing
module is edited by this file.  Neither `LowerBound welcomeSealedMachine
welcomeSpec 2` nor `Optimal welcomeSealedMachine welcomeSpec welcomeAnswer` is
claimed: `WelcomePEDispatchResiduals` is not discharged. -/

end ProofsLean.MNCore
