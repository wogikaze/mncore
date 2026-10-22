import ProofsLean.CendNonPlain

/-! # `12.convert-endian`: mixed lines of `.matrixRead` and closed rows

`ProofsLean/CendNonPlain.lean` reduces `LowerBound cendSealedMachine cendSpec 2`
to `CendNonPlainResidual`: every `.pe` line with at least one row outside the
closed class `cendL1ToPEOrExtInert` and not all-plain.  This module closes one
further slice of that residual, the lines that mix `.matrixRead` rows with the
already-closed families.

## The idea

`CendUnconditional` closes the all-`.matrixRead` lines
(`cendPE_allMatrixReadLines_not_correct`): the matrix store is identically zero
at the initial state, so every prepared write of every `.matrixRead` row carries
the zero bus.  That argument never used "all rows are `.matrixRead`" in the data
step, only that the *integer-stage inputs* are `.matrixRead` rows: the stage is

```
(expressions.filter parsedExprIsIntegerMatrixReadStageInput)
```

and `.matrixWrite`, `.l2bm`, the shared-block `.l1bm` operations and the
L1BM-to-PE broadcasts are not stage inputs, so they do not enter the prepared
list at all.  The `.noforward` row is the one other stage input, and the integer
stage prepares it as the empty write list.  Consequently:

* the integer stage prepares a **zero-data** write list for the whole line;
* the MSL/MSR, relu, block-float and matrix-MAU stages frame the PE registers
  (their filters are empty, or the matrix stage has no matrix-MAU row);
* the shared-block stage frames the PE registers unconditionally;
* the L1BM-to-PE broadcast stage preserves the all-zero `.lm1` bank at the
  initial state (`CendNonPlain.executeParsedL1ToPEProducers_lm1_zero`).

So a line whose stage inputs are `.matrixRead`/`.noforward` rows and whose other
rows lie in `cendL1ToPEOrExtInert` leaves both observed LM1 words at `0` at the
witness input, and is refuted like the all-`.matrixRead` family.

## What is new here

* §1 — the mixed row class `cendMixedReadRow`, its case analysis, the fact that
  its stage inputs are `.matrixRead`/`.noforward` rows, and its family facts.
* §2 — the zero-data extraction of the integer stage for lists of
  `.matrixRead`/`.noforward` rows
  (`prepareParsedIntegerMatrixReadLineCycles_data_zero_of_readOrNoForward`).
* §3 — the per-PE form of the L1BM-to-PE frame
  (`executeParsedL1ToPEProducers_lm1_zero_at`), which only needs the observed
  PE's `.lm1` bank to be zero.
* §4 — the walk-level extraction `cendMixedReadWalk_prepared`: a successful
  integer walk over a mixed list commits exactly a zero-data prepared list at
  the initial state.
* §5 — the line-level theorem
  `executeIntegerProducerInstructionLine_pe_lm1_zero_of_mixedRead` and its
  refutation `cendPE_mixedReadLines_not_correct`.
* §6 — the narrowed residual `CendMixedReadResidual`, its implication to
  `CendNonPlainResidual`, and the `CendLowerBoundTwo` reduction
  `cendLowerBound_two_of_mixedReadResidual`.

No `sorry`, no `admit`, no `native_decide`, no new axioms, no existing module is
edited.
-/

namespace ProofsLean.MNCore

open Issue
open PEMemory

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000
set_option linter.unusedSimpArgs false
set_option autoImplicit false

/-! ## 1. The mixed row class -/

/-- The two integer-stage inputs whose prepared data is zero at the initial
state: a `.matrixRead` row (zero matrix store) and a `.noforward` row (the stage
prepares it as the empty write list). -/
def cendReadOrNoForward (expression : ParsedExpr) : Bool :=
  parsedExprIsMatrixReadProducer expression ||
    (match expression.op with
     | .noforward => true
     | _ => false)

/-- **The mixed-class rows**: a `.matrixRead`/`.noforward` row, or a row of the
already-closed extended-inert/broadcast class `cendL1ToPEOrExtInert`.  A row
outside both classes writes a PE register file with value data (plain ALU,
float MAU, msl/msr, ...) and is left to the residual. -/
def cendMixedReadRow (expression : ParsedExpr) : Bool :=
  cendReadOrNoForward expression || cendL1ToPEOrExtInert expression

theorem cendReadOrNoForward_cases (expression : ParsedExpr)
    (row : cendReadOrNoForward expression = true) :
    expression.op = .noforward ∨ ∃ precision, expression.op = .matrixRead precision := by
  obtain ⟨op, sources, destinations, flush, text⟩ := expression
  simp only [cendReadOrNoForward, parsedExprIsMatrixReadProducer] at row
  cases op with
  | matrixRead precision => exact Or.inr ⟨precision, rfl⟩
  | noforward => exact Or.inl rfl
  | alu name precision unsigned arg => simp at row
  | immediate value unsigned => simp at row
  | zero => simp at row
  | mau precision matrix kind half round => simp at row
  | matrixWrite precision => simp at row
  | wait tag => simp at row
  | l1bm l1op => simp at row
  | l2bm l2op => simp at row

theorem cendMixedReadRow_cases (expression : ParsedExpr)
    (row : cendMixedReadRow expression = true) :
    cendReadOrNoForward expression = true ∨ cendL1ToPEOrExtInert expression = true := by
  have h := row
  simp only [cendMixedReadRow, Bool.or_eq_true] at h
  exact h

/-- **Every stage input of a mixed row is a `.matrixRead` or `.noforward` row.**
A `.matrixWrite`, `.l2bm`, `.l1bm` or `.wait` row is not an integer-stage input,
and the extended-inert class has only `.noforward` stage inputs
(`cendPEInertProducerExt_stageInput_noforward`); the broadcast class has none. -/
theorem cendMixedReadRow_stageInput (expression : ParsedExpr)
    (row : cendMixedReadRow expression = true)
    (stage : parsedExprIsIntegerMatrixReadStageInput expression = true) :
    expression.op = .noforward ∨ ∃ precision, expression.op = .matrixRead precision := by
  rcases cendMixedReadRow_cases expression row with read | closed
  · exact cendReadOrNoForward_cases expression read
  · have facts := cendL1ToPE_list_facts [expression] (fun item member => by
      simp only [List.mem_singleton] at member
      subst member
      exact closed)
    have member : expression ∈ [expression].filter
        parsedExprIsIntegerMatrixReadStageInput :=
      List.mem_filter.mpr ⟨by simp, stage⟩
    exact Or.inl (facts.2.2.2.2.2.2 expression member)

/-- **A `.matrixRead`/`.noforward` row writes none of the five value families.** -/
theorem cendReadOrNoForward_facts (expression : ParsedExpr)
    (row : cendReadOrNoForward expression = true) :
    parsedExprIsMslMsrProducer expression = false ∧
      parsedExprIsFloatReluProducer expression = false ∧
      parsedExprIsBlockFloatProducer expression = false ∧
      parsedExprIsMatrixMAUProducer expression = false ∧
      parsedExprIsSupportedFloatMAUProducer expression = false := by
  obtain ⟨op, sources, destinations, flush, text⟩ := expression
  simp only [cendReadOrNoForward, parsedExprIsMatrixReadProducer] at row
  cases op <;>
    simp_all [parsedExprIsMslMsrProducer, parsedExprIsFloatReluProducer,
      parsedExprIsBlockFloatProducer, parsedExprIsMatrixMAUProducer,
      parsedExprIsSupportedFloatMAUProducer]

/-- **A closed row writes none of the five value families.** -/
theorem cendL1ToPEOrExtInert_family_facts (expression : ParsedExpr)
    (row : cendL1ToPEOrExtInert expression = true) :
    parsedExprIsMslMsrProducer expression = false ∧
      parsedExprIsFloatReluProducer expression = false ∧
      parsedExprIsBlockFloatProducer expression = false ∧
      parsedExprIsMatrixMAUProducer expression = false ∧
      parsedExprIsSupportedFloatMAUProducer expression = false := by
  rcases cendL1ToPEOrExtInert_cases expression row with ext | broadcast
  · obtain ⟨msl, relu, block, mau, float, _, _⟩ :=
      cendPEInertProducerExt_facts expression ext
    exact ⟨msl, relu, block, mau, float⟩
  · obtain ⟨msl, relu, block, mau, float, _, _⟩ :=
      parsedExprIsL1ToPEProducer_facts expression broadcast
    exact ⟨msl, relu, block, mau, float⟩

/-- **A mixed row writes none of the five value families.** -/
theorem cendMixedReadRow_facts (expression : ParsedExpr)
    (row : cendMixedReadRow expression = true) :
    parsedExprIsMslMsrProducer expression = false ∧
      parsedExprIsFloatReluProducer expression = false ∧
      parsedExprIsBlockFloatProducer expression = false ∧
      parsedExprIsMatrixMAUProducer expression = false ∧
      parsedExprIsSupportedFloatMAUProducer expression = false := by
  rcases cendMixedReadRow_cases expression row with read | closed
  · exact cendReadOrNoForward_facts expression read
  · exact cendL1ToPEOrExtInert_family_facts expression closed

/-- **A mixed stage input passes the integer walk's outer producer filter.** -/
theorem cendMixedReadRow_outer (expression : ParsedExpr)
    (row : cendMixedReadRow expression = true)
    (stage : parsedExprIsIntegerMatrixReadStageInput expression = true) :
    (!parsedExprIsL2BMProducer expression && !parsedExprIsMslMsrProducer expression &&
      !parsedExprIsMatrixMAUProducer expression && !parsedExprIsBlockFloatProducer expression &&
      !parsedExprIsFloatReluProducer expression) = true := by
  rcases cendMixedReadRow_stageInput expression row stage with noforward | ⟨precision, hop⟩
  · obtain ⟨op, sources, destinations, flush, text⟩ := expression
    simp only at noforward
    subst noforward
    simp [parsedExprIsL2BMProducer, parsedExprIsMslMsrProducer,
      parsedExprIsMatrixMAUProducer, parsedExprIsBlockFloatProducer,
      parsedExprIsFloatReluProducer]
  · exact matrixRead_outerPredicate expression precision hop

/-- **A closed row is never a `.matrixRead` row.**  This is the formal sense in
which the mixed class strictly enlarges the closed class: a line with a
`.matrixRead` row can never be all-`cendL1ToPEOrExtInert`. -/
theorem cendL1ToPEOrExtInert_matrixRead_false (expression : ParsedExpr)
    (precision : ParsedPrecision) (hop : expression.op = .matrixRead precision) :
    cendL1ToPEOrExtInert expression = false := by
  obtain ⟨op, sources, destinations, flush, text⟩ := expression
  simp only at hop
  subst hop
  simp [cendL1ToPEOrExtInert, cendPEInertProducerExt, parsedExprIsPEInertProducer,
    parsedExprIsL1SharedBlockProducer, parsedExprIsMatrixWriteProducer,
    parsedExprIsL2BMProducer, parsedExprIsL1ToPEProducer]

/-! ## 2. The zero-data extraction for `.matrixRead`/`.noforward` lists

`prepareParsedIntegerMatrixReadLineExpressions` folds the executor's own
per-expression preparation over the integer stage's expression list.  A
`.matrixRead` row is prepared by `prepareParsedMatrixReadExprCycles` on the zero
matrix store, hence carries zero data (`CendUnconditional` §4); a `.noforward`
row is prepared as the empty write list.  So the fold prepares zero-data writes
for every list whose rows are `.matrixRead`/`.noforward` rows. -/

/-- **The line-preparation fold over `.matrixRead`/`.noforward` rows prepares
zero data.**  Each `.matrixRead` row is prepared by
`prepareParsedMatrixReadExprCycles` on the zero store, and a `.noforward` row
adds no write. -/
theorem prepareParsedIntegerMatrixReadLineExpressions_data_zero_of_readOrNoForward
    (files : IntegerRegisterFiles) (oldSlots : ProofsLean.MNCore.Forwarding.Slots)
    (control : ParsedMaskExecutionControl) (hasSingleLineMask noForward reduced : Bool) :
    ∀ (expressions : List ParsedExpr),
      (∀ expression ∈ expressions,
        expression.op = .noforward ∨ ∃ precision, expression.op = .matrixRead precision) →
      ∀ (writes : List PreparedParsedMaskedWrite)
        (nextSlots : ProofsLean.MNCore.Forwarding.Slots)
        (bars : List (Bool × BitVec 12))
        (result : List PreparedParsedMaskedWrite × ProofsLean.MNCore.Forwarding.Slots ×
          List (Bool × BitVec 12)),
        (∀ write ∈ writes, ∀ i : Fin 4, write.data i = 0) →
        prepareParsedIntegerMatrixReadLineExpressions files oldSlots welcomeZeroMatrixStore
          control hasSingleLineMask noForward reduced expressions writes nextSlots bars =
          .ok result →
        ∀ write ∈ result.1, ∀ i : Fin 4, write.data i = 0 := by
  intro expressions
  induction expressions with
  | nil =>
      intro _ writes nextSlots bars result prior prepared
      simp only [prepareParsedIntegerMatrixReadLineExpressions, StepResult.ok.injEq,
        Prod.mk.injEq] at prepared
      obtain ⟨rfl, rfl, rfl⟩ := prepared
      exact prior
  | cons expression rest ih =>
      intro allRows writes nextSlots bars result prior prepared
      have headRow := allRows expression (by simp)
      have restRows : ∀ item ∈ rest,
          item.op = .noforward ∨ ∃ precision, item.op = .matrixRead precision :=
        fun item member => allRows item (List.mem_cons_of_mem _ member)
      simp only [prepareParsedIntegerMatrixReadLineExpressions] at prepared
      rcases headRow with noforward | ⟨precision, hop⟩
      · rw [noforward_row_prepares_no_writes files oldSlots nextSlots
          welcomeZeroMatrixStore expression control hasSingleLineMask noForward reduced
          noforward] at prepared
        simp only [List.append_nil] at prepared
        exact ih restRows writes nextSlots bars result prior prepared
      · rw [prepareParsedIntegerMatrixReadLineExpression_matrixRead files oldSlots nextSlots
          welcomeZeroMatrixStore expression control hasSingleLineMask noForward reduced
          precision hop] at prepared
        cases head : prepareParsedMatrixReadExprCycles files nextSlots welcomeZeroMatrixStore
            expression control.directive hasSingleLineMask noForward control.context with
        | failure => simp [head] at prepared
        | unknown => simp [head] at prepared
        | ok expressionResult =>
            obtain ⟨expressionWrites, expressionSlots, expressionBars⟩ := expressionResult
            simp only [head] at prepared
            have expressionZero : ∀ write ∈ expressionWrites, ∀ i : Fin 4, write.data i = 0 :=
              prepareParsedMatrixReadExprCycles_data_zero files nextSlots expression
                control.directive hasSingleLineMask noForward control.context
                expressionWrites expressionSlots expressionBars head
            have combined : ∀ write ∈ writes ++ expressionWrites, ∀ i : Fin 4,
                write.data i = 0 := by
              intro write member
              rcases List.mem_append.mp member with earlier | later
              · exact prior write earlier
              · exact expressionZero write later
            exact ih restRows (writes ++ expressionWrites) expressionSlots
              (bars ++ expressionBars) result combined prepared

/-- **The integer-stage preparation of a `.matrixRead`/`.noforward` line
prepares zero data.** -/
theorem prepareParsedIntegerMatrixReadLineCycles_data_zero_of_readOrNoForward
    (files : IntegerRegisterFiles) (oldSlots : ProofsLean.MNCore.Forwarding.Slots)
    (control : ParsedMaskExecutionControl) (reduced : Bool)
    (expressions : List ParsedExpr)
    (allRows : ∀ expression ∈ expressions,
      expression.op = .noforward ∨ ∃ precision, expression.op = .matrixRead precision)
    (writes : List PreparedParsedMaskedWrite)
    (nextSlots : ProofsLean.MNCore.Forwarding.Slots)
    (bars : List (Bool × BitVec 12))
    (prepared : prepareParsedIntegerMatrixReadLineCycles files oldSlots welcomeZeroMatrixStore
      expressions control reduced = .ok (writes, nextSlots, bars)) :
    ∀ write ∈ writes, ∀ i : Fin 4, write.data i = 0 :=
  prepareParsedIntegerMatrixReadLineExpressions_data_zero_of_readOrNoForward files oldSlots
    control _ (expressions.any fun expression =>
      match expression.op with | .noforward => true | _ => false) reduced
    expressions allRows [] oldSlots [] (writes, nextSlots, bars)
    (by intro write member; simp at member) prepared

/-! ## 3. The L1BM-to-PE frame at a single PE

`CendNonPlain` proves the broadcast stage preserves the all-zero `.lm1` bank of
**every** PE.  The mixed-line proof only needs the observed PE, and the integer
stage of a mixed line may have written the other PEs.  The two lemmas below are
the per-PE restatements of `executeParsedL1ToPEProducer_lm1_zero` and
`executeParsedL1ToPEProducers_lm1_zero`; the underlying per-PE walk lemma
`executeParsedL1ToPEAtPEs_lm1_zero` is already per-PE. -/

/-- **The L1BM-to-PE producer preserves the zero `.lm1` bank of one PE.** -/
theorem executeParsedL1ToPEProducer_lm1_zero_at
    (readState currentState next : State) (expression : ParsedExpr) (p : PEId)
    (noForward hasSingleLineMask usePreIssueMask : Bool)
    (busZero : ∀ (access : ParsedL1ToPEAccess), lowerParsedL1ToPE? expression = some access →
      ∀ (pe : PEId) (cycle : Fin 4),
        l1ToPEBusAt readState expression access pe cycle = ⟨0, 0⟩)
    (zero : (currentState.peRegisters p).lm1 = fun _ => 0)
    (executed : executeParsedL1ToPEProducer readState currentState expression noForward
      hasSingleLineMask usePreIssueMask = .ok next) :
    (next.peRegisters p).lm1 = fun _ => 0 := by
  cases lowered : lowerParsedL1ToPE? expression with
  | none =>
      rw [executeParsedL1ToPEProducer, lowered] at executed
      simp at executed
  | some access =>
      rw [executeParsedL1ToPEProducer, lowered] at executed
      exact executeParsedL1ToPEAtPEs_lm1_zero readState expression access noForward
        hasSingleLineMask usePreIssueMask (busZero access lowered) (List.finRange 4096)
        currentState p next zero executed

/-- **The L1BM-to-PE family filter preserves the zero `.lm1` bank of one PE.** -/
theorem executeParsedL1ToPEProducers_lm1_zero_at
    (readState currentState next : State) (expressions : List ParsedExpr) (p : PEId)
    (noForward hasSingleLineMask usePreIssueMask : Bool)
    (busZero : ∀ expression ∈ expressions.filter parsedExprIsL1ToPEProducer,
      ∀ (access : ParsedL1ToPEAccess), lowerParsedL1ToPE? expression = some access →
      ∀ (pe : PEId) (cycle : Fin 4),
        l1ToPEBusAt readState expression access pe cycle = ⟨0, 0⟩)
    (zero : (currentState.peRegisters p).lm1 = fun _ => 0)
    (executed : executeParsedL1ToPEProducers readState currentState expressions noForward
      hasSingleLineMask usePreIssueMask = .ok next) :
    (next.peRegisters p).lm1 = fun _ => 0 := by
  cases filtered : expressions.filter parsedExprIsL1ToPEProducer with
  | nil =>
      rw [executeParsedL1ToPEProducers, filtered] at executed
      simp only [StepResult.ok.injEq] at executed
      subst executed
      exact zero
  | cons expression rest =>
      cases rest with
      | nil =>
          rw [executeParsedL1ToPEProducers, filtered] at executed
          exact executeParsedL1ToPEProducer_lm1_zero_at readState currentState next expression
            p noForward hasSingleLineMask usePreIssueMask
            (fun access lowered => busZero expression (by simp [filtered]) access lowered) zero
            executed
      | cons second remaining =>
          rw [executeParsedL1ToPEProducers, filtered] at executed
          simp at executed

/-! ## 4. The walk-level extraction at the initial state -/

/-- **The integer stage of a mixed line commits a zero-data list.**  A successful
walk over a list of `.matrixRead`/`.noforward` stage inputs at the
`cendInitialState` produces exactly the commit of the executor's own preparation
list, and every write of that list carries zero data (the matrix store is zero
and `.noforward` rows prepare nothing). -/
theorem cendMixedReadWalk_prepared
    (expressions : List ParsedExpr) (input : BitVec 64) (rest : List PEId) (next : State)
    (absent : welcomePE ∉ rest)
    (mixed : ∀ expression ∈ expressions.filter parsedExprIsIntegerMatrixReadStageInput,
      expression.op = .noforward ∨ ∃ precision, expression.op = .matrixRead precision)
    (floatEmpty : expressions.filter parsedExprIsSupportedFloatMAUProducer = [])
    (executed : executeIntegerProducerLineAtPEs expressions (welcomePE :: rest)
      (cendInitialState input) = .ok next) :
    ∃ (writes : List PreparedParsedMaskedWrite)
      (slots : ProofsLean.MNCore.Forwarding.Slots)
      (bars : List (Bool × BitVec 12)),
      prepareParsedIntegerMatrixReadLineCycles ((cendInitialState input).peRegisters cendPE)
        (stateForwardingSlots (cendInitialState input) cendPE)
        welcomeZeroMatrixStore
        (expressions.filter parsedExprIsIntegerMatrixReadStageInput)
        { directive := (cendInitialState input).maskDirective
          context :=
            { (ParsedIntegerContext.ofLinearIndex cendPE) with
              bar0 := ((cendInitialState input).peContext cendPE).bar0
              bar1 := ((cendInitialState input).peContext cendPE).bar1
              tWord := ((cendInitialState input).peContext cendPE).tWord }
          elapsedWords := (cendInitialState input).hazardClock } false =
        .ok (writes, slots, bars) ∧
      (∀ write ∈ writes, ∀ i : Fin 4, write.data i = 0) ∧
      next.peRegisters cendPE =
        commitParsedMaskedWrites ((cendInitialState input).peRegisters cendPE) writes := by
  obtain ⟨prepared, preparedEq, committed⟩ :=
    executeIntegerProducerLineAtPEs_zero_commit_list expressions rest
      (cendInitialState input) next absent floatEmpty executed
  obtain ⟨writes, slots, bars⟩ := prepared
  have storeZero : ((cendInitialState input).matrixRegisters
      (ParsedIntegerContext.ofLinearIndex cendPE).group
      (ParsedIntegerContext.ofLinearIndex cendPE).l2b
      (ParsedIntegerContext.ofLinearIndex cendPE).l1b) = welcomeZeroMatrixStore := rfl
  rw [storeZero] at preparedEq
  have dataZero := prepareParsedIntegerMatrixReadLineCycles_data_zero_of_readOrNoForward
    ((cendInitialState input).peRegisters cendPE)
    (stateForwardingSlots (cendInitialState input) cendPE) _ _
    (expressions.filter parsedExprIsIntegerMatrixReadStageInput) mixed
    writes slots bars preparedEq
  exact ⟨writes, slots, bars, preparedEq, dataZero, committed⟩

/-! ## 5. Mixed lines leave the observed LM1 bank at zero -/

/-- **A successful mixed line leaves the observed LM1 bank at zero.**  The
integer stage commits a zero-data list (`.matrixRead` and `.noforward` stage
inputs); the MSL/MSR, relu, block-float and matrix-MAU stages frame the PE
registers, the shared-block stage frames them unconditionally, and the
L1BM-to-PE broadcast stage preserves the zero `.lm1` bank at the initial
state. -/
theorem executeIntegerProducerInstructionLine_pe_lm1_zero_of_mixedRead
    (normalizedExpressions : List NormalizedExpr) (input : BitVec 64) (next : State)
    (rows : ∀ expression ∈ normalizedExpressions.map NormalizedExpr.toParsed,
      cendMixedReadRow expression = true)
    (success : executeIntegerProducerInstructionLine (.pe normalizedExpressions)
      (cendInitialState input) = .ok next) :
    ∀ address, (next.peRegisters cendPE).lm1 address = 0 := by
  have accepted := executeIntegerProducerInstructionLine_accepted_of_ok
    (.pe normalizedExpressions) (cendInitialState input) next success
  have waitsAny : (normalizedExpressions.map NormalizedExpr.toParsed).any
      (parsedExprWaitPending (cendInitialState input)) = false :=
    executeIntegerProducerInstructionLine_pe_waits_complete normalizedExpressions
      (cendInitialState input) next success
  have noUnsupportedAny : (normalizedExpressions.map NormalizedExpr.toParsed).any
      parsedExprIsUnsupportedRustAlu = false :=
    executeIntegerProducerInstructionLine_pe_noUnsupported_of_ok normalizedExpressions
      (cendInitialState input) next success
  have supportedAny : (normalizedExpressions.map NormalizedExpr.toParsed).all
      parsedExprIsSupportedPELineProducer = true :=
    executeIntegerProducerInstructionLine_pe_supported_of_ok normalizedExpressions
      (cendInitialState input) next success
  obtain ⟨nextPEs, nextMsl, nextRelu, nextBlockFloat, afterMatrix, nextShared, nextBroadcast,
    walkExecuted, mslExecuted, reluExecuted, blockExecuted, matrixExecuted, sharedExecuted,
    l1Executed, nextEq⟩ :=
    executeIntegerProducerInstructionLine_pe_stages_exists normalizedExpressions
      (cendInitialState input) next accepted waitsAny noUnsupportedAny supportedAny success
  have mslEmpty : (normalizedExpressions.map NormalizedExpr.toParsed).filter
      parsedExprIsMslMsrProducer = [] :=
    List.filter_eq_nil_iff.mpr fun expression member => by
      rw [(cendMixedReadRow_facts expression (rows expression member)).1]; simp
  have reluEmpty : (normalizedExpressions.map NormalizedExpr.toParsed).filter
      parsedExprIsFloatReluProducer = [] :=
    List.filter_eq_nil_iff.mpr fun expression member => by
      rw [(cendMixedReadRow_facts expression (rows expression member)).2.1]; simp
  have blockEmpty : (normalizedExpressions.map NormalizedExpr.toParsed).filter
      parsedExprIsBlockFloatProducer = [] :=
    List.filter_eq_nil_iff.mpr fun expression member => by
      rw [(cendMixedReadRow_facts expression (rows expression member)).2.2.1]; simp
  have mauEmpty : (normalizedExpressions.map NormalizedExpr.toParsed).filter
      parsedExprIsMatrixMAUProducer = [] :=
    List.filter_eq_nil_iff.mpr fun expression member => by
      rw [(cendMixedReadRow_facts expression (rows expression member)).2.2.2.1]; simp
  have floatEmpty : (normalizedExpressions.map NormalizedExpr.toParsed).filter
      parsedExprIsSupportedFloatMAUProducer = [] :=
    List.filter_eq_nil_iff.mpr fun expression member => by
      rw [(cendMixedReadRow_facts expression (rows expression member)).2.2.2.2]; simp
  have stageRows : ∀ expression ∈ (normalizedExpressions.map NormalizedExpr.toParsed).filter
      parsedExprIsIntegerMatrixReadStageInput,
      expression.op = .noforward ∨ ∃ precision, expression.op = .matrixRead precision :=
    fun expression member =>
      cendMixedReadRow_stageInput expression
        (rows expression (List.mem_filter.mp member).1) (List.mem_filter.mp member).2
  have outerStage :
      ((normalizedExpressions.map NormalizedExpr.toParsed).filter (fun expression =>
        !parsedExprIsL2BMProducer expression && !parsedExprIsMslMsrProducer expression &&
          !parsedExprIsMatrixMAUProducer expression && !parsedExprIsBlockFloatProducer expression &&
          !parsedExprIsFloatReluProducer expression)).filter
          parsedExprIsIntegerMatrixReadStageInput =
        (normalizedExpressions.map NormalizedExpr.toParsed).filter
          parsedExprIsIntegerMatrixReadStageInput := by
    rw [List.filter_filter]
    apply List.filter_congr
    intro item member
    cases stage : parsedExprIsIntegerMatrixReadStageInput item with
    | false => simp [stage]
    | true =>
        have outer := cendMixedReadRow_outer item (rows item member) stage
        simp [stage, outer]
  have floatEmptyOuter :
      ((normalizedExpressions.map NormalizedExpr.toParsed).filter (fun expression =>
        !parsedExprIsL2BMProducer expression && !parsedExprIsMslMsrProducer expression &&
          !parsedExprIsMatrixMAUProducer expression && !parsedExprIsBlockFloatProducer expression &&
          !parsedExprIsFloatReluProducer expression)).filter
          parsedExprIsSupportedFloatMAUProducer = [] :=
    List.filter_eq_nil_iff.mpr fun expression member =>
      (List.filter_eq_nil_iff.mp floatEmpty) expression
        (List.mem_filter.mp member).1
  obtain ⟨split, absent⟩ := plusTwoFinRange_split
  rw [split] at walkExecuted
  obtain ⟨prepared, preparedEq, committed⟩ :=
    executeIntegerProducerLineAtPEs_zero_commit_list
      ((normalizedExpressions.map NormalizedExpr.toParsed).filter (fun expression =>
        !parsedExprIsL2BMProducer expression && !parsedExprIsMslMsrProducer expression &&
          !parsedExprIsMatrixMAUProducer expression && !parsedExprIsBlockFloatProducer expression &&
          !parsedExprIsFloatReluProducer expression))
      ((List.finRange 4095).map Fin.succ) (cendInitialState input) nextPEs absent
      floatEmptyOuter walkExecuted
  obtain ⟨writes, slots, bars⟩ := prepared
  have storeZero : ((cendInitialState input).matrixRegisters
      (ParsedIntegerContext.ofLinearIndex cendPE).group
      (ParsedIntegerContext.ofLinearIndex cendPE).l2b
      (ParsedIntegerContext.ofLinearIndex cendPE).l1b) = welcomeZeroMatrixStore := rfl
  rw [storeZero] at preparedEq
  rw [outerStage] at preparedEq
  have dataZero : ∀ write ∈ writes, ∀ i : Fin 4, write.data i = 0 :=
    prepareParsedIntegerMatrixReadLineCycles_data_zero_of_readOrNoForward
      ((cendInitialState input).peRegisters cendPE)
      (stateForwardingSlots (cendInitialState input) cendPE)
      { directive := (cendInitialState input).maskDirective
        context :=
          { (ParsedIntegerContext.ofLinearIndex cendPE) with
            bar0 := ((cendInitialState input).peContext cendPE).bar0
            bar1 := ((cendInitialState input).peContext cendPE).bar1
            tWord := ((cendInitialState input).peContext cendPE).tWord }
        elapsedWords := (cendInitialState input).hazardClock } false
      ((normalizedExpressions.map NormalizedExpr.toParsed).filter
        parsedExprIsIntegerMatrixReadStageInput) stageRows writes slots bars preparedEq
  have nextMslEq : nextMsl = nextPEs := by
    rw [executeParsedMslMsrProducers_eq_self (cendInitialState input) nextPEs
      (normalizedExpressions.map NormalizedExpr.toParsed) _ _ mslEmpty] at mslExecuted
    exact (StepResult.ok.inj mslExecuted).symm
  have nextReluEq : nextRelu = nextMsl := by
    rw [executeParsedFloatReluProducers_eq_self (cendInitialState input) nextMsl
      (normalizedExpressions.map NormalizedExpr.toParsed) _ _ reluEmpty] at reluExecuted
    exact (StepResult.ok.inj reluExecuted).symm
  have nextBlockEq : nextBlockFloat = nextRelu := by
    rw [executeParsedBlockFloatProducer_eq_self (cendInitialState input) nextRelu
      (normalizedExpressions.map NormalizedExpr.toParsed) _ _ blockEmpty] at blockExecuted
    exact (StepResult.ok.inj blockExecuted).symm
  have matrixExecuted' := matrixExecuted
  rw [nextBlockEq, nextReluEq, nextMslEq] at matrixExecuted'
  have matrixFrame : afterMatrix.peRegisters = nextPEs.peRegisters :=
    funext fun pe =>
      executeParsedMatrixMAUAndWrites_peRegisters_frame_of_noMatrixMAU
        (cendInitialState input) nextPEs afterMatrix
        (normalizedExpressions.map NormalizedExpr.toParsed) _ _ mauEmpty matrixExecuted' pe
  have blockFrame : nextShared.peRegisters = afterMatrix.peRegisters :=
    executeParsedSharedBlockProducers_peRegisters (cendInitialState input) afterMatrix
      nextShared (normalizedExpressions.map NormalizedExpr.toParsed) _ sharedExecuted
  have afterZero : (nextShared.peRegisters cendPE).lm1 = fun _ => 0 := by
    rw [blockFrame, matrixFrame, committed]
    funext address
    exact commitParsedMaskedWrites_lm1_zero_of_data_zero _ writes dataZero
      (fun target => cendInitialPERegisters_lm1 input target) address
  have broadcastZero := executeParsedL1ToPEProducers_lm1_zero_at
    (cendInitialState input) nextShared nextBroadcast
    (normalizedExpressions.map NormalizedExpr.toParsed) cendPE _ _ _
    (fun expression member access lowered pe cycle =>
      cendInitialState_l1ToPEBusAt_zero input expression access pe cycle)
    afterZero l1Executed
  have registersEq : next.peRegisters = nextBroadcast.peRegisters := by
    rw [nextEq]
  intro address
  rw [registersEq]
  exact congrFun broadcastZero address

/-- **The mixed lines are refuted.**  At the witness input every mixed line keeps
the observed LM1 bank at the initial zero, while the target pair
`byteSwap64 cendWitness = 0x0807060504030201` is non-zero. -/
theorem cendPE_mixedReadLines_not_correct (expressions : List NormalizedExpr)
    (rows : ∀ expression ∈ expressions.map NormalizedExpr.toParsed,
      cendMixedReadRow expression = true) :
    ¬ ProofsLean.Correct cendSealedMachine cendSpec
      ([InstructionLine.pe expressions] : List InstructionLine) := by
  cases step : cendSealedMachine.step (.pe expressions) (cendInitialState cendWitness) with
  | none => exact cend_not_correct_of_step_none _ _ step
  | some next =>
      have executed := cendSealed_step_ok step
      have lineExecuted : executeIntegerProducerInstructionLine (.pe expressions)
          (cendInitialState cendWitness) = .ok next := by
        unfold executeNormalizedLine at executed
        simp only [Issue.InstructionLine.toNormalizedLine, NormalizedLine.toInstruction?] at executed
        exact executed
      have zero := executeIntegerProducerInstructionLine_pe_lm1_zero_of_mixedRead
        expressions cendWitness next rows lineExecuted
      refine cend_not_correct_of_lm1_zero expressions next step ?_
      intro address
      exact zero address

/-! ## 6. The narrowed residual and the bound-two reduction -/

/-- The lines this module closes: every row is a mixed row. -/
def CendMixedReadLines (expressions : List NormalizedExpr) : Prop :=
  ∀ expression ∈ expressions.map NormalizedExpr.toParsed,
    cendMixedReadRow expression = true

/-- The all-`.matrixRead` lines of `CendUnconditional` are mixed lines. -/
theorem cendMixedReadLines_of_allMatrixRead (expressions : List NormalizedExpr)
    (allRead : CendAllMatrixReadLines expressions) : CendMixedReadLines expressions := by
  intro expression member
  obtain ⟨precision, hop⟩ := allMatrixRead_mem_toParsed allRead member
  obtain ⟨op, sources, destinations, flush, text⟩ := expression
  simp only at hop
  subst hop
  simp [cendMixedReadRow, cendReadOrNoForward, parsedExprIsMatrixReadProducer]

/-- **The mixed class is not covered by the previous extended-inert/broadcast
class**: a line with a `.matrixRead` row is never all-`cendL1ToPEOrExtInert`
(the latter class contains no `.matrixRead` row). -/
theorem not_allClosed_of_matrixReadRow (expressions : List NormalizedExpr)
    (expression : ParsedExpr) (member : expression ∈ expressions.map NormalizedExpr.toParsed)
    (precision : ParsedPrecision) (hop : expression.op = .matrixRead precision) :
    ¬ (∀ item ∈ expressions.map NormalizedExpr.toParsed,
      cendL1ToPEOrExtInert item = true) := by
  intro all
  have closed := all expression member
  rw [cendL1ToPEOrExtInert_matrixRead_false expression precision hop] at closed
  simp at closed

/-- **The narrowed residual.**  Everything `CendNonPlainResidual` leaves open,
minus the mixed lines of §5.  A line still covered here has at least one
`.matrixRead`-free row and at least one row outside `cendL1ToPEOrExtInert` that
is not a `.matrixRead`/`.noforward` row, i.e. a PE-register writer from one of
the six value families: plain ALU (`.alu`/`.zero`/`.immediate`), float MAU,
float relu, `msl`/`msr`, or matrix MAU / block float — possibly mixed with
already-closed rows. -/
def CendMixedReadResidual : Prop :=
  ∀ expressions : List NormalizedExpr,
    ¬ CendClosedLines expressions →
    ¬ (∀ expression ∈ expressions.map NormalizedExpr.toParsed,
      cendL1ToPEOrExtInert expression = true) →
    ¬ (expressions.map NormalizedExpr.toParsed).all parsedExprIsPlainIntegerALU = true →
    ¬ CendMixedReadLines expressions →
    ¬ ProofsLean.Correct cendSealedMachine cendSpec
      ([InstructionLine.pe expressions] : List InstructionLine)

/-- **`CendNonPlainResidual` from the narrower residual.**  The mixed lines are
refuted by §5; everything else is the residual. -/
theorem cendNonPlainResidual_of_mixedReadResidual (residual : CendMixedReadResidual) :
    CendNonPlainResidual := by
  intro expressions notClosed notClosedExt notPlain
  by_cases mixed : CendMixedReadLines expressions
  · exact cendPE_mixedReadLines_not_correct expressions mixed
  · exact residual expressions notClosed notClosedExt notPlain mixed

/-- **`CendPENonClosedRefuted` from the narrower residual.** -/
theorem cendPENonClosedRefuted_of_mixedReadResidual (residual : CendMixedReadResidual) :
    CendPENonClosedRefuted :=
  cendPENonClosedRefuted_of_nonPlainResidual
    (cendNonPlainResidual_of_mixedReadResidual residual)

/-- **The unconditional lower bound at two from the narrower residual.** -/
theorem cendLowerBound_two_of_mixedReadResidual (residual : CendMixedReadResidual) :
    ProofsLean.LowerBound cendSealedMachine cendSpec 2 :=
  cendLowerBound_two_of_nonPlainResidual
    (cendNonPlainResidual_of_mixedReadResidual residual)

/-- The mixed lines, as a refutation statement. -/
def CendMixedReadLinesRefuted : Prop :=
  ∀ expressions : List NormalizedExpr, CendMixedReadLines expressions →
    ¬ ProofsLean.Correct cendSealedMachine cendSpec
      ([InstructionLine.pe expressions] : List InstructionLine)

/-- The mixed-line refutation holds (§5). -/
theorem cendMixedReadLinesRefuted_holds : CendMixedReadLinesRefuted :=
  fun expressions mixed => cendPE_mixedReadLines_not_correct expressions mixed

/-- **The narrowing is exact.**  `CendNonPlainResidual` splits into the narrower
residual and the mixed-line refutation, so the new residual is exactly the old
one minus the lines §5 closes — nothing weaker is assumed. -/
theorem cendNonPlainResidual_iff_mixedReadResidual :
    CendNonPlainResidual ↔ CendMixedReadResidual ∧ CendMixedReadLinesRefuted := by
  constructor
  · intro residual
    exact ⟨fun expressions notClosed notClosedExt notPlain _mixed =>
        residual expressions notClosed notClosedExt notPlain,
      cendMixedReadLinesRefuted_holds⟩
  · rintro ⟨residual, mixedRefuted⟩
    intro expressions notClosed notClosedExt notPlain
    by_cases mixed : CendMixedReadLines expressions
    · exact mixedRefuted expressions mixed
    · exact residual expressions notClosed notClosedExt notPlain mixed

/-- **The narrower residual is still exactly a gap.**  Reading
`CendLowerBoundTwo` through the `CendNonPlain` reduction: a proof of
`CendMixedReadResidual` gives `LowerBound cendSealedMachine cendSpec 2`, and
conversely the lower bound refutes every line of the residual. -/
theorem cendLowerBound_two_iff_mixedReadResidual :
    ProofsLean.LowerBound cendSealedMachine cendSpec 2 ↔ CendMixedReadResidual := by
  constructor
  · intro lower expressions _notClosed _notClosedExt _notPlain _mixed correct
    exact (cendLowerBound_two_iff_peLines.mp lower expressions) correct
  · exact cendLowerBound_two_of_mixedReadResidual

/-! ## 7. A concrete line that only the mixed class refutes

The narrowing is not vacuous: a line with one `.matrixRead` row and one L1BM
broadcast row is mixed (so §5 refutes it), but it is neither all-`.matrixRead`
(the broadcast row) nor all-`cendL1ToPEOrExtInert` (the read row) nor all-plain.
It therefore satisfies the three negative hypotheses of `CendNonPlainResidual`
and is exactly the kind of line the narrower residual drops. -/

/-- One `.matrixRead` row and one L1BM broadcast row. -/
def cendMixedExampleLine : List NormalizedExpr :=
  [⟨.matrixRead .d, [], [], none⟩, ⟨.l1bm .pbcast, [], [], none⟩]

theorem cendMixedExampleLine_mixed : CendMixedReadLines cendMixedExampleLine := by
  intro expression member
  obtain ⟨normalized, normalizedMem, rfl⟩ := List.mem_map.mp member
  simp [cendMixedExampleLine] at normalizedMem
  rcases normalizedMem with rfl | rfl <;>
    simp [cendMixedReadRow, cendReadOrNoForward, NormalizedExpr.toParsed,
      cendL1ToPEOrExtInert, parsedExprIsMatrixReadProducer, cendPEInertProducerExt,
      parsedExprIsPEInertProducer, parsedExprIsL1SharedBlockProducer,
      parsedExprIsL1ToPEProducer]

theorem cendMixedExampleLine_not_allRead : ¬ CendAllMatrixReadLines cendMixedExampleLine := by
  intro all
  have read := all ⟨.l1bm .pbcast, [], [], none⟩ (by
    simp [cendMixedExampleLine])
  obtain ⟨precision, hop⟩ := read
  simp [NormalizedExpr.toParsed] at hop

theorem cendMixedExampleLine_not_allInert :
    ¬ (∀ expression ∈ cendMixedExampleLine.map NormalizedExpr.toParsed,
      parsedExprIsPEInertProducer expression = true) := by
  intro all
  have inert := all ⟨.matrixRead .d, [], [], none, ""⟩ (by
    simp [cendMixedExampleLine, NormalizedExpr.toParsed])
  simp [NormalizedExpr.toParsed, parsedExprIsPEInertProducer,
    parsedExprIsL1SharedBlockProducer] at inert

theorem cendMixedExampleLine_not_allClosed :
    ¬ (∀ expression ∈ cendMixedExampleLine.map NormalizedExpr.toParsed,
      cendL1ToPEOrExtInert expression = true) :=
  not_allClosed_of_matrixReadRow cendMixedExampleLine
    ⟨.matrixRead .d, [], [], none, ""⟩ (by simp [cendMixedExampleLine, NormalizedExpr.toParsed])
    .d rfl

theorem cendMixedExampleLine_notPlain :
    (cendMixedExampleLine.map NormalizedExpr.toParsed).all parsedExprIsPlainIntegerALU = false := by
  simp [cendMixedExampleLine, NormalizedExpr.toParsed, parsedExprIsPlainIntegerALU,
    parsedExprIsIntegerProducer]

/-- **The smaller residual is strictly smaller.**  The example line satisfies
every negative hypothesis of `CendNonPlainResidual` and is refuted by §5. -/
theorem cendMixedExampleLine_new :
    CendMixedReadLines cendMixedExampleLine ∧
      ¬ CendClosedLines cendMixedExampleLine ∧
      ¬ (∀ expression ∈ cendMixedExampleLine.map NormalizedExpr.toParsed,
        cendL1ToPEOrExtInert expression = true) ∧
      (cendMixedExampleLine.map NormalizedExpr.toParsed).all
        parsedExprIsPlainIntegerALU = false := by
  refine ⟨cendMixedExampleLine_mixed, ?_, cendMixedExampleLine_not_allClosed,
    cendMixedExampleLine_notPlain⟩
  intro closed
  rcases closed with allRead | allInert
  · exact cendMixedExampleLine_not_allRead allRead
  · exact cendMixedExampleLine_not_allInert allInert

/-! ## Trust report -/

#print axioms cendReadOrNoForward_cases
#print axioms cendMixedReadRow_stageInput
#print axioms cendMixedReadRow_facts
#print axioms cendMixedReadRow_outer
#print axioms cendL1ToPEOrExtInert_matrixRead_false
#print axioms prepareParsedIntegerMatrixReadLineExpressions_data_zero_of_readOrNoForward
#print axioms prepareParsedIntegerMatrixReadLineCycles_data_zero_of_readOrNoForward
#print axioms executeParsedL1ToPEProducer_lm1_zero_at
#print axioms executeParsedL1ToPEProducers_lm1_zero_at
#print axioms cendMixedReadWalk_prepared
#print axioms executeIntegerProducerInstructionLine_pe_lm1_zero_of_mixedRead
#print axioms cendPE_mixedReadLines_not_correct
#print axioms cendMixedReadLines_of_allMatrixRead
#print axioms not_allClosed_of_matrixReadRow
#print axioms cendNonPlainResidual_of_mixedReadResidual
#print axioms cendPENonClosedRefuted_of_mixedReadResidual
#print axioms cendLowerBound_two_of_mixedReadResidual
#print axioms cendMixedReadLinesRefuted_holds
#print axioms cendNonPlainResidual_iff_mixedReadResidual
#print axioms cendMixedExampleLine_new
#print axioms cendLowerBound_two_iff_mixedReadResidual

end ProofsLean.MNCore

