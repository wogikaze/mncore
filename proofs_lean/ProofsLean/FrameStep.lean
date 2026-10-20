import ProofsLean.WholeMachineMachine

/-! Phase 2 frame reasoning for `.pe` rows, below the hazard-aware layer.

`WholeMachineMachine.lean` proves the first frame facts for `nop`. This module
extends them to PE rows at the `State` level:

* the nested per-stage executors of `executeIntegerProducerInstructionLine`
  reduce to the identity on an integer-ALU-only expression list;
* the per-PE walk over all 4096 PEs preserves L1BM, block memory, DAR state and
  matrix registers *for every expression list* (its only writes are the PE
  register files, forwarding, forwarding validity and PE context);
* hence a successful `.pe` step whose expressions are plain integer ALUs
  (`.alu`/`.zero`/`.immediate` that are neither legacy Rust-unsupported ALUs,
  MSL/MSR producers, float-relu producers nor block-float producers) leaves
  `l1bm`, `blockMemory`, `dar` and `matrixRegisters` unchanged.

What this module does **not** claim: that `peRegisters` or `forwarding` are
unchanged when the line has no destination. An ALU/zero/immediate producer
advances the ALU forwarding slots in `updateSupportedPELineForwarding` even
when it writes no register, so such a claim is false; the precise statement
needs a `noforward` expression, which is treated separately below. Even there,
`executeIntegerProducerLineAtPECore` rewrites `forwarding pe` with
`stateForwardingSlots state pe`, so invalid slots become poison; forwarding is
unchanged only when every validity bit at `pe` is set.

Two proved footprint discrepancies are recorded at the end of the file: an
integer-ALU line resets `l1bmTurnaroundValid` to `false` although
`normalizedLineFootprint` does not name `.l1bmTurnaround` for it, and a
`noforward` line can rewrite `forwarding` although its footprint only names
`.issueControl`.
-/
namespace ProofsLean.MNCore

open Issue
open PEMemory

/-! ## Stage identities for integer-ALU-only expression lists -/

theorem executeParsedMslMsrProducers_nil (readState currentState : State)
    (expressions : List ParsedExpr) (noForward hasSingleLineMask : Bool)
    (empty : expressions.filter parsedExprIsMslMsrProducer = []) :
    executeParsedMslMsrProducers readState currentState expressions noForward
        hasSingleLineMask =
      .ok currentState := by
  simp [executeParsedMslMsrProducers, empty]

theorem executeParsedFloatReluProducers_nil (readState currentState : State)
    (expressions : List ParsedExpr) (noForward hasSingleLineMask : Bool)
    (empty : expressions.filter parsedExprIsFloatReluProducer = []) :
    executeParsedFloatReluProducers readState currentState expressions noForward
        hasSingleLineMask =
      .ok currentState := by
  simp [executeParsedFloatReluProducers, empty]

theorem executeParsedBlockFloatProducer_nil (readState currentState : State)
    (expressions : List ParsedExpr) (noForward hasSingleLineMask : Bool)
    (empty : expressions.filter parsedExprIsBlockFloatProducer = []) :
    executeParsedBlockFloatProducer readState currentState expressions noForward
        hasSingleLineMask =
      .ok currentState := by
  simp [executeParsedBlockFloatProducer, empty]

theorem executeParsedMatrixMAUAndWrites_id (readState currentState : State)
    (expressions : List ParsedExpr) (noForward hasSingleLineMask : Bool)
    (noMAU : expressions.filter parsedExprIsMatrixMAUProducer = [])
    (noWrite : expressions.any parsedExprIsMatrixWriteProducer = false) :
    executeParsedMatrixMAUAndWrites readState currentState expressions noForward
        hasSingleLineMask =
      .ok currentState := by
  rw [executeParsedMatrixMAUAndWrites, executeParsedMatrixMAUProducer, noMAU]
  unfold executeParsedMatrixWritesAtMABs
  rw [noWrite]
  simp

theorem executeParsedL1ToPEProducers_nil (readState currentState : State)
    (expressions : List ParsedExpr) (noForward hasSingleLineMask usePreIssueMask : Bool)
    (empty : expressions.filter parsedExprIsL1ToPEProducer = []) :
    executeParsedL1ToPEProducers readState currentState expressions noForward
        hasSingleLineMask usePreIssueMask =
      .ok currentState := by
  simp [executeParsedL1ToPEProducers, empty]

theorem executeParsedSharedBlockExpression_integer (readState currentState : State)
    (expression : ParsedExpr) (updateTurnaround : Bool)
    (integer : parsedExprIsIntegerProducer expression = true) :
    executeParsedSharedBlockExpression readState currentState expression updateTurnaround =
      .ok currentState := by
  cases expression with
  | mk op sources destinations flush text =>
      cases op <;>
        simp_all [parsedExprIsIntegerProducer, executeParsedSharedBlockExpression]

theorem executeParsedSharedBlockProducerList_integer (readState : State)
    (updateTurnaround : Bool) :
    ∀ (expressions : List ParsedExpr) (currentState : State),
      expressions.all parsedExprIsIntegerProducer = true →
      executeParsedSharedBlockProducerList readState updateTurnaround expressions currentState =
        .ok currentState
  | [], currentState, _ => by simp [executeParsedSharedBlockProducerList]
  | expression :: rest, currentState, h => by
      rw [List.all_cons, Bool.and_eq_true] at h
      obtain ⟨hhead, hrest⟩ := h
      have head := executeParsedSharedBlockExpression_integer readState currentState
        expression updateTurnaround hhead
      simp [executeParsedSharedBlockProducerList, head,
        executeParsedSharedBlockProducerList_integer readState updateTurnaround rest
          currentState hrest]

theorem executeParsedSharedBlockProducers_integer (readState currentState : State)
    (expressions : List ParsedExpr) (updateTurnaround : Bool)
    (integer : expressions.all parsedExprIsIntegerProducer = true) :
    executeParsedSharedBlockProducers readState currentState expressions
        updateTurnaround =
      .ok currentState :=
  executeParsedSharedBlockProducerList_integer readState updateTurnaround expressions
    currentState integer

/-! ## The per-PE walk never touches non-PE state -/

/-- The per-PE integer-producer core preserves block memory, DAR state, L1BM and
matrix registers: its only updates are PE registers, forwarding, forwarding
validity and the PE context. This holds for **any** expression list. -/
theorem executeIntegerProducerLineAtPECore_frame (expressions : List ParsedExpr)
    (state next : State) (pe : PEId)
    (executed : executeIntegerProducerLineAtPECore expressions state pe = .ok next) :
    next.l1bm = state.l1bm ∧ next.blockMemory = state.blockMemory ∧
      next.dar = state.dar ∧ next.matrixRegisters = state.matrixRegisters := by
  rw [executeIntegerProducerLineAtPECore.eq_1] at executed
  split at executed
  · simp at executed
  · simp at executed
  · split at executed
    · simp at executed
    · simp at executed
    · simp only [updateSupportedPELineForwarding] at executed
      split at executed
      · simp at executed
      · simp at executed
      · simp only [StepResult.ok.injEq] at executed
        subst executed
        exact ⟨rfl, rfl, rfl, rfl⟩

theorem executeIntegerProducerLineAtPE_frame (expressions : List ParsedExpr)
    (state next : State) (pe : PEId)
    (executed : executeIntegerProducerLineAtPE expressions state pe = .ok next) :
    next.l1bm = state.l1bm ∧ next.blockMemory = state.blockMemory ∧
      next.dar = state.dar ∧ next.matrixRegisters = state.matrixRegisters := by
  unfold executeIntegerProducerLineAtPE at executed
  split at executed
  · simp at executed
  · exact executeIntegerProducerLineAtPECore_frame expressions state next pe executed

theorem executeIntegerProducerLineAtPEs_frame (expressions : List ParsedExpr)
    (pes : List PEId) (state next : State)
    (executed : executeIntegerProducerLineAtPEs expressions pes state = .ok next) :
    next.l1bm = state.l1bm ∧ next.blockMemory = state.blockMemory ∧
      next.dar = state.dar ∧ next.matrixRegisters = state.matrixRegisters := by
  induction pes generalizing state with
  | nil =>
      simp [executeIntegerProducerLineAtPEs] at executed
      subst executed
      exact ⟨rfl, rfl, rfl, rfl⟩
  | cons pe rest ih =>
      simp only [executeIntegerProducerLineAtPEs] at executed
      split at executed
      · simp at executed
      · simp at executed
      · rename_i intermediate headExecuted
        have head := executeIntegerProducerLineAtPE_frame expressions state intermediate pe
          headExecuted
        have tail := ih intermediate executed
        exact ⟨tail.1.trans head.1, tail.2.1.trans head.2.1,
          tail.2.2.1.trans head.2.2.1, tail.2.2.2.trans head.2.2.2⟩

/-! ## Plain integer-ALU expression lists -/

/-- Integer ALU producer with every special ALU family excluded: legacy
Rust-unsupported names, MSL/MSR, float-relu and block-float ALUs. -/
def parsedExprIsPlainIntegerALU (expression : ParsedExpr) : Bool :=
  parsedExprIsIntegerProducer expression &&
    !parsedExprIsUnsupportedRustAlu expression &&
    !parsedExprIsMslMsrProducer expression &&
    !parsedExprIsFloatReluProducer expression &&
    !parsedExprIsBlockFloatProducer expression

theorem parsedExprIsPlainIntegerALU_facts (expression : ParsedExpr)
    (h : parsedExprIsPlainIntegerALU expression = true) :
    parsedExprIsIntegerProducer expression = true ∧
    parsedExprIsUnsupportedRustAlu expression = false ∧
    parsedExprIsMslMsrProducer expression = false ∧
    parsedExprIsFloatReluProducer expression = false ∧
    parsedExprIsBlockFloatProducer expression = false ∧
    parsedExprIsSupportedPELineProducer expression = true ∧
    parsedExprWaitTag? expression = none ∧
    parsedExprIsMatrixMAUProducer expression = false ∧
    parsedExprIsMatrixWriteProducer expression = false ∧
    parsedExprIsL1ToPEProducer expression = false ∧
    parsedExprIsL2BMProducer expression = false ∧
    parsedExprIsNoForwardProducer expression = false ∧
    parsedExprMayWriteL1BMTurnaround expression = false := by
  cases expression with
  | mk op sources destinations flush text =>
      cases op <;>
        simp_all [parsedExprIsPlainIntegerALU, parsedExprIsIntegerProducer,
          parsedExprIsUnsupportedRustAlu, parsedExprIsMslMsrProducer,
          parsedExprIsFloatReluProducer, parsedExprIsBlockFloatProducer,
          parsedExprIsSupportedPELineProducer, parsedExprWaitTag?,
          parsedExprIsMatrixMAUProducer, parsedExprIsMatrixWriteProducer,
          parsedExprIsL1ToPEProducer, parsedExprIsL2BMProducer,
          parsedExprIsNoForwardProducer, parsedExprMayWriteL1BMTurnaround,
          parsedOpMayWriteL1BMTurnaround]

theorem plainIntegerALU_list_facts (expressions : List ParsedExpr) (state : State)
    (h : expressions.all parsedExprIsPlainIntegerALU = true) :
    expressions.all parsedExprIsIntegerProducer = true ∧
    expressions.all parsedExprIsSupportedPELineProducer = true ∧
    expressions.any parsedExprIsUnsupportedRustAlu = false ∧
    expressions.any (parsedExprWaitPending state) = false ∧
    expressions.filter parsedExprIsMslMsrProducer = [] ∧
    expressions.filter parsedExprIsFloatReluProducer = [] ∧
    expressions.filter parsedExprIsBlockFloatProducer = [] ∧
    expressions.filter parsedExprIsMatrixMAUProducer = [] ∧
    expressions.any parsedExprIsMatrixWriteProducer = false ∧
    expressions.filter parsedExprIsL1ToPEProducer = [] ∧
    expressions.any parsedExprIsNoForwardProducer = false ∧
    expressions.any parsedExprMayWriteL1BMTurnaround = false := by
  have all := List.all_eq_true.mp h
  have facts : ∀ e, e ∈ expressions →
      parsedExprIsIntegerProducer e = true ∧
      parsedExprIsUnsupportedRustAlu e = false ∧
      parsedExprIsMslMsrProducer e = false ∧
      parsedExprIsFloatReluProducer e = false ∧
      parsedExprIsBlockFloatProducer e = false ∧
      parsedExprIsSupportedPELineProducer e = true ∧
      parsedExprWaitTag? e = none ∧
      parsedExprIsMatrixMAUProducer e = false ∧
      parsedExprIsMatrixWriteProducer e = false ∧
      parsedExprIsL1ToPEProducer e = false ∧
      parsedExprIsL2BMProducer e = false ∧
      parsedExprIsNoForwardProducer e = false ∧
      parsedExprMayWriteL1BMTurnaround e = false :=
    fun e he => parsedExprIsPlainIntegerALU_facts e (all e he)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact List.all_eq_true.mpr fun e he => (facts e he).1
  · exact List.all_eq_true.mpr fun e he => (facts e he).2.2.2.2.2.1
  · exact List.any_eq_false.mpr fun e he => by
      simpa using (facts e he).2.1
  · exact List.any_eq_false.mpr fun e he => by
      simp [parsedExprWaitPending, (facts e he).2.2.2.2.2.2.1]
  · exact List.filter_eq_nil_iff.mpr fun e he => by
      simpa using (facts e he).2.2.1
  · exact List.filter_eq_nil_iff.mpr fun e he => by
      simpa using (facts e he).2.2.2.1
  · exact List.filter_eq_nil_iff.mpr fun e he => by
      simpa using (facts e he).2.2.2.2.1
  · exact List.filter_eq_nil_iff.mpr fun e he => by
      simpa using (facts e he).2.2.2.2.2.2.2.1
  · exact List.any_eq_false.mpr fun e he => by
      simpa using (facts e he).2.2.2.2.2.2.2.2.1
  · exact List.filter_eq_nil_iff.mpr fun e he => by
      simpa using (facts e he).2.2.2.2.2.2.2.2.2.1
  · exact List.any_eq_false.mpr fun e he => by
      simpa using (facts e he).2.2.2.2.2.2.2.2.2.2.2.1
  · exact List.any_eq_false.mpr fun e he => by
      simpa using (facts e he).2.2.2.2.2.2.2.2.2.2.2.2

/-! ## Step equation -/

/-- All stages of the plain-integer PE step except the per-PE walk are the
identity; the bundle also records the derived list-level facts. -/
theorem plainIntegerALU_stage_identities (normalizedExpressions : List NormalizedExpr)
    (state : State)
    (plain : (normalizedExpressions.map NormalizedExpr.toParsed).all
      parsedExprIsPlainIntegerALU = true) :
    (∀ currentState,
      executeParsedMslMsrProducers state currentState
        (normalizedExpressions.map NormalizedExpr.toParsed) false
        (normalizedExpressions.any (parsedExprHasSingleLineWriteMask ∘ NormalizedExpr.toParsed))
        = .ok currentState) ∧
    (∀ currentState,
      executeParsedFloatReluProducers state currentState
        (normalizedExpressions.map NormalizedExpr.toParsed) false
        (normalizedExpressions.any (parsedExprHasSingleLineWriteMask ∘ NormalizedExpr.toParsed))
        = .ok currentState) ∧
    (∀ currentState,
      executeParsedBlockFloatProducer state currentState
        (normalizedExpressions.map NormalizedExpr.toParsed) false
        (normalizedExpressions.any (parsedExprHasSingleLineWriteMask ∘ NormalizedExpr.toParsed))
        = .ok currentState) ∧
    (∀ currentState,
      executeParsedMatrixMAUAndWrites state currentState
        (normalizedExpressions.map NormalizedExpr.toParsed) false
        (normalizedExpressions.any (parsedExprHasSingleLineWriteMask ∘ NormalizedExpr.toParsed))
        = .ok currentState) ∧
    (∀ currentState,
      executeParsedSharedBlockProducers state currentState
        (normalizedExpressions.map NormalizedExpr.toParsed) true = .ok currentState) ∧
    (∀ currentState,
      executeParsedL1ToPEProducers state currentState
        (normalizedExpressions.map NormalizedExpr.toParsed) false
        (normalizedExpressions.any (parsedExprHasSingleLineWriteMask ∘ NormalizedExpr.toParsed))
        (parsedL1ToPEPrecedesOMRWriter
          (normalizedExpressions.map NormalizedExpr.toParsed)) = .ok currentState) ∧
    normalizedExpressions.all
      (parsedExprIsSupportedPELineProducer ∘ NormalizedExpr.toParsed) = true ∧
    normalizedExpressions.any
      (parsedExprIsUnsupportedRustAlu ∘ NormalizedExpr.toParsed) = false ∧
    normalizedExpressions.any
      ((parsedExprWaitPending state) ∘ NormalizedExpr.toParsed) = false ∧
    normalizedExpressions.any
      (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed) = false ∧
    normalizedExpressions.any
      (parsedExprMayWriteL1BMTurnaround ∘ NormalizedExpr.toParsed) = false ∧
    ¬ (∃ x ∈ normalizedExpressions,
      parsedExprIsNoForwardProducer x.toParsed = true) := by
  obtain ⟨integers, supported, noUnsupported, waits, mslEmpty, reluEmpty, blockEmpty,
    mauEmpty, noWrite, l1ToPEEmpty, noForwardAbsent, noTurnaroundAbsent⟩ :=
    plainIntegerALU_list_facts (normalizedExpressions.map NormalizedExpr.toParsed) state
      (by simpa using plain)
  have supportedAny : normalizedExpressions.all
      (parsedExprIsSupportedPELineProducer ∘ NormalizedExpr.toParsed) = true := by
    simpa [List.all_map] using supported
  have noUnsupportedAny : normalizedExpressions.any
      (parsedExprIsUnsupportedRustAlu ∘ NormalizedExpr.toParsed) = false := by
    simpa [List.any_map] using noUnsupported
  have waitsAny : normalizedExpressions.any
      ((parsedExprWaitPending state) ∘ NormalizedExpr.toParsed) = false := by
    simpa [List.any_map] using waits
  have noForwardAny : normalizedExpressions.any
      (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed) = false := by
    simpa [List.any_map] using noForwardAbsent
  have noTurnaroundAny : normalizedExpressions.any
      (parsedExprMayWriteL1BMTurnaround ∘ NormalizedExpr.toParsed) = false := by
    simpa [List.any_map] using noTurnaroundAbsent
  have noForwardExists : ¬ (∃ x ∈ normalizedExpressions,
      parsedExprIsNoForwardProducer x.toParsed = true) := by
    rw [← List.any_eq_true]
    simpa [List.any_map] using noForwardAbsent
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, supportedAny, noUnsupportedAny, waitsAny,
    noForwardAny, noTurnaroundAny, noForwardExists⟩
  · intro currentState
    exact executeParsedMslMsrProducers_nil state currentState
      (normalizedExpressions.map NormalizedExpr.toParsed) false _
      mslEmpty
  · intro currentState
    exact executeParsedFloatReluProducers_nil state currentState
      (normalizedExpressions.map NormalizedExpr.toParsed) false _
      reluEmpty
  · intro currentState
    exact executeParsedBlockFloatProducer_nil state currentState
      (normalizedExpressions.map NormalizedExpr.toParsed) false _
      blockEmpty
  · intro currentState
    exact executeParsedMatrixMAUAndWrites_id state currentState
      (normalizedExpressions.map NormalizedExpr.toParsed) false _
      mauEmpty noWrite
  · intro currentState
    exact executeParsedSharedBlockProducers_integer state currentState
      (normalizedExpressions.map NormalizedExpr.toParsed) true integers
  · intro currentState
    exact executeParsedL1ToPEProducers_nil state currentState
      (normalizedExpressions.map NormalizedExpr.toParsed) false _
      (parsedL1ToPEPrecedesOMRWriter
        (normalizedExpressions.map NormalizedExpr.toParsed)) l1ToPEEmpty

/-- Step equation with the per-PE stage result supplied. -/
theorem executeIntegerProducerInstructionLine_pe_plainIntegerALU
    (normalizedExpressions : List NormalizedExpr) (state nextPEs : State)
    (accepted : checkParsedTopLine
      (InstructionLine.pe normalizedExpressions).toParsed = true)
    (plain : (normalizedExpressions.map NormalizedExpr.toParsed).all
      parsedExprIsPlainIntegerALU = true)
    (executed : executeIntegerProducerLineAtPEs
      ((normalizedExpressions.map NormalizedExpr.toParsed).filter (fun expression =>
        !parsedExprIsL2BMProducer expression && !parsedExprIsMslMsrProducer expression &&
          !parsedExprIsMatrixMAUProducer expression &&
          !parsedExprIsBlockFloatProducer expression &&
          !parsedExprIsFloatReluProducer expression))
      (List.finRange 4096) state = .ok nextPEs) :
    executeIntegerProducerInstructionLine (.pe normalizedExpressions) state =
      .ok { nextPEs with
        hazardClock := nextPEs.hazardClock + InstructionLine.cost (.pe normalizedExpressions)
        l1bmTurnaroundValid := false } := by
  obtain ⟨mslId, reluId, blockId, matrixId, sharedId, l1ToPEId, supportedAny,
    noUnsupportedAny, waitsAny, noForwardAny, noTurnaroundAny, noForwardExists⟩ :=
    plainIntegerALU_stage_identities normalizedExpressions state plain
  simp [executeIntegerProducerInstructionLine, accepted, supportedAny, noUnsupportedAny,
    waitsAny, mslId, reluId, blockId, matrixId, sharedId, l1ToPEId,
    noForwardAny, noTurnaroundAny]
  rw [executed]

/-- Extraction of the per-PE stage from a successful plain-integer PE step. -/
theorem executeIntegerProducerInstructionLine_pe_plainIntegerALU_exists
    (normalizedExpressions : List NormalizedExpr) (state next : State)
    (accepted : checkParsedTopLine
      (InstructionLine.pe normalizedExpressions).toParsed = true)
    (plain : (normalizedExpressions.map NormalizedExpr.toParsed).all
      parsedExprIsPlainIntegerALU = true)
    (success : executeIntegerProducerInstructionLine (.pe normalizedExpressions) state
      = .ok next) :
    ∃ nextPEs,
      executeIntegerProducerLineAtPEs
        ((normalizedExpressions.map NormalizedExpr.toParsed).filter (fun expression =>
          !parsedExprIsL2BMProducer expression && !parsedExprIsMslMsrProducer expression &&
            !parsedExprIsMatrixMAUProducer expression &&
            !parsedExprIsBlockFloatProducer expression &&
            !parsedExprIsFloatReluProducer expression))
        (List.finRange 4096) state = .ok nextPEs ∧
      next = { nextPEs with
        hazardClock := nextPEs.hazardClock + InstructionLine.cost (.pe normalizedExpressions)
        l1bmTurnaroundValid := false } := by
  obtain ⟨mslId, reluId, blockId, matrixId, sharedId, l1ToPEId, supportedAny,
    noUnsupportedAny, waitsAny, noForwardAny, noTurnaroundAny, noForwardExists⟩ :=
    plainIntegerALU_stage_identities normalizedExpressions state plain
  unfold executeIntegerProducerInstructionLine at success
  simp [accepted, supportedAny, noUnsupportedAny, waitsAny, mslId, reluId, blockId,
    matrixId, sharedId, l1ToPEId, noForwardAny, noTurnaroundAny] at success
  split at success
  · simp at success
  · simp at success
  · rename_i nextPEs executed
    exact ⟨nextPEs, executed, by
      simp only [StepResult.ok.injEq] at success
      exact success.symm⟩

open Issue
open PEMemory

theorem prepareParsedIntegerMatrixReadLineExpression_noforward
    (files : PEMemory.IntegerRegisterFiles)
    (oldSlots nextSlots : Forwarding.Slots) (store : PEMemory.ParsedMatrixReadStore)
    (expression : ParsedExpr) (control : ParsedMaskExecutionControl)
    (hasSingleLineMask noForward reduced : Bool)
    (isNoforward : expression.op = .noforward) :
    PEMemory.prepareParsedIntegerMatrixReadLineExpression files oldSlots nextSlots store
        expression control hasSingleLineMask noForward reduced =
      .ok ([], nextSlots, []) := by
  cases expression with
  | mk op sources destinations flush text =>
      rw [show op = .noforward from isNoforward]
      rfl

theorem prepareParsedIntegerMatrixReadLineExpressions_noforward
    (files : PEMemory.IntegerRegisterFiles) (oldSlots : Forwarding.Slots)
    (store : PEMemory.ParsedMatrixReadStore) (control : ParsedMaskExecutionControl)
    (hasSingleLineMask noForward reduced : Bool) :
    ∀ (expressions : List ParsedExpr),
      (∀ expression ∈ expressions, expression.op = .noforward) →
      ∀ (writes : List PEMemory.PreparedParsedMaskedWrite)
        (nextSlots : Forwarding.Slots) (barUpdates : List (Bool × BitVec 12)),
        PEMemory.prepareParsedIntegerMatrixReadLineExpressions files oldSlots store control
          hasSingleLineMask noForward reduced expressions writes nextSlots barUpdates =
        .ok (writes, nextSlots, barUpdates)
  | [], _ => by simp [PEMemory.prepareParsedIntegerMatrixReadLineExpressions]
  | expression :: rest, all => by
      have headAll : expression.op = .noforward := all expression (by simp)
      have restAll : ∀ item ∈ rest, item.op = .noforward := by
        intro item member
        exact all item (by simp [member])
      intro writes nextSlots barUpdates
      have head := prepareParsedIntegerMatrixReadLineExpression_noforward files oldSlots
        nextSlots store expression control hasSingleLineMask noForward reduced headAll
      simp [PEMemory.prepareParsedIntegerMatrixReadLineExpressions, head,
        prepareParsedIntegerMatrixReadLineExpressions_noforward files oldSlots store control
          hasSingleLineMask noForward reduced rest restAll writes nextSlots barUpdates]

theorem prepareParsedIntegerMatrixReadLineCycles_noforward
    (files : PEMemory.IntegerRegisterFiles) (oldSlots : Forwarding.Slots)
    (store : PEMemory.ParsedMatrixReadStore) (control : ParsedMaskExecutionControl)
    (reduced : Bool) (expressions : List ParsedExpr)
    (all : ∀ expression ∈ expressions, expression.op = .noforward) :
    PEMemory.prepareParsedIntegerMatrixReadLineCycles files oldSlots store expressions
        control reduced =
      .ok ([], oldSlots, []) := by
  unfold PEMemory.prepareParsedIntegerMatrixReadLineCycles
  exact prepareParsedIntegerMatrixReadLineExpressions_noforward files oldSlots store control
    (expressions.any parsedExprHasSingleLineWriteMask)
    (expressions.any fun expression =>
      match expression.op with | .noforward => true | _ => false)
    reduced expressions all [] oldSlots []

theorem parsedIntegerMatrixReadLineFourCycleStep_noforward
    (files : PEMemory.IntegerRegisterFiles) (slots : Forwarding.Slots)
    (store : PEMemory.ParsedMatrixReadStore) (expressions : List ParsedExpr)
    (control : ParsedMaskExecutionControl) (reduced : Bool)
    (all : ∀ expression ∈ expressions, expression.op = .noforward) :
    PEMemory.parsedIntegerMatrixReadLineFourCycleStep files slots store expressions
        control reduced =
      .ok (files, slots, []) := by
  unfold PEMemory.parsedIntegerMatrixReadLineFourCycleStep
  rw [prepareParsedIntegerMatrixReadLineCycles_noforward files slots store control reduced
    expressions all]
  simp [PEMemory.commitParsedMaskedWrites]



open Issue
open PEMemory

theorem executeParsedFloatMAUsAtPE_noforward
    (readState currentFiles : PEMemory.IntegerRegisterFiles)
    (oldSlots : Forwarding.Slots) (context : PEMemory.ParsedIntegerContext)
    (expressions : List ParsedExpr) (directive : ParsedMaskDirective)
    (hasSingleLineMask : Bool)
    (floatEmpty : expressions.filter parsedExprIsSupportedFloatMAUProducer = []) :
    executeParsedFloatMAUsAtPE readState currentFiles oldSlots context expressions
        directive hasSingleLineMask =
      .ok (currentFiles, context.bar0, context.bar1,
        (fun _ => (⟨0, 0⟩ : IntegerALU.Bus)), false) := by
  unfold executeParsedFloatMAUsAtPE
  simp only [floatEmpty, List.isEmpty, Bool.not_true]
  rfl



open Issue
open PEMemory

theorem parsedExprIsIntegerMatrixReadStageInput_noforward (expression : ParsedExpr)
    (h : expression.op = .noforward) :
    parsedExprIsIntegerMatrixReadStageInput expression = true := by
  cases expression with
  | mk op sources destinations flush text =>
      rw [show op = .noforward from h]
      rfl

theorem parsedExprIsSupportedFloatMAUProducer_noforward (expression : ParsedExpr)
    (h : expression.op = .noforward) :
    parsedExprIsSupportedFloatMAUProducer expression = false := by
  cases expression with
  | mk op sources destinations flush text =>
      rw [show op = .noforward from h]
      rfl

theorem parsedExprIsIntegerBARWriter_noforward (expression : ParsedExpr)
    (h : expression.op = .noforward) :
    parsedExprIsIntegerBARWriter expression = false := by
  cases expression with
  | mk op sources destinations flush text =>
      rw [show op = .noforward from h]
      rfl

theorem parsedExprIsIntegerProducer_noforward (expression : ParsedExpr)
    (h : expression.op = .noforward) :
    parsedExprIsIntegerProducer expression = false := by
  cases expression with
  | mk op sources destinations flush text =>
      rw [show op = .noforward from h]
      rfl

theorem parsedExprIsMatrixReadProducer_noforward (expression : ParsedExpr)
    (h : expression.op = .noforward) :
    parsedExprIsMatrixReadProducer expression = false := by
  cases expression with
  | mk op sources destinations flush text =>
      rw [show op = .noforward from h]
      rfl

theorem parsedFloatMAUWritesBAR_noforward (lm1 : Bool) (expression : ParsedExpr)
    (h : expression.op = .noforward) :
    parsedFloatMAUWritesBAR lm1 expression = false := by
  unfold parsedFloatMAUWritesBAR
  rw [parsedExprIsSupportedFloatMAUProducer_noforward expression h]
  simp

theorem updateSupportedPELineForwarding_noforward_absent
    (old prepared : Forwarding.Slots) :
    updateSupportedPELineForwarding old prepared true false false false = .ok old := by
  unfold updateSupportedPELineForwarding
  rfl



open Issue
open PEMemory

theorem executeIntegerProducerLineAtPECore_peRegisters_noforward
    (expressions : List ParsedExpr) (state next : State) (pe : PEId)
    (all : ∀ expression ∈ expressions, expression.op = .noforward)
    (executed : executeIntegerProducerLineAtPECore expressions state pe = .ok next) :
    next.peRegisters = state.peRegisters := by
  have filterStage : expressions.filter parsedExprIsIntegerMatrixReadStageInput = expressions :=
    List.filter_eq_self.mpr fun expression member =>
      parsedExprIsIntegerMatrixReadStageInput_noforward expression (all expression member)
  have filterFloat : expressions.filter parsedExprIsSupportedFloatMAUProducer = [] :=
    List.filter_eq_nil_iff.mpr fun expression member => by
      rw [parsedExprIsSupportedFloatMAUProducer_noforward expression (all expression member)]
      simp
  rw [executeIntegerProducerLineAtPECore.eq_1] at executed
  rw [filterStage] at executed
  rw [parsedIntegerMatrixReadLineFourCycleStep_noforward (expressions := expressions)
    (all := all)] at executed
  simp only [] at executed
  rw [executeParsedFloatMAUsAtPE_noforward (floatEmpty := filterFloat)] at executed
  simp only [] at executed
  split at executed
  · simp at executed
  · simp at executed
  · simp only [StepResult.ok.injEq] at executed
    subst executed
    funext other
    by_cases h : other = pe <;> simp [h]



open Issue
open PEMemory

theorem parsedExprIsMslMsrProducer_noforward (expression : ParsedExpr)
    (h : expression.op = .noforward) : parsedExprIsMslMsrProducer expression = false := by
  cases expression with
  | mk op sources destinations flush text =>
      rw [show op = .noforward from h]; rfl

theorem parsedExprIsFloatReluProducer_noforward (expression : ParsedExpr)
    (h : expression.op = .noforward) : parsedExprIsFloatReluProducer expression = false := by
  cases expression with
  | mk op sources destinations flush text =>
      rw [show op = .noforward from h]; rfl

theorem parsedExprIsBlockFloatProducer_noforward (expression : ParsedExpr)
    (h : expression.op = .noforward) : parsedExprIsBlockFloatProducer expression = false := by
  cases expression with
  | mk op sources destinations flush text =>
      rw [show op = .noforward from h]; rfl

theorem parsedExprIsMatrixMAUProducer_noforward (expression : ParsedExpr)
    (h : expression.op = .noforward) : parsedExprIsMatrixMAUProducer expression = false := by
  cases expression with
  | mk op sources destinations flush text =>
      rw [show op = .noforward from h]; rfl

theorem parsedExprIsMatrixWriteProducer_noforward (expression : ParsedExpr)
    (h : expression.op = .noforward) : parsedExprIsMatrixWriteProducer expression = false := by
  cases expression with
  | mk op sources destinations flush text =>
      rw [show op = .noforward from h]; rfl

theorem parsedExprIsL1ToPEProducer_noforward (expression : ParsedExpr)
    (h : expression.op = .noforward) : parsedExprIsL1ToPEProducer expression = false := by
  cases expression with
  | mk op sources destinations flush text =>
      rw [show op = .noforward from h]; rfl

theorem parsedExprWaitTag_noforward (expression : ParsedExpr)
    (h : expression.op = .noforward) : parsedExprWaitTag? expression = none := by
  cases expression with
  | mk op sources destinations flush text =>
      rw [show op = .noforward from h]; rfl

theorem parsedExprIsSupportedPELineProducer_noforward (expression : ParsedExpr)
    (h : expression.op = .noforward) :
    parsedExprIsSupportedPELineProducer expression = true := by
  cases expression with
  | mk op sources destinations flush text =>
      rw [show op = .noforward from h]; rfl

theorem parsedExprIsUnsupportedRustAlu_noforward (expression : ParsedExpr)
    (h : expression.op = .noforward) : parsedExprIsUnsupportedRustAlu expression = false := by
  cases expression with
  | mk op sources destinations flush text =>
      rw [show op = .noforward from h]; rfl

theorem parsedExprIsNoForwardProducer_noforward (expression : ParsedExpr)
    (h : expression.op = .noforward) : parsedExprIsNoForwardProducer expression = true := by
  cases expression with
  | mk op sources destinations flush text =>
      rw [show op = .noforward from h]; rfl

theorem executeParsedSharedBlockExpression_noforward (readState currentState : State)
    (expression : ParsedExpr) (updateTurnaround : Bool)
    (h : expression.op = .noforward) :
    executeParsedSharedBlockExpression readState currentState expression updateTurnaround =
      .ok currentState := by
  cases expression with
  | mk op sources destinations flush text =>
      rw [show op = .noforward from h]
      rfl

theorem executeParsedSharedBlockProducerList_noforward (readState : State)
    (updateTurnaround : Bool) :
    ∀ (expressions : List ParsedExpr) (currentState : State),
      (∀ expression ∈ expressions, expression.op = .noforward) →
      executeParsedSharedBlockProducerList readState updateTurnaround expressions currentState =
        .ok currentState
  | [], currentState, _ => by simp [executeParsedSharedBlockProducerList]
  | expression :: rest, currentState, h => by
      have headAll : expression.op = .noforward := h expression (by simp)
      have restAll : ∀ item ∈ rest, item.op = .noforward := by
        intro item member
        exact h item (by simp [member])
      have head := executeParsedSharedBlockExpression_noforward readState currentState
        expression updateTurnaround headAll
      simp [executeParsedSharedBlockProducerList, head,
        executeParsedSharedBlockProducerList_noforward readState updateTurnaround rest
          currentState restAll]



open Issue
open PEMemory

theorem executeIntegerProducerLineAtPE_peRegisters_noforward
    (expressions : List ParsedExpr) (state next : State) (pe : PEId)
    (all : ∀ expression ∈ expressions, expression.op = .noforward)
    (executed : executeIntegerProducerLineAtPE expressions state pe = .ok next) :
    next.peRegisters = state.peRegisters := by
  have anyBAR : expressions.any parsedExprIsIntegerBARWriter = false :=
    List.any_eq_false.mpr fun expression member => by
      rw [parsedExprIsIntegerBARWriter_noforward expression (all expression member)]
      simp
  unfold executeIntegerProducerLineAtPE at executed
  simp [anyBAR] at executed
  exact executeIntegerProducerLineAtPECore_peRegisters_noforward expressions state next pe
    all executed

theorem executeIntegerProducerLineAtPEs_peRegisters_noforward
    (expressions : List ParsedExpr) (pes : List PEId) (state next : State)
    (all : ∀ expression ∈ expressions, expression.op = .noforward)
    (executed : executeIntegerProducerLineAtPEs expressions pes state = .ok next) :
    next.peRegisters = state.peRegisters := by
  induction pes generalizing state with
  | nil =>
      simp [executeIntegerProducerLineAtPEs] at executed
      subst executed
      rfl
  | cons pe rest ih =>
      simp only [executeIntegerProducerLineAtPEs] at executed
      split at executed
      · simp at executed
      · simp at executed
      · rename_i intermediate headExecuted
        have head := executeIntegerProducerLineAtPE_peRegisters_noforward expressions
          state intermediate pe all headExecuted
        have tail := ih intermediate executed
        exact tail.trans head

theorem noforward_list_facts (expressions : List ParsedExpr)
    (all : ∀ expression ∈ expressions, expression.op = .noforward) :
    expressions.all parsedExprIsSupportedPELineProducer = true ∧
    expressions.any parsedExprIsUnsupportedRustAlu = false ∧
    (∀ state, expressions.any (parsedExprWaitPending state) = false) ∧
    expressions.any parsedExprIsMatrixWriteProducer = false := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact List.all_eq_true.mpr fun e he => by
      rw [parsedExprIsSupportedPELineProducer_noforward e (all e he)]
  · exact List.any_eq_false.mpr fun e he => by
      rw [parsedExprIsUnsupportedRustAlu_noforward e (all e he)]
      simp
  · intro state
    exact List.any_eq_false.mpr fun e he => by
      simp [parsedExprWaitPending, parsedExprWaitTag_noforward e (all e he)]
  · exact List.any_eq_false.mpr fun e he => by
      rw [parsedExprIsMatrixWriteProducer_noforward e (all e he)]
      simp

theorem noforward_stage_identities (normalizedExpressions : List NormalizedExpr)
    (all : ∀ expression ∈ normalizedExpressions.map NormalizedExpr.toParsed,
      expression.op = .noforward) :
    (∀ (currentState : State) (noForward : Bool),
      executeParsedMslMsrProducers state currentState
        (normalizedExpressions.map NormalizedExpr.toParsed) noForward
        (normalizedExpressions.any (parsedExprHasSingleLineWriteMask ∘ NormalizedExpr.toParsed))
        = .ok currentState) ∧
    (∀ (currentState : State) (noForward : Bool),
      executeParsedFloatReluProducers state currentState
        (normalizedExpressions.map NormalizedExpr.toParsed) noForward
        (normalizedExpressions.any (parsedExprHasSingleLineWriteMask ∘ NormalizedExpr.toParsed))
        = .ok currentState) ∧
    (∀ (currentState : State) (noForward : Bool),
      executeParsedBlockFloatProducer state currentState
        (normalizedExpressions.map NormalizedExpr.toParsed) noForward
        (normalizedExpressions.any (parsedExprHasSingleLineWriteMask ∘ NormalizedExpr.toParsed))
        = .ok currentState) ∧
    (∀ (currentState : State) (noForward : Bool),
      executeParsedMatrixMAUAndWrites state currentState
        (normalizedExpressions.map NormalizedExpr.toParsed) noForward
        (normalizedExpressions.any (parsedExprHasSingleLineWriteMask ∘ NormalizedExpr.toParsed))
        = .ok currentState) ∧
    (∀ (currentState : State) (updateTurnaround : Bool),
      executeParsedSharedBlockProducers state currentState
        (normalizedExpressions.map NormalizedExpr.toParsed) updateTurnaround
        = .ok currentState) ∧
    (∀ (currentState : State) (noForward : Bool),
      executeParsedL1ToPEProducers state currentState
        (normalizedExpressions.map NormalizedExpr.toParsed) noForward
        (normalizedExpressions.any (parsedExprHasSingleLineWriteMask ∘ NormalizedExpr.toParsed))
        (parsedL1ToPEPrecedesOMRWriter
          (normalizedExpressions.map NormalizedExpr.toParsed)) = .ok currentState) := by
  have mslEmpty : (normalizedExpressions.map NormalizedExpr.toParsed).filter
      parsedExprIsMslMsrProducer = [] := by
    exact List.filter_eq_nil_iff.mpr fun e he => by
      rw [parsedExprIsMslMsrProducer_noforward e (all e he)]; simp
  have reluEmpty : (normalizedExpressions.map NormalizedExpr.toParsed).filter
      parsedExprIsFloatReluProducer = [] := by
    exact List.filter_eq_nil_iff.mpr fun e he => by
      rw [parsedExprIsFloatReluProducer_noforward e (all e he)]; simp
  have blockEmpty : (normalizedExpressions.map NormalizedExpr.toParsed).filter
      parsedExprIsBlockFloatProducer = [] := by
    exact List.filter_eq_nil_iff.mpr fun e he => by
      rw [parsedExprIsBlockFloatProducer_noforward e (all e he)]; simp
  have mauEmpty : (normalizedExpressions.map NormalizedExpr.toParsed).filter
      parsedExprIsMatrixMAUProducer = [] := by
    exact List.filter_eq_nil_iff.mpr fun e he => by
      rw [parsedExprIsMatrixMAUProducer_noforward e (all e he)]; simp
  have noWrite : (normalizedExpressions.map NormalizedExpr.toParsed).any
      parsedExprIsMatrixWriteProducer = false := by
    exact List.any_eq_false.mpr fun e he => by
      rw [parsedExprIsMatrixWriteProducer_noforward e (all e he)]
      simp
  have l1ToPEEmpty : (normalizedExpressions.map NormalizedExpr.toParsed).filter
      parsedExprIsL1ToPEProducer = [] := by
    exact List.filter_eq_nil_iff.mpr fun e he => by
      rw [parsedExprIsL1ToPEProducer_noforward e (all e he)]; simp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro currentState noForward
    exact executeParsedMslMsrProducers_nil state currentState
      (normalizedExpressions.map NormalizedExpr.toParsed) noForward _ mslEmpty
  · intro currentState noForward
    exact executeParsedFloatReluProducers_nil state currentState
      (normalizedExpressions.map NormalizedExpr.toParsed) noForward _ reluEmpty
  · intro currentState noForward
    exact executeParsedBlockFloatProducer_nil state currentState
      (normalizedExpressions.map NormalizedExpr.toParsed) noForward _ blockEmpty
  · intro currentState noForward
    exact executeParsedMatrixMAUAndWrites_id state currentState
      (normalizedExpressions.map NormalizedExpr.toParsed) noForward _ mauEmpty noWrite
  · intro currentState updateTurnaround
    exact executeParsedSharedBlockProducerList_noforward state updateTurnaround
      (normalizedExpressions.map NormalizedExpr.toParsed) currentState all
  · intro currentState noForward
    exact executeParsedL1ToPEProducers_nil state currentState
      (normalizedExpressions.map NormalizedExpr.toParsed) noForward _
      (parsedL1ToPEPrecedesOMRWriter
        (normalizedExpressions.map NormalizedExpr.toParsed)) l1ToPEEmpty
theorem executeIntegerProducerInstructionLine_accepted_of_ok
    (line : InstructionLine) (state next : State)
    (success : executeIntegerProducerInstructionLine line state = .ok next) :
    checkParsedTopLine line.toParsed = true := by
  by_contra h
  have rejected : checkParsedTopLine line.toParsed = false := by simpa using h
  unfold executeIntegerProducerInstructionLine at success
  simp [rejected] at success

theorem executeIntegerProducerInstructionLine_pe_peRegisters_noforward
    (normalizedExpressions : List NormalizedExpr) (state next : State)
    (all : ∀ expression ∈ normalizedExpressions.map NormalizedExpr.toParsed,
      expression.op = .noforward)
    (success : executeIntegerProducerInstructionLine (.pe normalizedExpressions) state
      = .ok next) :
    next.peRegisters = state.peRegisters := by
  have accepted := executeIntegerProducerInstructionLine_accepted_of_ok
    (.pe normalizedExpressions) state next success
  obtain ⟨mslId, reluId, blockId, matrixId, sharedId, l1ToPEId⟩ :=
    noforward_stage_identities normalizedExpressions all
  obtain ⟨supported, noUnsupported, waits, matrixWrite⟩ :=
    noforward_list_facts (normalizedExpressions.map NormalizedExpr.toParsed) all
  have supportedAny : normalizedExpressions.all
      (parsedExprIsSupportedPELineProducer ∘ NormalizedExpr.toParsed) = true := by
    simpa [List.all_map] using supported
  have noUnsupportedAny : normalizedExpressions.any
      (parsedExprIsUnsupportedRustAlu ∘ NormalizedExpr.toParsed) = false := by
    simpa [List.any_map] using noUnsupported
  have waitsAny : normalizedExpressions.any
      ((parsedExprWaitPending state) ∘ NormalizedExpr.toParsed) = false := by
    simpa [List.any_map] using waits state
  have matrixWriteAny : normalizedExpressions.any
      (parsedExprIsMatrixWriteProducer ∘ NormalizedExpr.toParsed) = false := by
    simpa [List.any_map] using matrixWrite
  unfold executeIntegerProducerInstructionLine at success
  simp [accepted, supportedAny, noUnsupportedAny, waitsAny] at success
  split at success
  · cases success
  · cases success
  · rename_i nextPEs executed
    rw [mslId] at success
    dsimp only at success
    rw [reluId] at success
    dsimp only at success
    rw [blockId] at success
    dsimp only at success
    rw [matrixId] at success
    dsimp only at success
    rw [sharedId] at success
    dsimp only at success
    rw [l1ToPEId] at success
    dsimp only at success
    simp only [StepResult.ok.injEq] at success
    rw [← success]
    exact executeIntegerProducerLineAtPEs_peRegisters_noforward
      ((normalizedExpressions.map NormalizedExpr.toParsed).filter fun expression =>
        !parsedExprIsL2BMProducer expression && !parsedExprIsMslMsrProducer expression &&
          !parsedExprIsMatrixMAUProducer expression &&
          !parsedExprIsBlockFloatProducer expression &&
          !parsedExprIsFloatReluProducer expression)
      (List.finRange 4096) state nextPEs
      (fun expression member => all expression (List.mem_filter.mp member).1)
      executed

theorem executeNormalizedLine_pe_peRegisters_noforward
    (normalizedExpressions : List NormalizedExpr) (state next : State)
    (all : ∀ expression ∈ normalizedExpressions.map NormalizedExpr.toParsed,
      expression.op = .noforward)
    (success : executeNormalizedLine (.pe normalizedExpressions) state = .ok next) :
    next.peRegisters = state.peRegisters := by
  simp only [executeNormalizedLine, NormalizedLine.toInstruction?] at success
  exact executeIntegerProducerInstructionLine_pe_peRegisters_noforward
    normalizedExpressions state next all success

theorem executeIntegerProducerInstructionLine_pe_plainIntegerALU_frame
    (normalizedExpressions : List NormalizedExpr) (state next : State)
    (plain : (normalizedExpressions.map NormalizedExpr.toParsed).all
      parsedExprIsPlainIntegerALU = true)
    (success : executeIntegerProducerInstructionLine (.pe normalizedExpressions) state
      = .ok next) :
    next.l1bm = state.l1bm ∧ next.blockMemory = state.blockMemory ∧
      next.dar = state.dar ∧ next.matrixRegisters = state.matrixRegisters := by
  have accepted := executeIntegerProducerInstructionLine_accepted_of_ok
    (.pe normalizedExpressions) state next success
  obtain ⟨nextPEs, executed, nextEq⟩ :=
    executeIntegerProducerInstructionLine_pe_plainIntegerALU_exists
      normalizedExpressions state next accepted plain success
  subst nextEq
  exact executeIntegerProducerLineAtPEs_frame _ (List.finRange 4096) state nextPEs executed

theorem executeNormalizedLine_pe_plainIntegerALU_frame
    (normalizedExpressions : List NormalizedExpr) (state next : State)
    (plain : (normalizedExpressions.map NormalizedExpr.toParsed).all
      parsedExprIsPlainIntegerALU = true)
    (success : executeNormalizedLine (.pe normalizedExpressions) state = .ok next) :
    next.l1bm = state.l1bm ∧ next.blockMemory = state.blockMemory ∧
      next.dar = state.dar ∧ next.matrixRegisters = state.matrixRegisters := by
  simp only [executeNormalizedLine, NormalizedLine.toInstruction?] at success
  exact executeIntegerProducerInstructionLine_pe_plainIntegerALU_frame
    normalizedExpressions state next plain success


theorem updateSupportedPELineForwarding_noforward_any
    (old prepared : Forwarding.Slots) (expressions : List ParsedExpr)
    (anyNoforward : (expressions.any fun expression =>
      match expression.op with | .noforward => true | _ => false) = true) :
    updateSupportedPELineForwarding old prepared
      (expressions.any fun expression =>
        match expression.op with | .noforward => true | _ => false)
      false false false = .ok old := by
  rw [anyNoforward]
  exact updateSupportedPELineForwarding_noforward_absent old prepared

theorem executeIntegerProducerLineAtPECore_forwarding_noforward
    (expressions : List ParsedExpr) (state next : State) (pe : PEId)
    (all : ∀ expression ∈ expressions, expression.op = .noforward)
    (anyNoforward : (expressions.any fun expression =>
      match expression.op with | .noforward => true | _ => false) = true)
    (executed : executeIntegerProducerLineAtPECore expressions state pe = .ok next) :
    next.forwarding pe = stateForwardingSlots state pe ∧
      ∀ other, other ≠ pe → next.forwarding other = state.forwarding other := by
  have filterStage : expressions.filter parsedExprIsIntegerMatrixReadStageInput = expressions :=
    List.filter_eq_self.mpr fun expression member =>
      parsedExprIsIntegerMatrixReadStageInput_noforward expression (all expression member)
  have filterFloat : expressions.filter parsedExprIsSupportedFloatMAUProducer = [] :=
    List.filter_eq_nil_iff.mpr fun expression member => by
      rw [parsedExprIsSupportedFloatMAUProducer_noforward expression (all expression member)]
      simp
  have anyALU : expressions.any parsedExprIsIntegerProducer = false :=
    List.any_eq_false.mpr fun expression member => by
      rw [parsedExprIsIntegerProducer_noforward expression (all expression member)]
      simp
  have anyMatrixRead : expressions.any parsedExprIsMatrixReadProducer = false :=
    List.any_eq_false.mpr fun expression member => by
      rw [parsedExprIsMatrixReadProducer_noforward expression (all expression member)]
      simp
  rw [executeIntegerProducerLineAtPECore.eq_1] at executed
  rw [filterStage] at executed
  rw [parsedIntegerMatrixReadLineFourCycleStep_noforward (expressions := expressions)
    (all := all)] at executed
  dsimp only at executed
  rw [executeParsedFloatMAUsAtPE_noforward (floatEmpty := filterFloat)] at executed
  dsimp only at executed
  simp only [anyALU, anyMatrixRead] at executed
  split at executed
  · cases executed
  · cases executed
  · rename_i forwarding heq
    have hEq := updateSupportedPELineForwarding_noforward_any
      (stateForwardingSlots state pe)
      (fun unit cycle =>
        if (decide (unit = Forwarding.Unit.mau) && false) = true then
          Forwarding.Value.known (⟨0, 0⟩ : IntegerALU.Bus)
        else stateForwardingSlots state pe unit cycle)
      expressions anyNoforward
    have hforward : forwarding = stateForwardingSlots state pe := by
      have h := hEq.symm.trans heq
      cases h
      rfl
    simp only [StepResult.ok.injEq] at executed
    subst executed
    constructor
    · simp [hforward]
    · intro other h
      simp [h]


theorem executeIntegerProducerLineAtPECore_forwarding_noforward_valid
    (expressions : List ParsedExpr) (state next : State) (pe : PEId)
    (all : ∀ expression ∈ expressions, expression.op = .noforward)
    (anyNoforward : (expressions.any fun expression =>
      match expression.op with | .noforward => true | _ => false) = true)
    (valid : ∀ unit cycle, state.forwardingValid pe unit cycle = true)
    (executed : executeIntegerProducerLineAtPECore expressions state pe = .ok next) :
    next.forwarding = state.forwarding := by
  have frame := executeIntegerProducerLineAtPECore_forwarding_noforward
    expressions state next pe all anyNoforward executed
  funext other
  by_cases h : other = pe
  · subst other
    rw [frame.1]
    funext unit cycle
    simp [stateForwardingSlots, valid unit cycle]
  · exact frame.2 other h

theorem parsedExprFootprint_plainIntegerALU_omits_l1bmTurnaround
    (expression : ParsedExpr)
    (plain : parsedExprIsPlainIntegerALU expression = true) :
    UnitResource.l1bmTurnaround ∉ (parsedExprFootprint expression).unitWrites := by
  obtain ⟨hint, hunsup, hmsl, hrelu, hblock, hsupported, hwait, hmau, hwrite,
    hl1tope, hl2bm, hnoforward, hturnaround⟩ :=
    parsedExprIsPlainIntegerALU_facts expression plain
  cases expression with
  | mk op sources destinations flush text =>
      cases op <;>
        simp_all [parsedExprIsPlainIntegerALU, parsedExprIsIntegerProducer,
          parsedExprFootprint, parsedOpUnitWrites, parsedOpMayWriteL1BMTurnaround]

theorem foldl_footprint_plainIntegerALU_omits_l1bmTurnaround
    (normalizedExpressions : List NormalizedExpr)
    (plain : (normalizedExpressions.map NormalizedExpr.toParsed).all
      parsedExprIsPlainIntegerALU = true)
    (initial : Footprint)
    (initialOk : UnitResource.l1bmTurnaround ∉ initial.unitWrites) :
    UnitResource.l1bmTurnaround ∉
      (normalizedExpressions.foldl (fun result expression =>
        Footprint.combine result (parsedExprFootprint expression.toParsed))
        initial).unitWrites := by
  induction normalizedExpressions generalizing initial with
  | nil => simpa using initialOk
  | cons expression rest ih =>
      simp only [List.map_cons, List.all_cons, Bool.and_eq_true] at plain
      obtain ⟨hhead, htail⟩ := plain
      rw [List.foldl_cons]
      rw [show Footprint.combine initial (parsedExprFootprint expression.toParsed) =
        { operandReads := initial.operandReads ++ (parsedExprFootprint expression.toParsed).operandReads,
          operandWrites := initial.operandWrites ++ (parsedExprFootprint expression.toParsed).operandWrites,
          unitReads := initial.unitReads ++ (parsedExprFootprint expression.toParsed).unitReads,
          unitWrites := initial.unitWrites ++ (parsedExprFootprint expression.toParsed).unitWrites }
        from rfl]
      apply ih htail
      simp only [List.mem_append, not_or]
      exact ⟨initialOk,
        parsedExprFootprint_plainIntegerALU_omits_l1bmTurnaround expression.toParsed hhead⟩

/-- Reconciled footprint: a plain integer-ALU `pe` line names the L1BM
turnaround latch. An earlier version of this theorem recorded the opposite
(`normalizedLineFootprint` omitted `.l1bmTurnaround`); `Footprint.lean` now
seeds every `pe` line without a `noforward` expression with the latch, matching
`executeIntegerProducerInstructionLine`, which assigns
`l1bmTurnaroundValid := false` for such a line. -/
theorem normalizedLineFootprint_pe_plainIntegerALU_names_l1bmTurnaround
    (normalizedExpressions : List NormalizedExpr)
    (plain : (normalizedExpressions.map NormalizedExpr.toParsed).all
      parsedExprIsPlainIntegerALU = true) :
    UnitResource.l1bmTurnaround ∈
      (normalizedLineFootprint (.pe normalizedExpressions)).unitWrites := by
  have predicate : ∀ expression : ParsedExpr,
      parsedExprIsNoforward expression = parsedExprIsNoForwardProducer expression := by
    intro expression
    cases expression with
    | mk op sources destinations flush text => cases op <;> rfl
  obtain ⟨_, _, _, _, _, _, _, _, _, _, noForwardAbsent, _⟩ :=
    plainIntegerALU_list_facts (normalizedExpressions.map NormalizedExpr.toParsed)
      rustSimulatorInitialState plain
  have noNoforward : (normalizedExpressions.map NormalizedExpr.toParsed).any
      parsedExprIsNoforward = false := by
    simpa [predicate] using noForwardAbsent
  simpa [normalizedLineFootprint] using
    peLineFootprint_l1bmTurnaround_in_writes normalizedExpressions noNoforward

/-- Reconciled footprint: a `noforward` expression's own footprint names the
forwarding payload it rewrites. An earlier version of this theorem recorded
that `.forwarding` was omitted; `parsedOpUnitWrites .noforward` now includes it,
matching `executeIntegerProducerLineAtPECore`, which assigns
`forwarding pe := stateForwardingSlots state pe`. -/
theorem parsedExprFootprint_noforward_names_forwarding (expression : ParsedExpr)
    (h : expression.op = .noforward) :
    UnitResource.forwarding ∈ (parsedExprFootprint expression).unitWrites := by
  cases expression with
  | mk op sources destinations flush text =>
      rw [show op = .noforward from h]
      simp [parsedExprFootprint, parsedOpUnitWrites]

/-- Reconciled footprint: folding a `noforward` expression into a line names
`.forwarding`. The earlier omission version of this lemma is no longer true
now that `parsedOpUnitWrites .noforward` includes `.forwarding`; the positive
form takes the expression as a member of the line instead of a universal
`all` hypothesis, because an empty fold cannot contain it. -/
theorem foldl_footprint_noforward_names_forwarding
    (normalizedExpressions : List NormalizedExpr)
    (expression : NormalizedExpr) (member : expression ∈ normalizedExpressions)
    (noforward : expression.toParsed.op = .noforward)
    (initial : Footprint) :
    UnitResource.forwarding ∈
      (normalizedExpressions.foldl (fun result current =>
        Footprint.combine result (parsedExprFootprint current.toParsed))
        initial).unitWrites := by
  exact Footprint.foldl_unitWrites_contains_effect normalizedExpressions
    (fun current => parsedExprFootprint current.toParsed) initial expression member
    UnitResource.forwarding
    (parsedExprFootprint_noforward_names_forwarding expression.toParsed noforward)

/-- Reconciled footprint: every `pe` line names `.forwarding` at the line
level. An earlier version of this theorem recorded an omission for
`noforward` lines; the seed now names forwarding for empty and wait-only lines
as well, because every successful `pe` line runs the forwarding update at every
PE. The `all` hypothesis is kept for continuity with the omission statement. -/
theorem normalizedLineFootprint_pe_noforward_names_forwarding
    (normalizedExpressions : List NormalizedExpr)
    (all : ∀ expression ∈ normalizedExpressions.map NormalizedExpr.toParsed,
      expression.op = .noforward) :
    UnitResource.forwarding ∈
      (normalizedLineFootprint (.pe normalizedExpressions)).unitWrites := by
  simpa [normalizedLineFootprint] using
    peLineFootprint_forwarding_in_writes normalizedExpressions

end ProofsLean.MNCore
