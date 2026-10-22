import ProofsLean.CendCycleClose

/-! # `12.convert-endian`: the non-plain families, one closed class at a time

`ProofsLean/CendCycleClose.lean` refutes the whole plain family and reduces
`LowerBound cendSealedMachine cendSpec 2` to the non-plain residual
`CendPENonClosedRefuted` (every `.pe` line outside `CendClosedLines`: the
all-`.matrixRead` lines and the all-PE-inert lines).

This module extends the closed side by the two families whose rows never write a
PE register file at all:

* a `.matrixWrite` row is executed by `executeParsedMatrixWritesAtMABs` inside
  the matrix-MAU/write stage, which only rewrites the matrix store
  (`executeParsedMatrixMAUAndWrites_peRegisters_frame_of_noMatrixMAU`);
* a `.l2bm` row is executed by `executeParsedSharedBlockProducers`, which only
  rewrites the L1BM/L2BM/DAR state
  (`executeParsedSharedBlockProducers_peRegisters`).

Both are already excluded from the integer stage
(`parsedExprIsIntegerMatrixReadStageInput` tests `!parsedExprIsMatrixWriteProducer`
and `!parsedExprIsL2BMProducer`) and from every other PE-register-writing stage,
so a line whose rows are all in the extended class keeps every PE register file.
At the witness `cendWitness` its observed LM1 bank therefore stays at the initial
`0`, while the target pair `byteSwap64 cendWitness = 0x0807060504030201` is
non-zero: `cend_not_correct_of_lm1_zero` refutes it.

## Results

**§1–§4 — the extended-inert class (`.matrixWrite`, `.l2bm`).**

* `cendPEInertProducerExt` — the six inert row shapes plus `.matrixWrite` and
  `.l2bm`, with its per-row facts (`cendPEInertProducerExt_facts`,
  `..._stageInput_noforward`) and list form (`cendPEInertProducerExt_list_facts`).
* `executeIntegerProducerInstructionLine_pe_peRegisters_of_extInert` — a
  successful `.pe` line whose rows are all extended-inert leaves `peRegisters`
  unchanged.
* `cendPE_extInertLines_not_correct` — every such line is incorrect.

**§5–§6 — the L1BM broadcast class.**

* `cendInitialState_l1ToPEBusAt_zero` — at the `cendInitialState` the L1BM bank
  and its turnaround words are zero, so every broadcast bus is `⟨0, 0⟩`.
* `writeParsedL1ToPEDestination?_lm1_zero`,
  `executeParsedL1ToPE_writeDestinations_lm1_zero`,
  `executeParsedL1ToPE_writeCycles_lm1_zero`,
  `executeParsedL1ToPEAtPEs_lm1_zero`,
  `executeParsedL1ToPEProducer_lm1_zero`,
  `executeParsedL1ToPEProducers_lm1_zero` — a zero-bus broadcast preserves the
  all-zero `.lm1` bank through the destination fold, the four-cycle fold, the
  4096-PE walk and the family filter.
* `cendL1ToPEOrExtInert` (`= cendPEInertProducerExt || parsedExprIsL1ToPEProducer`)
  and `executeIntegerProducerInstructionLine_pe_lm1_zero_of_l1ToPE` — a
  successful line whose rows are all in that class keeps the observed LM1 bank
  at zero.
* `cendPE_l1ToPEOrExtInertLines_not_correct` — every such line is incorrect.

**§7–§8 — the enlarged closed class and the exact residual.**

* `CendClosedLinesExt` / `cendPE_closedLinesExt_not_correct` — the closed class
  of `CendUnconditional` enlarged by both families.
* `CendNonPlainResidual` — the exact remaining statement: every line that is
  neither closed (`CendClosedLines`), nor in `cendL1ToPEOrExtInert`, nor
  all-plain is incorrect.  `cendPENonClosedRefuted_of_nonPlainResidual` derives
  `CendPENonClosedRefuted` from it and
  `cendLowerBound_two_of_nonPlainResidual` derives
  `LowerBound cendSealedMachine cendSpec 2`.

## What is still open

`CendNonPlainResidual` is not discharged.  Its lines have at least one row
outside `cendL1ToPEOrExtInert`, i.e. a PE-register-writing row from one of the
six value families the task lists: plain ALU (`.alu`/`.zero`/`.immediate`),
`.matrixRead`, float MAU, float relu, `msl`/`msr`, matrix MAU / block float.
Their writes do reach LM1 with input-dependent data, so a value argument per
family (and a mixed-line separation on the unique LM1 writer) is still needed.
This module does not assume or restate those obligations as axioms; it only
reduces the residual.

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

/-! ## 1. The extended inert class -/

/-- The rows that no PE-register-writing executor stage selects: the six
PE-inert shapes of `WelcomeGapShape.parsedExprIsPEInertProducer` (`.noforward`,
a non-pending `.wait` and the five shared-block `.l1bm` operations) plus the two
block/matrix-store writers `.matrixWrite` and `.l2bm`.

A `.matrixWrite` row is executed by the matrix-write stage inside
`executeParsedMatrixMAUAndWrites` (matrix store only), and a `.l2bm` row by
`executeParsedSharedBlockProducers` (L1BM/L2BM/DAR state only). -/
def cendPEInertProducerExt (expression : ParsedExpr) : Bool :=
  parsedExprIsPEInertProducer expression || parsedExprIsMatrixWriteProducer expression ||
    parsedExprIsL2BMProducer expression

theorem cendPEInertProducerExt_of_inert (expression : ParsedExpr)
    (inert : parsedExprIsPEInertProducer expression = true) :
    cendPEInertProducerExt expression = true := by
  simp [cendPEInertProducerExt, inert]

theorem cendPEInertProducerExt_of_matrixWrite (expression : ParsedExpr)
    (write : parsedExprIsMatrixWriteProducer expression = true) :
    cendPEInertProducerExt expression = true := by
  simp [cendPEInertProducerExt, write]

theorem cendPEInertProducerExt_of_l2bm (expression : ParsedExpr)
    (read : parsedExprIsL2BMProducer expression = true) :
    cendPEInertProducerExt expression = true := by
  simp [cendPEInertProducerExt, read]

/-- The three cases of the extended inert class. -/
theorem cendPEInertProducerExt_cases (expression : ParsedExpr)
    (ext : cendPEInertProducerExt expression = true) :
    parsedExprIsPEInertProducer expression = true ∨
      parsedExprIsMatrixWriteProducer expression = true ∨
      parsedExprIsL2BMProducer expression = true := by
  have h := ext
  simp only [cendPEInertProducerExt, Bool.or_eq_true] at h
  tauto

/-- **Every PE-register-writing predicate is false on an extended-inert row.** -/
theorem cendPEInertProducerExt_facts (expression : ParsedExpr)
    (ext : cendPEInertProducerExt expression = true) :
    parsedExprIsMslMsrProducer expression = false ∧
      parsedExprIsFloatReluProducer expression = false ∧
      parsedExprIsBlockFloatProducer expression = false ∧
      parsedExprIsMatrixMAUProducer expression = false ∧
      parsedExprIsSupportedFloatMAUProducer expression = false ∧
      parsedExprIsL1ToPEProducer expression = false ∧
      parsedExprIsIntegerBARWriter expression = false := by
  rcases cendPEInertProducerExt_cases expression ext with inert | write | read
  · obtain ⟨msl, relu, block, mau, _, float, l1, _, bar⟩ :=
      parsedExprIsPEInertProducer_facts expression inert
    exact ⟨msl, relu, block, mau, float, l1, bar⟩
  · cases expression with
    | mk op sources destinations flush text =>
      cases op <;>
        simp_all [parsedExprIsMatrixWriteProducer, parsedExprIsMslMsrProducer,
          parsedExprIsFloatReluProducer, parsedExprIsBlockFloatProducer,
          parsedExprIsMatrixMAUProducer, parsedExprIsSupportedFloatMAUProducer,
          parsedExprIsL1ToPEProducer, parsedExprIsIntegerBARWriter]
  · cases expression with
    | mk op sources destinations flush text =>
      cases op <;>
        simp_all [parsedExprIsL2BMProducer, parsedExprIsMslMsrProducer,
          parsedExprIsFloatReluProducer, parsedExprIsBlockFloatProducer,
          parsedExprIsMatrixMAUProducer, parsedExprIsSupportedFloatMAUProducer,
          parsedExprIsL1ToPEProducer, parsedExprIsIntegerBARWriter]

/-- **An extended-inert row is never a PE-stage input**, except for the
`.noforward` shape that the integer stage prepares as an empty write list. -/
theorem cendPEInertProducerExt_stageInput_noforward (expression : ParsedExpr)
    (ext : cendPEInertProducerExt expression = true)
    (stage : parsedExprIsIntegerMatrixReadStageInput expression = true) :
    expression.op = .noforward := by
  rcases cendPEInertProducerExt_cases expression ext with inert | write | read
  · exact parsedExprIsPEInertProducer_stageInput_noforward expression inert stage
  · have isWrite : parsedExprIsMatrixWriteProducer expression = true := write
    simp [parsedExprIsIntegerMatrixReadStageInput, isWrite] at stage
  · have isL2 : parsedExprIsL2BMProducer expression = true := read
    simp [parsedExprIsIntegerMatrixReadStageInput, isL2] at stage

/-! ## 2. The list facts used by the line-level proof -/

theorem cendPEInertProducerExt_list_facts (expressions : List ParsedExpr)
    (all : ∀ expression ∈ expressions, cendPEInertProducerExt expression = true) :
    expressions.filter parsedExprIsMslMsrProducer = [] ∧
      expressions.filter parsedExprIsFloatReluProducer = [] ∧
      expressions.filter parsedExprIsBlockFloatProducer = [] ∧
      expressions.filter parsedExprIsMatrixMAUProducer = [] ∧
      expressions.filter parsedExprIsSupportedFloatMAUProducer = [] ∧
      expressions.filter parsedExprIsL1ToPEProducer = [] ∧
      expressions.any parsedExprIsIntegerBARWriter = false ∧
      (∀ expression ∈ expressions.filter parsedExprIsIntegerMatrixReadStageInput,
        expression.op = .noforward) := by
  have facts := fun expression member =>
    cendPEInertProducerExt_facts expression (all expression member)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact List.filter_eq_nil_iff.mpr fun expression member => by
      rw [(facts expression member).1]; simp
  · exact List.filter_eq_nil_iff.mpr fun expression member => by
      rw [(facts expression member).2.1]; simp
  · exact List.filter_eq_nil_iff.mpr fun expression member => by
      rw [(facts expression member).2.2.1]; simp
  · exact List.filter_eq_nil_iff.mpr fun expression member => by
      rw [(facts expression member).2.2.2.1]; simp
  · exact List.filter_eq_nil_iff.mpr fun expression member => by
      rw [(facts expression member).2.2.2.2.1]; simp
  · exact List.filter_eq_nil_iff.mpr fun expression member => by
      rw [(facts expression member).2.2.2.2.2.1]; simp
  · exact List.any_eq_false.mpr fun expression member => by
      rw [(facts expression member).2.2.2.2.2.2]; simp
  · intro expression member
    exact cendPEInertProducerExt_stageInput_noforward expression
      (all expression (List.mem_filter.mp member).1) (List.mem_filter.mp member).2

/-! ## 3. The line-level frame

The proof follows `WelcomeGapShape.executeIntegerProducerInstructionLine_pe_peRegisters_of_inert`
stage by stage.  The only difference is the matrix-MAU/write stage: it may now
contain `.matrixWrite` rows, so it is not the identity, but it still preserves
every PE register file
(`executeParsedMatrixMAUAndWrites_peRegisters_frame_of_noMatrixMAU`). -/

theorem executeIntegerProducerInstructionLine_pe_peRegisters_of_extInert
    (normalizedExpressions : List NormalizedExpr) (state next : State)
    (all : ∀ expression ∈ normalizedExpressions.map NormalizedExpr.toParsed,
      cendPEInertProducerExt expression = true)
    (success : executeIntegerProducerInstructionLine (.pe normalizedExpressions) state
      = .ok next) :
    next.peRegisters = state.peRegisters := by
  have accepted := executeIntegerProducerInstructionLine_accepted_of_ok
    (.pe normalizedExpressions) state next success
  obtain ⟨mslEmpty, reluEmpty, blockEmpty, mauEmpty, floatEmpty,
    l1ToPEEmpty, noBAR, stageAll⟩ :=
    cendPEInertProducerExt_list_facts (normalizedExpressions.map NormalizedExpr.toParsed) all
  have supportedAny : normalizedExpressions.all
      (parsedExprIsSupportedPELineProducer ∘ NormalizedExpr.toParsed) = true := by
    simpa [List.all_map] using
      executeIntegerProducerInstructionLine_pe_supported_of_ok normalizedExpressions
        state next success
  have noUnsupportedAny : normalizedExpressions.any
      (parsedExprIsUnsupportedRustAlu ∘ NormalizedExpr.toParsed) = false := by
    simpa [List.any_map] using
      executeIntegerProducerInstructionLine_pe_noUnsupported_of_ok normalizedExpressions
        state next success
  have waitsAny : normalizedExpressions.any
      ((parsedExprWaitPending state) ∘ NormalizedExpr.toParsed) = false := by
    simpa [List.any_map] using
      executeIntegerProducerInstructionLine_pe_waits_complete normalizedExpressions
        state next success
  unfold executeIntegerProducerInstructionLine at success
  simp [accepted, supportedAny, noUnsupportedAny, waitsAny] at success
  split at success
  · cases success
  · cases success
  · rename_i nextPEs executed
    rw [executeParsedMslMsrProducers_nil state nextPEs
      (normalizedExpressions.map NormalizedExpr.toParsed) _ _ mslEmpty] at success
    dsimp only at success
    rw [executeParsedFloatReluProducers_nil state nextPEs
      (normalizedExpressions.map NormalizedExpr.toParsed) _ _ reluEmpty] at success
    dsimp only at success
    rw [executeParsedBlockFloatProducer_nil state nextPEs
      (normalizedExpressions.map NormalizedExpr.toParsed) _ _ blockEmpty] at success
    dsimp only at success
    split at success
    · cases success
    · cases success
    · rename_i afterMatrix matrixExec
      split at success
      · cases success
      · cases success
      · rename_i nextWithBlocks sharedExec
        rw [executeParsedL1ToPEProducers_nil state nextWithBlocks
          (normalizedExpressions.map NormalizedExpr.toParsed) _ _ _ l1ToPEEmpty] at success
        dsimp only at success
        simp only [StepResult.ok.injEq] at success
        rw [← success]
        simp only []
        rw [executeParsedSharedBlockProducers_peRegisters state afterMatrix nextWithBlocks
          (normalizedExpressions.map NormalizedExpr.toParsed) _ sharedExec]
        rw [show afterMatrix.peRegisters = nextPEs.peRegisters from
          funext fun pe =>
            executeParsedMatrixMAUAndWrites_peRegisters_frame_of_noMatrixMAU state nextPEs
              afterMatrix (normalizedExpressions.map NormalizedExpr.toParsed) _ _ mauEmpty
              matrixExec pe]
        exact executeIntegerProducerLineAtPEs_peRegisters_of_inert
          ((normalizedExpressions.map NormalizedExpr.toParsed).filter fun expression =>
            !parsedExprIsL2BMProducer expression && !parsedExprIsMslMsrProducer expression &&
              !parsedExprIsMatrixMAUProducer expression &&
              !parsedExprIsBlockFloatProducer expression &&
              !parsedExprIsFloatReluProducer expression)
          (List.finRange 4096)
          (fun expression member =>
            stageAll expression
              (List.mem_filter.mpr
                ⟨(List.mem_filter.mp (List.mem_filter.mp member).1).1,
                  (List.mem_filter.mp member).2⟩))
          (List.filter_eq_nil_iff.mpr fun expression member => by
            have member' : expression ∈ normalizedExpressions.map NormalizedExpr.toParsed :=
              (List.mem_filter.mp member).1
            have := (List.filter_eq_nil_iff.mp floatEmpty) expression member'
            simpa using this)
          (List.any_eq_false.mpr fun expression member => by
            have member' : expression ∈ normalizedExpressions.map NormalizedExpr.toParsed :=
              (List.mem_filter.mp member).1
            have := (List.any_eq_false.mp noBAR) expression member'
            simpa using this)
          state nextPEs executed

/-! ## 4. Extended-inert lines are incorrect -/

theorem cendPE_extInertLines_not_correct (expressions : List NormalizedExpr)
    (all : ∀ expression ∈ expressions.map NormalizedExpr.toParsed,
      cendPEInertProducerExt expression = true) :
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
      have frame := executeIntegerProducerInstructionLine_pe_peRegisters_of_extInert
        expressions (cendInitialState cendWitness) next all lineExecuted
      refine cend_not_correct_of_lm1_zero expressions next step ?_
      intro address
      rw [frame]
      exact cendInitialPERegisters_lm1 cendWitness address

/-! ## 5. The L1BM broadcast family: zero data at the initial state

At `cendInitialState` the L1BM banks and their turnaround words are zero
(`cendInitialState_l1bm_zero`), so every broadcast bus is the zero bus
(`cendInitialState_l1ToPEBusAt_zero`).  A broadcast writes with
`writeParsedL1ToPEDestination?`, whose only register-writing branch is a masked
store of `unpackALUBus output`; with `output = ⟨0, 0⟩` that store is the zero
bus, and a zero-bus masked store into an all-zero `.lm1` file leaves it zero
(`writeDirectAccessMasked_lm1_zero`).  The destination fold, the cycle fold and
the PE walk then preserve the all-zero `.lm1` bank.

Consequently a line whose rows are all extended-inert or `.l1bm` to-PE
broadcasts leaves the observed LM1 bank at its initial zero and is refuted by
`cend_not_correct_of_lm1_zero`.  A turnaround broadcast at the initial state is
not even executed (`l1bmTurnaroundValid` is `false`), so such a line is stuck;
that case is excluded by the successful-step hypothesis of the line lemma and
the `none` step is handled by `cend_not_correct_of_step_none` in the refutation. -/

/-- **The broadcast bus is zero at the `cendInitialState`.** -/
theorem cendInitialState_l1ToPEBusAt_zero (input : BitVec 64) (expression : ParsedExpr)
    (access : ParsedL1ToPEAccess) (pe : PEId) (cycle : Fin 4) :
    l1ToPEBusAt (cendInitialState input) expression access pe cycle = ⟨0, 0⟩ := by
  cases operation : expression.op with
  | l1bm l1op =>
      cases l1op <;>
        cases source : access.sourceBase <;>
        simp [l1ToPEBusAt, operation, cendInitialState, rustSimulatorInitialState,
          L1Transfer.pbcast, L1Transfer.pbcastTurnaround, L1Transfer.mbcast,
          L1Transfer.m4bcast, L1Transfer.distrib, L1Transfer.readL1Long, source]
  | alu name precision unsigned arg =>
      simp [l1ToPEBusAt, operation, cendInitialState, rustSimulatorInitialState]
  | immediate value unsigned =>
      simp [l1ToPEBusAt, operation, cendInitialState, rustSimulatorInitialState]
  | zero =>
      simp [l1ToPEBusAt, operation, cendInitialState, rustSimulatorInitialState]
  | mau precision matrix kind half round =>
      simp [l1ToPEBusAt, operation, cendInitialState, rustSimulatorInitialState]
  | matrixWrite precision =>
      simp [l1ToPEBusAt, operation, cendInitialState, rustSimulatorInitialState]
  | matrixRead precision =>
      simp [l1ToPEBusAt, operation, cendInitialState, rustSimulatorInitialState]
  | wait tag =>
      simp [l1ToPEBusAt, operation, cendInitialState, rustSimulatorInitialState]
  | noforward =>
      simp [l1ToPEBusAt, operation, cendInitialState, rustSimulatorInitialState]
  | l2bm l2op =>
      simp [l1ToPEBusAt, operation, cendInitialState, rustSimulatorInitialState]

/-- **A zero-bus broadcast write preserves the all-zero `.lm1` file.** -/
theorem writeParsedL1ToPEDestination?_lm1_zero
    (files : IntegerRegisterFiles) (maskRegisters : Masks.RegisterFile)
    (destination : ParsedOperand) (context : ParsedIntegerContext)
    (output : IntegerALU.Bus) (cycle : Fin 4) (directive : ParsedMaskDirective)
    (hasSingleLineMask : Bool)
    (zero : files.lm1 = fun _ => 0) (outputZero : output = ⟨0, 0⟩)
    (nextFiles : IntegerRegisterFiles) (barUpdate : Option (Bool × BitVec 12))
    (lowered : writeParsedL1ToPEDestination? files maskRegisters destination context output
      cycle directive hasSingleLineMask = some (nextFiles, barUpdate)) :
    nextFiles.lm1 = fun _ => 0 := by
  cases destination with
  | mem access negated extended rounded mask =>
      simp only [writeParsedL1ToPEDestination?] at lowered
      cases h : ParsedOperand.toDirectMemoryDestination?
          (ParsedOperand.mem access negated extended rounded mask) context.pe cycle
          context.bar0 context.bar1 context.tWord with
      | none => simp [h] at lowered
      | some found =>
          cases h2 : ParsedOperand.resolveMemoryWriteSelection?
              (ParsedOperand.mem access negated extended rounded mask) found.bank
              maskRegisters cycle directive hasSingleLineMask with
          | none => simp [h, h2] at lowered
          | some selection =>
              simp [h, h2] at lowered
              obtain ⟨rfl, rfl⟩ := lowered
              rw [outputZero, unpackALUBus_zero]
              cases found with
              | mk bank width address =>
                  cases bank with
                  | lm1 => exact writeDirectAccessMasked_lm1_zero files width address selection zero
                  | lm0 =>
                      rw [writeDirectAccessMasked_lm1_of_ne files _ _ selection (by simp)]
                      exact zero
                  | grf0 =>
                      rw [writeDirectAccessMasked_lm1_of_ne files _ _ selection (by simp)]
                      exact zero
                  | grf1 =>
                      rw [writeDirectAccessMasked_lm1_of_ne files _ _ selection (by simp)]
                      exact zero
                  | t =>
                      rw [writeDirectAccessMasked_lm1_of_ne files _ _ selection (by simp)]
                      exact zero
  | bar lm1 width mask =>
      simp only [writeParsedL1ToPEDestination?] at lowered
      cases h : ParsedOperand.resolveMemoryWriteSelection? (ParsedOperand.bar lm1 width mask)
        (if lm1 = true then PEMemory.Bank.lm1 else PEMemory.Bank.lm0) maskRegisters
        cycle directive hasSingleLineMask with
      | none => simp [h] at lowered
      | some selection =>
          simp [h] at lowered
          obtain ⟨rfl, rfl⟩ := lowered
          exact zero
  | nowrite =>
      simp only [writeParsedL1ToPEDestination?] at lowered
      obtain ⟨rfl, rfl⟩ := Option.some.inj lowered
      exact zero
  | omr entry mask => simp [writeParsedL1ToPEDestination?] at lowered
  | forward kind neg ext rnd => simp [writeParsedL1ToPEDestination?] at lowered
  | fixed value => simp [writeParsedL1ToPEDestination?] at lowered
  | matrix side width row => simp [writeParsedL1ToPEDestination?] at lowered
  | l1bm width address => simp [writeParsedL1ToPEDestination?] at lowered
  | l2bm address l2b => simp [writeParsedL1ToPEDestination?] at lowered
  | dar value => simp [writeParsedL1ToPEDestination?] at lowered

/-- **The L1BM-to-PE destination loop preserves the all-zero `.lm1` file.** -/
theorem executeParsedL1ToPE_writeDestinations_lm1_zero
    (currentState : State) (hasSingleLineMask : Bool) (maskRegisters : Masks.RegisterFile)
    (cycle : Fin 4) (context : ParsedIntegerContext) (output : IntegerALU.Bus)
    (outputZero : output = ⟨0, 0⟩) :
    ∀ (destinations : List ParsedOperand) (files : IntegerRegisterFiles) (bar0 bar1 : BitVec 12)
      (nextFiles : IntegerRegisterFiles) (nextBar0 nextBar1 : BitVec 12),
      files.lm1 = (fun _ => 0) →
      executeParsedL1ToPEAtPEs.writeCycles.writeDestinations currentState hasSingleLineMask
        maskRegisters cycle context output destinations files bar0 bar1 =
        some (nextFiles, nextBar0, nextBar1) →
      nextFiles.lm1 = fun _ => 0 := by
  intro destinations
  induction destinations with
  | nil =>
      intro files bar0 bar1 nextFiles nextBar0 nextBar1 zero executed
      rw [executeParsedL1ToPEAtPEs.writeCycles.writeDestinations] at executed
      obtain ⟨rfl, rfl, rfl⟩ := Option.some.inj executed
      exact zero
  | cons destination rest ih =>
      intro files bar0 bar1 nextFiles nextBar0 nextBar1 zero executed
      cases lowered : writeParsedL1ToPEDestination? files maskRegisters destination
          { context with bar0 := bar0, bar1 := bar1 } output cycle currentState.maskDirective
          hasSingleLineMask with
      | none =>
          rw [executeParsedL1ToPE_writeDestinations_cons_none currentState hasSingleLineMask
            maskRegisters cycle context output destination rest files bar0 bar1 lowered] at executed
          simp at executed
      | some pair =>
          obtain ⟨writeFiles, barUpdate⟩ := pair
          cases barUpdate with
          | none =>
              rw [executeParsedL1ToPE_writeDestinations_cons_some_none currentState
                hasSingleLineMask maskRegisters cycle context output destination rest files bar0
                bar1 writeFiles lowered] at executed
              exact ih writeFiles bar0 bar1 nextFiles nextBar0 nextBar1
                (writeParsedL1ToPEDestination?_lm1_zero files maskRegisters destination
                  { context with bar0 := bar0, bar1 := bar1 } output cycle
                  currentState.maskDirective hasSingleLineMask zero outputZero writeFiles none
                  lowered) executed
          | some update =>
              obtain ⟨lm1, value⟩ := update
              cases lm1 with
              | false =>
                  rw [executeParsedL1ToPE_writeDestinations_cons_some_false currentState
                    hasSingleLineMask maskRegisters cycle context output destination rest files
                    bar0 bar1 writeFiles value lowered] at executed
                  exact ih writeFiles value bar1 nextFiles nextBar0 nextBar1
                    (writeParsedL1ToPEDestination?_lm1_zero files maskRegisters destination
                      { context with bar0 := bar0, bar1 := bar1 } output cycle
                      currentState.maskDirective hasSingleLineMask zero outputZero writeFiles
                      (some (false, value)) lowered) executed
              | true =>
                  rw [executeParsedL1ToPE_writeDestinations_cons_some_true currentState
                    hasSingleLineMask maskRegisters cycle context output destination rest files
                    bar0 bar1 writeFiles value lowered] at executed
                  exact ih writeFiles bar0 value nextFiles nextBar0 nextBar1
                    (writeParsedL1ToPEDestination?_lm1_zero files maskRegisters destination
                      { context with bar0 := bar0, bar1 := bar1 } output cycle
                      currentState.maskDirective hasSingleLineMask zero outputZero writeFiles
                      (some (true, value)) lowered) executed

/-- **The L1BM-to-PE cycle loop preserves the all-zero `.lm1` file.** -/
theorem executeParsedL1ToPE_writeCycles_lm1_zero
    (readState currentState : State) (expression : ParsedExpr) (access : ParsedL1ToPEAccess)
    (hasSingleLineMask : Bool) (pe : PEId) (coordinates readContext : ParsedIntegerContext)
    (maskRegisters : Masks.RegisterFile)
    (busZero : ∀ cycle, l1ToPEBusAt readState expression access pe cycle = ⟨0, 0⟩) :
    ∀ (cycles : List (Fin 4)) (files : IntegerRegisterFiles) (bar0 bar1 : BitVec 12)
      (nextFiles : IntegerRegisterFiles) (nextBar0 nextBar1 : BitVec 12),
      files.lm1 = (fun _ => 0) →
      executeParsedL1ToPEAtPEs.writeCycles readState currentState expression access
        hasSingleLineMask pe coordinates readContext maskRegisters cycles files bar0 bar1 =
        .ok (nextFiles, nextBar0, nextBar1) →
      nextFiles.lm1 = fun _ => 0 := by
  intro cycles
  induction cycles with
  | nil =>
      intro files bar0 bar1 nextFiles nextBar0 nextBar1 zero executed
      rw [executeParsedL1ToPEAtPEs.writeCycles] at executed
      obtain ⟨rfl, rfl, rfl⟩ := StepResult.ok.inj executed
      exact zero
  | cons cycle rest ih =>
      intro files bar0 bar1 nextFiles nextBar0 nextBar1 zero executed
      rw [executeParsedL1ToPEAtPEs.writeCycles] at executed
      dsimp only at executed
      cases flush : resolveFlushSelection? expression.flush maskRegisters cycle with
      | none =>
          rw [flush] at executed
          dsimp only at executed
          simp at executed
      | some flushSelection =>
          rw [flush] at executed
          dsimp only at executed
          split at executed
          · simp at executed
          · rename_i middleFiles middleBar0 middleBar1 wrote
            exact ih middleFiles middleBar0 middleBar1 nextFiles nextBar0 nextBar1
              (executeParsedL1ToPE_writeDestinations_lm1_zero currentState hasSingleLineMask
                maskRegisters cycle _ _ (by
                  rw [busZero cycle]
                  exact parsedOutputAfterFlush_zero flushSelection)
                access.destinations files bar0 bar1 middleFiles middleBar0 middleBar1 zero
                wrote) executed

/-- **The L1BM-to-PE walk preserves the all-zero `.lm1` file at every PE.** -/
theorem executeParsedL1ToPEAtPEs_lm1_zero (readState : State)
    (expression : ParsedExpr) (access : ParsedL1ToPEAccess)
    (noForward hasSingleLineMask usePreIssueMask : Bool)
    (busZero : ∀ (pe : PEId) (cycle : Fin 4),
      l1ToPEBusAt readState expression access pe cycle = ⟨0, 0⟩) :
    ∀ (pes : List PEId) (state : State) (p : PEId) (next : State),
      (state.peRegisters p).lm1 = (fun _ => 0) →
      executeParsedL1ToPEAtPEs readState state expression access pes noForward
        hasSingleLineMask usePreIssueMask = .ok next →
      (next.peRegisters p).lm1 = fun _ => 0 := by
  intro pes
  induction pes with
  | nil =>
      intro state p next zero executed
      simp only [executeParsedL1ToPEAtPEs.eq_1, StepResult.ok.injEq] at executed
      subst executed
      exact zero
  | cons pe rest ih =>
      intro state p next zero executed
      rw [executeParsedL1ToPEAtPEs.eq_2] at executed
      split at executed
      · simp at executed
      · simp only [] at executed
        split at executed
        · simp at executed
        · simp at executed
        · rename_i files bar0 bar1 ran
          by_cases same : p = pe
          · subst same
            refine ih _ p next ?_ executed
            simpa using (executeParsedL1ToPE_writeCycles_lm1_zero readState state expression access
              hasSingleLineMask p _ _ _ (fun cycle => busZero p cycle) [0, 1, 2, 3]
              (state.peRegisters p) _ _ files bar0 bar1 zero ran)
          · refine ih _ p next ?_ executed
            simpa [same] using zero

/-- **The L1BM-to-PE producer preserves the all-zero `.lm1` file.** -/
theorem executeParsedL1ToPEProducer_lm1_zero
    (readState currentState next : State) (expression : ParsedExpr)
    (noForward hasSingleLineMask usePreIssueMask : Bool)
    (busZero : ∀ (access : ParsedL1ToPEAccess), lowerParsedL1ToPE? expression = some access →
      ∀ (pe : PEId) (cycle : Fin 4),
        l1ToPEBusAt readState expression access pe cycle = ⟨0, 0⟩)
    (zero : ∀ p, (currentState.peRegisters p).lm1 = fun _ => 0)
    (executed : executeParsedL1ToPEProducer readState currentState expression noForward
      hasSingleLineMask usePreIssueMask = .ok next) :
    ∀ p, (next.peRegisters p).lm1 = fun _ => 0 := by
  cases lowered : lowerParsedL1ToPE? expression with
  | none =>
      rw [executeParsedL1ToPEProducer, lowered] at executed
      simp at executed
  | some access =>
      rw [executeParsedL1ToPEProducer, lowered] at executed
      intro p
      exact executeParsedL1ToPEAtPEs_lm1_zero readState expression access noForward
        hasSingleLineMask usePreIssueMask (busZero access lowered) (List.finRange 4096)
        currentState p next (zero p) executed

/-- **The L1BM-to-PE family filter preserves the all-zero `.lm1` file.** -/
theorem executeParsedL1ToPEProducers_lm1_zero
    (readState currentState next : State) (expressions : List ParsedExpr)
    (noForward hasSingleLineMask usePreIssueMask : Bool)
    (busZero : ∀ expression ∈ expressions.filter parsedExprIsL1ToPEProducer,
      ∀ (access : ParsedL1ToPEAccess), lowerParsedL1ToPE? expression = some access →
      ∀ (pe : PEId) (cycle : Fin 4),
        l1ToPEBusAt readState expression access pe cycle = ⟨0, 0⟩)
    (zero : ∀ p, (currentState.peRegisters p).lm1 = fun _ => 0)
    (executed : executeParsedL1ToPEProducers readState currentState expressions noForward
      hasSingleLineMask usePreIssueMask = .ok next) :
    ∀ p, (next.peRegisters p).lm1 = fun _ => 0 := by
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
          exact executeParsedL1ToPEProducer_lm1_zero readState currentState next expression
            noForward hasSingleLineMask usePreIssueMask
            (fun access lowered => busZero expression (by simp [filtered]) access lowered) zero
            executed
      | cons second remaining =>
          rw [executeParsedL1ToPEProducers, filtered] at executed
          simp at executed

/-! ## 6. Whole lines whose PE writers are broadcasts or extended-inert rows -/

/-- **The row class of §6**: an extended-inert row, or an `.l1bm` to-PE
broadcast. -/
def cendL1ToPEOrExtInert (expression : ParsedExpr) : Bool :=
  cendPEInertProducerExt expression || parsedExprIsL1ToPEProducer expression

theorem cendL1ToPEOrExtInert_cases (expression : ParsedExpr)
    (row : cendL1ToPEOrExtInert expression = true) :
    cendPEInertProducerExt expression = true ∨
      parsedExprIsL1ToPEProducer expression = true := by
  have h := row
  simp only [cendL1ToPEOrExtInert, Bool.or_eq_true] at h
  exact h

/-- **A broadcast row writes no special-ALU, matrix-MAU or BAR state, and is not
an integer-stage input.** -/
theorem parsedExprIsL1ToPEProducer_facts (expression : ParsedExpr)
    (broadcast : parsedExprIsL1ToPEProducer expression = true) :
    parsedExprIsMslMsrProducer expression = false ∧
      parsedExprIsFloatReluProducer expression = false ∧
      parsedExprIsBlockFloatProducer expression = false ∧
      parsedExprIsMatrixMAUProducer expression = false ∧
      parsedExprIsSupportedFloatMAUProducer expression = false ∧
      parsedExprIsIntegerBARWriter expression = false ∧
      parsedExprIsIntegerMatrixReadStageInput expression = false := by
  cases expression with
  | mk op sources destinations flush text =>
    cases op with
    | l1bm l1op =>
        cases l1op <;>
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
            simp [parsedExprIsL1ToPEProducer, parsedExprIsMslMsrProducer,
              parsedExprIsFloatReluProducer, parsedExprIsBlockFloatProducer,
              parsedExprIsMatrixMAUProducer, parsedExprIsSupportedFloatMAUProducer,
              parsedExprIsIntegerBARWriter,
              parsedExprIsIntegerMatrixReadStageInput] at broadcast ⊢
    | alu name precision unsigned arg => simp [parsedExprIsL1ToPEProducer] at broadcast
    | immediate value unsigned => simp [parsedExprIsL1ToPEProducer] at broadcast
    | zero => simp [parsedExprIsL1ToPEProducer] at broadcast
    | mau precision matrix kind half round => simp [parsedExprIsL1ToPEProducer] at broadcast
    | matrixWrite precision => simp [parsedExprIsL1ToPEProducer] at broadcast
    | matrixRead precision => simp [parsedExprIsL1ToPEProducer] at broadcast
    | wait tag => simp [parsedExprIsL1ToPEProducer] at broadcast
    | noforward => simp [parsedExprIsL1ToPEProducer] at broadcast
    | l2bm l2op => simp [parsedExprIsL1ToPEProducer] at broadcast

theorem cendL1ToPE_list_facts (expressions : List ParsedExpr)
    (all : ∀ expression ∈ expressions, cendL1ToPEOrExtInert expression = true) :
    expressions.filter parsedExprIsMslMsrProducer = [] ∧
      expressions.filter parsedExprIsFloatReluProducer = [] ∧
      expressions.filter parsedExprIsBlockFloatProducer = [] ∧
      expressions.filter parsedExprIsMatrixMAUProducer = [] ∧
      expressions.filter parsedExprIsSupportedFloatMAUProducer = [] ∧
      expressions.any parsedExprIsIntegerBARWriter = false ∧
      (∀ expression ∈ expressions.filter parsedExprIsIntegerMatrixReadStageInput,
        expression.op = .noforward) := by
  have rowFacts := fun expression member =>
    cendL1ToPEOrExtInert_cases expression (all expression member)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact List.filter_eq_nil_iff.mpr fun expression member => by
      rcases rowFacts expression member with ext | broadcast
      · simpa using (cendPEInertProducerExt_facts expression ext).1
      · simpa using (parsedExprIsL1ToPEProducer_facts expression broadcast).1
  · exact List.filter_eq_nil_iff.mpr fun expression member => by
      rcases rowFacts expression member with ext | broadcast
      · simpa using (cendPEInertProducerExt_facts expression ext).2.1
      · simpa using (parsedExprIsL1ToPEProducer_facts expression broadcast).2.1
  · exact List.filter_eq_nil_iff.mpr fun expression member => by
      rcases rowFacts expression member with ext | broadcast
      · simpa using (cendPEInertProducerExt_facts expression ext).2.2.1
      · simpa using (parsedExprIsL1ToPEProducer_facts expression broadcast).2.2.1
  · exact List.filter_eq_nil_iff.mpr fun expression member => by
      rcases rowFacts expression member with ext | broadcast
      · simpa using (cendPEInertProducerExt_facts expression ext).2.2.2.1
      · simpa using (parsedExprIsL1ToPEProducer_facts expression broadcast).2.2.2.1
  · exact List.filter_eq_nil_iff.mpr fun expression member => by
      rcases rowFacts expression member with ext | broadcast
      · simpa using (cendPEInertProducerExt_facts expression ext).2.2.2.2.1
      · simpa using (parsedExprIsL1ToPEProducer_facts expression broadcast).2.2.2.2.1
  · exact List.any_eq_false.mpr fun expression member => by
      rcases rowFacts expression member with ext | broadcast
      · simpa using (cendPEInertProducerExt_facts expression ext).2.2.2.2.2.2
      · simpa using (parsedExprIsL1ToPEProducer_facts expression broadcast).2.2.2.2.2.1
  · intro expression member
    rcases rowFacts expression (List.mem_filter.mp member).1 with ext | broadcast
    · exact cendPEInertProducerExt_stageInput_noforward expression ext
        (List.mem_filter.mp member).2
    · have stageTrue := (List.mem_filter.mp member).2
      have stageFalse := (parsedExprIsL1ToPEProducer_facts expression broadcast).2.2.2.2.2.2
      rw [stageFalse] at stageTrue
      simp at stageTrue

/-- **A successful line whose rows are extended-inert or broadcasts leaves the
observed LM1 bank at the initial zero.** -/
theorem executeIntegerProducerInstructionLine_pe_lm1_zero_of_l1ToPE
    (normalizedExpressions : List NormalizedExpr) (input : BitVec 64) (next : State)
    (rows : ∀ expression ∈ normalizedExpressions.map NormalizedExpr.toParsed,
      cendL1ToPEOrExtInert expression = true)
    (success : executeIntegerProducerInstructionLine (.pe normalizedExpressions)
      (cendInitialState input) = .ok next) :
    ∀ address, (next.peRegisters cendPE).lm1 address = 0 := by
  have accepted := executeIntegerProducerInstructionLine_accepted_of_ok
    (.pe normalizedExpressions) (cendInitialState input) next success
  obtain ⟨mslEmpty, reluEmpty, blockEmpty, mauEmpty, floatEmpty, noBAR, stageAll⟩ :=
    cendL1ToPE_list_facts (normalizedExpressions.map NormalizedExpr.toParsed) rows
  have supportedAny : normalizedExpressions.all
      (parsedExprIsSupportedPELineProducer ∘ NormalizedExpr.toParsed) = true := by
    simpa [List.all_map] using
      executeIntegerProducerInstructionLine_pe_supported_of_ok normalizedExpressions
        (cendInitialState input) next success
  have noUnsupportedAny : normalizedExpressions.any
      (parsedExprIsUnsupportedRustAlu ∘ NormalizedExpr.toParsed) = false := by
    simpa [List.any_map] using
      executeIntegerProducerInstructionLine_pe_noUnsupported_of_ok normalizedExpressions
        (cendInitialState input) next success
  have waitsAny : normalizedExpressions.any
      ((parsedExprWaitPending (cendInitialState input)) ∘ NormalizedExpr.toParsed) = false := by
    simpa [List.any_map] using
      executeIntegerProducerInstructionLine_pe_waits_complete normalizedExpressions
        (cendInitialState input) next success
  unfold executeIntegerProducerInstructionLine at success
  simp [accepted, supportedAny, noUnsupportedAny, waitsAny] at success
  split at success
  · cases success
  · cases success
  · rename_i nextPEs executed
    rw [executeParsedMslMsrProducers_nil (cendInitialState input) nextPEs
      (normalizedExpressions.map NormalizedExpr.toParsed) _ _ mslEmpty] at success
    dsimp only at success
    rw [executeParsedFloatReluProducers_nil (cendInitialState input) nextPEs
      (normalizedExpressions.map NormalizedExpr.toParsed) _ _ reluEmpty] at success
    dsimp only at success
    rw [executeParsedBlockFloatProducer_nil (cendInitialState input) nextPEs
      (normalizedExpressions.map NormalizedExpr.toParsed) _ _ blockEmpty] at success
    dsimp only at success
    split at success
    · cases success
    · cases success
    · rename_i afterMatrix matrixExec
      split at success
      · cases success
      · cases success
      · rename_i afterBlocks sharedExec
        split at success
        · cases success
        · cases success
        · rename_i afterBroadcast broadcastExec
          simp only [StepResult.ok.injEq] at success
          have coreFrame := executeIntegerProducerLineAtPEs_peRegisters_of_inert
            ((normalizedExpressions.map NormalizedExpr.toParsed).filter fun expression =>
              !parsedExprIsL2BMProducer expression && !parsedExprIsMslMsrProducer expression &&
                !parsedExprIsMatrixMAUProducer expression &&
                !parsedExprIsBlockFloatProducer expression &&
                !parsedExprIsFloatReluProducer expression)
            (List.finRange 4096)
            (fun expression member =>
              stageAll expression
                (List.mem_filter.mpr
                  ⟨(List.mem_filter.mp (List.mem_filter.mp member).1).1,
                    (List.mem_filter.mp member).2⟩))
            (List.filter_eq_nil_iff.mpr fun expression member => by
              have member' : expression ∈ normalizedExpressions.map NormalizedExpr.toParsed :=
                (List.mem_filter.mp member).1
              have := (List.filter_eq_nil_iff.mp floatEmpty) expression member'
              simpa using this)
            (List.any_eq_false.mpr fun expression member => by
              have member' : expression ∈ normalizedExpressions.map NormalizedExpr.toParsed :=
                (List.mem_filter.mp member).1
              have := (List.any_eq_false.mp noBAR) expression member'
              simpa using this)
            (cendInitialState input) nextPEs executed
          have matrixFrame : afterMatrix.peRegisters = nextPEs.peRegisters :=
            funext fun pe =>
              executeParsedMatrixMAUAndWrites_peRegisters_frame_of_noMatrixMAU
                (cendInitialState input) nextPEs afterMatrix
                (normalizedExpressions.map NormalizedExpr.toParsed) _ _ mauEmpty matrixExec pe
          have blockFrame : afterBlocks.peRegisters = afterMatrix.peRegisters :=
            executeParsedSharedBlockProducers_peRegisters (cendInitialState input) afterMatrix
              afterBlocks (normalizedExpressions.map NormalizedExpr.toParsed) _ sharedExec
          have afterZero : ∀ p, (afterBlocks.peRegisters p).lm1 = fun _ => 0 := fun p => by
            rw [blockFrame, matrixFrame, coreFrame]
            rfl
          have broadcastZero := executeParsedL1ToPEProducers_lm1_zero
            (cendInitialState input) afterBlocks afterBroadcast
            (normalizedExpressions.map NormalizedExpr.toParsed) _ _ _
            (fun expression member access lowered pe cycle =>
              cendInitialState_l1ToPEBusAt_zero input expression access pe cycle)
            afterZero broadcastExec
          intro address
          rw [← success]
          simpa using congrFun (broadcastZero cendPE) address

/-- **Every line whose rows are extended-inert or broadcasts is incorrect.** -/
theorem cendPE_l1ToPEOrExtInertLines_not_correct (expressions : List NormalizedExpr)
    (rows : ∀ expression ∈ expressions.map NormalizedExpr.toParsed,
      cendL1ToPEOrExtInert expression = true) :
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
      have zero := executeIntegerProducerInstructionLine_pe_lm1_zero_of_l1ToPE
        expressions cendWitness next rows lineExecuted
      refine cend_not_correct_of_lm1_zero expressions next step ?_
      intro address
      exact zero address

/-! ## 7. The enlarged closed class -/

/-- The closed lines of `CendUnconditional`, the extended-inert family, and the
lines whose PE writers are L1BM to-PE broadcasts. -/
def CendClosedLinesExt (expressions : List NormalizedExpr) : Prop :=
  CendClosedLines expressions ∨
    (∀ expression ∈ expressions.map NormalizedExpr.toParsed,
      cendPEInertProducerExt expression = true) ∨
    (∀ expression ∈ expressions.map NormalizedExpr.toParsed,
      cendL1ToPEOrExtInert expression = true)

theorem cendPE_closedLinesExt_not_correct (expressions : List NormalizedExpr)
    (closed : CendClosedLinesExt expressions) :
    ¬ ProofsLean.Correct cendSealedMachine cendSpec
      ([InstructionLine.pe expressions] : List InstructionLine) := by
  rcases closed with closed | extInert | broadcast
  · exact cendPE_closedLines_not_correct expressions closed
  · exact cendPE_extInertLines_not_correct expressions extInert
  · exact cendPE_l1ToPEOrExtInertLines_not_correct expressions broadcast

/-! ## 8. The remaining statement -/

/-- **The residual after the extended-inert and broadcast closures.**  A `.pe`
line that is not in the closed class of `CendUnconditional`, not covered by the
extended-inert/broadcast class `cendL1ToPEOrExtInert`, and not all-plain.  The
plain family is discharged by `cendPE_plainLines_not_correct_unconditional`, the
closed class by `cendPE_closedLines_not_correct`, and the extended-inert /
broadcast class by `cendPE_l1ToPEOrExtInertLines_not_correct` (the all-inert
sub-case is `cendPE_extInertLines_not_correct`), so this is exactly what remains
of `CendPENonClosedRefuted`.

Equivalently, every line still covered here has at least one row outside
`cendL1ToPEOrExtInert`, i.e. a PE-register-writing row from one of the six
value families: plain ALU (`.alu`/`.zero`/`.immediate`), `.matrixRead`, float
MAU, float relu, `msl`/`msr`, or matrix MAU / block float. -/
def CendNonPlainResidual : Prop :=
  ∀ expressions : List NormalizedExpr,
    ¬ CendClosedLines expressions →
    ¬ (∀ expression ∈ expressions.map NormalizedExpr.toParsed,
      cendL1ToPEOrExtInert expression = true) →
    ¬ (expressions.map NormalizedExpr.toParsed).all parsedExprIsPlainIntegerALU = true →
    ¬ ProofsLean.Correct cendSealedMachine cendSpec
      ([InstructionLine.pe expressions] : List InstructionLine)

/-- **`CendPENonClosedRefuted` from the smaller residual.** -/
theorem cendPENonClosedRefuted_of_nonPlainResidual (residual : CendNonPlainResidual) :
    CendPENonClosedRefuted := by
  intro expressions notClosed
  by_cases broadcast : ∀ expression ∈ expressions.map NormalizedExpr.toParsed,
      cendL1ToPEOrExtInert expression = true
  · exact cendPE_l1ToPEOrExtInertLines_not_correct expressions broadcast
  · by_cases plain : (expressions.map NormalizedExpr.toParsed).all
        parsedExprIsPlainIntegerALU = true
    · exact cendPE_plainLines_not_correct_unconditional expressions plain
    · exact residual expressions notClosed broadcast plain

/-- **The unconditional lower bound at two from the smaller residual.** -/
theorem cendLowerBound_two_of_nonPlainResidual (residual : CendNonPlainResidual) :
    ProofsLean.LowerBound cendSealedMachine cendSpec 2 :=
  cendLowerBound_two_of_nonClosed_plainDischarged
    (cendPENonClosedRefuted_of_nonPlainResidual residual)

/-! ## Trust report -/

#print axioms cendPEInertProducerExt_facts
#print axioms cendPEInertProducerExt_stageInput_noforward
#print axioms cendPEInertProducerExt_list_facts
#print axioms executeIntegerProducerInstructionLine_pe_peRegisters_of_extInert
#print axioms cendPE_extInertLines_not_correct
#print axioms cendInitialState_l1ToPEBusAt_zero
#print axioms writeParsedL1ToPEDestination?_lm1_zero
#print axioms executeParsedL1ToPE_writeDestinations_lm1_zero
#print axioms executeParsedL1ToPE_writeCycles_lm1_zero
#print axioms executeParsedL1ToPEAtPEs_lm1_zero
#print axioms executeParsedL1ToPEProducer_lm1_zero
#print axioms executeParsedL1ToPEProducers_lm1_zero
#print axioms executeIntegerProducerInstructionLine_pe_lm1_zero_of_l1ToPE
#print axioms cendPE_l1ToPEOrExtInertLines_not_correct
#print axioms cendPE_closedLinesExt_not_correct
#print axioms cendPENonClosedRefuted_of_nonPlainResidual
#print axioms cendLowerBound_two_of_nonPlainResidual

end ProofsLean.MNCore
