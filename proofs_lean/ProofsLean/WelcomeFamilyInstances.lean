import ProofsLean.FrameStep
import ProofsLean.WelcomeHalfMAUCopy
import ProofsLean.WelcomeIntegerProvenance
import ProofsLean.WelcomeMatrixMAUCommit
import ProofsLean.WelcomeMatrixMAUShape
import ProofsLean.WelcomeLm1FrameResidual
import ProofsLean.WelcomeStageCommit
import ProofsLean.WelcomeValueBound
import ProofsLean.WelcomeWriterShape

/-! # Family writer instances for the six per-family shape obligations

`WelcomeValueBound.lean` §7 states six per-family `Prop`s
(`WelcomePEMatrixReadShapeObligation`, `WelcomePEMatrixMAUShapeObligation`,
`WelcomePEFloatMAUShapeObligation`, `WelcomePEMatrixWriteShapeObligation`,
`WelcomePEL1ToPEShapeObligation`, `WelcomePEL2BMShapeObligation`).  Each says that
every unrefuted line containing a row of the family satisfies
`WelcomePEWriteShape`.

## What this module proves

The family hypothesis of those `Prop`s does **not** say that the family row is
the unique `.lm1` writer: a family row that writes no PE bank can coexist with a
plain (or other) row that writes `lm1` (`welcomeLm1Writer_unique` only forbids
*two* `.lm1` writers).  `WelcomePEMatrixWriteShapeObligation` and
`WelcomePEL2BMShapeObligation` are entirely of this "writer is another row" kind,
because a `.matrixWrite` / `.l2bm` row never writes a PE register file.

This module therefore proves the *writer side* of the four families whose row
shapes are available, in the strongest form the existing lemmas support: the
distinguished family row is the only PE-register-writing row, and every other
row is PE-inert (`.noforward`, a non-pending `.wait`, a shared-block `.l1bm`
operation or a `.matrixWrite` row).  In that class the line's PE 0 register file
is exactly the family row's commit, and the row shape gives
`WelcomePEWriteShape`.

* `welcomePEWriteShape_of_floatMAUWriter_of_inertCompanions` — a float-MAU
  writer.  Uses the unconditional row shape
  `executeParsedFloatMAUsAtPE_zeroShape_static_unconditional`.
* `welcomePEWriteShape_of_matrixMAUWriter_of_inertCompanions` — a matrix-MAU
  writer, conditional on the datapath statement `WelcomePEMatrixMAUZeroBus`.
  Uses the generalized stage shape `executeParsedMatrixMAUAndWrites_shape_of_zeroBus`.
* `welcomePEWriteShape_singleton_of_floatMAU` and
  `welcomePEWriteShape_singleton_of_matrixMAU_of_zeroBus` — the one-row
  corollaries.

The `.matrixRead` writer case is already
`welcomePEWriteShape_of_matrixReadWriter` (`WelcomeWriterShape.lean` §6), and the
`.l1bm` broadcast writer case is
`welcomePEWriteShape_of_l1bmWriter_of_integerOrInert`
(`WelcomeIntegerProvenance.lean` §4); this module does not duplicate them.

## What is **not** proved

None of the six family `Prop`s is proved here.  The missing case is the
complement of the writer class above:

1. **The family row is not the unique `.lm1` writer.**  The line's shape is then
   decided by another row (plain, matrix-read, another family, or special ALU).
   That row's shape and the assembly have to be applied to a line that also
   contains the family row.  For `.matrixWrite` / `.l2bm` this is the *only*
   case.
2. **The family row is the writer, but companions belong to the middle
   families.**  Even with the family row as the writer, the other stages' write
   lists need write-list-level `.lm1` provenance (the stage bank frames
   `welcomePEStageLm1Frame` preserve the bank but do not identify the write
   list's `.lm1` destinations).  Round 42 records this as the remaining
   multi-family provenance gap.

No `sorry`, `admit`, `native_decide` or new axiom is used, no existing module is
edited, and neither `LowerBound 2` nor `Optimal` is claimed.
-/

namespace ProofsLean.MNCore

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false

open Issue
open PEMemory

/-! ## 1. Common facts -/

/-- The forwarding slots of every PE at the all-zero Welcome state are the
all-poison `welcomeZeroSlots`. -/
theorem welcomeFamily_initial_slots (pe : PEId) :
    stateForwardingSlots (welcomeInitialState welcomeZeroWords) pe = welcomeZeroSlots := by
  funext unit cycle
  simp [stateForwardingSlots, welcomeZeroSlots, welcomeInitialState, rustSimulatorInitialState]

/-! ## 2. The float-MAU writer -/

/-- **The syntactic facts of a supported float-MAU row.**  Such a row is not an
integer/matrix-read stage input, not a middle-family producer, not a
`.matrixWrite` row, not an L1BM-to-PE row and not a float-relu row. -/
theorem floatMAU_parsedExpr_predicates (expression : ParsedExpr)
    (float : parsedExprIsSupportedFloatMAUProducer expression = true) :
    parsedExprIsL2BMProducer expression = false ∧
    parsedExprIsMslMsrProducer expression = false ∧
    parsedExprIsMatrixMAUProducer expression = false ∧
    parsedExprIsBlockFloatProducer expression = false ∧
    parsedExprIsFloatReluProducer expression = false ∧
    parsedExprIsMatrixWriteProducer expression = false ∧
    parsedExprIsL1ToPEProducer expression = false ∧
    parsedExprIsIntegerMatrixReadStageInput expression = false := by
  rcases expression with ⟨op, sources, destinations, flush, text⟩
  cases op with
  | mau precision matrix kind half round =>
      cases precision <;> cases matrix <;>
        simp_all [parsedExprIsSupportedFloatMAUProducer, parsedExprIsL2BMProducer,
          parsedExprIsMslMsrProducer, parsedExprIsMatrixMAUProducer,
          parsedExprIsBlockFloatProducer, parsedExprIsFloatReluProducer,
          parsedExprIsMatrixWriteProducer, parsedExprIsL1ToPEProducer,
          parsedExprIsIntegerMatrixReadStageInput]
  | alu name precision unsigned arg =>
      simp_all [parsedExprIsSupportedFloatMAUProducer, parsedExprIsL2BMProducer,
        parsedExprIsMslMsrProducer, parsedExprIsMatrixMAUProducer,
        parsedExprIsBlockFloatProducer, parsedExprIsFloatReluProducer,
        parsedExprIsMatrixWriteProducer, parsedExprIsL1ToPEProducer,
        parsedExprIsIntegerMatrixReadStageInput]
  | immediate value unsigned =>
      simp_all [parsedExprIsSupportedFloatMAUProducer, parsedExprIsL2BMProducer,
        parsedExprIsMslMsrProducer, parsedExprIsMatrixMAUProducer,
        parsedExprIsBlockFloatProducer, parsedExprIsFloatReluProducer,
        parsedExprIsMatrixWriteProducer, parsedExprIsL1ToPEProducer,
        parsedExprIsIntegerMatrixReadStageInput]
  | zero =>
      simp_all [parsedExprIsSupportedFloatMAUProducer, parsedExprIsL2BMProducer,
        parsedExprIsMslMsrProducer, parsedExprIsMatrixMAUProducer,
        parsedExprIsBlockFloatProducer, parsedExprIsFloatReluProducer,
        parsedExprIsMatrixWriteProducer, parsedExprIsL1ToPEProducer,
        parsedExprIsIntegerMatrixReadStageInput]
  | matrixWrite precision =>
      simp_all [parsedExprIsSupportedFloatMAUProducer, parsedExprIsL2BMProducer,
        parsedExprIsMslMsrProducer, parsedExprIsMatrixMAUProducer,
        parsedExprIsBlockFloatProducer, parsedExprIsFloatReluProducer,
        parsedExprIsMatrixWriteProducer, parsedExprIsL1ToPEProducer,
        parsedExprIsIntegerMatrixReadStageInput]
  | matrixRead precision =>
      simp_all [parsedExprIsSupportedFloatMAUProducer, parsedExprIsL2BMProducer,
        parsedExprIsMslMsrProducer, parsedExprIsMatrixMAUProducer,
        parsedExprIsBlockFloatProducer, parsedExprIsFloatReluProducer,
        parsedExprIsMatrixWriteProducer, parsedExprIsL1ToPEProducer,
        parsedExprIsIntegerMatrixReadStageInput]
  | wait tag =>
      simp_all [parsedExprIsSupportedFloatMAUProducer, parsedExprIsL2BMProducer,
        parsedExprIsMslMsrProducer, parsedExprIsMatrixMAUProducer,
        parsedExprIsBlockFloatProducer, parsedExprIsFloatReluProducer,
        parsedExprIsMatrixWriteProducer, parsedExprIsL1ToPEProducer,
        parsedExprIsIntegerMatrixReadStageInput]
  | noforward =>
      simp_all [parsedExprIsSupportedFloatMAUProducer, parsedExprIsL2BMProducer,
        parsedExprIsMslMsrProducer, parsedExprIsMatrixMAUProducer,
        parsedExprIsBlockFloatProducer, parsedExprIsFloatReluProducer,
        parsedExprIsMatrixWriteProducer, parsedExprIsL1ToPEProducer,
        parsedExprIsIntegerMatrixReadStageInput]
  | l1bm operation =>
      cases operation <;>
        simp_all [parsedExprIsSupportedFloatMAUProducer, parsedExprIsL2BMProducer,
          parsedExprIsMslMsrProducer, parsedExprIsMatrixMAUProducer,
          parsedExprIsBlockFloatProducer, parsedExprIsFloatReluProducer,
          parsedExprIsMatrixWriteProducer, parsedExprIsL1ToPEProducer,
          parsedExprIsIntegerMatrixReadStageInput]
  | l2bm operation =>
      cases operation <;>
        simp_all [parsedExprIsSupportedFloatMAUProducer, parsedExprIsL2BMProducer,
          parsedExprIsMslMsrProducer, parsedExprIsMatrixMAUProducer,
          parsedExprIsBlockFloatProducer, parsedExprIsFloatReluProducer,
          parsedExprIsMatrixWriteProducer, parsedExprIsL1ToPEProducer,
          parsedExprIsIntegerMatrixReadStageInput]

/-- **A float-MAU writer at one PE of the all-zero line.**  If the integer-stage
filter contains only `.noforward` rows and the float filter is the single
writer `e`, the per-PE core step commits `e`'s row list. -/
theorem executeIntegerProducerLineAtPECore_floatWriter
    (expressions : List ParsedExpr) (e : ParsedExpr) (pe : PEId) (next : State)
    (float : parsedExprIsSupportedFloatMAUProducer e = true)
    (nodup : (e.toIssueExpr 0).writeBanks.Nodup)
    (floatFilter : expressions.filter parsedExprIsSupportedFloatMAUProducer = [e])
    (intAll : ∀ x ∈ expressions.filter parsedExprIsIntegerMatrixReadStageInput,
      x.op = .noforward)
    (executed : executeIntegerProducerLineAtPECore expressions
      (welcomeInitialState welcomeZeroWords) pe = .ok next) :
    ∃ writes, next.peRegisters pe =
      commitParsedMaskedWrites ((welcomeInitialState welcomeZeroWords).peRegisters pe) writes ∧
      (Lm1WritesDoubleCopy writes ∨ Lm1WritesNarrow writes) := by
  rw [executeIntegerProducerLineAtPECore.eq_1] at executed
  dsimp only at executed
  rw [parsedIntegerMatrixReadLineFourCycleStep_noforward
    (expressions := expressions.filter parsedExprIsIntegerMatrixReadStageInput) (all := intAll)]
    at executed
  dsimp only at executed
  split at executed
  · simp at executed
  · simp at executed
  · rename_i registersWithFloat floatBar0 floatBar1 floatOutputs hasMAUProducer floatExecuted
    simp only [updateSupportedPELineForwarding] at executed
    split at executed
    · simp at executed
    · simp at executed
    · rename_i forwarding updateExecuted
      simp only [StepResult.ok.injEq] at executed
      subst executed
      have slotsEq := welcomeFamily_initial_slots pe
      have readEq : (welcomeInitialState welcomeZeroWords).peRegisters pe = welcomeZeroFiles := rfl
      have floatCanonical : executeParsedFloatMAUsAtPE welcomeZeroFiles welcomeZeroFiles
          welcomeZeroSlots
          { pe := (ParsedIntegerContext.ofLinearIndex pe).pe,
            cycle := (ParsedIntegerContext.ofLinearIndex pe).cycle,
            bar0 := ((welcomeInitialState welcomeZeroWords).peContext pe).bar0,
            bar1 := ((welcomeInitialState welcomeZeroWords).peContext pe).bar1,
            tWord := ((welcomeInitialState welcomeZeroWords).peContext pe).tWord,
            group := (ParsedIntegerContext.ofLinearIndex pe).group,
            l2b := (ParsedIntegerContext.ofLinearIndex pe).l2b,
            l1b := (ParsedIntegerContext.ofLinearIndex pe).l1b,
            mab := (ParsedIntegerContext.ofLinearIndex pe).mab }
          [e] (welcomeInitialState welcomeZeroWords).maskDirective
          (expressions.any parsedExprHasSingleLineWriteMask) =
          .ok (registersWithFloat, floatBar0, floatBar1, floatOutputs, hasMAUProducer) := by
        have h := floatExecuted
        rw [readEq] at h
        rw [slotsEq] at h
        simpa [executeParsedFloatMAUsAtPE, floatFilter, float] using h
      obtain ⟨writes, commitEq, shape⟩ :=
        executeParsedFloatMAUsAtPE_zeroShape_static_unconditional e _ _ _ nodup
          registersWithFloat floatBar0 floatBar1 floatOutputs hasMAUProducer floatCanonical
      refine ⟨writes, ?_, shape⟩
      show (if pe = pe then registersWithFloat
        else (welcomeInitialState welcomeZeroWords).peRegisters pe) =
        commitParsedMaskedWrites ((welcomeInitialState welcomeZeroWords).peRegisters pe) writes
      rw [ite_eq_left rfl]
      exact commitEq

/-- **The float-MAU writer over the whole PE walk.**  At PE 0 (the head of
`List.finRange 4096`) the core commits the writer's list; the tail never revisits
PE 0. -/
theorem executeIntegerProducerLineAtPEs_floatWriter
    (expressions : List ParsedExpr) (e : ParsedExpr) (next : State)
    (float : parsedExprIsSupportedFloatMAUProducer e = true)
    (nodup : (e.toIssueExpr 0).writeBanks.Nodup)
    (floatFilter : expressions.filter parsedExprIsSupportedFloatMAUProducer = [e])
    (intAll : ∀ x ∈ expressions.filter parsedExprIsIntegerMatrixReadStageInput,
      x.op = .noforward)
    (executed : executeIntegerProducerLineAtPEs expressions (List.finRange 4096)
      (welcomeInitialState welcomeZeroWords) = .ok next) :
    ∃ writes, next.peRegisters welcomePE =
      commitParsedMaskedWrites welcomeZeroFiles writes ∧
      (Lm1WritesDoubleCopy writes ∨ Lm1WritesNarrow writes) := by
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
    have coreExecuted : executeIntegerProducerLineAtPECore expressions
        (welcomeInitialState welcomeZeroWords) welcomePE = .ok nextPEs := by
      unfold executeIntegerProducerLineAtPE at headExecuted
      split at headExecuted
      · simp at headExecuted
      · exact headExecuted
    obtain ⟨writes, commitEq, shape⟩ :=
      executeIntegerProducerLineAtPECore_floatWriter expressions e welcomePE nextPEs
        float nodup floatFilter intAll coreExecuted
    have notMem : welcomePE ∉ (List.finRange 4095).map Fin.succ := by
      intro hmem
      simp only [List.mem_map] at hmem
      obtain ⟨i, _, hi⟩ := hmem
      have := congrArg Fin.val hi
      simp [welcomePE] at this
    have tailFrame := executeIntegerProducerLineAtPEs_peRegisters_not_mem expressions
      ((List.finRange 4095).map Fin.succ) nextPEs next executed
      (fun pe p s n he different =>
        executeIntegerProducerLineAtPE_peRegisters_other expressions s n pe p different he)
      welcomePE notMem
    refine ⟨writes, ?_, shape⟩
    rw [tailFrame, commitEq]
    change commitParsedMaskedWrites welcomeZeroFiles writes =
      commitParsedMaskedWrites welcomeZeroFiles writes
    rfl

/-- **The float-MAU writer line shape.**  If the line has a single float-MAU row
`e`, every row the integer stage prepares is `.noforward`, the four middle
stages and the L1BM-to-PE stage have empty filters, and there is no `.l2bm` row,
then the line's PE 0 write shape is the float row's own shape.  The companions
may be `.noforward`, non-pending `.wait`, shared-block `.l1bm` or `.matrixWrite`
rows; all of those are PE-inert. -/
theorem welcomePEWriteShape_of_floatMAUWriter_of_inertCompanions
    (expressions : List NormalizedExpr) (e : ParsedExpr)
    (float : parsedExprIsSupportedFloatMAUProducer e = true)
    (nodup : (e.toIssueExpr 0).writeBanks.Nodup)
    (floatFilter : (expressions.map NormalizedExpr.toParsed).filter
      parsedExprIsSupportedFloatMAUProducer = [e])
    (intAll : ∀ x ∈ (expressions.map NormalizedExpr.toParsed).filter
      parsedExprIsIntegerMatrixReadStageInput, x.op = .noforward)
    (mslNil : (expressions.map NormalizedExpr.toParsed).filter
      parsedExprIsMslMsrProducer = [])
    (reluNil : (expressions.map NormalizedExpr.toParsed).filter
      parsedExprIsFloatReluProducer = [])
    (blockNil : (expressions.map NormalizedExpr.toParsed).filter
      parsedExprIsBlockFloatProducer = [])
    (mmauNil : (expressions.map NormalizedExpr.toParsed).filter
      parsedExprIsMatrixMAUProducer = [])
    (l2bmNil : (expressions.map NormalizedExpr.toParsed).filter
      parsedExprIsL2BMProducer = [])
    (l1Nil : (expressions.map NormalizedExpr.toParsed).filter
      parsedExprIsL1ToPEProducer = []) :
    WelcomePEWriteShape expressions := by
  apply welcomePEWriteShape_of_commit_shape
  intro next step
  have executed := welcomeSealed_step_ok step
  simp only [executeNormalizedLine, NormalizedLine.toInstruction?,
    Issue.InstructionLine.toNormalizedLine] at executed
  obtain ⟨accepted, waits, unsupported, supported⟩ :=
    executeIntegerProducerInstructionLine_pe_conditions expressions
      (welcomeInitialState welcomeZeroWords) next executed
  have outerFilter : (expressions.map NormalizedExpr.toParsed).filter (fun x =>
      !parsedExprIsL2BMProducer x && !parsedExprIsMslMsrProducer x &&
        !parsedExprIsMatrixMAUProducer x && !parsedExprIsBlockFloatProducer x &&
        !parsedExprIsFloatReluProducer x) = expressions.map NormalizedExpr.toParsed := by
    rw [List.filter_eq_self]
    intro x mem
    have l2 := (List.filter_eq_nil_iff.mp l2bmNil) x mem
    have msl := (List.filter_eq_nil_iff.mp mslNil) x mem
    have mmau := (List.filter_eq_nil_iff.mp mmauNil) x mem
    have block := (List.filter_eq_nil_iff.mp blockNil) x mem
    have relu := (List.filter_eq_nil_iff.mp reluNil) x mem
    simp [l2, msl, mmau, block, relu]
  obtain ⟨nextPEs, nextMsl, nextRelu, nextBlockFloat, afterMatrix, nextShared, nextBroadcast,
    walkExecuted, mslExecuted, reluExecuted, blockExecuted, matrixExecuted, sharedExecuted,
    l1Executed, nextEq⟩ :=
    executeIntegerProducerInstructionLine_pe_stages_exists expressions
      (welcomeInitialState welcomeZeroWords) next accepted waits unsupported supported executed
  rw [outerFilter] at walkExecuted
  obtain ⟨writes, commitWrites, shapeWrites⟩ :=
    executeIntegerProducerLineAtPEs_floatWriter (expressions.map NormalizedExpr.toParsed)
      e nextPEs float nodup floatFilter intAll walkExecuted
  have mslId : executeParsedMslMsrProducers (welcomeInitialState welcomeZeroWords) nextPEs
      (expressions.map NormalizedExpr.toParsed)
      (expressions.any (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed))
      (expressions.any (parsedExprHasSingleLineWriteMask ∘ NormalizedExpr.toParsed)) =
      .ok nextPEs := executeParsedMslMsrProducers_eq_self _ _ _ _ _ mslNil
  have nextMslEq : nextMsl = nextPEs := by
    rw [mslId] at mslExecuted; exact (StepResult.ok.inj mslExecuted).symm
  have reluId : executeParsedFloatReluProducers (welcomeInitialState welcomeZeroWords) nextMsl
      (expressions.map NormalizedExpr.toParsed)
      (expressions.any (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed))
      (expressions.any (parsedExprHasSingleLineWriteMask ∘ NormalizedExpr.toParsed)) =
      .ok nextMsl := executeParsedFloatReluProducers_eq_self _ _ _ _ _ reluNil
  have nextReluEq : nextRelu = nextMsl := by
    rw [reluId] at reluExecuted; exact (StepResult.ok.inj reluExecuted).symm
  have blockId : executeParsedBlockFloatProducer (welcomeInitialState welcomeZeroWords) nextRelu
      (expressions.map NormalizedExpr.toParsed)
      (expressions.any (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed))
      (expressions.any (parsedExprHasSingleLineWriteMask ∘ NormalizedExpr.toParsed)) =
      .ok nextRelu := executeParsedBlockFloatProducer_eq_self _ _ _ _ _ blockNil
  have nextBlockFloatEq : nextBlockFloat = nextRelu := by
    rw [blockId] at blockExecuted; exact (StepResult.ok.inj blockExecuted).symm
  have matrixFrame : afterMatrix.peRegisters welcomePE = nextBlockFloat.peRegisters welcomePE :=
    executeParsedMatrixMAUAndWrites_peRegisters_frame_of_noMatrixMAU
      (welcomeInitialState welcomeZeroWords) nextBlockFloat afterMatrix
      (expressions.map NormalizedExpr.toParsed)
      (expressions.any (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed))
      (expressions.any (parsedExprHasSingleLineWriteMask ∘ NormalizedExpr.toParsed))
      mmauNil matrixExecuted welcomePE
  have sharedFrame : nextShared.peRegisters welcomePE = afterMatrix.peRegisters welcomePE :=
    congrFun (executeParsedSharedBlockProducers_peRegisters
      (welcomeInitialState welcomeZeroWords) afterMatrix nextShared _ _ sharedExecuted) welcomePE
  have l1Id : executeParsedL1ToPEProducers (welcomeInitialState welcomeZeroWords) nextShared
      (expressions.map NormalizedExpr.toParsed)
      (expressions.any (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed))
      (expressions.any (parsedExprHasSingleLineWriteMask ∘ NormalizedExpr.toParsed))
      (parsedL1ToPEPrecedesOMRWriter (expressions.map NormalizedExpr.toParsed)) =
      .ok nextShared := executeParsedL1ToPEProducers_eq_self _ _ _ _ _ _ l1Nil
  have nextBroadcastEq : nextBroadcast = nextShared := by
    rw [l1Id] at l1Executed; exact (StepResult.ok.inj l1Executed).symm
  refine ⟨writes, ?_, shapeWrites⟩
  have peNext : next.peRegisters welcomePE = nextBroadcast.peRegisters welcomePE := by rw [nextEq]
  rw [peNext, nextBroadcastEq, sharedFrame, matrixFrame, nextBlockFloatEq, nextReluEq,
    nextMslEq, commitWrites]
  rfl

/-- **The one-row float-MAU writer instance.** -/
theorem welcomePEWriteShape_singleton_of_floatMAU (expression : NormalizedExpr)
    (float : parsedExprIsSupportedFloatMAUProducer expression.toParsed = true)
    (nodup : (expression.toParsed.toIssueExpr 0).writeBanks.Nodup) :
    WelcomePEWriteShape [expression] := by
  obtain ⟨l2bmF, mslF, mmauF, blockF, reluF, mwriteF, l1F, intF⟩ :=
    floatMAU_parsedExpr_predicates expression.toParsed float
  have mapEq : [expression].map NormalizedExpr.toParsed = [expression.toParsed] := rfl
  have intNil : ([expression].map NormalizedExpr.toParsed).filter
      parsedExprIsIntegerMatrixReadStageInput = [] := by
    rw [mapEq]; simp [intF]
  refine welcomePEWriteShape_of_floatMAUWriter_of_inertCompanions [expression]
    expression.toParsed float nodup ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [mapEq]; simp [float]
  · intro x hx
    rw [intNil] at hx
    simp at hx
  · rw [mapEq]; simp [mslF]
  · rw [mapEq]; simp [reluF]
  · rw [mapEq]; simp [blockF]
  · rw [mapEq]; simp [mmauF]
  · rw [mapEq]; simp [l2bmF]
  · rw [mapEq]; simp [l1F]

/-! ## 3. The matrix-MAU writer -/

/-- **The syntactic facts of a matrix-MAU row.** -/
theorem matrixMAU_parsedExpr_predicates (expression : ParsedExpr)
    (mau : parsedExprIsMatrixMAUProducer expression = true) :
    parsedExprIsL2BMProducer expression = false ∧
    parsedExprIsMslMsrProducer expression = false ∧
    parsedExprIsBlockFloatProducer expression = false ∧
    parsedExprIsFloatReluProducer expression = false ∧
    parsedExprIsMatrixWriteProducer expression = false ∧
    parsedExprIsL1ToPEProducer expression = false ∧
    parsedExprIsSupportedFloatMAUProducer expression = false ∧
    parsedExprIsIntegerMatrixReadStageInput expression = false := by
  rcases expression with ⟨op, sources, destinations, flush, text⟩
  cases op with
  | mau precision matrix kind half round =>
      cases precision <;> cases matrix <;>
        simp_all [parsedExprIsMatrixMAUProducer, parsedExprIsL2BMProducer,
          parsedExprIsMslMsrProducer, parsedExprIsBlockFloatProducer,
          parsedExprIsFloatReluProducer, parsedExprIsMatrixWriteProducer,
          parsedExprIsL1ToPEProducer, parsedExprIsSupportedFloatMAUProducer,
          parsedExprIsIntegerMatrixReadStageInput]
  | alu name precision unsigned arg => simp_all [parsedExprIsMatrixMAUProducer]
  | immediate value unsigned => simp_all [parsedExprIsMatrixMAUProducer]
  | zero => simp_all [parsedExprIsMatrixMAUProducer]
  | matrixWrite precision => simp_all [parsedExprIsMatrixMAUProducer]
  | matrixRead precision => simp_all [parsedExprIsMatrixMAUProducer]
  | wait tag => simp_all [parsedExprIsMatrixMAUProducer]
  | noforward => simp_all [parsedExprIsMatrixMAUProducer]
  | l1bm operation => cases operation <;> simp_all [parsedExprIsMatrixMAUProducer]
  | l2bm operation => cases operation <;> simp_all [parsedExprIsMatrixMAUProducer]

/-- **The matrix-MAU/write stage shape at an arbitrary current state.**  The
read state is the all-zero state (which is where the zero bus comes from), but
the incoming register file is arbitrary; the stage commits the row's list on it.
This is the form needed when the integer stage has already written non-`.lm1`
banks before the matrix stage. -/
theorem executeParsedMatrixMAUAndWrites_shape_of_zeroBus
    (zeroBus : WelcomePEMatrixMAUZeroBus)
    (expressions : List ParsedExpr) (expression : ParsedExpr) (currentState next : State)
    (noForward hasSingleLineMask : Bool)
    (filterResult : expressions.filter parsedExprIsMatrixMAUProducer = [expression])
    (nodup : (expression.toIssueExpr 0).writeBanks.Nodup)
    (executed : executeParsedMatrixMAUAndWrites (welcomeInitialState welcomeZeroWords)
      currentState expressions noForward hasSingleLineMask = .ok next) :
    ∃ writes, next.peRegisters welcomePE =
      commitParsedMaskedWrites (currentState.peRegisters welcomePE) writes ∧
      (Lm1WritesDoubleCopy writes ∨ Lm1WritesNarrow writes) := by
  rw [executeParsedMatrixMAUAndWrites.eq_1] at executed
  cases producer : executeParsedMatrixMAUProducer (welcomeInitialState welcomeZeroWords)
      currentState expressions noForward hasSingleLineMask with
  | failure => rw [producer] at executed; simp at executed
  | unknown => rw [producer] at executed; simp at executed
  | ok afterMAU =>
      rw [producer] at executed
      let w := (lm1StaticWidth expression).getD PEMemory.Width.word
      have widths : Lm1DestWidths w expression.destinations := lm1StaticWidth_spec expression nodup
      have countOk : Lm1DestCount expression.destinations := lm1DestCount_any expression.destinations
      have budget : (expression.destinations.filter ParsedOperand.isLm1MemoryDestination).length ≤ 1 :=
        lm1Destinations_count_le_one expression 0 nodup
      by_cases isDouble : w = PEMemory.Width.double
      · rw [isDouble] at widths
        obtain ⟨writes, committed, wsWidth, wsCopy⟩ :=
          executeParsedMatrixMAUProducer_shape currentState afterMAU expressions expression
            noForward hasSingleLineMask PEMemory.Width.double filterResult widths countOk zeroBus
            producer
        have frame := executeParsedMatrixWritesAtMABs_preserves_pe_state
          (welcomeInitialState welcomeZeroWords) afterMAU next allMABCoordinates expressions executed
        refine ⟨writes, ?_, Or.inl ?_⟩
        · rw [frame.1]; exact committed
        · exact lm1WriteFacts_doubleCopy writes
            (lm1WriteFacts_of_parts PEMemory.Width.double writes wsWidth wsCopy)
      · obtain ⟨writes, committed, wsWidth, wsCount⟩ :=
          executeParsedMatrixMAUProducer_widthCount (welcomeInitialState welcomeZeroWords)
            currentState afterMAU expressions expression noForward hasSingleLineMask w filterResult
            widths countOk budget producer
        have frame := executeParsedMatrixWritesAtMABs_preserves_pe_state
          (welcomeInitialState welcomeZeroWords) afterMAU next allMABCoordinates expressions executed
        refine ⟨writes, ?_, Or.inr (lm1WidthFacts_narrow writes w wsWidth isDouble wsCount)⟩
        rw [frame.1]; exact committed

/-- An integer-stage preparation whose row filter contains only `.noforward`
rows produces the empty write list. -/
theorem welcomeIntegerPrep_noforward (state : State) (pe : PEId)
    (expressions : List ParsedExpr)
    (intAll : ∀ x ∈ expressions.filter parsedExprIsIntegerMatrixReadStageInput,
      x.op = .noforward) :
    welcomeIntegerPrep state pe expressions =
      .ok ([], stateForwardingSlots state pe, []) := by
  unfold welcomeIntegerPrep
  exact prepareParsedIntegerMatrixReadLineCycles_noforward _ _ _ _ _ _ intAll

/-- The integer stage leaves every visited PE's register file unchanged when its
row filter contains only `.noforward` rows and the float filter is empty. -/
theorem executeIntegerProducerLineAtPEs_identity_of_noforward
    (expressions : List ParsedExpr) (pes : List PEId) (state next : State)
    (floatEmpty : expressions.filter parsedExprIsSupportedFloatMAUProducer = [])
    (intAll : ∀ x ∈ expressions.filter parsedExprIsIntegerMatrixReadStageInput,
      x.op = .noforward)
    (executed : executeIntegerProducerLineAtPEs expressions pes state = .ok next)
    (nodup : pes.Nodup) (p : PEId) (mem : p ∈ pes) :
    next.peRegisters p = state.peRegisters p := by
  obtain ⟨writes, slots, bars, prep, committed⟩ :=
    executeIntegerProducerLineAtPEs_prepared expressions pes state next floatEmpty executed
      nodup p mem
  rw [welcomeIntegerPrep_noforward state p expressions intAll] at prep
  simp only [StepResult.ok.injEq, Prod.mk.injEq] at prep
  obtain ⟨rfl, rfl, rfl⟩ := prep
  simpa [commitParsedMaskedWrites] using committed

/-- **The matrix-MAU writer line shape.**  The distinguished matrix-MAU row `e`
is the only matrix-MAU row; the integer-stage filter contains only `.noforward`
rows, there is no float-MAU row, and the other stage filters are empty.  All
companions are PE-inert (`.noforward`, non-pending `.wait`, shared `.l1bm` or
`.matrixWrite`).  The shape is conditional on `WelcomePEMatrixMAUZeroBus`. -/
theorem welcomePEWriteShape_of_matrixMAUWriter_of_inertCompanions
    (zeroBus : WelcomePEMatrixMAUZeroBus)
    (expressions : List NormalizedExpr) (e : ParsedExpr)
    (_mau : parsedExprIsMatrixMAUProducer e = true)
    (nodup : (e.toIssueExpr 0).writeBanks.Nodup)
    (mauFilter : (expressions.map NormalizedExpr.toParsed).filter
      parsedExprIsMatrixMAUProducer = [e])
    (floatNil : (expressions.map NormalizedExpr.toParsed).filter
      parsedExprIsSupportedFloatMAUProducer = [])
    (intAll : ∀ x ∈ (expressions.map NormalizedExpr.toParsed).filter
      parsedExprIsIntegerMatrixReadStageInput, x.op = .noforward)
    (mslNil : (expressions.map NormalizedExpr.toParsed).filter
      parsedExprIsMslMsrProducer = [])
    (reluNil : (expressions.map NormalizedExpr.toParsed).filter
      parsedExprIsFloatReluProducer = [])
    (blockNil : (expressions.map NormalizedExpr.toParsed).filter
      parsedExprIsBlockFloatProducer = [])
    (l1Nil : (expressions.map NormalizedExpr.toParsed).filter
      parsedExprIsL1ToPEProducer = []) :
    WelcomePEWriteShape expressions := by
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
  let outer := ((expressions.map NormalizedExpr.toParsed).filter (fun x =>
      !parsedExprIsL2BMProducer x && !parsedExprIsMslMsrProducer x &&
        !parsedExprIsMatrixMAUProducer x && !parsedExprIsBlockFloatProducer x &&
        !parsedExprIsFloatReluProducer x))
  have outerInt : ∀ x ∈ outer.filter parsedExprIsIntegerMatrixReadStageInput,
      x.op = .noforward := by
    intro x hx
    dsimp only [outer] at hx
    obtain ⟨houter, hint⟩ := List.mem_filter.mp hx
    have hmap : x ∈ expressions.map NormalizedExpr.toParsed :=
      (List.mem_filter.mp houter).1
    exact intAll x (List.mem_filter.mpr ⟨hmap, hint⟩)
  have outerFloat : outer.filter parsedExprIsSupportedFloatMAUProducer = [] := by
    rw [List.filter_eq_nil_iff]
    intro x hx
    dsimp only [outer] at hx
    have hmap : x ∈ expressions.map NormalizedExpr.toParsed :=
      (List.mem_filter.mp hx).1
    have := (List.filter_eq_nil_iff.mp floatNil) x hmap
    simp [this]
  have nextPEsRegs : nextPEs.peRegisters welcomePE =
      (welcomeInitialState welcomeZeroWords).peRegisters welcomePE :=
    executeIntegerProducerLineAtPEs_identity_of_noforward outer (List.finRange 4096)
      (welcomeInitialState welcomeZeroWords) nextPEs outerFloat outerInt walkExecuted
      (List.nodup_finRange 4096) welcomePE (List.mem_finRange welcomePE)
  have mslId : executeParsedMslMsrProducers (welcomeInitialState welcomeZeroWords) nextPEs
      (expressions.map NormalizedExpr.toParsed)
      (expressions.any (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed))
      (expressions.any (parsedExprHasSingleLineWriteMask ∘ NormalizedExpr.toParsed)) =
      .ok nextPEs := executeParsedMslMsrProducers_eq_self _ _ _ _ _ mslNil
  have nextMslEq : nextMsl = nextPEs := by
    rw [mslId] at mslExecuted; exact (StepResult.ok.inj mslExecuted).symm
  have reluId : executeParsedFloatReluProducers (welcomeInitialState welcomeZeroWords) nextMsl
      (expressions.map NormalizedExpr.toParsed)
      (expressions.any (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed))
      (expressions.any (parsedExprHasSingleLineWriteMask ∘ NormalizedExpr.toParsed)) =
      .ok nextMsl := executeParsedFloatReluProducers_eq_self _ _ _ _ _ reluNil
  have nextReluEq : nextRelu = nextMsl := by
    rw [reluId] at reluExecuted; exact (StepResult.ok.inj reluExecuted).symm
  have blockId : executeParsedBlockFloatProducer (welcomeInitialState welcomeZeroWords) nextRelu
      (expressions.map NormalizedExpr.toParsed)
      (expressions.any (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed))
      (expressions.any (parsedExprHasSingleLineWriteMask ∘ NormalizedExpr.toParsed)) =
      .ok nextRelu := executeParsedBlockFloatProducer_eq_self _ _ _ _ _ blockNil
  have nextBlockFloatEq : nextBlockFloat = nextRelu := by
    rw [blockId] at blockExecuted; exact (StepResult.ok.inj blockExecuted).symm
  obtain ⟨writes, commitWrites, shapeWrites⟩ :=
    executeParsedMatrixMAUAndWrites_shape_of_zeroBus zeroBus
      (expressions.map NormalizedExpr.toParsed) e nextBlockFloat afterMatrix
      (expressions.any (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed))
      (expressions.any (parsedExprHasSingleLineWriteMask ∘ NormalizedExpr.toParsed))
      mauFilter nodup matrixExecuted
  have sharedFrame : nextShared.peRegisters welcomePE = afterMatrix.peRegisters welcomePE :=
    congrFun (executeParsedSharedBlockProducers_peRegisters
      (welcomeInitialState welcomeZeroWords) afterMatrix nextShared _ _ sharedExecuted) welcomePE
  have l1Id : executeParsedL1ToPEProducers (welcomeInitialState welcomeZeroWords) nextShared
      (expressions.map NormalizedExpr.toParsed)
      (expressions.any (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed))
      (expressions.any (parsedExprHasSingleLineWriteMask ∘ NormalizedExpr.toParsed))
      (parsedL1ToPEPrecedesOMRWriter (expressions.map NormalizedExpr.toParsed)) =
      .ok nextShared := executeParsedL1ToPEProducers_eq_self _ _ _ _ _ _ l1Nil
  have nextBroadcastEq : nextBroadcast = nextShared := by
    rw [l1Id] at l1Executed; exact (StepResult.ok.inj l1Executed).symm
  refine ⟨writes, ?_, shapeWrites⟩
  have peNext : next.peRegisters welcomePE = nextBroadcast.peRegisters welcomePE := by rw [nextEq]
  rw [peNext, nextBroadcastEq, sharedFrame]
  rw [commitWrites]
  have nextBlockRegs : nextBlockFloat.peRegisters welcomePE = welcomeZeroFiles := by
    rw [nextBlockFloatEq, nextReluEq, nextMslEq, nextPEsRegs]
    rfl
  rw [nextBlockRegs]
  rfl

/-- **The one-row matrix-MAU writer instance** (conditional on
`WelcomePEMatrixMAUZeroBus`). -/
theorem welcomePEWriteShape_singleton_of_matrixMAU_of_zeroBus
    (zeroBus : WelcomePEMatrixMAUZeroBus) (expression : NormalizedExpr)
    (mau : parsedExprIsMatrixMAUProducer expression.toParsed = true)
    (nodup : (expression.toParsed.toIssueExpr 0).writeBanks.Nodup) :
    WelcomePEWriteShape [expression] := by
  obtain ⟨l2bmF, mslF, blockF, reluF, mwriteF, l1F, floatF, intF⟩ :=
    matrixMAU_parsedExpr_predicates expression.toParsed mau
  have mapEq : [expression].map NormalizedExpr.toParsed = [expression.toParsed] := rfl
  have intNil : ([expression].map NormalizedExpr.toParsed).filter
      parsedExprIsIntegerMatrixReadStageInput = [] := by
    rw [mapEq]; simp [intF]
  have floatNil : ([expression].map NormalizedExpr.toParsed).filter
      parsedExprIsSupportedFloatMAUProducer = [] := by
    rw [mapEq]; simp [floatF]
  refine welcomePEWriteShape_of_matrixMAUWriter_of_inertCompanions zeroBus [expression]
    expression.toParsed mau nodup ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [mapEq]; simp [mau]
  · exact floatNil
  · intro x hx
    rw [intNil] at hx
    simp at hx
  · rw [mapEq]; simp [mslF]
  · rw [mapEq]; simp [reluF]
  · rw [mapEq]; simp [blockF]
  · rw [mapEq]; simp [l1F]

/-! ## 4. The exact remainder

The writer instances above cover the class

```
line = family writer + PE-inert companions,
```

where "PE-inert" means `.noforward`, a non-pending `.wait`, a shared-block
`.l1bm` operation or `.matrixWrite`.  They do **not** prove the six family
`Prop`s, because each `Prop` also quantifies over lines in which the family row
is not the unique `.lm1` writer.  In that case the line's shape is the shape of
another row:

* another family row (`.matrixRead`, float MAU, matrix MAU, L1BM, ...);
* a plain `.alu`/`.zero`/`.immediate` row (the `WelcomePEPlainShapeObligation`
  case, which is proved in `WelcomePlainStep.lean`);
* a special-ALU row (the msl/msr, float-relu or block-float stage).

For `.matrixWrite` / `.l2bm` the family row is *always* PE-inert, so their
`Prop`s are entirely of the other-row case.  The other remaining gap, for the
four writer cases with non-inert companions, is the write-list-level `.lm1`
provenance of the middle stages (the bank frames
`welcomePEStageLm1Frame` only preserve the bank, they do not identify the write
list's `.lm1` destinations).  That is the round-42 remainder.

Neither `LowerBound 2` nor `Optimal` is claimed. -/

end ProofsLean.MNCore
