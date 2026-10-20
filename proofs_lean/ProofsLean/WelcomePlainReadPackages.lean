import ProofsLean.WelcomeWriterPackages
import ProofsLean.WelcomeFloatCompanion

/-! # Plain reads: the plain-writer disjunct and the `.matrixRead` row data

Round 50 left the per-line writer packages of `WelcomeWriterPackages.lean` with
two data components that were still *assumed*:

* the plain package required, for a plain `.lm1` writer `e`, the disjunction
  `notDouble ∨ WelcomePEInputIndependent` — the immediate-`.double` writer had
  to be excluded unless the line was input-independent;
* the `.matrixRead` package required the row-local lowering data
  `e.op = .matrixRead precision`, `e.sources = [.matrix sideY width (some row)]`
  and a static `.lm1` width.

This module proves both components, and shrinks the packages accordingly.

## 1. The immediate-`.double` case with arbitrary `.lm1`-free companions

`welcomePEMixedImmediateDouble_inputIndependent` (`WelcomeMixedStructure.lean`)
proved the input-independence of an `.immediate` plain writer, but only when the
companion rows are `.noforward` / `.wait` (they then prepare no write at all).
The generalisation here allows *arbitrary* companions whose stages are
`.lm1`-free:

* the writer is the unique `.lm1` writer (`welcomeLm1Writer_rows`), so the
  `.lm1` part of the integer stage's write list is exactly the writer's own
  list (`welcomeIntegerPrep_split` + `Lm1FreePreparedWrites` of the outer
  blocks);
* a `.zero` / `.immediate` row's write list does not depend on the incoming or
  outgoing forwarding slots (`welcomePlain_constantRow_writes_nextSlots`), so
  it is the same in the all-zero and all-five runs even when the companions
  change the slots in between;
* the float-MAU stage is `.lm1`-free on the companion rows
  (`welcomePE_walk_prepared_float_clean`), and so are the four middle stages and
  the L1BM-to-PE stage, so PE 0's `.lm1` bank after the line is the integer
  stage's `.lm1` commit (`welcomePE_lm1_commit_of_stageFree`);
* finally the two commits agree because they have equal `.lm1` write lists
  (`commitParsedMaskedWrites_lm1_congr_of_filter`).

This yields `welcomePE_plainConstantWriter_inputIndependent`, the
immediate-`.double` specialisation
`welcomePEPlainImmediateDouble_inputIndependent_arbitrary`, and the disjunction
`welcomeMixed_notDouble_or_inputIndependent_arbitrary`.

## 2. The plain package

`WelcomePEPlainWriterDataForDoubleFree` keeps only the split position and the
non-repetition of the writer.  The immediate-double disjunct is *proved*
(`welcomePEPlainWriterDataFor_notDouble_or_inputIndependent`) and the split /
non-repetition follow from `welcomeLine_nodup`; the float half follows from the
writer's uniqueness (`floatFilter_lm1Free_of_rows`).  Hence the package is a
theorem (`welcomePEPlainWriterDataDoubleFree`) and the plain-writer line shape
needs no package hypothesis (`welcomePEWriteShape_of_plainWriter_closed`).
The flag-free package of `WelcomeFlagFreePlain.lean` implies the split package
(`welcomePEPlainWriterDataFor_doubleFree_of_flagFree`).

## 3. The `.matrixRead` package

`WelcomePEMatrixReadWriterDataForSplit` keeps only the split and
non-repetition.  Inside the consumer, given a successful row step:

* the lowering `ParsedExpr.toDirectMatrixReadAccesses?` yields
  `e.op = .matrixRead precision` and
  `e.sources = [.matrix sideY width (some row)]`
  (`toDirectMatrixReadAccesses?_op_sources`);
* the static `.lm1` width is `lm1StaticWidth`, whose specification
  (`lm1StaticWidth_spec`) is exactly `welcomeLm1Writer_nodup`;
* the float half follows from the writer's uniqueness.

The row shape with these data derived is
`prepareParsedMatrixRead_row_shape_of_read`; the line shape is
`welcomePEWriteShape_of_matrixReadWriter_closed`, again with no package
hypothesis.  The slot-free package of `WelcomeSlotFree.lean` implies the split
package (`welcomePEMatrixReadWriterDataFor_split_of_slotFree`).

## 4. Assembly

Both packages being theorems, `WelcomePELm1WriteShapeObligation` follows from
the `.l1bm` package alone (`welcomePELm1WriteShapeObligation_of_l1NoSingleton`),
whose `.l1bm` component is refutable per round 50 — so this is a reduction of
the remaining `.l1bm` obstruction, not a satisfiable path.  `LowerBound 2` and
`Optimal` are **not** claimed.

No `sorry`, no `admit`, no `native_decide`, no new axioms, and no existing
module is edited.
-/

namespace ProofsLean.MNCore

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

open Issue
open PEMemory

/-! ## 1. A constant row's writes do not depend on the output slots -/

/-- **At fixed register files, a constant row's cycle writes do not depend on
the output slots.**  The `.zero` / `.immediate` branch of
`prepareParsedIntegerALUExprCycle` reads neither the incoming slots nor the
output slots: only the mask registers, the destination operands and the
immediate payload enter the write list. -/
theorem welcomePlain_constantCycle_writes_sameFiles
    (files : IntegerRegisterFiles) (oldSlots : ProofsLean.MNCore.Forwarding.Slots)
    (nextSlotsA nextSlotsB : ProofsLean.MNCore.Forwarding.Slots)
    (expression : ParsedExpr) (control : ParsedMaskExecutionControl)
    (hasSingleLineMask noForward reduced : Bool) (cycle : Fin 4)
    (constant : expression.op = .zero ∨
      ∃ payload sparse, expression.op = .immediate payload sparse)
    (writesA : List PreparedParsedMaskedWrite)
    (slotsA : ProofsLean.MNCore.Forwarding.Slots)
    (writesB : List PreparedParsedMaskedWrite)
    (slotsB : ProofsLean.MNCore.Forwarding.Slots)
    (prepA : prepareParsedIntegerALUExprCycle files oldSlots nextSlotsA expression control
      hasSingleLineMask noForward reduced cycle = .ok (writesA, slotsA))
    (prepB : prepareParsedIntegerALUExprCycle files oldSlots nextSlotsB expression control
      hasSingleLineMask noForward reduced cycle = .ok (writesB, slotsB)) :
    writesA = writesB := by
  unfold prepareParsedIntegerALUExprCycle at prepA prepB
  dsimp only at prepA prepB
  rcases constant with isZero | ⟨payload, sparse, isImmediate⟩
  · simp only [isZero] at prepA prepB
    repeat' (first | split at prepA | split at prepB | simp_all)
  · simp only [isImmediate] at prepA prepB
    repeat' (first | split at prepA | split at prepB | simp_all)

/-- **A constant row's cycle writes do not depend on the output slots or on the
non-mask part of the register file.**  The two register files only need equal
mask registers. -/
theorem welcomePlain_constantCycle_writes_nextSlots
    (filesA filesB : IntegerRegisterFiles)
    (maskEq : filesA.maskRegisters = filesB.maskRegisters)
    (oldSlots : ProofsLean.MNCore.Forwarding.Slots)
    (nextSlotsA nextSlotsB : ProofsLean.MNCore.Forwarding.Slots)
    (expression : ParsedExpr) (control : ParsedMaskExecutionControl)
    (hasSingleLineMask noForward reduced : Bool) (cycle : Fin 4)
    (constant : expression.op = .zero ∨
      ∃ payload sparse, expression.op = .immediate payload sparse)
    (writesA : List PreparedParsedMaskedWrite)
    (slotsA : ProofsLean.MNCore.Forwarding.Slots)
    (writesB : List PreparedParsedMaskedWrite)
    (slotsB : ProofsLean.MNCore.Forwarding.Slots)
    (prepA : prepareParsedIntegerALUExprCycle filesA oldSlots nextSlotsA expression control
      hasSingleLineMask noForward reduced cycle = .ok (writesA, slotsA))
    (prepB : prepareParsedIntegerALUExprCycle filesB oldSlots nextSlotsB expression control
      hasSingleLineMask noForward reduced cycle = .ok (writesB, slotsB)) :
    writesA = writesB := by
  cases hC : prepareParsedIntegerALUExprCycle filesB oldSlots nextSlotsA expression control
      hasSingleLineMask noForward reduced cycle with
  | failure =>
      have hfiles := prepareParsedIntegerALUExprCycle_constant_eq filesA filesB oldSlots
        nextSlotsA expression control hasSingleLineMask noForward reduced cycle constant maskEq
      rw [prepA, hC] at hfiles
      simp at hfiles
  | unknown =>
      have hfiles := prepareParsedIntegerALUExprCycle_constant_eq filesA filesB oldSlots
        nextSlotsA expression control hasSingleLineMask noForward reduced cycle constant maskEq
      rw [prepA, hC] at hfiles
      simp at hfiles
  | ok result =>
      obtain ⟨writesC, slotsC⟩ := result
      have hfiles := prepareParsedIntegerALUExprCycle_constant_eq filesA filesB oldSlots
        nextSlotsA expression control hasSingleLineMask noForward reduced cycle constant maskEq
      rw [prepA, hC] at hfiles
      simp only [StepResult.ok.injEq, Prod.mk.injEq] at hfiles
      rw [hfiles.1]
      exact welcomePlain_constantCycle_writes_sameFiles filesB oldSlots nextSlotsA nextSlotsB
        expression control hasSingleLineMask noForward reduced cycle constant writesC slotsC
        writesB slotsB hC prepB

/-- **A fold of constant cycles: the writes do not depend on the output slots or
on the non-mask part of the register file.** -/
theorem welcomePlain_constantCycles_writes_nextSlots
    (filesA filesB : IntegerRegisterFiles)
    (maskEq : filesA.maskRegisters = filesB.maskRegisters)
    (oldSlots : ProofsLean.MNCore.Forwarding.Slots)
    (expression : ParsedExpr) (control : ParsedMaskExecutionControl)
    (hasSingleLineMask noForward reduced : Bool)
    (constant : expression.op = .zero ∨
      ∃ payload sparse, expression.op = .immediate payload sparse)
    (cycles : List (Fin 4)) :
    ∀ (writes₀ : List PreparedParsedMaskedWrite)
      (nextA nextB : ProofsLean.MNCore.Forwarding.Slots)
      (writesA : List PreparedParsedMaskedWrite)
      (slotsA : ProofsLean.MNCore.Forwarding.Slots)
      (writesB : List PreparedParsedMaskedWrite)
      (slotsB : ProofsLean.MNCore.Forwarding.Slots),
      prepareParsedIntegerALUCycles filesA oldSlots expression control hasSingleLineMask
          noForward reduced cycles writes₀ nextA = .ok (writesA, slotsA) →
      prepareParsedIntegerALUCycles filesB oldSlots expression control hasSingleLineMask
          noForward reduced cycles writes₀ nextB = .ok (writesB, slotsB) →
      writesA = writesB := by
  induction cycles with
  | nil =>
      intro writes₀ nextA nextB writesA slotsA writesB slotsB prepA prepB
      simp only [prepareParsedIntegerALUCycles, StepResult.ok.injEq, Prod.mk.injEq] at prepA prepB
      exact prepA.1.symm.trans prepB.1
  | cons cycle rest ih =>
      intro writes₀ nextA nextB writesA slotsA writesB slotsB prepA prepB
      simp only [prepareParsedIntegerALUCycles] at prepA prepB
      cases hA : prepareParsedIntegerALUExprCycle filesA oldSlots nextA expression control
          hasSingleLineMask noForward reduced cycle with
      | failure => simp [hA] at prepA
      | unknown => simp [hA] at prepA
      | ok resultA =>
          obtain ⟨cycleWritesA, cycleSlotsA⟩ := resultA
          cases hB : prepareParsedIntegerALUExprCycle filesB oldSlots nextB expression control
              hasSingleLineMask noForward reduced cycle with
          | failure => simp [hB] at prepB
          | unknown => simp [hB] at prepB
          | ok resultB =>
              obtain ⟨cycleWritesB, cycleSlotsB⟩ := resultB
              simp only [hA] at prepA
              simp only [hB] at prepB
              have cycleEq : cycleWritesA = cycleWritesB :=
                welcomePlain_constantCycle_writes_nextSlots filesA filesB maskEq oldSlots
                  nextA nextB expression control hasSingleLineMask noForward reduced cycle
                  constant cycleWritesA cycleSlotsA cycleWritesB cycleSlotsB hA hB
              rw [cycleEq] at prepA
              exact ih (writes₀ ++ cycleWritesB) cycleSlotsA cycleSlotsB writesA slotsA
                writesB slotsB prepA prepB

/-- **A constant row's line-expression writes do not depend on the output slots
or on the non-mask part of the register files.** -/
theorem welcomePlain_constantRow_writes_nextSlots
    (filesA filesB : IntegerRegisterFiles)
    (maskEq : filesA.maskRegisters = filesB.maskRegisters)
    (oldSlots : ProofsLean.MNCore.Forwarding.Slots)
    (store : ParsedMatrixReadStore) (expression : ParsedExpr)
    (control : ParsedMaskExecutionControl) (hasSingleLineMask noForward reduced : Bool)
    (constant : expression.op = .zero ∨
      ∃ payload sparse, expression.op = .immediate payload sparse)
    (nextA nextB : ProofsLean.MNCore.Forwarding.Slots)
    (writesA : List PreparedParsedMaskedWrite)
    (slotsA : ProofsLean.MNCore.Forwarding.Slots)
    (barsA : List (Bool × BitVec 12))
    (writesB : List PreparedParsedMaskedWrite)
    (slotsB : ProofsLean.MNCore.Forwarding.Slots)
    (barsB : List (Bool × BitVec 12))
    (prepA : prepareParsedIntegerMatrixReadLineExpression filesA oldSlots nextA store expression
      control hasSingleLineMask noForward reduced = .ok (writesA, slotsA, barsA))
    (prepB : prepareParsedIntegerMatrixReadLineExpression filesB oldSlots nextB store expression
      control hasSingleLineMask noForward reduced = .ok (writesB, slotsB, barsB)) :
    writesA = writesB := by
  unfold prepareParsedIntegerMatrixReadLineExpression at prepA prepB
  rcases constant with isZero | ⟨payload, sparse, isImmediate⟩
  · simp only [isZero] at prepA prepB
    cases hA : prepareParsedIntegerALUExprCycles filesA oldSlots nextA expression control
        hasSingleLineMask noForward reduced with
    | failure => simp [hA] at prepA
    | unknown => simp [hA] at prepA
    | ok resultA =>
        obtain ⟨cyclesA, slotsA'⟩ := resultA
        cases hB : prepareParsedIntegerALUExprCycles filesB oldSlots nextB expression control
            hasSingleLineMask noForward reduced with
        | failure => simp [hB] at prepB
        | unknown => simp [hB] at prepB
        | ok resultB =>
            obtain ⟨cyclesB, slotsB'⟩ := resultB
            simp only [hA, StepResult.ok.injEq, Prod.mk.injEq] at prepA
            simp only [hB, StepResult.ok.injEq, Prod.mk.injEq] at prepB
            rw [← prepA.1, ← prepB.1]
            exact welcomePlain_constantCycles_writes_nextSlots filesA filesB maskEq oldSlots
              expression control hasSingleLineMask noForward reduced (Or.inl isZero)
              parsedIntegerALUCycles [] nextA nextB cyclesA slotsA' cyclesB slotsB' hA hB
  · simp only [isImmediate] at prepA prepB
    cases hA : prepareParsedIntegerALUExprCycles filesA oldSlots nextA expression control
        hasSingleLineMask noForward reduced with
    | failure => simp [hA] at prepA
    | unknown => simp [hA] at prepA
    | ok resultA =>
        obtain ⟨cyclesA, slotsA'⟩ := resultA
        cases hB : prepareParsedIntegerALUExprCycles filesB oldSlots nextB expression control
            hasSingleLineMask noForward reduced with
        | failure => simp [hB] at prepB
        | unknown => simp [hB] at prepB
        | ok resultB =>
            obtain ⟨cyclesB, slotsB'⟩ := resultB
            simp only [hA, StepResult.ok.injEq, Prod.mk.injEq] at prepA
            simp only [hB, StepResult.ok.injEq, Prod.mk.injEq] at prepB
            rw [← prepA.1, ← prepB.1]
            exact welcomePlain_constantCycles_writes_nextSlots filesA filesB maskEq oldSlots
              expression control hasSingleLineMask noForward reduced
              (Or.inr ⟨payload, sparse, isImmediate⟩) parsedIntegerALUCycles [] nextA nextB
              cyclesA slotsA' cyclesB slotsB' hA hB

/-! ## 2. The `.lm1` bank of a line, from the integer stage alone -/

/-- **The integer stage of the walk's row filter.**  `welcomeIntegerPrep` only
sees the integer-stage rows, and the walk filter keeps all of them. -/
theorem welcomeIntegerPrep_walk (state : State) (expressions : List NormalizedExpr) :
    welcomeIntegerPrep state welcomePE (welcomePEWalkFilter expressions) =
      welcomeIntegerPrep state welcomePE (expressions.map NormalizedExpr.toParsed) := by
  unfold welcomeIntegerPrep
  rw [welcomePEWalkFilter_integer]

/-- **The per-line commit split at an arbitrary input.**  The version in
`WelcomeWriterDispatch.lean` is stated at the all-zero input; the `.lm1` value
argument needs it at both inputs of `WelcomePEInputIndependent`. -/
theorem welcomePE_commit_split_input
    (input : ProofsLean.MNCore.PlusOne.Words)
    (nextPEs nextMsl nextRelu nextBlockFloat afterMatrix nextShared nextBroadcast next : State)
    (peEq : next.peRegisters welcomePE = nextBroadcast.peRegisters welcomePE)
    (intWrites mslWrites reluWrites blockWrites matrixWrites l1Writes :
      List PreparedParsedMaskedWrite)
    (intCommit : nextPEs.peRegisters welcomePE =
      commitParsedMaskedWrites ((welcomeInitialState input).peRegisters welcomePE) intWrites)
    (mslCommit : nextMsl.peRegisters welcomePE =
      commitParsedMaskedWrites (nextPEs.peRegisters welcomePE) mslWrites)
    (reluCommit : nextRelu.peRegisters welcomePE =
      commitParsedMaskedWrites (nextMsl.peRegisters welcomePE) reluWrites)
    (blockCommit : nextBlockFloat.peRegisters welcomePE =
      commitParsedMaskedWrites (nextRelu.peRegisters welcomePE) blockWrites)
    (matrixCommit : afterMatrix.peRegisters welcomePE =
      commitParsedMaskedWrites (nextBlockFloat.peRegisters welcomePE) matrixWrites)
    (sharedFrame : nextShared.peRegisters welcomePE = afterMatrix.peRegisters welcomePE)
    (l1Commit : nextBroadcast.peRegisters welcomePE =
      commitParsedMaskedWrites (nextShared.peRegisters welcomePE) l1Writes) :
    next.peRegisters welcomePE =
      commitParsedMaskedWrites ((welcomeInitialState input).peRegisters welcomePE)
        (intWrites ++ mslWrites ++ reluWrites ++ blockWrites ++ matrixWrites ++ l1Writes) := by
  rw [peEq, l1Commit, sharedFrame, matrixCommit, blockCommit, reluCommit, mslCommit, intCommit]
  simp only [← commitParsedMaskedWrites_append, List.append_assoc]


/-- **The per-PE walk at PE 0 commits the integer list and a `.lm1`-free float
list**, at an arbitrary state.  This is
`executeIntegerProducerLineAtPEs_zero_prepared_float_clean` with the all-zero
input generalised to any input, which the two-run comparison needs. -/
theorem welcomePE_walk_prepared_float_clean
    (expressions : List ParsedExpr) (state next : State)
    (noLm1 : ∀ expression ∈ expressions.filter parsedExprIsSupportedFloatMAUProducer,
      WelcomeRowHasNoLm1Destination expression)
    (executed : executeIntegerProducerLineAtPEs expressions (List.finRange 4096) state =
      .ok next) :
    ∃ intWrites floatWrites slots bars,
      welcomeIntegerPrep state welcomePE expressions = .ok (intWrites, slots, bars) ∧
      next.peRegisters welcomePE =
        commitParsedMaskedWrites (state.peRegisters welcomePE) (intWrites ++ floatWrites) ∧
      Lm1FreePreparedWrites floatWrites := by
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
    have coreExecuted : executeIntegerProducerLineAtPECore expressions state welcomePE =
        .ok nextPEs := by
      unfold executeIntegerProducerLineAtPE at headExecuted
      split at headExecuted
      · simp at headExecuted
      · exact headExecuted
    obtain ⟨intWrites, floatWrites, slots, bars, intPrep, intCommit, floatFree⟩ :=
      executeIntegerProducerLineAtPECore_prepared_float_clean expressions state nextPEs
        welcomePE noLm1 coreExecuted
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
    refine ⟨intWrites, floatWrites, slots, bars, intPrep, ?_, floatFree⟩
    rw [tailFrame]
    exact intCommit

/-- **The line's PE 0 `.lm1` bank is the integer stage's `.lm1` commit.**  The
float-MAU stage, the four middle producers and the L1BM-to-PE stage are all
`.lm1`-free on the companion rows, so their commit lists do not change the
`.lm1` bank of PE 0.  The float half is genuinely present here: its filter is
only required to be row-locally `.lm1`-free, not empty. -/
theorem welcomePE_lm1_commit_of_stageFree
    (expressions : List NormalizedExpr) (input : ProofsLean.MNCore.PlusOne.Words)
    (next : State) (_unrefuted : WelcomePEUnrefuted expressions)
    (floatFreeRows : ∀ expression ∈ (expressions.map NormalizedExpr.toParsed).filter
      parsedExprIsSupportedFloatMAUProducer, WelcomeRowHasNoLm1Destination expression)
    (middleFree : WelcomePEMiddleStageLm1Free expressions)
    (matrixFreeRows : WelcomePEMatrixMAUStageLm1Free expressions)
    (l1FreeRows : WelcomePEL1StageLm1Free expressions)
    (step : welcomeSealedMachine.step (.pe expressions) (welcomeInitialState input) = some next) :
    ∃ (intWrites : List PreparedParsedMaskedWrite)
      (slots : ProofsLean.MNCore.Forwarding.Slots) (bars : List (Bool × BitVec 12)),
      welcomeIntegerPrep (welcomeInitialState input) welcomePE
          (expressions.map NormalizedExpr.toParsed) = .ok (intWrites, slots, bars) ∧
        (next.peRegisters welcomePE).lm1 =
          (commitParsedMaskedWrites
            ((welcomeInitialState input).peRegisters welcomePE) intWrites).lm1 := by
  have executed := welcomeSealed_step_ok step
  simp only [executeNormalizedLine, NormalizedLine.toInstruction?,
    Issue.InstructionLine.toNormalizedLine] at executed
  obtain ⟨accepted, waits, unsupported, supported⟩ :=
    executeIntegerProducerInstructionLine_pe_conditions expressions
      (welcomeInitialState input) next executed
  obtain ⟨nextPEs, nextMsl, nextRelu, nextBlockFloat, afterMatrix, nextShared, nextBroadcast,
    walkExecuted, mslExecuted, reluExecuted, blockExecuted, matrixExecuted, sharedExecuted,
    l1Executed, nextEq⟩ :=
    executeIntegerProducerInstructionLine_pe_stages_exists expressions
      (welcomeInitialState input) next accepted waits unsupported supported executed
  have floatFreeWalk : ∀ expression ∈ (welcomePEWalkFilter expressions).filter
      parsedExprIsSupportedFloatMAUProducer, WelcomeRowHasNoLm1Destination expression := by
    rw [welcomePEWalkFilter_float]
    exact floatFreeRows
  obtain ⟨intWrites, floatWrites, intSlots, intBars, intPrepWalk, intCommit, floatFree⟩ :=
    welcomePE_walk_prepared_float_clean (welcomePEWalkFilter expressions)
      (welcomeInitialState input) nextPEs floatFreeWalk walkExecuted
  have intPrep : welcomeIntegerPrep (welcomeInitialState input) welcomePE
      (expressions.map NormalizedExpr.toParsed) = .ok (intWrites, intSlots, intBars) := by
    rw [← welcomeIntegerPrep_walk]
    exact intPrepWalk
  obtain ⟨mslWrites, mslCommit, mslFree⟩ :=
    welcomePEMslMsrStageLm1Provenance (welcomeInitialState input) nextPEs nextMsl
      (expressions.map NormalizedExpr.toParsed)
      (expressions.any (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed))
      (expressions.any (parsedExprHasSingleLineWriteMask ∘ NormalizedExpr.toParsed))
      (welcomePEMiddleStageLm1Free_msl expressions middleFree) mslExecuted
  obtain ⟨reluWrites, reluCommit, reluFree⟩ :=
    welcomePEFloatReluStageLm1Provenance (welcomeInitialState input) nextMsl nextRelu
      (expressions.map NormalizedExpr.toParsed)
      (expressions.any (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed))
      (expressions.any (parsedExprHasSingleLineWriteMask ∘ NormalizedExpr.toParsed))
      (welcomePEMiddleStageLm1Free_relu expressions middleFree) reluExecuted
  obtain ⟨blockWrites, blockCommit, blockFree⟩ :=
    welcomePEBlockFloatStageLm1Provenance (welcomeInitialState input) nextRelu nextBlockFloat
      (expressions.map NormalizedExpr.toParsed)
      (expressions.any (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed))
      (expressions.any (parsedExprHasSingleLineWriteMask ∘ NormalizedExpr.toParsed))
      (welcomePEMiddleStageLm1Free_block expressions middleFree) blockExecuted
  obtain ⟨matrixWrites, matrixCommit, matrixFree⟩ :=
    welcomePEMatrixMAUStageLm1Provenance (welcomeInitialState input) nextBlockFloat afterMatrix
      (expressions.map NormalizedExpr.toParsed)
      (expressions.any (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed))
      (expressions.any (parsedExprHasSingleLineWriteMask ∘ NormalizedExpr.toParsed))
      (welcomePEMiddleStageLm1Free_matrixMAU expressions matrixFreeRows) matrixExecuted
  obtain ⟨l1Writes, l1Commit, l1Free⟩ :=
    welcomePEL1ToPEStageLm1Provenance (welcomeInitialState input) nextShared nextBroadcast
      (expressions.map NormalizedExpr.toParsed)
      (expressions.any (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed))
      (expressions.any (parsedExprHasSingleLineWriteMask ∘ NormalizedExpr.toParsed))
      (parsedL1ToPEPrecedesOMRWriter (expressions.map NormalizedExpr.toParsed))
      (welcomePEMiddleStageLm1Free_l1 expressions l1FreeRows) l1Executed
  have sharedFrame : nextShared.peRegisters welcomePE = afterMatrix.peRegisters welcomePE :=
    congrFun (executeParsedSharedBlockProducers_peRegisters (welcomeInitialState input)
      afterMatrix nextShared (expressions.map NormalizedExpr.toParsed)
      (!(expressions.any (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed)))
      sharedExecuted) welcomePE
  have peEq : next.peRegisters welcomePE = nextBroadcast.peRegisters welcomePE := by
    rw [nextEq]
  have commitEq := welcomePE_commit_split_input input nextPEs nextMsl nextRelu nextBlockFloat
    afterMatrix nextShared nextBroadcast next peEq (intWrites ++ floatWrites) mslWrites
    reluWrites blockWrites matrixWrites l1Writes intCommit mslCommit reluCommit blockCommit
    matrixCommit sharedFrame l1Commit
  refine ⟨intWrites, intSlots, intBars, intPrep, ?_⟩
  rw [commitEq]
  have assoc : intWrites ++ floatWrites ++ mslWrites ++ reluWrites ++ blockWrites ++
      matrixWrites ++ l1Writes =
      intWrites ++ (floatWrites ++ (mslWrites ++ (reluWrites ++ (blockWrites ++
        (matrixWrites ++ l1Writes))))) := by
    simp only [List.append_assoc]
  rw [assoc]
  refine commitParsedMaskedWrites_lm1_concat_of_only
    ((welcomeInitialState input).peRegisters welcomePE) intWrites
    (floatWrites ++ (mslWrites ++ (reluWrites ++ (blockWrites ++
      (matrixWrites ++ l1Writes))))) ?_
  intro write member
  simp only [List.mem_append] at member
  tauto


/-! ## 3. The `.lm1` commit depends only on the `.lm1` writes -/

/-- **Two commit lists with the same `.lm1` part give the same `.lm1` bank.** -/
theorem commitParsedMaskedWrites_lm1_congr_of_filter
    (filesA filesB : IntegerRegisterFiles)
    (writesA writesB : List PreparedParsedMaskedWrite)
    (hfiles : filesA.lm1 = filesB.lm1)
    (hwrites : writesA.filter PreparedParsedMaskedWrite.isLm1Write =
      writesB.filter PreparedParsedMaskedWrite.isLm1Write) :
    (commitParsedMaskedWrites filesA writesA).lm1 =
      (commitParsedMaskedWrites filesB writesB).lm1 := by
  rw [commitParsedMaskedWrites_lm1_filter filesA writesA,
    commitParsedMaskedWrites_lm1_filter filesB writesB]
  exact commitParsedMaskedWrites_lm1_congr filesA filesB _ _ hfiles hwrites

/-- **The `.lm1` bank of a line with arbitrary `.lm1`-free companions of a
constant writer.**  The writer is the unique `.lm1` writer; every other
integer-stage row, and every middle-stage row, is `.lm1`-free.  Hence the
`.lm1` output is the writer's own constant write list, which does not depend on
the input (the two runs differ only in the `lm0` words). -/
theorem welcomePE_plainConstantWriter_inputIndependent
    (expressions : List NormalizedExpr) (unrefuted : WelcomePEUnrefuted expressions)
    (before after : List ParsedExpr) (e : ParsedExpr)
    (split : (expressions.map NormalizedExpr.toParsed).filter
        parsedExprIsIntegerMatrixReadStageInput = before ++ e :: after)
    (eMem : e ∈ expressions.map NormalizedExpr.toParsed)
    (eWriter : Issue.Bank.lm1 ∈ (e.toIssueExpr 0).writeBanks)
    (notInBefore : e ∉ before) (notInAfter : e ∉ after)
    (constant : e.op = .zero ∨ ∃ payload sparse, e.op = .immediate payload sparse)
    (floatFreeRows : ∀ expression ∈ (expressions.map NormalizedExpr.toParsed).filter
      parsedExprIsSupportedFloatMAUProducer, WelcomeRowHasNoLm1Destination expression)
    (middleFree : WelcomePEMiddleStageLm1Free expressions)
    (matrixFreeRows : WelcomePEMatrixMAUStageLm1Free expressions)
    (l1FreeRows : WelcomePEL1StageLm1Free expressions) :
    WelcomePEInputIndependent expressions := by
  intro nextA stepA nextB stepB
  obtain ⟨writesA, slotsA, barsA, prepA, lm1A⟩ :=
    welcomePE_lm1_commit_of_stageFree expressions welcomeZeroWords nextA unrefuted
      floatFreeRows middleFree matrixFreeRows l1FreeRows stepA
  obtain ⟨writesB, slotsB, barsB, prepB, lm1B⟩ :=
    welcomePE_lm1_commit_of_stageFree expressions welcomeAllFiveWords nextB unrefuted
      floatFreeRows middleFree matrixFreeRows l1FreeRows stepB
  rw [lm1A, lm1B]
  have rows := welcomeLm1Writer_rows expressions unrefuted e eMem eWriter
  have freeBefore : ∀ expression ∈ before, WelcomeRowHasNoLm1Destination expression := by
    intro expression member
    apply rows expression
    · have inFilter : expression ∈ (expressions.map NormalizedExpr.toParsed).filter
          parsedExprIsIntegerMatrixReadStageInput := by
        rw [split]
        exact List.mem_append_left _ member
      exact (List.mem_filter.mp inFilter).1
    · intro same
      exact notInBefore (same ▸ member)
  have freeAfter : ∀ expression ∈ after, WelcomeRowHasNoLm1Destination expression := by
    intro expression member
    apply rows expression
    · have inFilter : expression ∈ (expressions.map NormalizedExpr.toParsed).filter
          parsedExprIsIntegerMatrixReadStageInput := by
        rw [split]
        exact List.mem_append_right _ (List.mem_cons_of_mem _ member)
      exact (List.mem_filter.mp inFilter).1
    · intro same
      exact notInAfter (same ▸ member)
  obtain ⟨beforeWritesA, prefixSlotsA, beforeBarsA, rowWritesA, rowSlotsA, rowBarsA,
    afterWritesA, afterSlotsA, afterBarsA, rowPrepA, intWritesEqA, beforeFreeA, afterFreeA⟩ :=
    welcomeIntegerPrep_split (welcomeInitialState welcomeZeroWords)
      (expressions.map NormalizedExpr.toParsed) before after e split freeBefore freeAfter
      writesA slotsA barsA prepA
  obtain ⟨beforeWritesB, prefixSlotsB, beforeBarsB, rowWritesB, rowSlotsB, rowBarsB,
    afterWritesB, afterSlotsB, afterBarsB, rowPrepB, intWritesEqB, beforeFreeB, afterFreeB⟩ :=
    welcomeIntegerPrep_split (welcomeInitialState welcomeAllFiveWords)
      (expressions.map NormalizedExpr.toParsed) before after e split freeBefore freeAfter
      writesB slotsB barsB prepB
  have rowEq : rowWritesA = rowWritesB :=
    welcomePlain_constantRow_writes_nextSlots
      ((welcomeInitialState welcomeZeroWords).peRegisters welcomePE)
      ((welcomeInitialState welcomeAllFiveWords).peRegisters welcomePE) rfl
      (stateForwardingSlots (welcomeInitialState welcomeZeroWords) welcomePE)
      ((welcomeInitialState welcomeZeroWords).matrixRegisters
        (ParsedIntegerContext.ofLinearIndex welcomePE).group
        (ParsedIntegerContext.ofLinearIndex welcomePE).l2b
        (ParsedIntegerContext.ofLinearIndex welcomePE).l1b)
      e (parsedPEHazardControl (welcomeInitialState welcomeZeroWords) welcomePE)
      ((before ++ e :: after).any parsedExprHasSingleLineWriteMask)
      ((before ++ e :: after).any fun expression =>
        match expression.op with
        | ParsedOp.noforward => true
        | _ => false)
      false constant prefixSlotsA prefixSlotsB rowWritesA rowSlotsA rowBarsA rowWritesB
      rowSlotsB rowBarsB rowPrepA rowPrepB
  have filtA : beforeWritesA.filter PreparedParsedMaskedWrite.isLm1Write = [] := by
    rw [List.filter_eq_nil_iff]
    intro write member
    simpa using beforeFreeA write member
  have filtB : beforeWritesB.filter PreparedParsedMaskedWrite.isLm1Write = [] := by
    rw [List.filter_eq_nil_iff]
    intro write member
    simpa using beforeFreeB write member
  have filtA' : afterWritesA.filter PreparedParsedMaskedWrite.isLm1Write = [] := by
    rw [List.filter_eq_nil_iff]
    intro write member
    simpa using afterFreeA write member
  have filtB' : afterWritesB.filter PreparedParsedMaskedWrite.isLm1Write = [] := by
    rw [List.filter_eq_nil_iff]
    intro write member
    simpa using afterFreeB write member
  have filtEq : writesA.filter PreparedParsedMaskedWrite.isLm1Write =
      writesB.filter PreparedParsedMaskedWrite.isLm1Write := by
    rw [intWritesEqA, intWritesEqB, List.filter_append, List.filter_append,
      List.filter_append, List.filter_append, filtA, filtB, filtA', filtB', rowEq]
  exact commitParsedMaskedWrites_lm1_congr_of_filter _ _ _ _ rfl filtEq


/-- **A successful matrix-read lowering exposes the row's operation and source
list.**  This is the inversion of `ParsedExpr.toDirectMatrixReadAccesses?`: the
`match` on `(op, sources)` fires only for `.matrixRead precision` with the
singleton source `.matrix sideY width (some row)`, and the bind then fixes
`accesses`. -/
theorem toDirectMatrixReadAccesses?_op_sources
    (expression : ParsedExpr) (registers : ProofsLean.MNCore.Masks.RegisterFile)
    (directive : ParsedMaskDirective) (hasSingleLineMask : Bool)
    (context : ParsedIntegerContext) (accesses : ParsedMatrixReadAccesses)
    (lowered : ParsedExpr.toDirectMatrixReadAccesses? expression registers directive
      hasSingleLineMask context = some accesses) :
    expression.op = .matrixRead accesses.precision ∧
      ∃ (sideY : Bool) (width : Fin 5) (row : Fin (2 ^ 32)),
        expression.sources = [.matrix sideY width (some row)] ∧
          accesses.sideY = sideY ∧ accesses.row = row.val := by
  unfold ParsedExpr.toDirectMatrixReadAccesses? at lowered
  split at lowered
  · rename_i precision sideY width row hop hsources
    change (do
        let targets ← List.mapM (parsedMatrixReadTargetAt? registers directive
          hasSingleLineMask context) expression.destinations
        some ⟨precision, sideY, row.val, targets⟩) = some accesses at lowered
    cases h : List.mapM (parsedMatrixReadTargetAt? registers directive
        hasSingleLineMask context) expression.destinations with
    | none => simp [h] at lowered
    | some targets =>
        rw [h] at lowered
        change Option.bind (some targets)
          (fun ts => some ⟨precision, sideY, row.val, ts⟩) = some accesses at lowered
        simp only [Option.bind_some, Option.some.injEq] at lowered
        subst lowered
        exact ⟨hop, sideY, width, row, hsources, rfl, rfl⟩
  · nomatch lowered


/-- **The `.matrixRead` row's `.lm1` shape at the all-zero state, from the
lowering alone.**  Neither the precision, the source coordinates nor the static
width are hypotheses: the `.matrixRead` predicate gives the operation (to unfold
the row step), the lowering gives the source list and the coordinates, and the
static width is `lm1StaticWidth` (the row's unique `.lm1` destination width,
`lm1StaticWidth_spec` from `welcomeLm1Writer_nodup`). -/
theorem prepareParsedMatrixRead_row_shape_of_read
    (expression : ParsedExpr) (read : parsedExprIsMatrixReadProducer expression = true)
    (nextSlots : ProofsLean.MNCore.Forwarding.Slots)
    (control : ParsedMaskExecutionControl) (hasSingleLineMask noForward reduced : Bool)
    (nodup : (expression.toIssueExpr 0).writeBanks.Nodup)
    (writes : List PreparedParsedMaskedWrite)
    (slots : ProofsLean.MNCore.Forwarding.Slots) (bars : List (Bool × BitVec 12))
    (prepared : prepareParsedIntegerMatrixReadLineExpression welcomeZeroFiles welcomeZeroSlots
      nextSlots welcomeZeroMatrixStore expression control hasSingleLineMask noForward reduced
      = .ok (writes, slots, bars)) :
    Lm1WritesDoubleCopy writes ∨ Lm1WritesNarrow writes := by
  obtain ⟨precision, op⟩ : ∃ p : ParsedPrecision, expression.op = .matrixRead p := by
    obtain ⟨op, sources, destinations, flush, text⟩ := expression
    cases op <;> simp_all [parsedExprIsMatrixReadProducer]
  unfold prepareParsedIntegerMatrixReadLineExpression at prepared
  rw [op] at prepared
  simp only at prepared
  have cyclesOk : prepareParsedMatrixReadExprCycles welcomeZeroFiles nextSlots
      welcomeZeroMatrixStore expression control.directive hasSingleLineMask noForward
      control.context = .ok (writes, slots, bars) := by
    cases h : prepareParsedMatrixReadExprCycles welcomeZeroFiles nextSlots
        welcomeZeroMatrixStore expression control.directive hasSingleLineMask noForward
        control.context with
    | failure => simp [h] at prepared
    | unknown => simp [h] at prepared
    | ok result =>
        obtain ⟨doneWrites, doneSlots, doneBars⟩ := result
        rw [h] at prepared
        simp only [StepResult.ok.injEq, Prod.mk.injEq] at prepared
        rw [prepared.1, prepared.2.1, prepared.2.2]
  obtain ⟨accesses, lowered⟩ : ∃ accesses : ParsedMatrixReadAccesses,
      ParsedExpr.toDirectMatrixReadAccesses? expression welcomeZeroFiles.maskRegisters
        control.directive hasSingleLineMask { control.context with cycle := (0 : Fin 4) } =
        some accesses := by
    unfold prepareParsedMatrixReadExprCycles at cyclesOk
    simp only [parsedMatrixReadCycles] at cyclesOk
    unfold prepareParsedMatrixReadCycles at cyclesOk
    cases h0 : prepareParsedMatrixReadCycle welcomeZeroFiles nextSlots welcomeZeroMatrixStore
        expression control.directive hasSingleLineMask noForward
        { control.context with cycle := (0 : Fin 4) } with
    | failure => simp [h0] at cyclesOk
    | unknown => simp [h0] at cyclesOk
    | ok result =>
        obtain ⟨cycleWrites, cycleSlots, cycleBars⟩ := result
        obtain ⟨found, _flushSelection, hfound, _⟩ :=
          prepareParsedMatrixReadCycle_ok_inv welcomeZeroFiles nextSlots
            welcomeZeroMatrixStore expression control.directive hasSingleLineMask noForward
            { control.context with cycle := (0 : Fin 4) } cycleWrites cycleSlots cycleBars h0
        exact ⟨found, hfound⟩
  obtain ⟨hop, sideY, width, row, hsources, -, -⟩ :=
    toDirectMatrixReadAccesses?_op_sources expression welcomeZeroFiles.maskRegisters
      control.directive hasSingleLineMask { control.context with cycle := (0 : Fin 4) }
      accesses lowered
  exact prepareParsedMatrixReadExprCycles_zeroShapeStatic expression accesses.precision
    sideY width row hop hsources control.directive hasSingleLineMask noForward nextSlots
    control.context nodup writes slots bars cyclesOk


/-! ## 4. The immediate-`.double` case and the disjunction, with arbitrary
`.lm1`-free companions -/

/-- **The immediate-`.double` writer makes the line input-independent even when
the companions are arbitrary.**  This is
`welcomePEMixedImmediateDouble_inputIndependent` without the `.noforward` /
`.wait` restriction on the rows around the writer. -/
theorem welcomePEPlainImmediateDouble_inputIndependent_arbitrary
    (expressions : List NormalizedExpr) (unrefuted : WelcomePEUnrefuted expressions)
    (before after : List ParsedExpr) (e : ParsedExpr)
    (split : (expressions.map NormalizedExpr.toParsed).filter
        parsedExprIsIntegerMatrixReadStageInput = before ++ e :: after)
    (eMem : e ∈ expressions.map NormalizedExpr.toParsed)
    (eWriter : Issue.Bank.lm1 ∈ (e.toIssueExpr 0).writeBanks)
    (notInBefore : e ∉ before) (notInAfter : e ∉ after)
    (immediate : ∃ payload sparse, e.op = .immediate payload sparse)
    (floatFreeRows : ∀ expression ∈ (expressions.map NormalizedExpr.toParsed).filter
      parsedExprIsSupportedFloatMAUProducer, WelcomeRowHasNoLm1Destination expression)
    (middleFree : WelcomePEMiddleStageLm1Free expressions)
    (matrixFreeRows : WelcomePEMatrixMAUStageLm1Free expressions)
    (l1FreeRows : WelcomePEL1StageLm1Free expressions) :
    WelcomePEInputIndependent expressions :=
  welcomePE_plainConstantWriter_inputIndependent expressions unrefuted before after e split
    eMem eWriter notInBefore notInAfter (Or.inr immediate) floatFreeRows middleFree
    matrixFreeRows l1FreeRows

/-- **The writer is either free of the immediate-`.double` case or the line is
input-independent**, with arbitrary `.lm1`-free companions.  Generalises
`welcomeMixed_notDouble_or_inputIndependent`. -/
theorem welcomeMixed_notDouble_or_inputIndependent_arbitrary
    (expressions : List NormalizedExpr) (unrefuted : WelcomePEUnrefuted expressions)
    (before after : List ParsedExpr) (e : ParsedExpr)
    (split : (expressions.map NormalizedExpr.toParsed).filter
        parsedExprIsIntegerMatrixReadStageInput = before ++ e :: after)
    (eMem : e ∈ expressions.map NormalizedExpr.toParsed)
    (eWriter : Issue.Bank.lm1 ∈ (e.toIssueExpr 0).writeBanks)
    (notInBefore : e ∉ before) (notInAfter : e ∉ after)
    (floatFreeRows : ∀ expression ∈ (expressions.map NormalizedExpr.toParsed).filter
      parsedExprIsSupportedFloatMAUProducer, WelcomeRowHasNoLm1Destination expression)
    (middleFree : WelcomePEMiddleStageLm1Free expressions)
    (matrixFreeRows : WelcomePEMatrixMAUStageLm1Free expressions)
    (l1FreeRows : WelcomePEL1StageLm1Free expressions) :
    (∀ (payload : BitVec 32) (sparse : Bool), e.op = .immediate payload sparse →
      ∀ destination ∈ e.destinations,
        ParsedOperand.directDestinationBankWidth? destination ≠
          some (PEMemory.Bank.lm1, PEMemory.Width.double)) ∨
    WelcomePEInputIndependent expressions := by
  by_cases notDouble : ∀ (payload : BitVec 32) (sparse : Bool),
      e.op = .immediate payload sparse → ∀ destination ∈ e.destinations,
        ParsedOperand.directDestinationBankWidth? destination ≠
          some (PEMemory.Bank.lm1, PEMemory.Width.double)
  · exact Or.inl notDouble
  · refine Or.inr ?_
    push Not at notDouble
    obtain ⟨payload, sparse, immediate, destination, member, equals⟩ := notDouble
    exact welcomePEPlainImmediateDouble_inputIndependent_arbitrary expressions unrefuted
      before after e split eMem eWriter notInBefore notInAfter ⟨payload, sparse, immediate⟩
      floatFreeRows middleFree matrixFreeRows l1FreeRows

/-! ## 5. The plain package: the disjunct, the split and the float condition
are all proved

The flag-free plain package of `WelcomeFlagFreePlain.lean` records, for its plain
`.lm1` writer, the split position, the float-MAU absence, the non-repetition of
the writer and the disjunction `notDouble ∨ WelcomePEInputIndependent`.
Section 4 proves the disjunction, and the split / non-repetition follow from
`welcomeLine_nodup` (`List.mem_iff_append` plus the filtered `Nodup`), so the
package below records only the split and the non-repetition; its consumer
derives the float half from the writer's uniqueness.  The package itself is then
a theorem (`welcomePEPlainWriterDataFor_doubleFree`). -/

/-- **The plain-writer split data.** -/
def WelcomePEPlainWriterDataForDoubleFree (expressions : List NormalizedExpr) : Prop :=
  ∀ (e : ParsedExpr),
    e ∈ expressions.map NormalizedExpr.toParsed →
      parsedExprIsPlainIntegerALU e = true →
      Issue.Bank.lm1 ∈ (e.toIssueExpr 0).writeBanks →
      ∃ before after : List ParsedExpr,
        (expressions.map NormalizedExpr.toParsed).filter
            parsedExprIsIntegerMatrixReadStageInput = before ++ e :: after ∧
          e ∉ before ∧ e ∉ after

/-- The global plain-writer split package. -/
def WelcomePEPlainWriterDataDoubleFree : Prop :=
  ∀ expressions, WelcomePEUnrefuted expressions →
    WelcomePEPlainWriterDataForDoubleFree expressions

/-- **The flag-free package implies the split package** (the conservative
direction: the `e ∉ before` / `e ∉ after` conjuncts are kept, the float and
disjunct conjuncts are dropped, and they are recovered by the consumer). -/
theorem welcomePEPlainWriterDataFor_doubleFree_of_flagFree
    (expressions : List NormalizedExpr) (data : WelcomePEPlainWriterDataForFlagFree expressions) :
    WelcomePEPlainWriterDataForDoubleFree expressions := by
  intro e eMem plain writer
  obtain ⟨before, after, split, notBefore, notAfter, _, _⟩ := data e eMem plain writer
  exact ⟨before, after, split, notBefore, notAfter⟩

/-- **The global conservative direction.** -/
theorem welcomePEPlainWriterData_doubleFree_of_flagFree
    (data : WelcomePEPlainWriterDataFlagFree) : WelcomePEPlainWriterDataDoubleFree :=
  fun expressions unrefuted =>
    welcomePEPlainWriterDataFor_doubleFree_of_flagFree expressions (data expressions unrefuted)

/-- **A stage-input row splits the integer-stage filter at itself.** -/
theorem welcomeStageFilter_split (expressions : List NormalizedExpr) (e : ParsedExpr)
    (member : e ∈ (expressions.map NormalizedExpr.toParsed).filter
      parsedExprIsIntegerMatrixReadStageInput) :
    ∃ before after : List ParsedExpr,
      (expressions.map NormalizedExpr.toParsed).filter
          parsedExprIsIntegerMatrixReadStageInput = before ++ e :: after :=
  List.mem_iff_append.mp member

/-- **An accepted line's row is not repeated before itself.**  The projected row
list is duplicate free (`welcomeLine_nodup`), and the filtered list inherits
that; a repeated `e` in the decomposition would be a duplicate. -/
theorem welcomeStageFilter_not_mem_before (expressions : List NormalizedExpr)
    (unrefuted : WelcomePEUnrefuted expressions) (before after : List ParsedExpr)
    (e : ParsedExpr)
    (split : (expressions.map NormalizedExpr.toParsed).filter
        parsedExprIsIntegerMatrixReadStageInput = before ++ e :: after) :
    e ∉ before := by
  have nodup := (welcomeLine_nodup _
    (welcomePEUnrefuted_legal expressions unrefuted)).filter
    parsedExprIsIntegerMatrixReadStageInput
  rw [split] at nodup
  obtain ⟨_, _, disjoint⟩ := List.nodup_append.mp nodup
  exact fun member => disjoint e member e (by simp) rfl

/-- **An accepted line's row is not repeated after itself.** -/
theorem welcomeStageFilter_not_mem_after (expressions : List NormalizedExpr)
    (unrefuted : WelcomePEUnrefuted expressions) (before after : List ParsedExpr)
    (e : ParsedExpr)
    (split : (expressions.map NormalizedExpr.toParsed).filter
        parsedExprIsIntegerMatrixReadStageInput = before ++ e :: after) :
    e ∉ after := by
  have nodup := (welcomeLine_nodup _
    (welcomePEUnrefuted_legal expressions unrefuted)).filter
    parsedExprIsIntegerMatrixReadStageInput
  rw [split] at nodup
  obtain ⟨_, nodupCons, _⟩ := List.nodup_append.mp nodup
  exact (List.nodup_cons.mp nodupCons).1

/-- **The plain-writer split data is derivable from acceptance.**  No part of
the package is assumed. -/
theorem welcomePEPlainWriterDataFor_doubleFree (expressions : List NormalizedExpr)
    (unrefuted : WelcomePEUnrefuted expressions) :
    WelcomePEPlainWriterDataForDoubleFree expressions := by
  intro e eMem plain _writer
  have member : e ∈ (expressions.map NormalizedExpr.toParsed).filter
      parsedExprIsIntegerMatrixReadStageInput :=
    List.mem_filter.mpr ⟨eMem, plain_stageInput e plain⟩
  obtain ⟨before, after, split⟩ := welcomeStageFilter_split expressions e member
  exact ⟨before, after, split,
    welcomeStageFilter_not_mem_before expressions unrefuted before after e split,
    welcomeStageFilter_not_mem_after expressions unrefuted before after e split⟩

/-- **The global plain-writer package is a theorem.** -/
theorem welcomePEPlainWriterDataDoubleFree : WelcomePEPlainWriterDataDoubleFree :=
  fun expressions unrefuted =>
    welcomePEPlainWriterDataFor_doubleFree expressions unrefuted

/-- **The immediate-double disjunct is derivable for every plain writer.** -/
theorem welcomePEPlainWriterDataFor_notDouble_or_inputIndependent
    (expressions : List NormalizedExpr) (unrefuted : WelcomePEUnrefuted expressions)
    (e : ParsedExpr) (eMem : e ∈ expressions.map NormalizedExpr.toParsed)
    (plain : parsedExprIsPlainIntegerALU e = true)
    (writer : Issue.Bank.lm1 ∈ (e.toIssueExpr 0).writeBanks) :
    (∀ (payload : BitVec 32) (sparse : Bool), e.op = .immediate payload sparse →
      ∀ destination ∈ e.destinations,
        ParsedOperand.directDestinationBankWidth? destination ≠
          some (PEMemory.Bank.lm1, PEMemory.Width.double)) ∨
    WelcomePEInputIndependent expressions := by
  obtain ⟨before, after, split, notBefore, notAfter⟩ :=
    (welcomePEPlainWriterDataFor_doubleFree expressions unrefuted) e eMem plain writer
  obtain ⟨-, -, mslFalse, reluFalse, blockFalse, -, -, matrixMAUFalse, -, l1False, -⟩ :=
    parsedExprIsPlainIntegerALU_facts e plain
  have rows := welcomeLm1Writer_rows expressions unrefuted e eMem writer
  exact welcomeMixed_notDouble_or_inputIndependent_arbitrary expressions unrefuted before after
    e split eMem writer notBefore notAfter
    (floatFilter_lm1Free_of_rows expressions e rows
      (parsedExprIsPlainIntegerALU_notFloatMAU e plain))
    (welcomePEMiddleStageLm1Free_of_rows expressions e rows mslFalse reluFalse blockFalse)
    (welcomePEMatrixMAUStageLm1Free_of_rows expressions e rows matrixMAUFalse)
    (welcomePEL1StageLm1Free_of_rows expressions e rows l1False)

/-- **The plain-writer line shape from the split package.** -/
theorem welcomePEWriteShape_of_plainWriter_data_doubleFree
    (expressions : List NormalizedExpr)
    (data : WelcomePEPlainWriterDataForDoubleFree expressions)
    (unrefuted : WelcomePEUnrefuted expressions) (e : ParsedExpr)
    (eMem : e ∈ expressions.map NormalizedExpr.toParsed)
    (plain : parsedExprIsPlainIntegerALU e = true)
    (writer : Issue.Bank.lm1 ∈ (e.toIssueExpr 0).writeBanks) :
    WelcomePEWriteShape expressions := by
  obtain ⟨before, after, split, notBefore, notAfter⟩ := data e eMem plain writer
  obtain ⟨-, -, mslFalse, reluFalse, blockFalse, -, -, matrixMAUFalse, -, l1False, -⟩ :=
    parsedExprIsPlainIntegerALU_facts e plain
  have rows := welcomeLm1Writer_rows expressions unrefuted e eMem writer
  have floatFreeRows := floatFilter_lm1Free_of_rows expressions e rows
    (parsedExprIsPlainIntegerALU_notFloatMAU e plain)
  have middleFree :=
    welcomePEMiddleStageLm1Free_of_rows expressions e rows mslFalse reluFalse blockFalse
  have matrixFreeRows := welcomePEMatrixMAUStageLm1Free_of_rows expressions e rows matrixMAUFalse
  have l1FreeRows := welcomePEL1StageLm1Free_of_rows expressions e rows l1False
  by_cases notDouble : ∀ (payload : BitVec 32) (sparse : Bool),
      e.op = .immediate payload sparse → ∀ destination ∈ e.destinations,
        ParsedOperand.directDestinationBankWidth? destination ≠
          some (PEMemory.Bank.lm1, PEMemory.Width.double)
  · exact welcomePEWriteShape_of_plainWriter_arbitrary_floatRows expressions unrefuted before
      after e split eMem writer notBefore notAfter notDouble plain floatFreeRows middleFree
      matrixFreeRows l1FreeRows
  · refine Or.inr (Or.inr ?_)
    push Not at notDouble
    obtain ⟨payload, sparse, immediate, destination, member, equals⟩ := notDouble
    exact welcomePE_plainConstantWriter_inputIndependent expressions unrefuted before after
      e split eMem writer notBefore notAfter (Or.inr ⟨payload, sparse, immediate⟩)
      floatFreeRows middleFree matrixFreeRows l1FreeRows

/-- **The plain-writer line shape, with no package hypothesis.** -/
theorem welcomePEWriteShape_of_plainWriter_closed
    (expressions : List NormalizedExpr) (unrefuted : WelcomePEUnrefuted expressions)
    (e : ParsedExpr) (eMem : e ∈ expressions.map NormalizedExpr.toParsed)
    (plain : parsedExprIsPlainIntegerALU e = true)
    (writer : Issue.Bank.lm1 ∈ (e.toIssueExpr 0).writeBanks) :
    WelcomePEWriteShape expressions :=
  welcomePEWriteShape_of_plainWriter_data_doubleFree expressions
    (welcomePEPlainWriterDataFor_doubleFree expressions unrefuted)
    unrefuted e eMem plain writer

/-! ## 6. The `.matrixRead` package: the row-local data and the split are proved

`WelcomePEMatrixReadWriterDataForSlotFree` records, for a `.matrixRead` `.lm1`
writer, the split position, the non-repetition, the float-MAU absence **and**
five row-local data: `e.op = .matrixRead precision`,
`e.sources = [.matrix sideY width (some row)]`, and the static width of the
`.lm1` destinations.  The first two follow from a successful lowering
(`toDirectMatrixReadAccesses?_op_sources`) and the third from the writer's
unique `.lm1` destination (`lm1StaticWidth_spec`), which is
`welcomeLm1Writer_nodup`; the float half follows from the writer's uniqueness
(`floatFilter_lm1Free_of_rows`).  The package below keeps only the split and the
non-repetition, both derivable from acceptance, so it too is a theorem. -/

/-- **The `.matrixRead`-writer split data.** -/
def WelcomePEMatrixReadWriterDataForSplit (expressions : List NormalizedExpr) : Prop :=
  ∀ (e : ParsedExpr),
    e ∈ expressions.map NormalizedExpr.toParsed →
      parsedExprIsMatrixReadProducer e = true →
      Issue.Bank.lm1 ∈ (e.toIssueExpr 0).writeBanks →
      ∃ before after : List ParsedExpr,
        (expressions.map NormalizedExpr.toParsed).filter
            parsedExprIsIntegerMatrixReadStageInput = before ++ e :: after ∧
          e ∉ before ∧ e ∉ after

/-- The global `.matrixRead` split package. -/
def WelcomePEMatrixReadWriterDataSplit : Prop :=
  ∀ expressions, WelcomePEUnrefuted expressions →
    WelcomePEMatrixReadWriterDataForSplit expressions

/-- **The slot-free `.matrixRead` package implies the split package** (the
conservative direction: the row-local lowering data and the float conjunct are
dropped; the consumer recovers them). -/
theorem welcomePEMatrixReadWriterDataFor_split_of_slotFree
    (expressions : List NormalizedExpr) (data : WelcomePEMatrixReadWriterDataForSlotFree expressions) :
    WelcomePEMatrixReadWriterDataForSplit expressions := by
  intro e eMem read writer
  obtain ⟨before, after, precision, sideY, width, row, staticW, split, notBefore, notAfter,
    op, sources, staticWidth, floatEmpty⟩ := data e eMem read writer
  exact ⟨before, after, split, notBefore, notAfter⟩

/-- **The global conservative direction.** -/
theorem welcomePEMatrixReadWriterData_split_of_slotFree
    (data : WelcomePEMatrixReadWriterDataSlotFree) : WelcomePEMatrixReadWriterDataSplit :=
  fun expressions unrefuted =>
    welcomePEMatrixReadWriterDataFor_split_of_slotFree expressions (data expressions unrefuted)

/-- **A `.matrixRead` row is an integer-stage input.** -/
theorem welcomeMatrixRead_stageInput (expression : ParsedExpr)
    (read : parsedExprIsMatrixReadProducer expression = true) :
    parsedExprIsIntegerMatrixReadStageInput expression = true := by
  obtain ⟨op, sources, destinations, flush, text⟩ := expression
  cases op <;>
    simp_all [parsedExprIsMatrixReadProducer, parsedExprIsIntegerMatrixReadStageInput,
      parsedExprWaitTag?, parsedExprIsL2BMProducer, parsedExprIsMatrixWriteProducer,
      parsedExprIsL1MwriteProducer, parsedExprIsL1GatherProducer,
      parsedExprIsL1ReduceProducer, parsedExprIsL1ToPEProducer, parsedExprIsMatrixMAUProducer,
      parsedExprIsSupportedFloatMAUProducer, parsedExprIsMslMsrProducer,
      parsedExprIsBlockFloatProducer, parsedExprIsFloatReluProducer]

/-- **The `.matrixRead` split data is derivable from acceptance.** -/
theorem welcomePEMatrixReadWriterDataFor_split (expressions : List NormalizedExpr)
    (unrefuted : WelcomePEUnrefuted expressions) :
    WelcomePEMatrixReadWriterDataForSplit expressions := by
  intro e eMem read _writer
  have member : e ∈ (expressions.map NormalizedExpr.toParsed).filter
      parsedExprIsIntegerMatrixReadStageInput :=
    List.mem_filter.mpr ⟨eMem, welcomeMatrixRead_stageInput e read⟩
  obtain ⟨before, after, split⟩ := welcomeStageFilter_split expressions e member
  exact ⟨before, after, split,
    welcomeStageFilter_not_mem_before expressions unrefuted before after e split,
    welcomeStageFilter_not_mem_after expressions unrefuted before after e split⟩

/-- **The global `.matrixRead` package is a theorem.** -/
theorem welcomePEMatrixReadWriterDataSplit : WelcomePEMatrixReadWriterDataSplit :=
  fun expressions unrefuted =>
    welcomePEMatrixReadWriterDataFor_split expressions unrefuted

/-- **The `.matrixRead`-writer line shape from the split package.**  The
operation, the source coordinates and the static width are not package data:
they come from the row step (the lowering and the writer's unique `.lm1`
destination) inside the proof. -/
theorem welcomePEWriteShape_of_matrixReadWriter_data_split
    (expressions : List NormalizedExpr)
    (data : WelcomePEMatrixReadWriterDataForSplit expressions)
    (unrefuted : WelcomePEUnrefuted expressions) (e : ParsedExpr)
    (eMem : e ∈ expressions.map NormalizedExpr.toParsed)
    (read : parsedExprIsMatrixReadProducer e = true)
    (writer : Issue.Bank.lm1 ∈ (e.toIssueExpr 0).writeBanks) :
    WelcomePEWriteShape expressions := by
  obtain ⟨before, after, split, notBefore, notAfter⟩ := data e eMem read writer
  obtain ⟨precision, op⟩ : ∃ p : ParsedPrecision, e.op = .matrixRead p := by
    obtain ⟨operator, sources, destinations, flush, text⟩ := e
    cases operator <;> simp_all [parsedExprIsMatrixReadProducer]
  obtain ⟨mslFalse, reluFalse, blockFalse, matrixMAUFalse, l1False⟩ :=
    matrixRead_parsedExpr_predicates e precision op
  have rows := welcomeLm1Writer_rows expressions unrefuted e eMem writer
  have freeBefore : ∀ expression ∈ before, WelcomeRowHasNoLm1Destination expression := by
    intro expression member
    apply rows expression
    · have inFilter : expression ∈ (expressions.map NormalizedExpr.toParsed).filter
          parsedExprIsIntegerMatrixReadStageInput := by
        rw [split]
        exact List.mem_append_left _ member
      exact (List.mem_filter.mp inFilter).1
    · intro same
      exact notBefore (same ▸ member)
  have freeAfter : ∀ expression ∈ after, WelcomeRowHasNoLm1Destination expression := by
    intro expression member
    apply rows expression
    · have inFilter : expression ∈ (expressions.map NormalizedExpr.toParsed).filter
          parsedExprIsIntegerMatrixReadStageInput := by
        rw [split]
        exact List.mem_append_right _ (List.mem_cons_of_mem _ member)
      exact (List.mem_filter.mp inFilter).1
    · intro same
      exact notAfter (same ▸ member)
  refine welcomePEWriteShape_of_floatRows_intShape expressions
    (floatFilter_lm1Free_of_rows expressions e rows (matrixRead_notFloatMAU e precision op))
    (welcomePEMiddleStageLm1Free_of_rows expressions e rows mslFalse reluFalse blockFalse)
    (welcomePEMatrixMAUStageLm1Free_of_rows expressions e rows matrixMAUFalse)
    (welcomePEL1StageLm1Free_of_rows expressions e rows l1False) ?_
  intro intWrites intSlots intBars intPrep
  have splitWalk : (welcomePEWalkFilter expressions).filter
      parsedExprIsIntegerMatrixReadStageInput = before ++ e :: after := by
    rw [welcomePEWalkFilter_integer]
    exact split
  obtain ⟨beforeWrites, prefixSlots, beforeBars, rowWrites, rowSlots, rowBars, afterWrites,
    afterSlots, afterBars, rowPrep, intWritesEq, beforeFree, afterFree⟩ :=
    welcomeIntegerPrep_split (welcomeInitialState welcomeZeroWords)
      (welcomePEWalkFilter expressions) before after e splitWalk freeBefore freeAfter
      intWrites intSlots intBars intPrep
  rw [intWritesEq]
  exact lm1WritesShape_of_append_split (leading := beforeWrites) (middle := rowWrites)
    (trailing := afterWrites) rfl beforeFree
    ((prepareParsedMatrixRead_row_shape_of_read e read prefixSlots welcomeZeroControl
      _ _ false (welcomeLm1Writer_nodup expressions unrefuted e eMem) rowWrites rowSlots
      rowBars rowPrep)) afterFree

/-- **The `.matrixRead`-writer line shape, with no package hypothesis.** -/
theorem welcomePEWriteShape_of_matrixReadWriter_closed
    (expressions : List NormalizedExpr) (unrefuted : WelcomePEUnrefuted expressions)
    (e : ParsedExpr) (eMem : e ∈ expressions.map NormalizedExpr.toParsed)
    (read : parsedExprIsMatrixReadProducer e = true)
    (writer : Issue.Bank.lm1 ∈ (e.toIssueExpr 0).writeBanks) :
    WelcomePEWriteShape expressions :=
  welcomePEWriteShape_of_matrixReadWriter_data_split expressions
    (welcomePEMatrixReadWriterDataFor_split expressions unrefuted)
    unrefuted e eMem read writer

/-! ## 7. The assembly with the two shrunk packages

The dispatch of `WelcomeWriterPackages.lean` §7 uses the flag-free plain package
and the slot-free `.matrixRead` package.  With §5 and §6 both are replaced by
their shrunk forms; the `.l1bm` component is unchanged. -/

/-- **The residual bundle with the plain and `.matrixRead` conjuncts proved
away.**  Only the split positions, the float-MAU absence, and the `.l1bm`
row-local lowering shape remain as data. -/
def WelcomePEPlainReadWriterData : Prop :=
  WelcomePEPlainWriterDataDoubleFree ∧ WelcomePEMatrixReadWriterDataSplit ∧
    WelcomePEL1BMWriterDataNoSingleton

/-- **`WelcomePELm1WriteShapeObligation` from the three shrunk packages.** -/
theorem welcomePELm1WriteShapeObligation_of_plainReadSplit
    (data : WelcomePEPlainReadWriterData) : WelcomePELm1WriteShapeObligation := by
  obtain ⟨plain, read, l1⟩ := data
  intro expressions unrefuted
  by_cases hasWriter : ∃ e ∈ expressions.map NormalizedExpr.toParsed,
      Issue.Bank.lm1 ∈ (e.toIssueExpr 0).writeBanks
  · obtain ⟨e, eMem, eWriter⟩ := hasWriter
    have supported := List.all_eq_true.mp unrefuted.1.2.2.2 e eMem
    have notUnsupported : parsedExprIsUnsupportedRustAlu e = false := by
      simpa using (List.any_eq_false.mp unrefuted.1.2.2.1) e eMem
    rcases supportedProducer_partition e supported with
      isPlain | isFamily | isSpecial | isInert | isUnsupported
    · exact welcomePEWriteShape_of_plainWriter_data_doubleFree expressions
        (plain expressions unrefuted) unrefuted e eMem isPlain eWriter
    · rcases parsedExprIsFamilyProducer_cases e isFamily with
        readKind | mauKind | floatKind | writeKind | toPEKind | l2Kind
      · exact welcomePEWriteShape_of_matrixReadWriter_data_split expressions
          (read expressions unrefuted) unrefuted e eMem readKind eWriter
      · exact welcomePEWriteShape_of_matrixMAUWriter expressions unrefuted e eMem mauKind eWriter
      · exact welcomePEWriteShape_of_floatMAUWriter expressions unrefuted e eMem floatKind eWriter
      · have hphantom : ∀ x ∈ expressions.map NormalizedExpr.toParsed,
            Issue.Bank.lm1 ∈ (x.toIssueExpr 0).writeBanks → welcomePhantomWriterKind x := by
          intro x xMem xWriter
          have same : x = e :=
            welcomeLm1Writer_eq_of_two expressions unrefuted xMem eMem xWriter eWriter
          rw [same]
          exact Or.inr (Or.inr (Or.inr (Or.inl writeKind)))
        exact welcomePEWriteShape_of_freeStageCommit expressions
          (welcomePELm1PhantomWriterProvenance expressions unrefuted hphantom)
      · exact welcomePEWriteShape_of_l1bmWriter_dataNoSingleton expressions
          (l1 expressions unrefuted) unrefuted e eMem toPEKind eWriter
      · have hphantom : ∀ x ∈ expressions.map NormalizedExpr.toParsed,
            Issue.Bank.lm1 ∈ (x.toIssueExpr 0).writeBanks → welcomePhantomWriterKind x := by
          intro x xMem xWriter
          have same : x = e :=
            welcomeLm1Writer_eq_of_two expressions unrefuted xMem eMem xWriter eWriter
          rw [same]
          exact Or.inr (Or.inr (Or.inr (Or.inr l2Kind)))
        exact welcomePEWriteShape_of_freeStageCommit expressions
          (welcomePELm1PhantomWriterProvenance expressions unrefuted hphantom)
    · exact welcomePESpecialALUWriterShapeObligation expressions unrefuted
        ⟨e, eMem, eWriter, isSpecial⟩
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
      exact welcomePEWriteShape_of_freeStageCommit expressions
        (welcomePELm1PhantomWriterProvenance expressions unrefuted hphantom)
    · rw [notUnsupported] at isUnsupported
      cases isUnsupported
  · have hphantom : ∀ x ∈ expressions.map NormalizedExpr.toParsed,
        Issue.Bank.lm1 ∈ (x.toIssueExpr 0).writeBanks → welcomePhantomWriterKind x := by
      intro x xMem xWriter
      exact absurd ⟨x, xMem, xWriter⟩ hasWriter
    exact welcomePEWriteShape_of_freeStageCommit expressions
      (welcomePELm1PhantomWriterProvenance expressions unrefuted hphantom)

/-- **The conservative direction at the bundle level.**  The round-50
three-package bundle (`WelcomePEWriterKindDataResidualsThree`, whose `.l1bm`
component is refutable) implies the bundle of this module: the plain and
`.matrixRead` conjuncts are weakened, the `.l1bm` one is unchanged. -/
theorem welcomePEPlainReadWriterData_of_residualsThree
    (residuals : WelcomePEWriterKindDataResidualsThree) : WelcomePEPlainReadWriterData :=
  ⟨welcomePEPlainWriterData_doubleFree_of_flagFree residuals.1,
    welcomePEMatrixReadWriterData_split_of_slotFree residuals.2.1, residuals.2.2⟩


/-- **`WelcomePELm1WriteShapeObligation` from the `.l1bm` package alone.**  The
plain and `.matrixRead` packages are theorems of this module
(`welcomePEPlainWriterDataDoubleFree`, `welcomePEMatrixReadWriterDataSplit`), so
the only remaining data package is the `.l1bm` row-local lowering shape. -/
theorem welcomePELm1WriteShapeObligation_of_l1NoSingleton
    (l1 : WelcomePEL1BMWriterDataNoSingleton) : WelcomePELm1WriteShapeObligation :=
  welcomePELm1WriteShapeObligation_of_plainReadSplit
    ⟨welcomePEPlainWriterDataDoubleFree, welcomePEMatrixReadWriterDataSplit, l1⟩


end ProofsLean.MNCore
