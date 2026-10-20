import ProofsLean.WelcomeAssemblyFinal

/-! # Writer-kind data packages with the avoidable restrictions removed

Round 49 left four per-line writer-kind data packages as hypotheses in
`WelcomeAssemblyFinal.lean`.  This module weakens two of them and proves one of
the weakenings outright:

* **`WelcomePEFloatMAUWriterData`** required *every* integer-stage row of a line
  with a float-MAU `.lm1` writer to be `.noforward`.  That is not needed: the
  integer stage splits its file update as `intWrites ++ floatWrites`, and
  `welcomeIntegerPrep_lm1_free` makes `intWrites` `.lm1`-free as soon as the
  integer-stage rows carry no `.lm1` destination operand.  The latter follows
  from the issue checker's `.lm1`-writer uniqueness (`welcomeLm1Writer_unique`
  through the row bridge `welcomeLm1Writer_rows`).  The float row's own shape
  is needed at the *post-integer* register file, so the row-shape theorem is
  first generalised from `welcomeZeroFiles` to an arbitrary current file
  (`executeParsedFloatMAUsAtPE_zeroShape_current`); the datapath fact
  `WelcomePEFloatMAUCycleCopy` only constrains the *read* file, which is still
  `welcomeZeroFiles`.  The resulting package
  `WelcomePEFloatMAUWriterDataIntRows` is proved **unconditionally**.
* **`WelcomePEL1BMWriterData`** required the L1BM-to-PE filter to be `[e]`.
  That singleton is not a consequence of acceptance: `groupsUnique` only
  compares rows of the same issue group, and a broadcast row whose operands
  contain a `.l1bm … none` turnaround operand has group `.l1bmTurnaround`
  while an addressed one has group `.l1bm`.  It is also not needed: the
  executor itself rejects two L1BM-to-PE rows
  (`executeParsedL1ToPEProducers_multiple_fail`), so on a *successful* step the
  filter is a singleton, and on a failing step the write shape is vacuous.
  The weaker package `WelcomePEL1BMWriterDataNoSingleton` drops the singleton
  (and the empty-float-filter conjunct as well, replacing it by the row-local
  `.lm1`-freeness supplied by writer uniqueness).

Both weakenings come with their **conservative direction**: the round-49
packages imply the new ones, so no line that the old packages covered is lost.
The weakened float-MAU package is in fact proved **unconditionally**
(`welcomePEFloatMAUWriterData_intRows`), and the float-MAU writer case of the
line shape needs no hypothesis (`welcomePEWriteShape_of_floatMAUWriter`).

The `.l1bm` singleton is not merely unproven but **false** for the round-49
package: §6 exhibits an unrefuted two-row line with two L1BM-to-PE rows and
proves `¬ WelcomePEL1BMWriterData` (`l1ToPESecondRow_oldPackage_false`).  The
weakened package keeps only the row-local lowering shape, and the shape theorem
recovers the singleton from the L1BM-to-PE stage's success equation (§5).

The remaining row-local lowering shape is **also not derivable from
acceptance**: §6.1 exhibits an accepted unrefuted broadcast writer with two
`.mem` destinations and proves `¬ WelcomePEL1BMWriterDataNoSingleton`
(`l1ToPETwoDestination_weakPackage_false`).  Closing that case needs a
multi-destination form of `executeParsedL1ToPEProducer_mem_lm1_shape`; the
weakened package is strictly weaker than the round-49 one (conservative
direction proved) but it is not an unconditional statement.

The final section re-runs the assembly with the two weakened packages: the
float-MAU case needs no hypothesis at all, and the `.l1bm` case needs the
row-local lowering shape (single masked `.mem .lm1` destination of static
width).  The resulting conditional theorems are stated in terms of the
remaining plain, `.matrixRead` and weakened `.l1bm` packages
(`welcomePELm1WriteShapeObligation_of_plainReadL1`,
`welcomeLowerBound_two_of_plainReadL1` and `welcomeAnswer_optimal_of_plainReadL1`);
they do not cover multi-destination L1BM writers.

No `sorry`, no `admit`, no `native_decide`, no new axioms, and no existing
module is edited.  No unconditional `LowerBound 2` and no unconditional
`Optimal` is claimed: the last two theorems take the three packages as
hypotheses.
-/

namespace ProofsLean.MNCore

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open Issue
open PEMemory

/-! ## 1. The float-MAU row shape at an arbitrary current register file

`executeParsedFloatMAUsAtPE` reads through `readState` and commits onto
`currentFiles`; the zero-state row shape of `WelcomeHalfMAUCopy.lean` fixes both
to `welcomeZeroFiles`.  A float-MAU writer in a line with integer-stage
companions runs after their commit, so only the *read* file is zero while the
current file is arbitrary.  The proof of `executeParsedFloatMAUCyclesAtPE_shape`
already quantifies the current file freely (its `zeroRead` hypothesis is about
`readFiles`), so the zero-state proofs replay verbatim with the initial
accumulator replaced. -/

/-- **The float-MAU row: static width, copies and count at an arbitrary current
file.**  The read file is the all-zero one and the forwarding slots are poison. -/
theorem executeParsedFloatMAUsAtPE_zeroWidthCount_current
    (expression : ParsedExpr) (context : ParsedIntegerContext) (directive : ParsedMaskDirective)
    (hasSingleLineMask : Bool) (w : PEMemory.Width) (cycleCopy : WelcomePEFloatMAUCycleCopy)
    (widths : Lm1DestWidths w expression.destinations)
    (count : Lm1DestCount expression.destinations)
    (budget : (expression.destinations.filter ParsedOperand.isLm1MemoryDestination).length ≤ 1)
    (currentFiles : IntegerRegisterFiles)
    (nextFiles : IntegerRegisterFiles) (nextBar0 nextBar1 : BitVec 12)
    (nextOutputs : Fin 4 → IntegerALU.Bus) (hasMAUProducer : Bool)
    (executed : executeParsedFloatMAUsAtPE welcomeZeroFiles currentFiles welcomeZeroSlots context
      [expression] directive hasSingleLineMask =
      .ok (nextFiles, nextBar0, nextBar1, nextOutputs, hasMAUProducer)) :
    ∃ writes, nextFiles = commitParsedMaskedWrites currentFiles writes ∧
      Lm1WidthFacts w writes ∧ Lm1CopyFacts writes ∧
      (writes.filter PreparedParsedMaskedWrite.isLm1Write).length ≤ 4 := by
  rw [executeParsedFloatMAUsAtPE.eq_1] at executed
  by_cases supported : parsedExprIsSupportedFloatMAUProducer expression = true
  · rw [show List.filter parsedExprIsSupportedFloatMAUProducer [expression] = [expression] by
      simp [supported]] at executed
    split at executed
    · simp at executed
    · simp at executed
    · rename_i files bar0 bar1 outputs ran
      rw [executeParsedFloatMAUsAtPE.run] at ran
      cases cycleStep : executeParsedFloatMAUCyclesAtPE welcomeZeroFiles welcomeZeroSlots expression
          context directive hasSingleLineMask [0, 1, 2, 3] currentFiles context.bar0 context.bar1
          (fun _ => (⟨0, 0⟩ : IntegerALU.Bus)) with
      | failure => rw [cycleStep] at ran; simp at ran
      | unknown => rw [cycleStep] at ran; simp at ran
      | ok result =>
        obtain ⟨middleFiles, middleBar0, middleBar1, middleOutputs⟩ := result
        rw [cycleStep] at ran
        dsimp only at ran
        rw [executeParsedFloatMAUsAtPE.run.eq_1] at ran
        obtain ⟨rfl, rfl, rfl, rfl⟩ := StepResult.ok.inj ran
        obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := StepResult.ok.inj executed
        obtain ⟨writes, commit, widthFacts, copyFacts, countLe⟩ :=
          executeParsedFloatMAUCyclesAtPE_shape welcomeZeroFiles welcomeZeroSlots expression context
            directive hasSingleLineMask w cycleCopy rfl
            (fun unit c => welcomeZeroSlots_poison unit c) widths count budget
            [0, 1, 2, 3] currentFiles context.bar0 context.bar1 (fun _ => ⟨0, 0⟩)
            nextFiles nextBar0 nextBar1 nextOutputs cycleStep
        exact ⟨writes, commit, widthFacts, copyFacts, by simpa using countLe⟩
  · rw [show List.filter parsedExprIsSupportedFloatMAUProducer [expression] = [] by
      simp [supported]] at executed
    split at executed
    · simp at executed
    · simp at executed
    · rename_i files bar0 bar1 outputs ran
      rw [executeParsedFloatMAUsAtPE.run.eq_1] at ran
      obtain ⟨rfl, rfl, rfl, rfl⟩ := StepResult.ok.inj ran
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := StepResult.ok.inj executed
      exact ⟨[], by simp [commitParsedMaskedWrites], lm1WidthFacts_nil w, lm1CopyFacts_nil,
        by simp⟩

/-- **The float-MAU row shape at an arbitrary current file.**  Same statement as
`executeParsedFloatMAUsAtPE_zeroShape_static_unconditional` with the commit base
file generalised from `welcomeZeroFiles` to `currentFiles`. -/
theorem executeParsedFloatMAUsAtPE_zeroShape_current
    (expression : ParsedExpr) (context : ParsedIntegerContext) (directive : ParsedMaskDirective)
    (hasSingleLineMask : Bool)
    (nodup : (expression.toIssueExpr 0).writeBanks.Nodup)
    (currentFiles : IntegerRegisterFiles)
    (nextFiles : IntegerRegisterFiles) (nextBar0 nextBar1 : BitVec 12)
    (nextOutputs : Fin 4 → IntegerALU.Bus) (hasMAUProducer : Bool)
    (executed : executeParsedFloatMAUsAtPE welcomeZeroFiles currentFiles welcomeZeroSlots context
      [expression] directive hasSingleLineMask =
      .ok (nextFiles, nextBar0, nextBar1, nextOutputs, hasMAUProducer)) :
    ∃ writes, nextFiles = commitParsedMaskedWrites currentFiles writes ∧
      (Lm1WritesDoubleCopy writes ∨ Lm1WritesNarrow writes) := by
  let w := (lm1StaticWidth expression).getD PEMemory.Width.word
  obtain ⟨writes, commit, widthFacts, copyFacts, countLe⟩ :=
    executeParsedFloatMAUsAtPE_zeroWidthCount_current expression context directive
      hasSingleLineMask w welcomePEFloatMAUCycleCopy_holds
      (lm1StaticWidth_spec expression nodup) (lm1DestCount_any expression.destinations)
      (lm1Destinations_count_le_one expression 0 nodup) currentFiles nextFiles nextBar0 nextBar1
      nextOutputs hasMAUProducer executed
  refine ⟨writes, commit, ?_⟩
  by_cases isDouble : w = PEMemory.Width.double
  · left
    have facts : Lm1WriteFacts w writes := lm1WriteFacts_of_parts w writes widthFacts copyFacts
    rw [isDouble] at facts
    exact lm1WriteFacts_doubleCopy writes facts
  · exact Or.inr (lm1WidthFacts_narrow writes w widthFacts isDouble countLe)

/-! ## 2. The float-MAU writer inside the integer stage

`executeIntegerProducerLineAtPECore` runs the four-cycle integer/matrix-read
preparation and then the float-MAU stage on the whole line.  When a single
float-MAU row `e` is the line's `.lm1` writer, the integer companion rows carry
no `.lm1` destination (writer uniqueness), so the four-cycle list is `.lm1`-free
and the float list carries the writer's shape.  The final list is therefore
`intWrites ++ floatWrites` with a `.lm1`-free prefix. -/

/-- **The float-MAU writer at one PE, with `.lm1`-free integer companions.**
This is `executeIntegerProducerLineAtPECore_floatWriter` with the
all-`.noforward` integer-stage hypothesis replaced by the row-local statement
that the integer-stage rows carry no `.lm1` destination operand. -/
theorem executeIntegerProducerLineAtPECore_floatWriter_intRows
    (expressions : List ParsedExpr) (e : ParsedExpr) (pe : PEId) (next : State)
    (float : parsedExprIsSupportedFloatMAUProducer e = true)
    (nodup : (e.toIssueExpr 0).writeBanks.Nodup)
    (floatFilter : expressions.filter parsedExprIsSupportedFloatMAUProducer = [e])
    (intFree : ∀ x ∈ expressions.filter parsedExprIsIntegerMatrixReadStageInput,
      WelcomeRowHasNoLm1Destination x)
    (executed : executeIntegerProducerLineAtPECore expressions
      (welcomeInitialState welcomeZeroWords) pe = .ok next) :
    ∃ writes, next.peRegisters pe =
      commitParsedMaskedWrites ((welcomeInitialState welcomeZeroWords).peRegisters pe) writes ∧
      (Lm1WritesDoubleCopy writes ∨ Lm1WritesNarrow writes) := by
  rw [executeIntegerProducerLineAtPECore.eq_1] at executed
  dsimp only at executed
  split at executed
  · simp at executed
  · simp at executed
  · rename_i registers integerSlots barUpdates fourCycle
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
        unfold parsedIntegerMatrixReadLineFourCycleStep at fourCycle
        split at fourCycle
        · simp at fourCycle
        · simp at fourCycle
        · rename_i intWrites preparedSlots preparedBars prepared
          simp only [StepResult.ok.injEq, Prod.mk.injEq] at fourCycle
          obtain ⟨commitRegsEq, -, -⟩ := fourCycle
          have intWritesFree : Lm1FreePreparedWrites intWrites :=
            welcomeIntegerPrep_lm1_free (welcomeInitialState welcomeZeroWords) pe expressions
              intWrites preparedSlots preparedBars prepared intFree
          have slotsEq := welcomeFamily_initial_slots pe
          have readEq : (welcomeInitialState welcomeZeroWords).peRegisters pe = welcomeZeroFiles := rfl
          have floatCanonical : executeParsedFloatMAUsAtPE welcomeZeroFiles registers
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
          obtain ⟨floatWrites, floatCommitEq, floatShape⟩ :=
            executeParsedFloatMAUsAtPE_zeroShape_current e _ _ _ nodup registers
              registersWithFloat floatBar0 floatBar1 floatOutputs hasMAUProducer floatCanonical
          refine ⟨intWrites ++ floatWrites, ?_, ?_⟩
          · show (if pe = pe then registersWithFloat
              else (welcomeInitialState welcomeZeroWords).peRegisters pe) =
              commitParsedMaskedWrites ((welcomeInitialState welcomeZeroWords).peRegisters pe)
                (intWrites ++ floatWrites)
            rw [ite_eq_left rfl, floatCommitEq, ← commitRegsEq,
              ← commitParsedMaskedWrites_append]
          · exact lm1WritesShape_append_of_only_right intWrites floatWrites intWritesFree
              floatShape

/-- **The float-MAU writer over the whole PE walk, with `.lm1`-free integer
companions.**  At PE 0 (the head of `List.finRange 4096`) the core commits the
writer's list; the tail never revisits PE 0. -/
theorem executeIntegerProducerLineAtPEs_floatWriter_intRows
    (expressions : List ParsedExpr) (e : ParsedExpr) (next : State)
    (float : parsedExprIsSupportedFloatMAUProducer e = true)
    (nodup : (e.toIssueExpr 0).writeBanks.Nodup)
    (floatFilter : expressions.filter parsedExprIsSupportedFloatMAUProducer = [e])
    (intFree : ∀ x ∈ expressions.filter parsedExprIsIntegerMatrixReadStageInput,
      WelcomeRowHasNoLm1Destination x)
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
      executeIntegerProducerLineAtPECore_floatWriter_intRows expressions e welcomePE nextPEs
        float nodup floatFilter intFree coreExecuted
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

/-- **The float-MAU-writer dispatch, with `.lm1`-free integer companions.**  The
integer stage's list is `intWrites ++ floatWrites` with `intWrites` `.lm1`-free,
so the six-list shape follows from the float writer's own row shape. -/
theorem welcomePEWriteShape_of_floatMAUWriter_dispatch_intRows
    (expressions : List NormalizedExpr)
    (e : ParsedExpr)
    (float : parsedExprIsSupportedFloatMAUProducer e = true)
    (nodup : (e.toIssueExpr 0).writeBanks.Nodup)
    (floatFilter : (expressions.map NormalizedExpr.toParsed).filter
      parsedExprIsSupportedFloatMAUProducer = [e])
    (intFree : ∀ expression ∈ (expressions.map NormalizedExpr.toParsed).filter
      parsedExprIsIntegerMatrixReadStageInput, WelcomeRowHasNoLm1Destination expression)
    (middleFree : WelcomePEMiddleStageLm1Free expressions)
    (matrixFreeRows : WelcomePEMatrixMAUStageLm1Free expressions)
    (l1FreeRows : WelcomePEL1StageLm1Free expressions) :
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
  have floatFilterWalk : (welcomePEWalkFilter expressions).filter
      parsedExprIsSupportedFloatMAUProducer = [e] := by
    rw [welcomePEWalkFilter_float]
    exact floatFilter
  have intFreeWalk : ∀ expression ∈ (welcomePEWalkFilter expressions).filter
      parsedExprIsIntegerMatrixReadStageInput, WelcomeRowHasNoLm1Destination expression := by
    intro expression member
    exact intFree expression (by rw [welcomePEWalkFilter_integer] at member; exact member)
  obtain ⟨intWrites, intCommit, intShape⟩ :=
    executeIntegerProducerLineAtPEs_floatWriter_intRows (welcomePEWalkFilter expressions) e nextPEs
      float nodup floatFilterWalk intFreeWalk walkExecuted
  obtain ⟨mslWrites, mslCommit, mslFree⟩ :=
    welcomePEMslMsrStageLm1Provenance (welcomeInitialState welcomeZeroWords) nextPEs nextMsl
      (expressions.map NormalizedExpr.toParsed)
      (expressions.any (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed))
      (expressions.any (parsedExprHasSingleLineWriteMask ∘ NormalizedExpr.toParsed))
      (welcomePEMiddleStageLm1Free_msl expressions middleFree) mslExecuted
  obtain ⟨reluWrites, reluCommit, reluFree⟩ :=
    welcomePEFloatReluStageLm1Provenance (welcomeInitialState welcomeZeroWords) nextMsl nextRelu
      (expressions.map NormalizedExpr.toParsed)
      (expressions.any (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed))
      (expressions.any (parsedExprHasSingleLineWriteMask ∘ NormalizedExpr.toParsed))
      (welcomePEMiddleStageLm1Free_relu expressions middleFree) reluExecuted
  obtain ⟨blockWrites, blockCommit, blockFree⟩ :=
    welcomePEBlockFloatStageLm1Provenance (welcomeInitialState welcomeZeroWords) nextRelu
      nextBlockFloat (expressions.map NormalizedExpr.toParsed)
      (expressions.any (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed))
      (expressions.any (parsedExprHasSingleLineWriteMask ∘ NormalizedExpr.toParsed))
      (welcomePEMiddleStageLm1Free_block expressions middleFree) blockExecuted
  obtain ⟨matrixWrites, matrixCommit, matrixFree⟩ :=
    welcomePEMatrixMAUStageLm1Provenance (welcomeInitialState welcomeZeroWords) nextBlockFloat
      afterMatrix (expressions.map NormalizedExpr.toParsed)
      (expressions.any (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed))
      (expressions.any (parsedExprHasSingleLineWriteMask ∘ NormalizedExpr.toParsed))
      (welcomePEMiddleStageLm1Free_matrixMAU expressions matrixFreeRows) matrixExecuted
  obtain ⟨l1Writes, l1Commit, l1Free⟩ :=
    welcomePEL1ToPEStageLm1Provenance (welcomeInitialState welcomeZeroWords) nextShared
      nextBroadcast (expressions.map NormalizedExpr.toParsed)
      (expressions.any (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed))
      (expressions.any (parsedExprHasSingleLineWriteMask ∘ NormalizedExpr.toParsed))
      (parsedL1ToPEPrecedesOMRWriter (expressions.map NormalizedExpr.toParsed))
      (welcomePEMiddleStageLm1Free_l1 expressions l1FreeRows) l1Executed
  have sharedFrame : nextShared.peRegisters welcomePE = afterMatrix.peRegisters welcomePE :=
    congrFun (executeParsedSharedBlockProducers_peRegisters (welcomeInitialState welcomeZeroWords)
      afterMatrix nextShared (expressions.map NormalizedExpr.toParsed)
      (!(expressions.any (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed)))
      sharedExecuted) welcomePE
  have peEq : next.peRegisters welcomePE = nextBroadcast.peRegisters welcomePE := by
    rw [nextEq]
  refine ⟨intWrites ++ mslWrites ++ reluWrites ++ blockWrites ++ matrixWrites ++ l1Writes,
    executeIntegerProducerInstructionLine_pe_commit_split nextPEs nextMsl nextRelu
      nextBlockFloat afterMatrix nextShared nextBroadcast next peEq intWrites mslWrites
      reluWrites blockWrites matrixWrites l1Writes intCommit mslCommit reluCommit blockCommit
      matrixCommit sharedFrame l1Commit, ?_⟩
  exact lm1WritesShape_of_six_first intWrites mslWrites reluWrites blockWrites matrixWrites
    l1Writes intShape mslFree reluFree blockFree matrixFree l1Free

/-! ## 3. The weakened float-MAU package

The package keeps the float-Filter singleton (which the issue checker gives) and
replaces the `.noforward` demand by `.lm1`-freeness of the integer-stage rows
(which writer uniqueness gives). -/

/-- **The float-MAU-writer data of one line, weakened.**  The float-MAU filter is
the writer alone and every integer-stage row carries no `.lm1` destination
operand. -/
def WelcomePEFloatMAUWriterDataForIntRows (expressions : List NormalizedExpr) : Prop :=
  ∀ (e : ParsedExpr),
    e ∈ expressions.map NormalizedExpr.toParsed →
      parsedExprIsSupportedFloatMAUProducer e = true →
      Issue.Bank.lm1 ∈ (e.toIssueExpr 0).writeBanks →
      (expressions.map NormalizedExpr.toParsed).filter
          parsedExprIsSupportedFloatMAUProducer = [e] ∧
        (∀ expression ∈ (expressions.map NormalizedExpr.toParsed).filter
          parsedExprIsIntegerMatrixReadStageInput, WelcomeRowHasNoLm1Destination expression)

/-- The global weakened float-MAU-writer data package. -/
def WelcomePEFloatMAUWriterDataIntRows : Prop :=
  ∀ expressions, WelcomePEUnrefuted expressions → WelcomePEFloatMAUWriterDataForIntRows expressions

/-- **The float-MAU-writer line shape, from the weakened package data.** -/
theorem welcomePEWriteShape_of_floatMAUWriter_dataIntRows
    (expressions : List NormalizedExpr)
    (data : WelcomePEFloatMAUWriterDataForIntRows expressions)
    (unrefuted : WelcomePEUnrefuted expressions) (e : ParsedExpr)
    (eMem : e ∈ expressions.map NormalizedExpr.toParsed)
    (float : parsedExprIsSupportedFloatMAUProducer e = true)
    (writer : Issue.Bank.lm1 ∈ (e.toIssueExpr 0).writeBanks) :
    WelcomePEWriteShape expressions := by
  obtain ⟨floatFilter, intFree⟩ := data e eMem float writer
  obtain ⟨-, mslFalse, matrixMAUFalse, blockFalse, reluFalse, -, l1False, -⟩ :=
    floatMAU_parsedExpr_predicates e float
  exact welcomePEWriteShape_of_floatMAUWriter_dispatch_intRows expressions e float
    (welcomeLm1Writer_nodup expressions unrefuted e eMem) floatFilter intFree
    (welcomePEMiddleStageLm1Free_of_rows expressions e
      (welcomeLm1Writer_rows expressions unrefuted e eMem writer) mslFalse reluFalse blockFalse)
    (welcomePEMatrixMAUStageLm1Free_of_rows expressions e
      (welcomeLm1Writer_rows expressions unrefuted e eMem writer) matrixMAUFalse)
    (welcomePEL1StageLm1Free_of_rows expressions e
      (welcomeLm1Writer_rows expressions unrefuted e eMem writer) l1False)

/-! ## 4. The weakened float-MAU package is unconditional

Two independent issue-checker facts discharge its two conjuncts:

* the float-MAU filter is a singleton because every supported float-MAU row has
  issue group `.mauCalc` and `groupsUnique` forbids two rows of one group;
* the integer-stage rows carry no `.lm1` destination because the writer `e`
  already does, and two `.lm1`-writing rows of an accepted line are equal. -/

/-- **The float-MAU filter of an unrefuted line is the writer alone.** -/
theorem welcomeLine_floatMAU_filter_singleton
    (expressions : List NormalizedExpr) (unrefuted : WelcomePEUnrefuted expressions)
    (e : ParsedExpr) (eMem : e ∈ expressions.map NormalizedExpr.toParsed)
    (float : parsedExprIsSupportedFloatMAUProducer e = true) :
    (expressions.map NormalizedExpr.toParsed).filter
      parsedExprIsSupportedFloatMAUProducer = [e] := by
  have member : e ∈ (expressions.map NormalizedExpr.toParsed).filter
      parsedExprIsSupportedFloatMAUProducer := List.mem_filter.mpr ⟨eMem, float⟩
  exact filter_singleton_of_length_le_one _ _ e member
    (welcomeLine_filter_length_le_one_of_group expressions unrefuted
      parsedExprIsSupportedFloatMAUProducer Issue.Group.mauCalc
      (fun x _ hx => floatMAU_issueGroup x hx))

/-- **The integer-stage rows of a float-MAU-writer line are `.lm1`-free.**  The
float row is not an integer-stage input, so every integer-stage row is a row
other than the writer; a second `.lm1` writer would coincide with it. -/
theorem welcomeLine_intStage_lm1Free_of_floatWriter
    (expressions : List NormalizedExpr) (unrefuted : WelcomePEUnrefuted expressions)
    (e : ParsedExpr) (eMem : e ∈ expressions.map NormalizedExpr.toParsed)
    (float : parsedExprIsSupportedFloatMAUProducer e = true)
    (writer : Issue.Bank.lm1 ∈ (e.toIssueExpr 0).writeBanks) :
    ∀ expression ∈ (expressions.map NormalizedExpr.toParsed).filter
      parsedExprIsIntegerMatrixReadStageInput, WelcomeRowHasNoLm1Destination expression := by
  obtain ⟨-, -, -, -, -, -, -, intStageFalse⟩ := floatMAU_parsedExpr_predicates e float
  intro expression member
  have lineMem : expression ∈ expressions.map NormalizedExpr.toParsed :=
    List.mem_of_mem_filter member
  have different : expression ≠ e := by
    intro same
    subst same
    have keeps := (List.mem_filter.mp member).2
    rw [intStageFalse] at keeps
    exact absurd keeps (by simp)
  apply welcomeRowHasNoLm1Destination_of_writeBanks_not_mem expression 0
  intro expressionWriter
  exact different (welcomeLm1Writer_eq_of_two expressions unrefuted lineMem eMem
    expressionWriter writer)

/-- **The weakened float-MAU writer-kind package holds unconditionally.** -/
theorem welcomePEFloatMAUWriterData_intRows : WelcomePEFloatMAUWriterDataIntRows := by
  intro expressions unrefuted e eMem float writer
  exact ⟨welcomeLine_floatMAU_filter_singleton expressions unrefuted e eMem float,
    welcomeLine_intStage_lm1Free_of_floatWriter expressions unrefuted e eMem float writer⟩

/-- **The float-MAU writer case of the line shape, with no hypothesis.**  The
unique `.lm1` writer `e` being a float-MAU row already forces the line's write
shape. -/
theorem welcomePEWriteShape_of_floatMAUWriter
    (expressions : List NormalizedExpr) (unrefuted : WelcomePEUnrefuted expressions)
    (e : ParsedExpr) (eMem : e ∈ expressions.map NormalizedExpr.toParsed)
    (float : parsedExprIsSupportedFloatMAUProducer e = true)
    (writer : Issue.Bank.lm1 ∈ (e.toIssueExpr 0).writeBanks) :
    WelcomePEWriteShape expressions :=
  welcomePEWriteShape_of_floatMAUWriter_dataIntRows expressions
    (welcomePEFloatMAUWriterData_intRows expressions unrefuted) unrefuted e eMem float writer

/-- **Conservative direction: the round-49 float package implies the weakened
one.**  Nothing that satisfied "every integer-stage row is `.noforward`" is
excluded. -/
theorem welcomePEFloatMAUWriterDataFor_intRows_of_strong
    (expressions : List NormalizedExpr) (unrefuted : WelcomePEUnrefuted expressions)
    (data : WelcomePEFloatMAUWriterDataFor expressions) :
    WelcomePEFloatMAUWriterDataForIntRows expressions := by
  intro e eMem float writer
  obtain ⟨floatFilter, -⟩ := data e eMem float writer
  exact ⟨floatFilter, welcomeLine_intStage_lm1Free_of_floatWriter expressions unrefuted e eMem
    float writer⟩

/-- **Global conservative direction for the float-MAU package.** -/
theorem welcomePEFloatMAUWriterData_intRows_of_strong
    (data : WelcomePEFloatMAUWriterData) : WelcomePEFloatMAUWriterDataIntRows :=
  fun expressions unrefuted =>
    welcomePEFloatMAUWriterDataFor_intRows_of_strong expressions unrefuted
      (data expressions unrefuted)

/-! ## 5. The `.l1bm`-broadcast writer without the singleton-filter restriction

`executeParsedL1ToPEProducers` fails outright on two rows
(`executeParsedL1ToPEProducers_multiple_fail`), so a *successful* L1BM-to-PE
stage already has a singleton filter.  The filter need not be a singleton for
the package: the shape theorem strips the stage out of the step, receives its
success equation, and derives the singleton there. -/

/-- **A successful L1BM-to-PE stage has a singleton filter.**  If `e` is one of
the filter's rows and the stage returns `.ok`, then the filter is `[e]`. -/
theorem l1ToPEProducers_filter_eq_singleton_of_ok
    (readState currentState : State) (expressions : List ParsedExpr)
    (noForward hasSingleLineMask usePreIssueMask : Bool) (next : State)
    (e : ParsedExpr)
    (eMem : e ∈ expressions.filter parsedExprIsL1ToPEProducer)
    (executed : executeParsedL1ToPEProducers readState currentState expressions noForward
      hasSingleLineMask usePreIssueMask = .ok next) :
    expressions.filter parsedExprIsL1ToPEProducer = [e] := by
  unfold executeParsedL1ToPEProducers at executed
  cases hf : expressions.filter parsedExprIsL1ToPEProducer with
  | nil =>
      rw [hf] at eMem
      simp at eMem
  | cons x rest =>
      cases rest with
      | nil =>
          have same : e = x := by simpa [hf] using eMem
          subst same
          rfl
      | cons y rest' =>
          rw [hf] at executed
          simp at executed

/-- **The `.l1bm`-broadcast-writer data of one line, without the singleton
filter.**  The row-local lowering shape (one masked `.mem .lm1` destination of
static width `w`) is kept; the L1BM-to-PE filter singleton and the empty
float-MAU filter are dropped.  The singleton is recovered from the stage's
success equation, and the float filter's `.lm1`-freeness from writer uniqueness. -/
def WelcomePEL1BMWriterDataForNoSingleton (expressions : List NormalizedExpr) : Prop :=
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
            some (PEMemory.Bank.lm1, w)

/-- The global weakened `.l1bm`-writer data package. -/
def WelcomePEL1BMWriterDataNoSingleton : Prop :=
  ∀ expressions, WelcomePEUnrefuted expressions →
    WelcomePEL1BMWriterDataForNoSingleton expressions

/-- **The `.l1bm`-broadcast-writer dispatch without the singleton hypothesis.**
This is `welcomePEWriteShape_of_l1bmWriter_dispatch_floatRows` with the L1BM-to-PE
filter hypothesis removed: the singleton is derived from the stage's own success
equation, and the other stages' `.lm1`-freeness is taken in row-local form. -/
theorem welcomePEWriteShape_of_l1bmWriter_dispatch_noSingleton
    (expressions : List NormalizedExpr)
    (e : ParsedExpr) (access : ParsedL1ToPEAccess) (memoryAccess : Access)
    (negated extended rounded : Bool) (mask : Option ParsedMask) (w : PEMemory.Width)
    (lowered : lowerParsedL1ToPE? e = some access)
    (destinations : access.destinations =
      [ParsedOperand.mem memoryAccess negated extended rounded mask])
    (static : ParsedOperand.directDestinationBankWidth?
      (ParsedOperand.mem memoryAccess negated extended rounded mask) =
      some (PEMemory.Bank.lm1, w))
    (eMem : e ∈ expressions.map NormalizedExpr.toParsed)
    (l1Kind : parsedExprIsL1ToPEProducer e = true)
    (intFree : ∀ expression ∈ (expressions.map NormalizedExpr.toParsed).filter
        parsedExprIsIntegerMatrixReadStageInput, WelcomeRowHasNoLm1Destination expression)
    (floatFreeRows : ∀ expression ∈ (expressions.map NormalizedExpr.toParsed).filter
        parsedExprIsSupportedFloatMAUProducer, WelcomeRowHasNoLm1Destination expression)
    (middleFree : WelcomePEMiddleStageLm1Free expressions)
    (matrixFreeRows : WelcomePEMatrixMAUStageLm1Free expressions) :
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
  have l1Filter : (expressions.map NormalizedExpr.toParsed).filter
      parsedExprIsL1ToPEProducer = [e] :=
    l1ToPEProducers_filter_eq_singleton_of_ok (welcomeInitialState welcomeZeroWords) nextShared
      (expressions.map NormalizedExpr.toParsed)
      (expressions.any (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed))
      (expressions.any (parsedExprHasSingleLineWriteMask ∘ NormalizedExpr.toParsed))
      (parsedL1ToPEPrecedesOMRWriter (expressions.map NormalizedExpr.toParsed))
      nextBroadcast e (List.mem_filter.mpr ⟨eMem, l1Kind⟩) l1Executed
  have floatFreeWalk : ∀ expression ∈ (welcomePEWalkFilter expressions).filter
      parsedExprIsSupportedFloatMAUProducer, WelcomeRowHasNoLm1Destination expression := by
    intro expression member
    exact floatFreeRows expression (by rw [welcomePEWalkFilter_float] at member; exact member)
  obtain ⟨intWrites, floatWrites, intSlots, intBars, intPrep, intCommit, floatFree⟩ :=
    executeIntegerProducerLineAtPEs_zero_prepared_float_clean (welcomePEWalkFilter expressions)
      nextPEs floatFreeWalk walkExecuted
  have intWritesFree : Lm1FreePreparedWrites intWrites :=
    welcomeIntegerPrep_lm1_free (welcomeInitialState welcomeZeroWords) welcomePE
      (welcomePEWalkFilter expressions) intWrites intSlots intBars intPrep (by
        intro expression member
        exact intFree expression (by rw [welcomePEWalkFilter_integer] at member; exact member))
  have combinedFree : Lm1FreePreparedWrites (intWrites ++ floatWrites) :=
    lm1FreePreparedWrites_append intWritesFree floatFree
  obtain ⟨mslWrites, mslCommit, mslFree⟩ :=
    welcomePEMslMsrStageLm1Provenance (welcomeInitialState welcomeZeroWords) nextPEs nextMsl
      (expressions.map NormalizedExpr.toParsed)
      (expressions.any (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed))
      (expressions.any (parsedExprHasSingleLineWriteMask ∘ NormalizedExpr.toParsed))
      (welcomePEMiddleStageLm1Free_msl expressions middleFree) mslExecuted
  obtain ⟨reluWrites, reluCommit, reluFree⟩ :=
    welcomePEFloatReluStageLm1Provenance (welcomeInitialState welcomeZeroWords) nextMsl nextRelu
      (expressions.map NormalizedExpr.toParsed)
      (expressions.any (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed))
      (expressions.any (parsedExprHasSingleLineWriteMask ∘ NormalizedExpr.toParsed))
      (welcomePEMiddleStageLm1Free_relu expressions middleFree) reluExecuted
  obtain ⟨blockWrites, blockCommit, blockFree⟩ :=
    welcomePEBlockFloatStageLm1Provenance (welcomeInitialState welcomeZeroWords) nextRelu
      nextBlockFloat (expressions.map NormalizedExpr.toParsed)
      (expressions.any (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed))
      (expressions.any (parsedExprHasSingleLineWriteMask ∘ NormalizedExpr.toParsed))
      (welcomePEMiddleStageLm1Free_block expressions middleFree) blockExecuted
  obtain ⟨matrixWrites, matrixCommit, matrixFree⟩ :=
    welcomePEMatrixMAUStageLm1Provenance (welcomeInitialState welcomeZeroWords) nextBlockFloat
      afterMatrix (expressions.map NormalizedExpr.toParsed)
      (expressions.any (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed))
      (expressions.any (parsedExprHasSingleLineWriteMask ∘ NormalizedExpr.toParsed))
      (welcomePEMiddleStageLm1Free_matrixMAU expressions matrixFreeRows) matrixExecuted
  obtain ⟨l1Writes, l1Commit, l1Shape⟩ :=
    executeParsedL1ToPEProducers_mem_lm1_shape welcomeZeroWords nextShared nextBroadcast
      (expressions.map NormalizedExpr.toParsed) e access
      (expressions.any (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed))
      (expressions.any (parsedExprHasSingleLineWriteMask ∘ NormalizedExpr.toParsed))
      (parsedL1ToPEPrecedesOMRWriter (expressions.map NormalizedExpr.toParsed))
      memoryAccess negated extended rounded mask w lowered destinations static l1Filter
      l1Executed
  have sharedFrame : nextShared.peRegisters welcomePE = afterMatrix.peRegisters welcomePE :=
    congrFun (executeParsedSharedBlockProducers_peRegisters (welcomeInitialState welcomeZeroWords)
      afterMatrix nextShared (expressions.map NormalizedExpr.toParsed)
      (!(expressions.any (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed)))
      sharedExecuted) welcomePE
  have peEq : next.peRegisters welcomePE = nextBroadcast.peRegisters welcomePE := by
    rw [nextEq]
  refine ⟨(intWrites ++ floatWrites) ++ mslWrites ++ reluWrites ++ blockWrites ++ matrixWrites
      ++ l1Writes,
    executeIntegerProducerInstructionLine_pe_commit_split nextPEs nextMsl nextRelu
      nextBlockFloat afterMatrix nextShared nextBroadcast next peEq (intWrites ++ floatWrites)
      mslWrites reluWrites blockWrites matrixWrites l1Writes intCommit mslCommit reluCommit
      blockCommit matrixCommit sharedFrame l1Commit, ?_⟩
  exact lm1WritesShape_of_six_sixth (intWrites ++ floatWrites) mslWrites reluWrites blockWrites
    matrixWrites l1Writes combinedFree mslFree reluFree blockFree matrixFree l1Shape

/-- **The `.l1bm`-writer line shape, from the weakened package data.** -/
theorem welcomePEWriteShape_of_l1bmWriter_dataNoSingleton
    (expressions : List NormalizedExpr)
    (data : WelcomePEL1BMWriterDataForNoSingleton expressions)
    (unrefuted : WelcomePEUnrefuted expressions) (e : ParsedExpr)
    (eMem : e ∈ expressions.map NormalizedExpr.toParsed)
    (l1 : parsedExprIsL1ToPEProducer e = true)
    (writer : Issue.Bank.lm1 ∈ (e.toIssueExpr 0).writeBanks) :
    WelcomePEWriteShape expressions := by
  obtain ⟨access, memoryAccess, negated, extended, rounded, mask, w, lowered, destinations,
    static⟩ := data e eMem l1 writer
  obtain ⟨intStageFalse, floatFalse, -, mslFalse, reluFalse, blockFalse, matrixMAUFalse, -, -⟩ :=
    l1bmBroadcast_parsedExpr_predicates e access lowered
  have rows := welcomeLm1Writer_rows expressions unrefuted e eMem writer
  exact welcomePEWriteShape_of_l1bmWriter_dispatch_noSingleton expressions e access memoryAccess
    negated extended rounded mask w lowered destinations static eMem l1
    (fun expression member => rows expression (List.mem_of_mem_filter member) (by
      intro same
      subst same
      have keeps := (List.mem_filter.mp member).2
      rw [intStageFalse] at keeps
      exact absurd keeps (by simp)))
    (floatFilter_lm1Free_of_rows expressions e rows floatFalse)
    (welcomePEMiddleStageLm1Free_of_rows expressions e rows mslFalse reluFalse blockFalse)
    (welcomePEMatrixMAUStageLm1Free_of_rows expressions e rows matrixMAUFalse)

/-- **Conservative direction: the round-49 `.l1bm` package implies the weakened
one.**  The singleton filter and the empty-float-filter conjunct were the only
removed components; the row-local lowering shape is unchanged. -/
theorem welcomePEL1BMWriterDataFor_noSingleton_of_strong
    (expressions : List NormalizedExpr) (data : WelcomePEL1BMWriterDataFor expressions) :
    WelcomePEL1BMWriterDataForNoSingleton expressions := by
  intro e eMem l1 writer
  obtain ⟨access, memoryAccess, negated, extended, rounded, mask, w, lowered, destinations,
    static, -, -⟩ := data e eMem l1 writer
  exact ⟨access, memoryAccess, negated, extended, rounded, mask, w, lowered, destinations, static⟩

/-- **Global conservative direction for the `.l1bm` package.** -/
theorem welcomePEL1BMWriterData_noSingleton_of_strong
    (data : WelcomePEL1BMWriterData) : WelcomePEL1BMWriterDataNoSingleton :=
  fun expressions unrefuted =>
    welcomePEL1BMWriterDataFor_noSingleton_of_strong expressions (data expressions unrefuted)



/-! ## 6. Why the singleton filter is not a consequence of acceptance

The weakened package above does not *derive* the singleton from acceptance; it
derives it from the stage's success equation.  The distinction is real: the
following two-row line is accepted by the issue checker, is `WelcomePEUnrefuted`,
has two L1BM-to-PE rows, and therefore falsifies the round-49
`WelcomePEL1BMWriterData` outright.

* the first row is an addressed `.pbcast` row writing `.lm1`, so its issue group
  is `.l1bm` and it is the line's `.lm1` writer;
* the second row is a `.pbcast` row whose destination is the turnaround operand
  `.l1bm 1 none` (and whose source is an `.lm0` memory operand, so it does not
  write the LBF either).  Its issue group is `.l1bmTurnaround`, so
  `groupsUnique` — which only compares rows of the *same* group — permits it;
  it writes no bank, so `writesUnique` permits it; and it adds no LBF write, so
  `lbfWritesUnique` permits it.

This is the precise reason the singleton cannot be obtained from
`welcomeLm1Writer_unique`, `welcomeLine_nodup`, or the issue-group tool: those
only identify rows with the same group. -/

/-- The writer row of the two-row witness: an addressed `.pbcast` writing `.lm1`. -/
def l1ToPERowWitness : NormalizedExpr where
  op := .l1bm .pbcast
  sources := [.l1bm 1 (some 0)]
  destinations := [.mem (plusOneAccess .lm1 0) false false false none]
  flush := none

/-- The second L1BM-to-PE row of the witness.  It is a `.pbcast` row with a
turnaround operand in its destination list, hence issue group `.l1bmTurnaround`,
and it writes no bank. -/
def l1ToPESecondRowWitness : NormalizedExpr where
  op := .l1bm .pbcast
  sources := [.mem (plusOneAccess .lm0 0) false false false none]
  destinations := [.l1bm 1 none]
  flush := none

/-- The writer row's parsed view. -/
def l1ToPERowWitnessParsed : ParsedExpr := l1ToPERowWitness.toParsed

/-- The second row's parsed view. -/
def l1ToPESecondRowWitnessParsed : ParsedExpr := l1ToPESecondRowWitness.toParsed

/-- **The two rows of the witness have different issue groups.**  The writer is
an addressed `.pbcast` row (group `.l1bm`); the second row carries the turnaround
operand `.l1bm 1 none` in its destinations (group `.l1bmTurnaround`).  Since
`groupsUnique` only compares rows of the same group, it does not identify them. -/
theorem l1ToPESecondRow_groups_differ :
    l1ToPERowWitnessParsed.issueGroup = some Issue.Group.l1bm ∧
      l1ToPESecondRowWitnessParsed.issueGroup = some Issue.Group.l1bmTurnaround := by
  exact ⟨rfl, rfl⟩

/-- **The two-row witness is issue-legal.** -/
theorem l1ToPESecondRow_line_legal :
    LegalParsedLine [l1ToPERowWitnessParsed, l1ToPESecondRowWitnessParsed] := by
  unfold LegalParsedLine projectLine projectFrom ParsedExpr.toIssueExpr
    ParsedExpr.issueGroup ParsedExpr.issueMau ParsedOperand.accesses
    ParsedOperand.matrixUseCount ParsedExpr.hasTurnaround
    ParsedExpr.maskApplications ParsedOperand.writeMask?
    ParsedExpr.maskRegisterWrites ParsedOperand.maskRegisterWrite?
    ParsedExpr.barWrites ParsedOperand.barWriteBank?
    ParsedExpr.writesLbf ParsedExpr.nowriteOutputValid
  simp [l1ToPERowWitnessParsed, l1ToPESecondRowWitnessParsed, l1ToPERowWitness,
    l1ToPESecondRowWitness, Legal, idsUnique, groupsUnique, mauCountBounded, mauExpressions,
    mauPrecisionsAgree, matrixWritePairAgrees, matrixRegistersUnique, writesUnique,
    Expr.writeBanks, barWritesExcludeReads, readsAgree, localReadWriteAgree,
    immediateExcludesLm0, zeroFlushUnique, maskWidthsAgree, maskEntriesAgree,
    nowriteOutputsUnique, lbfWritesUnique, maskRegisterWritesUnique, projectFrom,
    Issue.plusOneAccess, NormalizedExpr.toParsed, ParsedExpr.toIssueExpr,
    ParsedExpr.maskApplications, ParsedExpr.maskRegisterWrites, ParsedExpr.barWrites,
    ParsedExpr.writesLbf, ParsedExpr.nowriteOutputValid, ParsedExpr.issueGroup,
    ParsedExpr.issueMau, ParsedExpr.hasTurnaround, ParsedOperand.matrixUseCount,
    ParsedOperand.accesses, ParsedOperand.barWriteBank?, ParsedOperand.writeMask?,
    ParsedOperand.maskRegisterWrite?, Expr.writeBanks, mauExpressions,
    List.any_cons, List.any_nil, List.filter_cons, List.filter_nil,
    List.filterMap_cons, List.filterMap_nil, Bool.true_and, Bool.false_and]

/-- **The two-row witness is accepted by the issue checker.** -/
theorem l1ToPESecondRow_line_accepted :
    checkParsedTopLine (InstructionLine.pe [l1ToPERowWitness, l1ToPESecondRowWitness]).toParsed =
      true := by
  have legal : LegalParsedLine
      ([l1ToPERowWitness, l1ToPESecondRowWitness].map NormalizedExpr.toParsed) := by
    simpa [l1ToPERowWitnessParsed, l1ToPESecondRowWitnessParsed] using l1ToPESecondRow_line_legal
  exact parsed_check_complete _ legal

/-- No wait of the witness is pending. -/
theorem l1ToPESecondRow_line_wait :
    ([l1ToPERowWitness, l1ToPESecondRowWitness].map NormalizedExpr.toParsed).any
      (parsedExprWaitPending (welcomeInitialState welcomeZeroWords)) = false := by
  simp [NormalizedExpr.toParsed, l1ToPERowWitness, l1ToPESecondRowWitness,
    l1ToPERowWitnessParsed, l1ToPESecondRowWitnessParsed, parsedExprWaitPending,
    parsedExprWaitTag?]

/-- The witness has no Rust-unsupported ALU row. -/
theorem l1ToPESecondRow_line_unsupported :
    ([l1ToPERowWitness, l1ToPESecondRowWitness].map NormalizedExpr.toParsed).any
      parsedExprIsUnsupportedRustAlu = false := by
  simp [NormalizedExpr.toParsed, l1ToPERowWitness, l1ToPESecondRowWitness,
    l1ToPERowWitnessParsed, l1ToPESecondRowWitnessParsed, parsedExprIsUnsupportedRustAlu]

/-- Both rows of the witness are supported producers. -/
theorem l1ToPESecondRow_line_supported :
    ([l1ToPERowWitness, l1ToPESecondRowWitness].map NormalizedExpr.toParsed).all
      parsedExprIsSupportedPELineProducer = true := by
  decide

/-- The witness is not an all-`.noforward` line. -/
theorem l1ToPESecondRow_line_notAllNoForward :
    ¬ WelcomeAllNoForward [l1ToPERowWitness, l1ToPESecondRowWitness] := by
  intro all
  have h := all l1ToPERowWitnessParsed
    (by simp [l1ToPERowWitnessParsed, NormalizedExpr.toParsed, l1ToPERowWitness,
      l1ToPESecondRowWitness])
  simp [NormalizedExpr.toParsed, l1ToPERowWitness, l1ToPESecondRowWitness,
    l1ToPERowWitnessParsed, l1ToPESecondRowWitnessParsed] at h

/-- The witness is not a single Welcome `iinc` line. -/
theorem l1ToPESecondRow_line_notSingle :
    ¬ WelcomeSingleWelcomeLine [l1ToPERowWitness, l1ToPESecondRowWitness] := by
  intro ⟨base, h⟩
  have len := congrArg List.length h
  simp [l1ToPERowWitness, l1ToPESecondRowWitness] at len

/-- **The two-row witness is unrefuted.** -/
theorem l1ToPESecondRow_unrefuted :
    WelcomePEUnrefuted [l1ToPERowWitness, l1ToPESecondRowWitness] :=
  ⟨⟨l1ToPESecondRow_line_accepted, l1ToPESecondRow_line_wait,
    l1ToPESecondRow_line_unsupported, l1ToPESecondRow_line_supported⟩,
    l1ToPESecondRow_line_notAllNoForward, l1ToPESecondRow_line_notSingle⟩

/-- The witness row writes bank `.lm1`. -/
theorem l1ToPESecondRow_writer_lm1 :
    Issue.Bank.lm1 ∈ (l1ToPERowWitnessParsed.toIssueExpr 0).writeBanks := by
  simp [l1ToPERowWitnessParsed, NormalizedExpr.toParsed, l1ToPERowWitness,
    ParsedExpr.toIssueExpr, Expr.writeBanks, ParsedOperand.accesses,
    ParsedExpr.barWrites, ParsedOperand.barWriteBank?, Issue.plusOneAccess]

/-- **The L1BM-to-PE filter of the witness has two rows.** -/
theorem l1ToPESecondRow_filter :
    ([l1ToPERowWitness, l1ToPESecondRowWitness].map NormalizedExpr.toParsed).filter
      parsedExprIsL1ToPEProducer = [l1ToPERowWitnessParsed, l1ToPESecondRowWitnessParsed] := by
  decide

/-- **The round-49 `.l1bm` package is false.**  The two-row witness is an
unrefuted line with two L1BM-to-PE rows, so its L1BM-to-PE filter cannot be the
singleton `[e]` for the writer.  The singleton component is therefore not a
consequence of acceptance; the weakened package above replaces it by the stage's
success equation. -/
theorem l1ToPESecondRow_oldPackage_false : ¬ WelcomePEL1BMWriterData := by
  intro data
  have d := data [l1ToPERowWitness, l1ToPESecondRowWitness] l1ToPESecondRow_unrefuted
  have h := d l1ToPERowWitnessParsed
    (by simp [l1ToPERowWitnessParsed, NormalizedExpr.toParsed, l1ToPERowWitness,
      l1ToPESecondRowWitness])
    (by decide) l1ToPESecondRow_writer_lm1
  obtain ⟨access, memoryAccess, negated, extended, rounded, mask, w, lowered, destinations,
    static, l1Filter, floatEmpty⟩ := h
  rw [l1ToPESecondRow_filter] at l1Filter
  exact absurd l1Filter (by decide)

/-! ### 6.1 The remaining single-destination row shape is also not derivable from acceptance

The weakened package still asks the writer's lowering to have a *single* masked
`.mem .lm1` destination.  That is not bookkeeping either: a broadcast row with
two `.mem` destinations (one `.lm1`, one `.lm0`) is accepted, is the line's
`.lm1` writer, and lowers to two destinations.  Such a row is outside the
weakened package, so
`welcomePEL1BMWriterDataNoSingleton` is not a consequence of acceptance either;
closing this case needs a multi-destination form of
`executeParsedL1ToPEProducer_mem_lm1_shape`. -/

/-- A broadcast `.pbcast` row with two `.mem` destinations (`.lm1` and `.lm0`). -/
def l1ToPETwoDestinationWitness : NormalizedExpr where
  op := .l1bm .pbcast
  sources := [.l1bm 1 (some 0)]
  destinations := [.mem (plusOneAccess .lm1 0) false false false none,
                   .mem (plusOneAccess .lm0 0) false false false none]
  flush := none

/-- The two-destination witness's parsed view. -/
def l1ToPETwoDestinationWitnessParsed : ParsedExpr := l1ToPETwoDestinationWitness.toParsed

/-- **The two-destination witness is issue-legal.** -/
theorem l1ToPETwoDestination_line_legal :
    LegalParsedLine [l1ToPETwoDestinationWitnessParsed] := by
  unfold LegalParsedLine projectLine projectFrom ParsedExpr.toIssueExpr
    ParsedExpr.issueGroup ParsedExpr.issueMau ParsedOperand.accesses
    ParsedOperand.matrixUseCount ParsedExpr.hasTurnaround
    ParsedExpr.maskApplications ParsedOperand.writeMask?
    ParsedExpr.maskRegisterWrites ParsedOperand.maskRegisterWrite?
    ParsedExpr.barWrites ParsedOperand.barWriteBank?
    ParsedExpr.writesLbf ParsedExpr.nowriteOutputValid
  simp [l1ToPETwoDestinationWitnessParsed, l1ToPETwoDestinationWitness, Legal, idsUnique,
    groupsUnique, mauCountBounded, mauExpressions, mauPrecisionsAgree, matrixWritePairAgrees,
    matrixRegistersUnique, writesUnique, Expr.writeBanks, barWritesExcludeReads, readsAgree,
    localReadWriteAgree, immediateExcludesLm0, zeroFlushUnique, maskWidthsAgree,
    maskEntriesAgree, nowriteOutputsUnique, lbfWritesUnique, maskRegisterWritesUnique,
    projectFrom, Issue.plusOneAccess, NormalizedExpr.toParsed, ParsedExpr.toIssueExpr,
    ParsedExpr.maskApplications, ParsedExpr.maskRegisterWrites, ParsedExpr.barWrites,
    ParsedExpr.writesLbf, ParsedExpr.nowriteOutputValid, ParsedExpr.issueGroup,
    ParsedExpr.issueMau, ParsedExpr.hasTurnaround, ParsedOperand.matrixUseCount,
    ParsedOperand.accesses, ParsedOperand.barWriteBank?, ParsedOperand.writeMask?,
    ParsedOperand.maskRegisterWrite?, Expr.writeBanks, mauExpressions,
    List.any_cons, List.any_nil, List.filter_cons, List.filter_nil,
    List.filterMap_cons, List.filterMap_nil, Bool.true_and, Bool.false_and]

/-- **The two-destination witness is accepted.** -/
theorem l1ToPETwoDestination_line_accepted :
    checkParsedTopLine (InstructionLine.pe [l1ToPETwoDestinationWitness]).toParsed = true := by
  have legal : LegalParsedLine
      ([l1ToPETwoDestinationWitness].map NormalizedExpr.toParsed) := by
    simpa [l1ToPETwoDestinationWitnessParsed] using l1ToPETwoDestination_line_legal
  exact parsed_check_complete _ legal

/-- No wait of the two-destination witness is pending. -/
theorem l1ToPETwoDestination_line_wait :
    ([l1ToPETwoDestinationWitness].map NormalizedExpr.toParsed).any
      (parsedExprWaitPending (welcomeInitialState welcomeZeroWords)) = false := by
  simp [NormalizedExpr.toParsed, l1ToPETwoDestinationWitness,
    l1ToPETwoDestinationWitnessParsed, parsedExprWaitPending, parsedExprWaitTag?]

/-- The two-destination witness has no Rust-unsupported ALU row. -/
theorem l1ToPETwoDestination_line_unsupported :
    ([l1ToPETwoDestinationWitness].map NormalizedExpr.toParsed).any
      parsedExprIsUnsupportedRustAlu = false := by
  simp [NormalizedExpr.toParsed, l1ToPETwoDestinationWitness,
    l1ToPETwoDestinationWitnessParsed, parsedExprIsUnsupportedRustAlu]

/-- The two-destination witness's row is a supported producer. -/
theorem l1ToPETwoDestination_line_supported :
    ([l1ToPETwoDestinationWitness].map NormalizedExpr.toParsed).all
      parsedExprIsSupportedPELineProducer = true := by
  decide

/-- The two-destination witness is not all-`.noforward`. -/
theorem l1ToPETwoDestination_line_notAllNoForward :
    ¬ WelcomeAllNoForward [l1ToPETwoDestinationWitness] := by
  intro all
  have h := all l1ToPETwoDestinationWitnessParsed
    (by simp [l1ToPETwoDestinationWitnessParsed, NormalizedExpr.toParsed,
      l1ToPETwoDestinationWitness])
  simp [NormalizedExpr.toParsed, l1ToPETwoDestinationWitness,
    l1ToPETwoDestinationWitnessParsed] at h

/-- The two-destination witness is not a single Welcome `iinc` line. -/
theorem l1ToPETwoDestination_line_notSingle :
    ¬ WelcomeSingleWelcomeLine [l1ToPETwoDestinationWitness] := by
  intro ⟨base, h⟩
  have hw : l1ToPETwoDestinationWitness = welcomeExpr base := by simpa using h
  have op := congrArg NormalizedExpr.op hw
  simp [l1ToPETwoDestinationWitness, welcomeExpr_op] at op

/-- **The two-destination witness is unrefuted.** -/
theorem l1ToPETwoDestination_unrefuted :
    WelcomePEUnrefuted [l1ToPETwoDestinationWitness] :=
  ⟨⟨l1ToPETwoDestination_line_accepted, l1ToPETwoDestination_line_wait,
    l1ToPETwoDestination_line_unsupported, l1ToPETwoDestination_line_supported⟩,
    l1ToPETwoDestination_line_notAllNoForward, l1ToPETwoDestination_line_notSingle⟩

/-- The two-destination witness writes bank `.lm1`. -/
theorem l1ToPETwoDestination_writer_lm1 :
    Issue.Bank.lm1 ∈ (l1ToPETwoDestinationWitnessParsed.toIssueExpr 0).writeBanks := by
  simp [l1ToPETwoDestinationWitnessParsed, NormalizedExpr.toParsed,
    l1ToPETwoDestinationWitness, ParsedExpr.toIssueExpr, Expr.writeBanks,
    ParsedOperand.accesses, ParsedExpr.barWrites, ParsedOperand.barWriteBank?,
    Issue.plusOneAccess]

/-- The two-destination witness is an L1BM-to-PE producer. -/
theorem l1ToPETwoDestination_l1Kind :
    parsedExprIsL1ToPEProducer l1ToPETwoDestinationWitnessParsed = true := by
  decide

/-- **The two-destination witness is outside the weakened package**: its
lowering has two destinations, so no single masked `.mem` destination can be its
whole destination list. -/
theorem l1ToPETwoDestination_noSingleShape :
    ¬ WelcomePEL1BMWriterDataForNoSingleton [l1ToPETwoDestinationWitness] := by
  intro data
  have h := data l1ToPETwoDestinationWitnessParsed
    (by simp [l1ToPETwoDestinationWitnessParsed, NormalizedExpr.toParsed,
      l1ToPETwoDestinationWitness])
    l1ToPETwoDestination_l1Kind l1ToPETwoDestination_writer_lm1
  obtain ⟨access, memoryAccess, negated, extended, rounded, mask, w, lowered, destinations,
    static⟩ := h
  have destEq := lowerParsedL1ToPE?_destinations_eq l1ToPETwoDestinationWitnessParsed access
    lowered
  rw [destEq] at destinations
  have len := congrArg List.length destinations
  simp [l1ToPETwoDestinationWitnessParsed, l1ToPETwoDestinationWitness,
    NormalizedExpr.toParsed] at len

/-- **The weakened `.l1bm` package is not a consequence of acceptance either.**
The remaining single-destination requirement excludes the accepted
two-destination broadcast writer; a multi-destination row-shape theorem is the
next genuine obligation. -/
theorem l1ToPETwoDestination_weakPackage_false :
    ¬ WelcomePEL1BMWriterDataNoSingleton := by
  intro data
  exact l1ToPETwoDestination_noSingleShape (data [l1ToPETwoDestinationWitness]
    l1ToPETwoDestination_unrefuted)

/-! ## 7. The assembly with the two weakened packages

The float-MAU writer case is now a theorem, so the per-line dispatch no longer
needs a float package.  The `.l1bm` case needs only the row-local lowering shape
of the weakened package; §6.1 shows that this shape is not a consequence of
acceptance, so the assembly below is conditional on three packages and does not
cover multi-destination L1BM writers. -/

/-- **`WelcomePELm1WriteShapeObligation` from the plain, `.matrixRead` and
weakened `.l1bm` packages.**  This is
`welcomePELm1WriteShapeObligation_of_writerKindData` with the float-MAU package
discharged (unconditional theorem) and the `.l1bm` package weakened. -/
theorem welcomePELm1WriteShapeObligation_of_plainReadL1
    (plain : WelcomePEPlainWriterDataFlagFree)
    (read : WelcomePEMatrixReadWriterDataSlotFree)
    (l1 : WelcomePEL1BMWriterDataNoSingleton) :
    WelcomePELm1WriteShapeObligation := by
  intro expressions unrefuted
  by_cases hasWriter : ∃ e ∈ expressions.map NormalizedExpr.toParsed,
      Issue.Bank.lm1 ∈ (e.toIssueExpr 0).writeBanks
  · obtain ⟨e, eMem, eWriter⟩ := hasWriter
    have supported := List.all_eq_true.mp unrefuted.1.2.2.2 e eMem
    have notUnsupported : parsedExprIsUnsupportedRustAlu e = false := by
      simpa using (List.any_eq_false.mp unrefuted.1.2.2.1) e eMem
    rcases supportedProducer_partition e supported with
      isPlain | isFamily | isSpecial | isInert | isUnsupported
    · exact welcomePEWriteShape_of_plainWriter_data_flagFree expressions
        (plain expressions unrefuted) unrefuted e eMem isPlain eWriter
    · rcases parsedExprIsFamilyProducer_cases e isFamily with
        readKind | mauKind | floatKind | writeKind | toPEKind | l2Kind
      · exact welcomePEWriteShape_of_matrixReadWriter_data_slotFree expressions
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

/-- **The residual bundle of the weakened assembly.**  Only the plain and
`.matrixRead` packages and the row-local `.l1bm` lowering shape remain.

This bundle is **not satisfiable**: `l1ToPETwoDestination_weakPackage_false`
(§6.1) proves its `.l1bm` component false on an accepted unrefuted line with a
two-destination broadcast writer.  The bundle therefore records the *exact
remaining l1 obstruction* (the multi-destination row shape) rather than a live
hypothesis. -/
def WelcomePEWriterKindDataResidualsThree : Prop :=
  WelcomePEPlainWriterDataFlagFree ∧
    WelcomePEMatrixReadWriterDataSlotFree ∧ WelcomePEL1BMWriterDataNoSingleton

/-- **The residual bundle form** of
`welcomePELm1WriteShapeObligation_of_plainReadL1`. -/
theorem welcomePELm1WriteShapeObligation_of_residualsThree
    (residuals : WelcomePEWriterKindDataResidualsThree) :
    WelcomePELm1WriteShapeObligation := by
  obtain ⟨plain, read, l1⟩ := residuals
  exact welcomePELm1WriteShapeObligation_of_plainReadL1 plain read l1

/-- **The conservative direction at the bundle level.**  The round-49 four-package
bundle implies the three-package bundle of this module. -/
theorem welcomePEWriterKindDataResidualsThree_of_writerKindData
    (residuals : WelcomePEWriterKindDataResiduals) :
    WelcomePEWriterKindDataResidualsThree :=
  ⟨residuals.1, residuals.2.1,
    welcomePEL1BMWriterData_noSingleton_of_strong residuals.2.2.2⟩

/-- **The round-49 four-package residual bundle is refutable.**  Its `.l1bm`
component requires the singleton filter on every unrefuted line, and
`l1ToPESecondRow_oldPackage_false` exhibits an accepted line with two
L1BM-to-PE rows. -/
theorem welcomePEWriterKindDataResiduals_false : ¬ WelcomePEWriterKindDataResiduals :=
  fun residuals => l1ToPESecondRow_oldPackage_false residuals.2.2.2

/-- **The three-package residual bundle is refutable.**  Its `.l1bm` component
still requires a single-destination lowering, and
`l1ToPETwoDestination_weakPackage_false` exhibits an accepted two-destination
broadcast writer. -/
theorem welcomePEWriterKindDataResidualsThree_false :
    ¬ WelcomePEWriterKindDataResidualsThree :=
  fun residuals => l1ToPETwoDestination_weakPackage_false residuals.2.2

/-- **`LowerBound welcomeSealedMachine welcomeSpec 2` from the three packages**
(conditional; not an unconditional lower bound).  The `.l1bm` hypothesis is
refutable as a global package (§6.1), so this is a reduction of the remaining l1
obstruction, not a satisfiable path. -/
theorem welcomeLowerBound_two_of_plainReadL1
    (plain : WelcomePEPlainWriterDataFlagFree)
    (read : WelcomePEMatrixReadWriterDataSlotFree)
    (l1 : WelcomePEL1BMWriterDataNoSingleton) :
    ProofsLean.LowerBound welcomeSealedMachine welcomeSpec 2 :=
  welcomeLowerBound_two_of_lm1WriteShapes
    (welcomePELm1WriteShapeObligation_of_plainReadL1 plain read l1)

/-- **`Optimal welcomeSealedMachine welcomeSpec welcomeAnswer` from the three
packages** (conditional; not an unconditional optimality claim).  The `.l1bm`
hypothesis is refutable as a global package (§6.1). -/
theorem welcomeAnswer_optimal_of_plainReadL1
    (plain : WelcomePEPlainWriterDataFlagFree)
    (read : WelcomePEMatrixReadWriterDataSlotFree)
    (l1 : WelcomePEL1BMWriterDataNoSingleton) :
    ProofsLean.Optimal welcomeSealedMachine welcomeSpec welcomeAnswer :=
  welcomeAnswer_optimal_of_lm1WriteShapes
    (welcomePELm1WriteShapeObligation_of_plainReadL1 plain read l1)


/-- **All `.l1bm` operations obey one issue-group rule.**  The group of a `.l1bm`
row depends only on whether it carries a turnaround operand, not on the
operation: the broadcast forms (`pbcast` / `mbcast` / `m4bcast` / `distrib`) and
the shared-block forms (`mwrite` / `m4write` / `gather` / `reduce` / `reduce4`)
with equal turnaround flag have equal issue group.  Consequently `groupsUnique`
can only identify two `.l1bm` rows whose turnaround flags agree. -/
theorem l1bm_issueGroup_form (expression : ParsedExpr)
    (l1 : ∃ operation : ParsedL1Op, expression.op = .l1bm operation) :
    expression.issueGroup =
      (if expression.hasTurnaround then some Issue.Group.l1bmTurnaround
        else some Issue.Group.l1bm) := by
  obtain ⟨operation, h⟩ := l1
  cases expression with
  | mk op sources destinations flush text =>
      simp only at h
      subst h
      rfl

/-- **Two `.l1bm` rows with the same turnaround flag share their issue group** —
whether they are broadcast or shared-block rows. -/
theorem l1bm_issueGroup_eq_of_turnaround_eq (first second : ParsedExpr)
    (firstL1 : ∃ operation : ParsedL1Op, first.op = .l1bm operation)
    (secondL1 : ∃ operation : ParsedL1Op, second.op = .l1bm operation)
    (same : first.hasTurnaround = second.hasTurnaround) :
    first.issueGroup = second.issueGroup := by
  rw [l1bm_issueGroup_form first firstL1, l1bm_issueGroup_form second secondL1, same]

end ProofsLean.MNCore
