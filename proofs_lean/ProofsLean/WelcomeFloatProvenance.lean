import ProofsLean.WelcomeWriterDispatch
import ProofsLean.WelcomeStageProvenance

/-! # Write-list-level `.lm1` provenance for the float-MAU stage

`WelcomeStageProvenance.lean` proves the list-level `.lm1` provenance of the five
middle stages: for a stage `S` with producer filter `f`, a row-local hypothesis
`∀ e ∈ expressions.filter f, WelcomeRowHasNoLm1Destination e` yields a write list
that both commits the outgoing PE 0 file and satisfies `Lm1FreePreparedWrites`.

The float-MAU stage `executeParsedFloatMAUsAtPE` is **not** one of those five: it
runs *inside* the integer stage (`executeIntegerProducerLineAtPECore`), on the
whole line, just after the four-cycle integer/matrix-read preparation.  Only the
bank-level frame `executeParsedFloatMAUsAtPE_lm1_free` existed, and
`WelcomeWriterDispatch.lean` therefore carries a `floatEmpty` hypothesis in the
four non-float dispatch theorems (no float-MAU row at all), so that the integer
stage's list is precisely `welcomeIntegerPrep`'s.

This module closes that gap with the write-list-level companion, in exactly the
shape of the five stage statements:

`∃ writes, nextFiles = commitParsedMaskedWrites currentFiles writes ∧
  Lm1FreePreparedWrites writes`,

and then records the consequence: `floatEmpty` can be replaced by row-locality
(`∀ x ∈ line, x ≠ e → WelcomeRowHasNoLm1Destination x`) in the four non-float
unique-writer dispatch theorems.

The per-destination base case is the *write itself*, not the bank: a gated-off
`.lm1` write is still an `.lm1` write, so the bank-level frame cannot be reused.
The float-MAU destination loop commits through
`writeParsedMslMsrDestination?`, whose write-level companion
`writeParsedMslMsrDestination?_clean_commit` is already proved in
`WelcomeStageProvenance.lean` §1 and is applied here.

## Status

* §1 `writeParsedMAUDestinations?_writeAll_clean_commit`,
  `writeParsedMAUDestinations?_clean_commit` — destination loop;
* §2 `executeParsedFloatMAUCyclesAtPE_clean` — cycle loop;
* §3 `executeParsedFloatMAUsAtPE_run_clean` — expression loop;
* §4 `executeParsedFloatMAUsAtPE_clean_commit` — the stage executor, its
  line-level form `..._of_rows`, and the consistency corollary
  `executeParsedFloatMAUsAtPE_lm1_frame_from_clean` (the existing bank-level
  frame is now a consequence);
* §5 `executeIntegerProducerLineAtPECore_prepared_float_clean`,
  `executeIntegerProducerLineAtPEs_zero_prepared_float_clean` — the PE-0 forms
  inside the integer stage, plus the line-level form
  `executeIntegerProducerLineAtPEs_zero_prepared_float_clean_of_line`;
* §6 `WelcomePEFloatMAUStageLm1Provenance` and its proof;
* §7 `floatEmpty` → row-locality: the four `_floatRows` dispatch theorems and
  the four `_unique_of_floatRows` corollaries, with
  `floatFilter_lm1Free_of_rows` and `matrixRead_notFloatMAU` as the bridges.

No `sorry`, no `admit`, no `native_decide`, no new axioms, and no existing
module is edited by this file.  Neither `LowerBound 2` nor `Optimal` is claimed.
-/

namespace ProofsLean.MNCore

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open Issue
open PEMemory

/-! ## 1. The float-MAU destination loop

`writeParsedMAUDestinations?.writeAll` folds `writeParsedMslMsrDestination?` over
the row's destinations, so the write-level base case of
`WelcomeStageProvenance.lean` §1 applies unchanged. -/

/-- **The float-MAU destination loop is a `.lm1`-free commit.** -/
theorem writeParsedMAUDestinations?_writeAll_clean_commit
    (context : ParsedIntegerContext) (output : IntegerALU.Bus) (flags : BitVec 4)
    (cycle : Fin 4) (directive : ParsedMaskDirective) (hasSingleLineMask : Bool) :
    ∀ (destinations : List ParsedOperand) (files : IntegerRegisterFiles) (bar0 bar1 : BitVec 12)
      (writes : ParsedMAUDestinationWrites),
      (∀ destination ∈ destinations,
        ∀ (bank : PEMemory.Bank) (width : PEMemory.Width),
          ParsedOperand.directDestinationBankWidth? destination = some (bank, width) →
            bank ≠ PEMemory.Bank.lm1) →
      writeParsedMAUDestinations?.writeAll context output flags cycle directive
        hasSingleLineMask destinations files bar0 bar1 = some writes →
      ∃ prepared, writes.files = commitParsedMaskedWrites files prepared ∧
        Lm1FreePreparedWrites prepared := by
  intro destinations
  induction destinations with
  | nil =>
      intro files bar0 bar1 writes noLm1 executed
      rw [writeParsedMAUDestinations?.writeAll] at executed
      obtain rfl := Option.some.inj executed
      exact ⟨[], rfl, lm1FreePreparedWrites_nil⟩
  | cons destination rest ih =>
      intro files bar0 bar1 writes noLm1 executed
      rw [writeParsedMAUDestinations?.writeAll] at executed
      cases lowered : writeParsedMslMsrDestination? files destination
          { context with bar0 := bar0, bar1 := bar1 } output flags cycle directive
          hasSingleLineMask with
      | none =>
          rw [lowered] at executed
          simp at executed
      | some write =>
          rw [lowered] at executed
          obtain ⟨headWrites, head, headFree⟩ :=
            writeParsedMslMsrDestination?_clean_commit files destination
              { context with bar0 := bar0, bar1 := bar1 } output flags cycle directive
              hasSingleLineMask
              (fun bank width static => noLm1 destination (by simp) bank width static)
              write lowered
          obtain ⟨tailWrites, tail, tailFree⟩ := ih write.files _ _ writes
            (fun item member bank width static =>
              noLm1 item (List.mem_cons_of_mem _ member) bank width static) executed
          exact ⟨headWrites ++ tailWrites, by
              rw [tail, head, commitParsedMaskedWrites_append],
            lm1FreePreparedWrites_append headFree tailFree⟩

/-- **The float-MAU destination writer is a `.lm1`-free commit.** -/
theorem writeParsedMAUDestinations?_clean_commit
    (files : IntegerRegisterFiles) (destinations : List ParsedOperand)
    (context : ParsedIntegerContext) (output : IntegerALU.Bus) (flags : BitVec 4)
    (cycle : Fin 4) (directive : ParsedMaskDirective) (hasSingleLineMask : Bool)
    (noLm1 : ∀ destination ∈ destinations,
      ∀ (bank : PEMemory.Bank) (width : PEMemory.Width),
        ParsedOperand.directDestinationBankWidth? destination = some (bank, width) →
          bank ≠ PEMemory.Bank.lm1)
    (writes : ParsedMAUDestinationWrites)
    (executed : writeParsedMAUDestinations? files destinations context output flags cycle
      directive hasSingleLineMask = some writes) :
    ∃ prepared, writes.files = commitParsedMaskedWrites files prepared ∧
      Lm1FreePreparedWrites prepared := by
  rw [writeParsedMAUDestinations?.eq_1] at executed
  exact writeParsedMAUDestinations?_writeAll_clean_commit context output flags cycle directive
    hasSingleLineMask destinations files context.bar0 context.bar1 writes noLm1 executed

/-! ## 2. The float-MAU cycle loop -/

/-- **The float-MAU cycle loop is a `.lm1`-free commit.** -/
theorem executeParsedFloatMAUCyclesAtPE_clean
    (readFiles : IntegerRegisterFiles) (oldSlots : Forwarding.Slots) (expression : ParsedExpr)
    (context : ParsedIntegerContext) (directive : ParsedMaskDirective)
    (hasSingleLineMask : Bool)
    (noLm1 : WelcomeRowHasNoLm1Destination expression) :
    ∀ (cycles : List (Fin 4)) (files : IntegerRegisterFiles) (bar0 bar1 : BitVec 12)
      (outputs : Fin 4 → IntegerALU.Bus) (nextFiles : IntegerRegisterFiles)
      (nextBar0 nextBar1 : BitVec 12) (nextOutputs : Fin 4 → IntegerALU.Bus),
      executeParsedFloatMAUCyclesAtPE readFiles oldSlots expression context directive
        hasSingleLineMask cycles files bar0 bar1 outputs =
        .ok (nextFiles, nextBar0, nextBar1, nextOutputs) →
      ∃ prepared, nextFiles = commitParsedMaskedWrites files prepared ∧
        Lm1FreePreparedWrites prepared := by
  intro cycles
  induction cycles with
  | nil =>
      intro files bar0 bar1 outputs nextFiles nextBar0 nextBar1 nextOutputs executed
      rw [executeParsedFloatMAUCyclesAtPE.eq_1] at executed
      obtain ⟨rfl, rfl, rfl, rfl⟩ := StepResult.ok.inj executed
      exact ⟨[], rfl, lm1FreePreparedWrites_nil⟩
  | cons cycle rest ih =>
      intro files bar0 bar1 outputs nextFiles nextBar0 nextBar1 nextOutputs executed
      rw [executeParsedFloatMAUCyclesAtPE.eq_2] at executed
      dsimp only at executed
      cases cycleStep : executeParsedFloatMAUCycleAtPE readFiles files oldSlots expression
          { context with cycle := cycle, bar0 := bar0, bar1 := bar1 } cycle with
      | failure =>
          rw [cycleStep] at executed
          dsimp only at executed
          simp at executed
      | unknown =>
          rw [cycleStep] at executed
          dsimp only at executed
          simp at executed
      | ok result =>
          obtain ⟨ignored, output, flags⟩ := result
          rw [cycleStep] at executed
          dsimp only at executed
          cases flush : resolveFlushSelection? expression.flush files.maskRegisters cycle with
          | none =>
              rw [flush] at executed
              dsimp only at executed
              simp at executed
          | some flushSelection =>
              rw [flush] at executed
              dsimp only at executed
              cases wrote : writeParsedMAUDestinations? files expression.destinations
                  { context with cycle := cycle, bar0 := bar0, bar1 := bar1 }
                  (parsedOutputAfterFlush flushSelection output) flags cycle directive
                  hasSingleLineMask with
              | none =>
                  rw [wrote] at executed
                  dsimp only at executed
                  simp at executed
              | some writes =>
                  rw [wrote] at executed
                  obtain ⟨headWrites, head, headFree⟩ :=
                    writeParsedMAUDestinations?_clean_commit files expression.destinations
                      { context with cycle := cycle, bar0 := bar0, bar1 := bar1 }
                      (parsedOutputAfterFlush flushSelection output) flags cycle directive
                      hasSingleLineMask noLm1 writes wrote
                  obtain ⟨tailWrites, tail, tailFree⟩ := ih writes.files writes.bar0 writes.bar1 _
                    nextFiles nextBar0 nextBar1 nextOutputs executed
                  exact ⟨headWrites ++ tailWrites, by
                      rw [tail, head, commitParsedMaskedWrites_append],
                    lm1FreePreparedWrites_append headFree tailFree⟩

/-! ## 3. The float-MAU expression loop -/

/-- **The float-MAU expression loop is a `.lm1`-free commit.** -/
theorem executeParsedFloatMAUsAtPE_run_clean
    (readFiles : IntegerRegisterFiles) (oldSlots : Forwarding.Slots)
    (context : ParsedIntegerContext) (directive : ParsedMaskDirective)
    (hasSingleLineMask : Bool) :
    ∀ (remaining : List ParsedExpr),
      (∀ expression ∈ remaining, WelcomeRowHasNoLm1Destination expression) →
      ∀ (files : IntegerRegisterFiles) (bar0 bar1 : BitVec 12)
        (outputs : Fin 4 → IntegerALU.Bus) (nextFiles : IntegerRegisterFiles)
        (nextBar0 nextBar1 : BitVec 12) (nextOutputs : Fin 4 → IntegerALU.Bus),
        executeParsedFloatMAUsAtPE.run readFiles oldSlots context directive hasSingleLineMask
          remaining files bar0 bar1 outputs = .ok (nextFiles, nextBar0, nextBar1, nextOutputs) →
        ∃ prepared, nextFiles = commitParsedMaskedWrites files prepared ∧
          Lm1FreePreparedWrites prepared := by
  intro remaining
  induction remaining with
  | nil =>
      intro noLm1 files bar0 bar1 outputs nextFiles nextBar0 nextBar1 nextOutputs executed
      rw [executeParsedFloatMAUsAtPE.run] at executed
      obtain ⟨rfl, rfl, rfl, rfl⟩ := StepResult.ok.inj executed
      exact ⟨[], rfl, lm1FreePreparedWrites_nil⟩
  | cons expression rest ih =>
      intro noLm1 files bar0 bar1 outputs nextFiles nextBar0 nextBar1 nextOutputs executed
      rw [executeParsedFloatMAUsAtPE.run] at executed
      split at executed
      · simp at executed
      · simp at executed
      · rename_i middleFiles middleBar0 middleBar1 middleOutputs ran
        obtain ⟨headWrites, head, headFree⟩ :=
          executeParsedFloatMAUCyclesAtPE_clean readFiles oldSlots expression context directive
            hasSingleLineMask (noLm1 expression (by simp)) [0, 1, 2, 3] files bar0 bar1
            (fun _ => ⟨0, 0⟩) middleFiles middleBar0 middleBar1 middleOutputs ran
        obtain ⟨tailWrites, tail, tailFree⟩ := ih
          (fun other member => noLm1 other (List.mem_cons_of_mem _ member))
          middleFiles middleBar0 middleBar1 middleOutputs nextFiles nextBar0 nextBar1 nextOutputs
          executed
        exact ⟨headWrites ++ tailWrites, by
            rw [tail, head, commitParsedMaskedWrites_append],
          lm1FreePreparedWrites_append headFree tailFree⟩

/-! ## 4. The float-MAU stage executor -/

/-- **The float-MAU stage is a `.lm1`-free commit.**  The hypothesis is exactly
the row-locality of the stage's producer filter: every row the executor runs has
no `.lm1` destination operand. -/
theorem executeParsedFloatMAUsAtPE_clean_commit
    (readState currentFiles : IntegerRegisterFiles) (oldSlots : Forwarding.Slots)
    (context : ParsedIntegerContext) (expressions : List ParsedExpr)
    (directive : ParsedMaskDirective) (hasSingleLineMask : Bool)
    (noLm1 : ∀ expression ∈ expressions.filter parsedExprIsSupportedFloatMAUProducer,
      WelcomeRowHasNoLm1Destination expression)
    (nextFiles : IntegerRegisterFiles) (nextBar0 nextBar1 : BitVec 12)
    (nextOutputs : Fin 4 → IntegerALU.Bus) (hasMAUProducer : Bool)
    (executed : executeParsedFloatMAUsAtPE readState currentFiles oldSlots context expressions
      directive hasSingleLineMask =
      .ok (nextFiles, nextBar0, nextBar1, nextOutputs, hasMAUProducer)) :
    ∃ prepared, nextFiles = commitParsedMaskedWrites currentFiles prepared ∧
      Lm1FreePreparedWrites prepared := by
  rw [executeParsedFloatMAUsAtPE.eq_1] at executed
  split at executed
  · simp at executed
  · simp at executed
  · rename_i files bar0 bar1 outputs ran
    obtain ⟨runWrites, runCommit, runFree⟩ := executeParsedFloatMAUsAtPE_run_clean readState
      oldSlots context directive hasSingleLineMask _ noLm1 currentFiles context.bar0
      context.bar1 _ files bar0 bar1 outputs ran
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := StepResult.ok.inj executed
    exact ⟨runWrites, runCommit, runFree⟩

/-- **The bank-level frame as a consequence.**  The existing frame
`executeParsedFloatMAUsAtPE_lm1_free` is implied by the write-list-level
statement: a `.lm1`-free commit leaves the `.lm1` bank alone.  This is the
consistency check tying the new statement to the frame it strengthens. -/
theorem executeParsedFloatMAUsAtPE_lm1_frame_from_clean
    (readState currentFiles : IntegerRegisterFiles) (oldSlots : Forwarding.Slots)
    (context : ParsedIntegerContext) (expressions : List ParsedExpr)
    (directive : ParsedMaskDirective) (hasSingleLineMask : Bool)
    (noLm1 : ∀ expression ∈ expressions.filter parsedExprIsSupportedFloatMAUProducer,
      WelcomeRowHasNoLm1Destination expression)
    (nextFiles : IntegerRegisterFiles) (nextBar0 nextBar1 : BitVec 12)
    (nextOutputs : Fin 4 → IntegerALU.Bus) (hasMAUProducer : Bool)
    (executed : executeParsedFloatMAUsAtPE readState currentFiles oldSlots context expressions
      directive hasSingleLineMask =
      .ok (nextFiles, nextBar0, nextBar1, nextOutputs, hasMAUProducer)) :
    nextFiles.lm1 = currentFiles.lm1 := by
  obtain ⟨prepared, commitEq, free⟩ :=
    executeParsedFloatMAUsAtPE_clean_commit readState currentFiles oldSlots context expressions
      directive hasSingleLineMask noLm1 nextFiles nextBar0 nextBar1 nextOutputs hasMAUProducer
      executed
  rw [commitEq]
  exact commitParsedMaskedWrites_lm1_frame currentFiles prepared free

/-! ## 5. The float-MAU list inside the integer stage

`executeIntegerProducerLineAtPECore` runs the four-cycle integer/matrix-read
stage and then `executeParsedFloatMAUsAtPE` on the whole (unfiltered) line.  The
next two lemmas are the float-carrying companions of
`executeIntegerProducerLineAtPECore_prepared_float` /
`executeIntegerProducerLineAtPEs_zero_prepared_float`
(`WelcomeWriterDispatch.lean` §5), with the float list's freeness added. -/

/-- **The integer core commits the prepared list and a `.lm1`-free float list.** -/
theorem executeIntegerProducerLineAtPECore_prepared_float_clean
    (expressions : List ParsedExpr) (state next : State) (pe : PEId)
    (noLm1 : ∀ expression ∈ expressions.filter parsedExprIsSupportedFloatMAUProducer,
      WelcomeRowHasNoLm1Destination expression)
    (executed : executeIntegerProducerLineAtPECore expressions state pe = .ok next) :
    ∃ intWrites floatWrites slots bars,
      welcomeIntegerPrep state pe expressions = .ok (intWrites, slots, bars) ∧
      next.peRegisters pe =
        commitParsedMaskedWrites (state.peRegisters pe) (intWrites ++ floatWrites) ∧
      Lm1FreePreparedWrites floatWrites := by
  rw [executeIntegerProducerLineAtPECore.eq_1] at executed
  dsimp only at executed
  split at executed
  · simp at executed
  · simp at executed
  · rename_i registers integerSlots barUpdates fourCycle
    split at executed
    · simp at executed
    · simp at executed
    · rename_i registersWithFloat floatBar0 floatBar1 floatOutputs hasMAUProducer floatMAU
      unfold parsedIntegerMatrixReadLineFourCycleStep at fourCycle
      split at fourCycle
      · simp at fourCycle
      · simp at fourCycle
      · rename_i intWrites preparedSlots preparedBars prepared
        simp only [StepResult.ok.injEq, Prod.mk.injEq] at fourCycle
        obtain ⟨commitRegsEq, -, -⟩ := fourCycle
        obtain ⟨floatWrites, floatCommitEq, floatFree⟩ :=
          executeParsedFloatMAUsAtPE_clean_commit (state.peRegisters pe) registers _ _ expressions
            _ _ noLm1 registersWithFloat floatBar0 floatBar1 floatOutputs hasMAUProducer floatMAU
        refine ⟨intWrites, floatWrites, preparedSlots, preparedBars, prepared, ?_, floatFree⟩
        simp only [updateSupportedPELineForwarding] at executed
        split at executed
        · simp at executed
        · simp at executed
        · simp only [StepResult.ok.injEq] at executed
          subst executed
          show (if pe = pe then registersWithFloat else state.peRegisters pe) =
            commitParsedMaskedWrites (state.peRegisters pe) (intWrites ++ floatWrites)
          rw [ite_eq_left rfl, floatCommitEq, ← commitRegsEq,
            ← commitParsedMaskedWrites_append]

/-- **The per-PE walk at PE 0 commits the prepared list and a `.lm1`-free float
list.**  The other 4095 PEs never revisit PE 0, so this is the PE 0 half of the
walk at the all-zero state. -/
theorem executeIntegerProducerLineAtPEs_zero_prepared_float_clean
    (expressions : List ParsedExpr) (next : State)
    (noLm1 : ∀ expression ∈ expressions.filter parsedExprIsSupportedFloatMAUProducer,
      WelcomeRowHasNoLm1Destination expression)
    (executed : executeIntegerProducerLineAtPEs expressions (List.finRange 4096)
      (welcomeInitialState welcomeZeroWords) = .ok next) :
    ∃ intWrites floatWrites slots bars,
      welcomeIntegerPrep (welcomeInitialState welcomeZeroWords) welcomePE expressions =
        .ok (intWrites, slots, bars) ∧
      next.peRegisters welcomePE =
        commitParsedMaskedWrites welcomeZeroFiles (intWrites ++ floatWrites) ∧
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
    have coreExecuted : executeIntegerProducerLineAtPECore expressions
        (welcomeInitialState welcomeZeroWords) welcomePE = .ok nextPEs := by
      unfold executeIntegerProducerLineAtPE at headExecuted
      split at headExecuted
      · simp at headExecuted
      · exact headExecuted
    obtain ⟨intWrites, floatWrites, slots, bars, intPrep, intCommit, floatFree⟩ :=
      executeIntegerProducerLineAtPECore_prepared_float_clean expressions
        (welcomeInitialState welcomeZeroWords) nextPEs welcomePE noLm1 coreExecuted
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

/-- **The line-level form of the executor statement.**  If *every* row of the
list has no `.lm1` destination operand, then the float-MAU stage's write list is
`.lm1`-free and commits the file it was run on. -/
theorem executeParsedFloatMAUsAtPE_clean_commit_of_rows
    (readState currentFiles : IntegerRegisterFiles) (oldSlots : Forwarding.Slots)
    (context : ParsedIntegerContext) (expressions : List ParsedExpr)
    (directive : ParsedMaskDirective) (hasSingleLineMask : Bool)
    (allRows : ∀ expression ∈ expressions, WelcomeRowHasNoLm1Destination expression)
    (nextFiles : IntegerRegisterFiles) (nextBar0 nextBar1 : BitVec 12)
    (nextOutputs : Fin 4 → IntegerALU.Bus) (hasMAUProducer : Bool)
    (executed : executeParsedFloatMAUsAtPE readState currentFiles oldSlots context expressions
      directive hasSingleLineMask =
      .ok (nextFiles, nextBar0, nextBar1, nextOutputs, hasMAUProducer)) :
    ∃ prepared, nextFiles = commitParsedMaskedWrites currentFiles prepared ∧
      Lm1FreePreparedWrites prepared :=
  executeParsedFloatMAUsAtPE_clean_commit readState currentFiles oldSlots context expressions
    directive hasSingleLineMask
    (fun expression member => allRows expression (List.mem_of_mem_filter member))
    nextFiles nextBar0 nextBar1 nextOutputs hasMAUProducer executed

/-- **The line-level form of the PE 0 statement.**  If every row of the `.pe` line
has no `.lm1` destination operand, then the integer stage's PE 0 file is the
commit of the prepared list followed by a `.lm1`-free float-MAU list.  No
`floatEmpty` hypothesis is needed. -/
theorem executeIntegerProducerLineAtPEs_zero_prepared_float_clean_of_line
    (expressions : List NormalizedExpr) (next : State)
    (rows : ∀ expression ∈ expressions.map NormalizedExpr.toParsed,
      WelcomeRowHasNoLm1Destination expression)
    (executed : executeIntegerProducerLineAtPEs (welcomePEWalkFilter expressions)
      (List.finRange 4096) (welcomeInitialState welcomeZeroWords) = .ok next) :
    ∃ intWrites floatWrites slots bars,
      welcomeIntegerPrep (welcomeInitialState welcomeZeroWords) welcomePE
        (welcomePEWalkFilter expressions) = .ok (intWrites, slots, bars) ∧
      next.peRegisters welcomePE =
        commitParsedMaskedWrites welcomeZeroFiles (intWrites ++ floatWrites) ∧
      Lm1FreePreparedWrites floatWrites := by
  refine executeIntegerProducerLineAtPEs_zero_prepared_float_clean
    (welcomePEWalkFilter expressions) next ?_ executed
  intro expression member
  rw [welcomePEWalkFilter_float] at member
  exact rows expression (List.mem_of_mem_filter member)

/-! ## 6. The stage-level proposition -/

/-- **The stage-level `.lm1` provenance proposition for the float-MAU stage.** -/
def WelcomePEFloatMAUStageLm1Provenance : Prop :=
  ∀ (readState currentFiles : IntegerRegisterFiles) (oldSlots : Forwarding.Slots)
    (context : ParsedIntegerContext) (expressions : List ParsedExpr)
    (directive : ParsedMaskDirective) (hasSingleLineMask : Bool),
    (∀ expression ∈ expressions.filter parsedExprIsSupportedFloatMAUProducer,
      WelcomeRowHasNoLm1Destination expression) →
    ∀ (nextFiles : IntegerRegisterFiles) (nextBar0 nextBar1 : BitVec 12)
      (nextOutputs : Fin 4 → IntegerALU.Bus) (hasMAUProducer : Bool),
      executeParsedFloatMAUsAtPE readState currentFiles oldSlots context expressions directive
        hasSingleLineMask = .ok (nextFiles, nextBar0, nextBar1, nextOutputs, hasMAUProducer) →
      ∃ writes, nextFiles = commitParsedMaskedWrites currentFiles writes ∧
        Lm1FreePreparedWrites writes

/-- **The float-MAU stage's write-list-level `.lm1` provenance.** -/
theorem welcomePEFloatMAUStageLm1Provenance : WelcomePEFloatMAUStageLm1Provenance :=
  fun readState currentFiles oldSlots context expressions directive hasSingleLineMask noLm1
    nextFiles nextBar0 nextBar1 nextOutputs hasMAUProducer executed =>
    executeParsedFloatMAUsAtPE_clean_commit readState currentFiles oldSlots context expressions
      directive hasSingleLineMask noLm1 nextFiles nextBar0 nextBar1 nextOutputs hasMAUProducer
      executed

/-! ## 7. Replacing `floatEmpty` by row-locality

`WelcomeWriterDispatch.lean` §6 takes `floatEmpty` — no float-MAU row at all — in
the four non-float dispatch theorems, so that the integer stage's list is exactly
`welcomeIntegerPrep`'s.  With the provenance above the integer stage's list can be
split as `intWrites ++ floatWrites` with the float half `.lm1`-free, which is all
the assembly needs: an `.lm1`-free suffix does not change the shape
(`lm1WritesShape_append_of_only`).

The four `_floatRows` theorems below are the dispatch theorems with `floatEmpty`
replaced by the row-local hypothesis on the float-MAU filter; the four
`_unique_of_floatRows` corollaries then drop even that, deriving it from "every
row other than `e` has no `.lm1` destination" plus the writer's own kind. -/

/-- **An `.lm1`-free suffix leaves the shape to the prefix.** -/
theorem lm1WritesShape_append_free_suffix (first second : List PreparedParsedMaskedWrite)
    (shape : Lm1WritesShape first) (free : Lm1FreePreparedWrites second) :
    Lm1WritesShape (first ++ second) :=
  lm1WritesShape_append_of_only first second (fun write member => free write member) shape

/-- **The plain-writer dispatch with a `.lm1`-free float list.**  This is
`welcomePEWriteShape_of_plainWriter_dispatch` with `floatEmpty` replaced by the
row-local hypothesis on the float-MAU filter. -/
theorem welcomePEWriteShape_of_plainWriter_dispatch_floatRows
    (expressions : List NormalizedExpr)
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
    (plain : parsedExprIsPlainIntegerALU e = true)
    (floatFreeRows : ∀ expression ∈ (expressions.map NormalizedExpr.toParsed).filter
        parsedExprIsSupportedFloatMAUProducer, WelcomeRowHasNoLm1Destination expression)
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
  have splitWalk : (welcomePEWalkFilter expressions).filter
      parsedExprIsIntegerMatrixReadStageInput = before ++ e :: after := by
    rw [welcomePEWalkFilter_integer]
    exact split
  have floatFreeWalk : ∀ expression ∈ (welcomePEWalkFilter expressions).filter
      parsedExprIsSupportedFloatMAUProducer, WelcomeRowHasNoLm1Destination expression := by
    intro expression member
    exact floatFreeRows expression (by rw [welcomePEWalkFilter_float] at member; exact member)
  obtain ⟨intWrites, floatWrites, intSlots, intBars, intPrep, intCommit, floatFree⟩ :=
    executeIntegerProducerLineAtPEs_zero_prepared_float_clean (welcomePEWalkFilter expressions)
      nextPEs floatFreeWalk walkExecuted
  obtain ⟨rowWrites, rowSlots, rowBars, rowPrep, intWritesEq⟩ :=
    welcomeIntegerPrep_single_writer (welcomeInitialState welcomeZeroWords)
      (welcomePEWalkFilter expressions) before after e splitWalk skipBefore skipAfter
      intWrites intSlots intBars intPrep
  have maskEq : ((welcomePEWalkFilter expressions).filter
      parsedExprIsIntegerMatrixReadStageInput).any parsedExprHasSingleLineWriteMask =
      parsedExprHasSingleLineWriteMask e := by
    rw [welcomePEWalkFilter_integer]
    exact flagEq
  rw [maskEq] at rowPrep
  have intShape : Lm1WritesShape intWrites := by
    rw [intWritesEq]
    exact plainRow_lm1_shape_of_linePrep e plain notDouble nodup _
      rowWrites rowSlots rowBars rowPrep
  have combinedShape : Lm1WritesShape (intWrites ++ floatWrites) :=
    lm1WritesShape_append_free_suffix intWrites floatWrites intShape floatFree
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
  refine ⟨(intWrites ++ floatWrites) ++ mslWrites ++ reluWrites ++ blockWrites ++ matrixWrites
      ++ l1Writes,
    executeIntegerProducerInstructionLine_pe_commit_split nextPEs nextMsl nextRelu
      nextBlockFloat afterMatrix nextShared nextBroadcast next peEq (intWrites ++ floatWrites)
      mslWrites reluWrites blockWrites matrixWrites l1Writes intCommit mslCommit reluCommit
      blockCommit matrixCommit sharedFrame l1Commit, ?_⟩
  exact lm1WritesShape_of_six_first (intWrites ++ floatWrites) mslWrites reluWrites blockWrites
    matrixWrites l1Writes combinedShape mslFree reluFree blockFree matrixFree l1Free

/-- **The `.matrixRead`-writer dispatch with a `.lm1`-free float list.** -/
theorem welcomePEWriteShape_of_matrixReadWriter_dispatch_floatRows
    (expressions : List NormalizedExpr)
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
        some (PEMemory.Bank.lm1, v) → v = staticW)
    (floatFreeRows : ∀ expression ∈ (expressions.map NormalizedExpr.toParsed).filter
        parsedExprIsSupportedFloatMAUProducer, WelcomeRowHasNoLm1Destination expression)
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
  have splitWalk : (welcomePEWalkFilter expressions).filter
      parsedExprIsIntegerMatrixReadStageInput = before ++ e :: after := by
    rw [welcomePEWalkFilter_integer]
    exact split
  have floatFreeWalk : ∀ expression ∈ (welcomePEWalkFilter expressions).filter
      parsedExprIsSupportedFloatMAUProducer, WelcomeRowHasNoLm1Destination expression := by
    intro expression member
    exact floatFreeRows expression (by rw [welcomePEWalkFilter_float] at member; exact member)
  obtain ⟨intWrites, floatWrites, intSlots, intBars, intPrep, intCommit, floatFree⟩ :=
    executeIntegerProducerLineAtPEs_zero_prepared_float_clean (welcomePEWalkFilter expressions)
      nextPEs floatFreeWalk walkExecuted
  obtain ⟨rowWrites, rowSlots, rowBars, rowPrep, intWritesEq⟩ :=
    welcomeIntegerPrep_single_writer (welcomeInitialState welcomeZeroWords)
      (welcomePEWalkFilter expressions) before after e splitWalk skipBefore skipAfter
      intWrites intSlots intBars intPrep
  have intShape : Lm1WritesShape intWrites := by
    rw [intWritesEq]
    exact matrixReadRow_lm1_shape e precision sideY width row op sources welcomeZeroControl
      _ _ false staticW nodup staticWidth rowWrites rowSlots rowBars rowPrep
  have combinedShape : Lm1WritesShape (intWrites ++ floatWrites) :=
    lm1WritesShape_append_free_suffix intWrites floatWrites intShape floatFree
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
  refine ⟨(intWrites ++ floatWrites) ++ mslWrites ++ reluWrites ++ blockWrites ++ matrixWrites
      ++ l1Writes,
    executeIntegerProducerInstructionLine_pe_commit_split nextPEs nextMsl nextRelu
      nextBlockFloat afterMatrix nextShared nextBroadcast next peEq (intWrites ++ floatWrites)
      mslWrites reluWrites blockWrites matrixWrites l1Writes intCommit mslCommit reluCommit
      blockCommit matrixCommit sharedFrame l1Commit, ?_⟩
  exact lm1WritesShape_of_six_first (intWrites ++ floatWrites) mslWrites reluWrites blockWrites
    matrixWrites l1Writes combinedShape mslFree reluFree blockFree matrixFree l1Free

/-- **The matrix-MAU-writer dispatch with a `.lm1`-free float list.** -/
theorem welcomePEWriteShape_of_matrixMAUWriter_dispatch_floatRows
    (expressions : List NormalizedExpr)
    (e : ParsedExpr)
    (mmau : parsedExprIsMatrixMAUProducer e = true)
    (nodup : (e.toIssueExpr 0).writeBanks.Nodup)
    (mauFilter : (expressions.map NormalizedExpr.toParsed).filter
      parsedExprIsMatrixMAUProducer = [e])
    (intFree : ∀ expression ∈ (expressions.map NormalizedExpr.toParsed).filter
        parsedExprIsIntegerMatrixReadStageInput, WelcomeRowHasNoLm1Destination expression)
    (floatFreeRows : ∀ expression ∈ (expressions.map NormalizedExpr.toParsed).filter
        parsedExprIsSupportedFloatMAUProducer, WelcomeRowHasNoLm1Destination expression)
    (middleFree : WelcomePEMiddleStageLm1Free expressions)
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
  obtain ⟨matrixWrites, matrixCommit, matrixShape⟩ :=
    executeParsedMatrixMAUAndWrites_shape_of_filter_singleton nextBlockFloat afterMatrix
      (expressions.map NormalizedExpr.toParsed) e
      (expressions.any (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed))
      (expressions.any (parsedExprHasSingleLineWriteMask ∘ NormalizedExpr.toParsed))
      mauFilter nodup matrixExecuted
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
  refine ⟨(intWrites ++ floatWrites) ++ mslWrites ++ reluWrites ++ blockWrites ++ matrixWrites
      ++ l1Writes,
    executeIntegerProducerInstructionLine_pe_commit_split nextPEs nextMsl nextRelu
      nextBlockFloat afterMatrix nextShared nextBroadcast next peEq (intWrites ++ floatWrites)
      mslWrites reluWrites blockWrites matrixWrites l1Writes intCommit mslCommit reluCommit
      blockCommit matrixCommit sharedFrame l1Commit, ?_⟩
  exact lm1WritesShape_of_six_fifth (intWrites ++ floatWrites) mslWrites reluWrites blockWrites
    matrixWrites l1Writes combinedFree mslFree reluFree blockFree matrixShape l1Free

/-- **The `.l1bm`-broadcast-writer dispatch with a `.lm1`-free float list.** -/
theorem welcomePEWriteShape_of_l1bmWriter_dispatch_floatRows
    (expressions : List NormalizedExpr)
    (e : ParsedExpr) (access : ParsedL1ToPEAccess) (memoryAccess : Access)
    (negated extended rounded : Bool) (mask : Option ParsedMask) (w : PEMemory.Width)
    (lowered : lowerParsedL1ToPE? e = some access)
    (destinations : access.destinations =
      [ParsedOperand.mem memoryAccess negated extended rounded mask])
    (static : ParsedOperand.directDestinationBankWidth?
      (ParsedOperand.mem memoryAccess negated extended rounded mask) =
      some (PEMemory.Bank.lm1, w))
    (l1Filter : (expressions.map NormalizedExpr.toParsed).filter
      parsedExprIsL1ToPEProducer = [e])
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

/-! ### 7.1 Row-locality suffices

For each of the four writer kinds the writer is not a float-MAU producer, so
every float-MAU row of the line is a row other than `e` and the row-local
statement supplies the float filter's freeness. -/

/-- A `.matrixRead` row is never a float-MAU producer. -/
theorem matrixRead_notFloatMAU (expression : ParsedExpr) (precision : ParsedPrecision)
    (op : expression.op = .matrixRead precision) :
    parsedExprIsSupportedFloatMAUProducer expression = false := by
  obtain ⟨operation, sources, destinations, flush, text⟩ := expression
  subst op
  simp [parsedExprIsSupportedFloatMAUProducer]

/-- **The float-MAU filter's freeness from row-locality.**  If every row of the
line other than `e` has no `.lm1` destination and `e` is not a float-MAU
producer, the line's float-MAU filter is `.lm1`-free. -/
theorem floatFilter_lm1Free_of_rows
    (expressions : List NormalizedExpr) (e : ParsedExpr)
    (rows : ∀ expression ∈ expressions.map NormalizedExpr.toParsed, expression ≠ e →
      WelcomeRowHasNoLm1Destination expression)
    (notFloat : parsedExprIsSupportedFloatMAUProducer e = false) :
    ∀ expression ∈ (expressions.map NormalizedExpr.toParsed).filter
      parsedExprIsSupportedFloatMAUProducer, WelcomeRowHasNoLm1Destination expression := by
  intro expression member
  have lineMem : expression ∈ expressions.map NormalizedExpr.toParsed :=
    List.mem_of_mem_filter member
  by_cases same : expression = e
  · subst same
    have keeps := (List.mem_filter.mp member).2
    rw [notFloat] at keeps
    exact absurd keeps (by simp)
  · exact rows expression lineMem same

/-- **The plain-writer unique dispatch, without `floatEmpty`.** -/
theorem welcomePEWriteShape_of_plainWriter_unique_of_floatRows
    (expressions : List NormalizedExpr)
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
    (plain : parsedExprIsPlainIntegerALU e = true)
    (rows : ∀ expression ∈ expressions.map NormalizedExpr.toParsed, expression ≠ e →
      WelcomeRowHasNoLm1Destination expression) :
    WelcomePEWriteShape expressions := by
  obtain ⟨-, -, mslFalse, reluFalse, blockFalse, -, -, matrixMAUFalse, -, l1False, -, -, -⟩ :=
    parsedExprIsPlainIntegerALU_facts e plain
  exact welcomePEWriteShape_of_plainWriter_dispatch_floatRows expressions before after e split
    skipBefore skipAfter flagEq notDouble nodup plain
    (floatFilter_lm1Free_of_rows expressions e rows
      (parsedExprIsPlainIntegerALU_notFloatMAU e plain))
    (welcomePEMiddleStageLm1Free_of_rows expressions e rows mslFalse reluFalse blockFalse)
    (welcomePEMatrixMAUStageLm1Free_of_rows expressions e rows matrixMAUFalse)
    (welcomePEL1StageLm1Free_of_rows expressions e rows l1False)

/-- **The `.matrixRead`-writer unique dispatch, without `floatEmpty`.** -/
theorem welcomePEWriteShape_of_matrixReadWriter_unique_of_floatRows
    (expressions : List NormalizedExpr)
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
        some (PEMemory.Bank.lm1, v) → v = staticW)
    (rows : ∀ expression ∈ expressions.map NormalizedExpr.toParsed, expression ≠ e →
      WelcomeRowHasNoLm1Destination expression) :
    WelcomePEWriteShape expressions := by
  obtain ⟨mslFalse, reluFalse, blockFalse, matrixMAUFalse, l1False⟩ :=
    matrixRead_parsedExpr_predicates e precision op
  exact welcomePEWriteShape_of_matrixReadWriter_dispatch_floatRows expressions before after e
    split skipBefore skipAfter precision sideY width row op sources staticW nodup staticWidth
    (floatFilter_lm1Free_of_rows expressions e rows
      (matrixRead_notFloatMAU e precision op))
    (welcomePEMiddleStageLm1Free_of_rows expressions e rows mslFalse reluFalse blockFalse)
    (welcomePEMatrixMAUStageLm1Free_of_rows expressions e rows matrixMAUFalse)
    (welcomePEL1StageLm1Free_of_rows expressions e rows l1False)

/-- **The matrix-MAU-writer unique dispatch, without `floatEmpty`.** -/
theorem welcomePEWriteShape_of_matrixMAUWriter_unique_of_floatRows
    (expressions : List NormalizedExpr)
    (e : ParsedExpr)
    (mmau : parsedExprIsMatrixMAUProducer e = true)
    (nodup : (e.toIssueExpr 0).writeBanks.Nodup)
    (mauFilter : (expressions.map NormalizedExpr.toParsed).filter
      parsedExprIsMatrixMAUProducer = [e])
    (rows : ∀ expression ∈ expressions.map NormalizedExpr.toParsed, expression ≠ e →
      WelcomeRowHasNoLm1Destination expression) :
    WelcomePEWriteShape expressions := by
  obtain ⟨-, mslFalse, blockFalse, reluFalse, -, l1False, floatFalse, intStageFalse⟩ :=
    matrixMAU_parsedExpr_predicates e mmau
  have intFree : ∀ expression ∈ (expressions.map NormalizedExpr.toParsed).filter
      parsedExprIsIntegerMatrixReadStageInput, WelcomeRowHasNoLm1Destination expression :=
    fun expression member => rows expression (List.mem_of_mem_filter member) (by
      intro same
      subst same
      have keeps := (List.mem_filter.mp member).2
      rw [intStageFalse] at keeps
      exact absurd keeps (by simp))
  exact welcomePEWriteShape_of_matrixMAUWriter_dispatch_floatRows expressions e mmau nodup
    mauFilter intFree (floatFilter_lm1Free_of_rows expressions e rows floatFalse)
    (welcomePEMiddleStageLm1Free_of_rows expressions e rows mslFalse reluFalse blockFalse)
    (welcomePEL1StageLm1Free_of_rows expressions e rows l1False)

/-- **The `.l1bm`-broadcast-writer unique dispatch, without `floatEmpty`.** -/
theorem welcomePEWriteShape_of_l1bmWriter_unique_of_floatRows
    (expressions : List NormalizedExpr)
    (e : ParsedExpr) (access : ParsedL1ToPEAccess) (memoryAccess : Access)
    (negated extended rounded : Bool) (mask : Option ParsedMask) (w : PEMemory.Width)
    (lowered : lowerParsedL1ToPE? e = some access)
    (destinations : access.destinations =
      [ParsedOperand.mem memoryAccess negated extended rounded mask])
    (static : ParsedOperand.directDestinationBankWidth?
      (ParsedOperand.mem memoryAccess negated extended rounded mask) =
      some (PEMemory.Bank.lm1, w))
    (l1Filter : (expressions.map NormalizedExpr.toParsed).filter
      parsedExprIsL1ToPEProducer = [e])
    (rows : ∀ expression ∈ expressions.map NormalizedExpr.toParsed, expression ≠ e →
      WelcomeRowHasNoLm1Destination expression) :
    WelcomePEWriteShape expressions := by
  obtain ⟨intStageFalse, floatFalse, -, mslFalse, reluFalse, blockFalse, matrixMAUFalse, -, -⟩ :=
    l1bmBroadcast_parsedExpr_predicates e access lowered
  have intFree : ∀ expression ∈ (expressions.map NormalizedExpr.toParsed).filter
      parsedExprIsIntegerMatrixReadStageInput, WelcomeRowHasNoLm1Destination expression :=
    fun expression member => rows expression (List.mem_of_mem_filter member) (by
      intro same
      subst same
      have keeps := (List.mem_filter.mp member).2
      rw [intStageFalse] at keeps
      exact absurd keeps (by simp))
  exact welcomePEWriteShape_of_l1bmWriter_dispatch_floatRows expressions e access memoryAccess
    negated extended rounded mask w lowered destinations static l1Filter intFree
    (floatFilter_lm1Free_of_rows expressions e rows floatFalse)
    (welcomePEMiddleStageLm1Free_of_rows expressions e rows mslFalse reluFalse blockFalse)
    (welcomePEMatrixMAUStageLm1Free_of_rows expressions e rows matrixMAUFalse)

end ProofsLean.MNCore
