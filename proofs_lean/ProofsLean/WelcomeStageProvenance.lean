import ProofsLean.WelcomeStageCommit
import ProofsLean.WelcomeIntegerProvenance
import ProofsLean.WelcomeMatrixMAUCommit

/-! # Write-list-level `.lm1` provenance for the five middle stages

`WelcomeAssembly.lean` reduces the line-level `.lm1` argument to per-stage
provenance obligations: if no row of the line names bank `.lm1`, no stage may
prepare an `.lm1` write.  The integer stage already has this as
`welcomeIntegerPrep_lm1_free` (`WelcomeIntegerProvenance.lean` §1); the five
middle stages — MSL/MSR, float-relu, block-float, matrix-MAU/write and
L1BM-to-PE — only had *bank-level* frames
(`welcomePEStageLm1Frame`, `WelcomeLm1FrameResidual.lean`).

This module states and proves the write-list-level companions.  Each stage
executor returns a state, not the list of writes it prepared, so the precise
statement is the strengthened commit form: **there is a write list that commits
the outgoing PE 0 register file from the incoming one and every write in it is
`.lm1`-free.**  For a stage `S` whose producer filter is `f`, the hypothesis is
exactly `∀ e ∈ expressions.filter f, WelcomeRowHasNoLm1Destination e`.

The proofs mirror the commit inductions of `WelcomeStageCommit.lean` /
`WelcomeMatrixMAUCommit.lean` — per-destination writer, destination loop, cycle
loop, per-PE step, PE walk and family filter — carrying the list predicate
`Lm1FreePreparedWrites` as an extra conjunct.  The per-destination base cases
are new: the bank-level halves
(`writeParsedMslMsrDestination?_lm1_of_ne`,
`writeParsedL1ToPEDestination?_lm1_of_ne`) only say that the resulting file's
`.lm1` bank is unchanged, which does not exclude an `.lm1` write whose mask
gates it off; the write itself has to be inspected.

## Status

* `WelcomePEMslMsrStageLm1Provenance` — proved (§1);
* `WelcomePEFloatReluStageLm1Provenance` — proved (§2);
* `WelcomePEBlockFloatStageLm1Provenance` — proved (§3);
* `WelcomePEL1ToPEStageLm1Provenance` — proved (§4);
* `WelcomePEMatrixMAUStageLm1Provenance` — proved (§5);
* `WelcomePEStageLm1ProvenanceForm` — the conjunction of the five (§6).

Every stage statement has the form

`∃ writes, next.peRegisters welcomePE = commitParsedMaskedWrites (… ) writes ∧
  Lm1FreePreparedWrites writes`,

and `Lm1FreePreparedWrites writes` is definitionally
`∀ w ∈ writes, PreparedParsedMaskedWrite.isLm1Write w = false`
(`lm1FreePreparedWrites_iff`).

No `sorry`, no `admit`, no `native_decide`, no new axioms, and no existing
module is edited by this file.  Neither `LowerBound 2` nor `Optimal` is claimed.
-/

namespace ProofsLean.MNCore

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

open Issue
open PEMemory

/-! ## 0. The list predicate and the `.lm1` bank test -/

/-- A prepared write list is `.lm1`-free when none of its writes targets bank
`.lm1`.  This is the `∀ w ∈ writes, PreparedParsedMaskedWrite.isLm1Write w =
false` form of the stage provenance. -/
def Lm1FreePreparedWrites (writes : List PreparedParsedMaskedWrite) : Prop :=
  ∀ write ∈ writes, PreparedParsedMaskedWrite.isLm1Write write = false

/-- The predicate is definitionally the requested `∀ w ∈ writes, … = false`. -/
theorem lm1FreePreparedWrites_iff (writes : List PreparedParsedMaskedWrite) :
    Lm1FreePreparedWrites writes ↔
      ∀ write ∈ writes, PreparedParsedMaskedWrite.isLm1Write write = false :=
  Iff.rfl

theorem lm1FreePreparedWrites_nil : Lm1FreePreparedWrites [] := by
  intro write member
  simp at member

theorem lm1FreePreparedWrites_append {head tail : List PreparedParsedMaskedWrite}
    (headFree : Lm1FreePreparedWrites head) (tailFree : Lm1FreePreparedWrites tail) :
    Lm1FreePreparedWrites (head ++ tail) := by
  intro write member
  rcases List.mem_append.mp member with member | member
  · exact headFree write member
  · exact tailFree write member

/-- A `Bool` bank test against `.lm1` is `false` for every other bank. -/
theorem bank_beq_lm1_eq_false (bank : PEMemory.Bank) (notLm1 : bank ≠ PEMemory.Bank.lm1) :
    (bank == PEMemory.Bank.lm1) = false := by
  simpa using notLm1

/-! ## 1. The MSL/MSR stage -/

/-- **The single-destination writer is a `.lm1`-free one-element commit.**  This
is the write-level companion of `writeParsedMslMsrDestination?_lm1_of_ne`: the
bank-level lemma can be satisfied by a gated-off `.lm1` write, so the list
itself is inspected here. -/
theorem writeParsedMslMsrDestination?_clean_commit
    (files : IntegerRegisterFiles) (destination : ParsedOperand)
    (context : ParsedIntegerContext) (output : IntegerALU.Bus) (flags : BitVec 4)
    (cycle : Fin 4) (directive : ParsedMaskDirective) (hasSingleLineMask : Bool)
    (noLm1 : ∀ (bank : PEMemory.Bank) (width : PEMemory.Width),
      ParsedOperand.directDestinationBankWidth? destination = some (bank, width) →
        bank ≠ PEMemory.Bank.lm1)
    (write : ParsedMslMsrDestinationWrite)
    (lowered : writeParsedMslMsrDestination? files destination context output flags cycle
      directive hasSingleLineMask = some write) :
    ∃ writes, write.files = commitParsedMaskedWrites files writes ∧
      Lm1FreePreparedWrites writes := by
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
              have notLm1 : found.bank ≠ PEMemory.Bank.lm1 :=
                noLm1 found.bank found.width static.symm
              refine ⟨[⟨some found, none, PEMemory.unpackALUBus output, selection⟩],
                by simp [commitParsedMaskedWrites], ?_⟩
              intro write member
              simp only [List.mem_singleton] at member
              subst member
              simpa [PreparedParsedMaskedWrite.isLm1Write] using
                bank_beq_lm1_eq_false found.bank notLm1
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
              refine ⟨[⟨none, some (found, cycle, flags), PEMemory.unpackALUBus output,
                ⟨selection, false⟩⟩], by simp [commitParsedMaskedWrites], ?_⟩
              intro write member
              simp only [List.mem_singleton] at member
              subst member
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
          exact ⟨[], rfl, lm1FreePreparedWrites_nil⟩
  | nowrite =>
      simp only [writeParsedMslMsrDestination?] at lowered
      obtain rfl := Option.some.inj lowered
      exact ⟨[], rfl, lm1FreePreparedWrites_nil⟩
  | forward kind neg ext rnd => simp [writeParsedMslMsrDestination?] at lowered
  | fixed value => simp [writeParsedMslMsrDestination?] at lowered
  | matrix side width row => simp [writeParsedMslMsrDestination?] at lowered
  | l1bm width address => simp [writeParsedMslMsrDestination?] at lowered
  | l2bm address l2b => simp [writeParsedMslMsrDestination?] at lowered
  | dar value => simp [writeParsedMslMsrDestination?] at lowered

/-- **The MSL/MSR destination loop is a `.lm1`-free commit.** -/
theorem executeParsedMslMsrAtPE_writeDestinations_clean
    (currentState : State) (hasSingleLineMask : Bool) (context : ParsedIntegerContext)
    (cycle : Fin 4) (output : IntegerALU.Bus) :
    ∀ (destinations : List ParsedOperand) (files : IntegerRegisterFiles) (bar0 bar1 : BitVec 12)
      (nextFiles : IntegerRegisterFiles) (nextBar0 nextBar1 : BitVec 12),
      (∀ destination ∈ destinations,
        ∀ (bank : PEMemory.Bank) (width : PEMemory.Width),
          ParsedOperand.directDestinationBankWidth? destination = some (bank, width) →
            bank ≠ PEMemory.Bank.lm1) →
      executeParsedMslMsrAtPE.runCycles.writeDestinations currentState hasSingleLineMask context
        cycle output destinations files bar0 bar1 = some (nextFiles, nextBar0, nextBar1) →
      ∃ writes, nextFiles = commitParsedMaskedWrites files writes ∧
        Lm1FreePreparedWrites writes := by
  intro destinations
  induction destinations with
  | nil =>
      intro files bar0 bar1 nextFiles nextBar0 nextBar1 noLm1 executed
      rw [executeParsedMslMsrAtPE.runCycles.writeDestinations] at executed
      obtain ⟨rfl, rfl, rfl⟩ := Option.some.inj executed
      exact ⟨[], rfl, lm1FreePreparedWrites_nil⟩
  | cons destination rest ih =>
      intro files bar0 bar1 nextFiles nextBar0 nextBar1 noLm1 executed
      rw [executeParsedMslMsrAtPE.runCycles.writeDestinations] at executed
      cases lowered : writeParsedMslMsrDestination? files destination
          { context with cycle := cycle, bar0 := bar0, bar1 := bar1 } output 0 cycle
          currentState.maskDirective hasSingleLineMask with
      | none =>
          rw [lowered] at executed
          simp at executed
      | some write =>
          rw [lowered] at executed
          have tailExecuted :
              executeParsedMslMsrAtPE.runCycles.writeDestinations currentState hasSingleLineMask
                context cycle output rest write.files
                (match write.barUpdate with
                  | some (false, value) => value
                  | _ => bar0)
                (match write.barUpdate with
                  | some (true, value) => value
                  | _ => bar1) = some (nextFiles, nextBar0, nextBar1) := executed
          obtain ⟨headWrites, head, headFree⟩ :=
            writeParsedMslMsrDestination?_clean_commit files destination
              { context with cycle := cycle, bar0 := bar0, bar1 := bar1 } output 0 cycle
              currentState.maskDirective hasSingleLineMask
              (fun bank width static =>
                noLm1 destination (by simp) bank width static)
              write lowered
          obtain ⟨tailWrites, tail, tailFree⟩ := ih write.files _ _ nextFiles _ _ 
            (fun item member => noLm1 item (List.mem_cons_of_mem _ member)) tailExecuted
          exact ⟨headWrites ++ tailWrites, by
              rw [tail, head, commitParsedMaskedWrites_append],
            lm1FreePreparedWrites_append headFree tailFree⟩

/-- **The MSL/MSR cycle loop is a `.lm1`-free commit.** -/
theorem executeParsedMslMsrAtPE_runCycles_clean
    (readState currentState : State) (expression : ParsedExpr) (hasSingleLineMask : Bool)
    (context : ParsedIntegerContext) (destinations : List ParsedOperand) (pe : PEId)
    (sourceAt : Fin 4 → Option ParsedIntegerInput)
    (noLm1 : WelcomeRowHasNoLm1Destination expression)
    (destinationsEq : destinations = expression.destinations) :
    ∀ (cycles : List (Fin 4)) (files : IntegerRegisterFiles) (bar0 bar1 : BitVec 12)
      (outputs : Fin 4 → IntegerALU.Bus) (nextFiles : IntegerRegisterFiles)
      (nextBar0 nextBar1 : BitVec 12) (nextOutputs : Fin 4 → IntegerALU.Bus),
      executeParsedMslMsrAtPE.runCycles readState currentState expression hasSingleLineMask
        context destinations pe sourceAt cycles files bar0 bar1 outputs =
        .ok (nextFiles, nextBar0, nextBar1, nextOutputs) →
      ∃ writes, nextFiles = commitParsedMaskedWrites files writes ∧
        Lm1FreePreparedWrites writes := by
  intro cycles
  induction cycles with
  | nil =>
      intro files bar0 bar1 outputs nextFiles nextBar0 nextBar1 nextOutputs executed
      rw [executeParsedMslMsrAtPE.runCycles] at executed
      obtain ⟨rfl, rfl, rfl, rfl⟩ := StepResult.ok.inj executed
      exact ⟨[], rfl, lm1FreePreparedWrites_nil⟩
  | cons cycle rest ih =>
      intro files bar0 bar1 outputs nextFiles nextBar0 nextBar1 nextOutputs executed
      rw [executeParsedMslMsrAtPE.runCycles] at executed
      dsimp only at executed
      cases source : sourceAt cycle with
      | none =>
          rw [source] at executed
          dsimp only at executed
          simp at executed
      | some value =>
          rw [source] at executed
          dsimp only at executed
          cases read : ParsedIntegerInput.readWithForwarding (readState.peRegisters pe)
              (stateForwardingSlots readState pe) cycle value with
          | failure =>
              rw [read] at executed
              dsimp only at executed
              simp at executed
          | unknown =>
              rw [read] at executed
              dsimp only at executed
              simp at executed
          | ok sourceBus =>
              rw [read] at executed
              dsimp only at executed
              cases flush : resolveFlushSelection? expression.flush files.maskRegisters cycle with
              | none =>
                  rw [flush] at executed
                  dsimp only at executed
                  simp at executed
              | some flushSelection =>
                  rw [flush] at executed
                  dsimp only at executed
                  cases wrote : executeParsedMslMsrAtPE.runCycles.writeDestinations currentState
                      hasSingleLineMask context cycle
                      (parsedOutputAfterFlush flushSelection (mslMsrOutputBus sourceBus))
                      destinations files bar0 bar1 with
                  | none =>
                      rw [wrote] at executed
                      dsimp only at executed
                      simp at executed
                  | some result =>
                      rw [wrote] at executed
                      dsimp only at executed
                      obtain ⟨middleFiles, middleBar0, middleBar1⟩ := result
                      obtain ⟨headWrites, head, headFree⟩ :=
                        executeParsedMslMsrAtPE_writeDestinations_clean currentState
                          hasSingleLineMask context cycle
                          (parsedOutputAfterFlush flushSelection (mslMsrOutputBus sourceBus))
                          destinations files bar0 bar1 middleFiles middleBar0 middleBar1
                          (fun destination member bank width static =>
                            noLm1 destination (destinationsEq ▸ member) bank width static)
                          wrote
                      obtain ⟨tailWrites, tail, tailFree⟩ := ih middleFiles middleBar0 middleBar1 _
                        nextFiles nextBar0 nextBar1 nextOutputs executed
                      exact ⟨headWrites ++ tailWrites, by
                          rw [tail, head, commitParsedMaskedWrites_append],
                        lm1FreePreparedWrites_append headFree tailFree⟩

/-- **The MSL/MSR per-PE step is a `.lm1`-free commit at the visited PE.** -/
theorem executeParsedMslMsrAtPE_pe_clean
    (readState currentState next : State) (expression : ParsedExpr) (pe : PEId)
    (noForward hasSingleLineMask : Bool)
    (noLm1 : WelcomeRowHasNoLm1Destination expression)
    (executed : executeParsedMslMsrAtPE readState currentState expression pe noForward
      hasSingleLineMask = .ok next) :
    ∃ writes, next.peRegisters pe =
      commitParsedMaskedWrites (currentState.peRegisters pe) writes ∧
      Lm1FreePreparedWrites writes := by
  rw [executeParsedMslMsrAtPE.eq_1] at executed
  cases lowered : lowerParsedMslMsr? expression with
  | none =>
      rw [lowered] at executed
      simp at executed
  | some accesses =>
      obtain ⟨isMsl, destinations⟩ := accesses
      rw [lowered] at executed
      dsimp only at executed
      split at executed
      · simp at executed
      · simp at executed
      · rename_i registers bar0 bar1 outputs ran
        rw [Id.run_pure] at executed
        simp only [StepResult.ok.injEq] at executed
        have destinationsEq :=
          lowerParsedMslMsr?_destinations expression isMsl destinations lowered
        obtain ⟨writes, committed, clean⟩ :=
          executeParsedMslMsrAtPE_runCycles_clean readState currentState expression
            hasSingleLineMask _ destinations _ _ noLm1 destinationsEq [0, 1, 2, 3]
            (currentState.peRegisters pe) _ _ _ registers bar0 bar1 outputs ran
        refine ⟨writes, ?_, clean⟩
        subst executed
        simpa using committed

/-- **The MSL/MSR per-PE step leaves every other PE untouched.**  (Re-exported
under a provenance-specific name so §1 is self-contained.) -/
theorem executeParsedMslMsrAtPE_peRegisters_frame'
    (readState currentState next : State) (expression : ParsedExpr) (pe other : PEId)
    (different : other ≠ pe) (noForward hasSingleLineMask : Bool)
    (executed : executeParsedMslMsrAtPE readState currentState expression pe noForward
      hasSingleLineMask = .ok next) :
    next.peRegisters other = currentState.peRegisters other :=
  executeParsedMslMsrAtPE_peRegisters_other readState currentState next expression pe other
    different noForward hasSingleLineMask executed

/-- **The MSL/MSR walk is a `.lm1`-free commit at every visited PE.** -/
theorem executeParsedMslMsrAtPEs_clean
    (readState : State) (expression : ParsedExpr) (noForward hasSingleLineMask : Bool)
    (noLm1 : WelcomeRowHasNoLm1Destination expression) :
    ∀ (pes : List PEId) (state : State) (p : PEId) (next : State),
      executeParsedMslMsrAtPEs readState state expression pes noForward hasSingleLineMask =
        .ok next →
      ∃ writes, next.peRegisters p = commitParsedMaskedWrites (state.peRegisters p) writes ∧
        Lm1FreePreparedWrites writes := by
  intro pes
  induction pes with
  | nil =>
      intro state p next executed
      simp only [executeParsedMslMsrAtPEs, StepResult.ok.injEq] at executed
      subst executed
      exact ⟨[], rfl, lm1FreePreparedWrites_nil⟩
  | cons pe rest ih =>
      intro state p next executed
      simp only [executeParsedMslMsrAtPEs] at executed
      split at executed
      · simp at executed
      · simp at executed
      · rename_i middle headExecuted
        obtain ⟨tailWrites, tail, tailFree⟩ := ih middle p next executed
        by_cases same : p = pe
        · rw [same] at tail ⊢
          obtain ⟨headWrites, headCommit, headFree⟩ :=
            executeParsedMslMsrAtPE_pe_clean readState state middle expression pe noForward
              hasSingleLineMask noLm1 headExecuted
          exact ⟨headWrites ++ tailWrites, by
              rw [tail, headCommit, commitParsedMaskedWrites_append],
            lm1FreePreparedWrites_append headFree tailFree⟩
        · have frame := executeParsedMslMsrAtPE_peRegisters_frame' readState state middle
            expression pe p same noForward hasSingleLineMask headExecuted
          exact ⟨tailWrites, by rw [tail, frame], tailFree⟩

/-- **The MSL/MSR producer filter is a `.lm1`-free commit at PE 0.** -/
theorem executeParsedMslMsrProducers_clean_commit
    (readState currentState next : State) (expressions : List ParsedExpr)
    (noForward hasSingleLineMask : Bool)
    (noLm1 : ∀ expression ∈ expressions.filter parsedExprIsMslMsrProducer,
      WelcomeRowHasNoLm1Destination expression)
    (executed : executeParsedMslMsrProducers readState currentState expressions noForward
      hasSingleLineMask = .ok next) :
    ∃ writes, next.peRegisters welcomePE =
      commitParsedMaskedWrites (currentState.peRegisters welcomePE) writes ∧
      Lm1FreePreparedWrites writes := by
  cases filtered : expressions.filter parsedExprIsMslMsrProducer with
  | nil =>
      rw [executeParsedMslMsrProducers, filtered] at executed
      simp only [StepResult.ok.injEq] at executed
      subst executed
      exact ⟨[], rfl, lm1FreePreparedWrites_nil⟩
  | cons expression rest =>
      cases rest with
      | nil =>
          rw [executeParsedMslMsrProducers, filtered] at executed
          exact executeParsedMslMsrAtPEs_clean readState expression noForward
            hasSingleLineMask (noLm1 expression (by simp [filtered]))
            (List.finRange 4096) currentState welcomePE next executed
      | cons second remaining =>
          rw [executeParsedMslMsrProducers, filtered] at executed
          simp at executed

/-- **The stage-level `.lm1` provenance proposition for the MSL/MSR stage.** -/
def WelcomePEMslMsrStageLm1Provenance : Prop :=
    ∀ (readState currentState next : State) (expressions : List ParsedExpr)
      (noForward hasSingleLineMask : Bool),
      (∀ expression ∈ expressions.filter parsedExprIsMslMsrProducer,
        WelcomeRowHasNoLm1Destination expression) →
      executeParsedMslMsrProducers readState currentState expressions noForward
        hasSingleLineMask = .ok next →
      ∃ writes, next.peRegisters welcomePE =
        commitParsedMaskedWrites (currentState.peRegisters welcomePE) writes ∧
        Lm1FreePreparedWrites writes

/-- **The MSL/MSR stage's write-list-level `.lm1` provenance.** -/
theorem welcomePEMslMsrStageLm1Provenance : WelcomePEMslMsrStageLm1Provenance :=
  fun readState currentState next expressions noForward hasSingleLineMask noLm1 executed =>
    executeParsedMslMsrProducers_clean_commit readState currentState next expressions
      noForward hasSingleLineMask noLm1 executed


/-! ## 2. The float-relu stage -/

/-- **The float-relu destination loop is a `.lm1`-free commit.** -/
theorem executeParsedFloatReluAtPE_writeDestinations_clean
    (currentState : State) (hasSingleLineMask : Bool) (coordinates : ParsedIntegerContext)
    (cycle : Fin 4) (flags : BitVec 4) (output : IntegerALU.Bus) :
    ∀ (destinations : List ParsedOperand) (files : IntegerRegisterFiles) (bar0 bar1 : BitVec 12)
      (nextFiles : IntegerRegisterFiles) (nextBar0 nextBar1 : BitVec 12),
      (∀ destination ∈ destinations,
        ∀ (bank : PEMemory.Bank) (width : PEMemory.Width),
          ParsedOperand.directDestinationBankWidth? destination = some (bank, width) →
            bank ≠ PEMemory.Bank.lm1) →
      executeParsedFloatReluAtPE.runCycles.writeDestinations currentState hasSingleLineMask
        coordinates cycle flags output destinations files bar0 bar1 =
        some (nextFiles, nextBar0, nextBar1) →
      ∃ writes, nextFiles = commitParsedMaskedWrites files writes ∧
        Lm1FreePreparedWrites writes := by
  intro destinations
  induction destinations with
  | nil =>
      intro files bar0 bar1 nextFiles nextBar0 nextBar1 noLm1 executed
      rw [executeParsedFloatReluAtPE.runCycles.writeDestinations] at executed
      obtain ⟨rfl, rfl, rfl⟩ := Option.some.inj executed
      exact ⟨[], rfl, lm1FreePreparedWrites_nil⟩
  | cons destination rest ih =>
      intro files bar0 bar1 nextFiles nextBar0 nextBar1 noLm1 executed
      rw [executeParsedFloatReluAtPE.runCycles.writeDestinations] at executed
      cases lowered : writeParsedMslMsrDestination? files destination
          { coordinates with cycle := cycle, bar0 := bar0, bar1 := bar1 } output flags cycle
          currentState.maskDirective hasSingleLineMask with
      | none =>
          rw [lowered] at executed
          simp at executed
      | some write =>
          rw [lowered] at executed
          have tailExecuted :
              executeParsedFloatReluAtPE.runCycles.writeDestinations currentState
                hasSingleLineMask coordinates cycle flags output rest write.files
                (match write.barUpdate with
                  | some (false, value) => value
                  | _ => bar0)
                (match write.barUpdate with
                  | some (true, value) => value
                  | _ => bar1) = some (nextFiles, nextBar0, nextBar1) := executed
          obtain ⟨headWrites, head, headFree⟩ :=
            writeParsedMslMsrDestination?_clean_commit files destination
              { coordinates with cycle := cycle, bar0 := bar0, bar1 := bar1 } output flags cycle
              currentState.maskDirective hasSingleLineMask
              (fun bank width static => noLm1 destination (by simp) bank width static)
              write lowered
          obtain ⟨tailWrites, tail, tailFree⟩ := ih write.files _ _ nextFiles _ _
            (fun item member => noLm1 item (List.mem_cons_of_mem _ member)) tailExecuted
          exact ⟨headWrites ++ tailWrites, by
              rw [tail, head, commitParsedMaskedWrites_append],
            lm1FreePreparedWrites_append headFree tailFree⟩

/-- **The float-relu cycle loop is a `.lm1`-free commit.** -/
theorem executeParsedFloatReluAtPE_runCycles_clean
    (readState currentState : State) (expression : ParsedExpr) (pe : PEId)
    (hasSingleLineMask : Bool) (coordinates sourceContext : ParsedIntegerContext)
    (noLm1 : WelcomeRowHasNoLm1Destination expression) :
    ∀ (cycles : List (Fin 4)) (files : IntegerRegisterFiles) (bar0 bar1 : BitVec 12)
      (outputs : Fin 4 → IntegerALU.Bus) (nextFiles : IntegerRegisterFiles)
      (nextBar0 nextBar1 : BitVec 12) (nextOutputs : Fin 4 → IntegerALU.Bus),
      executeParsedFloatReluAtPE.runCycles readState currentState expression pe
        hasSingleLineMask coordinates sourceContext cycles files bar0 bar1 outputs =
        .ok (nextFiles, nextBar0, nextBar1, nextOutputs) →
      ∃ writes, nextFiles = commitParsedMaskedWrites files writes ∧
        Lm1FreePreparedWrites writes := by
  intro cycles
  induction cycles with
  | nil =>
      intro files bar0 bar1 outputs nextFiles nextBar0 nextBar1 nextOutputs executed
      rw [executeParsedFloatReluAtPE.runCycles] at executed
      obtain ⟨rfl, rfl, rfl, rfl⟩ := StepResult.ok.inj executed
      exact ⟨[], rfl, lm1FreePreparedWrites_nil⟩
  | cons cycle rest ih =>
      intro files bar0 bar1 outputs nextFiles nextBar0 nextBar1 nextOutputs executed
      rw [executeParsedFloatReluAtPE.runCycles] at executed
      dsimp only at executed
      cases lower : lowerParsedFloatRelu? expression { sourceContext with cycle := cycle } with
      | none =>
          rw [lower] at executed
          dsimp only at executed
          simp at executed
      | some accesses =>
          rw [lower] at executed
          dsimp only at executed
          have destinationsEq :=
            lowerParsedFloatRelu?_destinations expression { sourceContext with cycle := cycle }
              accesses lower
          cases readA : ParsedIntegerInput.readWithForwarding (readState.peRegisters pe)
              (stateForwardingSlots readState pe) cycle accesses.sourceA with
          | failure =>
              rw [readA] at executed
              dsimp only at executed
              simp at executed
          | unknown =>
              rw [readA] at executed
              dsimp only at executed
              simp at executed
          | ok sourceA =>
              rw [readA] at executed
              dsimp only at executed
              cases sourceB? : accesses.sourceB with
              | none =>
                  rw [sourceB?] at executed
                  dsimp only at executed
                  cases flush : resolveFlushSelection? expression.flush files.maskRegisters cycle with
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
                        obtain ⟨headWrites, head, headFree⟩ :=
                          executeParsedFloatReluAtPE_writeDestinations_clean currentState
                            hasSingleLineMask coordinates cycle _ _ accesses.destinations files
                            bar0 bar1 middleFiles middleBar0 middleBar1
                            (fun destination member bank width static =>
                              noLm1 destination (destinationsEq ▸ member) bank width static)
                            wrote
                        obtain ⟨tailWrites, tail, tailFree⟩ := ih middleFiles middleBar0
                          middleBar1 _ nextFiles nextBar0 nextBar1 nextOutputs executed
                        exact ⟨headWrites ++ tailWrites, by
                            rw [tail, head, commitParsedMaskedWrites_append],
                          lm1FreePreparedWrites_append headFree tailFree⟩
              | some sourceBInput =>
                  rw [sourceB?] at executed
                  dsimp only at executed
                  cases readB : ParsedIntegerInput.readWithForwarding (readState.peRegisters pe)
                      (stateForwardingSlots readState pe) cycle sourceBInput with
                  | failure =>
                      rw [readB] at executed
                      dsimp only at executed
                      simp at executed
                  | unknown =>
                      rw [readB] at executed
                      dsimp only at executed
                      simp at executed
                  | ok sourceB =>
                      rw [readB] at executed
                      dsimp only at executed
                      cases flush : resolveFlushSelection? expression.flush files.maskRegisters cycle with
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
                            obtain ⟨headWrites, head, headFree⟩ :=
                              executeParsedFloatReluAtPE_writeDestinations_clean currentState
                                hasSingleLineMask coordinates cycle _ _ accesses.destinations files
                                bar0 bar1 middleFiles middleBar0 middleBar1
                                (fun destination member bank width static =>
                                  noLm1 destination (destinationsEq ▸ member) bank width static)
                                wrote
                            obtain ⟨tailWrites, tail, tailFree⟩ := ih middleFiles middleBar0
                              middleBar1 _ nextFiles nextBar0 nextBar1 nextOutputs executed
                            exact ⟨headWrites ++ tailWrites, by
                                rw [tail, head, commitParsedMaskedWrites_append],
                              lm1FreePreparedWrites_append headFree tailFree⟩

/-- **The float-relu per-PE step is a `.lm1`-free commit at the visited PE.** -/
theorem executeParsedFloatReluAtPE_pe_clean
    (readState currentState next : State) (expression : ParsedExpr) (pe : PEId)
    (noForward hasSingleLineMask : Bool)
    (noLm1 : WelcomeRowHasNoLm1Destination expression)
    (executed : executeParsedFloatReluAtPE readState currentState expression pe noForward
      hasSingleLineMask = .ok next) :
    ∃ writes, next.peRegisters pe =
      commitParsedMaskedWrites (currentState.peRegisters pe) writes ∧
      Lm1FreePreparedWrites writes := by
  rw [executeParsedFloatReluAtPE.eq_1] at executed
  dsimp only at executed
  split at executed
  · simp at executed
  · simp at executed
  · rename_i registers bar0 bar1 outputs ran
    rw [Id.run_pure] at executed
    simp only [StepResult.ok.injEq] at executed
    obtain ⟨writes, committed, clean⟩ :=
      executeParsedFloatReluAtPE_runCycles_clean readState currentState expression pe
        hasSingleLineMask _ _ noLm1 [0, 1, 2, 3] (currentState.peRegisters pe) _ _ _
        registers bar0 bar1 outputs ran
    refine ⟨writes, ?_, clean⟩
    subst executed
    simpa using committed

/-- **The float-relu walk is a `.lm1`-free commit at every visited PE.** -/
theorem executeParsedFloatReluAtPEs_clean
    (readState : State) (expression : ParsedExpr) (noForward hasSingleLineMask : Bool)
    (noLm1 : WelcomeRowHasNoLm1Destination expression) :
    ∀ (pes : List PEId) (state : State) (p : PEId) (next : State),
      executeParsedFloatReluAtPEs readState state expression pes noForward hasSingleLineMask =
        .ok next →
      ∃ writes, next.peRegisters p = commitParsedMaskedWrites (state.peRegisters p) writes ∧
        Lm1FreePreparedWrites writes := by
  intro pes
  induction pes with
  | nil =>
      intro state p next executed
      simp only [executeParsedFloatReluAtPEs, StepResult.ok.injEq] at executed
      subst executed
      exact ⟨[], rfl, lm1FreePreparedWrites_nil⟩
  | cons pe rest ih =>
      intro state p next executed
      simp only [executeParsedFloatReluAtPEs] at executed
      split at executed
      · simp at executed
      · simp at executed
      · rename_i middle headExecuted
        obtain ⟨tailWrites, tail, tailFree⟩ := ih middle p next executed
        by_cases same : p = pe
        · rw [same] at tail ⊢
          obtain ⟨headWrites, headCommit, headFree⟩ :=
            executeParsedFloatReluAtPE_pe_clean readState state middle expression pe noForward
              hasSingleLineMask noLm1 headExecuted
          exact ⟨headWrites ++ tailWrites, by
              rw [tail, headCommit, commitParsedMaskedWrites_append],
            lm1FreePreparedWrites_append headFree tailFree⟩
        · have frame := executeParsedFloatReluAtPE_peRegisters_other readState state middle
            expression pe p same noForward hasSingleLineMask headExecuted
          exact ⟨tailWrites, by rw [tail, frame], tailFree⟩

/-- **The float-relu producer filter is a `.lm1`-free commit at PE 0.** -/
theorem executeParsedFloatReluProducers_clean_commit
    (readState currentState next : State) (expressions : List ParsedExpr)
    (noForward hasSingleLineMask : Bool)
    (noLm1 : ∀ expression ∈ expressions.filter parsedExprIsFloatReluProducer,
      WelcomeRowHasNoLm1Destination expression)
    (executed : executeParsedFloatReluProducers readState currentState expressions noForward
      hasSingleLineMask = .ok next) :
    ∃ writes, next.peRegisters welcomePE =
      commitParsedMaskedWrites (currentState.peRegisters welcomePE) writes ∧
      Lm1FreePreparedWrites writes := by
  cases filtered : expressions.filter parsedExprIsFloatReluProducer with
  | nil =>
      rw [executeParsedFloatReluProducers, filtered] at executed
      simp only [StepResult.ok.injEq] at executed
      subst executed
      exact ⟨[], rfl, lm1FreePreparedWrites_nil⟩
  | cons expression rest =>
      cases rest with
      | nil =>
          rw [executeParsedFloatReluProducers, filtered] at executed
          exact executeParsedFloatReluAtPEs_clean readState expression noForward
            hasSingleLineMask (noLm1 expression (by simp [filtered]))
            (List.finRange 4096) currentState welcomePE next executed
      | cons second remaining =>
          rw [executeParsedFloatReluProducers, filtered] at executed
          simp at executed

/-- **The stage-level `.lm1` provenance proposition for the float-relu stage.** -/
def WelcomePEFloatReluStageLm1Provenance : Prop :=
    ∀ (readState currentState next : State) (expressions : List ParsedExpr)
      (noForward hasSingleLineMask : Bool),
      (∀ expression ∈ expressions.filter parsedExprIsFloatReluProducer,
        WelcomeRowHasNoLm1Destination expression) →
      executeParsedFloatReluProducers readState currentState expressions noForward
        hasSingleLineMask = .ok next →
      ∃ writes, next.peRegisters welcomePE =
        commitParsedMaskedWrites (currentState.peRegisters welcomePE) writes ∧
        Lm1FreePreparedWrites writes

/-- **The float-relu stage's write-list-level `.lm1` provenance.** -/
theorem welcomePEFloatReluStageLm1Provenance : WelcomePEFloatReluStageLm1Provenance :=
  fun readState currentState next expressions noForward hasSingleLineMask noLm1 executed =>
    executeParsedFloatReluProducers_clean_commit readState currentState next expressions
      noForward hasSingleLineMask noLm1 executed


/-! ## 3. The block-float stage -/

/-- **The block-float destination loop is a `.lm1`-free commit.** -/
theorem executeParsedBlockFloatAtMAB_apply_clean
    (currentState : State) (hasSingleLineMask : Bool) (cycle : Fin 4)
    (output : IntegerALU.Bus) (oldContext coords : ParsedIntegerContext) :
    ∀ (destinations : List ParsedOperand) (files : IntegerRegisterFiles) (bar0 bar1 : BitVec 12)
      (nextFiles : IntegerRegisterFiles) (nextBar0 nextBar1 : BitVec 12),
      (∀ destination ∈ destinations,
        ∀ (bank : PEMemory.Bank) (width : PEMemory.Width),
          ParsedOperand.directDestinationBankWidth? destination = some (bank, width) →
            bank ≠ PEMemory.Bank.lm1) →
      executeParsedBlockFloatAtMAB.apply currentState hasSingleLineMask cycle output oldContext
        coords destinations files bar0 bar1 = .ok (nextFiles, nextBar0, nextBar1) →
      ∃ writes, nextFiles = commitParsedMaskedWrites files writes ∧
        Lm1FreePreparedWrites writes := by
  intro destinations
  induction destinations with
  | nil =>
      intro files bar0 bar1 nextFiles nextBar0 nextBar1 noLm1 executed
      rw [executeParsedBlockFloatAtMAB.apply.eq_1] at executed
      obtain ⟨rfl, rfl, rfl⟩ := StepResult.ok.inj executed
      exact ⟨[], rfl, lm1FreePreparedWrites_nil⟩
  | cons destination rest ih =>
      intro files bar0 bar1 nextFiles nextBar0 nextBar1 noLm1 executed
      rw [executeParsedBlockFloatAtMAB.apply.eq_2] at executed
      dsimp only at executed
      cases lowered : writeParsedMslMsrDestination? files destination
          { coords with cycle := cycle, bar0 := bar0, bar1 := bar1, tWord := oldContext.tWord }
          output 0 cycle currentState.maskDirective hasSingleLineMask with
      | none =>
          rw [lowered] at executed
          simp at executed
      | some write =>
          rw [lowered] at executed
          have tailExecuted :
              executeParsedBlockFloatAtMAB.apply currentState hasSingleLineMask cycle output
                oldContext coords rest write.files
                (match write.barUpdate with
                  | some (false, value) => value
                  | _ => bar0)
                (match write.barUpdate with
                  | some (true, value) => value
                  | _ => bar1) = .ok (nextFiles, nextBar0, nextBar1) := executed
          obtain ⟨headWrites, head, headFree⟩ :=
            writeParsedMslMsrDestination?_clean_commit files destination
              { coords with cycle := cycle, bar0 := bar0, bar1 := bar1, tWord := oldContext.tWord }
              output 0 cycle currentState.maskDirective hasSingleLineMask
              (fun bank width static => noLm1 destination (by simp) bank width static)
              write lowered
          obtain ⟨tailWrites, tail, tailFree⟩ := ih write.files _ _ nextFiles _ _
            (fun item member => noLm1 item (List.mem_cons_of_mem _ member)) tailExecuted
          exact ⟨headWrites ++ tailWrites, by
              rw [tail, head, commitParsedMaskedWrites_append],
            lm1FreePreparedWrites_append headFree tailFree⟩

/-- **The block-float per-cycle four-PE loop is a `.lm1`-free commit at any
target PE.** -/
theorem executeParsedBlockFloatAtMAB_writePEs_clean
    (expression : ParsedExpr)
    (writeDestinations : Fin 4 → Fin 4 → IntegerALU.Bus → IntegerRegisterFiles →
      BitVec 12 → BitVec 12 → StepResult (IntegerRegisterFiles × BitVec 12 × BitVec 12))
    (writeClean : ∀ (pe : Fin 4) (cycle : Fin 4) (output : IntegerALU.Bus)
      (files : IntegerRegisterFiles) (bar0 bar1 : BitVec 12) (nextFiles : IntegerRegisterFiles)
      (nextBar0 nextBar1 : BitVec 12),
      writeDestinations pe cycle output files bar0 bar1 = .ok (nextFiles, nextBar0, nextBar1) →
      ∃ writes, nextFiles = commitParsedMaskedWrites files writes ∧
        Lm1FreePreparedWrites writes)
    (cycle : Fin 4) (buses : Fin 4 → IntegerALU.Bus) (target : Fin 4) :
    ∀ (pes : List (Fin 4)) (files : Fin 4 → IntegerRegisterFiles) (bar0 bar1 : Fin 4 → BitVec 12)
      (outputs : Fin 4 → Fin 4 → IntegerALU.Bus)
      (results : Fin 4 → IntegerRegisterFiles × BitVec 12 × BitVec 12 × (Fin 4 → IntegerALU.Bus)),
      executeParsedBlockFloatAtMAB.writePEs expression writeDestinations cycle buses pes files
        bar0 bar1 outputs = .ok results →
      ∃ writes, (results target).1 = commitParsedMaskedWrites (files target) writes ∧
        Lm1FreePreparedWrites writes := by
  intro pes
  induction pes with
  | nil =>
      intro files bar0 bar1 outputs results executed
      rw [executeParsedBlockFloatAtMAB.writePEs.eq_1] at executed
      obtain rfl := StepResult.ok.inj executed
      exact ⟨[], rfl, lm1FreePreparedWrites_nil⟩
  | cons pe rest ih =>
      intro files bar0 bar1 outputs results executed
      rw [executeParsedBlockFloatAtMAB.writePEs.eq_2] at executed
      dsimp only at executed
      cases flush : resolveFlushSelection? expression.flush (files pe).maskRegisters cycle with
      | none =>
          rw [flush] at executed
          dsimp only at executed
          simp at executed
      | some flushSelection =>
          rw [flush] at executed
          dsimp only at executed
          cases wrote : writeDestinations pe cycle
              (parsedOutputAfterFlush flushSelection (buses pe)) (files pe) (bar0 pe) (bar1 pe) with
          | failure =>
              rw [wrote] at executed
              dsimp only at executed
              simp at executed
          | unknown =>
              rw [wrote] at executed
              dsimp only at executed
              simp at executed
          | ok result =>
              obtain ⟨nextPEFiles, nextBar0, nextBar1⟩ := result
              rw [wrote] at executed
              dsimp only at executed
              obtain ⟨headWrites, head, headFree⟩ := writeClean pe cycle
                (parsedOutputAfterFlush flushSelection (buses pe)) (files pe) (bar0 pe) (bar1 pe)
                nextPEFiles nextBar0 nextBar1 wrote
              have tailExecuted :
                  executeParsedBlockFloatAtMAB.writePEs expression writeDestinations cycle buses
                    rest
                    (fun other => if (other == pe) = true then nextPEFiles else files other)
                    (fun other => if (other == pe) = true then nextBar0 else bar0 other)
                    (fun other => if (other == pe) = true then nextBar1 else bar1 other)
                    (fun other index =>
                      if (other == pe && index == cycle) = true
                      then parsedOutputAfterFlush flushSelection (buses pe)
                      else outputs other index) = .ok results := executed
              obtain ⟨tailWrites, tail, tailFree⟩ := ih _ _ _ _ _ tailExecuted
              by_cases same : target = pe
              · subst same
                refine ⟨headWrites ++ tailWrites, ?_,
                  lm1FreePreparedWrites_append headFree tailFree⟩
                rw [tail]
                simp only [beq_self_eq_true, ite_true]
                rw [head, commitParsedMaskedWrites_append]
              · refine ⟨tailWrites, ?_, tailFree⟩
                rw [tail]
                have different : (target == pe) = false := by
                  simp [same]
                simp [different]

/-- **The block-float cycle loop is a `.lm1`-free commit at any target PE.** -/
theorem executeParsedBlockFloatAtMAB_runCycles_clean
    (accesses : ParsedBlockFloatAccesses)
    (readCycle : Fin 4 → StepResult (Fin 4 → IntegerALU.Bus))
    (writeCycle : Fin 4 → (Fin 4 → IntegerALU.Bus) → (Fin 4 → IntegerRegisterFiles) →
      (Fin 4 → BitVec 12) → (Fin 4 → BitVec 12) → (Fin 4 → Fin 4 → IntegerALU.Bus) →
      StepResult (Fin 4 → IntegerRegisterFiles × BitVec 12 × BitVec 12 × (Fin 4 → IntegerALU.Bus)))
    (writeClean : ∀ (cycle : Fin 4) (buses : Fin 4 → IntegerALU.Bus)
      (files : Fin 4 → IntegerRegisterFiles) (bar0 bar1 : Fin 4 → BitVec 12)
      (outputs : Fin 4 → Fin 4 → IntegerALU.Bus)
      (results : Fin 4 → IntegerRegisterFiles × BitVec 12 × BitVec 12 × (Fin 4 → IntegerALU.Bus)),
      writeCycle cycle buses files bar0 bar1 outputs = .ok results →
      ∀ target : Fin 4, ∃ writes,
        (results target).1 = commitParsedMaskedWrites (files target) writes ∧
        Lm1FreePreparedWrites writes)
    (target : Fin 4) :
    ∀ (cycles : List (Fin 4)) (files : Fin 4 → IntegerRegisterFiles) (bar0 bar1 : Fin 4 → BitVec 12)
      (outputs : Fin 4 → Fin 4 → IntegerALU.Bus)
      (results : Fin 4 → IntegerRegisterFiles × BitVec 12 × BitVec 12 × (Fin 4 → IntegerALU.Bus)),
      executeParsedBlockFloatAtMAB.runCycles accesses readCycle writeCycle cycles files bar0 bar1
        outputs = .ok results →
      ∃ writes, (results target).1 = commitParsedMaskedWrites (files target) writes ∧
        Lm1FreePreparedWrites writes := by
  intro cycles
  induction cycles with
  | nil =>
      intro files bar0 bar1 outputs results executed
      rw [executeParsedBlockFloatAtMAB.runCycles.eq_1] at executed
      obtain rfl := StepResult.ok.inj executed
      exact ⟨[], rfl, lm1FreePreparedWrites_nil⟩
  | cons cycle rest ih =>
      intro files bar0 bar1 outputs results executed
      rw [executeParsedBlockFloatAtMAB.runCycles.eq_2] at executed
      dsimp only at executed
      split at executed
      · simp at executed
      · simp at executed
      · rename_i inputBuses ranRead
        split at executed
        · simp at executed
        · simp at executed
        · rename_i results' ranWrite
          obtain ⟨headWrites, head, headFree⟩ := writeClean cycle
            (parsedBlockFloatMab accesses.precision accesses.keep accesses.extended inputBuses)
            files bar0 bar1 outputs results' ranWrite target
          obtain ⟨tailWrites, tail, tailFree⟩ := ih (fun pe => (results' pe).1)
            (fun pe => (results' pe).2.1) (fun pe => (results' pe).2.2.1)
            (fun pe index => (results' pe).2.2.2 index) results executed
          exact ⟨headWrites ++ tailWrites, by
              rw [tail, head, commitParsedMaskedWrites_append],
            lm1FreePreparedWrites_append headFree tailFree⟩

/-- **The block-float write cycle is a `.lm1`-free commit.** -/
theorem executeParsedBlockFloat_writeCycle_clean
    (currentState : State) (hasSingleLineMask : Bool) (expression : ParsedExpr)
    (coordinate : MABCoordinate) (accesses : ParsedBlockFloatAccesses)
    (noLm1 : ∀ destination ∈ accesses.destinations,
      ∀ (bank : PEMemory.Bank) (width : PEMemory.Width),
        ParsedOperand.directDestinationBankWidth? destination = some (bank, width) →
          bank ≠ PEMemory.Bank.lm1)
    (writeCycle : Fin 4 → (Fin 4 → IntegerALU.Bus) → (Fin 4 → IntegerRegisterFiles) →
      (Fin 4 → BitVec 12) → (Fin 4 → BitVec 12) → (Fin 4 → Fin 4 → IntegerALU.Bus) →
      StepResult (Fin 4 → IntegerRegisterFiles × BitVec 12 × BitVec 12 × (Fin 4 → IntegerALU.Bus)))
    (form : ∀ (cycle : Fin 4) (buses : Fin 4 → IntegerALU.Bus)
      (files : Fin 4 → IntegerRegisterFiles) (bar0 bar1 : Fin 4 → BitVec 12)
      (outputs : Fin 4 → Fin 4 → IntegerALU.Bus),
      writeCycle cycle buses files bar0 bar1 outputs =
        Id.run (executeParsedBlockFloatAtMAB.writePEs expression
          (fun pe cycle output files bar0 bar1 =>
            Id.run (executeParsedBlockFloatAtMAB.apply currentState hasSingleLineMask cycle output
              (currentState.peContext (physicalPEId coordinate pe))
              (ParsedIntegerContext.ofLinearIndex (physicalPEId coordinate pe))
              accesses.destinations files bar0 bar1))
          cycle buses (List.finRange 4) files bar0 bar1 outputs))
    (cycle : Fin 4) (buses : Fin 4 → IntegerALU.Bus)
    (files : Fin 4 → IntegerRegisterFiles) (bar0 bar1 : Fin 4 → BitVec 12)
    (outputs : Fin 4 → Fin 4 → IntegerALU.Bus)
    (results : Fin 4 → IntegerRegisterFiles × BitVec 12 × BitVec 12 × (Fin 4 → IntegerALU.Bus))
    (executed : writeCycle cycle buses files bar0 bar1 outputs = .ok results)
    (target : Fin 4) :
    ∃ writes, (results target).1 = commitParsedMaskedWrites (files target) writes ∧
      Lm1FreePreparedWrites writes := by
  rw [form cycle buses files bar0 bar1 outputs] at executed
  have executed' :
      executeParsedBlockFloatAtMAB.writePEs expression
        (fun pe cycle output files bar0 bar1 =>
          Id.run (executeParsedBlockFloatAtMAB.apply currentState hasSingleLineMask cycle output
            (currentState.peContext (physicalPEId coordinate pe))
            (ParsedIntegerContext.ofLinearIndex (physicalPEId coordinate pe))
            accesses.destinations files bar0 bar1))
        cycle buses (List.finRange 4) files bar0 bar1 outputs = .ok results := executed
  exact executeParsedBlockFloatAtMAB_writePEs_clean expression _ 
    (fun pe cyc out fl b0 b1 nf nb0 nb1 hh =>
      executeParsedBlockFloatAtMAB_apply_clean currentState hasSingleLineMask cyc out
        (currentState.peContext (physicalPEId coordinate pe))
        (ParsedIntegerContext.ofLinearIndex (physicalPEId coordinate pe))
        accesses.destinations fl b0 b1 nf nb0 nb1 noLm1 hh)
    cycle buses target (List.finRange 4) files bar0 bar1 outputs results executed'


/-- **The block-float per-MAB step is a `.lm1`-free commit at each of its four
PEs.** -/
theorem executeParsedBlockFloatAtMAB_pe_clean
    (readState currentState : State) (expression : ParsedExpr) (coordinate : MABCoordinate)
    (noForward hasSingleLineMask : Bool)
    (noLm1 : WelcomeRowHasNoLm1Destination expression)
    (target : Fin 4) (next : State)
    (executed : executeParsedBlockFloatAtMAB readState currentState expression coordinate
      noForward hasSingleLineMask = .ok next) :
    ∃ writes, next.peRegisters (physicalPEId coordinate target) =
      commitParsedMaskedWrites (currentState.peRegisters (physicalPEId coordinate target)) writes ∧
      Lm1FreePreparedWrites writes := by
  rw [executeParsedBlockFloatAtMAB.eq_1] at executed
  cases lowered : lowerParsedBlockFloat? expression with
  | none =>
      rw [lowered] at executed
      simp at executed
  | some accesses =>
      rw [lowered] at executed
      dsimp only at executed
      have destinationsEq := lowerParsedBlockFloat?_destinations expression accesses lowered
      split at executed
      · simp at executed
      · simp at executed
      · rename_i results ran
        rw [Id.run_pure] at executed
        simp only [StepResult.ok.injEq] at executed
        obtain ⟨writes, committed, clean⟩ :=
          executeParsedBlockFloatAtMAB_runCycles_clean accesses _ _
            (fun cycle buses files bar0 bar1 outputs results h target =>
              executeParsedBlockFloat_writeCycle_clean currentState hasSingleLineMask
                expression coordinate accesses
                (fun destination member bank width static =>
                  noLm1 destination (destinationsEq ▸ member) bank width static)
                _ (fun _ _ _ _ _ _ => rfl) cycle buses files bar0 bar1 outputs results h target)
            target [0, 1, 2, 3] _ _ _ _ results ran
        refine ⟨writes, ?_, clean⟩
        subst executed
        rw [executeParsedBlockFloatAtMAB_foldl_peRegisters_target noForward coordinate results
          target (List.finRange 4) currentState (List.nodup_finRange 4)
          (List.mem_finRange target)]
        simpa using committed

/-- **The block-float walk is a `.lm1`-free commit at a fixed PE.** -/
theorem executeParsedBlockFloatAtMABs_clean
    (readState : State) (expression : ParsedExpr) (noForward hasSingleLineMask : Bool)
    (p : PEId) :
    ∀ (coordinates : List MABCoordinate) (state : State) (next : State),
      executeParsedBlockFloatAtMABs readState state expression coordinates noForward
        hasSingleLineMask = .ok next →
      (∀ (coordinate : MABCoordinate) (state' next' : State), coordinate ∈ coordinates →
        executeParsedBlockFloatAtMAB readState state' expression coordinate noForward
          hasSingleLineMask = .ok next' →
        ∃ writes, next'.peRegisters p = commitParsedMaskedWrites (state'.peRegisters p) writes ∧
          Lm1FreePreparedWrites writes) →
      ∃ writes, next.peRegisters p = commitParsedMaskedWrites (state.peRegisters p) writes ∧
        Lm1FreePreparedWrites writes := by
  intro coordinates
  induction coordinates with
  | nil =>
      intro state next executed _
      simp only [executeParsedBlockFloatAtMABs.eq_1, StepResult.ok.injEq] at executed
      subst executed
      exact ⟨[], rfl, lm1FreePreparedWrites_nil⟩
  | cons coordinate rest ih =>
      intro state next executed stepCommit
      rw [executeParsedBlockFloatAtMABs.eq_2] at executed
      split at executed
      · simp at executed
      · simp at executed
      · rename_i middle ran
        obtain ⟨headWrites, head, headFree⟩ := stepCommit coordinate state middle (by simp) ran
        obtain ⟨tailWrites, tail, tailFree⟩ := ih middle next executed
          (fun coordinate' state' next' member ran' =>
            stepCommit coordinate' state' next' (List.mem_cons_of_mem _ member) ran')
        exact ⟨headWrites ++ tailWrites, by
            rw [tail, head, commitParsedMaskedWrites_append],
          lm1FreePreparedWrites_append headFree tailFree⟩

/-- **The block-float producer filter is a `.lm1`-free commit at PE 0.** -/
theorem executeParsedBlockFloatProducer_clean_commit
    (readState currentState next : State) (expressions : List ParsedExpr)
    (noForward hasSingleLineMask : Bool)
    (noLm1 : ∀ expression ∈ expressions.filter parsedExprIsBlockFloatProducer,
      WelcomeRowHasNoLm1Destination expression)
    (executed : executeParsedBlockFloatProducer readState currentState expressions noForward
      hasSingleLineMask = .ok next) :
    ∃ writes, next.peRegisters welcomePE =
      commitParsedMaskedWrites (currentState.peRegisters welcomePE) writes ∧
      Lm1FreePreparedWrites writes := by
  cases filtered : expressions.filter parsedExprIsBlockFloatProducer with
  | nil =>
      rw [executeParsedBlockFloatProducer, filtered] at executed
      simp only [StepResult.ok.injEq] at executed
      subst executed
      exact ⟨[], rfl, lm1FreePreparedWrites_nil⟩
  | cons expression rest =>
      cases rest with
      | nil =>
          rw [executeParsedBlockFloatProducer, filtered] at executed
          have expressionNoLm1 := noLm1 expression (by simp [filtered])
          refine executeParsedBlockFloatAtMABs_clean readState expression noForward
            hasSingleLineMask welcomePE allMABCoordinates currentState next executed ?_
          intro coordinate state' next' member ran
          by_cases zero : coordinate = ⟨0, 0, 0, 0⟩
          · subst zero
            obtain ⟨ws, committed, clean⟩ := executeParsedBlockFloatAtMAB_pe_clean readState
              state' expression ⟨0, 0, 0, 0⟩ noForward hasSingleLineMask expressionNoLm1 0
              next' ran
            exact ⟨ws, committed, clean⟩
          · have frame := executeParsedBlockFloatAtMAB_peRegisters_frame readState state'
              expression coordinate noForward hasSingleLineMask welcomePE
              (fun pe hpe => zero (physicalPEId_welcomePE_eq coordinate pe hpe.symm)) next' ran
            exact ⟨[], frame, lm1FreePreparedWrites_nil⟩
      | cons second remaining =>
          rw [executeParsedBlockFloatProducer, filtered] at executed
          simp at executed

/-- **The stage-level `.lm1` provenance proposition for the block-float stage.** -/
def WelcomePEBlockFloatStageLm1Provenance : Prop :=
    ∀ (readState currentState next : State) (expressions : List ParsedExpr)
      (noForward hasSingleLineMask : Bool),
      (∀ expression ∈ expressions.filter parsedExprIsBlockFloatProducer,
        WelcomeRowHasNoLm1Destination expression) →
      executeParsedBlockFloatProducer readState currentState expressions noForward
        hasSingleLineMask = .ok next →
      ∃ writes, next.peRegisters welcomePE =
        commitParsedMaskedWrites (currentState.peRegisters welcomePE) writes ∧
        Lm1FreePreparedWrites writes

/-- **The block-float stage's write-list-level `.lm1` provenance.** -/
theorem welcomePEBlockFloatStageLm1Provenance : WelcomePEBlockFloatStageLm1Provenance :=
  fun readState currentState next expressions noForward hasSingleLineMask noLm1 executed =>
    executeParsedBlockFloatProducer_clean_commit readState currentState next expressions
      noForward hasSingleLineMask noLm1 executed


/-! ## 4. The L1BM-to-PE stage -/

/-- A successful `lowerParsedL1ToPE?` exposes the row's destination list.  (A
provenance-specific restatement; the `WelcomeLm1FrameResidual.lean` version is
not imported here.) -/
theorem lowerParsedL1ToPE?_destinations_eq (expression : ParsedExpr)
    (access : ParsedL1ToPEAccess)
    (lowered : lowerParsedL1ToPE? expression = some access) :
    access.destinations = expression.destinations := by
  obtain ⟨op, sources, destinations, flush, text⟩ := expression
  simp only [lowerParsedL1ToPE?] at lowered
  split at lowered <;>
    (try split at lowered) <;>
    (try split at lowered) <;>
    (try simp at lowered) <;>
    (try (rw [Option.bind_eq_some_iff] at lowered
          obtain ⟨u, -, hsome⟩ := lowered
          simp only [Option.some.injEq] at hsome
          rw [← hsome]))

/-- **The L1BM-to-PE destination writer is a `.lm1`-free one-element commit.** -/
theorem writeParsedL1ToPEDestination?_clean_commit
    (files : IntegerRegisterFiles) (maskRegisters : Masks.RegisterFile)
    (destination : ParsedOperand) (context : ParsedIntegerContext)
    (output : IntegerALU.Bus) (cycle : Fin 4) (directive : ParsedMaskDirective)
    (hasSingleLineMask : Bool)
    (noLm1 : ∀ (bank : PEMemory.Bank) (width : PEMemory.Width),
      ParsedOperand.directDestinationBankWidth? destination = some (bank, width) →
        bank ≠ PEMemory.Bank.lm1) :
    ∀ (nextFiles : IntegerRegisterFiles) (barUpdate : Option (Bool × BitVec 12)),
      writeParsedL1ToPEDestination? files maskRegisters destination context output cycle
        directive hasSingleLineMask = some (nextFiles, barUpdate) →
      ∃ writes, nextFiles = commitParsedMaskedWrites files writes ∧
        Lm1FreePreparedWrites writes := by
  intro nextFiles barUpdate lowered
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
              have static := ParsedOperand.toDirectMemoryDestination?_bankWidth
                (ParsedOperand.mem access negated extended rounded mask) context.pe cycle
                context.bar0 context.bar1 context.tWord
              rw [h] at static
              have notLm1 : found.bank ≠ PEMemory.Bank.lm1 :=
                noLm1 found.bank found.width static.symm
              refine ⟨[⟨some found, none, PEMemory.unpackALUBus output, selection⟩],
                by simp [commitParsedMaskedWrites], ?_⟩
              intro write member
              simp only [List.mem_singleton] at member
              subst member
              simpa [PreparedParsedMaskedWrite.isLm1Write] using
                bank_beq_lm1_eq_false found.bank notLm1
  | bar lm1 width mask =>
      simp only [writeParsedL1ToPEDestination?] at lowered
      cases h : ParsedOperand.resolveMemoryWriteSelection? (ParsedOperand.bar lm1 width mask)
          (if lm1 = true then PEMemory.Bank.lm1 else PEMemory.Bank.lm0) maskRegisters
          cycle directive hasSingleLineMask with
      | none => simp [h] at lowered
      | some selection =>
          simp [h] at lowered
          obtain ⟨rfl, rfl⟩ := lowered
          exact ⟨[], rfl, lm1FreePreparedWrites_nil⟩
  | nowrite =>
      simp only [writeParsedL1ToPEDestination?] at lowered
      obtain ⟨rfl, rfl⟩ := Option.some.inj lowered
      exact ⟨[], rfl, lm1FreePreparedWrites_nil⟩
  | omr entry mask => simp [writeParsedL1ToPEDestination?] at lowered
  | forward kind neg ext rnd => simp [writeParsedL1ToPEDestination?] at lowered
  | fixed value => simp [writeParsedL1ToPEDestination?] at lowered
  | matrix side width row => simp [writeParsedL1ToPEDestination?] at lowered
  | l1bm width address => simp [writeParsedL1ToPEDestination?] at lowered
  | l2bm address l2b => simp [writeParsedL1ToPEDestination?] at lowered
  | dar value => simp [writeParsedL1ToPEDestination?] at lowered

/-- **The L1BM-to-PE destination loop is a `.lm1`-free commit.** -/
theorem executeParsedL1ToPE_writeDestinations_clean
    (currentState : State) (hasSingleLineMask : Bool) (maskRegisters : Masks.RegisterFile)
    (cycle : Fin 4) (context : ParsedIntegerContext) (output : IntegerALU.Bus) :
    ∀ (destinations : List ParsedOperand) (files : IntegerRegisterFiles) (bar0 bar1 : BitVec 12)
      (nextFiles : IntegerRegisterFiles) (nextBar0 nextBar1 : BitVec 12),
      (∀ destination ∈ destinations,
        ∀ (bank : PEMemory.Bank) (width : PEMemory.Width),
          ParsedOperand.directDestinationBankWidth? destination = some (bank, width) →
            bank ≠ PEMemory.Bank.lm1) →
      executeParsedL1ToPEAtPEs.writeCycles.writeDestinations currentState hasSingleLineMask
        maskRegisters cycle context output destinations files bar0 bar1 =
        some (nextFiles, nextBar0, nextBar1) →
      ∃ writes, nextFiles = commitParsedMaskedWrites files writes ∧
        Lm1FreePreparedWrites writes := by
  intro destinations
  induction destinations with
  | nil =>
      intro files bar0 bar1 nextFiles nextBar0 nextBar1 noLm1 executed
      rw [executeParsedL1ToPEAtPEs.writeCycles.writeDestinations] at executed
      obtain ⟨rfl, rfl, rfl⟩ := Option.some.inj executed
      exact ⟨[], rfl, lm1FreePreparedWrites_nil⟩
  | cons destination rest ih =>
      intro files bar0 bar1 nextFiles nextBar0 nextBar1 noLm1 executed
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
              obtain ⟨headWrites, head, headFree⟩ :=
                writeParsedL1ToPEDestination?_clean_commit files maskRegisters destination
                  { context with bar0 := bar0, bar1 := bar1 } output cycle
                  currentState.maskDirective hasSingleLineMask
                  (fun bank width static => noLm1 destination (by simp) bank width static)
                  writeFiles none lowered
              obtain ⟨tailWrites, tail, tailFree⟩ := ih writeFiles bar0 bar1 nextFiles nextBar0
                nextBar1 (fun item member => noLm1 item (List.mem_cons_of_mem _ member)) executed
              exact ⟨headWrites ++ tailWrites, by
                  rw [tail, head, commitParsedMaskedWrites_append],
                lm1FreePreparedWrites_append headFree tailFree⟩
          | some update =>
              obtain ⟨lm1, value⟩ := update
              cases lm1 with
              | false =>
                  rw [executeParsedL1ToPE_writeDestinations_cons_some_false currentState
                    hasSingleLineMask maskRegisters cycle context output destination rest files
                    bar0 bar1 writeFiles value lowered] at executed
                  obtain ⟨headWrites, head, headFree⟩ :=
                    writeParsedL1ToPEDestination?_clean_commit files maskRegisters destination
                      { context with bar0 := bar0, bar1 := bar1 } output cycle
                      currentState.maskDirective hasSingleLineMask
                      (fun bank width static => noLm1 destination (by simp) bank width static)
                      writeFiles (some (false, value)) lowered
                  obtain ⟨tailWrites, tail, tailFree⟩ := ih writeFiles value bar1 nextFiles
                    nextBar0 nextBar1 (fun item member => noLm1 item (List.mem_cons_of_mem _ member))
                    executed
                  exact ⟨headWrites ++ tailWrites, by
                      rw [tail, head, commitParsedMaskedWrites_append],
                    lm1FreePreparedWrites_append headFree tailFree⟩
              | true =>
                  rw [executeParsedL1ToPE_writeDestinations_cons_some_true currentState
                    hasSingleLineMask maskRegisters cycle context output destination rest files
                    bar0 bar1 writeFiles value lowered] at executed
                  obtain ⟨headWrites, head, headFree⟩ :=
                    writeParsedL1ToPEDestination?_clean_commit files maskRegisters destination
                      { context with bar0 := bar0, bar1 := bar1 } output cycle
                      currentState.maskDirective hasSingleLineMask
                      (fun bank width static => noLm1 destination (by simp) bank width static)
                      writeFiles (some (true, value)) lowered
                  obtain ⟨tailWrites, tail, tailFree⟩ := ih writeFiles bar0 value nextFiles
                    nextBar0 nextBar1 (fun item member => noLm1 item (List.mem_cons_of_mem _ member))
                    executed
                  exact ⟨headWrites ++ tailWrites, by
                      rw [tail, head, commitParsedMaskedWrites_append],
                    lm1FreePreparedWrites_append headFree tailFree⟩

/-- **The L1BM-to-PE cycle loop is a `.lm1`-free commit.** -/
theorem executeParsedL1ToPE_writeCycles_clean
    (readState currentState : State) (expression : ParsedExpr) (access : ParsedL1ToPEAccess)
    (hasSingleLineMask : Bool) (pe : PEId) (coordinates readContext : ParsedIntegerContext)
    (maskRegisters : Masks.RegisterFile)
    (noLm1 : ∀ destination ∈ access.destinations,
      ∀ (bank : PEMemory.Bank) (width : PEMemory.Width),
        ParsedOperand.directDestinationBankWidth? destination = some (bank, width) →
          bank ≠ PEMemory.Bank.lm1) :
    ∀ (cycles : List (Fin 4)) (files : IntegerRegisterFiles) (bar0 bar1 : BitVec 12)
      (nextFiles : IntegerRegisterFiles) (nextBar0 nextBar1 : BitVec 12),
      executeParsedL1ToPEAtPEs.writeCycles readState currentState expression access
        hasSingleLineMask pe coordinates readContext maskRegisters cycles files bar0 bar1 =
        .ok (nextFiles, nextBar0, nextBar1) →
      ∃ writes, nextFiles = commitParsedMaskedWrites files writes ∧
        Lm1FreePreparedWrites writes := by
  intro cycles
  induction cycles with
  | nil =>
      intro files bar0 bar1 nextFiles nextBar0 nextBar1 executed
      rw [executeParsedL1ToPEAtPEs.writeCycles] at executed
      obtain ⟨rfl, rfl, rfl⟩ := StepResult.ok.inj executed
      exact ⟨[], rfl, lm1FreePreparedWrites_nil⟩
  | cons cycle rest ih =>
      intro files bar0 bar1 nextFiles nextBar0 nextBar1 executed
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
            obtain ⟨headWrites, head, headFree⟩ :=
              executeParsedL1ToPE_writeDestinations_clean currentState hasSingleLineMask
                maskRegisters cycle _ _ access.destinations files bar0 bar1 middleFiles
                middleBar0 middleBar1 noLm1 wrote
            obtain ⟨tailWrites, tail, tailFree⟩ := ih middleFiles middleBar0 middleBar1
              nextFiles nextBar0 nextBar1 executed
            exact ⟨headWrites ++ tailWrites, by
                rw [tail, head, commitParsedMaskedWrites_append],
              lm1FreePreparedWrites_append headFree tailFree⟩

/-- **The L1BM-to-PE walk is a `.lm1`-free commit at every visited PE.** -/
theorem executeParsedL1ToPEAtPEs_clean
    (readState : State) (expression : ParsedExpr) (access : ParsedL1ToPEAccess)
    (noForward hasSingleLineMask usePreIssueMask : Bool)
    (noLm1 : ∀ destination ∈ access.destinations,
      ∀ (bank : PEMemory.Bank) (width : PEMemory.Width),
        ParsedOperand.directDestinationBankWidth? destination = some (bank, width) →
          bank ≠ PEMemory.Bank.lm1) :
    ∀ (pes : List PEId) (state : State) (p : PEId) (next : State),
      executeParsedL1ToPEAtPEs readState state expression access pes noForward
        hasSingleLineMask usePreIssueMask = .ok next →
      ∃ writes, next.peRegisters p = commitParsedMaskedWrites (state.peRegisters p) writes ∧
        Lm1FreePreparedWrites writes := by
  intro pes
  induction pes with
  | nil =>
      intro state p next executed
      simp only [executeParsedL1ToPEAtPEs.eq_1, StepResult.ok.injEq] at executed
      subst executed
      exact ⟨[], rfl, lm1FreePreparedWrites_nil⟩
  | cons pe rest ih =>
      intro state p next executed
      rw [executeParsedL1ToPEAtPEs.eq_2] at executed
      split at executed
      · simp at executed
      · simp only [] at executed
        split at executed
        · simp at executed
        · simp at executed
        · rename_i files bar0 bar1 ran
          obtain ⟨tailWrites, tail, tailFree⟩ := ih _ p next executed
          by_cases same : p = pe
          · rw [same] at tail ⊢
            obtain ⟨headWrites, head, headFree⟩ :=
              executeParsedL1ToPE_writeCycles_clean readState state expression access
                hasSingleLineMask pe _ _ _ noLm1 [0, 1, 2, 3] (state.peRegisters pe) _ _ files
                bar0 bar1 ran
            refine ⟨headWrites ++ tailWrites, ?_,
              lm1FreePreparedWrites_append headFree tailFree⟩
            rw [tail]
            dsimp only
            rw [head, commitParsedMaskedWrites_append]
            simp
          · refine ⟨tailWrites, ?_, tailFree⟩
            rw [tail]
            simp [same]

/-- **The L1BM-to-PE producer is a `.lm1`-free commit at PE 0.** -/
theorem executeParsedL1ToPEProducer_clean_commit
    (readState currentState next : State) (expression : ParsedExpr)
    (noForward hasSingleLineMask usePreIssueMask : Bool)
    (noLm1 : WelcomeRowHasNoLm1Destination expression)
    (executed : executeParsedL1ToPEProducer readState currentState expression noForward
      hasSingleLineMask usePreIssueMask = .ok next) :
    ∃ writes, next.peRegisters welcomePE =
      commitParsedMaskedWrites (currentState.peRegisters welcomePE) writes ∧
      Lm1FreePreparedWrites writes := by
  cases lowered : lowerParsedL1ToPE? expression with
  | none =>
      rw [executeParsedL1ToPEProducer, lowered] at executed
      simp at executed
  | some access =>
      rw [executeParsedL1ToPEProducer, lowered] at executed
      have destinationsEq := lowerParsedL1ToPE?_destinations_eq expression access lowered
      exact executeParsedL1ToPEAtPEs_clean readState expression access noForward
        hasSingleLineMask usePreIssueMask
        (fun destination member bank width static =>
          noLm1 destination (destinationsEq ▸ member) bank width static)
        (List.finRange 4096) currentState welcomePE next executed

/-- **The L1BM-to-PE producer filter is a `.lm1`-free commit at PE 0.** -/
theorem executeParsedL1ToPEProducers_clean_commit
    (readState currentState next : State) (expressions : List ParsedExpr)
    (noForward hasSingleLineMask usePreIssueMask : Bool)
    (noLm1 : ∀ expression ∈ expressions.filter parsedExprIsL1ToPEProducer,
      WelcomeRowHasNoLm1Destination expression)
    (executed : executeParsedL1ToPEProducers readState currentState expressions noForward
      hasSingleLineMask usePreIssueMask = .ok next) :
    ∃ writes, next.peRegisters welcomePE =
      commitParsedMaskedWrites (currentState.peRegisters welcomePE) writes ∧
      Lm1FreePreparedWrites writes := by
  cases filtered : expressions.filter parsedExprIsL1ToPEProducer with
  | nil =>
      rw [executeParsedL1ToPEProducers, filtered] at executed
      simp only [StepResult.ok.injEq] at executed
      subst executed
      exact ⟨[], rfl, lm1FreePreparedWrites_nil⟩
  | cons expression rest =>
      cases rest with
      | nil =>
          rw [executeParsedL1ToPEProducers, filtered] at executed
          exact executeParsedL1ToPEProducer_clean_commit readState currentState next expression
            noForward hasSingleLineMask usePreIssueMask
            (noLm1 expression (by simp [filtered])) executed
      | cons second remaining =>
          rw [executeParsedL1ToPEProducers, filtered] at executed
          simp at executed

/-- **The stage-level `.lm1` provenance proposition for the L1BM-to-PE stage.** -/
def WelcomePEL1ToPEStageLm1Provenance : Prop :=
    ∀ (readState currentState next : State) (expressions : List ParsedExpr)
      (noForward hasSingleLineMask usePreIssueMask : Bool),
      (∀ expression ∈ expressions.filter parsedExprIsL1ToPEProducer,
        WelcomeRowHasNoLm1Destination expression) →
      executeParsedL1ToPEProducers readState currentState expressions noForward
        hasSingleLineMask usePreIssueMask = .ok next →
      ∃ writes, next.peRegisters welcomePE =
        commitParsedMaskedWrites (currentState.peRegisters welcomePE) writes ∧
        Lm1FreePreparedWrites writes

/-- **The L1BM-to-PE stage's write-list-level `.lm1` provenance.** -/
theorem welcomePEL1ToPEStageLm1Provenance : WelcomePEL1ToPEStageLm1Provenance :=
  fun readState currentState next expressions noForward hasSingleLineMask usePreIssueMask noLm1
    executed =>
    executeParsedL1ToPEProducers_clean_commit readState currentState next expressions
      noForward hasSingleLineMask usePreIssueMask noLm1 executed


/-! ## 5. The matrix-MAU/write stage

The matrix-MAU stage writes through the shared single-destination writer
`writeParsedMslMsrDestination?` (with a data-poison skip that produces no write),
installs the four per-MAB PE files with `commitParsedMatrixMAUPEState`, walks the
1024 MAB coordinates, propagates poison and finally runs the matrix-write stage,
which preserves every PE register file.  The provenance induction is the one of
`WelcomeMatrixMAUCommit.lean` with the clean-list conjunct carried along. -/

/-- **The matrix-MAU destination loop is a `.lm1`-free commit.** -/
theorem writeParsedMatrixMAUDestinationsAtPE_clean
    (currentState : State) (expression : ParsedExpr) (coordinate : MABCoordinate)
    (pe cycle : Fin 4) (poison hasSingleLineMask : Bool) (output : IntegerALU.Bus)
    (flags : BitVec 4) :
    ∀ (destinations : List ParsedOperand) (files : IntegerRegisterFiles) (bar0 bar1 : BitVec 12)
      (nextFiles : IntegerRegisterFiles) (nextBar0 nextBar1 : BitVec 12),
      (∀ destination ∈ destinations,
        ∀ (bank : PEMemory.Bank) (width : PEMemory.Width),
          ParsedOperand.directDestinationBankWidth? destination = some (bank, width) →
            bank ≠ PEMemory.Bank.lm1) →
      writeParsedMatrixMAUDestinationsAtPE currentState expression coordinate pe cycle poison
        hasSingleLineMask output flags destinations files bar0 bar1 = .ok (nextFiles, nextBar0, nextBar1) →
      ∃ writes, nextFiles = commitParsedMaskedWrites files writes ∧
        Lm1FreePreparedWrites writes := by
  intro destinations
  induction destinations with
  | nil =>
      intro files bar0 bar1 nextFiles nextBar0 nextBar1 noLm1 executed
      rw [writeParsedMatrixMAUDestinationsAtPE.eq_1] at executed
      obtain ⟨rfl, rfl, rfl⟩ := StepResult.ok.inj executed
      exact ⟨[], rfl, lm1FreePreparedWrites_nil⟩
  | cons destination rest ih =>
      intro files bar0 bar1 nextFiles nextBar0 nextBar1 noLm1 executed
      rw [writeParsedMatrixMAUDestinationsAtPE.eq_2] at executed
      have headNoLm1 : ∀ (bank : PEMemory.Bank) (width : PEMemory.Width),
          ParsedOperand.directDestinationBankWidth? destination = some (bank, width) →
            bank ≠ PEMemory.Bank.lm1 :=
        fun bank width static => noLm1 destination (by simp) bank width static
      cases destination
      case omr entry mask =>
        simp only [Id.run] at executed
        split at executed
        · simp at executed
        · simp only [parsedMatrixMAUDestinationDataPoisonApplies] at executed
          simp only [Bool.false_eq_true, ite_false] at executed
          split at executed
          · simp at executed
          · rename_i write h
            have tail := executed
            obtain ⟨headWrites, head, headFree⟩ :=
              writeParsedMslMsrDestination?_clean_commit files _ _ output flags
                cycle currentState.maskDirective hasSingleLineMask
                headNoLm1 write h
            obtain ⟨tailWrites, tail', tailFree⟩ := ih write.files _ _ nextFiles _ _
              (fun item member => noLm1 item (List.mem_cons_of_mem _ member)) tail
            exact ⟨headWrites ++ tailWrites, by
                rw [tail', head, commitParsedMaskedWrites_append],
              lm1FreePreparedWrites_append headFree tailFree⟩
      all_goals
        simp only [Id.run] at executed
        split at executed
        · split at executed
          · simp at executed
          · simp at executed
          · rename_i h
            have tail := executed
            obtain ⟨tailWrites, tail', tailFree⟩ := ih files bar0 bar1 nextFiles nextBar0
              nextBar1 (fun item member => noLm1 item (List.mem_cons_of_mem _ member)) tail
            exact ⟨tailWrites, tail', tailFree⟩
        · split at executed
          · simp at executed
          · rename_i write h
            have tail := executed
            obtain ⟨headWrites, head, headFree⟩ :=
              writeParsedMslMsrDestination?_clean_commit files _ _ output flags
                cycle currentState.maskDirective hasSingleLineMask
                headNoLm1 write h
            obtain ⟨tailWrites, tail', tailFree⟩ := ih write.files _ _ nextFiles _ _
              (fun item member => noLm1 item (List.mem_cons_of_mem _ member)) tail
            exact ⟨headWrites ++ tailWrites, by
                rw [tail', head, commitParsedMaskedWrites_append],
              lm1FreePreparedWrites_append headFree tailFree⟩

/-- **The matrix-MAU four-PE loop of one cycle is a `.lm1`-free commit at any
target PE.** -/
theorem executeParsedMatrixMAUPEWritesAtCycle_clean
    (currentState : State) (expression : ParsedExpr) (coordinate : MABCoordinate)
    (hasSingleLineMask : Bool) (cycle : Fin 4) (buses : Fin 4 → IntegerALU.Bus)
    (flags : Fin 4 → BitVec 4) (poison : Bool) (target : Fin 4)
    (noLm1 : WelcomeRowHasNoLm1Destination expression) :
    ∀ (pes : List (Fin 4)) (accum next : ParsedMatrixMAUWriteAccum),
      executeParsedMatrixMAUPEWritesAtCycle currentState expression coordinate hasSingleLineMask
        cycle buses flags poison pes accum = .ok next →
      ∃ writes, next.files target = commitParsedMaskedWrites (accum.files target) writes ∧
        Lm1FreePreparedWrites writes := by
  intro pes
  induction pes with
  | nil =>
      intro accum next executed
      rw [executeParsedMatrixMAUPEWritesAtCycle.eq_1] at executed
      obtain rfl := StepResult.ok.inj executed
      exact ⟨[], rfl, lm1FreePreparedWrites_nil⟩
  | cons pe rest ih =>
      intro accum next executed
      rw [executeParsedMatrixMAUPEWritesAtCycle.eq_2] at executed
      dsimp only at executed
      cases flush : resolveFlushSelection? expression.flush (accum.files pe).maskRegisters cycle with
      | none =>
          rw [flush] at executed
          simp at executed
      | some flushSelection =>
          rw [flush] at executed
          dsimp only at executed
          cases wrote : writeParsedMatrixMAUDestinationsAtPE currentState expression coordinate pe
              cycle poison hasSingleLineMask (parsedOutputAfterFlush flushSelection (buses pe))
              (flags pe) expression.destinations (accum.files pe) (accum.bar0 pe)
              (accum.bar1 pe) with
          | failure =>
              rw [wrote] at executed
              simp at executed
          | unknown =>
              rw [wrote] at executed
              simp at executed
          | ok result =>
              obtain ⟨nextFiles, nextBar0, nextBar1⟩ := result
              rw [wrote] at executed
              have tail := executed
              obtain ⟨headWrites, head, headFree⟩ :=
                writeParsedMatrixMAUDestinationsAtPE_clean currentState expression coordinate
                  pe cycle poison hasSingleLineMask
                  (parsedOutputAfterFlush flushSelection (buses pe)) (flags pe)
                  expression.destinations (accum.files pe) (accum.bar0 pe) (accum.bar1 pe)
                  nextFiles nextBar0 nextBar1
                  (fun destination member bank width static =>
                    noLm1 destination member bank width static)
                  wrote
              obtain ⟨tailWrites, tail', tailFree⟩ := ih _ next tail
              by_cases same : target = pe
              · subst same
                refine ⟨headWrites ++ tailWrites, ?_,
                  lm1FreePreparedWrites_append headFree tailFree⟩
                rw [tail']
                simp only [beq_self_eq_true, ite_true]
                rw [head, commitParsedMaskedWrites_append]
              · refine ⟨tailWrites, ?_, tailFree⟩
                rw [tail']
                have different : (target == pe) = false := by
                  simp [same]
                simp [different]

/-- **The matrix-MAU four-cycle loop of one coordinate is a `.lm1`-free commit
at any target PE.** -/
theorem executeParsedMatrixMAUWriteCycles_clean
    (readState currentState : State) (expression : ParsedExpr) (coordinate : MABCoordinate)
    (hasSingleLineMask : Bool) (target : Fin 4)
    (noLm1 : WelcomeRowHasNoLm1Destination expression) :
    ∀ (cycles : List (Fin 4)) (accum next : ParsedMatrixMAUWriteAccum),
      executeParsedMatrixMAUWriteCycles readState currentState expression coordinate
        hasSingleLineMask cycles accum = .ok next →
      ∃ writes, next.files target = commitParsedMaskedWrites (accum.files target) writes ∧
        Lm1FreePreparedWrites writes := by
  intro cycles
  induction cycles with
  | nil =>
      intro accum next executed
      rw [executeParsedMatrixMAUWriteCycles.eq_1] at executed
      obtain rfl := StepResult.ok.inj executed
      exact ⟨[], rfl, lm1FreePreparedWrites_nil⟩
  | cons cycle rest ih =>
      intro accum next executed
      rw [executeParsedMatrixMAUWriteCycles.eq_2] at executed
      cases calculation : executeParsedMatrixMAUAtMAB readState coordinate expression cycle with
      | failure =>
          rw [calculation] at executed
          simp at executed
      | unknown =>
          rw [calculation] at executed
          simp at executed
      | ok result =>
          rw [calculation] at executed
          dsimp only at executed
          cases writes : executeParsedMatrixMAUPEWritesAtCycle currentState expression coordinate
              hasSingleLineMask cycle result.1 result.2.1 result.2.2 (List.finRange 4) accum with
          | failure =>
              rw [writes] at executed
              simp at executed
          | unknown =>
              rw [writes] at executed
              simp at executed
          | ok nextAccum =>
              rw [writes] at executed
              have tail := executed
              obtain ⟨headWrites, head, headFree⟩ :=
                executeParsedMatrixMAUPEWritesAtCycle_clean currentState expression coordinate
                  hasSingleLineMask cycle result.1 result.2.1 result.2.2 target noLm1
                  (List.finRange 4) accum nextAccum writes
              obtain ⟨tailWrites, tail', tailFree⟩ := ih nextAccum next tail
              exact ⟨headWrites ++ tailWrites, by
                  rw [tail', head, commitParsedMaskedWrites_append],
                lm1FreePreparedWrites_append headFree tailFree⟩

/-- **The repackaged per-coordinate files are `.lm1`-free commits.** -/
theorem executeParsedMatrixMAUPEWritesAtMAB_files_clean
    (readState currentState : State) (expression : ParsedExpr) (coordinate : MABCoordinate)
    (hasSingleLineMask : Bool) (files : Fin 4 → IntegerRegisterFiles)
    (bar0 bar1 : Fin 4 → BitVec 12) (outputs : Fin 4 → Fin 4 → IntegerALU.Bus)
    (poisoned : Fin 4 → Bool) (target : Fin 4)
    (noLm1 : WelcomeRowHasNoLm1Destination expression)
    (executed : executeParsedMatrixMAUPEWritesAtMAB readState currentState expression coordinate
      hasSingleLineMask = .ok (files, bar0, bar1, outputs, poisoned)) :
    ∃ writes, files target =
      commitParsedMaskedWrites (currentState.peRegisters (physicalPEId coordinate target)) writes ∧
      Lm1FreePreparedWrites writes := by
  rw [executeParsedMatrixMAUPEWritesAtMAB.eq_1] at executed
  cases ran : executeParsedMatrixMAUWriteCycles readState currentState expression coordinate
      hasSingleLineMask (List.finRange 4)
      { files := fun pe => currentState.peRegisters (physicalPEId coordinate pe)
        bar0 := fun pe => (currentState.peContext (physicalPEId coordinate pe)).bar0
        bar1 := fun pe => (currentState.peContext (physicalPEId coordinate pe)).bar1
        outputs := fun _ _ => ⟨0, 0⟩
        poisoned := fun _ => false } with
  | failure =>
      rw [ran] at executed
      simp at executed
  | unknown =>
      rw [ran] at executed
      simp at executed
  | ok accum =>
      rw [ran] at executed
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := StepResult.ok.inj executed
      exact executeParsedMatrixMAUWriteCycles_clean readState currentState expression coordinate
        hasSingleLineMask target noLm1 (List.finRange 4)
        { files := fun pe => currentState.peRegisters (physicalPEId coordinate pe)
          bar0 := fun pe => (currentState.peContext (physicalPEId coordinate pe)).bar0
          bar1 := fun pe => (currentState.peContext (physicalPEId coordinate pe)).bar1
          outputs := fun _ _ => ⟨0, 0⟩
          poisoned := fun _ => false } accum ran

/-- **The per-coordinate matrix-MAU transition is a `.lm1`-free commit at each
of its four PEs.** -/
theorem executeParsedMatrixMAUTransitionAtMAB_pe_clean
    (readState currentState next : State) (expression : ParsedExpr) (coordinate : MABCoordinate)
    (noForward hasSingleLineMask : Bool) (noLm1 : WelcomeRowHasNoLm1Destination expression)
    (target : Fin 4)
    (executed : executeParsedMatrixMAUTransitionAtMAB readState currentState expression coordinate
      noForward hasSingleLineMask = .ok next) :
    ∃ writes, next.peRegisters (physicalPEId coordinate target) =
      commitParsedMaskedWrites (currentState.peRegisters (physicalPEId coordinate target)) writes ∧
      Lm1FreePreparedWrites writes := by
  rw [executeParsedMatrixMAUTransitionAtMAB.eq_1] at executed
  cases ran : executeParsedMatrixMAUPEWritesAtMAB readState currentState expression coordinate
      hasSingleLineMask with
  | failure =>
      rw [ran] at executed
      simp at executed
  | unknown =>
      rw [ran] at executed
      simp at executed
  | ok result =>
      rw [ran] at executed
      obtain ⟨files, bar0, bar1, outputs, poisoned⟩ := result
      simp only [StepResult.ok.injEq] at executed
      subst executed
      obtain ⟨writes, committed, clean⟩ :=
        executeParsedMatrixMAUPEWritesAtMAB_files_clean readState currentState expression
          coordinate hasSingleLineMask files bar0 bar1 outputs poisoned target noLm1 ran
      refine ⟨writes, ?_, clean⟩
      rw [commitParsedMatrixMAUPEState_eq_foldl]
      rw [commitParsedMatrixMAUPEState_foldl_peRegisters_target coordinate noForward files bar0
        bar1 outputs poisoned target (List.finRange 4) currentState (List.nodup_finRange 4)
        (List.mem_finRange target)]
      exact committed

/-- **The matrix-MAU walk over the MAB is a `.lm1`-free commit at a fixed PE.** -/
theorem executeParsedMatrixMAUAtMABs_clean
    (readState : State) (expression : ParsedExpr) (noForward hasSingleLineMask : Bool)
    (p : PEId) :
    ∀ (coordinates : List MABCoordinate) (state next : State),
      executeParsedMatrixMAUAtMABs readState state expression coordinates noForward
        hasSingleLineMask = .ok next →
      (∀ (coordinate : MABCoordinate) (state' next' : State), coordinate ∈ coordinates →
        executeParsedMatrixMAUTransitionAtMAB readState state' expression coordinate noForward
          hasSingleLineMask = .ok next' →
        ∃ writes, next'.peRegisters p = commitParsedMaskedWrites (state'.peRegisters p) writes ∧
          Lm1FreePreparedWrites writes) →
      ∃ writes, next.peRegisters p = commitParsedMaskedWrites (state.peRegisters p) writes ∧
        Lm1FreePreparedWrites writes := by
  intro coordinates
  induction coordinates with
  | nil =>
      intro state next executed _
      rw [executeParsedMatrixMAUAtMABs.eq_1] at executed
      obtain rfl := StepResult.ok.inj executed
      exact ⟨[], rfl, lm1FreePreparedWrites_nil⟩
  | cons coordinate rest ih =>
      intro state next executed stepCommit
      rw [executeParsedMatrixMAUAtMABs.eq_2] at executed
      cases ran : executeParsedMatrixMAUTransitionAtMAB readState state expression coordinate
          noForward hasSingleLineMask with
      | failure =>
          rw [ran] at executed
          simp at executed
      | unknown =>
          rw [ran] at executed
          simp at executed
      | ok middle =>
          rw [ran] at executed
          obtain ⟨headWrites, head, headFree⟩ :=
            stepCommit coordinate state middle (by simp) ran
          obtain ⟨tailWrites, tail, tailFree⟩ := ih middle next executed
            (fun coordinate' state' next' member ran' =>
              stepCommit coordinate' state' next' (List.mem_cons_of_mem _ member) ran')
          exact ⟨headWrites ++ tailWrites, by
              rw [tail, head, commitParsedMaskedWrites_append],
            lm1FreePreparedWrites_append headFree tailFree⟩

/-- **The matrix-MAU producer is a `.lm1`-free PE 0 commit.** -/
theorem executeParsedMatrixMAUProducer_clean_commit
    (readState currentState next : State) (expressions : List ParsedExpr)
    (noForward hasSingleLineMask : Bool)
    (noLm1 : ∀ expression ∈ expressions.filter parsedExprIsMatrixMAUProducer,
      WelcomeRowHasNoLm1Destination expression)
    (executed : executeParsedMatrixMAUProducer readState currentState expressions noForward
      hasSingleLineMask = .ok next) :
    ∃ writes, next.peRegisters welcomePE =
      commitParsedMaskedWrites (currentState.peRegisters welcomePE) writes ∧
      Lm1FreePreparedWrites writes := by
  cases filtered : expressions.filter parsedExprIsMatrixMAUProducer with
  | nil =>
      rw [executeParsedMatrixMAUProducer.eq_1, filtered] at executed
      dsimp only at executed
      simp only [StepResult.ok.injEq] at executed
      subst executed
      exact ⟨[], rfl, lm1FreePreparedWrites_nil⟩
  | cons expression rest =>
      cases rest with
      | nil =>
          have expressionNoLm1 := noLm1 expression (by simp [filtered])
          rw [executeParsedMatrixMAUProducer.eq_1, filtered] at executed
          dsimp only at executed
          cases ran : executeParsedMatrixMAUAtMABs readState currentState expression
              allMABCoordinates noForward hasSingleLineMask with
          | failure =>
              rw [ran] at executed
              simp at executed
          | unknown =>
              rw [ran] at executed
              simp at executed
          | ok afterMAU =>
              rw [ran] at executed
              simp only [StepResult.ok.injEq] at executed
              subst executed
              have stepCommit : ∀ (coordinate : MABCoordinate) (state' next' : State),
                  coordinate ∈ allMABCoordinates →
                  executeParsedMatrixMAUTransitionAtMAB readState state' expression coordinate
                    noForward hasSingleLineMask = .ok next' →
                  ∃ writes, next'.peRegisters welcomePE =
                    commitParsedMaskedWrites (state'.peRegisters welcomePE) writes ∧
                    Lm1FreePreparedWrites writes := by
                intro coordinate state' next' _ ran'
                by_cases zero : coordinate = ⟨0, 0, 0, 0⟩
                · subst zero
                  obtain ⟨ws, committedHead, clean⟩ :=
                    executeParsedMatrixMAUTransitionAtMAB_pe_clean readState state' next'
                      expression ⟨0, 0, 0, 0⟩ noForward hasSingleLineMask expressionNoLm1 0 ran'
                  exact ⟨ws, by simpa [physicalPEId, welcomePE] using committedHead, clean⟩
                · exact ⟨[], executeParsedMatrixMAUTransitionAtMAB_peRegisters_frame readState
                    state' next' expression coordinate noForward hasSingleLineMask welcomePE
                    (fun pe hpe => zero (physicalPEId_welcomePE_eq coordinate pe hpe.symm)) ran',
                    lm1FreePreparedWrites_nil⟩
              obtain ⟨writes, committed, clean⟩ :=
                executeParsedMatrixMAUAtMABs_clean readState expression noForward
                  hasSingleLineMask welcomePE allMABCoordinates currentState
                  afterMAU ran stepCommit
              refine ⟨writes, ?_, clean⟩
              rw [propagateParsedMatrixMAUPoison_preserves_peRegisters]
              exact committed
      | cons second remaining =>
          rw [executeParsedMatrixMAUProducer.eq_1, filtered] at executed
          dsimp only at executed
          simp at executed

/-- **The matrix-MAU/write stage is a `.lm1`-free PE 0 commit.** -/
theorem executeParsedMatrixMAUAndWrites_clean_commit
    (readState currentState next : State) (expressions : List ParsedExpr)
    (noForward hasSingleLineMask : Bool)
    (noLm1 : ∀ expression ∈ expressions.filter parsedExprIsMatrixMAUProducer,
      WelcomeRowHasNoLm1Destination expression)
    (executed : executeParsedMatrixMAUAndWrites readState currentState expressions noForward
      hasSingleLineMask = .ok next) :
    ∃ writes, next.peRegisters welcomePE =
      commitParsedMaskedWrites (currentState.peRegisters welcomePE) writes ∧
      Lm1FreePreparedWrites writes := by
  rw [executeParsedMatrixMAUAndWrites.eq_1] at executed
  cases producer : executeParsedMatrixMAUProducer readState currentState expressions noForward
      hasSingleLineMask with
  | failure =>
      rw [producer] at executed
      simp at executed
  | unknown =>
      rw [producer] at executed
      simp at executed
  | ok afterMAU =>
      rw [producer] at executed
      obtain ⟨writes, committed, clean⟩ :=
        executeParsedMatrixMAUProducer_clean_commit readState currentState afterMAU expressions
          noForward hasSingleLineMask noLm1 producer
      have frame := executeParsedMatrixWritesAtMABs_preserves_pe_state readState afterMAU next
        allMABCoordinates expressions executed
      exact ⟨writes, by rw [frame.1]; exact committed, clean⟩

/-- **The stage-level `.lm1` provenance proposition for the matrix-MAU/write stage.** -/
def WelcomePEMatrixMAUStageLm1Provenance : Prop :=
    ∀ (readState currentState next : State) (expressions : List ParsedExpr)
      (noForward hasSingleLineMask : Bool),
      (∀ expression ∈ expressions.filter parsedExprIsMatrixMAUProducer,
        WelcomeRowHasNoLm1Destination expression) →
      executeParsedMatrixMAUAndWrites readState currentState expressions noForward
        hasSingleLineMask = .ok next →
      ∃ writes, next.peRegisters welcomePE =
        commitParsedMaskedWrites (currentState.peRegisters welcomePE) writes ∧
        Lm1FreePreparedWrites writes

/-- **The matrix-MAU/write stage's write-list-level `.lm1` provenance.** -/
theorem welcomePEMatrixMAUStageLm1Provenance : WelcomePEMatrixMAUStageLm1Provenance :=
  fun readState currentState next expressions noForward hasSingleLineMask noLm1 executed =>
    executeParsedMatrixMAUAndWrites_clean_commit readState currentState next expressions
      noForward hasSingleLineMask noLm1 executed


/-! ## 6. The five middle-stage obligations bundled -/

/-- **The five middle-stage `.lm1` provenance obligations, bundled.** -/
def WelcomePEStageLm1ProvenanceForm : Prop :=
  WelcomePEMslMsrStageLm1Provenance ∧ WelcomePEFloatReluStageLm1Provenance ∧
    WelcomePEBlockFloatStageLm1Provenance ∧ WelcomePEMatrixMAUStageLm1Provenance ∧
      WelcomePEL1ToPEStageLm1Provenance

/-- **All five middle-stage write-list-level provenance obligations hold.** -/
theorem welcomePEStageLm1ProvenanceForm : WelcomePEStageLm1ProvenanceForm :=
  ⟨welcomePEMslMsrStageLm1Provenance, welcomePEFloatReluStageLm1Provenance,
    welcomePEBlockFloatStageLm1Provenance, welcomePEMatrixMAUStageLm1Provenance,
    welcomePEL1ToPEStageLm1Provenance⟩

end ProofsLean.MNCore
