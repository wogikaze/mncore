import ProofsLean.WelcomeAssembly

/-! # Per-stage commit obligations at PE 0

`WelcomeAssembly.lean` (§4) reduces the line-level PE 0 write shape of a `.pe`
line to six per-stage commit obligations, stated there as the `Prop`s
`WelcomePEMslMsrStageCommit`, `WelcomePEFloatReluStageCommit`,
`WelcomePEBlockFloatStageCommit`, `WelcomePEMatrixMAUStageCommit`,
`WelcomePEL1ToPEStageCommit` and `WelcomePEIntegerFloatStageCommit`.  This
module proves five of them; the sixth (`WelcomePEMatrixMAUStageCommit`) is
reduced below to the five recursor lemmas that remain, and stays a named `Prop`.

Each obligation says that a successful run of one stage is a commit of a list of
prepared masked writes on the PE 0 register file it started from.  The proofs
follow the same recipe for every stage:

* a **per-destination lemma** (`writeParsedMslMsrDestination?_commit`): the
  single-destination writer shared by the MSL/MSR, float-relu, block-float and
  float-MAU stages, and the matrix-MAU destination writer, is a commit of a
  one-element list on the file it was given;
* a **destination-loop lemma**, by structural induction over the destination
  operand list, using the `cons` equation of the lifted local recursor
  (`executeParsedMslMsrAtPE.runCycles.writeDestinations`): a successful loop is a
  commit of the concatenation of the per-destination lists;
* a **cycle-loop lemma**, by structural induction over the cycle list, using the
  `cons` equation of the lifted cycle recursor
  (`executeParsedMslMsrAtPE.runCycles`);
* a **per-PE lemma** (`..._pe_commit`), reading the cycle result off the
  `Id.run do` body and using `commitParsedMaskedWrites_append`;
* a **walk lemma**, by structural induction over the PE list, using the per-PE
  commit lemma for the visited PE and the per-PE frame lemma for the others;
* a **producer lemma** handling the family filter (`[]`, singleton, failure).

The local recursors of the executor are lifted to stable auxiliary declarations,
whose equation lemmas (`<def>.eq_1`, `<def>.<loop>`) are the interface used
throughout: `rw [executeParsedMslMsrAtPE.runCycles]` unfolds exactly one step of
a loop, so each `cons` case is settled by rewriting the scrutinee hypothesis and
reading off the recursive call.  This is the technique the round-36 note asked
for ("cons equation and a `= none ↔ = none` characterisation, then induct"); the
`= none` half is handled by rewriting the lowering hypothesis and closing the
resulting `none`-valued branch with `simp`.

## Status

Five of the six obligations are proved, each as a theorem of the same name:

* `welcomePEMslMsrStageCommit : WelcomePEMslMsrStageCommit` (§2);
* `welcomePEFloatReluStageCommit : WelcomePEFloatReluStageCommit` (§3);
* `welcomePEL1ToPEStageCommit : WelcomePEL1ToPEStageCommit` (§4);
* `welcomePEIntegerFloatStageCommit : WelcomePEIntegerFloatStageCommit` (§5);
* `welcomePEBlockFloatStageCommit : WelcomePEBlockFloatStageCommit` (§6).

The one still open is `WelcomePEMatrixMAUStageCommit`.  Its executor chain is
`executeParsedMatrixMAUAndWrites` → `executeParsedMatrixMAUProducer` (family
filter, then `executeParsedMatrixMAUAtMABs` over the 1024 MAB coordinates, then
`propagateParsedMatrixMAUPoison`) plus `executeParsedMatrixWritesAtMABs` (which
preserves every PE register file: `executeParsedMatrixWritesAtMAB_preserves_pe_state`
per coordinate).  The per-coordinate half needs five more recursor lemmas, in
the same style as §6:

1. `writeParsedMatrixMAUDestinationsAtPE` — the per-PE destination loop
   (`StepResult`, three branches; the `.omr` poison test and the
   `parsedMatrixMAUDestinationEnabled?` branch both return `.failure`);
2. `executeParsedMatrixMAUPEWritesAtCycle` — the four-PE loop over
   `List.finRange 4` threading a `ParsedMatrixMAUWriteAccum`
   (`files := fun index => if index == pe then nextFiles else accum.files index`);
3. `executeParsedMatrixMAUWriteCycles` — the four-cycle loop over the accumulator;
4. `executeParsedMatrixMAUPEWritesAtMAB` / `executeParsedMatrixMAUTransitionAtMAB`
   — repackaging plus `commitParsedMatrixMAUPEState (List.finRange 4) ...`
   (the analogue of the block-float fold: two projection lemmas are needed,
   a value one at `physicalPEId coordinate pe` and a frame one elsewhere);
5. `executeParsedMatrixMAUAtMABs` — the walk over the 1024 coordinates, with the
   same `physicalPEId_welcomePE_eq` reduction (`propagateParsedMatrixMAUPoison`
   preserves `peRegisters` definitionally in both branches).

None of these is assumed anywhere: `WelcomePEMatrixMAUStageCommit` remains a
named `Prop` in `WelcomeAssembly.lean`, unchanged.

No `sorry`, no `admit`, no `native_decide`, no new axioms, and no existing module
is edited by this file.
-/

namespace ProofsLean.MNCore

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

open Issue
open PEMemory

/-! ## 1. The shared per-destination writer

`writeParsedMslMsrDestination?` is the write step of the MSL/MSR, float-relu,
block-float and float-MAU stages (and the inner step of the matrix-MAU
destination writer).  A successful lowering to `write` replaces the incoming
file `files` by `write.files`, which is the commit of a one-element list:

* `.mem` lowers to a masked direct write (`writeDirectAccessMasked`);
* `.omr` lowers to a mask-register write (`Masks.writeRegister`), which is the
  `maskUpdate` form of a prepared write;
* `.bar` and `.nowrite` leave the file unchanged (the empty list);
* every other operand lowers to `none`, so the hypothesis is impossible. -/

/-- **The single-destination writer is a one-element commit.** -/
theorem writeParsedMslMsrDestination?_commit
    (files : IntegerRegisterFiles) (destination : ParsedOperand)
    (context : ParsedIntegerContext) (output : IntegerALU.Bus) (flags : BitVec 4)
    (cycle : Fin 4) (directive : ParsedMaskDirective) (hasSingleLineMask : Bool)
    (write : ParsedMslMsrDestinationWrite)
    (lowered : writeParsedMslMsrDestination? files destination context output flags cycle
      directive hasSingleLineMask = some write) :
    ∃ writes, write.files = commitParsedMaskedWrites files writes := by
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
              exact ⟨[⟨some found, none, PEMemory.unpackALUBus output, selection⟩], by
                simp [commitParsedMaskedWrites]⟩
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
              exact ⟨[⟨none, some (found, cycle, flags), PEMemory.unpackALUBus output,
                ⟨selection, false⟩⟩], by
                simp [commitParsedMaskedWrites]⟩
  | bar lm1 width mask =>
      simp only [writeParsedMslMsrDestination?] at lowered
      cases h : ParsedOperand.resolveMemoryWriteSelection? (ParsedOperand.bar lm1 width mask)
          (if lm1 = true then PEMemory.Bank.lm1 else PEMemory.Bank.lm0) files.maskRegisters
          cycle directive hasSingleLineMask with
      | none => simp [h] at lowered
      | some selection =>
          simp [h] at lowered
          subst lowered
          exact ⟨[], by simp [commitParsedMaskedWrites]⟩
  | nowrite =>
      simp only [writeParsedMslMsrDestination?] at lowered
      obtain rfl := Option.some.inj lowered
      exact ⟨[], by simp [commitParsedMaskedWrites]⟩
  | forward kind neg ext rnd => simp [writeParsedMslMsrDestination?] at lowered
  | fixed value => simp [writeParsedMslMsrDestination?] at lowered
  | matrix side width row => simp [writeParsedMslMsrDestination?] at lowered
  | l1bm width address => simp [writeParsedMslMsrDestination?] at lowered
  | l2bm address l2b => simp [writeParsedMslMsrDestination?] at lowered
  | dar value => simp [writeParsedMslMsrDestination?] at lowered

/-! ## 2. The MSL/MSR stage -/

/-- **The MSL/MSR destination loop is a commit.** -/
theorem executeParsedMslMsrAtPE_writeDestinations_commit
    (currentState : State) (hasSingleLineMask : Bool) (context : ParsedIntegerContext)
    (cycle : Fin 4) (output : IntegerALU.Bus) :
    ∀ (destinations : List ParsedOperand) (files : IntegerRegisterFiles) (bar0 bar1 : BitVec 12)
      (nextFiles : IntegerRegisterFiles) (nextBar0 nextBar1 : BitVec 12),
      executeParsedMslMsrAtPE.runCycles.writeDestinations currentState hasSingleLineMask context
        cycle output destinations files bar0 bar1 = some (nextFiles, nextBar0, nextBar1) →
      ∃ writes, nextFiles = commitParsedMaskedWrites files writes := by
  intro destinations
  induction destinations with
  | nil =>
      intro files bar0 bar1 nextFiles nextBar0 nextBar1 executed
      rw [executeParsedMslMsrAtPE.runCycles.writeDestinations] at executed
      obtain ⟨rfl, rfl, rfl⟩ := Option.some.inj executed
      exact ⟨[], rfl⟩
  | cons destination rest ih =>
      intro files bar0 bar1 nextFiles nextBar0 nextBar1 executed
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
          obtain ⟨headWrites, head⟩ := writeParsedMslMsrDestination?_commit files destination
            { context with cycle := cycle, bar0 := bar0, bar1 := bar1 } output 0 cycle
            currentState.maskDirective hasSingleLineMask write lowered
          obtain ⟨tailWrites, tail⟩ := ih write.files _ _ nextFiles _ _ tailExecuted
          exact ⟨headWrites ++ tailWrites, by
            rw [tail, head, commitParsedMaskedWrites_append]⟩

/-- **The MSL/MSR cycle loop is a commit.** -/
theorem executeParsedMslMsrAtPE_runCycles_commit
    (readState currentState : State) (expression : ParsedExpr) (hasSingleLineMask : Bool)
    (context : ParsedIntegerContext) (destinations : List ParsedOperand) (pe : PEId)
    (sourceAt : Fin 4 → Option ParsedIntegerInput) :
    ∀ (cycles : List (Fin 4)) (files : IntegerRegisterFiles) (bar0 bar1 : BitVec 12)
      (outputs : Fin 4 → IntegerALU.Bus) (nextFiles : IntegerRegisterFiles)
      (nextBar0 nextBar1 : BitVec 12) (nextOutputs : Fin 4 → IntegerALU.Bus),
      executeParsedMslMsrAtPE.runCycles readState currentState expression hasSingleLineMask
        context destinations pe sourceAt cycles files bar0 bar1 outputs =
        .ok (nextFiles, nextBar0, nextBar1, nextOutputs) →
      ∃ writes, nextFiles = commitParsedMaskedWrites files writes := by
  intro cycles
  induction cycles with
  | nil =>
      intro files bar0 bar1 outputs nextFiles nextBar0 nextBar1 nextOutputs executed
      rw [executeParsedMslMsrAtPE.runCycles] at executed
      obtain ⟨rfl, rfl, rfl, rfl⟩ := StepResult.ok.inj executed
      exact ⟨[], rfl⟩
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
                      obtain ⟨headWrites, head⟩ :=
                        executeParsedMslMsrAtPE_writeDestinations_commit currentState
                          hasSingleLineMask context cycle
                          (parsedOutputAfterFlush flushSelection (mslMsrOutputBus sourceBus))
                          destinations files bar0 bar1 middleFiles middleBar0 middleBar1 wrote
                      obtain ⟨tailWrites, tail⟩ := ih middleFiles middleBar0 middleBar1 _
                        nextFiles nextBar0 nextBar1 nextOutputs executed
                      exact ⟨headWrites ++ tailWrites, by
                        rw [tail, head, commitParsedMaskedWrites_append]⟩

/-- **The MSL/MSR per-PE step commits at the visited PE.** -/
theorem executeParsedMslMsrAtPE_pe_commit
    (readState currentState next : State) (expression : ParsedExpr) (pe : PEId)
    (noForward hasSingleLineMask : Bool)
    (executed : executeParsedMslMsrAtPE readState currentState expression pe noForward
      hasSingleLineMask = .ok next) :
    ∃ writes, next.peRegisters pe =
      commitParsedMaskedWrites (currentState.peRegisters pe) writes := by
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
        obtain ⟨writes, committed⟩ :=
          executeParsedMslMsrAtPE_runCycles_commit readState currentState expression
            hasSingleLineMask _ destinations _ _ [0, 1, 2, 3] (currentState.peRegisters pe) _ _ _
            registers bar0 bar1 outputs ran
        refine ⟨writes, ?_⟩
        subst executed
        simpa using committed

/-- **The MSL/MSR per-PE step leaves every other PE untouched.** -/
theorem executeParsedMslMsrAtPE_peRegisters_other
    (readState currentState next : State) (expression : ParsedExpr) (pe other : PEId)
    (different : other ≠ pe) (noForward hasSingleLineMask : Bool)
    (executed : executeParsedMslMsrAtPE readState currentState expression pe noForward
      hasSingleLineMask = .ok next) :
    next.peRegisters other = currentState.peRegisters other := by
  rw [executeParsedMslMsrAtPE.eq_1] at executed
  cases lowered : lowerParsedMslMsr? expression with
  | none =>
      rw [lowered] at executed
      simp at executed
  | some accesses =>
      rw [lowered] at executed
      dsimp only at executed
      split at executed
      · simp at executed
      · simp at executed
      · rw [Id.run_pure] at executed
        simp only [StepResult.ok.injEq] at executed
        subst executed
        simp [different]

/-- **The MSL/MSR walk commits at every PE it visits (and frames the others).** -/
theorem executeParsedMslMsrAtPEs_commit
    (readState : State) (expression : ParsedExpr) (noForward hasSingleLineMask : Bool) :
    ∀ (pes : List PEId) (state : State) (p : PEId) (next : State),
      executeParsedMslMsrAtPEs readState state expression pes noForward hasSingleLineMask =
        .ok next →
      ∃ writes, next.peRegisters p = commitParsedMaskedWrites (state.peRegisters p) writes := by
  intro pes
  induction pes with
  | nil =>
      intro state p next executed
      simp only [executeParsedMslMsrAtPEs, StepResult.ok.injEq] at executed
      subst executed
      exact ⟨[], rfl⟩
  | cons pe rest ih =>
      intro state p next executed
      simp only [executeParsedMslMsrAtPEs] at executed
      split at executed
      · simp at executed
      · simp at executed
      · rename_i middle headExecuted
        obtain ⟨tailWrites, tail⟩ := ih middle p next executed
        by_cases same : p = pe
        · rw [same] at tail ⊢
          obtain ⟨headWrites, headCommit⟩ :=
            executeParsedMslMsrAtPE_pe_commit readState state middle expression pe noForward
              hasSingleLineMask headExecuted
          exact ⟨headWrites ++ tailWrites, by
            rw [tail, headCommit, commitParsedMaskedWrites_append]⟩
        · have frame := executeParsedMslMsrAtPE_peRegisters_other readState state middle
            expression pe p same noForward hasSingleLineMask headExecuted
          exact ⟨tailWrites, by rw [tail, frame]⟩

/-- **The MSL/MSR producer commits PE 0.** -/
theorem executeParsedMslMsrProducers_commit
    (readState currentState next : State) (expressions : List ParsedExpr)
    (noForward hasSingleLineMask : Bool)
    (executed : executeParsedMslMsrProducers readState currentState expressions noForward
      hasSingleLineMask = .ok next) :
    ∃ writes, next.peRegisters welcomePE =
      commitParsedMaskedWrites (currentState.peRegisters welcomePE) writes := by
  cases filtered : expressions.filter parsedExprIsMslMsrProducer with
  | nil =>
      rw [executeParsedMslMsrProducers, filtered] at executed
      simp only [StepResult.ok.injEq] at executed
      subst executed
      exact ⟨[], rfl⟩
  | cons expression rest =>
      cases rest with
      | nil =>
          rw [executeParsedMslMsrProducers, filtered] at executed
          exact executeParsedMslMsrAtPEs_commit readState expression noForward hasSingleLineMask
            (List.finRange 4096) currentState welcomePE next executed
      | cons second remaining =>
          rw [executeParsedMslMsrProducers, filtered] at executed
          simp at executed

/-- **`WelcomePEMslMsrStageCommit`.** -/
theorem welcomePEMslMsrStageCommit : WelcomePEMslMsrStageCommit :=
  fun readState currentState next expressions noForward hasSingleLineMask executed =>
    executeParsedMslMsrProducers_commit readState currentState next expressions noForward
      hasSingleLineMask executed

/-! ## 3. The float-relu stage

Structurally the same as the MSL/MSR stage: one expression, four cycles, the same
single-destination writer; only the source reads and the output bus differ. -/

/-- **The float-relu destination loop is a commit.** -/
theorem executeParsedFloatReluAtPE_writeDestinations_commit
    (currentState : State) (hasSingleLineMask : Bool) (coordinates : ParsedIntegerContext)
    (cycle : Fin 4) (flags : BitVec 4) (output : IntegerALU.Bus) :
    ∀ (destinations : List ParsedOperand) (files : IntegerRegisterFiles) (bar0 bar1 : BitVec 12)
      (nextFiles : IntegerRegisterFiles) (nextBar0 nextBar1 : BitVec 12),
      executeParsedFloatReluAtPE.runCycles.writeDestinations currentState hasSingleLineMask
        coordinates cycle flags output destinations files bar0 bar1 =
        some (nextFiles, nextBar0, nextBar1) →
      ∃ writes, nextFiles = commitParsedMaskedWrites files writes := by
  intro destinations
  induction destinations with
  | nil =>
      intro files bar0 bar1 nextFiles nextBar0 nextBar1 executed
      rw [executeParsedFloatReluAtPE.runCycles.writeDestinations] at executed
      obtain ⟨rfl, rfl, rfl⟩ := Option.some.inj executed
      exact ⟨[], rfl⟩
  | cons destination rest ih =>
      intro files bar0 bar1 nextFiles nextBar0 nextBar1 executed
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
          obtain ⟨headWrites, head⟩ := writeParsedMslMsrDestination?_commit files destination
            { coordinates with cycle := cycle, bar0 := bar0, bar1 := bar1 } output flags cycle
            currentState.maskDirective hasSingleLineMask write lowered
          obtain ⟨tailWrites, tail⟩ := ih write.files _ _ nextFiles _ _ tailExecuted
          exact ⟨headWrites ++ tailWrites, by
            rw [tail, head, commitParsedMaskedWrites_append]⟩

/-- **The float-relu cycle loop is a commit.** -/
theorem executeParsedFloatReluAtPE_runCycles_commit
    (readState currentState : State) (expression : ParsedExpr) (pe : PEId)
    (hasSingleLineMask : Bool) (coordinates sourceContext : ParsedIntegerContext) :
    ∀ (cycles : List (Fin 4)) (files : IntegerRegisterFiles) (bar0 bar1 : BitVec 12)
      (outputs : Fin 4 → IntegerALU.Bus) (nextFiles : IntegerRegisterFiles)
      (nextBar0 nextBar1 : BitVec 12) (nextOutputs : Fin 4 → IntegerALU.Bus),
      executeParsedFloatReluAtPE.runCycles readState currentState expression pe
        hasSingleLineMask coordinates sourceContext cycles files bar0 bar1 outputs =
        .ok (nextFiles, nextBar0, nextBar1, nextOutputs) →
      ∃ writes, nextFiles = commitParsedMaskedWrites files writes := by
  intro cycles
  induction cycles with
  | nil =>
      intro files bar0 bar1 outputs nextFiles nextBar0 nextBar1 nextOutputs executed
      rw [executeParsedFloatReluAtPE.runCycles] at executed
      obtain ⟨rfl, rfl, rfl, rfl⟩ := StepResult.ok.inj executed
      exact ⟨[], rfl⟩
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
          obtain ⟨precision, name, unsigned, sourceAInput, sourceBOption, destinations⟩ :=
            accesses
          cases readA : ParsedIntegerInput.readWithForwarding (readState.peRegisters pe)
              (stateForwardingSlots readState pe) cycle sourceAInput with
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
              cases sourceB? : sourceBOption with
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
                        obtain ⟨headWrites, head⟩ :=
                          executeParsedFloatReluAtPE_writeDestinations_commit currentState
                            hasSingleLineMask coordinates cycle _ _ destinations files bar0 bar1
                            middleFiles middleBar0 middleBar1 wrote
                        obtain ⟨tailWrites, tail⟩ := ih middleFiles middleBar0 middleBar1 _
                          nextFiles nextBar0 nextBar1 nextOutputs executed
                        exact ⟨headWrites ++ tailWrites, by
                          rw [tail, head, commitParsedMaskedWrites_append]⟩
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
                            obtain ⟨headWrites, head⟩ :=
                              executeParsedFloatReluAtPE_writeDestinations_commit currentState
                                hasSingleLineMask coordinates cycle _ _ destinations files bar0 bar1
                                middleFiles middleBar0 middleBar1 wrote
                            obtain ⟨tailWrites, tail⟩ := ih middleFiles middleBar0 middleBar1 _
                              nextFiles nextBar0 nextBar1 nextOutputs executed
                            exact ⟨headWrites ++ tailWrites, by
                              rw [tail, head, commitParsedMaskedWrites_append]⟩

/-- **The float-relu per-PE step commits at the visited PE.** -/
theorem executeParsedFloatReluAtPE_pe_commit
    (readState currentState next : State) (expression : ParsedExpr) (pe : PEId)
    (noForward hasSingleLineMask : Bool)
    (executed : executeParsedFloatReluAtPE readState currentState expression pe noForward
      hasSingleLineMask = .ok next) :
    ∃ writes, next.peRegisters pe =
      commitParsedMaskedWrites (currentState.peRegisters pe) writes := by
  rw [executeParsedFloatReluAtPE.eq_1] at executed
  dsimp only at executed
  split at executed
  · simp at executed
  · simp at executed
  · rename_i registers bar0 bar1 outputs ran
    rw [Id.run_pure] at executed
    simp only [StepResult.ok.injEq] at executed
    obtain ⟨writes, committed⟩ :=
      executeParsedFloatReluAtPE_runCycles_commit readState currentState expression pe
        hasSingleLineMask _ _ [0, 1, 2, 3] (currentState.peRegisters pe) _ _ _ registers bar0 bar1
        outputs ran
    refine ⟨writes, ?_⟩
    subst executed
    simpa using committed

/-- **The float-relu per-PE step leaves every other PE untouched.** -/
theorem executeParsedFloatReluAtPE_peRegisters_other
    (readState currentState next : State) (expression : ParsedExpr) (pe other : PEId)
    (different : other ≠ pe) (noForward hasSingleLineMask : Bool)
    (executed : executeParsedFloatReluAtPE readState currentState expression pe noForward
      hasSingleLineMask = .ok next) :
    next.peRegisters other = currentState.peRegisters other := by
  rw [executeParsedFloatReluAtPE.eq_1] at executed
  dsimp only at executed
  split at executed
  · simp at executed
  · simp at executed
  · rw [Id.run_pure] at executed
    simp only [StepResult.ok.injEq] at executed
    subst executed
    simp [different]

/-- **The float-relu walk commits at every PE it visits (and frames the others).** -/
theorem executeParsedFloatReluAtPEs_commit
    (readState : State) (expression : ParsedExpr) (noForward hasSingleLineMask : Bool) :
    ∀ (pes : List PEId) (state : State) (p : PEId) (next : State),
      executeParsedFloatReluAtPEs readState state expression pes noForward hasSingleLineMask =
        .ok next →
      ∃ writes, next.peRegisters p = commitParsedMaskedWrites (state.peRegisters p) writes := by
  intro pes
  induction pes with
  | nil =>
      intro state p next executed
      simp only [executeParsedFloatReluAtPEs, StepResult.ok.injEq] at executed
      subst executed
      exact ⟨[], rfl⟩
  | cons pe rest ih =>
      intro state p next executed
      simp only [executeParsedFloatReluAtPEs] at executed
      split at executed
      · simp at executed
      · simp at executed
      · rename_i middle headExecuted
        obtain ⟨tailWrites, tail⟩ := ih middle p next executed
        by_cases same : p = pe
        · rw [same] at tail ⊢
          obtain ⟨headWrites, headCommit⟩ :=
            executeParsedFloatReluAtPE_pe_commit readState state middle expression pe noForward
              hasSingleLineMask headExecuted
          exact ⟨headWrites ++ tailWrites, by
            rw [tail, headCommit, commitParsedMaskedWrites_append]⟩
        · have frame := executeParsedFloatReluAtPE_peRegisters_other readState state middle
            expression pe p same noForward hasSingleLineMask headExecuted
          exact ⟨tailWrites, by rw [tail, frame]⟩

/-- **The float-relu producer commits PE 0.** -/
theorem executeParsedFloatReluProducers_commit
    (readState currentState next : State) (expressions : List ParsedExpr)
    (noForward hasSingleLineMask : Bool)
    (executed : executeParsedFloatReluProducers readState currentState expressions noForward
      hasSingleLineMask = .ok next) :
    ∃ writes, next.peRegisters welcomePE =
      commitParsedMaskedWrites (currentState.peRegisters welcomePE) writes := by
  cases filtered : expressions.filter parsedExprIsFloatReluProducer with
  | nil =>
      rw [executeParsedFloatReluProducers, filtered] at executed
      simp only [StepResult.ok.injEq] at executed
      subst executed
      exact ⟨[], rfl⟩
  | cons expression rest =>
      cases rest with
      | nil =>
          rw [executeParsedFloatReluProducers, filtered] at executed
          exact executeParsedFloatReluAtPEs_commit readState expression noForward
            hasSingleLineMask (List.finRange 4096) currentState welcomePE next executed
      | cons second remaining =>
          rw [executeParsedFloatReluProducers, filtered] at executed
          simp at executed

/-- **`WelcomePEFloatReluStageCommit`.** -/
theorem welcomePEFloatReluStageCommit : WelcomePEFloatReluStageCommit :=
  fun readState currentState next expressions noForward hasSingleLineMask executed =>
    executeParsedFloatReluProducers_commit readState currentState next expressions noForward
      hasSingleLineMask executed

/-! ## 4. The L1BM-to-PE broadcast stage

The broadcast stage walks the PE list, and for each visited PE runs a cycle loop
whose destination loop is `writeParsedL1ToPEDestination?` (a masked store of the
broadcast bus at a `.mem` destination, or nothing).  The per-PE frame is already
available as `executeParsedL1ToPEAtPEs_peRegisters_not_mem`; what is added here
is the commit half. -/

/-- **The L1BM-to-PE destination writer is a one-element commit.** -/
theorem writeParsedL1ToPEDestination?_commit
    (files : IntegerRegisterFiles) (maskRegisters : Masks.RegisterFile)
    (destination : ParsedOperand) (context : ParsedIntegerContext)
    (output : IntegerALU.Bus) (cycle : Fin 4) (directive : ParsedMaskDirective)
    (hasSingleLineMask : Bool) :
    ∀ (nextFiles : IntegerRegisterFiles) (barUpdate : Option (Bool × BitVec 12)),
      writeParsedL1ToPEDestination? files maskRegisters destination context output cycle
        directive hasSingleLineMask = some (nextFiles, barUpdate) →
      ∃ writes, nextFiles = commitParsedMaskedWrites files writes := by
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
              exact ⟨[⟨some found, none, PEMemory.unpackALUBus output, selection⟩], by
                simp [commitParsedMaskedWrites]⟩
  | bar lm1 width mask =>
      simp only [writeParsedL1ToPEDestination?] at lowered
      cases h : ParsedOperand.resolveMemoryWriteSelection? (ParsedOperand.bar lm1 width mask)
          (if lm1 = true then PEMemory.Bank.lm1 else PEMemory.Bank.lm0) maskRegisters
          cycle directive hasSingleLineMask with
      | none => simp [h] at lowered
      | some selection =>
          simp [h] at lowered
          obtain ⟨rfl, rfl⟩ := lowered
          exact ⟨[], by simp [commitParsedMaskedWrites]⟩
  | nowrite =>
      simp only [writeParsedL1ToPEDestination?] at lowered
      obtain ⟨rfl, rfl⟩ := Option.some.inj lowered
      exact ⟨[], by simp [commitParsedMaskedWrites]⟩
  | omr entry mask => simp [writeParsedL1ToPEDestination?] at lowered
  | forward kind neg ext rnd => simp [writeParsedL1ToPEDestination?] at lowered
  | fixed value => simp [writeParsedL1ToPEDestination?] at lowered
  | matrix side width row => simp [writeParsedL1ToPEDestination?] at lowered
  | l1bm width address => simp [writeParsedL1ToPEDestination?] at lowered
  | l2bm address l2b => simp [writeParsedL1ToPEDestination?] at lowered
  | dar value => simp [writeParsedL1ToPEDestination?] at lowered

/-- **The L1BM-to-PE destination loop, `none` case.** -/
theorem executeParsedL1ToPE_writeDestinations_cons_none
    (currentState : State) (hasSingleLineMask : Bool) (maskRegisters : Masks.RegisterFile)
    (cycle : Fin 4) (context : ParsedIntegerContext) (output : IntegerALU.Bus)
    (destination : ParsedOperand) (rest : List ParsedOperand)
    (files : IntegerRegisterFiles) (bar0 bar1 : BitVec 12)
    (lowered : writeParsedL1ToPEDestination? files maskRegisters destination
      { context with bar0 := bar0, bar1 := bar1 } output cycle currentState.maskDirective
      hasSingleLineMask = none) :
    executeParsedL1ToPEAtPEs.writeCycles.writeDestinations currentState hasSingleLineMask
        maskRegisters cycle context output (destination :: rest) files bar0 bar1 = none := by
  rw [executeParsedL1ToPEAtPEs.writeCycles.writeDestinations]
  simp only [lowered]
  rfl

/-- **The L1BM-to-PE destination loop, successful write without a BAR update.** -/
theorem executeParsedL1ToPE_writeDestinations_cons_some_none
    (currentState : State) (hasSingleLineMask : Bool) (maskRegisters : Masks.RegisterFile)
    (cycle : Fin 4) (context : ParsedIntegerContext) (output : IntegerALU.Bus)
    (destination : ParsedOperand) (rest : List ParsedOperand)
    (files : IntegerRegisterFiles) (bar0 bar1 : BitVec 12)
    (nextFiles : IntegerRegisterFiles)
    (lowered : writeParsedL1ToPEDestination? files maskRegisters destination
      { context with bar0 := bar0, bar1 := bar1 } output cycle currentState.maskDirective
      hasSingleLineMask = some (nextFiles, none)) :
    executeParsedL1ToPEAtPEs.writeCycles.writeDestinations currentState hasSingleLineMask
        maskRegisters cycle context output (destination :: rest) files bar0 bar1 =
      executeParsedL1ToPEAtPEs.writeCycles.writeDestinations currentState hasSingleLineMask
        maskRegisters cycle context output rest nextFiles bar0 bar1 := by
  rw [executeParsedL1ToPEAtPEs.writeCycles.writeDestinations]
  simp only [lowered]
  rfl

/-- **The L1BM-to-PE destination loop, successful write updating BAR0.** -/
theorem executeParsedL1ToPE_writeDestinations_cons_some_false
    (currentState : State) (hasSingleLineMask : Bool) (maskRegisters : Masks.RegisterFile)
    (cycle : Fin 4) (context : ParsedIntegerContext) (output : IntegerALU.Bus)
    (destination : ParsedOperand) (rest : List ParsedOperand)
    (files : IntegerRegisterFiles) (bar0 bar1 : BitVec 12)
    (nextFiles : IntegerRegisterFiles) (value : BitVec 12)
    (lowered : writeParsedL1ToPEDestination? files maskRegisters destination
      { context with bar0 := bar0, bar1 := bar1 } output cycle currentState.maskDirective
      hasSingleLineMask = some (nextFiles, some (false, value))) :
    executeParsedL1ToPEAtPEs.writeCycles.writeDestinations currentState hasSingleLineMask
        maskRegisters cycle context output (destination :: rest) files bar0 bar1 =
      executeParsedL1ToPEAtPEs.writeCycles.writeDestinations currentState hasSingleLineMask
        maskRegisters cycle context output rest nextFiles value bar1 := by
  rw [executeParsedL1ToPEAtPEs.writeCycles.writeDestinations]
  simp only [lowered]
  rfl

/-- **The L1BM-to-PE destination loop, successful write updating BAR1.** -/
theorem executeParsedL1ToPE_writeDestinations_cons_some_true
    (currentState : State) (hasSingleLineMask : Bool) (maskRegisters : Masks.RegisterFile)
    (cycle : Fin 4) (context : ParsedIntegerContext) (output : IntegerALU.Bus)
    (destination : ParsedOperand) (rest : List ParsedOperand)
    (files : IntegerRegisterFiles) (bar0 bar1 : BitVec 12)
    (nextFiles : IntegerRegisterFiles) (value : BitVec 12)
    (lowered : writeParsedL1ToPEDestination? files maskRegisters destination
      { context with bar0 := bar0, bar1 := bar1 } output cycle currentState.maskDirective
      hasSingleLineMask = some (nextFiles, some (true, value))) :
    executeParsedL1ToPEAtPEs.writeCycles.writeDestinations currentState hasSingleLineMask
        maskRegisters cycle context output (destination :: rest) files bar0 bar1 =
      executeParsedL1ToPEAtPEs.writeCycles.writeDestinations currentState hasSingleLineMask
        maskRegisters cycle context output rest nextFiles bar0 value := by
  rw [executeParsedL1ToPEAtPEs.writeCycles.writeDestinations]
  simp only [lowered]
  rfl

/-- **The L1BM-to-PE destination loop is a commit.** -/
theorem executeParsedL1ToPE_writeDestinations_commit
    (currentState : State) (hasSingleLineMask : Bool) (maskRegisters : Masks.RegisterFile)
    (cycle : Fin 4) (context : ParsedIntegerContext) (output : IntegerALU.Bus) :
    ∀ (destinations : List ParsedOperand) (files : IntegerRegisterFiles) (bar0 bar1 : BitVec 12)
      (nextFiles : IntegerRegisterFiles) (nextBar0 nextBar1 : BitVec 12),
      executeParsedL1ToPEAtPEs.writeCycles.writeDestinations currentState hasSingleLineMask
        maskRegisters cycle context output destinations files bar0 bar1 =
        some (nextFiles, nextBar0, nextBar1) →
      ∃ writes, nextFiles = commitParsedMaskedWrites files writes := by
  intro destinations
  induction destinations with
  | nil =>
      intro files bar0 bar1 nextFiles nextBar0 nextBar1 executed
      rw [executeParsedL1ToPEAtPEs.writeCycles.writeDestinations] at executed
      obtain ⟨rfl, rfl, rfl⟩ := Option.some.inj executed
      exact ⟨[], rfl⟩
  | cons destination rest ih =>
      intro files bar0 bar1 nextFiles nextBar0 nextBar1 executed
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
              obtain ⟨headWrites, head⟩ := writeParsedL1ToPEDestination?_commit files
                maskRegisters destination { context with bar0 := bar0, bar1 := bar1 } output
                cycle currentState.maskDirective hasSingleLineMask writeFiles none lowered
              obtain ⟨tailWrites, tail⟩ := ih writeFiles bar0 bar1 nextFiles nextBar0 nextBar1
                executed
              exact ⟨headWrites ++ tailWrites, by
                rw [tail, head, commitParsedMaskedWrites_append]⟩
          | some update =>
              obtain ⟨lm1, value⟩ := update
              cases lm1 with
              | false =>
                  rw [executeParsedL1ToPE_writeDestinations_cons_some_false currentState
                    hasSingleLineMask maskRegisters cycle context output destination rest files
                    bar0 bar1 writeFiles value lowered] at executed
                  obtain ⟨headWrites, head⟩ := writeParsedL1ToPEDestination?_commit files
                    maskRegisters destination { context with bar0 := bar0, bar1 := bar1 } output
                    cycle currentState.maskDirective hasSingleLineMask writeFiles
                    (some (false, value)) lowered
                  obtain ⟨tailWrites, tail⟩ := ih writeFiles value bar1 nextFiles nextBar0
                    nextBar1 executed
                  exact ⟨headWrites ++ tailWrites, by
                    rw [tail, head, commitParsedMaskedWrites_append]⟩
              | true =>
                  rw [executeParsedL1ToPE_writeDestinations_cons_some_true currentState
                    hasSingleLineMask maskRegisters cycle context output destination rest files
                    bar0 bar1 writeFiles value lowered] at executed
                  obtain ⟨headWrites, head⟩ := writeParsedL1ToPEDestination?_commit files
                    maskRegisters destination { context with bar0 := bar0, bar1 := bar1 } output
                    cycle currentState.maskDirective hasSingleLineMask writeFiles
                    (some (true, value)) lowered
                  obtain ⟨tailWrites, tail⟩ := ih writeFiles bar0 value nextFiles nextBar0
                    nextBar1 executed
                  exact ⟨headWrites ++ tailWrites, by
                    rw [tail, head, commitParsedMaskedWrites_append]⟩

/-- **The L1BM-to-PE cycle loop is a commit.** -/
theorem executeParsedL1ToPE_writeCycles_commit
    (readState currentState : State) (expression : ParsedExpr) (access : ParsedL1ToPEAccess)
    (hasSingleLineMask : Bool) (pe : PEId) (coordinates readContext : ParsedIntegerContext)
    (maskRegisters : Masks.RegisterFile) :
    ∀ (cycles : List (Fin 4)) (files : IntegerRegisterFiles) (bar0 bar1 : BitVec 12)
      (nextFiles : IntegerRegisterFiles) (nextBar0 nextBar1 : BitVec 12),
      executeParsedL1ToPEAtPEs.writeCycles readState currentState expression access
        hasSingleLineMask pe coordinates readContext maskRegisters cycles files bar0 bar1 =
        .ok (nextFiles, nextBar0, nextBar1) →
      ∃ writes, nextFiles = commitParsedMaskedWrites files writes := by
  intro cycles
  induction cycles with
  | nil =>
      intro files bar0 bar1 nextFiles nextBar0 nextBar1 executed
      rw [executeParsedL1ToPEAtPEs.writeCycles] at executed
      obtain ⟨rfl, rfl, rfl⟩ := StepResult.ok.inj executed
      exact ⟨[], rfl⟩
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
            obtain ⟨headWrites, head⟩ :=
              executeParsedL1ToPE_writeDestinations_commit currentState hasSingleLineMask
                maskRegisters cycle _ _ access.destinations files bar0 bar1 middleFiles
                middleBar0 middleBar1 wrote
            obtain ⟨tailWrites, tail⟩ := ih middleFiles middleBar0 middleBar1 nextFiles
              nextBar0 nextBar1 executed
            exact ⟨headWrites ++ tailWrites, by
              rw [tail, head, commitParsedMaskedWrites_append]⟩

/-- **The L1BM-to-PE walk commits at every PE it visits (and frames the others).** -/
theorem executeParsedL1ToPEAtPEs_commit
    (readState : State) (expression : ParsedExpr) (access : ParsedL1ToPEAccess)
    (noForward hasSingleLineMask usePreIssueMask : Bool) :
    ∀ (pes : List PEId) (state : State) (p : PEId) (next : State),
      executeParsedL1ToPEAtPEs readState state expression access pes noForward
        hasSingleLineMask usePreIssueMask = .ok next →
      ∃ writes, next.peRegisters p = commitParsedMaskedWrites (state.peRegisters p) writes := by
  intro pes
  induction pes with
  | nil =>
      intro state p next executed
      simp only [executeParsedL1ToPEAtPEs.eq_1, StepResult.ok.injEq] at executed
      subst executed
      exact ⟨[], rfl⟩
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
          obtain ⟨tailWrites, tail⟩ := ih _ p next executed
          by_cases same : p = pe
          · rw [same] at tail ⊢
            obtain ⟨headWrites, head⟩ :=
              executeParsedL1ToPE_writeCycles_commit readState state expression access
                hasSingleLineMask pe _ _ _ [0, 1, 2, 3] (state.peRegisters pe) _ _ files
                bar0 bar1 ran
            refine ⟨headWrites ++ tailWrites, ?_⟩
            rw [tail]
            dsimp only
            rw [head, commitParsedMaskedWrites_append]
            simp
          · refine ⟨tailWrites, ?_⟩
            rw [tail]
            simp [same]

/-- **The L1BM-to-PE producer commits PE 0.** -/
theorem executeParsedL1ToPEProducer_commit
    (readState currentState next : State) (expression : ParsedExpr)
    (noForward hasSingleLineMask usePreIssueMask : Bool)
    (executed : executeParsedL1ToPEProducer readState currentState expression noForward
      hasSingleLineMask usePreIssueMask = .ok next) :
    ∃ writes, next.peRegisters welcomePE =
      commitParsedMaskedWrites (currentState.peRegisters welcomePE) writes := by
  cases lowered : lowerParsedL1ToPE? expression with
  | none =>
      rw [executeParsedL1ToPEProducer, lowered] at executed
      simp at executed
  | some access =>
      rw [executeParsedL1ToPEProducer, lowered] at executed
      exact executeParsedL1ToPEAtPEs_commit readState expression access noForward
        hasSingleLineMask usePreIssueMask (List.finRange 4096) currentState welcomePE next
        executed

/-- **The L1BM-to-PE producer filter commits PE 0.** -/
theorem executeParsedL1ToPEProducers_commit
    (readState currentState next : State) (expressions : List ParsedExpr)
    (noForward hasSingleLineMask usePreIssueMask : Bool)
    (executed : executeParsedL1ToPEProducers readState currentState expressions noForward
      hasSingleLineMask usePreIssueMask = .ok next) :
    ∃ writes, next.peRegisters welcomePE =
      commitParsedMaskedWrites (currentState.peRegisters welcomePE) writes := by
  cases filtered : expressions.filter parsedExprIsL1ToPEProducer with
  | nil =>
      rw [executeParsedL1ToPEProducers, filtered] at executed
      simp only [StepResult.ok.injEq] at executed
      subst executed
      exact ⟨[], rfl⟩
  | cons expression rest =>
      cases rest with
      | nil =>
          rw [executeParsedL1ToPEProducers, filtered] at executed
          exact executeParsedL1ToPEProducer_commit readState currentState next expression
            noForward hasSingleLineMask usePreIssueMask executed
      | cons second remaining =>
          rw [executeParsedL1ToPEProducers, filtered] at executed
          simp at executed

/-- **`WelcomePEL1ToPEStageCommit`.** -/
theorem welcomePEL1ToPEStageCommit : WelcomePEL1ToPEStageCommit :=
  fun readState currentState next expressions noForward hasSingleLineMask usePreIssueMask
    executed =>
    executeParsedL1ToPEProducers_commit readState currentState next expressions noForward
      hasSingleLineMask usePreIssueMask executed

/-! ## 5. The integer stage with a float-MAU row

`executeIntegerProducerLineAtPECore` runs the integer/matrix-read four-cycle
stage and then the float-MAU stage on the resulting register file.  The
four-cycle half is `parsedIntegerMatrixReadLineFourCycleStep_ok_commit`
(`WelcomeProvenance.lean`); the float-MAU half is proved here, through the
matrix-MAU destination writer `writeParsedMAUDestinations?` and the cycle loop
`executeParsedFloatMAUCyclesAtPE`. -/

/-- **The matrix-MAU destination loop is a commit.** -/
theorem writeParsedMAUDestinations?_writeAll_commit
    (context : ParsedIntegerContext) (output : IntegerALU.Bus) (flags : BitVec 4)
    (cycle : Fin 4) (directive : ParsedMaskDirective) (hasSingleLineMask : Bool) :
    ∀ (destinations : List ParsedOperand) (files : IntegerRegisterFiles) (bar0 bar1 : BitVec 12)
      (writes : ParsedMAUDestinationWrites),
      writeParsedMAUDestinations?.writeAll context output flags cycle directive
        hasSingleLineMask destinations files bar0 bar1 = some writes →
      ∃ ws, writes.files = commitParsedMaskedWrites files ws := by
  intro destinations
  induction destinations with
  | nil =>
      intro files bar0 bar1 writes executed
      rw [writeParsedMAUDestinations?.writeAll] at executed
      obtain rfl := Option.some.inj executed
      exact ⟨[], rfl⟩
  | cons destination rest ih =>
      intro files bar0 bar1 writes executed
      rw [writeParsedMAUDestinations?.writeAll] at executed
      cases lowered : writeParsedMslMsrDestination? files destination
          { context with bar0 := bar0, bar1 := bar1 } output flags cycle directive
          hasSingleLineMask with
      | none =>
          rw [lowered] at executed
          simp at executed
      | some write =>
          rw [lowered] at executed
          have tailExecuted :
              writeParsedMAUDestinations?.writeAll context output flags cycle directive
                hasSingleLineMask rest write.files
                (match write.barUpdate with
                  | some (false, value) => value
                  | _ => bar0)
                (match write.barUpdate with
                  | some (true, value) => value
                  | _ => bar1) = some writes := executed
          obtain ⟨headWrites, head⟩ := writeParsedMslMsrDestination?_commit files destination
            { context with bar0 := bar0, bar1 := bar1 } output flags cycle directive
            hasSingleLineMask write lowered
          obtain ⟨tailWrites, tail⟩ := ih write.files _ _ writes tailExecuted
          exact ⟨headWrites ++ tailWrites, by
            rw [tail, head, commitParsedMaskedWrites_append]⟩

/-- **The matrix-MAU destination writer is a commit.** -/
theorem writeParsedMAUDestinations?_commit
    (files : IntegerRegisterFiles) (destinations : List ParsedOperand)
    (context : ParsedIntegerContext) (output : IntegerALU.Bus) (flags : BitVec 4)
    (cycle : Fin 4) (directive : ParsedMaskDirective) (hasSingleLineMask : Bool)
    (writes : ParsedMAUDestinationWrites)
    (executed : writeParsedMAUDestinations? files destinations context output flags cycle
      directive hasSingleLineMask = some writes) :
    ∃ ws, writes.files = commitParsedMaskedWrites files ws := by
  rw [writeParsedMAUDestinations?.eq_1] at executed
  exact writeParsedMAUDestinations?_writeAll_commit context output flags cycle directive
    hasSingleLineMask destinations files context.bar0 context.bar1 writes executed

/-- **The float-MAU cycle loop is a commit.** -/
theorem executeParsedFloatMAUCyclesAtPE_commit
    (readFiles : IntegerRegisterFiles) (oldSlots : Forwarding.Slots) (expression : ParsedExpr)
    (context : ParsedIntegerContext) (directive : ParsedMaskDirective)
    (hasSingleLineMask : Bool) :
    ∀ (cycles : List (Fin 4)) (files : IntegerRegisterFiles) (bar0 bar1 : BitVec 12)
      (outputs : Fin 4 → IntegerALU.Bus) (nextFiles : IntegerRegisterFiles)
      (nextBar0 nextBar1 : BitVec 12) (nextOutputs : Fin 4 → IntegerALU.Bus),
      executeParsedFloatMAUCyclesAtPE readFiles oldSlots expression context directive
        hasSingleLineMask cycles files bar0 bar1 outputs =
        .ok (nextFiles, nextBar0, nextBar1, nextOutputs) →
      ∃ writes, nextFiles = commitParsedMaskedWrites files writes := by
  intro cycles
  induction cycles with
  | nil =>
      intro files bar0 bar1 outputs nextFiles nextBar0 nextBar1 nextOutputs executed
      rw [executeParsedFloatMAUCyclesAtPE.eq_1] at executed
      obtain ⟨rfl, rfl, rfl, rfl⟩ := StepResult.ok.inj executed
      exact ⟨[], rfl⟩
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
                  obtain ⟨headWrites, head⟩ := writeParsedMAUDestinations?_commit files
                    expression.destinations { context with cycle := cycle, bar0 := bar0, bar1 := bar1 }
                    (parsedOutputAfterFlush flushSelection output) flags cycle directive
                    hasSingleLineMask writes wrote
                  obtain ⟨tailWrites, tail⟩ := ih writes.files writes.bar0 writes.bar1 _
                    nextFiles nextBar0 nextBar1 nextOutputs executed
                  exact ⟨headWrites ++ tailWrites, by
                    rw [tail, head, commitParsedMaskedWrites_append]⟩

/-- **The float-MAU expression loop is a commit.** -/
theorem executeParsedFloatMAUsAtPE_run_commit
    (readFiles : IntegerRegisterFiles) (oldSlots : Forwarding.Slots)
    (context : ParsedIntegerContext) (directive : ParsedMaskDirective)
    (hasSingleLineMask : Bool) :
    ∀ (remaining : List ParsedExpr) (files : IntegerRegisterFiles) (bar0 bar1 : BitVec 12)
      (outputs : Fin 4 → IntegerALU.Bus) (nextFiles : IntegerRegisterFiles)
      (nextBar0 nextBar1 : BitVec 12) (nextOutputs : Fin 4 → IntegerALU.Bus),
      executeParsedFloatMAUsAtPE.run readFiles oldSlots context directive hasSingleLineMask
        remaining files bar0 bar1 outputs = .ok (nextFiles, nextBar0, nextBar1, nextOutputs) →
      ∃ writes, nextFiles = commitParsedMaskedWrites files writes := by
  intro remaining
  induction remaining with
  | nil =>
      intro files bar0 bar1 outputs nextFiles nextBar0 nextBar1 nextOutputs executed
      rw [executeParsedFloatMAUsAtPE.run] at executed
      obtain ⟨rfl, rfl, rfl, rfl⟩ := StepResult.ok.inj executed
      exact ⟨[], rfl⟩
  | cons expression rest ih =>
      intro files bar0 bar1 outputs nextFiles nextBar0 nextBar1 nextOutputs executed
      rw [executeParsedFloatMAUsAtPE.run] at executed
      split at executed
      · simp at executed
      · simp at executed
      · rename_i middleFiles middleBar0 middleBar1 middleOutputs ran
        obtain ⟨headWrites, head⟩ := executeParsedFloatMAUCyclesAtPE_commit readFiles oldSlots
          expression context directive hasSingleLineMask [0, 1, 2, 3] files bar0 bar1
          (fun _ => ⟨0, 0⟩) middleFiles middleBar0 middleBar1 middleOutputs ran
        obtain ⟨tailWrites, tail⟩ := ih middleFiles middleBar0 middleBar1 middleOutputs
          nextFiles nextBar0 nextBar1 nextOutputs executed
        exact ⟨headWrites ++ tailWrites, by
          rw [tail, head, commitParsedMaskedWrites_append]⟩

/-- **The float-MAU stage is a commit.** -/
theorem executeParsedFloatMAUsAtPE_commit
    (readFiles currentFiles : IntegerRegisterFiles) (oldSlots : Forwarding.Slots)
    (context : ParsedIntegerContext) (expressions : List ParsedExpr)
    (directive : ParsedMaskDirective) (hasSingleLineMask : Bool)
    (nextFiles : IntegerRegisterFiles) (nextBar0 nextBar1 : BitVec 12)
    (nextOutputs : Fin 4 → IntegerALU.Bus) (hasMAUProducer : Bool)
    (executed : executeParsedFloatMAUsAtPE readFiles currentFiles oldSlots context expressions
      directive hasSingleLineMask =
      .ok (nextFiles, nextBar0, nextBar1, nextOutputs, hasMAUProducer)) :
    ∃ writes, nextFiles = commitParsedMaskedWrites currentFiles writes := by
  rw [executeParsedFloatMAUsAtPE.eq_1] at executed
  split at executed
  · simp at executed
  · simp at executed
  · rename_i files bar0 bar1 outputs ran
    obtain ⟨runWrites, runCommit⟩ := executeParsedFloatMAUsAtPE_run_commit readFiles oldSlots
      context directive hasSingleLineMask _ currentFiles context.bar0 context.bar1 _
      files bar0 bar1 outputs ran
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := StepResult.ok.inj executed
    exact ⟨runWrites, runCommit⟩

/-- **The per-PE core step commits even with a float-MAU row.** -/
theorem executeIntegerProducerLineAtPECore_peRegisters_commit_float
    (expressions : List ParsedExpr) (state next : State) (pe : PEId)
    (executed : executeIntegerProducerLineAtPECore expressions state pe = .ok next) :
    ∃ writes, next.peRegisters pe =
      commitParsedMaskedWrites (state.peRegisters pe) writes := by
  rw [executeIntegerProducerLineAtPECore.eq_1] at executed
  split at executed
  · simp at executed
  · simp at executed
  · rename_i registers integerSlots barUpdates fourCycle
    split at executed
    · simp at executed
    · simp at executed
    · rename_i registersWithFloat floatBar0 floatBar1 floatOutputs hasMAUProducer floatMAU
      simp only [updateSupportedPELineForwarding] at executed
      split at executed
      · simp at executed
      · simp at executed
      · simp only [StepResult.ok.injEq] at executed
        obtain ⟨intWrites, intCommit⟩ :=
          parsedIntegerMatrixReadLineFourCycleStep_ok_commit _ _ _ _ _ _ _ _ _ fourCycle
        obtain ⟨floatWrites, floatCommit⟩ :=
          executeParsedFloatMAUsAtPE_commit _ registers _ _ expressions _ _ registersWithFloat
            floatBar0 floatBar1 floatOutputs hasMAUProducer floatMAU
        refine ⟨intWrites ++ floatWrites, ?_⟩
        subst executed
        rw [floatCommit, intCommit, commitParsedMaskedWrites_append]
        simp

/-- **`WelcomePEIntegerFloatStageCommit`.** -/
theorem welcomePEIntegerFloatStageCommit : WelcomePEIntegerFloatStageCommit :=
  fun expressions state next pe executed =>
    executeIntegerProducerLineAtPECore_peRegisters_commit_float expressions state next pe
      executed

/-! ## 6. The block-float stage

`executeParsedBlockFloatAtMAB` runs, for one MAB coordinate, four cycles over the
four PEs of the MAB, each cycle applying the shared single-destination writer to
the row's destination operands (`executeParsedBlockFloatAtMAB.apply`), and then
installs the resulting four register files into the state with a
`List.finRange 4` fold.  The stage walks all 1024 MAB coordinates.

The proof has five layers:

* `executeParsedBlockFloatAtMAB_apply_commit` — the destination loop of one PE is
  a commit (structural induction over the destination list);
* `executeParsedBlockFloatAtMAB_writePEs_commit` — the four-PE loop is a commit
  at any chosen PE, given the per-PE writer's commit property (structural
  induction over `List.finRange 4`);
* `executeParsedBlockFloatAtMAB_runCycles_commit` — the four-cycle loop is a
  commit at any chosen PE, given the per-cycle writer's commit property;
* `executeParsedBlockFloatAtMAB_writeCycle_commit` — discharges that property for
  the concrete cycle writer (the four-PE loop over `apply`);
* `executeParsedBlockFloatAtMAB_pe_commit` and `..._peRegisters_frame` — the
  per-coordinate step commits at each of its four PEs and preserves every other
  PE, via the two fold lemmas (`..._foldl_peRegisters_target` /
  `..._foldl_peRegisters_frame`);
* `executeParsedBlockFloatAtMABs_commit` — the walk over the coordinates;
* `executeParsedBlockFloatProducer_commit` — the family filter, using that only
  the MAB coordinate `⟨0,0,0,0⟩` reaches PE 0 (`physicalPEId_welcomePE_eq`).

-/

theorem executeParsedBlockFloatAtMAB_apply_commit
    (currentState : State) (hasSingleLineMask : Bool) (cycle : Fin 4)
    (output : IntegerALU.Bus) (oldContext coords : ParsedIntegerContext) :
    ∀ (destinations : List ParsedOperand) (files : IntegerRegisterFiles) (bar0 bar1 : BitVec 12)
      (nextFiles : IntegerRegisterFiles) (nextBar0 nextBar1 : BitVec 12),
      executeParsedBlockFloatAtMAB.apply currentState hasSingleLineMask cycle output oldContext
        coords destinations files bar0 bar1 = .ok (nextFiles, nextBar0, nextBar1) →
      ∃ writes, nextFiles = commitParsedMaskedWrites files writes := by
  intro destinations
  induction destinations with
  | nil =>
      intro files bar0 bar1 nextFiles nextBar0 nextBar1 executed
      rw [executeParsedBlockFloatAtMAB.apply.eq_1] at executed
      obtain ⟨rfl, rfl, rfl⟩ := StepResult.ok.inj executed
      exact ⟨[], rfl⟩
  | cons destination rest ih =>
      intro files bar0 bar1 nextFiles nextBar0 nextBar1 executed
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
          obtain ⟨headWrites, head⟩ := writeParsedMslMsrDestination?_commit files destination
            { coords with cycle := cycle, bar0 := bar0, bar1 := bar1, tWord := oldContext.tWord }
            output 0 cycle currentState.maskDirective hasSingleLineMask write lowered
          obtain ⟨tailWrites, tail⟩ := ih write.files _ _ nextFiles _ _ tailExecuted
          exact ⟨headWrites ++ tailWrites, by
            rw [tail, head, commitParsedMaskedWrites_append]⟩

theorem executeParsedBlockFloatAtMAB_writePEs_commit
    (expression : ParsedExpr)
    (writeDestinations : Fin 4 → Fin 4 → IntegerALU.Bus → IntegerRegisterFiles →
      BitVec 12 → BitVec 12 → StepResult (IntegerRegisterFiles × BitVec 12 × BitVec 12))
    (writeCommit : ∀ (pe : Fin 4) (cycle : Fin 4) (output : IntegerALU.Bus)
      (files : IntegerRegisterFiles) (bar0 bar1 : BitVec 12) (nextFiles : IntegerRegisterFiles)
      (nextBar0 nextBar1 : BitVec 12),
      writeDestinations pe cycle output files bar0 bar1 = .ok (nextFiles, nextBar0, nextBar1) →
      ∃ writes, nextFiles = commitParsedMaskedWrites files writes)
    (cycle : Fin 4) (buses : Fin 4 → IntegerALU.Bus) (target : Fin 4) :
    ∀ (pes : List (Fin 4)) (files : Fin 4 → IntegerRegisterFiles) (bar0 bar1 : Fin 4 → BitVec 12)
      (outputs : Fin 4 → Fin 4 → IntegerALU.Bus)
      (results : Fin 4 → IntegerRegisterFiles × BitVec 12 × BitVec 12 × (Fin 4 → IntegerALU.Bus)),
      executeParsedBlockFloatAtMAB.writePEs expression writeDestinations cycle buses pes files
        bar0 bar1 outputs = .ok results →
      ∃ writes, (results target).1 = commitParsedMaskedWrites (files target) writes := by
  intro pes
  induction pes with
  | nil =>
      intro files bar0 bar1 outputs results executed
      rw [executeParsedBlockFloatAtMAB.writePEs.eq_1] at executed
      obtain rfl := StepResult.ok.inj executed
      exact ⟨[], rfl⟩
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
              obtain ⟨headWrites, head⟩ := writeCommit pe cycle
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
              obtain ⟨tailWrites, tail⟩ := ih _ _ _ _ _ tailExecuted
              by_cases same : target = pe
              · subst same
                refine ⟨headWrites ++ tailWrites, ?_⟩
                rw [tail]
                simp only [beq_self_eq_true, if_true]
                rw [head, commitParsedMaskedWrites_append]
              · refine ⟨tailWrites, ?_⟩
                rw [tail]
                have different : (target == pe) = false := by
                  simp [beq_iff_eq, same]
                simp [different]







theorem physicalPEId_inj (coordinate : MABCoordinate) {a b : Fin 4}
    (h : physicalPEId coordinate a = physicalPEId coordinate b) : a = b := by
  have := congrArg Fin.val h
  simp only [physicalPEId] at this
  have ha := a.isLt
  have hb := b.isLt
  omega

theorem physicalPEId_beq (coordinate : MABCoordinate) (a b : Fin 4) :
    (physicalPEId coordinate a == physicalPEId coordinate b) = (a == b) := by
  by_cases h : a = b
  · subst h
    simp
  · have h' : physicalPEId coordinate a ≠ physicalPEId coordinate b :=
      fun e => h (physicalPEId_inj coordinate e)
    simp [h, h']







theorem executeParsedBlockFloatAtMAB_foldl_peRegisters_frame (noForward : Bool) (coordinate : MABCoordinate)
    (results : Fin 4 → IntegerRegisterFiles × BitVec 12 × BitVec 12 × (Fin 4 → IntegerALU.Bus))
    (p : PEId) :
    ∀ (pes : List (Fin 4)) (state : State),
      (∀ pe ∈ pes, p ≠ physicalPEId coordinate pe) →
      ((pes.foldl (fun state pe =>
        let peId := physicalPEId coordinate pe
        let (files, bar0, bar1, outputs) := results pe
        let forwarding : Forwarding.Slots := fun unit cycle =>
          if noForward then state.forwarding peId unit cycle
          else if unit == .alu then .known (outputs cycle)
          else state.forwarding peId unit cycle
        let forwardingValid : Forwarding.Unit → Fin 4 → Bool := fun unit cycle =>
          if noForward then state.forwardingValid peId unit cycle
          else if unit == .alu then true
          else state.forwardingValid peId unit cycle
        { state with
          peRegisters := fun other => if other == peId then files else state.peRegisters other
          forwarding := fun other => if other == peId then forwarding else state.forwarding other
          forwardingValid := fun other => if other == peId then forwardingValid else state.forwardingValid other
          peContext := fun other => if other == peId then
            { state.peContext other with bar0 := bar0, bar1 := bar1 }
            else state.peContext other }) state)).peRegisters p = state.peRegisters p := by
  intro pes
  induction pes with
  | nil =>
      intro state _
      rfl
  | cons pe rest ih =>
      intro state notTouched
      rw [List.foldl_cons]
      rw [ih _ (fun pe' member => notTouched pe' (by simp [member]))]
      simp only []
      simp [beq_iff_eq, notTouched pe (by simp)]

theorem executeParsedBlockFloatAtMAB_foldl_peRegisters_target (noForward : Bool) (coordinate : MABCoordinate)
    (results : Fin 4 → IntegerRegisterFiles × BitVec 12 × BitVec 12 × (Fin 4 → IntegerALU.Bus))
    (target : Fin 4) :
    ∀ (pes : List (Fin 4)) (state : State), pes.Nodup → target ∈ pes →
      ((pes.foldl (fun state pe =>
        let peId := physicalPEId coordinate pe
        let (files, bar0, bar1, outputs) := results pe
        let forwarding : Forwarding.Slots := fun unit cycle =>
          if noForward then state.forwarding peId unit cycle
          else if unit == .alu then .known (outputs cycle)
          else state.forwarding peId unit cycle
        let forwardingValid : Forwarding.Unit → Fin 4 → Bool := fun unit cycle =>
          if noForward then state.forwardingValid peId unit cycle
          else if unit == .alu then true
          else state.forwardingValid peId unit cycle
        { state with
          peRegisters := fun other => if other == peId then files else state.peRegisters other
          forwarding := fun other => if other == peId then forwarding else state.forwarding other
          forwardingValid := fun other => if other == peId then forwardingValid else state.forwardingValid other
          peContext := fun other => if other == peId then
            { state.peContext other with bar0 := bar0, bar1 := bar1 }
            else state.peContext other }) state)).peRegisters (physicalPEId coordinate target) =
        (results target).1 := by
  intro pes
  induction pes with
  | nil =>
      intro state _ member
      simp at member
  | cons pe rest ih =>
      intro state nodup member
      obtain ⟨headNotMem, restNodup⟩ := List.nodup_cons.mp nodup
      rw [List.foldl_cons]
      by_cases same : target = pe
      · subst same
        rw [executeParsedBlockFloatAtMAB_foldl_peRegisters_frame noForward coordinate results
          (physicalPEId coordinate target) rest _
          (fun pe' member hpe' => headNotMem ((physicalPEId_inj coordinate hpe').symm ▸ member))]
        simp only []
        simp
      · have memberRest : target ∈ rest := by
          rcases List.mem_cons.mp member with h | h
          · exact absurd h same
          · exact h
        exact ih _ restNodup memberRest







theorem executeParsedBlockFloatAtMAB_runCycles_commit
    (accesses : ParsedBlockFloatAccesses)
    (readCycle : Fin 4 → StepResult (Fin 4 → IntegerALU.Bus))
    (writeCycle : Fin 4 → (Fin 4 → IntegerALU.Bus) → (Fin 4 → IntegerRegisterFiles) →
      (Fin 4 → BitVec 12) → (Fin 4 → BitVec 12) → (Fin 4 → Fin 4 → IntegerALU.Bus) →
      StepResult (Fin 4 → IntegerRegisterFiles × BitVec 12 × BitVec 12 × (Fin 4 → IntegerALU.Bus)))
    (writeCommit : ∀ (cycle : Fin 4) (buses : Fin 4 → IntegerALU.Bus)
      (files : Fin 4 → IntegerRegisterFiles) (bar0 bar1 : Fin 4 → BitVec 12)
      (outputs : Fin 4 → Fin 4 → IntegerALU.Bus)
      (results : Fin 4 → IntegerRegisterFiles × BitVec 12 × BitVec 12 × (Fin 4 → IntegerALU.Bus)),
      writeCycle cycle buses files bar0 bar1 outputs = .ok results →
      ∀ target : Fin 4, ∃ writes, (results target).1 = commitParsedMaskedWrites (files target) writes)
    (target : Fin 4) :
    ∀ (cycles : List (Fin 4)) (files : Fin 4 → IntegerRegisterFiles) (bar0 bar1 : Fin 4 → BitVec 12)
      (outputs : Fin 4 → Fin 4 → IntegerALU.Bus)
      (results : Fin 4 → IntegerRegisterFiles × BitVec 12 × BitVec 12 × (Fin 4 → IntegerALU.Bus)),
      executeParsedBlockFloatAtMAB.runCycles accesses readCycle writeCycle cycles files bar0 bar1 outputs = .ok results →
      ∃ writes, (results target).1 = commitParsedMaskedWrites (files target) writes := by
  intro cycles
  induction cycles with
  | nil =>
      intro files bar0 bar1 outputs results executed
      rw [executeParsedBlockFloatAtMAB.runCycles.eq_1] at executed
      obtain rfl := StepResult.ok.inj executed
      exact ⟨[], rfl⟩
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
          obtain ⟨headWrites, head⟩ := writeCommit cycle
            (parsedBlockFloatMab accesses.precision accesses.keep accesses.extended inputBuses)
            files bar0 bar1 outputs results' ranWrite target
          obtain ⟨tailWrites, tail⟩ := ih (fun pe => (results' pe).1)
            (fun pe => (results' pe).2.1) (fun pe => (results' pe).2.2.1)
            (fun pe index => (results' pe).2.2.2 index) results executed
          exact ⟨headWrites ++ tailWrites, by
            rw [tail, head, commitParsedMaskedWrites_append]⟩







theorem executeParsedBlockFloat_writeCycle_commit
    (currentState : State) (hasSingleLineMask : Bool) (expression : ParsedExpr)
    (coordinate : MABCoordinate) (accesses : ParsedBlockFloatAccesses)
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
    ∃ writes, (results target).1 = commitParsedMaskedWrites (files target) writes := by
  rw [form cycle buses files bar0 bar1 outputs] at executed
  have executed' :
      executeParsedBlockFloatAtMAB.writePEs expression
        (fun pe cycle output files bar0 bar1 =>
          Id.run (executeParsedBlockFloatAtMAB.apply currentState hasSingleLineMask cycle output
            (currentState.peContext (physicalPEId coordinate pe))
            (ParsedIntegerContext.ofLinearIndex (physicalPEId coordinate pe))
            accesses.destinations files bar0 bar1))
        cycle buses (List.finRange 4) files bar0 bar1 outputs = .ok results := executed
  exact executeParsedBlockFloatAtMAB_writePEs_commit expression _ (fun pe cyc out fl b0 b1 nf nb0 nb1 hh =>
    executeParsedBlockFloatAtMAB_apply_commit currentState hasSingleLineMask cyc out
      (currentState.peContext (physicalPEId coordinate pe))
      (ParsedIntegerContext.ofLinearIndex (physicalPEId coordinate pe))
      accesses.destinations fl b0 b1 nf nb0 nb1 hh)
    cycle buses target (List.finRange 4) files bar0 bar1 outputs results executed'

theorem executeParsedBlockFloatAtMAB_pe_commit
    (readState currentState : State) (expression : ParsedExpr) (coordinate : MABCoordinate)
    (noForward hasSingleLineMask : Bool) (target : Fin 4) (next : State)
    (executed : executeParsedBlockFloatAtMAB readState currentState expression coordinate
      noForward hasSingleLineMask = .ok next) :
    ∃ writes, next.peRegisters (physicalPEId coordinate target) =
      commitParsedMaskedWrites (currentState.peRegisters (physicalPEId coordinate target)) writes := by
  rw [executeParsedBlockFloatAtMAB.eq_1] at executed
  cases lowered : lowerParsedBlockFloat? expression with
  | none =>
      rw [lowered] at executed
      simp at executed
  | some accesses =>
      rw [lowered] at executed
      dsimp only at executed
      split at executed
      · simp at executed
      · simp at executed
      · rename_i results ran
        rw [Id.run_pure] at executed
        simp only [StepResult.ok.injEq] at executed
        obtain ⟨writes, committed⟩ :=
          executeParsedBlockFloatAtMAB_runCycles_commit accesses _ _
            (fun cycle buses files bar0 bar1 outputs results h target =>
              executeParsedBlockFloat_writeCycle_commit currentState hasSingleLineMask
                expression coordinate accesses _ (fun _ _ _ _ _ _ => rfl) cycle buses files bar0
                bar1 outputs results h target)
            target [0, 1, 2, 3] _ _ _ _ results ran
        refine ⟨writes, ?_⟩
        subst executed
        rw [executeParsedBlockFloatAtMAB_foldl_peRegisters_target noForward coordinate results target (List.finRange 4)
          currentState (List.nodup_finRange 4) (List.mem_finRange target)]
        simpa using committed







theorem executeParsedBlockFloatAtMAB_peRegisters_frame
    (readState currentState : State) (expression : ParsedExpr) (coordinate : MABCoordinate)
    (noForward hasSingleLineMask : Bool) (p : PEId)
    (notTouched : ∀ pe : Fin 4, p ≠ physicalPEId coordinate pe) (next : State)
    (executed : executeParsedBlockFloatAtMAB readState currentState expression coordinate
      noForward hasSingleLineMask = .ok next) :
    next.peRegisters p = currentState.peRegisters p := by
  rw [executeParsedBlockFloatAtMAB.eq_1] at executed
  cases lowered : lowerParsedBlockFloat? expression with
  | none =>
      rw [lowered] at executed
      simp at executed
  | some accesses =>
      rw [lowered] at executed
      dsimp only at executed
      split at executed
      · simp at executed
      · simp at executed
      · rename_i results ran
        rw [Id.run_pure] at executed
        simp only [StepResult.ok.injEq] at executed
        subst executed
        rw [executeParsedBlockFloatAtMAB_foldl_peRegisters_frame noForward coordinate results p (List.finRange 4) currentState
          (fun pe _ => notTouched pe)]

theorem physicalPEId_welcomePE_eq (coordinate : MABCoordinate) (pe : Fin 4)
    (h : physicalPEId coordinate pe = welcomePE) :
    coordinate = ⟨0, 0, 0, 0⟩ := by
  have hv : (((coordinate.group.val * 2 + coordinate.l2b.val) * 8 + coordinate.l1b.val) * 16 +
      coordinate.mab.val) * 4 + pe.val = 0 := by
    have := congrArg Fin.val h
    simpa [physicalPEId, welcomePE] using this
  have hg := coordinate.group.isLt
  have h2 := coordinate.l2b.isLt
  have h1 := coordinate.l1b.isLt
  have hm := coordinate.mab.isLt
  have hp := pe.isLt
  have hgroup : coordinate.group.val = 0 := by omega
  have hl2b : coordinate.l2b.val = 0 := by omega
  have hl1b : coordinate.l1b.val = 0 := by omega
  have hmab : coordinate.mab.val = 0 := by omega
  cases coordinate with
  | mk group l2b l1b mab =>
      cases group with
      | mk gv gp => cases l2b with
        | mk lv lp => cases l1b with
          | mk bv bp => cases mab with
            | mk mv mp => simp_all

theorem executeParsedBlockFloatAtMABs_commit
    (readState : State) (expression : ParsedExpr) (noForward hasSingleLineMask : Bool)
    (p : PEId) :
    ∀ (coordinates : List MABCoordinate) (state : State) (next : State),
      executeParsedBlockFloatAtMABs readState state expression coordinates noForward
        hasSingleLineMask = .ok next →
      (∀ (coordinate : MABCoordinate) (state' next' : State), coordinate ∈ coordinates →
        executeParsedBlockFloatAtMAB readState state' expression coordinate noForward
          hasSingleLineMask = .ok next' →
        ∃ writes, next'.peRegisters p = commitParsedMaskedWrites (state'.peRegisters p) writes) →
      ∃ writes, next.peRegisters p = commitParsedMaskedWrites (state.peRegisters p) writes := by
  intro coordinates
  induction coordinates with
  | nil =>
      intro state next executed _
      simp only [executeParsedBlockFloatAtMABs.eq_1, StepResult.ok.injEq] at executed
      subst executed
      exact ⟨[], rfl⟩
  | cons coordinate rest ih =>
      intro state next executed stepCommit
      rw [executeParsedBlockFloatAtMABs.eq_2] at executed
      split at executed
      · simp at executed
      · simp at executed
      · rename_i middle ran
        obtain ⟨headWrites, head⟩ := stepCommit coordinate state middle (by simp) ran
        obtain ⟨tailWrites, tail⟩ := ih middle next executed
          (fun coordinate' state' next' member ran' =>
            stepCommit coordinate' state' next' (List.mem_cons_of_mem _ member) ran')
        exact ⟨headWrites ++ tailWrites, by
          rw [tail, head, commitParsedMaskedWrites_append]⟩







theorem executeParsedBlockFloatProducer_commit
    (readState currentState next : State) (expressions : List ParsedExpr)
    (noForward hasSingleLineMask : Bool)
    (executed : executeParsedBlockFloatProducer readState currentState expressions noForward
      hasSingleLineMask = .ok next) :
    ∃ writes, next.peRegisters welcomePE =
      commitParsedMaskedWrites (currentState.peRegisters welcomePE) writes := by
  cases filtered : expressions.filter parsedExprIsBlockFloatProducer with
  | nil =>
      rw [executeParsedBlockFloatProducer, filtered] at executed
      simp only [StepResult.ok.injEq] at executed
      subst executed
      exact ⟨[], rfl⟩
  | cons expression rest =>
      cases rest with
      | nil =>
          rw [executeParsedBlockFloatProducer, filtered] at executed
          refine executeParsedBlockFloatAtMABs_commit readState expression noForward
            hasSingleLineMask welcomePE allMABCoordinates currentState next executed ?_
          intro coordinate state' next' member ran
          by_cases zero : coordinate = ⟨0, 0, 0, 0⟩
          · subst zero
            obtain ⟨ws, committed⟩ := executeParsedBlockFloatAtMAB_pe_commit readState state'
              expression ⟨0, 0, 0, 0⟩ noForward hasSingleLineMask 0 next' ran
            exact ⟨ws, committed⟩
          · have frame := executeParsedBlockFloatAtMAB_peRegisters_frame readState state'
              expression coordinate noForward hasSingleLineMask welcomePE
              (fun pe hpe => zero (physicalPEId_welcomePE_eq coordinate pe hpe.symm)) next' ran
            exact ⟨[], frame⟩
      | cons second remaining =>
          rw [executeParsedBlockFloatProducer, filtered] at executed
          simp at executed

theorem welcomePEBlockFloatStageCommit : WelcomePEBlockFloatStageCommit :=
  fun readState currentState next expressions noForward hasSingleLineMask executed =>
    executeParsedBlockFloatProducer_commit readState currentState next expressions noForward
      hasSingleLineMask executed

end ProofsLean.MNCore
