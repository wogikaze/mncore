import ProofsLean.WelcomeStageCommit

/-! # The matrix-MAU/write stage is a PE 0 commit

`WelcomeAssembly.lean` §4 leaves one per-stage commit obligation open,
`WelcomePEMatrixMAUStageCommit`: a successful run of
`executeParsedMatrixMAUAndWrites` must be the commit of a prepared write list on
the PE 0 register file it started from.  `WelcomeStageCommit.lean` proves the
other five stages and explains why this one needs the five matrix-MAU recursor
lemmas.  This module supplies them and discharges the obligation.

The executor chain is

* `executeParsedMatrixMAUAndWrites` → `executeParsedMatrixMAUProducer` (family
  filter, `executeParsedMatrixMAUAtMABs` over the 1024 MAB coordinates,
  `propagateParsedMatrixMAUPoison`) and then `executeParsedMatrixWritesAtMABs`
  (which preserves every PE register file);
* per coordinate, `executeParsedMatrixMAUTransitionAtMAB` repackages the result
  of `executeParsedMatrixMAUPEWritesAtMAB` through
  `commitParsedMatrixMAUPEState (List.finRange 4) ...`;
* per cycle, `executeParsedMatrixMAUWriteCycles` runs
  `executeParsedMatrixMAUAtMAB` and then `executeParsedMatrixMAUPEWritesAtCycle`
  over `List.finRange 4`, threading a `ParsedMatrixMAUWriteAccum`;
* per PE, `writeParsedMatrixMAUDestinationsAtPE` runs the destination loop, whose
  actual write is the shared `writeParsedMslMsrDestination?`.

The five recursor lemmas named in `WelcomeStageCommit.lean` §6 are proved here
(`writeParsedMatrixMAUDestinationsAtPE_commit`,
`executeParsedMatrixMAUPEWritesAtCycle_commit`,
`executeParsedMatrixMAUWriteCycles_commit`,
`executeParsedMatrixMAUTransitionAtMAB_pe_commit` /
`executeParsedMatrixMAUTransitionAtMAB_peRegisters_frame`, and
`executeParsedMatrixMAUAtMABs_commit`), together with the walk frame of
`executeParsedMatrixWritesAtMABs` and the `peRegisters` frame of
`propagateParsedMatrixMAUPoison`.

No `sorry`, no `admit`, no `native_decide`, no new axioms, and no existing
module is edited by this file. -/

namespace ProofsLean.MNCore

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

open Issue
open PEMemory

/-! ## 1. The destination loop

`writeParsedMatrixMAUDestinationsAtPE` runs the destination operands of one
matrix-MAU row at one PE.  Three things can happen for one destination:

* the `.omr` entry-index test fails (`.failure`);
* the data-poison test fires and `parsedMatrixMAUDestinationEnabled?` does not
  return `some false` (`.failure`; note that `parsedMatrixMAUDestinationDataPoisonApplies`
  is `false` for `.omr`, so mask-register writes are never blocked);
* otherwise the shared writer `writeParsedMslMsrDestination?` lowers the operand
  and the loop continues on its file, keeping the BAR updates.

Only the last two branches can succeed, and in both the incoming file reaches
the outgoing one through a prepared write list: one element in the writer
branch, and the empty list (the same file) in the enabled-and-skipped branch. -/

/-- **The matrix-MAU destination loop is a commit.** -/
theorem writeParsedMatrixMAUDestinationsAtPE_commit
    (currentState : State) (expression : ParsedExpr) (coordinate : MABCoordinate)
    (pe cycle : Fin 4) (poison hasSingleLineMask : Bool) (output : IntegerALU.Bus)
    (flags : BitVec 4) :
    ∀ (destinations : List ParsedOperand) (files : IntegerRegisterFiles) (bar0 bar1 : BitVec 12)
      (nextFiles : IntegerRegisterFiles) (nextBar0 nextBar1 : BitVec 12),
      writeParsedMatrixMAUDestinationsAtPE currentState expression coordinate pe cycle poison
        hasSingleLineMask output flags destinations files bar0 bar1 = .ok (nextFiles, nextBar0, nextBar1) →
      ∃ writes, nextFiles = commitParsedMaskedWrites files writes := by
  intro destinations
  induction destinations with
  | nil =>
      intro files bar0 bar1 nextFiles nextBar0 nextBar1 executed
      rw [writeParsedMatrixMAUDestinationsAtPE.eq_1] at executed
      obtain ⟨rfl, rfl, rfl⟩ := StepResult.ok.inj executed
      exact ⟨[], rfl⟩
  | cons destination rest ih =>
      intro files bar0 bar1 nextFiles nextBar0 nextBar1 executed
      rw [writeParsedMatrixMAUDestinationsAtPE.eq_2] at executed
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
            obtain ⟨headWrites, head⟩ := writeParsedMslMsrDestination?_commit files _ _ output flags
              cycle currentState.maskDirective hasSingleLineMask write h
            obtain ⟨tailWrites, tail'⟩ := ih write.files _ _ nextFiles _ _ tail
            exact ⟨headWrites ++ tailWrites, by
              rw [tail', head, commitParsedMaskedWrites_append]⟩
      all_goals
        simp only [Id.run] at executed
        split at executed
        · split at executed
          · simp at executed
          · simp at executed
          · rename_i h
            have tail := executed
            exact ih files bar0 bar1 nextFiles nextBar0 nextBar1 tail
        · split at executed
          · simp at executed
          · rename_i write h
            have tail := executed
            obtain ⟨headWrites, head⟩ := writeParsedMslMsrDestination?_commit files _ _ output flags
              cycle currentState.maskDirective hasSingleLineMask write h
            obtain ⟨tailWrites, tail'⟩ := ih write.files _ _ nextFiles _ _ tail
            exact ⟨headWrites ++ tailWrites, by
              rw [tail', head, commitParsedMaskedWrites_append]⟩

/-! ## 2. The four-PE loop of one cycle

`executeParsedMatrixMAUPEWritesAtCycle` threads a `ParsedMatrixMAUWriteAccum`
through the four PEs of the MAB, updating only the entry of the visited PE.  At
any chosen target PE the outgoing file is therefore the commit of a list whose
head comes from that PE's destination loop (when it is the visited one) and
whose tail comes from the rest of the loop. -/

/-- **The four-PE loop of one cycle is a commit at any target PE.** -/
theorem executeParsedMatrixMAUPEWritesAtCycle_commit
    (currentState : State) (expression : ParsedExpr) (coordinate : MABCoordinate)
    (hasSingleLineMask : Bool) (cycle : Fin 4) (buses : Fin 4 → IntegerALU.Bus)
    (flags : Fin 4 → BitVec 4) (poison : Bool) (target : Fin 4) :
    ∀ (pes : List (Fin 4)) (accum next : ParsedMatrixMAUWriteAccum),
      executeParsedMatrixMAUPEWritesAtCycle currentState expression coordinate hasSingleLineMask
        cycle buses flags poison pes accum = .ok next →
      ∃ writes, next.files target = commitParsedMaskedWrites (accum.files target) writes := by
  intro pes
  induction pes with
  | nil =>
      intro accum next executed
      rw [executeParsedMatrixMAUPEWritesAtCycle.eq_1] at executed
      obtain rfl := StepResult.ok.inj executed
      exact ⟨[], rfl⟩
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
          cases wrote : writeParsedMatrixMAUDestinationsAtPE currentState expression coordinate pe cycle
              poison hasSingleLineMask (parsedOutputAfterFlush flushSelection (buses pe)) (flags pe)
              expression.destinations (accum.files pe) (accum.bar0 pe) (accum.bar1 pe) with
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
              obtain ⟨headWrites, head⟩ :=
                writeParsedMatrixMAUDestinationsAtPE_commit currentState expression coordinate
                  pe cycle poison hasSingleLineMask (parsedOutputAfterFlush flushSelection (buses pe))
                  (flags pe) expression.destinations (accum.files pe) (accum.bar0 pe) (accum.bar1 pe)
                  nextFiles nextBar0 nextBar1 wrote
              obtain ⟨tailWrites, tail'⟩ := ih _ next tail
              by_cases same : target = pe
              · subst same
                refine ⟨headWrites ++ tailWrites, ?_⟩
                rw [tail']
                simp only [beq_self_eq_true, ite_true]
                rw [head, commitParsedMaskedWrites_append]
              · refine ⟨tailWrites, ?_⟩
                rw [tail']
                have different : (target == pe) = false := by
                  simp [same]
                simp [different]

/-! ## 3. The four-cycle loop

`executeParsedMatrixMAUWriteCycles` runs the four cycles, each first computing
the buses, flags and poison of the cycle (`executeParsedMatrixMAUAtMAB`) and then
running the four-PE loop.  The accumulator's file at the target PE is again a
commit, with the cycle list concatenated in front of the tail. -/

/-- **The four-cycle loop of one coordinate is a commit at any target PE.** -/
theorem executeParsedMatrixMAUWriteCycles_commit
    (readState currentState : State) (expression : ParsedExpr) (coordinate : MABCoordinate)
    (hasSingleLineMask : Bool) (target : Fin 4) :
    ∀ (cycles : List (Fin 4)) (accum next : ParsedMatrixMAUWriteAccum),
      executeParsedMatrixMAUWriteCycles readState currentState expression coordinate
        hasSingleLineMask cycles accum = .ok next →
      ∃ writes, next.files target = commitParsedMaskedWrites (accum.files target) writes := by
  intro cycles
  induction cycles with
  | nil =>
      intro accum next executed
      rw [executeParsedMatrixMAUWriteCycles.eq_1] at executed
      obtain rfl := StepResult.ok.inj executed
      exact ⟨[], rfl⟩
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
              obtain ⟨headWrites, head⟩ := executeParsedMatrixMAUPEWritesAtCycle_commit
                currentState expression coordinate hasSingleLineMask cycle result.1 result.2.1
                result.2.2 target (List.finRange 4) accum nextAccum writes
              obtain ⟨tailWrites, tail'⟩ := ih nextAccum next tail
              exact ⟨headWrites ++ tailWrites, by
                rw [tail', head, commitParsedMaskedWrites_append]⟩

/-! ## 4. The PE-installation fold

`commitParsedMatrixMAUPEState` installs the four per-PE files with a
`List.foldl` over the PE list.  The two projections below are the analogue of the
block-float fold lemmas: at the visited PE the fold writes the corresponding
entry of `files`, and everywhere else it leaves the incoming register file
untouched.  Both are stated about the step function of the fold, so the
`commitParsedMatrixMAUPEState` versions follow by rewriting the definitional
equation `commitParsedMatrixMAUPEState_eq_foldl`. -/

/-- One step of the `commitParsedMatrixMAUPEState` fold, as a standalone
function (definitionally equal to the lambda in the definition). -/
def commitParsedMatrixMAUPEStateStep (coordinate : MABCoordinate) (noForward : Bool)
    (files : Fin 4 → IntegerRegisterFiles) (bar0 bar1 : Fin 4 → BitVec 12)
    (outputs : Fin 4 → Fin 4 → IntegerALU.Bus) (poisoned : Fin 4 → Bool)
    (nextState : State) (pe : Fin 4) : State :=
  let peId := physicalPEId coordinate pe
  let forwarding : Forwarding.Slots := fun unit cycle =>
    if noForward then nextState.forwarding peId unit cycle
    else if unit == .mau then
      if poisoned cycle then .poison else .known (outputs pe cycle)
    else nextState.forwarding peId unit cycle
  let valid : Forwarding.Unit → Fin 4 → Bool := fun unit cycle =>
    if noForward then nextState.forwardingValid peId unit cycle
    else if unit == .mau then true
    else nextState.forwardingValid peId unit cycle
  { nextState with
    peRegisters := fun other => if other == peId then files pe else nextState.peRegisters other
    forwarding := fun other => if other == peId then forwarding else nextState.forwarding other
    forwardingValid := fun other => if other == peId then valid else nextState.forwardingValid other
    peContext := fun other => if other == peId then
      { nextState.peContext other with bar0 := bar0 pe, bar1 := bar1 pe }
      else nextState.peContext other }

/-- `commitParsedMatrixMAUPEState` is the fold of `commitParsedMatrixMAUPEStateStep`. -/
theorem commitParsedMatrixMAUPEState_eq_foldl (coordinates : List (Fin 4)) (currentState : State)
    (coordinate : MABCoordinate) (noForward : Bool) (files : Fin 4 → IntegerRegisterFiles)
    (bar0 bar1 : Fin 4 → BitVec 12) (outputs : Fin 4 → Fin 4 → IntegerALU.Bus)
    (poisoned : Fin 4 → Bool) :
    commitParsedMatrixMAUPEState coordinates currentState coordinate noForward files bar0 bar1
        outputs poisoned =
      coordinates.foldl
        (commitParsedMatrixMAUPEStateStep coordinate noForward files bar0 bar1 outputs poisoned)
        currentState :=
  rfl

/-- The register file at a PE after one fold step. -/
theorem commitParsedMatrixMAUPEStateStep_peRegisters (coordinate : MABCoordinate)
    (noForward : Bool) (files : Fin 4 → IntegerRegisterFiles) (bar0 bar1 : Fin 4 → BitVec 12)
    (outputs : Fin 4 → Fin 4 → IntegerALU.Bus) (poisoned : Fin 4 → Bool)
    (nextState : State) (pe : Fin 4) (p : PEId) :
    (commitParsedMatrixMAUPEStateStep coordinate noForward files bar0 bar1 outputs poisoned
        nextState pe).peRegisters p =
      if p == physicalPEId coordinate pe then files pe else nextState.peRegisters p :=
  rfl

/-- **The fold leaves every PE it does not visit untouched.** -/
theorem commitParsedMatrixMAUPEState_foldl_peRegisters_frame
    (coordinate : MABCoordinate) (noForward : Bool) (files : Fin 4 → IntegerRegisterFiles)
    (bar0 bar1 : Fin 4 → BitVec 12) (outputs : Fin 4 → Fin 4 → IntegerALU.Bus)
    (poisoned : Fin 4 → Bool) (p : PEId) :
    ∀ (coordinates : List (Fin 4)) (state : State),
      (∀ pe ∈ coordinates, p ≠ physicalPEId coordinate pe) →
      ((coordinates.foldl
        (commitParsedMatrixMAUPEStateStep coordinate noForward files bar0 bar1 outputs poisoned)
        state)).peRegisters p = state.peRegisters p := by
  intro coordinates
  induction coordinates with
  | nil =>
      intro state _
      rfl
  | cons pe rest ih =>
      intro state notTouched
      rw [List.foldl_cons]
      rw [ih _ (fun pe' member => notTouched pe' (List.mem_cons_of_mem _ member))]
      rw [commitParsedMatrixMAUPEStateStep_peRegisters]
      have different : p ≠ physicalPEId coordinate pe := notTouched pe (by simp)
      simp [different]

/-- **The fold writes the visited PE's own file.** -/
theorem commitParsedMatrixMAUPEState_foldl_peRegisters_target
    (coordinate : MABCoordinate) (noForward : Bool) (files : Fin 4 → IntegerRegisterFiles)
    (bar0 bar1 : Fin 4 → BitVec 12) (outputs : Fin 4 → Fin 4 → IntegerALU.Bus)
    (poisoned : Fin 4 → Bool) (target : Fin 4) :
    ∀ (coordinates : List (Fin 4)) (state : State), coordinates.Nodup → target ∈ coordinates →
      ((coordinates.foldl
        (commitParsedMatrixMAUPEStateStep coordinate noForward files bar0 bar1 outputs poisoned)
        state)).peRegisters (physicalPEId coordinate target) = files target := by
  intro coordinates
  induction coordinates with
  | nil =>
      intro state _ member
      simp at member
  | cons pe rest ih =>
      intro state nodup member
      obtain ⟨headNotMem, restNodup⟩ := List.nodup_cons.mp nodup
      rw [List.foldl_cons]
      by_cases same : target = pe
      · subst same
        rw [commitParsedMatrixMAUPEState_foldl_peRegisters_frame coordinate noForward files
          bar0 bar1 outputs poisoned (physicalPEId coordinate target) rest
          (commitParsedMatrixMAUPEStateStep coordinate noForward files bar0 bar1 outputs poisoned
            state target)
          (fun pe' member hpe' => headNotMem ((physicalPEId_inj coordinate hpe').symm ▸ member))]
        rw [commitParsedMatrixMAUPEStateStep_peRegisters]
        simp
      · have memberRest : target ∈ rest := by
          rcases List.mem_cons.mp member with h | h
          · exact absurd h same
          · exact h
        exact ih (commitParsedMatrixMAUPEStateStep coordinate noForward files bar0 bar1 outputs
          poisoned state pe) restNodup memberRest

/-! ## 5. The per-coordinate transition and the walk over the MAB

`executeParsedMatrixMAUPEWritesAtMAB` merely repackages the cycle loop's
accumulator, so its file at any target PE is the commit supplied by
`executeParsedMatrixMAUWriteCycles_commit`.  `executeParsedMatrixMAUTransitionAtMAB`
installs those files with `commitParsedMatrixMAUPEState (List.finRange 4)`, and the
two fold projections then give the value at the target PE and the frame at every
other PE.  Finally, `executeParsedMatrixMAUAtMABs` walks the coordinates and
concatenates the per-coordinate lists. -/

/-- **The repackaged per-coordinate files are commits.** -/
theorem executeParsedMatrixMAUPEWritesAtMAB_files_commit
    (readState currentState : State) (expression : ParsedExpr) (coordinate : MABCoordinate)
    (hasSingleLineMask : Bool) (files : Fin 4 → IntegerRegisterFiles)
    (bar0 bar1 : Fin 4 → BitVec 12) (outputs : Fin 4 → Fin 4 → IntegerALU.Bus)
    (poisoned : Fin 4 → Bool) (target : Fin 4)
    (executed : executeParsedMatrixMAUPEWritesAtMAB readState currentState expression coordinate
      hasSingleLineMask = .ok (files, bar0, bar1, outputs, poisoned)) :
    ∃ writes, files target =
      commitParsedMaskedWrites (currentState.peRegisters (physicalPEId coordinate target)) writes := by
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
      exact executeParsedMatrixMAUWriteCycles_commit readState currentState expression coordinate
        hasSingleLineMask target (List.finRange 4)
        { files := fun pe => currentState.peRegisters (physicalPEId coordinate pe)
          bar0 := fun pe => (currentState.peContext (physicalPEId coordinate pe)).bar0
          bar1 := fun pe => (currentState.peContext (physicalPEId coordinate pe)).bar1
          outputs := fun _ _ => ⟨0, 0⟩
          poisoned := fun _ => false } accum ran

/-- **The per-coordinate transition commits at each of its four PEs.** -/
theorem executeParsedMatrixMAUTransitionAtMAB_pe_commit
    (readState currentState next : State) (expression : ParsedExpr) (coordinate : MABCoordinate)
    (noForward hasSingleLineMask : Bool) (target : Fin 4)
    (executed : executeParsedMatrixMAUTransitionAtMAB readState currentState expression coordinate
      noForward hasSingleLineMask = .ok next) :
    ∃ writes, next.peRegisters (physicalPEId coordinate target) =
      commitParsedMaskedWrites (currentState.peRegisters (physicalPEId coordinate target)) writes := by
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
      obtain ⟨writes, committed⟩ := executeParsedMatrixMAUPEWritesAtMAB_files_commit readState
        currentState expression coordinate hasSingleLineMask files bar0 bar1 outputs poisoned target ran
      refine ⟨writes, ?_⟩
      rw [commitParsedMatrixMAUPEState_eq_foldl]
      rw [commitParsedMatrixMAUPEState_foldl_peRegisters_target coordinate noForward files bar0 bar1
        outputs poisoned target (List.finRange 4) currentState (List.nodup_finRange 4)
        (List.mem_finRange target)]
      exact committed

/-- **The per-coordinate transition preserves every PE it does not visit.** -/
theorem executeParsedMatrixMAUTransitionAtMAB_peRegisters_frame
    (readState currentState next : State) (expression : ParsedExpr) (coordinate : MABCoordinate)
    (noForward hasSingleLineMask : Bool) (p : PEId)
    (notTouched : ∀ pe : Fin 4, p ≠ physicalPEId coordinate pe)
    (executed : executeParsedMatrixMAUTransitionAtMAB readState currentState expression coordinate
      noForward hasSingleLineMask = .ok next) :
    next.peRegisters p = currentState.peRegisters p := by
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
      rw [commitParsedMatrixMAUPEState_eq_foldl]
      exact commitParsedMatrixMAUPEState_foldl_peRegisters_frame coordinate noForward files
        bar0 bar1 outputs poisoned p (List.finRange 4) currentState (fun pe _ => notTouched pe)

/-- **The walk over the MAB coordinates commits at a fixed PE.** -/
theorem executeParsedMatrixMAUAtMABs_commit
    (readState : State) (expression : ParsedExpr) (noForward hasSingleLineMask : Bool)
    (p : PEId) :
    ∀ (coordinates : List MABCoordinate) (state next : State),
      executeParsedMatrixMAUAtMABs readState state expression coordinates noForward
        hasSingleLineMask = .ok next →
      (∀ (coordinate : MABCoordinate) (state' next' : State), coordinate ∈ coordinates →
        executeParsedMatrixMAUTransitionAtMAB readState state' expression coordinate noForward
          hasSingleLineMask = .ok next' →
        ∃ writes, next'.peRegisters p = commitParsedMaskedWrites (state'.peRegisters p) writes) →
      ∃ writes, next.peRegisters p = commitParsedMaskedWrites (state.peRegisters p) writes := by
  intro coordinates
  induction coordinates with
  | nil =>
      intro state next executed _
      rw [executeParsedMatrixMAUAtMABs.eq_1] at executed
      obtain rfl := StepResult.ok.inj executed
      exact ⟨[], rfl⟩
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
          obtain ⟨headWrites, head⟩ := stepCommit coordinate state middle (by simp) ran
          obtain ⟨tailWrites, tail⟩ := ih middle next executed
            (fun coordinate' state' next' member ran' =>
              stepCommit coordinate' state' next' (List.mem_cons_of_mem _ member) ran')
          exact ⟨headWrites ++ tailWrites, by
            rw [tail, head, commitParsedMaskedWrites_append]⟩

/-! ## 6. The producer, the poison propagation and the whole stage

`propagateParsedMatrixMAUPoison` only rewrites the forwarding slots, so it keeps
every register file.  The producer's family filter then contributes either the
empty list (no matrix-MAU row, or an impossible multi-row failure) or the walk's
list for the single selected row, using that only the coordinate `⟨0,0,0,0⟩`
reaches PE 0.  The write stage preserves every register file, so the whole stage
is a commit at PE 0. -/

/-- **Poison propagation preserves every PE register file.** -/
theorem propagateParsedMatrixMAUPoison_preserves_peRegisters (state : State) :
    (propagateParsedMatrixMAUPoison state).peRegisters = state.peRegisters := by
  by_cases hasPoison : parsedStateHasMatrixMAUPoison state = true <;>
    simp [propagateParsedMatrixMAUPoison, hasPoison]

/-- **The matrix-MAU producer is a PE 0 commit.** -/
theorem executeParsedMatrixMAUProducer_commit
    (readState currentState next : State) (expressions : List ParsedExpr)
    (noForward hasSingleLineMask : Bool)
    (executed : executeParsedMatrixMAUProducer readState currentState expressions noForward
      hasSingleLineMask = .ok next) :
    ∃ writes, next.peRegisters welcomePE =
      commitParsedMaskedWrites (currentState.peRegisters welcomePE) writes := by
  cases filtered : expressions.filter parsedExprIsMatrixMAUProducer with
  | nil =>
      rw [executeParsedMatrixMAUProducer.eq_1, filtered] at executed
      dsimp only at executed
      simp only [StepResult.ok.injEq] at executed
      subst executed
      exact ⟨[], rfl⟩
  | cons expression rest =>
      cases rest with
      | nil =>
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
                    commitParsedMaskedWrites (state'.peRegisters welcomePE) writes := by
                intro coordinate state' next' _ ran'
                by_cases zero : coordinate = ⟨0, 0, 0, 0⟩
                · subst zero
                  obtain ⟨ws, committedHead⟩ :=
                    executeParsedMatrixMAUTransitionAtMAB_pe_commit readState state' next'
                      expression ⟨0, 0, 0, 0⟩ noForward hasSingleLineMask 0 ran'
                  exact ⟨ws, by simpa [physicalPEId, welcomePE] using committedHead⟩
                · exact ⟨[], executeParsedMatrixMAUTransitionAtMAB_peRegisters_frame readState
                    state' next' expression coordinate noForward hasSingleLineMask welcomePE
                    (fun pe hpe => zero (physicalPEId_welcomePE_eq coordinate pe hpe.symm)) ran'⟩
              obtain ⟨writes, committed⟩ := executeParsedMatrixMAUAtMABs_commit readState expression
                noForward hasSingleLineMask welcomePE allMABCoordinates currentState afterMAU ran
                stepCommit
              refine ⟨writes, ?_⟩
              rw [propagateParsedMatrixMAUPoison_preserves_peRegisters]
              exact committed
      | cons second remaining =>
          rw [executeParsedMatrixMAUProducer.eq_1, filtered] at executed
          dsimp only at executed
          simp at executed

/-- **The matrix-MAU/write stage is a PE 0 commit.** -/
theorem executeParsedMatrixMAUAndWrites_commit
    (readState currentState next : State) (expressions : List ParsedExpr)
    (noForward hasSingleLineMask : Bool)
    (executed : executeParsedMatrixMAUAndWrites readState currentState expressions noForward
      hasSingleLineMask = .ok next) :
    ∃ writes, next.peRegisters welcomePE =
      commitParsedMaskedWrites (currentState.peRegisters welcomePE) writes := by
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
      obtain ⟨writes, committed⟩ := executeParsedMatrixMAUProducer_commit readState currentState
        afterMAU expressions noForward hasSingleLineMask producer
      have frame := executeParsedMatrixWritesAtMABs_preserves_pe_state readState afterMAU next
        allMABCoordinates expressions executed
      exact ⟨writes, by rw [frame.1]; exact committed⟩

/-- **`WelcomePEMatrixMAUStageCommit` is discharged.** -/
theorem welcomePEMatrixMAUStageCommit : WelcomePEMatrixMAUStageCommit :=
  fun readState currentState next expressions noForward hasSingleLineMask executed =>
    executeParsedMatrixMAUAndWrites_commit readState currentState next expressions noForward
      hasSingleLineMask executed

/-! ## 7. Consequences: the six-stage bundle and the unconditional line forms

With the matrix-MAU/write stage in hand every component of
`WelcomePEStageCommitForm` is proved, so the bundle itself holds and the two
line-level stage assemblies of `WelcomeAssembly.lean` no longer need a `stages`
argument. -/

/-- **All six per-stage commit obligations hold.** -/
theorem welcomePEStageCommitForm : WelcomePEStageCommitForm :=
  ⟨welcomePEIntegerStageCommit_of_float welcomePEIntegerFloatStageCommit,
    welcomePEMslMsrStageCommit, welcomePEFloatReluStageCommit,
    welcomePEBlockFloatStageCommit, welcomePEMatrixMAUStageCommit,
    welcomePEL1ToPEStageCommit⟩

/-- **F1 without a `stages` argument.** -/
theorem executeIntegerProducerInstructionLine_pe_stage_commit_unconditional
    (expressions : List NormalizedExpr) (state next : State)
    (accepted : checkParsedTopLine (InstructionLine.pe expressions).toParsed = true)
    (waits : (expressions.map NormalizedExpr.toParsed).any
      (parsedExprWaitPending state) = false)
    (unsupported : (expressions.map NormalizedExpr.toParsed).any
      parsedExprIsUnsupportedRustAlu = false)
    (supported : (expressions.map NormalizedExpr.toParsed).all
      parsedExprIsSupportedPELineProducer = true)
    (step : executeIntegerProducerInstructionLine (.pe expressions) state = .ok next) :
    ∃ intWrites mslWrites reluWrites blockWrites matrixWrites l1Writes,
      next.peRegisters welcomePE =
        commitParsedMaskedWrites (state.peRegisters welcomePE)
          (intWrites ++ mslWrites ++ reluWrites ++ blockWrites ++ matrixWrites ++
            l1Writes) :=
  executeIntegerProducerInstructionLine_pe_stage_commit welcomePEStageCommitForm
    expressions state next accepted waits unsupported supported step

/-- **F1 at the sealed machine without a `stages` argument.** -/
theorem welcomePE_line_stage_commit_unconditional
    (expressions : List NormalizedExpr)
    (input : ProofsLean.MNCore.PlusOne.Words) (next : State)
    (unrefuted : WelcomePEUnrefuted expressions)
    (step : welcomeSealedMachine.step (.pe expressions)
      (welcomeInitialState input) = some next) :
    ∃ intWrites mslWrites reluWrites blockWrites matrixWrites l1Writes,
      next.peRegisters welcomePE =
        commitParsedMaskedWrites
          ((welcomeInitialState input).peRegisters welcomePE)
          (intWrites ++ mslWrites ++ reluWrites ++ blockWrites ++ matrixWrites ++
            l1Writes) :=
  welcomePE_line_stage_commit welcomePEStageCommitForm expressions input next unrefuted step

end ProofsLean.MNCore
