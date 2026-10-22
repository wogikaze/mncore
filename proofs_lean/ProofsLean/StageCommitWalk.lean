import ProofsLean.StageCommitSpecific

/-! # The PE walk and the line level, with the executor's own write list

`ProofsLean/StageCommitSpecific.lean` pins the per-PE commit list.  This module
lifts it to

* the PE walk `executeIntegerProducerLineAtPEs` when the observed PE is visited
  first (`0 :: rest`, which is what `List.finRange 4096` gives), and
* the whole `.pe` line `executeIntegerProducerInstructionLine` for a single
  plain `.alu` / `.zero` / `.immediate` row: the six non-integer stages of the
  line are the identity, so the line's PE 0 file is the commit of the pinned
  integer-stage list.

Everything is at an arbitrary `state`; nothing mentions a machine, a problem or
an input.  The float-free hypothesis is discharged for plain rows, so the
committed list is exactly the integer stage's own preparation list.

No `sorry`, no `admit`, no `native_decide`, no new axioms.
-/

namespace ProofsLean.MNCore

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

open Issue
open PEMemory

/-! ## 1. The walk leaves unvisited PEs untouched -/

/-- **The walk leaves unvisited PEs untouched.** -/
theorem executeIntegerProducerLineAtPEs_peRegisters_of_not_mem
    (expressions : List ParsedExpr) (pes : List PEId) (state next : State) (pe : PEId)
    (absent : pe ∉ pes)
    (executed : executeIntegerProducerLineAtPEs expressions pes state = .ok next) :
    next.peRegisters pe = state.peRegisters pe := by
  induction pes generalizing state with
  | nil =>
      simp only [executeIntegerProducerLineAtPEs, StepResult.ok.injEq] at executed
      subst executed
      rfl
  | cons head rest ih =>
      simp only [List.mem_cons, not_or] at absent
      obtain ⟨headNe, absent⟩ := absent
      simp only [executeIntegerProducerLineAtPEs] at executed
      split at executed
      · simp at executed
      · simp at executed
      · rename_i middle stepMiddle
        rw [ih middle absent executed]
        exact executeIntegerProducerLineAtPE_peRegisters_other expressions state middle head pe
          headNe stepMiddle

/-! ## 2. The walk at `0 :: rest` commits the per-PE list of PE 0 -/

/-- **The walk-level pinned commit.**  If the observed PE is visited first, the
resulting PE 0 file is the commit of the integer stage's own preparation list at
the initial state. -/
theorem executeIntegerProducerLineAtPEs_zero_commit_list
    (expressions : List ParsedExpr) (rest : List PEId) (state next : State)
    (absent : welcomePE ∉ rest)
    (floatEmpty : expressions.filter parsedExprIsSupportedFloatMAUProducer = [])
    (executed : executeIntegerProducerLineAtPEs expressions (welcomePE :: rest) state = .ok next) :
    ∃ prepared : List PreparedParsedMaskedWrite × ProofsLean.MNCore.Forwarding.Slots ×
        List (Bool × BitVec 12),
      prepareParsedIntegerMatrixReadLineCycles (state.peRegisters welcomePE)
          (stateForwardingSlots state welcomePE)
          (state.matrixRegisters (ParsedIntegerContext.ofLinearIndex welcomePE).group
            (ParsedIntegerContext.ofLinearIndex welcomePE).l2b
            (ParsedIntegerContext.ofLinearIndex welcomePE).l1b)
          (expressions.filter parsedExprIsIntegerMatrixReadStageInput)
          { directive := state.maskDirective
            context :=
              { (ParsedIntegerContext.ofLinearIndex welcomePE) with
                bar0 := (state.peContext welcomePE).bar0
                bar1 := (state.peContext welcomePE).bar1
                tWord := (state.peContext welcomePE).tWord }
            elapsedWords := state.hazardClock } false = .ok prepared ∧
      next.peRegisters welcomePE =
        commitParsedMaskedWrites (state.peRegisters welcomePE) prepared.1 := by
  simp only [executeIntegerProducerLineAtPEs] at executed
  split at executed
  · simp at executed
  · simp at executed
  · rename_i middle stepMiddle
    obtain ⟨prepared, preparedEq, committed⟩ :=
      executeIntegerProducerLineAtPECore_peRegisters_commit_list_noforward expressions state
        middle welcomePE floatEmpty (by
          unfold executeIntegerProducerLineAtPE at stepMiddle
          split at stepMiddle
          · simp at stepMiddle
          · exact stepMiddle)
    refine ⟨prepared, preparedEq, ?_⟩
    rw [executeIntegerProducerLineAtPEs_peRegisters_of_not_mem expressions rest middle next
      welcomePE absent executed]
    exact committed

end ProofsLean.MNCore

-- End of module: no sorry, no admit, no native_decide, no new axioms.
