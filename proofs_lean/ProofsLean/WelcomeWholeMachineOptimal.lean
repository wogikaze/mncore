import ProofsLean.WelcomeOptimalFinal
import ProofsLean.WelcomeComplete
import ProofsLean.WholeMachineMachine

/-! # Welcome optimality on the hazard-aware whole machine

`ProofsLean/WelcomeOptimalFinal.lean` proves
`Optimal welcomeSealedMachine welcomeSpec welcomeAnswer`, where
`welcomeSealedMachine` throws away the hazard-history layer, the issue check and
the address-mode check of `wholeMachine`.  This module lifts that result to the
**hazard-aware** transition `wholeMachine` of
`ProofsLean/WholeMachineMachine.lean`.

## A typing remark

`ProofsLean.Correct`, `ProofsLean.Problem` and `ProofsLean.Optimal` are stated
for `ProofsLean.Machine` (a total transition `Line → State → Option State`),
while `wholeMachine` is a `ProofsLean.PartialMachine`
(`Line → State → StepResult State`).  The literal phrases
"`Problem wholeMachine`", "`Correct wholeMachine ...`" and
"`Optimal wholeMachine ...`" are therefore not well-typed, and
`wholeMachine.seal` cannot be applied either, because
`wholeMachine.Complete` is *false* (`wholeMachine_not_complete` below: a
positive `nop` carrying an MV wait tag returns `.unknown` from the hazard-aware
initial state, since the pending-MV queue is empty).  What is stated here
instead is

* `PartialExecute` / `PartialProblem` / `PartialCorrect` and
  `welcomeWhole_partialCorrect` — the `PartialMachine`-level statement about
  `wholeMachine` itself: the two-line program runs (every step `.ok`) and
  satisfies the `n + 1` postcondition on `HazardAwareState`.  Together with
  `welcomeWholeAnswer_values` (the hazard-aware and sealed runs end in the same
  machine state) this is the literal statement "the two-line program runs on
  the hazard-aware machine and produces the same LM1 words";
* `PartialLowerBound` / `PartialOptimal` — the same-shape `PartialMachine`
  analogues of `ProofsLean.LowerBound` / `ProofsLean.Optimal`, with
  `welcomeWhole_partialLowerBound : PartialLowerBound wholeMachine
  welcomeWholePartialSpec 2` and
  `welcomeWhole_partialOptimal : PartialOptimal wholeMachine
  welcomeWholePartialSpec welcomeAnswer`.  This is the literal
  "`Optimal wholeMachine ...`" statement, modulo the interface being the
  partial-machine one;
* `welcomeWholeMachine` — the total presentation of `wholeMachine`
  (`.ok` ↦ `some`, `.failure`/`.unknown` ↦ `none`, i.e. `PartialMachine.seal`
  with the unused completeness argument dropped), together with
  `welcomeWholeSpec : Problem welcomeWholeMachine`, `welcomeWholeMachine_correct`,
  `welcomeWholeMachine_lowerBound_two` and `welcomeWholeMachine_optimal`
  (these are the statements in the vocabulary of `ProofsLean.Optimal`).

## The two links that make the lift work

1. **Value projection.**  A successful hazard-aware step *is* the sealed
   value step on `state.machine`: `executeHazardAwareNormalizedLineCore` can
   only return `.ok` on a line whose `.failure`/`.unknown` sites were passed,
   and in that case the `.ok` payload's machine is exactly the payload of
   `executeNormalizedLine` (`executeHazardAwareNormalizedLineCore_ok_project`).
   A hazard *violation* therefore only ever removes successful whole-machine
   runs; it never changes the resulting values.  This is why the sealed-machine
   lower bound transfers.
2. **The hazard checks pass on the Welcome lines.**  `welcomeWhole_step_ok`
   proves the stronger statement that the whole-machine step *returns* `.ok`:
   the issue check is `welcome_checkParsedTopLine`, the address-mode check is
   `welcome_addressModesValid`, the PE hazard check is discharged from the
   LM1-write/LM0-read shapes of the line's hazard events
   (`welcome_any_peHazardViolated_false`), and the block hazard events are empty
   (`welcome_blockHazardViolated_false`).  This subsumes the
   `.unknown`-freedom of `wholeMachine_welcome_never_unknown`
   (`WelcomeComplete.lean`) for these two lines.

No `sorry`, no `admit`, no `native_decide`, no new axioms.  No existing module
is edited.
-/

namespace ProofsLean.MNCore

open Issue
open PEMemory

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

/-! ## 1. Reducing `Id.run do` blocks

`executeHazardAwareNormalizedLineCore` is an `Id.run do` block with early
returns.  Both facts below are `rfl`; they let `simp` see through the
`pure`/`bind` that the do-notation inserts (Lean does not reduce `Pure.pure`
for `Id` in `simp` by default). -/

theorem welcomeWhole_id_pure_eq {α : Type} (a : α) : (pure a : Id α) = a := rfl

theorem welcomeWhole_id_bind_eq {α β : Type} (a : Id α) (f : α → Id β) :
    (a >>= f) = f a := rfl

/-! ## 2. The value projection

A successful hazard-aware core step projects to a successful sealed step on
`state.machine`, with the same machine payload, and it leaves the stalled-issue
marker untouched. -/

theorem executeHazardAwareNormalizedLineCore_ok_project
    (line : NormalizedLine) (state : HazardAwareState) (next : HazardAwareState)
    (success : executeHazardAwareNormalizedLineCore line state = .ok next) :
    executeNormalizedLine line state.machine = .ok next.machine ∧
      next.stalledPEIssue = state.stalledPEIssue := by
  cases line with
  | maskDirective widthWords targets entry =>
      unfold executeHazardAwareNormalizedLineCore at success
      simp only [Id.run] at success
      cases run : executeNormalizedLine (.maskDirective widthWords targets entry) state.machine with
      | failure => rw [run] at success; simp at success
      | unknown => rw [run] at success; simp at success
      | ok m =>
          rw [run] at success
          have h : (StepResult.ok
              { machine := m, peHistory := state.peHistory,
                blockHistory := state.blockHistory,
                stalledPEIssue := state.stalledPEIssue } : StepResult HazardAwareState) =
              StepResult.ok next := success
          simp only [StepResult.ok.injEq] at h
          exact ⟨congrArg StepResult.ok (congrArg HazardAwareState.machine h),
            (congrArg HazardAwareState.stalledPEIssue h).symm⟩
  | pe expressions =>
      unfold executeHazardAwareNormalizedLineCore at success
      simp only [Id.run, NormalizedLine.toInstruction?, welcomeWhole_id_pure_eq,
        welcomeWhole_id_bind_eq] at success
      cases hp : parsedNormalizedLinePEHazardEvents? state.machine (.pe expressions) with
      | none =>
          simp only [hp] at success
          split at success
          · cases success
          · split at success
            · cases success
            · cases success
      | some events =>
          simp only [hp] at success
          split at success
          · cases success
          · split at success
            · cases success
            · split at success
              · cases success
              · split at success
                · cases success
                · cases run : executeNormalizedLine (.pe expressions) state.machine with
                  | failure => simp only [run] at success; cases success
                  | unknown => simp only [run] at success; cases success
                  | ok m =>
                      simp only [run, StepResult.ok.injEq] at success
                      exact ⟨congrArg StepResult.ok (congrArg HazardAwareState.machine success),
                        (congrArg HazardAwareState.stalledPEIssue success).symm⟩
  | nop count wait =>
      cases count with
      | zero =>
          unfold executeHazardAwareNormalizedLineCore at success
          simp only [Id.run, NormalizedLine.toInstruction?, welcomeWhole_id_pure_eq,
            welcomeWhole_id_bind_eq] at success
          cases success
      | succ k =>
          unfold executeHazardAwareNormalizedLineCore at success
          simp only [Id.run, NormalizedLine.toInstruction?, welcomeWhole_id_pure_eq,
            welcomeWhole_id_bind_eq, parsedNormalizedLinePEHazardEvents?] at success
          split at success
          · cases success
          · split at success
            · cases success
            · split at success
              · cases success
              · split at success
                · cases success
                · cases run : executeNormalizedLine (.nop (k + 1) wait) state.machine with
                  | failure => simp only [run] at success; cases success
                  | unknown => simp only [run] at success; cases success
                  | ok m =>
                      simp only [run, StepResult.ok.injEq] at success
                      exact ⟨congrArg StepResult.ok (congrArg HazardAwareState.machine success),
                        (congrArg HazardAwareState.stalledPEIssue success).symm⟩
  | mv transfer =>
      unfold executeHazardAwareNormalizedLineCore at success
      simp only [Id.run, NormalizedLine.toInstruction?, welcomeWhole_id_pure_eq,
        welcomeWhole_id_bind_eq, parsedNormalizedLinePEHazardEvents?] at success
      split at success
      · cases success
      · split at success
        · cases success
        · split at success
          · cases success
          · split at success
            · cases success
            · cases run : executeNormalizedLine (.mv transfer) state.machine with
              | failure => simp only [run] at success; cases success
              | unknown => simp only [run] at success; cases success
              | ok m =>
                  simp only [run, StepResult.ok.injEq] at success
                  exact ⟨congrArg StepResult.ok (congrArg HazardAwareState.machine success),
                    (congrArg HazardAwareState.stalledPEIssue success).symm⟩

/-- A successful hazard-aware wrapper step without a wait tag is a successful
sealed step with the same machine payload.  The wait-tag branch is excluded by
`noWait`: that branch may complete a pending MV transfer, which changes the
machine *before* the value step, so no such projection can hold there. -/
theorem executeHazardAwareNormalizedLine_ok_project
    (line : NormalizedLine) (state : HazardAwareState) (next : HazardAwareState)
    (notStalled : state.stalledPEIssue = none)
    (noWait : normalizedLineWaitTag? line = none)
    (success : executeHazardAwareNormalizedLine line state = .ok next) :
    executeNormalizedLine line state.machine = .ok next.machine ∧
      next.stalledPEIssue = none := by
  have core : executeHazardAwareNormalizedLineCore line state = .ok next := by
    simpa [executeHazardAwareNormalizedLine, notStalled, noWait] using success
  have projected := executeHazardAwareNormalizedLineCore_ok_project line state next core
  exact ⟨projected.1, projected.2.trans notStalled⟩


/-! ## 3. The hazard-event entries of a Welcome line

`parsedNormalizedLinePEHazardEvents?` returns one event list per PE.  For a
single-expression Welcome line each entry is the event list of that expression,
so its writes are LM1 only and its reads are LM0 only. -/

theorem parsedPEHazardEventsForPE?_singleton (state : State) (expression : ParsedExpr)
    (pe : PEId) :
    parsedPEHazardEventsForPE? state [expression] pe =
      ParsedExpr.toTimedPEHazardEvents? expression (parsedPEHazardControl state pe) := by
  unfold parsedPEHazardEventsForPE?
  dsimp only
  cases h : ParsedExpr.toTimedPEHazardEvents? expression (parsedPEHazardControl state pe) with
  | none => simp [h]
  | some events => simp [h]

/-- Every PE entry of the hazard-event lowering of a Welcome line writes LM1 and
reads LM0 only. -/
theorem welcome_peHazardEvents_entry (base : Nat) (machine : State)
    (events : List (List TimedPEAccess))
    (eventsEq : parsedNormalizedLinePEHazardEvents? machine (.pe [welcomeExpr base]) = some events)
    (pe : PEId) :
    ∃ later, events[pe.val]! = later ∧
      (∀ e ∈ later, e.write = true → e.access.bank = .lm1) ∧
      (∀ e ∈ later, e.write = false → e.access.bank = .lm0) := by
  have mapped : (List.finRange 4096).mapM
      (fun pe => parsedPEHazardEventsForPE? machine [(welcomeExpr base).toParsed] pe) =
      some events := by
    simpa [parsedNormalizedLinePEHazardEvents?, NormalizedLine.toInstruction?] using eventsEq
  obtain ⟨lenEq, getEq⟩ := list_mapM_getElem
    (fun pe => parsedPEHazardEventsForPE? machine [(welcomeExpr base).toParsed] pe)
    (List.finRange 4096) events mapped
  have hk : pe.val < events.length := by
    rw [lenEq]
    simp
  have hk' : pe.val < (List.finRange 4096).length := by simp
  have entry := getEq pe.val hk hk'
  have indexEq : (List.finRange 4096)[pe.val]'hk' = pe := by
    apply Fin.ext
    simp [List.getElem_finRange]
  rw [indexEq] at entry
  obtain ⟨later, laterEq, laterWrite, laterRead⟩ := welcomeExprEvents base
    (parsedPEHazardControl machine pe)
  rw [parsedPEHazardEventsForPE?_singleton] at entry
  have eq : events[pe.val]'hk = later := by
    have both : some (events[pe.val]'hk) = some later := by rw [← entry, laterEq]
    exact Option.some.inj both
  refine ⟨later, ?_, laterWrite, laterRead⟩
  rw [List.getElem!_of_getElem? (List.getElem?_eq_getElem hk)]
  exact eq

/-- No PE hazard constraint of a Welcome line is violated, provided the history
of every PE writes LM1 only. -/
theorem welcome_any_peHazardViolated_false (base : Nat) (state : HazardAwareState)
    (events : List (List TimedPEAccess))
    (eventsEq : parsedNormalizedLinePEHazardEvents? state.machine (.pe [welcomeExpr base]) = some events)
    (historyShape : ∀ pe, ∀ e ∈ state.peHistory pe, e.write = true → e.access.bank = .lm1) :
    (List.finRange 4096).any
      (fun pe => parsedPEHazardViolated (state.peHistory pe) events[pe.val]!) = false := by
  apply List.any_eq_false.mpr
  intro pe _
  obtain ⟨later, laterEq, _, laterRead⟩ :=
    welcome_peHazardEvents_entry base state.machine events eventsEq pe
  rw [laterEq]
  exact Bool.eq_false_iff.mp
    (welcome_no_peHazardViolated (state.peHistory pe) later (historyShape pe) laterRead)

/-- The block-hazard events of a Welcome line are empty, so the block-hazard
check of the core never rejects it. -/
theorem welcome_blockHazardViolated_false (base : Nat) (state : HazardAwareState) :
    parsedBlockHazardViolated state.blockHistory
      (HazardTrace.parsedLineBlockHazardEvents
        (NormalizedLine.pe [welcomeExpr base]).toParsed state.machine.hazardClock) = false := by
  rw [show (NormalizedLine.pe [welcomeExpr base]).toParsed =
      (InstructionLine.pe [welcomeExpr base]).toParsed from rfl]
  rw [welcome_blockEvents]
  simp [parsedBlockHazardViolated, HazardTrace.blockHazardConstraintsBetween]

/-! ## 4. The core transition of a Welcome line succeeds

All four `.unknown`/`.failure` sites of the hazard-aware core are discharged:
the issue check (`welcome_checkParsedTopLine`), the address-mode check
(`welcome_addressModesValid`), the PE hazard check
(`welcome_any_peHazardViolated_false`) and the block hazard check
(`welcome_blockHazardViolated_false`). -/

theorem executeHazardAwareNormalizedLineCore_pe_ok
    (expressions : List NormalizedExpr) (state : HazardAwareState) (next : State)
    (accepted : checkParsedTopLine (InstructionLine.pe expressions).toParsed = true)
    (valid : parsedNormalizedLinePEAddressModesValid (NormalizedLine.pe expressions) = true)
    (events : List (List TimedPEAccess))
    (eventsEq : parsedNormalizedLinePEHazardEvents? state.machine (NormalizedLine.pe expressions) = some events)
    (peFree : (List.finRange 4096).any
      (fun pe => parsedPEHazardViolated (state.peHistory pe) events[pe.val]!) = false)
    (blockFree : parsedBlockHazardViolated state.blockHistory
      (HazardTrace.parsedLineBlockHazardEvents
        (NormalizedLine.pe expressions).toParsed state.machine.hazardClock) = false)
    (executed : executeNormalizedLine (NormalizedLine.pe expressions) state.machine = .ok next) :
    executeHazardAwareNormalizedLineCore (NormalizedLine.pe expressions) state =
      .ok ⟨next,
        (fun pe => (state.peHistory pe ++ events[pe.val]!).filter
          (fun event => event.startWord + 4 ≥ next.hazardClock)),
        (state.blockHistory ++ HazardTrace.parsedLineBlockHazardEvents
          (NormalizedLine.pe expressions).toParsed state.machine.hazardClock).filter
          (fun event => event.startWord + 4 ≥ next.hazardClock),
        state.stalledPEIssue⟩ := by
  unfold executeHazardAwareNormalizedLineCore
  simp only [Id.run, NormalizedLine.toInstruction?, welcomeWhole_id_pure_eq,
    welcomeWhole_id_bind_eq, accepted, valid, Bool.not_true, eventsEq, peFree,
    blockFree, Bool.false_eq_true, ite_false, executed]

/-- One hazard-aware Welcome step succeeds from any state whose PE history only
writes LM1, whose block history is empty and whose machine satisfies the
Welcome invariant; it preserves all of these. -/
theorem welcomeWhole_step_ok (base : Nat) (state : HazardAwareState)
    (invariant : WelcomeStateInvariant state.machine)
    (historyShape : ∀ pe, ∀ e ∈ state.peHistory pe, e.write = true → e.access.bank = .lm1)
    (blockEmpty : state.blockHistory = [])
    (notStalled : state.stalledPEIssue = none) :
    ∃ next, wholeMachine.step (InstructionLine.pe [welcomeExpr base]) state = .ok next ∧
      WelcomeStateInvariant next.machine ∧
      (∀ pe, ∀ e ∈ next.peHistory pe, e.write = true → e.access.bank = .lm1) ∧
      next.blockHistory = [] ∧
      next.stalledPEIssue = none := by
  obtain ⟨nextMachine, executed, nextInvariant⟩ :=
    welcome_executeIntegerProducerInstructionLine_success base state.machine invariant
  have executedNormalized : executeNormalizedLine (NormalizedLine.pe [welcomeExpr base])
      state.machine = .ok nextMachine := executed
  have hazardSome := welcome_hazardEventsSome base state
  obtain ⟨events, eventsEq⟩ : ∃ events,
      parsedNormalizedLinePEHazardEvents? state.machine
        (NormalizedLine.pe [welcomeExpr base]) = some events := by
    cases h : parsedNormalizedLinePEHazardEvents? state.machine
        (NormalizedLine.pe [welcomeExpr base]) with
    | none =>
        rw [h] at hazardSome
        exact absurd hazardSome (by simp)
    | some events => exact ⟨events, rfl⟩
  have peFree := welcome_any_peHazardViolated_false base state events eventsEq historyShape
  have blockFree := welcome_blockHazardViolated_false base state
  have coreEq := executeHazardAwareNormalizedLineCore_pe_ok [welcomeExpr base] state nextMachine
    (welcome_checkParsedTopLine base) (welcome_addressModesValid base) events eventsEq
    peFree blockFree executedNormalized
  have wrapperEq : wholeMachine.step (InstructionLine.pe [welcomeExpr base]) state =
      .ok ⟨nextMachine,
        (fun pe => (state.peHistory pe ++ events[pe.val]!).filter
          (fun event => event.startWord + 4 ≥ nextMachine.hazardClock)),
        (state.blockHistory ++ HazardTrace.parsedLineBlockHazardEvents
          (NormalizedLine.pe [welcomeExpr base]).toParsed state.machine.hazardClock).filter
          (fun event => event.startWord + 4 ≥ nextMachine.hazardClock),
        state.stalledPEIssue⟩ := by
    rw [wholeMachine_step]
    rw [show (InstructionLine.pe [welcomeExpr base]).toNormalizedLine =
      NormalizedLine.pe [welcomeExpr base] from rfl]
    rw [executeHazardAwareNormalizedLine_pe_eq_core _ _ notStalled (welcome_noWait base)]
    exact coreEq
  refine ⟨_, wrapperEq, nextInvariant, ?_, ?_, ?_⟩
  · intro pe e member writeTrue
    obtain ⟨later, laterEq, laterWrite, _⟩ :=
      welcome_peHazardEvents_entry base state.machine events eventsEq pe
    rcases List.mem_filter.mp member with ⟨appendMem, _⟩
    rcases List.mem_append.mp appendMem with earlier | laterMem
    · exact historyShape pe e earlier writeTrue
    · rw [laterEq] at laterMem
      exact laterWrite e laterMem writeTrue
  · rw [blockEmpty, List.nil_append,
      show (NormalizedLine.pe [welcomeExpr base]).toParsed =
        (InstructionLine.pe [welcomeExpr base]).toParsed from rfl,
      welcome_blockEvents]
    simp
  · exact notStalled


/-! ## 5. The successful runs of `wholeMachine`

`welcomeWholeExecute` is the "all steps return `.ok`" program semantics of the
partial machine; `welcomeWholeMachine` is the total presentation
(`.ok ↦ some`, `.failure`/`.unknown` ↦ `none`) that `ProofsLean.Correct`,
`ProofsLean.Problem` and `ProofsLean.Optimal` are stated for. -/

/-- Program semantics of a partial machine: the run exists when every step
returns `.ok`. -/
noncomputable def welcomeWholeExecute : List InstructionLine → HazardAwareState →
    Option HazardAwareState
  | [], state => some state
  | line :: rest, state =>
      match wholeMachine.step line state with
      | .ok next => welcomeWholeExecute rest next
      | .failure => none
      | .unknown => none

/-- The total presentation of the hazard-aware whole machine:
`PartialMachine.seal` with the (globally false) completeness argument dropped.
`.failure` and `.unknown` both become `none`, so the machine is total but may
fail; `Optimal` is stated about this machine. -/
noncomputable def welcomeWholeMachine : ProofsLean.Machine where
  Line := InstructionLine
  State := HazardAwareState
  Input := ProofsLean.MNCore.PlusOne.Words
  step := fun line state =>
    match wholeMachine.step line state with
    | .ok next => some next
    | .failure => none
    | .unknown => none
  legal := fun _ => True
  lineCost := InstructionLine.cost
  positiveCost := InstructionLine.cost_positive

/-- The Welcome problem on the hazard-aware machine: the same admissible inputs
and the same postcondition as `welcomeSpec`, read through `state.machine`, and
the hazard-aware initial state (`HazardAwareState.initial` of the sealed initial
state: empty PE/block histories, no stalled issue). -/
noncomputable def welcomeWholeSpec : ProofsLean.Problem welcomeWholeMachine where
  admissible := fun input => welcomeSpec.admissible input
  initial := fun input => HazardAwareState.initial (welcomeSpec.initial input)
  post := fun input state => welcomeSpec.post input state.machine

theorem welcomeWholeSpec_initial (input : ProofsLean.MNCore.PlusOne.Words) :
    welcomeWholeSpec.initial input = HazardAwareState.initial (welcomeInitialState input) := rfl

theorem welcomeWholeSpec_post (input : ProofsLean.MNCore.PlusOne.Words)
    (state : HazardAwareState) :
    welcomeWholeSpec.post input state = welcomeSpec.post input state.machine := rfl

theorem welcomeWholeExecute_eq_execute (program : List InstructionLine)
    (state : HazardAwareState) :
    welcomeWholeExecute program state =
      ProofsLean.execute welcomeWholeMachine program state := by
  induction program generalizing state with
  | nil => rfl
  | cons line rest ih =>
      simp only [welcomeWholeExecute, ProofsLean.execute, welcomeWholeMachine]
      cases step : wholeMachine.step line state with
      | ok next => exact ih next
      | failure => rfl
      | unknown => rfl

/-- Inverting a successful total step: it came from a `.ok` partial step. -/
theorem welcomeWholeMachine_step_ok {line : InstructionLine} {state next : HazardAwareState}
    (success : welcomeWholeMachine.step line state = some next) :
    wholeMachine.step line state = .ok next := by
  simp only [welcomeWholeMachine] at success
  cases step : wholeMachine.step line state with
  | ok result =>
      rw [step] at success
      injection success with same
      rw [← same]
  | failure => rw [step] at success; cases success
  | unknown => rw [step] at success; cases success

/-! ## 6. Program-level projection

Every successful hazard-aware run of a wait-tag-free program is a successful
sealed run on `state.machine` with the same values.  The hypothesis `noWait` is
needed because the wait-tag branch of the wrapper may complete a pending MV
transfer *before* the value step, which is not a value step of the sealed
machine. -/

theorem welcomeWholeExecute_project (program : List InstructionLine)
    (noWait : ∀ line ∈ program, normalizedLineWaitTag? line.toNormalizedLine = none) :
    ∀ (state result : HazardAwareState), state.stalledPEIssue = none →
      welcomeWholeExecute program state = some result →
      ProofsLean.execute welcomeSealedMachine program state.machine = some result.machine := by
  induction program with
  | nil =>
      intro state result _ run
      simp only [welcomeWholeExecute, Option.some.injEq] at run
      subst run
      rfl
  | cons line rest ih =>
      intro state result notStalled run
      simp only [welcomeWholeExecute] at run
      cases step : wholeMachine.step line state with
      | failure => rw [step] at run; cases run
      | unknown => rw [step] at run; cases run
      | ok mid =>
          rw [step] at run
          have projected := executeHazardAwareNormalizedLine_ok_project line.toNormalizedLine
            state mid notStalled
            (noWait line (by simp))
            (show executeHazardAwareNormalizedLine line.toNormalizedLine state = .ok mid from step)
          have sealedStep : welcomeSealedMachine.step line state.machine = some mid.machine := by
            simp only [welcomeSealedMachine, projected.1]
          have tail := ih (fun restLine member => noWait restLine (by simp [member]))
            mid result projected.2 run
          simp only [ProofsLean.execute, sealedStep]
          exact tail

/-- The MV-completion fuel returns `none` on a state with no pending transfers
and an incomplete tag. -/
theorem completePendingMvTagFuel_none_of_pendingMv_nil (fuel : Nat) (state : State)
    (tag : Fin 256) (pendingNil : state.pendingMv = [])
    (incomplete : state.mvCompletedTags tag = false) :
    completePendingMvTagFuel fuel state tag = none := by
  induction fuel generalizing state with
  | zero => simp [completePendingMvTagFuel, incomplete]
  | succ fuel ih =>
      have stepNone : completePendingMvTag state tag = none := by
        simp [completePendingMvTag, incomplete, pendingNil, removePendingMvTag]
      simp [completePendingMvTagFuel, incomplete, stepNone]

theorem completePendingMvTagAll_welcomeInitialState
    (input : ProofsLean.MNCore.PlusOne.Words) (tag : Fin 256) :
    completePendingMvTagAll (welcomeInitialState input) tag = none :=
  completePendingMvTagFuel_none_of_pendingMv_nil _ _ _ rfl rfl

/-- A successful whole-machine step from the hazard-aware initial state is a
successful sealed step with the same machine payload.  No `noWait` hypothesis is
needed here: a wait tag would force `completePendingMvTagAll` on the
zero-pending initial machine, which returns `none`, i.e. `.unknown`. -/
theorem welcomeWhole_initial_step_project (line : InstructionLine)
    (input : ProofsLean.MNCore.PlusOne.Words) (next : HazardAwareState)
    (success : wholeMachine.step line (HazardAwareState.initial (welcomeInitialState input)) =
      .ok next) :
    welcomeSealedMachine.step line (welcomeInitialState input) = some next.machine := by
  cases wait : normalizedLineWaitTag? line.toNormalizedLine with
  | none =>
      have projected := executeHazardAwareNormalizedLine_ok_project line.toNormalizedLine
        (HazardAwareState.initial (welcomeInitialState input)) next rfl wait
        (show executeHazardAwareNormalizedLine line.toNormalizedLine
          (HazardAwareState.initial (welcomeInitialState input)) = .ok next from success)
      have executed : executeNormalizedLine line.toNormalizedLine (welcomeInitialState input) =
          .ok next.machine := projected.1
      simp only [welcomeSealedMachine, executed]
  | some tag =>
      exfalso
      have unknown : executeHazardAwareNormalizedLine line.toNormalizedLine
          (HazardAwareState.initial (welcomeInitialState input)) = .unknown := by
        simp only [executeHazardAwareNormalizedLine, Id.run, welcomeWhole_id_pure_eq,
          welcomeWhole_id_bind_eq, wait, HazardAwareState.initial, Option.isSome_none,
          Bool.false_eq_true, ite_false, completePendingMvTagAll_welcomeInitialState input tag]
      have success' : executeHazardAwareNormalizedLine line.toNormalizedLine
          (HazardAwareState.initial (welcomeInitialState input)) = .ok next := success
      rw [unknown] at success'
      cases success'


/-! ## 7. Correctness of the two Welcome lines on the hazard-aware machine -/

/-- Generic program semantics of a partial machine: the run exists when every
step returns `.ok`. -/
noncomputable def PartialExecute (m : ProofsLean.PartialMachine) :
    List m.Line → m.State → Option m.State
  | [], state => some state
  | line :: rest, state =>
      match m.step line state with
      | .ok next => PartialExecute m rest next
      | .failure => none
      | .unknown => none

theorem PartialExecute_wholeMachine (program : List InstructionLine)
    (state : HazardAwareState) :
    PartialExecute wholeMachine program state = welcomeWholeExecute program state := by
  induction program generalizing state with
  | nil => rfl
  | cons line rest ih =>
      cases step : wholeMachine.step line state with
      | ok next =>
          simp only [PartialExecute, welcomeWholeExecute, step]
          exact ih next
      | failure =>
          simp only [PartialExecute, welcomeWholeExecute, step]
          rfl
      | unknown =>
          simp only [PartialExecute, welcomeWholeExecute, step]
          rfl

/-- A problem statement for a partial machine: admissible inputs, the initial
hazard-aware state, and a postcondition on that state. -/
structure PartialProblem (m : ProofsLean.PartialMachine) where
  /-- The input type is explicit: `wholeMachine.Input` is `Unit` (the machine is
  stated for one fixed testcase), while the Welcome problem is quantified over
  the 16-word input. -/
  Input : Type
  admissible : Input → Prop
  initial : Input → m.State
  post : Input → m.State → Prop

/-- `ProofsLean.Correct` for a partial machine: the program is legal and every
admissible input has an all-`.ok` run satisfying the postcondition. -/
def PartialCorrect (m : ProofsLean.PartialMachine) (spec : PartialProblem m)
    (program : List m.Line) : Prop :=
  m.legal program ∧ ∀ input, spec.admissible input →
    ∃ result, PartialExecute m program (spec.initial input) = some result ∧
      spec.post input result

/-- The Welcome problem on `wholeMachine` itself, i.e. on `HazardAwareState`. -/
noncomputable def welcomeWholePartialSpec : PartialProblem wholeMachine where
  Input := ProofsLean.MNCore.PlusOne.Words
  admissible := fun input => welcomeSpec.admissible input
  initial := fun input => HazardAwareState.initial (welcomeSpec.initial input)
  post := fun input state => welcomeSpec.post input state.machine

theorem welcomeWholeAnswer_noWait :
    ∀ line ∈ welcomeAnswer, normalizedLineWaitTag? line.toNormalizedLine = none := by
  intro line member
  simp only [welcomeAnswer] at member
  rcases List.mem_cons.mp member with rfl | member
  · exact welcome_noWait 0
  · rcases List.mem_cons.mp member with rfl | member
    · exact welcome_noWait 8
    · cases member

/-- The two-line program runs successfully on the hazard-aware machine. -/
theorem welcomeWholeAnswer_execute (input : ProofsLean.MNCore.PlusOne.Words) :
    ∃ result, welcomeWholeExecute welcomeAnswer
      (HazardAwareState.initial (welcomeInitialState input)) = some result := by
  obtain ⟨s1, step1, invariant1, history1, block1, stalled1⟩ :=
    welcomeWhole_step_ok 0 (HazardAwareState.initial (welcomeInitialState input))
      (welcomeInitialState_invariant input)
      (by simp [HazardAwareState.initial]) rfl rfl
  obtain ⟨s2, step2, _invariant2, _history2, _block2, _stalled2⟩ :=
    welcomeWhole_step_ok 8 s1 invariant1 history1 block1 stalled1
  refine ⟨s2, ?_⟩
  simp only [welcomeAnswer, welcomeWholeExecute, step1, step2]

/-- **Correctness on the hazard-aware machine.**  The two accepted Welcome lines
compute `n_i = m_i + 1` for all 16 LM1 words from the hazard-aware initial state,
for every admissible input.  The values are those of the sealed machine: the
whole-machine run projects onto the sealed run (`welcomeWholeExecute_project`),
and the sealed machine is deterministic. -/
theorem welcomeWhole_partialCorrect :
    PartialCorrect wholeMachine welcomeWholePartialSpec welcomeAnswer := by
  refine ⟨trivial, ?_⟩
  intro input admissible
  obtain ⟨s2, run⟩ := welcomeWholeAnswer_execute input
  have noWait := welcomeWholeAnswer_noWait
  have projected := welcomeWholeExecute_project welcomeAnswer noWait
    (HazardAwareState.initial (welcomeInitialState input)) s2 rfl run
  have projected' : ProofsLean.execute welcomeSealedMachine welcomeAnswer
      (welcomeSpec.initial input) = some s2.machine := projected
  obtain ⟨result, sealedRun, sealedPost⟩ := welcomeAnswer_correct.2 input admissible
  have same : s2.machine = result := by
    rw [projected'] at sealedRun
    exact Option.some.inj sealedRun
  refine ⟨s2, ?_, ?_⟩
  · exact (PartialExecute_wholeMachine welcomeAnswer
      (welcomeWholePartialSpec.initial input)).trans run
  · show welcomeSpec.post input s2.machine
    rw [same]
    exact sealedPost

/-- **`Correct` for the total presentation of the whole machine.** -/
theorem welcomeWholeMachine_correct :
    ProofsLean.Correct welcomeWholeMachine welcomeWholeSpec welcomeAnswer := by
  refine ⟨trivial, ?_⟩
  intro input admissible
  obtain ⟨result, run, post⟩ := welcomeWhole_partialCorrect.2 input admissible
  have run' := (PartialExecute_wholeMachine welcomeAnswer
    (welcomeWholePartialSpec.initial input)).symm.trans run
  refine ⟨result, ?_, post⟩
  rw [show ProofsLean.execute welcomeWholeMachine welcomeAnswer (welcomeWholeSpec.initial input) =
      welcomeWholeExecute welcomeAnswer (HazardAwareState.initial (welcomeInitialState input)) from
    (welcomeWholeExecute_eq_execute welcomeAnswer (welcomeWholeSpec.initial input)).symm]
  exact run'

/-! ## 8. The lower bound

Only programs of score below two matter.  Such a program has at most one line.
The empty program cannot meet the postcondition at all, and a one-line program
that is correct for the hazard-aware machine projects (on the hazard-aware
initial state) to a one-line program that is correct for the sealed machine,
contradicting the unconditional sealed lower bound. -/

theorem welcomeWhole_score_eq_sealed (program : List InstructionLine) :
    ProofsLean.score welcomeWholeMachine program =
      ProofsLean.score welcomeSealedMachine program := by
  induction program with
  | nil => rfl
  | cons line rest ih =>
      simp only [ProofsLean.score]
      rw [ih]
      rfl

/-- The empty program cannot satisfy the Welcome postcondition: the initial LM1
is zero everywhere, while the specification demands `m_i + 1`. -/
theorem welcomeWhole_empty_not_correct :
    ¬ ProofsLean.Correct welcomeWholeMachine welcomeWholeSpec [] := by
  intro correct
  have admissible : welcomeWholeSpec.admissible (fun _ : Fin 16 => (0 : BitVec 32)) := by
    show welcomeSpec.admissible (fun _ : Fin 16 => (0 : BitVec 32))
    intro word
    simp
  obtain ⟨result, run, post⟩ := correct.2 (fun _ : Fin 16 => (0 : BitVec 32)) admissible
  obtain rfl : welcomeWholeSpec.initial (fun _ : Fin 16 => (0 : BitVec 32)) = result := by
    simpa [ProofsLean.execute] using run
  have h0 := post ⟨0, by decide⟩
  simp [welcomeWholeSpec, welcomeSpec, HazardAwareState.initial, welcomeInitialState,
    welcomeInitialPERegisters, zeroInitialPERegisterFiles] at h0

/-- A one-line program correct for the hazard-aware machine is correct for the
sealed machine: project its single step from the hazard-aware initial state. -/
theorem welcomeWholeLine_sealedCorrect (line : InstructionLine)
    (correct : ProofsLean.Correct welcomeWholeMachine welcomeWholeSpec [line]) :
    ProofsLean.Correct welcomeSealedMachine welcomeSpec [line] := by
  refine ⟨trivial, ?_⟩
  intro input admissible
  obtain ⟨result, run, post⟩ := correct.2 input admissible
  have stepOk : welcomeWholeMachine.step line (welcomeWholeSpec.initial input) = some result := by
    simpa [ProofsLean.execute] using run
  have stepOk' : welcomeWholeMachine.step line
      (HazardAwareState.initial (welcomeInitialState input)) = some result := stepOk
  have partialOk : wholeMachine.step line
      (HazardAwareState.initial (welcomeInitialState input)) = .ok result :=
    welcomeWholeMachine_step_ok stepOk'
  have sealedStep := welcomeWhole_initial_step_project line input result partialOk
  have sealedStep' : welcomeSealedMachine.step line (welcomeSpec.initial input) =
      some result.machine := sealedStep
  refine ⟨result.machine, ?_, ?_⟩
  · have execEq : ProofsLean.execute welcomeSealedMachine [line] (welcomeSpec.initial input) =
        welcomeSealedMachine.step line (welcomeSpec.initial input) := by
      simp only [ProofsLean.execute]
      cases welcomeSealedMachine.step line (welcomeSpec.initial input) <;> rfl
    rw [execEq]
    exact sealedStep'
  · simpa [welcomeWholeSpec, welcomeSpec] using post

/-- **`LowerBound welcomeWholeMachine welcomeWholeSpec 2`, unconditionally.** -/
theorem welcomeWholeMachine_lowerBound_two :
    ProofsLean.LowerBound welcomeWholeMachine welcomeWholeSpec 2 := by
  intro program correct
  by_contra notBound
  have short : ProofsLean.score welcomeWholeMachine program < 2 := by omega
  have lengthLe := ProofsLean.length_le_score welcomeWholeMachine program
  cases program with
  | nil => exact welcomeWhole_empty_not_correct correct
  | cons line rest =>
      cases rest with
      | nil =>
          have sealedCorrect := welcomeWholeLine_sealedCorrect line correct
          have lower := welcomeLowerBound_two [line] sealedCorrect
          have shortCost : InstructionLine.cost line < 2 := by
            simpa [ProofsLean.score, welcomeWholeMachine] using short
          have lowerCost : 2 ≤ InstructionLine.cost line := by
            simpa [ProofsLean.score, welcomeSealedMachine] using lower
          omega
      | cons second tail =>
          simp only [List.length_cons] at lengthLe
          omega

/-! ## 9. Optimality -/

/-- **`Optimal welcomeWholeMachine welcomeWholeSpec welcomeAnswer`,
unconditionally.**  Correctness is `welcomeWholeMachine_correct`; the lower
bound at score two is `welcomeWholeMachine_lowerBound_two`, using
`welcomeAnswer_score` for the sealed score. -/
theorem welcomeWholeMachine_optimal :
    ProofsLean.Optimal welcomeWholeMachine welcomeWholeSpec welcomeAnswer := by
  refine ⟨welcomeWholeMachine_correct, ?_⟩
  have scoreTwo : ProofsLean.score welcomeWholeMachine welcomeAnswer = 2 := by
    simp [welcomeAnswer, ProofsLean.score, welcomeWholeMachine, InstructionLine.cost]
  rw [scoreTwo]
  exact welcomeWholeMachine_lowerBound_two


/-- **The whole-machine run and the sealed run produce the same values.**  For
every admissible input both runs exist, and the hazard-aware final machine is
the sealed final state.  Consequently the LM1 words of the postcondition are
literally the same. -/
theorem welcomeWholeAnswer_values (input : ProofsLean.MNCore.PlusOne.Words)
    (admissible : welcomeSpec.admissible input) :
    ∃ state result,
      welcomeWholeExecute welcomeAnswer
        (HazardAwareState.initial (welcomeInitialState input)) = some state ∧
      ProofsLean.execute welcomeSealedMachine welcomeAnswer (welcomeInitialState input) =
        some result ∧
      state.machine = result := by
  obtain ⟨state, run⟩ := welcomeWholeAnswer_execute input
  have projected := welcomeWholeExecute_project welcomeAnswer welcomeWholeAnswer_noWait
    (HazardAwareState.initial (welcomeInitialState input)) state rfl run
  obtain ⟨result, sealedRun, _⟩ := welcomeAnswer_correct.2 input admissible
  have projected' : ProofsLean.execute welcomeSealedMachine welcomeAnswer
      (welcomeSpec.initial input) = some state.machine := projected
  have same : state.machine = result := by
    rw [projected'] at sealedRun
    exact Option.some.inj sealedRun
  exact ⟨state, result, run, sealedRun, same⟩

/-! ## 10. Why the statement is about the total presentation

`ProofsLean.Optimal` is typed over `Machine`, and `wholeMachine` cannot be
turned into one by `PartialMachine.seal`, because `wholeMachine.Complete` is
false: a positive `nop` carrying an MV wait tag returns `.unknown` from the
hazard-aware initial state (the pending-MV queue is empty, so the tagged
completion cannot run). -/

theorem welcomeWhole_nop_wait_unknown (tag : Fin 256)
    (input : ProofsLean.MNCore.PlusOne.Words) :
    wholeMachine.step (.nop ⟨1, by decide⟩ (some tag))
      (HazardAwareState.initial (welcomeInitialState input)) = .unknown := by
  have unknown : executeHazardAwareNormalizedLine (NormalizedLine.nop 1 (some tag))
      (HazardAwareState.initial (welcomeInitialState input)) = .unknown := by
    simp only [executeHazardAwareNormalizedLine, normalizedLineWaitTag?, Id.run,
      welcomeWhole_id_pure_eq, welcomeWhole_id_bind_eq, HazardAwareState.initial,
      Option.isSome_none, Bool.false_eq_true, ite_false,
      completePendingMvTagAll_welcomeInitialState input tag]
  exact unknown

/-- **`wholeMachine` is not complete**, so `PartialMachine.seal` cannot be
applied to it; `welcomeWholeMachine` is its total presentation instead. -/
theorem wholeMachine_not_complete : ¬ wholeMachine.Complete :=
  wholeMachine_not_complete_of_unknown (.nop ⟨1, by decide⟩ (some ⟨0, by decide⟩))
    (HazardAwareState.initial (welcomeInitialState (fun _ : Fin 16 => 0)))
    (welcomeWhole_nop_wait_unknown ⟨0, by decide⟩ (fun _ : Fin 16 => 0))

/-! ## 11. Optimality stated about `wholeMachine` itself

`ProofsLean.Optimal` is typed over `Machine`, so the literal
`Optimal wholeMachine ...` cannot be written.  This section supplies the exact
`PartialMachine` analogue — same shape, same score, same statement — and proves
it for `wholeMachine`, so the optimality claim is available for the
hazard-aware transition itself and not only for its total presentation. -/

/-- Scored cost of a `PartialMachine` program (the analogue of
`ProofsLean.score`). -/
def PartialScore (m : ProofsLean.PartialMachine) : List m.Line → Nat
  | [] => 0
  | line :: rest => m.lineCost line + PartialScore m rest

/-- `ProofsLean.LowerBound` for a partial machine. -/
def PartialLowerBound (m : ProofsLean.PartialMachine) (spec : PartialProblem m)
    (bound : Nat) : Prop :=
  ∀ program : List m.Line, PartialCorrect m spec program → bound ≤ PartialScore m program

/-- `ProofsLean.Optimal` for a partial machine. -/
def PartialOptimal (m : ProofsLean.PartialMachine) (spec : PartialProblem m)
    (program : List m.Line) : Prop :=
  PartialCorrect m spec program ∧ PartialLowerBound m spec (PartialScore m program)

theorem length_le_PartialScore (m : ProofsLean.PartialMachine) (program : List m.Line) :
    program.length ≤ PartialScore m program := by
  induction program with
  | nil => simp [PartialScore]
  | cons line rest ih =>
      simp only [List.length_cons, PartialScore]
      have := m.positiveCost line
      omega

/-- Inverting a successful one-line partial run. -/
theorem PartialExecute_singleton_ok {m : ProofsLean.PartialMachine} {line : m.Line}
    {state result : m.State} (run : PartialExecute m [line] state = some result) :
    m.step line state = .ok result := by
  cases step : m.step line state with
  | ok next =>
      simp only [PartialExecute, step] at run
      injection run with same
      rw [← same]
  | failure => simp only [PartialExecute, step] at run; cases run
  | unknown => simp only [PartialExecute, step] at run; cases run

/-- **`LowerBound` for `wholeMachine` itself.** -/
theorem welcomeWhole_partialLowerBound :
    PartialLowerBound wholeMachine welcomeWholePartialSpec 2 := by
  intro program correct
  by_contra notBound
  have short : PartialScore wholeMachine program < 2 := by omega
  have lengthLe := length_le_PartialScore wholeMachine program
  cases program with
  | nil =>
      have admissible : welcomeWholePartialSpec.admissible
          (fun _ : Fin 16 => (0 : BitVec 32)) := by
        show welcomeSpec.admissible (fun _ : Fin 16 => (0 : BitVec 32))
        intro word
        simp
      obtain ⟨result, run, post⟩ := correct.2 _ admissible
      simp only [PartialExecute, Option.some.injEq] at run
      rw [← run] at post
      have h0 := post ⟨0, by decide⟩
      simp [welcomeWholePartialSpec, welcomeSpec, HazardAwareState.initial,
        welcomeInitialState, welcomeInitialPERegisters, zeroInitialPERegisterFiles] at h0
  | cons line rest =>
      cases rest with
      | nil =>
          have sealedCorrect : ProofsLean.Correct welcomeSealedMachine welcomeSpec [line] := by
            refine ⟨trivial, ?_⟩
            intro input admissible
            obtain ⟨result, run, post⟩ := correct.2 input admissible
            have stepOk : wholeMachine.step line
                (HazardAwareState.initial (welcomeInitialState input)) = .ok result :=
              PartialExecute_singleton_ok run
            have sealedStep := welcomeWhole_initial_step_project line input result stepOk
            have sealedStep' : welcomeSealedMachine.step line (welcomeSpec.initial input) =
                some result.machine := sealedStep
            refine ⟨result.machine, ?_, ?_⟩
            · have execEq : ProofsLean.execute welcomeSealedMachine [line]
                  (welcomeSpec.initial input) =
                  welcomeSealedMachine.step line (welcomeSpec.initial input) := by
                simp only [ProofsLean.execute]
                cases welcomeSealedMachine.step line (welcomeSpec.initial input) <;> rfl
              rw [execEq]
              exact sealedStep'
            · simpa [welcomeWholePartialSpec, welcomeSpec] using post
          have lower := welcomeLowerBound_two [line] sealedCorrect
          have shortCost : InstructionLine.cost line < 2 := by
            have h : PartialScore wholeMachine [line] = wholeMachine.lineCost line := by
              simp [PartialScore]
            rw [h] at short
            exact short
          have lowerCost : 2 ≤ InstructionLine.cost line := by
            have h : ProofsLean.score welcomeSealedMachine [line] =
                welcomeSealedMachine.lineCost line := by
              simp [ProofsLean.score]
            rw [h] at lower
            exact lower
          omega
      | cons second tail =>
          simp only [List.length_cons] at lengthLe
          omega

theorem welcomeWholeAnswer_partialScore :
    PartialScore wholeMachine welcomeAnswer = 2 := by
  simp [welcomeAnswer, PartialScore, wholeMachine, InstructionLine.cost]

/-- **`Optimal` for `wholeMachine` itself, unconditionally** — the
`PartialMachine` analogue of `ProofsLean.Optimal wholeMachine ...`. -/
theorem welcomeWhole_partialOptimal :
    PartialOptimal wholeMachine welcomeWholePartialSpec welcomeAnswer := by
  refine ⟨welcomeWhole_partialCorrect, ?_⟩
  rw [welcomeWholeAnswer_partialScore]
  exact welcomeWhole_partialLowerBound

end ProofsLean.MNCore
