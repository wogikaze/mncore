import ProofsLean.WholeMachineStep

/-! A whole-machine `PartialMachine` with a **broad legality domain**.

The worklist policy (`docs/formal-semantics-worklist.md`): `legal` must admit
every normalized executable line, and operational violations (parallel-issue
conflicts, PE/block hazards, invalid forwarding reads) must show up as
`.failure` from `step` instead of shrinking `legal`. `partialMachine` in
`ProgramLegality.lean` follows that policy but has `State := Unit` and a
placeholder `step`; this module keeps the same broad domain while stepping on
the real `HazardAwareState`.

The two machines are deliberately separate:

* `wholeMachine` — broad `legal`, real state, used for correctness and
  footprint reasoning.
* `hazardAwareInstructionMachine` (in `WholeMachineStep.lean`) — the same
  transition but with the issue checker baked into `legal`; kept as the old
  projection, not used for enumeration.

What this module does **not** claim: that `step` agrees with the Rust
simulator or with hardware; that every accepted line returns `.ok` (it may
still return `.unknown` where semantics are unconnected); or that the
source-to-`InstructionLine` normalization is complete.
-/

namespace ProofsLean.MNCore

open Issue

/-- Broad-domain whole-machine step.

`step` is exactly the hazard-aware normalized-line transition, so mask
directives and PE/MV lines follow the same semantics as program execution.
`legal` admits every list of instruction lines, per the worklist policy. -/
noncomputable def wholeMachine : ProofsLean.PartialMachine where
  Line := InstructionLine
  State := HazardAwareState
  Input := Unit
  step := fun line state => executeHazardAwareNormalizedLine line.toNormalizedLine state
  legal := fun _ => True
  lineCost := InstructionLine.cost
  positiveCost := InstructionLine.cost_positive

theorem wholeMachine_legal_all (program : wholeMachine.Program) :
    wholeMachine.legal program := trivial

/-- The step is definitionally the hazard-aware transition, so every existing
theorem about `executeHazardAwareNormalizedLine` transfers without rewriting. -/
theorem wholeMachine_step (line : InstructionLine) (state : HazardAwareState) :
    wholeMachine.step line state
      = executeHazardAwareNormalizedLine line.toNormalizedLine state := rfl

/-- A step on a stalled PE issue is a known failure, not an unknown. -/
theorem wholeMachine_rejects_issue_while_stalled
    (line blocked : NormalizedLine) (state : HazardAwareState)
    (stalled : state.stalledPEIssue = some blocked) (instruction : InstructionLine)
    (normalized : instruction.toNormalizedLine = line) :
    wholeMachine.step instruction state = .failure := by
  subst normalized
  simp [wholeMachine, executeHazardAwareNormalizedLine, stalled]

/-- Every successful whole-machine step comes from the normalized-line
executor, so footprint reasoning can be done once on that executor. -/
theorem wholeMachine_step_ok (line : InstructionLine) (state next : HazardAwareState)
    (success : wholeMachine.step line state = .ok next) :
    executeHazardAwareNormalizedLine line.toNormalizedLine state = .ok next := by
  simpa [wholeMachine] using success

/-- The broad machine is still incomplete: accepted rows whose value transition
is not connected return `.unknown`. This is stated so that `seal` is not
applied accidentally; it must be discharged per line set, not globally. -/
theorem wholeMachine_not_complete_of_unknown (line : InstructionLine)
    (state : HazardAwareState)
    (unknown : executeHazardAwareNormalizedLine line.toNormalizedLine state = .unknown) :
    ¬ wholeMachine.Complete := by
  intro complete
  exact complete line state (by simpa [wholeMachine] using unknown)

/-- The broad domain of `wholeMachine` and of the placeholder `partialMachine`
coincide: both admit every normalized executable line. `wholeMachine` differs
only in carrying the real state and the real transition, so results about the
legality domain transfer without restating them per machine. -/
theorem wholeMachine_legal_iff_partialMachine_legal (program : List InstructionLine) :
    wholeMachine.legal program ↔ partialMachine.legal program := by
  simp [wholeMachine, partialMachine]

/-- Every executable row emitted by successful source normalization is admitted
by the whole machine, matching `normalizedExecutableLine_legal`. -/
theorem wholeMachine_normalizedExecutableLine_legal
    (source : ParsedLine) (normalized : List NormalizedLine)
    (_success : source.normalizeForSubmission? = some normalized)
    (candidate : NormalizedLine) (_member : candidate ∈ normalized)
    (line : InstructionLine) (_emitted : candidate.toInstruction? = some line) :
    wholeMachine.legal [line] := by
  exact wholeMachine_legal_all [line]

/-- A positive `nop` line at the whole-machine level. This is the first
`wholeMachine` step equation: it restates the existing hazard-aware theorem so
that downstream work can refer to `wholeMachine.step` instead of the raw
executor. -/
theorem wholeMachine_nop_step (state : HazardAwareState) (count : Nat)
    (notStalled : state.stalledPEIssue = none) :
    wholeMachine.step (.nop ⟨count + 1, Nat.succ_pos count⟩ none) state =
      .ok { state with
        machine := { state.machine with
          hazardClock := state.machine.hazardClock + (count + 1) }
        peHistory := fun pe => (state.peHistory pe).filter fun event =>
          event.startWord + 4 ≥ state.machine.hazardClock + (count + 1)
        blockHistory := state.blockHistory.filter fun event =>
          event.startWord + 4 ≥ state.machine.hazardClock + (count + 1) } := by
  simpa [wholeMachine, Issue.InstructionLine.toNormalizedLine] using
    executeHazardAwareNormalizedLine_positive_nop state count notStalled

/-- Core-level: a PE line rejected by the issue checker is a known failure. -/
theorem executeHazardAwareNormalizedLineCore_pe_issue_failure
    (exprs : List NormalizedExpr) (state : HazardAwareState)
    (rejected : checkParsedTopLine (Issue.InstructionLine.pe exprs).toParsed = false) :
    executeHazardAwareNormalizedLineCore (.pe exprs) state = .failure := by
  simp [executeHazardAwareNormalizedLineCore, NormalizedLine.toInstruction?, rejected]

/-- With no stalled issue and no wait tag among the expressions, the
hazard-aware wrapper for a PE line is the core transition.

The `noWait` hypothesis is necessary: `normalizedLineWaitTag?` scans the
expressions for a wait tag, so without it the statement is false. -/
theorem executeHazardAwareNormalizedLine_pe_eq_core (exprs : List NormalizedExpr)
    (state : HazardAwareState) (notStalled : state.stalledPEIssue = none)
    (noWait : (exprs.findSome? fun expression => parsedExprWaitTag? expression.toParsed) = none) :
    executeHazardAwareNormalizedLine (.pe exprs) state
      = executeHazardAwareNormalizedLineCore (.pe exprs) state := by
  simp [executeHazardAwareNormalizedLine, normalizedLineWaitTag?, notStalled, noWait]

/-- Issue rejection of a PE line is a `.failure` of `wholeMachine.step`. -/
theorem wholeMachine_pe_issue_failure (exprs : List NormalizedExpr)
    (state : HazardAwareState) (notStalled : state.stalledPEIssue = none)
    (noWait : (exprs.findSome? fun expression => parsedExprWaitTag? expression.toParsed) = none)
    (rejected : checkParsedTopLine (Issue.InstructionLine.pe exprs).toParsed = false) :
    wholeMachine.step (.pe exprs) state = .failure := by
  show executeHazardAwareNormalizedLine (.pe exprs) state = .failure
  rw [executeHazardAwareNormalizedLine_pe_eq_core exprs state notStalled noWait]
  exact executeHazardAwareNormalizedLineCore_pe_issue_failure exprs state rejected

/-- First frame-style lemma: a positive `nop` changes only the hazard clock and
the two histories, leaving PE registers, block memory, mask directives and
forwarding untouched. This is the shape Phase 2 generalises to every line. -/
theorem wholeMachine_nop_frame (state : HazardAwareState) (count : Nat)
    (notStalled : state.stalledPEIssue = none) :
    ∃ next, wholeMachine.step (.nop ⟨count + 1, Nat.succ_pos count⟩ none) state = .ok next ∧
      next.machine.peRegisters = state.machine.peRegisters ∧
      next.machine.l1bm = state.machine.l1bm ∧
      next.machine.blockMemory = state.machine.blockMemory ∧
      next.machine.maskDirective = state.machine.maskDirective ∧
      next.machine.forwarding = state.machine.forwarding := by
  refine ⟨_, wholeMachine_nop_step state count notStalled, rfl, rfl, rfl, rfl, rfl⟩

/-- The wrapper reduction for MV lines: `normalizedLineWaitTag?` is `none` for
`.mv`, so only the stalled-issue check stands between the wrapper and the core. -/
theorem executeHazardAwareNormalizedLine_mv_eq_core (transfer : NormalizedMv)
    (state : HazardAwareState) (notStalled : state.stalledPEIssue = none) :
    executeHazardAwareNormalizedLine (.mv transfer) state
      = executeHazardAwareNormalizedLineCore (.mv transfer) state := by
  simp [executeHazardAwareNormalizedLine, normalizedLineWaitTag?, notStalled]

/-- The wrapper reduction for a `nop` without a wait tag. -/
theorem executeHazardAwareNormalizedLine_nop_eq_core (count : Nat)
    (state : HazardAwareState) (notStalled : state.stalledPEIssue = none) :
    executeHazardAwareNormalizedLine (.nop count none) state
      = executeHazardAwareNormalizedLineCore (.nop count none) state := by
  simp [executeHazardAwareNormalizedLine, normalizedLineWaitTag?, notStalled]

/-- First version of the Phase 2 frame predicate: two machine states agree on
every modelled resource except the hazard clock. Phase 2 must prove, for every
line, that the footprint of the line covers every field that may change; this
predicate is the "everything else is unchanged" side of that statement. -/
def SameResources (a b : State) : Prop :=
  a.peRegisters = b.peRegisters ∧
  a.l1bm = b.l1bm ∧
  a.l1bmTurnaround = b.l1bmTurnaround ∧
  a.l1bmTurnaroundValid = b.l1bmTurnaroundValid ∧
  a.blockMemory = b.blockMemory ∧
  a.dar = b.dar ∧
  a.darBuffer = b.darBuffer ∧
  a.darBufferReadAddress = b.darBufferReadAddress ∧
  a.darWriteAddress = b.darWriteAddress ∧
  a.mvCompletedTags = b.mvCompletedTags ∧
  a.pendingMv = b.pendingMv ∧
  a.matrixRegisters = b.matrixRegisters ∧
  a.forwarding = b.forwarding ∧
  a.forwardingValid = b.forwardingValid ∧
  a.maskDirective = b.maskDirective ∧
  a.peContext = b.peContext

/-- A `nop` preserves every resource; only the clock and the histories move. -/
theorem wholeMachine_nop_sameResources (state : HazardAwareState) (count : Nat)
    (notStalled : state.stalledPEIssue = none) :
    ∃ next, wholeMachine.step (.nop ⟨count + 1, Nat.succ_pos count⟩ none) state = .ok next ∧
      SameResources state.machine next.machine := by
  refine ⟨_, wholeMachine_nop_step state count notStalled, ?_⟩
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Core-level: an MV line rejected by the issue checker is a known failure. -/
theorem executeHazardAwareNormalizedLineCore_mv_issue_failure
    (transfer : NormalizedMv) (state : HazardAwareState)
    (rejected : checkParsedTopLine (Issue.InstructionLine.mv transfer).toParsed = false) :
    executeHazardAwareNormalizedLineCore (.mv transfer) state = .failure := by
  simp [executeHazardAwareNormalizedLineCore, NormalizedLine.toInstruction?, rejected]

/-- Whole-machine: issue rejection of an MV line is a failure. -/
theorem wholeMachine_mv_issue_failure (transfer : NormalizedMv)
    (state : HazardAwareState) (notStalled : state.stalledPEIssue = none)
    (rejected : checkParsedTopLine (Issue.InstructionLine.mv transfer).toParsed = false) :
    wholeMachine.step (.mv transfer) state = .failure := by
  show executeHazardAwareNormalizedLine (.mv transfer) state = .failure
  rw [executeHazardAwareNormalizedLine_mv_eq_core transfer state notStalled]
  exact executeHazardAwareNormalizedLineCore_mv_issue_failure transfer state rejected

theorem SameResources.refl (a : State) : SameResources a a := by
  simp [SameResources]

theorem SameResources.symm {a b : State} (h : SameResources a b) : SameResources b a := by
  unfold SameResources at *
  aesop

theorem SameResources.trans {a b c : State} (hab : SameResources a b)
    (hbc : SameResources b c) : SameResources a c := by
  unfold SameResources at *
  aesop

/-- A `nop` MV transfer advances the clock and changes nothing else. Stated on
`State`, i.e. below the hazard-aware history layer, where the Phase 2 frame is
proved first. -/
theorem executeNormalizedLine_mvnop (transfer : NormalizedMv) (state : State)
    (nop : transfer.kind = .nop)
    (accepted : checkParsedTopLine (Issue.InstructionLine.mv transfer).toParsed = true) :
    executeNormalizedLine (.mv transfer) state
      = .ok { state with hazardClock := state.hazardClock + 1 } := by
  simp [executeNormalizedLine, NormalizedLine.toInstruction?,
    executeIntegerProducerInstructionLine, accepted, nop]

theorem SameResources.peRegisters_eq {a b : State} (h : SameResources a b) :
    a.peRegisters = b.peRegisters := h.1

theorem SameResources.l1bm_eq {a b : State} (h : SameResources a b) :
    a.l1bm = b.l1bm := h.2.1

theorem SameResources.blockMemory_eq {a b : State} (h : SameResources a b) :
    a.blockMemory = b.blockMemory := h.2.2.2.2.1

theorem SameResources.forwarding_eq {a b : State} (h : SameResources a b) :
    a.forwarding = b.forwarding := h.2.2.2.2.2.2.2.2.2.2.2.2.1

end ProofsLean.MNCore
