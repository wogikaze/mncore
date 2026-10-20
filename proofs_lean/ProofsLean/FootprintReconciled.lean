import ProofsLean.FrameStep

/-! Phase 2 footprint reconciliation.

`Footprint.lean` originally claimed two omissions that the executor does not
honour (recorded by `FrameStep.lean`):

* a plain integer-ALU `.pe` line assigns `l1bmTurnaroundValid := false` while
  its footprint did not name `.l1bmTurnaround`;
* a `.noforward` line rewrites `forwarding` while its footprint named only
  `.issueControl`.

Both are now reconciled at the source:

* `parsedOpUnitWrites .noforward = [.issueControl, .forwarding]`;
* `peLineFootprint` seeds every `.pe` line with `.forwarding` (every successful
  PE line runs the per-PE forwarding update, including empty/wait-only lines)
  and with `.l1bmTurnaround` when the line has no `noforward` expression.

This module records three things.

1. The positive replacements for the old counterexample statements: the
   reconciled footprint names `.l1bmTurnaround` for plain integer-ALU lines and
   `.forwarding` for `noforward` lines (the old omission statements are
   explicitly negated below, so they can no longer be restated).
2. A field-level frame for plain integer-ALU `.pe` lines: a successful step
   leaves every `State` field outside the footprint's write set unchanged. The
   footprint names `.alu`/operand writes (PE registers), `.forwarding`
   (payload + validity), `.bar` (PE context, when a BAR destination exists),
   `.hazardClock`, and `.l1bmTurnaround`; the theorem below proves that the
   remaining fields are unchanged (and additionally that the turnaround
   *payload* is unchanged, which is stronger than the resource name).
3. The same field-level frame for `.nop` and `.mv` lines.

The executor evidence is `executeIntegerProducerInstructionLine` in
`ProofsLean/WholeMachineStep.lean` and `viz/core/src/machine.rs`
(`if !noforward { ... self.blocks.lbi ... }`,
`if !noforward { ... fwd_error / forwarding payload ... }`).
-/
namespace ProofsLean.MNCore

open Issue
open PEMemory

/-! ## The two reconciled footprint statements -/

/-- Every `.pe` line names the forwarding resource at the line level, so the
line-level `noforward` counterexample is gone: the statement
`UnitResource.forwarding ∉ ...unitWrites` is now false for every expression
list (including the empty list, where the old omission proof happened to hold
because the per-expression fold added nothing). -/
theorem normalizedLineFootprint_pe_forwarding_not_omitted
    (normalizedExpressions : List NormalizedExpr) :
    ¬ (UnitResource.forwarding ∉
      (normalizedLineFootprint (.pe normalizedExpressions)).unitWrites) := by
  intro omitted
  exact omitted (peLineFootprint_forwarding_in_writes normalizedExpressions)

/-- The reconciled per-expression statement for `noforward`: the expression's
own footprint names `.forwarding`. This is the positive replacement of
`parsedExprFootprint_noforward_omits_forwarding`. -/
theorem parsedExprFootprint_noforward_forwarding_not_omitted (expression : ParsedExpr)
    (noforward : expression.op = .noforward) :
    ¬ (UnitResource.forwarding ∉ (parsedExprFootprint expression).unitWrites) := by
  intro omitted
  exact omitted (parsedExprFootprint_noforward_names_forwarding expression noforward)

/-- The reconciled line-level statement for `noforward` lines: the footprint
names `.forwarding`. This is the positive replacement of
`normalizedLineFootprint_pe_noforward_omits_forwarding`; the `all` hypothesis is
the one from the old statement. -/
theorem normalizedLineFootprint_pe_noforward_forwarding_not_omitted
    (normalizedExpressions : List NormalizedExpr)
    (all : ∀ expression ∈ normalizedExpressions.map NormalizedExpr.toParsed,
      expression.op = .noforward) :
    ¬ (UnitResource.forwarding ∉
      (normalizedLineFootprint (.pe normalizedExpressions)).unitWrites) := by
  intro omitted
  exact omitted (normalizedLineFootprint_pe_noforward_names_forwarding
    normalizedExpressions all)

/-- The reconciled statement for plain integer-ALU lines: the footprint names
`.l1bmTurnaround`. This is the positive replacement of
`normalizedLineFootprint_pe_plainIntegerALU_omits_l1bmTurnaround`. -/
theorem normalizedLineFootprint_pe_plainIntegerALU_turnaround_not_omitted
    (normalizedExpressions : List NormalizedExpr)
    (plain : (normalizedExpressions.map NormalizedExpr.toParsed).all
      parsedExprIsPlainIntegerALU = true) :
    ¬ (UnitResource.l1bmTurnaround ∉
      (normalizedLineFootprint (.pe normalizedExpressions)).unitWrites) := by
  intro omitted
  exact omitted (normalizedLineFootprint_pe_plainIntegerALU_names_l1bmTurnaround
    normalizedExpressions plain)

/-! ## Frames below the line level -/

/-- Every `State` field that the per-PE walk cannot touch. The walk's only
updates are `peRegisters`, `forwarding`, `forwardingValid` and `peContext`
(`executeIntegerProducerLineAtPECore`), so this predicate is what a line-level
frame can inherit from the walk. `hazardClock` is included because the clock is
advanced once per line, after the walk. -/
def SameOtherFields (a b : State) : Prop :=
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
  a.maskDirective = b.maskDirective ∧
  a.hazardClock = b.hazardClock

theorem SameOtherFields.refl (a : State) : SameOtherFields a a := by
  simp [SameOtherFields]

theorem SameOtherFields.trans {a b c : State} (hab : SameOtherFields a b)
    (hbc : SameOtherFields b c) : SameOtherFields a c := by
  unfold SameOtherFields at *
  aesop

/-- The per-PE core only writes PE registers, forwarding, forwarding validity
and the PE context. This holds for an arbitrary expression list. -/
theorem executeIntegerProducerLineAtPECore_sameOther (expressions : List ParsedExpr)
    (state next : State) (pe : PEId)
    (executed : executeIntegerProducerLineAtPECore expressions state pe = .ok next) :
    SameOtherFields state next := by
  rw [executeIntegerProducerLineAtPECore.eq_1] at executed
  split at executed
  · cases executed
  · cases executed
  · split at executed
    · cases executed
    · cases executed
    · simp only [updateSupportedPELineForwarding] at executed
      split at executed
      · cases executed
      · cases executed
      · simp only [StepResult.ok.injEq] at executed
        subst executed
        exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem executeIntegerProducerLineAtPE_sameOther (expressions : List ParsedExpr)
    (state next : State) (pe : PEId)
    (executed : executeIntegerProducerLineAtPE expressions state pe = .ok next) :
    SameOtherFields state next := by
  unfold executeIntegerProducerLineAtPE at executed
  split at executed
  · cases executed
  · exact executeIntegerProducerLineAtPECore_sameOther expressions state next pe executed

theorem executeIntegerProducerLineAtPEs_sameOther (expressions : List ParsedExpr)
    (pes : List PEId) (state next : State)
    (executed : executeIntegerProducerLineAtPEs expressions pes state = .ok next) :
    SameOtherFields state next := by
  induction pes generalizing state with
  | nil =>
      simp [executeIntegerProducerLineAtPEs] at executed
      subst executed
      exact SameOtherFields.refl state
  | cons pe rest ih =>
      simp only [executeIntegerProducerLineAtPEs] at executed
      split at executed
      · cases executed
      · cases executed
      · rename_i intermediate headExecuted
        exact SameOtherFields.trans
          (executeIntegerProducerLineAtPE_sameOther expressions state intermediate pe
            headExecuted)
          (ih intermediate executed)

/-! ## Field-level frame: plain integer-ALU `.pe` lines -/

/-- A successful plain integer-ALU `.pe` line leaves every `State` field that
the footprint does not name unchanged.

Named by the footprint of such a line: `peRegisters` (`.alu` plus
destination operand writes), `forwarding`/`forwardingValid` (`.forwarding`),
`peContext` (`.bar`, only for the BAR-destination subclass), `hazardClock`
(`.hazardClock`) and `l1bmTurnaroundValid` (`.l1bmTurnaround`). The theorem
covers everything else, and is stronger than the resource-level claim for
`.l1bmTurnaround`: the turnaround payload is unchanged, only the validity
latch moves to `false`. -/
theorem executeNormalizedLine_pe_plainIntegerALU_field_frame
    (normalizedExpressions : List NormalizedExpr) (state next : State)
    (plain : (normalizedExpressions.map NormalizedExpr.toParsed).all
      parsedExprIsPlainIntegerALU = true)
    (success : executeNormalizedLine (.pe normalizedExpressions) state = .ok next) :
    next.l1bm = state.l1bm ∧
    next.l1bmTurnaround = state.l1bmTurnaround ∧
    next.l1bmTurnaroundValid = false ∧
    next.blockMemory = state.blockMemory ∧
    next.dar = state.dar ∧
    next.darBuffer = state.darBuffer ∧
    next.darBufferReadAddress = state.darBufferReadAddress ∧
    next.darWriteAddress = state.darWriteAddress ∧
    next.mvCompletedTags = state.mvCompletedTags ∧
    next.pendingMv = state.pendingMv ∧
    next.matrixRegisters = state.matrixRegisters ∧
    next.maskDirective = state.maskDirective ∧
    next.hazardClock =
      state.hazardClock + InstructionLine.cost (.pe normalizedExpressions) := by
  simp only [executeNormalizedLine, NormalizedLine.toInstruction?] at success
  have accepted := executeIntegerProducerInstructionLine_accepted_of_ok
    (.pe normalizedExpressions) state next success
  obtain ⟨nextPEs, executed, nextEq⟩ :=
    executeIntegerProducerInstructionLine_pe_plainIntegerALU_exists
      normalizedExpressions state next accepted plain success
  have frame := executeIntegerProducerLineAtPEs_sameOther _ (List.finRange 4096)
    state nextPEs executed
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := frame
  subst nextEq
  refine ⟨h1.symm, h2.symm, rfl, h4.symm, h5.symm, h6.symm, h7.symm, h8.symm,
    h9.symm, h10.symm, h11.symm, h12.symm, ?_⟩
  rw [h13]

/-- The strongest per-PE-stage-unconditional step equation available for the
plain integer-ALU class: the per-PE walk's success is *derived* from the line's
success instead of assumed, and the result state is pinned down.

A hypothesis-free version (`... = .ok ...` for every `state`) is false for any
class that lets an ALU read a source. A `.forward` source whose
`forwardingValid` bit is false is lowered to poison, and
`ParsedIntegerInput.readWithForwarding` returns `.failure` for it (the proved
lemma `disabledForwardingSlot_read_fails`); `executeIntegerProducerLineAtPEs`
and `executeIntegerProducerInstructionLine` propagate that `.failure`. The
plain predicate says nothing about read success, and
`executeIntegerProducerInstructionLine_pe_never_unknown_of_stages` only
excludes `.unknown` (its `peKnown` hypothesis is an `.unknown` statement), so it
cannot supply the missing `.ok`. The undischarged hypothesis is per-PE read
success (equivalently, `stateForwardingSlots` being free of poison at every
read slot); it is not derivable from `plain`. -/
theorem executeNormalizedLine_pe_plainIntegerALU_pe_stage
    (normalizedExpressions : List NormalizedExpr) (state next : State)
    (plain : (normalizedExpressions.map NormalizedExpr.toParsed).all
      parsedExprIsPlainIntegerALU = true)
    (success : executeNormalizedLine (.pe normalizedExpressions) state = .ok next) :
    ∃ nextPEs,
      executeIntegerProducerLineAtPEs
        ((normalizedExpressions.map NormalizedExpr.toParsed).filter (fun expression =>
          !parsedExprIsL2BMProducer expression && !parsedExprIsMslMsrProducer expression &&
            !parsedExprIsMatrixMAUProducer expression &&
            !parsedExprIsBlockFloatProducer expression &&
            !parsedExprIsFloatReluProducer expression))
        (List.finRange 4096) state = .ok nextPEs ∧
      next = { nextPEs with
        hazardClock := nextPEs.hazardClock + InstructionLine.cost (.pe normalizedExpressions)
        l1bmTurnaroundValid := false } := by
  simp only [executeNormalizedLine, NormalizedLine.toInstruction?] at success
  have accepted := executeIntegerProducerInstructionLine_accepted_of_ok
    (.pe normalizedExpressions) state next success
  exact executeIntegerProducerInstructionLine_pe_plainIntegerALU_exists
    normalizedExpressions state next accepted plain success

/-! ## Field-level frame: `.nop` and `.mv` lines -/

/-- A successful `.nop` line changes only the hazard clock. The footprint of a
positive `nop` names `.hazardClock`; the footprint of `.nop 0` is empty and the
clock increment is zero, so the state is unchanged there. -/
theorem executeNormalizedLine_nop_field_frame (count : Nat) (wait : Option (Fin 256))
    (state next : State)
    (success : executeNormalizedLine (.nop count wait) state = .ok next) :
    next = { state with hazardClock := state.hazardClock + count } := by
  cases count with
  | zero =>
      simp [executeNormalizedLine, NormalizedLine.toInstruction?] at success
  | succ count =>
      unfold executeNormalizedLine at success
      simp only [NormalizedLine.toInstruction?] at success
      unfold executeIntegerProducerInstructionLine at success
      by_cases accepted : checkParsedTopLine
        (InstructionLine.nop ⟨count + 1, Nat.succ_pos count⟩ wait).toParsed
      · cases wait with
        | none =>
            simp [accepted] at success
            exact success.symm
        | some tag =>
            by_cases complete : state.mvCompletedTags tag
            · simp [accepted, complete] at success
              exact success.symm
            · simp [accepted, complete] at success
      · simp [accepted] at success

/-- `executeParsedMvMemory` stages writes but only changes `pendingMv` and
`mvCompletedTags`. Every field in this conjunction is unchanged, including the
hazard clock (the caller advances it). -/
theorem executeParsedMvMemory_sameExceptStaging (state : State) (transfer : ParsedMv)
    (next : State) (success : executeParsedMvMemory state transfer = .ok next) :
    next.l1bm = state.l1bm ∧
    next.l1bmTurnaround = state.l1bmTurnaround ∧
    next.l1bmTurnaroundValid = state.l1bmTurnaroundValid ∧
    next.blockMemory = state.blockMemory ∧
    next.dar = state.dar ∧
    next.darBuffer = state.darBuffer ∧
    next.darBufferReadAddress = state.darBufferReadAddress ∧
    next.darWriteAddress = state.darWriteAddress ∧
    next.peRegisters = state.peRegisters ∧
    next.matrixRegisters = state.matrixRegisters ∧
    next.forwarding = state.forwarding ∧
    next.forwardingValid = state.forwardingValid ∧
    next.maskDirective = state.maskDirective ∧
    next.peContext = state.peContext ∧
    next.hazardClock = state.hazardClock := by
  unfold executeParsedMvMemory at success
  split at success
  · cases success
  · split at success
    · simp only [StepResult.ok.injEq] at success
      subst success
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · simp only [StepResult.ok.injEq] at success
      subst success
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A successful `.mv` line advances the clock by one and otherwise changes at
most `pendingMv` and `mvCompletedTags` (both named by `.mv` in the footprint;
the nop-kind `.mv` changes neither). Every other field is unchanged. -/
theorem executeNormalizedLine_mv_field_frame (transfer : NormalizedMv) (state next : State)
    (success : executeNormalizedLine (.mv transfer) state = .ok next) :
    next.l1bm = state.l1bm ∧
    next.l1bmTurnaround = state.l1bmTurnaround ∧
    next.l1bmTurnaroundValid = state.l1bmTurnaroundValid ∧
    next.blockMemory = state.blockMemory ∧
    next.dar = state.dar ∧
    next.darBuffer = state.darBuffer ∧
    next.darBufferReadAddress = state.darBufferReadAddress ∧
    next.darWriteAddress = state.darWriteAddress ∧
    next.peRegisters = state.peRegisters ∧
    next.matrixRegisters = state.matrixRegisters ∧
    next.forwarding = state.forwarding ∧
    next.forwardingValid = state.forwardingValid ∧
    next.maskDirective = state.maskDirective ∧
    next.peContext = state.peContext ∧
    next.hazardClock = state.hazardClock + 1 := by
  simp only [executeNormalizedLine, NormalizedLine.toInstruction?] at success
  have accepted := executeIntegerProducerInstructionLine_accepted_of_ok
    (.mv transfer) state next success
  unfold executeIntegerProducerInstructionLine at success
  simp only [accepted, Bool.not_true, Bool.false_eq_true, ite_false] at success
  cases isNop : transfer.kind == .nop with
  | true =>
      simp only [isNop, ite_true] at success
      cases success
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | false =>
      simp only [isNop, ite_false] at success
      cases memoryResult : executeParsedMvMemory state transfer.toParsed with
      | failure =>
          rw [memoryResult] at success
          cases success
      | unknown =>
          rw [memoryResult] at success
          cases success
      | ok nextMv =>
          rw [memoryResult] at success
          have frame := executeParsedMvMemory_sameExceptStaging state transfer.toParsed
            nextMv memoryResult
          obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := frame
          cases success
          refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, ?_⟩
          rw [h15]

end ProofsLean.MNCore
