import ProofsLean.ConvertEndianLowerBound
import ProofsLean.CendValueFamilies

/-! # `12.convert-endian` — the two-unit-line obligation

`ProofsLean/ConvertEndianLowerBound.lean` reduces `LowerBound cendSealedMachine
cendSpec 3` to the one-line residual `CendPELinesRefuted` and the two-line
obligation

```
CendTwoLinesRefuted :=
  ∀ first second, cost first = 1 → cost second = 1 →
    ¬ Correct cendSealedMachine cendSpec [first, second].
```

This module isolates **what the first line can hand the second** and reduces
`CendTwoLinesRefuted` to a single residual over that handoff.

## What is proved here

* §1 — the cost-one lines are exactly `.pe`, `.mv` and `nop/1`.
* §2 — **a second line that frames the observed PE's register file is useless.**
  If a successful step of `second` leaves `peRegisters` unchanged (`nop`, `mv`, or
  a `.pe` line all of whose rows are `.noforward`), then `[first, second]` is
  correct only if the single line `[first]` is.  Since every single line is
  refuted (the one-line residual for `.pe`, unconditional frame arguments for
  `nop`/`mv`), such a pair is never correct — for *any* first line, and with no
  cost hypothesis on either side.
* §3 — the **step shapes** of the two remaining first-line kinds: a successful
  `nop/1` only advances the hazard clock, and a successful `mv` changes only the
  clock, the pending-transfer list and the completed-tag table — and at the
  `12.convert-endian` initial state the completed-tag table is the constant
  `false`, so the transfer writes do not change it.  Hence a `nop`/`mv` first
  line hands the second line the initial register/forwarding/matrix state
  together with a clock/pending bookkeeping delta, and so cannot add a datapath
  value.  (The *formal* value congruence over that delta — the executor's
  independence from `hazardClock` and `pendingMv` — is recorded in §6 as part of
  the residual; the executor writes the elapsed clock into its control record,
  so a general proof needs an induction over every stage.)
* §4 — the **forwarding handoff**: every `.forward` read fails at the initial
  state (the Rust uninitialised-forwarding path), the initial slots are `poison`,
  and a `.noforward` line preserves the validity bits.  A `.pe` line *does* write
  the observed PE's slots, but only through
  `updateSupportedPELineForwarding` / `updateIntegerLineForwardingValid`, i.e.
  with the payload its own supported integer/float stages produced.
* §5 — the **commit does not mix halves when the mask flags are whole-word**:
  if every write's selection flags are `0` or `allOnes`, then a commit step keeps
  the old LM1 word or overwrites it *as a whole* with one data word, and a chain
  of such commits (one per executor stage of a line) leaves the initial word or
  one data word of one of the committed lists
  (`cendCommitChain_lm1_old_or_data`).  This is the form in which the one-line
  value analysis can be pushed through a commit; the half-mix closure
  `cendMixWords` of `CendValueFamilies` is its conservative superset.
  **Caveat:** the whole-word flag invariant holds at the initial state
  (`CendFinal.resolveMaskSelection_zero_flags`) but is *broken* by an OMR mask
  write: `prepareParsedIntegerMaskExprCycle` stores
  `newFlags = output.flags` (`BitVec.ofBoolListLE` of the four ALU flag bits) into
  the mask registers, and `newFlags &&& allOnes` is that flag pattern.  So a
  first line can plant an arbitrary ALU flag pattern, a second line's `.entry`
  mask can read it, and half masks (hence 16-bit-half mixing) are *reachable* in
  the two-line case.  The whole-word lemmas are conditional tools, not the final
  argument.
* §6 — the **residual**: the pairs not closed by §2 are exactly those whose
  second line is a live `.pe` line (a `.pe` line with at least one non-
  `.noforward` row).  The residual is named
  `CendTwoLiveSecondLinesRefuted`; given the one-line residual it is *exactly*
  the two-line obligation (`cendTwoLinesRefuted_iff_liveSecondLines`) and
  *exactly* the bound at three (`cendLowerBound_three_iff_liveSecondLines`).
* §7 — `CendTwoLinesRefuted` from the residual, then
  `LowerBound cendSealedMachine cendSpec 3`, and `Optimal` from the official
  answer's correctness and three-word score.

## What is *not* closed here

`CendTwoLiveSecondLinesRefuted`.  **The value analysis sketched in
`research/experiments/cend-proof/REPORT.md` §1.3 is not sufficient for it**, for
a reason worth recording:

* at `cendWitness = 0x0102030405060708` the report's two-stage table `W2`
  (`|W2| = 57740`) contains *neither* full target word `0x08070605` /
  `0x04030201`, which is the check that was run;
* but the second line's commit may use 16-bit-half masks (see §5), and
  `W2` **does** contain a word with high half `0x0807` and a word with low half
  `0x0605` (verified here with the report's own `value_closure.py` model:
  `any_high16 = any_low16 = True` at the witness).  With half masks a single
  line can combine those two halves from two different commits.  The
  half-mix closure `cendMixWords (L ∪ W2)` therefore *does* contain
  `0x08070605` (`cendMixWords_mem` needs exactly such a pair), so the
  half-mix-level value argument cannot close the two-line case either.

What remains is therefore a **joint** second-line reachability statement: no
single `.pe` line, from the state the first line left, has both (i) the mask
flags and (ii) the two lane words it needs to place the target halves at the two
observed LM1 indices.  Its coarse superset (the two-stage table plus arbitrary
half masks) is *not* target-free, so the obligation needs either the per-row
lane/mask constraints or a program-dependent witness.  The executor link for a
certificate would be the one-line argument's `LinePreparedDataInClosure`
(`ProofsLean/ValueProvenance.lean`) instantiated at the handoff state; it is not
carried out here.  The `imm P` shape (`first = imm i"P" $r0v`) additionally needs
a program-dependent witness over the 32-bit payload (report §1.4).

Consequently this module does **not** prove `CendTwoLinesRefuted`,
`LowerBound cendSealedMachine cendSpec 3` or `Optimal` unconditionally: the
statements below are reductions to the named residuals, and the `Optimal`
statement additionally takes the judge-accepted three-line answer's Lean
correctness and score as hypotheses (the answer has not been connected to
`executeNormalizedLine` in the tree).

No `sorry`, no `admit`, no `native_decide`, no new axioms, and no existing
module is edited.
-/

namespace ProofsLean.MNCore

open Issue
open PEMemory

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false

/-! ## 1. The cost-one lines -/

/-- **The cost-one lines.**  A line of cost one is a `.pe` line, an `.mv` line,
or a `nop/1`. -/
theorem cendCostOne_cases (line : InstructionLine) (cost : InstructionLine.cost line = 1) :
    (∃ expressions : List NormalizedExpr, line = .pe expressions) ∨
      (∃ transfer : NormalizedMv, line = .mv transfer) ∨
      (∃ wait : Option (Fin 256), line = .nop ⟨1, by decide⟩ wait) := by
  cases line with
  | pe expressions => exact Or.inl ⟨expressions, rfl⟩
  | mv transfer => exact Or.inr (Or.inl ⟨transfer, rfl⟩)
  | nop count wait =>
      right; right
      have value : count.val = 1 := cost
      have same : count = (⟨1, by decide⟩ : {n : Nat // 0 < n}) :=
        Subtype.ext (by simpa using value)
      subst same
      exact ⟨wait, rfl⟩

/-! ## 2. A framing second line is useless

`CendLineFramesRegisters second` is the only property of the second line used
here: a successful step leaves every PE register file unchanged.  The observed
output pair is a function of the observed PE's file, so such a second line
contributes nothing: the program is correct only if the first line alone is,
and the first line alone is refuted. -/

/-- A line whose successful step leaves every PE register file unchanged. -/
def CendLineFramesRegisters (line : InstructionLine) : Prop :=
  ∀ (state next : State), cendSealedMachine.step line state = some next →
    next.peRegisters = state.peRegisters

theorem cendLineFrames_nop (count : {n : Nat // 0 < n}) (wait : Option (Fin 256)) :
    CendLineFramesRegisters (.nop count wait) := by
  intro state next step
  exact executeNormalizedLine_nop_peRegisters count.val wait state next (cendSealed_step_ok step)

theorem cendLineFrames_mv (transfer : NormalizedMv) :
    CendLineFramesRegisters (.mv transfer) := by
  intro state next step
  exact executeNormalizedLine_mv_peRegisters transfer state next (cendSealed_step_ok step)

theorem cendLineFrames_noforward (expressions : List NormalizedExpr)
    (all : CendAllNoForward expressions) :
    CendLineFramesRegisters (.pe expressions) := by
  intro state next step
  exact executeNormalizedLine_pe_peRegisters_noforward expressions state next
    (fun expression member => all expression member) (cendSealed_step_ok step)

/-- **One-line execution is the line step.** -/
theorem cend_execute_single (line : InstructionLine) (state : State) :
    ProofsLean.execute cendSealedMachine [line] state = cendSealedMachine.step line state := by
  cases h : cendSealedMachine.step line state with
  | none => simp [ProofsLean.execute, h]
  | some next => simp [ProofsLean.execute, h]

/-- **Two-line execution is the two steps.** -/
theorem cend_execute_two (first second : InstructionLine) (state : State) :
    ProofsLean.execute cendSealedMachine [first, second] state =
      (cendSealedMachine.step first state).bind (fun middle => cendSealedMachine.step second middle) := by
  cases h : cendSealedMachine.step first state with
  | none => simp [ProofsLean.execute, h]
  | some middle => simp [ProofsLean.execute, h, cend_execute_single]

/-- **A framing second line collapses the program to its first line.** -/
theorem cendCorrect_single_of_frame (first second : InstructionLine)
    (frames : CendLineFramesRegisters second)
    (correct : ProofsLean.Correct cendSealedMachine cendSpec [first, second]) :
    ProofsLean.Correct cendSealedMachine cendSpec [first] := by
  refine ⟨by simp [cendSealedMachine], ?_⟩
  intro input admissible
  obtain ⟨result, executed, post⟩ := correct.2 input admissible
  have executed' : ProofsLean.execute cendSealedMachine [first, second]
      (cendInitialState input) = some result := executed
  rw [cend_execute_two] at executed'
  obtain ⟨middle, firstStep, secondStep⟩ := Option.bind_eq_some_iff.mp executed'
  refine ⟨middle, ?_, ?_⟩
  · exact (cend_execute_single first (cendSpec.initial input)).trans firstStep
  · have same : cendOutputPair middle = cendOutputPair result := by
      unfold cendOutputPair
      rw [frames middle result secondStep]
    have post' : cendOutputPair result = byteSwap64 input := post
    show cendOutputPair middle = byteSwap64 input
    rw [same]
    exact post'

/-- No single line is correct, given the one-line residual. -/
theorem cendSingle_not_correct (peLines : CendPELinesRefuted) (line : InstructionLine) :
    ¬ ProofsLean.Correct cendSealedMachine cendSpec [line] := by
  cases line with
  | pe expressions => exact peLines expressions
  | nop count wait => exact cendNop_not_correct count wait
  | mv transfer => exact cendMv_not_correct transfer

/-- **The second-framing reduction.**  A second line that frames the register
file is refuted for *every* first line, with no cost hypothesis on either side. -/
theorem cendTwoLines_second_frame_not_correct (peLines : CendPELinesRefuted)
    (first second : InstructionLine) (frames : CendLineFramesRegisters second) :
    ¬ ProofsLean.Correct cendSealedMachine cendSpec [first, second] :=
  fun correct =>
    cendSingle_not_correct peLines first (cendCorrect_single_of_frame first second frames correct)

/-! ## 3. The step shapes of a `nop/1` and an `mv` first line

At the `12.convert-endian` initial state the completed-tag table is the constant
`false` (`mvCompletedTags := fun _ => false`), so an `mv` transfer can only write
`false` into it again: the tag table is untouched.  A `nop/1` with a wait tag is
stuck (the tag is never completed), so a successful `nop/1` is a pure clock
advance.  These shapes say exactly what a `nop`/`mv` first line can hand the
second: no register, forwarding or matrix value at all. -/

theorem cendInitial_mvCompletedTags (input : BitVec 64) (tag : Fin 256) :
    (cendInitialState input).mvCompletedTags tag = false := rfl

theorem cendInitial_pendingMv (input : BitVec 64) :
    (cendInitialState input).pendingMv = [] := rfl

theorem cendInitial_forwardingValid (input : BitVec 64) (pe : PEId)
    (unit : Forwarding.Unit) (cycle : Fin 4) :
    (cendInitialState input).forwardingValid pe unit cycle = false := rfl

/-- **A successful `mv` transfer, decomposed.**  With `kind ≠ nop` the memory
stage returns exactly the pending-list/tag-table update. -/
theorem cendMvMemory_transfer_shape (state : State) (transfer : ParsedMv)
    (notNop : transfer.kind ≠ .nop) (writes : List (MVSemantics.Cell × BitVec 64))
    (pending : MVSemantics.parsedMvPendingWritesWithDAR? state.blockMemory state.dar
      transfer = some writes) :
    executeParsedMvMemory state transfer =
      .ok { state with
        pendingMv := state.pendingMv ++ [{ tag := transfer.tag, writes := writes }]
        mvCompletedTags := fun tag =>
          if transfer.tag == some tag then false else state.mvCompletedTags tag } := by
  unfold executeParsedMvMemory
  rw [pending]
  have hbeq : (transfer.kind == .nop) = false := by
    cases h : transfer.kind == .nop with
    | false => rfl
    | true => exact absurd (beq_iff_eq.mp h) notNop
  simp [hbeq]

/-- **A successful `mv` transfer with `kind = nop` changes nothing.** -/
theorem cendMvMemory_nop_shape (state : State) (transfer : ParsedMv)
    (isNop : transfer.kind = .nop) (writes : List (MVSemantics.Cell × BitVec 64))
    (pending : MVSemantics.parsedMvPendingWritesWithDAR? state.blockMemory state.dar
      transfer = some writes) :
    executeParsedMvMemory state transfer = .ok state := by
  unfold executeParsedMvMemory
  rw [pending]
  simp [isNop]

/-- **A successful `mv` memory transition exposes its pending writes.** -/
theorem cendMvMemory_somePending (state : State) (transfer : ParsedMv) (next : State)
    (executed : executeParsedMvMemory state transfer = .ok next) :
    ∃ writes, MVSemantics.parsedMvPendingWritesWithDAR? state.blockMemory state.dar transfer =
      some writes := by
  cases h : MVSemantics.parsedMvPendingWritesWithDAR? state.blockMemory state.dar transfer with
  | none =>
      unfold executeParsedMvMemory at executed
      rw [h] at executed
      simp at executed
  | some writes => exact ⟨writes, rfl⟩

/-- **A successful `nop/1` only advances the clock.** -/
theorem cendNop_step_clock (input : BitVec 64) (wait : Option (Fin 256)) (next : State)
    (step : cendSealedMachine.step (.nop ⟨1, by decide⟩ wait) (cendInitialState input) =
      some next) :
    next = { cendInitialState input with
      hazardClock := (cendInitialState input).hazardClock + 1 } := by
  have executed := cendSealed_step_ok step
  simp only [Issue.InstructionLine.toNormalizedLine] at executed
  cases wait with
  | none =>
      have executed' : executeIntegerProducerInstructionLine (.nop ⟨1, by decide⟩ none)
          (cendInitialState input) = .ok next := by
        simpa [executeNormalizedLine, NormalizedLine.toInstruction?] using executed
      rw [executeIntegerProducerInstructionLine_nop ⟨1, by decide⟩ none _
        (by decide) rfl] at executed'
      exact (StepResult.ok.inj executed').symm
  | some tag =>
      have executed' : executeIntegerProducerInstructionLine (.nop ⟨1, by decide⟩ (some tag))
          (cendInitialState input) = .ok next := by
        simpa [executeNormalizedLine, NormalizedLine.toInstruction?] using executed
      have accepted := executeIntegerProducerInstructionLine_accepted_of_ok
        (InstructionLine.nop ⟨1, by decide⟩ (some tag)) (cendInitialState input) next executed'
      have pending : (cendInitialState input).mvCompletedTags tag = false := rfl
      rw [executeIntegerProducerInstructionLine_wait_pending_unknown ⟨1, by decide⟩ tag
        (cendInitialState input) accepted pending] at executed'
      simp at executed'

/-- **A successful `mv` only changes the clock and the pending-transfer list.** -/
theorem cendMv_step_shape (input : BitVec 64) (transfer : NormalizedMv) (next : State)
    (step : cendSealedMachine.step (.mv transfer) (cendInitialState input) = some next) :
    ∃ pending : List PendingMv,
      next = { cendInitialState input with
        pendingMv := pending
        hazardClock := (cendInitialState input).hazardClock + 1 } := by
  have executed := cendSealed_step_ok step
  simp only [Issue.InstructionLine.toNormalizedLine] at executed
  by_cases isNop : transfer.kind = .nop
  · have executed' : executeIntegerProducerInstructionLine (.mv transfer)
        (cendInitialState input) = .ok next := by
      simpa [executeNormalizedLine, NormalizedLine.toInstruction?] using executed
    rw [executeIntegerProducerInstructionLine_mvnop transfer (cendInitialState input) isNop rfl]
      at executed'
    refine ⟨(cendInitialState input).pendingMv, ?_⟩
    exact (StepResult.ok.inj executed').symm
  · have notNopBool : (transfer.kind == .nop) = false := by
      cases h : transfer.kind == .nop with
      | false => rfl
      | true => exact absurd (beq_iff_eq.mp h) isNop
    have executed' : executeIntegerProducerInstructionLine (.mv transfer)
        (cendInitialState input) = .ok next := by
      simpa [executeNormalizedLine, NormalizedLine.toInstruction?] using executed
    cases memoryResult : executeParsedMvMemory (cendInitialState input) transfer.toParsed with
    | failure =>
        have failed : executeIntegerProducerInstructionLine (.mv transfer)
            (cendInitialState input) = .failure := by
          simp [executeIntegerProducerInstructionLine, InstructionLine.toParsed,
            notNopBool, memoryResult]
        rw [failed] at executed'
        simp at executed'
    | unknown =>
        exact absurd memoryResult
          (executeParsedMvMemory_never_unknown (cendInitialState input) transfer.toParsed)
    | ok middle =>
        have nextEq : next = { middle with hazardClock := middle.hazardClock + 1 } := by
          rw [executeIntegerProducerInstructionLine_mv_transfer_success transfer
            (cendInitialState input) middle rfl isNop memoryResult] at executed'
          exact (StepResult.ok.inj executed').symm
        obtain ⟨writes, pending⟩ := cendMvMemory_somePending (cendInitialState input)
          transfer.toParsed middle memoryResult
        have notNopParsed : transfer.toParsed.kind ≠ .nop := by
          show transfer.kind ≠ .nop
          exact isNop
        have middleEq : middle = { cendInitialState input with
            pendingMv := (cendInitialState input).pendingMv ++
              [{ tag := transfer.toParsed.tag, writes := writes }]
            mvCompletedTags := fun tag =>
              if transfer.toParsed.tag == some tag then false
              else (cendInitialState input).mvCompletedTags tag } := by
          rw [cendMvMemory_transfer_shape (cendInitialState input) transfer.toParsed
            notNopParsed writes pending] at memoryResult
          exact (StepResult.ok.inj memoryResult).symm
        refine ⟨(cendInitialState input).pendingMv ++
          [{ tag := transfer.toParsed.tag, writes := writes }], ?_⟩
        rw [nextEq, middleEq]
        have tagsEq : (fun tag =>
              if transfer.toParsed.tag == some tag then false
              else (cendInitialState input).mvCompletedTags tag) =
            (cendInitialState input).mvCompletedTags := by
          funext tag
          simp [cendInitialState, rustSimulatorInitialState]
        rw [tagsEq]

/-! ## 4. The forwarding handoff

At the initial state every forwarding slot is disabled (validity `false`), and a
disabled slot is presented to every reader as `poison`, which the parsed-input
reader turns into a known failure.  A `.noforward` line preserves the validity
bits, so the slots stay poison after such a first line.  A `.pe` line *does*
write the observed PE's forwarding slots (`executeIntegerProducerLineAtPECore`),
but only with the payload its own supported ALU/MAU/matrix-read stages produced,
through `updateSupportedPELineForwarding`, and only enables validity through
`updateIntegerLineForwardingValid`. -/

/-- **Every `.forward` read fails at the `12.convert-endian` initial state.** -/
theorem cendInitial_forward_read_fails (input : BitVec 64) (pe : PEId) (cycle : Fin 4)
    (kind : ParsedForward) :
    ParsedIntegerInput.readWithForwarding ((cendInitialState input).peRegisters pe)
      (stateForwardingSlots (cendInitialState input) pe) cycle (.forward kind false) =
        .failure := by
  exact rustSimulatorInitialState_forwarding_read_fails pe cycle kind

/-- The initial forwarding slots are poison. -/
theorem cendInitial_forwardingSlots_poison (input : BitVec 64) (pe : PEId)
    (unit : Forwarding.Unit) (cycle : Fin 4) :
    stateForwardingSlots (cendInitialState input) pe unit cycle = .poison :=
  stateForwardingSlots_invalid_is_poison _ _ _ _ (cendInitial_forwardingValid input pe unit cycle)

/-- **A `.noforward` line preserves the forwarding validity bits.** -/
theorem cendForwardingValidity_noforward (old : Forwarding.Unit → Fin 4 → Bool)
    (slots : Forwarding.Slots) :
    updateIntegerLineForwardingValid old slots true = old :=
  noforward_preserves_forwarding_validity old slots

/-- **A `.noforward` line adds no forwarding payload.**  A successful
all-`.noforward` `.pe` line writes the observed PE's forwarding slots back as
`stateForwardingSlots state pe`: the slots stay poison at the initial state. -/
theorem cendPE_noforward_forwarding_frame (expressions : List ParsedExpr) (state next : State)
    (pe : PEId)
    (all : ∀ expression ∈ expressions, expression.op = .noforward)
    (anyNoforward : (expressions.any fun expression =>
      match expression.op with | .noforward => true | _ => false) = true)
    (executed : executeIntegerProducerLineAtPECore expressions state pe = .ok next) :
    next.forwarding pe = stateForwardingSlots state pe ∧
      ∀ other, other ≠ pe → next.forwarding other = state.forwarding other :=
  executeIntegerProducerLineAtPECore_forwarding_noforward expressions state next pe all
    anyNoforward executed

/-! ## 5. The commit masks are whole-word: no half mixing

At the `12.convert-endian` initial state the mask register file is zero, and every
mask resolution (`resolveParsedMaskFlags?`) returns flags `0` or `allOnes`:
a `.pattern` mask gives `allOnes`/`0` per cycle, an `.entry` mask with index
`> 0` reads a mask register (zero initially, and a mask-register write stores
exactly a resolved flag vector) or the directive-entry bits (again `allOnes`/`0`).
`CendFinal.resolveMaskSelection_zero_flags` is the zero-register instance.

For such flags `selectedWordMask` is `0` or `allOnes`, so a commit step either
keeps the old LM1 word or overwrites it **as a whole** with one data word.  The
half-mix closure `cendMixWords` of the one-line corpus
(`CendValueFamilies.commitParsedMaskedWrites_lm1_mixWords`) is therefore
conservative; the two-line value obligation is the *whole-word* statement that
no data word of the second line equals `byteSwap64`'s high/low 32-bit word — the
form of the two-stage certificate in `research/experiments/cend-proof/REPORT.md`
§1.3. -/

/-- A mask register file whose entries are only `0` or `allOnes`. -/
def CendMaskRegistersWholeWord (registers : Masks.RegisterFile) : Prop :=
  ∀ (entry : Fin 15) (cycle : Fin 4),
    registers entry cycle = 0 ∨ registers entry cycle = BitVec.allOnes 4

theorem cendInitial_maskRegisters_wholeWord (input : BitVec 64) :
    CendMaskRegistersWholeWord (cendInitialPERegisters input).maskRegisters := by
  intro entry cycle
  exact Or.inl rfl

/-- **A whole-word flag vector selects a whole-word mask.** -/
theorem cendSelectedMask_zero_or_allOnes (flags : BitVec 4) (longLong : Bool)
    (index : Fin 4) (whole : flags = 0 ∨ flags = BitVec.allOnes 4) :
    selectedWordMask flags longLong index = 0 ∨
      selectedWordMask flags longLong index = BitVec.allOnes 32 := by
  rcases whole with rfl | rfl
  · cases longLong with
    | true =>
        left
        unfold selectedWordMask
        simp
    | false =>
        by_cases h : index.val < 2
        · left
          unfold selectedWordMask
          simp [h]
        · right
          unfold selectedWordMask
          simp [h]
  · cases longLong with
    | true =>
        right
        unfold selectedWordMask
        rw [BitVec.getLsbD_allOnes]
        have hpos : 3 - index.val < 4 := by omega
        simp [hpos]
    | false =>
        by_cases h : index.val < 2
        · right
          have h01 : index.val = 0 ∨ index.val = 1 := by omega
          rcases h01 with h0 | h1
          · have hidx : index = (⟨0, by decide⟩ : Fin 4) := Fin.ext h0
            subst hidx
            decide
          · have hidx : index = (⟨1, by decide⟩ : Fin 4) := Fin.ext h1
            subst hidx
            decide
        · right
          unfold selectedWordMask
          simp [h]

/-- **A whole-word merge keeps the old word or takes the new one.** -/
theorem cendMergeSelectedWord_old_or_data (old data : BitVec 32) (flags : BitVec 4)
    (longLong : Bool) (index : Fin 4) (whole : flags = 0 ∨ flags = BitVec.allOnes 4) :
    mergeSelectedWord old data (selectedWordMask flags longLong index) = old ∨
      mergeSelectedWord old data (selectedWordMask flags longLong index) = data := by
  rcases cendSelectedMask_zero_or_allOnes flags longLong index whole with h | h
  · left
    unfold mergeSelectedWord
    rw [h]
    rw [show ~~~(0 : BitVec 32) = BitVec.allOnes 32 from by decide]
    rw [BitVec.and_allOnes]
    rw [show (data &&& (0 : BitVec 32)) = 0 from BitVec.and_zero]
    exact BitVec.or_zero
  · right
    unfold mergeSelectedWord
    rw [h]
    rw [show ~~~(BitVec.allOnes 32) = (0 : BitVec 32) from by decide]
    rw [show (old &&& (0 : BitVec 32)) = 0 from BitVec.and_zero]
    rw [BitVec.and_allOnes]
    exact BitVec.zero_or

/-- **One commit step at an LM1 word keeps the old word or takes one data word.** -/
theorem cendCommitStep_lm1_old_or_data (files : IntegerRegisterFiles)
    (write : PreparedParsedMaskedWrite) (target : Fin Bank.lm1.capacity)
    (whole : ∀ (width : PEMemory.Width) (address : Fin Bank.lm1.capacity)
        (data : WordBus) (selection : PEWordSelection),
      write.destination = some ⟨.lm1, width, address⟩ → write.data = data →
      write.selection = selection → selection.flags = 0 ∨ selection.flags = BitVec.allOnes 4) :
    (welcomeCommitStep files write).lm1 target = files.lm1 target ∨
      ∃ (width : PEMemory.Width) (address : Fin Bank.lm1.capacity) (index : Fin 4),
        write.destination = some ⟨.lm1, width, address⟩ ∧
          (welcomeCommitStep files write).lm1 target = write.data index := by
  obtain ⟨destination, maskUpdate, data, selection⟩ := write
  cases maskUpdate with
  | some update =>
      left
      simp only [welcomeCommitStep]
  | none =>
      cases destination with
      | none =>
          left
          simp only [welcomeCommitStep]
      | some access =>
          obtain ⟨bank, width, address⟩ := access
          cases bank with
          | lm1 =>
              simp only [welcomeCommitStep]
              rw [writeDirectAccessMasked_lm1_apply]
              by_cases within : PEMemory.distance Bank.lm1 address target <
                  PEMemory.count Bank.lm1 width
              · rw [PEMemory.writeWordsMasked_at _ width files.lm1 address target data
                  selection.flags selection.longLong within]
                have hflags := whole width address data selection rfl rfl rfl
                rcases cendMergeSelectedWord_old_or_data (files.lm1 target)
                    (data ⟨PEMemory.distance Bank.lm1 address target,
                      Nat.lt_of_lt_of_le within (PEMemory.count_le_four _ _)⟩)
                    selection.flags selection.longLong _ hflags with h | h
                · exact Or.inl h
                · exact Or.inr ⟨width, address, _, rfl, h⟩
              · left
                rw [PEMemory.writeWordsMasked_preserves_outside _ width files.lm1 address
                  target data selection.flags selection.longLong (Nat.le_of_not_lt within)]
          | lm0 =>
              left
              simp only [welcomeCommitStep]
              rw [writeDirectAccessMasked_lm1_eq _ _ _ _ _ _ (by decide)]
          | grf0 =>
              left
              simp only [welcomeCommitStep]
              rw [writeDirectAccessMasked_lm1_eq _ _ _ _ _ _ (by decide)]
          | grf1 =>
              left
              simp only [welcomeCommitStep]
              rw [writeDirectAccessMasked_lm1_eq _ _ _ _ _ _ (by decide)]
          | t =>
              left
              simp only [welcomeCommitStep]
              rw [writeDirectAccessMasked_lm1_eq _ _ _ _ _ _ (by decide)]

/-- **A whole commit at an LM1 word keeps the old word or takes one data word.** -/
theorem cendCommitParsedMaskedWrites_lm1_old_or_data (files : IntegerRegisterFiles)
    (writes : List PreparedParsedMaskedWrite) (target : Fin Bank.lm1.capacity)
    (whole : ∀ write ∈ writes, ∀ (width : PEMemory.Width)
        (address : Fin Bank.lm1.capacity) (data : WordBus) (selection : PEWordSelection),
      write.destination = some ⟨.lm1, width, address⟩ → write.data = data →
      write.selection = selection → selection.flags = 0 ∨ selection.flags = BitVec.allOnes 4) :
    (commitParsedMaskedWrites files writes).lm1 target = files.lm1 target ∨
      ∃ write ∈ writes, ∃ (width : PEMemory.Width) (address : Fin Bank.lm1.capacity)
          (index : Fin 4),
        write.destination = some ⟨.lm1, width, address⟩ ∧
          (commitParsedMaskedWrites files writes).lm1 target = write.data index := by
  induction writes generalizing files with
  | nil => exact Or.inl rfl
  | cons write rest ih =>
      rw [commitParsedMaskedWrites_cons]
      have tail := ih (welcomeCommitStep files write)
        (fun item member => whole item (List.mem_cons_of_mem _ member))
      rcases tail with hkeep | ⟨item, member, width, address, index, destination, value⟩
      · rcases cendCommitStep_lm1_old_or_data files write target
            (whole write (by simp)) with hold | ⟨width, address, index, destination, value⟩
        · exact Or.inl (hkeep.trans hold)
        · exact Or.inr ⟨write, by simp, width, address, index, destination,
            hkeep.trans value⟩
      · exact Or.inr ⟨item, List.mem_cons_of_mem _ member, width, address, index,
          destination, value⟩

/-- The commit chain of a list of prepared-write lists (one list per executor
stage of a line). -/
def cendCommitChain (files : IntegerRegisterFiles) :
    List (List PreparedParsedMaskedWrite) → IntegerRegisterFiles
  | [] => files
  | writes :: rest => cendCommitChain (commitParsedMaskedWrites files writes) rest

/-- **No mixing along a chain of whole-word commits.**  A line's LM1 word after
the commit chain of its stages is the initial word or **one data word** of one
of the committed lists; whole-word masks never assemble a word from two
different data words. -/
theorem cendCommitChain_lm1_old_or_data (files : IntegerRegisterFiles)
    (stages : List (List PreparedParsedMaskedWrite)) (target : Fin Bank.lm1.capacity)
    (whole : ∀ stage ∈ stages, ∀ write ∈ stage, ∀ (width : PEMemory.Width)
        (address : Fin Bank.lm1.capacity) (data : WordBus) (selection : PEWordSelection),
      write.destination = some ⟨.lm1, width, address⟩ → write.data = data →
      write.selection = selection → selection.flags = 0 ∨ selection.flags = BitVec.allOnes 4) :
    (cendCommitChain files stages).lm1 target = files.lm1 target ∨
      ∃ stage ∈ stages, ∃ write ∈ stage, ∃ (width : PEMemory.Width)
          (address : Fin Bank.lm1.capacity) (index : Fin 4),
        write.destination = some ⟨.lm1, width, address⟩ ∧
          (cendCommitChain files stages).lm1 target = write.data index := by
  induction stages generalizing files with
  | nil => exact Or.inl rfl
  | cons writes rest ih =>
      rw [show cendCommitChain files (writes :: rest) =
          cendCommitChain (commitParsedMaskedWrites files writes) rest from rfl]
      have tail := ih (commitParsedMaskedWrites files writes)
        (fun stage member => whole stage (List.mem_cons_of_mem _ member))
      rcases tail with hlast | ⟨stage, member, write, inStage, width, address, index, dest, value⟩
      · rcases cendCommitParsedMaskedWrites_lm1_old_or_data files writes target
            (whole writes (by simp)) with hold | ⟨write, member, width, address, index, dest, value⟩
        · exact Or.inl (hlast.trans hold)
        · exact Or.inr ⟨writes, by simp, write, member, width, address, index, dest,
            hlast.trans value⟩
      · exact Or.inr ⟨stage, List.mem_cons_of_mem _ member, write, inStage, width, address,
          index, dest, value⟩

/-! ## 6. The residual over the first line's handoff and the assembly

The pairs closed in §2 have a framing second line.  What is left is a second
`.pe` line with a live row: it reads the state the first line left (registers,
forwarding payloads, matrix store) and commits one more datapath value at LM1
word `0`.  That is exactly the two-line value obligation. -/

/-- **The residual over the first line's handoff.**  For every first line (any
kind) and every `.pe` second line with at least one non-`.noforward` row, the
program `[first, .pe second]` is not correct.  The first line's handoff is
unconstrained here on purpose: the value argument of the report §1.3 has to
bound it, and this is the named statement that remains. -/
def CendTwoLiveSecondLinesRefuted : Prop :=
  ∀ (first : InstructionLine) (second : List NormalizedExpr),
    InstructionLine.cost first = 1 → ¬ CendAllNoForward second →
    ¬ ProofsLean.Correct cendSealedMachine cendSpec
      ([first, InstructionLine.pe second] : ProofsLean.Program cendSealedMachine)

/-- The residual is a special case of the two-line obligation. -/
theorem cendTwoLiveSecondLines_of_twoLines (twoLines : CendTwoLinesRefuted) :
    CendTwoLiveSecondLinesRefuted := by
  intro first second firstCost _ correct
  exact twoLines first (.pe second) firstCost rfl correct

/-- **`CendTwoLinesRefuted` from the live-second-`.pe` residual.**  The only
second-line kinds are `.pe`, `.mv` and `.nop` (§1); `.mv`/`.nop` frame the
register file and are closed by §2, and a `.pe` line with only `.noforward` rows
frames it as well.  The remaining `.pe` rows are the residual. -/
theorem cendTwoLinesRefuted_of_liveSecondLines (peLines : CendPELinesRefuted)
    (live : CendTwoLiveSecondLinesRefuted) : CendTwoLinesRefuted := by
  intro first second firstCost secondCost correct
  rcases cendCostOne_cases second secondCost with ⟨expressions, rfl⟩ |
    ⟨transfer, rfl⟩ | ⟨wait, rfl⟩
  · by_cases noforward : CendAllNoForward expressions
    · exact cendTwoLines_second_frame_not_correct peLines first (.pe expressions)
        (cendLineFrames_noforward expressions noforward) correct
    · exact live first expressions firstCost noforward correct
  · exact cendTwoLines_second_frame_not_correct peLines first (.mv transfer)
      (cendLineFrames_mv transfer) correct
  · exact cendTwoLines_second_frame_not_correct peLines first
      (.nop ⟨1, by decide⟩ wait) (cendLineFrames_nop _ _) correct

/-- **The residual is exactly the two-line obligation**, given the one-line
residual: §2 closes every framing second line, and the residual is the rest. -/
theorem cendTwoLinesRefuted_iff_liveSecondLines (peLines : CendPELinesRefuted) :
    CendTwoLinesRefuted ↔ CendTwoLiveSecondLinesRefuted :=
  ⟨cendTwoLiveSecondLines_of_twoLines, cendTwoLinesRefuted_of_liveSecondLines peLines⟩

/-- **The bound three is exactly the live-second-line value obligation**, given
the one-line residual. -/
theorem cendLowerBound_three_iff_liveSecondLines (peLines : CendPELinesRefuted) :
    ProofsLean.LowerBound cendSealedMachine cendSpec 3 ↔ CendTwoLiveSecondLinesRefuted := by
  rw [cendLowerBound_three_iff_residuals]
  exact ⟨fun residual => cendTwoLiveSecondLines_of_twoLines residual.2,
    fun live => ⟨peLines, cendTwoLinesRefuted_of_liveSecondLines peLines live⟩⟩

/-! ## 7. The bound at three and optimality -/

/-- **`LowerBound cendSealedMachine cendSpec 3`** from the one-line residual and
the live-second-line residual. -/
theorem cendLowerBound_three_of_liveSecondLines (peLines : CendPELinesRefuted)
    (live : CendTwoLiveSecondLinesRefuted) :
    ProofsLean.LowerBound cendSealedMachine cendSpec 3 :=
  cendLowerBound_three_of_residuals peLines
    (cendTwoLinesRefuted_of_liveSecondLines peLines live)

/-- A program of unit-cost lines has score equal to its length. -/
theorem cend_score_of_unitCost (program : ProofsLean.Program cendSealedMachine)
    (unitCost : ∀ line ∈ program, cendSealedMachine.lineCost line = 1) :
    ProofsLean.score cendSealedMachine program = program.length := by
  induction program with
  | nil => rfl
  | cons line rest ih =>
      have head : cendSealedMachine.lineCost line = 1 := unitCost line (by simp)
      have tail : ∀ item ∈ rest, cendSealedMachine.lineCost item = 1 :=
        fun item member => unitCost item (by simp [member])
      simp only [ProofsLean.score, List.length_cons]
      rw [head, ih tail]
      omega

/-- **The official answer's three-word score.**  The judge record
`problems/challenge/12.convert-endian/answer.json` is `"lines": 3` with
`score=3 j=3 m=0 bytes=102`; a Lean answer of three unit-cost lines therefore has
score three. -/
theorem cendAnswer_score_three (answer : ProofsLean.Program cendSealedMachine)
    (lengthThree : answer.length = 3)
    (unitCost : ∀ line ∈ answer, cendSealedMachine.lineCost line = 1) :
    ProofsLean.score cendSealedMachine answer = 3 := by
  rw [cend_score_of_unitCost answer unitCost, lengthThree]

/-- **`Optimal` from the answer's correctness and word count.**  The official
three-line answer has not been connected to `executeNormalizedLine` in this
module, so its `Correct` is an explicit hypothesis; the lower bound is the
theorem above.  With `lengthThree = 3` this is exactly
`Optimal cendSealedMachine cendSpec cendAnswer` for the judge-accepted answer. -/
theorem cendOptimal_of_liveSecondLines (peLines : CendPELinesRefuted)
    (live : CendTwoLiveSecondLinesRefuted)
    (answer : ProofsLean.Program cendSealedMachine)
    (correct : ProofsLean.Correct cendSealedMachine cendSpec answer)
    (lengthThree : answer.length = 3)
    (unitCost : ∀ line ∈ answer, cendSealedMachine.lineCost line = 1) :
    ProofsLean.Optimal cendSealedMachine cendSpec answer :=
  ⟨correct, by
    rw [cendAnswer_score_three answer lengthThree unitCost]
    exact cendLowerBound_three_of_liveSecondLines peLines live⟩

end ProofsLean.MNCore

-- End of module: no sorry, no admit, no native_decide, no new axioms.
#print axioms ProofsLean.MNCore.cendTwoLinesRefuted_of_liveSecondLines
#print axioms ProofsLean.MNCore.cendLowerBound_three_of_liveSecondLines
#print axioms ProofsLean.MNCore.cendOptimal_of_liveSecondLines
#print axioms ProofsLean.MNCore.cendCommitChain_lm1_old_or_data
#print axioms ProofsLean.MNCore.cendTwoLinesRefuted_iff_liveSecondLines
#print axioms ProofsLean.MNCore.cendLowerBound_three_iff_liveSecondLines
