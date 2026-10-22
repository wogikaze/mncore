import ProofsLean.WelcomeStageCommit

/-! # Line-level stage commits with the executor's own write list

`executeIntegerProducerLineAtPECore_peRegisters_commit_float` (in
`WelcomeStageCommit.lean`) is stated at an **arbitrary** `State`, but its write
list is existentially quantified:

```
∃ writes, next.peRegisters pe = commitParsedMaskedWrites (state.peRegisters pe) writes
```

An existential list cannot bound the write *destinations*, so it cannot be used
to transfer a write shape (narrow windows, copied `.double` words, ...) from one
input to another.  This module pins the executor's own list:

* `parsedIntegerMatrixReadLineFourCycleStep_commit_eq` — the four-cycle integer
  stage commits exactly the first component of its preparation result;
* `executeIntegerProducerLineAtPECore_peRegisters_commit_list` — a successful
  per-PE core step at **any** state commits `prepared.1 ++ floatWrites`, where
  `prepared` is the integer stage's own `prepareParsedIntegerMatrixReadLineCycles`
  result (named by an equation) and `floatWrites` is the float-MAU stage's list;
* `executeIntegerProducerLineAtPECore_peRegisters_commit_list_noforward` — when
  the line has no supported float-MAU producer the float stage is the identity,
  so the committed list is exactly the integer stage's list (no existential left);
* `prepareParsedIntegerMatrixReadLineExpression_plain` — for a plain
  `.alu`/`.zero`/`.immediate` row the integer stage's expression preparation is
  **definitionally** `prepareParsedIntegerALUExprCycles` followed by
  `parsedIntegerALUBarUpdates`.  Combined with
  `ProofsLean/PlainALUDestination.lean` this gives the destinations of every
  plain row at any state.

Nothing here mentions a machine, a problem, an input or a state predicate: the
only state assumption is the success of the step, so this module can be imported
by any problem whose one-line argument needs the executor's write list at a
non-zero input.

No `sorry`, no `admit`, no `native_decide`, no new axioms.
-/

namespace ProofsLean.MNCore

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

open Issue
open PEMemory

/-! ## 1. The four-cycle integer stage commits its own preparation list -/

/-- **The integer stage's commit, with the list pinned.**  If the preparation of
the four integer cycles returns `prepared`, the stage's register file is exactly
the commit of `prepared.1`. -/
theorem parsedIntegerMatrixReadLineFourCycleStep_commit_eq
    (files : IntegerRegisterFiles) (slots : ProofsLean.MNCore.Forwarding.Slots)
    (store : ParsedMatrixReadStore) (expressions : List ParsedExpr)
    (control : ParsedMaskExecutionControl) (reduced : Bool)
    (prepared : List PreparedParsedMaskedWrite × ProofsLean.MNCore.Forwarding.Slots ×
      List (Bool × BitVec 12))
    (preparedEq : prepareParsedIntegerMatrixReadLineCycles files slots store expressions
      control reduced = .ok prepared) :
    parsedIntegerMatrixReadLineFourCycleStep files slots store expressions control reduced =
      .ok (commitParsedMaskedWrites files prepared.1, prepared.2.1, prepared.2.2) := by
  unfold parsedIntegerMatrixReadLineFourCycleStep
  rw [preparedEq]

/-! ## 2. The per-PE core step's commit, with the integer stage's list pinned -/

/-- **The per-PE core step commits `prepared.1 ++ floatWrites`**, where
`prepared` is the integer stage's own `prepareParsedIntegerMatrixReadLineCycles`
result (fixed by the equation in the conclusion) and `floatWrites` is the
float-MAU stage's write list.  The state is arbitrary; the only assumption is
that the step succeeds. -/
theorem executeIntegerProducerLineAtPECore_peRegisters_commit_list
    (expressions : List ParsedExpr) (state next : State) (pe : PEId)
    (executed : executeIntegerProducerLineAtPECore expressions state pe = .ok next) :
    ∃ (prepared : List PreparedParsedMaskedWrite × ProofsLean.MNCore.Forwarding.Slots ×
        List (Bool × BitVec 12))
      (floatWrites : List PreparedParsedMaskedWrite),
      prepareParsedIntegerMatrixReadLineCycles (state.peRegisters pe)
          (stateForwardingSlots state pe)
          (state.matrixRegisters (ParsedIntegerContext.ofLinearIndex pe).group
            (ParsedIntegerContext.ofLinearIndex pe).l2b
            (ParsedIntegerContext.ofLinearIndex pe).l1b)
          (expressions.filter parsedExprIsIntegerMatrixReadStageInput)
          { directive := state.maskDirective
            context :=
              { (ParsedIntegerContext.ofLinearIndex pe) with
                bar0 := (state.peContext pe).bar0
                bar1 := (state.peContext pe).bar1
                tWord := (state.peContext pe).tWord }
            elapsedWords := state.hazardClock } false = .ok prepared ∧
      next.peRegisters pe =
        commitParsedMaskedWrites (state.peRegisters pe) (prepared.1 ++ floatWrites) := by
  unfold executeIntegerProducerLineAtPECore parsedIntegerMatrixReadLineFourCycleStep at executed
  dsimp only at executed
  cases preparedEq : prepareParsedIntegerMatrixReadLineCycles (state.peRegisters pe)
      (stateForwardingSlots state pe)
      (state.matrixRegisters (ParsedIntegerContext.ofLinearIndex pe).group
        (ParsedIntegerContext.ofLinearIndex pe).l2b
        (ParsedIntegerContext.ofLinearIndex pe).l1b)
      (expressions.filter parsedExprIsIntegerMatrixReadStageInput)
      { directive := state.maskDirective
        context :=
          { (ParsedIntegerContext.ofLinearIndex pe) with
            bar0 := (state.peContext pe).bar0
            bar1 := (state.peContext pe).bar1
            tWord := (state.peContext pe).tWord }
        elapsedWords := state.hazardClock } false with
  | failure =>
      simp only [preparedEq] at executed
      simp at executed
  | unknown =>
      simp only [preparedEq] at executed
      simp at executed
  | ok prepared =>
      obtain ⟨intWrites, intSlots, intBars⟩ := prepared
      simp only [preparedEq] at executed
      cases floatEq : executeParsedFloatMAUsAtPE (state.peRegisters pe)
          (commitParsedMaskedWrites (state.peRegisters pe) intWrites)
          (stateForwardingSlots state pe)
          { (ParsedIntegerContext.ofLinearIndex pe) with
            bar0 := (state.peContext pe).bar0
            bar1 := (state.peContext pe).bar1
            tWord := (state.peContext pe).tWord }
          expressions state.maskDirective (expressions.any parsedExprHasSingleLineWriteMask) with
      | failure =>
          simp only [floatEq] at executed
          simp at executed
      | unknown =>
          simp only [floatEq] at executed
          simp at executed
      | ok floatResult =>
          obtain ⟨floatFiles, floatBar0, floatBar1, floatOutputs, hasMAUProducer⟩ := floatResult
          obtain ⟨floatWrites, floatCommitted⟩ :=
            executeParsedFloatMAUsAtPE_commit (state.peRegisters pe)
              (commitParsedMaskedWrites (state.peRegisters pe) intWrites)
              (stateForwardingSlots state pe)
              { (ParsedIntegerContext.ofLinearIndex pe) with
                bar0 := (state.peContext pe).bar0
                bar1 := (state.peContext pe).bar1
                tWord := (state.peContext pe).tWord }
              expressions state.maskDirective (expressions.any parsedExprHasSingleLineWriteMask)
              floatFiles floatBar0 floatBar1 floatOutputs hasMAUProducer floatEq
          simp only [floatEq] at executed
          split at executed
          · simp at executed
          · simp at executed
          · refine ⟨(intWrites, intSlots, intBars), floatWrites, rfl, ?_⟩
            simp only [StepResult.ok.injEq] at executed
            subst executed
            simpa [commitParsedMaskedWrites_append] using floatCommitted

/-! ## 3. The float-free case: no existential left -/

/-- **The per-PE core step's commit with no float-MAU producer.**  The committed
list is exactly the integer stage's own preparation list. -/
theorem executeIntegerProducerLineAtPECore_peRegisters_commit_list_noforward
    (expressions : List ParsedExpr) (state next : State) (pe : PEId)
    (floatEmpty : expressions.filter parsedExprIsSupportedFloatMAUProducer = [])
    (executed : executeIntegerProducerLineAtPECore expressions state pe = .ok next) :
    ∃ prepared : List PreparedParsedMaskedWrite × ProofsLean.MNCore.Forwarding.Slots ×
        List (Bool × BitVec 12),
      prepareParsedIntegerMatrixReadLineCycles (state.peRegisters pe)
          (stateForwardingSlots state pe)
          (state.matrixRegisters (ParsedIntegerContext.ofLinearIndex pe).group
            (ParsedIntegerContext.ofLinearIndex pe).l2b
            (ParsedIntegerContext.ofLinearIndex pe).l1b)
          (expressions.filter parsedExprIsIntegerMatrixReadStageInput)
          { directive := state.maskDirective
            context :=
              { (ParsedIntegerContext.ofLinearIndex pe) with
                bar0 := (state.peContext pe).bar0
                bar1 := (state.peContext pe).bar1
                tWord := (state.peContext pe).tWord }
            elapsedWords := state.hazardClock } false = .ok prepared ∧
      next.peRegisters pe =
        commitParsedMaskedWrites (state.peRegisters pe) prepared.1 := by
  unfold executeIntegerProducerLineAtPECore parsedIntegerMatrixReadLineFourCycleStep at executed
  dsimp only at executed
  cases preparedEq : prepareParsedIntegerMatrixReadLineCycles (state.peRegisters pe)
      (stateForwardingSlots state pe)
      (state.matrixRegisters (ParsedIntegerContext.ofLinearIndex pe).group
        (ParsedIntegerContext.ofLinearIndex pe).l2b
        (ParsedIntegerContext.ofLinearIndex pe).l1b)
      (expressions.filter parsedExprIsIntegerMatrixReadStageInput)
      { directive := state.maskDirective
        context :=
          { (ParsedIntegerContext.ofLinearIndex pe) with
            bar0 := (state.peContext pe).bar0
            bar1 := (state.peContext pe).bar1
            tWord := (state.peContext pe).tWord }
        elapsedWords := state.hazardClock } false with
  | failure =>
      simp only [preparedEq] at executed
      simp at executed
  | unknown =>
      simp only [preparedEq] at executed
      simp at executed
  | ok prepared =>
      obtain ⟨intWrites, intSlots, intBars⟩ := prepared
      simp only [preparedEq] at executed
      rw [executeParsedFloatMAUsAtPE_noforward (floatEmpty := floatEmpty)] at executed
      dsimp only at executed
      simp only [updateSupportedPELineForwarding] at executed
      split at executed
      · simp at executed
      · simp at executed
      · refine ⟨(intWrites, intSlots, intBars), rfl, ?_⟩
        simp only [StepResult.ok.injEq] at executed
        subst executed
        simp

/-! ## 4. Plain rows: the integer stage is the plain ALU cycle preparation -/

/-- **A plain row's preparation is the plain ALU cycle preparation.**  For an
`.alu` / `.zero` / `.immediate` row, `prepareParsedIntegerMatrixReadLineExpression`
is *definitionally* `prepareParsedIntegerALUExprCycles` followed by the row's BAR
updates.  No state, machine or problem appears. -/
theorem prepareParsedIntegerMatrixReadLineExpression_plain
    (files : IntegerRegisterFiles) (oldSlots nextSlots : ProofsLean.MNCore.Forwarding.Slots)
    (store : ParsedMatrixReadStore) (expression : ParsedExpr)
    (control : ParsedMaskExecutionControl) (hasSingleLineMask noForward reduced : Bool)
    (plain : (∃ name precision unsigned arg, expression.op = .alu name precision unsigned arg) ∨
      expression.op = .zero ∨ ∃ value unsigned, expression.op = .immediate value unsigned) :
    prepareParsedIntegerMatrixReadLineExpression files oldSlots nextSlots store expression
        control hasSingleLineMask noForward reduced =
      match prepareParsedIntegerALUExprCycles files oldSlots nextSlots expression control
          hasSingleLineMask noForward reduced with
      | .failure => .failure
      | .unknown => .unknown
      | .ok (writes, outputSlots) =>
          .ok (writes, outputSlots, parsedIntegerALUBarUpdates expression writes) := by
  rcases plain with ⟨name, precision, unsigned, arg, hop⟩ | hop | ⟨value, unsigned, hop⟩
  all_goals
    simp only [prepareParsedIntegerMatrixReadLineExpression, hop]
    cases preparedCycle : prepareParsedIntegerALUExprCycles files oldSlots nextSlots expression
      control hasSingleLineMask noForward reduced with
    | failure => rfl
    | unknown => rfl
    | ok prepared =>
        obtain ⟨writes, outputSlots⟩ := prepared
        rfl

end ProofsLean.MNCore

-- End of module: no sorry, no admit, no native_decide, no new axioms.
