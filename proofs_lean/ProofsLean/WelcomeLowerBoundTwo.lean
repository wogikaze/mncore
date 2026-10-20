import ProofsLean.WelcomeLowerBound

/-! # Bound two for the sealed Welcome machine: every non-`.pe` short line

`WelcomeLowerBound.lean` reduces `LowerBound welcomeSealedMachine welcomeSpec 2`
to the statement that **every** line of cost below two is refuted:

```
∀ line : InstructionLine, InstructionLine.cost line < 2 →
  ¬ Correct welcomeSealedMachine welcomeSpec [line]
```

This module proves that statement for every line *except* the `.pe` lines that
pass the issue checker, are not all-`noforward` rows and are not a single
Welcome `iinc` row. The three constructors of `InstructionLine` are handled as
follows.

* `.nop count wait` with `count < 2`: a stuck step (`check` failure or an
  incomplete wait tag) refutes the line outright; a successful step only
  advances `hazardClock` (`executeIntegerProducerInstructionLine_nop`,
  `executeIntegerProducerInstructionLine_wait_completed`), so the observed PE's
  register file is unchanged. LM1 word 0 therefore stays zero while the
  all-zero admissible input demands one.
* `.mv transfer`: the transfer either fails/unknowns, or rewrites only
  `pendingMv`, `mvCompletedTags`, `blockMemory` and the clock. LM1 is untouched.
* `.pe expressions`: four syntactic conditions are proved to refute the line
  (rejected issue checker, pending `wait` tag, Rust-unsupported ALU, a
  non-supported producer), and the all-`noforward` class is refuted through
  `executeNormalizedLine_pe_peRegisters_noforward` of `FrameStep.lean`. That
  class includes `[]`, which is vacuously all-`noforward`.

The predicate `WelcomePEUnrefuted` names the **exact remaining gap**: a `.pe`
line that passes all four syntactic checks, is not all-`.noforward` and is not
a single Welcome `iinc` row. `welcomeLowerBound_two_of_unrefuted` proves the
lower bound from a refutation of that class, and
`welcomeLowerBound_two_iff_unrefuted` shows that this is an equivalent
restatement of the bound, not a weakening of it. The class is inhabited
(`welcomePEUnrefuted_inhabited`), so the hypothesis is not vacuous.

The value argument for the remaining class is **not** formalised here. It is
expected to need the following two ingredients (neither is proved in this
module, and the informal statement below is not a Lean claim):

1. by `writesUnique` in `LegalParsedLine`, at most one expression of a
   successful line writes PE bank LM1;
2. with the all-zero input, that single expression cannot leave all sixteen
   LM1 words equal to one: a `.word`/`.long` destination touches at most eight
   words (four cycles, one or two words per cycle), and a `.double`
   destination writes its data words 2 and 3 from the raw source bus, which is
   zero at the initial state.

Consequently neither `LowerBound welcomeSealedMachine welcomeSpec 2` nor
`Optimal welcomeSealedMachine welcomeSpec welcomeAnswer` is claimed by this
module.

In terms of the `ParsedOp` constructors, the refuted `.pe` rows are: any row
with a `wait` tag (pending at the initial state), any `.noforward` row, and any
row rejected by the issue checker or outside the supported-producer set. The
open class may therefore contain arbitrary `.alu` rows other than the single
Welcome shape, `.immediate`, `.zero`, `.matrixRead`, `.mau`, `.matrixWrite`,
`.l1bm` and `.l2bm` rows, alone or in supported combinations that pass the
issue checker without a second LM1 writer.
-/

namespace ProofsLean.MNCore

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

open Issue
open PEMemory

/-! ## The all-zero admissible input and the two refutation patterns -/

/-- The all-zero input word vector. Its sixteen words are all within the
admissible range `0..50`. -/
def welcomeZeroWords : ProofsLean.MNCore.PlusOne.Words := fun _ => 0

theorem welcomeZeroWords_admissible : welcomeSpec.admissible welcomeZeroWords := by
  intro i
  simp [welcomeZeroWords]

/-- The initial state of the specification is `welcomeInitialState`. -/
@[simp] theorem welcomeSpec_initial (input : ProofsLean.MNCore.PlusOne.Words) :
    welcomeSpec.initial input = welcomeInitialState input := rfl

/-- A one-line program executes exactly one sealed step. -/
theorem welcomeSealed_step_some {line : InstructionLine} {state next : State}
    (h : executeNormalizedLine line.toNormalizedLine state = .ok next) :
    welcomeSealedMachine.step line state = some next := by
  simp [welcomeSealedMachine, h]

/-- A successful sealed step is an `.ok` value transition. -/
theorem welcomeSealed_step_ok {line : InstructionLine} {state next : State}
    (h : welcomeSealedMachine.step line state = some next) :
    executeNormalizedLine line.toNormalizedLine state = .ok next := by
  cases e : executeNormalizedLine line.toNormalizedLine state with
  | ok s => simpa [welcomeSealedMachine, e] using h
  | failure => simp [welcomeSealedMachine, e] at h
  | unknown => simp [welcomeSealedMachine, e] at h

/-- A `.failure` value transition leaves the sealed step stuck. -/
theorem welcomeSealed_step_failure {line : InstructionLine} {state : State}
    (h : executeNormalizedLine line.toNormalizedLine state = .failure) :
    welcomeSealedMachine.step line state = none := by
  simp [welcomeSealedMachine, h]

/-- An `.unknown` value transition leaves the sealed step stuck. -/
theorem welcomeSealed_step_unknown {line : InstructionLine} {state : State}
    (h : executeNormalizedLine line.toNormalizedLine state = .unknown) :
    welcomeSealedMachine.step line state = none := by
  simp [welcomeSealedMachine, h]

/-- A line whose step is stuck cannot be the only line of a correct program. -/
theorem welcome_not_correct_of_step_none (line : InstructionLine)
    (stuck : welcomeSealedMachine.step line (welcomeInitialState welcomeZeroWords) = none) :
    ¬ ProofsLean.Correct welcomeSealedMachine welcomeSpec
      (([line] : List InstructionLine)) := by
  intro correct
  obtain ⟨result, executed, _⟩ := correct.2 welcomeZeroWords welcomeZeroWords_admissible
  rw [welcomeSpec_initial] at executed
  have stepResult : welcomeSealedMachine.step line (welcomeInitialState welcomeZeroWords) =
      some result := by
    simpa [ProofsLean.execute] using executed
  rw [stuck] at stepResult
  simp at stepResult

/-- A line whose successful step leaves the observed PE's register file at the
initial one falsifies the specification on the all-zero input: spec word 0 must
become one, but it starts at zero. -/
theorem welcome_not_correct_of_step_frame (line : InstructionLine) (next : State)
    (step : welcomeSealedMachine.step line (welcomeInitialState welcomeZeroWords) = some next)
    (frame : next.peRegisters = (welcomeInitialState welcomeZeroWords).peRegisters) :
    ¬ ProofsLean.Correct welcomeSealedMachine welcomeSpec
      (([line] : List InstructionLine)) := by
  intro correct
  obtain ⟨result, executed, post⟩ := correct.2 welcomeZeroWords welcomeZeroWords_admissible
  rw [welcomeSpec_initial] at executed
  simp only [welcomeSpec] at post
  have stepResult : welcomeSealedMachine.step line (welcomeInitialState welcomeZeroWords) =
      some result := by
    simpa [ProofsLean.execute] using executed
  rw [step] at stepResult
  have resultEq : result = next := (Option.some.inj stepResult).symm
  subst result
  have word := post ⟨0, by decide⟩
  rw [frame] at word
  simp [welcomeInitialState, welcomeInitialPERegisters,
    zeroInitialPERegisterFiles, welcomeZeroWords] at word

/-! ## `nop` lines -/

/-- A successful `.nop` step only advances the hazard clock. -/
theorem executeIntegerProducerInstructionLine_nop_peRegisters
    (count : {n : Nat // 0 < n}) (wait : Option (Fin 256)) (state next : State)
    (executed : executeIntegerProducerInstructionLine (.nop count wait) state = .ok next) :
    next.peRegisters = state.peRegisters := by
  by_cases accepted : checkParsedTopLine (.nop count.val wait) = true
  · cases wait with
    | none =>
        rw [executeIntegerProducerInstructionLine_nop count none state accepted rfl] at executed
        cases executed
        rfl
    | some tag =>
        by_cases completed : state.mvCompletedTags tag = true
        · rw [executeIntegerProducerInstructionLine_wait_completed count tag state accepted
            completed] at executed
          cases executed
          rfl
        · have pending : state.mvCompletedTags tag = false := by
            cases h : state.mvCompletedTags tag <;> simp_all
          rw [executeIntegerProducerInstructionLine_wait_pending_unknown count tag state
            accepted pending] at executed
          simp at executed
  · have rejected : checkParsedTopLine (.nop count.val wait) = false := by
      cases h : checkParsedTopLine (.nop count.val wait) <;> simp_all
    have failure : executeIntegerProducerInstructionLine (.nop count wait) state = .failure := by
      simp [executeIntegerProducerInstructionLine, InstructionLine.toParsed, rejected]
    rw [failure] at executed
    simp at executed

/-- A successful normalized `.nop` step only advances the hazard clock. -/
theorem executeNormalizedLine_nop_peRegisters (count : Nat) (wait : Option (Fin 256))
    (state next : State)
    (executed : executeNormalizedLine (.nop count wait) state = .ok next) :
    next.peRegisters = state.peRegisters := by
  cases count with
  | zero => simp [executeNormalizedLine, NormalizedLine.toInstruction?] at executed
  | succ count =>
      simp only [executeNormalizedLine, NormalizedLine.toInstruction?] at executed
      exact executeIntegerProducerInstructionLine_nop_peRegisters ⟨count + 1, Nat.succ_pos count⟩
        wait state next executed

/-- **`.nop` case.** No single `nop` line of cost below two is correct. -/
theorem welcomeNop_not_correct (count : {n : Nat // 0 < n}) (wait : Option (Fin 256))
    (_short : InstructionLine.cost (.nop count wait) < 2) :
    ¬ ProofsLean.Correct welcomeSealedMachine welcomeSpec
      (([InstructionLine.nop count wait] : List InstructionLine)) := by
  cases step : welcomeSealedMachine.step (InstructionLine.nop count wait)
      (welcomeInitialState welcomeZeroWords) with
  | none => exact welcome_not_correct_of_step_none _ step
  | some next =>
      apply welcome_not_correct_of_step_frame _ next step
      have executed := welcomeSealed_step_ok step
      exact executeNormalizedLine_nop_peRegisters count.val wait _ next executed

/-! ## `mv` lines -/

/-- A successful MV transfer leaves every PE register file untouched. -/
theorem executeParsedMvMemory_peRegisters (state : State) (transfer : ParsedMv) (next : State)
    (executed : executeParsedMvMemory state transfer = .ok next) :
    next.peRegisters = state.peRegisters := by
  unfold executeParsedMvMemory at executed
  split at executed
  · cases executed
  · split at executed
    · cases executed
      rfl
    · cases executed
      rfl

/-- A successful `.mv` value transition leaves every PE register file untouched. -/
theorem executeIntegerProducerInstructionLine_mv_peRegisters
    (transfer : NormalizedMv) (state next : State)
    (executed : executeIntegerProducerInstructionLine (.mv transfer) state = .ok next) :
    next.peRegisters = state.peRegisters := by
  by_cases isNop : transfer.kind = .nop
  · rw [executeIntegerProducerInstructionLine_mvnop transfer state isNop rfl] at executed
    cases executed
    rfl
  · have accepted : checkParsedTopLine (InstructionLine.mv transfer).toParsed = true := rfl
    have hbeq : (transfer.kind == .nop) = false := by
      cases h : transfer.kind == .nop with
      | false => rfl
      | true => exact absurd (beq_iff_eq.mp h) isNop
    cases memoryResult : executeParsedMvMemory state transfer.toParsed with
    | failure =>
        have stepEq : executeIntegerProducerInstructionLine (.mv transfer) state = .failure := by
          simp [executeIntegerProducerInstructionLine, accepted, hbeq, memoryResult]
        rw [stepEq] at executed
        simp at executed
    | unknown =>
        exact (executeParsedMvMemory_never_unknown state transfer.toParsed memoryResult).elim
    | ok middle =>
        have stepEq : executeIntegerProducerInstructionLine (.mv transfer) state =
            .ok { middle with hazardClock := middle.hazardClock + 1 } :=
          executeIntegerProducerInstructionLine_mv_transfer_success transfer state middle rfl
            isNop memoryResult
        rw [stepEq] at executed
        cases executed
        exact executeParsedMvMemory_peRegisters state transfer.toParsed middle memoryResult

/-- A successful normalized `.mv` step only advances the hazard clock or the
block-memory bookkeeping. -/
theorem executeNormalizedLine_mv_peRegisters (transfer : NormalizedMv) (state next : State)
    (executed : executeNormalizedLine (.mv transfer) state = .ok next) :
    next.peRegisters = state.peRegisters := by
  simp only [executeNormalizedLine, NormalizedLine.toInstruction?] at executed
  exact executeIntegerProducerInstructionLine_mv_peRegisters transfer state next executed

/-- **`.mv` case.** No single MV line is correct. -/
theorem welcomeMv_not_correct (transfer : NormalizedMv) :
    ¬ ProofsLean.Correct welcomeSealedMachine welcomeSpec
      (([InstructionLine.mv transfer] : List InstructionLine)) := by
  cases step : welcomeSealedMachine.step (InstructionLine.mv transfer)
      (welcomeInitialState welcomeZeroWords) with
  | none => exact welcome_not_correct_of_step_none _ step
  | some next =>
      apply welcome_not_correct_of_step_frame _ next step
      have executed := welcomeSealed_step_ok step
      exact executeNormalizedLine_mv_peRegisters transfer _ next executed

/-! ## `.pe` lines: the syntactic rejection cases -/

/-- A `.pe` line rejected by the issue checker fails before any state change. -/
theorem executeNormalizedLine_pe_checkFalse (expressions : List NormalizedExpr) (state : State)
    (rejected : checkParsedTopLine (InstructionLine.pe expressions).toParsed = false) :
    executeNormalizedLine (.pe expressions) state = .failure := by
  simp [executeNormalizedLine, NormalizedLine.toInstruction?,
    executeIntegerProducerInstructionLine, rejected]

/-- A `.pe` line with a pending `wait` tag is epistemically unknown. -/
theorem executeNormalizedLine_pe_waitPending (expressions : List NormalizedExpr) (state : State)
    (accepted : checkParsedTopLine (InstructionLine.pe expressions).toParsed = true)
    (pending : (expressions.map NormalizedExpr.toParsed).any (parsedExprWaitPending state) = true) :
    executeNormalizedLine (.pe expressions) state = .unknown := by
  simp [executeNormalizedLine, NormalizedLine.toInstruction?,
    executeIntegerProducerInstructionLine, accepted, pending]

/-- A `.pe` line containing a Rust-unsupported ALU row fails. -/
theorem executeNormalizedLine_pe_unsupported (expressions : List NormalizedExpr) (state : State)
    (accepted : checkParsedTopLine (InstructionLine.pe expressions).toParsed = true)
    (waitsComplete : (expressions.map NormalizedExpr.toParsed).any
      (parsedExprWaitPending state) = false)
    (unsupported : (expressions.map NormalizedExpr.toParsed).any
      parsedExprIsUnsupportedRustAlu = true) :
    executeNormalizedLine (.pe expressions) state = .failure := by
  simp [executeNormalizedLine, NormalizedLine.toInstruction?,
    executeIntegerProducerInstructionLine, accepted, waitsComplete, unsupported]

/-- A `.pe` line with a non-supported producer row is epistemically unknown. -/
theorem executeNormalizedLine_pe_notSupported (expressions : List NormalizedExpr) (state : State)
    (accepted : checkParsedTopLine (InstructionLine.pe expressions).toParsed = true)
    (waitsComplete : (expressions.map NormalizedExpr.toParsed).any
      (parsedExprWaitPending state) = false)
    (noUnsupported : (expressions.map NormalizedExpr.toParsed).any
      parsedExprIsUnsupportedRustAlu = false)
    (notSupported : (expressions.map NormalizedExpr.toParsed).all
      parsedExprIsSupportedPELineProducer = false) :
    executeNormalizedLine (.pe expressions) state = .unknown := by
  simp [executeNormalizedLine, NormalizedLine.toInstruction?,
    executeIntegerProducerInstructionLine, accepted, waitsComplete, noUnsupported,
    notSupported]

theorem welcomePe_checkFalse_not_correct (expressions : List NormalizedExpr)
    (rejected : checkParsedTopLine (InstructionLine.pe expressions).toParsed = false) :
    ¬ ProofsLean.Correct welcomeSealedMachine welcomeSpec
      (([InstructionLine.pe expressions] : List InstructionLine)) := by
  apply welcome_not_correct_of_step_none
  exact welcomeSealed_step_failure (executeNormalizedLine_pe_checkFalse expressions
    (welcomeInitialState welcomeZeroWords) rejected)

theorem welcomePe_waitPending_not_correct (expressions : List NormalizedExpr)
    (accepted : checkParsedTopLine (InstructionLine.pe expressions).toParsed = true)
    (pending : (expressions.map NormalizedExpr.toParsed).any
      (parsedExprWaitPending (welcomeInitialState welcomeZeroWords)) = true) :
    ¬ ProofsLean.Correct welcomeSealedMachine welcomeSpec
      (([InstructionLine.pe expressions] : List InstructionLine)) := by
  apply welcome_not_correct_of_step_none
  exact welcomeSealed_step_unknown (executeNormalizedLine_pe_waitPending expressions
    (welcomeInitialState welcomeZeroWords) accepted pending)

theorem welcomePe_unsupported_not_correct (expressions : List NormalizedExpr)
    (accepted : checkParsedTopLine (InstructionLine.pe expressions).toParsed = true)
    (waitsComplete : (expressions.map NormalizedExpr.toParsed).any
      (parsedExprWaitPending (welcomeInitialState welcomeZeroWords)) = false)
    (unsupported : (expressions.map NormalizedExpr.toParsed).any
      parsedExprIsUnsupportedRustAlu = true) :
    ¬ ProofsLean.Correct welcomeSealedMachine welcomeSpec
      (([InstructionLine.pe expressions] : List InstructionLine)) := by
  apply welcome_not_correct_of_step_none
  exact welcomeSealed_step_failure (executeNormalizedLine_pe_unsupported expressions
    (welcomeInitialState welcomeZeroWords) accepted waitsComplete unsupported)

theorem welcomePe_notSupported_not_correct (expressions : List NormalizedExpr)
    (accepted : checkParsedTopLine (InstructionLine.pe expressions).toParsed = true)
    (waitsComplete : (expressions.map NormalizedExpr.toParsed).any
      (parsedExprWaitPending (welcomeInitialState welcomeZeroWords)) = false)
    (noUnsupported : (expressions.map NormalizedExpr.toParsed).any
      parsedExprIsUnsupportedRustAlu = false)
    (notSupported : (expressions.map NormalizedExpr.toParsed).all
      parsedExprIsSupportedPELineProducer = false) :
    ¬ ProofsLean.Correct welcomeSealedMachine welcomeSpec
      (([InstructionLine.pe expressions] : List InstructionLine)) := by
  apply welcome_not_correct_of_step_none
  exact welcomeSealed_step_unknown (executeNormalizedLine_pe_notSupported expressions
    (welcomeInitialState welcomeZeroWords) accepted waitsComplete noUnsupported notSupported)

/-! ## `.pe` lines: the all-`noforward` case -/

/-- Every parsed expression of the line is a `.noforward` row. -/
def WelcomeAllNoForward (expressions : List NormalizedExpr) : Prop :=
  ∀ expression ∈ expressions.map NormalizedExpr.toParsed, expression.op = .noforward

/-- The line consists of exactly one Welcome `iinc` expression. Lines of this
shape are refuted in `WelcomeLowerBound.lean` for **every** base
(`welcomeWelcomeLine_anyBase_not_correct`). -/
def WelcomeSingleWelcomeLine (expressions : List NormalizedExpr) : Prop :=
  ∃ base : Nat, expressions = [welcomeExpr base]

/-- An all-`.noforward` `.pe` line, successful or not, never touches the PE
register files. -/
theorem welcomePe_noforward_not_correct (expressions : List NormalizedExpr)
    (all : WelcomeAllNoForward expressions) :
    ¬ ProofsLean.Correct welcomeSealedMachine welcomeSpec
      (([InstructionLine.pe expressions] : List InstructionLine)) := by
  cases step : welcomeSealedMachine.step (InstructionLine.pe expressions)
      (welcomeInitialState welcomeZeroWords) with
  | none => exact welcome_not_correct_of_step_none _ step
  | some next =>
      apply welcome_not_correct_of_step_frame _ next step
      have executed := welcomeSealed_step_ok step
      exact executeNormalizedLine_pe_peRegisters_noforward expressions
        (welcomeInitialState welcomeZeroWords) next all executed

/-! ## The exact remaining gap -/

/-- The four syntactic conditions under which a `.pe` line is not refuted by
`welcomePe_*_not_correct`: accepted issue checker, no pending wait tag, no
Rust-unsupported ALU row and only supported producers. -/
def WelcomePEAccepted (expressions : List NormalizedExpr) : Prop :=
  checkParsedTopLine (InstructionLine.pe expressions).toParsed = true ∧
  (expressions.map NormalizedExpr.toParsed).any
      (parsedExprWaitPending (welcomeInitialState welcomeZeroWords)) = false ∧
  (expressions.map NormalizedExpr.toParsed).any parsedExprIsUnsupportedRustAlu = false ∧
  (expressions.map NormalizedExpr.toParsed).all parsedExprIsSupportedPELineProducer = true

/-- **The unrefuted case.** A syntactically accepted `.pe` line that is neither
all-`.noforward` nor a single Welcome `iinc` row. This is exactly the class for
which this module does not prove a refutation; the value argument bounding the
LM1 writes of the single `LegalParsedLine.writesUnique`-permitted LM1 writer is
not formalised here. -/
def WelcomePEUnrefuted (expressions : List NormalizedExpr) : Prop :=
  WelcomePEAccepted expressions ∧ ¬ WelcomeAllNoForward expressions ∧
    ¬ WelcomeSingleWelcomeLine expressions

/-! ## The open class is inhabited

The gap predicate is not vacuous: the single-expression line below is
syntactically accepted, is not all-`.noforward`, and is not a Welcome `iinc`
row, so it lies in `WelcomePEUnrefuted`. Its `.long` destination covers only
eight words, so an LM1-coverage argument should refute it, but that argument
is exactly the part of the value analysis that this module leaves open. -/

/-- A normalized immediate expression of value one with an `.lm1` long-word
destination. -/
def welcomeImmediateOneExpr : NormalizedExpr where
  op := .immediate 1 false
  sources := []
  destinations := [plusOneWrite]
  flush := none

theorem welcomeImmediateOne_issueLegal : LegalParsedLine [welcomeImmediateOneExpr.toParsed] := by
  unfold LegalParsedLine projectLine projectFrom ParsedExpr.toIssueExpr
    ParsedExpr.issueGroup ParsedExpr.issueMau ParsedOperand.accesses
    ParsedOperand.matrixUseCount ParsedExpr.hasTurnaround
    ParsedExpr.maskApplications ParsedOperand.writeMask?
    ParsedExpr.maskRegisterWrites ParsedOperand.maskRegisterWrite?
    ParsedExpr.barWrites ParsedOperand.barWriteBank?
    ParsedExpr.writesLbf ParsedExpr.nowriteOutputValid
  simp [welcomeImmediateOneExpr, Legal, idsUnique, groupsUnique, mauCountBounded,
    mauExpressions, mauPrecisionsAgree, matrixWritePairAgrees, matrixRegistersUnique,
    writesUnique, Expr.writeBanks, barWritesExcludeReads, readsAgree, localReadWriteAgree,
    immediateExcludesLm0, zeroFlushUnique, maskWidthsAgree, maskEntriesAgree,
    nowriteOutputsUnique, lbfWritesUnique, maskRegisterWritesUnique, projectFrom,
    NormalizedExpr.toParsed, Issue.plusOneWrite, Issue.plusOneWriteAt,
    Issue.plusOneAccess]

theorem welcomeImmediateOne_check :
    checkParsedTopLine (InstructionLine.pe [welcomeImmediateOneExpr]).toParsed = true := by
  have legal : LegalParsedLine [welcomeImmediateOneExpr.toParsed] :=
    welcomeImmediateOne_issueLegal
  have accepted := parsed_topline_check_complete
    (ParsedLine.pe [welcomeImmediateOneExpr.toParsed]) legal
  simpa [InstructionLine.toParsed] using accepted

/-- **Non-vacuity.** The open case is inhabited, by the constant-one immediate
line. This line is not covered by any theorem of this module or of
`WelcomeLowerBound.lean`. -/
theorem welcomePEUnrefuted_inhabited : WelcomePEUnrefuted [welcomeImmediateOneExpr] := by
  refine ⟨⟨welcomeImmediateOne_check, ?_, ?_, ?_⟩, ?_, ?_⟩
  · simp [welcomeImmediateOneExpr, NormalizedExpr.toParsed, parsedExprWaitPending,
      parsedExprWaitTag?]
  · simp [welcomeImmediateOneExpr, NormalizedExpr.toParsed,
      parsedExprIsUnsupportedRustAlu]
  · simp [welcomeImmediateOneExpr, NormalizedExpr.toParsed,
      parsedExprIsSupportedPELineProducer]
  · intro all
    have h := all welcomeImmediateOneExpr.toParsed (by simp [welcomeImmediateOneExpr])
    simp [welcomeImmediateOneExpr, NormalizedExpr.toParsed] at h
  · intro single
    obtain ⟨base, equal⟩ := single
    have expressionEq : welcomeImmediateOneExpr = welcomeExpr base := by simpa using equal
    have opEq : welcomeImmediateOneExpr.op = (welcomeExpr base).op := by rw [expressionEq]
    simp [welcomeImmediateOneExpr, welcomeExpr_op] at opEq

/-- Every `.pe` line outside `WelcomePEUnrefuted` is refuted. -/
theorem welcomePE_not_correct_of_not_unrefuted (expressions : List NormalizedExpr)
    (open_ : ¬ WelcomePEUnrefuted expressions) :
    ¬ ProofsLean.Correct welcomeSealedMachine welcomeSpec
      (([InstructionLine.pe expressions] : List InstructionLine)) := by
  by_cases accepted : WelcomePEAccepted expressions
  · by_cases allNoforward : WelcomeAllNoForward expressions
    · exact welcomePe_noforward_not_correct expressions allNoforward
    · by_cases singleWelcome : WelcomeSingleWelcomeLine expressions
      · obtain ⟨base, rfl⟩ := singleWelcome
        exact welcomeWelcomeLine_anyBase_not_correct base
      · exact absurd ⟨accepted, allNoforward, singleWelcome⟩ open_
  · by_cases checkTrue : checkParsedTopLine (InstructionLine.pe expressions).toParsed = true
    · by_cases pendingFalse : (expressions.map NormalizedExpr.toParsed).any
          (parsedExprWaitPending (welcomeInitialState welcomeZeroWords)) = false
      · by_cases unsupportedFalse : (expressions.map NormalizedExpr.toParsed).any
            parsedExprIsUnsupportedRustAlu = false
        · by_cases supportedTrue : (expressions.map NormalizedExpr.toParsed).all
              parsedExprIsSupportedPELineProducer = true
          · exact absurd ⟨checkTrue, pendingFalse, unsupportedFalse, supportedTrue⟩ accepted
          · have supportedFalse : (expressions.map NormalizedExpr.toParsed).all
                parsedExprIsSupportedPELineProducer = false := by
              cases h : (expressions.map NormalizedExpr.toParsed).all
                  parsedExprIsSupportedPELineProducer <;> simp_all
            exact welcomePe_notSupported_not_correct expressions checkTrue pendingFalse
              unsupportedFalse supportedFalse
        · have unsupportedTrue : (expressions.map NormalizedExpr.toParsed).any
              parsedExprIsUnsupportedRustAlu = true := by
            cases h : (expressions.map NormalizedExpr.toParsed).any
                parsedExprIsUnsupportedRustAlu <;> simp_all
          exact welcomePe_unsupported_not_correct expressions checkTrue pendingFalse
            unsupportedTrue
      · have pendingTrue : (expressions.map NormalizedExpr.toParsed).any
            (parsedExprWaitPending (welcomeInitialState welcomeZeroWords)) = true := by
          cases h : (expressions.map NormalizedExpr.toParsed).any
              (parsedExprWaitPending (welcomeInitialState welcomeZeroWords)) <;> simp_all
        exact welcomePe_waitPending_not_correct expressions checkTrue pendingTrue
    · have checkFalse : checkParsedTopLine (InstructionLine.pe expressions).toParsed = false := by
        cases h : checkParsedTopLine (InstructionLine.pe expressions).toParsed <;> simp_all
      exact welcomePe_checkFalse_not_correct expressions checkFalse

/-- Every line of cost below two outside the open `.pe` class is refuted. -/
theorem welcomeShortLine_not_correct (line : InstructionLine)
    (short : InstructionLine.cost line < 2)
    (open_ : ∀ expressions : List NormalizedExpr, WelcomePEUnrefuted expressions →
      ¬ ProofsLean.Correct welcomeSealedMachine welcomeSpec
        (([InstructionLine.pe expressions] : List InstructionLine))) :
    ¬ ProofsLean.Correct welcomeSealedMachine welcomeSpec
      (([line] : List InstructionLine)) := by
  cases line with
  | pe expressions =>
      by_cases h : WelcomePEUnrefuted expressions
      · exact open_ expressions h
      · exact welcomePE_not_correct_of_not_unrefuted expressions h
  | nop count wait => exact welcomeNop_not_correct count wait short
  | mv transfer => exact welcomeMv_not_correct transfer

/-- **Conditional bound.** If every syntactically accepted, non-all-`.noforward`
`.pe` line is refuted, then the sealed Welcome machine has lower bound two.
The hypothesis is exactly `WelcomePEUnrefuted`, the unformalised value case. -/
theorem welcomeLowerBound_two_of_unrefuted
    (open_ : ∀ expressions : List NormalizedExpr, WelcomePEUnrefuted expressions →
      ¬ ProofsLean.Correct welcomeSealedMachine welcomeSpec
        (([InstructionLine.pe expressions] : List InstructionLine))) :
    ProofsLean.LowerBound welcomeSealedMachine welcomeSpec 2 := by
  rw [welcomeLowerBound_two_iff_rejects_short_lines]
  intro line short
  exact welcomeShortLine_not_correct line short open_

/-- **The gap, exactly.** The bound is equivalent to the refutation of the open
`WelcomePEUnrefuted` class, so that class is neither stronger nor weaker than
the missing piece of `WelcomeLowerBound.lean`. -/
theorem welcomeLowerBound_two_iff_unrefuted :
    ProofsLean.LowerBound welcomeSealedMachine welcomeSpec 2 ↔
      (∀ expressions : List NormalizedExpr, WelcomePEUnrefuted expressions →
        ¬ ProofsLean.Correct welcomeSealedMachine welcomeSpec
          (([InstructionLine.pe expressions] : List InstructionLine))) := by
  constructor
  · intro lower expressions _unrefuted
    rw [welcomeLowerBound_two_iff_rejects_short_lines] at lower
    exact lower (.pe expressions) (by simp [InstructionLine.cost])
  · exact welcomeLowerBound_two_of_unrefuted

end ProofsLean.MNCore
