import ProofsLean.ConvertEndian
import ProofsLean.WelcomeLowerBoundTwo
import ProofsLean.GenericLowerBound

/-! # `12.convert-endian` — the one-line lower bound on the sealed machine

This module states the Convert Endian problem on the **sealed whole-machine
value model** (`step := executeNormalizedLine`, non-`.ok` results sealed to
`none`) and reduces the lower bound at **two** (no one-line program) to a
single, explicitly stated value argument for `.pe` lines.  The empty program,
every `nop`, every `mv`, every syntactically rejected `.pe` line and every
all-`.noforward` `.pe` line are refuted unconditionally.

The observed PE is `n0c0b0m0p0`; the input is the PE-0 projection of the
official four-PE problem: one 64-bit word at LM0 long address `0`.  The
postcondition is bit-exact and asks for `byteSwap64` of that word at LM1 long
address `0`.  Observing one PE is a weakening of the official problem (sound
for a lower bound); the bit-exact postcondition is *stronger* than the official
`1e-4` tolerance, so the formal lower bound is for a stronger specification.

## What is proved here

* `cendSealedMachine`, `cendSpec`, `cendInitialState` — the problem.
* `cendEmpty_not_correct` — the empty program.
* `cendNop_not_correct`, `cendMv_not_correct` — every single `nop` / `mv` line.
* `cendPE_checkFalse_not_correct`, `cendPE_waitPending_not_correct`,
  `cendPE_unsupported_not_correct`, `cendPE_notSupported_not_correct`,
  `cendPE_noforward_not_correct` — the syntactic `.pe` cases.
* `CendPEUnrefuted` — the exact remaining class: accepted, supported,
  wait-free and not all-`.noforward`.
* `cendLowerBound_two_of_peLines` / `cendLowerBound_two_of_unrefuted` —
  `LowerBound cendSealedMachine cendSpec 2` from the value argument for that
  class; `cendLowerBound_two_iff_peLines` shows the bound is *equivalent* to
  it.
* `cendLowerBound_three_of_residuals` / `cendLowerBound_three_iff_residuals` —
  the optimality bound `3` from the one-line residual plus
  `CendTwoLinesRefuted` (the two-unit-line value argument).

Neither residual is assumed by any unconditional theorem here.  The companion
report in `research/experiments/cend-proof/` records the bounded execution
samples, the two-stage datapath value closure and the remaining executor link
(`ProofsLean/ValueProvenance.lean`).

No `sorry`, no `admit`, no `native_decide`, no new axioms.
-/

namespace ProofsLean.MNCore

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

open Issue
open PEMemory

/-! ## 1. The input, initial state, sealed machine and specification -/

/-- Zero-initialised PE register file carrying the observed PE's input word in
LM0 long word `0` (the two 32-bit words, most significant first).  LM1, the GRF
files, `T` and the mask registers are zero, matching `Machine::new`. -/
def cendInitialPERegisters (input : BitVec 64) : IntegerRegisterFiles :=
  { zeroInitialPERegisterFiles with
    lm0 := fun address =>
      if address.val = 0 then input.extractLsb' 32 32
      else if address.val = 1 then input.extractLsb' 0 32
      else 0 }

/-- The initial whole-machine state of the PE-0 projection: every PE carries
the same input word. -/
def cendInitialState (input : BitVec 64) : State :=
  { rustSimulatorInitialState with
    peRegisters := fun _ => cendInitialPERegisters input }

theorem cendInitialState_peRegisters (input : BitVec 64) (pe : PEId) :
    (cendInitialState input).peRegisters pe = cendInitialPERegisters input := rfl

theorem cendInitialState_maskDirective (input : BitVec 64) :
    (cendInitialState input).maskDirective = rustSimulatorInitialState.maskDirective := rfl

theorem cendInitialState_context (input : BitVec 64) (pe : PEId) :
    (cendInitialState input).peContext pe = ParsedIntegerContext.ofLinearIndex pe := rfl

/-- The observed LM0 long word of the initial state is the input word. -/
theorem cendInitialLm0_readPair (input : BitVec 64) :
    FloatPEMemory.readPair .lm0 (cendInitialPERegisters input).lm0
      ⟨0, by decide⟩ = input := by
  unfold FloatPEMemory.readPair PEMemory.readWords PEMemory.advance PEMemory.count
    PEMemory.Width.words PEMemory.Bank.capacity cendInitialPERegisters
  simp only [Fin.val_zero, Nat.reduceAdd]
  simp
  exact BitVec.extractLsb'_append_extractLsb' 

/-- The observed PE (`n0c0b0m0p0`). -/
abbrev cendPE : PEId := welcomePE

/-- The observed output pair (LM1 long word `0`) of a state. -/
def cendOutputPair (state : State) : BitVec 64 :=
  FloatPEMemory.readPair .lm1 (state.peRegisters cendPE).lm1 ⟨0, by decide⟩

theorem cendInitialLm1_readPair (input : BitVec 64) :
    FloatPEMemory.readPair .lm1 (cendInitialPERegisters input).lm1
      ⟨0, by decide⟩ = 0 := by
  unfold FloatPEMemory.readPair PEMemory.readWords PEMemory.advance PEMemory.count
    PEMemory.Width.words PEMemory.Bank.capacity cendInitialPERegisters
  simp [zeroInitialPERegisterFiles]

theorem cendInitialState_outputPair (input : BitVec 64) :
    cendOutputPair (cendInitialState input) = 0 := by
  unfold cendOutputPair cendInitialState
  exact cendInitialLm1_readPair input

/-- The sealed whole-machine value model of Convert Endian. -/
noncomputable def cendSealedMachine : ProofsLean.Machine where
  Line := InstructionLine
  State := State
  Input := BitVec 64
  step := fun line state =>
    match executeNormalizedLine line.toNormalizedLine state with
    | .ok next => some next
    | _ => none
  legal := fun _ => true
  lineCost := InstructionLine.cost
  positiveCost := InstructionLine.cost_positive

/-- The Convert Endian problem on the sealed machine, observed at PE 0 and
at LM1 long address `0`. -/
noncomputable def cendSpec : ProofsLean.Problem cendSealedMachine where
  admissible := fun _ => True
  initial := cendInitialState
  post := fun input state => cendOutputPair state = byteSwap64 input

theorem cendSpec_initial (input : BitVec 64) :
    cendSpec.initial input = cendInitialState input := rfl

theorem cendSpec_admissible (input : BitVec 64) : cendSpec.admissible input := trivial

/-- The witness word: byte reversal `0x0807060504030201` has two 32-bit halves
`0x08070605` and `0x04030201`, neither of which is reachable as a 32-bit output
word by two supported ALU stages from the initial word (see the report). -/
def cendWitness : BitVec 64 := 0x0102030405060708

theorem cendTarget_witness_ne_zero : byteSwap64 cendWitness ≠ 0 := by
  decide

/-! ## 2. Sealed-step inversion helpers -/

theorem cendSealed_step_ok {line : InstructionLine} {state next : State}
    (h : cendSealedMachine.step line state = some next) :
    executeNormalizedLine line.toNormalizedLine state = .ok next := by
  cases e : executeNormalizedLine line.toNormalizedLine state with
  | ok s => simpa [cendSealedMachine, e] using h
  | failure => simp [cendSealedMachine, e] at h
  | unknown => simp [cendSealedMachine, e] at h

theorem cendSealed_step_none_of_failure {line : InstructionLine} {state : State}
    (h : executeNormalizedLine line.toNormalizedLine state = .failure) :
    cendSealedMachine.step line state = none := by
  simp [cendSealedMachine, h]

theorem cendSealed_step_none_of_unknown {line : InstructionLine} {state : State}
    (h : executeNormalizedLine line.toNormalizedLine state = .unknown) :
    cendSealedMachine.step line state = none := by
  simp [cendSealedMachine, h]

/-- A line whose step is stuck at the initial state is incorrect: the program
has no result on that input. -/
theorem cend_not_correct_of_step_none (line : InstructionLine) (input : BitVec 64)
    (stuck : cendSealedMachine.step line (cendInitialState input) = none) :
    ¬ ProofsLean.Correct cendSealedMachine cendSpec [line] := by
  intro correct
  obtain ⟨result, executed, _post⟩ := correct.2 input (cendSpec_admissible input)
  rw [cendSpec_initial] at executed
  have stepResult : cendSealedMachine.step line (cendInitialState input) = some result := by
    simpa [ProofsLean.execute] using executed
  rw [stuck] at stepResult
  simp at stepResult

/-- A line whose successful step leaves every PE register file unchanged is
incorrect whenever the target pair is non-zero. -/
theorem cend_not_correct_of_step_frame (line : InstructionLine) (input : BitVec 64)
    (next : State)
    (step : cendSealedMachine.step line (cendInitialState input) = some next)
    (frame : next.peRegisters = (cendInitialState input).peRegisters)
    (targetNe : byteSwap64 input ≠ 0) :
    ¬ ProofsLean.Correct cendSealedMachine cendSpec [line] := by
  intro correct
  obtain ⟨result, executed, post⟩ := correct.2 input (cendSpec_admissible input)
  rw [cendSpec_initial] at executed
  have stepResult : cendSealedMachine.step line (cendInitialState input) = some result := by
    simpa [ProofsLean.execute] using executed
  rw [step] at stepResult
  have resultEq : result = next := (Option.some.inj stepResult).symm
  subst result
  have word := post
  unfold cendSpec at word
  simp only at word
  unfold cendOutputPair at word
  rw [frame] at word
  change FloatPEMemory.readPair .lm1 (cendInitialPERegisters input).lm1
    ⟨0, by decide⟩ = byteSwap64 input at word
  rw [cendInitialLm1_readPair] at word
  exact targetNe word.symm

/-! ## 3. The empty program, `nop` and `mv` -/

theorem cendEmpty_not_correct :
    ¬ ProofsLean.Correct cendSealedMachine cendSpec
      ([] : ProofsLean.Program cendSealedMachine) := by
  intro correct
  obtain ⟨result, executed, post⟩ := correct.2 cendWitness (cendSpec_admissible _)
  rw [cendSpec_initial] at executed
  have stateEq : cendInitialState cendWitness = result := by
    have h : (some (cendInitialState cendWitness) : Option cendSealedMachine.State) =
        some result := by
      simpa [ProofsLean.execute] using executed
    exact Option.some.inj h
  subst stateEq
  unfold cendSpec at post
  simp only at post
  rw [cendInitialState_outputPair] at post
  exact cendTarget_witness_ne_zero post.symm

theorem cendNop_not_correct (count : {n : Nat // 0 < n}) (wait : Option (Fin 256)) :
    ¬ ProofsLean.Correct cendSealedMachine cendSpec
      ([InstructionLine.nop count wait] : List InstructionLine) := by
  cases step : cendSealedMachine.step (InstructionLine.nop count wait)
      (cendInitialState cendWitness) with
  | none => exact cend_not_correct_of_step_none _ _ step
  | some next =>
      apply cend_not_correct_of_step_frame _ _ next step
      · have executed := cendSealed_step_ok step
        exact executeNormalizedLine_nop_peRegisters count.val wait _ next executed
      · exact cendTarget_witness_ne_zero

theorem cendMv_not_correct (transfer : NormalizedMv) :
    ¬ ProofsLean.Correct cendSealedMachine cendSpec
      ([InstructionLine.mv transfer] : List InstructionLine) := by
  cases step : cendSealedMachine.step (InstructionLine.mv transfer)
      (cendInitialState cendWitness) with
  | none => exact cend_not_correct_of_step_none _ _ step
  | some next =>
      apply cend_not_correct_of_step_frame _ _ next step
      · have executed := cendSealed_step_ok step
        exact executeNormalizedLine_mv_peRegisters transfer _ next executed
      · exact cendTarget_witness_ne_zero

/-! ## 4. Syntactic `.pe` refutations and the exact residual class -/

/-- Every parsed expression of the line is a `.noforward` row. -/
def CendAllNoForward (expressions : List NormalizedExpr) : Prop :=
  ∀ expression ∈ expressions.map NormalizedExpr.toParsed, expression.op = .noforward

theorem cend_waitPending_eq (input : BitVec 64) (expression : ParsedExpr) :
    parsedExprWaitPending (cendInitialState input) expression =
      parsedExprWaitPending rustSimulatorInitialState expression := rfl

theorem cendPE_checkFalse_not_correct (expressions : List NormalizedExpr)
    (rejected : checkParsedTopLine (InstructionLine.pe expressions).toParsed = false) :
    ¬ ProofsLean.Correct cendSealedMachine cendSpec
      ([InstructionLine.pe expressions] : List InstructionLine) :=
  cend_not_correct_of_step_none (line := InstructionLine.pe expressions) cendWitness
    (cendSealed_step_none_of_failure (line := InstructionLine.pe expressions)
      (executeNormalizedLine_pe_checkFalse expressions (cendInitialState cendWitness) rejected))

theorem cendPE_waitPending_not_correct (expressions : List NormalizedExpr)
    (accepted : checkParsedTopLine (InstructionLine.pe expressions).toParsed = true)
    (pending : (expressions.map NormalizedExpr.toParsed).any
      (parsedExprWaitPending (cendInitialState cendWitness)) = true) :
    ¬ ProofsLean.Correct cendSealedMachine cendSpec
      ([InstructionLine.pe expressions] : List InstructionLine) :=
  cend_not_correct_of_step_none _ _ (cendSealed_step_none_of_unknown
    (executeNormalizedLine_pe_waitPending expressions (cendInitialState cendWitness)
      accepted pending))

theorem cendPE_unsupported_not_correct (expressions : List NormalizedExpr)
    (accepted : checkParsedTopLine (InstructionLine.pe expressions).toParsed = true)
    (waitsComplete : (expressions.map NormalizedExpr.toParsed).any
      (parsedExprWaitPending (cendInitialState cendWitness)) = false)
    (unsupported : (expressions.map NormalizedExpr.toParsed).any
      parsedExprIsUnsupportedRustAlu = true) :
    ¬ ProofsLean.Correct cendSealedMachine cendSpec
      ([InstructionLine.pe expressions] : List InstructionLine) :=
  cend_not_correct_of_step_none _ _ (cendSealed_step_none_of_failure
    (executeNormalizedLine_pe_unsupported expressions (cendInitialState cendWitness)
      accepted waitsComplete unsupported))

theorem cendPE_notSupported_not_correct (expressions : List NormalizedExpr)
    (accepted : checkParsedTopLine (InstructionLine.pe expressions).toParsed = true)
    (waitsComplete : (expressions.map NormalizedExpr.toParsed).any
      (parsedExprWaitPending (cendInitialState cendWitness)) = false)
    (noUnsupported : (expressions.map NormalizedExpr.toParsed).any
      parsedExprIsUnsupportedRustAlu = false)
    (notSupported : (expressions.map NormalizedExpr.toParsed).all
      parsedExprIsSupportedPELineProducer = false) :
    ¬ ProofsLean.Correct cendSealedMachine cendSpec
      ([InstructionLine.pe expressions] : List InstructionLine) :=
  cend_not_correct_of_step_none _ _ (cendSealed_step_none_of_unknown
    (executeNormalizedLine_pe_notSupported expressions (cendInitialState cendWitness)
      accepted waitsComplete noUnsupported notSupported))

/-- An all-`.noforward` `.pe` line never touches the PE register files. -/
theorem cendPE_noforward_not_correct (expressions : List NormalizedExpr)
    (all : CendAllNoForward expressions) :
    ¬ ProofsLean.Correct cendSealedMachine cendSpec
      ([InstructionLine.pe expressions] : List InstructionLine) := by
  cases step : cendSealedMachine.step (InstructionLine.pe expressions)
      (cendInitialState cendWitness) with
  | none => exact cend_not_correct_of_step_none _ _ step
  | some next =>
      apply cend_not_correct_of_step_frame _ _ next step
      · have executed := cendSealed_step_ok step
        exact executeNormalizedLine_pe_peRegisters_noforward expressions
          (cendInitialState cendWitness) next all executed
      · exact cendTarget_witness_ne_zero

/-- The four syntactic conditions under which a `.pe` line is not refuted by the
`cendPE_*` theorems: accepted issue checker, no pending wait tag, no
Rust-unsupported ALU row and only supported producers. -/
def CendPEAccepted (expressions : List NormalizedExpr) : Prop :=
  checkParsedTopLine (InstructionLine.pe expressions).toParsed = true ∧
  (expressions.map NormalizedExpr.toParsed).any
      (parsedExprWaitPending (cendInitialState cendWitness)) = false ∧
  (expressions.map NormalizedExpr.toParsed).any parsedExprIsUnsupportedRustAlu = false ∧
  (expressions.map NormalizedExpr.toParsed).all parsedExprIsSupportedPELineProducer = true

/-- **The unrefuted class.**  A syntactically accepted `.pe` line which is not
all-`.noforward`.  The remaining obligation is the value argument for the one
`LegalParsedLine.writesUnique`-permitted `.lm1` writer of such a line. -/
def CendPEUnrefuted (expressions : List NormalizedExpr) : Prop :=
  CendPEAccepted expressions ∧ ¬ CendAllNoForward expressions

/-! ## 5. The residual single-`.pe`-line value argument -/

/-- **The residual.**  No single `.pe` issue line is correct.  This is the
per-line value argument: at the witness input (or a program-dependent witness
for the `.immediate` case) the LM1 words produced by one issue line cannot be
the two halves of the byte-reversed word. -/
def CendPELinesRefuted : Prop :=
  ∀ expressions : List NormalizedExpr,
    ¬ ProofsLean.Correct cendSealedMachine cendSpec
      ([InstructionLine.pe expressions] : List InstructionLine)

/-- **Bound two from the residual.**  The empty program, `nop` and `mv` lines
are refuted unconditionally; only single `.pe` lines remain. -/
theorem cendLowerBound_two_of_peLines (peLines : CendPELinesRefuted) :
    ProofsLean.LowerBound cendSealedMachine cendSpec 2 := by
  intro program correct
  by_cases bound : 2 ≤ ProofsLean.score cendSealedMachine program
  · exact bound
  · have short : ProofsLean.score cendSealedMachine program < 2 := by omega
    rcases (ProofsLean.MNCore.Generic.score_lt_two_iff cendSealedMachine program).mp short with
      empty | ⟨line, programEq, costOne⟩
    · subst empty
      exact False.elim (cendEmpty_not_correct correct)
    · subst programEq
      cases line with
      | pe expressions => exact False.elim (peLines expressions correct)
      | nop count wait =>
          exact False.elim (cendNop_not_correct count wait correct)
      | mv transfer =>
          exact False.elim (cendMv_not_correct transfer correct)

/-- **The equivalence.**  Bound two is *exactly* the single-`.pe`-line value
argument. -/
theorem cendLowerBound_two_iff_peLines :
    ProofsLean.LowerBound cendSealedMachine cendSpec 2 ↔ CendPELinesRefuted := by
  constructor
  · intro lower expressions
    intro correct
    have bound := lower [InstructionLine.pe expressions] correct
    change 2 ≤ cendSealedMachine.lineCost (InstructionLine.pe expressions) at bound
    rw [show cendSealedMachine.lineCost (InstructionLine.pe expressions) = 1 from rfl] at bound
    omega
  · exact cendLowerBound_two_of_peLines

/-- **Bound two from the residual class.**  All syntactic rejections and the
all-`.noforward` rows are refuted unconditionally. -/
theorem cendLowerBound_two_of_unrefuted
    (unrefuted : ∀ expressions : List NormalizedExpr, CendPEUnrefuted expressions →
      ¬ ProofsLean.Correct cendSealedMachine cendSpec
        ([InstructionLine.pe expressions] : List InstructionLine)) :
    ProofsLean.LowerBound cendSealedMachine cendSpec 2 :=
  cendLowerBound_two_of_peLines (fun expressions => by
    intro correct
    by_cases noforward : CendAllNoForward expressions
    · exact cendPE_noforward_not_correct expressions noforward correct
    · by_cases hcheck : checkParsedTopLine (InstructionLine.pe expressions).toParsed = true
      · by_cases hwait : (expressions.map NormalizedExpr.toParsed).any
            (parsedExprWaitPending (cendInitialState cendWitness)) = false
        · by_cases hunsupported : (expressions.map NormalizedExpr.toParsed).any
              parsedExprIsUnsupportedRustAlu = false
          · by_cases hsupported : (expressions.map NormalizedExpr.toParsed).all
                parsedExprIsSupportedPELineProducer = true
            · exact unrefuted expressions ⟨⟨hcheck, hwait, hunsupported, hsupported⟩,
                noforward⟩ correct
            · exact cendPE_notSupported_not_correct expressions hcheck hwait
                hunsupported (by simpa using hsupported) correct
          · exact cendPE_unsupported_not_correct expressions hcheck hwait
              (by simpa using hunsupported) correct
        · exact cendPE_waitPending_not_correct expressions hcheck
            (by simpa using hwait) correct
      · exact cendPE_checkFalse_not_correct expressions (by simpa using hcheck) correct)


/-! ## 6. The optimality obligation at bound three -/

/-- The sealed machine's score is the sum of its own line costs. -/
theorem cend_score_eq (program : ProofsLean.Program cendSealedMachine) :
    ProofsLean.score cendSealedMachine program =
      (program.map cendSealedMachine.lineCost).sum := by
  induction program with
  | nil => rfl
  | cons line rest ih => simp [ProofsLean.score, ih]

/-- A program of score below three is empty, a single unit-cost line, or two
unit-cost lines.  Only `positiveCost` is used. -/
theorem cend_score_lt_three_iff (program : ProofsLean.Program cendSealedMachine) :
    ProofsLean.score cendSealedMachine program < 3 ↔
      program = [] ∨
      (∃ line : cendSealedMachine.Line, program = [line] ∧
        cendSealedMachine.lineCost line ≤ 2) ∨
      (∃ first second : cendSealedMachine.Line, program = [first, second] ∧
        cendSealedMachine.lineCost first = 1 ∧ cendSealedMachine.lineCost second = 1) := by
  constructor
  · intro short
    rw [cend_score_eq] at short
    cases program with
    | nil => exact Or.inl rfl
    | cons first rest =>
        cases rest with
        | nil =>
            right; left
            refine ⟨first, rfl, ?_⟩
            have positive := cendSealedMachine.positiveCost first
            simp only [List.map_cons, List.sum_cons, List.sum_nil, Nat.add_zero] at short
            omega
        | cons second tail =>
            have firstPositive := cendSealedMachine.positiveCost first
            have secondPositive := cendSealedMachine.positiveCost second
            cases tail with
            | nil =>
                right; right
                refine ⟨first, second, rfl, ?_, ?_⟩ <;>
                  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                    Nat.add_zero] at short <;> omega
            | cons third rest =>
                have thirdPositive := cendSealedMachine.positiveCost third
                simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                  Nat.add_zero] at short
                omega
  · intro shape
    rcases shape with rfl | ⟨line, rfl, costBound⟩ | ⟨first, second, rfl, firstOne, secondOne⟩
    · simp [cend_score_eq]
    · rw [cend_score_eq]
      change cendSealedMachine.lineCost line < 3
      omega
    · rw [cend_score_eq]
      simp [firstOne, secondOne]

/-- **The two-line obligation.**  No program of two unit-cost lines is correct.
This is the remaining "one less than the confirmed minimum" statement: the
three-line answer is optimal exactly when this holds together with
`CendPELinesRefuted`. -/
def CendTwoLinesRefuted : Prop :=
  ∀ (first second : InstructionLine),
    InstructionLine.cost first = 1 → InstructionLine.cost second = 1 →
    ¬ ProofsLean.Correct cendSealedMachine cendSpec
      ([first, second] : ProofsLean.Program cendSealedMachine)

/-- **Bound three from the one- and two-line obligations.** -/
theorem cendLowerBound_three_of_residuals
    (peLines : CendPELinesRefuted) (twoLines : CendTwoLinesRefuted) :
    ProofsLean.LowerBound cendSealedMachine cendSpec 3 := by
  intro program correct
  by_cases bound : 3 ≤ ProofsLean.score cendSealedMachine program
  · exact bound
  · have short : ProofsLean.score cendSealedMachine program < 3 := by omega
    rcases (cend_score_lt_three_iff program).mp short with
      empty | ⟨line, programEq, costBound⟩ | ⟨first, second, programEq, firstOne, secondOne⟩
    · subst empty
      exact False.elim (cendEmpty_not_correct correct)
    · subst programEq
      by_cases costOne : cendSealedMachine.lineCost line = 1
      · have lower := cendLowerBound_two_of_peLines peLines
        have bound := lower [line] correct
        rw [cend_score_eq] at bound
        simp [costOne] at bound
      · have costTwo : cendSealedMachine.lineCost line = 2 := by
          have positive := cendSealedMachine.positiveCost line
          omega
        cases line with
        | pe expressions =>
            exact False.elim (by
              change cendSealedMachine.lineCost (InstructionLine.pe expressions) = 2 at costTwo
              rw [show cendSealedMachine.lineCost (InstructionLine.pe expressions) = 1 from rfl]
                at costTwo
              omega)
        | nop count wait =>
            exact False.elim (cendNop_not_correct count wait correct)
        | mv transfer =>
            exact False.elim (by
              change cendSealedMachine.lineCost (InstructionLine.mv transfer) = 2 at costTwo
              rw [show cendSealedMachine.lineCost (InstructionLine.mv transfer) = 1 from rfl]
                at costTwo
              omega)
    · subst programEq
      exact False.elim (twoLines first second
        (show InstructionLine.cost first = 1 from firstOne)
        (show InstructionLine.cost second = 1 from secondOne) correct)

/-- The bound-three reduction in the same shape as the bound-two one: the
one-line bound plus the exact two-line obligation. -/
theorem cendLowerBound_three_iff_residuals :
    ProofsLean.LowerBound cendSealedMachine cendSpec 3 ↔
      CendPELinesRefuted ∧ CendTwoLinesRefuted := by
  constructor
  · intro lower
    constructor
    · intro expressions
      intro correct
      have bound := lower ([InstructionLine.pe expressions] :
        ProofsLean.Program cendSealedMachine) correct
      rw [cend_score_eq] at bound
      change 3 ≤ cendSealedMachine.lineCost (InstructionLine.pe expressions) at bound
      have bound' : 3 ≤ cendSealedMachine.lineCost (InstructionLine.pe expressions) := bound
      have cost : cendSealedMachine.lineCost (InstructionLine.pe expressions) = 1 := rfl
      omega
    · intro first second firstOne secondOne
      intro correct
      have bound := lower ([first, second] : ProofsLean.Program cendSealedMachine) correct
      rw [cend_score_eq] at bound
      change 3 ≤ cendSealedMachine.lineCost first + cendSealedMachine.lineCost second at bound
      have bound' : 3 ≤ cendSealedMachine.lineCost first +
          cendSealedMachine.lineCost second := bound
      have firstCost : cendSealedMachine.lineCost first = 1 := firstOne
      have secondCost : cendSealedMachine.lineCost second = 1 := secondOne
      omega
  · intro residuals
    exact cendLowerBound_three_of_residuals residuals.1 residuals.2

end ProofsLean.MNCore

-- End of module: no sorry, no admit, no native_decide, no new axioms.
