import ProofsLean.WelcomeOptimalFinal
import ProofsLean.FloatSubtract

/-! # Problem `1.a-b` (A − B) on the sealed whole-machine value model

This module states problem `1.a-b` — `C = A − B` for two `16`-word float
vectors — on the same **sealed whole-machine value model** that
`ProofsLean/WelcomeOptimalFinal.lean` uses for the Welcome problem, proves every
one-line refutation that does not need new executor analysis, and reduces
`LowerBound abSealedMachine abSpec 2` to an explicitly stated residual class.

## The model

`abSealedMachine` is the sealed machine: `Line` and `lineCost` are the
whole-machine ones, the state is the real `State`, and `step` is the value
transition `executeNormalizedLine` that `wholeMachine.step` invokes *after* its
issue, address-mode and hazard-history checks.  A non-`.ok` value transition is
`none`.  As in `WelcomeOptimal.lean`, the hazard-history rejection layer and the
`.failure`/`.unknown` distinction are **sealed away**; every theorem below is
stated about this restricted machine and carries that restriction.

The initial state puts `A` into LM0 words `0..15` and `B` into LM0 words
`16..31` (the problem's `$lm[0:16]` / `$lm[16:32]`), leaves LM1 zero and is
otherwise the simulator default.  The specification observes PE 0's LM1 words
`0..15` (the problem's `$ln[0:16]`) and asks for the **bit-exact** single
precision difference `FloatSubtract.subtract A[i] B[i]`, where
`subtract x y = singleFma x 1.0 (-y)` is the datapath of `fvadd x -y out`.

**Strength of this specification.**  Two of its differences from the official
problem are weakenings, i.e. sound for a lower bound (a program correct for the
official problem is also correct here):

* it observes only **one** PE's LM1 words `0..15`, while the official problem
  observes all 4096 PEs;
* its inputs are **PE-uniform** (`A` and `B` in every PE's LM0), a subset of the
  official per-PE inputs, and every input is admissible (the official problem
  restricts the values to `[-512, 512]`).

One difference is *not* a weakening: the target is **bit-exact**, while the
official judge allows an absolute error of `1e-4`.  The bit-exact specification
is therefore *stronger* than the official one, and `LowerBound abSealedMachine
abSpec 2` does **not** formally imply the official tolerance bound; the
transfer needs a tolerance-valued postcondition.  The refutations proved here
are robust in the sense that they exhibit a word that is off by at least `1.0`
(an untouched word reading `0` against a target of `1.0`) or a wrong sign bit
against a target of `-1.0`, so any tolerance below `1.0` is violated as well;
that robustness is *argued*, not formalised.

## Results proved here (all unconditional)

* `abEmpty_not_correct` — the empty program is incorrect.
* `abNop_not_correct`, `abMv_not_correct` — no single `nop` / `mv` line.
* `abPE_checkFalse_not_correct`, `abPE_waitPending_not_correct`,
  `abPE_unsupported_not_correct`, `abPE_notSupported_not_correct` — every
  syntactically rejected `.pe` line.
* `abPE_noforward_not_correct` — every all-`.noforward` `.pe` line.
* `abPE_singleWelcomeLine_not_correct` — every single `iinc` line.
* `abPENotUnrefuted_not_correct` — every `.pe` line outside the residual class
  `AbPEUnrefuted`.
* `abShortLine_not_correct` — every line of cost below two outside the residual
  class, hence `abLowerBound_two_of_residual` and the exact equivalence
  `abLowerBound_two_iff_residual`.
* `ab_not_correct_of_narrowAtOnes` — **the `1.a-b` value argument**: a line
  whose PE 0 write list at the input `A = 1.0, B = 0` is narrow (at most four
  windows of at most two words) is incorrect.  This is the A − B analogue of
  `welcome_not_correct_of_lm1Narrow`.
* `abTarget_five_eq_zero` and `abEmpty_correct_at_zero` — the two *negative*
  results that explain why the Welcome write-shape chain alone cannot close
  `1.a-b` (see the final section).

## The remainder

`AbPEUnrefuted` is non-empty: it contains every accepted line whose PE 0 write
list at the all-zero input is not narrow (for instance a line with four
`.double` destinations).  The last section states the two obligations that
close it (`ABNarrowTransfer`, `AbDoubleOrIndependent`) and proves
`abLowerBound_two_of_transfer`; neither is proved here.  The final section also
records *why*: the Welcome chain's shapes are stated at the all-zero initial
state, where `1.a-b`'s target equals the initial LM1 value `0`, so no zero-input
refutation can exist; and the third (input-independent) disjunct compares the
all-zero input with the all-five input, whose `1.a-b` target is *also* zero.

No `sorry`, no `admit`, no `native_decide`, no new axioms, no edited module.
-/

namespace ProofsLean.MNCore

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

open Issue
open PEMemory

/-! ## 1. The input, the initial state and the sealed machine -/

/-- The 16 observed / supplied 32-bit words of one vector. -/
abbrev ABWords := ProofsLean.MNCore.PlusOne.Words

/-- The `1.a-b` input: the minuend `A` and the subtrahend `B`. -/
structure ABInput where
  /-- `A`, stored in LM0 words `0..15`. -/
  left : ABWords
  /-- `B`, stored in LM0 words `16..31`. -/
  right : ABWords

/-- LM0 of the initial PE files: `A` in words `0..15`, `B` in words `16..31`,
zero elsewhere. -/
def abInitialLm0 (input : ABInput) (address : Fin Bank.lm0.capacity) : BitVec 32 :=
  if h : address.val < 16 then
    input.left ⟨address.val, h⟩
  else if h2 : address.val < 32 then
    input.right ⟨address.val - 16, by have := address.isLt; omega⟩
  else 0

/-- Zero-initialised PE register file carrying `A` and `B` in LM0.  LM1, the
GRF files, `T` and the mask registers are zero, matching `Machine::new`. -/
def abInitialPERegisters (input : ABInput) : IntegerRegisterFiles :=
  { zeroInitialPERegisterFiles with lm0 := abInitialLm0 input }

/-- The initial whole-machine state of `1.a-b`: every PE carries the same
input words (the semantics is PE-uniform). -/
def abInitialState (input : ABInput) : State :=
  { rustSimulatorInitialState with peRegisters := fun _ => abInitialPERegisters input }

theorem abInitialState_peRegisters (input : ABInput) (pe : PEId) :
    (abInitialState input).peRegisters pe = abInitialPERegisters input := rfl

theorem abInitialState_maskDirective (input : ABInput) :
    (abInitialState input).maskDirective = welcomeMaskDirective := rfl

theorem abInitialState_context (input : ABInput) (pe : PEId) :
    (abInitialState input).peContext pe = ParsedIntegerContext.ofLinearIndex pe := rfl

theorem abInitialState_invariant (input : ABInput) :
    WelcomeStateInvariant (abInitialState input) :=
  ⟨rfl, fun _ => ⟨rfl, rfl⟩⟩

theorem abInitialPERegisters_lm1 (input : ABInput) (address : Fin Bank.lm1.capacity) :
    (abInitialPERegisters input).lm1 address = 0 := rfl

theorem abInitialLm0_left (input : ABInput) (word : Fin 16) :
    abInitialLm0 input ⟨word.val, by have := word.isLt; change word.val < 4096; omega⟩ =
      input.left word := by
  simp [abInitialLm0, word.isLt]

theorem abInitialLm0_right (input : ABInput) (word : Fin 16) :
    abInitialLm0 input
        ⟨16 + word.val, by have := word.isLt; change 16 + word.val < 4096; omega⟩ =
      input.right word := by
  have h16 : ¬ (16 + word.val < 16) := by omega
  have h32 : 16 + word.val < 32 := by have := word.isLt; omega
  simp [abInitialLm0, h16, h32]

theorem abInitialLm0_other (input : ABInput) (address : Fin Bank.lm0.capacity)
    (large : 32 ≤ address.val) : abInitialLm0 input address = 0 := by
  have h16 : ¬ address.val < 16 := by omega
  have h32 : ¬ address.val < 32 := by omega
  simp [abInitialLm0, h16, h32]

/-- The sealed whole-machine value model of `1.a-b`. -/
noncomputable def abSealedMachine : ProofsLean.Machine where
  Line := InstructionLine
  State := State
  Input := ABInput
  step := fun line state =>
    match executeNormalizedLine line.toNormalizedLine state with
    | .ok next => some next
    | _ => none
  legal := fun _ => True
  lineCost := InstructionLine.cost
  positiveCost := InstructionLine.cost_positive

/-- The observed PE (`n0c0b0m0p0`, as in the Welcome model). -/
abbrev abPE : PEId := welcomePE

/-- The `1.a-b` target word: the bit-exact single precision difference. -/
def abTarget (input : ABInput) (i : Fin 16) : BitVec 32 :=
  ProofsLean.MNCore.FloatSubtract.subtract (input.left i) (input.right i)

/-- The problem: LM0 holds `A` and `B`, LM1 starts zero, and PE 0's LM1 word
`i` must be `A[i] − B[i]`. -/
noncomputable def abSpec : ProofsLean.Problem abSealedMachine where
  admissible := fun _ => True
  initial := abInitialState
  post := fun input state => ∀ i : Fin 16,
    (state.peRegisters abPE).lm1
      ⟨i.val, by have := i.isLt; change i.val < 4096; omega⟩ =
      abTarget input i

/-- The initial state of the specification is `abInitialState`. -/
@[simp] theorem abSpec_initial (input : ABInput) :
    abSpec.initial input = abInitialState input := rfl

theorem abSpec_admissible (input : ABInput) : abSpec.admissible input := trivial

/-! ## 2. Concrete inputs and their target values -/

def abZeroWords : ABWords := fun _ => 0
/-- The float `1.0` (`0x3F800000`) in every lane. -/
def abOneWords : ABWords := fun _ => 0x3F800000
/-- The integer `5` in every lane.  This is the Welcome chain's all-five input:
`abInitialState (5, 0)` is exactly `welcomeInitialState welcomeAllFiveWords`. -/
def abFiveWords : ABWords := fun _ => 5

/-- `A = B = 0`: the target is zero in every word. -/
def abZeroInput : ABInput := ⟨abZeroWords, abZeroWords⟩
/-- `A = 1.0`, `B = 0`: the target is `0x3F800000` in every word. -/
def abOneLeftInput : ABInput := ⟨abOneWords, abZeroWords⟩
/-- `A = 0`, `B = 1.0`: the target is `0xBF800000` in every word. -/
def abZeroRightInput : ABInput := ⟨abZeroWords, abOneWords⟩
/-- `A = 5`, `B = 0`: the target is `0` in every word (see
`abTarget_five_eq_zero`). -/
def abFiveInput : ABInput := ⟨abFiveWords, abZeroWords⟩

theorem abTarget_zero (i : Fin 16) : abTarget abZeroInput i = 0 := by
  simp only [abTarget, abZeroInput, abZeroWords,
    ProofsLean.MNCore.FloatSubtract.subtract,
    ProofsLean.MNCore.FloatSubtract.negateBits]
  decide

theorem abTarget_oneLeft (i : Fin 16) :
    abTarget abOneLeftInput i = 0x3F800000 := by
  simp only [abTarget, abOneLeftInput, abOneWords, abZeroWords,
    ProofsLean.MNCore.FloatSubtract.subtract,
    ProofsLean.MNCore.FloatSubtract.negateBits]
  decide

theorem abTarget_zeroRight (i : Fin 16) :
    abTarget abZeroRightInput i = 0xBF800000 := by
  simp only [abTarget, abZeroRightInput, abZeroWords, abOneWords,
    ProofsLean.MNCore.FloatSubtract.subtract,
    ProofsLean.MNCore.FloatSubtract.negateBits]
  decide

/-- **Negative result: the Welcome all-five input has `1.a-b` target zero.**
The `FloatSubtract` model (like the MAU it models) flushes the denormal
`5 * 1.0 - 0` to zero, so the input `A = 5, B = 0` asks for zero in every word —
exactly what the all-zero input asks for.  Consequently the third
(input-independent) disjunct of `WelcomePELm1WriteShapeObligation`, which only
compares those two inputs, cannot refute a `1.a-b` line. -/
theorem abTarget_five_eq_zero (i : Fin 16) : abTarget abFiveInput i = 0 := by
  simp only [abTarget, abFiveInput, abFiveWords, abZeroWords,
    ProofsLean.MNCore.FloatSubtract.subtract,
    ProofsLean.MNCore.FloatSubtract.negateBits]
  decide

theorem abTarget_oneLeft_ne_zero (i : Fin 16) :
    abTarget abOneLeftInput i ≠ 0 := by
  rw [abTarget_oneLeft]
  decide

theorem abTarget_zeroRight_ne_zero (i : Fin 16) :
    abTarget abZeroRightInput i ≠ 0 := by
  rw [abTarget_zeroRight]
  decide

/-- **Negative result: the all-zero input cannot refute any `1.a-b` program.**
The empty program is already correct there, because the target `0 - 0` equals
the initial LM1 value `0`.  Every refutation of a correct candidate therefore
has to use a non-zero input, which is exactly what the Welcome write-shape
chain (stated at the all-zero initial state) cannot supply. -/
theorem abEmpty_correct_at_zero :
    ∃ result, ProofsLean.execute abSealedMachine
        ([] : ProofsLean.Program abSealedMachine) (abInitialState abZeroInput) = some result ∧
      abSpec.post abZeroInput result := by
  refine ⟨abInitialState abZeroInput, rfl, ?_⟩
  intro i
  show ((abInitialState abZeroInput).peRegisters abPE).lm1 _ = abTarget abZeroInput i
  rw [abTarget_zero]
  exact abInitialPERegisters_lm1 abZeroInput _

/-! ### The zero and all-five inputs are the Welcome chain's initial states -/

theorem abInitialLm0_zero :
    abInitialLm0 abZeroInput = fun address =>
      if h : address.val < 16 then welcomeZeroWords ⟨address.val, h⟩ else 0 := by
  funext address
  unfold abInitialLm0
  by_cases h16 : address.val < 16
  · simp [h16, abZeroInput, abZeroWords, welcomeZeroWords]
  · by_cases h32 : address.val < 32
    · simp [h16, h32, abZeroInput, abZeroWords]
    · simp [h16, h32, abZeroInput, abZeroWords]

theorem abInitialLm0_five :
    abInitialLm0 abFiveInput = fun address =>
      if h : address.val < 16 then welcomeAllFiveWords ⟨address.val, h⟩ else 0 := by
  funext address
  unfold abInitialLm0
  by_cases h16 : address.val < 16
  · simp [h16, abFiveInput, abFiveWords, welcomeAllFiveWords]
  · by_cases h32 : address.val < 32
    · simp [h16, h32, abFiveInput, abFiveWords, abZeroWords]
    · simp [h16, h32, abFiveInput, abFiveWords, abZeroWords]

theorem abZeroInput_initialState :
    abInitialState abZeroInput = welcomeInitialState welcomeZeroWords := by
  unfold abInitialState welcomeInitialState abInitialPERegisters
    welcomeInitialPERegisters
  rw [abInitialLm0_zero]

theorem abFiveInput_initialState :
    abInitialState abFiveInput = welcomeInitialState welcomeAllFiveWords := by
  unfold abInitialState welcomeInitialState abInitialPERegisters
    welcomeInitialPERegisters
  rw [abInitialLm0_five]

theorem abSealed_step_eq (line : InstructionLine) (state : State) :
    abSealedMachine.step line state = welcomeSealedMachine.step line state := rfl

/-! ## 3. The two generic refutation patterns

Both are stated for an *arbitrary* admissible input, so the same proof serves
the all-ones input and the `A = 0, B = 1` input. -/

/-- A line whose step is stuck at the initial state of an admissible input is
incorrect: the program has no result at all on that input. -/
theorem ab_not_correct_of_step_none (line : InstructionLine) (input : ABInput)
    (stuck : abSealedMachine.step line (abInitialState input) = none) :
    ¬ ProofsLean.Correct abSealedMachine abSpec ([line] : List InstructionLine) := by
  intro correct
  obtain ⟨result, executed, _post⟩ := correct.2 input (abSpec_admissible input)
  rw [abSpec_initial] at executed
  have stepResult : abSealedMachine.step line (abInitialState input) = some result := by
    simpa [ProofsLean.execute] using executed
  rw [stuck] at stepResult
  simp at stepResult

/-- A line whose successful step leaves every PE register file unchanged is
incorrect whenever some observed word of that input has a non-zero target: the
output word keeps its initial value `0`. -/
theorem ab_not_correct_of_step_frame (line : InstructionLine) (input : ABInput)
    (next : State)
    (step : abSealedMachine.step line (abInitialState input) = some next)
    (frame : next.peRegisters = (abInitialState input).peRegisters)
    (i : Fin 16) (targetNe : abTarget input i ≠ 0) :
    ¬ ProofsLean.Correct abSealedMachine abSpec ([line] : List InstructionLine) := by
  intro correct
  obtain ⟨result, executed, post⟩ := correct.2 input (abSpec_admissible input)
  rw [abSpec_initial] at executed
  have stepResult : abSealedMachine.step line (abInitialState input) = some result := by
    simpa [ProofsLean.execute] using executed
  rw [step] at stepResult
  have resultEq : result = next := (Option.some.inj stepResult).symm
  subst result
  have word := post i
  rw [frame] at word
  have initial : ((abInitialState input).peRegisters abPE).lm1
      ⟨i.val, by have := i.isLt; change i.val < 4096; omega⟩ = 0 := rfl
  rw [initial] at word
  exact targetNe word.symm

/-- A successful sealed step is an `.ok` value transition. -/
theorem abSealed_step_ok {line : InstructionLine} {state next : State}
    (h : abSealedMachine.step line state = some next) :
    executeNormalizedLine line.toNormalizedLine state = .ok next := by
  cases e : executeNormalizedLine line.toNormalizedLine state with
  | ok s => simpa [abSealedMachine, e] using h
  | failure => simp [abSealedMachine, e] at h
  | unknown => simp [abSealedMachine, e] at h

theorem abSealed_step_none_of_failure {line : InstructionLine} {state : State}
    (h : executeNormalizedLine line.toNormalizedLine state = .failure) :
    abSealedMachine.step line state = none := by
  simp [abSealedMachine, h]

theorem abSealed_step_none_of_unknown {line : InstructionLine} {state : State}
    (h : executeNormalizedLine line.toNormalizedLine state = .unknown) :
    abSealedMachine.step line state = none := by
  simp [abSealedMachine, h]

/-! ## 4. The empty program -/

/-- The empty program is incorrect: on `A = 1.0, B = 0` it leaves LM1 word `0`
at its initial value `0`, while the specification demands `0x3F800000`. -/
theorem abEmpty_not_correct :
    ¬ ProofsLean.Correct abSealedMachine abSpec
      ([] : ProofsLean.Program abSealedMachine) := by
  intro correct
  obtain ⟨result, executed, post⟩ := correct.2 abOneLeftInput (abSpec_admissible _)
  have executed' : ProofsLean.execute abSealedMachine []
      (abInitialState abOneLeftInput) = some result := by
    have h := executed
    rw [abSpec_initial] at h
    exact h
  have stateEq : abInitialState abOneLeftInput = result := by
    have h : (some (abInitialState abOneLeftInput) : Option abSealedMachine.State) =
        some result := by
      simpa [ProofsLean.execute] using executed'
    exact Option.some.inj h
  subst stateEq
  have wanted := post ⟨0, by decide⟩
  have initial : ((abInitialState abOneLeftInput).peRegisters abPE).lm1
      ⟨0, by decide⟩ = 0 := rfl
  rw [initial, abTarget_oneLeft] at wanted
  exact absurd wanted.symm (by decide)

/-! ## 5. `.nop` lines -/

/-- **`.nop` case.** No single `nop` line is correct for `1.a-b`. -/
theorem abNop_not_correct (count : {n : Nat // 0 < n}) (wait : Option (Fin 256))
    (_short : InstructionLine.cost (.nop count wait) < 2) :
    ¬ ProofsLean.Correct abSealedMachine abSpec
      ([InstructionLine.nop count wait] : List InstructionLine) := by
  cases step : abSealedMachine.step (InstructionLine.nop count wait)
      (abInitialState abOneLeftInput) with
  | none => exact ab_not_correct_of_step_none _ _ step
  | some next =>
      apply ab_not_correct_of_step_frame _ _ next step
      · have executed := abSealed_step_ok step
        exact executeNormalizedLine_nop_peRegisters count.val wait _ next executed
      · exact abTarget_oneLeft_ne_zero ⟨0, by decide⟩

/-! ## 6. `.mv` lines -/

/-- **`.mv` case.** No single MV line is correct for `1.a-b`. -/
theorem abMv_not_correct (transfer : NormalizedMv) :
    ¬ ProofsLean.Correct abSealedMachine abSpec
      ([InstructionLine.mv transfer] : List InstructionLine) := by
  cases step : abSealedMachine.step (InstructionLine.mv transfer)
      (abInitialState abOneLeftInput) with
  | none => exact ab_not_correct_of_step_none _ _ step
  | some next =>
      apply ab_not_correct_of_step_frame _ _ next step
      · have executed := abSealed_step_ok step
        exact executeNormalizedLine_mv_peRegisters transfer _ next executed
      · exact abTarget_oneLeft_ne_zero ⟨0, by decide⟩

/-! ## 7. `.pe` lines: the syntactic rejection cases -/

theorem abPE_checkFalse_not_correct (expressions : List NormalizedExpr)
    (rejected : checkParsedTopLine (InstructionLine.pe expressions).toParsed = false) :
    ¬ ProofsLean.Correct abSealedMachine abSpec
      ([InstructionLine.pe expressions] : List InstructionLine) :=
  ab_not_correct_of_step_none _ _
    (abSealed_step_none_of_failure (line := .pe expressions)
      (executeNormalizedLine_pe_checkFalse expressions (abInitialState abOneLeftInput)
        rejected))

/-- The initial `1.a-b` states never complete an MV tag, so a `wait` row is
pending in exactly the same way as in the Welcome initial state. -/
theorem ab_waitPending_eq (input : ABInput) (expression : ParsedExpr) :
    parsedExprWaitPending (abInitialState input) expression =
      parsedExprWaitPending (welcomeInitialState welcomeZeroWords) expression := by
  unfold parsedExprWaitPending
  rw [show (abInitialState input).mvCompletedTags =
      (welcomeInitialState welcomeZeroWords).mvCompletedTags from rfl]

theorem abPE_waitPending_not_correct (expressions : List NormalizedExpr)
    (accepted : checkParsedTopLine (InstructionLine.pe expressions).toParsed = true)
    (pending : (expressions.map NormalizedExpr.toParsed).any
      (parsedExprWaitPending (abInitialState abOneLeftInput)) = true) :
    ¬ ProofsLean.Correct abSealedMachine abSpec
      ([InstructionLine.pe expressions] : List InstructionLine) :=
  ab_not_correct_of_step_none _ _
    (abSealed_step_none_of_unknown (line := .pe expressions)
      (executeNormalizedLine_pe_waitPending expressions (abInitialState abOneLeftInput)
        accepted pending))

theorem abPE_unsupported_not_correct (expressions : List NormalizedExpr)
    (accepted : checkParsedTopLine (InstructionLine.pe expressions).toParsed = true)
    (waitsComplete : (expressions.map NormalizedExpr.toParsed).any
      (parsedExprWaitPending (abInitialState abOneLeftInput)) = false)
    (unsupported : (expressions.map NormalizedExpr.toParsed).any
      parsedExprIsUnsupportedRustAlu = true) :
    ¬ ProofsLean.Correct abSealedMachine abSpec
      ([InstructionLine.pe expressions] : List InstructionLine) :=
  ab_not_correct_of_step_none _ _
    (abSealed_step_none_of_failure (line := .pe expressions)
      (executeNormalizedLine_pe_unsupported expressions (abInitialState abOneLeftInput)
        accepted waitsComplete unsupported))

theorem abPE_notSupported_not_correct (expressions : List NormalizedExpr)
    (accepted : checkParsedTopLine (InstructionLine.pe expressions).toParsed = true)
    (waitsComplete : (expressions.map NormalizedExpr.toParsed).any
      (parsedExprWaitPending (abInitialState abOneLeftInput)) = false)
    (noUnsupported : (expressions.map NormalizedExpr.toParsed).any
      parsedExprIsUnsupportedRustAlu = false)
    (notSupported : (expressions.map NormalizedExpr.toParsed).all
      parsedExprIsSupportedPELineProducer = false) :
    ¬ ProofsLean.Correct abSealedMachine abSpec
      ([InstructionLine.pe expressions] : List InstructionLine) :=
  ab_not_correct_of_step_none _ _
    (abSealed_step_none_of_unknown (line := .pe expressions)
      (executeNormalizedLine_pe_notSupported expressions (abInitialState abOneLeftInput)
        accepted waitsComplete noUnsupported notSupported))

/-! ## 8. `.pe` lines: all-`noforward` -/

/-- **All-`.noforward` lines** never touch the PE register files. -/
theorem abPE_noforward_not_correct (expressions : List NormalizedExpr)
    (all : WelcomeAllNoForward expressions) :
    ¬ ProofsLean.Correct abSealedMachine abSpec
      ([InstructionLine.pe expressions] : List InstructionLine) := by
  cases step : abSealedMachine.step (InstructionLine.pe expressions)
      (abInitialState abOneLeftInput) with
  | none => exact ab_not_correct_of_step_none _ _ step
  | some next =>
      apply ab_not_correct_of_step_frame _ _ next step
      · have executed := abSealed_step_ok step
        exact executeNormalizedLine_pe_peRegisters_noforward expressions _
          next all executed
      · exact abTarget_oneLeft_ne_zero ⟨0, by decide⟩

/-! ## 9. `.pe` lines: a single Welcome `iinc` row

Such a line commits four `.long` writes, i.e. eight of the sixteen observed
words.  `welcomeAnyBaseWord` provides an observed word outside all four write
windows for **every** base, and the committed writes preserve a read of it
(`welcomeWrites_preserves_read_of_outside`).  Neither fact mentions the input,
so the argument runs unchanged on `A = 1.0, B = 0`: the untouched word keeps
its initial `0` while the target is `0x3F800000`. -/

theorem abPE_singleWelcomeLine_not_correct (base : Nat) :
    ¬ ProofsLean.Correct abSealedMachine abSpec
      ([InstructionLine.pe [welcomeExpr base]] : List InstructionLine) := by
  intro correct
  obtain ⟨word, untouched⟩ := welcomeAnyBaseWord base
  obtain ⟨result, executed, post⟩ := correct.2 abOneLeftInput (abSpec_admissible _)
  obtain ⟨next, stepEq, _lineExecuted, _invariant, value⟩ :=
    welcomeSealed_step base (abInitialState abOneLeftInput)
      (abInitialState_invariant abOneLeftInput)
  have executed' : ProofsLean.execute abSealedMachine
      [InstructionLine.pe [welcomeExpr base]] (abInitialState abOneLeftInput) =
      some result := by
    have h := executed
    rw [abSpec_initial] at h
    exact h
  have stepResult : abSealedMachine.step (InstructionLine.pe [welcomeExpr base])
      (abInitialState abOneLeftInput) = some result := by
    simpa [ProofsLean.execute] using executed'
  rw [abSealed_step_eq, stepEq] at stepResult
  have resultEq : result = next := (Option.some.inj stepResult).symm
  subst result
  have readZero : readDirectAccess (next.peRegisters abPE)
      ⟨.lm1, .long, welcomeWordLongAddress word⟩ (welcomeWordIndex word) = 0 := by
    rw [value abPE]
    have preserved := welcomeWrites_preserves_read_of_outside base
      ((abInitialState abOneLeftInput).peRegisters abPE)
      ((abInitialState abOneLeftInput).peRegisters abPE) [0, 1, 2, 3]
      (welcomeWordLongAddress word) (welcomeWordIndex word)
      (by intro c _member; exact untouched c)
    simp only [List.map_cons, List.map_nil] at preserved
    rw [preserved, readDirectAccess_welcomeWord]
    exact abInitialPERegisters_lm1 abOneLeftInput _
  have wordZero : (next.peRegisters abPE).lm1
      ⟨word.val, by have := word.isLt; change word.val < 4096; omega⟩ = 0 := by
    rw [← readDirectAccess_welcomeWord (next.peRegisters abPE) word]
    exact readZero
  have wanted := post word
  rw [wordZero, abTarget_oneLeft] at wanted
  exact absurd wanted.symm (by decide)

/-! ## 10. The residual class of `.pe` lines -/

/-- The four syntactic conditions under which a `.pe` line is not refuted by
the syntactic cases above.  This mirrors `WelcomePEAccepted`, stated with the
`1.a-b` initial state; the two agree because `parsedExprWaitPending` only
inspects `mvCompletedTags`. -/
def AbPEAccepted (expressions : List NormalizedExpr) : Prop :=
  checkParsedTopLine (InstructionLine.pe expressions).toParsed = true ∧
  (expressions.map NormalizedExpr.toParsed).any
      (parsedExprWaitPending (abInitialState abOneLeftInput)) = false ∧
  (expressions.map NormalizedExpr.toParsed).any parsedExprIsUnsupportedRustAlu = false ∧
  (expressions.map NormalizedExpr.toParsed).all parsedExprIsSupportedPELineProducer = true

theorem abPEAccepted_iff_welcome (expressions : List NormalizedExpr) :
    AbPEAccepted expressions ↔ WelcomePEAccepted expressions := by
  unfold AbPEAccepted WelcomePEAccepted
  rw [show (expressions.map NormalizedExpr.toParsed).any
      (parsedExprWaitPending (abInitialState abOneLeftInput)) =
      (expressions.map NormalizedExpr.toParsed).any
        (parsedExprWaitPending (welcomeInitialState welcomeZeroWords)) from
    congrArg (fun pending => (expressions.map NormalizedExpr.toParsed).any pending)
      (funext fun expression => ab_waitPending_eq abOneLeftInput expression)]

/-- **The residual class.** A syntactically accepted `.pe` line that is not
all-`.noforward`.  `WelcomePEUnrefuted` additionally excludes the single
Welcome `iinc` rows; here those are refuted
(`abPE_singleWelcomeLine_not_correct`), so the class is strictly smaller. -/
def AbPEUnrefuted (expressions : List NormalizedExpr) : Prop :=
  AbPEAccepted expressions ∧ ¬ WelcomeAllNoForward expressions

theorem abPEUnrefuted_iff (expressions : List NormalizedExpr) :
    AbPEUnrefuted expressions ↔
      WelcomePEAccepted expressions ∧ ¬ WelcomeAllNoForward expressions := by
  unfold AbPEUnrefuted
  rw [abPEAccepted_iff_welcome]

/-- **Non-vacuity.**  The residual class is inhabited: the constant-one
immediate line of the Welcome chain's `welcomePEUnrefuted_inhabited` is
accepted, is not all-`.noforward`, and is not a Welcome `iinc` row, so it lies
in `AbPEUnrefuted`. -/
theorem abPEUnrefuted_inhabited : AbPEUnrefuted [welcomeImmediateOneExpr] := by
  rw [abPEUnrefuted_iff]
  exact ⟨welcomePEUnrefuted_inhabited.1, welcomePEUnrefuted_inhabited.2.1⟩

/-- Every `.pe` line outside `AbPEUnrefuted` is refuted. -/
theorem abPENotUnrefuted_not_correct (expressions : List NormalizedExpr)
    (outside : ¬ AbPEUnrefuted expressions) :
    ¬ ProofsLean.Correct abSealedMachine abSpec
      ([InstructionLine.pe expressions] : List InstructionLine) := by
  by_cases accepted : AbPEAccepted expressions
  · by_cases allNoforward : WelcomeAllNoForward expressions
    · exact abPE_noforward_not_correct expressions allNoforward
    · exact absurd ⟨accepted, allNoforward⟩ outside
  · by_cases checkTrue : checkParsedTopLine (InstructionLine.pe expressions).toParsed = true
    · by_cases pendingFalse : (expressions.map NormalizedExpr.toParsed).any
          (parsedExprWaitPending (abInitialState abOneLeftInput)) = false
      · by_cases unsupportedFalse : (expressions.map NormalizedExpr.toParsed).any
            parsedExprIsUnsupportedRustAlu = false
        · by_cases supportedTrue : (expressions.map NormalizedExpr.toParsed).all
              parsedExprIsSupportedPELineProducer = true
          · exact absurd ⟨checkTrue, pendingFalse, unsupportedFalse, supportedTrue⟩ accepted
          · have supportedFalse : (expressions.map NormalizedExpr.toParsed).all
                parsedExprIsSupportedPELineProducer = false := by
              cases h : (expressions.map NormalizedExpr.toParsed).all
                  parsedExprIsSupportedPELineProducer <;> simp_all
            exact abPE_notSupported_not_correct expressions checkTrue pendingFalse
              unsupportedFalse supportedFalse
        · have unsupportedTrue : (expressions.map NormalizedExpr.toParsed).any
              parsedExprIsUnsupportedRustAlu = true := by
            cases h : (expressions.map NormalizedExpr.toParsed).any
                parsedExprIsUnsupportedRustAlu <;> simp_all
          exact abPE_unsupported_not_correct expressions checkTrue pendingFalse
            unsupportedTrue
      · have pendingTrue : (expressions.map NormalizedExpr.toParsed).any
            (parsedExprWaitPending (abInitialState abOneLeftInput)) = true := by
          cases h : (expressions.map NormalizedExpr.toParsed).any
              (parsedExprWaitPending (abInitialState abOneLeftInput)) <;> simp_all
        exact abPE_waitPending_not_correct expressions checkTrue pendingTrue
    · have checkFalse : checkParsedTopLine (InstructionLine.pe expressions).toParsed = false := by
        cases h : checkParsedTopLine (InstructionLine.pe expressions).toParsed <;> simp_all
      exact abPE_checkFalse_not_correct expressions checkFalse

/-- Every line of cost below two outside the residual class is refuted. -/
theorem abShortLine_not_correct (line : InstructionLine)
    (short : InstructionLine.cost line < 2)
    (residual : ∀ expressions : List NormalizedExpr, AbPEUnrefuted expressions →
      ¬ ProofsLean.Correct abSealedMachine abSpec
        ([InstructionLine.pe expressions] : List InstructionLine)) :
    ¬ ProofsLean.Correct abSealedMachine abSpec
      ([line] : List InstructionLine) := by
  cases line with
  | pe expressions =>
      by_cases h : AbPEUnrefuted expressions
      · exact residual expressions h
      · exact abPENotUnrefuted_not_correct expressions h
  | nop count wait => exact abNop_not_correct count wait short
  | mv transfer => exact abMv_not_correct transfer

/-- A program of score zero is empty. -/
theorem abScore_eq_zero (p : ProofsLean.Program abSealedMachine) :
    ProofsLean.score abSealedMachine p = 0 ↔ p = [] := by
  constructor
  · cases p with
    | nil => intro _; rfl
    | cons line rest =>
        intro h
        have positive := abSealedMachine.positiveCost line
        simp only [ProofsLean.score] at h
        omega
  · intro h
    rw [h]
    rfl

/-- **`LowerBound abSealedMachine abSpec 2` is equivalent to the unrestricted
one-line statement.** -/
theorem abLowerBound_two_iff_rejects_short_lines :
    ProofsLean.LowerBound abSealedMachine abSpec 2 ↔
      (∀ line : InstructionLine, InstructionLine.cost line < 2 →
        ¬ ProofsLean.Correct abSealedMachine abSpec [line]) := by
  constructor
  · intro lower line short correct
    have bound := lower [line] correct
    have scoreLine : ProofsLean.score abSealedMachine [line] =
        InstructionLine.cost line := rfl
    rw [scoreLine] at bound
    omega
  · intro rejects p correct
    by_contra hle
    have short : ProofsLean.score abSealedMachine p < 2 := by omega
    cases p with
    | nil => exact abEmpty_not_correct correct
    | cons line rest =>
        have positive : 0 < InstructionLine.cost line :=
          abSealedMachine.positiveCost line
        have scoreEq : ProofsLean.score abSealedMachine (line :: rest) =
            InstructionLine.cost line + ProofsLean.score abSealedMachine rest := rfl
        have restZero : ProofsLean.score abSealedMachine rest = 0 := by
          rw [scoreEq] at short
          omega
        have restEmpty : rest = [] := (abScore_eq_zero rest).mp restZero
        subst rest
        have costShort : InstructionLine.cost line < 2 := by
          rw [scoreEq] at short
          simp only [ProofsLean.score] at short
          omega
        exact rejects line costShort correct

/-- **The lower bound from the residual class.** -/
theorem abLowerBound_two_of_residual
    (residual : ∀ expressions : List NormalizedExpr, AbPEUnrefuted expressions →
      ¬ ProofsLean.Correct abSealedMachine abSpec
        ([InstructionLine.pe expressions] : List InstructionLine)) :
    ProofsLean.LowerBound abSealedMachine abSpec 2 := by
  rw [abLowerBound_two_iff_rejects_short_lines]
  intro line short
  exact abShortLine_not_correct line short residual

/-- **The gap, exactly.**  The bound is equivalent to the refutation of the
residual class, so `AbPEUnrefuted` is neither stronger nor weaker than the
missing piece. -/
theorem abLowerBound_two_iff_residual :
    ProofsLean.LowerBound abSealedMachine abSpec 2 ↔
      (∀ expressions : List NormalizedExpr, AbPEUnrefuted expressions →
        ¬ ProofsLean.Correct abSealedMachine abSpec
          ([InstructionLine.pe expressions] : List InstructionLine)) := by
  constructor
  · intro lower expressions _unrefuted
    rw [abLowerBound_two_iff_rejects_short_lines] at lower
    exact lower (.pe expressions) (by simp [InstructionLine.cost])
  · exact abLowerBound_two_of_residual

/-! ## 11. The A − B value argument at a non-zero input

The Welcome chain's narrow shape is stated at the **all-zero** initial state,
where `1.a-b`'s target equals the initial LM1 value, so it cannot refute
anything.  The value argument below is the `1.a-b` analogue of
`welcome_not_correct_of_lm1Narrow` at the input `A = 1.0, B = 0`, where every
target word is `0x3F800000` and an untouched word still reads its initial `0`.

The hypothesis is the *write-list shape at that input*: the line commits a list
of prepared writes whose `.lm1` destinations fit in at most four windows of at
most two words.  Producing that shape from the executor for a non-zero initial
state is the missing executor link (see section 12). -/

/-- **The narrow shape at the `A = 1.0, B = 0` input.**  The line's step from
that input commits a write list whose `.lm1` destinations lie in at most four
windows of at most two words. -/
def ABNarrowAtOnes (expressions : List NormalizedExpr) : Prop :=
  ∀ next, abSealedMachine.step (.pe expressions) (abInitialState abOneLeftInput) = some next →
    ∃ (writes : List PreparedParsedMaskedWrite)
      (windows : List (Fin Bank.lm1.capacity × Nat)),
      next.peRegisters abPE =
        commitParsedMaskedWrites ((abInitialState abOneLeftInput).peRegisters abPE) writes ∧
      (∀ write ∈ writes, ∀ (width : PEMemory.Width) (address : Fin Bank.lm1.capacity),
        write.destination = some ⟨.lm1, width, address⟩ →
          (address, count .lm1 width) ∈ windows) ∧
      windows.length ≤ 4 ∧ (∀ window ∈ windows, window.2 ≤ 2)

/-- **The `1.a-b` narrow refutation.**  A line whose PE 0 write list at
`A = 1.0, B = 0` is narrow is incorrect: some observed word is untouched, keeps
its initial `0`, while the target is `0x3F800000`. -/
theorem ab_not_correct_of_narrowAtOnes (expressions : List NormalizedExpr)
    (shape : ABNarrowAtOnes expressions) :
    ¬ ProofsLean.Correct abSealedMachine abSpec
      ([InstructionLine.pe expressions] : List InstructionLine) := by
  cases step : abSealedMachine.step (.pe expressions) (abInitialState abOneLeftInput) with
  | none => exact ab_not_correct_of_step_none _ _ step
  | some next =>
      intro correct
      obtain ⟨writes, windows, committed, covers, bound, sizes⟩ := shape next step
      obtain ⟨word, untouched⟩ := exists_uncovered_of_windows windows bound sizes
      obtain ⟨result, executed, post⟩ := correct.2 abOneLeftInput (abSpec_admissible _)
      have executed' : ProofsLean.execute abSealedMachine
          [InstructionLine.pe expressions] (abInitialState abOneLeftInput) =
          some result := by
        have h := executed
        rw [abSpec_initial] at h
        exact h
      have stepResult : abSealedMachine.step (InstructionLine.pe expressions)
          (abInitialState abOneLeftInput) = some result := by
        simpa [ProofsLean.execute] using executed'
      rw [step] at stepResult
      have resultEq : result = next := (Option.some.inj stepResult).symm
      subst result
      have zero : (next.peRegisters abPE).lm1 (lm1Target word) = 0 := by
        rw [committed]
        apply commitParsedMaskedWrites_lm1_word_zero
          ((abInitialState abOneLeftInput).peRegisters abPE) writes (lm1Target word)
        · intro write writeMem width address data selection destination dataEq selectionEq
          subst dataEq selectionEq
          have member := covers write writeMem width address destination
          by_cases within : distance .lm1 address (lm1Target word) < count .lm1 width
          · exact absurd within (untouched (address, count .lm1 width) member)
          · exact Or.inl (Nat.le_of_not_lt within)
        · exact abInitialPERegisters_lm1 abOneLeftInput _
      have wordZero : (next.peRegisters abPE).lm1
          ⟨word.val, by have := word.isLt; change word.val < 4096; omega⟩ = 0 := by
        simpa [lm1Target] using zero
      have wanted := post word
      rw [wordZero, abTarget_oneLeft] at wanted
      exact absurd wanted.symm (by decide)

end ProofsLean.MNCore

-- End of module: no sorry, no admit, no native_decide, no new axioms.
