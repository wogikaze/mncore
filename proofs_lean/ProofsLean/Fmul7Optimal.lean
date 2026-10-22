import ProofsLean.WelcomeValueBound
import ProofsLean.LineExec
import ProofsLean.FloatMultiply

/-! # `2.fmul7` — specification, the five-line answer, and the model-gap check

`problems/2.fmul7` asks for `C = A * 7.0` on `32` float words per PE.  The
accepted answer is five issue lines:

```
imm ui"0x40E00000" $t
fvmul $lm0v $aluf $ln0v
fvmul $lm8v $t $ln8v
fvmul $lm16v $t $ln16v
fvmul $lm24v $t $ln24v
```

This module fixes the sealed value model, the five-line answer, its score, the
two-product-per-line rejection (the formal half of the model-gap check), the
executor link that yields `Correct`, and the counting skeleton of the lower
bound.  The full `LowerBound 5` over every `InstructionLine` is **not** claimed
here; the remaining per-line shape obligation is named explicitly.

No `sorry`, no `admit`, no `native_decide`, no new axioms.
-/

namespace ProofsLean.MNCore

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

open Issue
open PEMemory

/-! ## 1. Input, initial state, target -/

/-- The observed PE's 32 input floats.  Only PE 0 is observed here; this is the
weaker (easier) specification, so a lower bound for it is a lower bound for the
official per-PE specification. -/
abbrev Fmul7Input := Fin 32 → BitVec 32

/-- `Fin 32` as an LM0 address. -/
def fmul7Lm0Index (word : Fin 32) : Fin PEMemory.Bank.lm0.capacity :=
  Fin.castLE (by decide : 32 ≤ PEMemory.Bank.lm0.capacity) word

/-- `Fin 32` as an LM1 address. -/
def fmul7Lm1Index (word : Fin 32) : Fin PEMemory.Bank.lm1.capacity :=
  Fin.castLE (by decide : 32 ≤ PEMemory.Bank.lm1.capacity) word

theorem fmul7Lm0Index_val (word : Fin 32) : (fmul7Lm0Index word).val = word.val := rfl

theorem fmul7Lm1Index_val (word : Fin 32) : (fmul7Lm1Index word).val = word.val := rfl

/-- PE 0's initial register file: the input in LM0 words `0..31`, everything
else zero.  Other PEs keep the simulator's zero file. -/
def fmul7InitialPERegisters (input : Fmul7Input) (pe : PEId) : IntegerRegisterFiles :=
  if pe.val = 0 then
    { zeroInitialPERegisterFiles with
      lm0 := fun address =>
        if h : address.val < 32 then input ⟨address.val, h⟩ else 0 }
  else zeroInitialPERegisterFiles

/-- The whole-machine initial state of the sealed model. -/
def fmul7InitialState (input : Fmul7Input) : State :=
  { rustSimulatorInitialState with
    peRegisters := fmul7InitialPERegisters input }

theorem fmul7InitialState_peRegisters (input : Fmul7Input) (pe : PEId) :
    (fmul7InitialState input).peRegisters pe = fmul7InitialPERegisters input pe := rfl

theorem fmul7InitialState_lm0 (input : Fmul7Input) (word : Fin 32) :
    ((fmul7InitialState input).peRegisters 0).lm0 (fmul7Lm0Index word) = input word := by
  rw [show (fmul7InitialState input).peRegisters 0 = fmul7InitialPERegisters input 0 from rfl]
  unfold fmul7InitialPERegisters
  simp only [Fin.val_zero, ite_true]
  rw [dif_pos (show (fmul7Lm0Index word).val < 32 by
    rw [fmul7Lm0Index_val]; exact word.isLt)]
  congr 1

theorem fmul7InitialState_lm1_zero (input : Fmul7Input) (word : Fin 32) :
    ((fmul7InitialState input).peRegisters 0).lm1 (fmul7Lm1Index word) = 0 := by
  rw [fmul7InitialState_peRegisters]
  unfold fmul7InitialPERegisters
  split <;> simp [zeroInitialPERegisterFiles]

theorem fmul7InitialState_t_zero (input : Fmul7Input) (address : Fin PEMemory.Bank.t.capacity) :
    ((fmul7InitialState input).peRegisters 0).t address = 0 := by
  rw [fmul7InitialState_peRegisters]
  unfold fmul7InitialPERegisters
  split <;> simp [zeroInitialPERegisterFiles]

/-- The exact value the model's `fvmul` produces for the constant `7.0`. -/
def fmul7Target (input : Fmul7Input) (index : Fin 32) : BitVec 32 :=
  FloatMultiply.multiply (input index) FloatMultiply.seven

/-- The sealed value model, exactly as `mul7SealedMachine`: the real `State`,
`executeNormalizedLine` as the step, and issue/hazard history sealed away. -/
noncomputable def fmul7SealedMachine : ProofsLean.Machine where
  Line := InstructionLine
  State := State
  Input := Fmul7Input
  step := fun line state =>
    match executeNormalizedLine line.toNormalizedLine state with
    | .ok next => some next
    | _ => none
  legal := fun _ => True
  lineCost := InstructionLine.cost
  positiveCost := InstructionLine.cost_positive

/-- PE 0's `LM1` words `0..31` must be `A * 7.0`. -/
noncomputable def fmul7Spec : ProofsLean.Problem fmul7SealedMachine where
  admissible := fun _ => True
  initial := fmul7InitialState
  post := fun input state => ∀ index : Fin 32,
    (state.peRegisters 0).lm1 (fmul7Lm1Index index) = fmul7Target input index

theorem fmul7Spec_initial (input : Fmul7Input) :
    fmul7Spec.initial input = fmul7InitialState input := rfl

theorem fmul7Spec_admissible (input : Fmul7Input) : fmul7Spec.admissible input := trivial

/-! ## 2. The five-line answer -/

/-- A `.long` region at `base`: four cycles at `base, base+2, base+4, base+6`,
each writing two words. -/
def fmul7LongRegion (base : Nat) : Region :=
  ⟨2, base, base + 2, base + 4, base + 6, false, none⟩

def fmul7TLong : ParsedOperand :=
  .mem ⟨.t, fmul7LongRegion 0⟩ false false false none

def fmul7Lm0Long (base : Nat) : ParsedOperand :=
  .mem ⟨.lm0, fmul7LongRegion base⟩ false false false none

def fmul7Lm1Long (base : Nat) : ParsedOperand :=
  .mem ⟨.lm1, fmul7LongRegion base⟩ false false false none

/-- `imm ui"0x40E00000" $t`: the float `7.0` in `$t` (and on `$aluf`). -/
def fmul7ImmExpr : NormalizedExpr where
  op := .immediate 0x40E00000 false
  sources := []
  destinations := [fmul7TLong]
  flush := none

/-- `fvmul $lm<base>v $t $ln<base>v`: eight output floats from the eight input
floats at `base`. -/
def fmul7MulExpr (base : Nat) : NormalizedExpr where
  op := .mau .f false .mul none false
  sources := [fmul7Lm0Long base, fmul7TLong]
  destinations := [fmul7Lm1Long base]
  flush := none

/-- `fvmul $t $t $ln<base>v`: the all-`$t` form used to test the same-line
constant hole.  It has no LM0 read, so the immediate-excludes-LM0 rule does not
apply. -/
def fmul7MulTExpr (base : Nat) : NormalizedExpr where
  op := .mau .f false .mul none false
  sources := [fmul7TLong, fmul7TLong]
  destinations := [fmul7Lm1Long base]
  flush := none

/-- The accepted five-line answer (the first `fvmul` may equivalently read
`$aluf`; this module uses `$t` for all four to keep one source form). -/
def fmul7Answer : ProofsLean.Program fmul7SealedMachine :=
  [.pe [fmul7ImmExpr],
   .pe [fmul7MulExpr 0],
   .pe [fmul7MulExpr 8],
   .pe [fmul7MulExpr 16],
   .pe [fmul7MulExpr 24]]

theorem fmul7Answer_length : fmul7Answer.length = 5 := rfl

theorem fmul7Answer_score :
    ProofsLean.score fmul7SealedMachine fmul7Answer = 5 := rfl

/-! ## 3. Model-gap check: two calculations cannot share a line -/

/-- Two parsed expressions that share an issue group are rejected by the local
issue checker.  This is the `groupsUnique` component of `Legal`. -/
theorem checkParsedLine_pair_same_group_rejected (e f : ParsedExpr) (group : Group)
    (eGroup : e.issueGroup = some group) (fGroup : f.issueGroup = some group) :
    checkParsedLine [e, f] = false := by
  have notLegal : ¬ LegalParsedLine [e, f] := by
    intro legal
    have groups : groupsUnique (projectLine [e, f]) := legal.2.1
    have memoryE : e.toIssueExpr 0 ∈ projectLine [e, f] := by
      simp [projectLine, projectFrom]
    have memoryF : f.toIssueExpr 1 ∈ projectLine [e, f] := by
      simp [projectLine, projectFrom]
    have ids : (e.toIssueExpr 0).id ≠ (f.toIssueExpr 1).id := by
      simp [ParsedExpr.toIssueExpr]
    have sameGroup : (e.toIssueExpr 0).group = some group := by
      simpa [ParsedExpr.toIssueExpr] using eGroup
    have otherGroup : (f.toIssueExpr 1).group = some group := by
      simpa [ParsedExpr.toIssueExpr] using fGroup
    exact (groups (e.toIssueExpr 0) memoryE (f.toIssueExpr 1) memoryF ids group sameGroup)
      otherGroup
  cases checked : checkParsedLine [e, f] with
  | false => rfl
  | true => exact False.elim (notLegal (parsed_check_sound [e, f] checked))

/-- Two `fvmul` expressions in one issue line are rejected: both are in the
single `.mauCalc` issue group.  This rules out a 16-word product line. -/
theorem fmul7_two_products_same_line_rejected (base₀ base₁ : Nat) :
    checkParsedLine
      [(fmul7MulExpr base₀).toParsed, (fmul7MulExpr base₁).toParsed] = false :=
  checkParsedLine_pair_same_group_rejected _ _ .mauCalc rfl rfl

/-- Consequently `executeNormalizedLine` on a two-product line fails, because
`executeIntegerProducerInstructionLine` starts with `checkParsedTopLine`. -/
theorem fmul7_two_products_line_step_failure (base₀ base₁ : Nat) (state : State) :
    executeNormalizedLine
      (.pe [fmul7MulExpr base₀, fmul7MulExpr base₁]) state = .failure := by
  have checked : checkParsedTopLine
      (InstructionLine.pe [fmul7MulExpr base₀, fmul7MulExpr base₁]).toParsed = false := by
    simpa [checkParsedTopLine, InstructionLine.toParsed, NormalizedExpr.toParsed] using
      fmul7_two_products_same_line_rejected base₀ base₁
  unfold executeNormalizedLine
  simp only [NormalizedLine.toInstruction?]
  unfold executeIntegerProducerInstructionLine
  rw [checked]
  rfl

/-- **The same-line `imm` + LM0-reading `fvmul` is issue-rejected** by SDM 3.6.1's
"immediate excludes LM0 access" rule.  This closes the four-line hole
`[imm+fvmul, fvmul, fvmul, fvmul]` at the issue checker, before any value
argument. -/
theorem fmul7_imm_plus_product_same_line_rejected (base : Nat) :
    checkParsedLine [fmul7ImmExpr.toParsed, (fmul7MulExpr base).toParsed] = false := by
  have notLegal : ¬ LegalParsedLine [fmul7ImmExpr.toParsed, (fmul7MulExpr base).toParsed] := by
    intro legal
    rcases legal with ⟨_, _, _, _, _, _, _, _, _, _, immediate, _, _, _, _, _, _⟩
    have immMem : fmul7ImmExpr.toParsed.toIssueExpr 0 ∈
        projectLine [fmul7ImmExpr.toParsed, (fmul7MulExpr base).toParsed] := by
      simp [projectLine, projectFrom]
    have mulMem : (fmul7MulExpr base).toParsed.toIssueExpr 1 ∈
        projectLine [fmul7ImmExpr.toParsed, (fmul7MulExpr base).toParsed] := by
      simp [projectLine, projectFrom]
    have immFlag : (fmul7ImmExpr.toParsed.toIssueExpr 0).immediate = true := rfl
    have readsEq : ((fmul7MulExpr base).toParsed.toIssueExpr 1).reads =
        [⟨.lm0, fmul7LongRegion base⟩, ⟨.t, fmul7LongRegion 0⟩] := rfl
    have readMem : (⟨.lm0, fmul7LongRegion base⟩ : Access) ∈
        ((fmul7MulExpr base).toParsed.toIssueExpr 1).reads := by
      rw [readsEq]
      simp
    have noLm0 := (immediate _ immMem immFlag).1 _ mulMem
      (⟨.lm0, fmul7LongRegion base⟩ : Access) readMem
    exact noLm0 rfl
  cases checked : checkParsedLine [fmul7ImmExpr.toParsed, (fmul7MulExpr base).toParsed] with
  | false => rfl
  | true => exact False.elim (notLegal (parsed_check_sound _ checked))

/-- The four-line shape `[imm+fvmul, fvmul, fvmul, fvmul]` fails at its first
line: the combined line is rejected. -/
theorem fmul7_four_line_imm_plus_product_step_failure
    (base₀ base₁ base₂ : Nat) (state : State) :
    executeNormalizedLine
      (.pe [fmul7ImmExpr, fmul7MulExpr base₀]) state = .failure := by
  have checked : checkParsedTopLine
      (InstructionLine.pe [fmul7ImmExpr, fmul7MulExpr base₀]).toParsed = false := by
    simpa [checkParsedTopLine, InstructionLine.toParsed, NormalizedExpr.toParsed] using
      fmul7_imm_plus_product_same_line_rejected base₀
  unfold executeNormalizedLine
  simp only [NormalizedLine.toInstruction?]
  unfold executeIntegerProducerInstructionLine
  rw [checked]
  rfl

/-! ## 4. The executor link and `Correct` -/

/-- The exact execution/value obligation for the five-line answer.  It is the
missing executor algebra: five line steps at every input and the `LM1`
readback.  Nothing below assumes it; `fmul7Answer_correct_of_link` is the
conditional consumer. -/
structure Fmul7AnswerExecutorLink : Prop where
  executes : ∀ input : Fmul7Input, ∃ result : State,
    ProofsLean.execute fmul7SealedMachine fmul7Answer (fmul7InitialState input) = some result
  values : ∀ (input : Fmul7Input) (result : State),
    ProofsLean.execute fmul7SealedMachine fmul7Answer (fmul7InitialState input) = some result →
    ∀ index : Fin 32,
      (result.peRegisters 0).lm1 (fmul7Lm1Index index) = fmul7Target input index

/-- **The five-line answer is `Correct` once its executor link is supplied.** -/
theorem fmul7Answer_correct_of_link (link : Fmul7AnswerExecutorLink) :
    ProofsLean.Correct fmul7SealedMachine fmul7Spec fmul7Answer := by
  refine ⟨trivial, fun input _ => ?_⟩
  obtain ⟨result, executed⟩ := link.executes input
  exact ⟨result, executed, link.values input result executed⟩

/-! ## 5. The counting skeleton of the lower bound -/

/-- The eight output words covered by the product at `slot`: words
`8 * slot .. 8 * slot + 7`. -/
def fmul7Window (slot : Fin 4) : Finset (Fin 32) :=
  Finset.univ.filter fun index => index.val / 8 = slot.val

theorem fmul7Window_card (slot : Fin 4) : (fmul7Window slot).card = 8 := by
  revert slot
  decide

theorem fmul7Window_disjoint {left right : Fin 4} (different : left ≠ right) :
    Disjoint (fmul7Window left) (fmul7Window right) := by
  rw [Finset.disjoint_left]
  intro index leftMem rightMem
  simp only [fmul7Window, Finset.mem_filter, Finset.mem_univ, true_and] at leftMem rightMem
  have equal : left.val = right.val := by omega
  exact different (Fin.ext equal)

/-- Three windows of at most eight words cannot cover the 32 output words. -/
theorem fmul7_exists_uncovered_of_three (first second third : Finset (Fin 32))
    (firstCard : first.card ≤ 8) (secondCard : second.card ≤ 8) (thirdCard : third.card ≤ 8) :
    ∃ index : Fin 32, index ∉ first ∪ second ∪ third := by
  have unionCard : (first ∪ second ∪ third).card ≤ 24 := by
    have h₁ : (first ∪ second).card ≤ first.card + second.card := Finset.card_union_le _ _
    have h₂ : (first ∪ second ∪ third).card ≤ (first ∪ second).card + third.card :=
      Finset.card_union_le _ _
    omega
  have universeCard : (Finset.univ : Finset (Fin 32)).card = 32 := by decide
  have strict : (first ∪ second ∪ third).card <
      (Finset.univ : Finset (Fin 32)).card := by omega
  obtain ⟨index, _, uncovered⟩ := Finset.exists_mem_notMem_of_card_lt_card strict
  exact ⟨index, uncovered⟩

/-- The per-line shape obligation: the constant line does not touch `LM1`, a
product line leaves words outside its window and the `t` bank unchanged, and a
product line executed with a zero `t` bank writes zero in its window. -/
structure Fmul7LineShapeResidual : Prop where
  constFrame : ∀ (state next : State),
    executeNormalizedLine (.pe [fmul7ImmExpr]) state = .ok next →
    ∀ index : Fin 32,
      (next.peRegisters 0).lm1 (fmul7Lm1Index index) =
        (state.peRegisters 0).lm1 (fmul7Lm1Index index)
  productFrame : ∀ (slot : Fin 4) (state next : State),
    executeNormalizedLine (.pe [fmul7MulExpr (8 * slot.val)]) state = .ok next →
    ∀ index : Fin 32, index ∉ fmul7Window slot →
      (next.peRegisters 0).lm1 (fmul7Lm1Index index) =
        (state.peRegisters 0).lm1 (fmul7Lm1Index index)
  productTFrame : ∀ (slot : Fin 4) (state next : State),
    executeNormalizedLine (.pe [fmul7MulExpr (8 * slot.val)]) state = .ok next →
    ∀ address, (next.peRegisters 0).t address = (state.peRegisters 0).t address
  productZero : ∀ (slot : Fin 4) (state next : State),
    (∀ address, (state.peRegisters 0).t address = 0) →
    executeNormalizedLine (.pe [fmul7MulExpr (8 * slot.val)]) state = .ok next →
    ∀ index : Fin 32, index ∈ fmul7Window slot →
      (next.peRegisters 0).lm1 (fmul7Lm1Index index) = 0

/-! ## 6. Shape classes and the frame/zero invariants -/

/-- The constant line `imm 7.0 $t`. -/
def Fmul7ConstLine (line : InstructionLine) : Prop :=
  line = .pe [fmul7ImmExpr]

/-- A canonical product line `fvmul $lm<8*slot>v $t $ln<8*slot>v`. -/
def Fmul7ProductLine (line : InstructionLine) : Prop :=
  ∃ slot : Fin 4, line = .pe [fmul7MulExpr (8 * slot.val)]

/-- The syntactic shape class of the answer: one constant line and four
canonical product lines. -/
def Fmul7ShapeLine (line : InstructionLine) : Prop :=
  Fmul7ConstLine line ∨ Fmul7ProductLine line

theorem fmul7_step_ok {line : InstructionLine} {state next : State}
    (executed : fmul7SealedMachine.step line state = some next) :
    executeNormalizedLine line.toNormalizedLine state = .ok next := by
  unfold fmul7SealedMachine at executed
  cases result : executeNormalizedLine line.toNormalizedLine state with
  | ok value => simpa [result] using executed
  | failure => simp [result] at executed
  | unknown => simp [result] at executed

/-- A shape program leaves every output word outside all product windows at its
initial value. -/
theorem fmul7_shape_frame
    (residual : Fmul7LineShapeResidual)
    (program : List InstructionLine)
    (shape : ∀ line ∈ program, Fmul7ShapeLine line)
    (index : Fin 32)
    (outside : ∀ line ∈ program, ∀ slot : Fin 4,
      line = .pe [fmul7MulExpr (8 * slot.val)] → index ∉ fmul7Window slot)
    (state next : State)
    (executed : ProofsLean.execute fmul7SealedMachine program state = some next) :
    (next.peRegisters 0).lm1 (fmul7Lm1Index index) =
      (state.peRegisters 0).lm1 (fmul7Lm1Index index) := by
  induction program generalizing state with
  | nil =>
      simp only [ProofsLean.execute] at executed
      injection executed with equal
      subst equal
      rfl
  | cons line rest ih =>
      simp only [ProofsLean.execute] at executed
      cases step : fmul7SealedMachine.step line state with
      | none => simp [step] at executed
      | some mid =>
          simp [step] at executed
          have lineFrame : (mid.peRegisters 0).lm1 (fmul7Lm1Index index) =
              (state.peRegisters 0).lm1 (fmul7Lm1Index index) := by
            rcases shape line (by simp) with const | ⟨slot, product⟩
            · rw [const] at step
              exact residual.constFrame state mid (fmul7_step_ok step) index
            · rw [product] at step
              exact residual.productFrame slot state mid (fmul7_step_ok step) index
                (outside line (by simp) slot product)
          rw [ih (fun l mem => shape l (List.mem_cons_of_mem _ mem))
            (fun l mem slot product => outside l (List.mem_cons_of_mem _ mem) slot product)
            mid executed, lineFrame]

/-- A shape program consisting only of product lines, started with a zero `LM1`
and a zero `t` bank, ends with a zero `LM1` and a zero `t` bank. -/
theorem fmul7_products_zero
    (residual : Fmul7LineShapeResidual)
    (program : List InstructionLine)
    (allProducts : ∀ line ∈ program, Fmul7ProductLine line)
    (state next : State)
    (lm1Zero : ∀ index : Fin 32, (state.peRegisters 0).lm1 (fmul7Lm1Index index) = 0)
    (tZero : ∀ address, (state.peRegisters 0).t address = 0)
    (executed : ProofsLean.execute fmul7SealedMachine program state = some next) :
    (∀ index : Fin 32, (next.peRegisters 0).lm1 (fmul7Lm1Index index) = 0) ∧
      (∀ address, (next.peRegisters 0).t address = 0) := by
  induction program generalizing state with
  | nil =>
      simp only [ProofsLean.execute] at executed
      injection executed with equal
      subst equal
      exact ⟨lm1Zero, tZero⟩
  | cons line rest ih =>
      simp only [ProofsLean.execute] at executed
      cases step : fmul7SealedMachine.step line state with
      | none => simp [step] at executed
      | some mid =>
          simp [step] at executed
          obtain ⟨slot, product⟩ := allProducts line (by simp)
          have normEq : line.toNormalizedLine =
              .pe [fmul7MulExpr (8 * slot.val)] := by
            rw [product]
            rfl
          have ok : executeNormalizedLine (.pe [fmul7MulExpr (8 * slot.val)]) state = .ok mid := by
            rw [← normEq]
            exact fmul7_step_ok step
          have midT : ∀ address, (mid.peRegisters 0).t address = 0 := by
            intro address
            rw [residual.productTFrame slot state mid ok address]
            exact tZero address
          have midLm1 : ∀ index : Fin 32, (mid.peRegisters 0).lm1 (fmul7Lm1Index index) = 0 := by
            intro index
            by_cases within : index ∈ fmul7Window slot
            · exact residual.productZero slot state mid tZero ok index within
            · rw [residual.productFrame slot state mid ok index within]
              exact lm1Zero index
          exact ih (fun l mem => allProducts l (List.mem_cons_of_mem _ mem))
            mid midLm1 midT executed

/-! ## 7. The all-ones witness and the counting theorem -/

/-- The all-`1.0` input: every target word is `7.0`. -/
def fmul7AllOnes : Fmul7Input := fun _ => 0x3F800000

theorem fmul7Target_allOnes (index : Fin 32) :
    fmul7Target fmul7AllOnes index = 0x40E00000 := by
  simp [fmul7Target, fmul7AllOnes, FloatMultiply.multiply]
  decide

theorem fmul7Target_allOnes_ne_zero (index : Fin 32) :
    fmul7Target fmul7AllOnes index ≠ 0 := by
  rw [fmul7Target_allOnes]
  decide

/-- A shape program's score is its length: every shape line is a `.pe` line. -/
theorem fmul7_shape_score_eq_length (program : List InstructionLine)
    (shape : ∀ line ∈ program, Fmul7ShapeLine line) :
    ProofsLean.score fmul7SealedMachine program = program.length := by
  induction program with
  | nil => rfl
  | cons line rest inductionHypothesis =>
      have cost : fmul7SealedMachine.lineCost line = 1 := by
        rcases shape line (by simp) with const | ⟨slot, product⟩
        · rw [const]
          rfl
        · rw [product]
          rfl
      have tail := inductionHypothesis (fun l mem => shape l (List.mem_cons_of_mem _ mem))
      simp only [ProofsLean.score, List.length_cons]
      rw [cost, tail]
      omega

/-- **The combinatorial coverage obligation.**  A shape program of at most four
lines either has one output word outside every product window, or all of its
lines are products.  This is a finite statement about the five shape forms; it
is separated from the executor argument so that the semantic part is reusable. -/
def Fmul7ShapeCoverage (program : List InstructionLine) : Prop :=
  (∃ index : Fin 32, ∀ line ∈ program, ∀ slot : Fin 4,
    line = .pe [fmul7MulExpr (8 * slot.val)] → index ∉ fmul7Window slot) ∨
  (∀ line ∈ program, Fmul7ProductLine line)

/-- **`score ≥ 5` for every correct shape program**, from the per-line shape
contract and the finite coverage obligation.  This is *not* `LowerBound`: the
shape restriction and the two residual Props are hypotheses. -/
theorem fmul7_shape_score_five
    (residual : Fmul7LineShapeResidual)
    (coverage : ∀ program : List InstructionLine, program.length ≤ 4 →
      (∀ line ∈ program, Fmul7ShapeLine line) → Fmul7ShapeCoverage program)
    (program : List InstructionLine)
    (shape : ∀ line ∈ program, Fmul7ShapeLine line)
    (correct : ProofsLean.Correct fmul7SealedMachine fmul7Spec program) :
    5 ≤ ProofsLean.score fmul7SealedMachine program := by
  rw [fmul7_shape_score_eq_length program shape]
  by_cases short : program.length ≤ 4
  · obtain ⟨result, executed, post⟩ := correct.2 fmul7AllOnes trivial
    have postZero := post ⟨0, by decide⟩
    rcases coverage program short shape with uncovered | allProducts
    · obtain ⟨index, outside⟩ := uncovered
      have frame := fmul7_shape_frame residual program shape index outside
        (fmul7InitialState fmul7AllOnes) result executed
      have initialZero := fmul7InitialState_lm1_zero fmul7AllOnes index
      have zero : (result.peRegisters 0).lm1 (fmul7Lm1Index index) = 0 := by
        rw [frame, initialZero]
      have targetNe : fmul7Target fmul7AllOnes index ≠ 0 :=
        fmul7Target_allOnes_ne_zero index
      have postZero' : (result.peRegisters 0).lm1 (fmul7Lm1Index index) =
          fmul7Target fmul7AllOnes index := post index
      exact False.elim (targetNe (by rw [← postZero', zero]))
    · have zeroAll := fmul7_products_zero residual program allProducts
        (fmul7InitialState fmul7AllOnes) result
        (fun index => fmul7InitialState_lm1_zero fmul7AllOnes index)
        (fun address => fmul7InitialState_t_zero fmul7AllOnes address)
        executed
      have targetNe : fmul7Target fmul7AllOnes 0 ≠ 0 :=
        fmul7Target_allOnes_ne_zero 0
      have zeroZero : (result.peRegisters 0).lm1 (fmul7Lm1Index 0) = 0 := zeroAll.1 0
      have postZero' : (result.peRegisters 0).lm1 (fmul7Lm1Index 0) =
          fmul7Target fmul7AllOnes 0 := post 0
      exact False.elim (targetNe (by rw [← postZero', zeroZero]))
  · omega

/-! ## 8. Trust report -/

#print axioms fmul7Answer_score
#print axioms fmul7_two_products_same_line_rejected
#print axioms fmul7_two_products_line_step_failure
#print axioms fmul7_imm_plus_product_same_line_rejected
#print axioms fmul7_four_line_imm_plus_product_step_failure
#print axioms fmul7Answer_correct_of_link
#print axioms fmul7_shape_score_five

end ProofsLean.MNCore
