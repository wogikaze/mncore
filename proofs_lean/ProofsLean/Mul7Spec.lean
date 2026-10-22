import ProofsLean.WelcomeOptimal
import ProofsLean.SingleFMA

/-! # Problem `4.mul7` — the specification on the sealed whole-machine value model

`problems/challenge/4.mul7` ("Mul 7") asks for

> `Y[i] = X[i] * 7` for every `i`, with `X : ULong $lm[0:32]` shaped
> `(16_MAB:1, 4_PE:1, 16:1)` and `Y : ULong $ln[0:32]` of the same shape,
> `0 <= X[i] <= 1000`.

So the reference semantics is **integer** multiplication by `7`, on `1024`
output words: `16 MAB x 4 PE x 16 ULong` per PE.

## The domain actually admitted here

`X[i] <= 1000` is the problem's own bound (`problem.md`), and the shipped
testcase `testcase.vsm` only contains values in `0..1000`. Because
`X[i] <= 1000 < 2^32` the high 32-bit half of every input `ULong` is zero, so
the input is represented below by its low 32-bit half (`Mul7Input`), with the
initial state writing that half into the even LM1/LM0 32-bit word of each lane
and `0` into the odd one. This is exactly the `ULong` little-endian image of the
problem's input, and it is the only place where the representation is chosen.

The output relation is **bit exact**: the even word of lane `w` must hold
`7 * X[w]` (no wrap is possible: `7 * 1000 = 7000 < 2^32`), and the odd word
must stay `0`. Because `7 * X <= 7000` the reference `ULong` value is exactly
`7 * X`, so the bit-exact relation is the problem's relation.

## The machine

`mul7SealedMachine` is the same sealed value model as
`ProofsLean/WelcomeOptimal.lean`'s `welcomeSealedMachine`:
`Line := InstructionLine`, the real `State`, and `step` is the value transition
`executeNormalizedLine` that `wholeMachine.step` invokes *after* its issue,
address-mode and hazard-history checks. The hazard-history rejection layer and
the `.failure` / `.unknown` distinction are sealed away, and `legal` is `True`.
Every theorem about `mul7SealedMachine` carries that restriction.

Only the 64 PEs of board `0` are constrained (`16 MAB x 4 PE`), matching the
testcase, which only reads `n0c0b0m{0..15}p{0..3}`. The remaining `4032` PEs of
the real machine carry no specification here: this is a **weaker** requirement
than the official one, which is the sound direction for a lower bound (a
correct program for the official problem is correct here).

## Results

* `mul7InitialPERegisters_lm0_low` / `_lm0_high` / `_lm1` — the initial memory
  image.
* `mul7Spec_admissible_input` — the domain is non-empty.
* `mul7Spec_required_low` — for the all-`5` input every even word of every
  observed lane must become `35`, while it starts at `0`.

No `sorry`, no `admit`, no `native_decide`, no new axioms, no edited module.
-/

namespace ProofsLean.MNCore

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

open Issue
open PEMemory

/-! ## 1. Input, PE coordinates, lanes -/

/-- The `4.mul7` input: the low `32` bits of the `16 x 4 x 16` input `ULong`s,
indexed by `(MAB, PE, word)`. Admissible inputs have `toNat <= 1000`, so the high
half of the source `ULong` is zero and this is the whole value. -/
abbrev Mul7Input := Fin 16 → Fin 4 → Fin 16 → BitVec 32

/-- Board `0`, `MAB = m`, `PE = p` is the linear PE index `4 * m + p`; the
testcase's flat output order `(m, p, word)` is `((4 * m + p) * 16 + word)`. -/
def mul7PE (m : Fin 16) (p : Fin 4) : PEId := ⟨4 * m.val + p.val, by omega⟩

theorem mul7PE_val (m : Fin 16) (p : Fin 4) : (mul7PE m p).val = 4 * m.val + p.val := rfl

/-- The even `32`-bit word of lane `w`: the low half of the `ULong`. -/
def mul7Low (w : Fin 16) : Fin Bank.lm1.capacity :=
  ⟨2 * w.val, by have := w.isLt; change 2 * w.val < 4096; omega⟩

/-- The odd `32`-bit word of lane `w`: the high half of the `ULong`. -/
def mul7High (w : Fin 16) : Fin Bank.lm1.capacity :=
  ⟨2 * w.val + 1, by have := w.isLt; change 2 * w.val + 1 < 4096; omega⟩

theorem mul7Low_val (w : Fin 16) : (mul7Low w).val = 2 * w.val := rfl

theorem mul7High_val (w : Fin 16) : (mul7High w).val = 2 * w.val + 1 := rfl

theorem mul7Low_injective : Function.Injective mul7Low := by
  intro a b equal
  have values := congrArg Fin.val equal
  simp only [mul7Low_val] at values
  exact Fin.ext (by omega)

/-- The `(MAB, PE)` lane of a PE, or `none` outside board `0`'s 64 PEs. -/
def mul7LaneOfPE (pe : PEId) : Option (Fin 16 × Fin 4) :=
  if h : pe.val < 64 then
    some (⟨pe.val / 4, by omega⟩, ⟨pe.val % 4, Nat.mod_lt _ (by decide)⟩)
  else none

theorem mul7LaneOfPE_observed (m : Fin 16) (p : Fin 4) :
    mul7LaneOfPE (mul7PE m p) = some (m, p) := by
  have bounded : (mul7PE m p).val < 64 := by
    have hm := m.isLt
    have hp := p.isLt
    rw [mul7PE_val]
    omega
  unfold mul7LaneOfPE
  rw [dif_pos bounded]
  simp only [Option.some.injEq, Prod.mk.injEq]
  have hval : (mul7PE m p).val = 4 * m.val + p.val := mul7PE_val m p
  constructor
  · apply Fin.ext
    simp only [hval]
    omega
  · apply Fin.ext
    simp only [hval]
    omega

/-! ## 2. The initial state -/

/-- Zeroed files with the input in the even LM0 word of each of the 16 lanes of
this PE; the odd (`ULong` high) word is zero. -/
def mul7InitialPERegisters (input : Mul7Input) (pe : PEId) : IntegerRegisterFiles :=
  match mul7LaneOfPE pe with
  | none => zeroInitialPERegisterFiles
  | some lane =>
      { zeroInitialPERegisterFiles with
        lm0 := fun address =>
          if h : address.val < 32 ∧ address.val % 2 = 0 then
            input lane.1 lane.2 ⟨address.val / 2, by have := h.1; omega⟩
          else 0 }

/-- The initial whole-machine state of `4.mul7`: the simulator default with the
input installed in LM0 of board `0`'s 64 PEs. -/
def mul7InitialState (input : Mul7Input) : State :=
  { rustSimulatorInitialState with
    peRegisters := fun pe => mul7InitialPERegisters input pe }

theorem mul7InitialState_peRegisters (input : Mul7Input) (pe : PEId) :
    (mul7InitialState input).peRegisters pe = mul7InitialPERegisters input pe := rfl

theorem mul7InitialPERegisters_lm1 (input : Mul7Input) (pe : PEId)
    (address : Fin Bank.lm1.capacity) :
    (mul7InitialPERegisters input pe).lm1 address = 0 := by
  unfold mul7InitialPERegisters
  split
  · simp [zeroInitialPERegisterFiles]
  · simp [zeroInitialPERegisterFiles]

theorem mul7InitialState_lm1 (input : Mul7Input) (pe : PEId)
    (address : Fin Bank.lm1.capacity) :
    ((mul7InitialState input).peRegisters pe).lm1 address = 0 := by
  rw [mul7InitialState_peRegisters]
  exact mul7InitialPERegisters_lm1 input pe address

theorem mul7InitialPERegisters_lm0_low (input : Mul7Input) (m : Fin 16)
    (p : Fin 4) (w : Fin 16) :
    (mul7InitialPERegisters input (mul7PE m p)).lm0 (mul7Low w) = input m p w := by
  simp only [mul7InitialPERegisters, mul7LaneOfPE_observed m p, mul7Low, Fin.val_mk]
  have lowLt : 2 * w.val < 32 := by have := w.isLt; omega
  have even : 2 * w.val % 2 = 0 := by omega
  rw [dif_pos ⟨lowLt, even⟩]
  exact congrArg (input m p) (Fin.ext (by show 2 * w.val / 2 = w.val; omega))

theorem mul7InitialPERegisters_lm0_high (input : Mul7Input) (m : Fin 16)
    (p : Fin 4) (w : Fin 16) :
    (mul7InitialPERegisters input (mul7PE m p)).lm0 (mul7High w) = 0 := by
  simp only [mul7InitialPERegisters, mul7LaneOfPE_observed m p, mul7High, Fin.val_mk]
  have odd : ¬ (2 * w.val + 1 < 32 ∧ (2 * w.val + 1) % 2 = 0) := by
    intro h
    have := h.2
    omega
  rw [dif_neg odd]

theorem mul7InitialPERegisters_other (input : Mul7Input) (pe : PEId)
    (outside : 64 ≤ pe.val) (address : Fin Bank.lm0.capacity) :
    (mul7InitialPERegisters input pe).lm0 address = 0 := by
  have none_eq : mul7LaneOfPE pe = none := by
    unfold mul7LaneOfPE
    rw [dif_neg (by omega)]
  simp only [mul7InitialPERegisters, none_eq]
  simp [zeroInitialPERegisterFiles]

/-! ## 3. The sealed machine and the specification -/

/-- The sealed whole-machine value model, exactly as
`ProofsLean.MNCore.welcomeSealedMachine`: a non-`.ok` value transition is
`none` and issue/hazard history is not consulted. -/
noncomputable def mul7SealedMachine : ProofsLean.Machine where
  Line := InstructionLine
  State := State
  Input := Mul7Input
  step := fun line state =>
    match executeNormalizedLine line.toNormalizedLine state with
    | .ok next => some next
    | _ => none
  legal := fun _ => True
  lineCost := InstructionLine.cost
  positiveCost := InstructionLine.cost_positive

/-- **The `4.mul7` specification.** `X[i] <= 1000`; LM1 starts zero; the even
word of lane `w` of each observed PE must become `7 * X[w]` and the odd word
must stay `0`. -/
noncomputable def mul7Spec : ProofsLean.Problem mul7SealedMachine where
  admissible := fun input => ∀ (m : Fin 16) (p : Fin 4) (w : Fin 16),
    (input m p w).toNat ≤ 1000
  initial := mul7InitialState
  post := fun input state => ∀ (m : Fin 16) (p : Fin 4) (w : Fin 16),
    (state.peRegisters (mul7PE m p)).lm1 (mul7Low w) = (7 : BitVec 32) * input m p w ∧
    (state.peRegisters (mul7PE m p)).lm1 (mul7High w) = 0

theorem mul7Spec_initial (input : Mul7Input) : mul7Spec.initial input = mul7InitialState input :=
  rfl

theorem mul7Spec_admissible_iff (input : Mul7Input) :
    mul7Spec.admissible input ↔
      ∀ (m : Fin 16) (p : Fin 4) (w : Fin 16), (input m p w).toNat ≤ 1000 :=
  Iff.rfl

/-- The domain is inhabited. -/
def mul7ZeroInput : Mul7Input := fun _ _ _ => 0

theorem mul7Spec_admissible_input : mul7Spec.admissible mul7ZeroInput := by
  intro m p w
  simp [mul7ZeroInput]

/-- The all-`5` input: admissible, and every observed even word must become
`35`, while it starts at `0`. -/
def mul7FiveInput : Mul7Input := fun _ _ _ => 5

theorem mul7FiveInput_admissible : mul7Spec.admissible mul7FiveInput := by
  intro m p w
  show (5 : BitVec 32).toNat ≤ 1000
  decide

theorem mul7SevenMulFive : (7 : BitVec 32) * 5 = 35 := by decide

theorem mul7FiveInput_required (m : Fin 16) (p : Fin 4) (w : Fin 16) :
    (7 : BitVec 32) * mul7FiveInput m p w = 35 := by
  show (7 : BitVec 32) * 5 = 35
  exact mul7SevenMulFive

theorem mul7ThirtyFive_ne_zero : (35 : BitVec 32) ≠ 0 := by decide

/-- Every observed even word of the all-`5` input is required to be `35`, which
is not its initial value. -/
theorem mul7Spec_required_low (state : State)
    (post : mul7Spec.post mul7FiveInput state) (m : Fin 16) (p : Fin 4) (w : Fin 16) :
    (state.peRegisters (mul7PE m p)).lm1 (mul7Low w) = 35 := by
  rw [(post m p w).1, mul7FiveInput_required]

theorem mul7Spec_initial_low_is_zero (m : Fin 16) (p : Fin 4) (w : Fin 16) :
    ((mul7InitialState mul7FiveInput).peRegisters (mul7PE m p)).lm1 (mul7Low w) = 0 :=
  mul7InitialState_lm1 mul7FiveInput (mul7PE m p) (mul7Low w)

end ProofsLean.MNCore

-- End of module: no sorry, no admit, no native_decide, no new axioms.
