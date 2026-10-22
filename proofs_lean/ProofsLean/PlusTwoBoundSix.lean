import ProofsLean.PlusTwoSuffix
import ProofsLean.ABWidthBound
import ProofsLean.ValueProvenance

/-! # `2.plus-two` at cost `6`: slot geometry, the copy slot, and the residual

`ProofsLean/PlusTwoSuffix.lean` reduces the refutation of the recorded five-line
answer to the corrected `BAR1`-relative frame, and shows that the counting
obligation `PlusTwoLineCoverage` of `ProofsLean/PlusTwoLowerBound.lean` is
**false** (a `.double` destination changes eight of the twenty observed words,
not four).  This module records what the `LowerBound 6` floor argument of
`research/experiments/plustwo-search/` actually needs, proves the parts that are
independent of the destination projection, and states the exact residual.

## The floor argument, and where it is *not* a counting argument

The search report (§4) argues:

* a non-2LW ALU op computes only the MSB long of its two-long bus; the LSB long is
  the first source's low long unchanged.  A `.word` destination stores four
  computed words, a `.long` destination four computed longs, a `.double`
  destination four computed longs plus four pass-through longs.  So one line
  *computes* at most four output longs;
* twenty observed output longs therefore need at least five lines, and if
  exactly five every line must compute four, leaving no line for the constant
  `2` that `x + 2` requires;
* pass-through delivery "moves values but does not create them".

The first two steps are the floor.  The third is the subtle one, and §5 below
shows precisely why the naive count is not sufficient: at the all-zero input
**all twenty targets are the same value `2`**, so a single computed `2` may be
relayed by pass-through slots.  Counting computed longs *and* counting writes
therefore does not refute five lines; the refutation needs the
*input-parametric* provenance recorded as the residual in §6.

## What is proved here

* `plusTwo_score_le_five_length` — a program of cost at most five has at most
  five lines;
* `parsedDirectAddress_aligned` — the resolved `LM1` destination address is
  aligned to its width (`toDirectMemoryAccessMode?` divides by `width.words`);
* `unpackALUBus_three`, `unpackALUBus_three_of_evaluateBus`,
  `plusTwoPassThroughSlot_is_read_word` — **the copy slot**: bus slot `3`, the
  only slot a `.double` destination can pass through into an observed word
  (slot `1` is the computed low word of the result), carries the first source's
  low long word, or zero for a rounded operand.  A pass-through store therefore
  relays a word that already existed in the state;
* `plusTwoZero_readDirectAccess_zero`, `plusTwoZero_pack_readDirectAccess_zero`,
  `plusTwoInitialState_forwarding_poison`, `plusTwoZero_fixed_value` — at the
  all-zero input every PE-file read is zero, uninitialised forwarding is poison,
  and the observed PE's fixed operands are `0` or the `msb1` replication;
* `plusTwoFirstCycleCheck_eq_true`, `plusTwoZero_computed_slot_no_two` — **no `2`
  from the initial state**: for every integer ALU op, precision and pair of
  initial operand buses, the two computed bus words are never the 32-bit value
  `2` (`1` *is* reachable — `inc 0` — which is why the five-line refutation cannot
  be a one-cycle statement);
* `PlusTwoLineWriteBudget`, `PlusTwoFirstLineCorrectBudget`,
  `plusTwo_execute_correctWords`, `plusTwoLowerBound_four_of_lineBudgets` —
  **`LowerBound 4`** from the two per-line budgets, by a union bound
  (`3 + 8 + 8 = 19 < 20`).

No `sorry`, no `admit`, no `native_decide`, no new axioms, no existing module is
edited.
-/

namespace ProofsLean.MNCore

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

open Issue
open PEMemory

/-! ## 1. Cost and length -/

/-- **A program of cost at most five has at most five lines.**  Every line costs
at least one, so the score dominates the length. -/
theorem plusTwo_score_le_five_length (p : List InstructionLine)
    (cost : ProofsLean.score plusTwoSealedMachine p ≤ 5) : p.length ≤ 5 := by
  have length := ProofsLean.length_le_score plusTwoSealedMachine p
  omega

/-! ## 2. The slot geometry of an `LM1` write at an observed word

An `LM1` destination address is aligned to its width: `toDirectMemoryAccessMode?`
resolves it as `(raw / width.words * width.words) % bank.capacity`, so it is
divisible by `width.words` (`parsedDirectAddress_aligned` below).

**The slot geometry.**  A bus covers the four words `address, ..., address+3` in
slots `0, 1, 2, 3` (`PEMemory.writeWords`), and the observed words are the odd
ones `2k+1`.  For a `.double` destination the address is a multiple of `4`, so
slot `0` lands on `≡ 0`, slot `1` on `≡ 1`, slot `2` on `≡ 2` and slot `3` on
`≡ 3 (mod 4)`; a `.long` destination is even, so its odd word is slot `1`; a
`.word` destination's odd word is slot `0`.  Hence **every observed word
congruent to `1` modulo `4` — ten of them, `1, 5, ..., 37` — is written from the
computed slots `0`, `1`**, and only the words congruent to `3` can be written
from the pass-through slot `3` (§3 identifies what slot `3` carries). -/

/-- **Alignment of the resolved direct address.** -/
theorem parsedDirectAddress_aligned (raw capacity words : Nat) (_positive : 0 < words)
    (divides : words ∣ capacity) :
    ((raw / words * words) % capacity) % words = 0 := by
  rw [Nat.mod_mod_of_dvd _ divides]
  exact Nat.mul_mod_left _ _

/-- The word count of every width divides the `LM1` capacity. -/
theorem lm1_count_dvd_capacity (width : Width) : count .lm1 width ∣ 4096 := by
  cases width <;> decide

/-- `count .lm1 width` is the width's word count: `1`, `2` or `4`. -/
theorem lm1_count_eq_words (width : Width) : count .lm1 width = width.words := by
  cases width <;> rfl

/-! ## 3. The copy slot relays a word of the state

The low long of an integer-ALU result is the first source's low long
(`IntegerALU.ordinary_lsb_passthrough`), or zero when the operand was reduced
(`IntegerALU.reduced_lsb_zero`).  Bus slot `3` is the low word of that low long,
so a `.double` pass-through store never computes: it stores a word that was
already present in the read state. -/

/-- Bus slot `3` is the low word of the low long word. -/
theorem unpackALUBus_three (bus : IntegerALU.Bus) :
    unpackALUBus bus 3 = bus.low.extractLsb' 0 32 := by
  simp [unpackALUBus]

/-- **A computed slot only reads the high long.**  Slot `0` stores the high word
of the computed long and slot `1` its low word. -/
theorem unpackALUBus_slot_zero (bus : IntegerALU.Bus) :
    unpackALUBus bus (0 : Fin 4) = bus.high.extractLsb' 32 32 := by
  simp [unpackALUBus]

theorem unpackALUBus_slot_one (bus : IntegerALU.Bus) :
    unpackALUBus bus (1 : Fin 4) = bus.high.extractLsb' 0 32 := by
  simp [unpackALUBus]

/-- The computed half of the ALU bus does not depend on the rounding flag. -/
theorem evaluateBus_high_eq (p : IntegerALU.Precision) (op : IntegerALU.Op)
    (x y : IntegerALU.Bus) (left right : Bool) :
    (IntegerALU.evaluateBus p op x y left).value.high =
      (IntegerALU.evaluateBus p op x y right).value.high := rfl

/-- **Bus slot `3` of an ALU result is the first source's slot `3`** (or zero for
a rounded operand).  This is the value a `.double` destination's pass-through
half stores. -/
theorem unpackALUBus_three_of_evaluateBus (p : IntegerALU.Precision)
    (op : IntegerALU.Op) (x y : IntegerALU.Bus) (reduced : Bool)
    (notPassa : op ≠ .passa) :
    unpackALUBus (IntegerALU.evaluateBus p op x y reduced).value 3 =
      if reduced then 0 else unpackALUBus x 3 := by
  rw [unpackALUBus_three]
  cases reduced with
  | false =>
      rw [IntegerALU.ordinary_lsb_passthrough p op x y notPassa, unpackALUBus_three]
      simp
  | true =>
      rw [IntegerALU.reduced_lsb_zero p op x y notPassa]
      simp

/-- `passa` copies both longs, so its slot `3` is also the first source's. -/
theorem unpackALUBus_three_of_evaluateBus_passa (p : IntegerALU.Precision)
    (x y : IntegerALU.Bus) (reduced : Bool) :
    unpackALUBus (IntegerALU.evaluateBus p .passa x y reduced).value 3 =
      unpackALUBus x 3 := by
  rw [unpackALUBus_three, IntegerALU.passa_copies_lsb, unpackALUBus_three]

/-- **The pass-through slot of a `.double` store is a read word.**  A store whose
data bus is an ALU result takes its slot-`3` word from the first source's bus (or
zero for a rounded operand), so it relays a word of the read state. -/
theorem plusTwoPassThroughSlot_is_read_word (p : IntegerALU.Precision)
    (op : IntegerALU.Op) (x y : IntegerALU.Bus) (reduced : Bool) :
    unpackALUBus (IntegerALU.evaluateBus p op x y reduced).value 3 =
        unpackALUBus x 3 ∨
      unpackALUBus (IntegerALU.evaluateBus p op x y reduced).value 3 = 0 := by
  by_cases passa : op = .passa
  · subst passa
    exact Or.inl (unpackALUBus_three_of_evaluateBus_passa p x y reduced)
  · rw [unpackALUBus_three_of_evaluateBus p op x y reduced passa]
    cases reduced with
    | false => exact Or.inl rfl
    | true => exact Or.inr rfl

/-! ## 4. The initial state at the all-zero input

At the all-zero input every PE memory word is zero, the observed PE's fixed
operands are `0` or the `msb1` replication, and forwarding is poison.  These are
the three facts that make "no constant `2`" a finite computation. -/

/-- Every word read from any bank, width, address and bus index of the all-zero
input's PE file is `0`. -/
theorem plusTwoZero_readDirectAccess_zero (bank : PEMemory.Bank) (width : Width)
    (address : Fin bank.capacity) (index : Fin 4) :
    readDirectAccess (plusTwoInitialPERegisters plusTwoZeroWords)
      ⟨bank, width, address⟩ index = 0 := by
  rw [plusTwoInitialPERegisters_zero]
  cases bank <;>
    simp [readDirectAccess, readRegisterBank, readWords, zeroInitialPERegisterFiles]

/-- The all-zero input's PE-file bus read is the zero bus. -/
theorem plusTwoZero_pack_readDirectAccess_zero (bank : PEMemory.Bank) (width : Width)
    (address : Fin bank.capacity) :
    pack (readDirectAccess (plusTwoInitialPERegisters plusTwoZeroWords)
      ⟨bank, width, address⟩) = (⟨0, 0⟩ : IntegerALU.Bus) := by
  simp [pack, plusTwoZero_readDirectAccess_zero]

/-- Uninitialised forwarding slots are poison at the initial state: no
forwarding path can supply a hidden constant to the first line. -/
theorem plusTwoInitialState_forwarding_poison (input : PlusTwoWords) (pe : PEId)
    (unit : ProofsLean.MNCore.Forwarding.Unit) (cycle : Fin 4) :
    stateForwardingSlots (plusTwoInitialState input) pe unit cycle = .poison :=
  stateForwardingSlots_invalid_is_poison _ _ _ _
    (rustSimulatorInitialState_forwarding_invalid pe unit cycle)

/-- The observed PE's context is the zero coordinate. -/
theorem plusTwoPE_context_fields :
    (ParsedIntegerContext.ofLinearIndex plusTwoPE).group = 0 ∧
      (ParsedIntegerContext.ofLinearIndex plusTwoPE).l2b = 0 ∧
      (ParsedIntegerContext.ofLinearIndex plusTwoPE).l1b = 0 ∧
      (ParsedIntegerContext.ofLinearIndex plusTwoPE).mab = 0 ∧
      (ParsedIntegerContext.ofLinearIndex plusTwoPE).pe = 0 := by
  decide

/-- **The fixed operands of the observed PE.**  At `PE 0` (linear index `0`) every
fixed operand is `0`, except `$msb1`, whose value is `2 ^ (width - 1)`; so the
replicated fixed bus is either the zero bus or the `msb1` replication. -/
theorem plusTwoZero_fixed_value (fixed : ParsedFixed) (p : IntegerALU.Precision) :
    ParsedFixed.integerValue fixed p
        (ParsedIntegerContext.ofLinearIndex plusTwoPE).group
        (ParsedIntegerContext.ofLinearIndex plusTwoPE).l2b
        (ParsedIntegerContext.ofLinearIndex plusTwoPE).l1b
        (ParsedIntegerContext.ofLinearIndex plusTwoPE).mab
        (ParsedIntegerContext.ofLinearIndex plusTwoPE).pe = 0 ∨
      ParsedFixed.integerValue fixed p
        (ParsedIntegerContext.ofLinearIndex plusTwoPE).group
        (ParsedIntegerContext.ofLinearIndex plusTwoPE).l2b
        (ParsedIntegerContext.ofLinearIndex plusTwoPE).l1b
        (ParsedIntegerContext.ofLinearIndex plusTwoPE).mab
        (ParsedIntegerContext.ofLinearIndex plusTwoPE).pe = 2 ^ (p.width - 1) := by
  obtain ⟨hg, hl2, hl1, hm, hp⟩ := plusTwoPE_context_fields
  cases fixed <;> simp [ParsedFixed.integerValue, hg, hl2, hl1, hm, hp]

/-! ### The finite check: a first-cycle computed word is never `2`

The operand buses of the first line's first cycle can only be the zero bus, the
`msb1` replication, or a rounded form of either (forwarding is poison and every
memory read is zero).  The check below evaluates every integer ALU op at every
precision on those buses and confirms that the two computed bus words are never
`2`. -/

/-- The zero bus. -/
def plusTwoZeroBus (p : IntegerALU.Precision) : IntegerALU.Bus :=
  replicateIntegerLane p 0

/-- The `msb1` replication at a precision. -/
def plusTwoMsbBus (p : IntegerALU.Precision) : IntegerALU.Bus :=
  replicateIntegerLane p (2 ^ (p.width - 1))

/-- The three operand buses a first cycle can read at the all-zero input. -/
def plusTwoInitialBuses (p : IntegerALU.Precision) : List IntegerALU.Bus :=
  [plusTwoZeroBus p, plusTwoMsbBus p, roundSingleInputBusToHalf (plusTwoMsbBus p)]

/-- The precisions, as a list for the finite check. -/
def plusTwoPrecisions : List IntegerALU.Precision := [.long, .word, .half]

/-- Every `IntegerALU.Op` constructor, as a list for the finite check. -/
def plusTwoIntegerOps : List IntegerALU.Op :=
  [.arith .inc true, .arith .inc false, .arith .dec true, .arith .dec false,
   .arith .add true, .arith .add false, .arith .sub true, .arith .sub false,
   .bitNot, .logicalNot, .bitAnd, .bitOr, .bitXor,
   .maximum true, .maximum false, .minimum true, .minimum false,
   .shift .left, .shift (.right true), .shift (.right false),
   .shift .rotateLeft, .shift .rotateRight, .packbit, .passa]

theorem mem_plusTwoPrecisions (p : IntegerALU.Precision) : p ∈ plusTwoPrecisions := by
  cases p <;> simp [plusTwoPrecisions]

theorem mem_plusTwoIntegerOps (op : IntegerALU.Op) : op ∈ plusTwoIntegerOps := by
  cases op with
  | arith a u => cases a <;> cases u <;> simp [plusTwoIntegerOps]
  | shift s =>
      cases s with
      | right u => cases u <;> simp [plusTwoIntegerOps]
      | left => simp [plusTwoIntegerOps]
      | rotateLeft => simp [plusTwoIntegerOps]
      | rotateRight => simp [plusTwoIntegerOps]
  | maximum u => cases u <;> simp [plusTwoIntegerOps]
  | minimum u => cases u <;> simp [plusTwoIntegerOps]
  | bitNot => simp [plusTwoIntegerOps]
  | logicalNot => simp [plusTwoIntegerOps]
  | bitAnd => simp [plusTwoIntegerOps]
  | bitOr => simp [plusTwoIntegerOps]
  | bitXor => simp [plusTwoIntegerOps]
  | packbit => simp [plusTwoIntegerOps]
  | passa => simp [plusTwoIntegerOps]

/-- The finite check: no integer ALU op at any precision, applied to two initial
buses, gives the 32-bit word `2` in computed slot `0` or `1`. -/
def plusTwoFirstCycleCheck : Bool :=
  plusTwoPrecisions.all fun p =>
    plusTwoIntegerOps.all fun op =>
      (plusTwoInitialBuses p).all fun x =>
        (plusTwoInitialBuses p).all fun y =>
          ([0, 1] : List (Fin 4)).all fun slot =>
            decide (unpackALUBus (IntegerALU.evaluateBus p op x y false).value slot ≠ 2)

/-- **The check runs.**  `decide` evaluates the `3 × 24 × 3 × 3 × 2` cases; no
`native_decide` and no extra axiom is involved. -/
theorem plusTwoFirstCycleCheck_eq_true : plusTwoFirstCycleCheck = true := by
  decide

/-- **No `2` from the initial state.**  Whatever integer ALU op and precision the
first cycle of a line runs, and whatever of the three available initial operand
buses it reads, the computed half of its result never holds the 32-bit value
`2`. -/
theorem plusTwoZero_computed_slot_no_two (p : IntegerALU.Precision)
    (op : IntegerALU.Op) (x y : IntegerALU.Bus)
    (xMem : x ∈ plusTwoInitialBuses p) (yMem : y ∈ plusTwoInitialBuses p)
    (slot : Fin 4) (computed : slot.val < 2) (reduced : Bool) :
    unpackALUBus (IntegerALU.evaluateBus p op x y reduced).value slot ≠ 2 := by
  have hprec := List.all_eq_true.mp plusTwoFirstCycleCheck_eq_true p
    (mem_plusTwoPrecisions p)
  have hop := List.all_eq_true.mp hprec op (mem_plusTwoIntegerOps op)
  have hx := List.all_eq_true.mp hop x xMem
  have hy := List.all_eq_true.mp hx y yMem
  have check0 : (IntegerALU.evaluateBus p op x y false).value.high.extractLsb' 32 32 ≠ 2 := by
    have := of_decide_eq_true (List.all_eq_true.mp hy (0 : Fin 4) (by simp))
    simpa [unpackALUBus] using this
  have check1 : (IntegerALU.evaluateBus p op x y false).value.high.extractLsb' 0 32 ≠ 2 := by
    have := of_decide_eq_true (List.all_eq_true.mp hy (1 : Fin 4) (by simp))
    simpa [unpackALUBus] using this
  have slotCases : slot = (0 : Fin 4) ∨ slot = (1 : Fin 4) := by
    have bounded := slot.isLt
    have values : slot.val = 0 ∨ slot.val = 1 := by omega
    rcases values with zero | one
    · exact Or.inl (Fin.ext zero)
    · exact Or.inr (Fin.ext one)
  rcases slotCases with zero | one
  · subst zero
    have highEq := evaluateBus_high_eq p op x y reduced false
    simp only [unpackALUBus, highEq]
    exact check0
  · subst one
    have highEq := evaluateBus_high_eq p op x y reduced false
    simp only [unpackALUBus, highEq]
    exact check1

/-! ## 5. The per-line budgets and `LowerBound 4`

The two obligations below are the *counting form* of the destination projection:
the write list of a successful line has at most four `LM1` writes, each covering
at most two observed words, and the first line of a run cannot fill more than
three of them at the all-zero input (its first cycle's write is never a correct
value: the computed slots are not `2` by §4, and the pass-through slots relay
`0` by §3 and §4).

`LowerBound 4` follows by a union bound: three lines fill at most
`3 + 8 + 8 = 19 < 20` observed words. -/

/-- **The per-line write budget.**  A successful line changes at most eight of
the twenty observed words (four `.lm1` writes of width at most four words; a
four-word window contains at most two odd words). -/
def PlusTwoLineWriteBudget : Prop :=
  ∀ (line : InstructionLine) (state next : State),
    plusTwoSealedMachine.step line state = some next →
      ∃ S : Finset (Fin 20), S.card ≤ 8 ∧
        ∀ k, k ∉ S →
          (next.peRegisters plusTwoPE).lm1 (plusTwoLowAddress k) =
            (state.peRegisters plusTwoPE).lm1 (plusTwoLowAddress k)

/-- **The first-line budget at the all-zero input.**  The first line of a run
sets at most three of the twenty observed words to the target `2`. -/
def PlusTwoFirstLineCorrectBudget : Prop :=
  ∀ (head : InstructionLine) (next : State),
    plusTwoSealedMachine.step head (plusTwoSpec.initial plusTwoZeroWords) = some next →
      ∃ S : Finset (Fin 20), S.card ≤ 3 ∧
        ∀ k, k ∉ S →
          (next.peRegisters plusTwoPE).lm1 (plusTwoLowAddress k) ≠ 2

/-- **Counting propagation of "is not the target".**  Along a program of `n`
lines, at most `8 * n` observed words can leave the incoming set: if the incoming
state is never `2` outside `S0`, the outgoing state is never `2` outside a set of
size at most `S0.card + 8 * n`. -/
theorem plusTwo_execute_notTwo (budget : PlusTwoLineWriteBudget)
    (p : List InstructionLine) :
    ∀ (state next : State) (S0 : Finset (Fin 20)),
      ProofsLean.execute plusTwoSealedMachine p state = some next →
      (∀ k, k ∉ S0 →
        (state.peRegisters plusTwoPE).lm1 (plusTwoLowAddress k) ≠ 2) →
      ∃ S : Finset (Fin 20), S.card ≤ S0.card + 8 * p.length ∧
        ∀ k, k ∉ S →
          (next.peRegisters plusTwoPE).lm1 (plusTwoLowAddress k) ≠ 2 := by
  induction p with
  | nil =>
      intro state next S0 executed initial
      have nextEq : next = state := (Option.some.inj executed).symm
      subst nextEq
      exact ⟨S0, by simp, initial⟩
  | cons line rest ih =>
      intro state next S0 executed initial
      rw [ProofsLean.execute.eq_2] at executed
      cases hstep : plusTwoSealedMachine.step line state with
      | none => rw [hstep] at executed; simp at executed
      | some middle =>
          rw [hstep] at executed
          simp only [Option.bind_some] at executed
          obtain ⟨S1, card1, unchanged1⟩ := budget line state middle hstep
          obtain ⟨S2, card2, zero2⟩ := ih middle next (S0 ∪ S1) executed
            (fun k hk => by
              rw [unchanged1 k (by intro mem; exact hk (Finset.mem_union_right _ mem))]
              exact initial k (by intro mem; exact hk (Finset.mem_union_left _ mem)))
          refine ⟨S2, ?_, zero2⟩
          have unionLe : (S0 ∪ S1).card ≤ S0.card + S1.card := Finset.card_union_le _ _
          simp only [List.length_cons]
          omega

/-- **`LowerBound 4` from the two per-line budgets.**  A program of at most three
lines cannot be correct: the first line fills at most three of the twenty
observed words, each later line at most eight, so at most nineteen words hold the
target while the specification demands all twenty. -/
theorem plusTwoLowerBound_four_of_lineBudgets (budget : PlusTwoLineWriteBudget)
    (firstBudget : PlusTwoFirstLineCorrectBudget) :
    ProofsLean.LowerBound plusTwoSealedMachine plusTwoSpec 4 := by
  intro p correct
  by_contra notBound
  have scoreLt : ProofsLean.score plusTwoSealedMachine p < 4 := by omega
  have lengthLe : p.length ≤ ProofsLean.score plusTwoSealedMachine p :=
    ProofsLean.length_le_score plusTwoSealedMachine p
  have lengthLt : p.length < 4 := by omega
  obtain ⟨result, executed, post⟩ :=
    correct.2 plusTwoZeroWords plusTwoZeroWords_admissible
  rw [plusTwoSpec_initial] at executed
  have initialZero : ∀ k : Fin 20,
      ((plusTwoInitialState plusTwoZeroWords).peRegisters plusTwoPE).lm1
        (plusTwoLowAddress k) = 0 :=
    fun k => plusTwoInitialState_lm1_zero plusTwoZeroWords (plusTwoLowAddress k)
  cases p with
  | nil =>
      have resultEq : result = plusTwoInitialState plusTwoZeroWords :=
        (Option.some.inj executed).symm
      subst resultEq
      have target := (post ⟨0, by decide⟩).2
      rw [initialZero] at target
      simp [plusTwoZeroWords] at target
  | cons head rest =>
      rw [ProofsLean.execute.eq_2] at executed
      cases hstep : plusTwoSealedMachine.step head
          (plusTwoInitialState plusTwoZeroWords) with
      | none => rw [hstep] at executed; simp at executed
      | some middle =>
          rw [hstep] at executed
          simp only [Option.bind_some] at executed
          obtain ⟨S1, card1, wrong1⟩ := firstBudget head middle hstep
          obtain ⟨S2, card2, notTwo⟩ := plusTwo_execute_notTwo budget rest
            middle result S1 executed wrong1
          have restLe : rest.length ≤ 2 := by
            simp only [List.length_cons] at lengthLt
            omega
          have small : S2.card < 20 := by omega
          have hex : ∃ k : Fin 20, k ∉ S2 := by
            by_contra noK
            have allMem : S2 = Finset.univ :=
              Finset.eq_univ_of_forall (fun k => by
                by_contra hk
                exact noK ⟨k, hk⟩)
            rw [allMem] at small
            simp at small
          obtain ⟨k, hk⟩ := hex
          exact notTwo k hk (post k).2

/-! ## 6. The residual for `LowerBound 6`

The two budgets of §5 are counting statements, and they cannot reach `6`: at the
all-zero input every one of the twenty targets is the *same* value `2`, so one
computed `2` may be relayed by the pass-through slot of many later lines (§3
shows that slot relays a state word; §2 shows it can reach the ten words
congruent to `3` modulo `4`).  The counting route therefore stops at four lines,
and `LowerBound 5` is *not* available this way — the tree's existing
`plusTwoLowerBound_five_of_coverage` needs the false `PlusTwoLineCoverage`.

The missing statement is the *input-parametric* provenance of the output longs:

> for each output `k`, the value `input k + 2` is computed by some cycle of some
> line, and different outputs need different computed longs, because
> `input ↦ input k + 2` and `input ↦ input j + 2` are different functions.

Twenty computed longs need five lines of four.  If exactly five lines suffice,
every cycle of every line must compute one of the twenty, so no line can be a
setup line; but computing `input k + 2` needs an operand `2` (`inc` adds one, and
every binary op needs a second operand), and at the first line no source supplies
`2`: memory and registers are zero, forwarding is poison, and the fixed operands
of the observed PE are `0` or `msb1` (§4).  A line that creates `2` spends
computed slots and cannot also compute four outputs, so five lines cannot compute
all twenty outputs.  Hence `LowerBound 6`.

Concretely the residual has two halves, both already framed in the tree:

1. **The destination projection** (`ProofsLean/ALURequestProvenance.lean`):
   `prepareParsedIntegerALUExprCycles_destination_map` gives the four lowered
   destinations of a successful plain-ALU row, and
   `ProofsLean/ValueProvenance.lean` gives the read-value closure.  Composing
   them with §2 gives `PlusTwoLineWriteBudget` for the plain ALU family; the
   other producer families (matrix read, float MAU, matrix MAU, block float,
   L1BM→PE, MSL/MSR) still need their own count and slot lemmas, as
   `ProofsLean/ABWidthBound.lean` lists them, and the first-line budget needs the
   write-selection masks composed with §4's data words.
2. **The universality step** above: the output word `k` holds `input k + 2` as a
   function of the input, while a pass-through slot relays a single read word
   (§3).  This is an input-parametric statement about the executor; it is the
   part the counting budgets deliberately do not cover, and it is why this module
   stops at `LowerBound 4`.

No `LowerBound 6` is claimed here. -/

end ProofsLean.MNCore

-- End of module: no sorry, no admit, no native_decide, no new axioms.
