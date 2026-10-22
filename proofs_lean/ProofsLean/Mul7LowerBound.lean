import ProofsLean.Mul7Spec
import ProofsLean.FootprintReconciled

/-! # Problem `4.mul7` — the one-line refutation

`Mul7Spec.lean` fixes the specification on the sealed whole-machine value model.
This module proves that **no single instruction line computes `7 * X` on all
`1024` output words of `4.mul7`**, i.e. `LowerBound mul7SealedMachine mul7Spec 2`,
modulo one explicitly stated write-shape obligation for `.pe` lines.

## Why the argument is a *write-shape* argument

The specification constrains `16` lanes per PE, i.e. `32` `32`-bit LM1 words per
PE, of which the `16` even ("low half") words must become `7 * X != 0` for the
all-`5` input, while LM1 starts at zero.

A single instruction line can only write LM1 through **one** destination
schedule of **four** cycles, each cycle covering at most `count .lm1 width <= 4`
consecutive `32`-bit words (`count_le_four`). Four consecutive integers contain
at most two even ones, so at most `4 * 2 = 8` of the `16` even words can be
touched. At least eight even words therefore keep their initial value `0`,
which is not the required `35`. No analysis of *what* the line computes is
needed — only of *where* it can write.

That is the whole content of `Mul7OneLineLm1Footprint` below: outside a set of
at most `8` lane indices the LM1 image is unchanged. The set is indexed by PE,
because BAR/T-indirect addressing lets different PEs write different lanes; the
counting argument is applied to the single observed PE `mul7PE 0 0`. The counting half
(`mul7_exists_unwritten_lane`, `mul7_oneLine_not_correct`) is proved
unconditionally; the footprint half is discharged unconditionally for `.nop`
and `.mv` lines and stated as the residual `Mul7PELineFootprint` for `.pe`.

## Results

* `mul7_exists_unwritten_lane` — from a set of at most `8` lane indices, one of
  the `16` lanes is missing (unconditional counting).
* `mul7_oneLine_not_correct_of_footprint` — a single line whose LM1 image
  changes on at most `8` lanes is incorrect (unconditional).
* `mul7Empty_not_correct` — the empty program is incorrect.
* `mul7NopLine_not_correct` / `mul7MvLine_not_correct` — every `.nop` / `.mv`
  single line of cost `< 2` is incorrect (**unconditional**).
* `mul7PELine_not_correct` — every `.pe` single line is incorrect, from
  `Mul7PELineFootprint`.
* `mul7LowerBound_two_of_peFootprint` — `LowerBound mul7SealedMachine mul7Spec 2`
  from `Mul7PELineFootprint`.
* `mul7ShortLine_not_correct` — the exact shape of the residual: every single
  line of cost `< 2` that is incorrect.

No `sorry`, no `admit`, no `native_decide`, no new axioms, no edited module.
-/

namespace ProofsLean.MNCore

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

open Issue
open PEMemory

/-! ## 1. Counting: eight lanes cannot cover sixteen -/

/-- **Unconditional counting core.** A set of at most `8` of the `16` lane
indices misses at least one lane. -/
theorem mul7_exists_unwritten_lane (S : Finset (Fin 16)) (card : S.card ≤ 8) :
    ∃ w : Fin 16, w ∉ S := by
  by_contra missing
  push_neg at missing
  have subset : (Finset.univ : Finset (Fin 16)) ⊆ S := fun w _ => missing w
  have sixteen : (Finset.univ : Finset (Fin 16)).card ≤ S.card :=
    Finset.card_le_card subset
  have : (Finset.univ : Finset (Fin 16)).card = 16 := by
    rw [Finset.card_univ, Fintype.card_fin]
  omega

/-- Every line that the sealed step executes successfully is **issue-legal**:
`executeIntegerProducerInstructionLine` rejects a line whose
`checkParsedTopLine` fails, so a successful step carries the issue check. This
is what makes the residual write shape plausible: the parsed issue checker
allows at most one writer per PE memory, hence at most one `.lm1` destination
schedule per line. -/
theorem mul7_pe_executed_accepted (expressions : List NormalizedExpr)
    (state next : State)
    (executed : executeNormalizedLine (.pe expressions) state = .ok next) :
    checkParsedTopLine (InstructionLine.pe expressions).toParsed = true :=
  executeIntegerProducerInstructionLine_accepted_of_ok _ state next executed

/-! ## 2. The write-shape obligation -/

/-- **The residual write-shape obligation.** One instruction line changes the
LM1 image of every PE only on at most `8` of the `16` lane indices, for both
halves of each lane.

This is a statement about *addresses only*: the data written is arbitrary, and
the statement says nothing about values. It is the analogue, for `4.mul7`, of
`WelcomePEWriteShape`: the place where the executor's four-cycle destination
schedule has to be inverted. -/
def Mul7OneLineLm1Footprint (line : InstructionLine) : Prop :=
  ∀ (state next : State),
    executeNormalizedLine line.toNormalizedLine state = .ok next →
    ∃ S : PEId → Finset (Fin 16), (∀ pe, (S pe).card ≤ 8) ∧
      ∀ (pe : PEId) (w : Fin 16), w ∉ S pe →
        (next.peRegisters pe).lm1 (mul7Low w) = (state.peRegisters pe).lm1 (mul7Low w) ∧
        (next.peRegisters pe).lm1 (mul7High w) = (state.peRegisters pe).lm1 (mul7High w)

/-! ## 3. The refutation from the write shape -/

/-- A successful sealed step of a one-line program. -/
theorem mul7_execute_singleton_step (line : InstructionLine) (state result : State)
    (run : ProofsLean.execute mul7SealedMachine [line] state = some result) :
    mul7SealedMachine.step line state = some result := by
  simpa [ProofsLean.execute] using run

/-- Inverting the sealed step: success is a successful `executeNormalizedLine`. -/
theorem mul7_step_execute (line : InstructionLine) (state result : State)
    (step : mul7SealedMachine.step line state = some result) :
    executeNormalizedLine line.toNormalizedLine state = .ok result := by
  have expanded : (match executeNormalizedLine line.toNormalizedLine state with
      | .ok next => some next
      | _ => none) = some result := step
  cases h : executeNormalizedLine line.toNormalizedLine state with
  | ok next =>
      rw [h] at expanded
      simp only [Option.some.injEq] at expanded
      rw [expanded]
  | failure => rw [h] at expanded; exact absurd expanded (by simp)
  | unknown => rw [h] at expanded; exact absurd expanded (by simp)

/-- **A single line that writes at most eight lanes is incorrect.**  Take the
all-`5` input: every one of the `16` even words of every observed PE must
become `35`, but at least one lane is untouched and stays `0`. -/
theorem mul7_oneLine_not_correct_of_footprint (line : InstructionLine)
    (footprint : Mul7OneLineLm1Footprint line) :
    ¬ ProofsLean.Correct mul7SealedMachine mul7Spec [line] := by
  intro correct
  obtain ⟨result, run, post⟩ := correct.2 mul7FiveInput mul7FiveInput_admissible
  have step := mul7_execute_singleton_step line _ result run
  have executed : executeNormalizedLine line.toNormalizedLine
      (mul7InitialState mul7FiveInput) = .ok result :=
    mul7_step_execute line _ result (by simpa [mul7Spec_initial] using step)
  obtain ⟨S, card, unchanged⟩ := footprint _ _ executed
  obtain ⟨w, outside⟩ := mul7_exists_unwritten_lane (S (mul7PE 0 0)) (card (mul7PE 0 0))
  have same := (unchanged (mul7PE 0 0) w outside).1
  have required := mul7Spec_required_low result post 0 0 w
  have initial := mul7Spec_initial_low_is_zero 0 0 w
  rw [same, initial] at required
  exact mul7ThirtyFive_ne_zero required.symm

/-! ## 4. The empty program -/

/-- The empty program is incorrect: LM1 starts at zero and must become `35`. -/
theorem mul7Empty_not_correct :
    ¬ ProofsLean.Correct mul7SealedMachine mul7Spec [] := by
  intro correct
  obtain ⟨result, run, post⟩ := correct.2 mul7FiveInput mul7FiveInput_admissible
  have same : result = mul7InitialState mul7FiveInput := by
    have simplified := run.symm
    simp only [ProofsLean.execute] at simplified
    exact Option.some.inj simplified
  have required := mul7Spec_required_low result post 0 0 0
  rw [same, mul7Spec_initial_low_is_zero] at required
  exact mul7ThirtyFive_ne_zero required.symm

/-! ## 5. `.nop` and `.mv` lines: unconditional -/

/-- Every `.nop` line of cost `< 2` leaves the PE register files untouched, so
it satisfies the write-shape obligation with the empty lane set. -/
theorem mul7NopLine_footprint (count : {n : Nat // 0 < n}) (wait : Option (Fin 256))
    (cost : InstructionLine.cost (.nop count wait) < 2) :
    Mul7OneLineLm1Footprint (.nop count wait) := by
  intro state next executed
  have count_one : count.val = 1 := by
    have positive := count.property
    simp only [InstructionLine.cost] at cost
    omega
  have executed' : executeNormalizedLine (NormalizedLine.nop 1 wait) state = .ok next := by
    simpa [Issue.InstructionLine.toNormalizedLine, count_one] using executed
  have frame := executeNormalizedLine_nop_field_frame 1 wait state next executed'
  refine ⟨fun _ => ∅, by simp, ?_⟩
  intro pe w _
  have same : next.peRegisters = state.peRegisters := by rw [frame]
  rw [same]
  exact ⟨rfl, rfl⟩

/-- Every `.mv` line leaves the PE register files untouched, so it satisfies the
write-shape obligation with the empty lane set. -/
theorem mul7MvLine_footprint (transfer : NormalizedMv) :
    Mul7OneLineLm1Footprint (.mv transfer) := by
  intro state next executed
  have frame := executeNormalizedLine_mv_field_frame transfer state next executed
  have same : next.peRegisters = state.peRegisters := frame.2.2.2.2.2.2.2.2.1
  refine ⟨fun _ => ∅, by simp, ?_⟩
  intro pe w _
  rw [same]
  exact ⟨rfl, rfl⟩

theorem mul7NopLine_not_correct (count : {n : Nat // 0 < n}) (wait : Option (Fin 256))
    (cost : InstructionLine.cost (.nop count wait) < 2) :
    ¬ ProofsLean.Correct mul7SealedMachine mul7Spec [.nop count wait] :=
  mul7_oneLine_not_correct_of_footprint _ (mul7NopLine_footprint count wait cost)

theorem mul7MvLine_not_correct (transfer : NormalizedMv) :
    ¬ ProofsLean.Correct mul7SealedMachine mul7Spec [.mv transfer] :=
  mul7_oneLine_not_correct_of_footprint _ (mul7MvLine_footprint transfer)

/-! ## 6. `.pe` lines: the residual -/

/-- The residual write-shape obligation for `.pe` lines. It is exactly
`Mul7OneLineLm1Footprint` specialised to a single `.pe` line, i.e. to one
four-cycle LM1 destination schedule. -/
def Mul7PELineFootprint : Prop :=
  ∀ (expressions : List NormalizedExpr),
    Mul7OneLineLm1Footprint (.pe expressions)

theorem mul7PELine_not_correct (expressions : List NormalizedExpr)
    (footprint : Mul7PELineFootprint) :
    ¬ ProofsLean.Correct mul7SealedMachine mul7Spec [.pe expressions] :=
  mul7_oneLine_not_correct_of_footprint _ (footprint expressions)

/-- Every single line of cost `< 2` is incorrect, from the `.pe` residual. -/
theorem mul7ShortLine_not_correct (footprint : Mul7PELineFootprint)
    (line : InstructionLine) (cost : InstructionLine.cost line < 2) :
    ¬ ProofsLean.Correct mul7SealedMachine mul7Spec [line] := by
  cases line with
  | pe expressions => exact mul7PELine_not_correct expressions footprint
  | nop count wait => exact mul7NopLine_not_correct count wait cost
  | mv transfer => exact mul7MvLine_not_correct transfer

/-! ## 7. The lower bound -/

/-- **`LowerBound mul7SealedMachine mul7Spec 2`** from the `.pe` write shape. -/
theorem mul7LowerBound_two_of_peFootprint (footprint : Mul7PELineFootprint) :
    ProofsLean.LowerBound mul7SealedMachine mul7Spec 2 := by
  intro program correct
  by_contra notBound
  have short : ProofsLean.score mul7SealedMachine program < 2 := by omega
  have lengthLe := ProofsLean.length_le_score mul7SealedMachine program
  cases program with
  | nil =>
      exact mul7Empty_not_correct correct
  | cons line rest =>
      cases rest with
      | nil =>
          have lineCost : InstructionLine.cost line < 2 := by
            simpa [ProofsLean.score, mul7SealedMachine] using short
          exact mul7ShortLine_not_correct footprint line lineCost correct
      | cons second tail =>
          simp only [List.length_cons] at lengthLe
          omega

/-- The residual restated as the exact remaining gap: refuting every single line
of cost `< 2` is *equivalent* to the lower bound. -/
theorem mul7LowerBound_two_iff_shortLines :
    ProofsLean.LowerBound mul7SealedMachine mul7Spec 2 ↔
      ∀ (line : InstructionLine), InstructionLine.cost line < 2 →
        ¬ ProofsLean.Correct mul7SealedMachine mul7Spec [line] := by
  constructor
  · intro lower line cost correct
    have bound := lower [line] correct
    have evaluated : ProofsLean.score mul7SealedMachine [line] = InstructionLine.cost line := by
      simp [ProofsLean.score, mul7SealedMachine]
    rw [evaluated] at bound
    omega
  · intro refute
    intro program correct
    by_contra notBound
    have short : ProofsLean.score mul7SealedMachine program < 2 := by omega
    have lengthLe := ProofsLean.length_le_score mul7SealedMachine program
    cases program with
    | nil => exact mul7Empty_not_correct correct
    | cons line rest =>
        cases rest with
        | nil =>
            have lineCost : InstructionLine.cost line < 2 := by
              simpa [ProofsLean.score, mul7SealedMachine] using short
            exact refute line lineCost correct
        | cons second tail =>
            simp only [List.length_cons] at lengthLe
            omega

end ProofsLean.MNCore

-- End of module: no sorry, no admit, no native_decide, no new axioms.
