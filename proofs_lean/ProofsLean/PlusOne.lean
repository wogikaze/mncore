import ProofsLean.Enumeration
import ProofsLean.IntegerALU
import ProofsLean.PEMemory

/- A source-level model of the two long-word `iinc` lines in Welcome.
This model deliberately has only these two lines.  Its optimality theorem is
therefore restricted; it is not a claim about all legal MN-Core programs. -/
namespace ProofsLean.MNCore.PlusOne

abbrev Words := Fin 16 → BitVec 32

structure State where
  lm0 : Words
  lm1 : Words

abbrev Line := Fin 2

/-- `$lm0v` or `$lm8v` / `$ln0v` or `$ln8v`: four long-word accesses. -/
def schedule (line : Line) : PEMemory.Schedule :=
  .auto (8 * line.val) 2

theorem schedule_well_formed (line : Line) (bank : PEMemory.Bank)
    (hbank : bank = .lm0 ∨ bank = .lm1) :
    (schedule line).WellFormed bank .long := by
  rcases hbank with rfl | rfl
  all_goals simp [schedule, PEMemory.Schedule.WellFormed, PEMemory.Bank.capacity,
    PEMemory.Width.words]; omega

theorem address_at (line : Line) (bank : PEMemory.Bank)
    (hbank : bank = .lm0 ∨ bank = .lm1) (cycle : Fin 4) :
    (PEMemory.address bank .long (schedule line) 0 .direct 0 cycle).val =
      8 * line.val + 2 * cycle.val := by
  rcases hbank with rfl | rfl
  all_goals simp [PEMemory.address, PEMemory.count, PEMemory.baseOffset,
    PEMemory.Schedule.at, PEMemory.Adjustment.offset, schedule,
    PEMemory.Bank.capacity, PEMemory.Width.words]
  all_goals have hline := line.isLt
  all_goals have hcycle := cycle.isLt
  all_goals omega

def increment (x : BitVec 32) : BitVec 32 :=
  (IntegerALU.evaluateLane (.arith .inc false) x 0).value

theorem increment_eq_add_one (x : BitVec 32) : increment x = x + 1 := rfl

theorem increment_numerical (x : BitVec 32) (bounded : x.toNat ≤ 50) :
    (increment x).toNat = x.toNat + 1 := by
  rw [increment_eq_add_one, BitVec.toNat_add]
  have below : x.toNat + 1 < 2 ^ 32 := by omega
  simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt below]

def incrementPair (high low : BitVec 32) : BitVec 64 :=
  (IntegerALU.evaluateBus .word (.arith .inc false)
    ⟨high ++ low, 0⟩ ⟨0, 0⟩ false).value.high

theorem increment_pair_spec (high low : BitVec 32) :
    incrementPair high low = increment high ++ increment low := by
  simp [incrementPair, IntegerALU.evaluateBus, IntegerALU.lane,
    IntegerALU.Precision.lanes, IntegerALU.Precision.width,
    IntegerALU.evaluateLane, IntegerALU.arithmetic, increment,
    List.range, List.range.loop]
  rw [BitVec.extractLsb'_append_eq_right, BitVec.extractLsb'_append_eq_left]
  change (low + 1#32).setWidth 64 ||| ((high + 1#32).setWidth 64 <<< 32) =
    (high + 1#32) ++ (low + 1#32)
  calc
    _ = ((high + 1#32).setWidth 64 <<< 32) ||| (low + 1#32).setWidth 64 :=
      BitVec.or_comm _ _
    _ = ((high + 1#32) ++ (low + 1#32)).setWidth 64 :=
      (BitVec.setWidth_append_eq_shiftLeft_setWidth_or).symm
    _ = _ := by simp

/-- One long-word line handles four cycles, with two 32-bit lanes per cycle. -/
def step (line : Line) (state : State) : State :=
  { state with lm1 := fun address =>
      if address.val / 8 = line.val then increment (state.lm0 address)
      else state.lm1 address }

def machine : Machine where
  Line := Line
  State := State
  Input := Words
  step := fun line state => some (step line state)
  legal := fun _ => True
  lineCost := fun _ => 1
  positiveCost := fun _ => by decide

def problem : Problem machine where
  admissible := fun input => ∀ i, (input i).toNat ≤ 50
  initial := fun input => ⟨input, fun _ => 0⟩
  post := fun input state => ∀ i, (state.lm1 i).toNat = (input i).toNat + 1

def answer : Program machine := [⟨0, by decide⟩, ⟨1, by decide⟩]

theorem answer_correct : Correct machine problem answer := by
  refine ⟨True.intro, ?_⟩
  intro input admissible
  refine ⟨step 1 (step 0 ⟨input, fun _ => 0⟩), rfl, ?_⟩
  intro i
  have hi := i.isLt
  by_cases h : i.val / 8 = 1
  · simpa [step, h] using increment_numerical (input i) (admissible i)
  · have h0 : i.val / 8 = 0 := by omega
    have hlt : i.val < 8 := by omega
    simpa [step, h0, hlt] using increment_numerical (input i) (admissible i)

def zeroInput : Words := fun _ => 0

theorem zero_admissible : problem.admissible zeroInput := by
  intro i
  simp [zeroInput]

theorem empty_incorrect : ¬ Correct machine problem [] := by
  intro h
  obtain ⟨result, run, post⟩ := h.2 zeroInput zero_admissible
  have eq : result = problem.initial zeroInput := by
    exact Option.some.inj (by simpa [execute] using run.symm)
  subst result
  have wrong := post (⟨0, by decide⟩ : Fin 16)
  simp [problem, zeroInput] at wrong

theorem one_line_incorrect (line : Line) : ¬ Correct machine problem [line] := by
  intro h
  obtain ⟨result, run, post⟩ := h.2 zeroInput zero_admissible
  have eq : result = step line (problem.initial zeroInput) := by
    exact Option.some.inj (by simpa [execute, machine] using run.symm)
  subst result
  have cases : line.val = 0 ∨ line.val = 1 := by omega
  rcases cases with h0 | h1
  · have wrong := post (⟨8, by decide⟩ : Fin 16)
    simp [problem, step, zeroInput, h0] at wrong
    exact (by decide : ¬ ((if (8 : Nat) < 8 then increment 0 else (0 : BitVec 32)).toNat = 1)) wrong
  · have wrong := post (⟨0, by decide⟩ : Fin 16)
    simp [problem, step, zeroInput, h1] at wrong

theorem score_eq_length (p : Program machine) : score machine p = p.length := by
  induction p with
  | nil => rfl
  | cons line rest ih =>
    simp only [score, List.length_cons]
    change 1 + score machine rest = rest.length + 1
    omega

theorem two_line_lower_bound : LowerBound machine problem 2 := by
  intro p correct
  by_cases enough : 2 ≤ score machine p
  · exact enough
  have short : score machine p < 2 := by omega
  have hlen : p.length < 2 := by
    rw [score_eq_length] at short
    omega
  cases p with
  | nil => exact False.elim (empty_incorrect correct)
  | cons line rest =>
    cases rest with
    | nil => exact False.elim (one_line_incorrect line correct)
    | cons next tail =>
      simp only [List.length_cons] at hlen
      omega

theorem answer_optimal_in_restricted_model : Optimal machine problem answer := by
  have answer_score : score machine answer = 2 := by decide
  exact ⟨answer_correct, by rw [answer_score]; exact two_line_lower_bound⟩

end ProofsLean.MNCore.PlusOne
