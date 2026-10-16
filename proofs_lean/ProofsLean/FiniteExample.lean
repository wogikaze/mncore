import ProofsLean.Enumeration
import ProofsLean.PartialSemantics

namespace ProofsLean.FiniteExample

/- A complete, deliberately small test machine. This is NOT the MN-Core ISA.
The constant instruction demonstrates why all instruction alternatives and the
distinction between all-input correctness and testcase correctness matter. -/
inductive Line where
  | flipLeft
  | flipRight
  | fillTrue
  deriving DecidableEq, Repr

instance : Fintype Line := ⟨{.flipLeft, .flipRight, .fillTrue}, by intro x; cases x <;> simp⟩

def machine : Machine where
  Line := Line
  State := Bool × Bool
  Input := Bool × Bool
  step := fun line state => some (match line with
    | .flipLeft => (!state.1, state.2)
    | .flipRight => (state.1, !state.2)
    | .fillTrue => (true, true))
  legal := fun _ => True
  lineCost := fun _ => 1
  positiveCost := fun _ => by decide

/-- The alphabet every legal program draws from: all three lines are legal. -/
def alphabet : List Line := [.flipLeft, .flipRight, .fillTrue]

theorem covers : LegalLinesCovered machine alphabet :=
  legalLinesCovered_of_total (fun line => by
    cases line
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))

def problem : Problem machine where
  admissible := fun _ => True
  initial := id
  post := fun input output => output = (!input.1, !input.2)


theorem empty_refuted : Refutes machine problem [] (false, false) := by
  simp [Refutes, problem, execute, machine, id]

theorem left_refuted : Refutes machine problem [.flipLeft] (false, false) := by
  simp [Refutes, problem, execute, machine]

theorem right_refuted : Refutes machine problem [.flipRight] (false, false) := by
  simp [Refutes, problem, execute, machine]

theorem fill_refuted : Refutes machine problem [.fillTrue] (true, true) := by
  simp [Refutes, problem, execute, machine]

theorem rejects_all_short :
    ∀ p ∈ shortPrograms machine alphabet 2, ¬ Correct machine problem p := by
  intro p member
  have listed : p ∈ [[], [.flipLeft], [.flipRight], [.fillTrue]] := by
    rcases List.mem_filter.mp member with ⟨enumerated, _⟩
    exact enumerated
  have cases : p = [] ∨ p = [.flipLeft] ∨ p = [.flipRight] ∨ p = [.fillTrue] := by
    simpa only [List.mem_cons, List.not_mem_nil, or_false] using listed
  rcases cases with rfl | rfl | rfl | rfl
  · exact refutes_not_correct empty_refuted
  · exact refutes_not_correct left_refuted
  · exact refutes_not_correct right_refuted
  · exact refutes_not_correct fill_refuted

def lowerCertificate : BoundCertificate machine problem 2 :=
  enumerationCertificate machine problem alphabet 2
    (legalLinesCoveredBelow_of_covered covers) rejects_all_short

theorem two_lines_correct : Correct machine problem [.flipLeft, .flipRight] := by
  refine ⟨True.intro, ?_⟩
  intro input _
  exact ⟨(!input.1, !input.2), by simp [execute, machine, problem, id], rfl⟩

def optimalCertificate : OptimalityCertificate machine problem where
  program := [.flipLeft, .flipRight]
  correct := two_lines_correct
  lower := lowerCertificate

theorem two_lines_optimal : Optimal machine problem [.flipLeft, .flipRight] :=
  optimalCertificate.sound

theorem fill_correct_on_one_case :
    Correct machine (problem.restrict [(false, false)]) [.fillTrue] := by
  refine ⟨True.intro, ?_⟩
  intro input allowed
  have eq : input = (false, false) := List.mem_singleton.mp allowed.1
  subst input
  exact ⟨(true, true), by simp [execute, machine, problem, Problem.restrict], rfl⟩

theorem testcase_correct_does_not_imply_general_correct :
    Correct machine (problem.restrict [(false, false)]) [.fillTrue] ∧
      ¬ Correct machine problem [.fillTrue] :=
  ⟨fill_correct_on_one_case, refutes_not_correct fill_refuted⟩

theorem one_case_has_no_two_line_lower_bound :
    ¬ LowerBound machine (problem.restrict [(false, false)]) 2 :=
  shorter_correct_refutes_bound fill_correct_on_one_case (by decide)

def missingSemantics : PartialMachine where
  Line := Unit
  State := Unit
  Input := Unit
  step := fun _ _ => .unknown
  legal := fun _ => True
  lineCost := fun _ => 1
  positiveCost := fun _ => by decide

theorem missing_cannot_be_sealed : ¬ missingSemantics.Complete :=
  unknown_prevents_sealing missingSemantics ⟨(), (), rfl⟩

/- Regression: legality-relative coverage matters for machines whose line type
is infinite. Here `Line := Nat`, but only lines below 3 may legally issue, so
the finite alphabet [0, 1, 2] covers every legal program while no total cover
of Nat can exist. -/
namespace Bounded

def machine : Machine where
  Line := Nat
  State := Nat
  Input := Unit
  step := fun line state => some (state + line)
  legal := fun p => ∀ l ∈ p, l < 3
  lineCost := fun _ => 1
  positiveCost := fun _ => by decide

private theorem nat_lt_three_mem {n : Nat} (h : n < 3) : n ∈ [0, 1, 2] := by
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  omega

theorem covers : LegalLinesCovered machine ([0, 1, 2] : List Nat) := by
  intro p legal line mem
  exact nat_lt_three_mem (legal line mem)

theorem covers_below_two : LegalLinesCoveredBelow machine ([0, 1, 2] : List Nat) 2 :=
  legalLinesCoveredBelow_of_covered covers

theorem legalLines_finite : (legalLines machine).Finite :=
  legalLines_finite_of_covered covers

theorem no_total_cover : ¬ ∀ line : machine.Line, line ∈ ([0, 1, 2] : List Nat) := by
  intro total
  exact absurd (total (3 : Nat)) (by decide)

end Bounded

end ProofsLean.FiniteExample
