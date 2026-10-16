import ProofsLean.Optimality
import Mathlib.Data.Fintype.Basic

namespace ProofsLean

/-- Enumerates all line sequences of length at most `n`, using Mathlib's finite
universe as the line alphabet. A line is one whole parallel issue group. -/
noncomputable def programsUpTo (α : Type) [Fintype α] [DecidableEq α] : Nat → List (List α)
  | 0 => [[]]
  | n + 1 => [] :: (Finset.univ.toList).flatMap
      (fun line => (programsUpTo α n).map (line :: ·))

theorem programsUpTo_complete (α : Type) [Fintype α] [DecidableEq α]
    (n : Nat) (p : List α) (length : p.length ≤ n) :
    p ∈ programsUpTo α n := by
  induction n generalizing p with
  | zero =>
    cases p with
    | nil => simp [programsUpTo]
    | cons line rest => simp at length
  | succ n ih =>
    cases p with
    | nil => simp [programsUpTo]
    | cons line rest =>
      have head : line ∈ Finset.univ.toList := by simp
      have tail : rest ∈ programsUpTo α n := by
        apply ih
        simpa using length
      simp only [programsUpTo, List.mem_cons, List.mem_flatMap, List.mem_map]
      exact Or.inr ⟨line, head, rest, tail, rfl⟩

noncomputable def shortPrograms (m : Machine) [Fintype m.Line] [DecidableEq m.Line]
    (bound : Nat) : List (Program m) :=
  (programsUpTo m.Line (bound - 1)).filter (fun p => decide (score m p < bound))

theorem shortPrograms_complete {m : Machine} [Fintype m.Line] [DecidableEq m.Line]
    {bound : Nat} (p : Program m) (short : score m p < bound) :
    p ∈ shortPrograms m bound := by
  have member := programsUpTo_complete m.Line (bound - 1) p (by
    have length := length_le_score m p
    omega)
  simp [shortPrograms, List.mem_filter, member, short]

noncomputable def enumerationCertificate (m : Machine) [Fintype m.Line] [DecidableEq m.Line]
    (spec : Problem m) (bound : Nat)
    (rejected : ∀ p ∈ shortPrograms m bound, ¬ Correct m spec p) :
    BoundCertificate m spec bound where
  candidates := shortPrograms m bound
  complete := shortPrograms_complete
  rejected := rejected

end ProofsLean
