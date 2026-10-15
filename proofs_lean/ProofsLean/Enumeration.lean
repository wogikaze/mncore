import ProofsLean.Optimality

namespace ProofsLean

/-- Enumerates sequences, including combinations of different lines and operands.
The alphabet must contain whole parallel issue lines to model the real ISA. -/
def programsUpTo (alphabet : List α) : Nat → List (List α)
  | 0 => [[]]
  | n + 1 => [] :: alphabet.flatMap (fun line => (programsUpTo alphabet n).map (line :: ·))

theorem programsUpTo_complete (alphabet : List α) (n : Nat) (p : List α)
    (covered : ∀ line ∈ p, line ∈ alphabet) (length : p.length ≤ n) :
    p ∈ programsUpTo alphabet n := by
  induction n generalizing p with
  | zero =>
    cases p with
    | nil => simp [programsUpTo]
    | cons line rest => simp at length
  | succ n ih =>
    cases p with
    | nil => simp [programsUpTo]
    | cons line rest =>
      have head : line ∈ alphabet := covered line (by simp)
      have tail : rest ∈ programsUpTo alphabet n :=
        ih rest (fun x hx => covered x (by simp [hx])) (by simp only [List.length_cons] at length; omega)
      simp only [programsUpTo, List.mem_cons, List.mem_flatMap, List.mem_map]
      exact Or.inr ⟨line, head, rest, tail, rfl⟩

def shortPrograms (m : Machine) (alphabet : List m.Line) (bound : Nat) : List (Program m) :=
  (programsUpTo alphabet (bound - 1)).filter (fun p => decide (score m p < bound))

/-- Coverage is explicit: knowing all opcode names is insufficient to establish
`covers`, which must also cover operands, masks and all legal simultaneous issues. -/
theorem shortPrograms_complete {m : Machine} {alphabet : List m.Line} {bound : Nat}
    (covers : ∀ line : m.Line, line ∈ alphabet)
    (p : Program m) (short : score m p < bound) :
    p ∈ shortPrograms m alphabet bound := by
  have length := length_le_score m p
  have member := programsUpTo_complete alphabet (bound - 1) p
    (fun line _ => covers line) (by omega)
  simp [shortPrograms, List.mem_filter, member, short]

def enumerationCertificate (m : Machine) (spec : Problem m)
    (alphabet : List m.Line) (bound : Nat)
    (covers : ∀ line : m.Line, line ∈ alphabet)
    (rejected : ∀ p ∈ shortPrograms m alphabet bound, ¬ Correct m spec p) :
    BoundCertificate m spec bound where
  candidates := shortPrograms m alphabet bound
  complete := shortPrograms_complete covers
  rejected := rejected

end ProofsLean
