import ProofsLean.Optimality
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Set.Finite.Basic

namespace ProofsLean

/-- Enumerates all line sequences of length at most `n` over an explicit line
alphabet. Coverage is relative to legality: the alphabet must contain every line
that occurs in a legal program, which is more than knowing the opcode names —
it must cover operands, masks and every legal simultaneous issue. For MN-Core,
whose line AST has Nat/String/Int/List fields and is therefore infinite, the
remaining obligation is a proof of finiteness of `legalLines` (bounded
addresses, immediates, operand ranges and legal parallel issue), NOT finiteness
of the AST type itself. -/
def programsUpTo (alphabet : List α) : Nat → List (List α)
  | 0 => [[]]
  | n + 1 => [] :: alphabet.flatMap
      (fun line => (programsUpTo alphabet n).map (line :: ·))

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
      have head : line ∈ alphabet := covered line List.mem_cons_self
      have tail : rest ∈ programsUpTo alphabet n := by
        apply ih
        · intro line' mem
          exact covered line' (List.mem_cons_of_mem line mem)
        · simpa using length
      simp only [programsUpTo, List.mem_cons, List.mem_flatMap, List.mem_map]
      exact Or.inr ⟨line, head, rest, tail, rfl⟩

def shortPrograms (m : Machine) (alphabet : List m.Line) (bound : Nat) :
    List (Program m) :=
  (programsUpTo alphabet (bound - 1)).filter (fun p => decide (score m p < bound))

/-- Lines that actually occur in at least one legal program. For machines with
an infinite line type this set may still be finite. -/
def legalLines (m : Machine) : Set m.Line := {line | ∃ p, m.legal p ∧ line ∈ p}

/-- An alphabet covers a machine when it lists every line occurring in a legal
program. Lines that can never legally issue place no obligation on enumeration. -/
def LegalLinesCovered (m : Machine) (alphabet : List m.Line) : Prop :=
  ∀ p, m.legal p → ∀ line ∈ p, line ∈ alphabet

theorem shortPrograms_complete {m : Machine} {alphabet : List m.Line} {bound : Nat}
    (covers : LegalLinesCovered m alphabet) (p : Program m) (legal : m.legal p)
    (short : score m p < bound) : p ∈ shortPrograms m alphabet bound := by
  have member := programsUpTo_complete alphabet (bound - 1) p (covers p legal) (by
    have length := length_le_score m p
    omega)
  simp [shortPrograms, List.mem_filter, member, short]

def enumerationCertificate (m : Machine) (spec : Problem m) (alphabet : List m.Line)
    (bound : Nat) (covers : LegalLinesCovered m alphabet)
    (rejected : ∀ p ∈ shortPrograms m alphabet bound, ¬ Correct m spec p) :
    BoundCertificate m spec bound where
  candidates := shortPrograms m alphabet bound
  complete := fun p legal short => shortPrograms_complete covers p legal short
  rejected := rejected

theorem legalLinesCovered_of_total {m : Machine} {alphabet : List m.Line}
    (covers : ∀ line : m.Line, line ∈ alphabet) : LegalLinesCovered m alphabet :=
  fun _ _ line _ => covers line

theorem legalLinesCovered_univ {m : Machine} [Fintype m.Line] :
    LegalLinesCovered m Finset.univ.toList :=
  legalLinesCovered_of_total
    (fun line => Finset.mem_toList.mpr (Finset.mem_univ line))

theorem legalLinesCovered_of_finite {m : Machine} (h : (legalLines m).Finite) :
    LegalLinesCovered m h.toFinset.toList := by
  intro p legal line mem
  exact Finset.mem_toList.mpr (h.mem_toFinset.mpr ⟨p, legal, mem⟩)

theorem legalLines_finite_of_covered {m : Machine} {alphabet : List m.Line}
    (h : LegalLinesCovered m alphabet) : (legalLines m).Finite :=
  Set.Finite.subset (List.finite_toSet alphabet)
    (fun _ ⟨p, legal, mem⟩ => h p legal _ mem)

theorem legalLines_finite_iff {m : Machine} :
    (legalLines m).Finite ↔ ∃ alphabet, LegalLinesCovered m alphabet :=
  ⟨fun h => ⟨h.toFinset.toList, legalLinesCovered_of_finite h⟩,
    fun ⟨_, h⟩ => legalLines_finite_of_covered h⟩

/-- Fintype convenience: when the line type itself is finite, no separate
coverage argument is needed. -/
noncomputable def fintypeCertificate (m : Machine) [Fintype m.Line]
    (spec : Problem m) (bound : Nat)
    (rejected : ∀ p ∈ shortPrograms m Finset.univ.toList bound,
      ¬ Correct m spec p) :
    BoundCertificate m spec bound :=
  enumerationCertificate m spec Finset.univ.toList bound legalLinesCovered_univ
    rejected

end ProofsLean
