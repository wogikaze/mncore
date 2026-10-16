import ProofsLean.Semantics

namespace ProofsLean

def LowerBound (m : Machine) (spec : Problem m) (bound : Nat) : Prop :=
  ∀ p : Program m, Correct m spec p → bound ≤ score m p

def Optimal (m : Machine) (spec : Problem m) (p : Program m) : Prop :=
  Correct m spec p ∧ LowerBound m spec (score m p)

/-- Each listed candidate must be rejected, and every legal shorter program must
be listed. Illegal shorter programs place no obligation on the enumeration.
Neither failed edits nor a count of rejected candidates establishes coverage. -/
structure BoundCertificate (m : Machine) (spec : Problem m) (bound : Nat) where
  candidates : List (Program m)
  complete : ∀ p, m.legal p → score m p < bound → p ∈ candidates
  rejected : ∀ p ∈ candidates, ¬ Correct m spec p

theorem BoundCertificate.sound (certificate : BoundCertificate m spec bound) :
    LowerBound m spec bound := by
  intro p correct
  by_cases h : bound ≤ score m p
  · exact h
  · have short : score m p < bound := by omega
    exact False.elim
      (certificate.rejected p (certificate.complete p correct.1 short) correct)

/-- A symbolic lower-bound certificate can rule out a whole family of programs
without materializing that family as a list. This is intended for bounds where
the instruction alphabet is finite but far too large to enumerate explicitly:
`contains` describes a proof-friendly superset of all legal short programs,
and `rejected` proves every member of that family incorrect. -/
structure SymbolicBoundCertificate (m : Machine) (spec : Problem m) (bound : Nat) where
  contains : Program m → Prop
  covers : ∀ p, m.legal p → score m p < bound → contains p
  rejected : ∀ p, contains p → ¬ Correct m spec p

theorem SymbolicBoundCertificate.sound
    (certificate : SymbolicBoundCertificate m spec bound) :
    LowerBound m spec bound := by
  intro p correct
  by_cases h : bound ≤ score m p
  · exact h
  · have short : score m p < bound := by omega
    exact False.elim
      (certificate.rejected p (certificate.covers p correct.1 short) correct)

/-- Every concrete enumeration certificate is also a symbolic one, using
membership in its finite candidate list as the family predicate. -/
def BoundCertificate.toSymbolic
    (certificate : BoundCertificate m spec bound) :
    SymbolicBoundCertificate m spec bound where
  contains := fun p => p ∈ certificate.candidates
  covers := certificate.complete
  rejected := certificate.rejected

structure OptimalityCertificate (m : Machine) (spec : Problem m) where
  program : Program m
  correct : Correct m spec program
  lower : BoundCertificate m spec (score m program)

theorem OptimalityCertificate.sound (certificate : OptimalityCertificate m spec) :
    Optimal m spec certificate.program :=
  ⟨certificate.correct, certificate.lower.sound⟩

/-- An actual shorter correct program contradicts a purported lower bound. -/
theorem shorter_correct_refutes_bound (correct : Correct m spec p)
    (short : score m p < bound) : ¬ LowerBound m spec bound := by
  intro lower
  have := lower p correct
  omega

end ProofsLean
