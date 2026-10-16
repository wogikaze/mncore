import ProofsLean.Enumeration
import ProofsLean.FiniteIssue

/-! Connect the bounded MN-Core instruction-line carrier to the generic
cost-bounded enumeration interface. Parser, assembler and hazard completeness
are intentionally separate obligations. -/
namespace ProofsLean.MNCore.Issue

/-- Fixed-cost-bounded instruction lines satisfying the proved payload
    envelopes form a finite subtype. The envelope condition is what remains to
    be established for every genuinely legal line. -/
theorem InstructionLine.costBelowEnvelope_finite (bound : Nat) :
    Finite {line : InstructionLine //
      InstructionLine.cost line < bound ∧ line.inFiniteEnvelope bound} := by
  letI : Finite {line : InstructionLine // line.inFiniteEnvelope bound} :=
    InstructionLine.inFiniteEnvelope_finite bound
  exact Finite.of_injective
    (fun line : {line : InstructionLine //
      InstructionLine.cost line < bound ∧ line.inFiniteEnvelope bound} =>
        (⟨line.1, line.2.2⟩ : {line : InstructionLine //
          line.inFiniteEnvelope bound}))
    (by
      intro a b equal
      apply Subtype.ext
      exact congrArg
        (fun line : {line : InstructionLine // line.inFiniteEnvelope bound} => line.1)
        equal)

/-- A concrete finite alphabet for one cost bound, obtained from the
Mathlib `Fintype` of the bounded-envelope subtype. The list can be enormous;
this definition is for completeness proofs and does not claim enumeration is
computationally practical. -/
noncomputable def InstructionLine.costBelowEnvelopeAlphabet (bound : Nat) :
    List InstructionLine := by
  let Carrier := {line : InstructionLine //
    InstructionLine.cost line < bound ∧ line.inFiniteEnvelope bound}
  letI : Finite Carrier := InstructionLine.costBelowEnvelope_finite bound
  letI : Fintype Carrier := Fintype.ofFinite _
  exact (Finset.univ.image fun candidate : Carrier => candidate.1).toList

theorem InstructionLine.mem_costBelowEnvelopeAlphabet (bound : Nat)
    (line : InstructionLine) (cost : InstructionLine.cost line < bound)
    (envelope : line.inFiniteEnvelope bound) :
    line ∈ InstructionLine.costBelowEnvelopeAlphabet bound := by
  classical
  simp only [InstructionLine.costBelowEnvelopeAlphabet,
    Finset.mem_toList, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨⟨line, cost, envelope⟩, rfl⟩

/-- If the supplied legal-line obligation places every bounded legal line in
the proved payload envelope, the explicit Fintype alphabet covers them all. -/
theorem InstructionLine.legalCostBelowEnvelope_covered
    (bound : Nat)
    (legal : InstructionLine → Prop)
    (covered : ∀ line, legal line → InstructionLine.cost line < bound →
      line.inFiniteEnvelope bound) :
    ∀ line, legal line → InstructionLine.cost line < bound →
      line ∈ InstructionLine.costBelowEnvelopeAlphabet bound := by
  intro line isLegal cost
  exact InstructionLine.mem_costBelowEnvelopeAlphabet bound line cost
    (covered line isLegal cost)

/-- If every legal line below the score bound satisfies the payload envelope,
then the legal, cost-bounded lines have a finite carrier. This is the remaining
linewise inclusion obligation needed by the machine-specific enumeration. -/
theorem InstructionLine.legalCostBelowEnvelope_finite
    (bound : Nat)
    (legal : InstructionLine → Prop)
    (covered : ∀ line, legal line → InstructionLine.cost line < bound →
      line.inFiniteEnvelope bound) :
    Finite {line : InstructionLine //
      legal line ∧ InstructionLine.cost line < bound} := by
  letI : Finite {line : InstructionLine //
      InstructionLine.cost line < bound ∧ line.inFiniteEnvelope bound} :=
    InstructionLine.costBelowEnvelope_finite bound
  exact Finite.of_injective
    (fun line : {line : InstructionLine //
      legal line ∧ InstructionLine.cost line < bound} =>
        (⟨line.1, line.2.2, covered line.1 line.2.1 line.2.2⟩ :
          {line : InstructionLine //
            InstructionLine.cost line < bound ∧ line.inFiniteEnvelope bound}))
    (by
      intro a b equal
      apply Subtype.ext
      exact congrArg
        (fun line : {line : InstructionLine //
          InstructionLine.cost line < bound ∧ line.inFiniteEnvelope bound} => line.1)
        equal)

/-- The legal subset itself has a `Fintype`, whenever every bounded legal line
satisfies the payload envelope. This is the exact finite carrier needed by a
machine-specific alphabet; the legality predicate remains an explicit input. -/
noncomputable def InstructionLine.legalCostBelowFintype
    (bound : Nat)
    (legal : InstructionLine → Prop)
    (covered : ∀ line, legal line → InstructionLine.cost line < bound →
      line.inFiniteEnvelope bound) :
    Fintype {line : InstructionLine //
      legal line ∧ InstructionLine.cost line < bound} := by
  letI : Finite {line : InstructionLine //
      legal line ∧ InstructionLine.cost line < bound} :=
    InstructionLine.legalCostBelowEnvelope_finite bound legal covered
  exact Fintype.ofFinite _

/-- A concrete list of precisely the legal lines below a fixed cost bound. -/
noncomputable def InstructionLine.legalCostBelowAlphabet
    (bound : Nat)
    (legal : InstructionLine → Prop)
    (covered : ∀ line, legal line → InstructionLine.cost line < bound →
      line.inFiniteEnvelope bound) :
    List InstructionLine := by
  let Carrier := {line : InstructionLine //
    legal line ∧ InstructionLine.cost line < bound}
  letI : Fintype Carrier := InstructionLine.legalCostBelowFintype
    bound legal covered
  exact (Finset.univ.image fun candidate : Carrier => candidate.1).toList

theorem InstructionLine.mem_legalCostBelowAlphabet
    (bound : Nat)
    (legal : InstructionLine → Prop)
    (covered : ∀ line, legal line → InstructionLine.cost line < bound →
      line.inFiniteEnvelope bound)
    (line : InstructionLine) (isLegal : legal line)
    (cost : InstructionLine.cost line < bound) :
    line ∈ InstructionLine.legalCostBelowAlphabet bound legal covered := by
  classical
  simp only [InstructionLine.legalCostBelowAlphabet, Finset.mem_toList,
    Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨⟨line, isLegal, cost⟩, rfl⟩

end ProofsLean.MNCore.Issue
