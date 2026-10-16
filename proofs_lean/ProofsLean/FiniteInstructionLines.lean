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

end ProofsLean.MNCore.Issue
