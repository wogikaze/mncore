import ProofsLean.FiniteInstructionLines
import ProofsLean.HazardTrace
import ProofsLean.ParsedIntegerStep

/-! Program-level legality projection for normalized MN-Core instruction rows.
This combines local issue checks with the existing PE and block hazard
analyzers; source-parser completeness and full ISA semantics remain separate. -/
namespace ProofsLean.MNCore.Issue

open ProofsLean.MNCore.HazardTrace
open ProofsLean.MNCore.PEMemory

def InstructionLine.toParsedMaskedStatements : InstructionLine →
    List ParsedMaskedSourceStatement
  | .pe expressions =>
      [.issue (.pe (expressions.map NormalizedExpr.toParsed))]
  | .nop count _ => List.replicate count.val (.issue .nop)
  | .mv _ => [.issue .nop]

def InstructionLine.programToParsedMaskedSource
    (program : List InstructionLine) : List ParsedMaskedSourceStatement :=
  program.flatMap InstructionLine.toParsedMaskedStatements

def InstructionLine.programIssueAndHazardLegal
    (program : List InstructionLine) : Prop :=
  (∀ line ∈ program, line.localIssueLegal) ∧
    parsedSourceBlockHazardSafe (program.map InstructionLine.toParsed) 0 ∧
    ∀ control : ParsedMaskExecutionControl,
      parsedSourcePEHazardViolations?
        (InstructionLine.programToParsedMaskedSource program) control = some []

theorem InstructionLine.programIssueAndHazardLegal_line_local
    (program : List InstructionLine)
    (legal : InstructionLine.programIssueAndHazardLegal program)
    (line : InstructionLine) (member : line ∈ program) :
    line.localIssueLegal :=
  legal.1 line member

theorem InstructionLine.programIssueAndHazardLegal_line_envelope
    (bound : Nat) (program : List InstructionLine)
    (legal : InstructionLine.programIssueAndHazardLegal program)
    (line : InstructionLine) (member : line ∈ program)
    (cost : line.cost < bound) :
    line.inFiniteEnvelope bound :=
  InstructionLine.localIssueLegal_inFiniteEnvelope bound line
    (legal.1 line member) cost

def InstructionLine.programLegalLinesCostBelow (bound : Nat) : Set InstructionLine :=
  {line | ∃ program, InstructionLine.programIssueAndHazardLegal program ∧
    line ∈ program ∧ line.cost < bound}

theorem InstructionLine.programLegalLinesCostBelow_covered
    (bound : Nat) :
    ∀ line ∈ InstructionLine.programLegalLinesCostBelow bound,
      line ∈ InstructionLine.costBelowEnvelopeAlphabet bound := by
  intro line member
  rcases member with ⟨program, legal, lineMember, cost⟩
  exact InstructionLine.mem_costBelowEnvelopeAlphabet bound line cost
    (InstructionLine.programIssueAndHazardLegal_line_envelope
      bound program legal line lineMember cost)

theorem InstructionLine.programLegalLinesCostBelow_finite (bound : Nat) :
    (InstructionLine.programLegalLinesCostBelow bound).Finite := by
  apply Set.Finite.subset (List.finite_toSet
    (InstructionLine.costBelowEnvelopeAlphabet bound))
  exact InstructionLine.programLegalLinesCostBelow_covered bound

theorem InstructionLine.programIssueAndHazardLegal_nil :
    InstructionLine.programIssueAndHazardLegal [] := by
  constructor
  · simp
  constructor
  · exact parsedSourceBlockHazardSafe_nil 0
  · intro control
    change parsedSourcePEHazardViolations? [] control = some []
    simp [parsedSourcePEHazardViolations?, parsedSourcePEHazardConstraints?,
      parsedSourcePEHazardEvents?,
      ProofsLean.ControlNormalization.compileAdvancing,
      collectPEHazardConstraints, collectPEHazardConstraintsAux,
      violatingPEHazardConstraints]

end ProofsLean.MNCore.Issue
