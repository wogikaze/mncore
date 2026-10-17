import ProofsLean.FiniteInstructionLines
import ProofsLean.HazardTrace
import ProofsLean.ParsedIntegerStep
import ProofsLean.PartialSemantics

/-! Program-level projections for normalized MN-Core instruction rows.
The candidate-domain machine deliberately treats every normalized executable
line sequence as legal. Issue conflicts, runtime hazards, and disabled-unit
errors belong in `step`; the older checker-constrained projection is retained
below only as a bounded-enumeration theorem, not as the machine legality rule. -/
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

/-- Broad normalized-source domain. `InstructionLine` is already the executable
result type of successful source normalization, so all values of this line type
are admitted here. Operational issue and hazard failures will be represented
by `.failure` in `step` as semantics are connected. -/
def _root_.ProofsLean.MNCore.partialMachine : ProofsLean.PartialMachine where
  Line := InstructionLine
  State := Unit
  Input := Unit
  step := fun _ _ => .unknown
  legal := fun _ => True
  lineCost := InstructionLine.cost
  positiveCost := InstructionLine.cost_positive

theorem _root_.ProofsLean.MNCore.partialMachine_legal_all
    (program : ProofsLean.MNCore.partialMachine.Program) :
    ProofsLean.MNCore.partialMachine.legal program := by
  trivial

/-- Every executable row emitted by successful source normalization belongs to
the broad machine domain. Zero-cost records and mask controls have no
`InstructionLine` image and are handled by normalization/control lowering. -/
theorem _root_.ProofsLean.MNCore.normalizedExecutableLine_legal
    (source : ParsedLine) (normalized : List NormalizedLine)
    (_success : source.normalizeForSubmission? = some normalized)
    (candidate : NormalizedLine) (_member : candidate ∈ normalized)
    (line : InstructionLine) (emitted : candidate.toInstruction? = some line) :
    ProofsLean.MNCore.partialMachine.legal [line] := by
  exact ProofsLean.MNCore.partialMachine_legal_all [line]

/-- Historical bounded projection used to prove finite normalized-line
alphabets. It is intentionally not the legal predicate of `partialMachine`:
the issue and hazard filters are diagnostic constraints until moved into step. -/
def _root_.ProofsLean.MNCore.boundedIssueMachine : ProofsLean.PartialMachine where
  Line := InstructionLine
  State := Unit
  Input := Unit
  step := fun _ _ => .unknown
  legal := InstructionLine.programIssueAndHazardLegal
  lineCost := InstructionLine.cost
  positiveCost := InstructionLine.cost_positive

theorem _root_.ProofsLean.MNCore.partialMachine_not_complete :
    ¬ ProofsLean.MNCore.partialMachine.Complete := by
  apply ProofsLean.unknown_prevents_sealing
  exact ⟨InstructionLine.pe [], (), rfl⟩

theorem _root_.ProofsLean.MNCore.boundedIssueMachine_not_complete :
    ¬ ProofsLean.MNCore.boundedIssueMachine.Complete := by
  apply ProofsLean.unknown_prevents_sealing
  exact ⟨InstructionLine.pe [], (), rfl⟩

/-- Partial bridge from the finite assembler-word carrier to bounded
enumeration. Every encoded word is admitted, so this is an over-approximation
of legal assembler output; the source-to-word and word-to-semantics relations
are intentionally not claimed here. -/
def encodedUniverseMachine : ProofsLean.PartialMachine where
  Line := AssemblerInstructionWord
  State := Unit
  Input := Unit
  step := fun _ _ => .unknown
  legal := fun _ => True
  lineCost := fun _ => 1
  positiveCost := by intro _; decide

noncomputable def encodedUniverseAlphabet : List AssemblerInstructionWord := by
  classical
  exact Finset.univ.toList

theorem mem_encodedUniverseAlphabet (line : AssemblerInstructionWord) :
    line ∈ encodedUniverseAlphabet := by
  classical
  change line ∈ (Finset.univ : Finset AssemblerInstructionWord).toList
  exact Finset.mem_toList.mpr (Finset.mem_univ line)

theorem encodedUniverseAlphabet_coversBelow (bound : Nat) :
    encodedUniverseMachine.LegalLinesCoveredBelow encodedUniverseAlphabet bound := by
  classical
  intro program legal short line member
  exact mem_encodedUniverseAlphabet (line : AssemblerInstructionWord)

theorem encodedUniverse_shortPrograms_complete {bound : Nat}
    (program : encodedUniverseMachine.Program)
    (legal : encodedUniverseMachine.legal program)
    (short : encodedUniverseMachine.score program < bound) :
    program ∈ encodedUniverseMachine.shortPrograms encodedUniverseAlphabet bound :=
  encodedUniverseMachine.shortPrograms_complete
    (encodedUniverseAlphabet_coversBelow bound) program legal short

theorem encodedUniverse_legalLinesCostBelow_finite (bound : Nat) :
    (encodedUniverseMachine.legalLinesCostBelow bound).Finite := by
  classical
  apply Set.Finite.subset (List.finite_toSet encodedUniverseAlphabet)
  intro line member
  exact mem_encodedUniverseAlphabet (line : AssemblerInstructionWord)

theorem encodedUniverseMachine_not_complete :
    ¬ encodedUniverseMachine.Complete := by
  apply ProofsLean.unknown_prevents_sealing
  exact ⟨Sum.inl (0 : BitVec 426), (), rfl⟩


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

theorem _root_.ProofsLean.MNCore.boundedIssueMachine_legalLinesCostBelow_finite (bound : Nat) :
    (ProofsLean.PartialMachine.legalLinesCostBelow
      ProofsLean.MNCore.boundedIssueMachine bound).Finite := by
  apply Set.Finite.subset (List.finite_toSet
    (InstructionLine.costBelowEnvelopeAlphabet bound))
  intro line member
  rcases member with ⟨program, legal, lineMember, cost⟩
  exact InstructionLine.mem_costBelowEnvelopeAlphabet bound line cost
    (InstructionLine.programIssueAndHazardLegal_line_envelope
      bound program legal line lineMember cost)

/-- The cost-bounded legal line set itself has a Mathlib `Fintype`. This uses
the program-level local issue and cross-line hazard predicate, not merely the
single-line envelope. -/
noncomputable def _root_.ProofsLean.MNCore.boundedIssueMachine_legalLineFintype
    (bound : Nat) :
    Fintype {line : InstructionLine //
      line ∈ ProofsLean.PartialMachine.legalLinesCostBelow
        ProofsLean.MNCore.boundedIssueMachine bound} := by
  letI : Finite {line : InstructionLine //
      line ∈ ProofsLean.PartialMachine.legalLinesCostBelow
        ProofsLean.MNCore.boundedIssueMachine bound} :=
    ProofsLean.MNCore.boundedIssueMachine_legalLinesCostBelow_finite bound
  exact Fintype.ofFinite _

/-- Exact bound-specific alphabet for lines occurring in legal, short MN-Core
programs. Its construction is noncomputable because the finite carrier may be
astronomically large, but it directly discharges the generic coverage premise. -/
noncomputable def _root_.ProofsLean.MNCore.boundedIssueMachine_legalLineAlphabet
    (bound : Nat) : List InstructionLine := by
  let Carrier := {line : InstructionLine //
    line ∈ ProofsLean.PartialMachine.legalLinesCostBelow
      ProofsLean.MNCore.boundedIssueMachine bound}
  letI : Fintype Carrier :=
    ProofsLean.MNCore.boundedIssueMachine_legalLineFintype bound
  exact (Finset.univ : Finset Carrier).toList.map Subtype.val

theorem _root_.ProofsLean.MNCore.boundedIssueMachine_legalLineAlphabet_covers
    (bound : Nat) :
    ProofsLean.PartialMachine.LegalLinesCoveredBelow
      ProofsLean.MNCore.boundedIssueMachine
      (ProofsLean.MNCore.boundedIssueMachine_legalLineAlphabet bound) bound := by
  intro program legal short line member
  have cost : line.cost < bound := by
    exact lt_of_le_of_lt
      (ProofsLean.PartialMachine.lineCost_le_score
        ProofsLean.MNCore.boundedIssueMachine program line member)
      short
  have occurs : line ∈ ProofsLean.PartialMachine.legalLinesCostBelow
      ProofsLean.MNCore.boundedIssueMachine bound :=
    ⟨program, legal, member, cost⟩
  classical
  let Carrier := {candidate : InstructionLine //
    candidate ∈ ProofsLean.PartialMachine.legalLinesCostBelow
      ProofsLean.MNCore.boundedIssueMachine bound}
  letI : Fintype Carrier :=
    ProofsLean.MNCore.boundedIssueMachine_legalLineFintype bound
  change line ∈ ((Finset.univ : Finset Carrier).toList.map Subtype.val)
  apply List.mem_map.mpr
  refine ⟨⟨line, occurs⟩, ?_, rfl⟩
  exact Finset.mem_toList.mpr (Finset.mem_univ _)

theorem _root_.ProofsLean.MNCore.boundedIssueMachine_exactAlphabet_shortPrograms_complete
    (bound : Nat) (program : ProofsLean.MNCore.boundedIssueMachine.Program)
    (legal : ProofsLean.MNCore.boundedIssueMachine.legal program)
    (short : ProofsLean.MNCore.boundedIssueMachine.score program < bound) :
    program ∈ ProofsLean.PartialMachine.shortPrograms
      ProofsLean.MNCore.boundedIssueMachine
      (ProofsLean.MNCore.boundedIssueMachine_legalLineAlphabet bound) bound :=
  ProofsLean.PartialMachine.shortPrograms_complete
    ProofsLean.MNCore.boundedIssueMachine
    (ProofsLean.MNCore.boundedIssueMachine_legalLineAlphabet_covers bound)
    program legal short

theorem _root_.ProofsLean.MNCore.boundedIssueMachine_costBelowAlphabet_covers
    (bound : Nat) :
    ProofsLean.PartialMachine.LegalLinesCoveredBelow
      ProofsLean.MNCore.boundedIssueMachine
      (InstructionLine.costBelowEnvelopeAlphabet bound) bound := by
  intro program legal short line member
  have cost : line.cost < bound := by
    exact lt_of_le_of_lt
      (ProofsLean.PartialMachine.lineCost_le_score
        ProofsLean.MNCore.boundedIssueMachine program line member)
      short
  exact InstructionLine.mem_costBelowEnvelopeAlphabet bound line cost
    (InstructionLine.programIssueAndHazardLegal_line_envelope
      bound program legal line member cost)

theorem _root_.ProofsLean.MNCore.boundedIssueMachine_shortPrograms_complete
    (bound : Nat) (program : ProofsLean.MNCore.boundedIssueMachine.Program)
    (legal : ProofsLean.MNCore.boundedIssueMachine.legal program)
    (short : ProofsLean.MNCore.boundedIssueMachine.score program < bound) :
    program ∈ ProofsLean.PartialMachine.shortPrograms
      ProofsLean.MNCore.boundedIssueMachine
      (InstructionLine.costBelowEnvelopeAlphabet bound) bound :=
  ProofsLean.PartialMachine.shortPrograms_complete
    ProofsLean.MNCore.boundedIssueMachine
    (ProofsLean.MNCore.boundedIssueMachine_costBelowAlphabet_covers bound)
    program legal short

end ProofsLean.MNCore.Issue
