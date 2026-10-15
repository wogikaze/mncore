import ProofsLean.Semantics

namespace ProofsLean

/-- Unknown semantics is distinct from a known execution failure. A missing ISA
implementation must not be used as a counterexample to program correctness. -/
inductive StepResult (State : Type) where
  | ok (state : State)
  | failure
  | unknown
  deriving Repr

structure PartialMachine where
  Line : Type
  State : Type
  Input : Type
  step : Line → State → StepResult State
  legal : List Line → Prop
  lineCost : Line → Nat
  positiveCost : ∀ line, 0 < lineCost line

def PartialMachine.Complete (m : PartialMachine) : Prop :=
  ∀ line state, m.step line state ≠ .unknown

/-- Conversion to the total proof interface requires semantic coverage for all
lines and all states. This does not establish correspondence with physical hardware. -/
def PartialMachine.seal (m : PartialMachine) (_complete : m.Complete) : Machine where
  Line := m.Line
  State := m.State
  Input := m.Input
  step := fun line state => match m.step line state with
    | .ok result => some result
    | .failure => none
    | .unknown => none
  legal := m.legal
  lineCost := m.lineCost
  positiveCost := m.positiveCost

theorem unknown_prevents_sealing (m : PartialMachine)
    (missing : ∃ line state, m.step line state = .unknown) : ¬ m.Complete := by
  intro complete
  obtain ⟨line, state, unknown⟩ := missing
  exact complete line state unknown

theorem sealed_success {m : PartialMachine} {line : m.Line} {state result : m.State}
    (complete : m.Complete)
    (success : m.step line state = .ok result) :
    (m.seal complete).step line state = some result := by
  simp [PartialMachine.seal, success]

theorem sealed_failure {m : PartialMachine} {line : m.Line} {state : m.State}
    (complete : m.Complete)
    (failure : m.step line state = .failure) :
    (m.seal complete).step line state = none := by
  simp [PartialMachine.seal, failure]

end ProofsLean
