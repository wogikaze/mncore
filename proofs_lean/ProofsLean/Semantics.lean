import Std

namespace ProofsLean

/-- A semantic model. `Line` represents a complete parallel issue line, not one
unit's instruction. State must include memory, forwarding, communication and hazards.
This interface is not an implementation of the MN-Core ISA. -/
structure Machine where
  Line : Type
  State : Type
  Input : Type
  step : Line → State → Option State
  legal : List Line → Prop
  lineCost : Line → Nat
  positiveCost : ∀ line, 0 < lineCost line

abbrev Program (m : Machine) := List m.Line

def execute (m : Machine) : Program m → m.State → Option m.State
  | [], state => some state
  | line :: rest, state => (m.step line state).bind (execute m rest)

def score (m : Machine) : Program m → Nat
  | [] => 0
  | line :: rest => m.lineCost line + score m rest

theorem length_le_score (m : Machine) (p : Program m) : p.length ≤ score m p := by
  induction p with
  | nil => simp [score]
  | cons line rest ih =>
    have positive := m.positiveCost line
    simp only [List.length_cons, score]
    omega

/-- Input domain, initialization (including any zero-memory assumptions), and
output relation (including precision/tolerance) are explicit parts of a problem. -/
structure Problem (m : Machine) where
  admissible : m.Input → Prop
  initial : m.Input → m.State
  post : m.Input → m.State → Prop

def Correct (m : Machine) (spec : Problem m) (p : Program m) : Prop :=
  m.legal p ∧ ∀ input, spec.admissible input →
    ∃ result, execute m p (spec.initial input) = some result ∧ spec.post input result

/-- A domain restriction is a different specification, not a proof for all inputs. -/
def Problem.restrict (spec : Problem m) (inputs : List m.Input) : Problem m :=
  { spec with admissible := fun input => input ∈ inputs ∧ spec.admissible input }

theorem correct_restrict (h : Correct m spec p) (inputs : List m.Input) :
    Correct m (spec.restrict inputs) p := by
  refine ⟨h.1, ?_⟩
  intro input admissible
  exact h.2 input admissible.2

/-- A concrete admissible input that falsifies a program, including failed execution. -/
def Refutes (m : Machine) (spec : Problem m) (p : Program m) (input : m.Input) : Prop :=
  spec.admissible input ∧
    ¬ ∃ result, execute m p (spec.initial input) = some result ∧ spec.post input result

theorem refutes_not_correct (h : Refutes m spec p input) : ¬ Correct m spec p := by
  intro correct
  exact h.2 (correct.2 input h.1)

end ProofsLean
