import ProofsLean.SingleFMA

/-! Value-level model for the `fvmul` stage of problem 2 (multiply by 7).
As in the MAU datapath, multiplication is the FMA product with a zero
accumulator. The file covers one lane; the 4-line memory schedule is tracked
separately and is not yet connected to `PEMachine`. -/
namespace ProofsLean.MNCore.FloatMultiply

def multiply (left right : BitVec 32) : BitVec 32 :=
  SingleFMA.singleFma left right 0

def abstractMultiply {Atom : Type}
    (left right : AbstractValue Atom (BitVec 32)) :
    AbstractValue Atom (BitVec 32) :=
  AbstractValue.ternary .floatingMau (fun a b _ => multiply a b) left right
    (AbstractValue.constant .floatingMau 0)

theorem abstractMultiply_evaluation {Atom : Type}
    (left right : AbstractValue Atom (BitVec 32))
    (environment : Atom → BitVec 32) :
    (abstractMultiply left right).evaluate environment =
      multiply (left.evaluate environment) (right.evaluate environment) := by
  exact AbstractValue.ternary_evaluation .floatingMau
    (fun a b _ => multiply a b) left right
    (AbstractValue.constant .floatingMau 0) environment

def seven : BitVec 32 := 0x40E00000

theorem seven_times_one : multiply 0x3F800000 seven = seven := by decide

theorem seven_times_zero : multiply 0 seven = 0 := by decide

theorem seven_times_two : multiply 0x40000000 seven = 0x41600000 := by decide

theorem abstractMultiply_preserves_dependencies {Atom : Type}
    (left right : AbstractValue Atom (BitVec 32))
    (leftEnv rightEnv : Atom → BitVec 32)
    (agree : ∀ atom, atom ∈ (abstractMultiply left right).dependencies →
      leftEnv atom = rightEnv atom) :
    (abstractMultiply left right).evaluate leftEnv =
      (abstractMultiply left right).evaluate rightEnv :=
  AbstractValue.depends_only_on_inputs _ leftEnv rightEnv agree

end ProofsLean.MNCore.FloatMultiply
