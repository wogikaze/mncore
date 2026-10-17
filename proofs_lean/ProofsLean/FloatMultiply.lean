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

/-- Apply `fvmul` independently to the two single-precision lanes in a PE bus. -/
def multiplyBus (left right : BitVec 64) : BitVec 64 :=
  multiply (left.extractLsb' 32 32) (right.extractLsb' 32 32) ++
    multiply (left.extractLsb' 0 32) (right.extractLsb' 0 32)

def sevenBus : BitVec 64 := seven ++ seven

def multiplySevenBus (input : BitVec 64) : BitVec 64 :=
  multiplyBus input sevenBus

theorem multiplySevenBus_high (input : BitVec 64) :
    (multiplySevenBus input).extractLsb' 32 32 =
      multiply (input.extractLsb' 32 32) seven := by
  simp only [multiplySevenBus, multiplyBus, sevenBus]
  rw [BitVec.extractLsb'_append_eq_left, BitVec.extractLsb'_append_eq_left]

theorem multiplySevenBus_low (input : BitVec 64) :
    (multiplySevenBus input).extractLsb' 0 32 =
      multiply (input.extractLsb' 0 32) seven := by
  simp only [multiplySevenBus, multiplyBus, sevenBus]
  rw [BitVec.extractLsb'_append_eq_right, BitVec.extractLsb'_append_eq_right]

def abstractMultiplySevenBus {Atom : Type}
    (input : AbstractValue Atom (BitVec 64)) :
    AbstractValue Atom (BitVec 64) :=
  AbstractValue.unary .floatingMau multiplySevenBus input

theorem abstractMultiplySevenBus_evaluation {Atom : Type}
    (input : AbstractValue Atom (BitVec 64))
    (environment : Atom → BitVec 64) :
    (abstractMultiplySevenBus input).evaluate environment =
      multiplySevenBus (input.evaluate environment) := by
  exact AbstractValue.unary_evaluation .floatingMau multiplySevenBus input environment

theorem abstractMultiplySevenBus_dependencies_are_sound {Atom : Type}
    (input : AbstractValue Atom (BitVec 64))
    (leftEnv rightEnv : Atom → BitVec 64)
    (agree : ∀ atom, atom ∈ (abstractMultiplySevenBus input).dependencies →
      leftEnv atom = rightEnv atom) :
    (abstractMultiplySevenBus input).evaluate leftEnv =
      (abstractMultiplySevenBus input).evaluate rightEnv :=
  AbstractValue.depends_only_on_inputs _ leftEnv rightEnv agree

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
