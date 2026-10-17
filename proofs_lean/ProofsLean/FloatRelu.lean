import ProofsLean.OperatorAbstraction

/-! Value abstraction for the single-precision `frelu` used by problem 3.
The challenge input domain contains finite values only. IEEE negative zero
compares equal to zero, so both signed zeros select the second operand. -/
namespace ProofsLean.MNCore.FloatRelu

def isZero (value : BitVec 32) : Bool :=
  value.extractLsb' 0 31 == 0

def isNonnegative (value : BitVec 32) : Bool :=
  !value.msb || isZero value

def negativeZero : BitVec 32 := 0x80000000

def relu (condition value : BitVec 32) : BitVec 32 :=
  if isNonnegative condition then value else negativeZero

def abstractRelu {Atom : Type}
    (condition value : AbstractValue Atom (BitVec 32)) :
    AbstractValue Atom (BitVec 32) :=
  AbstractValue.binary .floatingMau relu condition value

theorem abstractRelu_evaluation {Atom : Type}
    (condition value : AbstractValue Atom (BitVec 32))
    (environment : Atom → BitVec 32) :
    (abstractRelu condition value).evaluate environment =
      relu (condition.evaluate environment) (value.evaluate environment) := by
  exact AbstractValue.binary_evaluation .floatingMau relu condition value environment

theorem relu_positive (value : BitVec 32) : relu 0x3F800000 value = value := by
  have h : isNonnegative (0x3F800000 : BitVec 32) = true := by decide
  change (if isNonnegative (0x3F800000 : BitVec 32) then value else negativeZero) = value
  rw [h]
  rfl

theorem relu_negative (value : BitVec 32) : relu 0xBF800000 value = negativeZero := by
  have h : isNonnegative (0xBF800000 : BitVec 32) = false := by decide
  change (if isNonnegative (0xBF800000 : BitVec 32) then value else negativeZero) = negativeZero
  rw [h]
  rfl

theorem relu_positive_zero (value : BitVec 32) : relu 0 value = value := by
  have h : isNonnegative (0 : BitVec 32) = true := by decide
  change (if isNonnegative (0 : BitVec 32) then value else negativeZero) = value
  rw [h]
  rfl

theorem relu_negative_zero (value : BitVec 32) : relu 0x80000000 value = value := by
  have h : isNonnegative (0x80000000 : BitVec 32) = true := by decide
  change (if isNonnegative (0x80000000 : BitVec 32) then value else negativeZero) = value
  rw [h]
  rfl

theorem abstractRelu_dependencies_are_sound {Atom : Type}
    (condition value : AbstractValue Atom (BitVec 32))
    (leftEnv rightEnv : Atom → BitVec 32)
    (agree : ∀ atom, atom ∈ (abstractRelu condition value).dependencies →
      leftEnv atom = rightEnv atom) :
    (abstractRelu condition value).evaluate leftEnv =
      (abstractRelu condition value).evaluate rightEnv :=
  AbstractValue.depends_only_on_inputs _ leftEnv rightEnv agree

end ProofsLean.MNCore.FloatRelu
