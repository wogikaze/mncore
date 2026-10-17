import ProofsLean.SingleFMA

/-! A bit-level model of the `fvadd x -y out` datapath used by problem 1.a-b.
The instruction is a fused multiply-add with a unit multiplier and a
sign-flipped second addend. This file proves the constant/dependency tracking
for that cross-unit operation; full address and issue semantics remain separate
obligations. -/
namespace ProofsLean.MNCore.FloatSubtract

def negateBits (value : BitVec 32) : BitVec 32 := value ^^^ 0x80000000

def subtract (left right : BitVec 32) : BitVec 32 :=
  SingleFMA.singleFma left 0x3F800000 (negateBits right)

def abstractSubtract {Atom : Type}
    (left right : AbstractValue Atom (BitVec 32)) :
    AbstractValue Atom (BitVec 32) :=
  AbstractValue.ternary .floatingMau (fun a _ c => subtract a c) left
    (AbstractValue.constant .floatingMau 0x3F800000) right

theorem abstractSubtract_evaluation {Atom : Type}
    (left right : AbstractValue Atom (BitVec 32))
    (environment : Atom → BitVec 32) :
    (abstractSubtract left right).evaluate environment =
      subtract (left.evaluate environment) (right.evaluate environment) := by
  exact AbstractValue.ternary_evaluation .floatingMau (fun a _ c => subtract a c) left
    (AbstractValue.constant .floatingMau 0x3F800000) right environment

theorem subtract_one_zero : subtract 0x3F800000 0x3F800000 = 0 := by decide

theorem subtract_positive : subtract 0x41200000 0x40000000 = 0x41000000 := by decide

theorem subtract_negative : subtract 0x40000000 0x41200000 = 0xC1000000 := by decide

theorem subtract_preserves_dependencies {Atom : Type}
    (left right : AbstractValue Atom (BitVec 32))
    (leftEnv rightEnv : Atom → BitVec 32)
    (agree : ∀ atom, atom ∈ (abstractSubtract left right).dependencies →
      leftEnv atom = rightEnv atom) :
    (abstractSubtract left right).evaluate leftEnv =
      (abstractSubtract left right).evaluate rightEnv :=
  AbstractValue.depends_only_on_inputs _ leftEnv rightEnv agree

end ProofsLean.MNCore.FloatSubtract
