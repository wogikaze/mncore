import ProofsLean.PartialSemantics

/-! A sound, operation-independent abstraction for constant and data dependence.

Every modeled unit can construct results with the same smart constructors. If
all inputs are constants, the operation is evaluated exactly. Otherwise the
expression retains its inputs and therefore a conservative dependency set.
This abstraction is exact about constants and dependencies, while strict value
semantics can remain limited to operations needed for a correctness proof. -/
namespace ProofsLean.MNCore

inductive UnitKind where
  | integerAlu
  | floatingMau
  | matrixUnit
  | l1BlockMemory
  | l2BlockMemory
  | mvTransfer
  | peTransfer
  deriving DecidableEq, Repr

def UnitKind.all : List UnitKind :=
  [.integerAlu, .floatingMau, .matrixUnit, .l1BlockMemory,
   .l2BlockMemory, .mvTransfer, .peTransfer]

theorem UnitKind.mem_all (unit : UnitKind) : unit ∈ UnitKind.all := by
  cases unit <;> simp [UnitKind.all]

inductive Expr (Atom : Type u) (Value : Type v) where
  | constant (value : Value)
  | input (atom : Atom)
  | unary (op : Value → Value) (arg : Expr Atom Value)
  | binary (op : Value → Value → Value)
      (left right : Expr Atom Value)
  | ternary (op : Value → Value → Value → Value)
      (first second third : Expr Atom Value)

namespace Expr

variable {Atom : Type u} {Value : Type v}

def evaluate (environment : Atom → Value) : Expr Atom Value → Value
  | .constant value => value
  | .input atom => environment atom
  | .unary op arg => op (evaluate environment arg)
  | .binary op left right => op (evaluate environment left) (evaluate environment right)
  | .ternary op first second third =>
      op (evaluate environment first) (evaluate environment second)
        (evaluate environment third)

def dependencies : Expr Atom Value → List Atom
  | .constant _ => []
  | .input atom => [atom]
  | .unary _ arg => dependencies arg
  | .binary _ left right => dependencies left ++ dependencies right
  | .ternary _ first second third =>
      dependencies first ++ dependencies second ++ dependencies third

def mkUnary (op : Value → Value) (arg : Expr Atom Value) : Expr Atom Value :=
  match arg with
  | .constant value => .constant (op value)
  | _ => .unary op arg

def mkBinary (op : Value → Value → Value) (left right : Expr Atom Value) :
    Expr Atom Value :=
  match left, right with
  | .constant x, .constant y => .constant (op x y)
  | _, _ => .binary op left right

def mkTernary (op : Value → Value → Value → Value)
    (first second third : Expr Atom Value) : Expr Atom Value :=
  match first, second, third with
  | .constant x, .constant y, .constant z => .constant (op x y z)
  | _, _, _ => .ternary op first second third

theorem evaluate_unary (environment : Atom → Value)
    (op : Value → Value) (arg : Expr Atom Value) :
    (mkUnary op arg).evaluate environment = op (arg.evaluate environment) := by
  cases arg <;> rfl

theorem evaluate_binary (environment : Atom → Value)
    (op : Value → Value → Value) (left right : Expr Atom Value) :
    (mkBinary op left right).evaluate environment =
      op (left.evaluate environment) (right.evaluate environment) := by
  cases left <;> cases right <;> rfl

theorem evaluate_ternary (environment : Atom → Value)
    (op : Value → Value → Value → Value)
    (first second third : Expr Atom Value) :
    (mkTernary op first second third).evaluate environment =
      op (first.evaluate environment) (second.evaluate environment)
        (third.evaluate environment) := by
  cases first <;> cases second <;> cases third <;> rfl

theorem evaluate_constant (value : Value) (environment : Atom → Value) :
    (constant value : Expr Atom Value).evaluate environment = value := rfl

theorem depends_only_on_inputs (expression : Expr Atom Value)
    (leftEnvironment rightEnvironment : Atom → Value)
    (agree : ∀ atom, atom ∈ expression.dependencies →
      leftEnvironment atom = rightEnvironment atom) :
    expression.evaluate leftEnvironment = expression.evaluate rightEnvironment := by
  induction expression with
  | constant value => rfl
  | input atom => exact agree atom (by simp [dependencies])
  | unary op arg ih =>
      simp only [evaluate]
      congr 1
      apply ih
      intro atom member
      exact agree atom (by simpa [dependencies] using member)
  | binary op left right ihLeft ihRight =>
      simp only [evaluate]
      congr 1
      · apply ihLeft
        intro atom member
        exact agree atom (by simp [dependencies, member])
      · apply ihRight
        intro atom member
        exact agree atom (by simp [dependencies, member])
  | ternary op first second third ihFirst ihSecond ihThird =>
      simp only [evaluate]
      congr 1
      · apply ihFirst
        intro atom member
        exact agree atom (by simp [dependencies, member])
      · apply ihSecond
        intro atom member
        exact agree atom (by simp [dependencies, member])
      · apply ihThird
        intro atom member
        exact agree atom (by simp [dependencies, member])

end Expr

/-! The producer tag records which architectural unit produced a value; the
expression carries its constants and exact/conservative input dependencies. -/
structure AbstractValue (Atom : Type u) (Value : Type v) where
  producer : UnitKind
  expression : Expr Atom Value

def AbstractValue.constant (unit : UnitKind) (value : Value) :
    AbstractValue Atom Value := ⟨unit, .constant value⟩

def AbstractValue.input (unit : UnitKind) (atom : Atom) :
    AbstractValue Atom Value := ⟨unit, .input atom⟩

def AbstractValue.unary (unit : UnitKind) (op : Value → Value)
    (arg : AbstractValue Atom Value) : AbstractValue Atom Value :=
  ⟨unit, Expr.mkUnary op arg.expression⟩

def AbstractValue.binary (unit : UnitKind) (op : Value → Value → Value)
    (left right : AbstractValue Atom Value) : AbstractValue Atom Value :=
  ⟨unit, Expr.mkBinary op left.expression right.expression⟩

def AbstractValue.ternary (unit : UnitKind)
    (op : Value → Value → Value → Value)
    (first second third : AbstractValue Atom Value) : AbstractValue Atom Value :=
  ⟨unit, Expr.mkTernary op first.expression second.expression third.expression⟩

namespace AbstractValue

variable {Atom : Type u} {Value : Type v}

def evaluate (environment : Atom → Value)
    (value : AbstractValue Atom Value) : Value :=
  value.expression.evaluate environment

def dependencies (value : AbstractValue Atom Value) : List Atom :=
  value.expression.dependencies

theorem depends_only_on_inputs (value : AbstractValue Atom Value)
    (leftEnvironment rightEnvironment : Atom → Value)
    (agree : ∀ atom, atom ∈ value.dependencies →
      leftEnvironment atom = rightEnvironment atom) :
    value.evaluate leftEnvironment = value.evaluate rightEnvironment :=
  value.expression.depends_only_on_inputs leftEnvironment rightEnvironment agree

theorem unary_evaluation (unit : UnitKind) (op : Value → Value)
    (input : AbstractValue Atom Value) (environment : Atom → Value) :
    (unary unit op input).evaluate environment = op (input.evaluate environment) := by
  exact Expr.evaluate_unary environment op input.expression

theorem binary_evaluation (unit : UnitKind) (op : Value → Value → Value)
    (left right : AbstractValue Atom Value) (environment : Atom → Value) :
    (binary unit op left right).evaluate environment =
      op (left.evaluate environment) (right.evaluate environment) := by
  exact Expr.evaluate_binary environment op left.expression right.expression

theorem ternary_evaluation (unit : UnitKind)
    (op : Value → Value → Value → Value)
    (first second third : AbstractValue Atom Value)
    (environment : Atom → Value) :
    (ternary unit op first second third).evaluate environment =
      op (first.evaluate environment) (second.evaluate environment)
        (third.evaluate environment) := by
  exact Expr.evaluate_ternary environment op first.expression second.expression
    third.expression

end AbstractValue

end ProofsLean.MNCore
