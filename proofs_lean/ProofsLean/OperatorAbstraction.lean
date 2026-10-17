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

/-! Cross-unit operators can change representation (for example, a bus plus
flags produces a `BusResult`). This companion abstraction keeps an evaluator,
an exact constant result when available, and a conservative dependency set
without requiring input and output types to be equal. -/
structure AbstractComputation (Atom : Type u) (Input : Type v) (Output : Type w) where
  producer : UnitKind
  run : (Atom → Input) → Output
  dependencies : List Atom
  constantValue : Option Output

namespace AbstractComputation

variable {Atom : Type u} {Input : Type v} {Output : Type w}

def constant (unit : UnitKind) (value : Output) : AbstractComputation Atom Input Output :=
  ⟨unit, fun _ => value, [], some value⟩

def evaluate (computation : AbstractComputation Atom Input Output)
    (environment : Atom → Input) : Output :=
  computation.run environment

def binary (unit : UnitKind) (operation : Input → Input → Output)
    (left right : AbstractValue Atom Input) : AbstractComputation Atom Input Output :=
  let folded := match left.expression, right.expression with
    | .constant x, .constant y => some (operation x y)
    | _, _ => none
  ⟨unit, fun environment => operation (left.evaluate environment) (right.evaluate environment),
    left.dependencies ++ right.dependencies, folded⟩

def unary (unit : UnitKind) (operation : Input → Output) (input : AbstractValue Atom Input) :
    AbstractComputation Atom Input Output :=
  let folded := match input.expression with
    | .constant value => some (operation value)
    | _ => none
  ⟨unit, fun environment => operation (input.evaluate environment), input.dependencies, folded⟩

def ternary (unit : UnitKind) (operation : Input → Input → Input → Output)
    (first second third : AbstractValue Atom Input) :
    AbstractComputation Atom Input Output :=
  let folded := match first.expression, second.expression, third.expression with
    | .constant x, .constant y, .constant z => some (operation x y z)
    | _, _, _ => none
  ⟨unit, fun environment => operation (first.evaluate environment)
      (second.evaluate environment) (third.evaluate environment),
    first.dependencies ++ second.dependencies ++ third.dependencies, folded⟩

theorem binary_records_producer (unit : UnitKind) (operation : Input → Input → Output)
    (left right : AbstractValue Atom Input) :
    (binary unit operation left right).producer = unit := rfl

theorem unary_records_producer (unit : UnitKind) (operation : Input → Output)
    (input : AbstractValue Atom Input) :
    (unary unit operation input).producer = unit := rfl

theorem ternary_records_producer (unit : UnitKind)
    (operation : Input → Input → Input → Output)
    (first second third : AbstractValue Atom Input) :
    (ternary unit operation first second third).producer = unit := rfl

theorem binary_evaluation (unit : UnitKind) (operation : Input → Input → Output)
    (left right : AbstractValue Atom Input) (environment : Atom → Input) :
    (binary unit operation left right).evaluate environment =
      operation (left.evaluate environment) (right.evaluate environment) := rfl

theorem unary_evaluation (unit : UnitKind) (operation : Input → Output)
    (input : AbstractValue Atom Input) (environment : Atom → Input) :
    (unary unit operation input).evaluate environment = operation (input.evaluate environment) := rfl

theorem ternary_evaluation (unit : UnitKind) (operation : Input → Input → Input → Output)
    (first second third : AbstractValue Atom Input) (environment : Atom → Input) :
    (ternary unit operation first second third).evaluate environment =
      operation (first.evaluate environment) (second.evaluate environment)
        (third.evaluate environment) := rfl

theorem binary_constants_exact (unit inputUnit : UnitKind)
    (operation : Input → Input → Output) (left right : Input) :
    (binary unit operation (AbstractValue.constant (Atom := Atom) inputUnit left)
      (AbstractValue.constant (Atom := Atom) inputUnit right)).constantValue =
        some (operation left right) := rfl

theorem unary_constants_exact (unit inputUnit : UnitKind) (operation : Input → Output)
    (input : Input) :
    (unary unit operation (AbstractValue.constant (Atom := Atom) inputUnit input)).constantValue =
      some (operation input) := rfl

theorem ternary_constants_exact (unit inputUnit : UnitKind)
    (operation : Input → Input → Input → Output) (first second third : Input) :
    (ternary unit operation (AbstractValue.constant (Atom := Atom) inputUnit first)
      (AbstractValue.constant (Atom := Atom) inputUnit second)
      (AbstractValue.constant (Atom := Atom) inputUnit third)).constantValue =
        some (operation first second third) := rfl

theorem binary_dependencies_are_sound (unit : UnitKind) (operation : Input → Input → Output)
    (left right : AbstractValue Atom Input)
    (leftEnvironment rightEnvironment : Atom → Input)
    (agree : ∀ atom, atom ∈ (binary unit operation left right).dependencies →
      leftEnvironment atom = rightEnvironment atom) :
    (binary unit operation left right).evaluate leftEnvironment =
      (binary unit operation left right).evaluate rightEnvironment := by
  simp only [binary_evaluation]
  congr 1
  · apply left.depends_only_on_inputs leftEnvironment rightEnvironment
    intro atom member
    exact agree atom (by simp [binary, member])
  · apply right.depends_only_on_inputs leftEnvironment rightEnvironment
    intro atom member
    exact agree atom (by simp [binary, member])

theorem unary_dependencies_are_sound (unit : UnitKind) (operation : Input → Output)
    (input : AbstractValue Atom Input)
    (leftEnvironment rightEnvironment : Atom → Input)
    (agree : ∀ atom, atom ∈ (unary unit operation input).dependencies →
      leftEnvironment atom = rightEnvironment atom) :
    (unary unit operation input).evaluate leftEnvironment =
      (unary unit operation input).evaluate rightEnvironment := by
  rw [unary_evaluation, unary_evaluation]
  congr 1
  apply input.depends_only_on_inputs leftEnvironment rightEnvironment
  intro atom member
  exact agree atom (by simpa [unary] using member)

theorem ternary_dependencies_are_sound (unit : UnitKind)
    (operation : Input → Input → Input → Output)
    (first second third : AbstractValue Atom Input)
    (leftEnvironment rightEnvironment : Atom → Input)
    (agree : ∀ atom, atom ∈ (ternary unit operation first second third).dependencies →
      leftEnvironment atom = rightEnvironment atom) :
    (ternary unit operation first second third).evaluate leftEnvironment =
      (ternary unit operation first second third).evaluate rightEnvironment := by
  have firstAgrees : ∀ atom, atom ∈ first.dependencies →
      leftEnvironment atom = rightEnvironment atom := by
    intro atom member
    exact agree atom (by simp [ternary, member])
  have secondAgrees : ∀ atom, atom ∈ second.dependencies →
      leftEnvironment atom = rightEnvironment atom := by
    intro atom member
    exact agree atom (by simp [ternary, member])
  have thirdAgrees : ∀ atom, atom ∈ third.dependencies →
      leftEnvironment atom = rightEnvironment atom := by
    intro atom member
    exact agree atom (by simp [ternary, member])
  rw [ternary_evaluation, ternary_evaluation,
    first.depends_only_on_inputs leftEnvironment rightEnvironment firstAgrees,
    second.depends_only_on_inputs leftEnvironment rightEnvironment secondAgrees,
    third.depends_only_on_inputs leftEnvironment rightEnvironment thirdAgrees]

end AbstractComputation

end ProofsLean.MNCore
