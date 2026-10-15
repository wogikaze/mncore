import ProofsLean.PartialSemantics

/- MN-Core 2 manual (2026-06-02), §3.6.12 and tables 3.9–3.11.
This is an ALU datapath fragment, not a machine step or an exhaustive ISA.
Operands here have already been read and precision-reduced. Memory accesses,
mask application, forwarding, parallel issue and legality remain outside it. -/
namespace ProofsLean.MNCore.IntegerALU

inductive Precision where
  | long | word | half
  deriving DecidableEq, Repr

def Precision.width : Precision → Nat
  | .long => 64
  | .word => 32
  | .half => 16

def Precision.lanes : Precision → Nat
  | .long => 1
  | .word => 2
  | .half => 4

inductive Arithmetic where
  | inc | dec | add | sub
  deriving DecidableEq, Repr

structure LaneResult (width : Nat) where
  value : BitVec width
  flag : Bool
  deriving DecidableEq, Repr

/-- Unsigned arithmetic flags detect carry/borrow; signed flags test the wrapped
output sign, NOT signed-overflow detection. -/
def arithmetic (op : Arithmetic) (unsigned : Bool) (x y : BitVec w) : LaneResult w :=
  let value := match op with
    | .inc => x + 1
    | .dec => x - 1
    | .add => x + y
    | .sub => x - y
  let noOverflow := match op with
    | .inc => decide (x.toNat + 1 < 2 ^ w)
    | .dec => decide (1 ≤ x.toNat)
    | .add => decide (x.toNat + y.toNat < 2 ^ w)
    | .sub => decide (y.toNat ≤ x.toNat)
  ⟨value, if unsigned then noOverflow else !value.msb⟩

inductive Shift where
  | left | right (unsigned : Bool) | rotateLeft | rotateRight
  deriving DecidableEq, Repr

/-- The manual first discards shift-count bits above log2(2*width).
Logical/arithmetic shifts saturate at width; rotations wrap at width. -/
def shift (op : Shift) (x y : BitVec w) : LaneResult w :=
  let count := y.toNat % (2 * w)
  let value := match op with
    | .left => x <<< min count w
    | .right true => x >>> min count w
    | .right false => x.sshiftRight (min count w)
    | .rotateLeft => x.rotateLeft count
    | .rotateRight => x.rotateRight count
  ⟨value, decide (value = 0)⟩

inductive Op where
  | arith (op : Arithmetic) (unsigned : Bool)
  | bitNot | logicalNot | bitAnd | bitOr | bitXor
  | maximum (unsigned : Bool) | minimum (unsigned : Bool)
  | shift (op : Shift) | packbit
  | passa
  deriving DecidableEq, Repr

def evaluateLane (op : Op) (x y : BitVec w) : LaneResult w :=
  match op with
  | .arith a u => arithmetic a u x y
  | .shift s => shift s x y
  | .packbit => ⟨(x <<< 1) ||| (if y.msb then 1 else 0), !y.msb⟩
  | .bitNot => let value := ~~~x; ⟨value, decide (value = 0)⟩
  | .logicalNot => let value := if x = 0 then 1 else 0; ⟨value, decide (value = 0)⟩
  | .bitAnd => let value := x &&& y; ⟨value, decide (value = 0)⟩
  | .bitOr => let value := x ||| y; ⟨value, decide (value = 0)⟩
  | .bitXor => let value := x ^^^ y; ⟨value, decide (value = 0)⟩
  | .maximum unsigned =>
    let selectX := if unsigned then decide (y.toNat ≤ x.toNat) else decide (y.toInt ≤ x.toInt)
    ⟨if selectX then x else y, selectX⟩
  | .minimum unsigned =>
    let selectX := if unsigned then decide (x.toNat ≤ y.toNat) else decide (x.toInt ≤ y.toInt)
    ⟨if selectX then x else y, selectX⟩
  | .passa => ⟨x, decide (x = 0)⟩

structure Bus where
  high : BitVec 64
  low : BitVec 64
  deriving DecidableEq, Repr

structure BusResult where
  value : Bus
  /-- Index 0 is the least significant mask bit / half-word. -/
  flags : Fin 4 → Bool

/-- Lane indices run from LSB to MSB within the MSB long-word. -/
def lane (p : Precision) (x : Bus) (index : Nat) : BitVec p.width :=
  x.high.extractLsb' (index * p.width) p.width

/-- This input is the bus AFTER operand precision reduction. The caller must
implement that conversion; merely setting this parameter does not convert x. -/
def evaluateBus (p : Precision) (op : Op) (x y : Bus)
    (firstOperandWasReduced : Bool) : BusResult :=
  let result := fun index => evaluateLane op (lane p x index) (lane p y index)
  let high := (List.range p.lanes).foldl (fun acc index =>
    acc ||| ((result index).value.setWidth 64 <<< (index * p.width))) 0
  let low := if op = .passa then x.low else if firstOperandWasReduced then 0 else x.low
  ⟨⟨high, low⟩, fun bit => (result (bit.val / (4 / p.lanes))).flag⟩

/-- Unsupported instructions remain unknown, never failed/rejected candidates. -/
inductive Request where
  | integer (p : Precision) (op : Op)
  | unimplemented (encoding : Nat)

def partialEvaluate (request : Request) (x y : Bus) (reduced : Bool) : StepResult BusResult :=
  match request with
  | .integer p op => .ok (evaluateBus p op x y reduced)
  | .unimplemented _ => .unknown

theorem unsupported_is_unknown (encoding : Nat) (x y : Bus) (reduced : Bool) :
    partialEvaluate (.unimplemented encoding) x y reduced = .unknown := rfl

theorem signedness_preserves_arithmetic_bits (op : Arithmetic) (x y : BitVec w) :
    (arithmetic op true x y).value = (arithmetic op false x y).value := by
  cases op <;> rfl

theorem addition_wraps (unsigned : Bool) (x y : BitVec w) :
    (arithmetic .add unsigned x y).value.toNat = (x.toNat + y.toNat) % 2 ^ w := rfl

theorem unsigned_sub_flag (x y : BitVec w) :
    (arithmetic .sub true x y).flag = decide (y.toNat ≤ x.toNat) := rfl

theorem signed_add_flag (x y : BitVec w) :
    (arithmetic .add false x y).flag = !(x + y).msb := rfl

theorem shift_ignores_high_count_bits (op : Shift) (x y z : BitVec w)
    (sameLowBits : y.toNat % (2 * w) = z.toNat % (2 * w)) :
    shift op x y = shift op x z := by
  simp only [shift, sameLowBits]

theorem large_logical_left_is_zero (x y : BitVec w)
    (large : w ≤ y.toNat % (2 * w)) :
    (shift .left x y).value = 0 := by
  simp [shift, Nat.min_eq_right large]

theorem packbit_flag (x y : BitVec w) :
    (evaluateLane .packbit x y).flag = !y.msb := rfl

theorem max_tie_selects_first (unsigned : Bool) (x : BitVec w) :
    evaluateLane (.maximum unsigned) x x = ⟨x, true⟩ := by
  cases unsigned <;> simp [evaluateLane]

theorem min_tie_selects_first (unsigned : Bool) (x : BitVec w) :
    evaluateLane (.minimum unsigned) x x = ⟨x, true⟩ := by
  cases unsigned <;> simp [evaluateLane]

theorem ordinary_lsb_passthrough (p : Precision) (op : Op) (x y : Bus)
    (notPassa : op ≠ .passa) :
    (evaluateBus p op x y false).value.low = x.low := by
  simp [evaluateBus, notPassa]

theorem reduced_lsb_zero (p : Precision) (op : Op) (x y : Bus)
    (notPassa : op ≠ .passa) :
    (evaluateBus p op x y true).value.low = 0 := by
  simp [evaluateBus, notPassa]

theorem passa_copies_lsb (p : Precision) (x y : Bus) (reduced : Bool) :
    (evaluateBus p .passa x y reduced).value.low = x.low := by
  simp [evaluateBus]

theorem long_flag_replicated (op : Op) (x y : Bus) (reduced : Bool) (bit : Fin 4) :
    (evaluateBus .long op x y reduced).flags bit =
      (evaluateBus .long op x y reduced).flags 0 := by
  simp [evaluateBus, Precision.lanes, Nat.div_eq_of_lt bit.isLt]

theorem word_flags_replicated (op : Op) (x y : Bus) (reduced : Bool) :
    (evaluateBus .word op x y reduced).flags 0 =
      (evaluateBus .word op x y reduced).flags 1 ∧
    (evaluateBus .word op x y reduced).flags 2 =
      (evaluateBus .word op x y reduced).flags 3 := ⟨rfl, rfl⟩

/- Concrete edge checks are kernel reductions. They test this fragment; they
are not evidence of completeness or correspondence with the reference binary. -/
example : arithmetic .inc true (65535#16) 0 = ⟨0, false⟩ := by decide
example : arithmetic .inc false (65535#16) 0 = ⟨0, true⟩ := by decide
example : arithmetic .dec true (0#32) 0 = ⟨4294967295, false⟩ := by decide
example : arithmetic .inc false (9223372036854775807#64) 0 =
    ⟨9223372036854775808, false⟩ := by decide
example : arithmetic .inc true (9223372036854775807#64) 0 =
    ⟨9223372036854775808, true⟩ := by decide
example : evaluateLane (.maximum false) (65535#16) 1 = ⟨1, false⟩ := by decide
example : evaluateLane (.maximum true) (65535#16) 1 = ⟨65535, true⟩ := by decide
example : (evaluateLane .logicalNot (0#16) 0).flag = false := by decide
example : (evaluateLane .logicalNot (1#16) 0).flag = true := by decide
example : shift .left (1#16) 16 = ⟨0, true⟩ := by decide
example : shift .left (1#16) 32 = ⟨1, false⟩ := by decide
example : shift (.right false) (32768#16) 31 = ⟨65535, false⟩ := by decide
example : shift (.right true) (32768#16) 31 = ⟨0, true⟩ := by decide
example : shift .rotateLeft (32768#16) 17 = ⟨1, false⟩ := by decide
example : evaluateLane .packbit (32768#16) 32768 = ⟨1, false⟩ := by decide
example : (evaluateBus .half (.arith .inc false)
    ⟨0x0000ffff7fff8000, 0x0123456789abcdef⟩ ⟨0, 0⟩ false).value.high =
      0x0001000080008001 := by decide
example : (evaluateBus .half (.arith .inc false)
    ⟨0x0000ffff7fff8000, 0⟩ ⟨0, 0⟩ false).flags 0 = false ∧
    (evaluateBus .half (.arith .inc false)
    ⟨0x0000ffff7fff8000, 0⟩ ⟨0, 0⟩ false).flags 3 = true := by decide

end ProofsLean.MNCore.IntegerALU
