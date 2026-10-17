import Std.Tactic.BVDecide
import ProofsLean.OperatorAbstraction

/-! Executable, bit-level single precision MN-Core vector FMA model.

The significand product applies the SDM's dropped-partial-product correction;
the accumulator is aligned to the measured MAU grid with sticky jamming; the
sum is rounded once using round-to-nearest-even. This file uses only kernel
reduction over integers/naturals and bitvectors, so concrete cases can be
checked by `decide`. The gpfn3 differential harness remains an independent
implementation check. -/
namespace ProofsLean.MNCore.SingleFMA

inductive Value where
  | zero (negative : Bool)
  | infinity (negative : Bool)
  | finite (negative : Bool) (significand : Nat) (exponent : Int)
  deriving DecidableEq, Repr

def infinityBits (negative : Bool) : BitVec 32 :=
  BitVec.ofNat 32 ((if negative then 1 else 0) * 2 ^ 31 + 255 * 2 ^ 23)

def decode (bits : BitVec 32) : Value := Id.run do
  let raw := bits.toNat
  let negative := raw / 2 ^ 31 % 2 == 1
  let exponent := raw / 2 ^ 23 % 256
  let mantissa := raw % 2 ^ 23
  if exponent == 0 then return .zero negative
  if exponent == 255 then return .infinity negative
  return .finite negative (2 ^ 23 + mantissa) (Int.ofNat exponent - 127 - 23)

def topBit (n : Nat) : Nat := n.log2

def roundPack (negative : Bool) (significand : Nat) (exponent : Int) : BitVec 32 := Id.run do
  if significand == 0 then return 0
  let p := topBit significand
  let kept := if p > 23 then
    let shift := p - 23
    let truncated := significand / 2 ^ shift
    let remainder := significand % 2 ^ shift
    let halfway := 2 ^ (shift - 1)
    let increment := remainder > halfway || (remainder == halfway && truncated % 2 == 1)
    truncated + if increment then 1 else 0
  else significand * 2 ^ (23 - p)
  let carry := kept / 2 ^ 24 != 0
  let normalized := if carry then kept / 2 else kept
  let finalP := p + if carry then 1 else 0
  let biased := exponent + Int.ofNat finalP + 127
  if biased >= 255 then return infinityBits negative
  if biased <= 0 then return 0
  let sign := if negative then 2 ^ 31 else 0
  return BitVec.ofNat 32 (sign + Int.toNat biased * 2 ^ 23 + normalized % 2 ^ 23)

def encode : Value → BitVec 32
  | .zero _ => 0
  | .infinity negative => infinityBits negative
  | .finite negative significand exponent => roundPack negative significand exponent

def multiply (left right : Value) : Value :=
  let negative := match left with
    | .zero n | .infinity n | .finite n _ _ =>
      match right with
      | .zero m | .infinity m | .finite m _ _ => n != m
  match left, right with
  | .zero _, _ | _, .zero _ => .zero negative
  | .infinity _, _ | _, .infinity _ => .infinity negative
  | .finite _ a ea, .finite _ b eb =>
      let product := a * b
      let lowA := a % 32
      let lowB := b % 32
      let dropped := lowA * lowB
      let corrected := if dropped == 0 then product else product - dropped + 256
      .finite negative corrected (ea + eb)

def stickyShiftRight (value distance : Nat) : Nat :=
  if distance == 0 then value
  else if distance >= 127 then if value == 0 then 0 else 1
  else
    let quotient := value / 2 ^ distance
    let sticky := value % 2 ^ distance != 0
    if sticky && quotient % 2 == 0 then quotient + 1 else quotient

def normalize (significand : Nat) (exponent : Int) : Nat × Int :=
  let shift := 125 - topBit significand
  (significand * 2 ^ shift, exponent - Int.ofNat shift)

def add (left right : Value) : Value :=
  match left, right with
  | .infinity a, .infinity b => .infinity (a && b)
  | .infinity n, _ | _, .infinity n => .infinity n
  | .zero a, .zero b => .zero (a && b)
  | .zero _, value | value, .zero _ => value
  | .finite na sa ea, .finite nb sb eb =>
      let (sa, ea) := normalize sa ea
      let (sb, eb) := normalize sb eb
      let (nh, sh, eh, nl, sl, el) :=
        if ea >= eb then (na, sa, ea, nb, sb, eb) else (nb, sb, eb, na, sa, ea)
      let distance := Int.toNat (eh - el)
      let sl := stickyShiftRight sl distance
      if nh == nl then .finite nh (sh + sl) eh
      else if sh > sl then .finite nh (sh - sl) eh
      else if sl > sh then .finite nl (sl - sh) eh
      else .zero false

def alignAccumulator (accumulator : Value) (grid : Int) : Value :=
  match accumulator with
  | .finite negative sig exponent =>
      if exponent >= grid then accumulator
      else if Int.ofNat (topBit sig) + exponent - grid <= -2 then .zero false
      else
        let shift := Int.toNat (grid - exponent)
        let kept := if shift >= 128 then 0 else sig / 2 ^ shift
        let sticky := shift >= 128 || sig % 2 ^ shift != 0
        .finite negative (if sticky && kept % 2 == 0 then kept + 1 else kept) grid
  | _ => accumulator

def singleFma (a b c : BitVec 32) : BitVec 32 :=
  let av := decode a
  let bv := decode b
  let cv := decode c
  let aligned := match av, bv with
    | .finite _ _ ea, .finite _ _ eb => alignAccumulator cv (ea + eb + 5)
    | _, _ => cv
  encode (add (multiply av bv) aligned)

def abstractSingleFma {Atom : Type}
    (a b c : AbstractValue Atom (BitVec 32)) :
    AbstractValue Atom (BitVec 32) :=
  AbstractValue.ternary .floatingMau singleFma a b c

theorem abstractSingleFma_evaluation {Atom : Type}
    (a b c : AbstractValue Atom (BitVec 32))
    (environment : Atom → BitVec 32) :
    (abstractSingleFma a b c).evaluate environment =
      singleFma (a.evaluate environment) (b.evaluate environment)
        (c.evaluate environment) := by
  exact AbstractValue.ternary_evaluation .floatingMau singleFma a b c environment

theorem sdm_dropped_partial_product_example :
    singleFma 0x49800008 0x49800008 0xD3800000 = 0x4A000010 := by decide

theorem one_fma_one : singleFma 0x3F800000 0x3F800000 0 = 0x3F800000 := by decide

theorem cancellation_is_positive_zero :
    singleFma 0xBF800000 0x3F800000 0x3F800000 = 0 := by decide

theorem overflow_to_infinity :
    singleFma 0x7F7FFFFF 0x40000000 0 = 0x7F800000 := by decide

theorem ties_round_to_even :
    singleFma 0x3F800000 0x3F800000 0x33800000 = 0x3F800000 := by decide

theorem ties_round_up_to_odd :
    singleFma 0x3F800000 0x3F800000 0x33C00000 = 0x3F800001 := by decide

end ProofsLean.MNCore.SingleFMA
