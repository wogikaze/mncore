import Std

/- Integer operations of the result reduction network in `viz/core/src/rrn.rs`.
Floating-point RRN addition is specified separately because it uses the MN-Core
rounding datapath rather than host or Lean floating-point arithmetic. -/
namespace ProofsLean.MNCore.RRN

inductive IntegerOp where
  | maximum | minimum | add | bitAnd | bitOr | allNonzero | anyNonzero
  deriving DecidableEq, Repr

inductive IntegerPrecision where
  | half | word | long
  deriving DecidableEq, Repr

def IntegerPrecision.width : IntegerPrecision → Nat
  | .half => 16
  | .word => 32
  | .long => 64

def IntegerPrecision.lanes (precision : IntegerPrecision) : Nat :=
  64 / precision.width

def signMagnitudeKey (value : BitVec width) : Int :=
  let signPlace := 2 ^ (width - 1)
  let magnitude := value.toNat % signPlace
  if value.toNat / signPlace == 1 then
    -(Int.ofNat magnitude) - 1
  else Int.ofNat magnitude

def extreme (takeMaximum : Bool) (values : List (BitVec width)) : BitVec width :=
  match values with
  | [] => 0
  | first :: rest =>
      rest.foldl (fun best value =>
        let better := if takeMaximum
          then signMagnitudeKey best < signMagnitudeKey value
          else signMagnitudeKey value < signMagnitudeKey best
        if better then value else best) first

/-- Exact integer RRN stage for the operations implemented by Rust `reduce`.
Inputs are lane elements of one precision, already extracted from the buses. -/
def reduceInteger (op : IntegerOp) (values : List (BitVec width)) : BitVec width :=
  match op with
  | .maximum => extreme true values
  | .minimum => extreme false values
  | .add => values.foldl (fun acc value => acc + value) 0
  | .bitAnd => values.foldl BitVec.and (BitVec.ofNat width (2 ^ width - 1))
  | .bitOr => values.foldl BitVec.or 0
  | .allNonzero => BitVec.ofNat width (if values.all (fun value => value != 0) then 1 else 0)
  | .anyNonzero => BitVec.ofNat width (if values.any (fun value => value != 0) then 1 else 0)

/-- Reduce each precision lane independently across the supplied L1BM words,
then reassemble the 64-bit long word. -/
def reduceLongInteger (op : IntegerOp) (precision : IntegerPrecision)
    (values : List (BitVec 64)) : BitVec 64 :=
  let width := precision.width
  let laneValues := (List.range precision.lanes).map fun lane =>
    let inputs := values.map fun value => value.extractLsb' (lane * width) width
    (reduceInteger op inputs).toNat * 2 ^ (lane * width)
  BitVec.ofNat 64 (laneValues.foldl (· + ·) 0)

theorem add_wraps_8bit :
    reduceInteger .add [BitVec.ofNat 8 250, BitVec.ofNat 8 10] = BitVec.ofNat 8 4 := by decide

theorem bitwise_and_8bit :
    reduceInteger .bitAnd [BitVec.ofNat 8 15, BitVec.ofNat 8 6] = BitVec.ofNat 8 6 := by decide

theorem bitwise_or_8bit :
    reduceInteger .bitOr [BitVec.ofNat 8 8, BitVec.ofNat 8 3] = BitVec.ofNat 8 11 := by decide

theorem sign_magnitude_max_orders_negative_below_positive :
    signMagnitudeKey (BitVec.ofNat 8 129) < signMagnitudeKey (BitVec.ofNat 8 1) := by decide

theorem max_prefers_positive_zero_over_negative_zero :
    reduceInteger .maximum [BitVec.ofNat 8 128, BitVec.ofNat 8 0] = BitVec.ofNat 8 0 := by decide

theorem min_prefers_negative_zero_over_positive_zero :
    reduceInteger .minimum [BitVec.ofNat 8 0, BitVec.ofNat 8 128] = BitVec.ofNat 8 128 := by decide

theorem all_nonzero_is_logical :
    reduceInteger .allNonzero [BitVec.ofNat 8 7, BitVec.ofNat 8 2] = BitVec.ofNat 8 1 := by decide

theorem any_nonzero_is_logical :
    reduceInteger .anyNonzero [BitVec.ofNat 8 0, BitVec.ofNat 8 2] = BitVec.ofNat 8 1 := by decide

theorem half_precision_reduction_is_lane_wise :
    reduceLongInteger .add .half
      [BitVec.ofNat 64 0x0001000200030004, BitVec.ofNat 64 0x0005000600070008] =
      BitVec.ofNat 64 0x00060008000a000c := by decide

end ProofsLean.MNCore.RRN
