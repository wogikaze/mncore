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

inductive FloatPrecision where
  | half | single | double
  deriving DecidableEq, Repr

/-- Native floating RRN formats. Half precision is excluded because the Rust
block model aliases half `fadd` through single-precision extension/rounding. -/
inductive NativeFloatPrecision where
  | single | double
  deriving DecidableEq, Repr

def NativeFloatPrecision.format : NativeFloatPrecision → FloatPrecision
  | .single => .single
  | .double => .double

def FloatPrecision.exponentBits : FloatPrecision → Nat
  | .half => 6
  | .single => 8
  | .double => 11

def FloatPrecision.mantissaBits : FloatPrecision → Nat
  | .half => 9
  | .single => 23
  | .double => 52

def FloatPrecision.width (precision : FloatPrecision) : Nat :=
  1 + precision.exponentBits + precision.mantissaBits

def FloatPrecision.exponentMax (precision : FloatPrecision) : Nat :=
  2 ^ precision.exponentBits - 1

def FloatPrecision.bias (precision : FloatPrecision) : Nat :=
  2 ^ (precision.exponentBits - 1) - 1

/-- Round an unsigned significand right by `shift`, using round-to-nearest-even.
The `shift ≥ 128` case matches the Rust u128 helper. -/
def roundShift (value shift : Nat) : Nat :=
  if shift == 0 then value
  else if shift >= 128 then 0
  else
    let quotient := value / 2 ^ shift
    let remainder := value % 2 ^ shift
    let halfway := 2 ^ (shift - 1)
    quotient + if halfway < remainder || (remainder == halfway && quotient % 2 == 1)
      then 1 else 0

def floatExponent (precision : FloatPrecision) (bits : Nat) : Nat :=
  bits / 2 ^ precision.mantissaBits % 2 ^ precision.exponentBits

def floatSignificand (precision : FloatPrecision) (bits : Nat) : Nat :=
  (2 ^ precision.mantissaBits + bits % 2 ^ precision.mantissaBits) * 8

def floatIsNegative (precision : FloatPrecision) (bits : Nat) : Bool :=
  bits / 2 ^ (precision.width - 1) % 2 == 1

def maxFloatExponent (precision : FloatPrecision) (values : List Nat) : Nat :=
  (values.map (floatExponent precision)).foldl Nat.max 0

/-- Signed, exponent-aligned RRN significand sum before final format rounding. -/
def floatAlignedSum (precision : FloatPrecision) (values : List Nat) : Int :=
  let maxExponent := maxFloatExponent precision values
  values.foldl (fun sum bits =>
    let exponent := floatExponent precision bits
    if exponent == 0 then sum
    else
      let aligned := roundShift (floatSignificand precision bits) (maxExponent - exponent)
      if floatIsNegative precision bits then sum - Int.ofNat aligned
      else sum + Int.ofNat aligned) 0

def roundPack (precision : FloatPrecision) (negative : Bool)
    (significand : Nat) (exponent : Int) : Nat :=
  if significand == 0 then 0
  else
    let topBit := Nat.log2 significand
    let mantissaBits := precision.mantissaBits
    let (kept, normalizedTop) := if topBit > mantissaBits then
      let rounded := roundShift significand (topBit - mantissaBits)
      if rounded >= 2 ^ (mantissaBits + 1) then (rounded / 2, topBit + 1)
      else (rounded, topBit)
    else (significand * 2 ^ (mantissaBits - topBit), topBit)
    let biased := exponent + Int.ofNat normalizedTop + Int.ofNat precision.bias
    if biased >= Int.ofNat precision.exponentMax then
      (if negative then 1 else 0) * 2 ^ (precision.width - 1) +
        precision.exponentMax * 2 ^ mantissaBits
    else if biased <= 0 then 0
    else
      (if negative then 1 else 0) * 2 ^ (precision.width - 1) +
        biased.toNat * 2 ^ mantissaBits + kept % 2 ^ mantissaBits

def floatInfinity (precision : FloatPrecision) (negative : Bool) : Nat :=
  (if negative then 1 else 0) * 2 ^ (precision.width - 1) +
    precision.exponentMax * 2 ^ precision.mantissaBits

/-- RRN floating addition for the finite formats implemented by `rrn::fadd`.
Exponent-zero operands are ignored, infinities follow the emulator's sign rule,
and finite sums are rounded once into the requested output format. -/
def reduceFloatAdd (input output : FloatPrecision) (values : List Nat) : Nat :=
  let maxExponent := maxFloatExponent input values
  if maxExponent == 0 then 0
  else if maxExponent == input.exponentMax then
    floatInfinity output (values.all fun bits =>
      floatExponent input bits != input.exponentMax || floatIsNegative input bits)
  else
    let sum := floatAlignedSum input values
    if sum == 0 then 0
    else
      let exponent := Int.ofNat maxExponent - Int.ofNat input.bias -
        Int.ofNat input.mantissaBits - 3
      roundPack output (sum < 0) sum.natAbs exponent

def extendFloatBits (input output : FloatPrecision) (bits : Nat) : Nat :=
  let exponent := floatExponent input bits
  let negative := floatIsNegative input bits
  if exponent == 0 then 0
  else if exponent == input.exponentMax then floatInfinity output negative
  else
    let significand := 2 ^ input.mantissaBits + bits % 2 ^ input.mantissaBits
    let binaryExponent := Int.ofNat exponent - Int.ofNat input.bias -
      Int.ofNat input.mantissaBits
    roundPack output negative significand binaryExponent

/-- Reduce each native floating lane independently, including direct half
precision RRN operations used by MV. -/
def reduceLongFloatAddFormat (format : FloatPrecision)
    (values : List (BitVec 64)) : BitVec 64 :=
  let width := format.width
  let laneValues := (List.range (64 / width)).map fun lane =>
    let shift := 64 - width * (lane + 1)
    let inputs := values.map fun value =>
      (value.extractLsb' shift width).toNat
    reduceFloatAdd format format inputs * 2 ^ shift
  BitVec.ofNat 64 (laneValues.foldl (· + ·) 0)

/-- Reduce each native single/double lane independently across L1BM words. -/
def reduceLongFloatAdd (precision : NativeFloatPrecision)
    (values : List (BitVec 64)) : BitVec 64 :=
  reduceLongFloatAddFormat precision.format values

/-- Half alias path: widen each half lane to single, reduce in the single
network, round each result to half, and pack four halves. The 16-MAB case
first reduces each group of four to single precision. -/
def reduceHalfAliasLongWord (fourMabs : Bool) (values : List (BitVec 64)) : BitVec 64 :=
  let laneResults := (List.range 4).map fun lane =>
    let halfInputs := values.map fun word =>
      word.toNat / 2 ^ ((3 - lane) * 16) % 2 ^ 16
    let singleInputs := halfInputs.map (extendFloatBits .half .single)
    let result := if fourMabs then
      reduceFloatAdd .single .half singleInputs
    else
      let stage := (List.range 4).map fun group =>
        reduceFloatAdd .single .single ((singleInputs.drop (group * 4)).take 4)
      reduceFloatAdd .single .half stage
    result * 2 ^ (48 - lane * 16)
  BitVec.ofNat 64 (laneResults.foldl (· + ·) 0)

/-- Explicit output-rounding path for native single/double input. `values`
contains each MAB's two source long words; `sourceTwoWords` determines whether
the second word contributes. Missing output lanes are packed as zero, matching
the emulator's zero-filled result bus. -/
def reduceRoundedLongFloat (fourMabs sourceTwoWords : Bool)
    (precision : NativeFloatPrecision)
    (values : List (BitVec 64 × BitVec 64)) : BitVec 64 :=
  let format := precision.format
  let width := format.width
  let lanesPerWord := 64 / width
  let activeLanes := lanesPerWord * (if sourceTwoWords then 2 else 1)
  let laneResults := (List.range 4).map fun lane =>
    let inputs := if lane < activeLanes then
      values.map fun words =>
        let word := if lane < lanesPerWord then words.1 else words.2
        (word.extractLsb' ((lanesPerWord - 1 - lane % lanesPerWord) * width) width).toNat
    else []
    let result := if fourMabs then reduceFloatAdd format .half inputs
      else
        let stage := (List.range 4).map fun group =>
          reduceFloatAdd format format ((inputs.drop (group * 4)).take 4)
        reduceFloatAdd format .half stage
    result * 2 ^ (48 - lane * 16)
  BitVec.ofNat 64 (laneResults.foldl (· + ·) 0)

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
    let shift := 64 - width * (lane + 1)
    let inputs := values.map fun value => value.extractLsb' shift width
    (reduceInteger op inputs).toNat * 2 ^ shift
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

theorem round_shift_tie_to_even_down : roundShift 10 2 = 2 := by decide

theorem round_shift_tie_to_even_up : roundShift 14 2 = 4 := by decide

theorem round_shift_tie_odd_quotient_up : roundShift 22 2 = 6 := by decide

theorem round_shift_u128_overflow_distance_is_zero : roundShift (2 ^ 128 - 1) 128 = 0 := by decide

theorem single_precision_one_plus_two_aligned_sum :
    floatAlignedSum .single [0x3f800000, 0x40000000] = 3 * 2 ^ 25 := by decide

theorem single_precision_opposites_cancel_before_rounding :
    floatAlignedSum .single [0x3f800000, 0xbf800000] = 0 := by decide

theorem single_round_pack_one :
    roundPack .single false (2 ^ 26) (-26) = 0x3f800000 := by decide

theorem single_rrn_one_plus_two_is_three :
    reduceFloatAdd .single .single [0x3f800000, 0x40000000] = 0x40400000 := by decide

theorem single_rrn_opposites_cancel_to_positive_zero :
    reduceFloatAdd .single .single [0x3f800000, 0xbf800000] = 0 := by decide

theorem single_rrn_infinity_sign_matches_all_infinities :
    reduceFloatAdd .single .single [0x7f800000, 0xff800000] = 0x7f800000 := by decide

theorem single_longword_rrn_reduces_each_lane :
    reduceLongFloatAdd .single
      [BitVec.ofNat 64 0x3f8000003f800000, BitVec.ofNat 64 0x4000000040000000] =
      BitVec.ofNat 64 0x4040000040400000 := by decide

theorem half_one_extends_exactly_to_single_one :
    extendFloatBits .half .single 0x3e00 = 0x3f800000 := by decide

theorem negative_half_infinity_extends_with_sign :
    extendFloatBits .half .single 0xfe00 = 0xff800000 := by decide

theorem half_alias_four_mab_sum_rounds_and_packs :
    reduceHalfAliasLongWord true
      (List.replicate 4 (BitVec.ofNat 64 0x3e003e003e003e00)) =
      BitVec.ofNat 64 0x4200420042004200 := by decide

theorem half_alias_sixteen_mab_uses_two_stages :
    reduceHalfAliasLongWord false
      (List.replicate 16 (BitVec.ofNat 64 0x3e003e003e003e00)) =
      BitVec.ofNat 64 0x4600460046004600 := by decide

theorem half_alias_preserves_half_lane_order :
    reduceHalfAliasLongWord true
      (List.replicate 4 (BitVec.ofNat 64 0x3e00400041004200)) =
      BitVec.ofNat 64 0x4200440045004600 := by decide

theorem rounded_single_word_keeps_msb_lanes_first :
    reduceRoundedLongFloat true false .single
      [(BitVec.ofNat 64 0x3f80000040000000, 0)] =
      BitVec.ofNat 64 0x3e00400000000000 := by decide

end ProofsLean.MNCore.RRN
