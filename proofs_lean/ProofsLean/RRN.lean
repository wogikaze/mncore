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

def FloatPrecision.mauMulFullBits : FloatPrecision → Option Nat
  | .half => none
  | .single => some 18
  | .double => some 36

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

/-! ### Block-float input validation

The matrix MAU consumes block-float encodings. Every element normally shares
the block's maximum exponent. Half precision additionally permits exponent
zero as the extended representation used by `bfe`; this mirrors the emulator's
`check_bf` rule and deliberately leaves mantissa/sign bits untouched. -/

def blockFloatCommonExponent (precision : FloatPrecision) (values : List Nat) : Nat :=
  maxFloatExponent precision values

def blockFloatExponentValid (precision : FloatPrecision) (values : List Nat) : Bool :=
  let common := blockFloatCommonExponent precision values
  values.all fun bits =>
    let exponent := floatExponent precision bits
    exponent == common || (precision == .half && exponent == 0)

theorem blockFloatExponentValid_empty (precision : FloatPrecision) :
    blockFloatExponentValid precision [] = true := by
  simp [blockFloatExponentValid]

theorem blockFloatExponentValid_single (precision : FloatPrecision) (bits : Nat) :
    blockFloatExponentValid precision [bits] = true := by
  simp [blockFloatExponentValid, blockFloatCommonExponent, maxFloatExponent,
    floatExponent]

theorem blockFloatExponentValid_half_zero_exponent_is_allowed (bits : Nat)
    (zeroExponent : floatExponent .half bits = 0) :
    blockFloatExponentValid .half [bits, 0] = true := by
  simp [blockFloatExponentValid, blockFloatCommonExponent, maxFloatExponent,
    zeroExponent]

theorem blockFloatExponentValid_rejects_mismatched_single_exponents
    (left right : Nat) (leftExponent rightExponent : Nat)
    (leftExp : floatExponent .single left = leftExponent)
    (rightExp : floatExponent .single right = rightExponent)
    (different : leftExponent ≠ rightExponent) :
    blockFloatExponentValid .single [left, right] = false := by
  simp [blockFloatExponentValid, blockFloatCommonExponent, maxFloatExponent,
    leftExp, rightExp]
  omega

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

/-! ### Vector MAU fused multiply-add -/

inductive MAUValue where
  | zero (negative : Bool)
  | infinity (negative : Bool)
  | finite (negative : Bool) (significand : Nat) (exponent : Int)
  deriving DecidableEq, Repr

def decodeMAUValue (precision : FloatPrecision) (bits : Nat) : MAUValue :=
  let exponent := floatExponent precision bits
  let negative := floatIsNegative precision bits
  if exponent == 0 then .zero negative
  else if exponent == precision.exponentMax then .infinity negative
  else .finite negative
    (2 ^ precision.mantissaBits + bits % 2 ^ precision.mantissaBits)
    (Int.ofNat exponent - Int.ofNat precision.bias - Int.ofNat precision.mantissaBits)

def encodeMAUValue (precision : FloatPrecision) : MAUValue → Nat
  | .zero _ => 0
  | .infinity negative => floatInfinity precision negative
  | .finite negative significand exponent =>
      roundPack precision negative significand exponent

def multiplyMAUValues (precision : FloatPrecision) (left right : MAUValue) : MAUValue :=
  let negative := match left, right with
    | .zero leftNeg, .zero rightNeg => leftNeg != rightNeg
    | .zero leftNeg, .infinity rightNeg => leftNeg != rightNeg
    | .zero leftNeg, .finite rightNeg .. => leftNeg != rightNeg
    | .infinity leftNeg, .zero rightNeg => leftNeg != rightNeg
    | .infinity leftNeg, .infinity rightNeg => leftNeg != rightNeg
    | .infinity leftNeg, .finite rightNeg .. => leftNeg != rightNeg
    | .finite leftNeg .., .zero rightNeg => leftNeg != rightNeg
    | .finite leftNeg .., .infinity rightNeg => leftNeg != rightNeg
    | .finite leftNeg .., .finite rightNeg .. => leftNeg != rightNeg
  match left, right with
  | .zero _, _ | _, .zero _ => .zero negative
  | .infinity _, _ | _, .infinity _ => .infinity negative
  | .finite _ leftSig leftExp, .finite _ rightSig rightExp =>
      let rawProduct := leftSig * rightSig
      let product := match precision.mauMulFullBits with
        | none => rawProduct
        | some full =>
            let lowBits := precision.mantissaBits - full
            let lowMask := 2 ^ lowBits - 1
            let dropped := (leftSig % 2 ^ lowBits) * (rightSig % 2 ^ lowBits)
            if dropped == 0 then rawProduct
            else rawProduct - dropped + 2 ^ (2 * lowBits - 2)
      .finite negative product (leftExp + rightExp)

def alignMAUAccumulator (value : MAUValue) (grid : Int) : MAUValue :=
  match value with
  | .finite negative significand exponent =>
      if exponent >= grid then value else
        let lead := exponent + Int.ofNat (Nat.log2 significand)
        if lead - grid <= -2 then .zero false else
          let shift := (grid - exponent).toNat
          let kept := if shift >= 128 then 0 else significand / 2 ^ shift
          let sticky := shift >= 128 || significand % 2 ^ shift != 0
          .finite negative (kept + if sticky && kept % 2 == 0 then 1 else 0) grid
  | _ => value

theorem alignMAUAccumulator_sticky_jams_into_odd_lsb :
    alignMAUAccumulator (.finite false 7 0) 1 = .finite false 3 1 := by
  decide

def addMAUValues : MAUValue → MAUValue → MAUValue
  | .infinity negativeA, .infinity negativeB => .infinity (negativeA && negativeB)
  | .infinity negative, _ | _, .infinity negative => .infinity negative
  | .zero negativeA, .zero negativeB => .zero (negativeA && negativeB)
  | .zero _, value | value, .zero _ => value
  | .finite negativeA sigA expA, .finite negativeB sigB expB => Id.run do
      let top : Nat := 125
      let normalize (significand : Nat) (exponent : Int) :=
        let p := Nat.log2 significand
        (significand * 2 ^ (top - p), exponent - Int.ofNat (top - p))
      let (sigA, expA) := normalize sigA expA
      let (sigB, expB) := normalize sigB expB
      let (negativeHigh, sigHigh, expHigh, sigLow, expLow) :=
        if expA >= expB then (negativeA, sigA, expA, sigB, expB)
        else (negativeB, sigB, expB, sigA, expA)
      let distance := (expHigh - expLow).toNat
      let shiftedLow := if distance == 0 then sigLow
        else if distance >= 127 then if sigLow == 0 then 0 else 1
        else
          let kept := sigLow / 2 ^ distance
          let sticky := sigLow % 2 ^ distance != 0
          kept + if sticky && kept % 2 == 0 then 1 else 0
      if negativeA == negativeB then
        return .finite negativeHigh (sigHigh + shiftedLow) expHigh
      else if sigHigh > shiftedLow then
        return .finite negativeHigh (sigHigh - shiftedLow) expHigh
      else if shiftedLow > sigHigh then
        return .finite (!negativeHigh) (shiftedLow - sigHigh) expHigh
      else return .zero false

theorem addMAUValues_sticky_jams_into_odd_lsb :
    addMAUValues (.finite false (2 ^ 125) 1)
      (.finite false (2 ^ 125 + 3) 0) =
      .finite false (2 ^ 125 + 2 ^ 124 + 1) 1 := by
  decide

def vectorMAUFma (inputPrecision accumulatorPrecision outputPrecision : FloatPrecision)
    (left right accumulator : Nat) : Nat :=
  let leftValue := decodeMAUValue inputPrecision left
  let rightValue := decodeMAUValue inputPrecision right
  let accumulatorValue := decodeMAUValue accumulatorPrecision accumulator
  let alignedAccumulator := match leftValue, rightValue with
    | .finite _ _ leftExp, .finite _ _ rightExp =>
        let mantissa := Int.ofNat inputPrecision.mantissaBits
        let full := Int.ofNat (inputPrecision.mauMulFullBits.getD inputPrecision.mantissaBits)
        alignMAUAccumulator accumulatorValue
          (leftExp + rightExp + mantissa - full)
    | _, _ => accumulatorValue
  encodeMAUValue outputPrecision
    (addMAUValues (multiplyMAUValues inputPrecision leftValue rightValue)
      alignedAccumulator)

theorem vectorMAUFma_half_one_plus_one_rounds_to_two :
    vectorMAUFma .half .single .half 0x3e00 0x3e00 0x3f800000 = 0x4000 := by
  decide

/-! ### Matrix block-float dot products

The matrix MAU keeps the dot-product accumulator unrounded until it is added
to the optional FMA accumulator. The representation below follows Rust
`float::bf_dot`: block mantissas are truncated to the selected BF width, each
product carries its exact binary exponent, and the returned grid is used to
align the accumulator before the final output rounding. -/

abbrev MAUDotTerm := Bool × Nat × Int

def decodeBlockFloatLane (precision : FloatPrecision) (keptBits : Nat)
    (bits : Nat) : Bool × Nat × Nat :=
  (floatIsNegative precision bits,
    floatExponent precision bits,
    bits % 2 ^ precision.mantissaBits / 2 ^ (precision.mantissaBits - keptBits))

def blockFloatProductTerms (precision : FloatPrecision) (keptBits commonA commonB : Nat)
    (left right : List Nat) : List MAUDotTerm := Id.run do
  let mut terms := []
  for (x, y) in left.zip right do
    let (negativeA, exponentA, mantissaA) := decodeBlockFloatLane precision keptBits x
    let (negativeB, exponentB, mantissaB) := decodeBlockFloatLane precision keptBits y
    if mantissaA != 0 && mantissaB != 0 then
      let exponentA := if exponentA == 0 then commonA - min commonA 6 else exponentA
      let exponentB := if exponentB == 0 then commonB - min commonB 6 else exponentB
      let mut product := mantissaA * mantissaB
      match precision.mauMulFullBits with
      | some full =>
          if keptBits == precision.mantissaBits then
            let lowBits := precision.mantissaBits - full
            let dropped := (mantissaA % 2 ^ lowBits) * (mantissaB % 2 ^ lowBits)
            if dropped != 0 then
              product := product - dropped + 2 ^ (2 * lowBits - 2)
      | none => pure ()
      let exponent := Int.ofNat exponentA + Int.ofNat exponentB -
        2 * Int.ofNat precision.bias - 2 * Int.ofNat (keptBits - 1)
      terms := terms ++ [(negativeA != negativeB, product, exponent)]
  return terms

def blockFloatDotGrid (precision : FloatPrecision) (keptBits commonA commonB : Nat) : Int :=
  let low := match precision.mauMulFullBits with
    | some full => if keptBits == precision.mantissaBits then full + keptBits
        else 2 * keptBits
    | none => 2 * keptBits
  Int.ofNat commonA + Int.ofNat commonB - 2 * Int.ofNat precision.bias + 2 -
    Int.ofNat low

def matrixBlockFloatDot (precision : FloatPrecision) (keptBits : Nat)
    (left right : List Nat) : MAUValue × Option Int := Id.run do
  let commonA := maxFloatExponent precision left
  let commonB := maxFloatExponent precision right
  if commonA == 0 || commonB == 0 then
    return (.zero false, none)
  if commonA == precision.exponentMax || commonB == precision.exponentMax then
    return (.infinity false, none)
  let grid := blockFloatDotGrid precision keptBits commonA commonB
  let terms := blockFloatProductTerms precision keptBits commonA commonB left right
  let some first := terms.head? | return (.zero false, some grid)
  let minExponent := terms.foldl (fun current term => min current term.2.2) first.2.2
  let exact := terms.all fun term =>
    let shift := (term.2.2 - minExponent).toNat
    shift <= 16 && 128 - (Nat.log2 term.2.1 + 1) < shift + 4
  if exact then
    let total := terms.foldl (fun current term =>
      let magnitude := Int.ofNat (term.2.1 * 2 ^ (term.2.2 - minExponent).toNat)
      current + if term.1 then -magnitude else magnitude) 0
    if total == 0 then return (.zero false, some grid)
    return (.finite (total < 0) total.natAbs minExponent, some grid)
  let accumulated := terms.foldl (fun current term =>
    addMAUValues current (.finite term.1 term.2.1 term.2.2)) (.zero false)
  return (accumulated, some grid)

theorem matrixBlockFloatDot_half_raw_mantissa_product :
    matrixBlockFloatDot .half 9 [0x3f00] [0x3f00] =
      (.finite false 65536 (-16), some (-16)) := by
  decide

theorem matrixBlockFloatDot_half_extended_lane_uses_common_minus_six :
    matrixBlockFloatDot .half 9 [0x01ff, 0x1401] [0x1401, 0x1401] =
      (.finite false (575 * 2 ^ 117) (-181), some (-58)) := by
  decide

theorem matrixBlockFloatDot_zero_block (precision : FloatPrecision) (keptBits : Nat)
    (right : List Nat) :
    matrixBlockFloatDot precision keptBits [] right = (.zero false, none) := by
  simp [matrixBlockFloatDot, maxFloatExponent]

def matrixBlockFloatFma (input accumulatorPrecision output : FloatPrecision) (keptBits : Nat)
    (left right : List Nat) (accumulator : Nat) : Nat :=
  let (dot, grid) := matrixBlockFloatDot input keptBits left right
  let c := decodeMAUValue accumulatorPrecision accumulator
  let aligned := match grid with
    | some value => alignMAUAccumulator c value
    | none => c
  encodeMAUValue output (addMAUValues dot aligned)

theorem matrixBlockFloatFma_half_raw_product_plus_single_one :
    matrixBlockFloatFma .half .single .single 9 [0x3f00] [0x3f00]
      0x3f800000 = 0x40000000 := by
  decide

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

/-- Sixteen-input native floating reduction: round each consecutive group of
four into the input format, then reduce those four intermediate results.
This mirrors `rrn::reduce16` used by the 16x1 L1BM path. -/
def reduceLongFloatAdd16 (precision : NativeFloatPrecision)
    (values : List (BitVec 64)) : BitVec 64 :=
  let format := precision.format
  let width := format.width
  let laneValues := (List.range (64 / width)).map fun lane =>
    let shift := 64 - width * (lane + 1)
    let inputs := values.map fun value => (value.extractLsb' shift width).toNat
    let stages := (List.range 4).map fun group =>
      reduceFloatAdd format format ((inputs.drop (group * 4)).take 4)
    reduceFloatAdd format format stages * 2 ^ shift
  BitVec.ofNat 64 (laneValues.foldl (· + ·) 0)

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
