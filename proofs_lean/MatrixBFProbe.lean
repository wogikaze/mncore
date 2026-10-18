import ProofsLean.RRN

open ProofsLean.MNCore.RRN

def parseBlockFormat (code : String) : FloatPrecision × FloatPrecision × Nat :=
  match code with
  | "d" => (.double, .double, 52)
  | "f" => (.single, .single, 23)
  | "g" => (.single, .single, 18)
  | "h" => (.half, .single, 9)
  | _ => (.single, .single, 23)

def parseFormat (code : String) : FloatPrecision :=
  match code with
  | "d" => .double
  | "s" => .single
  | "h" => .half
  | _ => .single

def parseLanes (field : String) : List Nat :=
  (field.splitOn ",").map String.toNat!

def evaluateMatrixBFRow (row : String) : Nat := Id.run do
  let fields := row.splitOn "\t"
  let inputCode := fields[0]!
  let outputCode := fields[1]!
  let (inputFormat, accumulatorFormat, expectedKept) := parseBlockFormat inputCode
  let outputFormat := parseFormat outputCode
  let kept := fields[2]!.toNat!
  if kept != expectedKept then panic! "unexpected kept mantissa width"
  let accumulator := fields[4]!.toNat!
  let left := parseLanes fields[5]!
  let right := parseLanes fields[6]!
  if left.length != right.length then panic! "dot lane counts differ"
  return matrixBlockFloatFma inputFormat accumulatorFormat outputFormat kept
    left right accumulator

def main : IO Unit := do
  let stdin ← IO.getStdin
  let input ← stdin.readToEnd
  for row in input.splitOn "\n" do
    if !row.isEmpty then
      IO.println (evaluateMatrixBFRow row)
