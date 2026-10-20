import ProofsLean.WelcomeMatrixMAUShape

/-! # The matrix-MAU datapath statement `WelcomePEMatrixMAUZeroBus`

`WelcomeMatrixMAUShape.lean` isolates the datapath statement
`WelcomePEMatrixMAUZeroBus`: at the all-zero initial state every bus produced by
`executeParsedMatrixMAUAtMAB` has a zero low half.  This module discharges it.

The proof has three parts, following §10.3 of the shape module:

* **The row computation.**  At the all-zero store, with a zero or negative-zero
  accumulator, every output row of `parsedMatrixMAUCalculateRows?` is `0`
  (`parsedMatrixMAUCalculateRows_zero_store`, and the usable guarded form
  `parsedMatrixMAUCalculateRows_zero_store_of_fma`).  The `do` block of the
  definition contains a `match precision with …` in the accumulator decode,
  which elaborates as a dependent match; we therefore prove the statement for
  each concrete float precision (`.d`, `.f`, `.g`, `.h`) and then dispatch on
  `precision`.  The accumulator is only read for `kind = .fma`, so the guarded
  form states the length hypothesis under that equation and applies to the
  `mul`/`add`/`passa` calculations, whose accumulator list is empty.

* **The calculation decomposition.**  A successful
  `executeParsedMatrixMAUCalculationAtMAB` at the all-zero state forces the
  source shape of its calculation kind, reads the vector (and accumulator)
  lanes as zero, and feeds them to the row computation
  (`executeParsedMatrixMAUCalculationAtMAB_{mul,add,passa,fma}_rows`, assembled
  generically as `executeParsedMatrixMAUCalculationAtMAB_zero_rows`).

* **The packing step.**  `parsedMatrixMAUPackPEBus?` of a list of zero lanes has
  a zero low half (only the non-round `.h` layout has a nonzero low half in
  general, and it needs rows 2 and 3 to be zero).  The per-PE packed bus of the
  all-zero row list is `⟨0, 0⟩`, and `parsedMatrixMAUPackOutputs` preserves a
  zero low half over the four-PE list.

* **The datapath statement.**  A successful `executeParsedMatrixMAUAtMAB` at the
  all-zero state has such zero rows and therefore zero-low buses.

No `sorry`, no `admit`, no `native_decide`, no new axioms, and no existing
module is edited by this file. -/

namespace ProofsLean.MNCore

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

open Issue
open PEMemory

/-! ## 1. The row computation at the all-zero store -/

/-- The logical row count is four times the per-PE row count. -/
theorem parsedMatrixMAURowCount_eq_four_mul (precision : ParsedPrecision) :
    parsedMatrixMAURowCount precision = 4 * parsedMatrixMAURowsPerPE precision := by
  cases precision <;> rfl

/-- **Row computation, double precision.** -/
theorem parsedMatrixMAUCalculateRows_zero_store_d
    (coordinate : MABCoordinate) (sideY : Bool) (kind : CalcKind) (half : Option Char)
    (round : Bool) (vector accumulator : List Nat)
    (_out : parsedMatrixMAUOutputFormat .d round ≠ none)
    (accZero : ∀ value ∈ accumulator, ∃ negative,
      RRN.decodeMAUValue (parsedMatrixMAUAccumulatorFormat .d) value = RRN.MAUValue.zero negative)
    (fmaLength : kind = .fma → accumulator.length = 4 * parsedMatrixMAUAccumulatorLanesPerPE .d) :
    parsedMatrixMAUCalculateRows? (fun _ _ _ _ => 0) coordinate sideY .d kind half round
      vector accumulator = some (List.replicate (parsedMatrixMAURowCount .d) 0) := by
  unfold parsedMatrixMAUCalculateRows?
  simp only [parsedMatrixMAUFloatFormat, parsedMatrixMAUOutputFormat,
    Option.bind_eq_bind, Option.bind_some]
  apply list_mapM_range_replicate
  intro row hrow
  simp only [parsedMatrixMAURowCount, parsedMatrixMAUAccumulatorLanesPerPE] at hrow
  have prodEq := parsedMatrixMAUProductRow_zero_store coordinate.mab sideY .d row
    (by simp [parsedMatrixMAUFloatFormat])
  by_cases active : parsedMatrixMAURowActive half row = true
  · rw [ite_eq_left active]
    by_cases fma : (kind == .fma) = true
    · rw [prodEq]
      simp only [Option.bind_eq_bind, Option.bind_some]
      have kindEq : kind = .fma := by simpa using fma
      have rowLt : row < accumulator.length := by
        rw [fmaLength kindEq]
        simp only [parsedMatrixMAUAccumulatorLanesPerPE]
        omega
      rw [ite_eq_left fma]
      rw [List.getElem?_eq_getElem rowLt]
      obtain ⟨negative, decoded⟩ := accZero accumulator[row] (List.getElem_mem rowLt)
      exact congrArg some (parsedMatrixMAUCalculateRow_zero RRN.FloatPrecision.double
        (if round = true then RRN.FloatPrecision.single else RRN.FloatPrecision.double)
        RRN.FloatPrecision.double (parsedMatrixMAUKeptMantissaBits .d)
        (parsedMatrixMAUDotWidth .d) vector (accumulator[row]) negative decoded)
    · rw [prodEq]
      simp only [Option.bind_eq_bind, Option.bind_some]
      rw [ite_eq_right fma]
      exact congrArg some (parsedMatrixMAUCalculateRow_zero RRN.FloatPrecision.double
        (if round = true then RRN.FloatPrecision.single else RRN.FloatPrecision.double)
        RRN.FloatPrecision.double (parsedMatrixMAUKeptMantissaBits .d)
        (parsedMatrixMAUDotWidth .d) vector 0 false (decodeMAUValue_zero _))
  · rw [ite_eq_right active]
    by_cases fma : (kind == .fma) = true
    · rw [ite_eq_left fma]
      have kindEq : kind = .fma := by simpa using fma
      have rowLt : row < accumulator.length := by
        rw [fmaLength kindEq]
        simp only [parsedMatrixMAUAccumulatorLanesPerPE]
        omega
      rw [List.getElem?_eq_getElem rowLt]
      simp only [Option.bind_eq_bind, Option.bind_some]
      obtain ⟨negative, decoded⟩ := accZero accumulator[row] (List.getElem_mem rowLt)
      exact congrArg some (parsedMatrixMAUCalculateRow_zero RRN.FloatPrecision.double
        (if round = true then RRN.FloatPrecision.single else RRN.FloatPrecision.double)
        RRN.FloatPrecision.double (parsedMatrixMAUKeptMantissaBits .d)
        0 vector (accumulator[row]) negative decoded)
    · rw [ite_eq_right fma]
      exact congrArg some (parsedMatrixMAUCalculateRow_zero RRN.FloatPrecision.double
        (if round = true then RRN.FloatPrecision.single else RRN.FloatPrecision.double)
        RRN.FloatPrecision.double (parsedMatrixMAUKeptMantissaBits .d)
        0 vector 0 false (decodeMAUValue_zero _))

/-- **Row computation, single precision (`.f`).** -/
theorem parsedMatrixMAUCalculateRows_zero_store_f
    (coordinate : MABCoordinate) (sideY : Bool) (kind : CalcKind) (half : Option Char)
    (round : Bool) (vector accumulator : List Nat)
    (_out : parsedMatrixMAUOutputFormat .f round ≠ none)
    (accZero : ∀ value ∈ accumulator, ∃ negative,
      RRN.decodeMAUValue (parsedMatrixMAUAccumulatorFormat .f) value = RRN.MAUValue.zero negative)
    (fmaLength : kind = .fma → accumulator.length = 4 * parsedMatrixMAUAccumulatorLanesPerPE .f) :
    parsedMatrixMAUCalculateRows? (fun _ _ _ _ => 0) coordinate sideY .f kind half round
      vector accumulator = some (List.replicate (parsedMatrixMAURowCount .f) 0) := by
  unfold parsedMatrixMAUCalculateRows?
  simp only [parsedMatrixMAUFloatFormat, parsedMatrixMAUOutputFormat,
    Option.bind_eq_bind, Option.bind_some]
  apply list_mapM_range_replicate
  intro row hrow
  simp only [parsedMatrixMAURowCount, parsedMatrixMAUAccumulatorLanesPerPE] at hrow
  have prodEq := parsedMatrixMAUProductRow_zero_store coordinate.mab sideY .f row
    (by simp [parsedMatrixMAUFloatFormat])
  by_cases active : parsedMatrixMAURowActive half row = true
  · rw [ite_eq_left active]
    by_cases fma : (kind == .fma) = true
    · rw [prodEq]
      simp only [Option.bind_eq_bind, Option.bind_some]
      have kindEq : kind = .fma := by simpa using fma
      have rowLt : row < accumulator.length := by
        rw [fmaLength kindEq]
        simp only [parsedMatrixMAUAccumulatorLanesPerPE]
        omega
      rw [ite_eq_left fma]
      rw [List.getElem?_eq_getElem rowLt]
      obtain ⟨negative, decoded⟩ := accZero accumulator[row] (List.getElem_mem rowLt)
      exact congrArg some (parsedMatrixMAUCalculateRow_zero RRN.FloatPrecision.single
        RRN.FloatPrecision.single RRN.FloatPrecision.single
        (parsedMatrixMAUKeptMantissaBits .f)
        (parsedMatrixMAUDotWidth .f) vector (accumulator[row]) negative decoded)
    · rw [prodEq]
      simp only [Option.bind_eq_bind, Option.bind_some]
      rw [ite_eq_right fma]
      exact congrArg some (parsedMatrixMAUCalculateRow_zero RRN.FloatPrecision.single
        RRN.FloatPrecision.single RRN.FloatPrecision.single
        (parsedMatrixMAUKeptMantissaBits .f)
        (parsedMatrixMAUDotWidth .f) vector 0 false (decodeMAUValue_zero _))
  · rw [ite_eq_right active]
    by_cases fma : (kind == .fma) = true
    · rw [ite_eq_left fma]
      have kindEq : kind = .fma := by simpa using fma
      have rowLt : row < accumulator.length := by
        rw [fmaLength kindEq]
        simp only [parsedMatrixMAUAccumulatorLanesPerPE]
        omega
      rw [List.getElem?_eq_getElem rowLt]
      simp only [Option.bind_eq_bind, Option.bind_some]
      obtain ⟨negative, decoded⟩ := accZero accumulator[row] (List.getElem_mem rowLt)
      exact congrArg some (parsedMatrixMAUCalculateRow_zero RRN.FloatPrecision.single
        RRN.FloatPrecision.single RRN.FloatPrecision.single
        (parsedMatrixMAUKeptMantissaBits .f)
        0 vector (accumulator[row]) negative decoded)
    · rw [ite_eq_right fma]
      exact congrArg some (parsedMatrixMAUCalculateRow_zero RRN.FloatPrecision.single
        RRN.FloatPrecision.single RRN.FloatPrecision.single
        (parsedMatrixMAUKeptMantissaBits .f)
        0 vector 0 false (decodeMAUValue_zero _))

/-- **Row computation, single precision (`.g`).** -/
theorem parsedMatrixMAUCalculateRows_zero_store_g
    (coordinate : MABCoordinate) (sideY : Bool) (kind : CalcKind) (half : Option Char)
    (round : Bool) (vector accumulator : List Nat)
    (_out : parsedMatrixMAUOutputFormat .g round ≠ none)
    (accZero : ∀ value ∈ accumulator, ∃ negative,
      RRN.decodeMAUValue (parsedMatrixMAUAccumulatorFormat .g) value = RRN.MAUValue.zero negative)
    (fmaLength : kind = .fma → accumulator.length = 4 * parsedMatrixMAUAccumulatorLanesPerPE .g) :
    parsedMatrixMAUCalculateRows? (fun _ _ _ _ => 0) coordinate sideY .g kind half round
      vector accumulator = some (List.replicate (parsedMatrixMAURowCount .g) 0) := by
  unfold parsedMatrixMAUCalculateRows?
  simp only [parsedMatrixMAUFloatFormat, parsedMatrixMAUOutputFormat,
    Option.bind_eq_bind, Option.bind_some]
  apply list_mapM_range_replicate
  intro row hrow
  simp only [parsedMatrixMAURowCount, parsedMatrixMAUAccumulatorLanesPerPE] at hrow
  have prodEq := parsedMatrixMAUProductRow_zero_store coordinate.mab sideY .g row
    (by simp [parsedMatrixMAUFloatFormat])
  by_cases active : parsedMatrixMAURowActive half row = true
  · rw [ite_eq_left active]
    by_cases fma : (kind == .fma) = true
    · rw [prodEq]
      simp only [Option.bind_eq_bind, Option.bind_some]
      have kindEq : kind = .fma := by simpa using fma
      have rowLt : row < accumulator.length := by
        rw [fmaLength kindEq]
        simp only [parsedMatrixMAUAccumulatorLanesPerPE]
        omega
      rw [ite_eq_left fma]
      rw [List.getElem?_eq_getElem rowLt]
      obtain ⟨negative, decoded⟩ := accZero accumulator[row] (List.getElem_mem rowLt)
      exact congrArg some (parsedMatrixMAUCalculateRow_zero RRN.FloatPrecision.single
        RRN.FloatPrecision.single RRN.FloatPrecision.single
        (parsedMatrixMAUKeptMantissaBits .g)
        (parsedMatrixMAUDotWidth .g) vector (accumulator[row]) negative decoded)
    · rw [prodEq]
      simp only [Option.bind_eq_bind, Option.bind_some]
      rw [ite_eq_right fma]
      exact congrArg some (parsedMatrixMAUCalculateRow_zero RRN.FloatPrecision.single
        RRN.FloatPrecision.single RRN.FloatPrecision.single
        (parsedMatrixMAUKeptMantissaBits .g)
        (parsedMatrixMAUDotWidth .g) vector 0 false (decodeMAUValue_zero _))
  · rw [ite_eq_right active]
    by_cases fma : (kind == .fma) = true
    · rw [ite_eq_left fma]
      have kindEq : kind = .fma := by simpa using fma
      have rowLt : row < accumulator.length := by
        rw [fmaLength kindEq]
        simp only [parsedMatrixMAUAccumulatorLanesPerPE]
        omega
      rw [List.getElem?_eq_getElem rowLt]
      simp only [Option.bind_eq_bind, Option.bind_some]
      obtain ⟨negative, decoded⟩ := accZero accumulator[row] (List.getElem_mem rowLt)
      exact congrArg some (parsedMatrixMAUCalculateRow_zero RRN.FloatPrecision.single
        RRN.FloatPrecision.single RRN.FloatPrecision.single
        (parsedMatrixMAUKeptMantissaBits .g)
        0 vector (accumulator[row]) negative decoded)
    · rw [ite_eq_right fma]
      exact congrArg some (parsedMatrixMAUCalculateRow_zero RRN.FloatPrecision.single
        RRN.FloatPrecision.single RRN.FloatPrecision.single
        (parsedMatrixMAUKeptMantissaBits .g)
        0 vector 0 false (decodeMAUValue_zero _))

/-- **Row computation, half precision.** -/
theorem parsedMatrixMAUCalculateRows_zero_store_h
    (coordinate : MABCoordinate) (sideY : Bool) (kind : CalcKind) (half : Option Char)
    (round : Bool) (vector accumulator : List Nat)
    (_out : parsedMatrixMAUOutputFormat .h round ≠ none)
    (accZero : ∀ value ∈ accumulator, ∃ negative,
      RRN.decodeMAUValue (parsedMatrixMAUAccumulatorFormat .h) value = RRN.MAUValue.zero negative)
    (fmaLength : kind = .fma → accumulator.length = 4 * parsedMatrixMAUAccumulatorLanesPerPE .h) :
    parsedMatrixMAUCalculateRows? (fun _ _ _ _ => 0) coordinate sideY .h kind half round
      vector accumulator = some (List.replicate (parsedMatrixMAURowCount .h) 0) := by
  unfold parsedMatrixMAUCalculateRows?
  simp only [parsedMatrixMAUFloatFormat, parsedMatrixMAUOutputFormat,
    Option.bind_eq_bind, Option.bind_some]
  apply list_mapM_range_replicate
  intro row hrow
  simp only [parsedMatrixMAURowCount, parsedMatrixMAUAccumulatorLanesPerPE] at hrow
  have prodEq := parsedMatrixMAUProductRow_zero_store coordinate.mab sideY .h row
    (by simp [parsedMatrixMAUFloatFormat])
  by_cases active : parsedMatrixMAURowActive half row = true
  · rw [ite_eq_left active]
    by_cases fma : (kind == .fma) = true
    · rw [prodEq]
      simp only [Option.bind_eq_bind, Option.bind_some]
      have kindEq : kind = .fma := by simpa using fma
      have rowLt : row < accumulator.length := by
        rw [fmaLength kindEq]
        simp only [parsedMatrixMAUAccumulatorLanesPerPE]
        omega
      rw [ite_eq_left fma]
      rw [List.getElem?_eq_getElem rowLt]
      obtain ⟨negative, decoded⟩ := accZero accumulator[row] (List.getElem_mem rowLt)
      exact congrArg some (parsedMatrixMAUCalculateRow_zero RRN.FloatPrecision.half
        (if round = true then RRN.FloatPrecision.half else RRN.FloatPrecision.single)
        RRN.FloatPrecision.single (parsedMatrixMAUKeptMantissaBits .h)
        (parsedMatrixMAUDotWidth .h) vector (accumulator[row]) negative decoded)
    · rw [prodEq]
      simp only [Option.bind_eq_bind, Option.bind_some]
      rw [ite_eq_right fma]
      exact congrArg some (parsedMatrixMAUCalculateRow_zero RRN.FloatPrecision.half
        (if round = true then RRN.FloatPrecision.half else RRN.FloatPrecision.single)
        RRN.FloatPrecision.single (parsedMatrixMAUKeptMantissaBits .h)
        (parsedMatrixMAUDotWidth .h) vector 0 false (decodeMAUValue_zero _))
  · rw [ite_eq_right active]
    by_cases fma : (kind == .fma) = true
    · rw [ite_eq_left fma]
      have kindEq : kind = .fma := by simpa using fma
      have rowLt : row < accumulator.length := by
        rw [fmaLength kindEq]
        simp only [parsedMatrixMAUAccumulatorLanesPerPE]
        omega
      rw [List.getElem?_eq_getElem rowLt]
      simp only [Option.bind_eq_bind, Option.bind_some]
      obtain ⟨negative, decoded⟩ := accZero accumulator[row] (List.getElem_mem rowLt)
      exact congrArg some (parsedMatrixMAUCalculateRow_zero RRN.FloatPrecision.half
        (if round = true then RRN.FloatPrecision.half else RRN.FloatPrecision.single)
        RRN.FloatPrecision.single (parsedMatrixMAUKeptMantissaBits .h)
        0 vector (accumulator[row]) negative decoded)
    · rw [ite_eq_right fma]
      exact congrArg some (parsedMatrixMAUCalculateRow_zero RRN.FloatPrecision.half
        (if round = true then RRN.FloatPrecision.half else RRN.FloatPrecision.single)
        RRN.FloatPrecision.single (parsedMatrixMAUKeptMantissaBits .h)
        0 vector 0 false (decodeMAUValue_zero _))

/-- **The row computation at the all-zero store.**  A zero store and a zero or
negative-zero accumulator make every output row `0`.

The accumulator is only read when `kind = .fma`, so the length hypothesis is
guarded by that equation: for `mul`/`add`/`passa` the accumulator list is empty
and the lemma applies with a vacuous guard. -/
theorem parsedMatrixMAUCalculateRows_zero_store_of_fma
    (coordinate : MABCoordinate) (sideY : Bool) (precision : ParsedPrecision)
    (kind : CalcKind) (half : Option Char) (round : Bool) (vector accumulator : List Nat)
    (float : parsedMatrixMAUFloatFormat precision ≠ none)
    (out : parsedMatrixMAUOutputFormat precision round ≠ none)
    (accZero : ∀ value ∈ accumulator, ∃ negative,
      RRN.decodeMAUValue (parsedMatrixMAUAccumulatorFormat precision) value =
        RRN.MAUValue.zero negative)
    (fmaLength : kind = .fma → accumulator.length =
      4 * parsedMatrixMAUAccumulatorLanesPerPE precision) :
    parsedMatrixMAUCalculateRows? (fun _ _ _ _ => 0) coordinate sideY precision kind half round
      vector accumulator = some (List.replicate (parsedMatrixMAURowCount precision) 0) := by
  cases precision
  · exact parsedMatrixMAUCalculateRows_zero_store_d coordinate sideY kind half round vector
      accumulator out accZero fmaLength
  · exact parsedMatrixMAUCalculateRows_zero_store_f coordinate sideY kind half round vector
      accumulator out accZero fmaLength
  · exact parsedMatrixMAUCalculateRows_zero_store_g coordinate sideY kind half round vector
      accumulator out accZero fmaLength
  · exact parsedMatrixMAUCalculateRows_zero_store_h coordinate sideY kind half round vector
      accumulator out accZero fmaLength
  · exact absurd float (by simp [parsedMatrixMAUFloatFormat])
  · exact absurd float (by simp [parsedMatrixMAUFloatFormat])
  · exact absurd float (by simp [parsedMatrixMAUFloatFormat])

/-- **The row computation at the all-zero store** in the recorded §10.3 form,
with the accumulator length hypothesis unconditional. -/
theorem parsedMatrixMAUCalculateRows_zero_store
    (coordinate : MABCoordinate) (sideY : Bool) (precision : ParsedPrecision)
    (kind : CalcKind) (half : Option Char) (round : Bool) (vector accumulator : List Nat)
    (float : parsedMatrixMAUFloatFormat precision ≠ none)
    (out : parsedMatrixMAUOutputFormat precision round ≠ none)
    (accZero : ∀ value ∈ accumulator, ∃ negative,
      RRN.decodeMAUValue (parsedMatrixMAUAccumulatorFormat precision) value =
        RRN.MAUValue.zero negative)
    (accLength : accumulator.length = 4 * parsedMatrixMAUAccumulatorLanesPerPE precision) :
    parsedMatrixMAUCalculateRows? (fun _ _ _ _ => 0) coordinate sideY precision kind half round
      vector accumulator = some (List.replicate (parsedMatrixMAURowCount precision) 0) :=
  parsedMatrixMAUCalculateRows_zero_store_of_fma coordinate sideY precision kind half round
    vector accumulator float out accZero (fun _ => accLength)

/-! ## 1b. The calculation at the all-zero store, per calculation kind

A successful `executeParsedMatrixMAUCalculationAtMAB` at the all-zero state has
the source shape its `kind` demands.  The vector (and, for `fma`, the
accumulator) read is a successful read at the all-zero state, so the row
computation of §1 yields zero rows.  These four lemmas are the per-kind form of
that fact; the generic form is assembled in §1c. -/

/-- **The `mul` calculation succeeds only on zero rows.**  The matrix
sources of a `mul` calculation are `[matrix, vector]`; after the successful
vector read the row computation is the all-zero one. -/
theorem executeParsedMatrixMAUCalculationAtMAB_mul_rows
    (coordinate : MABCoordinate) (cycle : Fin 4) (precision : ParsedPrecision)
    (half : Option Char) (round : Bool) (sideY : Bool) (width : Fin 5)
    (vectorSource : ParsedOperand) (destinations : List ParsedOperand)
    (flush : Option ParsedMask) (text : String) (rows : List Nat) (poison flagsUnavailable : Bool)
    (executed : executeParsedMatrixMAUCalculationAtMAB (welcomeInitialState welcomeZeroWords) coordinate
      { op := .mau precision true .mul half round
        sources := [.matrix sideY width none, vectorSource],
        destinations := destinations, flush := flush, text := text } cycle
      = .ok (rows, poison, flagsUnavailable)) :
    rows = List.replicate (parsedMatrixMAURowCount precision) 0 := by
  simp only [executeParsedMatrixMAUCalculationAtMAB] at executed
  simp only [Id.run, pure, bind, Id] at executed
  cases hf : parsedMatrixMAUFloatFormat precision with
  | none => rw [hf] at executed; simp at executed
  | some vectorFormat =>
    rw [hf] at executed
    dsimp only at executed
    cases read : readParsedMatrixMAUSourceAtMAB (welcomeInitialState welcomeZeroWords) coordinate vectorSource
        vectorFormat (parsedMatrixMAUVectorLanesPerPE precision) cycle with
    | failure => rw [read] at executed; simp at executed
    | unknown => rw [read] at executed; simp at executed
    | ok vectorValues =>
      rw [read] at executed
      dsimp only at executed
      cases rowsCalc : parsedMatrixMAUCalculateRows?
          ((welcomeInitialState welcomeZeroWords).matrixRegisters coordinate.group coordinate.l2b coordinate.l1b)
          coordinate sideY precision .mul half round vectorValues [] with
      | none => rw [rowsCalc] at executed; simp at executed
      | some rowValues =>
        rw [rowsCalc] at executed
        simp only [StepResult.ok.injEq] at executed
        obtain ⟨rfl, _, _⟩ := executed
        have float : parsedMatrixMAUFloatFormat precision ≠ none := by rw [hf]; simp
        have out : parsedMatrixMAUOutputFormat precision round ≠ none := by
          cases precision <;> simp [parsedMatrixMAUOutputFormat, parsedMatrixMAUFloatFormat] at float ⊢
        rw [welcomeZero_matrixStore coordinate.group coordinate.l2b coordinate.l1b] at rowsCalc
        have rowsEq := parsedMatrixMAUCalculateRows_zero_store_of_fma coordinate sideY precision .mul half round
          vectorValues [] float out (fun _ h => absurd h (by simp)) (fun h => absurd h (by decide))
        rw [rowsEq] at rowsCalc
        exact (Option.some.inj rowsCalc).symm

/-- **The `add` calculation succeeds only on zero rows.**  The matrix
sources of a `add` calculation are `[matrix, vector]`; after the successful
vector read the row computation is the all-zero one. -/
theorem executeParsedMatrixMAUCalculationAtMAB_add_rows
    (coordinate : MABCoordinate) (cycle : Fin 4) (precision : ParsedPrecision)
    (half : Option Char) (round : Bool) (sideY : Bool) (width : Fin 5)
    (vectorSource : ParsedOperand) (destinations : List ParsedOperand)
    (flush : Option ParsedMask) (text : String) (rows : List Nat) (poison flagsUnavailable : Bool)
    (executed : executeParsedMatrixMAUCalculationAtMAB (welcomeInitialState welcomeZeroWords) coordinate
      { op := .mau precision true .add half round
        sources := [.matrix sideY width none, vectorSource],
        destinations := destinations, flush := flush, text := text } cycle
      = .ok (rows, poison, flagsUnavailable)) :
    rows = List.replicate (parsedMatrixMAURowCount precision) 0 := by
  simp only [executeParsedMatrixMAUCalculationAtMAB] at executed
  simp only [Id.run, pure, bind, Id] at executed
  cases hf : parsedMatrixMAUFloatFormat precision with
  | none => rw [hf] at executed; simp at executed
  | some vectorFormat =>
    rw [hf] at executed
    dsimp only at executed
    cases read : readParsedMatrixMAUSourceAtMAB (welcomeInitialState welcomeZeroWords) coordinate vectorSource
        vectorFormat (parsedMatrixMAUVectorLanesPerPE precision) cycle with
    | failure => rw [read] at executed; simp at executed
    | unknown => rw [read] at executed; simp at executed
    | ok vectorValues =>
      rw [read] at executed
      dsimp only at executed
      cases rowsCalc : parsedMatrixMAUCalculateRows?
          ((welcomeInitialState welcomeZeroWords).matrixRegisters coordinate.group coordinate.l2b coordinate.l1b)
          coordinate sideY precision .add half round vectorValues [] with
      | none => rw [rowsCalc] at executed; simp at executed
      | some rowValues =>
        rw [rowsCalc] at executed
        simp only [StepResult.ok.injEq] at executed
        obtain ⟨rfl, _, _⟩ := executed
        have float : parsedMatrixMAUFloatFormat precision ≠ none := by rw [hf]; simp
        have out : parsedMatrixMAUOutputFormat precision round ≠ none := by
          cases precision <;> simp [parsedMatrixMAUOutputFormat, parsedMatrixMAUFloatFormat] at float ⊢
        rw [welcomeZero_matrixStore coordinate.group coordinate.l2b coordinate.l1b] at rowsCalc
        have rowsEq := parsedMatrixMAUCalculateRows_zero_store_of_fma coordinate sideY precision .add half round
          vectorValues [] float out (fun _ h => absurd h (by simp)) (fun h => absurd h (by decide))
        rw [rowsEq] at rowsCalc
        exact (Option.some.inj rowsCalc).symm

/-- **The `passa` calculation succeeds only on zero rows.**  The matrix
sources of a `passa` calculation are `[matrix, vector]`; after the successful
vector read the row computation is the all-zero one. -/
theorem executeParsedMatrixMAUCalculationAtMAB_passa_rows
    (coordinate : MABCoordinate) (cycle : Fin 4) (precision : ParsedPrecision)
    (half : Option Char) (round : Bool) (sideY : Bool) (width : Fin 5)
    (vectorSource : ParsedOperand) (destinations : List ParsedOperand)
    (flush : Option ParsedMask) (text : String) (rows : List Nat) (poison flagsUnavailable : Bool)
    (executed : executeParsedMatrixMAUCalculationAtMAB (welcomeInitialState welcomeZeroWords) coordinate
      { op := .mau precision true .passa half round
        sources := [.matrix sideY width none, vectorSource],
        destinations := destinations, flush := flush, text := text } cycle
      = .ok (rows, poison, flagsUnavailable)) :
    rows = List.replicate (parsedMatrixMAURowCount precision) 0 := by
  simp only [executeParsedMatrixMAUCalculationAtMAB] at executed
  simp only [Id.run, pure, bind, Id] at executed
  cases hf : parsedMatrixMAUFloatFormat precision with
  | none => rw [hf] at executed; simp at executed
  | some vectorFormat =>
    rw [hf] at executed
    dsimp only at executed
    cases read : readParsedMatrixMAUSourceAtMAB (welcomeInitialState welcomeZeroWords) coordinate vectorSource
        vectorFormat (parsedMatrixMAUVectorLanesPerPE precision) cycle with
    | failure => rw [read] at executed; simp at executed
    | unknown => rw [read] at executed; simp at executed
    | ok vectorValues =>
      rw [read] at executed
      dsimp only at executed
      cases rowsCalc : parsedMatrixMAUCalculateRows?
          ((welcomeInitialState welcomeZeroWords).matrixRegisters coordinate.group coordinate.l2b coordinate.l1b)
          coordinate sideY precision .passa half round vectorValues [] with
      | none => rw [rowsCalc] at executed; simp at executed
      | some rowValues =>
        rw [rowsCalc] at executed
        simp only [StepResult.ok.injEq] at executed
        obtain ⟨rfl, _, _⟩ := executed
        have float : parsedMatrixMAUFloatFormat precision ≠ none := by rw [hf]; simp
        have out : parsedMatrixMAUOutputFormat precision round ≠ none := by
          cases precision <;> simp [parsedMatrixMAUOutputFormat, parsedMatrixMAUFloatFormat] at float ⊢
        rw [welcomeZero_matrixStore coordinate.group coordinate.l2b coordinate.l1b] at rowsCalc
        have rowsEq := parsedMatrixMAUCalculateRows_zero_store_of_fma coordinate sideY precision .passa half round
          vectorValues [] float out (fun _ h => absurd h (by simp)) (fun h => absurd h (by decide))
        rw [rowsEq] at rowsCalc
        exact (Option.some.inj rowsCalc).symm

/-- **The `fma` calculation succeeds only on zero rows.**  The matrix sources of
an `fma` calculation are `[matrix, vector, accumulator]`; the accumulator read
returns zero-decoding lanes, which is the guarded length hypothesis of the row
computation. -/
theorem executeParsedMatrixMAUCalculationAtMAB_fma_rows
    (coordinate : MABCoordinate) (cycle : Fin 4) (precision : ParsedPrecision)
    (half : Option Char) (round : Bool) (sideY : Bool) (width : Fin 5)
    (vectorSource accumulatorSource : ParsedOperand) (destinations : List ParsedOperand)
    (flush : Option ParsedMask) (text : String) (rows : List Nat) (poison flagsUnavailable : Bool)
    (executed : executeParsedMatrixMAUCalculationAtMAB (welcomeInitialState welcomeZeroWords) coordinate
      { op := .mau precision true .fma half round
        sources := [.matrix sideY width none, vectorSource, accumulatorSource],
        destinations := destinations, flush := flush, text := text } cycle
      = .ok (rows, poison, flagsUnavailable)) :
    rows = List.replicate (parsedMatrixMAURowCount precision) 0 := by
  simp only [executeParsedMatrixMAUCalculationAtMAB] at executed
  simp only [Id.run, pure, bind, Id] at executed
  cases hf : parsedMatrixMAUFloatFormat precision with
  | none => rw [hf] at executed; simp at executed
  | some vectorFormat =>
    rw [hf] at executed
    simp only [Id.run, pure, bind, Id] at executed
    cases read : readParsedMatrixMAUSourceAtMAB (welcomeInitialState welcomeZeroWords) coordinate vectorSource
        vectorFormat (parsedMatrixMAUVectorLanesPerPE precision) cycle with
    | failure => rw [read] at executed; simp at executed
    | unknown => rw [read] at executed; simp at executed
    | ok vectorValues =>
      rw [read] at executed
      simp only [Id.run, pure, bind, Id] at executed
      cases readAcc : readParsedMatrixMAUSourceAtMAB (welcomeInitialState welcomeZeroWords) coordinate
          accumulatorSource (parsedMatrixMAUAccumulatorFormat precision)
          (parsedMatrixMAUAccumulatorLanesPerPE precision) cycle with
      | failure => rw [readAcc] at executed; simp at executed
      | unknown => rw [readAcc] at executed; simp at executed
      | ok accumulatorValues =>
        rw [readAcc] at executed
        simp only [Id.run, pure, bind, Id] at executed
        cases rowsCalc : parsedMatrixMAUCalculateRows?
            ((welcomeInitialState welcomeZeroWords).matrixRegisters coordinate.group coordinate.l2b coordinate.l1b)
            coordinate sideY precision .fma half round vectorValues accumulatorValues with
        | none => rw [rowsCalc] at executed; simp at executed
        | some rowValues =>
          rw [rowsCalc] at executed
          simp only [StepResult.ok.injEq] at executed
          obtain ⟨rfl, _, _⟩ := executed
          have float : parsedMatrixMAUFloatFormat precision ≠ none := by rw [hf]; simp
          have out : parsedMatrixMAUOutputFormat precision round ≠ none := by
            cases precision <;> simp [parsedMatrixMAUOutputFormat, parsedMatrixMAUFloatFormat] at float ⊢
          obtain ⟨accLen, accZero⟩ := readParsedMatrixMAUSourceAtMAB_zero coordinate accumulatorSource
            (parsedMatrixMAUAccumulatorFormat precision)
            (parsedMatrixMAUAccumulatorLanesPerPE precision) cycle accumulatorValues readAcc
          rw [welcomeZero_matrixStore coordinate.group coordinate.l2b coordinate.l1b] at rowsCalc
          have rowsEq := parsedMatrixMAUCalculateRows_zero_store_of_fma coordinate sideY precision .fma
            half round vectorValues accumulatorValues float out accZero (fun _ => accLen)
          rw [rowsEq] at rowsCalc
          exact (Option.some.inj rowsCalc).symm

/-! ## 1c. The calculation at the all-zero store, generic form

`executeParsedMatrixMAUCalculationAtMAB` first matches the `op` and the source
list, so a successful calculation forces the source shape of its `kind`.  The
generic lemma below performs that shape analysis and applies the per-kind
lemma of §1b. -/

theorem executeParsedMatrixMAUCalculationAtMAB_zero_rows
    (coordinate : MABCoordinate) (op : ParsedOp) (sources : List ParsedOperand)
    (destinations : List ParsedOperand) (flush : Option ParsedMask) (text : String)
    (cycle : Fin 4) (rows : List Nat) (poison flagsUnavailable : Bool)
    (executed : executeParsedMatrixMAUCalculationAtMAB (welcomeInitialState welcomeZeroWords) coordinate
      { op := op, sources := sources, destinations := destinations, flush := flush, text := text } cycle
      = .ok (rows, poison, flagsUnavailable)) :
    ∃ precision kind half round,
      op = .mau precision true kind half round ∧
      rows = List.replicate (parsedMatrixMAURowCount precision) 0 := by
  cases hOp : op with
  | mau precision matrix kind half round =>
    cases matrix
    · simp [hOp, executeParsedMatrixMAUCalculationAtMAB] at executed
    · cases kind
      · cases sources with
        | nil => simp [hOp, executeParsedMatrixMAUCalculationAtMAB] at executed
        | cons a rest =>
          cases a with
          | matrix y width row =>
            cases row with
            | some r => simp [hOp, executeParsedMatrixMAUCalculationAtMAB] at executed
            | none =>
              cases rest with
              | nil => simp [hOp, executeParsedMatrixMAUCalculationAtMAB] at executed
              | cons b rest2 =>
                cases rest2 with
                | nil => simp [hOp, executeParsedMatrixMAUCalculationAtMAB] at executed
                | cons c rest3 =>
                  cases rest3 with
                  | nil =>
                    rw [hOp] at executed
                    exact ⟨precision, .fma, half, round, rfl,
                      executeParsedMatrixMAUCalculationAtMAB_fma_rows coordinate cycle precision half round
                        y width b c destinations flush text rows poison flagsUnavailable executed⟩
                  | cons d rest4 => simp [hOp, executeParsedMatrixMAUCalculationAtMAB] at executed
          | _ => simp [hOp, executeParsedMatrixMAUCalculationAtMAB] at executed
      · cases sources with
        | nil => simp [hOp, executeParsedMatrixMAUCalculationAtMAB] at executed
        | cons a rest =>
          cases a with
          | matrix y width row =>
            cases row with
            | some r => simp [hOp, executeParsedMatrixMAUCalculationAtMAB] at executed
            | none =>
              cases rest with
              | nil => simp [hOp, executeParsedMatrixMAUCalculationAtMAB] at executed
              | cons b rest2 =>
                cases rest2 with
                | nil =>
                  rw [hOp] at executed
                  exact ⟨precision, .mul, half, round, rfl,
                    executeParsedMatrixMAUCalculationAtMAB_mul_rows coordinate cycle precision half round
                      y width b destinations flush text rows poison flagsUnavailable executed⟩
                | cons c rest3 =>
                  cases rest3 with
                  | nil => simp [hOp, executeParsedMatrixMAUCalculationAtMAB] at executed
                  | cons d rest4 => simp [hOp, executeParsedMatrixMAUCalculationAtMAB] at executed
          | _ => simp [hOp, executeParsedMatrixMAUCalculationAtMAB] at executed
      · cases sources with
        | nil => simp [hOp, executeParsedMatrixMAUCalculationAtMAB] at executed
        | cons a rest =>
          cases a with
          | matrix y width row =>
            cases row with
            | some r => simp [hOp, executeParsedMatrixMAUCalculationAtMAB] at executed
            | none =>
              cases rest with
              | nil => simp [hOp, executeParsedMatrixMAUCalculationAtMAB] at executed
              | cons b rest2 =>
                cases rest2 with
                | nil =>
                  rw [hOp] at executed
                  exact ⟨precision, .add, half, round, rfl,
                    executeParsedMatrixMAUCalculationAtMAB_add_rows coordinate cycle precision half round
                      y width b destinations flush text rows poison flagsUnavailable executed⟩
                | cons c rest3 =>
                  cases rest3 with
                  | nil => simp [hOp, executeParsedMatrixMAUCalculationAtMAB] at executed
                  | cons d rest4 => simp [hOp, executeParsedMatrixMAUCalculationAtMAB] at executed
          | _ => simp [hOp, executeParsedMatrixMAUCalculationAtMAB] at executed
      · cases sources with
        | nil => simp [hOp, executeParsedMatrixMAUCalculationAtMAB] at executed
        | cons a rest =>
          cases a with
          | matrix y width row =>
            cases row with
            | some r => simp [hOp, executeParsedMatrixMAUCalculationAtMAB] at executed
            | none =>
              cases rest with
              | nil => simp [hOp, executeParsedMatrixMAUCalculationAtMAB] at executed
              | cons b rest2 =>
                cases rest2 with
                | nil =>
                  rw [hOp] at executed
                  exact ⟨precision, .passa, half, round, rfl,
                    executeParsedMatrixMAUCalculationAtMAB_passa_rows coordinate cycle precision half round
                      y width b destinations flush text rows poison flagsUnavailable executed⟩
                | cons c rest3 =>
                  cases rest3 with
                  | nil => simp [hOp, executeParsedMatrixMAUCalculationAtMAB] at executed
                  | cons d rest4 => simp [hOp, executeParsedMatrixMAUCalculationAtMAB] at executed
          | _ => simp [hOp, executeParsedMatrixMAUCalculationAtMAB] at executed
  | alu name precision unsigned arg => simp [hOp, executeParsedMatrixMAUCalculationAtMAB] at executed
  | immediate value unsigned => simp [hOp, executeParsedMatrixMAUCalculationAtMAB] at executed
  | zero => simp [hOp, executeParsedMatrixMAUCalculationAtMAB] at executed
  | matrixWrite precision => simp [hOp, executeParsedMatrixMAUCalculationAtMAB] at executed
  | matrixRead precision => simp [hOp, executeParsedMatrixMAUCalculationAtMAB] at executed
  | wait tag => simp [hOp, executeParsedMatrixMAUCalculationAtMAB] at executed
  | noforward => simp [hOp, executeParsedMatrixMAUCalculationAtMAB] at executed
  | l1bm lop => simp [hOp, executeParsedMatrixMAUCalculationAtMAB] at executed
  | l2bm lop => simp [hOp, executeParsedMatrixMAUCalculationAtMAB] at executed

/-! ## 2. The packing step: zero rows pack into zero-low buses -/

/-- The per-PE slice of the all-zero row list is an all-zero lane list. -/
theorem parsedMatrixMAUPEValues_zero (precision : ParsedPrecision) (pe : Fin 4) :
    ((List.replicate (parsedMatrixMAURowCount precision) 0).drop
        (pe.val * parsedMatrixMAURowsPerPE precision)).take
        (parsedMatrixMAURowsPerPE precision)
      = List.replicate (parsedMatrixMAURowsPerPE precision) 0 := by
  rw [parsedMatrixMAURowCount_eq_four_mul, List.drop_replicate, List.take_replicate]
  have hle : pe.val * parsedMatrixMAURowsPerPE precision ≤
      3 * parsedMatrixMAURowsPerPE precision :=
    Nat.mul_le_mul_right _ (by have := pe.isLt; omega)
  have h1 : 4 * parsedMatrixMAURowsPerPE precision - 3 * parsedMatrixMAURowsPerPE precision
      = parsedMatrixMAURowsPerPE precision := by omega
  have hmin : parsedMatrixMAURowsPerPE precision ≤
      4 * parsedMatrixMAURowsPerPE precision - pe.val * parsedMatrixMAURowsPerPE precision := by
    omega
  rw [Nat.min_eq_left hmin]

/-- **The zero lane list packs into a zero-low bus.**  Only the non-round `.h`
layout has a nonzero low half in general, and it needs the low two lanes
(rows 2 and 3), which are zero here. -/
theorem parsedMatrixMAUPEOutput_zero_low (precision : ParsedPrecision) (round : Bool)
    (pe : Fin 4) (bus : IntegerALU.Bus) (flag : BitVec 4)
    (packed : parsedMatrixMAUPEOutput? precision round
      (List.replicate (parsedMatrixMAURowCount precision) 0) pe = some (bus, flag)) :
    bus.low = 0 := by
  unfold parsedMatrixMAUPEOutput? at packed
  dsimp only at packed
  rw [parsedMatrixMAUPEValues_zero precision pe] at packed
  cases precision <;> cases round <;>
    simp [parsedMatrixMAUFloatFormat, parsedMatrixMAURowsPerPE, parsedMatrixMAUPackPEBus?,
      parsedMatrixMAUFlags?, parsedMatrixMAUOutputFormat, parsedMatrixMAUPositive,
      RRN.floatIsNegative, Option.bind_eq_bind, Option.bind_some] at packed ⊢
  all_goals
    rw [← packed.1]

/-- **Packing preserves a zero low half.**  If every input bus has a zero low
half and the row list is the all-zero list, every bus of a successful
`parsedMatrixMAUPackOutputs` has a zero low half. -/
theorem parsedMatrixMAUPackOutputs_low_zero
    (precision : ParsedPrecision) (round flagsUnavailable : Bool)
    (rows : List Nat) (poison : Bool)
    (rowsZero : rows = List.replicate (parsedMatrixMAURowCount precision) 0)
    (pes : List (Fin 4)) (buses : Fin 4 → IntegerALU.Bus) (flags : Fin 4 → BitVec 4)
    (busesZero : ∀ pe, (buses pe).low = 0)
    (nextBuses : Fin 4 → IntegerALU.Bus) (nextFlags : Fin 4 → BitVec 4) (nextPoison : Bool) :
    parsedMatrixMAUPackOutputs precision round flagsUnavailable rows poison pes buses flags
      = .ok (nextBuses, nextFlags, nextPoison) →
    ∀ pe, (nextBuses pe).low = 0 := by
  induction pes generalizing buses flags with
  | nil =>
      intro executed
      rw [parsedMatrixMAUPackOutputs.eq_1] at executed
      obtain ⟨rfl, rfl, rfl⟩ := StepResult.ok.inj executed
      exact busesZero
  | cons pe rest ih =>
      intro executed
      rw [parsedMatrixMAUPackOutputs.eq_2] at executed
      cases packed : parsedMatrixMAUPEOutput? precision round rows pe with
      | none =>
          rw [packed] at executed
          simp at executed
      | some output =>
          obtain ⟨bus, flag⟩ := output
          rw [packed] at executed
          have busLow : bus.low = 0 := by
            rw [rowsZero] at packed
            exact parsedMatrixMAUPEOutput_zero_low precision round pe bus flag packed
          exact ih (fun index => if index == pe then bus else buses index)
            (fun index => if index == pe then (if flagsUnavailable then 0 else flag) else flags index)
            (fun index => by
              by_cases same : index == pe
              · simp only [same, ite_true]; exact busLow
              · simp only [same, ite_false]; exact busesZero index)
            executed

/-! ## 3. The datapath statement `WelcomePEMatrixMAUZeroBus`

A successful `executeParsedMatrixMAUAtMAB` at the all-zero state has zero rows
(§1c) and packs them with `parsedMatrixMAUPackOutputs`; §2 turns the zero rows
into zero-low buses.  The poison component of the pack result is the input
poison, so the pack hypothesis matches the low-half lemma. -/

theorem parsedMatrixMAUPackOutputs_poison
    (precision : ParsedPrecision) (round flagsUnavailable : Bool) (rows : List Nat) (poison : Bool)
    (pes : List (Fin 4)) (buses : Fin 4 → IntegerALU.Bus) (flags : Fin 4 → BitVec 4)
    (nextBuses : Fin 4 → IntegerALU.Bus) (nextFlags : Fin 4 → BitVec 4) (nextPoison : Bool) :
    parsedMatrixMAUPackOutputs precision round flagsUnavailable rows poison pes buses flags
      = .ok (nextBuses, nextFlags, nextPoison) → nextPoison = poison := by
  induction pes generalizing buses flags with
  | nil =>
      intro executed
      rw [parsedMatrixMAUPackOutputs.eq_1] at executed
      obtain ⟨rfl, rfl, rfl⟩ := StepResult.ok.inj executed
      rfl
  | cons pe rest ih =>
      intro executed
      rw [parsedMatrixMAUPackOutputs.eq_2] at executed
      cases packed : parsedMatrixMAUPEOutput? precision round rows pe with
      | none => rw [packed] at executed; simp at executed
      | some output =>
          obtain ⟨bus, flag⟩ := output
          rw [packed] at executed
          exact ih _ _ executed

theorem welcomePEMatrixMAUZeroBus : WelcomePEMatrixMAUZeroBus := by
  intro coordinate expression cycle buses flags poison executed pe
  unfold executeParsedMatrixMAUAtMAB at executed
  cases calculation : executeParsedMatrixMAUCalculationAtMAB (welcomeInitialState welcomeZeroWords)
      coordinate expression cycle with
  | failure => simp [calculation] at executed
  | unknown => simp [calculation] at executed
  | ok result =>
    obtain ⟨rows, poison', flagsUnavailable⟩ := result
    simp only [calculation] at executed
    obtain ⟨precision, kind, half, round, opEq, rowsZero⟩ :=
      executeParsedMatrixMAUCalculationAtMAB_zero_rows coordinate expression.op expression.sources
        expression.destinations expression.flush expression.text cycle rows poison' flagsUnavailable
        calculation
    rw [opEq] at executed
    simp only at executed
    have poisonEq : poison = poison' :=
      parsedMatrixMAUPackOutputs_poison precision round flagsUnavailable rows poison'
        (List.finRange 4) (fun _ => ⟨0, 0⟩) (fun _ => 0) buses flags poison executed
    rw [← poisonEq] at executed
    exact parsedMatrixMAUPackOutputs_low_zero precision round flagsUnavailable rows poison rowsZero
      (List.finRange 4) (fun _ => ⟨0, 0⟩) (fun _ => 0) (fun _ => rfl) buses flags poison executed pe

end ProofsLean.MNCore
