import ProofsLean.CendValueFamilies

/-! # `12.convert-endian`: the block-float and matrix-MAU value families

`ProofsLean/CendValueFamilies.lean` closed the `msl`/`msr` family and left the
block-float and matrix-MAU families in `CendMslMsrResidual`.  This module applies
the same recipe to the two remaining float families and states their narrowed
residual.

## What is proved here

* §1 — **target avoidance via the generating list**: `0x08070605` is in
  `cendMixWords L` iff some `hi ∈ L` has high half `0x0807` and some `lo ∈ L`
  has low half `0x0605` (and independently for `0x04030201`).  The kernel checks
  therefore run over `L` (linear), not over the quadratic closure.
* §2 — the **block-float generating list** at `cendWitness`: the high-word
  halves of `parsedBlockFloatMab p keep extended buses` for every admissible
  `(p, keep, extended)` and every constant initial bus / fixed-source pattern of
  the observed MAB.  The target halves are kernel-checked absent
  (`cendBlockFloatWords_avoid`).
* §3 — the **matrix-MAU generating list**: the zero-store zero-row packs for
  every precision, round and lane, and the `.fma` packs of every PE-read
  accumulator lane list of the ten initial buses under the eight float-attribute
  combinations.  The target halves are kernel-checked absent
  (`cendMatrixMAUWords_avoid`).
* §4 — the **prepared-write data bridge**:
  `writeParsedMslMsrDestination?_data_mixWords` turns high-word halves of the
  stage output into `cendMixWords` data of the prepared write, and
  `executeParsedBlockFloatAtMAB_apply_data` carries it through the block-float
  destination fold (commit equation, data membership and LM1 alignment).  The
  per-cycle PE fold `executeParsedBlockFloatAtMAB_writePEs_data` and the
  four-cycle fold `executeParsedBlockFloatAtMAB_runCycles_data` compose this
  through the rest of the block-float stage.
* §4b — the **constant-read value theorems**:
  `cendBlockFloatHigh_mem`, `cendBlockFloatConstantBuses_data`,
  `executeParsedBlockFloatAtMAB_apply_data_constant` and
  `commitParsedMaskedWrites_lm1_blockFloat_constant` connect the concrete list
  members to the observed LM1 word for a constant four-lane read vector.
* §5 — the **two row classes**, their family facts, the narrowed residual
  `CendMatrixFamiliesResidual`, the exact split
  `cendMslMsrResidual_iff_matrixFamiliesResidual`, and the reductions
  `cendMixedReadResidual_of_matrixFamiliesResidual` and
  `cendLowerBound_two_of_matrixFamiliesResidual` to
  `LowerBound cendSealedMachine cendSpec 2`.
* §6 — **non-vacuity witnesses**: concrete lines in each new class.

## What is *not* closed here

The two line-level refutations are stated as the `Prop`s
`CendBlockFloatLinesRefuted` and `CendMatrixMAULinesRefuted`; they are *not*
proved in this module and are not assumed by any unconditional theorem.  What
remains for each is the same two-step argument as for `msl`/`msr`:

1. the **four-lane source provenance** at the observed MAB: a `.mem` source
   differs between the four lanes only by the `madpe` address prefix (so the
   read vector is a prefix pattern of two initial buses), while a `.fixed`
   source yields one of the six fixed patterns — the generating list currently
   covers the constant vectors and the fixed patterns;
2. the **data-carrying MAB/stage chain and line assembly**: the destination
   fold, the per-cycle PE fold (`executeParsedBlockFloatAtMAB_writePEs_data`)
   and the four-cycle fold (`executeParsedBlockFloatAtMAB_runCycles_data`) are
   proved for block float, but the MAB walk and the line assembly (which must
   also frame the integer, `msl`/`msr`, relu, matrix, shared-block and L1BM
   stages) are not carried out here.

Coverage caveats of the two lists: the block-float list enumerates `.h` keeps
`0…10` only, and both lists use **constant** four-lane read vectors (the fixed
patterns are included for block float), so `.mem` reads whose `madpe` prefix
makes the four lanes differ are not covered yet.

The matrix-MAU destination fold is not carried out here either; it uses the same
`writeParsedMslMsrDestination?` bridge (`writeParsedMslMsrDestination?_data_mixWords`)
but has to discharge the poison gate and the `.omr` entry check.

No `sorry`, no `admit`, no `native_decide`, no `bv_decide`, no new axioms, and
no existing module is edited.
-/

namespace ProofsLean.MNCore

open Issue
open PEMemory

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false

/-! ## 1. Target avoidance via the generating list -/

/-- **No list word carries a forbidden half.**  The check is the conjunction of
the high-half test for `hi` and the low-half test for `lo`. -/
def CendHalvesAbsent (L : List (BitVec 32)) (hi lo : BitVec 32) : Bool :=
  L.all fun word =>
    (word &&& 0xffff0000 != (hi &&& 0xffff0000)) &&
      (word &&& 0x0000ffff != (lo &&& 0x0000ffff))

theorem cendHalvesAbsent_high {L : List (BitVec 32)} {hi lo : BitVec 32}
    (check : CendHalvesAbsent L hi lo = true) {word : BitVec 32} (member : word ∈ L) :
    word &&& 0xffff0000 ≠ hi &&& 0xffff0000 := by
  have perWord := List.all_eq_true.mp check word member
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at perWord
  exact perWord.1

theorem cendHalvesAbsent_low {L : List (BitVec 32)} {hi lo : BitVec 32}
    (check : CendHalvesAbsent L hi lo = true) {word : BitVec 32} (member : word ∈ L) :
    word &&& 0x0000ffff ≠ lo &&& 0x0000ffff := by
  have perWord := List.all_eq_true.mp check word member
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at perWord
  exact perWord.2

/-- **The high target is outside the closure.** -/
theorem cendMixWords_ne_of_halves {L : List (BitVec 32)} {hi lo : BitVec 32}
    (check : CendHalvesAbsent L hi lo = true) :
    hi ∉ cendMixWords L := by
  intro member
  obtain ⟨a, ha, b, hb, hword⟩ := cendMixWords_exists member
  have hEq : a &&& 0xffff0000 = hi &&& 0xffff0000 := by
    rw [hword, cendHalfMix_high]
  exact cendHalvesAbsent_high check ha hEq

/-- **The low target is outside the closure.** -/
theorem cendMixWords_ne_target_low_of_halves {L : List (BitVec 32)} {hi lo : BitVec 32}
    (check : CendHalvesAbsent L hi lo = true) :
    lo ∉ cendMixWords L := by
  intro member
  obtain ⟨a, ha, b, hb, hword⟩ := cendMixWords_exists member
  have hEq : b &&& 0x0000ffff = lo &&& 0x0000ffff := by
    rw [hword, cendHalfMix_low]
  exact cendHalvesAbsent_low check hb hEq

theorem cendHalvesAbsent_of_subset {L M : List (BitVec 32)} {hi lo : BitVec 32}
    (subset : ∀ word ∈ L, word ∈ M) (check : CendHalvesAbsent M hi lo = true) :
    CendHalvesAbsent L hi lo = true := by
  unfold CendHalvesAbsent
  rw [List.all_eq_true]
  intro word member
  have perWord := List.all_eq_true.mp check word (subset word member)
  simpa using perWord

/-! ## 2. The block-float generating list -/

/-- The high word of the block-float output of the observed lane, read off the
five local parameters of `parsedBlockFloat`'s map. -/
def cendBlockFloatLane (precision : RRN.FloatPrecision) (keep : Nat) (extended : Bool)
    (maxExponent common value : Nat) : Nat :=
  let mantissaBits := precision.mantissaBits
  let exponentMax := precision.exponentMax
  let width := precision.width
  let dropped := mantissaBits - keep
  let exponent (value : Nat) := value / 2 ^ mantissaBits % 2 ^ precision.exponentBits
  let mantissa (value : Nat) := value % 2 ^ mantissaBits
  let sign (value : Nat) := value / 2 ^ (width - 1) % 2 * 2 ^ (width - 1)
  let topOnes (value : Nat) := mantissa value / 2 ^ dropped == 2 ^ keep - 1
  if common >= exponentMax then
    sign value + exponentMax * 2 ^ mantissaBits
  else if maxExponent == 0 then sign value
  else if exponent value == 0 then
    if extended then sign value else sign value + common * 2 ^ mantissaBits
  else
    let distance := common - exponent value
    let extendedFlag := extended &&
      (distance > 6 + dropped || (distance == 6 + dropped && !topOnes value))
    let shift := (if extendedFlag then distance - 6 else distance) + 1 +
      (if precision == .half then 0 else dropped)
    let rounded := RRN.roundShift (2 ^ mantissaBits + mantissa value) shift
    let resultMantissa := if precision == .half then rounded else rounded * 2 ^ dropped
    if resultMantissa == 0 then
      if extended then sign value else sign value + common * 2 ^ mantissaBits
    else
      sign value + (if extendedFlag then 0 else common) * 2 ^ mantissaBits +
        resultMantissa % 2 ^ mantissaBits

/-- The block maximum of a lane list (the `maxExponent` local of
`parsedBlockFloat`). -/
def cendBlockFloatMax (precision : RRN.FloatPrecision) (values : List Nat) : Nat :=
  (values.map (RRN.floatExponent precision)).foldl Nat.max 0

/-- The `common` exponent local of `parsedBlockFloat`. -/
def cendBlockFloatCommon (precision : RRN.FloatPrecision) (keep : Nat)
    (values : List Nat) : Nat :=
  cendBlockFloatMax precision values +
    (if values.any fun value =>
      RRN.floatExponent precision value == cendBlockFloatMax precision values &&
        value % 2 ^ precision.mantissaBits / 2 ^ (precision.mantissaBits - keep) ==
          2 ^ keep - 1 then 1 else 0) +
    (if precision == .half then precision.mantissaBits - keep else 0)

/-- **`parsedBlockFloat` is the map of `cendBlockFloatLane`.** -/
theorem parsedBlockFloat_eq_map_lane (precision : RRN.FloatPrecision) (keep : Nat)
    (extended : Bool) (values : List Nat) :
    parsedBlockFloat precision values keep extended =
      values.map fun value =>
        cendBlockFloatLane precision keep extended (cendBlockFloatMax precision values)
          (cendBlockFloatCommon precision keep values) value := by
  rfl

/-- The `(precision, keep, extended)` triples of `bfn`/`bfe` covered by the
generating list.  For `.h` the `keep` operand may be any `Fin 256`; the list
enumerates `keep = 0…10` (the reduction of `keep > 10` to `keep = 10` is not
formalized in this module). -/
def cendBlockFloatCases : List (ParsedPrecision × Nat × Bool) :=
  [(.d, 52, false), (.f, 23, false), (.g, 18, false)] ++
    (List.range 11).flatMap fun keep =>
      [(.h, keep, false), (.h, keep, true)]

/-- The high word of the block-float output at the observed lane. -/
def cendBlockFloatHigh (precision : ParsedPrecision) (keep : Nat) (extended : Bool)
    (buses : Fin 4 → IntegerALU.Bus) : BitVec 64 :=
  (parsedBlockFloatMab precision keep extended buses 0).high

/-- The six fixed-source input vectors of the observed MAB. -/
def cendBlockFloatFixedInputs (precision : ParsedPrecision) : List (Fin 4 → IntegerALU.Bus) :=
  [ParsedFixed.l2bid, .l1bid, .mabid, .peid, .subpeid, .msb1].map fun fixed =>
    fun lane =>
      let peId := physicalPEId (⟨0, 0, 0, 0⟩ : MABCoordinate) lane
      let context := ParsedIntegerContext.ofLinearIndex peId
      replicateIntegerLane precision.laneWidth
        (ParsedFixed.integerValue fixed precision.laneWidth context.group context.l2b
          context.l1b context.mab context.pe)

/-- **The generating list of the block-float family at `cendWitness`**: the
halves of the high word for every admissible triple, every bus of the ten-bus
initial family (constant four-lane read vector) and every fixed-source pattern
of the observed MAB. -/
def cendBlockFloatWords : List (BitVec 32) :=
  0 :: cendBlockFloatCases.flatMap fun triple =>
    ((cendInitialBuses cendWitness).map (fun bus _ => bus) ++
      cendBlockFloatFixedInputs triple.1).flatMap fun buses =>
      let high := cendBlockFloatHigh triple.1 triple.2.1 triple.2.2 buses
      [high.extractLsb' 32 32, high.extractLsb' 0 32]

/-- The target words are absent from the block-float generating list. -/
theorem cendBlockFloatWords_avoid :
    CendHalvesAbsent cendBlockFloatWords 0x08070605 0x04030201 = true := by
  decide

theorem cendBlockFloatWords_target_high_avoid :
    (0x08070605 : BitVec 32) ∉ cendMixWords cendBlockFloatWords :=
  cendMixWords_ne_of_halves cendBlockFloatWords_avoid

theorem cendBlockFloatWords_target_low_avoid :
    (0x04030201 : BitVec 32) ∉ cendMixWords cendBlockFloatWords :=
  cendMixWords_ne_target_low_of_halves cendBlockFloatWords_avoid



/-! ## 3. The matrix-MAU generating list

With the all-zero matrix store of `cendInitialState`, `matrixBlockFloatDot`
returns the zero value on its early `commonA == 0` branch for every vector read,
so the calculated rows are the accumulator rows alone: `0` for the kinds
`.mul`/`.add`/`.passa`, and `encodeMAUValue (decodeMAUValue accBits)` of the
PE-read accumulator lanes for `.fma`.  Matrix-MAU sources are `.mem`/`.forward`
only (`parsedFloatMAUSourceAttrs?`), and at the initial state every `.mem` read
is one of the ten initial buses while every `.forward` read fails.  The observed
write only needs data words `0`/`1`, i.e. the high word of the packed output
bus. -/

/-- The zero matrix store of the initial state. -/
def cendZeroMatrixStore : PEMemory.ParsedMatrixReadStore := fun _ _ _ _ => 0

/-- The zero row list of a precision (the non-`.fma` row result at the zero
store). -/
def cendMatrixMAUZeroRows (precision : ParsedPrecision) : List Nat :=
  List.replicate (parsedMatrixMAURowCount precision) 0

/-- The accumulator lane lists a PE read of `bus` can hand to matrix MAU. -/
def cendMatrixMAUAccumulatorValues (precision : ParsedPrecision) (bus : IntegerALU.Bus)
    (negate extend round : Bool) : List (List Nat) :=
  match parsedMatrixMAUDecodeLanes? (parsedMatrixMAUAccumulatorFormat precision)
      (parsedMatrixMAUAccumulatorLanesPerPE precision) bus negate extend round with
  | none => []
  | some lanes => [lanes]

/-- The rows a `.fma` calculation can produce at the zero store from one
accumulator lane list. -/
def cendMatrixMAUFmaRows (precision : ParsedPrecision) (half : Option Char) (round : Bool)
    (accumulator : List Nat) : Option (List Nat) :=
  parsedMatrixMAUCalculateRows? cendZeroMatrixStore
    (⟨0, 0, 0, 0⟩ : MABCoordinate) false precision .fma half round
    (List.replicate (4 * parsedMatrixMAUVectorLanesPerPE precision) 0) accumulator

/-- The four-PE accumulator lane lists of a constant memory read bus, for the
eight attribute combinations the float lowering can produce. -/
def cendMatrixMAUFmaAccumulators (precision : ParsedPrecision)
    (bus : IntegerALU.Bus) : List (List Nat) :=
  [false, true].flatMap fun negate =>
    [false, true].flatMap fun extend =>
      [false, true].flatMap fun round =>
        (cendMatrixMAUAccumulatorValues precision bus negate extend round).map
          fun lanes => lanes ++ lanes ++ lanes ++ lanes

/-- The two halves of a packed bus's high word, or the empty list on failure. -/
def cendMatrixMAUHighHalves (packed : Option (IntegerALU.Bus × BitVec 4)) : List (BitVec 32) :=
  match packed with
  | none => []
  | some (out, _) => [out.high.extractLsb' 32 32, out.high.extractLsb' 0 32]

/-- The precision indexed by `0…3` (`.d`, `.f`, `.g`, `.h`). -/
def cendMatrixMAUPrecision (index : Nat) : ParsedPrecision :=
  match index with
  | 0 => .d
  | 1 => .f
  | 2 => .g
  | _ => .h

/-- **The generating list of the matrix-MAU family at `cendWitness`.** -/
def cendMatrixMAUWords : List (BitVec 32) :=
  0 :: (List.range 4).flatMap fun precisionIndex =>
    let precision := cendMatrixMAUPrecision precisionIndex
    [false, true].flatMap fun round =>
      ((List.finRange 4).flatMap fun pe =>
        cendMatrixMAUHighHalves
          (parsedMatrixMAUPEOutput? precision round (cendMatrixMAUZeroRows precision) pe)) ++
      [false, true].flatMap fun halfUpper =>
        (cendInitialBuses cendWitness).flatMap fun bus =>
          (cendMatrixMAUFmaAccumulators precision bus).flatMap fun accumulator =>
            match cendMatrixMAUFmaRows precision (if halfUpper then some 'u' else none)
                round accumulator with
            | none => []
            | some rows =>
              (List.finRange 4).flatMap fun pe =>
                cendMatrixMAUHighHalves (parsedMatrixMAUPEOutput? precision round rows pe)

/-- The target words are absent from the matrix-MAU generating list. -/
theorem cendMatrixMAUWords_avoid :
    CendHalvesAbsent cendMatrixMAUWords 0x08070605 0x04030201 = true := by
  decide

theorem cendMatrixMAUWords_target_high_avoid :
    (0x08070605 : BitVec 32) ∉ cendMixWords cendMatrixMAUWords :=
  cendMixWords_ne_of_halves cendMatrixMAUWords_avoid

theorem cendMatrixMAUWords_target_low_avoid :
    (0x04030201 : BitVec 32) ∉ cendMixWords cendMatrixMAUWords :=
  cendMixWords_ne_target_low_of_halves cendMatrixMAUWords_avoid


/-! ## 4. The prepared-write data of the two families

`writeParsedMslMsrDestination?_dataAligned` (from `CendValueFamilies`) already
proves that every destination lowering of the shared writer commits exactly one
prepared write whose data bus is the (already flushed) output and whose LM1
destinations are aligned.  The only family-specific input is therefore the
**high-word halves** of the output bus: `unpackALUBus` at indices `0`/`1` reads
those two halves, and `commitParsedMaskedWrites_lm1_mixWords` keeps the observed
LM1 word in the closure of any list containing them. -/

/-- **The first two data words of a bus whose high halves are list members.** -/
theorem unpackALUBus_mixWords_of_high_mem {L : List (BitVec 32)}
    {bus : IntegerALU.Bus}
    (h0 : bus.high.extractLsb' 32 32 ∈ L) (h1 : bus.high.extractLsb' 0 32 ∈ L) :
    ∀ (i : Fin 4), i.val < 2 → unpackALUBus bus i ∈ cendMixWords L := by
  intro i hi
  have hi01 : i.val = 0 ∨ i.val = 1 := by omega
  rcases hi01 with h | h
  · have hindex : i = (⟨0, by decide⟩ : Fin 4) := Fin.ext h
    subst hindex
    simpa [PEMemory.unpackALUBus] using cendMixWords_of_mem h0
  · have hindex : i = (⟨1, by decide⟩ : Fin 4) := Fin.ext h
    subst hindex
    simpa [PEMemory.unpackALUBus] using cendMixWords_of_mem h1

/-- **A prepared write of the shared destination writer carries closure data.** -/
theorem writeParsedMslMsrDestination?_data_mixWords {L : List (BitVec 32)}
    (files : IntegerRegisterFiles) (destination : ParsedOperand)
    (context : ParsedIntegerContext) (output : IntegerALU.Bus) (flags : BitVec 4)
    (cycle : Fin 4) (directive : ParsedMaskDirective) (hasSingleLineMask : Bool)
    (write : ParsedMslMsrDestinationWrite)
    (hData : ∀ (i : Fin 4), i.val < 2 → unpackALUBus output i ∈ cendMixWords L)
    (lowered : writeParsedMslMsrDestination? files destination context output flags cycle
      directive hasSingleLineMask = some write) :
    ∃ prepared : PreparedParsedMaskedWrite,
      write.files = commitParsedMaskedWrites files [prepared] ∧
      prepared.data = unpackALUBus output ∧
      (∀ (i : Fin 4), i.val < 2 → prepared.data i ∈ cendMixWords L) ∧
      (∀ (width : PEMemory.Width) (address : Fin Bank.lm1.capacity),
        prepared.destination = some ⟨Bank.lm1, width, address⟩ →
          address.val % PEMemory.count Bank.lm1 width = 0) := by
  obtain ⟨prepared, committed, dataEq, aligned⟩ :=
    writeParsedMslMsrDestination?_dataAligned files destination context output flags cycle
      directive hasSingleLineMask write lowered
  refine ⟨prepared, committed, dataEq, ?_, aligned⟩
  intro i hi
  rw [dataEq]
  exact hData i hi

/-- **The block-float destination fold keeps the commit equation, the closure
data and the alignment.** -/
theorem executeParsedBlockFloatAtMAB_apply_data {L : List (BitVec 32)}
    (currentState : State) (hasSingleLineMask : Bool) (cycle : Fin 4)
    (output : IntegerALU.Bus) (oldContext coords : ParsedIntegerContext)
    (hData : ∀ (i : Fin 4), i.val < 2 → unpackALUBus output i ∈ cendMixWords L) :
    ∀ (destinations : List ParsedOperand) (files : IntegerRegisterFiles) (bar0 bar1 : BitVec 12)
      (nextFiles : IntegerRegisterFiles) (nextBar0 nextBar1 : BitVec 12),
      executeParsedBlockFloatAtMAB.apply currentState hasSingleLineMask cycle output oldContext
        coords destinations files bar0 bar1 = .ok (nextFiles, nextBar0, nextBar1) →
      ∃ writes : List PreparedParsedMaskedWrite,
        nextFiles = commitParsedMaskedWrites files writes ∧
        (∀ write ∈ writes, ∀ (i : Fin 4), i.val < 2 →
          write.data i ∈ cendMixWords L) ∧
        (∀ write ∈ writes, ∀ (width : PEMemory.Width) (address : Fin Bank.lm1.capacity),
          write.destination = some ⟨Bank.lm1, width, address⟩ →
            address.val % PEMemory.count Bank.lm1 width = 0) := by
  intro destinations
  induction destinations with
  | nil =>
      intro files bar0 bar1 nextFiles nextBar0 nextBar1 executed
      rw [executeParsedBlockFloatAtMAB.apply.eq_1] at executed
      obtain ⟨rfl, rfl, rfl⟩ := StepResult.ok.inj executed
      exact ⟨[], rfl, by intro write member; simp at member,
        by intro write member; simp at member⟩
  | cons destination rest ih =>
      intro files bar0 bar1 nextFiles nextBar0 nextBar1 executed
      rw [executeParsedBlockFloatAtMAB.apply.eq_2] at executed
      dsimp only at executed
      cases lowered : writeParsedMslMsrDestination? files destination
          { coords with cycle := cycle, bar0 := bar0, bar1 := bar1, tWord := oldContext.tWord }
          output 0 cycle currentState.maskDirective hasSingleLineMask with
      | none =>
          rw [lowered] at executed
          simp at executed
      | some write =>
          rw [lowered] at executed
          obtain ⟨prepared, committed, dataEq, dataOk, aligned⟩ :=
            writeParsedMslMsrDestination?_data_mixWords files destination
              { coords with cycle := cycle, bar0 := bar0, bar1 := bar1, tWord := oldContext.tWord }
              output 0 cycle currentState.maskDirective hasSingleLineMask write hData lowered
          obtain ⟨restWrites, restCommit, restData, restAligned⟩ :=
            ih write.files
              (match write.barUpdate with
               | some (false, value) => value
               | _ => bar0)
              (match write.barUpdate with
               | some (true, value) => value
               | _ => bar1)
              nextFiles nextBar0 nextBar1 executed
          refine ⟨prepared :: restWrites, ?_, ?_, ?_⟩
          · rw [restCommit, committed,
              show (prepared :: restWrites) = [prepared] ++ restWrites from rfl,
              commitParsedMaskedWrites_append]
          · intro item member i hi
            rcases List.mem_cons.mp member with rfl | later
            · exact dataOk i hi
            · exact restData item later i hi
          · intro item member width address dest
            rcases List.mem_cons.mp member with rfl | later
            · exact aligned width address dest
            · exact restAligned item later width address dest





/-- **The block-float per-cycle PE fold keeps the commit equation and the
closure data.**  `writeDestinations` is the shared destination writer of the
executor; the hypothesis is its data theorem (supplied by
`executeParsedBlockFloatAtMAB_apply_data` at the concrete definitional form). -/
theorem executeParsedBlockFloatAtMAB_writePEs_data {L : List (BitVec 32)}
    (expression : ParsedExpr)
    (writeDestinations : Fin 4 → Fin 4 → IntegerALU.Bus → IntegerRegisterFiles →
      BitVec 12 → BitVec 12 → StepResult (IntegerRegisterFiles × BitVec 12 × BitVec 12))
    (writeData : ∀ (pe : Fin 4) (cycle : Fin 4) (output : IntegerALU.Bus)
      (files : IntegerRegisterFiles) (bar0 bar1 : BitVec 12)
      (nextFiles : IntegerRegisterFiles) (nextBar0 nextBar1 : BitVec 12),
      (∀ (i : Fin 4), i.val < 2 → unpackALUBus output i ∈ cendMixWords L) →
      writeDestinations pe cycle output files bar0 bar1 = .ok (nextFiles, nextBar0, nextBar1) →
      ∃ writes : List PreparedParsedMaskedWrite,
        nextFiles = commitParsedMaskedWrites files writes ∧
        (∀ write ∈ writes, ∀ (i : Fin 4), i.val < 2 →
          write.data i ∈ cendMixWords L) ∧
        (∀ write ∈ writes, ∀ (width : PEMemory.Width) (address : Fin Bank.lm1.capacity),
          write.destination = some ⟨Bank.lm1, width, address⟩ →
            address.val % PEMemory.count Bank.lm1 width = 0))
    (cycle : Fin 4) (buses : Fin 4 → IntegerALU.Bus)
    (busesHigh : ∀ pe : Fin 4, (buses pe).high.extractLsb' 32 32 ∈ L ∧
      (buses pe).high.extractLsb' 0 32 ∈ L)
    (hz : (0 : BitVec 32) ∈ L) (target : Fin 4) :
    ∀ (pes : List (Fin 4)) (files : Fin 4 → IntegerRegisterFiles)
      (bar0 bar1 : Fin 4 → BitVec 12)
      (outputs : Fin 4 → Fin 4 → IntegerALU.Bus)
      (results : Fin 4 → IntegerRegisterFiles × BitVec 12 × BitVec 12 × (Fin 4 → IntegerALU.Bus)),
      executeParsedBlockFloatAtMAB.writePEs expression writeDestinations cycle buses pes files
        bar0 bar1 outputs = .ok results →
      ∃ writes : List PreparedParsedMaskedWrite,
        (results target).1 = commitParsedMaskedWrites (files target) writes ∧
        (∀ write ∈ writes, ∀ (i : Fin 4), i.val < 2 →
          write.data i ∈ cendMixWords L) ∧
        (∀ write ∈ writes, ∀ (width : PEMemory.Width) (address : Fin Bank.lm1.capacity),
          write.destination = some ⟨Bank.lm1, width, address⟩ →
            address.val % PEMemory.count Bank.lm1 width = 0) := by
  intro pes
  induction pes with
  | nil =>
      intro files bar0 bar1 outputs results executed
      rw [executeParsedBlockFloatAtMAB.writePEs.eq_1] at executed
      obtain rfl := StepResult.ok.inj executed
      exact ⟨[], rfl, by intro write member; simp at member,
        by intro write member; simp at member⟩
  | cons pe rest ih =>
      intro files bar0 bar1 outputs results executed
      rw [executeParsedBlockFloatAtMAB.writePEs.eq_2] at executed
      dsimp only at executed
      cases flush : resolveFlushSelection? expression.flush (files pe).maskRegisters cycle with
      | none =>
          rw [flush] at executed
          simp at executed
      | some flushSelection =>
          rw [flush] at executed
          dsimp only at executed
          cases wrote : writeDestinations pe cycle
              (parsedOutputAfterFlush flushSelection (buses pe)) (files pe) (bar0 pe) (bar1 pe) with
          | failure =>
              rw [wrote] at executed
              simp at executed
          | unknown =>
              rw [wrote] at executed
              simp at executed
          | ok result =>
              rw [wrote] at executed
              dsimp only at executed
              obtain ⟨nextPEFiles, nextBar0, nextBar1⟩ := result
              have flushData : ∀ (i : Fin 4), i.val < 2 →
                  unpackALUBus (parsedOutputAfterFlush flushSelection (buses pe)) i ∈
                    cendMixWords L :=
                cendOutputAfterFlush_data_mixWords (busesHigh pe).1 (busesHigh pe).2 hz
                  flushSelection
              obtain ⟨headWrites, headCommit, headData, headAligned⟩ :=
                writeData pe cycle _ _ _ _ nextPEFiles nextBar0 nextBar1 flushData wrote
              obtain ⟨tailWrites, tailCommit, tailData, tailAligned⟩ :=
                ih (fun other => if other == pe then nextPEFiles else files other)
                  (fun other => if other == pe then nextBar0 else bar0 other)
                  (fun other => if other == pe then nextBar1 else bar1 other)
                  (fun other index =>
                    if other == pe && index == cycle then
                      parsedOutputAfterFlush flushSelection (buses pe)
                    else outputs other index)
                  results executed
              by_cases same : target = pe
              · subst same
                refine ⟨headWrites ++ tailWrites, ?_, ?_, ?_⟩
                · rw [tailCommit, headCommit, commitParsedMaskedWrites_append]
                  simp only [beq_iff_eq, ite_true]
                · intro item member i hi
                  rcases List.mem_append.mp member with head | tail
                  · exact headData item head i hi
                  · exact tailData item tail i hi
                · intro item member width address dest
                  rcases List.mem_append.mp member with head | tail
                  · exact headAligned item head width address dest
                  · exact tailAligned item tail width address dest
              · have different : (target == pe) = false := by
                  simp [beq_iff_eq, same]
                refine ⟨tailWrites, ?_, tailData, tailAligned⟩
                rw [tailCommit]
                simp [different]


/-- **The block-float four-cycle fold keeps the commit equation and the closure
data.** -/
theorem executeParsedBlockFloatAtMAB_runCycles_data {L : List (BitVec 32)}
    (accesses : ParsedBlockFloatAccesses)
    (readCycle : Fin 4 → StepResult (Fin 4 → IntegerALU.Bus))
    (writeCycle : Fin 4 → (Fin 4 → IntegerALU.Bus) → (Fin 4 → IntegerRegisterFiles) →
      (Fin 4 → BitVec 12) → (Fin 4 → BitVec 12) → (Fin 4 → Fin 4 → IntegerALU.Bus) →
      StepResult (Fin 4 → IntegerRegisterFiles × BitVec 12 × BitVec 12 × (Fin 4 → IntegerALU.Bus)))
    (writeCycleData : ∀ (cycle : Fin 4) (buses : Fin 4 → IntegerALU.Bus)
      (files : Fin 4 → IntegerRegisterFiles) (bar0 bar1 : Fin 4 → BitVec 12)
      (outputs : Fin 4 → Fin 4 → IntegerALU.Bus)
      (results : Fin 4 → IntegerRegisterFiles × BitVec 12 × BitVec 12 × (Fin 4 → IntegerALU.Bus)),
      (∀ pe : Fin 4, (buses pe).high.extractLsb' 32 32 ∈ L ∧
        (buses pe).high.extractLsb' 0 32 ∈ L) →
      writeCycle cycle buses files bar0 bar1 outputs = .ok results →
      ∃ writes : List PreparedParsedMaskedWrite,
        (results (0 : Fin 4)).1 = commitParsedMaskedWrites (files (0 : Fin 4)) writes ∧
        (∀ write ∈ writes, ∀ (i : Fin 4), i.val < 2 →
          write.data i ∈ cendMixWords L) ∧
        (∀ write ∈ writes, ∀ (width : PEMemory.Width) (address : Fin Bank.lm1.capacity),
          write.destination = some ⟨Bank.lm1, width, address⟩ →
            address.val % PEMemory.count Bank.lm1 width = 0))
    (inputHigh : ∀ (cycle : Fin 4) (buses : Fin 4 → IntegerALU.Bus),
      readCycle cycle = .ok buses →
      ∀ pe : Fin 4,
        (parsedBlockFloatMab accesses.precision accesses.keep accesses.extended buses pe).high.extractLsb'
            32 32 ∈ L ∧
          (parsedBlockFloatMab accesses.precision accesses.keep accesses.extended buses pe).high.extractLsb'
            0 32 ∈ L) :
    ∀ (cycles : List (Fin 4)) (files : Fin 4 → IntegerRegisterFiles)
      (bar0 bar1 : Fin 4 → BitVec 12)
      (outputs : Fin 4 → Fin 4 → IntegerALU.Bus)
      (results : Fin 4 → IntegerRegisterFiles × BitVec 12 × BitVec 12 × (Fin 4 → IntegerALU.Bus)),
      executeParsedBlockFloatAtMAB.runCycles accesses readCycle writeCycle cycles files bar0 bar1
        outputs = .ok results →
      ∃ writes : List PreparedParsedMaskedWrite,
        (results (0 : Fin 4)).1 = commitParsedMaskedWrites (files (0 : Fin 4)) writes ∧
        (∀ write ∈ writes, ∀ (i : Fin 4), i.val < 2 →
          write.data i ∈ cendMixWords L) ∧
        (∀ write ∈ writes, ∀ (width : PEMemory.Width) (address : Fin Bank.lm1.capacity),
          write.destination = some ⟨Bank.lm1, width, address⟩ →
            address.val % PEMemory.count Bank.lm1 width = 0) := by
  intro cycles
  induction cycles with
  | nil =>
      intro files bar0 bar1 outputs results executed
      rw [executeParsedBlockFloatAtMAB.runCycles.eq_1] at executed
      obtain rfl := StepResult.ok.inj executed
      exact ⟨[], rfl, by intro write member; simp at member,
        by intro write member; simp at member⟩
  | cons cycle rest ih =>
      intro files bar0 bar1 outputs results executed
      rw [executeParsedBlockFloatAtMAB.runCycles.eq_2] at executed
      dsimp only at executed
      split at executed
      · simp at executed
      · simp at executed
      · rename_i inputBuses ranRead
        split at executed
        · simp at executed
        · simp at executed
        · rename_i results' ranWrite
          obtain ⟨headWrites, headCommit, headData, headAligned⟩ :=
            writeCycleData cycle
              (parsedBlockFloatMab accesses.precision accesses.keep accesses.extended inputBuses)
              files bar0 bar1 outputs results' (inputHigh cycle inputBuses ranRead) ranWrite
          have tail := ih (fun pe => (results' pe).1) (fun pe => (results' pe).2.1)
            (fun pe => (results' pe).2.2.1) (fun pe index => (results' pe).2.2.2 index)
            results executed
          obtain ⟨tailWrites, tailCommit, tailData, tailAligned⟩ := tail
          refine ⟨headWrites ++ tailWrites, ?_, ?_, ?_⟩
          · rw [tailCommit, headCommit, commitParsedMaskedWrites_append]
          · intro item member i hi
            rcases List.mem_append.mp member with head | tail
            · exact headData item head i hi
            · exact tailData item tail i hi
          · intro item member width address dest
            rcases List.mem_append.mp member with head | tail
            · exact headAligned item head width address dest
            · exact tailAligned item tail width address dest


/-! ### 4b. The constant-read value theorems -/

/-- **The block-float generating list contains every constant-read output.** -/
theorem cendBlockFloatHigh_mem {precision : ParsedPrecision} {keep : Nat} {extended : Bool}
    (htriple : (precision, keep, extended) ∈ cendBlockFloatCases)
    {buses : Fin 4 → IntegerALU.Bus}
    (hbuses : buses ∈ (cendInitialBuses cendWitness).map (fun bus _ => bus) ++
      cendBlockFloatFixedInputs precision) :
    (cendBlockFloatHigh precision keep extended buses).extractLsb' 32 32 ∈
        cendBlockFloatWords ∧
      (cendBlockFloatHigh precision keep extended buses).extractLsb' 0 32 ∈
        cendBlockFloatWords := by
  have hhi : (cendBlockFloatHigh precision keep extended buses).extractLsb' 32 32 ∈
      cendBlockFloatWords := by
    apply List.mem_cons_of_mem
    exact List.mem_flatMap.mpr ⟨(precision, keep, extended), htriple,
      List.mem_flatMap.mpr ⟨buses, hbuses, by simp⟩⟩
  have hlo : (cendBlockFloatHigh precision keep extended buses).extractLsb' 0 32 ∈
      cendBlockFloatWords := by
    apply List.mem_cons_of_mem
    exact List.mem_flatMap.mpr ⟨(precision, keep, extended), htriple,
      List.mem_flatMap.mpr ⟨buses, hbuses, by simp⟩⟩
  exact ⟨hhi, hlo⟩

/-- **A constant bus read of the ten-bus initial family yields closure data.** -/
theorem cendBlockFloatConstantBuses_data {precision : ParsedPrecision} {keep : Nat}
    {extended : Bool} (htriple : (precision, keep, extended) ∈ cendBlockFloatCases)
    (bus : IntegerALU.Bus) (hbus : bus ∈ cendInitialBuses cendWitness) :
    ∀ (i : Fin 4), i.val < 2 →
      unpackALUBus (parsedBlockFloatMab precision keep extended (fun _ => bus) 0) i ∈
        cendMixWords cendBlockFloatWords := by
  have hbuses : (fun _ => bus) ∈ (cendInitialBuses cendWitness).map (fun bus _ => bus) ++
      cendBlockFloatFixedInputs precision :=
    List.mem_append_left _ (List.mem_map.mpr ⟨bus, hbus, rfl⟩)
  obtain ⟨h0, h1⟩ := cendBlockFloatHigh_mem htriple hbuses
  exact unpackALUBus_mixWords_of_high_mem h0 h1

/-- **Committing a constant-read block-float write list keeps the observed LM1
word in the closure.** -/
theorem commitParsedMaskedWrites_lm1_blockFloat_constant {precision : ParsedPrecision}
    {keep : Nat} {extended : Bool} (_htriple : (precision, keep, extended) ∈
      cendBlockFloatCases)
    (_bus : IntegerALU.Bus) (_hbus : _bus ∈ cendInitialBuses cendWitness)
    (files : IntegerRegisterFiles) (writes : List PreparedParsedMaskedWrite)
    (dataOk : ∀ write ∈ writes, ∀ (i : Fin 4), i.val < 2 →
      write.data i ∈ cendMixWords cendBlockFloatWords)
    (destAligned : ∀ write ∈ writes, ∀ (width : PEMemory.Width)
      (address : Fin Bank.lm1.capacity),
      write.destination = some ⟨Bank.lm1, width, address⟩ →
        address.val % PEMemory.count Bank.lm1 width = 0)
    (target : Fin Bank.lm1.capacity) (targetLt : target.val < 2)
    (hold : files.lm1 target ∈ cendMixWords cendBlockFloatWords) :
    (commitParsedMaskedWrites files writes).lm1 target ∈
      cendMixWords cendBlockFloatWords :=
  commitParsedMaskedWrites_lm1_mixWords writes target targetLt dataOk destAligned files hold

/-- **The block-float destination fold at a constant read commits closure-data
writes.** -/
theorem executeParsedBlockFloatAtMAB_apply_data_constant {precision : ParsedPrecision}
    {keep : Nat} {extended : Bool} (htriple : (precision, keep, extended) ∈
      cendBlockFloatCases)
    (currentState : State) (hasSingleLineMask : Bool) (cycle : Fin 4)
    (bus : IntegerALU.Bus) (hbus : bus ∈ cendInitialBuses cendWitness)
    (oldContext coords : ParsedIntegerContext) :
    ∀ (destinations : List ParsedOperand) (files : IntegerRegisterFiles) (bar0 bar1 : BitVec 12)
      (nextFiles : IntegerRegisterFiles) (nextBar0 nextBar1 : BitVec 12),
      executeParsedBlockFloatAtMAB.apply currentState hasSingleLineMask cycle
        (parsedBlockFloatMab precision keep extended (fun _ => bus) 0) oldContext coords
        destinations files bar0 bar1 = .ok (nextFiles, nextBar0, nextBar1) →
      ∃ writes : List PreparedParsedMaskedWrite,
        nextFiles = commitParsedMaskedWrites files writes ∧
        (∀ write ∈ writes, ∀ (i : Fin 4), i.val < 2 →
          write.data i ∈ cendMixWords cendBlockFloatWords) ∧
        (∀ write ∈ writes, ∀ (width : PEMemory.Width) (address : Fin Bank.lm1.capacity),
          write.destination = some ⟨Bank.lm1, width, address⟩ →
            address.val % PEMemory.count Bank.lm1 width = 0) := by
  have hbuses : (fun _ => bus) ∈ (cendInitialBuses cendWitness).map (fun bus _ => bus) ++
      cendBlockFloatFixedInputs precision :=
    List.mem_append_left _ (List.mem_map.mpr ⟨bus, hbus, rfl⟩)
  obtain ⟨h0, h1⟩ := cendBlockFloatHigh_mem htriple hbuses
  intro destinations files bar0 bar1 nextFiles nextBar0 nextBar1 executed
  exact executeParsedBlockFloatAtMAB_apply_data currentState hasSingleLineMask cycle _
    oldContext coords (unpackALUBus_mixWords_of_high_mem h0 h1)
    destinations files bar0 bar1 nextFiles nextBar0 nextBar1 executed

/-- **The matrix-MAU poison gate is open when the poison flag is false.**  This
is the flag the zero-store / valid-lane computation of the initial state
produces; it is the hypothesis under which the destination fold is transparent. -/
theorem parsedMatrixMAUDestinationDataPoisonApplies_false (destination : ParsedOperand) :
    parsedMatrixMAUDestinationDataPoisonApplies false destination = false := by
  cases destination <;> rfl

/-! ## 5. The two row classes and the narrowed residual -/

/-- The block-float rows: `bfn` at `.d`/`.f`/`.g`/`.h`, `bfe` at `.h`. -/
def cendBlockFloatRow (expression : ParsedExpr) : Bool :=
  parsedExprIsBlockFloatProducer expression

/-- The matrix-MAU rows: `.mau p true kind half round` at the four float
precisions. -/
def cendMatrixMAURow (expression : ParsedExpr) : Bool :=
  parsedExprIsMatrixMAUProducer expression

/-- **A block-float row is never a member of the other value families.** -/
theorem cendBlockFloatRow_family_facts (expression : ParsedExpr)
    (row : cendBlockFloatRow expression = true) :
    parsedExprIsMslMsrProducer expression = false ∧
      parsedExprIsFloatReluProducer expression = false ∧
      parsedExprIsMatrixMAUProducer expression = false ∧
      parsedExprIsSupportedFloatMAUProducer expression = false ∧
      parsedExprIsL1ToPEProducer expression = false := by
  obtain ⟨op, sources, destinations, flush, text⟩ := expression
  simp only [cendBlockFloatRow, parsedExprIsBlockFloatProducer] at row
  cases op with
  | alu name precision unsigned arg =>
      cases name <;> cases precision <;>
        simp_all [parsedExprIsMslMsrProducer, parsedExprIsFloatReluProducer,
          parsedExprIsMatrixMAUProducer, parsedExprIsSupportedFloatMAUProducer,
          parsedExprIsL1ToPEProducer]
  | noforward => simp_all [parsedExprIsMslMsrProducer, parsedExprIsFloatReluProducer,
      parsedExprIsMatrixMAUProducer, parsedExprIsSupportedFloatMAUProducer,
      parsedExprIsL1ToPEProducer]
  | immediate value unsigned => simp_all [parsedExprIsMslMsrProducer,
      parsedExprIsFloatReluProducer, parsedExprIsMatrixMAUProducer,
      parsedExprIsSupportedFloatMAUProducer, parsedExprIsL1ToPEProducer]
  | zero => simp_all [parsedExprIsMslMsrProducer, parsedExprIsFloatReluProducer,
      parsedExprIsMatrixMAUProducer, parsedExprIsSupportedFloatMAUProducer,
      parsedExprIsL1ToPEProducer]
  | mau precision matrix kind half round => simp_all [parsedExprIsMslMsrProducer,
      parsedExprIsFloatReluProducer, parsedExprIsMatrixMAUProducer,
      parsedExprIsSupportedFloatMAUProducer, parsedExprIsL1ToPEProducer]
  | matrixWrite precision => simp_all [parsedExprIsMslMsrProducer,
      parsedExprIsFloatReluProducer, parsedExprIsMatrixMAUProducer,
      parsedExprIsSupportedFloatMAUProducer, parsedExprIsL1ToPEProducer]
  | wait tag => simp_all [parsedExprIsMslMsrProducer, parsedExprIsFloatReluProducer,
      parsedExprIsMatrixMAUProducer, parsedExprIsSupportedFloatMAUProducer,
      parsedExprIsL1ToPEProducer]
  | l1bm l1op => cases l1op <;> simp_all [parsedExprIsMslMsrProducer,
      parsedExprIsFloatReluProducer, parsedExprIsMatrixMAUProducer,
      parsedExprIsSupportedFloatMAUProducer, parsedExprIsL1ToPEProducer]
  | l2bm l2op => simp_all [parsedExprIsMslMsrProducer, parsedExprIsFloatReluProducer,
      parsedExprIsMatrixMAUProducer, parsedExprIsSupportedFloatMAUProducer,
      parsedExprIsL1ToPEProducer]
  | matrixRead precision => simp_all [parsedExprIsMslMsrProducer,
      parsedExprIsFloatReluProducer, parsedExprIsMatrixMAUProducer,
      parsedExprIsSupportedFloatMAUProducer, parsedExprIsL1ToPEProducer]

/-- **A matrix-MAU row is never a member of the other value families.** -/
theorem cendMatrixMAURow_family_facts (expression : ParsedExpr)
    (row : cendMatrixMAURow expression = true) :
    parsedExprIsMslMsrProducer expression = false ∧
      parsedExprIsFloatReluProducer expression = false ∧
      parsedExprIsBlockFloatProducer expression = false ∧
      parsedExprIsSupportedFloatMAUProducer expression = false ∧
      parsedExprIsL1ToPEProducer expression = false := by
  obtain ⟨op, sources, destinations, flush, text⟩ := expression
  simp only [cendMatrixMAURow, parsedExprIsMatrixMAUProducer] at row
  cases op with
  | alu name precision unsigned arg => simp_all [parsedExprIsMslMsrProducer,
      parsedExprIsFloatReluProducer, parsedExprIsBlockFloatProducer,
      parsedExprIsSupportedFloatMAUProducer, parsedExprIsL1ToPEProducer]
  | noforward => simp_all [parsedExprIsMslMsrProducer, parsedExprIsFloatReluProducer,
      parsedExprIsBlockFloatProducer, parsedExprIsSupportedFloatMAUProducer,
      parsedExprIsL1ToPEProducer]
  | immediate value unsigned => simp_all [parsedExprIsMslMsrProducer,
      parsedExprIsFloatReluProducer, parsedExprIsBlockFloatProducer,
      parsedExprIsSupportedFloatMAUProducer, parsedExprIsL1ToPEProducer]
  | zero => simp_all [parsedExprIsMslMsrProducer, parsedExprIsFloatReluProducer,
      parsedExprIsBlockFloatProducer, parsedExprIsSupportedFloatMAUProducer,
      parsedExprIsL1ToPEProducer]
  | mau precision matrix kind half round =>
      cases precision <;> cases matrix <;> cases kind <;> cases half <;> cases round <;>
        simp_all [parsedExprIsMslMsrProducer, parsedExprIsFloatReluProducer,
          parsedExprIsBlockFloatProducer, parsedExprIsSupportedFloatMAUProducer,
          parsedExprIsL1ToPEProducer]
  | matrixWrite precision => simp_all [parsedExprIsMslMsrProducer,
      parsedExprIsFloatReluProducer, parsedExprIsBlockFloatProducer,
      parsedExprIsSupportedFloatMAUProducer, parsedExprIsL1ToPEProducer]
  | wait tag => simp_all [parsedExprIsMslMsrProducer, parsedExprIsFloatReluProducer,
      parsedExprIsBlockFloatProducer, parsedExprIsSupportedFloatMAUProducer,
      parsedExprIsL1ToPEProducer]
  | l1bm l1op => cases l1op <;> simp_all [parsedExprIsMslMsrProducer,
      parsedExprIsFloatReluProducer, parsedExprIsBlockFloatProducer,
      parsedExprIsSupportedFloatMAUProducer, parsedExprIsL1ToPEProducer]
  | l2bm l2op => simp_all [parsedExprIsMslMsrProducer, parsedExprIsFloatReluProducer,
      parsedExprIsBlockFloatProducer, parsedExprIsSupportedFloatMAUProducer,
      parsedExprIsL1ToPEProducer]
  | matrixRead precision => simp_all [parsedExprIsMslMsrProducer,
      parsedExprIsFloatReluProducer, parsedExprIsBlockFloatProducer,
      parsedExprIsSupportedFloatMAUProducer, parsedExprIsL1ToPEProducer]

/-- A block-float class row: a `.matrixRead`/`.noforward` row, an
extended-inert row, or a block-float row. -/
def cendBlockFloatFamilyRow (expression : ParsedExpr) : Bool :=
  (cendReadOrNoForward expression || cendPEInertProducerExt expression) ||
    parsedExprIsBlockFloatProducer expression

/-- A matrix-MAU class row: a `.matrixRead`/`.noforward` row, an
extended-inert row, or a matrix-MAU row. -/
def cendMatrixMAUFamilyRow (expression : ParsedExpr) : Bool :=
  (cendReadOrNoForward expression || cendPEInertProducerExt expression) ||
    parsedExprIsMatrixMAUProducer expression

/-- The lines of the block-float class. -/
def CendBlockFloatLines (expressions : List NormalizedExpr) : Prop :=
  ∀ expression ∈ expressions.map NormalizedExpr.toParsed,
    cendBlockFloatFamilyRow expression = true

/-- The lines of the matrix-MAU class. -/
def CendMatrixMAULines (expressions : List NormalizedExpr) : Prop :=
  ∀ expression ∈ expressions.map NormalizedExpr.toParsed,
    cendMatrixMAUFamilyRow expression = true

/-- The block-float class, as a refutation statement. -/
def CendBlockFloatLinesRefuted : Prop :=
  ∀ expressions : List NormalizedExpr, CendBlockFloatLines expressions →
    ¬ ProofsLean.Correct cendSealedMachine cendSpec
      ([InstructionLine.pe expressions] : List InstructionLine)

/-- The matrix-MAU class, as a refutation statement. -/
def CendMatrixMAULinesRefuted : Prop :=
  ∀ expressions : List NormalizedExpr, CendMatrixMAULines expressions →
    ¬ ProofsLean.Correct cendSealedMachine cendSpec
      ([InstructionLine.pe expressions] : List InstructionLine)

/-- **The narrowed residual.**  `CendMslMsrResidual` minus the block-float and
matrix-MAU line classes. -/
def CendMatrixFamiliesResidual : Prop :=
  ∀ expressions : List NormalizedExpr,
    ¬ CendClosedLines expressions →
    ¬ (∀ expression ∈ expressions.map NormalizedExpr.toParsed,
      cendL1ToPEOrExtInert expression = true) →
    ¬ (expressions.map NormalizedExpr.toParsed).all parsedExprIsPlainIntegerALU = true →
    ¬ CendMixedReadLines expressions →
    ¬ CendMslMsrLines expressions →
    ¬ CendBlockFloatLines expressions →
    ¬ CendMatrixMAULines expressions →
    ¬ ProofsLean.Correct cendSealedMachine cendSpec
      ([InstructionLine.pe expressions] : List InstructionLine)

/-- **The exact split of `CendMslMsrResidual`.**  Given the two refutations, the
old residual is exactly the narrowed residual: every line in the new classes is
refuted, and every other line is left to the narrowed residual. -/
theorem cendMslMsrResidual_iff_matrixFamiliesResidual
    (block : CendBlockFloatLinesRefuted) (matrix : CendMatrixMAULinesRefuted) :
    CendMslMsrResidual ↔ CendMatrixFamiliesResidual := by
  constructor
  · intro residual expressions notClosed notExt notPlain notMixed notMsl _block _matrix
    exact residual expressions notClosed notExt notPlain notMixed notMsl
  · intro residual expressions notClosed notExt notPlain notMixed notMsl
    by_cases isBlock : CendBlockFloatLines expressions
    · exact block expressions isBlock
    · by_cases isMatrix : CendMatrixMAULines expressions
      · exact matrix expressions isMatrix
      · exact residual expressions notClosed notExt notPlain notMixed notMsl isBlock isMatrix

/-- **`CendMixedReadResidual` from the narrowed residual and the two
refutations.** -/
theorem cendMixedReadResidual_of_matrixFamiliesResidual
    (residual : CendMatrixFamiliesResidual)
    (block : CendBlockFloatLinesRefuted) (matrix : CendMatrixMAULinesRefuted) :
    CendMixedReadResidual :=
  cendMixedReadResidual_of_mslMsrResidual
    ((cendMslMsrResidual_iff_matrixFamiliesResidual block matrix).mpr residual)

/-- **The unconditional lower bound at two from the narrowed residual.** -/
theorem cendLowerBound_two_of_matrixFamiliesResidual
    (residual : CendMatrixFamiliesResidual)
    (block : CendBlockFloatLinesRefuted) (matrix : CendMatrixMAULinesRefuted) :
    ProofsLean.LowerBound cendSealedMachine cendSpec 2 :=
  cendLowerBound_two_of_mixedReadResidual
    (cendMixedReadResidual_of_matrixFamiliesResidual residual block matrix)


/-! ## 6. Non-vacuity witnesses -/

/-- One `.matrixRead` row and one block-float row. -/
def cendBlockFloatExampleLine : List NormalizedExpr :=
  [⟨.matrixRead .d, [], [], none⟩, ⟨.alu .bfn (some .d) false none, [], [], none⟩]

/-- One `.matrixRead` row and one matrix-MAU row. -/
def cendMatrixMAUExampleLine : List NormalizedExpr :=
  [⟨.matrixRead .d, [], [], none⟩, ⟨.mau .d true .mul none false, [], [], none⟩]

theorem cendBlockFloatExampleLine_mem : CendBlockFloatLines cendBlockFloatExampleLine := by
  intro expression member
  obtain ⟨normalized, normalizedMem, rfl⟩ := List.mem_map.mp member
  simp only [cendBlockFloatExampleLine, List.mem_cons, List.not_mem_nil, or_false] at normalizedMem
  rcases normalizedMem with rfl | rfl
  · simp [NormalizedExpr.toParsed, cendBlockFloatFamilyRow, cendReadOrNoForward,
      parsedExprIsMatrixReadProducer]
  · simp [NormalizedExpr.toParsed, cendBlockFloatFamilyRow, cendReadOrNoForward,
      cendPEInertProducerExt, parsedExprIsMatrixReadProducer, parsedExprIsBlockFloatProducer]

theorem cendMatrixMAUExampleLine_mem : CendMatrixMAULines cendMatrixMAUExampleLine := by
  intro expression member
  obtain ⟨normalized, normalizedMem, rfl⟩ := List.mem_map.mp member
  simp only [cendMatrixMAUExampleLine, List.mem_cons, List.not_mem_nil, or_false] at normalizedMem
  rcases normalizedMem with rfl | rfl
  · simp [NormalizedExpr.toParsed, cendMatrixMAUFamilyRow, cendReadOrNoForward,
      parsedExprIsMatrixReadProducer]
  · simp [NormalizedExpr.toParsed, cendMatrixMAUFamilyRow, cendReadOrNoForward,
      cendPEInertProducerExt, parsedExprIsMatrixReadProducer, parsedExprIsMatrixMAUProducer]

theorem cendBlockFloatExampleLine_notMixed : ¬ CendMixedReadLines cendBlockFloatExampleLine := by
  intro mixed
  have row := mixed ⟨.alu .bfn (some .d) false none, [], [], none, ""⟩ (by
    simp [cendBlockFloatExampleLine, NormalizedExpr.toParsed])
  simpa [NormalizedExpr.toParsed, cendMixedReadRow, cendReadOrNoForward, cendL1ToPEOrExtInert,
    cendPEInertProducerExt, parsedExprIsMatrixReadProducer, parsedExprIsBlockFloatProducer,
    parsedExprIsMslMsrProducer, parsedExprIsPEInertProducer, parsedExprIsL1SharedBlockProducer,
    parsedExprIsMatrixWriteProducer, parsedExprIsL2BMProducer, parsedExprIsL1ToPEProducer] using row

theorem cendMatrixMAUExampleLine_notMixed : ¬ CendMixedReadLines cendMatrixMAUExampleLine := by
  intro mixed
  have row := mixed ⟨.mau .d true .mul none false, [], [], none, ""⟩ (by
    simp [cendMatrixMAUExampleLine, NormalizedExpr.toParsed])
  simpa [NormalizedExpr.toParsed, cendMixedReadRow, cendReadOrNoForward, cendL1ToPEOrExtInert,
    cendPEInertProducerExt, parsedExprIsMatrixReadProducer, parsedExprIsMatrixMAUProducer,
    parsedExprIsMslMsrProducer, parsedExprIsPEInertProducer, parsedExprIsL1SharedBlockProducer,
    parsedExprIsMatrixWriteProducer, parsedExprIsL2BMProducer, parsedExprIsL1ToPEProducer] using row

theorem cendBlockFloatExampleLine_notClosed : ¬ CendClosedLines cendBlockFloatExampleLine := by
  intro closed
  rcases closed with allRead | allInert
  · have read := allRead ⟨.alu .bfn (some .d) false none, [], [], none⟩ (by
      simp [cendBlockFloatExampleLine, NormalizedExpr.toParsed])
    obtain ⟨precision, hop⟩ := read
    simp [NormalizedExpr.toParsed] at hop
  · have inert := allInert ⟨.alu .bfn (some .d) false none, [], [], none, ""⟩ (by
      simp [cendBlockFloatExampleLine, NormalizedExpr.toParsed])
    simp_all [NormalizedExpr.toParsed, parsedExprIsPEInertProducer,
      parsedExprIsL1SharedBlockProducer, parsedExprIsBlockFloatProducer]

theorem cendMatrixMAUExampleLine_notClosed : ¬ CendClosedLines cendMatrixMAUExampleLine := by
  intro closed
  rcases closed with allRead | allInert
  · have read := allRead ⟨.mau .d true .mul none false, [], [], none⟩ (by
      simp [cendMatrixMAUExampleLine, NormalizedExpr.toParsed])
    obtain ⟨precision, hop⟩ := read
    simp [NormalizedExpr.toParsed] at hop
  · have inert := allInert ⟨.mau .d true .mul none false, [], [], none, ""⟩ (by
      simp [cendMatrixMAUExampleLine, NormalizedExpr.toParsed])
    simp_all [NormalizedExpr.toParsed, parsedExprIsPEInertProducer,
      parsedExprIsL1SharedBlockProducer, parsedExprIsMatrixMAUProducer]

/-- **The block-float class is non-vacuous**: the example line is in it, is not
closed, not mixed and not in the `msl`/`msr` class. -/
theorem cendBlockFloatExampleLine_new :
    CendBlockFloatLines cendBlockFloatExampleLine ∧
      ¬ CendClosedLines cendBlockFloatExampleLine ∧
      ¬ CendMixedReadLines cendBlockFloatExampleLine ∧
      ¬ CendMslMsrLines cendBlockFloatExampleLine := by
  refine ⟨cendBlockFloatExampleLine_mem, cendBlockFloatExampleLine_notClosed,
    cendBlockFloatExampleLine_notMixed, ?_⟩
  intro msl
  have row := msl ⟨.alu .bfn (some .d) false none, [], [], none, ""⟩ (by
    simp [cendBlockFloatExampleLine, NormalizedExpr.toParsed])
  simpa [NormalizedExpr.toParsed, cendMslMsrRow, cendReadOrNoForward, cendPEInertProducerExt,
    parsedExprIsMatrixReadProducer, parsedExprIsBlockFloatProducer, parsedExprIsMslMsrProducer,
    parsedExprIsPEInertProducer, parsedExprIsL1SharedBlockProducer,
    parsedExprIsMatrixWriteProducer, parsedExprIsL2BMProducer] using row

/-- **The matrix-MAU class is non-vacuous**: the example line is in it, is not
closed, not mixed and not in the `msl`/`msr` class. -/
theorem cendMatrixMAUExampleLine_new :
    CendMatrixMAULines cendMatrixMAUExampleLine ∧
      ¬ CendClosedLines cendMatrixMAUExampleLine ∧
      ¬ CendMixedReadLines cendMatrixMAUExampleLine ∧
      ¬ CendMslMsrLines cendMatrixMAUExampleLine := by
  refine ⟨cendMatrixMAUExampleLine_mem, cendMatrixMAUExampleLine_notClosed,
    cendMatrixMAUExampleLine_notMixed, ?_⟩
  intro msl
  have row := msl ⟨.mau .d true .mul none false, [], [], none, ""⟩ (by
    simp [cendMatrixMAUExampleLine, NormalizedExpr.toParsed])
  simpa [NormalizedExpr.toParsed, cendMslMsrRow, cendReadOrNoForward, cendPEInertProducerExt,
    parsedExprIsMatrixReadProducer, parsedExprIsMatrixMAUProducer, parsedExprIsMslMsrProducer,
    parsedExprIsPEInertProducer, parsedExprIsL1SharedBlockProducer,
    parsedExprIsMatrixWriteProducer, parsedExprIsL2BMProducer] using row

/-! ## Trust report -/

#print axioms cendMixWords_ne_of_halves
#print axioms cendBlockFloatWords_avoid
#print axioms cendBlockFloatWords_target_high_avoid
#print axioms cendBlockFloatWords_target_low_avoid
#print axioms cendMatrixMAUWords_avoid
#print axioms cendMatrixMAUWords_target_high_avoid
#print axioms cendMatrixMAUWords_target_low_avoid
#print axioms unpackALUBus_mixWords_of_high_mem
#print axioms writeParsedMslMsrDestination?_data_mixWords
#print axioms executeParsedBlockFloatAtMAB_apply_data
#print axioms cendBlockFloatRow_family_facts
#print axioms cendMatrixMAURow_family_facts
#print axioms cendMslMsrResidual_iff_matrixFamiliesResidual
#print axioms cendMixedReadResidual_of_matrixFamiliesResidual
#print axioms cendLowerBound_two_of_matrixFamiliesResidual
#print axioms cendBlockFloatExampleLine_new
#print axioms cendMatrixMAUExampleLine_new
#print axioms cendBlockFloatHigh_mem
#print axioms cendBlockFloatConstantBuses_data
#print axioms executeParsedBlockFloatAtMAB_apply_data_constant
#print axioms commitParsedMaskedWrites_lm1_blockFloat_constant
#print axioms executeParsedBlockFloatAtMAB_writePEs_data
#print axioms executeParsedBlockFloatAtMAB_runCycles_data
#print axioms parsedMatrixMAUDestinationDataPoisonApplies_false

end ProofsLean.MNCore
