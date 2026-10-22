import ProofsLean.CendLm1Witness

/-! # `12.convert-endian`: the half-mix value algebra of the LM1 commit

This module isolates the *value algebra* the executor half of the LM1 word
obligation needs, independently of the executor:

* the datapath table is shown to cover every integer ALU opcode the parser can
  lower (`cendParsedIntegerOp_table_cover`): the only table entries missing from
  `cendDatapathWords` are the unsigned arithmetic variants, whose *high* words
  (the only words an observed write can carry) coincide with the signed ones;
* `cendHalfMix` / `cendHalfMixWords` is the value set a commit over such data can
  produce.  A write merges its data word into the destination with one of four
  half masks (`selectedWordMask_lt_two_cases`), so each 16-bit half of a
  committed word is either zero or the corresponding half of one datapath word.
  The set is therefore `{ hi16(d1) ++ lo16(d2) : d1, d2 ∈ datapath ∪ {0} }`;
* neither target word (`0xefcdab89`, `0x67452301`) is in that set, because no
  datapath word at the witness has the required 16-bit half in the required
  position (`cendDatapathWords_targetHalves_avoid`).

The algebra of `mergeSelectedWord` over the set is `mergeSelectedWord_halfMix_mem`
and the mask case split is `selectedWordMask_lt_two_cases`.

No `sorry`, no `admit`, no `native_decide`, no new axioms.
-/

namespace ProofsLean.MNCore

open Issue
open PEMemory

set_option maxHeartbeats 1600000
set_option maxRecDepth 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false

/-! ## 1. The parsed integer opcode table sits inside `cendOpTable` -/

/-- Unsigned and signed arithmetic compute the same value; the difference is
only the carry flag.  Only the high bus word is observed, so the data words of a
`.arith _ true` datapath are the data words of its `.arith _ false` twin. -/
theorem evaluateBus_arith_true_high (a : IntegerALU.Arithmetic)
    (p : IntegerALU.Precision) (sx sy : IntegerALU.Bus) (r : Bool) :
    (IntegerALU.evaluateBus p (.arith a true) sx sy r).value.high =
      (IntegerALU.evaluateBus p (.arith a false) sx sy false).value.high := by
  cases a <;> cases p <;> rfl

/-- Equality of the high bus word suffices for the equality of the first two
data words. -/
theorem unpackALUBus_high_congr {left right : IntegerALU.Bus}
    (high : left.high = right.high) (i : Fin 4) (lt : i.val < 2) :
    unpackALUBus left i = unpackALUBus right i := by
  have h01 : i.val = 0 ∨ i.val = 1 := by omega
  rcases h01 with h | h
  · have hi : i = (⟨0, by decide⟩ : Fin 4) := Fin.ext h
    subst hi
    simp [PEMemory.unpackALUBus, high]
  · have hi : i = (⟨1, by decide⟩ : Fin 4) := Fin.ext h
    subst hi
    simp [PEMemory.unpackALUBus, high]

/-- The high-word data of an integer datapath is independent of the
`firstOperandWasReduced` flag. -/
theorem evaluateBus_data_reduced_irrelevant (p : IntegerALU.Precision)
    (op : IntegerALU.Op) (sx sy : IntegerALU.Bus) (r : Bool) (i : Fin 4)
    (hi : i.val < 2) :
    unpackALUBus (IntegerALU.evaluateBus p op sx sy r).value i =
      unpackALUBus (IntegerALU.evaluateBus p op sx sy false).value i := by
  apply unpackALUBus_high_congr
  · cases op <;> rfl
  · exact hi

theorem cendOpTable_mem_arith (p : ParsedPrecision) (a : IntegerALU.Arithmetic) :
    (p.laneWidth, IntegerALU.Op.arith a false) ∈ cendOpTable := by
  cases p <;> cases a <;> decide

theorem cendOpTable_mem_maximum (p : ParsedPrecision) (u : Bool) :
    (p.laneWidth, IntegerALU.Op.maximum u) ∈ cendOpTable := by
  cases p <;> cases u <;> decide

theorem cendOpTable_mem_minimum (p : ParsedPrecision) (u : Bool) :
    (p.laneWidth, IntegerALU.Op.minimum u) ∈ cendOpTable := by
  cases p <;> cases u <;> decide

theorem cendOpTable_mem_shiftRight (p : ParsedPrecision) (u : Bool) :
    (p.laneWidth, IntegerALU.Op.shift (IntegerALU.Shift.right u)) ∈ cendOpTable := by
  cases p <;> cases u <;> decide

/-- Every integer opcode the parser can lower into a datapath op has a
value-equivalent table entry at every precision.  The entry differs only for the
unsigned arithmetic variants, where `evaluateBus_arith_true_high` supplies the
high-word equality. -/
theorem cendParsedIntegerOp_table_cover (name : ParsedAluName) (unsigned : Bool)
    (op : IntegerALU.Op) (h : name.toIntegerOp unsigned = some op)
    (precision : ParsedPrecision) :
    ∃ op', (precision.laneWidth, op') ∈ cendOpTable ∧
      ∀ (sx sy : IntegerALU.Bus) (r : Bool) (i : Fin 4), i.val < 2 →
        unpackALUBus (IntegerALU.evaluateBus precision.laneWidth op sx sy r).value i =
          unpackALUBus (IntegerALU.evaluateBus precision.laneWidth op' sx sy false).value i := by
  cases name with
  | inc =>
      cases unsigned
      · simp only [ParsedAluName.toIntegerOp, Option.some.injEq] at h
        subst op
        exact ⟨.arith .inc false, cendOpTable_mem_arith precision .inc,
          fun sx sy r i hi => evaluateBus_data_reduced_irrelevant precision.laneWidth _ sx sy r i hi⟩
      · simp only [ParsedAluName.toIntegerOp, Option.some.injEq] at h
        subst op
        refine ⟨.arith .inc false, cendOpTable_mem_arith precision .inc, ?_⟩
        intro sx sy r i hi
        rw [evaluateBus_data_reduced_irrelevant precision.laneWidth (.arith .inc true) sx sy r i hi]
        exact unpackALUBus_high_congr (evaluateBus_arith_true_high .inc precision.laneWidth sx sy false) i hi
  | dec =>
      cases unsigned
      · simp only [ParsedAluName.toIntegerOp, Option.some.injEq] at h
        subst op
        exact ⟨.arith .dec false, cendOpTable_mem_arith precision .dec,
          fun sx sy r i hi => evaluateBus_data_reduced_irrelevant precision.laneWidth _ sx sy r i hi⟩
      · simp only [ParsedAluName.toIntegerOp, Option.some.injEq] at h
        subst op
        refine ⟨.arith .dec false, cendOpTable_mem_arith precision .dec, ?_⟩
        intro sx sy r i hi
        rw [evaluateBus_data_reduced_irrelevant precision.laneWidth (.arith .dec true) sx sy r i hi]
        exact unpackALUBus_high_congr (evaluateBus_arith_true_high .dec precision.laneWidth sx sy false) i hi
  | add =>
      cases unsigned
      · simp only [ParsedAluName.toIntegerOp, Option.some.injEq] at h
        subst op
        exact ⟨.arith .add false, cendOpTable_mem_arith precision .add,
          fun sx sy r i hi => evaluateBus_data_reduced_irrelevant precision.laneWidth _ sx sy r i hi⟩
      · simp only [ParsedAluName.toIntegerOp, Option.some.injEq] at h
        subst op
        refine ⟨.arith .add false, cendOpTable_mem_arith precision .add, ?_⟩
        intro sx sy r i hi
        rw [evaluateBus_data_reduced_irrelevant precision.laneWidth (.arith .add true) sx sy r i hi]
        exact unpackALUBus_high_congr (evaluateBus_arith_true_high .add precision.laneWidth sx sy false) i hi
  | sub =>
      cases unsigned
      · simp only [ParsedAluName.toIntegerOp, Option.some.injEq] at h
        subst op
        exact ⟨.arith .sub false, cendOpTable_mem_arith precision .sub,
          fun sx sy r i hi => evaluateBus_data_reduced_irrelevant precision.laneWidth _ sx sy r i hi⟩
      · simp only [ParsedAluName.toIntegerOp, Option.some.injEq] at h
        subst op
        refine ⟨.arith .sub false, cendOpTable_mem_arith precision .sub, ?_⟩
        intro sx sy r i hi
        rw [evaluateBus_data_reduced_irrelevant precision.laneWidth (.arith .sub true) sx sy r i hi]
        exact unpackALUBus_high_congr (evaluateBus_arith_true_high .sub precision.laneWidth sx sy false) i hi
  | not =>
      simp only [ParsedAluName.toIntegerOp, Option.some.injEq] at h
      subst op
      exact ⟨.bitNot, by cases precision <;> decide, fun sx sy r i hi => evaluateBus_data_reduced_irrelevant precision.laneWidth _ sx sy r i hi⟩
  | lnot =>
      simp only [ParsedAluName.toIntegerOp, Option.some.injEq] at h
      subst op
      exact ⟨.logicalNot, by cases precision <;> decide, fun sx sy r i hi => evaluateBus_data_reduced_irrelevant precision.laneWidth _ sx sy r i hi⟩
  | and =>
      simp only [ParsedAluName.toIntegerOp, Option.some.injEq] at h
      subst op
      exact ⟨.bitAnd, by cases precision <;> decide, fun sx sy r i hi => evaluateBus_data_reduced_irrelevant precision.laneWidth _ sx sy r i hi⟩
  | or =>
      simp only [ParsedAluName.toIntegerOp, Option.some.injEq] at h
      subst op
      exact ⟨.bitOr, by cases precision <;> decide, fun sx sy r i hi => evaluateBus_data_reduced_irrelevant precision.laneWidth _ sx sy r i hi⟩
  | xor =>
      simp only [ParsedAluName.toIntegerOp, Option.some.injEq] at h
      subst op
      exact ⟨.bitXor, by cases precision <;> decide, fun sx sy r i hi => evaluateBus_data_reduced_irrelevant precision.laneWidth _ sx sy r i hi⟩
  | max =>
      cases unsigned
      · simp only [ParsedAluName.toIntegerOp, Option.some.injEq] at h
        subst op
        exact ⟨.maximum false, cendOpTable_mem_maximum precision false,
          fun sx sy r i hi => evaluateBus_data_reduced_irrelevant precision.laneWidth _ sx sy r i hi⟩
      · simp only [ParsedAluName.toIntegerOp, Option.some.injEq] at h
        subst op
        exact ⟨.maximum true, cendOpTable_mem_maximum precision true,
          fun sx sy r i hi => evaluateBus_data_reduced_irrelevant precision.laneWidth _ sx sy r i hi⟩
  | min =>
      cases unsigned
      · simp only [ParsedAluName.toIntegerOp, Option.some.injEq] at h
        subst op
        exact ⟨.minimum false, cendOpTable_mem_minimum precision false,
          fun sx sy r i hi => evaluateBus_data_reduced_irrelevant precision.laneWidth _ sx sy r i hi⟩
      · simp only [ParsedAluName.toIntegerOp, Option.some.injEq] at h
        subst op
        exact ⟨.minimum true, cendOpTable_mem_minimum precision true,
          fun sx sy r i hi => evaluateBus_data_reduced_irrelevant precision.laneWidth _ sx sy r i hi⟩
  | packbit =>
      simp only [ParsedAluName.toIntegerOp, Option.some.injEq] at h
      subst op
      exact ⟨.packbit, by cases precision <;> decide, fun sx sy r i hi => evaluateBus_data_reduced_irrelevant precision.laneWidth _ sx sy r i hi⟩
  | passa =>
      simp only [ParsedAluName.toIntegerOp, Option.some.injEq] at h
      subst op
      exact ⟨.passa, by cases precision <;> decide, fun sx sy r i hi => evaluateBus_data_reduced_irrelevant precision.laneWidth _ sx sy r i hi⟩
  | lsl =>
      simp only [ParsedAluName.toIntegerOp, Option.some.injEq] at h
      subst op
      exact ⟨.shift .left, by cases precision <;> decide, fun sx sy r i hi => evaluateBus_data_reduced_irrelevant precision.laneWidth _ sx sy r i hi⟩
  | lsr =>
      cases unsigned
      · simp only [ParsedAluName.toIntegerOp, Option.some.injEq] at h
        subst op
        exact ⟨.shift (.right false), cendOpTable_mem_shiftRight precision false,
          fun sx sy r i hi => evaluateBus_data_reduced_irrelevant precision.laneWidth _ sx sy r i hi⟩
      · simp only [ParsedAluName.toIntegerOp, Option.some.injEq] at h
        subst op
        exact ⟨.shift (.right true), cendOpTable_mem_shiftRight precision true,
          fun sx sy r i hi => evaluateBus_data_reduced_irrelevant precision.laneWidth _ sx sy r i hi⟩
  | bsl =>
      simp only [ParsedAluName.toIntegerOp, Option.some.injEq] at h
      subst op
      exact ⟨.shift .rotateLeft, by cases precision <;> decide, fun sx sy r i hi => evaluateBus_data_reduced_irrelevant precision.laneWidth _ sx sy r i hi⟩
  | bsr =>
      simp only [ParsedAluName.toIntegerOp, Option.some.injEq] at h
      subst op
      exact ⟨.shift .rotateRight, by cases precision <;> decide, fun sx sy r i hi => evaluateBus_data_reduced_irrelevant precision.laneWidth _ sx sy r i hi⟩
  | msl => simp [ParsedAluName.toIntegerOp] at h
  | msr => simp [ParsedAluName.toIntegerOp] at h
  | rsqrt => simp [ParsedAluName.toIntegerOp] at h
  | floor => simp [ParsedAluName.toIntegerOp] at h
  | ftoi => simp [ParsedAluName.toIntegerOp] at h
  | bfe => simp [ParsedAluName.toIntegerOp] at h
  | bfn => simp [ParsedAluName.toIntegerOp] at h
  | relu => simp [ParsedAluName.toIntegerOp] at h
  | relu0 => simp [ParsedAluName.toIntegerOp] at h
  | relu1 => simp [ParsedAluName.toIntegerOp] at h
  | relu2 => simp [ParsedAluName.toIntegerOp] at h
  | relu3 => simp [ParsedAluName.toIntegerOp] at h
  | lrelud => simp [ParsedAluName.toIntegerOp] at h
  | lreluo => simp [ParsedAluName.toIntegerOp] at h
  | ilrelud => simp [ParsedAluName.toIntegerOp] at h

/-- **Every table datapath word is in `cendDatapathWords`.** -/
theorem cendDatapathWords_mem_of_table (x : BitVec 64) (p : IntegerALU.Precision)
    (op : IntegerALU.Op) (sx sy : IntegerALU.Bus)
    (hx : sx ∈ cendInitialBuses x) (hy : sy ∈ cendInitialBuses x)
    (hspec : (p, op) ∈ cendOpTable) (i : Fin 4) (hi : i.val < 2) :
    unpackALUBus (IntegerALU.evaluateBus p op sx sy false).value i ∈
      cendDatapathWords x := by
  unfold cendDatapathWords
  refine List.mem_flatMap.mpr ⟨sx, hx, List.mem_flatMap.mpr ⟨sy, hy, ?_⟩⟩
  refine List.mem_flatMap.mpr ⟨(p, op), hspec, ?_⟩
  have h01 : i.val = 0 ∨ i.val = 1 := by omega
  rcases h01 with h | h
  · have hi' : i = (⟨0, by decide⟩ : Fin 4) := Fin.ext h
    subst hi'
    simp [PEMemory.unpackALUBus]
  · have hi' : i = (⟨1, by decide⟩ : Fin 4) := Fin.ext h
    subst hi'
    simp [PEMemory.unpackALUBus]

/-- The integer request of a plain `.alu` op exposes its precision and datapath
op exactly. -/
theorem cendALU_evaluated_request (name : ParsedAluName) (precision : ParsedPrecision)
    (unsigned : Bool) (arg : Option (Fin 256)) (sx sy : IntegerALU.Bus)
    (reduced : Bool) (output : IntegerALU.BusResult)
    (evaluated : evaluateParsedIntegerAlu (.alu name (some precision) unsigned arg)
      sx sy reduced = .ok output) :
    ∃ op : IntegerALU.Op, name.toIntegerOp unsigned = some op ∧
      output = IntegerALU.evaluateBus precision.laneWidth op sx sy reduced := by
  unfold evaluateParsedIntegerAlu at evaluated
  simp only [ParsedOp.executionRequest, ParsedOp.integerRequest] at evaluated
  by_cases supported : name.supportsIntegerAt precision = true
  · rw [if_pos supported] at evaluated
    cases h : name.toIntegerOp unsigned with
    | none => rw [h] at evaluated; simp at evaluated
    | some op =>
        rw [h] at evaluated
        simp only [StepResult.ok.injEq] at evaluated
        exact ⟨op, rfl, evaluated.symm⟩
  · rw [if_neg supported] at evaluated
    simp at evaluated

/-- **The data words of any evaluated plain integer ALU op are datapath words.**
The two operand buses only need to be initial buses. -/
theorem cendALU_dataWord_mem (x : BitVec 64) (name : ParsedAluName)
    (precision : ParsedPrecision) (unsigned : Bool) (arg : Option (Fin 256))
    (sx sy : IntegerALU.Bus) (hx : sx ∈ cendInitialBuses x)
    (hy : sy ∈ cendInitialBuses x) (reduced : Bool) (output : IntegerALU.BusResult)
    (evaluated : evaluateParsedIntegerAlu (.alu name (some precision) unsigned arg)
      sx sy reduced = .ok output)
    (i : Fin 4) (hi : i.val < 2) :
    unpackALUBus output.value i ∈ cendDatapathWords x := by
  obtain ⟨op, hop, houtput⟩ := cendALU_evaluated_request name precision unsigned arg
    sx sy reduced output evaluated
  subst houtput
  obtain ⟨op', hspec, hsame⟩ := cendParsedIntegerOp_table_cover name unsigned op hop precision
  rw [hsame sx sy reduced i hi]
  exact cendDatapathWords_mem_of_table x precision.laneWidth op' sx sy hx hy hspec i hi

/-! ## 2. The half-mix value set -/

/-- The data words a prepared write can carry: `0` (a flushed or zero bus) and
the datapath table words. -/
def cendDataWords (x : BitVec 64) : List (BitVec 32) :=
  0 :: cendDatapathWords x

theorem cendDataWords_zero (x : BitVec 64) : (0 : BitVec 32) ∈ cendDataWords x :=
  List.mem_cons_self

theorem cendDataWords_of_datapath (x : BitVec 64) (word : BitVec 32)
    (member : word ∈ cendDatapathWords x) : word ∈ cendDataWords x :=
  List.mem_cons_of_mem _ member

/-- One 32-bit word assembled from the high 16 bits of `hi` and the low 16 bits
of `lo`. -/
def cendHalfMix (hi lo : BitVec 32) : BitVec 32 :=
  (hi &&& 0xffff0000) ||| (lo &&& 0x0000ffff)

theorem cendHalfMix_zero_zero : cendHalfMix 0 0 = 0 := by
  unfold cendHalfMix
  decide

/-- The value set of one observed LM1 word: both 16-bit halves are independently
either zero or the corresponding half of a datapath word. -/
def cendHalfMixWords (x : BitVec 64) : List (BitVec 32) :=
  (cendDataWords x).flatMap fun hi =>
    (cendDataWords x).map fun lo => cendHalfMix hi lo

theorem cendHalfMixWords_mem (x : BitVec 64) (hi lo : BitVec 32)
    (hhi : hi ∈ cendDataWords x) (hlo : lo ∈ cendDataWords x) :
    cendHalfMix hi lo ∈ cendHalfMixWords x := by
  unfold cendHalfMixWords
  exact List.mem_flatMap.mpr ⟨hi, hhi, List.mem_map.mpr ⟨lo, hlo, rfl⟩⟩

theorem cendHalfMixWords_exists (x : BitVec 64) (word : BitVec 32)
    (member : word ∈ cendHalfMixWords x) :
    ∃ hi ∈ cendDataWords x, ∃ lo ∈ cendDataWords x, word = cendHalfMix hi lo := by
  obtain ⟨hi, hhi, hmap⟩ := List.mem_flatMap.mp member
  obtain ⟨lo, hlo, rfl⟩ := List.mem_map.mp hmap
  exact ⟨hi, hhi, lo, hlo, rfl⟩

theorem cendHalfMixWords_zero (x : BitVec 64) :
    (0 : BitVec 32) ∈ cendHalfMixWords x := by
  have := cendHalfMixWords_mem x 0 0 (cendDataWords_zero x) (cendDataWords_zero x)
  rwa [cendHalfMix_zero_zero] at this

/-- The high half of a mix is the high half of its first argument. -/
theorem cendHalfMix_high (hi lo : BitVec 32) :
    cendHalfMix hi lo &&& 0xffff0000 = hi &&& 0xffff0000 := by
  unfold cendHalfMix
  calc ((hi &&& 0xffff0000) ||| (lo &&& 0x0000ffff)) &&& 0xffff0000
      = ((hi &&& 0xffff0000) &&& 0xffff0000) |||
          ((lo &&& 0x0000ffff) &&& 0xffff0000) := by
        rw [BitVec.and_or_distrib_right]
    _ = (hi &&& (0xffff0000 &&& 0xffff0000)) |||
          (lo &&& (0x0000ffff &&& 0xffff0000)) := by
        rw [BitVec.and_assoc, BitVec.and_assoc]
    _ = (hi &&& 0xffff0000) ||| (lo &&& 0) := by
        rw [show (0xffff0000 : BitVec 32) &&& 0xffff0000 = 0xffff0000 from by decide,
          show (0x0000ffff : BitVec 32) &&& 0xffff0000 = 0 from by decide]
    _ = hi &&& 0xffff0000 := by simp

/-- The low half of a mix is the low half of its second argument. -/
theorem cendHalfMix_low (hi lo : BitVec 32) :
    cendHalfMix hi lo &&& 0x0000ffff = lo &&& 0x0000ffff := by
  unfold cendHalfMix
  calc ((hi &&& 0xffff0000) ||| (lo &&& 0x0000ffff)) &&& 0x0000ffff
      = ((hi &&& 0xffff0000) &&& 0x0000ffff) |||
          ((lo &&& 0x0000ffff) &&& 0x0000ffff) := by
        rw [BitVec.and_or_distrib_right]
    _ = (hi &&& (0xffff0000 &&& 0x0000ffff)) |||
          (lo &&& (0x0000ffff &&& 0x0000ffff)) := by
        rw [BitVec.and_assoc, BitVec.and_assoc]
    _ = (hi &&& 0) ||| (lo &&& 0x0000ffff) := by
        rw [show (0xffff0000 : BitVec 32) &&& 0x0000ffff = 0 from by decide,
          show (0x0000ffff : BitVec 32) &&& 0x0000ffff = 0x0000ffff from by decide]
    _ = lo &&& 0x0000ffff := by simp

/-! ## 3. Target avoidance over the half-mix set -/

/-- One kernel check: no datapath word at the witness has a nonzero-mask
projection equal to any of the four target 16-bit halves in its position. -/
theorem cendDatapathWords_targetHalves_avoid :
    (cendDatapathWords cendLm1Witness).all (fun d =>
      ((d &&& 0xffff0000 != (0xefcd0000 : BitVec 32)) &&
       (d &&& 0x0000ffff != (0x0000ab89 : BitVec 32))) &&
      ((d &&& 0xffff0000 != (0x67450000 : BitVec 32)) &&
       (d &&& 0x0000ffff != (0x00002301 : BitVec 32)))) = true := by
  decide

theorem cendDatapathWords_mask_ne (mask target : BitVec 32) (word : BitVec 32)
    (member : word ∈ cendDatapathWords cendLm1Witness)
    (check : (cendDatapathWords cendLm1Witness).all (fun d => d &&& mask != target) =
      true) :
    word &&& mask ≠ target := by
  have checked := List.all_eq_true.mp check word member
  simpa using checked

/-- The high-mask projection of the combined kernel check (target `0xefcd0000`). -/
theorem cendDatapathWords_highMask_efcd_check :
    (cendDatapathWords cendLm1Witness).all
      (fun d => d &&& 0xffff0000 != (0xefcd0000 : BitVec 32)) = true := by
  rw [List.all_eq_true]
  intro d member
  have check := List.all_eq_true.mp cendDatapathWords_targetHalves_avoid d member
  simp only [Bool.and_eq_true] at check
  exact check.1.1

/-- The low-mask projection of the combined kernel check (target `0x0000ab89`). -/
theorem cendDatapathWords_lowMask_ab89_check :
    (cendDatapathWords cendLm1Witness).all
      (fun d => d &&& 0x0000ffff != (0x0000ab89 : BitVec 32)) = true := by
  rw [List.all_eq_true]
  intro d member
  have check := List.all_eq_true.mp cendDatapathWords_targetHalves_avoid d member
  simp only [Bool.and_eq_true] at check
  exact check.1.2

/-- The high-mask projection of the combined kernel check (target `0x67450000`). -/
theorem cendDatapathWords_highMask_6745_check :
    (cendDatapathWords cendLm1Witness).all
      (fun d => d &&& 0xffff0000 != (0x67450000 : BitVec 32)) = true := by
  rw [List.all_eq_true]
  intro d member
  have check := List.all_eq_true.mp cendDatapathWords_targetHalves_avoid d member
  simp only [Bool.and_eq_true] at check
  exact check.2.1

/-- The low-mask projection of the combined kernel check (target `0x00002301`). -/
theorem cendDatapathWords_lowMask_2301_check :
    (cendDatapathWords cendLm1Witness).all
      (fun d => d &&& 0x0000ffff != (0x00002301 : BitVec 32)) = true := by
  rw [List.all_eq_true]
  intro d member
  have check := List.all_eq_true.mp cendDatapathWords_targetHalves_avoid d member
  simp only [Bool.and_eq_true] at check
  exact check.2.2

theorem cendDataWords_mask_ne (mask target : BitVec 32) (word : BitVec 32)
    (member : word ∈ cendDataWords cendLm1Witness)
    (zero : (0 : BitVec 32) &&& mask ≠ target)
    (check : (cendDatapathWords cendLm1Witness).all (fun d => d &&& mask != target) =
      true) :
    word &&& mask ≠ target := by
  rcases List.mem_cons.mp member with rfl | later
  · exact zero
  · exact cendDatapathWords_mask_ne mask target word later check

/-- **No half-mix is the target high word.** -/
theorem cendHalfMixWords_ne_target_high (word : BitVec 32)
    (member : word ∈ cendHalfMixWords cendLm1Witness) :
    word ≠ (byteSwap64 cendLm1Witness).extractLsb' 32 32 := by
  obtain ⟨hi, hhi, lo, hlo, rfl⟩ := cendHalfMixWords_exists _ _ member
  rw [cendLm1Witness_target_high]
  intro same
  have highEq : hi &&& 0xffff0000 = (0xefcd0000 : BitVec 32) := by
    have h := congrArg (fun word => word &&& 0xffff0000) same
    rw [cendHalfMix_high] at h
    rw [show (0xefcdab89 : BitVec 32) &&& 0xffff0000 = 0xefcd0000 from by decide] at h
    exact h
  exact cendDataWords_mask_ne (0xffff0000) (0xefcd0000) hi hhi (by decide)
    cendDatapathWords_highMask_efcd_check highEq

/-- **No half-mix is the target low word.** -/
theorem cendHalfMixWords_ne_target_low (word : BitVec 32)
    (member : word ∈ cendHalfMixWords cendLm1Witness) :
    word ≠ (byteSwap64 cendLm1Witness).extractLsb' 0 32 := by
  obtain ⟨hi, hhi, lo, hlo, rfl⟩ := cendHalfMixWords_exists _ _ member
  rw [cendLm1Witness_target_low]
  intro same
  have lowEq : lo &&& 0x0000ffff = (0x00002301 : BitVec 32) := by
    have h := congrArg (fun word => word &&& 0x0000ffff) same
    rw [cendHalfMix_low] at h
    rw [show (0x67452301 : BitVec 32) &&& 0x0000ffff = 0x00002301 from by decide] at h
    exact h
  exact cendDataWords_mask_ne (0x0000ffff) (0x00002301) lo hlo (by decide)
    cendDatapathWords_lowMask_2301_check lowEq

/-! ## 4. Masks and merges -/

theorem halfMask_pair_value (a b : Bool) :
    ((if a then (0xffff : BitVec 32) <<< 16 else 0) |||
      (if b then (0xffff : BitVec 32) else 0)) ∈
        [0, BitVec.allOnes 32, (0xffff0000 : BitVec 32), 0x0000ffff] := by
  cases a <;> cases b <;> decide

theorem allOnes_single_mem (a : Bool) :
    (if a then BitVec.allOnes 32 else (0 : BitVec 32)) ∈
      [0, BitVec.allOnes 32, (0xffff0000 : BitVec 32), 0x0000ffff] := by
  cases a <;> decide

/-- At the two observed data-word indices every selected-word mask is one of the
four half masks. -/
theorem selectedWordMask_lt_two_cases (flags : BitVec 4) (longLong : Bool)
    (index : Fin 4) (lt : index.val < 2) :
    selectedWordMask flags longLong index = 0 ∨
      selectedWordMask flags longLong index = BitVec.allOnes 32 ∨
      selectedWordMask flags longLong index = 0xffff0000 ∨
      selectedWordMask flags longLong index = 0x0000ffff := by
  have h01 : index.val = 0 ∨ index.val = 1 := by omega
  rcases h01 with h | h
  · have hindex : index = (⟨0, by decide⟩ : Fin 4) := Fin.ext h
    subst hindex
    cases longLong
    · simp only [selectedWordMask, Nat.zero_lt_two, if_true]
      simpa [List.mem_cons] using halfMask_pair_value (flags.getLsbD 3) (flags.getLsbD 2)
    · simp only [selectedWordMask]
      simpa [List.mem_cons] using allOnes_single_mem (flags.getLsbD 3)
  · have hindex : index = (⟨1, by decide⟩ : Fin 4) := Fin.ext h
    subst hindex
    cases longLong
    · simp only [selectedWordMask, Nat.one_lt_two, if_true]
      simpa [List.mem_cons] using halfMask_pair_value (flags.getLsbD 1) (flags.getLsbD 0)
    · simp only [selectedWordMask]
      simpa [List.mem_cons] using allOnes_single_mem (flags.getLsbD 2)

/-- **The merge of a half-mix with a data word stays in the half-mix set.** -/
theorem mergeSelectedWord_halfMix_mem (x : BitVec 64) (old data mask : BitVec 32)
    (hold : old ∈ cendHalfMixWords x) (hdata : data ∈ cendDataWords x)
    (hmask : mask = 0 ∨ mask = BitVec.allOnes 32 ∨
      mask = 0xffff0000 ∨ mask = 0x0000ffff) :
    mergeSelectedWord old data mask ∈ cendHalfMixWords x := by
  obtain ⟨hi, hhi, lo, hlo, rfl⟩ := cendHalfMixWords_exists _ _ hold
  rcases hmask with rfl | rfl | rfl | rfl
  · rw [show mergeSelectedWord (cendHalfMix hi lo) data 0 = cendHalfMix hi lo from by
      unfold mergeSelectedWord
      rw [show ~~~(0 : BitVec 32) = BitVec.allOnes 32 from by decide]
      rw [show cendHalfMix hi lo &&& (BitVec.allOnes 32) = cendHalfMix hi lo from
        BitVec.and_allOnes]
      rw [show data &&& (0 : BitVec 32) = 0 from BitVec.and_zero]
      rw [show (cendHalfMix hi lo) ||| (0 : BitVec 32) = cendHalfMix hi lo from BitVec.or_zero]]
    exact cendHalfMixWords_mem x hi lo hhi hlo
  · rw [show mergeSelectedWord (cendHalfMix hi lo) data (BitVec.allOnes 32) =
        cendHalfMix data data from by
      unfold mergeSelectedWord
      rw [show ~~~(BitVec.allOnes 32 : BitVec 32) = 0 from by decide]
      rw [show cendHalfMix hi lo &&& (0 : BitVec 32) = 0 from BitVec.and_zero]
      rw [show data &&& (BitVec.allOnes 32) = data from BitVec.and_allOnes]
      rw [show (0 : BitVec 32) ||| data = data from BitVec.zero_or]
      unfold cendHalfMix
      rw [← BitVec.and_or_distrib_left,
        show (0xffff0000 : BitVec 32) ||| 0x0000ffff = BitVec.allOnes 32 from by decide]
      exact (BitVec.and_allOnes).symm]
    exact cendHalfMixWords_mem x data data hdata hdata
  · rw [show mergeSelectedWord (cendHalfMix hi lo) data 0xffff0000 = cendHalfMix data lo from by
      unfold mergeSelectedWord
      rw [show ~~~(0xffff0000 : BitVec 32) = 0x0000ffff from by decide]
      rw [show cendHalfMix hi lo &&& 0x0000ffff = lo &&& 0x0000ffff from cendHalfMix_low hi lo]
      unfold cendHalfMix
      exact BitVec.or_comm _ _]
    exact cendHalfMixWords_mem x data lo hdata hlo
  · rw [show mergeSelectedWord (cendHalfMix hi lo) data 0x0000ffff = cendHalfMix hi data from by
      unfold mergeSelectedWord
      rw [show ~~~(0x0000ffff : BitVec 32) = 0xffff0000 from by decide]
      rw [show cendHalfMix hi lo &&& 0xffff0000 = hi &&& 0xffff0000 from cendHalfMix_high hi lo]
      unfold cendHalfMix
      rfl]
    exact cendHalfMixWords_mem x hi data hhi hdata

/-! ## 5. Trust report -/

#print axioms cendALU_dataWord_mem
#print axioms cendDatapathWords_targetHalves_avoid
#print axioms cendHalfMixWords_ne_target_high
#print axioms cendHalfMixWords_ne_target_low
#print axioms selectedWordMask_lt_two_cases
#print axioms mergeSelectedWord_halfMix_mem

end ProofsLean.MNCore
