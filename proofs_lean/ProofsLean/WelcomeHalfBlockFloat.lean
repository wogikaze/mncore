import ProofsLean.WelcomeResiduals

/-! # The half-precision block-float writer

`WelcomeResiduals.lean` split the block-float writer case into the low
precisions `.d`/`.f`/`.g` (proved) and the remaining non-low case
(`WelcomePEBlockFloatNonLowWriterShapeObligation`).  For a block-float row
`parsedExprIsBlockFloatProducer` admits only `.d`, `.f`, `.g` and `.h`, and the
lowering preserves the row's precision, so the non-low case is exactly the
`.h` (half) writer.

The `.h` case is not an instance of the existing fold lemma
`welcomePEBlockFloatMabShape_of_busCopy`: that lemma needs the third word of
`parsedBlockFloatMab .h keep extended buses pe` to be a copy for **arbitrary**
input buses, which is false (`parsedBlockFloatMab_h_third_word_not_copy`).
What is available is the *read*: the block-float stage always reads at
`welcomeInitialState welcomeZeroWords`, where every forward slot is poison
(so a forwarding source would fail) and every memory read is the zero bus.
Hence every successful input bus is built from half lanes that are either
below `2^9` (a `.fixed` value of `0`, `1`, `2`, `3`, or `32768` at the zero
coordinate) or the sign mask `32768`; on such values `parsedBlockFloat .half`
takes the `maxExponent = 0` branch and returns `0` or `32768`
(`parsedBlockFloat_half_nice`).  Every output lane is therefore a sign lane,
so the third word is a copy.

This module formalises that read analysis and feeds it into the same fold over
`allMABCoordinates` used for the low precisions:

1. `halfBlockFloatMab_word_two_copy`: the `.h` third-word copy from input buses
   whose lanes are small-or-sign (`HalfLaneValue`).
2. `readPEs_halfBusValue` / `blockFloatZero_readPEs_halfCopy`: the read analysis
   at the all-zero state, including the `.fixed`/`.mem`/`.forward` case split.
3. `executeParsedBlockFloatAtMAB_runCycles_lm1Facts_read` and
   `welcomePEBlockFloatMabShape_of_readCopy`: the per-coordinate fold with the
   copy hypothesis restricted to the buses the stage actually reads.
4. `executeParsedBlockFloatProducer_shape_of_singleton_half`: the `.h` stage
   shape at PE 0.
5. `welcomePEBlockFloatNonLowWriterShapeObligation`: the obligation, through
   `WelcomePEBlockFloatWriterShapeObligation`'s split and the shared assembly
   of `WelcomeResiduals.lean`.

No `sorry`, no `admit`, no `native_decide`, no new axioms.  No existing module
is edited.  Neither `LowerBound welcomeSealedMachine welcomeSpec 2` nor
`Optimal welcomeSealedMachine welcomeSpec welcomeAnswer` is claimed: the
remaining residuals are the `flagEq` plain/masked companion case and the final
assembly, as recorded in `WelcomeResiduals.lean`. -/

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

namespace ProofsLean.MNCore

open Issue
open PEMemory

/-! ## 1. The `.h` block-float datapath -/

/-- An input half lane that the zero state can produce: below `2^9` (so its
exponent field is zero) or the sign mask. -/
def HalfLaneValue (v : Nat) : Prop := v < 512 ∨ v = 32768

/-- A converted half lane: zero or the sign mask. -/
def HalfSignLane (v : Nat) : Prop := v = 0 ∨ v = 32768

/-- The 16-bit lane of a bus read by the `.h` block-float datapath. -/
def halfReadLane (bus : IntegerALU.Bus) (lane : Nat) : Nat :=
  if lane < 4 then bus.high.extractLsb' (48 - 16 * lane) 16 |>.toNat
  else bus.low.extractLsb' (48 - 16 * (lane - 4)) 16 |>.toNat

/-- The four PEs contributing to one exponent block of the half datapath. -/
def halfPositions (lane : Nat) : List (Fin 4 × Nat) :=
  (List.finRange 4).flatMap fun pe =>
    (List.range 4).map fun offset => (pe, (lane / 4) * 4 + offset)

/-- One converted lane of the half block-float datapath. -/
def halfConvertedLane (inputs : Fin 4 → IntegerALU.Bus) (keep : Nat) (extended : Bool)
    (pe : Fin 4) (lane : Nat) : Nat :=
  (parsedBlockFloat (parsedFloatFormat .h)
    ((halfPositions lane).map fun (sourcePE, sourceLane) =>
      halfReadLane (inputs sourcePE) sourceLane) keep extended)[
        (halfPositions lane).idxOf (pe, lane)]!

/-- The eight output lanes of the half datapath at one PE. -/
def halfLanes (inputs : Fin 4 → IntegerALU.Bus) (keep : Nat) (extended : Bool)
    (pe : Fin 4) : List Nat := (List.range 8).map (halfConvertedLane inputs keep extended pe)

/-- The `.h` branch of `parsedBlockFloatMab`, written out so that its local
definitions can be reasoned about. -/
def halfBlockFloatMab (keep : Nat) (extended : Bool)
    (inputs : Fin 4 → IntegerALU.Bus) : Fin 4 → IntegerALU.Bus := Id.run do
  let laneCount := 8
  let laneWidth := 16
  let readLane (pe : Fin 4) (lane : Nat) : Nat :=
    let bus := inputs pe
    if lane < 4 then bus.high.extractLsb' (48 - 16 * lane) 16 |>.toNat
    else bus.low.extractLsb' (48 - 16 * (lane - 4)) 16 |>.toNat
  let positionsFor (lane : Nat) : List (Fin 4 × Nat) :=
    (List.finRange 4).flatMap fun pe =>
      (List.range 4).map fun offset => (pe, (lane / 4) * 4 + offset)
  let convertedLane (pe : Fin 4) (lane : Nat) : Nat := Id.run do
    let positions := positionsFor lane
    let values := positions.map fun (sourcePE, sourceLane) => readLane sourcePE sourceLane
    let converted := parsedBlockFloat (parsedFloatFormat .h) values keep extended
    let targetIndex := positions.idxOf (pe, lane)
    return converted[targetIndex]!
  return fun pe => Id.run do
    let lanes := (List.range laneCount).map (convertedLane pe)
    if laneWidth == 64 then
      return ⟨BitVec.ofNat 64 lanes[0]!, 0⟩
    else if laneWidth == 32 then
      return ⟨BitVec.ofNat 64 (lanes[0]! * 2 ^ 32 + lanes[1]!), 0⟩
    else
      let high := (List.range 4).foldl (fun acc lane =>
        acc + lanes[lane]! * 2 ^ (48 - 16 * lane)) 0
      let low := (List.range 4).foldl (fun acc lane =>
        acc + lanes[lane + 4]! * 2 ^ (48 - 16 * lane)) 0
      return ⟨BitVec.ofNat 64 high, BitVec.ofNat 64 low⟩

theorem parsedBlockFloatMab_h_eq_half (inputs : Fin 4 → IntegerALU.Bus) (keep : Nat)
    (extended : Bool) :
    parsedBlockFloatMab .h keep extended inputs = halfBlockFloatMab keep extended inputs := rfl

theorem halfBlockFloatMab_low_eq (inputs : Fin 4 → IntegerALU.Bus) (keep : Nat)
    (extended : Bool) (pe : Fin 4) :
    (halfBlockFloatMab keep extended inputs pe).low =
      BitVec.ofNat 64 ((List.range 4).foldl (fun acc lane =>
        acc + (halfLanes inputs keep extended pe)[lane + 4]! * 2 ^ (48 - 16 * lane)) 0) := rfl

/-! ## The arithmetic of `parsedBlockFloat .half` on small lanes -/

theorem foldl_max_zero (l : List Nat) (h : ∀ x ∈ l, x = 0) : l.foldl Nat.max 0 = 0 := by
  induction l with
  | nil => rfl
  | cons a t ih =>
      rw [List.foldl_cons]
      have ha : a = 0 := h a (by simp)
      rw [ha]
      exact ih (fun x hx => h x (by simp [hx]))

/-- **Half block float of small lanes is zero or the sign mask.** -/
theorem parsedBlockFloat_half_nice (values : List Nat) (keep : Nat) (extended : Bool)
    (hsmall : ∀ v ∈ values, HalfLaneValue v) :
    ∀ v ∈ parsedBlockFloat RRN.FloatPrecision.half values keep extended, HalfSignLane v := by
  have hExp : ∀ x ∈ values, x / 2 ^ 9 % 2 ^ 6 = 0 := by
    intro x hx
    rcases hsmall x hx with h | h
    · have hdiv : x / 512 = 0 := Nat.div_eq_of_lt (by omega)
      rw [show (2 : Nat) ^ 9 = 512 from by decide, hdiv]
      simp
    · subst h
      decide
  have hmap : values.map (fun x => x / 2 ^ 9 % 2 ^ 6) = values.map (fun _ => 0) := by
    apply List.map_congr_left
    intro x hx
    exact hExp x hx
  have hMax : (values.map (fun x => x / 2 ^ 9 % 2 ^ 6)).foldl Nat.max 0 = 0 := by
    rw [hmap]
    apply foldl_max_zero
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rfl
  intro v hv
  unfold parsedBlockFloat at hv
  rw [List.mem_map] at hv
  obtain ⟨x, hx, rfl⟩ := hv
  simp only [RRN.FloatPrecision.mantissaBits, RRN.FloatPrecision.exponentBits,
    RRN.FloatPrecision.width, RRN.FloatPrecision.exponentMax, hMax, hExp x hx]
  have hCommonLt : ¬ (((0 +
      (if (values.any fun value =>
          value / 2 ^ 9 % 2 ^ 6 == 0 && value % 2 ^ 9 / 2 ^ (9 - keep) == 2 ^ keep - 1) = true
        then 1 else 0)) +
      (if (RRN.FloatPrecision.half == RRN.FloatPrecision.half) = true then 9 - keep else 0)) ≥
        2 ^ 6 - 1) := by
    have h1 : (if (values.any fun value =>
        value / 2 ^ 9 % 2 ^ 6 == 0 && value % 2 ^ 9 / 2 ^ (9 - keep) == 2 ^ keep - 1) = true
        then (1 : Nat) else 0) ≤ 1 := by split <;> omega
    have h2 : (if (RRN.FloatPrecision.half == RRN.FloatPrecision.half) = true
        then (9 - keep : Nat) else 0) ≤ 9 := by
      rw [if_pos (show (RRN.FloatPrecision.half == RRN.FloatPrecision.half) = true from by decide)]
      omega
    have h63 : (2 : Nat) ^ 6 - 1 = 63 := by decide
    omega
  rw [if_neg hCommonLt]
  rw [if_pos (show (0 == 0) = true from by decide)]
  have h15 : (1 + 6 + 9 - 1 : Nat) = 15 := by decide
  rw [h15]
  rcases hsmall x hx with h | h
  · left
    have hdiv : x / 32768 = 0 := Nat.div_eq_of_lt (by omega)
    rw [show (2 : Nat) ^ 15 = 32768 from by decide, hdiv]
  · right
    subst h
    decide

/-- A `!` lookup in a list of sign lanes is a sign lane. -/
theorem getElem!_halfSignLane (l : List Nat) (h : ∀ v ∈ l, HalfSignLane v) (i : Nat) :
    HalfSignLane (l[i]!) := by
  rw [List.getElem!_eq_getElem?_getD]
  cases hl : l[i]? with
  | none =>
      simp only [Option.getD_none, HalfSignLane]
      exact Or.inl rfl
  | some v =>
      simp only [Option.getD_some]
      exact h v (List.mem_of_getElem? hl)

theorem halfConvertedLane_nice (inputs : Fin 4 → IntegerALU.Bus) (keep : Nat)
    (extended : Bool) (pe : Fin 4) (lane : Nat) (hlane : lane < 8)
    (hnice : ∀ (p : Fin 4) (l : Nat), l < 8 → HalfLaneValue (halfReadLane (inputs p) l)) :
    HalfSignLane (halfConvertedLane inputs keep extended pe lane) := by
  unfold halfConvertedLane
  apply getElem!_halfSignLane
  intro v hv
  have hsmall : ∀ x ∈ (halfPositions lane).map (fun (sourcePE, sourceLane) =>
      halfReadLane (inputs sourcePE) sourceLane), HalfLaneValue x := by
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨⟨sourcePE, sourceLane⟩, hpair, rfl⟩ := hx
    rw [halfPositions, List.mem_flatMap] at hpair
    obtain ⟨groupPE, hgroup, hmem⟩ := hpair
    rw [List.mem_map] at hmem
    obtain ⟨offset, hoffset, hEq⟩ := hmem
    injection hEq with hpe hlaneEq
    subst hpe
    subst hlaneEq
    exact hnice groupPE _ (by
      have := List.mem_range.mp hoffset
      omega)
  exact parsedBlockFloat_half_nice _ keep extended hsmall v hv

theorem halfLanes_nice (inputs : Fin 4 → IntegerALU.Bus) (keep : Nat) (extended : Bool)
    (pe : Fin 4)
    (hnice : ∀ (p : Fin 4) (l : Nat), l < 8 → HalfLaneValue (halfReadLane (inputs p) l)) :
    ∀ v ∈ halfLanes inputs keep extended pe, HalfSignLane v := by
  intro v hv
  rw [halfLanes, List.mem_map] at hv
  obtain ⟨lane, hlane, rfl⟩ := hv
  exact halfConvertedLane_nice inputs keep extended pe lane (List.mem_range.mp hlane) hnice

/-! ## The low word of the half datapath -/

theorem halfLanes_length (inputs : Fin 4 → IntegerALU.Bus) (keep : Nat) (extended : Bool)
    (pe : Fin 4) : (halfLanes inputs keep extended pe).length = 8 := by
  simp [halfLanes]

theorem halfLowFold_eq (lanes : List Nat) :
    (List.range 4).foldl (fun acc lane => acc + lanes[lane + 4]! * 2 ^ (48 - 16 * lane)) 0 =
      lanes[4]! * 2 ^ 48 + lanes[5]! * 2 ^ 32 + lanes[6]! * 2 ^ 16 + lanes[7]! := by
  have hr : List.range 4 = [0, 1, 2, 3] := by decide
  rw [hr]
  simp [List.foldl]

theorem halfLowWord_toNat (a b c d : Nat) (ha : a < 2 ^ 16) (hb : b < 2 ^ 16)
    (hc : c < 2 ^ 16) (hd : d < 2 ^ 16) :
    (((BitVec.ofNat 64 (a * 2 ^ 48 + b * 2 ^ 32 + c * 2 ^ 16 + d)).extractLsb' 32 32).toNat) =
      a * 2 ^ 16 + b := by
  rw [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  omega

/-- **The third word of the half datapath is a copy.** -/
theorem halfBlockFloatMab_word_two_copy (inputs : Fin 4 → IntegerALU.Bus) (keep : Nat)
    (extended : Bool) (pe : Fin 4) (bound : 2 < 4)
    (hnice : ∀ (p : Fin 4) (l : Nat), l < 8 → HalfLaneValue (halfReadLane (inputs p) l)) :
    IsWelcomeCopy
      ((unpackALUBus (halfBlockFloatMab keep extended inputs pe)) ⟨2, bound⟩) := by
  rw [unpackALUBus_of_val_eq_two _ ⟨2, bound⟩ rfl]
  rw [halfBlockFloatMab_low_eq]
  rw [halfLowFold_eq]
  have hsign := halfLanes_nice inputs keep extended pe hnice
  have h4 : HalfSignLane ((halfLanes inputs keep extended pe)[4]!) :=
    getElem!_halfSignLane _ hsign 4
  have h5 : HalfSignLane ((halfLanes inputs keep extended pe)[5]!) :=
    getElem!_halfSignLane _ hsign 5
  have h6 : HalfSignLane ((halfLanes inputs keep extended pe)[6]!) :=
    getElem!_halfSignLane _ hsign 6
  have h7 : HalfSignLane ((halfLanes inputs keep extended pe)[7]!) :=
    getElem!_halfSignLane _ hsign 7
  have hbound : ∀ v : Nat, HalfSignLane v → v < 2 ^ 16 := by
    intro v hv
    rcases hv with rfl | rfl <;> decide
  have htoNat := halfLowWord_toNat _ _ _ _ (hbound _ h4) (hbound _ h5) (hbound _ h6) (hbound _ h7)
  have heq : (BitVec.ofNat 64
      ((halfLanes inputs keep extended pe)[4]! * 2 ^ 48 +
        (halfLanes inputs keep extended pe)[5]! * 2 ^ 32 +
        (halfLanes inputs keep extended pe)[6]! * 2 ^ 16 +
        (halfLanes inputs keep extended pe)[7]!)).extractLsb' 32 32 =
      BitVec.ofNat 32 ((halfLanes inputs keep extended pe)[4]! * 2 ^ 16 +
        (halfLanes inputs keep extended pe)[5]!) := by
    apply BitVec.eq_of_toNat_eq
    rw [htoNat, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt]
    have h4' := hbound _ h4
    have h5' := hbound _ h5
    omega
  rw [heq]
  rcases h4 with h4 | h4 <;> rcases h5 with h5 | h5 <;>
    rw [h4, h5] <;> (unfold IsWelcomeCopy welcomeCopyMask; decide)


/-! ## The zero-state read analysis -/

/-- Every 16-bit lane of the bus is a value the zero state can produce. -/
def HalfBusValue (bus : IntegerALU.Bus) : Prop :=
  ∀ l : Nat, l < 8 → HalfLaneValue (halfReadLane bus l)

theorem halfReadLane_nice_of_bus (bus : IntegerALU.Bus) (h : HalfBusValue bus) (l : Nat)
    (hl : l < 8) : HalfLaneValue (halfReadLane bus l) := h l hl

theorem halfBusValue_zero : HalfBusValue (⟨0, 0⟩ : IntegerALU.Bus) := by
  unfold HalfBusValue
  intro l hl
  unfold halfReadLane
  split <;> (simp; unfold HalfLaneValue; decide)

theorem halfBusValue_replicate_of_concrete (v : Nat)
    (hv : v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 ∨ v = 32768) :
    HalfBusValue (replicateIntegerLane .half v) := by
  rcases hv with rfl | rfl | rfl | rfl | rfl
  all_goals
    unfold HalfBusValue
    intro l hl
    have hcases : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3 ∨ l = 4 ∨ l = 5 ∨ l = 6 ∨ l = 7 := by omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      (unfold halfReadLane HalfLaneValue; decide)

theorem fin4_cases (pe : Fin 4) : pe = 0 ∨ pe = 1 ∨ pe = 2 ∨ pe = 3 := by
  rcases pe with ⟨p, hp⟩
  have h : p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 3 := by omega
  rcases h with h | h | h | h
  · left; apply Fin.ext; exact h
  · right; left; apply Fin.ext; exact h
  · right; right; left; apply Fin.ext; exact h
  · right; right; right; apply Fin.ext; exact h

/-- The `.half` fixed value at the zero coordinate is zero, `pe`, or the sign
mask. -/
theorem halfFixedValue_zeroCoordinate (fixed : ParsedFixed) (pe : Fin 4) :
    ParsedFixed.integerValue fixed .half 0 0 0 0 pe = 0 ∨
      ParsedFixed.integerValue fixed .half 0 0 0 0 pe = 1 ∨
      ParsedFixed.integerValue fixed .half 0 0 0 0 pe = 2 ∨
      ParsedFixed.integerValue fixed .half 0 0 0 0 pe = 3 ∨
      ParsedFixed.integerValue fixed .half 0 0 0 0 pe = 32768 := by
  cases fixed with
  | l2bid => exact Or.inl rfl
  | l1bid => exact Or.inl rfl
  | mabid => exact Or.inl rfl
  | peid =>
      rcases fin4_cases pe with h | h | h | h
      · left; rw [h]; rfl
      · right; left; rw [h]; rfl
      · right; right; left; rw [h]; rfl
      · right; right; right; left; rw [h]; rfl
  | subpeid =>
      rcases fin4_cases pe with h | h | h | h
      · left; rw [h]; rfl
      · right; left; rw [h]; rfl
      · right; right; left; rw [h]; rfl
      · right; right; right; left; rw [h]; rfl
  | msb1 =>
      right; right; right; right
      rfl

theorem halfBusValue_fixed_zeroCoordinate (fixed : ParsedFixed) (pe : Fin 4) :
    HalfBusValue (replicateIntegerLane .half
      (ParsedFixed.integerValue fixed .half 0 0 0 0 pe)) := by
  exact halfBusValue_replicate_of_concrete _
    (halfFixedValue_zeroCoordinate fixed pe)

/-- The coordinate context fields of the zero coordinate. -/
theorem zeroCoordinate_group (pe : Fin 4) :
    (ParsedIntegerContext.ofLinearIndex
      (physicalPEId (⟨0, 0, 0, 0⟩ : MABCoordinate) pe)).group = 0 := by
  apply Fin.ext
  simp [ParsedIntegerContext.ofLinearIndex, physicalPEId]
  have := pe.isLt
  omega

theorem zeroCoordinate_l2b (pe : Fin 4) :
    (ParsedIntegerContext.ofLinearIndex
      (physicalPEId (⟨0, 0, 0, 0⟩ : MABCoordinate) pe)).l2b = 0 := by
  apply Fin.ext
  simp [ParsedIntegerContext.ofLinearIndex, physicalPEId]
  have := pe.isLt
  omega

theorem zeroCoordinate_l1b (pe : Fin 4) :
    (ParsedIntegerContext.ofLinearIndex
      (physicalPEId (⟨0, 0, 0, 0⟩ : MABCoordinate) pe)).l1b = 0 := by
  apply Fin.ext
  simp [ParsedIntegerContext.ofLinearIndex, physicalPEId]
  have := pe.isLt
  omega

theorem zeroCoordinate_mab (pe : Fin 4) :
    (ParsedIntegerContext.ofLinearIndex
      (physicalPEId (⟨0, 0, 0, 0⟩ : MABCoordinate) pe)).mab = 0 := by
  apply Fin.ext
  simp [ParsedIntegerContext.ofLinearIndex, physicalPEId]
  have := pe.isLt
  omega

theorem zeroCoordinate_pe (pe : Fin 4) :
    (ParsedIntegerContext.ofLinearIndex
      (physicalPEId (⟨0, 0, 0, 0⟩ : MABCoordinate) pe)).pe = pe := by
  apply Fin.ext
  simp [ParsedIntegerContext.ofLinearIndex, physicalPEId]
  try omega

theorem halfRead_rounding_zero (rounded : Bool) :
    ParsedIntegerInput.applyRounding rounded (⟨0, 0⟩ : IntegerALU.Bus) = ⟨0, 0⟩ := by
  cases rounded
  · rfl
  · unfold ParsedIntegerInput.applyRounding
    decide

theorem zeroForwardingSlots_poison (pe : PEId) :
    stateForwardingSlots (welcomeInitialState welcomeZeroWords) pe =
      fun _ _ => Forwarding.Value.poison := by
  funext unit cycle
  simp [stateForwardingSlots, welcomeInitialState, rustSimulatorInitialState_forwarding_invalid]


/-! ## The per-source zero read -/

theorem halfFixedValue_zeroCoordinateContext (fixed : ParsedFixed) (pe : Fin 4) :
    ParsedFixed.integerValue fixed .half
      (ParsedIntegerContext.ofLinearIndex
        (physicalPEId (⟨0, 0, 0, 0⟩ : MABCoordinate) pe)).group
      (ParsedIntegerContext.ofLinearIndex
        (physicalPEId (⟨0, 0, 0, 0⟩ : MABCoordinate) pe)).l2b
      (ParsedIntegerContext.ofLinearIndex
        (physicalPEId (⟨0, 0, 0, 0⟩ : MABCoordinate) pe)).l1b
      (ParsedIntegerContext.ofLinearIndex
        (physicalPEId (⟨0, 0, 0, 0⟩ : MABCoordinate) pe)).mab
      (ParsedIntegerContext.ofLinearIndex
        (physicalPEId (⟨0, 0, 0, 0⟩ : MABCoordinate) pe)).pe =
      ParsedFixed.integerValue fixed .half 0 0 0 0 pe := by
  rw [zeroCoordinate_group, zeroCoordinate_l2b, zeroCoordinate_l1b, zeroCoordinate_mab,
    zeroCoordinate_pe]

theorem toParsedIntegerInput?_shape
    (operand : ParsedOperand) (precision : IntegerALU.Precision)
    (group : Fin 4) (l2b : Fin 2) (l1b : Fin 8) (mab : Fin 16)
    (pe cycle : Fin 4) (bar0 bar1 : BitVec 12) (tWord : BitVec 32)
    (input : ParsedIntegerInput)
    (lowered : ParsedOperand.toParsedIntegerInput? operand precision group l2b l1b mab pe cycle
      bar0 bar1 tWord = some input) :
    (∃ fixed, input = .fixed (replicateIntegerLane precision
      (ParsedFixed.integerValue fixed precision group l2b l1b mab pe))) ∨
    (∃ access rounded, input = .memory access rounded) ∨
    (∃ kind rounded, input = .forward kind rounded) := by
  cases operand with
  | fixed fixed =>
      exact Or.inl ⟨fixed, (Option.some.inj lowered).symm⟩
  | forward kind negated extended rounded =>
      exact Or.inr (Or.inr ⟨kind, rounded, (Option.some.inj lowered).symm⟩)
  | mem access negated extended rounded mask =>
      cases resolved : ParsedOperand.toDirectMemoryAccess? (.mem access false false false none)
          pe cycle bar0 bar1 tWord with
      | none => simp [ParsedOperand.toParsedIntegerInput?, resolved] at lowered
      | some resolvedAccess =>
          exact Or.inr (Or.inl ⟨resolvedAccess, rounded, by
            simp [ParsedOperand.toParsedIntegerInput?, resolved] at lowered
            exact lowered.symm⟩)
  | bar lm1 width mask =>
      cases resolved : ParsedOperand.toDirectMemoryAccess? (.bar lm1 width mask)
          pe cycle bar0 bar1 tWord with
      | none => simp [ParsedOperand.toParsedIntegerInput?, resolved] at lowered
      | some resolvedAccess =>
          exact Or.inr (Or.inl ⟨resolvedAccess, false, by
            simp [ParsedOperand.toParsedIntegerInput?, resolved] at lowered
            exact lowered.symm⟩)
  | omr entry mask =>
      cases resolved : ParsedOperand.toDirectMemoryAccess? (.omr entry mask)
          pe cycle bar0 bar1 tWord with
      | none => simp [ParsedOperand.toParsedIntegerInput?, resolved] at lowered
      | some resolvedAccess =>
          exact Or.inr (Or.inl ⟨resolvedAccess, false, by
            simp [ParsedOperand.toParsedIntegerInput?, resolved] at lowered
            exact lowered.symm⟩)
  | matrix group' width row =>
      cases resolved : ParsedOperand.toDirectMemoryAccess? (.matrix group' width row)
          pe cycle bar0 bar1 tWord with
      | none => simp [ParsedOperand.toParsedIntegerInput?, resolved] at lowered
      | some resolvedAccess =>
          exact Or.inr (Or.inl ⟨resolvedAccess, false, by
            simp [ParsedOperand.toParsedIntegerInput?, resolved] at lowered
            exact lowered.symm⟩)
  | nowrite =>
      cases resolved : ParsedOperand.toDirectMemoryAccess? .nowrite
          pe cycle bar0 bar1 tWord with
      | none => simp [ParsedOperand.toParsedIntegerInput?, resolved] at lowered
      | some resolvedAccess =>
          exact Or.inr (Or.inl ⟨resolvedAccess, false, by
            simp [ParsedOperand.toParsedIntegerInput?, resolved] at lowered
            exact lowered.symm⟩)
  | l1bm width address =>
      cases resolved : ParsedOperand.toDirectMemoryAccess? (.l1bm width address)
          pe cycle bar0 bar1 tWord with
      | none => simp [ParsedOperand.toParsedIntegerInput?, resolved] at lowered
      | some resolvedAccess =>
          exact Or.inr (Or.inl ⟨resolvedAccess, false, by
            simp [ParsedOperand.toParsedIntegerInput?, resolved] at lowered
            exact lowered.symm⟩)
  | l2bm address l2b' =>
      cases resolved : ParsedOperand.toDirectMemoryAccess? (.l2bm address l2b')
          pe cycle bar0 bar1 tWord with
      | none => simp [ParsedOperand.toParsedIntegerInput?, resolved] at lowered
      | some resolvedAccess =>
          exact Or.inr (Or.inl ⟨resolvedAccess, false, by
            simp [ParsedOperand.toParsedIntegerInput?, resolved] at lowered
            exact lowered.symm⟩)
  | dar address =>
      cases resolved : ParsedOperand.toDirectMemoryAccess? (.dar address)
          pe cycle bar0 bar1 tWord with
      | none => simp [ParsedOperand.toParsedIntegerInput?, resolved] at lowered
      | some resolvedAccess =>
          exact Or.inr (Or.inl ⟨resolvedAccess, false, by
            simp [ParsedOperand.toParsedIntegerInput?, resolved] at lowered
            exact lowered.symm⟩)

theorem zero_read_halfBusValue (accesses : ParsedBlockFloatAccesses)
    (pe : Fin 4) (cycle : Fin 4)
    (input : ParsedIntegerInput) (bus : IntegerALU.Bus)
    (lowered : ParsedOperand.toParsedIntegerInput? accesses.source .half
      (ParsedIntegerContext.ofLinearIndex
        (physicalPEId (⟨0, 0, 0, 0⟩ : MABCoordinate) pe)).group
      (ParsedIntegerContext.ofLinearIndex
        (physicalPEId (⟨0, 0, 0, 0⟩ : MABCoordinate) pe)).l2b
      (ParsedIntegerContext.ofLinearIndex
        (physicalPEId (⟨0, 0, 0, 0⟩ : MABCoordinate) pe)).l1b
      (ParsedIntegerContext.ofLinearIndex
        (physicalPEId (⟨0, 0, 0, 0⟩ : MABCoordinate) pe)).mab
      (ParsedIntegerContext.ofLinearIndex
        (physicalPEId (⟨0, 0, 0, 0⟩ : MABCoordinate) pe)).pe cycle
      ((welcomeInitialState welcomeZeroWords).peContext
        (physicalPEId (⟨0, 0, 0, 0⟩ : MABCoordinate) pe)).bar0
      ((welcomeInitialState welcomeZeroWords).peContext
        (physicalPEId (⟨0, 0, 0, 0⟩ : MABCoordinate) pe)).bar1
      ((welcomeInitialState welcomeZeroWords).peContext
        (physicalPEId (⟨0, 0, 0, 0⟩ : MABCoordinate) pe)).tWord = some input)
    (read : ParsedIntegerInput.readWithForwarding
      ((welcomeInitialState welcomeZeroWords).peRegisters
        (physicalPEId (⟨0, 0, 0, 0⟩ : MABCoordinate) pe))
      (stateForwardingSlots (welcomeInitialState welcomeZeroWords)
        (physicalPEId (⟨0, 0, 0, 0⟩ : MABCoordinate) pe)) cycle input = .ok bus) :
    HalfBusValue bus := by
  rcases toParsedIntegerInput?_shape accesses.source .half
    (ParsedIntegerContext.ofLinearIndex
      (physicalPEId (⟨0, 0, 0, 0⟩ : MABCoordinate) pe)).group
    (ParsedIntegerContext.ofLinearIndex
      (physicalPEId (⟨0, 0, 0, 0⟩ : MABCoordinate) pe)).l2b
    (ParsedIntegerContext.ofLinearIndex
      (physicalPEId (⟨0, 0, 0, 0⟩ : MABCoordinate) pe)).l1b
    (ParsedIntegerContext.ofLinearIndex
      (physicalPEId (⟨0, 0, 0, 0⟩ : MABCoordinate) pe)).mab
    (ParsedIntegerContext.ofLinearIndex
      (physicalPEId (⟨0, 0, 0, 0⟩ : MABCoordinate) pe)).pe cycle
    ((welcomeInitialState welcomeZeroWords).peContext
      (physicalPEId (⟨0, 0, 0, 0⟩ : MABCoordinate) pe)).bar0
    ((welcomeInitialState welcomeZeroWords).peContext
      (physicalPEId (⟨0, 0, 0, 0⟩ : MABCoordinate) pe)).bar1
    ((welcomeInitialState welcomeZeroWords).peContext
      (physicalPEId (⟨0, 0, 0, 0⟩ : MABCoordinate) pe)).tWord
    input lowered with
    ⟨fixed, rfl⟩ | ⟨access, rounded, rfl⟩ | ⟨kind, rounded, rfl⟩
  · simp only [ParsedIntegerInput.readWithForwarding, ParsedIntegerInput.read,
      StepResult.ok.injEq] at read
    subst read
    rw [halfFixedValue_zeroCoordinateContext]
    exact halfBusValue_fixed_zeroCoordinate fixed pe
  · simp only [ParsedIntegerInput.readWithForwarding, ParsedIntegerInput.read,
      StepResult.ok.injEq] at read
    subst read
    show HalfBusValue (ParsedIntegerInput.applyRounding rounded
      (pack (readDirectAccess (welcomeInitialPERegisters welcomeZeroWords) access)))
    rw [welcomeZero_pack_readDirectAccess_zero, halfRead_rounding_zero]
    exact halfBusValue_zero
  · rw [zeroForwardingSlots_poison] at read
    simp [ParsedIntegerInput.readWithForwarding] at read


theorem readPEs_halfBusValue (accesses : ParsedBlockFloatAccesses)
    (half : accesses.precision = .h) (cycle : Fin 4) :
    ∀ (pes : List (Fin 4)) (buses0 buses : Fin 4 → IntegerALU.Bus),
      (∀ pe, HalfBusValue (buses0 pe)) →
      executeParsedBlockFloatAtMAB.readPEs (welcomeInitialState welcomeZeroWords)
        (⟨0, 0, 0, 0⟩ : MABCoordinate) accesses cycle pes buses0 = .ok buses →
      ∀ pe, HalfBusValue (buses pe) := by
  intro pes
  induction pes with
  | nil =>
      intro buses0 buses h0 ran
      rw [executeParsedBlockFloatAtMAB.readPEs.eq_1] at ran
      obtain rfl := StepResult.ok.inj ran
      exact h0
  | cons pe rest ih =>
      intro buses0 buses h0 ran
      rw [executeParsedBlockFloatAtMAB.readPEs.eq_2] at ran
      dsimp only at ran
      split at ran
      · rename_i source lowered
        rw [half] at lowered
        split at ran
        · simp at ran
        · simp at ran
        · rename_i bus read
          exact ih (fun other => if (other == pe) = true then bus else buses0 other) buses
            (by
              intro other
              by_cases same : other = pe
              · subst same
                simp only [beq_self_eq_true, if_true]
                exact zero_read_halfBusValue accesses other cycle source bus lowered read
              · have hne : (other == pe) = false := by simp [same]
                simp only [hne, Bool.false_eq_true, if_false]
                exact h0 other)
            ran
      · simp at ran

theorem blockFloatZero_readPEs_halfCopy (accesses : ParsedBlockFloatAccesses)
    (half : accesses.precision = .h) (cycle : Fin 4) (inputBuses : Fin 4 → IntegerALU.Bus)
    (ran : executeParsedBlockFloatAtMAB.readPEs (welcomeInitialState welcomeZeroWords)
      (⟨0, 0, 0, 0⟩ : MABCoordinate) accesses cycle (List.finRange 4)
      (fun _ => (⟨0, 0⟩ : IntegerALU.Bus)) = .ok inputBuses) :
    ∀ (pe : Fin 4) (bound : 2 < 4),
      IsWelcomeCopy ((unpackALUBus (parsedBlockFloatMab accesses.precision accesses.keep
        accesses.extended inputBuses pe)) ⟨2, bound⟩) := by
  intro pe bound
  have hbuses : ∀ p, HalfBusValue (inputBuses p) :=
    readPEs_halfBusValue accesses half cycle (List.finRange 4)
      (fun _ => (⟨0, 0⟩ : IntegerALU.Bus)) inputBuses
      (fun _ => halfBusValue_zero) ran
  rw [half, parsedBlockFloatMab_h_eq_half]
  exact halfBlockFloatMab_word_two_copy inputBuses accesses.keep accesses.extended pe bound
    (fun p l hl => halfReadLane_nice_of_bus (inputBuses p) (hbuses p) l hl)


theorem executeParsedBlockFloatAtMAB_runCycles_lm1Facts_read
    (accesses : ParsedBlockFloatAccesses)
    (readCycle : Fin 4 → StepResult (Fin 4 → IntegerALU.Bus))
    (writeCycle : Fin 4 → (Fin 4 → IntegerALU.Bus) → (Fin 4 → IntegerRegisterFiles) →
      (Fin 4 → BitVec 12) → (Fin 4 → BitVec 12) → (Fin 4 → Fin 4 → IntegerALU.Bus) →
      StepResult (Fin 4 → IntegerRegisterFiles × BitVec 12 × BitVec 12 × (Fin 4 → IntegerALU.Bus)))
    (w : PEMemory.Width)
    (writeFacts : ∀ (cycle : Fin 4) (buses : Fin 4 → IntegerALU.Bus)
      (busesCopy : ∀ (pe : Fin 4) (bound : 2 < 4),
        IsWelcomeCopy ((unpackALUBus (buses pe)) ⟨2, bound⟩))
      (files : Fin 4 → IntegerRegisterFiles) (bar0 bar1 : Fin 4 → BitVec 12)
      (outputs : Fin 4 → Fin 4 → IntegerALU.Bus)
      (results : Fin 4 → IntegerRegisterFiles × BitVec 12 × BitVec 12 × (Fin 4 → IntegerALU.Bus)),
      writeCycle cycle buses files bar0 bar1 outputs = .ok results →
      ∀ target : Fin 4, ∃ writes, (results target).1 = commitParsedMaskedWrites (files target) writes ∧
        Lm1WriteFacts w writes ∧
        (writes.filter PreparedParsedMaskedWrite.isLm1Write).length ≤ 1)
    (readCopy : ∀ (cycle : Fin 4) (buses : Fin 4 → IntegerALU.Bus),
      readCycle cycle = .ok buses →
      ∀ (pe : Fin 4) (bound : 2 < 4),
        IsWelcomeCopy ((unpackALUBus (parsedBlockFloatMab accesses.precision accesses.keep
          accesses.extended buses pe)) ⟨2, bound⟩))
    (target : Fin 4) :
    ∀ (cycles : List (Fin 4)) (files : Fin 4 → IntegerRegisterFiles)
      (bar0 bar1 : Fin 4 → BitVec 12) (outputs : Fin 4 → Fin 4 → IntegerALU.Bus)
      (results : Fin 4 → IntegerRegisterFiles × BitVec 12 × BitVec 12 × (Fin 4 → IntegerALU.Bus)),
      executeParsedBlockFloatAtMAB.runCycles accesses readCycle writeCycle cycles files bar0 bar1
        outputs = .ok results →
      ∃ writes, (results target).1 = commitParsedMaskedWrites (files target) writes ∧
        Lm1WriteFacts w writes ∧
        (writes.filter PreparedParsedMaskedWrite.isLm1Write).length ≤ cycles.length := by
  intro cycles
  induction cycles with
  | nil =>
      intro files bar0 bar1 outputs results executed
      rw [executeParsedBlockFloatAtMAB.runCycles.eq_1] at executed
      obtain rfl := StepResult.ok.inj executed
      exact ⟨[], rfl, lm1WriteFacts_nil w, by simp⟩
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
          obtain ⟨headWrites, headCommit, headShape, headCount⟩ :=
            writeFacts cycle
              (parsedBlockFloatMab accesses.precision accesses.keep accesses.extended inputBuses)
              (readCopy cycle inputBuses ranRead)
              files bar0 bar1 outputs results' ranWrite target
          obtain ⟨tailWrites, tailCommit, tailShape, tailCount⟩ :=
            ih (fun pe => (results' pe).1) (fun pe => (results' pe).2.1)
              (fun pe => (results' pe).2.2.1) (fun pe index => (results' pe).2.2.2 index)
              results executed
          refine ⟨headWrites ++ tailWrites, ?_, ?_, ?_⟩
          · rw [tailCommit, headCommit, commitParsedMaskedWrites_append]
          · exact lm1WriteFacts_append w headWrites tailWrites headShape tailShape
          · rw [List.filter_append, List.length_append]
            have bound : (headWrites.filter PreparedParsedMaskedWrite.isLm1Write).length +
                (tailWrites.filter PreparedParsedMaskedWrite.isLm1Write).length ≤
                rest.length + 1 := by omega
            simpa [List.length_cons] using bound

theorem welcomePEBlockFloatMabShape_of_readCopy
    (readState currentState : State) (expression : ParsedExpr) (coordinate : MABCoordinate)
    (noForward hasSingleLineMask : Bool) (next : State)
    (accesses : ParsedBlockFloatAccesses) (w : PEMemory.Width)
    (lowered : lowerParsedBlockFloat? expression = some accesses)
    (staticWidth : ∀ destination ∈ accesses.destinations,
      ∀ (bank : PEMemory.Bank) (width : PEMemory.Width),
        ParsedOperand.directDestinationBankWidth? destination = some (bank, width) →
          bank = PEMemory.Bank.lm1 → width = w)
    (countBound : (accesses.destinations.filter ParsedOperand.isLm1MemoryDestination).length ≤ 1)
    (readCopy : ∀ (cycle : Fin 4) (inputBuses : Fin 4 → IntegerALU.Bus),
      executeParsedBlockFloatAtMAB.readPEs readState coordinate accesses cycle (List.finRange 4)
        (fun _ => (⟨0, 0⟩ : IntegerALU.Bus)) = .ok inputBuses →
      ∀ (pe : Fin 4) (bound : 2 < 4),
        IsWelcomeCopy ((unpackALUBus (parsedBlockFloatMab accesses.precision accesses.keep
          accesses.extended inputBuses pe)) ⟨2, bound⟩))
    (executed : executeParsedBlockFloatAtMAB readState currentState expression coordinate
      noForward hasSingleLineMask = .ok next) :
    ∀ pe : Fin 4,
      ∃ writes : List PreparedParsedMaskedWrite,
        next.peRegisters (physicalPEId coordinate pe) =
          commitParsedMaskedWrites
            (currentState.peRegisters (physicalPEId coordinate pe)) writes ∧
        (Lm1WritesDoubleCopy writes ∨ Lm1WritesNarrow writes) := by
  intro pe
  rw [executeParsedBlockFloatAtMAB.eq_1, lowered] at executed
  dsimp only at executed
  split at executed
  · simp at executed
  · simp at executed
  · rename_i results ran
    rw [Id.run_pure] at executed
    simp only [StepResult.ok.injEq] at executed
    obtain ⟨writes, committed, shape, count⟩ :=
      executeParsedBlockFloatAtMAB_runCycles_lm1Facts_read accesses _ _ w
        (fun cycle buses busesCopy files bar0 bar1 outputs results h target =>
          executeParsedBlockFloat_writeCycle_lm1Facts currentState hasSingleLineMask expression coordinate accesses w
            staticWidth countBound _ (fun _ _ _ _ _ _ => rfl) cycle buses busesCopy files bar0 bar1
            outputs results h target)
        (by
          intro cycle buses h
          exact readCopy cycle buses h)
        pe [0, 1, 2, 3] _ _ _ _ results ran
    subst executed
    refine ⟨writes, ?_, ?_⟩
    · rw [blockFloatFoldl_peRegisters_target noForward coordinate results pe
        (List.finRange 4) currentState (List.nodup_finRange 4) (List.mem_finRange pe)]
      simpa using committed
    · by_cases isDouble : w = PEMemory.Width.double
      · left
        rw [isDouble] at shape
        exact lm1WriteFacts_doubleCopy writes shape
      · right
        exact lm1WriteFacts_narrow writes w shape isDouble (by simpa using count)

/-- The block-float coordinate `⟨0,0,0,0⟩` shape at PE 0 for half precision. -/
theorem executeParsedBlockFloatAtMAB_zero_shape_half
    (state next : State) (expression : ParsedExpr)
    (noForward hasSingleLineMask : Bool)
    (accesses : ParsedBlockFloatAccesses) (w : PEMemory.Width)
    (lowered : lowerParsedBlockFloat? expression = some accesses)
    (staticWidth : ∀ destination ∈ accesses.destinations,
      ∀ (bank : PEMemory.Bank) (width : PEMemory.Width),
        ParsedOperand.directDestinationBankWidth? destination = some (bank, width) →
          bank = PEMemory.Bank.lm1 → width = w)
    (countBound : (accesses.destinations.filter ParsedOperand.isLm1MemoryDestination).length ≤ 1)
    (half : accesses.precision = .h)
    (executed : executeParsedBlockFloatAtMAB (welcomeInitialState welcomeZeroWords) state expression
      ⟨0, 0, 0, 0⟩ noForward hasSingleLineMask = .ok next) :
    ∃ writes, next.peRegisters welcomePE =
      commitParsedMaskedWrites (state.peRegisters welcomePE) writes ∧
      Lm1WritesShape writes := by
  obtain ⟨writes, committed, shape⟩ :=
    welcomePEBlockFloatMabShape_of_readCopy (welcomeInitialState welcomeZeroWords) state expression
      ⟨0, 0, 0, 0⟩ noForward hasSingleLineMask next accesses w lowered staticWidth countBound
      (fun cycle inputBuses ran => blockFloatZero_readPEs_halfCopy accesses half cycle inputBuses ran)
      executed 0
  rw [physicalPEId_zero_zero] at committed
  exact ⟨writes, committed, shape⟩

theorem executeParsedBlockFloatProducer_shape_of_singleton_half
    (currentState next : State) (expressions : List ParsedExpr) (e : ParsedExpr)
    (noForward hasSingleLineMask : Bool)
    (filtered : expressions.filter parsedExprIsBlockFloatProducer = [e])
    (accesses : ParsedBlockFloatAccesses)
    (lowered : lowerParsedBlockFloat? e = some accesses)
    (half : accesses.precision = .h)
    (nodup : (e.toIssueExpr 0).writeBanks.Nodup)
    (executed : executeParsedBlockFloatProducer (welcomeInitialState welcomeZeroWords)
      currentState expressions noForward hasSingleLineMask = .ok next) :
    ∃ writes, next.peRegisters welcomePE =
      commitParsedMaskedWrites (currentState.peRegisters welcomePE) writes ∧
      Lm1WritesShape writes := by
  have staticWidth : ∀ destination ∈ accesses.destinations,
      ∀ (bank : PEMemory.Bank) (width : PEMemory.Width),
        ParsedOperand.directDestinationBankWidth? destination = some (bank, width) →
          bank = PEMemory.Bank.lm1 → width = (lm1StaticWidth e).getD PEMemory.Width.word := by
    intro destination member bank width resolved bankEq
    rw [lowerParsedBlockFloat?_destinations e accesses lowered] at member
    rw [bankEq] at resolved
    exact lm1StaticWidth_spec e nodup destination member width resolved
  have countBound : (accesses.destinations.filter ParsedOperand.isLm1MemoryDestination).length ≤ 1 := by
    rw [lowerParsedBlockFloat?_destinations e accesses lowered]
    exact lm1Destinations_count_le_one e 0 nodup
  simp only [executeParsedBlockFloatProducer, filtered] at executed
  rw [allMABCoordinates_eq_zero_cons] at executed
  refine executeParsedBlockFloatAtMABs_shape_at_zero (welcomeInitialState welcomeZeroWords) e
    noForward hasSingleLineMask (allMABCoordinates.drop 1) currentState next ?_ ?_ executed
  · intro state' next' ran
    exact executeParsedBlockFloatAtMAB_zero_shape_half state' next' e noForward hasSingleLineMask
      accesses ((lm1StaticWidth e).getD PEMemory.Width.word) lowered staticWidth countBound half ran
  · intro coordinate member pe same
    exact zero_not_mem_allMABCoordinates_drop
      (by rw [physicalPEId_welcomePE_eq coordinate pe same] at member; exact member)


theorem lowerParsedBlockFloat?_precision_cases (expression : ParsedExpr)
    (accesses : ParsedBlockFloatAccesses)
    (lowered : lowerParsedBlockFloat? expression = some accesses) :
    accesses.precision = .d ∨ accesses.precision = .f ∨
      accesses.precision = .g ∨ accesses.precision = .h := by
  obtain ⟨op, sources, destinations, flush, text⟩ := expression
  simp only [lowerParsedBlockFloat?] at lowered
  repeat' (first
    | split at lowered
    | simp_all
    | rw [Option.bind_eq_some_iff] at lowered
    | rcases lowered with ⟨_, _, lowered⟩)

theorem lowerParsedBlockFloat?_half_of_not_low (expression : ParsedExpr)
    (accesses : ParsedBlockFloatAccesses)
    (lowered : lowerParsedBlockFloat? expression = some accesses)
    (notLow : ¬ (accesses.precision = .d ∨ accesses.precision = .f ∨
      accesses.precision = .g)) :
    accesses.precision = .h := by
  rcases lowerParsedBlockFloat?_precision_cases expression accesses lowered with
    h | h | h | h
  · exact absurd (Or.inl h) notLow
  · exact absurd (Or.inr (Or.inl h)) notLow
  · exact absurd (Or.inr (Or.inr h)) notLow
  · exact h


theorem welcomePEBlockFloatNonLowWriterShapeObligation :
    WelcomePEBlockFloatNonLowWriterShapeObligation := by
  intro expressions unrefuted ⟨e, eMem, eWriter, isBlock, notLow⟩
  apply welcomePEWriteShape_of_commit_shape
  intro next step
  have executed := welcomeSealed_step_ok step
  simp only [executeNormalizedLine, NormalizedLine.toInstruction?,
    Issue.InstructionLine.toNormalizedLine] at executed
  obtain ⟨accepted, waits, unsupported, supported⟩ :=
    executeIntegerProducerInstructionLine_pe_conditions expressions
      (welcomeInitialState welcomeZeroWords) next executed
  obtain ⟨nextPEs, nextMsl, nextRelu, nextBlockFloat, afterMatrix, nextShared, nextBroadcast,
    walkExecuted, mslExecuted, reluExecuted, blockExecuted, matrixExecuted, sharedExecuted,
    l1Executed, nextEq⟩ :=
    executeIntegerProducerInstructionLine_pe_stages_exists expressions
      (welcomeInitialState welcomeZeroWords) next accepted waits unsupported supported executed
  have rows := welcomeLm1Writer_rows expressions unrefuted e eMem eWriter
  have eNodup := welcomeLm1Writer_nodup expressions unrefuted e eMem
  obtain ⟨eMslFalse, eReluFalse, eMatrixFalse, eL1False, eFloatFalse, eIntFalse⟩ :=
    welcomeBlockFloat_stageProfile e isBlock
  have eFilterMem : e ∈ (expressions.map NormalizedExpr.toParsed).filter
      parsedExprIsBlockFloatProducer :=
    List.mem_filter.mpr ⟨eMem, isBlock⟩
  have blockFilter : (expressions.map NormalizedExpr.toParsed).filter
      parsedExprIsBlockFloatProducer = [e] :=
    filter_singleton_of_length_le_one parsedExprIsBlockFloatProducer _ e eFilterMem
      (blockFloatFilter_length_le_one (welcomeInitialState welcomeZeroWords) nextRelu
        nextBlockFloat (expressions.map NormalizedExpr.toParsed) _ _ blockExecuted)
  obtain ⟨accesses, lowered⟩ :=
    executeParsedBlockFloatProducer_lowering_exists (welcomeInitialState welcomeZeroWords)
      nextRelu nextBlockFloat (expressions.map NormalizedExpr.toParsed) e _ _ blockFilter
      blockExecuted
  have half : accesses.precision = .h := by
    apply lowerParsedBlockFloat?_half_of_not_low e accesses lowered
    intro low
    exact notLow (fun other otherLowered => by
      rw [lowered] at otherLowered
      obtain rfl := Option.some.inj otherLowered
      exact low)
  obtain ⟨blockWrites, blockCommit, blockShape⟩ :=
    executeParsedBlockFloatProducer_shape_of_singleton_half nextRelu nextBlockFloat
      (expressions.map NormalizedExpr.toParsed) e _ _ blockFilter accesses lowered half
      eNodup blockExecuted
  have intRows : ∀ expression ∈ (expressions.map NormalizedExpr.toParsed).filter
      parsedExprIsIntegerMatrixReadStageInput,
      expression.op = .noforward ∨ (∃ tag : Fin 256, expression.op = .wait tag) ∨
        WelcomeRowHasNoLm1Destination expression := by
    intro expression member
    refine Or.inr (Or.inr ?_)
    refine rows expression (List.mem_of_mem_filter member) ?_
    intro same
    rw [same] at member
    have keeps := (List.mem_filter.mp member).2
    rw [eIntFalse] at keeps
    simp at keeps
  have floatRows : ∀ expression ∈ (expressions.map NormalizedExpr.toParsed).filter
      parsedExprIsSupportedFloatMAUProducer, WelcomeRowHasNoLm1Destination expression :=
    fun expression member => stageFilter_noLm1_of_rows _ e rows
      parsedExprIsSupportedFloatMAUProducer eFloatFalse expression member
  obtain ⟨intWrites, floatWrites, slots, bars, intPrep, intCommit, intFree, floatFree⟩ :=
    executeIntegerProducerLineAtPEs_zero_prepared_float_clean_of_line_split expressions nextPEs
      intRows floatRows walkExecuted
  obtain ⟨mslWrites, mslCommit, mslFree⟩ :=
    executeParsedMslMsrProducers_clean_commit (welcomeInitialState welcomeZeroWords)
      nextPEs nextMsl (expressions.map NormalizedExpr.toParsed) _ _
      (fun expression member => stageFilter_noLm1_of_rows _ e rows
        parsedExprIsMslMsrProducer eMslFalse expression member) mslExecuted
  obtain ⟨reluWrites, reluCommit, reluFree⟩ :=
    executeParsedFloatReluProducers_clean_commit (welcomeInitialState welcomeZeroWords)
      nextMsl nextRelu (expressions.map NormalizedExpr.toParsed) _ _
      (fun expression member => stageFilter_noLm1_of_rows _ e rows
        parsedExprIsFloatReluProducer eReluFalse expression member) reluExecuted
  obtain ⟨matrixWrites, matrixCommit, matrixFree⟩ :=
    executeParsedMatrixMAUAndWrites_clean_commit (welcomeInitialState welcomeZeroWords)
      nextBlockFloat afterMatrix (expressions.map NormalizedExpr.toParsed) _ _
      (fun expression member => stageFilter_noLm1_of_rows _ e rows
        parsedExprIsMatrixMAUProducer eMatrixFalse expression member) matrixExecuted
  obtain ⟨l1Writes, l1Commit, l1Free⟩ :=
    executeParsedL1ToPEProducers_clean_commit (welcomeInitialState welcomeZeroWords)
      nextShared nextBroadcast (expressions.map NormalizedExpr.toParsed) _ _ _
      (fun expression member => stageFilter_noLm1_of_rows _ e rows
        parsedExprIsL1ToPEProducer eL1False expression member) l1Executed
  have sharedFrame : nextShared.peRegisters welcomePE = afterMatrix.peRegisters welcomePE :=
    congrFun (executeParsedSharedBlockProducers_peRegisters (welcomeInitialState welcomeZeroWords)
      afterMatrix nextShared (expressions.map NormalizedExpr.toParsed)
      (!(expressions.any (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed)))
      sharedExecuted) welcomePE
  have commitEq := executeIntegerProducerInstructionLine_pe_commit_split nextPEs nextMsl
    nextRelu nextBlockFloat afterMatrix nextShared nextBroadcast next (by rw [nextEq])
    (intWrites ++ floatWrites) mslWrites reluWrites blockWrites matrixWrites l1Writes
    intCommit mslCommit reluCommit blockCommit matrixCommit sharedFrame l1Commit
  exact ⟨(intWrites ++ floatWrites) ++ mslWrites ++ reluWrites ++ blockWrites ++
    matrixWrites ++ l1Writes, commitEq,
    lm1WritesShape_of_six_fourth (intWrites ++ floatWrites) mslWrites reluWrites blockWrites
      matrixWrites l1Writes (lm1FreePreparedWrites_append intFree floatFree) mslFree reluFree
      blockShape matrixFree l1Free⟩

/-! ## 6. The block-float and special-ALU writer obligations, unconditionally -/

/-- **The block-float writer obligation.**  The low-precision case is
`welcomePEBlockFloatLowPrecisionWriterShapeObligation` of `WelcomeResiduals.lean`
and the non-low case is the `.h` theorem above. -/
theorem welcomePEBlockFloatWriterShapeObligation :
    WelcomePEBlockFloatWriterShapeObligation :=
  welcomePEBlockFloatWriterShapeObligation_of_low_and_nonLow
    welcomePEBlockFloatLowPrecisionWriterShapeObligation
    welcomePEBlockFloatNonLowWriterShapeObligation

/-- **The special-ALU writer obligation.**  The `msl`/`msr` and float-relu
families are `WelcomeResiduals.lean`'s unconditional theorems; the block-float
family is the theorem above. -/
theorem welcomePESpecialALUWriterShapeObligation :
    WelcomePESpecialALUWriterShapeObligation :=
  welcomePESpecialALUWriterShapeObligation_of_three welcomePEMslMsrWriterShapeObligation
    welcomePEFloatReluWriterShapeObligation welcomePEBlockFloatWriterShapeObligation

end ProofsLean.MNCore
