import ProofsLean.WelcomeFloatMAUShape

/-! # The `.h` cycle copy fact at the all-zero state

`WelcomeFloatMAUShape.lean` reduced the float-MAU row shape at the all-zero
state to a single datapath statement, `WelcomePEFloatMAUHalfCycleCopy`: a
successful half-precision (`.mau .h ...`) cycle of
`executeParsedFloatMAUCycleAtPE` at `welcomeZeroFiles` with every forwarding
slot still poison has a copied third data word.

This module discharges that statement.  The proof has three layers.

* **The source layer.**  `parsedFloatMAUSourceAttrs?` accepts only `.mem` and
  `.forward` operands.  A `.mem` source lowers to `.memory access false`, and a
  `.forward` source lowers to `.forward kind false`.  At the all-zero register
  file every memory access reads `⟨0,0⟩`
  (`welcomeZero_pack_readDirectAccess_zero`), while a `.forward` read from a
  poison slot is `.failure`.  Hence every source bus of a *successful* cycle is
  `⟨0,0⟩`.

* **The lowering layer.**  Each of `lowerParsedHalfMultiply?`,
  `lowerParsedHalfAdd?`, `lowerParsedHalfFma?` and `lowerParsedHalfPassa?`
  returns only sources produced by `parsedFloatMAUSourceAttrs?`; the inversion
  lemmas below unfold the `do` blocks and read that off.

* **The datapath layer.**  With zero source lanes, `prepareHalfMulInput` is
  `0` or the sign mask, `prepareHalfAddSource` is a list of half/single zeros,
  and `prepareHalfMultiplyBus`, `prepareHalfFmaBus` and `prepareHalfPassa`
  therefore return `⟨0,0⟩` (checked case by case on the finitely many flag
  combinations).  A zero bus has a copied third data word.

No `sorry`, no `admit`, no `native_decide`, no new axioms.  The main result is
`welcomePEFloatMAUHalfCycleCopy_holds`; the corollaries
`welcomePEFloatMAUCycleCopy_holds` and
`executeParsedFloatMAUsAtPE_zeroShape_static_unconditional` remove the
hypothesis from the statements of `WelcomeFloatMAUShape.lean`.
-/

namespace ProofsLean.MNCore

open Issue
open PEMemory

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

/-! ## 1. Reading a source at the all-zero state -/

/-- Rounding the zero single bus to half pairs leaves it zero. -/
theorem welcomeHalfMAU_roundSingleInputBusToHalf_zero :
    roundSingleInputBusToHalf (⟨0, 0⟩ : IntegerALU.Bus) = ⟨0, 0⟩ := by decide

/-- Source rounding preserves the zero bus. -/
theorem welcomeHalfMAU_applyRounding_zero (rounded : Bool) :
    ParsedIntegerInput.applyRounding rounded (⟨0, 0⟩ : IntegerALU.Bus) = ⟨0, 0⟩ := by
  cases rounded
  · rfl
  · exact welcomeHalfMAU_roundSingleInputBusToHalf_zero

/-- **Where a float-MAU source can come from.**  `parsedFloatMAUSourceAttrs?`
only accepts `.mem` and `.forward` operands, and it lowers them to
`.memory access false` and `.forward kind false` respectively. -/
theorem welcomeHalfMAU_sourceAttrs_shape
    (operand : ParsedOperand) (context : ParsedIntegerContext)
    (input : ParsedIntegerInput) (neg ext rnd : Bool)
    (lowered : parsedFloatMAUSourceAttrs? operand context = some (input, neg, ext, rnd)) :
    (∃ access, input = .memory access false) ∨ (∃ kind, input = .forward kind false) := by
  cases operand with
  | mem access neg ext rnd mask =>
      simp only [parsedFloatMAUSourceAttrs?] at lowered
      rw [Option.map_eq_some_iff] at lowered
      obtain ⟨raw, hraw, hpair⟩ := lowered
      obtain rfl := (Prod.mk.inj hpair).1
      simp only [ParsedOperand.toParsedIntegerInput?] at hraw
      rw [Option.map_eq_some_iff] at hraw
      obtain ⟨resolved, hdirect, hmemory⟩ := hraw
      left
      exact ⟨resolved, hmemory.symm⟩
  | forward kind neg ext rnd =>
      simp only [parsedFloatMAUSourceAttrs?] at lowered
      rw [Option.map_eq_some_iff] at lowered
      obtain ⟨raw, hraw, hpair⟩ := lowered
      obtain rfl := (Prod.mk.inj hpair).1
      right
      refine ⟨kind, ?_⟩
      have hraw' : ParsedOperand.toParsedIntegerInput? (.forward kind neg ext false)
          .long context.group context.l2b context.l1b context.mab context.pe context.cycle
          context.bar0 context.bar1 context.tWord = some (.forward kind false) := rfl
      rw [hraw'] at hraw
      exact (Option.some.inj hraw).symm
  | fixed kind => simp [parsedFloatMAUSourceAttrs?] at lowered
  | bar lm1 width mask => simp [parsedFloatMAUSourceAttrs?] at lowered
  | omr entry mask => simp [parsedFloatMAUSourceAttrs?] at lowered
  | matrix y width row => simp [parsedFloatMAUSourceAttrs?] at lowered
  | nowrite => simp [parsedFloatMAUSourceAttrs?] at lowered
  | l1bm width address => simp [parsedFloatMAUSourceAttrs?] at lowered
  | l2bm address l2b => simp [parsedFloatMAUSourceAttrs?] at lowered
  | dar address => simp [parsedFloatMAUSourceAttrs?] at lowered

/-- **A successful source read at the all-zero state is the zero bus.**  A
memory source reads zero in every bank; a forwarding source reads from a
poison slot, which would make the cycle fail rather than succeed. -/
theorem welcomeHalfMAU_sourceAttrs_read_zero
    (operand : ParsedOperand) (context : ParsedIntegerContext)
    (input : ParsedIntegerInput) (neg ext rnd : Bool)
    (slots : Forwarding.Slots) (cycle : Fin 4) (bus : IntegerALU.Bus)
    (poisoned : ∀ unit c, slots unit c = .poison)
    (lowered : parsedFloatMAUSourceAttrs? operand context = some (input, neg, ext, rnd))
    (read : ParsedIntegerInput.readWithForwarding welcomeZeroFiles slots cycle input = .ok bus) :
    bus = ⟨0, 0⟩ := by
  rcases welcomeHalfMAU_sourceAttrs_shape operand context input neg ext rnd lowered with
    ⟨access, rfl⟩ | ⟨kind, rfl⟩
  · simp only [ParsedIntegerInput.readWithForwarding, ParsedIntegerInput.read,
      StepResult.ok.injEq] at read
    rw [welcomeZero_pack_readDirectAccess_zero] at read
    rw [welcomeHalfMAU_applyRounding_zero] at read
    exact read.symm
  · simp [ParsedIntegerInput.readWithForwarding, poisoned] at read

/-! ## 2. The half datapath on zero lanes -/

/-- A zero source bus with any sign and source-rounding flags is either zero
or the four-lane sign mask. -/
theorem welcomeHalfMAU_prepareHalfMulInput_zero (negate round : Bool) :
    prepareHalfMulInput (⟨0, 0⟩ : IntegerALU.Bus) negate round =
      (if negate then BitVec.ofNat 64 (2 ^ 63 + 2 ^ 47 + 2 ^ 31 + 2 ^ 15) else 0) := by
  cases negate <;> cases round <;> decide

/-- The half multiply bus of two zero/sign-mask inputs is the zero bus. -/
theorem welcomeHalfMAU_prepareHalfMultiplyBus_zero (negateA negateB round : Bool) :
    prepareHalfMultiplyBus
      (if negateA then BitVec.ofNat 64 (2 ^ 63 + 2 ^ 47 + 2 ^ 31 + 2 ^ 15) else 0)
      (if negateB then BitVec.ofNat 64 (2 ^ 63 + 2 ^ 47 + 2 ^ 31 + 2 ^ 15) else 0)
      round = (⟨0, 0⟩ : IntegerALU.Bus) := by
  cases negateA <;> cases negateB <;> cases round <;> decide

/-- Half lanes of a zero source bus are zero or negative zero. -/
theorem welcomeHalfMAU_prepareHalfAddSource_zero (negate extend round : Bool) :
    prepareHalfAddSource (⟨0, 0⟩ : IntegerALU.Bus) negate extend round false =
      (if negate then [0x8000, 0x8000, 0x8000, 0x8000] else [0, 0, 0, 0]) := by
  cases negate <;> cases extend <;> cases round <;> decide

/-- Single lanes of a zero source bus used as an accumulator are zero or
negative zero. -/
theorem welcomeHalfMAU_prepareHalfAddSource_zero_accumulator (negate extend round : Bool) :
    prepareHalfAddSource (⟨0, 0⟩ : IntegerALU.Bus) negate extend round true =
      (if negate then [0x80000000, 0x80000000, 0x80000000, 0x80000000] else [0, 0, 0, 0]) := by
  cases negate <;> cases extend <;> cases round <;> decide

/-- The half FMA bus of zero/sign-mask lanes plus the constant `1.0` half lanes
is the zero bus. -/
theorem welcomeHalfMAU_prepareHalfFmaBus_ones_zero (negateA negateC round : Bool) :
    prepareHalfFmaBus
      (if negateA then [0x8000, 0x8000, 0x8000, 0x8000] else [0, 0, 0, 0])
      [0x3e00, 0x3e00, 0x3e00, 0x3e00]
      (if negateC then [0x80000000, 0x80000000, 0x80000000, 0x80000000] else [0, 0, 0, 0])
      round = (⟨0, 0⟩ : IntegerALU.Bus) := by
  cases negateA <;> cases negateC <;> cases round <;> decide

/-- The half FMA bus of zero/sign-mask half lanes and zero/negative-zero single
accumulator lanes is the zero bus. -/
theorem welcomeHalfMAU_prepareHalfFmaBus_zero (negateA negateB negateC round : Bool) :
    prepareHalfFmaBus
      (if negateA then [0x8000, 0x8000, 0x8000, 0x8000] else [0, 0, 0, 0])
      (if negateB then [0x8000, 0x8000, 0x8000, 0x8000] else [0, 0, 0, 0])
      (if negateC then [0x80000000, 0x80000000, 0x80000000, 0x80000000] else [0, 0, 0, 0])
      round = (⟨0, 0⟩ : IntegerALU.Bus) := by
  cases negateA <;> cases negateB <;> cases negateC <;> cases round <;> decide

/-- The inactive (all-zero input) half FMA bus is the zero bus. -/
theorem welcomeHalfMAU_prepareHalfFmaBus_zero_zeros (negateC round : Bool) :
    prepareHalfFmaBus [0, 0, 0, 0] [0, 0, 0, 0]
      (if negateC then [0x80000000, 0x80000000, 0x80000000, 0x80000000] else [0, 0, 0, 0])
      round = (⟨0, 0⟩ : IntegerALU.Bus) := by
  cases negateC <;> cases round <;> decide

/-- The half pass-through bus of the zero bus is the zero bus. -/
theorem welcomeHalfMAU_prepareHalfPassa_zero (negate sourceRound outputRound : Bool) :
    prepareHalfPassa (⟨0, 0⟩ : IntegerALU.Bus) negate sourceRound outputRound =
      (⟨0, 0⟩ : IntegerALU.Bus) := by
  cases negate <;> cases sourceRound <;> cases outputRound <;> decide

/-! ## 3. Source-shape inversion of the half lowerings -/

/-- `lowerParsedHalfMultiply?` only produces sources obtained through
`parsedFloatMAUSourceAttrs?`. -/
theorem welcomeHalfMAU_lowerHalfMultiply_sources
    (sources destinations : List ParsedOperand) (flush : Option ParsedMask) (text : String)
    (context : ParsedIntegerContext) (half : Option Char) (round : Bool)
    (sourceA : ParsedIntegerInput) (negateA extendA roundA : Bool)
    (sourceB : ParsedIntegerInput) (negateB extendB roundB : Bool)
    (dests : List ParsedOperand)
    (lowered : lowerParsedHalfMultiply?
      ⟨.mau .h false .mul half round, sources, destinations, flush, text⟩ context =
      some (sourceA, negateA, extendA, roundA, sourceB, negateB, extendB, roundB, dests)) :
    ∃ a b, sources = [a, b] ∧
      parsedFloatMAUSourceAttrs? a context = some (sourceA, negateA, extendA, roundA) ∧
      parsedFloatMAUSourceAttrs? b context = some (sourceB, negateB, extendB, roundB) := by
  simp only [lowerParsedHalfMultiply?] at lowered
  cases sources with
  | nil => simp at lowered
  | cons a rest =>
    cases rest with
    | nil => simp at lowered
    | cons b rest =>
      cases rest with
      | nil =>
        cases destinations with
        | nil => simp at lowered
        | cons d rest2 =>
          dsimp only at lowered
          cases hA : parsedFloatMAUSourceAttrs? a context with
          | none => simp [hA] at lowered
          | some pA =>
            obtain ⟨inputA, negA, extA, rndA⟩ := pA
            cases hB : parsedFloatMAUSourceAttrs? b context with
            | none => simp [hA, hB] at lowered
            | some pB =>
              obtain ⟨inputB, negB, extB, rndB⟩ := pB
              simp [hA, hB] at lowered
              rw [Option.bind_eq_some_iff] at lowered
              obtain ⟨u, hu, hsome⟩ := lowered
              simp [guard] at hu
              have hTuple := Option.some.inj hsome
              simp only [Prod.mk.injEq] at hTuple
              obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hTuple
              exact ⟨a, b, rfl, hA, hB⟩
      | cons x rest => simp at lowered

/-- `lowerParsedHalfAdd?` only produces sources obtained through
`parsedFloatMAUSourceAttrs?`. -/
theorem welcomeHalfMAU_lowerHalfAdd_sources
    (sources destinations : List ParsedOperand) (flush : Option ParsedMask) (text : String)
    (context : ParsedIntegerContext) (half : Option Char) (round : Bool)
    (sourceA : ParsedIntegerInput) (negateA extendA roundA : Bool)
    (sourceC : ParsedIntegerInput) (negateC extendC roundC : Bool)
    (dests : List ParsedOperand)
    (lowered : lowerParsedHalfAdd?
      ⟨.mau .h false .add half round, sources, destinations, flush, text⟩ context =
      some (sourceA, negateA, extendA, roundA, sourceC, negateC, extendC, roundC, dests)) :
    ∃ a c, sources = [a, c] ∧
      parsedFloatMAUSourceAttrs? a context = some (sourceA, negateA, extendA, roundA) ∧
      parsedFloatMAUSourceAttrs? c context = some (sourceC, negateC, extendC, roundC) := by
  simp only [lowerParsedHalfAdd?] at lowered
  cases sources with
  | nil => simp at lowered
  | cons a rest =>
    cases rest with
    | nil => simp at lowered
    | cons c rest =>
      cases rest with
      | nil =>
        cases destinations with
        | nil => simp at lowered
        | cons d rest2 =>
          dsimp only at lowered
          cases hA : parsedFloatMAUSourceAttrs? a context with
          | none => simp [hA] at lowered
          | some pA =>
            obtain ⟨inputA, negA, extA, rndA⟩ := pA
            cases hC : parsedFloatMAUSourceAttrs? c context with
            | none => simp [hA, hC] at lowered
            | some pC =>
              obtain ⟨inputC, negC, extC, rndC⟩ := pC
              simp [hA, hC] at lowered
              rw [Option.bind_eq_some_iff] at lowered
              obtain ⟨u, hu, hsome⟩ := lowered
              simp [guard] at hu
              have hTuple := Option.some.inj hsome
              simp only [Prod.mk.injEq] at hTuple
              obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hTuple
              exact ⟨a, c, rfl, hA, hC⟩
      | cons x rest => simp at lowered

/-- `lowerParsedHalfFma?` only produces sources obtained through
`parsedFloatMAUSourceAttrs?`. -/
theorem welcomeHalfMAU_lowerHalfFma_sources
    (sources destinations : List ParsedOperand) (flush : Option ParsedMask) (text : String)
    (context : ParsedIntegerContext) (half : Option Char) (round : Bool)
    (sourceA : ParsedIntegerInput) (negateA extendA roundA : Bool)
    (sourceB : ParsedIntegerInput) (negateB extendB roundB : Bool)
    (sourceC : ParsedIntegerInput) (negateC extendC roundC : Bool)
    (dests : List ParsedOperand)
    (lowered : lowerParsedHalfFma?
      ⟨.mau .h false .fma half round, sources, destinations, flush, text⟩ context =
      some (sourceA, negateA, extendA, roundA, sourceB, negateB, extendB, roundB,
        sourceC, negateC, extendC, roundC, dests)) :
    ∃ a b c, sources = [a, b, c] ∧
      parsedFloatMAUSourceAttrs? a context = some (sourceA, negateA, extendA, roundA) ∧
      parsedFloatMAUSourceAttrs? b context = some (sourceB, negateB, extendB, roundB) ∧
      parsedFloatMAUSourceAttrs? c context = some (sourceC, negateC, extendC, roundC) := by
  simp only [lowerParsedHalfFma?] at lowered
  cases sources with
  | nil => simp at lowered
  | cons a rest =>
    cases rest with
    | nil => simp at lowered
    | cons b rest =>
      cases rest with
      | nil => simp at lowered
      | cons c rest =>
        cases rest with
        | nil =>
          cases destinations with
          | nil => simp at lowered
          | cons d rest2 =>
            dsimp only at lowered
            cases hA : parsedFloatMAUSourceAttrs? a context with
            | none => simp [hA] at lowered
            | some pA =>
              obtain ⟨inputA, negA, extA, rndA⟩ := pA
              cases hB : parsedFloatMAUSourceAttrs? b context with
              | none => simp [hA, hB] at lowered
              | some pB =>
                obtain ⟨inputB, negB, extB, rndB⟩ := pB
                cases hC : parsedFloatMAUSourceAttrs? c context with
                | none => simp [hA, hB, hC] at lowered
                | some pC =>
                  obtain ⟨inputC, negC, extC, rndC⟩ := pC
                  simp [hA, hB, hC] at lowered
                  rw [Option.bind_eq_some_iff] at lowered
                  obtain ⟨u, hu, hsome⟩ := lowered
                  simp [guard] at hu
                  have hTuple := Option.some.inj hsome
                  simp only [Prod.mk.injEq] at hTuple
                  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ :=
                    hTuple
                  exact ⟨a, b, c, rfl, hA, hB, hC⟩
        | cons x rest => simp at lowered

/-- `lowerParsedHalfPassa?` only produces sources obtained through
`parsedFloatMAUSourceAttrs?`. -/
theorem welcomeHalfMAU_lowerHalfPassa_sources
    (sources destinations : List ParsedOperand) (flush : Option ParsedMask) (text : String)
    (context : ParsedIntegerContext) (half : Option Char) (round : Bool)
    (source : ParsedIntegerInput) (negate extend sourceRound : Bool)
    (dests : List ParsedOperand)
    (lowered : lowerParsedHalfPassa?
      ⟨.mau .h false .passa half round, sources, destinations, flush, text⟩ context =
      some (source, negate, extend, sourceRound, dests)) :
    ∃ a, sources = [a] ∧
      parsedFloatMAUSourceAttrs? a context = some (source, negate, extend, sourceRound) := by
  simp only [lowerParsedHalfPassa?] at lowered
  cases sources with
  | nil => simp at lowered
  | cons a rest =>
    cases rest with
    | cons x rest => simp at lowered
    | nil =>
      cases destinations with
      | nil => simp at lowered
      | cons d rest2 =>
        dsimp only at lowered
        cases hA : parsedFloatMAUSourceAttrs? a context with
        | none => simp [hA] at lowered
        | some pA =>
          obtain ⟨inputA, negA, extA, rndA⟩ := pA
          simp [hA] at lowered
          rw [Option.bind_eq_some_iff] at lowered
          obtain ⟨u, hu, hsome⟩ := lowered
          simp [guard] at hu
          have hTuple := Option.some.inj hsome
          simp only [Prod.mk.injEq] at hTuple
          obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hTuple
          exact ⟨a, rfl, hA⟩

end ProofsLean.MNCore

namespace ProofsLean.MNCore

open Issue
open PEMemory

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

/-! ## 4. The four `.h` cycle branches -/

/-- **The `.h .mul` branch.**  Both sources read the zero bus; the half
multiply bus of zero/sign-mask inputs is the zero bus, hence a copy. -/
theorem welcomeHalfMAU_cycle_mul_copy
    (readFiles currentFiles : IntegerRegisterFiles) (oldSlots : Forwarding.Slots)
    (sources destinations : List ParsedOperand) (flush : Option ParsedMask) (text : String)
    (context : ParsedIntegerContext) (cycle : Fin 4)
    (files : IntegerRegisterFiles) (output : IntegerALU.Bus) (flags : BitVec 4)
    (half : Option Char) (round : Bool)
    (zeroRead : readFiles = welcomeZeroFiles)
    (poisoned : ∀ unit c, oldSlots unit c = .poison)
    (executed : executeParsedFloatMAUCycleAtPE readFiles currentFiles oldSlots
      ⟨.mau .h false .mul half round, sources, destinations, flush, text⟩ context cycle
      = .ok (files, output, flags)) :
    IsWelcomeCopy (output.low.extractLsb' 32 32) := by
  subst zeroRead
  simp only [executeParsedFloatMAUCycleAtPE] at executed
  cases lowered : lowerParsedHalfMultiply?
      (⟨.mau .h false .mul half round, sources, destinations, flush, text⟩ : ParsedExpr)
      { context with cycle := cycle } with
  | none =>
      rw [lowered] at executed
      simp only [parsedFloatMAULoweringMiss] at executed
      split at executed <;> simp at executed
  | some accesses =>
      rw [lowered] at executed
      dsimp only at executed
      obtain ⟨sourceA, negateA, extendA, roundA, sourceB, negateB, extendB, roundB, dests⟩ :=
        accesses
      split at executed
      · simp at executed
      · cases readA : ParsedIntegerInput.readWithForwarding welcomeZeroFiles oldSlots cycle sourceA with
        | failure => rw [readA] at executed; simp at executed
        | unknown => rw [readA] at executed; simp at executed
        | ok sourceABus =>
          cases readB : ParsedIntegerInput.readWithForwarding welcomeZeroFiles oldSlots cycle sourceB with
          | failure => rw [readA, readB] at executed; simp at executed
          | unknown => rw [readA, readB] at executed; simp at executed
          | ok sourceBBus =>
            rw [readA, readB] at executed
            dsimp only at executed
            obtain ⟨a, b, sourcesEq, attrA, attrB⟩ : ∃ a b, sources = [a, b] ∧
                parsedFloatMAUSourceAttrs? a { context with cycle := cycle } =
                  some (sourceA, negateA, extendA, roundA) ∧
                parsedFloatMAUSourceAttrs? b { context with cycle := cycle } =
                  some (sourceB, negateB, extendB, roundB) :=
              welcomeHalfMAU_lowerHalfMultiply_sources sources destinations flush text
                { context with cycle := cycle } half round sourceA negateA extendA roundA
                sourceB negateB extendB roundB dests lowered
            have hbusA : sourceABus = ⟨0, 0⟩ :=
              welcomeHalfMAU_sourceAttrs_read_zero a { context with cycle := cycle }
                sourceA negateA extendA roundA oldSlots cycle sourceABus poisoned attrA readA
            have hbusB : sourceBBus = ⟨0, 0⟩ :=
              welcomeHalfMAU_sourceAttrs_read_zero b { context with cycle := cycle }
                sourceB negateB extendB roundB oldSlots cycle sourceBBus poisoned attrB readB
            subst hbusA
            subst hbusB
            have hsplit := StepResult.ok.inj executed
            simp only [Prod.mk.injEq] at hsplit
            rw [← hsplit.2.1]
            by_cases hsel : parsedMauHalfSelectsPE half context.pe = true
            · rw [ite_eq_left hsel, welcomeHalfMAU_prepareHalfMulInput_zero negateA roundA,
                welcomeHalfMAU_prepareHalfMulInput_zero negateB roundB,
                welcomeHalfMAU_prepareHalfMultiplyBus_zero negateA negateB round]
              exact isWelcomeCopy_extractLsb_zero
            · rw [ite_eq_right hsel]
              exact isWelcomeCopy_extractLsb_zero

/-- **The `.h .add` branch.**  The source lanes and the accumulator lanes are
zero/negative-zero, and adding them to the constant one lanes leaves zero. -/
theorem welcomeHalfMAU_cycle_add_copy
    (readFiles currentFiles : IntegerRegisterFiles) (oldSlots : Forwarding.Slots)
    (sources destinations : List ParsedOperand) (flush : Option ParsedMask) (text : String)
    (context : ParsedIntegerContext) (cycle : Fin 4)
    (files : IntegerRegisterFiles) (output : IntegerALU.Bus) (flags : BitVec 4)
    (half : Option Char) (round : Bool)
    (zeroRead : readFiles = welcomeZeroFiles)
    (poisoned : ∀ unit c, oldSlots unit c = .poison)
    (executed : executeParsedFloatMAUCycleAtPE readFiles currentFiles oldSlots
      ⟨.mau .h false .add half round, sources, destinations, flush, text⟩ context cycle
      = .ok (files, output, flags)) :
    IsWelcomeCopy (output.low.extractLsb' 32 32) := by
  subst zeroRead
  simp only [executeParsedFloatMAUCycleAtPE] at executed
  cases lowered : lowerParsedHalfAdd?
      (⟨.mau .h false .add half round, sources, destinations, flush, text⟩ : ParsedExpr)
      { context with cycle := cycle } with
  | none =>
      rw [lowered] at executed
      simp only [parsedFloatMAULoweringMiss] at executed
      split at executed <;> simp at executed
  | some accesses =>
      rw [lowered] at executed
      dsimp only at executed
      obtain ⟨sourceA, negateA, extendA, roundA, sourceC, negateC, extendC, roundC, dests⟩ :=
        accesses
      split at executed
      · simp at executed
      · cases readA : ParsedIntegerInput.readWithForwarding welcomeZeroFiles oldSlots cycle sourceA with
        | failure => rw [readA] at executed; simp at executed
        | unknown => rw [readA] at executed; simp at executed
        | ok sourceABus =>
          cases readC : ParsedIntegerInput.readWithForwarding welcomeZeroFiles oldSlots cycle sourceC with
          | failure => rw [readA, readC] at executed; simp at executed
          | unknown => rw [readA, readC] at executed; simp at executed
          | ok sourceCBus =>
            rw [readA, readC] at executed
            dsimp only at executed
            obtain ⟨a, c, sourcesEq, attrA, attrC⟩ : ∃ a c, sources = [a, c] ∧
                parsedFloatMAUSourceAttrs? a { context with cycle := cycle } =
                  some (sourceA, negateA, extendA, roundA) ∧
                parsedFloatMAUSourceAttrs? c { context with cycle := cycle } =
                  some (sourceC, negateC, extendC, roundC) :=
              welcomeHalfMAU_lowerHalfAdd_sources sources destinations flush text
                { context with cycle := cycle } half round sourceA negateA extendA roundA
                sourceC negateC extendC roundC dests lowered
            have hbusA : sourceABus = ⟨0, 0⟩ :=
              welcomeHalfMAU_sourceAttrs_read_zero a { context with cycle := cycle }
                sourceA negateA extendA roundA oldSlots cycle sourceABus poisoned attrA readA
            have hbusC : sourceCBus = ⟨0, 0⟩ :=
              welcomeHalfMAU_sourceAttrs_read_zero c { context with cycle := cycle }
                sourceC negateC extendC roundC oldSlots cycle sourceCBus poisoned attrC readC
            subst hbusA
            subst hbusC
            have hsplit := StepResult.ok.inj executed
            simp only [Prod.mk.injEq] at hsplit
            rw [← hsplit.2.1]
            by_cases hsel : parsedMauHalfSelectsPE half context.pe = true
            · rw [ite_eq_left hsel, welcomeHalfMAU_prepareHalfAddSource_zero negateA extendA roundA,
                welcomeHalfMAU_prepareHalfAddSource_zero_accumulator negateC extendC roundC,
                welcomeHalfMAU_prepareHalfFmaBus_ones_zero negateA negateC round]
              exact isWelcomeCopy_extractLsb_zero
            · rw [ite_eq_right hsel,
                welcomeHalfMAU_prepareHalfAddSource_zero_accumulator negateC extendC roundC,
                welcomeHalfMAU_prepareHalfFmaBus_zero_zeros negateC round]
              exact isWelcomeCopy_extractLsb_zero

/-- **The `.h .fma` branch.**  Three zero source lanes and a zero accumulator
lane multiply-add to zero. -/
theorem welcomeHalfMAU_cycle_fma_copy
    (readFiles currentFiles : IntegerRegisterFiles) (oldSlots : Forwarding.Slots)
    (sources destinations : List ParsedOperand) (flush : Option ParsedMask) (text : String)
    (context : ParsedIntegerContext) (cycle : Fin 4)
    (files : IntegerRegisterFiles) (output : IntegerALU.Bus) (flags : BitVec 4)
    (half : Option Char) (round : Bool)
    (zeroRead : readFiles = welcomeZeroFiles)
    (poisoned : ∀ unit c, oldSlots unit c = .poison)
    (executed : executeParsedFloatMAUCycleAtPE readFiles currentFiles oldSlots
      ⟨.mau .h false .fma half round, sources, destinations, flush, text⟩ context cycle
      = .ok (files, output, flags)) :
    IsWelcomeCopy (output.low.extractLsb' 32 32) := by
  subst zeroRead
  simp only [executeParsedFloatMAUCycleAtPE] at executed
  cases lowered : lowerParsedHalfFma?
      (⟨.mau .h false .fma half round, sources, destinations, flush, text⟩ : ParsedExpr)
      { context with cycle := cycle } with
  | none =>
      rw [lowered] at executed
      simp only [parsedFloatMAULoweringMiss] at executed
      split at executed <;> simp at executed
  | some accesses =>
      rw [lowered] at executed
      dsimp only at executed
      obtain ⟨sourceA, negateA, extendA, roundA, sourceB, negateB, extendB, roundB,
        sourceC, negateC, extendC, roundC, dests⟩ := accesses
      split at executed
      · simp at executed
      · cases readA : ParsedIntegerInput.readWithForwarding welcomeZeroFiles oldSlots cycle sourceA with
        | failure => rw [readA] at executed; simp at executed
        | unknown => rw [readA] at executed; simp at executed
        | ok sourceABus =>
          cases readB : ParsedIntegerInput.readWithForwarding welcomeZeroFiles oldSlots cycle sourceB with
          | failure => rw [readA, readB] at executed; simp at executed
          | unknown => rw [readA, readB] at executed; simp at executed
          | ok sourceBBus =>
            cases readC : ParsedIntegerInput.readWithForwarding welcomeZeroFiles oldSlots cycle sourceC with
            | failure => rw [readA, readB, readC] at executed; simp at executed
            | unknown => rw [readA, readB, readC] at executed; simp at executed
            | ok sourceCBus =>
              rw [readA, readB, readC] at executed
              dsimp only at executed
              obtain ⟨a, b, c, sourcesEq, attrA, attrB, attrC⟩ : ∃ a b c, sources = [a, b, c] ∧
                  parsedFloatMAUSourceAttrs? a { context with cycle := cycle } =
                    some (sourceA, negateA, extendA, roundA) ∧
                  parsedFloatMAUSourceAttrs? b { context with cycle := cycle } =
                    some (sourceB, negateB, extendB, roundB) ∧
                  parsedFloatMAUSourceAttrs? c { context with cycle := cycle } =
                    some (sourceC, negateC, extendC, roundC) :=
                welcomeHalfMAU_lowerHalfFma_sources sources destinations flush text
                  { context with cycle := cycle } half round sourceA negateA extendA roundA
                  sourceB negateB extendB roundB sourceC negateC extendC roundC dests lowered
              have hbusA : sourceABus = ⟨0, 0⟩ :=
                welcomeHalfMAU_sourceAttrs_read_zero a { context with cycle := cycle }
                  sourceA negateA extendA roundA oldSlots cycle sourceABus poisoned attrA readA
              have hbusB : sourceBBus = ⟨0, 0⟩ :=
                welcomeHalfMAU_sourceAttrs_read_zero b { context with cycle := cycle }
                  sourceB negateB extendB roundB oldSlots cycle sourceBBus poisoned attrB readB
              have hbusC : sourceCBus = ⟨0, 0⟩ :=
                welcomeHalfMAU_sourceAttrs_read_zero c { context with cycle := cycle }
                  sourceC negateC extendC roundC oldSlots cycle sourceCBus poisoned attrC readC
              subst hbusA
              subst hbusB
              subst hbusC
              have hsplit := StepResult.ok.inj executed
              simp only [Prod.mk.injEq] at hsplit
              rw [← hsplit.2.1]
              by_cases hsel : parsedMauHalfSelectsPE half context.pe = true
              · rw [ite_eq_left hsel, welcomeHalfMAU_prepareHalfAddSource_zero negateA extendA roundA,
                  welcomeHalfMAU_prepareHalfAddSource_zero negateB extendB roundB,
                  welcomeHalfMAU_prepareHalfAddSource_zero_accumulator negateC extendC roundC,
                  welcomeHalfMAU_prepareHalfFmaBus_zero negateA negateB negateC round]
                exact isWelcomeCopy_extractLsb_zero
              · rw [ite_eq_right hsel,
                  welcomeHalfMAU_prepareHalfAddSource_zero_accumulator negateC extendC roundC,
                  welcomeHalfMAU_prepareHalfFmaBus_zero_zeros negateC round]
                exact isWelcomeCopy_extractLsb_zero

/-- **The `.h .passa` branch.**  The pass-through of the zero bus is zero. -/
theorem welcomeHalfMAU_cycle_passa_copy
    (readFiles currentFiles : IntegerRegisterFiles) (oldSlots : Forwarding.Slots)
    (sources destinations : List ParsedOperand) (flush : Option ParsedMask) (text : String)
    (context : ParsedIntegerContext) (cycle : Fin 4)
    (files : IntegerRegisterFiles) (output : IntegerALU.Bus) (flags : BitVec 4)
    (half : Option Char) (round : Bool)
    (zeroRead : readFiles = welcomeZeroFiles)
    (poisoned : ∀ unit c, oldSlots unit c = .poison)
    (executed : executeParsedFloatMAUCycleAtPE readFiles currentFiles oldSlots
      ⟨.mau .h false .passa half round, sources, destinations, flush, text⟩ context cycle
      = .ok (files, output, flags)) :
    IsWelcomeCopy (output.low.extractLsb' 32 32) := by
  subst zeroRead
  simp only [executeParsedFloatMAUCycleAtPE] at executed
  cases lowered : lowerParsedHalfPassa?
      (⟨.mau .h false .passa half round, sources, destinations, flush, text⟩ : ParsedExpr)
      { context with cycle := cycle } with
  | none =>
      rw [lowered] at executed
      simp only [parsedFloatMAULoweringMiss] at executed
      split at executed <;> simp at executed
  | some accesses =>
      rw [lowered] at executed
      dsimp only at executed
      obtain ⟨source, negate, extend, sourceRound, dests⟩ := accesses
      split at executed
      · simp at executed
      · cases readA : ParsedIntegerInput.readWithForwarding welcomeZeroFiles oldSlots cycle source with
        | failure => rw [readA] at executed; simp at executed
        | unknown => rw [readA] at executed; simp at executed
        | ok sourceBus =>
          rw [readA] at executed
          dsimp only at executed
          obtain ⟨a, sourcesEq, attrA⟩ : ∃ a, sources = [a] ∧
              parsedFloatMAUSourceAttrs? a { context with cycle := cycle } =
                some (source, negate, extend, sourceRound) :=
            welcomeHalfMAU_lowerHalfPassa_sources sources destinations flush text
              { context with cycle := cycle } half round source negate extend sourceRound
              dests lowered
          have hbus : sourceBus = ⟨0, 0⟩ :=
            welcomeHalfMAU_sourceAttrs_read_zero a { context with cycle := cycle }
              source negate extend sourceRound oldSlots cycle sourceBus poisoned attrA readA
          subst hbus
          have hsplit := StepResult.ok.inj executed
          simp only [Prod.mk.injEq] at hsplit
          rw [← hsplit.2.1]
          by_cases hsel : parsedMauHalfSelectsPE half context.pe = true
          · rw [ite_eq_left hsel, welcomeHalfMAU_prepareHalfPassa_zero negate sourceRound round]
            exact isWelcomeCopy_extractLsb_zero
          · rw [ite_eq_right hsel]
            exact isWelcomeCopy_extractLsb_zero

/-! ## 5. The half-cycle copy fact -/

/-- **`WelcomePEFloatMAUHalfCycleCopy` holds.**  A successful half-precision
float-MAU cycle at the all-zero register file, with every forwarding slot still
poison, produces a bus whose low half's high word is a copied word. -/
theorem welcomePEFloatMAUHalfCycleCopy_holds : WelcomePEFloatMAUHalfCycleCopy := by
  intro readFiles currentFiles oldSlots expression context cycle files output flags kind half round
    isHalf zeroRead poisoned executed
  obtain ⟨op, sources, destinations, flush, text⟩ := expression
  obtain rfl : op = .mau .h false kind half round := isHalf
  cases kind with
  | fma =>
      exact welcomeHalfMAU_cycle_fma_copy readFiles currentFiles oldSlots sources destinations
        flush text context cycle files output flags half round zeroRead poisoned executed
  | mul =>
      exact welcomeHalfMAU_cycle_mul_copy readFiles currentFiles oldSlots sources destinations
        flush text context cycle files output flags half round zeroRead poisoned executed
  | add =>
      exact welcomeHalfMAU_cycle_add_copy readFiles currentFiles oldSlots sources destinations
        flush text context cycle files output flags half round zeroRead poisoned executed
  | passa =>
      exact welcomeHalfMAU_cycle_passa_copy readFiles currentFiles oldSlots sources destinations
        flush text context cycle files output flags half round zeroRead poisoned executed

/-- **The full datapath fact, without hypotheses.**  This is
`WelcomePEFloatMAUCycleCopy` with its half-precision case discharged. -/
theorem welcomePEFloatMAUCycleCopy_holds : WelcomePEFloatMAUCycleCopy :=
  welcomePEFloatMAUCycleCopy_of_half welcomePEFloatMAUHalfCycleCopy_holds

/-- **The float-MAU row shape at the all-zero state, unconditionally.**  The
prepared write list of one float-MAU row is committed at the all-zero register
file and is either all copied `.double` blocks or fits in four narrow
windows. -/
theorem executeParsedFloatMAUsAtPE_zeroShape_static_unconditional
    (expression : ParsedExpr) (context : ParsedIntegerContext) (directive : ParsedMaskDirective)
    (hasSingleLineMask : Bool)
    (nodup : (expression.toIssueExpr 0).writeBanks.Nodup)
    (nextFiles : IntegerRegisterFiles) (nextBar0 nextBar1 : BitVec 12)
    (nextOutputs : Fin 4 → IntegerALU.Bus) (hasMAUProducer : Bool)
    (executed : executeParsedFloatMAUsAtPE welcomeZeroFiles welcomeZeroFiles welcomeZeroSlots context
      [expression] directive hasSingleLineMask =
      .ok (nextFiles, nextBar0, nextBar1, nextOutputs, hasMAUProducer)) :
    ∃ writes, nextFiles = commitParsedMaskedWrites welcomeZeroFiles writes ∧
      (Lm1WritesDoubleCopy writes ∨ Lm1WritesNarrow writes) :=
  executeParsedFloatMAUsAtPE_zeroShape_static welcomePEFloatMAUHalfCycleCopy_holds expression
    context directive hasSingleLineMask nodup nextFiles nextBar0 nextBar1 nextOutputs
    hasMAUProducer executed

end ProofsLean.MNCore
