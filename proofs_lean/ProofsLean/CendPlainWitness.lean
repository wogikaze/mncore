import ProofsLean.ProgramWitness
import ProofsLean.ALUReadSetBound
import ProofsLean.ChannelResiduals

/-! # `12.convert-endian`: program-dependent witnesses for the plain-ALU family

`ProofsLean/ProgramWitness.lean` built the diagonalisation kernel and closed the
*constant* family: a plain row whose opcode is `.zero` or `.immediate` has an
input-independent observed pair, so the empty read set refutes it.  The remaining
plain family is the `.alu` rows, where the observed pair genuinely depends on the
input.  This module closes every such line whose **read set misses one of the two
input words**, and states the exact residual: the lines whose read set provably
touches both LM0 word `0` (the high input half) and LM0 word `1` (the low half).

## 1. The line's concrete read set

A plain `.pe` line's integer-stage preparation is a *function of a concrete,
input-independent set of register words*: the PE-0 mask file is
`zeroInitialPERegisterFiles.maskRegisters`, the forwarding slots, the matrix
store, the mask directive, the BAR/T context and the clock are the same at every
`cendInitialState`.  `cendLineReadSet` is that set,
`preparedListReadSet` at those channels.  At the initial state the *only* words
that differ between two inputs are LM0 words `0` (high 32 bits of the input) and
`1` (low 32 bits), so a line whose read set misses one of them cannot tell apart
two inputs that agree on the other half.

## 2. The factorisation, and the refutation

`cendPE_plain_prepared_eq` is the factorisation: agreement on a set `halves` of
input halves that *covers* the read set (`covered`) forces the prepared write
list, the forwarded slots and the BAR list to be the same at both inputs.  It is
`ChannelResiduals`' `prepareParsedIntegerMatrixReadLineCycles_congr_plain`
composed with `ProgramWitness`'s `cendInitialPERegisters_agree_of_halves`.
`cendPE_plain_determined` lifts this through `commitParsedMaskedWrites_lm1_congr`
to the observed pair, and `cendPE_plain_not_correct_of_freeHalves` applies the
diagonalisation kernel: a plain line whose read set misses an input half is
**incorrect**.

The set `halves` is not chosen by hand: `cendTouchedHalves` is *the set of input
halves the read set touches*, and `cendPE_plain_not_correct_of_readSet` is the
unconditional form.  It refutes every plain line — one row or many — whose read
set omits LM0 word `0` or LM0 word `1`
(`cendPE_plain_not_correct_of_avoidsHigh` / `_of_avoidsLow`).

## 3. What is exact about the residual

`CendPlainALUBothHalvesRefuted` is the remaining class: plain lines whose read
set contains both input words.  Every plain line is refuted from it
(`cendPE_plain_not_correct`, `cendPE_plainLines_not_correct`), so the plain-ALU
family of `CendPENonConstantRefuted` is now exactly that class.  The class is not
empty: a wide (`.long`/`.double`) source reads a window containing both words,
and no collision argument can separate two inputs that agree on the *whole*
window.

## 4. Turning the hypothesis into a computation on the line's constants

§5 makes the freeness hypothesis checkable.  At the `12.convert-endian` initial
context (BAR `0`, BAR `1`, `T` word `0`) an LM0 `.mem` source resolves to

```
((candidate + offset) / words * words) % 4096
```

where `candidate` is one of the region's four encoded addresses and `offset` is
the MAB offset (`0`, or one access width when `madpe` is set).  That is
`cendResolvedLm0Address`, proved here from the executor's own
`ParsedOperand.toDirectMemoryAccess?`; `cendOperandLm0Words` enumerates the words
that window can touch, and `cendExpressionsLm0Words` folds it over a line.
`CendLineReadSetLm0Words` is the one remaining bridge (the `accessRegion` half of
the enumeration), and `cendPE_plain_not_correct_of_words` /
`_of_wordsLow` turn it into refutations: a plain line whose own region constants
keep it away from LM0 word `0` (resp. `1`) is **incorrect**.

## Trust

No `sorry`, no `admit`, no `native_decide`, no `bv_decide`, no new axioms, and no
existing module is edited.  Every theorem below depends only on `propext`,
`Classical.choice` and `Quot.sound`; in particular the collision kernel used
here (`cendPE_not_correct_of_freeHalves`) is free of `ByteSwap`'s pre-existing
`_native.bv_decide` axiom.
-/

namespace ProofsLean.MNCore

open Issue
open PEMemory

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false

/-! ## 1. The line's concrete read set at the `12.convert-endian` initial state -/

/-- The words a plain `.pe` line's integer-stage preparation reads at the
`12.convert-endian` initial state.  Every channel argument of
`preparedListReadSet` is input-independent:
`(cendInitialState x).peRegisters cendPE` has the zero mask file for every `x`,
and `parsedPEHazardControl (cendInitialState x) cendPE` is the same record for
every `x` (the context's BAR/T words are `0`, the directive and the clock are
the Rust initial state's).  So this is one set of words, not a family. -/
noncomputable def cendLineReadSet (expressions : List NormalizedExpr) : Set WordRef :=
  preparedListReadSet zeroInitialPERegisterFiles.maskRegisters
    ((expressions.map NormalizedExpr.toParsed).filter parsedExprIsIntegerMatrixReadStageInput)
    (parsedPEHazardControl (cendInitialState 0) cendPE)

/-- **The read set does not depend on the input.** -/
theorem cendLineReadSet_eq (expressions : List NormalizedExpr) (x : BitVec 64) :
    preparedListReadSet ((cendInitialState x).peRegisters cendPE).maskRegisters
        ((expressions.map NormalizedExpr.toParsed).filter
          parsedExprIsIntegerMatrixReadStageInput)
        (parsedPEHazardControl (cendInitialState x) cendPE) =
      cendLineReadSet expressions := rfl

/-- The mask file of the preparation is the input-independent zero file. -/
theorem cendInitialState_maskRegisters_eq (x : BitVec 64) :
    ((cendInitialState x).peRegisters cendPE).maskRegisters =
      zeroInitialPERegisterFiles.maskRegisters := rfl

/-- The hazard control of the preparation is input-independent. -/
theorem cendInitialState_control_eq (x : BitVec 64) :
    parsedPEHazardControl (cendInitialState x) cendPE =
      parsedPEHazardControl (cendInitialState 0) cendPE := rfl

/-- The forwarding slots of the preparation are input-independent. -/
theorem cendInitialState_slots_eq (x : BitVec 64) :
    stateForwardingSlots (cendInitialState x) cendPE =
      stateForwardingSlots (cendInitialState 0) cendPE := rfl

/-- The matrix store of the preparation is input-independent. -/
theorem cendInitialState_store_eq (x : BitVec 64) :
    (cendInitialState x).matrixRegisters
        (ParsedIntegerContext.ofLinearIndex cendPE).group
        (ParsedIntegerContext.ofLinearIndex cendPE).l2b
        (ParsedIntegerContext.ofLinearIndex cendPE).l1b =
      (cendInitialState 0).matrixRegisters
        (ParsedIntegerContext.ofLinearIndex cendPE).group
        (ParsedIntegerContext.ofLinearIndex cendPE).l2b
        (ParsedIntegerContext.ofLinearIndex cendPE).l1b := rfl

/-! ## 2. The factorisation: the prepared write list is a function of the reads -/

/-- Plainness of every row that survives the integer-stage filter. -/
theorem cend_plain_filtered (expressions : List NormalizedExpr)
    (plain : (expressions.map NormalizedExpr.toParsed).all
      parsedExprIsPlainIntegerALU = true) :
    ∀ expression ∈ (expressions.map NormalizedExpr.toParsed).filter
      parsedExprIsIntegerMatrixReadStageInput,
      parsedExprIsPlainIntegerALU expression = true :=
  plain_of_filter_stageInput _ plain

/-- **The factorisation, on the executor's own preparation result.**  If two
inputs agree on every half of a set `halves` that covers the line's read set, the
prepared write list, the forwarded slots and the BAR update list are the same at
both.  This is the whole semantic content of the read-set bound: the prepared
list is a function of the mask file, the forwarding slots, the matrix store, the
hazard control and the words in `cendLineReadSet`, and only the last of those can
depend on the input. -/
theorem cendPE_plain_prepared_eq (expressions : List NormalizedExpr)
    (plain : (expressions.map NormalizedExpr.toParsed).all
      parsedExprIsPlainIntegerALU = true)
    (halves : Finset InputHalf)
    (covered : ∀ w ∈ cendLineReadSet expressions, w.1 = PEMemory.Bank.lm0 →
      (w.2.val = 0 → InputHalf.high ∈ halves) ∧
      (w.2.val = 1 → InputHalf.low ∈ halves))
    (x y : BitVec 64)
    (agreeHalves : ∀ half ∈ halves, InputHalf.value half x = InputHalf.value half y)
    (writesX : List PreparedParsedMaskedWrite)
    (slotsX : ProofsLean.MNCore.Forwarding.Slots)
    (barsX : List (Bool × BitVec 12))
    (writesY : List PreparedParsedMaskedWrite)
    (slotsY : ProofsLean.MNCore.Forwarding.Slots)
    (barsY : List (Bool × BitVec 12))
    (hX : welcomeIntegerPrep (cendInitialState x) welcomePE
      (expressions.map NormalizedExpr.toParsed) = .ok (writesX, slotsX, barsX))
    (hY : welcomeIntegerPrep (cendInitialState y) welcomePE
      (expressions.map NormalizedExpr.toParsed) = .ok (writesY, slotsY, barsY)) :
    writesX = writesY ∧ slotsX = slotsY ∧ barsX = barsY := by
  have agreeFiles : FilesAgreeOn (cendLineReadSet expressions)
      ((cendInitialState x).peRegisters cendPE) ((cendInitialState y).peRegisters cendPE) :=
    cendInitialPERegisters_agree_of_halves halves (cendLineReadSet expressions) covered x y
      agreeHalves
  have hX' : prepareParsedIntegerMatrixReadLineCycles ((cendInitialState x).peRegisters cendPE)
      (stateForwardingSlots (cendInitialState x) cendPE)
      ((cendInitialState x).matrixRegisters (ParsedIntegerContext.ofLinearIndex cendPE).group
        (ParsedIntegerContext.ofLinearIndex cendPE).l2b
        (ParsedIntegerContext.ofLinearIndex cendPE).l1b)
      ((expressions.map NormalizedExpr.toParsed).filter
        parsedExprIsIntegerMatrixReadStageInput)
      (parsedPEHazardControl (cendInitialState x) cendPE) false =
        .ok (writesX, slotsX, barsX) := hX
  have hY' : prepareParsedIntegerMatrixReadLineCycles ((cendInitialState y).peRegisters cendPE)
      (stateForwardingSlots (cendInitialState x) cendPE)
      ((cendInitialState x).matrixRegisters (ParsedIntegerContext.ofLinearIndex cendPE).group
        (ParsedIntegerContext.ofLinearIndex cendPE).l2b
        (ParsedIntegerContext.ofLinearIndex cendPE).l1b)
      ((expressions.map NormalizedExpr.toParsed).filter
        parsedExprIsIntegerMatrixReadStageInput)
      (parsedPEHazardControl (cendInitialState x) cendPE) false =
        .ok (writesY, slotsY, barsY) := hY
  exact prepareParsedIntegerMatrixReadLineCycles_congr_plain
    ((cendInitialState x).peRegisters cendPE) ((cendInitialState y).peRegisters cendPE)
    (stateForwardingSlots (cendInitialState x) cendPE)
    (stateForwardingSlots (cendInitialState x) cendPE)
    ((cendInitialState x).matrixRegisters (ParsedIntegerContext.ofLinearIndex cendPE).group
      (ParsedIntegerContext.ofLinearIndex cendPE).l2b
      (ParsedIntegerContext.ofLinearIndex cendPE).l1b)
    ((expressions.map NormalizedExpr.toParsed).filter
      parsedExprIsIntegerMatrixReadStageInput)
    (parsedPEHazardControl (cendInitialState x) cendPE) false
    (cendLineReadSet expressions)
    (cend_plain_filtered expressions plain)
    (fun w hw => hw) rfl rfl agreeFiles
    writesX slotsX barsX writesY slotsY barsY hX' hY'

/-! ## 3. The observed pair is determined by the read halves -/

/-- **The observed pair factors through the read halves.**  This is the form the
diagonalisation kernel consumes: two inputs agreeing on `halves` produce the same
observed LM1 pair after a successful step. -/
theorem cendPE_plain_determined (expressions : List NormalizedExpr)
    (plain : (expressions.map NormalizedExpr.toParsed).all
      parsedExprIsPlainIntegerALU = true)
    (halves : Finset InputHalf)
    (covered : ∀ w ∈ cendLineReadSet expressions, w.1 = PEMemory.Bank.lm0 →
      (w.2.val = 0 → InputHalf.high ∈ halves) ∧
      (w.2.val = 1 → InputHalf.low ∈ halves))
    (x y : BitVec 64)
    (agreeHalves : ∀ half ∈ halves, InputHalf.value half x = InputHalf.value half y) :
    ∀ nextX nextY : State, cendStep expressions x = some nextX →
      cendStep expressions y = some nextY →
      cendOutputPair nextX = cendOutputPair nextY := by
  intro nextX nextY stepX stepY
  obtain ⟨writesX, slotsX, barsX, prepX, commitX⟩ :=
    cendSealed_pe_prepared expressions (cendInitialState x) plain stepX
  obtain ⟨writesY, slotsY, barsY, prepY, commitY⟩ :=
    cendSealed_pe_prepared expressions (cendInitialState y) plain stepY
  have same := cendPE_plain_prepared_eq expressions plain halves covered x y agreeHalves
    writesX slotsX barsX writesY slotsY barsY prepX prepY
  have writesEq : writesX = writesY := same.1
  have lm1Eq : (nextX.peRegisters cendPE).lm1 = (nextY.peRegisters cendPE).lm1 := by
    rw [commitX, commitY, writesEq]
    exact commitParsedMaskedWrites_lm1_congr _ _ _ _ rfl rfl
  unfold cendOutputPair
  rw [lm1Eq]

/-- **Every plain line whose read set misses an input half is incorrect.**  The
hypothesis `free` is the diagonalisation's input: a half outside the read set.
The witness pair is built from the line's own signature (`cendPE_not_correct_of_freeHalves`
uses `0` and the free-half-one probe). -/
theorem cendPE_plain_not_correct_of_freeHalves (expressions : List NormalizedExpr)
    (plain : (expressions.map NormalizedExpr.toParsed).all
      parsedExprIsPlainIntegerALU = true)
    (halves : Finset InputHalf)
    (covered : ∀ w ∈ cendLineReadSet expressions, w.1 = PEMemory.Bank.lm0 →
      (w.2.val = 0 → InputHalf.high ∈ halves) ∧
      (w.2.val = 1 → InputHalf.low ∈ halves))
    (free : ∃ half, half ∉ halves) :
    ¬ ProofsLean.Correct cendSealedMachine cendSpec
      ([InstructionLine.pe expressions] : List InstructionLine) :=
  cendPE_not_correct_of_freeHalves expressions halves free
    (cendPE_plain_determined expressions plain halves covered)

/-! ## 4. The halves the read set actually touches

`cendTouchedHalves` is not a hand-picked set: it is the set of input halves whose
LM0 word occurs in `cendLineReadSet`.  The `covered` obligation of §2–§3 then
holds by construction, so the only hypothesis left is *freeness*: the read set
omits one of the two input words. -/

/-- The register word that carries one input half at the initial state. -/
def InputHalf.word : InputHalf → WordRef
  | .high => ⟨PEMemory.Bank.lm0, ⟨0, by decide⟩⟩
  | .low => ⟨PEMemory.Bank.lm0, ⟨1, by decide⟩⟩

@[simp] theorem InputHalf.word_high :
    InputHalf.word .high = ⟨PEMemory.Bank.lm0, ⟨0, by decide⟩⟩ := rfl

@[simp] theorem InputHalf.word_low :
    InputHalf.word .low = ⟨PEMemory.Bank.lm0, ⟨1, by decide⟩⟩ := rfl

theorem InputHalf.word_bank (half : InputHalf) :
    (InputHalf.word half).1 = PEMemory.Bank.lm0 := by
  cases half <;> rfl

/-- The two input halves form a finite type; `InputHalf` is declared in
`ProgramWitness` without the instance, so it is provided here. -/
instance : Fintype InputHalf :=
  ⟨{.high, .low}, by
    intro half
    cases half <;> simp⟩

/-- An LM0 word at address `0` is the high input half's word. -/
theorem wordRef_eq_high (bank : PEMemory.Bank) (address : Fin bank.capacity)
    (hbank : bank = PEMemory.Bank.lm0) (haddr : address.val = 0) :
    (⟨bank, address⟩ : WordRef) = InputHalf.word .high := by
  subst hbank
  have same : address = (⟨0, by decide⟩ : Fin PEMemory.Bank.lm0.capacity) := Fin.ext haddr
  subst same
  rfl

/-- An LM0 word at address `1` is the low input half's word. -/
theorem wordRef_eq_low (bank : PEMemory.Bank) (address : Fin bank.capacity)
    (hbank : bank = PEMemory.Bank.lm0) (haddr : address.val = 1) :
    (⟨bank, address⟩ : WordRef) = InputHalf.word .low := by
  subst hbank
  have same : address = (⟨1, by decide⟩ : Fin PEMemory.Bank.lm0.capacity) := Fin.ext haddr
  subst same
  rfl

/-- **The input halves the line's read set touches.** -/
noncomputable def cendTouchedHalves (expressions : List NormalizedExpr) :
    Finset InputHalf := by
  classical
  exact Finset.univ.filter (fun half => InputHalf.word half ∈ cendLineReadSet expressions)

theorem cendTouchedHalves_mem (expressions : List NormalizedExpr) (half : InputHalf) :
    half ∈ cendTouchedHalves expressions ↔
      InputHalf.word half ∈ cendLineReadSet expressions := by
  classical
  unfold cendTouchedHalves
  rw [Finset.mem_filter]
  exact ⟨fun member => member.2, fun member => ⟨Finset.mem_univ half, member⟩⟩

/-- The read set's LM0 words are exactly its touched halves: every LM0 word in
the read set is one of the two input words, or carries no input data. -/
theorem cendLineReadSet_covered_touched (expressions : List NormalizedExpr) :
    ∀ w ∈ cendLineReadSet expressions, w.1 = PEMemory.Bank.lm0 →
      (w.2.val = 0 → InputHalf.high ∈ cendTouchedHalves expressions) ∧
      (w.2.val = 1 → InputHalf.low ∈ cendTouchedHalves expressions) := by
  rintro ⟨bank, address⟩ hw hbank
  constructor
  · intro isZero
    rw [cendTouchedHalves_mem]
    rw [← wordRef_eq_high bank address hbank isZero]
    exact hw
  · intro isOne
    rw [cendTouchedHalves_mem]
    rw [← wordRef_eq_low bank address hbank isOne]
    exact hw

/-- **Every plain line whose read set misses one input word is incorrect.**  This
is the unconditional plain-ALU refutation, for a single row or a whole line: no hypothesis about
the line is left except its plainness and the freeness of the read set. -/
theorem cendPE_plain_not_correct_of_readSet (expressions : List NormalizedExpr)
    (plain : (expressions.map NormalizedExpr.toParsed).all
      parsedExprIsPlainIntegerALU = true)
    (free : ∃ half, InputHalf.word half ∉ cendLineReadSet expressions) :
    ¬ ProofsLean.Correct cendSealedMachine cendSpec
      ([InstructionLine.pe expressions] : List InstructionLine) := by
  obtain ⟨half, outside⟩ := free
  refine cendPE_plain_not_correct_of_freeHalves expressions plain
    (cendTouchedHalves expressions) (cendLineReadSet_covered_touched expressions) ?_
  refine ⟨half, ?_⟩
  rw [cendTouchedHalves_mem]
  exact outside

/-- The high input half is free as soon as the read set omits LM0 word `0`. -/
theorem cendPE_plain_not_correct_of_avoidsHigh (expressions : List NormalizedExpr)
    (plain : (expressions.map NormalizedExpr.toParsed).all
      parsedExprIsPlainIntegerALU = true)
    (avoids : InputHalf.word .high ∉ cendLineReadSet expressions) :
    ¬ ProofsLean.Correct cendSealedMachine cendSpec
      ([InstructionLine.pe expressions] : List InstructionLine) :=
  cendPE_plain_not_correct_of_readSet expressions plain ⟨.high, avoids⟩

/-- The low input half is free as soon as the read set omits LM0 word `1`. -/
theorem cendPE_plain_not_correct_of_avoidsLow (expressions : List NormalizedExpr)
    (plain : (expressions.map NormalizedExpr.toParsed).all
      parsedExprIsPlainIntegerALU = true)
    (avoids : InputHalf.word .low ∉ cendLineReadSet expressions) :
    ¬ ProofsLean.Correct cendSealedMachine cendSpec
      ([InstructionLine.pe expressions] : List InstructionLine) :=
  cendPE_plain_not_correct_of_readSet expressions plain ⟨.low, avoids⟩

/-! ## 5. The exact residual: plain lines that read both input words

The class below is what the collision argument cannot reach: lines whose read set
contains **both** LM0 word `0` and LM0 word `1`, so every pair of inputs that the
line cannot distinguish has the same target pair as well.  The reduction
`cendPE_plain_not_correct` shows that this is the *only* gap left in the plain
family: the family is refuted as soon as the both-halves class is. -/

/-- A plain line whose read set provably touches both input words. -/
def CendPlainALUBothHalves (expressions : List NormalizedExpr) : Prop :=
  InputHalf.word .high ∈ cendLineReadSet expressions ∧
    InputHalf.word .low ∈ cendLineReadSet expressions

/-- **The residual of the plain-ALU family.**  Plain lines that read both input
words are incorrect. -/
def CendPlainALUBothHalvesRefuted : Prop :=
  ∀ expressions : List NormalizedExpr,
    (expressions.map NormalizedExpr.toParsed).all parsedExprIsPlainIntegerALU = true →
    CendPlainALUBothHalves expressions →
    ¬ ProofsLean.Correct cendSealedMachine cendSpec
      ([InstructionLine.pe expressions] : List InstructionLine)

/-- **Every plain line is refuted from the both-halves residual.**  The read set
either omits an input word (§4) or touches both (§5).  Combined with
`ProgramWitness`'s constant family, this reduces the whole
`CendPENonConstantRefuted` plain-ALU family to `CendPlainALUBothHalvesRefuted`. -/
theorem cendPE_plain_not_correct (both : CendPlainALUBothHalvesRefuted)
    (expressions : List NormalizedExpr)
    (plain : (expressions.map NormalizedExpr.toParsed).all
      parsedExprIsPlainIntegerALU = true) :
    ¬ ProofsLean.Correct cendSealedMachine cendSpec
      ([InstructionLine.pe expressions] : List InstructionLine) := by
  by_cases free : ∃ half, InputHalf.word half ∉ cendLineReadSet expressions
  · exact cendPE_plain_not_correct_of_readSet expressions plain free
  · push Not at free
    exact both expressions plain
      ⟨free .high, free .low⟩


/-! ## 5. The concrete LM0 address bound: the line's own constants decide the halves

§4 refutes every plain line whose read set misses an input word, but takes that
freeness as a hypothesis.  This section turns it into a computation on the line's
**own region constants**: a `.mem` source in bank LM0 resolves at the
`12.convert-endian` initial context to `((candidate + offset) / words * words) %
4096`, where `candidate` is one of the region's four encoded addresses and
`offset` is the MAB offset (`0`, or one access width when `madpe` is set).
`cendOperandLm0Words` enumerates the words that window can touch, and
`cendOperand_readsRegion` proves it is a sound over-approximation.  The read-set
bound `aluCycleReadSet_subset_sourceReadUpperBound`
(`ProofsLean/ALUReadSetBound.lean`) lifts this to the whole line, and
`cendLineReadSet_lm0_words` is the resulting statement: every LM0 word in the
line's read set is in the finite set computed from its operands. -/

/-- The LM0 words one candidate address of a region can reach: the resolved
address is the candidate aligned down to a multiple of the access width, either
without or with the MAB offset, and the access covers `width.words` words. -/
noncomputable def cendLm0WordsAt (width : PEMemory.Width) (candidate : Nat) : Finset Nat :=
  ({0, width.words} : Finset Nat).biUnion (fun offset =>
    (Finset.range width.words).image (fun index =>
      (((candidate + offset) / width.words * width.words) % PEMemory.Bank.lm0.capacity +
        index) % PEMemory.Bank.lm0.capacity))

/-- **The LM0 words one region can reach** at the `12.convert-endian` initial
context, where BAR `0`, BAR `1` and the `T` word are all `0`. -/
noncomputable def cendRegionLm0Words (region : Issue.Region) : Finset Nat :=
  match parsedWidth? region.width with
  | none => ∅
  | some width =>
      region.addressCandidates.foldr
        (fun candidate acc => acc ∪ cendLm0WordsAt width candidate) ∅

/-- **The LM0 words one operand can read.** -/
noncomputable def cendOperandLm0Words : ParsedOperand → Finset Nat
  | .mem access _ _ _ _ =>
      if access.bank = Issue.Bank.lm0 then cendRegionLm0Words access.region else ∅
  | _ => ∅

/-- The MAB offset is either `0` or one access width. -/
theorem madpeOffset_mem (region : Issue.Region) (width : PEMemory.Width) (pe : Fin 4) :
    (match region.madpe with
      | some threshold => if pe.val ≤ threshold then width.words else 0
      | none => 0) ∈ ({0, width.words} : Finset Nat) := by
  cases hmad : region.madpe with
  | none => simp
  | some threshold => by_cases hle : pe.val ≤ threshold <;> simp [hle]

/-- The bank a resolved direct access takes is the issue bank's register bank. -/
theorem issueBank_of_resolved
    (bank : Issue.Bank) (region : Issue.Region) (pe cycle : Fin 4)
    (bar0 bar1 : BitVec 12) (tWord : BitVec 32) (access : DirectMemoryAccess)
    (hres : ParsedOperand.toDirectMemoryAccess? (.mem ⟨bank, region⟩ false false false none)
      pe cycle bar0 bar1 tWord = some access) :
    issueBankToRegisterBank bank = some access.bank := by
  cases hb : issueBankToRegisterBank bank with
  | none =>
      simp [ParsedOperand.toDirectMemoryAccess?, ParsedOperand.toDirectMemoryAccessMode?, hb] at hres
  | some rb =>
    cases hwd : parsedWidth? region.width with
    | none =>
        simp [ParsedOperand.toDirectMemoryAccess?, ParsedOperand.toDirectMemoryAccessMode?, hb,
          hwd] at hres
    | some width =>
      simp only [ParsedOperand.toDirectMemoryAccess?, ParsedOperand.toDirectMemoryAccessMode?,
        hb, hwd, Bool.or_false, Bool.not_false, Bool.true_and, Bool.false_eq_true, reduceIte,
        Option.isSome_none] at hres
      split at hres
      · simp at hres
      · simp only [Option.some.injEq] at hres
        subst hres
        rfl

/-- **The resolved address of an LM0 `.mem` source at the `12.convert-endian`
initial context.**  Both BAR words and the `T` word are `0`, so the address is
the region's candidate address plus the MAB offset, aligned down to the access
width and reduced modulo the LM0 capacity. -/
theorem cendResolvedLm0Address
    (region : Issue.Region) (rounded : Bool)
    (precision : IntegerALU.Precision) (group : Fin 4) (l2b : Fin 2) (l1b : Fin 8)
    (mab : Fin 16) (pe cycle : Fin 4) (access : DirectMemoryAccess)
    (hres : ParsedOperand.toParsedIntegerInput? (.mem ⟨.lm0, region⟩ false false rounded none)
      precision group l2b l1b mab pe cycle 0 0 0 = some (.memory access rounded))
    (hbank : access.bank = PEMemory.Bank.lm0) :
    ∃ width : PEMemory.Width, parsedWidth? region.width = some width ∧
      access.width = width ∧
      ∃ c ∈ region.addressCandidates,
        access.address.val = ((c + (match region.madpe with
          | some threshold => if pe.val ≤ threshold then width.words else 0
          | none => 0)) / width.words * width.words) % PEMemory.Bank.lm0.capacity := by
  simp only [ParsedOperand.toParsedIntegerInput?, ParsedOperand.toDirectMemoryAccess?,
    ParsedOperand.toDirectMemoryAccessMode?, Option.isSome_none, Bool.not_false,
    Bool.true_and, Bool.or_false, Bool.false_eq_true, reduceIte] at hres
  cases hb : issueBankToRegisterBank Issue.Bank.lm0 with
  | none => simp [hb] at hres
  | some rb =>
    rw [hb] at hres
    have hrb : rb = PEMemory.Bank.lm0 := by
      simpa [issueBankToRegisterBank] using hb.symm
    subst hrb
    cases hwWidth : parsedWidth? region.width with
    | none => simp [hwWidth] at hres
    | some width =>
      simp only [hwWidth] at hres
      split at hres
      · simp at hres
      · simp only [Option.map_some, Option.some.injEq,
          ParsedIntegerInput.memory.injEq] at hres
        obtain ⟨hEq, -⟩ := hres
        rw [← hEq]
        refine ⟨width, rfl, rfl, ?_⟩
        have hc : parsedRegionAddressAt region cycle ∈ region.addressCandidates := by
          unfold Region.addressCandidates parsedRegionAddressAt
          split <;> · split <;> simp
        have h1 : (PEMemory.Bank.lm0 == PEMemory.Bank.t) = false := by decide
        have h2 : (PEMemory.Bank.lm0 == PEMemory.Bank.lm0) = true := by decide
        have h3 : (PEMemory.Bank.lm0 == PEMemory.Bank.lm1) = false := by decide
        refine ⟨_, hc, ?_⟩
        simp [h1, h2, h3]
        rfl

/-- The LM0 count of a width is its word count. -/
theorem count_lm0 (width : PEMemory.Width) :
    PEMemory.count PEMemory.Bank.lm0 width = width.words := rfl

/-- The words a list of operands can reach. -/
noncomputable def cendOperandsLm0Words (sources : List ParsedOperand) : Finset Nat :=
  sources.foldr (fun operand acc => acc ∪ cendOperandLm0Words operand) ∅

/-- Membership in the operand fold, in `∃` form. -/
theorem mem_cendOperandsLm0Words_iff (sources : List ParsedOperand) (word : Nat) :
    word ∈ cendOperandsLm0Words sources ↔
      ∃ operand ∈ sources, word ∈ cendOperandLm0Words operand := by
  induction sources with
  | nil => simp [cendOperandsLm0Words]
  | cons operand rest ih =>
      simp only [cendOperandsLm0Words, List.foldr_cons, List.mem_cons] at ih ⊢
      rw [Finset.mem_union, ih]
      constructor
      · rintro (⟨item, member, h⟩ | h)
        · exact ⟨item, Or.inr member, h⟩
        · exact ⟨operand, Or.inl rfl, h⟩
      · rintro ⟨item, rfl | member, h⟩
        · exact Or.inr h
        · exact Or.inl ⟨item, member, h⟩

/-- **The words the line's own operands can reach.**  A fold of
`cendOperandLm0Words` over the rows that survive the integer-stage filter. -/
noncomputable def cendExpressionsLm0Words (expressions : List ParsedExpr) : Finset Nat :=
  expressions.foldr (fun expression acc => acc ∪ cendOperandsLm0Words expression.sources) ∅

/-- Membership in the expression fold, in `∃` form. -/
theorem mem_cendExpressionsLm0Words_iff (expressions : List ParsedExpr) (word : Nat) :
    word ∈ cendExpressionsLm0Words expressions ↔
      ∃ expression ∈ expressions, word ∈ cendOperandsLm0Words expression.sources := by
  induction expressions with
  | nil => simp [cendExpressionsLm0Words]
  | cons expression rest ih =>
      simp only [cendExpressionsLm0Words, List.foldr_cons, List.mem_cons] at ih ⊢
      rw [Finset.mem_union, ih]
      constructor
      · rintro (⟨item, member, h⟩ | h)
        · exact ⟨item, Or.inr member, h⟩
        · exact ⟨expression, Or.inl rfl, h⟩
      · rintro ⟨item, rfl | member, h⟩
        · exact Or.inr h
        · exact Or.inl ⟨item, member, h⟩

/-- **The one remaining bridge of §5.**  Every LM0 word a resolved operand reads
is one of the words the operand's own region constants can reach
(`cendOperandLm0Words`).

`cendResolvedLm0Address` proves the mathematical content: the resolved address is
`((candidate + offset) / words * words) % 4096` for one of the region's four
encoded addresses and the MAB offset.  What is missing is its `accessRegion`
half — turning `w ∈ accessRegion access` plus that address equation into
membership of `w.2.val` in the enumerated window — because the `Fin` proof of
`DirectMemoryAccess.address` is pinned to the address value, which turns the
step into dependent elimination rather than a rewrite.  Everything else of the
address criterion is proved below; `cendPE_plain_not_correct_of_words` consumes
this statement and nothing else. -/
def CendOperandLm0WordsCoverReads : Prop :=
  ∀ (operand : ParsedOperand) (precision : IntegerALU.Precision) (group : Fin 4)
    (l2b : Fin 2) (l1b : Fin 8) (mab : Fin 16) (pe cycle : Fin 4)
    (input : ParsedIntegerInput),
    ParsedOperand.toParsedIntegerInput? operand precision group l2b l1b mab pe cycle
      0 0 0 = some input →
    ∀ (w : WordRef), w ∈ ProofsLean.MNCore.ParsedIntegerInput.readsRegion input →
      w.1 = PEMemory.Bank.lm0 → w.2.val ∈ cendOperandLm0Words operand

/-- **Every LM0 word the line's read set contains is one its operands reach.**
This is the read-set bound (`aluCycleReadSet_subset_sourceReadUpperBound` from
`ProofsLean/ALUReadSetBound.lean`) composed with the operand bridge. -/
def CendLineReadSetLm0Words : Prop :=
  ∀ (expressions : List NormalizedExpr),
    (expressions.map NormalizedExpr.toParsed).all parsedExprIsPlainIntegerALU = true →
    ∀ (w : WordRef), w ∈ cendLineReadSet expressions → w.1 = PEMemory.Bank.lm0 →
      w.2.val ∈ cendExpressionsLm0Words
        ((expressions.map NormalizedExpr.toParsed).filter
          parsedExprIsIntegerMatrixReadStageInput)

/-- **A plain line whose operands cannot reach LM0 word `0` is incorrect.**  The
read set omits LM0 word `0`, so the high input half is free and §4's
diagonalisation applies. -/
theorem cendPE_plain_not_correct_of_words (bridge : CendLineReadSetLm0Words)
    (expressions : List NormalizedExpr)
    (plain : (expressions.map NormalizedExpr.toParsed).all
      parsedExprIsPlainIntegerALU = true)
    (avoids : (0 : Nat) ∉ cendExpressionsLm0Words
      ((expressions.map NormalizedExpr.toParsed).filter
        parsedExprIsIntegerMatrixReadStageInput)) :
    ¬ ProofsLean.Correct cendSealedMachine cendSpec
      ([InstructionLine.pe expressions] : List InstructionLine) := by
  have notHigh : InputHalf.word .high ∉ cendLineReadSet expressions := by
    intro member
    exact avoids (bridge expressions plain (InputHalf.word .high) member rfl)
  exact cendPE_plain_not_correct_of_avoidsHigh expressions plain notHigh

/-- **A plain line whose operands cannot reach LM0 word `1` is incorrect.** -/
theorem cendPE_plain_not_correct_of_wordsLow (bridge : CendLineReadSetLm0Words)
    (expressions : List NormalizedExpr)
    (plain : (expressions.map NormalizedExpr.toParsed).all
      parsedExprIsPlainIntegerALU = true)
    (avoids : (1 : Nat) ∉ cendExpressionsLm0Words
      ((expressions.map NormalizedExpr.toParsed).filter
        parsedExprIsIntegerMatrixReadStageInput)) :
    ¬ ProofsLean.Correct cendSealedMachine cendSpec
      ([InstructionLine.pe expressions] : List InstructionLine) := by
  have notLow : InputHalf.word .low ∉ cendLineReadSet expressions := by
    intro member
    exact avoids (by simpa using bridge expressions plain (InputHalf.word .low) member rfl)
  exact cendPE_plain_not_correct_of_avoidsLow expressions plain notLow


/-! ## 6. The plain-ALU family, on the class name

`CendPENonConstantRefuted` asks for a refutation of every line outside
`CendConstantLines`; the plain-ALU family is the part of it whose rows are all
plain integer ALU rows, and §5's `cendPE_plain_not_correct` refutes that whole
family from the single both-halves residual.  Note that this covers the constant
family of `ProgramWitness` too: a constant row has no input-dependent read, so
its read set misses a half and `CendClosedLines` / `CendConstantLines` are not
needed as hypotheses. -/

/-- The plain-ALU lines: every row is a plain integer ALU row. -/
def CendPlainLines (expressions : List NormalizedExpr) : Prop :=
  (expressions.map NormalizedExpr.toParsed).all parsedExprIsPlainIntegerALU = true

/-- **Every plain-ALU line is refuted from the both-halves residual.** -/
theorem cendPE_plainLines_not_correct (both : CendPlainALUBothHalvesRefuted)
    (expressions : List NormalizedExpr) (plain : CendPlainLines expressions) :
    ¬ ProofsLean.Correct cendSealedMachine cendSpec
      ([InstructionLine.pe expressions] : List InstructionLine) :=
  cendPE_plain_not_correct both expressions plain

/-- **The plain-ALU part of `CendPENonConstantRefuted`**, in the same shape as
`CendConstantLines`: the hypotheses `¬ CendClosedLines` and `¬ CendConstantLines`
of `CendPENonConstantRefuted` are not used, because §4 and §5 cover those lines
by the read set rather than by their class. -/
theorem cendPENonConstantRefuted_plain (both : CendPlainALUBothHalvesRefuted)
    (expressions : List NormalizedExpr) (_closed : ¬ CendClosedLines expressions)
    (_constant : ¬ CendConstantLines expressions) (plain : CendPlainLines expressions) :
    ¬ ProofsLean.Correct cendSealedMachine cendSpec
      ([InstructionLine.pe expressions] : List InstructionLine) :=
  cendPE_plain_not_correct both expressions plain

/-- **The both-halves residual plus the read-set bridge closes every plain line
that cannot reach the high input word.**  Combining §5's syntactic criterion with
§6's class statement: if the line's own region constants keep it away from LM0
word `0`, the high input half is free and the line is incorrect. -/
theorem cendPE_plainLines_not_correct_of_words (bridge : CendLineReadSetLm0Words)
    (both : CendPlainALUBothHalvesRefuted)
    (expressions : List NormalizedExpr) (plain : CendPlainLines expressions)
    (avoids : (0 : Nat) ∉ cendExpressionsLm0Words
      ((expressions.map NormalizedExpr.toParsed).filter
        parsedExprIsIntegerMatrixReadStageInput)) :
    ¬ ProofsLean.Correct cendSealedMachine cendSpec
      ([InstructionLine.pe expressions] : List InstructionLine) :=
  cendPE_plain_not_correct_of_words bridge expressions plain avoids

end ProofsLean.MNCore
