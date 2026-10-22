import ProofsLean.CendPlainWitness

/-! # `12.convert-endian`: the read-set bridge from region constants

`ProofsLean/CendPlainWitness.lean` reduced the plain-ALU family of
`12.convert-endian` to the region-constant criterion
`cendPE_plain_not_correct_of_words` / `_of_wordsLow`, but left the two bridges
`CendOperandLm0WordsCoverReads` and `CendLineReadSetLm0Words` as named
hypotheses: turning a word `w` of the executor's `accessRegion` into a member of
the enumerated window `cendOperandLm0Words` failed because the `Fin` proof of
`DirectMemoryAccess.address` is pinned to the address value, which makes the
step a dependent elimination rather than a rewrite.

This module closes the technical residual and states exactly what survives of
the line-level statement.

## 1. The Nat-witness restatement of the address equation

`cendResolvedLm0AddressNat` states the already-proved address equation of
`cendResolvedLm0Address` with a fresh Nat witness `start` and the equation
`start = access.address.val`.  The existential body is then about a *variable*,
so substituting the address value is a plain `Nat` rewrite.

## 2. The `accessRegion` half

`accessRegion_word_val` turns `w ∈ accessRegion access` into
`w.2.val = (access.address.val + index) % capacity` for some word index below the
access width.  With §1 this is a `Finset.mem_image` step.

## 3. The enumeration

`mem_cendLm0WordsAt` and `mem_cendRegionLm0Words` place that address in the
`Finset` image `cendLm0WordsAt`, and `mem_addressCandidates_foldr` distributes
over the region's candidate addresses.

## 4. The operand bridge

`cendOperandLm0WordsCoverReads` is proved unconditionally.

## 5. The line bridge

The literal `CendLineReadSetLm0Words` of `CendPlainWitness` quantifies over
**every** plain line, including `.zero` / `.immediate` rows.  Such a row has an
empty source list but reads its *destination* region (its two executor sources
are the destination itself), so the literal statement is **false**; §7 proves
`¬ CendLineReadSetLm0Words` on the concrete plain row `zeroRow` of
`ProofsLean/FootprintCoverage.lean`.  The true line-level form is
`CendALUOperandLm0WordsCoverReads`, restricted to lines whose rows are all
`.alu` rows — exactly the plain non-constant rows of the narrow family.

## 6. The unconditional narrow family

`CendPlainALUNarrow` is the plain all-`.alu` family whose region constants keep
the line away from LM0 word `0` or from LM0 word `1`.  `cendPE_plainALUNarrow_closed`
refutes it unconditionally, and `cendPENonConstantRefuted_plain_narrow` is the
corresponding residual-free variant of
`CendPlainWitness.cendPENonConstantRefuted_plain` (which assumed the both-halves
residual).

Finally, `CendPlainALUWordBothRefuted` is the *syntactic* residual: the line's
computed word set contains both `0` and `1`.  It implies the old read-set
both-halves condition on all-`.alu` lines, and `cendPE_alu_not_correct` reduces
every plain all-`.alu` line to it: the narrow part stays unconditional, and the
residual is now a finite computation on the line's constants.  The genuinely
open class is the wide `.long`/`.double` one, which no read-set/collision
argument can close.

## Trust

No `sorry`, no `admit`, no `native_decide`, no new axioms, and no existing
module is edited.
-/

namespace ProofsLean.MNCore

open Issue
open PEMemory

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false

/-! ## 1. The Nat-witness restatement of the address equation -/

/-- **The resolved address of an LM0 `.mem` source, about a Nat variable.**
This is `cendResolvedLm0Address` with the address replaced by a fresh Nat
witness `start` constrained by `start = access.address.val`.  The existential
body's equation mentions only `start`, so it can be rewritten without
transporting the `Fin access.bank.capacity` proof. -/
theorem cendResolvedLm0AddressNat
    (region : Issue.Region) (rounded : Bool)
    (precision : IntegerALU.Precision) (group : Fin 4) (l2b : Fin 2) (l1b : Fin 8)
    (mab : Fin 16) (pe cycle : Fin 4) (access : DirectMemoryAccess)
    (hres : ParsedOperand.toParsedIntegerInput? (.mem ⟨.lm0, region⟩ false false rounded none)
      precision group l2b l1b mab pe cycle 0 0 0 = some (.memory access rounded))
    (hbank : access.bank = PEMemory.Bank.lm0) :
    ∃ start : Nat, start = access.address.val ∧
      ∃ width : PEMemory.Width, parsedWidth? region.width = some width ∧
        access.width = width ∧
        ∃ c ∈ region.addressCandidates,
          start = ((c + (match region.madpe with
            | some threshold => if pe.val ≤ threshold then width.words else 0
            | none => 0)) / width.words * width.words) % PEMemory.Bank.lm0.capacity := by
  obtain ⟨width, hwidth?, hwidthEq, c, hc, haddr⟩ :=
    cendResolvedLm0Address region rounded precision group l2b l1b mab pe cycle access hres hbank
  exact ⟨access.address.val, rfl, width, hwidth?, hwidthEq, c, hc, haddr⟩

/-! ## 2. The `accessRegion` half: address values -/

/-- **The address of a word of an access region.**  Every word of
`accessRegion ⟨bank, width, start⟩` has its address equal to the resolved start
address plus a word index below the access width, modulo the bank capacity. -/
theorem accessRegion_word_val (bank : PEMemory.Bank) (width : PEMemory.Width)
    (start : Fin bank.capacity) (w : WordRef)
    (hw : w ∈ accessRegion ⟨bank, width, start⟩) :
    ∃ index : Nat, index < PEMemory.count bank width ∧
      w.2.val = (start.val + index) % bank.capacity := by
  obtain ⟨address, hwEq, within⟩ := (mem_accessRegion_iff ⟨bank, width, start⟩ w).mp hw
  subst hwEq
  refine ⟨PEMemory.distance bank start address, within, ?_⟩
  have hstep : address = PEMemory.advance bank start (PEMemory.distance bank start address) :=
    (advance_distance_capacity bank start address).symm
  calc
    (⟨bank, address⟩ : WordRef).2.val = address.val := rfl
    _ = (PEMemory.advance bank start (PEMemory.distance bank start address)).val :=
      congrArg Fin.val hstep
    _ = (start.val + PEMemory.distance bank start address) % bank.capacity := rfl

/-- The same statement for an access record, without destructuring it. -/
theorem accessRegion_word_val' (access : DirectMemoryAccess) (w : WordRef)
    (hw : w ∈ accessRegion access) :
    ∃ index : Nat, index < PEMemory.count access.bank access.width ∧
      w.2.val = (access.address.val + index) % access.bank.capacity := by
  obtain ⟨bank, width, start⟩ := access
  exact accessRegion_word_val bank width start w hw

/-! ## 3. The enumeration as a `Finset` image -/

/-- **Membership in the enumerated window at one candidate address.** -/
theorem mem_cendLm0WordsAt (width : PEMemory.Width) (candidate : Nat) (index : Nat)
    (hindex : index < width.words) (offset : Nat)
    (hoff : offset ∈ ({0, width.words} : Finset Nat)) :
    (((candidate + offset) / width.words * width.words) % PEMemory.Bank.lm0.capacity +
        index) % PEMemory.Bank.lm0.capacity ∈ cendLm0WordsAt width candidate := by
  unfold cendLm0WordsAt
  rw [Finset.mem_biUnion]
  exact ⟨offset, hoff, Finset.mem_image.mpr ⟨index, Finset.mem_range.mpr hindex, rfl⟩⟩

/-- **Membership in the fold over the region's candidate addresses.** -/
theorem mem_addressCandidates_foldr (candidates : List Nat) (width : PEMemory.Width)
    (x : Nat) :
    x ∈ candidates.foldr (fun candidate acc => acc ∪ cendLm0WordsAt width candidate) ∅ ↔
      ∃ candidate ∈ candidates, x ∈ cendLm0WordsAt width candidate := by
  induction candidates with
  | nil => simp
  | cons candidate rest ih =>
      rw [List.foldr_cons, Finset.mem_union, ih]
      simp only [List.mem_cons]
      constructor
      · rintro (⟨c, hc, hx⟩ | h)
        · exact ⟨c, Or.inr hc, hx⟩
        · exact ⟨candidate, Or.inl rfl, h⟩
      · rintro ⟨c, rfl | hc, hx⟩
        · exact Or.inr hx
        · exact Or.inl ⟨c, hc, hx⟩

/-- **Membership in the enumerated window of a region.** -/
theorem mem_cendRegionLm0Words (region : Issue.Region) (width : PEMemory.Width)
    (hwidth : parsedWidth? region.width = some width)
    (candidate : Nat) (hc : candidate ∈ region.addressCandidates) (index : Nat)
    (hindex : index < width.words) (offset : Nat)
    (hoff : offset ∈ ({0, width.words} : Finset Nat)) :
    (((candidate + offset) / width.words * width.words) % PEMemory.Bank.lm0.capacity +
        index) % PEMemory.Bank.lm0.capacity ∈ cendRegionLm0Words region := by
  unfold cendRegionLm0Words
  rw [hwidth]
  exact (mem_addressCandidates_foldr region.addressCandidates width _).mpr
    ⟨candidate, hc, mem_cendLm0WordsAt width candidate index hindex offset hoff⟩

/-! ## 4. The operand bridge -/

/-- **The operand-level bridge of the region-constant criterion.**  Every LM0
word the executor reads through a successfully resolved integer source operand is
one of the words the operand's own region constants enumerate in
`cendOperandLm0Words`.

The proof is the Nat-witness restatement of §1: the address equation is first
turned into an equation about `start = access.address.val` (a plain `Nat`), and
only then is `w ∈ accessRegion` unfolded into `w.2.val = (start + index) % 4096`
with `index` below the access width.  The last step is `Finset.mem_image`. -/
theorem cendOperandLm0WordsCoverReads_proof : CendOperandLm0WordsCoverReads := by
  intro operand precision group l2b l1b mab pe cycle input hres w hw hbankW
  cases operand with
  | mem access neg ext rounded mask =>
      obtain ⟨ibank, region⟩ := access
      rw [parsed_integer_memory_input_preserves_rounding_and_ignores_mask] at hres
      cases hacc : ParsedOperand.toDirectMemoryAccess? (.mem ⟨ibank, region⟩ false false false none)
          pe cycle 0 0 0 with
      | none =>
          rw [hacc] at hres
          simp at hres
      | some resolved =>
          simp only [hacc, Option.map_some, Option.some.injEq] at hres
          subst hres
          simp only [ParsedIntegerInput.readsRegion_memory] at hw
          have hbankResolved : resolved.bank = PEMemory.Bank.lm0 := by
            have h := accessRegion_bank resolved hw
            rw [hbankW] at h
            exact h.symm
          have hIssueBank : ibank = Issue.Bank.lm0 := by
            have h := issueBank_of_resolved ibank region pe cycle 0 0 0 resolved hacc
            rw [hbankResolved] at h
            cases hb : ibank <;> simp [issueBankToRegisterBank, hb] at h ⊢
          subst hIssueBank
          have hparsed : ParsedOperand.toParsedIntegerInput?
              (.mem ⟨.lm0, region⟩ false false rounded none) precision group l2b l1b mab
              pe cycle 0 0 0 = some (.memory resolved rounded) := by
            rw [parsed_integer_memory_input_preserves_rounding_and_ignores_mask, hacc]
            rfl
          obtain ⟨start, hstart, width, hwidth, hwidthEq, candidate, hc, hstartEq⟩ :=
            cendResolvedLm0AddressNat region rounded precision group l2b l1b mab pe cycle
              resolved hparsed hbankResolved
          obtain ⟨index, hindex, hval⟩ := accessRegion_word_val' resolved w hw
          have hindex' : index < width.words := by
            rw [hbankResolved, hwidthEq] at hindex
            simpa [PEMemory.count] using hindex
          have hoffset : (match region.madpe with
              | some threshold => if pe.val ≤ threshold then width.words else 0
              | none => 0) ∈ ({0, width.words} : Finset Nat) :=
            madpeOffset_mem region width pe
          have hwords : w.2.val ∈ cendLm0WordsAt width candidate := by
            rw [hval, ← hstart, hbankResolved, hstartEq]
            exact mem_cendLm0WordsAt width candidate index hindex' _ hoffset
          have hregion : w.2.val ∈ cendRegionLm0Words region := by
            unfold cendRegionLm0Words
            rw [hwidth]
            exact (mem_addressCandidates_foldr region.addressCandidates width _).mpr
              ⟨candidate, hc, hwords⟩
          simpa [cendOperandLm0Words] using hregion
  | fixed kind =>
      simp only [ParsedOperand.toParsedIntegerInput?, Option.some.injEq] at hres
      subst hres
      simp only [ParsedIntegerInput.readsRegion_fixed] at hw
      exact absurd hw (by simp)
  | forward kind neg ext rounded =>
      simp only [ParsedOperand.toParsedIntegerInput?, Option.some.injEq] at hres
      subst hres
      simp only [ParsedIntegerInput.readsRegion_forward] at hw
      exact absurd hw (by simp)
  | bar lm1 width mask =>
      simp [ParsedOperand.toParsedIntegerInput?, ParsedOperand.toDirectMemoryAccess?,
        ParsedOperand.toDirectMemoryAccessMode?] at hres
  | omr entry mask =>
      simp [ParsedOperand.toParsedIntegerInput?, ParsedOperand.toDirectMemoryAccess?,
        ParsedOperand.toDirectMemoryAccessMode?] at hres
  | matrix y width row =>
      simp [ParsedOperand.toParsedIntegerInput?, ParsedOperand.toDirectMemoryAccess?,
        ParsedOperand.toDirectMemoryAccessMode?] at hres
  | nowrite =>
      simp [ParsedOperand.toParsedIntegerInput?, ParsedOperand.toDirectMemoryAccess?,
        ParsedOperand.toDirectMemoryAccessMode?] at hres
  | l1bm width address =>
      simp [ParsedOperand.toParsedIntegerInput?, ParsedOperand.toDirectMemoryAccess?,
        ParsedOperand.toDirectMemoryAccessMode?] at hres
  | l2bm address l2b =>
      simp [ParsedOperand.toParsedIntegerInput?, ParsedOperand.toDirectMemoryAccess?,
        ParsedOperand.toDirectMemoryAccessMode?] at hres
  | dar address =>
      simp [ParsedOperand.toParsedIntegerInput?, ParsedOperand.toDirectMemoryAccess?,
        ParsedOperand.toDirectMemoryAccessMode?] at hres

/-! ## 5. The line-level bridge for all-`.alu` lines -/

/-- **The line-level bridge for plain all-`.alu` lines.**  Every LM0 word the
line's prepared read set contains is one of the words its source operands'
region constants enumerate.

The all-`.alu` hypothesis is essential: a `.zero` / `.immediate` row reads its
*destination* region (its two executor sources are the destination itself) while
its source list is empty (§7). -/
def CendALUOperandLm0WordsCoverReads : Prop :=
  ∀ (expressions : List NormalizedExpr),
    (∀ expression ∈ expressions.map NormalizedExpr.toParsed,
      ∃ (name : ParsedAluName) (precision : Option ParsedPrecision)
        (unsigned : Bool) (arg : Option (Fin 256)),
        expression.op = .alu name precision unsigned arg) →
    ∀ (w : WordRef), w ∈ cendLineReadSet expressions → w.1 = PEMemory.Bank.lm0 →
      w.2.val ∈ cendExpressionsLm0Words
        ((expressions.map NormalizedExpr.toParsed).filter
          parsedExprIsIntegerMatrixReadStageInput)

/-- **The all-`.alu` line bridge, proved.**  The read set of one prepared cycle
is inside `sourceReadUpperBound` (`aluCycleReadSet_subset_sourceReadUpperBound`),
and the operand bridge of §4 covers each word of that bound. -/
theorem cendALUOperandLm0WordsCoverReads_proof : CendALUOperandLm0WordsCoverReads := by
  intro expressions hallu w hw hbank
  unfold cendLineReadSet at hw
  unfold preparedListReadSet parsedExpressionReadSet at hw
  obtain ⟨expression, hmember, cycle, _hcycle, hread⟩ := hw
  have hmapMem : expression ∈ expressions.map NormalizedExpr.toParsed :=
    List.mem_of_mem_filter hmember
  obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hmapMem
  obtain ⟨name, precision, unsigned, arg, hop⟩ :=
    hallu source.toParsed (List.mem_map.mpr ⟨source, hsource, rfl⟩)
  have hbound : w ∈ sourceReadUpperBound source.toParsed
      (parsedPEHazardControl (cendInitialState 0) cendPE).context.group
      (parsedPEHazardControl (cendInitialState 0) cendPE).context.l2b
      (parsedPEHazardControl (cendInitialState 0) cendPE).context.l1b
      (parsedPEHazardControl (cendInitialState 0) cendPE).context.mab
      (parsedPEHazardControl (cendInitialState 0) cendPE).context.pe
      (parsedPEHazardControl (cendInitialState 0) cendPE).context.bar0
      (parsedPEHazardControl (cendInitialState 0) cendPE).context.bar1
      (parsedPEHazardControl (cendInitialState 0) cendPE).context.tWord :=
    aluCycleReadSet_subset_sourceReadUpperBound zeroInitialPERegisterFiles.maskRegisters
      source.toParsed (parsedPEHazardControl (cendInitialState 0) cendPE)
      (((expressions.map NormalizedExpr.toParsed).filter
        parsedExprIsIntegerMatrixReadStageInput).any parsedExprHasSingleLineWriteMask)
      cycle ⟨name, precision, unsigned, arg, hop⟩ hread
  unfold sourceReadUpperBound at hbound
  obtain ⟨oper, hoper, cycle', precision', input, hres, hregion⟩ := hbound
  have hoperWords : w.2.val ∈ cendOperandLm0Words oper := by
    refine cendOperandLm0WordsCoverReads_proof oper precision'
      (parsedPEHazardControl (cendInitialState 0) cendPE).context.group
      (parsedPEHazardControl (cendInitialState 0) cendPE).context.l2b
      (parsedPEHazardControl (cendInitialState 0) cendPE).context.l1b
      (parsedPEHazardControl (cendInitialState 0) cendPE).context.mab
      (parsedPEHazardControl (cendInitialState 0) cendPE).context.pe
      cycle' input ?_ w hregion hbank
    simpa [parsedPEHazardControl, cendInitialState, rustSimulatorInitialState,
      ParsedIntegerContext.ofLinearIndex] using hres
  have hexprWords : w.2.val ∈ cendOperandsLm0Words source.toParsed.sources :=
    (mem_cendOperandsLm0Words_iff source.toParsed.sources w.2.val).mpr
      ⟨oper, hoper, hoperWords⟩
  exact (mem_cendExpressionsLm0Words_iff _ w.2.val).mpr
    ⟨source.toParsed, hmember, hexprWords⟩

/-! ## 6. The unconditional narrow family -/

/-- **The plain narrow family of `12.convert-endian`.**  Every row is an `.alu`
row, and the line's own region constants keep it away from LM0 word `0` or from
LM0 word `1`.  Such a line misses the corresponding input half, so §4's
diagonalisation refutes it; no both-halves residual is assumed. -/
def CendPlainALUNarrow (expressions : List NormalizedExpr) : Prop :=
  (∀ expression ∈ expressions.map NormalizedExpr.toParsed,
    ∃ (name : ParsedAluName) (precision : Option ParsedPrecision)
      (unsigned : Bool) (arg : Option (Fin 256)),
      expression.op = .alu name precision unsigned arg) ∧
  ((0 : Nat) ∉ cendExpressionsLm0Words
      ((expressions.map NormalizedExpr.toParsed).filter
        parsedExprIsIntegerMatrixReadStageInput) ∨
    (1 : Nat) ∉ cendExpressionsLm0Words
      ((expressions.map NormalizedExpr.toParsed).filter
        parsedExprIsIntegerMatrixReadStageInput))

/-- **A plain all-`.alu` line whose operands cannot reach LM0 word `0` is
incorrect.**  This is `cendPE_plain_not_correct_of_words` with the bridge
discharged: the region-constant criterion is now a theorem, not a hypothesis. -/
theorem cendPE_alu_not_correct_of_words
    (expressions : List NormalizedExpr)
    (plain : (expressions.map NormalizedExpr.toParsed).all
      parsedExprIsPlainIntegerALU = true)
    (hallu : ∀ expression ∈ expressions.map NormalizedExpr.toParsed,
      ∃ (name : ParsedAluName) (precision : Option ParsedPrecision)
        (unsigned : Bool) (arg : Option (Fin 256)),
        expression.op = .alu name precision unsigned arg)
    (avoids : (0 : Nat) ∉ cendExpressionsLm0Words
      ((expressions.map NormalizedExpr.toParsed).filter
        parsedExprIsIntegerMatrixReadStageInput)) :
    ¬ ProofsLean.Correct cendSealedMachine cendSpec
      ([InstructionLine.pe expressions] : List InstructionLine) := by
  have notHigh : InputHalf.word .high ∉ cendLineReadSet expressions := by
    intro member
    exact avoids (cendALUOperandLm0WordsCoverReads_proof expressions hallu
      (InputHalf.word .high) member rfl)
  exact cendPE_plain_not_correct_of_avoidsHigh expressions plain notHigh

/-- **A plain all-`.alu` line whose operands cannot reach LM0 word `1` is
incorrect.** -/
theorem cendPE_alu_not_correct_of_wordsLow
    (expressions : List NormalizedExpr)
    (plain : (expressions.map NormalizedExpr.toParsed).all
      parsedExprIsPlainIntegerALU = true)
    (hallu : ∀ expression ∈ expressions.map NormalizedExpr.toParsed,
      ∃ (name : ParsedAluName) (precision : Option ParsedPrecision)
        (unsigned : Bool) (arg : Option (Fin 256)),
        expression.op = .alu name precision unsigned arg)
    (avoids : (1 : Nat) ∉ cendExpressionsLm0Words
      ((expressions.map NormalizedExpr.toParsed).filter
        parsedExprIsIntegerMatrixReadStageInput)) :
    ¬ ProofsLean.Correct cendSealedMachine cendSpec
      ([InstructionLine.pe expressions] : List InstructionLine) := by
  have notLow : InputHalf.word .low ∉ cendLineReadSet expressions := by
    intro member
    exact avoids (by
      simpa using cendALUOperandLm0WordsCoverReads_proof expressions hallu
        (InputHalf.word .low) member rfl)
  exact cendPE_plain_not_correct_of_avoidsLow expressions plain notLow

/-- **The unconditional narrow family.**  A plain all-`.alu` line whose region
constants keep it away from LM0 word `0` *or* away from LM0 word `1` is
incorrect. -/
theorem cendPE_alu_not_correct_of_narrow
    (expressions : List NormalizedExpr)
    (plain : (expressions.map NormalizedExpr.toParsed).all
      parsedExprIsPlainIntegerALU = true)
    (hallu : ∀ expression ∈ expressions.map NormalizedExpr.toParsed,
      ∃ (name : ParsedAluName) (precision : Option ParsedPrecision)
        (unsigned : Bool) (arg : Option (Fin 256)),
        expression.op = .alu name precision unsigned arg)
    (avoids : (0 : Nat) ∉ cendExpressionsLm0Words
        ((expressions.map NormalizedExpr.toParsed).filter
          parsedExprIsIntegerMatrixReadStageInput) ∨
      (1 : Nat) ∉ cendExpressionsLm0Words
        ((expressions.map NormalizedExpr.toParsed).filter
          parsedExprIsIntegerMatrixReadStageInput)) :
    ¬ ProofsLean.Correct cendSealedMachine cendSpec
      ([InstructionLine.pe expressions] : List InstructionLine) := by
  rcases avoids with avoids | avoids
  · exact cendPE_alu_not_correct_of_words expressions plain hallu avoids
  · exact cendPE_alu_not_correct_of_wordsLow expressions plain hallu avoids

/-- **A plain all-`.alu` line whose operands cannot reach LM0 word `0` is
incorrect**, in the class shape of `CendPlainLines`. -/
theorem cendPE_aluLines_not_correct_of_words
    (expressions : List NormalizedExpr) (plain : CendPlainLines expressions)
    (hallu : ∀ expression ∈ expressions.map NormalizedExpr.toParsed,
      ∃ (name : ParsedAluName) (precision : Option ParsedPrecision)
        (unsigned : Bool) (arg : Option (Fin 256)),
        expression.op = .alu name precision unsigned arg)
    (avoids : (0 : Nat) ∉ cendExpressionsLm0Words
      ((expressions.map NormalizedExpr.toParsed).filter
        parsedExprIsIntegerMatrixReadStageInput)) :
    ¬ ProofsLean.Correct cendSealedMachine cendSpec
      ([InstructionLine.pe expressions] : List InstructionLine) :=
  cendPE_alu_not_correct_of_words expressions plain hallu avoids

/-- **The syntactic both-words class.**  The line's own region constants reach
both LM0 word `0` and LM0 word `1`.  For an all-`.alu` line this is implied by
the read-set both-halves condition (the bridge says the read set's LM0 words are
inside the enumerated set), so refuting this class refutes the old
`CendPlainALUBothHalves` residual on that family. -/
def CendPlainALUWordBoth (expressions : List NormalizedExpr) : Prop :=
  (0 : Nat) ∈ cendExpressionsLm0Words
      ((expressions.map NormalizedExpr.toParsed).filter
        parsedExprIsIntegerMatrixReadStageInput) ∧
    (1 : Nat) ∈ cendExpressionsLm0Words
      ((expressions.map NormalizedExpr.toParsed).filter
        parsedExprIsIntegerMatrixReadStageInput)

/-- **The syntactic residual of the plain all-`.alu` family.**  This is the old
both-halves residual with the read-set hypothesis replaced by its checkable,
sufficient condition `CendPlainALUWordBoth`. -/
def CendPlainALUWordBothRefuted : Prop :=
  ∀ (expressions : List NormalizedExpr),
    (expressions.map NormalizedExpr.toParsed).all parsedExprIsPlainIntegerALU = true →
    (∀ expression ∈ expressions.map NormalizedExpr.toParsed,
      ∃ (name : ParsedAluName) (precision : Option ParsedPrecision)
        (unsigned : Bool) (arg : Option (Fin 256)),
        expression.op = .alu name precision unsigned arg) →
    CendPlainALUWordBoth expressions →
    ¬ ProofsLean.Correct cendSealedMachine cendSpec
      ([InstructionLine.pe expressions] : List InstructionLine)

/-- **Every plain all-`.alu` line is refuted from the syntactic residual.**  If
the line reaches one input word syntactically, the narrow theorem of §6 applies;
otherwise it reaches both, which is the residual. -/
theorem cendPE_alu_not_correct (bothWord : CendPlainALUWordBothRefuted)
    (expressions : List NormalizedExpr)
    (plain : (expressions.map NormalizedExpr.toParsed).all
      parsedExprIsPlainIntegerALU = true)
    (hallu : ∀ expression ∈ expressions.map NormalizedExpr.toParsed,
      ∃ (name : ParsedAluName) (precision : Option ParsedPrecision)
        (unsigned : Bool) (arg : Option (Fin 256)),
        expression.op = .alu name precision unsigned arg) :
    ¬ ProofsLean.Correct cendSealedMachine cendSpec
      ([InstructionLine.pe expressions] : List InstructionLine) := by
  by_cases h0 : (0 : Nat) ∈ cendExpressionsLm0Words
      ((expressions.map NormalizedExpr.toParsed).filter
        parsedExprIsIntegerMatrixReadStageInput)
  · by_cases h1 : (1 : Nat) ∈ cendExpressionsLm0Words
        ((expressions.map NormalizedExpr.toParsed).filter
          parsedExprIsIntegerMatrixReadStageInput)
    · exact bothWord expressions plain hallu ⟨h0, h1⟩
    · exact cendPE_alu_not_correct_of_wordsLow expressions plain hallu h1
  · exact cendPE_alu_not_correct_of_words expressions plain hallu h0

/-- **The plain narrow family is refuted end-to-end.**  This is the residual-free
form of the narrow half of `cendPENonConstantRefuted_plain`: no read-set bridge
and no `CendPlainALUBothHalvesRefuted` are assumed. -/
theorem cendPE_plainALUNarrow_closed
    (expressions : List NormalizedExpr)
    (plain : (expressions.map NormalizedExpr.toParsed).all
      parsedExprIsPlainIntegerALU = true)
    (narrow : CendPlainALUNarrow expressions) :
    ¬ ProofsLean.Correct cendSealedMachine cendSpec
      ([InstructionLine.pe expressions] : List InstructionLine) :=
  cendPE_alu_not_correct_of_narrow expressions plain narrow.1 narrow.2

/-- **The plain all-`.alu` part of `CendPENonConstantRefuted`, from the syntactic
residual.**  Unconditional in the both-halves read-set residual; the remaining
obligation is the checkable `CendPlainALUWordBothRefuted`. -/
theorem cendPENonConstantRefuted_plain_of_wordBoth
    (bothWord : CendPlainALUWordBothRefuted)
    (expressions : List NormalizedExpr)
    (_closed : ¬ CendClosedLines expressions)
    (_constant : ¬ CendConstantLines expressions)
    (plain : CendPlainLines expressions)
    (hallu : ∀ expression ∈ expressions.map NormalizedExpr.toParsed,
      ∃ (name : ParsedAluName) (precision : Option ParsedPrecision)
        (unsigned : Bool) (arg : Option (Fin 256)),
        expression.op = .alu name precision unsigned arg) :
    ¬ ProofsLean.Correct cendSealedMachine cendSpec
      ([InstructionLine.pe expressions] : List InstructionLine) :=
  cendPE_alu_not_correct bothWord expressions plain hallu

/-- **The narrow part of `CendPENonConstantRefuted`, unconditionally.**  This is
the residual-free variant of `CendPlainWitness.cendPENonConstantRefuted_plain`:
the both-halves residual is replaced by the region-constant criterion
`CendPlainALUNarrow`, which is checked on the line's own constants. -/
theorem cendPENonConstantRefuted_plain_narrow
    (expressions : List NormalizedExpr)
    (_closed : ¬ CendClosedLines expressions)
    (_constant : ¬ CendConstantLines expressions)
    (plain : CendPlainLines expressions)
    (narrow : CendPlainALUNarrow expressions) :
    ¬ ProofsLean.Correct cendSealedMachine cendSpec
      ([InstructionLine.pe expressions] : List InstructionLine) :=
  cendPE_plainALUNarrow_closed expressions plain narrow

/-! ## 7. The `.zero` obstruction to the literal line-level statement

The literal `CendLineReadSetLm0Words` of `CendPlainWitness` quantifies over every
plain line, including `.zero` / `.immediate` rows.  Such a row has an empty source
list but reads its *destination* region: its two executor sources are the
destination itself.  The read-set half of this obstruction is already
machine-checked in `ProofsLean/FootprintCoverage.lean`
(`zeroRow_readSet_nonempty`); below it is strengthened with the bank of the
resolved destination and instantiated at the `12.convert-endian` state. -/

/-- **The `.zero` row's prepared read set is nonempty, and entirely LM0.**  The
witness is the resolved destination access of the row; its bank is read off the
static destination bank/width projection, so the read set contains an LM0 word
although `zeroRow` has no source operands at all. -/
theorem zeroRow_readSet_bank (state : State) :
    ∃ w : WordRef, w ∈ preparedListReadSet (state.peRegisters plusTwoPE).maskRegisters
      ((([zeroRow].map NormalizedExpr.toParsed).filter
        parsedExprIsIntegerMatrixReadStageInput))
      (parsedPEHazardControl state plusTwoPE) ∧ w.1 = PEMemory.Bank.lm0 := by
  obtain ⟨access, haccess⟩ := zeroDestination_resolves state 0
  have hbankAccess : access.bank = PEMemory.Bank.lm0 := by
    have hpair : (access.bank, access.width) = (PEMemory.Bank.lm0, PEMemory.Width.long) := by
      have staticEq := ParsedOperand.toDirectMemoryDestination?_bankWidth zeroDestination
        (parsedPEHazardControl state plusTwoPE).context.pe 0
        (parsedPEHazardControl state plusTwoPE).context.bar0
        (parsedPEHazardControl state plusTwoPE).context.bar1
        (parsedPEHazardControl state plusTwoPE).context.tWord
      rw [haccess] at staticEq
      have hstatic : ParsedOperand.directDestinationBankWidth? zeroDestination =
          some (PEMemory.Bank.lm0, PEMemory.Width.long) := by
        simp [zeroDestination, ParsedOperand.directDestinationBankWidth?,
          issueBankToRegisterBank, parsedWidth?]
      rw [hstatic] at staticEq
      exact Option.some.inj staticEq
    exact congrArg Prod.fst hpair
  have hany : (([zeroRow].map NormalizedExpr.toParsed).filter
      parsedExprIsIntegerMatrixReadStageInput).any parsedExprHasSingleLineWriteMask = false := by
    rw [zeroRow_filter]
    simp [zeroRow, NormalizedExpr.toParsed, parsedExprHasSingleLineWriteMask,
      parsedOperandHasSingleLineWriteMask]
  refine ⟨⟨access.bank, access.address⟩, ?_, hbankAccess⟩
  rw [zeroRow_filter]
  simp only [preparedListReadSet, parsedExpressionReadSet, hany]
  refine ⟨zeroRow.toParsed, by simp, 0, by simp [parsedIntegerALUCycles], ?_⟩
  simp only [aluCycleReadSet, zeroRow, NormalizedExpr.toParsed]
  obtain ⟨ws, hws⟩ := Option.isSome_iff_exists.mp
    (ParsedOperand.resolveMemoryWriteSelection_mem_isSome
      ⟨.lm0, ⟨2, 0, 0, 0, 0, false, none⟩⟩ access none
      (state.peRegisters plusTwoPE).maskRegisters 0
      (parsedPEHazardControl state plusTwoPE).directive false)
  obtain ⟨fs, hfs⟩ := resolveFlushSelection?_always_resolves none
    (state.peRegisters plusTwoPE).maskRegisters 0
  simp only [zeroDestination] at haccess
  simp [ParsedExpr.toDirectMaskedConstantWrites?, ParsedExpr.toDirectMaskedConstantDestinations?,
    ParsedExpr.toDirectMaskedConstantDestination?,
    ParsedExpr.toDirectMaskedIntegerAccessesInLine?, ParsedOp.executionRequest,
    zeroDestination, haccess, hws, hfs, optionConstantReads, constantTargetReads,
    maskedIntegerReads, ParsedIntegerInput.readsRegion,
    parsedExprHasSingleLineWriteMask, parsedOperandHasSingleLineWriteMask]
  exact mem_accessRegion_self access

/-- The strengthened `.zero` obstruction at the `12.convert-endian` initial
state, phrased with the read set `cendLineReadSet` actually computes. -/
theorem zeroRow_cend_readSet :
    ∃ w : WordRef, w ∈ cendLineReadSet [zeroRow] ∧ w.1 = PEMemory.Bank.lm0 := by
  obtain ⟨w, hw, hbank⟩ := zeroRow_readSet_bank (cendInitialState 0)
  exact ⟨w, by
    simpa [cendLineReadSet, plusTwoPE, cendPE, cendInitialState, cendInitialPERegisters]
      using hw, hbank⟩

/-- **The literal line-level bridge is false.**  `zeroRow` is a plain integer
row (`zeroRow_plain`), survives the integer-stage filter (`zeroRow_stage`), and
has no source operands, yet its prepared read set contains an LM0 word.  Hence
the conclusion "every LM0 word of the read set is among the words the *source*
operands reach" fails at that word: `CendLineReadSetLm0Words` cannot be proved
and must be replaced by its all-`.alu` form (§5). -/
theorem cendLineReadSetLm0Words_false : ¬ CendLineReadSetLm0Words := by
  intro bridge
  obtain ⟨w, hw, hbank⟩ := zeroRow_cend_readSet
  have hmem := bridge [zeroRow] zeroRow_plain w hw hbank
  rw [zeroRow_filter] at hmem
  simp [cendExpressionsLm0Words, cendOperandsLm0Words, zeroRow, NormalizedExpr.toParsed] at hmem

end ProofsLean.MNCore
