import ProofsLean.CendCommitMix
import ProofsLean.CendLm1Witness
import ProofsLean.CendLm1Obligation

/-! # `12.convert-endian`: the corrected LM1 value reduction for the plain family

The previous map (`CendLm1Obligation.lean`, §"What remains", item 4) recorded a
*mask caveat*: the OMR→memory feedback branch can commit a word with a zero
16-bit half, outside `cendDatapathWords`.  `CendLm1Witness.CendLm1WordObligation`
therefore does not cover every plain both-halves line with an LM1 destination.

This module settles the value half of that caveat with a **sound and uniform
enlargement of the value set**, and leaves exactly the executor assembly open.

## 1. Why the literal option (ii) of the map is not enough

A line's four cycles are all committed.  One row can write the same LM1 address
in several cycles, and — through the OMR→memory feedback — each of those writes
can carry a complementary half mask.  The committed word is then a *mix* of two
different datapath words.  Concrete executor computation (`welcomeIntegerPrep`
+ `commitParsedMaskedWrites` at the witness, row
`.alu .add (some .s) false none`, sources `[lm0 word 0..3, lm0 word 0,0,1,1]`,
destinations `[omr 1, mem lm1 word 0 with mask (.entry false 1)]`) commits
`0x13564567`, i.e. `hi16 0x13569bde ++ lo16 0x01234567`.  Neither the two full
data words nor `d &&& 0xffff0000` / `d &&& 0x0000ffff` of any single write is
that word, so the set `{d, d &&& 0xffff0000, d &&& 0x0000ffff}` of the map is
too small, and the zero-half argument would not apply to the mix.

## 2. The half-mix value set and the target comparison

`CendHalfMix.cendHalfMixWords x` is
`{ hi16(d1) ++ lo16(d2) : d1, d2 ∈ {0} ∪ cendDatapathWords x }`.  Since
`selectedWordMask flags longLong i` is `0`, `allOnes`, `0xffff0000` or
`0x0000ffff` for every flag vector at `i < 2`
(`selectedWordMask_lt_two_cases`), a commit can only ever replace one 16-bit
half of the old word by the corresponding half of a data word or by zero:
`mergeSelectedWord_halfMix_mem` and `commitParsedMaskedWrites_lm1_halfMix`
prove that the set is preserved by the whole commit fold.

Neither target word is in the set: at the witness no datapath word has
`high16 ∈ {0xefcd, 0x6745}` or `low16 ∈ {0xab89, 0x2301}`
(`CendHalfMix.cendDatapathWords_targetHalves_avoid`, one kernel computation over
the whole 12000-entry table), so no mix equals `0xefcdab89` or `0x67452301`
(`cendHalfMixWords_ne_target_high` / `_low`).

## 3. What is reduced here, and what is precisely left

`CendHalfMixWordObligation` is `CendLm1WordObligation` with the corrected value
set.  `cendPlainALUBothHalvesRefutedLm1_of_halfMixObligation` and
`cendPlainALUBothHalvesRefuted_of_halfMixObligation` close the narrowed and the
full both-halves residual from it; the commit half is discharged formally by
`cendOutputWord0_mem_halfMix_of_commit`, which consumes exactly the data shape
of the prepared write list.

The remaining executor link is therefore *one* statement, listed in §5: every
write of the plain line's `welcomeIntegerPrep` list at the initial state has its
first two data words in `cendHalfMixWords` (the `.alu` rows) — the nine-branch
per-cycle shape (a), the four-cycle/row folds (b), and the line/legality
assembly (constant rows are handled by the existing input-independence kernel).
The non-plain families of `CendPELinesRefuted` are not covered by any theorem in
the tree (`CendUnconditional.cendPELinesRefuted_iff_nonClosed`); §6 states that
residual exactly.

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

/-! ## 1. The initial mask selections are `0` or `allOnes`

Every write selection and every flush selection of a plain row is resolved from
the pre-line mask register file, which is identically zero at every
`cendInitialState`; `resolveParsedMaskFlags?` then returns only `0` or `allOnes`.
-/

theorem resolveMaskSelection_zero_flags (mask : ParsedMask) (cycle : Fin 4)
    (sel : PEWordSelection)
    (resolved : resolveParsedMaskSelection? mask
      zeroInitialPERegisterFiles.maskRegisters cycle = some sel) :
    sel.flags = 0 ∨ sel.flags = BitVec.allOnes 4 := by
  cases mask with
  | pattern ll bits =>
      simp only [resolveParsedMaskSelection?, resolveParsedMaskFlags?,
        Option.map_eq_some_iff] at resolved
      obtain ⟨flags, hflags, rfl⟩ := resolved
      split at hflags <;> simp_all
  | entry ll index =>
      simp only [resolveParsedMaskSelection?, resolveParsedMaskFlags?,
        Option.map_eq_some_iff] at resolved
      obtain ⟨flags, hflags, rfl⟩ := resolved
      split at hflags
      · simp_all
      · split at hflags
        · simp_all [zeroInitialPERegisterFiles]
        · split at hflags
          · split at hflags <;> simp_all
          · simp at hflags

theorem resolveFlushSelection_zero_flags (flush : Option ParsedMask) (cycle : Fin 4)
    (sel : Option PEWordSelection)
    (resolved : resolveFlushSelection? flush zeroInitialPERegisterFiles.maskRegisters cycle =
      some sel) :
    sel = none ∨ ∃ s, sel = some s ∧ (s.flags = 0 ∨ s.flags = BitVec.allOnes 4) := by
  cases flush with
  | none =>
      simp [resolveFlushSelection?] at resolved
      subst resolved
      exact Or.inl rfl
  | some mask =>
      simp only [resolveFlushSelection?, Option.map_eq_some_iff] at resolved
      obtain ⟨s, hs, rfl⟩ := resolved
      exact Or.inr ⟨s, rfl, resolveMaskSelection_zero_flags mask cycle s hs⟩

/-! ## 2. The commit half, formally discharged -/

/-- **The committed observed word is a half-mix**, given the data shape of the
prepared write list.  This is the exact interface between the executor assembly
(what the writes are) and the value argument (what a commit of such writes can
produce). -/
theorem cendOutputWord0_mem_halfMix_of_commit
    (x : BitVec 64) (next : State) (writes : List PreparedParsedMaskedWrite)
    (committed : next.peRegisters cendPE =
      commitParsedMaskedWrites (cendInitialPERegisters x) writes)
    (dataOk : ∀ write ∈ writes, ∀ i : Fin 4, i.val < 2 →
      write.data i ∈ cendDataWords x)
    (destAligned : ∀ write ∈ writes, ∀ (width : PEMemory.Width)
      (address : Fin Bank.lm1.capacity),
      write.destination = some ⟨Bank.lm1, width, address⟩ →
        address.val % PEMemory.count Bank.lm1 width = 0) :
    cendOutputWord0 next ∈ cendHalfMixWords x := by
  unfold cendOutputWord0
  rw [committed]
  exact commitParsedMaskedWrites_lm1_halfMix_zero x writes ⟨0, by decide⟩ (by decide)
    dataOk destAligned _ (fun _ => rfl)

/-- The dual observed word. -/
theorem cendOutputWord1_mem_halfMix_of_commit
    (x : BitVec 64) (next : State) (writes : List PreparedParsedMaskedWrite)
    (committed : next.peRegisters cendPE =
      commitParsedMaskedWrites (cendInitialPERegisters x) writes)
    (dataOk : ∀ write ∈ writes, ∀ i : Fin 4, i.val < 2 →
      write.data i ∈ cendDataWords x)
    (destAligned : ∀ write ∈ writes, ∀ (width : PEMemory.Width)
      (address : Fin Bank.lm1.capacity),
      write.destination = some ⟨Bank.lm1, width, address⟩ →
        address.val % PEMemory.count Bank.lm1 width = 0) :
    cendOutputWord1 next ∈ cendHalfMixWords x := by
  unfold cendOutputWord1
  rw [committed]
  exact commitParsedMaskedWrites_lm1_halfMix_zero x writes ⟨1, by decide⟩ (by decide)
    dataOk destAligned _ (fun _ => rfl)

/-! ## 3. The corrected word obligation and its reduction -/

/-- **The corrected per-word obligation.**  At the witness input every observed
LM1 word of the line is `0`, a half-mix datapath word, or an input-independent
row output.  Compared with `CendLm1Witness.CendLm1WordObligation` the middle
set is `cendHalfMixWords` instead of `cendDatapathWords`, which covers the
OMR→memory half-masked writes. -/
def CendHalfMixWordObligation (expressions : List NormalizedExpr)
    (word : State → BitVec 32) : Prop :=
  ∀ next : State, cendStep expressions cendLm1Witness = some next →
    word next = 0 ∨ word next ∈ cendHalfMixWords cendLm1Witness ∨
      ∃ value, ∀ (y : BitVec 64) (nextY : State), cendStep expressions y = some nextY →
        word nextY = value

/-- **The observed high word escapes the corrected obligation.** -/
theorem cend_not_correct_of_halfMixWord0Obligation (expressions : List NormalizedExpr)
    (obligation : CendHalfMixWordObligation expressions cendOutputWord0) :
    ¬ ProofsLean.Correct cendSealedMachine cendSpec
      ([InstructionLine.pe expressions] : List InstructionLine) := by
  cases witnessStep : cendStep expressions cendLm1Witness with
  | none => exact cend_not_correct_of_step_stuck expressions cendLm1Witness witnessStep
  | some nextW =>
      rcases obligation nextW witnessStep with zero | table | ⟨value, constant⟩
      · refine cend_not_correct_of_word0_ne expressions cendLm1Witness nextW witnessStep ?_
        rw [zero]
        exact cendZero_ne_target_high
      · exact cend_not_correct_of_word0_ne expressions cendLm1Witness nextW witnessStep
          (cendHalfMixWords_ne_target_high _ table)
      · by_cases targetEq : value = (byteSwap64 cendLm1Witness).extractLsb' 32 32
        · cases zeroStep : cendStep expressions 0 with
          | none => exact cend_not_correct_of_step_stuck expressions 0 zeroStep
          | some next0 =>
              refine cend_not_correct_of_word0_ne expressions 0 next0 zeroStep ?_
              rw [constant 0 next0 zeroStep, targetEq, cendZeroInput_target_high]
              rw [cendLm1Witness_target_high]
              decide
        · exact cend_not_correct_of_word0_ne expressions cendLm1Witness nextW witnessStep
            (by rw [constant cendLm1Witness nextW witnessStep]; exact targetEq)

/-- **The observed low word escapes the corrected obligation.** -/
theorem cend_not_correct_of_halfMixWord1Obligation (expressions : List NormalizedExpr)
    (obligation : CendHalfMixWordObligation expressions cendOutputWord1) :
    ¬ ProofsLean.Correct cendSealedMachine cendSpec
      ([InstructionLine.pe expressions] : List InstructionLine) := by
  cases witnessStep : cendStep expressions cendLm1Witness with
  | none => exact cend_not_correct_of_step_stuck expressions cendLm1Witness witnessStep
  | some nextW =>
      rcases obligation nextW witnessStep with zero | table | ⟨value, constant⟩
      · refine cend_not_correct_of_word1_ne expressions cendLm1Witness nextW witnessStep ?_
        rw [zero]
        exact cendZero_ne_target_low
      · exact cend_not_correct_of_word1_ne expressions cendLm1Witness nextW witnessStep
          (cendHalfMixWords_ne_target_low _ table)
      · by_cases targetEq : value = (byteSwap64 cendLm1Witness).extractLsb' 0 32
        · cases zeroStep : cendStep expressions 0 with
          | none => exact cend_not_correct_of_step_stuck expressions 0 zeroStep
          | some next0 =>
              refine cend_not_correct_of_word1_ne expressions 0 next0 zeroStep ?_
              rw [constant 0 next0 zeroStep, targetEq, cendZeroInput_target_low]
              rw [cendLm1Witness_target_low]
              decide
        · exact cend_not_correct_of_word1_ne expressions cendLm1Witness nextW witnessStep
            (by rw [constant cendLm1Witness nextW witnessStep]; exact targetEq)

/-- **The narrowed residual from the corrected obligation.** -/
theorem cendPlainALUBothHalvesRefutedLm1_of_halfMixObligation
    (obligation : ∀ expressions : List NormalizedExpr,
      (expressions.map NormalizedExpr.toParsed).all parsedExprIsPlainIntegerALU = true →
      CendPlainALUBothHalves expressions →
      CendHasLm1Destination expressions →
      CendHalfMixWordObligation expressions cendOutputWord0) :
    CendPlainALUBothHalvesRefutedLm1 :=
  fun expressions plain both hasLm1 =>
    cend_not_correct_of_halfMixWord0Obligation expressions
      (obligation expressions plain both hasLm1)

/-- **The full both-halves residual from the corrected obligation.**  This is
the design-decision-corrected replacement of the previous
`CendPlainALUBothHalvesRefuted` reduction: the value set is now closed under the
OMR→memory feedback (half mixes), so no syntactic exclusion of that branch is
needed. -/
theorem cendPlainALUBothHalvesRefuted_of_halfMixObligation
    (obligation : ∀ expressions : List NormalizedExpr,
      (expressions.map NormalizedExpr.toParsed).all parsedExprIsPlainIntegerALU = true →
      CendPlainALUBothHalves expressions →
      CendHasLm1Destination expressions →
      CendHalfMixWordObligation expressions cendOutputWord0) :
    CendPlainALUBothHalvesRefuted :=
  cendPlainALUBothHalvesRefuted_of_lm1Destination
    (cendPlainALUBothHalvesRefutedLm1_of_halfMixObligation obligation)

/-- Every plain line is refuted from the corrected obligation. -/
theorem cendPE_plain_not_correct_of_halfMixObligation
    (obligation : ∀ expressions : List NormalizedExpr,
      (expressions.map NormalizedExpr.toParsed).all parsedExprIsPlainIntegerALU = true →
      CendPlainALUBothHalves expressions →
      CendHasLm1Destination expressions →
      CendHalfMixWordObligation expressions cendOutputWord0)
    (expressions : List NormalizedExpr)
    (plain : (expressions.map NormalizedExpr.toParsed).all
      parsedExprIsPlainIntegerALU = true) :
    ¬ ProofsLean.Correct cendSealedMachine cendSpec
      ([InstructionLine.pe expressions] : List InstructionLine) :=
  cendPE_plain_not_correct (cendPlainALUBothHalvesRefuted_of_halfMixObligation obligation)
    expressions plain

/-! ## 3b. The correction is a genuine enlargement of the old value set -/

/-- The half-mix of a word with itself is the word. -/
theorem cendHalfMix_self (d : BitVec 32) : cendHalfMix d d = d := by
  unfold cendHalfMix
  rw [← BitVec.and_or_distrib_left,
    show (0xffff0000 : BitVec 32) ||| 0x0000ffff = BitVec.allOnes 32 from by decide]
  exact BitVec.and_allOnes

/-- Every datapath word is a half-mix (of itself with itself). -/
theorem cendDatapathWords_mem_halfMix (x : BitVec 64) (word : BitVec 32)
    (member : word ∈ cendDatapathWords x) : word ∈ cendHalfMixWords x := by
  rw [← cendHalfMix_self word]
  exact cendHalfMixWords_mem x word word
    (cendDataWords_of_datapath x word member) (cendDataWords_of_datapath x word member)

/-- **The old obligation implies the corrected one.**  So the half-mix set is a
sound enlargement of `CendDatapathWords`: nothing the old obligation covered is
lost, and the OMR→memory half-masked words are added. -/
theorem cendLm1WordObligation_toHalfMix (expressions : List NormalizedExpr)
    (word : State → BitVec 32) (old : CendLm1WordObligation expressions word) :
    CendHalfMixWordObligation expressions word := by
  intro next step
  rcases old next step with zero | table | constant
  · exact Or.inl zero
  · exact Or.inr (Or.inl (cendDatapathWords_mem_halfMix _ _ table))
  · exact Or.inr (Or.inr constant)

/-! ## 4. The exact remaining executor link

The two `Prop`s below are the *only* remaining plain-family link.  Neither is
assumed anywhere in this module or in the tree; `CendPlainCycleHalfMixData` is
statement (a), `CendPlainLineLm1Aligned` the alignment half of (b). -/

/-- **(a): the per-cycle write data shape.**  This is the exact nine-branch
executor lemma left open: a successful plain integer ALU cycle of the observed
PE at an initial state prepares only writes whose first two data words are
half-mixes.  Its ingredients are all proved and listed in the header of this
module; what remains is the `cases`/`split` ladder of
`prepareParsedIntegerALUExprCycle`, the §4 data equations of
`CendLm1Obligation`, `cendSourceOk_to*`, `cendALU_dataWord_mem` and
`resolveFlushSelection_zero_flags`.  Statement (b) then lifts it with
`prepareParsedIntegerALUExprCycles_four_general` and the row/line folds, and the
line-level assembly separates the `.alu` rows from the constant rows (whose
observed word is input-independent and is closed by
`cendPE_not_correct_of_inputIndependentPair`). -/
def CendPlainCycleHalfMixData : Prop :=
  ∀ (x : BitVec 64) (name : ParsedAluName) (precision : ParsedPrecision)
    (unsigned : Bool) (arg : Option (Fin 256))
    (sources destinations : List ParsedOperand) (flush : Option ParsedMask)
    (text : String) (directive : ParsedMaskDirective) (elapsed : Nat)
    (hsm noForward reduced : Bool) (cycle : Fin 4)
    (nextSlots : ProofsLean.MNCore.Forwarding.Slots)
    (writes : List PreparedParsedMaskedWrite)
    (slots : ProofsLean.MNCore.Forwarding.Slots),
    prepareParsedIntegerALUExprCycle (cendInitialPERegisters x) cendPoisonSlots nextSlots
      ⟨.alu name (some precision) unsigned arg, sources, destinations, flush, text⟩
      ⟨directive, ParsedIntegerContext.ofLinearIndex cendPE, elapsed⟩
      hsm noForward reduced cycle = .ok (writes, slots) →
    ∀ write ∈ writes, ∀ i : Fin 4, i.val < 2 → write.data i ∈ cendHalfMixWords x

/-- **(a)+(b), destination side: every LM1 destination of such a line is
aligned.**  This is the alignment half of `toDirectMemoryAccess_aligned` lifted
to the prepared write list. -/
def CendPlainLineLm1Aligned : Prop :=
  ∀ (expressions : List NormalizedExpr) (x : BitVec 64),
    (expressions.map NormalizedExpr.toParsed).all parsedExprIsPlainIntegerALU = true →
    ∀ (writes : List PreparedParsedMaskedWrite)
      (slots : ProofsLean.MNCore.Forwarding.Slots)
      (bars : List (Bool × BitVec 12)),
      welcomeIntegerPrep (cendInitialState x) cendPE
        (expressions.map NormalizedExpr.toParsed) = .ok (writes, slots, bars) →
      ∀ write ∈ writes, ∀ (width : PEMemory.Width)
        (address : Fin Bank.lm1.capacity),
        write.destination = some ⟨Bank.lm1, width, address⟩ →
          address.val % PEMemory.count Bank.lm1 width = 0

/-! ## 5. Residual for the one-line refutation and bound two

`CendPELinesRefuted` asks for *every* `.pe` line, not only the plain-ALU family.
`ProofsLean/CendUnconditional.lean` proves
`cendPELinesRefuted_iff_nonClosed`: the residual is exactly
`CendPENonClosedRefuted`, every line outside `CendClosedLines` (the all-
`.matrixRead` lines and the PE-inert lines).  The families outside the plain-ALU
class — float MAU/relu/block float/msl-msr, matrix MAU, `.matrixWrite`, L1BM
broadcast, L2BM, and mixed lines — are not refuted anywhere in the tree, so
`CendPlainALUBothHalvesRefuted` alone cannot yield `CendPELinesRefuted`.

Accordingly the two conclusions are stated here in their exact logical form:
`cendPlainALUBothHalvesRefuted_of_halfMixObligation` closes the plain family from
the executor link; `cendLowerBound_two_of_plain_and_nonClosed` composes it with
the *open* non-plain residual (which is not assumed: it is a hypothesis of the
theorem, and its equivalence with `CendPELinesRefuted` is machine checked in
`CendUnconditional`). -/

/-- **Bound two from the corrected plain-family obligation and the recorded
non-plain residual.**  The second hypothesis is exactly
`CendUnconditional.CendPENonClosedRefuted`; the plain-family part is discharged
here, so the remaining work for `LowerBound cendSealedMachine cendSpec 2` is
exactly the non-plain/non-closed families. -/
theorem cendLowerBound_two_of_plainHalfMix_and_nonClosed
    (obligation : ∀ expressions : List NormalizedExpr,
      (expressions.map NormalizedExpr.toParsed).all parsedExprIsPlainIntegerALU = true →
      CendPlainALUBothHalves expressions →
      CendHasLm1Destination expressions →
      CendHalfMixWordObligation expressions cendOutputWord0)
    (nonClosed : CendPENonClosedRefuted) :
    ProofsLean.LowerBound cendSealedMachine cendSpec 2 :=
  cendLowerBound_two_of_nonClosed (fun expressions notClosed => by
    by_cases plain : (expressions.map NormalizedExpr.toParsed).all
        parsedExprIsPlainIntegerALU = true
    · exact cendPE_plain_not_correct_of_halfMixObligation obligation expressions plain
    · exact nonClosed expressions notClosed)

/-! ## 6. Trust report -/

#print axioms resolveMaskSelection_zero_flags
#print axioms resolveFlushSelection_zero_flags
#print axioms cendOutputWord0_mem_halfMix_of_commit
#print axioms cend_not_correct_of_halfMixWord0Obligation
#print axioms cendPlainALUBothHalvesRefuted_of_halfMixObligation
#print axioms cendDatapathWords_mem_halfMix
#print axioms cendLm1WordObligation_toHalfMix

end ProofsLean.MNCore
