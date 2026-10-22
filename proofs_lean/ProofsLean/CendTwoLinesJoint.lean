import ProofsLean.CendTwoLines
import ProofsLean.CendCycleData
import ProofsLean.CendCycleClose

/-! # `12.convert-endian` — the joint mask/value obligation for two lines

`ProofsLean/CendTwoLines.lean` reduces the two-unit-line obligation
`CendTwoLinesRefuted` (and, with the one-line residual, the optimality bound
`LowerBound cendSealedMachine cendSpec 3`) to

```
CendTwoLiveSecondLinesRefuted :=
  ∀ first second, cost first = 1 → ¬ CendAllNoForward second →
    ¬ Correct cendSealedMachine cendSpec [first, .pe second].
```

The empirical characterisation of the two-line search
(`research/experiments/cend2-search/README.md`) says that the obstruction is
**joint mask/value alignment**, not a one-stage value-set obstruction: the
second line can produce a data word that carries a target 16-bit half, but the
mask nibble the first line planted at that cycle selects a *different* 16-bit
half (or the wrong 32-bit word), i.e. the set of lanes whose data is a
byte-reversed half is disjoint from the lanes the planted mask commits.  This
module formalises exactly that joint obligation, and isolates the remaining
executor-shaped statement.

## What is proved here

* §1 — **per-half provenance of a masked merge.**  `selectedWordMask` is one of
  four masks at the two observed word indices (`0`, `allOnes`, the high half
  mask, the low half mask; `selectedWordMask_lt_two_cases`).  A merge with the
  high half mask takes its high 16 bits from the data word and its low 16 bits
  from the old word, and dually for the low mask; a merge with `0` keeps the old
  word and a merge with `allOnes` takes the data word.  Consequently a masked
  merge *cannot* produce the target word when every half the mask selects from
  the data word differs from the corresponding half of the target
  (`CendSelectedHalfSafe` / `mergeSelectedWord_ne_target_of_selectedHalfSafe`).
  This is the formal content of "the lanes the planted mask commits are not the
  byte-reversed halves".

* §2 — **the joint commit-chain theorem.**  A whole commit chain (one line's
  four cycles, or both lines) keeps the observed LM1 word away from the target
  word when the initial word is away and every write's selected halves are
  away (`commitParsedMaskedWrites_lm1_ne_target_of_selectedHalfSafe`).  The
  proof is an induction over the write list; the only changing case is an
  aligned covering `.lm1` write, where `writeWordsMasked_at` reduces the commit
  to one `mergeSelectedWord` and §1 applies.  No value-set closure is involved:
  the hypothesis is per write and per 16-bit half, which is exactly the joint
  reachability statement the search calls for.

* §3 — **the two-line reduction.**  `cendTwoCommitChains_ne_target` composes the
  two folds (`initial → after line 1 → after line 2`).
  `CendTwoLineCommitShape` is the remaining executor-shaped statement, in the
  necessary disjunctive form: for every cost-one first line and every live
  second `.pe` line either the program is stuck on every input, or there is an
  input at which both steps succeed with a two-fold commitment decomposition
  that is aligned and jointly half-safe at the observed word.
  `cendTwoLiveSecondLinesRefuted_of_commitShape` proves
  `CendTwoLiveSecondLinesRefuted` from it, and
  `cendLowerBound_three_of_commitShape` composes it with the one-line residual
  `CendPELinesRefuted` into `LowerBound cendSealedMachine cendSpec 3` and
  `Optimal` for the three-line answer.

* §4 — **the empirical near-hit, formalised.**  At `cendWitness` the target high
  word is `0x08070605`, and the near-hit bus word is `0x08050607` with mask
  nibble `0x3`.  The nibble `0x3` sets bits `1` and `0`, i.e. it selects the
  *second* observed word (`selectedWordMask 0x3 false 1 = allOnes`), while word
  `0` is left untouched (`selectedWordMask 0x3 false 0 = 0`): the commit places
  the data in the wrong word.  The probe nibbles are checked too (`8` selects
  the high half of word `0`, `4` its low half).

* §5 — **the one-stage value set at the witness.**  At `cendWitness` no
  one-stage datapath word carries `0x0807` (high) or `0x0605` (low), nor
  `0x0403`/`0x0201`, so no one-stage half-mix is either target word
  (`cendHalfMixWords_ne_target_high_witness`,
  `cendHalfMixWords_ne_target_low_witness`).  The first line therefore cannot
  supply the target word; a two-line program must assemble it from 16-bit
  halves, which is exactly the joint obligation.  (The empirical two-stage
  search finds halves, and no aligned combination; §1–§3 are the formal shape
  of that statement.)

* §6 — **first-line mask provenance.**  A selection resolved at the initial
  mask register file is whole-word (`cendInitialMaskSelection_flags`,
  `cendInitialFlushSelection_flags`), and a whole-word selection never mixes
  the observed word (`mergeSelectedWord_of_wholeWordFlags`).  Half masking only
  becomes available to the *second* line, through the OMR flag nibbles the
  first line plants (`prepareParsedIntegerMaskWrite` stores
  `BitVec.ofBoolListLE` of the ALU flag bits).  §6b composes this with a
  target-free value set into joint safety
  (`cendCommitsHalfSafe_of_wholeWord_dataSet`), with the `cendWitness`
  instances for both target words.

* §7 — **the lower bound at three**, from the one-line residual and the joint
  shape.

## What is *not* closed here

`CendTwoLineCommitShape`.  Its two conjunctive halves are:

1. the **commit decomposition** of a successful `.pe` step into
   `commitParsedMaskedWrites` of a prepared write list for *arbitrary* (not
   only plain integer ALU) rows, and
2. the **joint safety** of the prepared writes: for every prepared write and
   every observed index `0`/`1`, the 16-bit halves selected by
   `selectedWordMask selection.flags selection.longLong index` differ from the
   corresponding halves of the target word.

Statement (1) is available for plain integer ALU lines
(`cendSealed_pe_prepared`, used by the one-line plain-family closure); for the
other families it is the same executor link the one-line residual
(`CendPENonClosedRefuted`) needs.  Statement (2) is the finite joint
reachability check of the empirical search; §1 isolates it as a per-write
predicate over `(data word, flag nibble)`, §6b discharges it from whole-word
masks plus a target-free value set, and §4 shows what its failure looks like on
the near-hit.

The two-line search in `research/experiments/cend2-search/` is *hazard-checked
assembly*: it forbids a second line that reads a register or memory word the
first line wrote (`DataRaceError`).  The sealed Lean model executes
`InstructionLine`s without the assembler hazard checker, so its two-line space
is strictly larger (a semantically legal, judge-rejected pair is a legal
`cendSealedMachine` program).  `CendTwoLineCommitShape` is stated over the
sealed model, so it is the statement that remains necessary for the Lean
bound; the empirical negative result does not by itself imply it.

No `sorry`, no `admit`, no `native_decide`, no new axioms.  This module does not
edit any existing module.
-/

namespace ProofsLean.MNCore

open Issue
open PEMemory

set_option maxHeartbeats 3200000
set_option maxRecDepth 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false

/-! ## 1. Per-half provenance of the masked merge

`mergeSelectedWord old data enable` replaces the bits of `old` selected by
`enable` with the bits of `data`.  At the observed indices the enable mask is one
of four values, and each has a closed form for the merged word. -/

/-- The four masks that can reach an observed LM1 word. -/
def CendHalfMaskCase (mask : BitVec 32) : Prop :=
  mask = 0 ∨ mask = BitVec.allOnes 32 ∨ mask = 0xffff0000 ∨ mask = 0x0000ffff

theorem cendHalfMaskCase_of_selected (flags : BitVec 4) (longLong : Bool)
    (index : Fin 4) (lt : index.val < 2) :
    CendHalfMaskCase (selectedWordMask flags longLong index) := by
  rcases selectedWordMask_lt_two_cases flags longLong index lt with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))

theorem mergeSelectedWord_zero_eq (old data : BitVec 32) :
    mergeSelectedWord old data 0 = old := by
  show (old &&& ~~~(0 : BitVec 32)) ||| (data &&& 0) = old
  rw [show ~~~(0 : BitVec 32) = BitVec.allOnes 32 from by decide]
  rw [show old &&& BitVec.allOnes 32 = old from BitVec.and_allOnes]
  rw [show data &&& (0 : BitVec 32) = 0 from BitVec.and_zero]
  rw [show old ||| (0 : BitVec 32) = old from BitVec.or_zero]

theorem mergeSelectedWord_allOnes_eq (old data : BitVec 32) :
    mergeSelectedWord old data (BitVec.allOnes 32) = data := by
  show (old &&& ~~~(BitVec.allOnes 32)) ||| (data &&& BitVec.allOnes 32) = data
  rw [show ~~~(BitVec.allOnes 32) = (0 : BitVec 32) from by decide]
  rw [show old &&& (0 : BitVec 32) = 0 from BitVec.and_zero]
  rw [show data &&& BitVec.allOnes 32 = data from BitVec.and_allOnes]
  rw [show (0 : BitVec 32) ||| data = data from BitVec.zero_or]

/-- The high-half provenance of the high half mask: the high 16 bits come from
the data word. -/
theorem mergeSelectedWord_highMask_high (old data : BitVec 32) :
    (mergeSelectedWord old data 0xffff0000) &&& 0xffff0000 = data &&& 0xffff0000 := by
  show ((old &&& ~~~(0xffff0000 : BitVec 32)) ||| (data &&& 0xffff0000)) &&& 0xffff0000
      = data &&& 0xffff0000
  rw [show ~~~(0xffff0000 : BitVec 32) = 0x0000ffff from by decide]
  rw [BitVec.and_or_distrib_right]
  rw [BitVec.and_assoc, BitVec.and_assoc]
  rw [show ((0x0000ffff : BitVec 32) &&& 0xffff0000) = 0 from by decide,
    show ((0xffff0000 : BitVec 32) &&& 0xffff0000) = 0xffff0000 from by decide]
  rw [show old &&& (0 : BitVec 32) = 0 from BitVec.and_zero]
  rw [show (0 : BitVec 32) ||| (data &&& 0xffff0000) = data &&& 0xffff0000 from
    BitVec.zero_or]

/-- The low-half provenance of the low half mask: the low 16 bits come from the
data word. -/
theorem mergeSelectedWord_lowMask_low (old data : BitVec 32) :
    (mergeSelectedWord old data 0x0000ffff) &&& 0x0000ffff = data &&& 0x0000ffff := by
  show ((old &&& ~~~(0x0000ffff : BitVec 32)) ||| (data &&& 0x0000ffff)) &&& 0x0000ffff
      = data &&& 0x0000ffff
  rw [show ~~~(0x0000ffff : BitVec 32) = 0xffff0000 from by decide]
  rw [BitVec.and_or_distrib_right]
  rw [BitVec.and_assoc, BitVec.and_assoc]
  rw [show ((0xffff0000 : BitVec 32) &&& 0x0000ffff) = 0 from by decide,
    show ((0x0000ffff : BitVec 32) &&& 0x0000ffff) = 0x0000ffff from by decide]
  rw [show old &&& (0 : BitVec 32) = 0 from BitVec.and_zero]
  rw [show (0 : BitVec 32) ||| (data &&& 0x0000ffff) = data &&& 0x0000ffff from
    BitVec.zero_or]

/-- **Joint selection safety.**  Every 16-bit half the mask selects from the
data word differs from the corresponding half of the target word.  The mask
`0xffff0000` selects the high half, `0x0000ffff` the low half, and `allOnes`
both halves. -/
def CendSelectedHalfSafe (target data : BitVec 32) (mask : BitVec 32) : Prop :=
  (mask = 0xffff0000 → data &&& 0xffff0000 ≠ target &&& 0xffff0000) ∧
    (mask = 0x0000ffff → data &&& 0x0000ffff ≠ target &&& 0x0000ffff) ∧
      (mask = BitVec.allOnes 32 → data ≠ target)

theorem cendSelectedHalfSafe_zero (target data : BitVec 32) :
    CendSelectedHalfSafe target data 0 := by
  unfold CendSelectedHalfSafe
  exact ⟨fun h => by simp at h, fun h => by simp at h, fun h => by simp at h⟩

theorem cendSelectedHalfSafe_allOnes {target data : BitVec 32}
    (ne : data ≠ target) : CendSelectedHalfSafe target data (BitVec.allOnes 32) := by
  unfold CendSelectedHalfSafe
  exact ⟨fun h => by simp at h, fun h => by simp at h, fun _ => ne⟩

theorem cendSelectedHalfSafe_highMask {target data : BitVec 32}
    (ne : data &&& 0xffff0000 ≠ target &&& 0xffff0000) :
    CendSelectedHalfSafe target data 0xffff0000 := by
  unfold CendSelectedHalfSafe
  refine ⟨fun _ => ne, fun h => ?_, fun h => by simp at h⟩
  exact absurd h (by decide)

theorem cendSelectedHalfSafe_lowMask {target data : BitVec 32}
    (ne : data &&& 0x0000ffff ≠ target &&& 0x0000ffff) :
    CendSelectedHalfSafe target data 0x0000ffff := by
  unfold CendSelectedHalfSafe
  refine ⟨fun h => ?_, fun _ => ne, fun h => by simp at h⟩
  exact absurd h (by decide)

/-- **A jointly safe merge never produces the target word.**  This is the
per-half form of the empirical "the committed lanes do not carry the
byte-reversed halves": the old word is already away from the target, and every
half the mask overwrites with the data word is the wrong half. -/
theorem mergeSelectedWord_ne_target_of_selectedHalfSafe (target old data mask : BitVec 32)
    (hold : old ≠ target) (hmask : CendHalfMaskCase mask)
    (hsafe : CendSelectedHalfSafe target data mask) :
    mergeSelectedWord old data mask ≠ target := by
  rcases hmask with rfl | rfl | rfl | rfl
  · rw [mergeSelectedWord_zero_eq]
    exact hold
  · rw [mergeSelectedWord_allOnes_eq]
    exact hsafe.2.2 rfl
  · intro h
    apply hsafe.1 rfl
    have : (mergeSelectedWord old data 0xffff0000) &&& 0xffff0000 = target &&& 0xffff0000 := by
      rw [h]
    rwa [mergeSelectedWord_highMask_high] at this
  · intro h
    apply hsafe.2.1 rfl
    have : (mergeSelectedWord old data 0x0000ffff) &&& 0x0000ffff = target &&& 0x0000ffff := by
      rw [h]
    rwa [mergeSelectedWord_lowMask_low] at this

/-! ## 2. The joint commit-chain theorem

`commitParsedMaskedWrites` folds the prepared writes in issue order.  At the two
observed words the only writes that change the word are aligned covering `.lm1`
writes, and each reduces to a single `mergeSelectedWord` with one of the four
half masks.  Hence the joint selection safety is preserved by the whole fold. -/

/-- **The joint commit-chain theorem.**  If the observed word starts away from
the target and every prepared write's selected halves are away, the committed
word is away.  No value-set closure and no whole-word invariant is used. -/
theorem commitParsedMaskedWrites_lm1_ne_target_of_selectedHalfSafe
    (writes : List PreparedParsedMaskedWrite) (target : Fin Bank.lm1.capacity)
    (targetLt : target.val < 2) (targetWord : BitVec 32)
    (destAligned : ∀ write ∈ writes, ∀ (width : PEMemory.Width)
      (address : Fin Bank.lm1.capacity),
      write.destination = some ⟨Bank.lm1, width, address⟩ →
        address.val % PEMemory.count Bank.lm1 width = 0)
    (safe : ∀ write ∈ writes, ∀ i : Fin 4, i.val < 2 →
      CendSelectedHalfSafe targetWord (write.data i)
        (selectedWordMask write.selection.flags write.selection.longLong i)) :
    ∀ files : IntegerRegisterFiles, files.lm1 target ≠ targetWord →
      (commitParsedMaskedWrites files writes).lm1 target ≠ targetWord := by
  induction writes with
  | nil =>
      intro files hold
      simpa [commitParsedMaskedWrites] using hold
  | cons write rest ih =>
      intro files hold
      rw [commitParsedMaskedWrites_cons]
      apply ih
      · intro item member width address destination
        exact destAligned item (List.mem_cons_of_mem _ member) width address destination
      · intro item member i hi
        exact safe item (List.mem_cons_of_mem _ member) i hi
      · obtain ⟨destination, maskUpdate, data, selection⟩ := write
        cases maskUpdate with
        | some update =>
            exact hold
        | none =>
            cases destination with
            | none => exact hold
            | some access =>
                obtain ⟨bank, width, address⟩ := access
                cases bank with
                | lm1 =>
                    show ((welcomeCommitStep files
                      ⟨some ⟨Bank.lm1, width, address⟩, none, data, selection⟩).lm1
                        target) ≠ targetWord
                    simp only [welcomeCommitStep]
                    rw [writeDirectAccessMasked_lm1_apply]
                    by_cases within : PEMemory.distance Bank.lm1 address target <
                        PEMemory.count Bank.lm1 width
                    · rw [PEMemory.writeWordsMasked_at _ width files.lm1 address target data
                        selection.flags selection.longLong within]
                      have indexLt : (⟨PEMemory.distance Bank.lm1 address target,
                          Nat.lt_of_lt_of_le within (PEMemory.count_le_four _ _)⟩ :
                          Fin 4).val < 2 :=
                        distance_lm1_lt_two width address target
                          (destAligned ⟨some ⟨Bank.lm1, width, address⟩, none, data,
                            selection⟩ (by simp) width address rfl) within targetLt
                      exact mergeSelectedWord_ne_target_of_selectedHalfSafe targetWord
                        (files.lm1 target) (data ⟨PEMemory.distance Bank.lm1 address target,
                          Nat.lt_of_lt_of_le within (PEMemory.count_le_four _ _)⟩)
                        (selectedWordMask selection.flags selection.longLong
                          ⟨PEMemory.distance Bank.lm1 address target,
                            Nat.lt_of_lt_of_le within (PEMemory.count_le_four _ _)⟩)
                        hold
                        (cendHalfMaskCase_of_selected selection.flags selection.longLong
                          ⟨PEMemory.distance Bank.lm1 address target,
                            Nat.lt_of_lt_of_le within (PEMemory.count_le_four _ _)⟩ indexLt)
                        (safe ⟨some ⟨Bank.lm1, width, address⟩, none, data, selection⟩
                          (by simp) ⟨PEMemory.distance Bank.lm1 address target,
                            Nat.lt_of_lt_of_le within (PEMemory.count_le_four _ _)⟩ indexLt)
                    · rw [PEMemory.writeWordsMasked_preserves_outside _ width files.lm1 address
                        target data selection.flags selection.longLong
                        (Nat.le_of_not_lt within)]
                      exact hold
                | lm0 =>
                    show ((welcomeCommitStep files
                      ⟨some ⟨Bank.lm0, width, address⟩, none, data, selection⟩).lm1
                        target) ≠ targetWord
                    simp only [welcomeCommitStep]
                    rw [writeDirectAccessMasked_lm1_eq _ _ _ _ _ _ (by decide)]
                    exact hold
                | grf0 =>
                    show ((welcomeCommitStep files
                      ⟨some ⟨Bank.grf0, width, address⟩, none, data, selection⟩).lm1
                        target) ≠ targetWord
                    simp only [welcomeCommitStep]
                    rw [writeDirectAccessMasked_lm1_eq _ _ _ _ _ _ (by decide)]
                    exact hold
                | grf1 =>
                    show ((welcomeCommitStep files
                      ⟨some ⟨Bank.grf1, width, address⟩, none, data, selection⟩).lm1
                        target) ≠ targetWord
                    simp only [welcomeCommitStep]
                    rw [writeDirectAccessMasked_lm1_eq _ _ _ _ _ _ (by decide)]
                    exact hold
                | t =>
                    show ((welcomeCommitStep files
                      ⟨some ⟨Bank.t, width, address⟩, none, data, selection⟩).lm1
                        target) ≠ targetWord
                    simp only [welcomeCommitStep]
                    rw [writeDirectAccessMasked_lm1_eq _ _ _ _ _ _ (by decide)]
                    exact hold

/-! ## 3. The two-line handoff

The two lines commit through two `commitParsedMaskedWrites` folds: the first from
the initial register files, the second from the files the first line left.  The
joint chain theorem applies to each fold. -/

/-- Every `.lm1` destination of the prepared writes is aligned. -/
def CendCommitsAligned (writes : List PreparedParsedMaskedWrite) : Prop :=
  ∀ write ∈ writes, ∀ (width : PEMemory.Width) (address : Fin Bank.lm1.capacity),
    write.destination = some ⟨Bank.lm1, width, address⟩ →
      address.val % PEMemory.count Bank.lm1 width = 0

/-- Every prepared write is jointly half-safe at the two observed words. -/
def CendCommitsHalfSafe (targetWord : BitVec 32)
    (writes : List PreparedParsedMaskedWrite) : Prop :=
  ∀ write ∈ writes, ∀ i : Fin 4, i.val < 2 →
    CendSelectedHalfSafe targetWord (write.data i)
      (selectedWordMask write.selection.flags write.selection.longLong i)

/-- **The joint chain at the initial files.**  The observed word starts at `0`,
so it is away from a non-zero target, and the joint chain theorem applies. -/
theorem cendOutputWord0_ne_of_commitChain
    (x : BitVec 64) (files : IntegerRegisterFiles)
    (writes : List PreparedParsedMaskedWrite) (targetWord : BitVec 32)
    (aligned : CendCommitsAligned writes) (safe : CendCommitsHalfSafe targetWord writes)
    (committed : files = commitParsedMaskedWrites (cendInitialPERegisters x) writes)
    (targetNe : targetWord ≠ 0) :
    files.lm1 ⟨0, by decide⟩ ≠ targetWord := by
  rw [committed]
  exact commitParsedMaskedWrites_lm1_ne_target_of_selectedHalfSafe writes
    ⟨0, by decide⟩ (by decide) targetWord aligned safe
    (cendInitialPERegisters x)
    (fun zeroTarget => targetNe zeroTarget.symm)

/-- **The two-fold composition.**  If the first line's commit chain is jointly
half-safe from the initial files and the second line's chain is jointly
half-safe from the first line's files, the observed word after both lines is not
the target word.  This is the formal "joint mask/value alignment" statement:
no value-set closure, no whole-word invariant, only the per-write alignment of
the committed 16-bit halves. -/
theorem cendTwoCommitChains_ne_target
    (x : BitVec 64) (s1Files : IntegerRegisterFiles) (s2 : State)
    (writes1 writes2 : List PreparedParsedMaskedWrite) (targetWord : BitVec 32)
    (aligned1 : CendCommitsAligned writes1) (aligned2 : CendCommitsAligned writes2)
    (safe1 : CendCommitsHalfSafe targetWord writes1)
    (safe2 : CendCommitsHalfSafe targetWord writes2)
    (commit1 : s1Files =
      commitParsedMaskedWrites (cendInitialPERegisters x) writes1)
    (commit2 : s2.peRegisters cendPE =
      commitParsedMaskedWrites s1Files writes2)
    (targetNe : targetWord ≠ 0) :
    cendOutputWord0 s2 ≠ targetWord := by
  have firstNe : s1Files.lm1 ⟨0, by decide⟩ ≠ targetWord :=
    cendOutputWord0_ne_of_commitChain x s1Files writes1 targetWord aligned1 safe1
      commit1 targetNe
  have secondNe : (commitParsedMaskedWrites s1Files writes2).lm1 ⟨0, by decide⟩ ≠
      targetWord :=
    commitParsedMaskedWrites_lm1_ne_target_of_selectedHalfSafe writes2
      ⟨0, by decide⟩ (by decide) targetWord aligned2 safe2 s1Files firstNe
  intro same
  unfold cendOutputWord0 at same
  rw [commit2] at same
  exact secondNe same

/-- **The remaining executor-shaped statement.**  For every cost-one first line
and every live second `.pe` line either

* the two-line program is stuck on every input (then it cannot be `Correct`), or
* there is an input at which both steps succeed with a two-fold commit
  decomposition that is aligned and jointly half-safe at the observed word.

The witness is program-dependent (as the one-line `imm` case already is); the
target word at that witness is non-zero so the initial word is away.  This is
the necessary statement: a correct program is never stuck on all inputs, so its
correctness forces the safe-witness branch.  The target word is the high word of
`byteSwap64`, i.e. the observed word `0` of the `12.convert-endian`
postcondition. -/
def CendTwoLineCommitShape : Prop :=
  ∀ (first : InstructionLine) (second : List NormalizedExpr),
    InstructionLine.cost first = 1 → ¬ CendAllNoForward second →
    (∀ x : BitVec 64,
        (cendSealedMachine.step first (cendInitialState x)).bind
          (fun middle => cendSealedMachine.step (InstructionLine.pe second) middle) = none) ∨
      ∃ (x : BitVec 64) (s1 s2 : State)
        (writes1 writes2 : List PreparedParsedMaskedWrite),
        cendSealedMachine.step first (cendInitialState x) = some s1 ∧
        cendSealedMachine.step (InstructionLine.pe second) s1 = some s2 ∧
        s1.peRegisters cendPE =
          commitParsedMaskedWrites (cendInitialPERegisters x) writes1 ∧
        s2.peRegisters cendPE = commitParsedMaskedWrites (s1.peRegisters cendPE) writes2 ∧
        CendCommitsAligned writes1 ∧ CendCommitsAligned writes2 ∧
        CendCommitsHalfSafe ((byteSwap64 x).extractLsb' 32 32) writes1 ∧
        CendCommitsHalfSafe ((byteSwap64 x).extractLsb' 32 32) writes2 ∧
        (byteSwap64 x).extractLsb' 32 32 ≠ 0

/-- **`CendTwoLiveSecondLinesRefuted` from the executor-shaped statement.**  The
whole value/commit argument is discharged here; only `CendTwoLineCommitShape`
remains.  A correct program is not stuck on any input, so the safe-witness
branch applies, and the two-fold joint chain theorem contradicts the
postcondition at that witness. -/
theorem cendTwoLiveSecondLinesRefuted_of_commitShape
    (shape : CendTwoLineCommitShape) : CendTwoLiveSecondLinesRefuted := by
  intro first second firstCost notNoforward correct
  rcases shape first second firstCost notNoforward with stuck | safeWitness
  · obtain ⟨result, executed, -⟩ := correct.2 cendWitness (cendSpec_admissible cendWitness)
    rw [cendSpec_initial, cend_execute_two] at executed
    rw [stuck cendWitness] at executed
    simp at executed
  · obtain ⟨x, s1, s2, writes1, writes2, step1, step2, commit1, commit2,
      aligned1, aligned2, safe1, safe2, targetNe⟩ := safeWitness
    obtain ⟨result, executed, post⟩ := correct.2 x (cendSpec_admissible x)
    rw [cendSpec_initial] at executed
    rw [cend_execute_two] at executed
    obtain ⟨middle, firstStep, secondStep⟩ := Option.bind_eq_some_iff.mp executed
    rw [step1] at firstStep
    have middleEq : middle = s1 := (Option.some.inj firstStep).symm
    rw [show middle = s1 from middleEq] at secondStep
    rw [step2] at secondStep
    have resultEq : result = s2 := (Option.some.inj secondStep).symm
    have post' : cendOutputPair s2 = byteSwap64 x := by
      have := post
      unfold cendSpec at this
      simp only at this
      rw [resultEq] at this
      exact this
    have word0 : cendOutputWord0 s2 = (byteSwap64 x).extractLsb' 32 32 := by
      have pair := post'
      rw [cendOutputPair_eq_append] at pair
      have ext := congrArg (fun value : BitVec 64 => value.extractLsb' 32 32) pair
      rw [show BitVec.extractLsb' 32 32 (cendOutputWord0 s2 ++ cendOutputWord1 s2) =
          cendOutputWord0 s2 from BitVec.extractLsb'_append_eq_left] at ext
      simpa [cendOutputWord0] using ext
    exact cendTwoCommitChains_ne_target x (s1.peRegisters cendPE) s2 writes1 writes2
      ((byteSwap64 x).extractLsb' 32 32) aligned1 aligned2 safe1 safe2 commit1 commit2
      targetNe word0

/-! ## 4. The empirical near-hit, formalised

The search's sharpest witness is `cendWitness = 0x0102030405060708`; its target
high word is `0x08070605`.  On PE2 the two-line ALU fragment produces the whole
target word in one bus word; on PE0 (the observed PE) the same program gives
`0x08050607`.  On both, the first line's flags at that cycle are `0x3`.  The
nibble `0x3` sets bits `1` and `0`, i.e. it selects the *second* observed word
(`selectedWordMask 0x3 false 1 = allOnes`) and leaves the *first* word untouched
(`selectedWordMask 0x3 false 0 = 0`).  The data and the mask are therefore
misaligned by word position.  The probe nibbles are checked too: `8` selects the
high half of word `0`, `4` its low half. -/

theorem cendNearHit_target_high :
    (byteSwap64 cendWitness).extractLsb' 32 32 = 0x08070605 :=
  cendWitness_target_high

/-- The near-hit nibble `0x3` leaves the first observed word untouched. -/
theorem cendNearHit_word0_uncommitted :
    selectedWordMask (0x3 : BitVec 4) false 0 = 0 := by decide

/-- The near-hit nibble `0x3` selects the *second* observed word whole. -/
theorem cendNearHit_word1_selected :
    selectedWordMask (0x3 : BitVec 4) false 1 = BitVec.allOnes 32 := by decide

/-- The probe nibble `8` is the high half mask of the first observed word. -/
theorem cendProbe_highHalf :
    selectedWordMask (0x8 : BitVec 4) false 0 = 0xffff0000 := by decide

/-- The probe nibble `4` is the low half mask of the first observed word. -/
theorem cendProbe_lowHalf :
    selectedWordMask (0x4 : BitVec 4) false 0 = 0x0000ffff := by decide

/-- The PE0 near-hit bus word. -/
theorem cendNearHit_bus_ne_target :
    (0x08050607 : BitVec 32) ≠ 0x08070605 := by decide

/-- **The wrong-word commit.**  A commit of the near-hit bus word with the
planted nibble `0x3` at the first observed word writes nothing there: the target
word stays uncommitted, because the nibble selects the second word. -/
theorem cendNearHit_word0_keeps_old (old : BitVec 32) :
    mergeSelectedWord old (0x08050607 : BitVec 32)
      (selectedWordMask (0x3 : BitVec 4) false 0) = old := by
  rw [cendNearHit_word0_uncommitted, mergeSelectedWord_zero_eq]

/-- The PE0 near-hit bus word is itself away from the target word, so even a
commit of it would be safe at the first observed word.  The PE2 obstruction is
the *wrong position* (word `1` instead of word `0`), which the mask facts above
record. -/
theorem cendNearHit_bus_safe (old : BitVec 32) (hold : old ≠ 0x08070605) :
    mergeSelectedWord old (0x08050607 : BitVec 32)
      (selectedWordMask (0x3 : BitVec 4) false 0) ≠ 0x08070605 := by
  rw [cendNearHit_word0_keeps_old]
  exact hold

/-! ## 5. The one-stage value set at the witness

The *first* line's committed words are (for the plain family) one-stage
half-mixes of `cendDatapathWords` (`cendHalfMixWordObligation_of_plain` in
`ProofsLean/CendCycleClose.lean`).  At `cendWitness` no datapath word carries
`0x0807` in its high 16 bits or `0x0605` in its low 16 bits, and dually
`0x0403`/`0x0201` for the second target word.  Hence no one-stage half-mix at
the witness is either target word: the first line cannot supply the whole
target word, so a two-line program must assemble it from 16-bit halves — which
is exactly the joint obligation of §1–§3. -/

/-- One kernel check over the one-stage datapath table at `cendWitness`: no word
carries a target 16-bit half in the target position. -/
theorem cendDatapathWords_cendWitness_targetHalves_avoid :
    (cendDatapathWords cendWitness).all (fun word =>
      (word &&& 0xffff0000 != (0x08070000 : BitVec 32)) &&
      (word &&& 0x0000ffff != (0x00000605 : BitVec 32)) &&
      (word &&& 0xffff0000 != (0x04030000 : BitVec 32)) &&
      (word &&& 0x0000ffff != (0x00000201 : BitVec 32))) = true := by
  decide

theorem cendDatapathWords_high_half_ne (word : BitVec 32)
    (member : word ∈ cendDatapathWords cendWitness) :
    word &&& 0xffff0000 ≠ 0x08070000 := by
  have h := List.all_eq_true.mp cendDatapathWords_cendWitness_targetHalves_avoid
    word member
  intro same
  rw [same] at h
  simp at h

theorem cendDatapathWords_low_half_ne (word : BitVec 32)
    (member : word ∈ cendDatapathWords cendWitness) :
    word &&& 0x0000ffff ≠ 0x00000605 := by
  have h := List.all_eq_true.mp cendDatapathWords_cendWitness_targetHalves_avoid
    word member
  intro same
  rw [same] at h
  simp at h

theorem cendDatapathWords_second_high_half_ne (word : BitVec 32)
    (member : word ∈ cendDatapathWords cendWitness) :
    word &&& 0xffff0000 ≠ 0x04030000 := by
  have h := List.all_eq_true.mp cendDatapathWords_cendWitness_targetHalves_avoid
    word member
  intro same
  rw [same] at h
  simp at h

theorem cendDatapathWords_second_low_half_ne (word : BitVec 32)
    (member : word ∈ cendDatapathWords cendWitness) :
    word &&& 0x0000ffff ≠ 0x00000201 := by
  have h := List.all_eq_true.mp cendDatapathWords_cendWitness_targetHalves_avoid
    word member
  intro same
  rw [same] at h
  simp at h

/-- The data-word list is `0` prepended to the datapath table. -/
theorem cendDataWords_mem_cases (word : BitVec 32)
    (member : word ∈ cendDataWords cendWitness) :
    word = 0 ∨ word ∈ cendDatapathWords cendWitness :=
  List.mem_cons.mp member

theorem cendDataWords_high_half_ne (word : BitVec 32)
    (member : word ∈ cendDataWords cendWitness) :
    word &&& 0xffff0000 ≠ 0x08070000 := by
  rcases cendDataWords_mem_cases word member with rfl | mem
  · decide
  · exact cendDatapathWords_high_half_ne word mem

theorem cendDataWords_low_half_ne (word : BitVec 32)
    (member : word ∈ cendDataWords cendWitness) :
    word &&& 0x0000ffff ≠ 0x00000605 := by
  rcases cendDataWords_mem_cases word member with rfl | mem
  · decide
  · exact cendDatapathWords_low_half_ne word mem

theorem cendDataWords_second_high_half_ne (word : BitVec 32)
    (member : word ∈ cendDataWords cendWitness) :
    word &&& 0xffff0000 ≠ 0x04030000 := by
  rcases cendDataWords_mem_cases word member with rfl | mem
  · decide
  · exact cendDatapathWords_second_high_half_ne word mem

theorem cendDataWords_second_low_half_ne (word : BitVec 32)
    (member : word ∈ cendDataWords cendWitness) :
    word &&& 0x0000ffff ≠ 0x00000201 := by
  rcases cendDataWords_mem_cases word member with rfl | mem
  · decide
  · exact cendDatapathWords_second_low_half_ne word mem

/-- **No one-stage half-mix is the target high word at the witness.**  The high
16 bits of a half-mix are the high 16 bits of its first argument, and no data
word has high half `0x0807`. -/
theorem cendHalfMixWords_ne_target_high_witness (word : BitVec 32)
    (member : word ∈ cendHalfMixWords cendWitness) :
    word ≠ 0x08070605 := by
  obtain ⟨hi, hhi, lo, hlo, rfl⟩ := cendHalfMixWords_exists cendWitness word member
  intro same
  have high := congrArg (fun value => value &&& 0xffff0000) same
  simp only [cendHalfMix_high] at high
  exact cendDataWords_high_half_ne hi hhi high

/-- **No one-stage half-mix is the target low word at the witness.** -/
theorem cendHalfMixWords_ne_target_low_witness (word : BitVec 32)
    (member : word ∈ cendHalfMixWords cendWitness) :
    word ≠ 0x04030201 := by
  obtain ⟨hi, hhi, lo, hlo, rfl⟩ := cendHalfMixWords_exists cendWitness word member
  intro same
  have low := congrArg (fun value => value &&& 0x0000ffff) same
  simp only [cendHalfMix_low] at low
  exact cendDataWords_second_low_half_ne lo hlo low

/-! ## 6. First-line mask provenance: whole-word selections

A *first* line resolves its mask selections from the initial mask register file,
which is identically zero, so its selections are `0` or `allOnes`: the first
line cannot mix 16-bit halves at all.  Half masking only becomes available to the
*second* line, through the OMR flag nibbles the first line plants
(`prepareParsedIntegerMaskWrite` stores `BitVec.ofBoolListLE` of the ALU flags).
This is the first half of the empirical characterisation. -/

/-- A mask selection resolved at the initial register files is whole-word. -/
theorem cendInitialMaskSelection_flags (input : BitVec 64) (mask : ParsedMask)
    (cycle : Fin 4) (sel : PEWordSelection)
    (resolved : resolveParsedMaskSelection? mask
      (cendInitialPERegisters input).maskRegisters cycle = some sel) :
    sel.flags = 0 ∨ sel.flags = BitVec.allOnes 4 := by
  rw [cendInitialPERegisters_maskRegisters_fun] at resolved
  exact resolveMaskSelection_zero_flags mask cycle sel resolved

/-- A flush selection resolved at the initial register files is whole-word. -/
theorem cendInitialFlushSelection_flags (input : BitVec 64) (flush : Option ParsedMask)
    (cycle : Fin 4) (sel : Option PEWordSelection)
    (resolved : resolveFlushSelection? flush
      (cendInitialPERegisters input).maskRegisters cycle = some sel) :
    sel = none ∨ ∃ chosen, sel = some chosen ∧
      (chosen.flags = 0 ∨ chosen.flags = BitVec.allOnes 4) := by
  rw [cendInitialPERegisters_maskRegisters_fun] at resolved
  exact resolveFlushSelection_zero_flags flush cycle sel resolved

/-- Enumerate the four indices. -/
theorem cendFinFour_cases (index : Fin 4) :
    index = (⟨0, by decide⟩ : Fin 4) ∨ index = (⟨1, by decide⟩ : Fin 4) ∨
      index = (⟨2, by decide⟩ : Fin 4) ∨ index = (⟨3, by decide⟩ : Fin 4) := by
  have bound := index.isLt
  have h : index.val = 0 ∨ index.val = 1 ∨ index.val = 2 ∨ index.val = 3 := by omega
  rcases h with h | h | h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Or.inl (Fin.ext h))
  · exact Or.inr (Or.inr (Or.inl (Fin.ext h)))
  · exact Or.inr (Or.inr (Or.inr (Fin.ext h)))

/-- With zero flags every selected-word mask is `0` or `allOnes`. -/
theorem selectedWordMask_zero_flags (longLong : Bool) (index : Fin 4) :
    selectedWordMask (0 : BitVec 4) longLong index = 0 ∨
      selectedWordMask (0 : BitVec 4) longLong index = BitVec.allOnes 32 := by
  rcases cendFinFour_cases index with rfl | rfl | rfl | rfl <;>
    cases longLong <;> decide

/-- With all-ones flags every selected-word mask is `allOnes`. -/
theorem selectedWordMask_allOnes_flags (longLong : Bool) (index : Fin 4) :
    selectedWordMask (BitVec.allOnes 4) longLong index = BitVec.allOnes 32 := by
  rcases cendFinFour_cases index with rfl | rfl | rfl | rfl <;>
    cases longLong <;> decide

/-- **A whole-word selection never mixes the observed word.**  If the flags are
`0` or `allOnes`, the selected-word mask is `0` or `allOnes` for every index and
width, so the merge keeps the old word or replaces it by the data word. -/
theorem mergeSelectedWord_of_wholeWordFlags (old data : BitVec 32) (flags : BitVec 4)
    (whole : flags = 0 ∨ flags = BitVec.allOnes 4) (longLong : Bool) (index : Fin 4) :
    mergeSelectedWord old data (selectedWordMask flags longLong index) = old ∨
      mergeSelectedWord old data (selectedWordMask flags longLong index) = data := by
  rcases whole with rfl | rfl
  · rcases selectedWordMask_zero_flags longLong index with h | h
    · left
      rw [h]
      exact mergeSelectedWord_zero_eq old data
    · right
      rw [h]
      exact mergeSelectedWord_allOnes_eq old data
  · right
    rw [selectedWordMask_allOnes_flags longLong index]
    exact mergeSelectedWord_allOnes_eq old data

/-! ## 6b. From the one-line value set to joint safety

The first line's part of `CendTwoLineCommitShape` is dischargeable from two
facts the one-line work already provides: the first line's selections are
whole-word (`resolveMaskSelection_zero_flags` at the zero initial mask file), and
its prepared data words lie in a value set that avoids the target word.  The
composition below is the exact interface; at `cendWitness` the value set is
`cendHalfMixWords` and §5 proves it avoids both target words. -/

/-- With zero flags the selected-word mask at an observed index is `0`. -/
theorem selectedWordMask_zero_flags_lt_two (longLong : Bool) (index : Fin 4)
    (lt : index.val < 2) :
    selectedWordMask (0 : BitVec 4) longLong index = 0 := by
  have h01 : index.val = 0 ∨ index.val = 1 := by omega
  rcases h01 with h | h
  · have hi : index = (⟨0, by decide⟩ : Fin 4) := Fin.ext h
    subst hi
    cases longLong <;> decide
  · have hi : index = (⟨1, by decide⟩ : Fin 4) := Fin.ext h
    subst hi
    cases longLong <;> decide

/-- **Whole-word masks plus a target-free value set give joint safety.** -/
theorem cendCommitsHalfSafe_of_wholeWord_dataSet
    (target : BitVec 32) (dataSet : List (BitVec 32))
    (writes : List PreparedParsedMaskedWrite)
    (whole : ∀ write ∈ writes, write.selection.flags = 0 ∨
      write.selection.flags = BitVec.allOnes 4)
    (dataOk : ∀ write ∈ writes, ∀ i : Fin 4, i.val < 2 → write.data i ∈ dataSet)
    (avoid : ∀ word ∈ dataSet, word ≠ target) :
    CendCommitsHalfSafe target writes := by
  intro write member i hi
  rcases whole write member with h | h
  · have hzero : selectedWordMask write.selection.flags write.selection.longLong i = 0 := by
      rw [h]
      exact selectedWordMask_zero_flags_lt_two write.selection.longLong i hi
    rw [hzero]
    exact cendSelectedHalfSafe_zero target (write.data i)
  · have hall : selectedWordMask write.selection.flags write.selection.longLong i =
        BitVec.allOnes 32 := by
      rw [h]
      exact selectedWordMask_allOnes_flags write.selection.longLong i
    rw [hall]
    exact cendSelectedHalfSafe_allOnes (avoid (write.data i) (dataOk write member i hi))

/-- The first line at `cendWitness` with target-free one-stage half-mix data is
jointly half-safe for the high target word. -/
theorem cendCommitsHalfSafe_cendWitness_high
    (writes : List PreparedParsedMaskedWrite)
    (whole : ∀ write ∈ writes, write.selection.flags = 0 ∨
      write.selection.flags = BitVec.allOnes 4)
    (dataOk : ∀ write ∈ writes, ∀ i : Fin 4, i.val < 2 →
      write.data i ∈ cendHalfMixWords cendWitness) :
    CendCommitsHalfSafe (0x08070605 : BitVec 32) writes :=
  cendCommitsHalfSafe_of_wholeWord_dataSet _ (cendHalfMixWords cendWitness) writes
    whole dataOk cendHalfMixWords_ne_target_high_witness

/-- The dual statement for the low target word. -/
theorem cendCommitsHalfSafe_cendWitness_low
    (writes : List PreparedParsedMaskedWrite)
    (whole : ∀ write ∈ writes, write.selection.flags = 0 ∨
      write.selection.flags = BitVec.allOnes 4)
    (dataOk : ∀ write ∈ writes, ∀ i : Fin 4, i.val < 2 →
      write.data i ∈ cendHalfMixWords cendWitness) :
    CendCommitsHalfSafe (0x04030201 : BitVec 32) writes :=
  cendCommitsHalfSafe_of_wholeWord_dataSet _ (cendHalfMixWords cendWitness) writes
    whole dataOk cendHalfMixWords_ne_target_low_witness

/-! ## 7. The lower bound at three -/

/-- **`CendTwoLinesRefuted` from the one-line residual and the joint shape.** -/
theorem cendTwoLinesRefuted_of_commitShape (peLines : CendPELinesRefuted)
    (shape : CendTwoLineCommitShape) : CendTwoLinesRefuted :=
  cendTwoLinesRefuted_of_liveSecondLines peLines
    (cendTwoLiveSecondLinesRefuted_of_commitShape shape)

/-- **`LowerBound cendSealedMachine cendSpec 3`** from the one-line residual and
the joint shape. -/
theorem cendLowerBound_three_of_commitShape (peLines : CendPELinesRefuted)
    (shape : CendTwoLineCommitShape) :
    ProofsLean.LowerBound cendSealedMachine cendSpec 3 :=
  cendLowerBound_three_of_liveSecondLines peLines
    (cendTwoLiveSecondLinesRefuted_of_commitShape shape)

/-- **`Optimal` for the official three-line answer** from the one-line residual,
the joint shape, and the answer's Lean correctness and word count. -/
theorem cendOptimal_of_commitShape (peLines : CendPELinesRefuted)
    (shape : CendTwoLineCommitShape)
    (answer : ProofsLean.Program cendSealedMachine)
    (correct : ProofsLean.Correct cendSealedMachine cendSpec answer)
    (lengthThree : answer.length = 3)
    (unitCost : ∀ line ∈ answer, cendSealedMachine.lineCost line = 1) :
    ProofsLean.Optimal cendSealedMachine cendSpec answer :=
  cendOptimal_of_liveSecondLines peLines
    (cendTwoLiveSecondLinesRefuted_of_commitShape shape) answer correct lengthThree unitCost

/-! ## 8. Trust report -/

#print axioms mergeSelectedWord_ne_target_of_selectedHalfSafe
#print axioms commitParsedMaskedWrites_lm1_ne_target_of_selectedHalfSafe
#print axioms cendTwoCommitChains_ne_target
#print axioms cendTwoLiveSecondLinesRefuted_of_commitShape
#print axioms cendDatapathWords_cendWitness_targetHalves_avoid
#print axioms cendHalfMixWords_ne_target_high_witness
#print axioms cendInitialMaskSelection_flags
#print axioms selectedWordMask_zero_flags_lt_two
#print axioms cendCommitsHalfSafe_of_wholeWord_dataSet
#print axioms cendCommitsHalfSafe_cendWitness_high
#print axioms mergeSelectedWord_of_wholeWordFlags
#print axioms cendLowerBound_three_of_commitShape


end ProofsLean.MNCore
