import ProofsLean.CendHalfMix

/-! # `12.convert-endian`: the LM1 commit preserves the half-mix value set

`commitParsedMaskedWrites` folds the prepared writes into the pre-line register
files.  This module proves the value half of the commit step for the two observed
LM1 words (addresses `0` and `1`):

* `distance_lm1_lt_two` — an aligned LM1 write that covers word `0` or `1` has
  `distance < 2`; the alignment modulo the access width rules out the
  wrap-around offsets `2` and `3`;
* `commitParsedMaskedWrites_lm1_halfMix` — if every write's first two data words
  are datapath words, and every LM1 destination is aligned, then the committed
  word at address `0`/`1` stays in the half-mix set `cendHalfMixWords`.

The proof is an induction over the write list with the invariant
`files.lm1 target ∈ cendHalfMixWords x`.  The only case that changes the word is
a covering `.lm1` write, where `writeWordsMasked_at` reduces the commit to
`mergeSelectedWord` with one of the four half masks
(`selectedWordMask_lt_two_cases`) and `mergeSelectedWord_halfMix_mem` closes it.

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

/-- **An aligned covering LM1 write has data index below two.**  `count .lm1 w`
is `1`, `2` or `4`; the aligned start and `target < 2` rule out the wrap-around
distances `2` and `3`. -/
theorem distance_lm1_lt_two (width : PEMemory.Width)
    (address target : Fin Bank.lm1.capacity)
    (aligned : address.val % PEMemory.count Bank.lm1 width = 0)
    (within : PEMemory.distance Bank.lm1 address target <
      PEMemory.count Bank.lm1 width)
    (targetLt : target.val < 2) :
    PEMemory.distance Bank.lm1 address target < 2 := by
  have hdist : PEMemory.distance Bank.lm1 address target =
      (target.val + 4096 - address.val) % 4096 := rfl
  rw [hdist] at within ⊢
  have hs : address.val < 4096 := address.isLt
  cases width with
  | word =>
      have hc : PEMemory.count Bank.lm1 PEMemory.Width.word = 1 := rfl
      rw [hc] at within
      omega
  | long =>
      have hc : PEMemory.count Bank.lm1 PEMemory.Width.long = 2 := rfl
      rw [hc] at within
      have hal : address.val % 2 = 0 := by simpa [hc] using aligned
      omega
  | double =>
      have hc : PEMemory.count Bank.lm1 PEMemory.Width.double = 4 := rfl
      rw [hc] at within
      have hal : address.val % 4 = 0 := by simpa [hc] using aligned
      omega

/-- **The commit preserves the half-mix value set at word `0`/`1`.** -/
theorem commitParsedMaskedWrites_lm1_halfMix
    (x : BitVec 64) (writes : List PreparedParsedMaskedWrite)
    (target : Fin Bank.lm1.capacity) (targetLt : target.val < 2)
    (dataOk : ∀ write ∈ writes, ∀ i : Fin 4, i.val < 2 →
      write.data i ∈ cendDataWords x)
    (destAligned : ∀ write ∈ writes, ∀ (width : PEMemory.Width)
      (address : Fin Bank.lm1.capacity),
      write.destination = some ⟨Bank.lm1, width, address⟩ →
        address.val % PEMemory.count Bank.lm1 width = 0) :
    ∀ files : IntegerRegisterFiles, files.lm1 target ∈ cendHalfMixWords x →
      (commitParsedMaskedWrites files writes).lm1 target ∈ cendHalfMixWords x := by
  induction writes with
  | nil =>
      intro files hold
      simpa [commitParsedMaskedWrites] using hold
  | cons write rest ih =>
      intro files hold
      rw [commitParsedMaskedWrites_cons]
      apply ih
      · intro item member i hi
        exact dataOk item (List.mem_cons_of_mem _ member) i hi
      · intro item member width address destination
        exact destAligned item (List.mem_cons_of_mem _ member) width address destination
      · obtain ⟨destination, maskUpdate, data, selection⟩ := write
        cases maskUpdate with
        | some update =>
            show (welcomeCommitStep files
              ⟨destination, some update, data, selection⟩).lm1 target ∈
                cendHalfMixWords x
            simp only [welcomeCommitStep]
            exact hold
        | none =>
            cases destination with
            | none =>
                show (welcomeCommitStep files
                  ⟨none, none, data, selection⟩).lm1 target ∈ cendHalfMixWords x
                simp only [welcomeCommitStep]
                exact hold
            | some access =>
                obtain ⟨bank, width, address⟩ := access
                cases bank with
                | lm1 =>
                    show (welcomeCommitStep files
                      ⟨some ⟨Bank.lm1, width, address⟩, none, data, selection⟩).lm1
                        target ∈ cendHalfMixWords x
                    simp only [welcomeCommitStep]
                    rw [writeDirectAccessMasked_lm1_apply]
                    by_cases within : PEMemory.distance Bank.lm1 address target <
                        PEMemory.count Bank.lm1 width
                    · rw [PEMemory.writeWordsMasked_at _ width files.lm1 address target data
                        selection.flags selection.longLong within]
                      apply mergeSelectedWord_halfMix_mem
                      · exact hold
                      · exact dataOk ⟨some ⟨Bank.lm1, width, address⟩, none, data, selection⟩
                          (by simp) ⟨PEMemory.distance Bank.lm1 address target,
                            Nat.lt_of_lt_of_le within (PEMemory.count_le_four _ _)⟩
                          (distance_lm1_lt_two width address target
                            (destAligned ⟨some ⟨Bank.lm1, width, address⟩, none, data,
                              selection⟩ (by simp) width address rfl) within targetLt)
                      · exact selectedWordMask_lt_two_cases selection.flags
                          selection.longLong ⟨PEMemory.distance Bank.lm1 address target,
                            Nat.lt_of_lt_of_le within (PEMemory.count_le_four _ _)⟩
                          (distance_lm1_lt_two width address target
                            (destAligned ⟨some ⟨Bank.lm1, width, address⟩, none, data,
                              selection⟩ (by simp) width address rfl) within targetLt)
                    · rw [PEMemory.writeWordsMasked_preserves_outside _ width files.lm1 address
                        target data selection.flags selection.longLong
                        (Nat.le_of_not_lt within)]
                      exact hold
                | lm0 =>
                    show (welcomeCommitStep files
                      ⟨some ⟨Bank.lm0, width, address⟩, none, data, selection⟩).lm1
                        target ∈ cendHalfMixWords x
                    simp only [welcomeCommitStep]
                    rw [writeDirectAccessMasked_lm1_eq _ _ _ _ _ _ (by decide)]
                    exact hold
                | grf0 =>
                    show (welcomeCommitStep files
                      ⟨some ⟨Bank.grf0, width, address⟩, none, data, selection⟩).lm1
                        target ∈ cendHalfMixWords x
                    simp only [welcomeCommitStep]
                    rw [writeDirectAccessMasked_lm1_eq _ _ _ _ _ _ (by decide)]
                    exact hold
                | grf1 =>
                    show (welcomeCommitStep files
                      ⟨some ⟨Bank.grf1, width, address⟩, none, data, selection⟩).lm1
                        target ∈ cendHalfMixWords x
                    simp only [welcomeCommitStep]
                    rw [writeDirectAccessMasked_lm1_eq _ _ _ _ _ _ (by decide)]
                    exact hold
                | t =>
                    show (welcomeCommitStep files
                      ⟨some ⟨Bank.t, width, address⟩, none, data, selection⟩).lm1
                        target ∈ cendHalfMixWords x
                    simp only [welcomeCommitStep]
                    rw [writeDirectAccessMasked_lm1_eq _ _ _ _ _ _ (by decide)]
                    exact hold

/-- The initial-state corollary: starting from the zero LM1 bank. -/
theorem commitParsedMaskedWrites_lm1_halfMix_zero
    (x : BitVec 64) (writes : List PreparedParsedMaskedWrite)
    (target : Fin Bank.lm1.capacity) (targetLt : target.val < 2)
    (dataOk : ∀ write ∈ writes, ∀ i : Fin 4, i.val < 2 →
      write.data i ∈ cendDataWords x)
    (destAligned : ∀ write ∈ writes, ∀ (width : PEMemory.Width)
      (address : Fin Bank.lm1.capacity),
      write.destination = some ⟨Bank.lm1, width, address⟩ →
        address.val % PEMemory.count Bank.lm1 width = 0)
    (files : IntegerRegisterFiles) (zero : ∀ address, files.lm1 address = 0) :
    (commitParsedMaskedWrites files writes).lm1 target ∈ cendHalfMixWords x :=
  commitParsedMaskedWrites_lm1_halfMix x writes target targetLt dataOk destAligned
    files (by rw [zero]; exact cendHalfMixWords_zero x)

/-! ## Trust report -/

#print axioms distance_lm1_lt_two
#print axioms commitParsedMaskedWrites_lm1_halfMix

end ProofsLean.MNCore
