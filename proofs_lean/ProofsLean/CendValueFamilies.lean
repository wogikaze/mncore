import ProofsLean.CendMixedRead

/-! # `12.convert-endian`: the value-carrying families, one at a time

`ProofsLean/CendMixedRead.lean` reduced `LowerBound cendSealedMachine cendSpec 2`
to `CendMixedReadResidual`: every `.pe` line with at least one PE-register
writer outside the closed classes (plain ALU, `.matrixRead`, the inert rows and
the L1BM broadcast).  The remaining writers are the six value families of the
executor: plain ALU (already discharged unconditionally by
`CendCycleClose`), float MAU, float relu, `msl`/`msr`, matrix MAU and block
float.

This module closes the **`msl`/`msr` family**.  The key observation is the
executor's own value equation (`WholeMachineStep.mslMsrOutputBus`):

```
mslMsrOutputBus source = ⟨source.high, 0⟩
```

so the words an `msl`/`msr` row hands to its destinations are the two 32-bit
halves of the high word of *one* integer-bus read.  At the `12.convert-endian`
initial state every such read is one of a finite family
(`CendLm1Obligation.cendMemoryBus_rounded_mem` / `cendFixedBus_mem`), and the
flush can only zero 16-bit halves.  Hence the data words live in a finite list
of 32-bit words, and the masked commit can only recombine their 16-bit halves.

## What is proved here

* §1 — the **half-mix closure** `cendMixWords L` of an arbitrary word list, its
  merge closure under the four selected-word masks, and the **generic commit
  preservation** `commitParsedMaskedWrites_lm1_mixWords`: if every write's first
  two data words lie in the closure, the committed LM1 word does too.
* §2 — the **flush lemma**: flushing a bus with an arbitrary flag vector only
  zeroes 16-bit halves of its high word, so the two observed data words stay in
  the closure of the halves.
* §3 — the concrete value list `cendMslWords` of the `msl`/`msr` family at
  `cendWitness`, and the kernel check that the target high word
  `0x08070605` is not in its closure.
* §4 — the **source provenance** of an `msl`/`msr` read at the observed PE: the
  read happens at `mslMsrSourcePE cendPE isMsl` (`⟨3⟩` or `⟨1⟩`), and every
  bus it can return is either one of the ten buses of `cendInitialBuses` or the
  `.fixed` long lane of one of `{0, 1, 3, 2 ^ 63}`.
* §5 — the **data theorem for the `msl`/`msr` stage**: every prepared write the
  stage commits at the observed PE carries its first two data words in the
  closure, and the destination fold/cycle fold/PE walk/stage all keep the
  commit equation.
* §6 — the **line theorem** `cendPE_mslMsrLines_not_correct`: a line whose rows
  are all `.matrixRead`/`.noforward`/extended-inert rows or `msl`/`msr` rows is
  refuted at `cendWitness`.  The integer stage of such a line prepares a
  zero-data list, the `msl`/`msr` stage commits family-data writes, and the
  remaining stages frame the observed PE (`nextMsl = nextRelu = nextBlockFloat`,
  the matrix-MAU stage frames, the shared-block stage frames, the L1BM-to-PE
  stage is empty).
* §7 — the narrowed residual `CendMslMsrResidual`, the exact split
  `cendMixedReadResidual_iff_mslMsrResidual`, and the reductions
  `cendMixedReadResidual_of_mslMsrResidual`,
  `cendPENonClosedRefuted_of_mslMsrResidual` and
  `cendLowerBound_two_of_mslMsrResidual` to `LowerBound cendSealedMachine
  cendSpec 2`.
* §8 — a concrete line (`[.matrixRead, .msl]`) that is in the new class, so the
  narrowing is not vacuous.

## What is *not* closed here

The class `cendMslMsrRow` deliberately excludes **L1BM-to-PE broadcast rows**
(`.pbcast`, `.mbcast`, `.m4bcast`, `.distrib`): a line that combines an `msl`/`msr`
row with a broadcast row is *not* covered, because the broadcast stage commits
its own (zero-bus, hence zero-data) write list and a data-carrying version of
`executeParsedL1ToPEProducers_commit` is not carried out here.  That is the one
remaining *mixture* with an `msl`/`msr` row; lines all of whose value rows are
`.matrixRead`/`.noforward`/inert/`msl`-`msr` rows are closed unconditionally.
The other three value families of the task (float relu, block float, matrix
MAU), float MAU and the plain-ALU rows mixed with value rows are untouched and
remain in `CendMslMsrResidual`.

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

/-! ## 1. The half-mix closure of an arbitrary word list

`CendHalfMix.cendHalfMixWords x` is the closure of the concrete data-word list
`cendDataWords x` of the plain family.  The `msl`/`msr` family reads a different
(also finite) word list, so the same algebra is proved once for an arbitrary
list `L` of 32-bit words.  A committed word is built from the 16-bit halves of
two list members, and the four selected-word masks only ever replace one 16-bit
half. -/

/-- **Every 32-bit word whose two 16-bit halves come from `L`.**  This is
`cendHalfMixWords` with an arbitrary generating list. -/
def cendMixWords (L : List (BitVec 32)) : List (BitVec 32) :=
  L.flatMap fun hi => L.map fun lo => cendHalfMix hi lo

theorem cendMixWords_mem {L : List (BitVec 32)} {hi lo : BitVec 32}
    (hhi : hi ∈ L) (hlo : lo ∈ L) : cendHalfMix hi lo ∈ cendMixWords L :=
  List.mem_flatMap.mpr ⟨hi, hhi, List.mem_map.mpr ⟨lo, hlo, rfl⟩⟩

theorem cendMixWords_exists {L : List (BitVec 32)} {word : BitVec 32}
    (member : word ∈ cendMixWords L) :
    ∃ hi ∈ L, ∃ lo ∈ L, word = cendHalfMix hi lo := by
  obtain ⟨hi, hhi, hmap⟩ := List.mem_flatMap.mp member
  obtain ⟨lo, hlo, rfl⟩ := List.mem_map.mp hmap
  exact ⟨hi, hhi, lo, hlo, rfl⟩

theorem cendMixWords_zero {L : List (BitVec 32)} (zero : (0 : BitVec 32) ∈ L) :
    (0 : BitVec 32) ∈ cendMixWords L := by
  have member := cendMixWords_mem zero zero
  rwa [cendHalfMix_zero_zero] at member

theorem cendMixWords_of_mem {L : List (BitVec 32)} {w : BitVec 32} (member : w ∈ L) :
    w ∈ cendMixWords L := by
  rw [← cendHalfMix_self w]
  exact cendMixWords_mem member member

/-- **The merge of a closure member with a closure member stays in the
closure.**  `selectedWordMask` is one of the four half masks at the two observed
data-word indices, and each of them keeps one 16-bit half of the old word and
one of the data word. -/
theorem mergeSelectedWord_mixWords_mem {L : List (BitVec 32)} (old data mask : BitVec 32)
    (hold : old ∈ cendMixWords L) (hdata : data ∈ cendMixWords L)
    (hmask : mask = 0 ∨ mask = BitVec.allOnes 32 ∨
      mask = 0xffff0000 ∨ mask = 0x0000ffff) :
    mergeSelectedWord old data mask ∈ cendMixWords L := by
  obtain ⟨hi, hhi, lo, hlo, rfl⟩ := cendMixWords_exists hold
  obtain ⟨mid, hmid, low, hlow, rfl⟩ := cendMixWords_exists hdata
  have hOldHigh : cendHalfMix hi lo &&& 0xffff0000 = hi &&& 0xffff0000 :=
    cendHalfMix_high hi lo
  have hOldLow : cendHalfMix hi lo &&& 0x0000ffff = lo &&& 0x0000ffff :=
    cendHalfMix_low hi lo
  have hDataHigh : cendHalfMix mid low &&& 0xffff0000 = mid &&& 0xffff0000 :=
    cendHalfMix_high mid low
  have hDataLow : cendHalfMix mid low &&& 0x0000ffff = low &&& 0x0000ffff :=
    cendHalfMix_low mid low
  rcases hmask with rfl | rfl | rfl | rfl
  · rw [show mergeSelectedWord (cendHalfMix hi lo) (cendHalfMix mid low) 0 =
        cendHalfMix hi lo from by
      unfold mergeSelectedWord
      rw [show ~~~(0 : BitVec 32) = BitVec.allOnes 32 from by decide]
      rw [show cendHalfMix hi lo &&& (BitVec.allOnes 32) = cendHalfMix hi lo from
        BitVec.and_allOnes]
      rw [show cendHalfMix mid low &&& (0 : BitVec 32) = 0 from BitVec.and_zero]
      rw [show (cendHalfMix hi lo) ||| (0 : BitVec 32) = cendHalfMix hi lo from BitVec.or_zero]]
    exact cendMixWords_mem hhi hlo
  · rw [show mergeSelectedWord (cendHalfMix hi lo) (cendHalfMix mid low)
        (BitVec.allOnes 32) = cendHalfMix mid low from by
      unfold mergeSelectedWord
      rw [show ~~~(BitVec.allOnes 32 : BitVec 32) = 0 from by decide]
      rw [show cendHalfMix hi lo &&& (0 : BitVec 32) = 0 from BitVec.and_zero]
      rw [show cendHalfMix mid low &&& (BitVec.allOnes 32) = cendHalfMix mid low from
        BitVec.and_allOnes]
      rw [show (0 : BitVec 32) ||| cendHalfMix mid low = cendHalfMix mid low from
        BitVec.zero_or]]
    exact cendMixWords_mem hmid hlow
  · rw [show mergeSelectedWord (cendHalfMix hi lo) (cendHalfMix mid low) 0xffff0000 =
        cendHalfMix mid lo from by
      unfold mergeSelectedWord
      rw [show ~~~(0xffff0000 : BitVec 32) = 0x0000ffff from by decide,
        hOldLow, hDataHigh]
      exact BitVec.or_comm _ _]
    exact cendMixWords_mem hmid hlo
  · rw [show mergeSelectedWord (cendHalfMix hi lo) (cendHalfMix mid low) 0x0000ffff =
        cendHalfMix hi low from by
      unfold mergeSelectedWord
      rw [show ~~~(0x0000ffff : BitVec 32) = 0xffff0000 from by decide,
        hOldHigh, hDataLow]
      rfl]
    exact cendMixWords_mem hhi hlow

/-- **The commit preserves the closure at word `0`/`1`.**  Copy of
`CendCommitMix.commitParsedMaskedWrites_lm1_halfMix` with the data words taken
from an arbitrary generating list. -/
theorem commitParsedMaskedWrites_lm1_mixWords {L : List (BitVec 32)}
    (writes : List PreparedParsedMaskedWrite)
    (target : Fin Bank.lm1.capacity) (targetLt : target.val < 2)
    (dataOk : ∀ write ∈ writes, ∀ i : Fin 4, i.val < 2 → write.data i ∈ cendMixWords L)
    (destAligned : ∀ write ∈ writes, ∀ (width : PEMemory.Width)
      (address : Fin Bank.lm1.capacity),
      write.destination = some ⟨Bank.lm1, width, address⟩ →
        address.val % PEMemory.count Bank.lm1 width = 0) :
    ∀ files : IntegerRegisterFiles, files.lm1 target ∈ cendMixWords L →
      (commitParsedMaskedWrites files writes).lm1 target ∈ cendMixWords L := by
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
                cendMixWords L
            simp only [welcomeCommitStep]
            exact hold
        | none =>
            cases destination with
            | none =>
                show (welcomeCommitStep files
                  ⟨none, none, data, selection⟩).lm1 target ∈ cendMixWords L
                simp only [welcomeCommitStep]
                exact hold
            | some access =>
                obtain ⟨bank, width, address⟩ := access
                cases bank with
                | lm1 =>
                    show (welcomeCommitStep files
                      ⟨some ⟨Bank.lm1, width, address⟩, none, data, selection⟩).lm1
                        target ∈ cendMixWords L
                    simp only [welcomeCommitStep]
                    rw [writeDirectAccessMasked_lm1_apply]
                    by_cases within : PEMemory.distance Bank.lm1 address target <
                        PEMemory.count Bank.lm1 width
                    · rw [PEMemory.writeWordsMasked_at _ width files.lm1 address target data
                        selection.flags selection.longLong within]
                      apply mergeSelectedWord_mixWords_mem
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
                        target ∈ cendMixWords L
                    simp only [welcomeCommitStep]
                    rw [writeDirectAccessMasked_lm1_eq _ _ _ _ _ _ (by decide)]
                    exact hold
                | grf0 =>
                    show (welcomeCommitStep files
                      ⟨some ⟨Bank.grf0, width, address⟩, none, data, selection⟩).lm1
                        target ∈ cendMixWords L
                    simp only [welcomeCommitStep]
                    rw [writeDirectAccessMasked_lm1_eq _ _ _ _ _ _ (by decide)]
                    exact hold
                | grf1 =>
                    show (welcomeCommitStep files
                      ⟨some ⟨Bank.grf1, width, address⟩, none, data, selection⟩).lm1
                        target ∈ cendMixWords L
                    simp only [welcomeCommitStep]
                    rw [writeDirectAccessMasked_lm1_eq _ _ _ _ _ _ (by decide)]
                    exact hold
                | t =>
                    show (welcomeCommitStep files
                      ⟨some ⟨Bank.t, width, address⟩, none, data, selection⟩).lm1
                        target ∈ cendMixWords L
                    simp only [welcomeCommitStep]
                    rw [writeDirectAccessMasked_lm1_eq _ _ _ _ _ _ (by decide)]
                    exact hold

/-! ## 2. Flushing only zeroes 16-bit halves

`parsedOutputAfterFlush` wraps a bus in `Masks.flushBus`, which ANDs the high
word with `halfMask` (long) or `doubleMask` (double).  Both masks are unions of
16-bit (resp. 32-bit) chunks, so at the two observed data-word indices the mask
is one of `0`, `0xffff`, `0xffff0000` or `0xffffffff`: each 16-bit half of the
data word is either kept or zeroed.  That is exactly membership in the half-mix
closure of the original words' halves. -/

theorem cendWriteEnable_high_cases (width : Masks.Width) (flags : BitVec 4) :
    (Masks.writeEnable width flags).high.extractLsb' 32 32 ∈
        ([0, 0xffff, 0xffff0000, BitVec.allOnes 32] : List (BitVec 32)) ∧
      (Masks.writeEnable width flags).high.extractLsb' 0 32 ∈
        ([0, 0xffff, 0xffff0000, BitVec.allOnes 32] : List (BitVec 32)) := by
  cases width <;> revert flags <;> decide

theorem cendAndMask_mixWords {L : List (BitVec 32)} {w : BitVec 32} (hw : w ∈ L)
    (hz : (0 : BitVec 32) ∈ L) {mask : BitVec 32}
    (hmask : mask ∈ ([0, 0xffff, 0xffff0000, BitVec.allOnes 32] : List (BitVec 32))) :
    w &&& mask ∈ cendMixWords L := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmask
  rcases hmask with rfl | rfl | rfl | rfl
  · rw [show w &&& (0 : BitVec 32) = cendHalfMix 0 0 from by
      rw [cendHalfMix_zero_zero]
      simp]
    exact cendMixWords_mem hz hz
  · rw [show w &&& (0xffff : BitVec 32) = cendHalfMix 0 w from by
      unfold cendHalfMix
      simp]
    exact cendMixWords_mem hz hw
  · rw [show w &&& (0xffff0000 : BitVec 32) = cendHalfMix w 0 from by
      unfold cendHalfMix
      simp]
    exact cendMixWords_mem hw hz
  · rw [show w &&& BitVec.allOnes 32 = cendHalfMix w w from by
      rw [cendHalfMix_self, BitVec.and_allOnes]]
    exact cendMixWords_mem hw hw

theorem cendFlushEnable_high (width : Masks.Width) (flags : BitVec 4) (b : IntegerALU.Bus) :
    (Masks.flushBus width flags b).high = b.high &&& (Masks.writeEnable width flags).high := by
  cases width <;> rfl

/-- **Flushing a bus only zeroes 16-bit halves of its high word.** -/
theorem cendFlush_data_mixWords {L : List (BitVec 32)} {b : IntegerALU.Bus}
    (h0 : b.high.extractLsb' 32 32 ∈ L) (h1 : b.high.extractLsb' 0 32 ∈ L)
    (hz : (0 : BitVec 32) ∈ L)
    (width : Masks.Width) (flags : BitVec 4) :
    ∀ (i : Fin 4), i.val < 2 →
      unpackALUBus (Masks.flushBus width flags b) i ∈ cendMixWords L := by
  intro i hi
  obtain ⟨hc0, hc1⟩ := cendWriteEnable_high_cases width flags
  have hshape := cendFlushEnable_high width flags b
  have hi01 : i.val = 0 ∨ i.val = 1 := by omega
  rcases hi01 with h | h
  · have hindex : i = (⟨0, by decide⟩ : Fin 4) := Fin.ext h
    subst hindex
    show (Masks.flushBus width flags b).high.extractLsb' 32 32 ∈ cendMixWords L
    rw [hshape, BitVec.extractLsb'_and]
    exact cendAndMask_mixWords h0 hz hc0
  · have hindex : i = (⟨1, by decide⟩ : Fin 4) := Fin.ext h
    subst hindex
    show (Masks.flushBus width flags b).high.extractLsb' 0 32 ∈ cendMixWords L
    rw [hshape, BitVec.extractLsb'_and]
    exact cendAndMask_mixWords h1 hz hc1

/-- The same for the executor's `parsedOutputAfterFlush` wrapper. -/
theorem cendOutputAfterFlush_data_mixWords {L : List (BitVec 32)} {b : IntegerALU.Bus}
    (h0 : b.high.extractLsb' 32 32 ∈ L) (h1 : b.high.extractLsb' 0 32 ∈ L)
    (hz : (0 : BitVec 32) ∈ L) (selection : Option PEWordSelection) :
    ∀ (i : Fin 4), i.val < 2 →
      unpackALUBus (parsedOutputAfterFlush selection b) i ∈ cendMixWords L := by
  intro i hi
  have hi01 : i.val = 0 ∨ i.val = 1 := by omega
  cases selection with
  | none =>
      rcases hi01 with h | h
      · have hindex : i = (⟨0, by decide⟩ : Fin 4) := Fin.ext h
        subst hindex
        simpa [parsedOutputAfterFlush, unpackALUBus] using cendMixWords_of_mem h0
      · have hindex : i = (⟨1, by decide⟩ : Fin 4) := Fin.ext h
        subst hindex
        simpa [parsedOutputAfterFlush, unpackALUBus] using cendMixWords_of_mem h1
  | some selected =>
      exact cendFlush_data_mixWords h0 h1 hz (if selected.longLong then Masks.Width.double
        else Masks.Width.long) selected.flags i hi

/-! ## 3. The `msl`/`msr` value list at the witness -/

/-- The two 32-bit halves of a bus's high word. -/
def cendBusHalves (bus : IntegerALU.Bus) : List (BitVec 32) :=
  [bus.high.extractLsb' 32 32, bus.high.extractLsb' 0 32]

/-- The `.fixed` long lanes an `msl`/`msr` source can read.  The source is read
at `mslMsrSourcePE cendPE isMsl`, which is `⟨3⟩` (MSL) or `⟨1⟩` (MSR); at
`ParsedIntegerContext.ofLinearIndex` those carry `$l2bid = $l1bid = $mabid =
0`, `$peid ∈ {1, 3}`, `$subpeid ∈ {1, 3}` and `$msb1 = 2 ^ 63`. -/
def cendMslFixedWords : List (BitVec 32) := [0, 1, 3, 0x80000000]

/-- **The generating list of the `msl`/`msr` family at `cendWitness`**: the four
fixed lanes plus the halves of every bus of the ten-bus initial family. -/
def cendMslWords : List (BitVec 32) :=
  cendMslFixedWords ++ (cendInitialBuses cendWitness).flatMap cendBusHalves

theorem cendMslWords_zero : (0 : BitVec 32) ∈ cendMslWords :=
  List.mem_append_left _ (by simp [cendMslFixedWords])

theorem cendInitialBus_halves_mem (bus : IntegerALU.Bus)
    (member : bus ∈ cendInitialBuses cendWitness) :
    bus.high.extractLsb' 32 32 ∈ cendMslWords ∧
      bus.high.extractLsb' 0 32 ∈ cendMslWords := by
  have h0 : bus.high.extractLsb' 32 32 ∈ (cendInitialBuses cendWitness).flatMap
      cendBusHalves := List.mem_flatMap.mpr ⟨bus, member, by simp [cendBusHalves]⟩
  have h1 : bus.high.extractLsb' 0 32 ∈ (cendInitialBuses cendWitness).flatMap
      cendBusHalves := List.mem_flatMap.mpr ⟨bus, member, by simp [cendBusHalves]⟩
  exact ⟨List.mem_append_right _ h0, List.mem_append_right _ h1⟩

/-- The fixed long lane of the source PE is one of the four fixed words. -/
theorem cendMslFixedBus_halves {v : Nat} (hv : v ∈ [0, 1, 3, 2 ^ 63]) :
    (⟨BitVec.ofNat 64 v, BitVec.ofNat 64 v⟩ : IntegerALU.Bus).high.extractLsb' 32 32 ∈
        cendMslWords ∧
      (⟨BitVec.ofNat 64 v, BitVec.ofNat 64 v⟩ : IntegerALU.Bus).high.extractLsb' 0 32 ∈
        cendMslWords := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl <;> decide

theorem cendWitness_target_high :
    (byteSwap64 cendWitness).extractLsb' 32 32 = 0x08070605 := by decide

theorem cendWitness_target_low :
    (byteSwap64 cendWitness).extractLsb' 0 32 = 0x04030201 := by decide

/-- **The target high word is not a half-mix of the family words.**  The kernel
check runs over the 24-word generating list and its 576 half-mixes. -/
theorem cendMslWords_target_high_avoid :
    (0x08070605 : BitVec 32) ∉ cendMixWords cendMslWords := by
  decide

/-- The target low word is not a half-mix either. -/
theorem cendMslWords_target_low_avoid :
    (0x04030201 : BitVec 32) ∉ cendMixWords cendMslWords := by
  decide

/-! ## 4. Source provenance of an `msl`/`msr` read

The `msl`/`msr` stage of the observed PE reads its single source operand at the
*neighbouring* PE `mslMsrSourcePE cendPE isMsl` (`⟨3⟩` for `msl`, `⟨1⟩` for
`msr`) and with the `.long` lane width.  At the `12.convert-endian` initial
state every PE carries the same register file, so a `.memory` read is one of the
ten buses of `cendInitialBuses` (`cendMemoryBus_rounded_mem`, through the
alignment of the address resolver), a `.fixed` read is the `.long` replication
of a fixed channel value — one of `{0, 1, 3, 2 ^ 63}` at those PEs
(`parsed_fixed_integerValue_ofLinearIndex`) — and a `.forward` read *fails*
because every slot is poison. -/

/-- **A bus whose two high-word halves are family words.** -/
def CendMslBusOk (bus : IntegerALU.Bus) : Prop :=
  bus.high.extractLsb' 32 32 ∈ cendMslWords ∧ bus.high.extractLsb' 0 32 ∈ cendMslWords

/-- **Every successful read of this source lands in the family list.** -/
def CendMslSourceOk (cycle : Fin 4) (input : ParsedIntegerInput) : Prop :=
  ∀ bus, ParsedIntegerInput.readWithForwarding (cendInitialPERegisters cendWitness)
    cendPoisonSlots cycle input = .ok bus → CendMslBusOk bus

theorem cendMslSourceOk_memory (cycle : Fin 4) (access : DirectMemoryAccess) (rounded : Bool)
    (aligned : access.address.val % PEMemory.count access.bank access.width = 0) :
    CendMslSourceOk cycle (.memory access rounded) := by
  intro bus read
  simp only [ParsedIntegerInput.readWithForwarding, ParsedIntegerInput.read,
    StepResult.ok.injEq] at read
  subst read
  simpa [CendMslBusOk, readDirectAccess] using cendInitialBus_halves_mem _
    (cendMemoryBus_rounded_mem cendWitness access.bank access.width access.address rounded aligned)

/-- The fixed long lane of a source-PE context is one of the four family words. -/
theorem cendMslSourcePE_value (isMsl : Bool) (fixed : ParsedFixed) :
    ParsedFixed.integerValue fixed .long
      (ParsedIntegerContext.ofLinearIndex (mslMsrSourcePE cendPE isMsl)).group
      (ParsedIntegerContext.ofLinearIndex (mslMsrSourcePE cendPE isMsl)).l2b
      (ParsedIntegerContext.ofLinearIndex (mslMsrSourcePE cendPE isMsl)).l1b
      (ParsedIntegerContext.ofLinearIndex (mslMsrSourcePE cendPE isMsl)).mab
      (ParsedIntegerContext.ofLinearIndex (mslMsrSourcePE cendPE isMsl)).pe ∈
        [0, 1, 3, 2 ^ 63] := by
  rw [parsed_fixed_integerValue_ofLinearIndex]
  cases isMsl <;> cases fixed <;> decide

theorem cendMslSourceOk_fixed (cycle : Fin 4) (index : Fin 4096) (fixed : ParsedFixed)
    (small : ParsedFixed.integerValue fixed .long
      (ParsedIntegerContext.ofLinearIndex index).group
      (ParsedIntegerContext.ofLinearIndex index).l2b
      (ParsedIntegerContext.ofLinearIndex index).l1b
      (ParsedIntegerContext.ofLinearIndex index).mab
      (ParsedIntegerContext.ofLinearIndex index).pe ∈ [0, 1, 3, 2 ^ 63]) :
    CendMslSourceOk cycle (.fixed (replicateIntegerLane .long
      (ParsedFixed.integerValue fixed .long
        (ParsedIntegerContext.ofLinearIndex index).group
        (ParsedIntegerContext.ofLinearIndex index).l2b
        (ParsedIntegerContext.ofLinearIndex index).l1b
        (ParsedIntegerContext.ofLinearIndex index).mab
        (ParsedIntegerContext.ofLinearIndex index).pe))) := by
  intro bus read
  simp only [ParsedIntegerInput.readWithForwarding, ParsedIntegerInput.read,
    StepResult.ok.injEq] at read
  subst read
  simpa [CendMslBusOk, replicateIntegerLane] using cendMslFixedBus_halves small

theorem cendMslSourceOk_forward (cycle : Fin 4) (kind : ParsedForward) (rounded : Bool) :
    CendMslSourceOk cycle (.forward kind rounded) := by
  intro bus read
  simp [ParsedIntegerInput.readWithForwarding, cendPoisonSlots] at read

/-- **Every source input the `msl`/`msr` lowering produces is a family source.** -/
theorem cendMslSourceOk_toParsedIntegerInput (isMsl : Bool) (operand : ParsedOperand)
    (cycle : Fin 4) (bar0 bar1 : BitVec 12) (tWord : BitVec 32) (input : ParsedIntegerInput)
    (resolved : ParsedOperand.toParsedIntegerInput? operand .long
      (ParsedIntegerContext.ofLinearIndex (mslMsrSourcePE cendPE isMsl)).group
      (ParsedIntegerContext.ofLinearIndex (mslMsrSourcePE cendPE isMsl)).l2b
      (ParsedIntegerContext.ofLinearIndex (mslMsrSourcePE cendPE isMsl)).l1b
      (ParsedIntegerContext.ofLinearIndex (mslMsrSourcePE cendPE isMsl)).mab
      (ParsedIntegerContext.ofLinearIndex (mslMsrSourcePE cendPE isMsl)).pe cycle bar0 bar1 tWord
      = some input) : CendMslSourceOk cycle input := by
  cases operand with
  | fixed fixed =>
      simp only [ParsedOperand.toParsedIntegerInput?, Option.some.injEq] at resolved
      subst resolved
      exact cendMslSourceOk_fixed cycle (mslMsrSourcePE cendPE isMsl) fixed
        (cendMslSourcePE_value isMsl fixed)
  | forward kind negated extended rounded =>
      simp only [ParsedOperand.toParsedIntegerInput?, Option.some.injEq] at resolved
      subst resolved
      exact cendMslSourceOk_forward cycle kind rounded
  | mem access negated extended rounded mask =>
      simp only [ParsedOperand.toParsedIntegerInput?] at resolved
      cases hr : ParsedOperand.toDirectMemoryAccess? (.mem access false false false none)
          (ParsedIntegerContext.ofLinearIndex (mslMsrSourcePE cendPE isMsl)).pe cycle bar0 bar1
          tWord with
      | none => simp [hr] at resolved
      | some resolvedAccess =>
          simp only [hr, Option.map_some, Option.some.injEq] at resolved
          subst resolved
          exact cendMslSourceOk_memory cycle resolvedAccess rounded
            (parsedOperand_toDirectMemoryAccessMode_count_aligned
              (.mem access false false false none) false
              (ParsedIntegerContext.ofLinearIndex (mslMsrSourcePE cendPE isMsl)).pe cycle
              bar0 bar1 tWord resolvedAccess hr)
  | nowrite => simp [ParsedOperand.toParsedIntegerInput?, ParsedOperand.toDirectMemoryAccess?,
    ParsedOperand.toDirectMemoryAccessMode?] at resolved
  | omr entry mask => simp [ParsedOperand.toParsedIntegerInput?, ParsedOperand.toDirectMemoryAccess?,
    ParsedOperand.toDirectMemoryAccessMode?] at resolved
  | bar lm1 width mask => simp [ParsedOperand.toParsedIntegerInput?, ParsedOperand.toDirectMemoryAccess?,
    ParsedOperand.toDirectMemoryAccessMode?] at resolved
  | matrix group width row => simp [ParsedOperand.toParsedIntegerInput?, ParsedOperand.toDirectMemoryAccess?,
    ParsedOperand.toDirectMemoryAccessMode?] at resolved
  | l1bm width address => simp [ParsedOperand.toParsedIntegerInput?, ParsedOperand.toDirectMemoryAccess?,
    ParsedOperand.toDirectMemoryAccessMode?] at resolved
  | l2bm address l2b => simp [ParsedOperand.toParsedIntegerInput?, ParsedOperand.toDirectMemoryAccess?,
    ParsedOperand.toDirectMemoryAccessMode?] at resolved
  | dar address => simp [ParsedOperand.toParsedIntegerInput?, ParsedOperand.toDirectMemoryAccess?,
    ParsedOperand.toDirectMemoryAccessMode?] at resolved

/-! ## 5. The data theorem for the `msl`/`msr` stage -/

/-- **Every prepared write of one `msl`/`msr` destination is the commit of a
single write whose data bus is the row's flushed output and whose `.lm1`
destination is aligned.** -/
theorem writeParsedMslMsrDestination?_dataAligned
    (files : IntegerRegisterFiles) (destination : ParsedOperand)
    (context : ParsedIntegerContext) (output : IntegerALU.Bus) (flags : BitVec 4)
    (cycle : Fin 4) (directive : ParsedMaskDirective) (hasSingleLineMask : Bool)
    (write : ParsedMslMsrDestinationWrite)
    (lowered : writeParsedMslMsrDestination? files destination context output flags cycle
      directive hasSingleLineMask = some write) :
    ∃ prepared : PreparedParsedMaskedWrite,
      write.files = commitParsedMaskedWrites files [prepared] ∧
      prepared.data = unpackALUBus output ∧
      (∀ (width : PEMemory.Width) (address : Fin Bank.lm1.capacity),
        prepared.destination = some ⟨Bank.lm1, width, address⟩ →
          address.val % PEMemory.count Bank.lm1 width = 0) := by
  cases destination with
  | mem access negated extended rounded mask =>
      simp only [writeParsedMslMsrDestination?] at lowered
      cases h : ParsedOperand.toDirectMemoryDestination?
          (.mem access negated extended rounded mask) context.pe cycle context.bar0 context.bar1
          context.tWord with
      | none => simp [h] at lowered
      | some found =>
          cases h2 : ParsedOperand.resolveMemoryWriteSelection?
              (.mem access negated extended rounded mask) found.bank files.maskRegisters cycle
              directive hasSingleLineMask with
          | none => simp [h, h2] at lowered
          | some selection =>
              simp [writeParsedMslMsrDestination?, h, h2] at lowered
              obtain rfl := lowered
              refine ⟨⟨some found, none, unpackALUBus output, selection⟩, ?_, rfl, ?_⟩
              · simp [commitParsedMaskedWrites, writeDirectAccessMasked]
              · intro width address dest
                simp only [Option.some.injEq] at dest
                obtain rfl : found = ⟨Bank.lm1, width, address⟩ := dest
                exact parsedOperand_toDirectMemoryAccessMode_count_aligned _ true context.pe
                  cycle context.bar0 context.bar1 context.tWord _ h
  | omr entry mask =>
      simp only [writeParsedMslMsrDestination?] at lowered
      cases h : ParsedOperand.toMaskRegisterEntry? (.omr entry mask) with
      | none => simp [h] at lowered
      | some found =>
          cases h2 : ParsedOperand.resolveOmrWriteSelection? (.omr entry mask)
              files.maskRegisters cycle directive hasSingleLineMask with
          | none => simp [h, h2] at lowered
          | some selection =>
              simp [writeParsedMslMsrDestination?, h, h2] at lowered
              obtain rfl := lowered
              refine ⟨⟨none, some (found, cycle, flags), unpackALUBus output,
                ⟨selection, false⟩⟩, ?_, rfl, ?_⟩
              · simp [commitParsedMaskedWrites]
              · intro width address dest
                simp at dest
  | bar lm1 width mask =>
      simp only [writeParsedMslMsrDestination?] at lowered
      cases h : ParsedOperand.resolveMemoryWriteSelection? (ParsedOperand.bar lm1 width mask)
          (if lm1 = true then Bank.lm1 else Bank.lm0) files.maskRegisters cycle directive
          hasSingleLineMask with
      | none => simp [h] at lowered
      | some selection =>
          simp [writeParsedMslMsrDestination?, h] at lowered
          obtain rfl := lowered
          refine ⟨⟨none, none, unpackALUBus output, selection⟩, ?_, rfl, ?_⟩
          · simp [commitParsedMaskedWrites]
          · intro width address dest
            simp at dest
  | nowrite =>
      simp only [writeParsedMslMsrDestination?] at lowered
      obtain rfl := Option.some.inj lowered
      refine ⟨⟨none, none, unpackALUBus output, ⟨0, false⟩⟩, ?_, rfl, ?_⟩
      · simp [commitParsedMaskedWrites]
      · intro width address dest
        simp at dest
  | forward kind negated extended rounded => simp [writeParsedMslMsrDestination?] at lowered
  | fixed value => simp [writeParsedMslMsrDestination?] at lowered
  | matrix group width row => simp [writeParsedMslMsrDestination?] at lowered
  | l1bm width address => simp [writeParsedMslMsrDestination?] at lowered
  | l2bm address l2b => simp [writeParsedMslMsrDestination?] at lowered
  | dar address => simp [writeParsedMslMsrDestination?] at lowered

/-- **The `msl`/`msr` destination fold keeps the commit equation, the data
membership and the alignment.** -/
theorem executeParsedMslMsrAtPE_writeDestinations_data
    (currentState : State) (hasSingleLineMask : Bool) (context : ParsedIntegerContext)
    (cycle : Fin 4) (output : IntegerALU.Bus)
    (dataOk : ∀ i : Fin 4, i.val < 2 → (unpackALUBus output) i ∈ cendMixWords cendMslWords) :
    ∀ (destinations : List ParsedOperand) (files : IntegerRegisterFiles) (bar0 bar1 : BitVec 12)
      (nextFiles : IntegerRegisterFiles) (nextBar0 nextBar1 : BitVec 12),
      executeParsedMslMsrAtPE.runCycles.writeDestinations currentState hasSingleLineMask context
        cycle output destinations files bar0 bar1 = some (nextFiles, nextBar0, nextBar1) →
      ∃ writes : List PreparedParsedMaskedWrite,
        nextFiles = commitParsedMaskedWrites files writes ∧
        (∀ write ∈ writes, ∀ i : Fin 4, i.val < 2 →
          write.data i ∈ cendMixWords cendMslWords) ∧
        (∀ write ∈ writes, ∀ (width : PEMemory.Width) (address : Fin Bank.lm1.capacity),
          write.destination = some ⟨Bank.lm1, width, address⟩ →
            address.val % PEMemory.count Bank.lm1 width = 0) := by
  intro destinations
  induction destinations with
  | nil =>
      intro files bar0 bar1 nextFiles nextBar0 nextBar1 executed
      rw [executeParsedMslMsrAtPE.runCycles.writeDestinations] at executed
      obtain ⟨rfl, rfl, rfl⟩ := Option.some.inj executed
      exact ⟨[], rfl, by intro write member; simp at member,
        by intro write member; simp at member⟩
  | cons destination rest ih =>
      intro files bar0 bar1 nextFiles nextBar0 nextBar1 executed
      rw [executeParsedMslMsrAtPE.runCycles.writeDestinations] at executed
      cases lowered : writeParsedMslMsrDestination? files destination
          { context with cycle := cycle, bar0 := bar0, bar1 := bar1 } output 0 cycle
          currentState.maskDirective hasSingleLineMask with
      | none =>
          rw [lowered] at executed
          simp at executed
      | some write =>
          rw [lowered] at executed
          obtain ⟨prepared, committed, dataEq, aligned⟩ :=
            writeParsedMslMsrDestination?_dataAligned files destination
              { context with cycle := cycle, bar0 := bar0, bar1 := bar1 } output 0 cycle
              currentState.maskDirective hasSingleLineMask write lowered
          obtain ⟨restWrites, restCommit, restData, restAligned⟩ :=
            ih write.files _ _ nextFiles _ _ executed
          refine ⟨prepared :: restWrites, ?_, ?_, ?_⟩
          · rw [restCommit, committed,
              show (prepared :: restWrites) = [prepared] ++ restWrites from rfl,
              commitParsedMaskedWrites_append]
          · intro item member i hi
            rcases List.mem_cons.mp member with rfl | later
            · rw [dataEq]; exact dataOk i hi
            · exact restData item later i hi
          · intro item member width address dest
            rcases List.mem_cons.mp member with rfl | later
            · exact aligned width address dest
            · exact restAligned item later width address dest

/-- **The four-cycle fold of the `msl`/`msr` row keeps the data membership.** -/
theorem executeParsedMslMsrAtPE_runCycles_data
    (readState currentState : State) (expression : ParsedExpr) (hasSingleLineMask : Bool)
    (context : ParsedIntegerContext) (destinations : List ParsedOperand) (sourcePE : PEId)
    (sourceAt : Fin 4 → Option ParsedIntegerInput)
    (sourceReadOk : ∀ (cycle : Fin 4) (bus : IntegerALU.Bus),
      (match sourceAt cycle with
        | some source => ParsedIntegerInput.readWithForwarding (readState.peRegisters sourcePE)
            (stateForwardingSlots readState sourcePE) cycle source
        | none => .unknown) = .ok bus → CendMslBusOk bus) :
    ∀ (cycles : List (Fin 4)) (files : IntegerRegisterFiles) (bar0 bar1 : BitVec 12)
      (outputs : Fin 4 → IntegerALU.Bus) (nextFiles : IntegerRegisterFiles)
      (nextBar0 nextBar1 : BitVec 12) (nextOutputs : Fin 4 → IntegerALU.Bus),
      executeParsedMslMsrAtPE.runCycles readState currentState expression hasSingleLineMask
        context destinations sourcePE sourceAt cycles files bar0 bar1 outputs =
        .ok (nextFiles, nextBar0, nextBar1, nextOutputs) →
      ∃ writes : List PreparedParsedMaskedWrite,
        nextFiles = commitParsedMaskedWrites files writes ∧
        (∀ write ∈ writes, ∀ i : Fin 4, i.val < 2 →
          write.data i ∈ cendMixWords cendMslWords) ∧
        (∀ write ∈ writes, ∀ (width : PEMemory.Width) (address : Fin Bank.lm1.capacity),
          write.destination = some ⟨Bank.lm1, width, address⟩ →
            address.val % PEMemory.count Bank.lm1 width = 0) := by
  intro cycles
  induction cycles with
  | nil =>
      intro files bar0 bar1 outputs nextFiles nextBar0 nextBar1 nextOutputs executed
      rw [executeParsedMslMsrAtPE.runCycles] at executed
      obtain ⟨rfl, rfl, rfl, rfl⟩ := StepResult.ok.inj executed
      exact ⟨[], rfl, by intro write member; simp at member,
        by intro write member; simp at member⟩
  | cons cycle rest ih =>
      intro files bar0 bar1 outputs nextFiles nextBar0 nextBar1 nextOutputs executed
      rw [executeParsedMslMsrAtPE.runCycles] at executed
      dsimp only at executed
      cases source : sourceAt cycle with
      | none =>
          rw [source] at executed
          simp at executed
      | some value =>
          rw [source] at executed
          dsimp only at executed
          cases read : ParsedIntegerInput.readWithForwarding (readState.peRegisters sourcePE)
              (stateForwardingSlots readState sourcePE) cycle value with
          | failure =>
              rw [read] at executed
              simp at executed
          | unknown =>
              rw [read] at executed
              simp at executed
          | ok sourceBus =>
              rw [read] at executed
              dsimp only at executed
              cases flush : resolveFlushSelection? expression.flush files.maskRegisters cycle with
              | none =>
                  rw [flush] at executed
                  simp at executed
              | some flushSelection =>
                  rw [flush] at executed
                  dsimp only at executed
                  obtain ⟨busOkHigh, busOkLow⟩ := sourceReadOk cycle sourceBus (by
                    rw [source]; exact read)
                  have dataOk : ∀ i : Fin 4, i.val < 2 →
                      (unpackALUBus (parsedOutputAfterFlush flushSelection
                        (mslMsrOutputBus sourceBus))) i ∈ cendMixWords cendMslWords := by
                    intro i hi
                    apply cendOutputAfterFlush_data_mixWords
                    · simpa [mslMsrOutputBus] using busOkHigh
                    · simpa [mslMsrOutputBus] using busOkLow
                    · exact cendMslWords_zero
                    · exact hi
                  cases wrote : executeParsedMslMsrAtPE.runCycles.writeDestinations currentState
                      hasSingleLineMask context cycle (parsedOutputAfterFlush flushSelection
                        (mslMsrOutputBus sourceBus)) destinations files bar0 bar1 with
                  | none =>
                      rw [wrote] at executed
                      dsimp only at executed
                      simp at executed
                  | some result =>
                      rw [wrote] at executed
                      dsimp only at executed
                      obtain ⟨middleFiles, middleBar0, middleBar1⟩ := result
                      obtain ⟨headWrites, headCommit, headData, headAligned⟩ :=
                        executeParsedMslMsrAtPE_writeDestinations_data currentState
                          hasSingleLineMask context cycle (parsedOutputAfterFlush flushSelection
                            (mslMsrOutputBus sourceBus)) dataOk destinations
                          files bar0 bar1 middleFiles middleBar0 middleBar1 wrote
                      obtain ⟨tailWrites, tailCommit, tailData, tailAligned⟩ :=
                        ih middleFiles middleBar0 middleBar1 _ nextFiles nextBar0 nextBar1
                          nextOutputs executed
                      exact ⟨headWrites ++ tailWrites, by
                          rw [tailCommit, headCommit, commitParsedMaskedWrites_append],
                        by
                          intro item member i hi
                          rcases List.mem_append.mp member with head | tail
                          · exact headData item head i hi
                          · exact tailData item tail i hi,
                        by
                          intro item member width address dest
                          rcases List.mem_append.mp member with head | tail
                          · exact headAligned item head width address dest
                          · exact tailAligned item tail width address dest⟩

/-- The source-input function the `msl`/`msr` per-PE executor builds. -/
def cendMslSourceAt (readState : State) (pe : PEId) (isMsl : Bool)
    (expression : ParsedExpr) (cycle : Fin 4) : Option ParsedIntegerInput :=
  match expression.sources with
  | [source] =>
      let sourcePE := mslMsrSourcePE pe isMsl
      let oldContext := readState.peContext sourcePE
      let coordinates := ParsedIntegerContext.ofLinearIndex sourcePE
      ParsedOperand.toParsedIntegerInput? source .long coordinates.group coordinates.l2b
        coordinates.l1b coordinates.mab coordinates.pe cycle oldContext.bar0 oldContext.bar1
        oldContext.tWord
  | _ => none

/-- **The per-PE `msl`/`msr` step commits family-data writes at the observed
PE.** -/
theorem executeParsedMslMsrAtPE_data_initial
    (expression : ParsedExpr) (isMsl : Bool) (destinations : List ParsedOperand)
    (lowered : lowerParsedMslMsr? expression = some (isMsl, destinations))
    (noForward hasSingleLineMask : Bool) (currentState next : State)
    (executed : executeParsedMslMsrAtPE (cendInitialState cendWitness) currentState expression
      welcomePE noForward hasSingleLineMask = .ok next) :
    ∃ writes : List PreparedParsedMaskedWrite,
      next.peRegisters welcomePE =
        commitParsedMaskedWrites (currentState.peRegisters welcomePE) writes ∧
      (∀ write ∈ writes, ∀ i : Fin 4, i.val < 2 →
        write.data i ∈ cendMixWords cendMslWords) ∧
      (∀ write ∈ writes, ∀ (width : PEMemory.Width) (address : Fin Bank.lm1.capacity),
        write.destination = some ⟨Bank.lm1, width, address⟩ →
          address.val % PEMemory.count Bank.lm1 width = 0) := by
  have registersEq : (cendInitialState cendWitness).peRegisters (mslMsrSourcePE welcomePE isMsl) =
      cendInitialPERegisters cendWitness := rfl
  have poisonEq : stateForwardingSlots (cendInitialState cendWitness)
      (mslMsrSourcePE welcomePE isMsl) = cendPoisonSlots := by
    funext unit cycle
    exact cendInitialForwardingSlots_poison cendWitness (mslMsrSourcePE welcomePE isMsl) unit cycle
  have sourceReadOk : ∀ (cycle : Fin 4) (bus : IntegerALU.Bus),
      (match cendMslSourceAt (cendInitialState cendWitness) welcomePE isMsl expression cycle with
        | some source => ParsedIntegerInput.readWithForwarding
            ((cendInitialState cendWitness).peRegisters (mslMsrSourcePE welcomePE isMsl))
            (stateForwardingSlots (cendInitialState cendWitness)
              (mslMsrSourcePE welcomePE isMsl)) cycle source
        | none => .unknown) = .ok bus → CendMslBusOk bus := by
    intro cycle bus h
    dsimp only [cendMslSourceAt] at h
    cases hs : expression.sources with
    | nil =>
        rw [hs] at h
        simp at h
    | cons operand rest =>
        cases rest with
        | nil =>
            rw [hs] at h
            dsimp only at h
            cases resolved : ParsedOperand.toParsedIntegerInput? operand .long
                (ParsedIntegerContext.ofLinearIndex (mslMsrSourcePE welcomePE isMsl)).group
                (ParsedIntegerContext.ofLinearIndex (mslMsrSourcePE welcomePE isMsl)).l2b
                (ParsedIntegerContext.ofLinearIndex (mslMsrSourcePE welcomePE isMsl)).l1b
                (ParsedIntegerContext.ofLinearIndex (mslMsrSourcePE welcomePE isMsl)).mab
                (ParsedIntegerContext.ofLinearIndex (mslMsrSourcePE welcomePE isMsl)).pe cycle
                ((cendInitialState cendWitness).peContext (mslMsrSourcePE welcomePE isMsl)).bar0
                ((cendInitialState cendWitness).peContext (mslMsrSourcePE welcomePE isMsl)).bar1
                ((cendInitialState cendWitness).peContext (mslMsrSourcePE welcomePE isMsl)).tWord with
            | none =>
                rw [resolved] at h
                simp at h
            | some source =>
                rw [resolved] at h
                simp only at h
                rw [registersEq, poisonEq] at h
                exact cendMslSourceOk_toParsedIntegerInput isMsl operand cycle
                  ((cendInitialState cendWitness).peContext
                    (mslMsrSourcePE welcomePE isMsl)).bar0
                  ((cendInitialState cendWitness).peContext
                    (mslMsrSourcePE welcomePE isMsl)).bar1
                  ((cendInitialState cendWitness).peContext
                    (mslMsrSourcePE welcomePE isMsl)).tWord source resolved bus h
        | cons second more =>
            rw [hs] at h
            simp at h
  rw [executeParsedMslMsrAtPE.eq_1] at executed
  rw [lowered] at executed
  dsimp only at executed
  split at executed
  · simp at executed
  · simp at executed
  · rename_i registers bar0 bar1 outputs ran
    rw [Id.run_pure] at executed
    simp only [StepResult.ok.injEq] at executed
    obtain ⟨writes, committed, dataOk, aligned⟩ :=
      executeParsedMslMsrAtPE_runCycles_data (cendInitialState cendWitness) currentState
        expression hasSingleLineMask _ destinations (mslMsrSourcePE welcomePE isMsl)
        (cendMslSourceAt (cendInitialState cendWitness) welcomePE isMsl expression) sourceReadOk
        [0, 1, 2, 3] (currentState.peRegisters welcomePE) _ _ _ registers bar0 bar1 outputs ran
    refine ⟨writes, ?_, dataOk, aligned⟩
    rw [← executed]
    simpa using committed

/-- **The `msl`/`msr` PE walk commits family-data writes at the observed PE.** -/
theorem executeParsedMslMsrAtPEs_data_initial
    (expression : ParsedExpr) (isMsl : Bool) (destinations : List ParsedOperand)
    (lowered : lowerParsedMslMsr? expression = some (isMsl, destinations))
    (noForward hasSingleLineMask : Bool) :
    ∀ (pes : List PEId) (state next : State),
      executeParsedMslMsrAtPEs (cendInitialState cendWitness) state expression pes noForward
        hasSingleLineMask = .ok next →
      ∃ writes : List PreparedParsedMaskedWrite,
        next.peRegisters welcomePE =
          commitParsedMaskedWrites (state.peRegisters welcomePE) writes ∧
        (∀ write ∈ writes, ∀ i : Fin 4, i.val < 2 →
          write.data i ∈ cendMixWords cendMslWords) ∧
        (∀ write ∈ writes, ∀ (width : PEMemory.Width) (address : Fin Bank.lm1.capacity),
          write.destination = some ⟨Bank.lm1, width, address⟩ →
            address.val % PEMemory.count Bank.lm1 width = 0) := by
  intro pes
  induction pes with
  | nil =>
      intro state next executed
      simp only [executeParsedMslMsrAtPEs, StepResult.ok.injEq] at executed
      subst executed
      exact ⟨[], rfl, by intro write member; simp at member,
        by intro write member; simp at member⟩
  | cons pe rest ih =>
      intro state next executed
      simp only [executeParsedMslMsrAtPEs] at executed
      split at executed
      · simp at executed
      · simp at executed
      · rename_i middle headExecuted
        obtain ⟨tailWrites, tailCommit, tailData, tailAligned⟩ := ih middle next executed
        by_cases same : pe = welcomePE
        · rw [same] at headExecuted
          obtain ⟨headWrites, headCommit, headData, headAligned⟩ :=
            executeParsedMslMsrAtPE_data_initial expression isMsl destinations lowered noForward
              hasSingleLineMask state middle headExecuted
          refine ⟨headWrites ++ tailWrites, ?_, ?_, ?_⟩
          · rw [tailCommit, headCommit,
              show (headWrites ++ tailWrites) = headWrites ++ tailWrites from rfl,
              commitParsedMaskedWrites_append]
          · intro item member i hi
            rcases List.mem_append.mp member with head | tail
            · exact headData item head i hi
            · exact tailData item tail i hi
          · intro item member width address dest
            rcases List.mem_append.mp member with head | tail
            · exact headAligned item head width address dest
            · exact tailAligned item tail width address dest
        · have frame := executeParsedMslMsrAtPE_peRegisters_other (cendInitialState cendWitness)
            state middle expression pe welcomePE (fun h => same h.symm) noForward hasSingleLineMask
            headExecuted
          exact ⟨tailWrites, by rw [tailCommit, frame], tailData, tailAligned⟩

/-- **The `msl`/`msr` stage commits family-data writes at the observed PE.** -/
theorem executeParsedMslMsrProducers_data_initial
    (expressions : List ParsedExpr) (noForward hasSingleLineMask : Bool)
    (currentState next : State)
    (executed : executeParsedMslMsrProducers (cendInitialState cendWitness) currentState
      expressions noForward hasSingleLineMask = .ok next) :
    ∃ writes : List PreparedParsedMaskedWrite,
      next.peRegisters welcomePE =
        commitParsedMaskedWrites (currentState.peRegisters welcomePE) writes ∧
      (∀ write ∈ writes, ∀ i : Fin 4, i.val < 2 →
        write.data i ∈ cendMixWords cendMslWords) ∧
      (∀ write ∈ writes, ∀ (width : PEMemory.Width) (address : Fin Bank.lm1.capacity),
        write.destination = some ⟨Bank.lm1, width, address⟩ →
          address.val % PEMemory.count Bank.lm1 width = 0) := by
  cases filtered : expressions.filter parsedExprIsMslMsrProducer with
  | nil =>
      rw [executeParsedMslMsrProducers, filtered] at executed
      simp only [StepResult.ok.injEq] at executed
      subst executed
      exact ⟨[], rfl, by intro write member; simp at member,
        by intro write member; simp at member⟩
  | cons expression rest =>
      cases rest with
      | nil =>
          rw [executeParsedMslMsrProducers, filtered] at executed
          cases lowered : lowerParsedMslMsr? expression with
          | none =>
              have split := plusTwoFinRange_split.1
              rw [split] at executed
              simp [executeParsedMslMsrAtPEs,
                executeParsedMslMsrAtPE_lowering_failure (cendInitialState cendWitness) currentState
                  expression plusTwoPE noForward hasSingleLineMask lowered] at executed
          | some accesses =>
              obtain ⟨isMsl, destinations⟩ := accesses
              exact executeParsedMslMsrAtPEs_data_initial expression isMsl destinations lowered
                noForward hasSingleLineMask (List.finRange 4096) currentState next executed
      | cons second remaining =>
          rw [executeParsedMslMsrProducers, filtered] at executed
          simp at executed

/-! ## 6. The `msl`/`msr` line class -/

/-- **The rows the `msl`/`msr` class covers**: a `.matrixRead`/`.noforward` row, an
extended-inert row (`.wait`, a shared-block `.l1bm`, `.matrixWrite`, `.l2bm`), or
an `msl`/`msr` row.  L1BM-to-PE broadcast rows are *not* in the class; they are
handled by the zero-bus frame of `CendNonPlain` and are the one remaining
mixture with an `msl`/`msr` row. -/
def cendMslMsrRow (expression : ParsedExpr) : Bool :=
  (cendReadOrNoForward expression || cendPEInertProducerExt expression) ||
    parsedExprIsMslMsrProducer expression

theorem cendMslMsrRow_cases (expression : ParsedExpr) (row : cendMslMsrRow expression = true) :
    cendReadOrNoForward expression = true ∨ cendPEInertProducerExt expression = true ∨
      parsedExprIsMslMsrProducer expression = true := by
  have h := row
  simp only [cendMslMsrRow, Bool.or_eq_true] at h
  rcases h with both | msl
  · rcases both with read | ext
    · exact Or.inl read
    · exact Or.inr (Or.inl ext)
  · exact Or.inr (Or.inr msl)

/-- **An `msl`/`msr` class row is never a float-relu, block-float, matrix-MAU,
float-MAU or L1BM-to-PE row.** -/
theorem cendMslMsrRow_family_facts (expression : ParsedExpr)
    (row : cendMslMsrRow expression = true) :
    parsedExprIsFloatReluProducer expression = false ∧
      parsedExprIsBlockFloatProducer expression = false ∧
      parsedExprIsMatrixMAUProducer expression = false ∧
      parsedExprIsSupportedFloatMAUProducer expression = false ∧
      parsedExprIsL1ToPEProducer expression = false := by
  obtain ⟨op, sources, destinations, flush, text⟩ := expression
  simp only [cendMslMsrRow, cendReadOrNoForward, parsedExprIsMatrixReadProducer,
    cendPEInertProducerExt, parsedExprIsPEInertProducer, parsedExprIsL1SharedBlockProducer,
    parsedExprIsMatrixWriteProducer, parsedExprIsL2BMProducer] at row
  cases op with
  | alu name precision unsigned arg =>
      cases name <;> cases precision <;>
        simp_all [parsedExprIsFloatReluProducer, parsedExprIsBlockFloatProducer,
          parsedExprIsMatrixMAUProducer, parsedExprIsSupportedFloatMAUProducer,
          parsedExprIsL1ToPEProducer, parsedExprIsMslMsrProducer]
  | noforward => simp_all [parsedExprIsFloatReluProducer, parsedExprIsBlockFloatProducer,
      parsedExprIsMatrixMAUProducer, parsedExprIsSupportedFloatMAUProducer,
      parsedExprIsL1ToPEProducer, parsedExprIsMslMsrProducer]
  | immediate value unsigned => simp_all [parsedExprIsFloatReluProducer,
      parsedExprIsBlockFloatProducer, parsedExprIsMatrixMAUProducer,
      parsedExprIsSupportedFloatMAUProducer, parsedExprIsL1ToPEProducer, parsedExprIsMslMsrProducer]
  | zero => simp_all [parsedExprIsFloatReluProducer, parsedExprIsBlockFloatProducer,
      parsedExprIsMatrixMAUProducer, parsedExprIsSupportedFloatMAUProducer,
      parsedExprIsL1ToPEProducer, parsedExprIsMslMsrProducer]
  | mau precision matrix kind half round => simp_all [parsedExprIsFloatReluProducer,
      parsedExprIsBlockFloatProducer, parsedExprIsMatrixMAUProducer,
      parsedExprIsSupportedFloatMAUProducer, parsedExprIsL1ToPEProducer, parsedExprIsMslMsrProducer]
  | matrixWrite precision => simp_all [parsedExprIsFloatReluProducer,
      parsedExprIsBlockFloatProducer, parsedExprIsMatrixMAUProducer,
      parsedExprIsSupportedFloatMAUProducer, parsedExprIsL1ToPEProducer, parsedExprIsMslMsrProducer]
  | wait tag => simp_all [parsedExprIsFloatReluProducer, parsedExprIsBlockFloatProducer,
      parsedExprIsMatrixMAUProducer, parsedExprIsSupportedFloatMAUProducer,
      parsedExprIsL1ToPEProducer, parsedExprIsMslMsrProducer]
  | l1bm l1op =>
      cases l1op <;> simp_all [parsedExprIsFloatReluProducer, parsedExprIsBlockFloatProducer,
        parsedExprIsMatrixMAUProducer, parsedExprIsSupportedFloatMAUProducer,
        parsedExprIsL1ToPEProducer, parsedExprIsMslMsrProducer]
  | l2bm l2op => simp_all [parsedExprIsFloatReluProducer, parsedExprIsBlockFloatProducer,
      parsedExprIsMatrixMAUProducer, parsedExprIsSupportedFloatMAUProducer,
      parsedExprIsL1ToPEProducer, parsedExprIsMslMsrProducer]
  | matrixRead precision => simp_all [parsedExprIsFloatReluProducer,
      parsedExprIsBlockFloatProducer, parsedExprIsMatrixMAUProducer,
      parsedExprIsSupportedFloatMAUProducer, parsedExprIsL1ToPEProducer, parsedExprIsMslMsrProducer]

/-- **Every stage input of an `msl`/`msr` class row is a `.matrixRead` or
`.noforward` row.** -/
theorem cendMslMsrRow_stageInput (expression : ParsedExpr)
    (row : cendMslMsrRow expression = true)
    (stage : parsedExprIsIntegerMatrixReadStageInput expression = true) :
    expression.op = .noforward ∨ ∃ precision, expression.op = .matrixRead precision := by
  rcases cendMslMsrRow_cases expression row with read | ext | msl
  · exact cendReadOrNoForward_cases expression read
  · exact Or.inl (cendPEInertProducerExt_stageInput_noforward expression ext stage)
  · obtain ⟨op, sources, destinations, flush, text⟩ := expression
    simp only [parsedExprIsMslMsrProducer] at msl
    cases op with
    | alu name precision unsigned arg =>
        cases name <;> cases precision <;>
          simp_all [parsedExprIsIntegerMatrixReadStageInput, parsedExprIsMslMsrProducer]
    | _ => simp_all [parsedExprIsIntegerMatrixReadStageInput, parsedExprIsMslMsrProducer]

/-- The lines of the `msl`/`msr` class. -/
def CendMslMsrLines (expressions : List NormalizedExpr) : Prop :=
  ∀ expression ∈ expressions.map NormalizedExpr.toParsed, cendMslMsrRow expression = true

/-- **A successful `msl`/`msr`-class line keeps the observed LM1 word `0` in the
family half-mix set**, hence is incorrect at `cendWitness`. -/
theorem cendPE_mslMsrLines_not_correct (expressions : List NormalizedExpr)
    (rows : CendMslMsrLines expressions) :
    ¬ ProofsLean.Correct cendSealedMachine cendSpec
      ([InstructionLine.pe expressions] : List InstructionLine) := by
  cases step : cendSealedMachine.step (.pe expressions) (cendInitialState cendWitness) with
  | none => exact cend_not_correct_of_step_none _ _ step
  | some next =>
      have executed := cendSealed_step_ok step
      have lineExecuted : executeIntegerProducerInstructionLine (.pe expressions)
          (cendInitialState cendWitness) = .ok next := by
        unfold executeNormalizedLine at executed
        simp only [Issue.InstructionLine.toNormalizedLine, NormalizedLine.toInstruction?] at executed
        exact executed
      have accepted := executeIntegerProducerInstructionLine_accepted_of_ok
        (.pe expressions) (cendInitialState cendWitness) next lineExecuted
      have waitsAny := executeIntegerProducerInstructionLine_pe_waits_complete expressions
        (cendInitialState cendWitness) next lineExecuted
      have noUnsupportedAny := executeIntegerProducerInstructionLine_pe_noUnsupported_of_ok
        expressions (cendInitialState cendWitness) next lineExecuted
      have supportedAny := executeIntegerProducerInstructionLine_pe_supported_of_ok
        expressions (cendInitialState cendWitness) next lineExecuted
      obtain ⟨nextPEs, nextMsl, nextRelu, nextBlockFloat, afterMatrix, nextShared,
        nextBroadcast, walkExecuted, mslExecuted, reluExecuted, blockExecuted, matrixExecuted,
        sharedExecuted, l1Executed, nextEq⟩ :=
        executeIntegerProducerInstructionLine_pe_stages_exists expressions
          (cendInitialState cendWitness) next accepted waitsAny noUnsupportedAny supportedAny
          lineExecuted
      have parsedRows : ∀ expression ∈ expressions.map NormalizedExpr.toParsed,
          cendMslMsrRow expression = true := rows
      have reluEmpty : (expressions.map NormalizedExpr.toParsed).filter
          parsedExprIsFloatReluProducer = [] :=
        List.filter_eq_nil_iff.mpr fun expression member => by
          rw [(cendMslMsrRow_family_facts expression (parsedRows expression member)).1]; simp
      have blockEmpty : (expressions.map NormalizedExpr.toParsed).filter
          parsedExprIsBlockFloatProducer = [] :=
        List.filter_eq_nil_iff.mpr fun expression member => by
          rw [(cendMslMsrRow_family_facts expression (parsedRows expression member)).2.1]; simp
      have mauEmpty : (expressions.map NormalizedExpr.toParsed).filter
          parsedExprIsMatrixMAUProducer = [] :=
        List.filter_eq_nil_iff.mpr fun expression member => by
          rw [(cendMslMsrRow_family_facts expression (parsedRows expression member)).2.2.1]; simp
      have floatEmpty : (expressions.map NormalizedExpr.toParsed).filter
          parsedExprIsSupportedFloatMAUProducer = [] :=
        List.filter_eq_nil_iff.mpr fun expression member => by
          rw [(cendMslMsrRow_family_facts expression (parsedRows expression member)).2.2.2.1]; simp
      have l1Empty : (expressions.map NormalizedExpr.toParsed).filter
          parsedExprIsL1ToPEProducer = [] :=
        List.filter_eq_nil_iff.mpr fun expression member => by
          rw [(cendMslMsrRow_family_facts expression (parsedRows expression member)).2.2.2.2]; simp
      -- the integer stage: a zero-data prepared list at the observed PE
      have stageRows : ∀ expression ∈ ((expressions.map NormalizedExpr.toParsed).filter
          (fun expression =>
            !parsedExprIsL2BMProducer expression && !parsedExprIsMslMsrProducer expression &&
              !parsedExprIsMatrixMAUProducer expression && !parsedExprIsBlockFloatProducer expression &&
              !parsedExprIsFloatReluProducer expression)).filter
          parsedExprIsIntegerMatrixReadStageInput,
          expression.op = .noforward ∨ ∃ precision, expression.op = .matrixRead precision := by
        intro expression member
        exact cendMslMsrRow_stageInput expression
          (parsedRows expression (List.mem_filter.mp (List.mem_filter.mp member).1).1)
          (List.mem_filter.mp member).2
      have floatEmptyOuter : ((expressions.map NormalizedExpr.toParsed).filter (fun expression =>
          !parsedExprIsL2BMProducer expression && !parsedExprIsMslMsrProducer expression &&
            !parsedExprIsMatrixMAUProducer expression && !parsedExprIsBlockFloatProducer expression &&
            !parsedExprIsFloatReluProducer expression)).filter
          parsedExprIsSupportedFloatMAUProducer = [] :=
        List.filter_eq_nil_iff.mpr fun expression member =>
          (List.filter_eq_nil_iff.mp floatEmpty) expression (List.mem_filter.mp member).1
      obtain ⟨split, absent⟩ := plusTwoFinRange_split
      rw [split] at walkExecuted
      obtain ⟨intWrites, intSlots, intBars, intPrepared, intDataZero, intCommit⟩ :=
        cendMixedReadWalk_prepared
          ((expressions.map NormalizedExpr.toParsed).filter (fun expression =>
            !parsedExprIsL2BMProducer expression && !parsedExprIsMslMsrProducer expression &&
              !parsedExprIsMatrixMAUProducer expression && !parsedExprIsBlockFloatProducer expression &&
              !parsedExprIsFloatReluProducer expression))
          cendWitness ((List.finRange 4095).map Fin.succ) nextPEs absent stageRows floatEmptyOuter
          walkExecuted
      have intZero : ∀ target : Fin Bank.lm1.capacity,
          (nextPEs.peRegisters cendPE).lm1 target = 0 := by
        intro target
        rw [intCommit]
        exact commitParsedMaskedWrites_lm1_zero_of_data_zero
          ((cendInitialState cendWitness).peRegisters cendPE) intWrites intDataZero
          (fun address => cendInitialPERegisters_lm1 cendWitness address) target
      -- the msl/msr stage: a family-data write list at the observed PE
      obtain ⟨mslWrites, mslCommit, mslData, mslAligned⟩ :=
        executeParsedMslMsrProducers_data_initial (expressions.map NormalizedExpr.toParsed)
          _ _ nextPEs nextMsl mslExecuted
      -- the remaining stages frame the observed PE
      have reluEq : nextRelu = nextMsl := by
        rw [executeParsedFloatReluProducers_eq_self (cendInitialState cendWitness) nextMsl
          (expressions.map NormalizedExpr.toParsed) _ _ reluEmpty] at reluExecuted
        exact (StepResult.ok.inj reluExecuted).symm
      have blockEq : nextBlockFloat = nextRelu := by
        rw [executeParsedBlockFloatProducer_eq_self (cendInitialState cendWitness) nextRelu
          (expressions.map NormalizedExpr.toParsed) _ _ blockEmpty] at blockExecuted
        exact (StepResult.ok.inj blockExecuted).symm
      have matrixFrame : afterMatrix.peRegisters = nextBlockFloat.peRegisters := by
        funext pe
        exact executeParsedMatrixMAUAndWrites_peRegisters_frame_of_noMatrixMAU
          (cendInitialState cendWitness) nextBlockFloat afterMatrix
          (expressions.map NormalizedExpr.toParsed) _ _ mauEmpty matrixExecuted pe
      have sharedFrame : nextShared.peRegisters = afterMatrix.peRegisters :=
        executeParsedSharedBlockProducers_peRegisters (cendInitialState cendWitness) afterMatrix
          nextShared (expressions.map NormalizedExpr.toParsed) _ sharedExecuted
      have l1Eq : nextBroadcast = nextShared := by
        rw [executeParsedL1ToPEProducers_nil (cendInitialState cendWitness) nextShared
          (expressions.map NormalizedExpr.toParsed) _ _ _ l1Empty] at l1Executed
        exact (StepResult.ok.inj l1Executed).symm
      -- the observed word lands in the family value set
      have observed : (next.peRegisters cendPE).lm1 (⟨0, by decide⟩ : Fin Bank.lm1.capacity) ∈
          cendMixWords cendMslWords := by
        have registersEq : next.peRegisters = nextBroadcast.peRegisters := by rw [nextEq]
        have startMem : (nextPEs.peRegisters cendPE).lm1
            (⟨0, by decide⟩ : Fin Bank.lm1.capacity) ∈ cendMixWords cendMslWords := by
          rw [intZero]
          exact cendMixWords_zero cendMslWords_zero
        rw [registersEq, l1Eq, sharedFrame, matrixFrame, blockEq, reluEq, mslCommit]
        exact commitParsedMaskedWrites_lm1_mixWords mslWrites
          (⟨0, by decide⟩ : Fin Bank.lm1.capacity) (by decide) mslData mslAligned _
          startMem
      refine cend_not_correct_of_word0_ne expressions cendWitness next step ?_
      intro same
      have targetEq : cendOutputWord0 next = 0x08070605 := by
        rw [same, cendWitness_target_high]
      have observedEq : (next.peRegisters cendPE).lm1
          (⟨0, by decide⟩ : Fin Bank.lm1.capacity) = 0x08070605 := by
        rw [show (next.peRegisters cendPE).lm1 (⟨0, by decide⟩ : Fin Bank.lm1.capacity) =
          cendOutputWord0 next from rfl]
        exact targetEq
      rw [observedEq] at observed
      exact cendMslWords_target_high_avoid observed

/-! ## 7. The narrowed residual, exactness and the reductions -/

/-- The `msl`/`msr` class, as a refutation statement. -/
def CendMslMsrLinesRefuted : Prop :=
  ∀ expressions : List NormalizedExpr, CendMslMsrLines expressions →
    ¬ ProofsLean.Correct cendSealedMachine cendSpec
      ([InstructionLine.pe expressions] : List InstructionLine)

/-- The `msl`/`msr` class is refuted (§6). -/
theorem cendMslMsrLinesRefuted_holds : CendMslMsrLinesRefuted :=
  fun expressions rows => cendPE_mslMsrLines_not_correct expressions rows

/-- **The narrowed residual.**  Everything `CendMixedReadResidual` leaves open,
minus the `msl`/`msr` class of §6. -/
def CendMslMsrResidual : Prop :=
  ∀ expressions : List NormalizedExpr,
    ¬ CendClosedLines expressions →
    ¬ (∀ expression ∈ expressions.map NormalizedExpr.toParsed,
      cendL1ToPEOrExtInert expression = true) →
    ¬ (expressions.map NormalizedExpr.toParsed).all parsedExprIsPlainIntegerALU = true →
    ¬ CendMixedReadLines expressions →
    ¬ CendMslMsrLines expressions →
    ¬ ProofsLean.Correct cendSealedMachine cendSpec
      ([InstructionLine.pe expressions] : List InstructionLine)

/-- **`CendMixedReadResidual` from the narrower residual.** -/
theorem cendMixedReadResidual_of_mslMsrResidual (residual : CendMslMsrResidual) :
    CendMixedReadResidual := by
  intro expressions notClosed notClosedExt notPlain notMixed
  by_cases msl : CendMslMsrLines expressions
  · exact cendPE_mslMsrLines_not_correct expressions msl
  · exact residual expressions notClosed notClosedExt notPlain notMixed msl

/-- **`CendPENonClosedRefuted` from the narrower residual.** -/
theorem cendPENonClosedRefuted_of_mslMsrResidual (residual : CendMslMsrResidual) :
    CendPENonClosedRefuted :=
  cendPENonClosedRefuted_of_mixedReadResidual
    (cendMixedReadResidual_of_mslMsrResidual residual)

/-- **The unconditional lower bound at two from the narrower residual.** -/
theorem cendLowerBound_two_of_mslMsrResidual (residual : CendMslMsrResidual) :
    ProofsLean.LowerBound cendSealedMachine cendSpec 2 :=
  cendLowerBound_two_of_mixedReadResidual
    (cendMixedReadResidual_of_mslMsrResidual residual)

/-- **The narrowing is exact.**  The mixed residual splits into the narrower
residual and the `msl`/`msr` refutation, so the new residual is exactly the old
one minus the lines §6 closes. -/
theorem cendMixedReadResidual_iff_mslMsrResidual :
    CendMixedReadResidual ↔ CendMslMsrResidual ∧ CendMslMsrLinesRefuted := by
  constructor
  · intro residual
    exact ⟨fun expressions notClosed notClosedExt notPlain notMixed _msl =>
        residual expressions notClosed notClosedExt notPlain notMixed,
      cendMslMsrLinesRefuted_holds⟩
  · rintro ⟨residual, refuted⟩ expressions notClosed notClosedExt notPlain notMixed
    by_cases msl : CendMslMsrLines expressions
    · exact refuted expressions msl
    · exact residual expressions notClosed notClosedExt notPlain notMixed msl

/-! ## 8. A concrete line that only the new class refutes -/

/-- One `.matrixRead` row and one `msl` row. -/
def cendMslExampleLine : List NormalizedExpr :=
  [⟨.matrixRead .d, [], [], none⟩, ⟨.alu .msl none false none, [], [], none⟩]

theorem cendMslExampleLine_msl : CendMslMsrLines cendMslExampleLine := by
  intro expression member
  obtain ⟨normalized, normalizedMem, rfl⟩ := List.mem_map.mp member
  simp only [cendMslExampleLine, List.mem_cons, List.not_mem_nil, or_false] at normalizedMem
  rcases normalizedMem with rfl | rfl
  · simp [NormalizedExpr.toParsed, cendMslMsrRow, cendReadOrNoForward,
      parsedExprIsMatrixReadProducer]
  · simp [NormalizedExpr.toParsed, cendMslMsrRow, cendReadOrNoForward,
      cendPEInertProducerExt, parsedExprIsMatrixReadProducer, parsedExprIsMslMsrProducer]

theorem cendMslExampleLine_notMixed : ¬ CendMixedReadLines cendMslExampleLine := by
  intro mixed
  have row := mixed ⟨.alu .msl none false none, [], [], none, ""⟩ (by
    simp [cendMslExampleLine, NormalizedExpr.toParsed])
  simp_all [NormalizedExpr.toParsed, cendMixedReadRow, cendReadOrNoForward, cendL1ToPEOrExtInert,
    cendPEInertProducerExt, parsedExprIsMatrixReadProducer, parsedExprIsMslMsrProducer,
    parsedExprIsPEInertProducer, parsedExprIsL1SharedBlockProducer,
    parsedExprIsMatrixWriteProducer, parsedExprIsL2BMProducer,
    parsedExprIsL1ToPEProducer]

theorem cendMslExampleLine_notClosed : ¬ CendClosedLines cendMslExampleLine := by
  intro closed
  rcases closed with allRead | allInert
  · have read := allRead ⟨.alu .msl none false none, [], [], none⟩ (by
      simp [cendMslExampleLine, NormalizedExpr.toParsed])
    obtain ⟨precision, hop⟩ := read
    simp [NormalizedExpr.toParsed] at hop
  · have inert := allInert ⟨.alu .msl none false none, [], [], none, ""⟩ (by
      simp [cendMslExampleLine, NormalizedExpr.toParsed])
    simp_all [NormalizedExpr.toParsed, parsedExprIsPEInertProducer,
      parsedExprIsL1SharedBlockProducer]

/-- **The new residual is strictly smaller.**  The example line is in the
`msl`/`msr` class, so §6 refutes it, while it satisfies the three negative
hypotheses of `CendMixedReadResidual`. -/
theorem cendMslExampleLine_new :
    CendMslMsrLines cendMslExampleLine ∧
      ¬ CendClosedLines cendMslExampleLine ∧
      ¬ CendMixedReadLines cendMslExampleLine :=
  ⟨cendMslExampleLine_msl, cendMslExampleLine_notClosed, cendMslExampleLine_notMixed⟩

/-! ## Trust report -/

#print axioms cendMixWords_mem
#print axioms mergeSelectedWord_mixWords_mem
#print axioms commitParsedMaskedWrites_lm1_mixWords
#print axioms cendFlush_data_mixWords
#print axioms cendOutputAfterFlush_data_mixWords
#print axioms cendMslWords_target_high_avoid
#print axioms cendMslWords_target_low_avoid
#print axioms cendMslSourcePE_value
#print axioms cendMslSourceOk_toParsedIntegerInput
#print axioms writeParsedMslMsrDestination?_dataAligned
#print axioms executeParsedMslMsrAtPE_writeDestinations_data
#print axioms executeParsedMslMsrAtPE_runCycles_data
#print axioms executeParsedMslMsrAtPE_data_initial
#print axioms executeParsedMslMsrAtPEs_data_initial
#print axioms executeParsedMslMsrProducers_data_initial
#print axioms cendMslMsrRow_family_facts
#print axioms cendMslMsrRow_stageInput
#print axioms cendPE_mslMsrLines_not_correct
#print axioms cendMslMsrLinesRefuted_holds
#print axioms cendMixedReadResidual_of_mslMsrResidual
#print axioms cendLowerBound_two_of_mslMsrResidual
#print axioms cendMixedReadResidual_iff_mslMsrResidual
#print axioms cendMslExampleLine_new

end ProofsLean.MNCore
