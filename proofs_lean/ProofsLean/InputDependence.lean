import ProofsLean.PlusTwoBoundSix

/-! # An input-dependence kernel for the PE-memory floor arguments

`ProofsLean/PlusTwoBoundSix.lean` shows that the counting route to
`LowerBound plusTwoSealedMachine plusTwoSpec 6` cannot work: at the all-zero
input every observed word holds the same value `2`, so pass-through copies
suffice.  The honest floor is **input-parametric**: the output word `k` must
carry `input k + 2` as a function of the input, and the twenty functions
`input ↦ input k + 2` are distinct.

This module builds the reusable kernel for that argument.  It is problem-free
where possible, and it is organised exactly like the counting kernel it
replaces:

1. **Read locality** (§1–§2).  A direct PE-memory access resolves to one region
   of at most four words (`accessRegion`, `accessRegion_subset_advance`), and
   `readDirectAccess` is unchanged when the register files change outside that
   region (`readDirectAccess_congr`).  Every integer source operand is either a
   direct memory access (`.memory`), a constant bus (`.fixed`) or a forwarding
   slot (`.forward`), so the bus a line reads from an operand is unchanged
   outside that one region (`ParsedIntegerInput.readWithForwarding_congr_of_agree`,
   `ParsedIntegerInput.readsRegion_shape`).  The contrapositive
   (`exists_word_diff_of_readDirectAccess_ne`) is the tracing engine: a
   different read bus exhibits a different word *inside* the region.

2. **Independence** (§3–§4).  If two register files agree on the region a
   prepared write reads, the prepared write is *the same write record*
   (`prepareParsedMaskedWriteWithForwarding_congr_of_agree`); its `data` bus is
   therefore identical (`prepareParsedMaskedWriteWithForwarding_data_eq_of_agree`).
   Committing the same write list to two files that agree on a word set `R`
   keeps them agreeing on `R` (`commitParsedMaskedWrites_congr_on`), and the
   pinned-commit-list form `peRegisters_congr_of_commitList` is the bridge the
   per-family provenance lemmas feed.

3. **Chain through a program** (§5).  The independence of §4 is lifted to a
   whole program: if every line is *write-determined* on its read footprint
   (`LineDeterminedAt`), and the footprints avoid a difference set `D`, then two
   executions from states that agree outside `D` end agreeing outside `D`
   (`execute_agreeOutside_of_determined`).  The contrapositive
   (`exists_footprint_meets_of_output_ne`) is the usable form: a different
   output word forces some line's footprint to meet `D`.  `nop` lines satisfy
   the contract (`nop_lineDeterminedOn`).

4. **The `2.plus-two` application** (§6).  The reduction is instantiated at
   `plusTwoSpec`: two inputs that agree away from index `j` give initial states
   that agree outside the LM0 word of input `j`
   (`plusTwoInitialPERegisters_agree_outside`), and a prepared write avoiding
   that word is unchanged (`plusTwo_preparedWrite_input_independent`).  Hence
   **a correct program must, for every `j`, contain a line whose read footprint
   contains the LM0 word of input `j`**
   (`plusTwo_output_forces_concrete_read`), and a program that never reads input
   `j` is incorrect (`plusTwo_not_correct_of_footprint_avoids`).

The exact remaining executor obligation is named:
`PlusTwoWriteDetermination` says that a line's committed PE-0 write list is a
function of its reads.  §3–§4 discharge it for one prepared write and for a
commit list; the composition over a line's four cycles and its producer stages
(and the auxiliary forwarding / mask-register / BAR / clock channels) is what is
still missing.  No `LowerBound 6` is claimed here.

No `sorry`, no `admit`, no `native_decide`, no new axioms. -/

namespace ProofsLean.MNCore

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
set_option autoImplicit false

open Issue
open PEMemory

/-! ## 1. Word references, agreement, and the region of one access -/

/-- A concrete addressable 32-bit word of a PE register file.  The bank is part
of the reference so that agreement can be stated for the five files at once. -/
abbrev WordRef : Type := Sigma (fun bank : PEMemory.Bank => Fin bank.capacity)

/-- The value of one PE-register word. -/
def wordValue (files : IntegerRegisterFiles) (w : WordRef) : BitVec 32 :=
  match w with
  | ⟨.lm0, address⟩ => files.lm0 address
  | ⟨.lm1, address⟩ => files.lm1 address
  | ⟨.grf0, address⟩ => files.grf0 address
  | ⟨.grf1, address⟩ => files.grf1 address
  | ⟨.t, address⟩ => files.t address

@[simp] theorem wordValue_mk (files : IntegerRegisterFiles) (bank : PEMemory.Bank)
    (address : Fin bank.capacity) :
    wordValue files ⟨bank, address⟩ =
      (match bank with
       | .lm0 => files.lm0 address
       | .lm1 => files.lm1 address
       | .grf0 => files.grf0 address
       | .grf1 => files.grf1 address
       | .t => files.t address) := by
  cases bank <;> rfl

theorem wordValue_lm0 (files : IntegerRegisterFiles) (address : Fin PEMemory.Bank.lm0.capacity) :
    wordValue files ⟨.lm0, address⟩ = files.lm0 address := rfl

theorem wordValue_lm1 (files : IntegerRegisterFiles) (address : Fin PEMemory.Bank.lm1.capacity) :
    wordValue files ⟨.lm1, address⟩ = files.lm1 address := rfl

/-- **Agreement on a set of words.**  Two register files agree on `R` when they
store the same 32-bit value at every word of `R`. -/
def FilesAgreeOn (R : Set WordRef) (files files' : IntegerRegisterFiles) : Prop :=
  ∀ w, w ∈ R → wordValue files w = wordValue files' w

theorem filesAgreeOn_refl (R : Set WordRef) (files : IntegerRegisterFiles) :
    FilesAgreeOn R files files := fun _ _ => rfl

theorem filesAgreeOn_symm {R : Set WordRef} {files files' : IntegerRegisterFiles}
    (h : FilesAgreeOn R files files') : FilesAgreeOn R files' files :=
  fun w hw => (h w hw).symm

theorem filesAgreeOn_trans {R : Set WordRef} {files files' files'' : IntegerRegisterFiles}
    (h : FilesAgreeOn R files files') (h' : FilesAgreeOn R files' files'') :
    FilesAgreeOn R files files'' :=
  fun w hw => (h w hw).trans (h' w hw)

theorem FilesAgreeOn.mono {R R' : Set WordRef} {files files' : IntegerRegisterFiles}
    (h : FilesAgreeOn R files files') (subset : R' ⊆ R) : FilesAgreeOn R' files files' :=
  fun w hw => h w (subset hw)

/-- `advance` inverts `distance` at every capacity. -/
theorem nat_advance_distance_capacity (capacity start target : Nat) (hcap : 0 < capacity)
    (hs : start < capacity) (ht : target < capacity) :
    (start + (target + capacity - start) % capacity) % capacity = target := by
  rcases Nat.lt_or_ge target start with hlt | hge
  · have h1 : target + capacity - start < capacity := by omega
    rw [Nat.mod_eq_of_lt h1]
    have h2 : start + (target + capacity - start) = target + capacity := by omega
    rw [h2, Nat.add_mod_right]
    exact Nat.mod_eq_of_lt ht
  · have h1 : target + capacity - start = (target - start) + capacity := by omega
    have h2 : target - start < capacity := by omega
    have h3 : (target - start + capacity) % capacity = target - start := by
      rw [Nat.add_mod_right, Nat.mod_eq_of_lt h2]
    rw [h1, h3]
    have h4 : start + (target - start) = target := by omega
    rw [h4, Nat.mod_eq_of_lt ht]

/-- **`advance` inverts `distance`** at every bank. -/
theorem advance_distance_capacity (bank : PEMemory.Bank) (start target : Fin bank.capacity) :
    advance bank start (distance bank start target) = target := by
  apply Fin.ext
  have ht := target.isLt
  have hs := start.isLt
  have hcap := bank.capacity_positive
  change (start.val + distance bank start target) % bank.capacity = target.val
  unfold distance
  exact nat_advance_distance_capacity bank.capacity start.val target.val hcap hs ht

/-- **The words covered by one direct access.**  A read or write of a direct
PE-memory access touches exactly the words at distance `< count bank width`
from the resolved address; `count` is at most four. -/
def accessRegion (access : DirectMemoryAccess) : Set WordRef :=
  match access with
  | ⟨bank, width, start⟩ =>
      {w | ∃ address : Fin bank.capacity,
        w = ⟨bank, address⟩ ∧ distance bank start address < count bank width}

theorem mem_accessRegion_iff (access : DirectMemoryAccess) (w : WordRef) :
    w ∈ accessRegion access ↔
      ∃ (address : Fin access.bank.capacity),
        w = ⟨access.bank, address⟩ ∧
          distance access.bank access.address address <
            count access.bank access.width := by
  cases access with
  | mk bank width start => rfl

theorem accessRegion_bank (access : DirectMemoryAccess) {w : WordRef}
    (hw : w ∈ accessRegion access) : w.1 = access.bank := by
  obtain ⟨bank, width, start⟩ := access
  obtain ⟨address, hwEq, within⟩ := (mem_accessRegion_iff ⟨bank, width, start⟩ w).mp hw
  rw [hwEq]

/-- **A direct access covers at most four words.**  The region is contained in
the four-word window starting at the resolved address. -/
theorem accessRegion_subset_advance (access : DirectMemoryAccess) :
    accessRegion access ⊆
      {w | ∃ i : Fin 4, w = ⟨access.bank, advance access.bank access.address i.val⟩} := by
  intro w hw
  obtain ⟨address, hwEq, within⟩ := (mem_accessRegion_iff access w).mp hw
  subst hwEq
  refine ⟨⟨distance access.bank access.address address,
    Nat.lt_of_lt_of_le within (count_le_four access.bank access.width)⟩, ?_⟩
  rw [advance_distance_capacity]

/-- A read of a window is the window word at the corresponding index, or zero
outside the written width. -/
theorem readWords_congr (bank : PEMemory.Bank) (width : PEMemory.Width) (memory memory' : PEMemory.Memory bank)
    (start : Fin bank.capacity)
    (h : ∀ address : Fin bank.capacity,
      distance bank start address < count bank width → memory address = memory' address) :
    readWords bank width memory start = readWords bank width memory' start := by
  funext index
  simp only [readWords]
  by_cases within : index.val < count bank width
  · rw [ite_eq_left within, ite_eq_left within]
    exact h (advance bank start index.val) (by rw [distance_advance]; exact within)
  · rw [ite_eq_right within, ite_eq_right within]

/-- **Read locality of one direct access.**  Changing the register files
outside `accessRegion access` does not change the four-word bus read by that
access.  This is the read half of the dependency kernel. -/
theorem readDirectAccess_congr (access : DirectMemoryAccess) (files files' :
    IntegerRegisterFiles) (h : FilesAgreeOn (accessRegion access) files files') :
    readDirectAccess files access = readDirectAccess files' access := by
  obtain ⟨bank, width, start⟩ := access
  cases bank with
  | lm0 =>
      show readWords .lm0 width files.lm0 start = readWords .lm0 width files'.lm0 start
      apply readWords_congr
      intro address within
      exact h ⟨.lm0, address⟩ ⟨address, rfl, within⟩
  | lm1 =>
      show readWords .lm1 width files.lm1 start = readWords .lm1 width files'.lm1 start
      apply readWords_congr
      intro address within
      exact h ⟨.lm1, address⟩ ⟨address, rfl, within⟩
  | grf0 =>
      show readWords .grf0 width files.grf0 start = readWords .grf0 width files'.grf0 start
      apply readWords_congr
      intro address within
      exact h ⟨.grf0, address⟩ ⟨address, rfl, within⟩
  | grf1 =>
      show readWords .grf1 width files.grf1 start = readWords .grf1 width files'.grf1 start
      apply readWords_congr
      intro address within
      exact h ⟨.grf1, address⟩ ⟨address, rfl, within⟩
  | t =>
      show readWords .t width files.t start = readWords .t width files'.t start
      apply readWords_congr
      intro address within
      exact h ⟨.t, address⟩ ⟨address, rfl, within⟩

/-- **The contrapositive engine at one access.**  If two register files read
different four-word buses at an access, then they differ at some word *inside*
that access's region.  This is the form used to trace a differing output back to
a differing input word. -/
theorem exists_word_diff_of_readDirectAccess_ne (access : DirectMemoryAccess)
    (files files' : IntegerRegisterFiles)
    (hne : readDirectAccess files access ≠ readDirectAccess files' access) :
    ∃ w, w ∈ accessRegion access ∧ wordValue files w ≠ wordValue files' w := by
  by_contra none
  apply hne
  apply readDirectAccess_congr
  intro w hw
  by_contra different
  exact none ⟨w, hw, different⟩

/-! ## 2. Read locality of one source operand

An integer source is a `.memory` access, a `.fixed` constant bus, or a
`.forward` slot.  Only the first reads the register files, and it reads exactly
the region of §1. -/

theorem ParsedIntegerInput.read_congr_memory (files files' : IntegerRegisterFiles)
    (access : DirectMemoryAccess) (rounded : Bool)
    (h : FilesAgreeOn (accessRegion access) files files') :
    ParsedIntegerInput.read files (.memory access rounded) =
      ParsedIntegerInput.read files' (.memory access rounded) := by
  simp only [ParsedIntegerInput.read, readDirectAccess_congr access files files' h]

theorem ParsedIntegerInput.read_fixed (files files' : IntegerRegisterFiles)
    (value : IntegerALU.Bus) :
    ParsedIntegerInput.read files (.fixed value) = ParsedIntegerInput.read files' (.fixed value) :=
  rfl

/-- **Rounding is a pure function of the bus**, so read agreement survives the
`.e` / rounding attribute. -/
theorem ParsedIntegerInput.readWithForwarding_rounding_congr
    (bus bus' : IntegerALU.Bus) (rounded : Bool) (h : bus = bus') :
    ParsedIntegerInput.applyRounding rounded bus =
      ParsedIntegerInput.applyRounding rounded bus' := by
  rw [h]

/-- **Read locality of a forwarding-aware source read.**  When the forwarding
slots agree, the bus read from an operand depends on the register files only
through the operand's own kind: a memory source through its region, a fixed
source not at all, and a forwarding source not at all. -/
theorem ParsedIntegerInput.readWithForwarding_congr_of_read
    (files files' : IntegerRegisterFiles) (slots : Forwarding.Slots)
    (cycle : Fin 4) (input : ParsedIntegerInput)
    (hRead : ParsedIntegerInput.read files input = ParsedIntegerInput.read files' input) :
    ParsedIntegerInput.readWithForwarding files slots cycle input =
      ParsedIntegerInput.readWithForwarding files' slots cycle input := by
  cases input with
  | memory access rounded => simpa [ParsedIntegerInput.readWithForwarding] using hRead
  | fixed value => simpa [ParsedIntegerInput.readWithForwarding] using hRead
  | forward kind rounded => simp [ParsedIntegerInput.readWithForwarding]

/-- **Read locality of a memory source through the forwarding layer.** -/
theorem ParsedIntegerInput.readWithForwarding_memory_congr
    (files files' : IntegerRegisterFiles) (slots : Forwarding.Slots)
    (cycle : Fin 4) (access : DirectMemoryAccess) (rounded : Bool)
    (h : FilesAgreeOn (accessRegion access) files files') :
    ParsedIntegerInput.readWithForwarding files slots cycle (.memory access rounded) =
      ParsedIntegerInput.readWithForwarding files' slots cycle (.memory access rounded) :=
  ParsedIntegerInput.readWithForwarding_congr_of_read files files' slots cycle _
    (ParsedIntegerInput.read_congr_memory files files' access rounded h)


/-! ## 3. Independence of one prepared write

A prepared write is a pure function of the two source reads: the lowered
destination, the mask selection and the flush selection are already fixed in
`accesses`, and the data bus is `unpackALUBus` of the evaluated ALU result.  So
agreement of the two reads gives *the same write record*, hence the same
committed data. -/

/-- **The read footprint of one integer source.**  A memory source reads its
one access region; fixed and forwarding sources read no PE-register word. -/
def ParsedIntegerInput.readsRegion : ParsedIntegerInput → Set WordRef
  | .memory access _ => accessRegion access
  | .fixed _ => ∅
  | .forward _ _ => ∅

theorem ParsedIntegerInput.readsRegion_memory (access : DirectMemoryAccess)
    (rounded : Bool) :
    ParsedIntegerInput.readsRegion (.memory access rounded) = accessRegion access := rfl

theorem ParsedIntegerInput.readsRegion_fixed (value : IntegerALU.Bus) :
    ParsedIntegerInput.readsRegion (.fixed value) = ∅ := rfl

theorem ParsedIntegerInput.readsRegion_forward (kind : Issue.ParsedForward)
    (rounded : Bool) :
    ParsedIntegerInput.readsRegion (.forward kind rounded) = ∅ := rfl

/-- **A source reads at most one region of at most four words.**  An integer
source is either a constant bus, a forwarding slot (both read no PE-register
word), or a single direct access whose region lies in one four-word window. -/
theorem ParsedIntegerInput.readsRegion_shape (input : ParsedIntegerInput) :
    ParsedIntegerInput.readsRegion input = ∅ ∨
      ∃ (access : DirectMemoryAccess) (rounded : Bool),
        input = .memory access rounded ∧
          ParsedIntegerInput.readsRegion input ⊆
            {w | ∃ i : Fin 4, w = ⟨access.bank, advance access.bank access.address i.val⟩} := by
  cases input with
  | memory access rounded =>
      exact Or.inr ⟨access, rounded, rfl, accessRegion_subset_advance access⟩
  | fixed value => exact Or.inl rfl
  | forward kind rounded => exact Or.inl rfl


/-- **A source is read-located by its footprint.**  When the register files
agree on the source's read region, both reads of the forwarding-aware source
return the same result. -/
theorem ParsedIntegerInput.readWithForwarding_congr_of_agree
    (files files' : IntegerRegisterFiles) (slots : Forwarding.Slots)
    (cycle : Fin 4) (input : ParsedIntegerInput)
    (h : FilesAgreeOn (ParsedIntegerInput.readsRegion input) files files') :
    ParsedIntegerInput.readWithForwarding files slots cycle input =
      ParsedIntegerInput.readWithForwarding files' slots cycle input := by
  cases input with
  | memory access rounded =>
      exact ParsedIntegerInput.readWithForwarding_memory_congr files files' slots cycle
        access rounded h
  | fixed value => rfl
  | forward kind rounded => rfl

/-- **The prepared write is determined by its two source reads.** -/
theorem prepareParsedMaskedWriteWithForwarding_congr
    (files files' : IntegerRegisterFiles) (slots : Forwarding.Slots)
    (cycle : Fin 4) (accesses : ParsedMaskedIntegerAccesses) (reduced : Bool)
    (hX : ParsedIntegerInput.readWithForwarding files slots cycle accesses.sourceX =
      ParsedIntegerInput.readWithForwarding files' slots cycle accesses.sourceX)
    (hY : ParsedIntegerInput.readWithForwarding files slots cycle accesses.sourceY =
      ParsedIntegerInput.readWithForwarding files' slots cycle accesses.sourceY) :
    prepareParsedMaskedWriteWithForwarding files slots cycle accesses reduced =
      prepareParsedMaskedWriteWithForwarding files' slots cycle accesses reduced := by
  unfold prepareParsedMaskedWriteWithForwarding
  cases hx : ParsedIntegerInput.readWithForwarding files slots cycle accesses.sourceX with
  | failure =>
      have hx' : ParsedIntegerInput.readWithForwarding files' slots cycle accesses.sourceX =
          .failure := by rw [← hX]; exact hx
      simp [hx, hx']
  | unknown =>
      have hx' : ParsedIntegerInput.readWithForwarding files' slots cycle accesses.sourceX =
          .unknown := by rw [← hX]; exact hx
      simp [hx, hx']
  | ok x =>
      have hx' : ParsedIntegerInput.readWithForwarding files' slots cycle accesses.sourceX =
          .ok x := by rw [← hX]; exact hx
      cases hy : ParsedIntegerInput.readWithForwarding files slots cycle accesses.sourceY with
      | failure =>
          have hy' : ParsedIntegerInput.readWithForwarding files' slots cycle accesses.sourceY =
              .failure := by rw [← hY]; exact hy
          simp [hx, hx', hy, hy']
      | unknown =>
          have hy' : ParsedIntegerInput.readWithForwarding files' slots cycle accesses.sourceY =
              .unknown := by rw [← hY]; exact hy
          simp [hx, hx', hy, hy']
      | ok y =>
          have hy' : ParsedIntegerInput.readWithForwarding files' slots cycle accesses.sourceY =
              .ok y := by rw [← hY]; exact hy
          cases he : Issue.evaluateParsedIntegerAlu accesses.op x y reduced with
          | failure => simp [hx, hx', hy, hy', he]
          | unknown => simp [hx, hx', hy, hy', he]
          | ok output => simp [hx, hx', hy, hy', he]

/-- **Independence of one prepared write.**  If the files agree on the read
regions of both sources, the prepared write is the same record. -/
theorem prepareParsedMaskedWriteWithForwarding_congr_of_agree
    (files files' : IntegerRegisterFiles) (slots : Forwarding.Slots)
    (cycle : Fin 4) (accesses : ParsedMaskedIntegerAccesses) (reduced : Bool)
    (hX : FilesAgreeOn (ParsedIntegerInput.readsRegion accesses.sourceX) files files')
    (hY : FilesAgreeOn (ParsedIntegerInput.readsRegion accesses.sourceY) files files') :
    prepareParsedMaskedWriteWithForwarding files slots cycle accesses reduced =
      prepareParsedMaskedWriteWithForwarding files' slots cycle accesses reduced :=
  prepareParsedMaskedWriteWithForwarding_congr files files' slots cycle accesses reduced
    (ParsedIntegerInput.readWithForwarding_congr_of_agree files files' slots cycle
      accesses.sourceX hX)
    (ParsedIntegerInput.readWithForwarding_congr_of_agree files files' slots cycle
      accesses.sourceY hY)

/-- **The committed data of a prepared write is independent of the input outside
the read regions.**  Both successful preparations produce the same write, so in
particular the same data bus. -/
theorem prepareParsedMaskedWriteWithForwarding_data_congr
    (files files' : IntegerRegisterFiles) (slots : Forwarding.Slots)
    (cycle : Fin 4) (accesses : ParsedMaskedIntegerAccesses) (reduced : Bool)
    (write write' : PreparedParsedMaskedWrite)
    (prepared : prepareParsedMaskedWriteWithForwarding files slots cycle accesses reduced =
      .ok write)
    (prepared' : prepareParsedMaskedWriteWithForwarding files' slots cycle accesses reduced =
      .ok write')
    (hX : FilesAgreeOn (ParsedIntegerInput.readsRegion accesses.sourceX) files files')
    (hY : FilesAgreeOn (ParsedIntegerInput.readsRegion accesses.sourceY) files files') :
    write = write' := by
  rw [prepareParsedMaskedWriteWithForwarding_congr_of_agree files files' slots cycle accesses
    reduced hX hY] at prepared
  exact StepResult.ok.inj (prepared.symm.trans prepared')

/-- The data-bus form of the same independence. -/
theorem prepareParsedMaskedWriteWithForwarding_data_eq_of_agree
    (files files' : IntegerRegisterFiles) (slots : Forwarding.Slots)
    (cycle : Fin 4) (accesses : ParsedMaskedIntegerAccesses) (reduced : Bool)
    (write write' : PreparedParsedMaskedWrite)
    (prepared : prepareParsedMaskedWriteWithForwarding files slots cycle accesses reduced =
      .ok write)
    (prepared' : prepareParsedMaskedWriteWithForwarding files' slots cycle accesses reduced =
      .ok write')
    (hX : FilesAgreeOn (ParsedIntegerInput.readsRegion accesses.sourceX) files files')
    (hY : FilesAgreeOn (ParsedIntegerInput.readsRegion accesses.sourceY) files files') :
    write.data = write'.data := by
  rw [prepareParsedMaskedWriteWithForwarding_data_congr files files' slots cycle accesses
    reduced write write' prepared prepared' hX hY]

/-! ## 4. Independence of a committed write list

Committing the same write list to two files that agree on `R` keeps them
agreeing on `R`: a word of `R` is either written (then both runs store the same
data through the same selection) or untouched (then the old agreement applies). -/

/-- A masked write is a selection between the old and the new word. -/
theorem mergeSelectedWord_congr {old old' new enable : BitVec 32} (h : old = old') :
    mergeSelectedWord old new enable = mergeSelectedWord old' new enable := by rw [h]

/-- The word-level form of `writeWordsMasked`. -/
theorem writeWordsMasked_apply (bank : PEMemory.Bank) (width : PEMemory.Width) (memory : Memory bank)
    (start target : Fin bank.capacity) (data : WordBus) (flags : BitVec 4)
    (longLong : Bool) :
    writeWordsMasked bank width memory start data flags longLong target =
      if within : distance bank start target < count bank width then
        mergeSelectedWord (memory target)
          (data ⟨distance bank start target,
            Nat.lt_of_lt_of_le within (count_le_four bank width)⟩)
          (selectedWordMask flags longLong
            ⟨distance bank start target,
              Nat.lt_of_lt_of_le within (count_le_four bank width)⟩)
      else memory target := by
  by_cases within : distance bank start target < count bank width
  · rw [dite_eq_left within,
      writeWordsMasked_at bank width memory start target data flags longLong within]
  · rw [dite_eq_right within]
    exact writeWordsMasked_preserves_outside bank width memory start target data flags
      longLong (Nat.le_of_not_lt within)

/-- A masked write at one word only depends on the old word at that word. -/
theorem writeWordsMasked_congr (bank : PEMemory.Bank) (width : PEMemory.Width) (memory memory' : Memory bank)
    (start target : Fin bank.capacity) (data : WordBus) (flags : BitVec 4)
    (longLong : Bool) (h : memory target = memory' target) :
    writeWordsMasked bank width memory start data flags longLong target =
      writeWordsMasked bank width memory' start data flags longLong target := by
  rw [writeWordsMasked_apply, writeWordsMasked_apply]
  by_cases within : distance bank start target < count bank width
  · rw [dite_eq_left within, dite_eq_left within, h]
  · rw [dite_eq_right within, dite_eq_right within]
    exact h

/-- Updating the mask-register file leaves every bank word unchanged. -/
theorem wordValue_update_maskRegisters (files : IntegerRegisterFiles)
    (masks : ProofsLean.MNCore.Masks.RegisterFile) (w : WordRef) :
    wordValue { files with maskRegisters := masks } w = wordValue files w := by
  obtain ⟨bank, address⟩ := w
  cases bank <;> rfl

/-- **One commit step is independent of the input outside `R`.**  Committing the
same prepared write to two files that agree on `R` keeps them agreeing on `R`. -/
theorem welcomeCommitStep_word_congr (files files' : IntegerRegisterFiles)
    (write : PreparedParsedMaskedWrite) (R : Set WordRef)
    (hAgree : FilesAgreeOn R files files') (w : WordRef) (hw : w ∈ R) :
    wordValue (welcomeCommitStep files write) w =
      wordValue (welcomeCommitStep files' write) w := by
  obtain ⟨destination, maskUpdate, data, selection⟩ := write
  cases maskUpdate with
  | some update =>
      simp only [welcomeCommitStep]
      rw [wordValue_update_maskRegisters, wordValue_update_maskRegisters]
      exact hAgree w hw
  | none =>
      cases destination with
      | none => simpa [welcomeCommitStep] using hAgree w hw
      | some access =>
          obtain ⟨abank, awidth, aaddress⟩ := access
          obtain ⟨wbank, waddress⟩ := w
          have hW : wordValue files ⟨wbank, waddress⟩ =
              wordValue files' ⟨wbank, waddress⟩ := hAgree ⟨wbank, waddress⟩ hw
          cases wbank <;> cases abank <;>
            simp only [welcomeCommitStep, writeDirectAccessMasked, writeRegisterBankMasked,
              wordValue] <;>
            first
            | exact hW
            | exact writeWordsMasked_congr _ _ _ _ _ _ _ _ _ hW

/-- **A commit list is independent of the input outside `R`.** -/
theorem commitParsedMaskedWrites_congr_on (files files' : IntegerRegisterFiles)
    (writes : List PreparedParsedMaskedWrite) (R : Set WordRef)
    (hAgree : FilesAgreeOn R files files') :
    FilesAgreeOn R (commitParsedMaskedWrites files writes)
      (commitParsedMaskedWrites files' writes) := by
  induction writes generalizing files files' with
  | nil => simpa [commitParsedMaskedWrites] using hAgree
  | cons write rest ih =>
      rw [commitParsedMaskedWrites_cons, commitParsedMaskedWrites_cons]
      exact ih _ _ (fun w hw => welcomeCommitStep_word_congr files files' write R hAgree w hw)




/-! ## 5. The program-level chain

The independence of §4 is lifted to a whole program.  The only per-line input is
a *read footprint* and the statement that agreement on it determines the write
list committed to the observed PE.  Everything else — the lock-step induction,
the growing agreement set and the contrapositive — is proved here once. -/

/-- A line's step is the machine step of the sealed model. -/
def StepTo (line : InstructionLine) (state next : State) : Prop :=
  plusTwoSealedMachine.step line state = some next

theorem stepTo_iff (line : InstructionLine) (state next : State) :
    StepTo line state next ↔ plusTwoSealedMachine.step line state = some next :=
  Iff.rfl

/-- A write list that explains the observed PE's commit in one step. -/
def CommitsWrites (pe : PEId) (state next : State)
    (writes : List PreparedParsedMaskedWrite) : Prop :=
  next.peRegisters pe = commitParsedMaskedWrites (state.peRegisters pe) writes

/-- **Per-line write determination at one PE.**  Two states that agree on the
line's read footprint and both take the line to a next state commit the *same*
write list to `pe`.  For the plain integer executor this is §3: the prepared
writes are functions of the source reads, and a line's write list is the
concatenation of its prepared writes. -/
def LineDeterminedAt (footprint : InstructionLine → State → Set WordRef)
    (pe : PEId) (line : InstructionLine) : Prop :=
  ∀ (s s' next next' : State),
    FilesAgreeOn (footprint line s ∪ footprint line s')
      (s.peRegisters pe) (s'.peRegisters pe) →
    StepTo line s next → StepTo line s' next' →
    ∃ writes writes',
      CommitsWrites pe s next writes ∧ CommitsWrites pe s' next' writes' ∧ writes = writes'

/-- Per-line write determination at every PE. -/
def LineDeterminedOn (footprint : InstructionLine → State → Set WordRef)
    (line : InstructionLine) : Prop :=
  ∀ pe, LineDeterminedAt footprint pe line

/-- The uniform form of the per-line contract. -/
def LineWriteDetermined (footprint : InstructionLine → State → Set WordRef) : Prop :=
  ∀ line, LineDeterminedOn footprint line

/-- **The program chain.**  If every line of a program is write-determined and no
line's footprint meets the difference set `D`, then two executions from states
that agree outside `D` end agreeing outside `D`. -/
theorem execute_agreeOutside_of_determined
    (footprint : InstructionLine → State → Set WordRef)
    (program : List InstructionLine) (pe : PEId) (D : Set WordRef)
    (determined : ∀ line ∈ program, LineDeterminedAt footprint pe line)
    (avoids : ∀ line ∈ program, ∀ s s' : State,
      footprint line s ∪ footprint line s' ⊆ Dᶜ)
    (s0 s0' : State) (hInit : FilesAgreeOn Dᶜ (s0.peRegisters pe) (s0'.peRegisters pe))
    (final final' : State)
    (run : ProofsLean.execute plusTwoSealedMachine program s0 = some final)
    (run' : ProofsLean.execute plusTwoSealedMachine program s0' = some final') :
    FilesAgreeOn Dᶜ (final.peRegisters pe) (final'.peRegisters pe) := by
  induction program generalizing s0 s0' with
  | nil =>
      simp only [ProofsLean.execute] at run run'
      have same : final = s0 := (Option.some.inj run).symm
      have same' : final' = s0' := (Option.some.inj run').symm
      rw [same, same']
      exact hInit
  | cons line rest ih =>
      rw [ProofsLean.execute.eq_2] at run run'
      cases hstep : plusTwoSealedMachine.step line s0 with
      | none => rw [hstep] at run; simp at run
      | some middle =>
          rw [hstep] at run
          simp only [Option.bind_some] at run
          cases hstep' : plusTwoSealedMachine.step line s0' with
          | none => rw [hstep'] at run'; simp at run'
          | some middle' =>
              rw [hstep'] at run'
              simp only [Option.bind_some] at run'
              have agrees : FilesAgreeOn (footprint line s0 ∪ footprint line s0')
                  (s0.peRegisters pe) (s0'.peRegisters pe) :=
                hInit.mono (avoids line (by simp) s0 s0')
              obtain ⟨writes, writes', commit, commit', sameWrites⟩ :=
                determined line (by simp) s0 s0' middle middle' agrees hstep hstep'
              have hMiddle : FilesAgreeOn Dᶜ (middle.peRegisters pe)
                  (middle'.peRegisters pe) := by
                rw [commit, commit']
                subst sameWrites
                exact commitParsedMaskedWrites_congr_on _ _ writes Dᶜ hInit
              exact ih (fun item mem => determined item (List.mem_cons_of_mem _ mem))
                (fun item mem s s' => avoids item (List.mem_cons_of_mem _ mem) s s')
                middle middle' hMiddle run run'

/-- **The usable contrapositive.**  If two executions of the same program end
with different values at an observed word `w` that is not in the difference set
`D`, while the initial states agreed outside `D`, then some line of the program
has a read footprint that meets `D`.  This is the exact form the floor argument
uses: a differing output word can only come from a line that read a differing
input word. -/
theorem exists_footprint_meets_of_output_ne
    (footprint : InstructionLine → State → Set WordRef)
    (program : List InstructionLine) (pe : PEId) (D : Set WordRef)
    (determined : ∀ line ∈ program, LineDeterminedAt footprint pe line)
    (s0 s0' : State) (hInit : FilesAgreeOn Dᶜ (s0.peRegisters pe) (s0'.peRegisters pe))
    (final final' : State)
    (run : ProofsLean.execute plusTwoSealedMachine program s0 = some final)
    (run' : ProofsLean.execute plusTwoSealedMachine program s0' = some final')
    (w : WordRef) (hw : w ∉ D)
    (different : wordValue (final.peRegisters pe) w ≠
      wordValue (final'.peRegisters pe) w) :
    ∃ line ∈ program, ∃ s s' : State, ∃ v : WordRef,
      v ∈ D ∧ (v ∈ footprint line s ∨ v ∈ footprint line s') := by
  by_contra none
  have avoids : ∀ line ∈ program, ∀ s s' : State,
      footprint line s ∪ footprint line s' ⊆ Dᶜ := by
    intro line mem s s' v hv
    by_contra outside
    exact none ⟨line, mem, s, s', v, by simpa using outside, hv⟩
  exact different (execute_agreeOutside_of_determined footprint program pe D determined
    avoids s0 s0' hInit final final' run run' w hw)

/-! ### Concrete instances of the per-line contract

A line whose step leaves the PE register files untouched is determined by the
empty footprint.  `nop` lines are the basic case: they only advance the hazard
clock (and may fail on an uncompleted wait tag, in which case there is no next
state at all). -/

theorem commitParsedMaskedWrites_nil (files : IntegerRegisterFiles) :
    commitParsedMaskedWrites files [] = files := rfl

/-- A line that does not touch the register files is determined by any footprint. -/
theorem lineDeterminedAt_of_frame (footprint : InstructionLine → State → Set WordRef)
    (line : InstructionLine)
    (frame : ∀ state next : State, StepTo line state next →
      next.peRegisters = state.peRegisters) :
    ∀ pe, LineDeterminedAt footprint pe line := by
  intro pe s s' next next' agrees step step'
  refine ⟨[], [], ?_, ?_, rfl⟩
  · show next.peRegisters pe = commitParsedMaskedWrites (s.peRegisters pe) []
    rw [frame s next step, commitParsedMaskedWrites_nil]
  · show next'.peRegisters pe = commitParsedMaskedWrites (s'.peRegisters pe) []
    rw [frame s' next' step', commitParsedMaskedWrites_nil]

/-- `nop` lines leave the PE register files untouched. -/
theorem nop_step_peRegisters_frame (count : {n : Nat // 0 < n})
    (wait : Option (Fin 256)) (state next : State)
    (step : StepTo (InstructionLine.nop count wait) state next) :
    next.peRegisters = state.peRegisters := by
  have stepEq : plusTwoSealedMachine.step (InstructionLine.nop count wait) state =
      some next := step
  cases h : executeNormalizedLine (InstructionLine.nop count wait).toNormalizedLine state with
  | ok next' =>
      have same : next' = next := by
        simpa only [plusTwoSealedMachine, h, Option.some.injEq] using stepEq
      subst same
      exact executeNormalizedLine_nop_peRegisters count.val wait state next' h
  | unknown => simp [plusTwoSealedMachine, h] at stepEq
  | failure => simp [plusTwoSealedMachine, h] at stepEq

/-- **`nop` lines satisfy the contract.** -/
theorem nop_lineDeterminedOn (footprint : InstructionLine → State → Set WordRef)
    (count : {n : Nat // 0 < n}) (wait : Option (Fin 256)) :
    LineDeterminedOn footprint (InstructionLine.nop count wait) :=
  lineDeterminedAt_of_frame footprint _
    (fun _ _ step => nop_step_peRegisters_frame count wait _ _ step)


/-! ## 6. The `2.plus-two` application

The floor argument of §6 of `PlusTwoBoundSix.lean` is input-parametric: output
word `k` must carry `input k + 2`, so changing input word `j` must change output
word `j`.  The kernel turns that into a statement about reads:

* the two initial states differ exactly at the LM0 word of input `j` (§6.1);
* a prepared write that avoids that word is unchanged (§6.2);
* so a correct program must contain a line whose read footprint meets the word
  of input `j` (§6.3).

§6.3 is stated for an abstract read footprint and the per-line determination
contract of §5; `PlusTwoWriteDetermination` below is the exact executor
obligation that remains to be discharged for the real `.pe` step. -/

/-- The LM0 word holding input `j`: the low word of the `j`-th even Long slot. -/
def plusTwoInputWord (j : Fin 20) : WordRef :=
  ⟨.lm0, plusTwoLowAddress j⟩

theorem plusTwoInputWord_bank (j : Fin 20) : (plusTwoInputWord j).1 = .lm0 := rfl

/-- The LM1 word carrying the low half of output `j`. -/
def plusTwoOutputWord (j : Fin 20) : WordRef :=
  ⟨.lm1, plusTwoLowAddress j⟩

/-- The initial files only depend on the input through the LM0 file. -/
theorem plusTwoInitialPERegisters_lm1 (input : PlusTwoWords) :
    (plusTwoInitialPERegisters input).lm1 = zeroInitialPERegisterFiles.lm1 := rfl

theorem plusTwoInitialPERegisters_grf0 (input : PlusTwoWords) :
    (plusTwoInitialPERegisters input).grf0 = zeroInitialPERegisterFiles.grf0 := rfl

theorem plusTwoInitialPERegisters_grf1 (input : PlusTwoWords) :
    (plusTwoInitialPERegisters input).grf1 = zeroInitialPERegisterFiles.grf1 := rfl

theorem plusTwoInitialPERegisters_t (input : PlusTwoWords) :
    (plusTwoInitialPERegisters input).t = zeroInitialPERegisterFiles.t := rfl

theorem plusTwoInitialPERegisters_maskRegisters (input : PlusTwoWords) :
    (plusTwoInitialPERegisters input).maskRegisters =
      zeroInitialPERegisterFiles.maskRegisters := rfl

/-- **§6.1 — the initial states differ only at the input word.**  Two inputs that
agree away from index `j` give register files that agree on every word except
the LM0 word of input `j`. -/
theorem plusTwoInitialPERegisters_agree_outside (input input' : PlusTwoWords)
    (j : Fin 20) (agree : ∀ k, k ≠ j → input k = input' k) :
    FilesAgreeOn ({plusTwoInputWord j} : Set WordRef)ᶜ
      (plusTwoInitialPERegisters input) (plusTwoInitialPERegisters input') := by
  intro w hw
  obtain ⟨bank, address⟩ := w
  cases bank with
  | lm0 =>
      show plusTwoInitialLm0 input address = plusTwoInitialLm0 input' address
      by_cases isJ : address = plusTwoLowAddress j
      · exact absurd (by show (⟨PEMemory.Bank.lm0, address⟩ : WordRef) ∈
          ({plusTwoInputWord j} : Set WordRef); rw [isJ]; exact Set.mem_singleton _) hw
      · unfold plusTwoInitialLm0
        by_cases inside : address.val % 2 = 1 ∧ address.val / 2 < 20
        · rw [dite_eq_left inside, dite_eq_left inside]
          apply agree
          intro sameIndex
          apply isJ
          apply Fin.ext
          have values := congrArg Fin.val sameIndex
          have split := Nat.div_add_mod address.val 2
          simp only [plusTwoLowAddress] at values ⊢
          omega
        · rw [dite_eq_right inside, dite_eq_right inside]
  | lm1 => rfl
  | grf0 => rfl
  | grf1 => rfl
  | t => rfl

/-- **§6.2 — a prepared write avoiding input word `j` is unchanged.**  This is
the independence of §3 instantiated at the `2.plus-two` initial files: if both
sources of a prepared write avoid the LM0 word of input `j`, changing only
`input j` does not change the write. -/
theorem plusTwo_preparedWrite_input_independent
    (input input' : PlusTwoWords) (j : Fin 20)
    (agree : ∀ k, k ≠ j → input k = input' k)
    (slots : Forwarding.Slots) (cycle : Fin 4)
    (accesses : ParsedMaskedIntegerAccesses) (reduced : Bool)
    (hX : plusTwoInputWord j ∉ ParsedIntegerInput.readsRegion accesses.sourceX)
    (hY : plusTwoInputWord j ∉ ParsedIntegerInput.readsRegion accesses.sourceY) :
    prepareParsedMaskedWriteWithForwarding (plusTwoInitialPERegisters input) slots cycle
        accesses reduced =
      prepareParsedMaskedWriteWithForwarding (plusTwoInitialPERegisters input') slots cycle
        accesses reduced := by
  apply prepareParsedMaskedWriteWithForwarding_congr_of_agree
  · exact FilesAgreeOn.mono
      (plusTwoInitialPERegisters_agree_outside input input' j agree)
      (fun w hw same => hX (same ▸ hw))
  · exact FilesAgreeOn.mono
      (plusTwoInitialPERegisters_agree_outside input input' j agree)
      (fun w hw same => hY (same ▸ hw))

/-- The output word of `j` is not the input word of `j`: outputs live in LM1,
the input in LM0. -/
theorem plusTwoOutputWord_not_inputWord (j : Fin 20) :
    plusTwoOutputWord j ≠ plusTwoInputWord j := by
  intro same
  have banks : (PEMemory.Bank.lm1) = (PEMemory.Bank.lm0) := congrArg Sigma.fst same
  cases banks

/-- **§6.3 — the chain instantiated at `2.plus-two`.**  If every line of a
program is write-determined on a footprint that avoids the input word of `j`,
then two inputs differing only at `j` produce the same PE-0 register words. -/
theorem plusTwo_execute_agreeOutside
    (footprint : InstructionLine → State → Set WordRef)
    (program : List InstructionLine) (j : Fin 20)
    (determined : ∀ line ∈ program, LineDeterminedAt footprint plusTwoPE line)
    (avoids : ∀ line ∈ program, ∀ s s' : State,
      footprint line s ∪ footprint line s' ⊆ ({plusTwoInputWord j} : Set WordRef)ᶜ)
    (input input' : PlusTwoWords) (agree : ∀ k, k ≠ j → input k = input' k)
    (final final' : State)
    (run : ProofsLean.execute plusTwoSealedMachine program
      (plusTwoSpec.initial input) = some final)
    (run' : ProofsLean.execute plusTwoSealedMachine program
      (plusTwoSpec.initial input') = some final') :
    FilesAgreeOn ({plusTwoInputWord j} : Set WordRef)ᶜ
      (final.peRegisters plusTwoPE) (final'.peRegisters plusTwoPE) :=
  execute_agreeOutside_of_determined footprint program plusTwoPE
    ({plusTwoInputWord j} : Set WordRef) determined avoids
    (plusTwoSpec.initial input) (plusTwoSpec.initial input')
    (plusTwoInitialPERegisters_agree_outside input input' j agree) final final' run run'

/-- **The headline residual reduction.**  A correct `2.plus-two` program needs,
for every input index `j`, a line whose read footprint contains the LM0 word of
input `j`.  This is the input-parametric statement that the counting route of
`PlusTwoBoundSix.lean` could not state: output `j` is `input j + 2`, a function
of input `j`, so some line must read input `j`.

The only unproved input is `determined`, the per-line write determination of the
real `.pe` step; §3–§4 discharge it for prepared writes, and
`PlusTwoWriteDetermination` names the exact executor obligation. -/
theorem plusTwo_output_forces_footprint_meets
    (footprint : InstructionLine → State → Set WordRef)
    (program : List InstructionLine)
    (determined : ∀ line ∈ program, LineDeterminedAt footprint plusTwoPE line)
    (correct : ProofsLean.Correct plusTwoSealedMachine plusTwoSpec program)
    (j : Fin 20) :
    ∃ line ∈ program, ∃ s s' : State,
      plusTwoInputWord j ∈ footprint line s ∨ plusTwoInputWord j ∈ footprint line s' := by
  -- two admissible inputs differing only at `j`
  let zeroInput : PlusTwoWords := fun _ => 0
  let oneInput : PlusTwoWords := fun k => if k = j then 1 else 0
  have zeroAdmissible : plusTwoSpec.admissible zeroInput := by
    intro k
    simp [zeroInput]
  have oneAdmissible : plusTwoSpec.admissible oneInput := by
    intro k
    by_cases isJ : k = j
    · simp [oneInput, isJ]
    · simp [oneInput, isJ]
  have agree : ∀ k, k ≠ j → zeroInput k = oneInput k := by
    intro k other
    simp [zeroInput, oneInput, other]
  obtain ⟨final, run, post⟩ := correct.2 zeroInput zeroAdmissible
  obtain ⟨final', run', post'⟩ := correct.2 oneInput oneAdmissible
  have initialAgree : FilesAgreeOn ({plusTwoInputWord j} : Set WordRef)ᶜ
      ((plusTwoSpec.initial zeroInput).peRegisters plusTwoPE)
      ((plusTwoSpec.initial oneInput).peRegisters plusTwoPE) :=
    plusTwoInitialPERegisters_agree_outside zeroInput oneInput j agree
  have different : wordValue (final.peRegisters plusTwoPE) (plusTwoOutputWord j) ≠
      wordValue (final'.peRegisters plusTwoPE) (plusTwoOutputWord j) := by
    have low := (post j).2
    have low' := (post' j).2
    simp only [plusTwoOutputWord, wordValue_lm1]
    rw [low, low']
    simp [zeroInput, oneInput]
  have outside : plusTwoOutputWord j ∉ ({plusTwoInputWord j} : Set WordRef) := by
    intro mem
    have same := Set.mem_singleton_iff.mp mem
    exact plusTwoOutputWord_not_inputWord j same
  obtain ⟨line, mem, s, s', v, inD, inFootprint⟩ :=
    exists_footprint_meets_of_output_ne footprint program plusTwoPE
      ({plusTwoInputWord j} : Set WordRef) determined
      (plusTwoSpec.initial zeroInput)
      (plusTwoSpec.initial oneInput)
      (by simpa [plusTwoSpec, plusTwoInitialState] using
        plusTwoInitialPERegisters_agree_outside zeroInput oneInput j agree)
      final final' run run' (plusTwoOutputWord j) outside different
  have vSame : v = plusTwoInputWord j := Set.mem_singleton_iff.mp inD
  subst vSame
  exact ⟨line, mem, s, s', inFootprint⟩


/-! ### The concrete read footprint of a `.pe` line

The hazard-event lowering of `ParsedIntegerStep` already resolves each source
operand's direct accesses for the four PE cycles.  Its non-write events are the
syntactic candidate for a `.pe` line's read footprint; `accessRegion` turns each
of them into at most four register words. -/

/-- The direct accesses a `.pe` line's source operands resolve to, across the
four PE cycles, as reported by the hazard-event lowering. -/
def peLineSourceAccesses (expressions : List NormalizedExpr) (pe : PEId)
    (state : State) : List DirectMemoryAccess :=
  let control := parsedPEHazardControl state pe
  ((expressions.map fun expression =>
      (ParsedExpr.toTimedPEHazardEvents? expression.toParsed control).getD []).flatten).filterMap
    fun event => if event.write then none else some event.access

/-- **The concrete read footprint of a line.**  For a `.pe` line it is the union
of the access regions of the line's source operands; for a `nop` or `mv` line it
is empty at the PE-register level. -/
def plusTwoLineFootprint (line : InstructionLine) (state : State) : Set WordRef :=
  match line with
  | .pe expressions =>
      {w | ∃ access ∈ peLineSourceAccesses expressions plusTwoPE state,
        w ∈ accessRegion access}
  | _ => ∅

theorem plusTwoLineFootprint_nop (count : {n : Nat // 0 < n})
    (wait : Option (Fin 256)) (state : State) :
    plusTwoLineFootprint (.nop count wait) state = ∅ := rfl

theorem plusTwoLineFootprint_mem (expressions : List NormalizedExpr) (state : State)
    {w : WordRef} :
    w ∈ plusTwoLineFootprint (.pe expressions) state ↔
      ∃ access ∈ peLineSourceAccesses expressions plusTwoPE state, w ∈ accessRegion access :=
  Iff.rfl

/-- **The residual, specialised to the concrete footprint.**  Every line commits
the same PE-0 write list to two states that agree on the region its source
operands resolve to.  §3–§4 discharge this for one prepared write and for a
commit list; what remains is the composition over the line's four cycles and its
producer stages, which must additionally track the forwarding, mask-register,
PE-context, mask-directive and hazard-clock channels of the `.pe` step. -/
def PlusTwoWriteDetermination : Prop :=
  ∀ line, LineDeterminedAt plusTwoLineFootprint plusTwoPE line

/-- **The concrete form of the headline reduction.**  A correct `2.plus-two`
program has, for every input index `j`, a line whose *concrete* read footprint
(the hazard-event lowering of its sources) contains the LM0 word of input `j`. -/
theorem plusTwo_output_forces_concrete_read
    (program : List InstructionLine)
    (determined : ∀ line ∈ program, LineDeterminedAt plusTwoLineFootprint plusTwoPE line)
    (correct : ProofsLean.Correct plusTwoSealedMachine plusTwoSpec program)
    (j : Fin 20) :
    ∃ line ∈ program, ∃ s s' : State,
      plusTwoInputWord j ∈ plusTwoLineFootprint line s ∨
        plusTwoInputWord j ∈ plusTwoLineFootprint line s' :=
  plusTwo_output_forces_footprint_meets plusTwoLineFootprint program determined correct j

/-- The same reduction from the single named residual. -/
theorem plusTwo_output_forces_concrete_read_of_determination
    (determination : PlusTwoWriteDetermination)
    (program : List InstructionLine)
    (correct : ProofsLean.Correct plusTwoSealedMachine plusTwoSpec program)
    (j : Fin 20) :
    ∃ line ∈ program, ∃ s s' : State,
      plusTwoInputWord j ∈ plusTwoLineFootprint line s ∨
        plusTwoInputWord j ∈ plusTwoLineFootprint line s' :=
  plusTwo_output_forces_footprint_meets plusTwoLineFootprint program
    (fun line _ => determination line) correct j

/-! ### The executor bridge

The bridge from a pinned commit list (as produced by
`executeIntegerProducerLineAtPECore_peRegisters_commit_list`) to output-word
agreement.  This is the shape every per-family provenance lemma has to feed. -/

/-- **Commit-list bridge.**  If two successful lines both commit the *same*
write list to `pe`'s file, then their PE files agree on every word set on which
the two input files agreed. -/
theorem peRegisters_congr_of_commitList
    (state state' next next' : State) (pe : PEId)
    (writes : List PreparedParsedMaskedWrite) (R : Set WordRef)
    (commit : next.peRegisters pe =
      commitParsedMaskedWrites (state.peRegisters pe) writes)
    (commit' : next'.peRegisters pe =
      commitParsedMaskedWrites (state'.peRegisters pe) writes)
    (hAgree : FilesAgreeOn R (state.peRegisters pe) (state'.peRegisters pe)) :
    FilesAgreeOn R (next.peRegisters pe) (next'.peRegisters pe) := by
  rw [commit, commit']
  exact commitParsedMaskedWrites_congr_on _ _ writes R hAgree



/-- **A program that never reads input `j` is incorrect.**  This is the
contrapositive of the headline reduction in directly usable form: every correct
`2.plus-two` program must contain, for every index `j`, a line whose read
footprint contains the LM0 word of input `j`. -/
theorem plusTwo_not_correct_of_footprint_avoids
    (program : List InstructionLine)
    (determined : ∀ line ∈ program, LineDeterminedAt plusTwoLineFootprint plusTwoPE line)
    (j : Fin 20)
    (avoids : ∀ line ∈ program, ∀ s s' : State,
      plusTwoInputWord j ∉ plusTwoLineFootprint line s ∧
        plusTwoInputWord j ∉ plusTwoLineFootprint line s') :
    ¬ ProofsLean.Correct plusTwoSealedMachine plusTwoSpec program := by
  intro correct
  obtain ⟨line, mem, s, s', meets⟩ :=
    plusTwo_output_forces_concrete_read program determined correct j
  rcases meets with inside | inside
  · exact (avoids line mem s s').1 inside
  · exact (avoids line mem s s').2 inside

/-- **The counting remark.**  `2.plus-two` has twenty input words, and a correct
program must read every one of them (previous theorem).  A `.pe` line's footprint
is the union of at most `2 × 4` access regions of at most four words each, one
per source operand and cycle, so this reduction alone does not bound the line
count: the five-line floor still needs the computed-slot count of
`PlusTwoBoundSix.lean` §5 composed with this input-parametric reduction.  The
statement below records the exact shape of that composition: a program is
correct only if, for every `j`, some line reads input `j`. -/
theorem plusTwo_correct_imp_forall_input_read
    (program : List InstructionLine)
    (determined : ∀ line ∈ program, LineDeterminedAt plusTwoLineFootprint plusTwoPE line)
    (correct : ProofsLean.Correct plusTwoSealedMachine plusTwoSpec program) :
    ∀ j : Fin 20, ∃ line ∈ program, ∃ s s' : State,
      plusTwoInputWord j ∈ plusTwoLineFootprint line s ∨
        plusTwoInputWord j ∈ plusTwoLineFootprint line s' :=
  fun j => plusTwo_output_forces_concrete_read program determined correct j


/-! ## 7. What is proved, and the exact residual

**Proved here (no hypotheses).**

* §1–§2: one direct access is one region of at most four words; reads are
  unchanged outside it; a differing read bus exhibits a differing word in it.
  Every integer source operand is a memory access, a fixed bus, or a forwarding
  slot, and only the first reads PE-register words.
* §3: a prepared write is the same record whenever its two source reads agree;
  in particular its committed `data` bus is the same.
* §4: committing the same write list preserves agreement on any word set.
* §5: the program chain and its contrapositive.
* §6: the `2.plus-two` instantiation.  Correctness of a program forces, for
  every input index `j`, a line whose read footprint contains the LM0 word of
  input `j`; a program that never reads input `j` is incorrect.

**The single residual.**

`PlusTwoWriteDetermination` (`∀ line, LineDeterminedAt plusTwoLineFootprint
plusTwoPE line`): a successful line's committed PE-0 write list is a function of
the words its sources read.  The kernel reduces the floor argument to this
statement and nothing else.  Two things are needed to discharge it:

1. *Composition over a line.*  §3 proves the prepared-write case and §4 the
   commit-list case; a line's write list is the concatenation of its cycles'
   prepared writes (`prepareParsedALUProducerLineCycles`,
   `prepareParsedIntegerMatrixReadLineCycles`), so this is an induction over the
   four cycles and the expression list.  The destination and mask selection of
   each write are already fixed by `accesses`, hence independent of the reads.
2. *Auxiliary channels.*  The `.pe` step also consults the forwarding slots,
   the per-PE mask registers, the BAR/T context, the mask directive and the
   hazard clock.  `plusTwoLineFootprint` covers only the PE-register words, so
   the determination proof must also show that those channels agree, or be
   restated over a richer invariant (forwarding agreement is itself produced by
   the same reads, so this is a joint induction with the chain).

**How the residual meets the floor.**  Combined with the slot count of
`PlusTwoBoundSix.lean` §5, the residual says each of the twenty output words
needs a line that reads its input word; the slot count says a line can compute
at most four outputs and that creating the constant `2` costs computed slots.
That composition — not this module — is the step that yields `LowerBound 6`.

No `LowerBound 6` is claimed. -/

end ProofsLean.MNCore
