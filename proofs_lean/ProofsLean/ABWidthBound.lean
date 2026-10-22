import ProofsLean.ABLowerBound
import ProofsLean.WelcomeFlagFreePlain
import ProofsLean.WelcomeL12Shape

/-! # `1.a-b` by width/count: the exact bound is `16`, not `8`

## The question

`ProofsLean/ABLowerBound.lean` reduces `LowerBound abSealedMachine abSpec 2` to
refuting every accepted `.pe` one-liner (`AbPEUnrefuted`).  The existing value
kernel `ab_not_correct_of_narrowAtOnes` refutes a line whose PE 0 write list at
the input `A = 1.0, B = 0` is covered by at most four windows of at most two
words — a *destination shape* that has to be produced per family and per input
state.  This module tests the cheaper hypothesis:

> a single expression writes at most eight `.lm1` words at PE 0, so one line
> cannot write the sixteen observed words, and one untouched word (initial `0`
> against the non-zero target) refutes the line.

## Answer: the hypothesis is **false**, and `16` is sharp

A `.lm1` destination is a `Region` of width `1`, `2` or `4` words
(`PEMemory.Width.word / long / double`), and each of the four cycles writes the
*same* destination operand at the cycle's own address.  So one expression writes
`4 * count .lm1 w` words at PE 0:

| width | words per write | words per expression |
|---|---|---|
| `.word`   | 1 | 4 |
| `.long`   | 2 | 8 |
| `.double` | 4 | **16** |

The bound `8` therefore holds exactly for `.word`/`.long` destinations.  A
`.double` (two-long-word) destination — the family the official tools measure as
"2LW IALU destination: 8 computed + 8 pass-through values" — writes **all
sixteen** observed words, so *no* width/count bound below `16` can refute it and
the untouched-word argument is unavailable there.

This is proved concretely below:

* `abWidthDouble_linePrepDestinations` — the `iinc` row of
  `ProofsLean/WelcomeComplete.lean` with its `.long` destination replaced by a
  `.double` one at the four aligned addresses `0, 4, 8, 12` produces, by kernel
  computation, **exactly four `.lm1 .double` writes at `0, 4, 8, 12`**;
* `abWidthDouble_linePrepWrites` — that list has `lm1WriteCount = 4` and
  `lm1WriteWords = 16` (and every one of its writes has the all-ones long-long
  selection, so all four words of each write are written).  The list is
  committed verbatim by the integer stage
  (`StageCommitSpecific.parsedIntegerMatrixReadLineFourCycleStep_commit_eq`:
  the four-cycle step's register file is `commitParsedMaskedWrites files
  prepared.1`), so the sixteen words are written by the executor, not by a
  hand-made list;
* `abWidthDouble_covers_all` — the four windows `0, 4, 8, 12` cover every
  observed word `0..15`;
* `l1ToPEWrites_double_budget` — the same `16` for the L1BM→PE family *by
  construction*: `l1ToPEWrites .double addresses selections` is always four
  `.lm1 .double` writes.

## What is proved here

* the **exact arithmetic** of one line's `.lm1` width: a write list with at
  most four `.lm1` writes, all of the static width `w`, writes at most
  `4 * count .lm1 w` words, and `4 * count .lm1 w ≤ 8` iff `w ≠ .double`
  (`lm1WriteWords_le_count_mul`, `four_mul_count_le_eight`);
* the **general counting kernel** `exists_uncovered_of_totalWidth`: a write list
  of total `.lm1` width below `16` leaves an observed word untouched — the
  widest form of the narrow argument (no windows, no addresses, no state
  transfer);
* the **value kernel** `ab_not_correct_of_lm1TotalWidth` at the input
  `A = 1.0, B = 0`: a one-line `.pe` program whose PE 0 file is the commit of a
  write list of total `.lm1` width below `16` is incorrect;
* the **witnesses** that the hypothesis fails for `.double` destinations
  (`abWidthDouble_linePrepDestinations`, `abWidthDouble_linePrepWrites`,
  `abWidthDouble_covers_all`, `l1ToPEWrites_double_budget`,
  `abWidthBound_eight_false`).

## Where each family's count bound already lives in the tree

The count half `≤ 4` is *not* new work; it is already proved per family, and the
statements take the write state as an arbitrary parameter (the *read* state is
the all-zero one in the shape lemmas, which is exactly why the `.double` case
needs new data work):

| family | lemma giving `≤ 4` writes and the static width |
|---|---|
| plain ALU (all 9 cycle branches) | `Lm1ChunkFacts` (`WelcomePlainStep.lean`): at most one `.lm1` write per cycle; the four chunks are assembled by `lm1WritesShape_of_chunks` |
| `.matrixRead` | `prepareParsedMatrixReadExprCycles_lm1Facts` (`≤ 4`, `Lm1WriteFacts w`) |
| float MAU (all precisions) | `executeParsedFloatMAUCyclesAtPE_widthCount` (`≤ cycles.length = 4`, `Lm1WidthFacts w`) |
| matrix MAU | `executeParsedMatrixMAUProducer_widthCount` (`≤ 4`, `Lm1WidthFacts w`) |
| block float | `executeParsedBlockFloatAtMAB_runCycles_lm1Facts_read` (`≤ cycles.length = 4`) |
| `.l1bm` → PE | `l1ToPEWrites_length` (**exactly** 4, one static width per list) |
| msl/msr destination writer | `writeParsedMslMsrDestination?_widthCount` (one write per destination, `≤ 1` per cycle) |
| `.matrixWrite`, `.l2bm`, the five middle stages of a row without an `.lm1` destination | `Lm1FreePreparedWrites` / the stage commitments of `WelcomeStageProvenance.lean`, so `0` |
| `noforward`, `wait` | empty write lists |

A legal line (`writesUnique`) has at most one `.lm1`-writing row, so the
line's `.lm1` writes come from that row's four cycles.  The family-independent
bound is therefore `4 * count .lm1 w ∈ {4, 8, 16}`, and it is `16` — not
`< 16` — for every family that accepts a `.double` `.lm1` destination.  It is
`8` for `.word`/`.long` destinations, and for those
`ab_not_correct_of_lm1WidthNotDouble` closes the line with no copy analysis at
all.

## The remaining `.double` case, and the cheapest route through it

At the input `A = 0, B = 1.0` (target `0xBF800000 = -1.0`) every initial
memory/register word is `0` or `0x3F800000`, and the `.fixed` source constants
are small; so bus words `2, 3` of any prepared write — the low long word, which
is `0` for the MAU/block-float/relu buses (`doubleMAUVectorBus_low`), the
source read's low long word for the IALU (`evaluateBus`'s `low = x.low`), and
block-memory data (`0` initially) for `.matrixRead`/`.l1bm` — are never
`0xBF800000`.  Covering all sixteen observed words with four 4-aligned
`.double` windows forces the windows `0, 4, 8, 12` (`abWidthDouble_covers_all`
is the positive half), hence the eight words at addresses
`2, 3, 6, 7, 10, 11, 14, 15` are written from data words `2, 3` (or keep their
initial `0` when the selection gates them off) and are wrong.  That turns the
`.double` case into a *single generic read-value lemma*, not a per-family copy
analysis; the destination and selection geometry it needs is already proved
above (`abWidthDouble_linePrepDestinations`, `abWidthDouble_linePrepSelections`).

## What is deliberately *not* claimed

No `LowerBound`, no `Optimal`.  The `.double` case still needs a data argument:
its four writes carry `4` bus words each, but only the first long word (bus
words `0, 1`) is computed; bus words `2, 3` are `0` (MAU) or the source read's
low long word (IALU), so the sixteen written words contain at most eight
computed values.  Turning "at most eight computed" into a refutation needs the
*data* facts (bus words `2, 3`) at the non-zero input, which is what
`ABLowerBound.lean`'s section 12 records as the missing executor link; the
section above reduces those facts to a single generic read-value lemma rather
than a per-family copy analysis.

No `sorry`, no `admit`, no `native_decide`, no new axioms, and no existing
module is edited by this file.
-/

namespace ProofsLean.MNCore

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

open Issue
open PEMemory

/-! ## 1. The `.lm1` word budget of a prepared write list -/

/-- The number of words a prepared write spends on `.lm1`, read off its
destination: `count .lm1 width` for an `.lm1` destination and `0` otherwise. -/
def lm1WidthOfDestination : Option DirectMemoryAccess → Nat
  | some access =>
      if access.bank == PEMemory.Bank.lm1 then count access.bank access.width else 0
  | none => 0

/-- The `.lm1` indicator of a prepared destination. -/
def lm1CountOfDestination : Option DirectMemoryAccess → Nat
  | some access => if access.bank == PEMemory.Bank.lm1 then 1 else 0
  | none => 0

/-- The total number of `.lm1` words a prepared write list writes (a word count
with multiplicity: two writes covering the same word count twice). -/
def lm1WriteWords (writes : List PreparedParsedMaskedWrite) : Nat :=
  (writes.map (fun write => lm1WidthOfDestination write.destination)).sum

/-- The number of `.lm1` writes of a prepared list. -/
def lm1WriteCount (writes : List PreparedParsedMaskedWrite) : Nat :=
  (writes.map (fun write => lm1CountOfDestination write.destination)).sum

theorem lm1WidthOfDestination_lm1 (width : PEMemory.Width)
    (address : Fin Bank.lm1.capacity) :
    lm1WidthOfDestination (some ⟨PEMemory.Bank.lm1, width, address⟩) =
      count PEMemory.Bank.lm1 width := by
  simp [lm1WidthOfDestination]

theorem lm1WidthOfDestination_nonLm1 (bank : PEMemory.Bank) (h : bank ≠ PEMemory.Bank.lm1)
    (width : PEMemory.Width) (address : Fin bank.capacity) :
    lm1WidthOfDestination (some ⟨bank, width, address⟩) = 0 := by
  simp [lm1WidthOfDestination, h]

theorem lm1CountOfDestination_lm1 (width : PEMemory.Width)
    (address : Fin Bank.lm1.capacity) :
    lm1CountOfDestination (some ⟨PEMemory.Bank.lm1, width, address⟩) = 1 := by
  simp [lm1CountOfDestination]

theorem lm1WidthOfDestination_none : lm1WidthOfDestination none = 0 := rfl

theorem lm1CountOfDestination_none : lm1CountOfDestination none = 0 := rfl

theorem lm1WriteWords_append (first second : List PreparedParsedMaskedWrite) :
    lm1WriteWords (first ++ second) = lm1WriteWords first + lm1WriteWords second := by
  simp [lm1WriteWords, List.map_append, List.sum_append]

theorem lm1WriteCount_append (first second : List PreparedParsedMaskedWrite) :
    lm1WriteCount (first ++ second) = lm1WriteCount first + lm1WriteCount second := by
  simp [lm1WriteCount, List.map_append, List.sum_append]

theorem lm1WriteWords_cons (head : PreparedParsedMaskedWrite)
    (tail : List PreparedParsedMaskedWrite) :
    lm1WriteWords (head :: tail) =
      lm1WidthOfDestination head.destination + lm1WriteWords tail := by
  simp [lm1WriteWords]

theorem lm1WriteCount_cons (head : PreparedParsedMaskedWrite)
    (tail : List PreparedParsedMaskedWrite) :
    lm1WriteCount (head :: tail) =
      lm1CountOfDestination head.destination + lm1WriteCount tail := by
  simp [lm1WriteCount]

/-- The destination-based indicator is the executor's own `isLm1Write` flag. -/
theorem lm1CountOfDestination_eq_flag (write : PreparedParsedMaskedWrite) :
    lm1CountOfDestination write.destination =
      (if PreparedParsedMaskedWrite.isLm1Write write then 1 else 0) := by
  cases destination : write.destination with
  | none => simp [lm1CountOfDestination, destination, PreparedParsedMaskedWrite.isLm1Write]
  | some access =>
      obtain ⟨bank, width, address⟩ := access
      cases bank <;>
        simp [lm1CountOfDestination, destination, PreparedParsedMaskedWrite.isLm1Write]

/-- `lm1WriteCount` is the executor's own `.lm1` filter length. -/
theorem lm1WriteCount_eq_filter_length (writes : List PreparedParsedMaskedWrite) :
    lm1WriteCount writes =
      (writes.filter PreparedParsedMaskedWrite.isLm1Write).length := by
  induction writes with
  | nil => rfl
  | cons head tail ih =>
      rw [lm1WriteCount_cons, ih, List.filter_cons, lm1CountOfDestination_eq_flag]
      split <;> simp <;> omega

/-- The word budget read off the destination list. -/
theorem lm1WriteWords_map_destinations (writes : List PreparedParsedMaskedWrite) :
    lm1WriteWords writes =
      ((writes.map (fun write => write.destination)).map lm1WidthOfDestination).sum := by
  simp [lm1WriteWords, List.map_map, Function.comp_def]

/-- The write count read off the destination list. -/
theorem lm1WriteCount_map_destinations (writes : List PreparedParsedMaskedWrite) :
    lm1WriteCount writes =
      ((writes.map (fun write => write.destination)).map lm1CountOfDestination).sum := by
  simp [lm1WriteCount, List.map_map, Function.comp_def]

/-- **The entry-wise budget.**  A per-write bound `entry ≤ flag * bound` lifts to
the whole list. -/
theorem lm1WriteWords_le_count_mul_entry (writes : List PreparedParsedMaskedWrite)
    (bound : Nat)
    (perWrite : ∀ write ∈ writes, lm1WidthOfDestination write.destination ≤
      lm1CountOfDestination write.destination * bound) :
    lm1WriteWords writes ≤ lm1WriteCount writes * bound := by
  induction writes with
  | nil => simp [lm1WriteWords, lm1WriteCount]
  | cons head tail ih =>
      have headBound := perWrite head (by simp)
      have tailBound := ih (fun write member =>
        perWrite write (List.mem_cons_of_mem _ member))
      rw [lm1WriteWords_cons, lm1WriteCount_cons]
      have expand : (lm1CountOfDestination head.destination + lm1WriteCount tail) *
          bound =
          lm1CountOfDestination head.destination * bound +
            lm1WriteCount tail * bound := by
        rw [Nat.add_mul]
      rw [expand]
      exact Nat.add_le_add headBound tailBound

/-- **The word budget of one line.**  If the write list has at most four
`.lm1` writes and every `.lm1` destination has the same static width `w`, then
the list writes at most `4 * count .lm1 w` words at PE 0. -/
theorem lm1WriteWords_le_count_mul (writes : List PreparedParsedMaskedWrite)
    (w : PEMemory.Width) (countLe : lm1WriteCount writes ≤ 4)
    (widths : ∀ write ∈ writes, ∀ (width : PEMemory.Width)
      (address : Fin Bank.lm1.capacity),
      write.destination = some ⟨PEMemory.Bank.lm1, width, address⟩ → width = w) :
    lm1WriteWords writes ≤ 4 * count PEMemory.Bank.lm1 w := by
  have perWrite : ∀ write ∈ writes, lm1WidthOfDestination write.destination ≤
      lm1CountOfDestination write.destination * count PEMemory.Bank.lm1 w := by
    intro write member
    cases destination : write.destination with
    | none => simp [lm1WidthOfDestination, destination, PreparedParsedMaskedWrite.isLm1Write]
    | some access =>
        obtain ⟨bank, width, address⟩ := access
        cases bank with
        | lm1 =>
            have widthEq := widths write member width address destination
            subst widthEq
            simp only [destination, lm1WidthOfDestination_lm1, lm1CountOfDestination_lm1]
            omega
        | grf0 => simp [lm1WidthOfDestination, destination, PreparedParsedMaskedWrite.isLm1Write]
        | grf1 => simp [lm1WidthOfDestination, destination, PreparedParsedMaskedWrite.isLm1Write]
        | lm0 => simp [lm1WidthOfDestination, destination, PreparedParsedMaskedWrite.isLm1Write]
        | t => simp [lm1WidthOfDestination, destination, PreparedParsedMaskedWrite.isLm1Write]
  have budget := lm1WriteWords_le_count_mul_entry writes (count PEMemory.Bank.lm1 w) perWrite
  calc lm1WriteWords writes
      ≤ lm1WriteCount writes * count PEMemory.Bank.lm1 w := budget
    _ ≤ 4 * count PEMemory.Bank.lm1 w := Nat.mul_le_mul_right _ countLe

/-- **The exact trichotomy.**  One line's `.lm1` budget is below the sixteen
observed words exactly when its static width is not `.double`. -/
theorem four_mul_count_le_eight (w : PEMemory.Width) :
    4 * count PEMemory.Bank.lm1 w ≤ 8 ↔ w ≠ PEMemory.Width.double := by
  cases w <;> decide

theorem four_mul_count_le_sixteen (w : PEMemory.Width) :
    4 * count PEMemory.Bank.lm1 w ≤ 16 := by
  cases w <;> decide

/-! ## 2. The counting kernel: a total `.lm1` width below `16` leaves a word -/

/-- A window of `size` words starting at `start` covers at most `size` of the
sixteen observed words (the modular distance is injective). -/
theorem card_window_le_size (start : Fin Bank.lm1.capacity) (size : Nat) :
    ((Finset.univ : Finset (Fin 16)).filter
      (fun t => distance .lm1 start (lm1Target t) < size)).card ≤ size := by
  classical
  let windowSet := (Finset.univ : Finset (Fin 16)).filter
    (fun t => distance .lm1 start (lm1Target t) < size)
  change windowSet.card ≤ size
  rw [← Fintype.card_coe windowSet]
  calc Fintype.card ↥windowSet ≤ Fintype.card (Fin size) := by
        apply Fintype.card_le_of_injective
          (fun t : ↥windowSet =>
            (⟨distance .lm1 start (lm1Target t.1), by
              have member := t.2
              simp only [windowSet, Finset.mem_filter, Finset.mem_univ, true_and] at member
              omega⟩ : Fin size))
        intro a b same
        apply Subtype.ext
        have hd : distance .lm1 start (lm1Target a.1) =
            distance .lm1 start (lm1Target b.1) := by
          simpa using same
        have ea := advance_distance start (lm1Target a.1)
        have eb := advance_distance start (lm1Target b.1)
        exact lm1Target_injective (by rw [← ea, ← eb, hd])
    _ = size := by simp

/-- The observed words one prepared write covers. -/
def lm1WriteCover (write : PreparedParsedMaskedWrite) : Finset (Fin 16) :=
  match write.destination with
  | some ⟨PEMemory.Bank.lm1, width, address⟩ =>
      (Finset.univ : Finset (Fin 16)).filter
        (fun t => distance .lm1 address (lm1Target t) < count PEMemory.Bank.lm1 width)
  | _ => ∅

theorem lm1WriteCover_card_le (write : PreparedParsedMaskedWrite) :
    (lm1WriteCover write).card ≤ lm1WidthOfDestination write.destination := by
  cases destination : write.destination with
  | none => simp [lm1WriteCover, lm1WidthOfDestination, destination]
  | some access =>
      obtain ⟨bank, width, address⟩ := access
      cases bank with
      | lm0 => simp [lm1WriteCover, lm1WidthOfDestination, destination]
      | lm1 =>
          have := card_window_le_size address width.words
          simpa [lm1WriteCover, lm1WidthOfDestination, destination, count] using this
      | grf0 => simp [lm1WriteCover, lm1WidthOfDestination, destination]
      | grf1 => simp [lm1WriteCover, lm1WidthOfDestination, destination]
      | t => simp [lm1WriteCover, lm1WidthOfDestination, destination]

/-- The observed words covered by a write list. -/
def lm1WriteCoverAll (writes : List PreparedParsedMaskedWrite) : Finset (Fin 16) :=
  (Finset.univ : Finset (Fin 16)).filter
    (fun t => ∃ write ∈ writes, t ∈ lm1WriteCover write)

theorem lm1WriteCoverAll_card_le (writes : List PreparedParsedMaskedWrite) :
    (lm1WriteCoverAll writes).card ≤ lm1WriteWords writes := by
  induction writes with
  | nil => simp [lm1WriteCoverAll, lm1WriteWords]
  | cons head tail ih =>
      have subset : lm1WriteCoverAll (head :: tail) ⊆
          lm1WriteCover head ∪ lm1WriteCoverAll tail := by
        intro t member
        simp only [lm1WriteCoverAll, Finset.mem_filter, Finset.mem_univ, true_and] at member
        obtain ⟨write, writeMem, covers⟩ := member
        rcases List.mem_cons.mp writeMem with same | later
        · subst same
          exact Finset.mem_union_left _ covers
        · exact Finset.mem_union_right _
            (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨write, later, covers⟩⟩)
      calc (lm1WriteCoverAll (head :: tail)).card
          ≤ (lm1WriteCover head ∪ lm1WriteCoverAll tail).card := Finset.card_le_card subset
        _ ≤ (lm1WriteCover head).card + (lm1WriteCoverAll tail).card := Finset.card_union_le _ _
        _ ≤ lm1WidthOfDestination head.destination + lm1WriteWords tail :=
            Nat.add_le_add (lm1WriteCover_card_le head) ih
        _ = lm1WriteWords (head :: tail) := by rw [lm1WriteWords_cons]

/-- **The counting kernel.**  A write list of total `.lm1` width below `16`
leaves one observed word uncovered. -/
theorem exists_uncovered_of_totalWidth (writes : List PreparedParsedMaskedWrite)
    (total : lm1WriteWords writes < 16) :
    ∃ t : Fin 16, ∀ write ∈ writes, ∀ (width : PEMemory.Width)
      (address : Fin Bank.lm1.capacity),
      write.destination = some ⟨PEMemory.Bank.lm1, width, address⟩ →
        count PEMemory.Bank.lm1 width ≤ distance .lm1 address (lm1Target t) := by
  classical
  have strict : (lm1WriteCoverAll writes).card <
      (Finset.univ : Finset (Fin 16)).card := by
    have bound := lm1WriteCoverAll_card_le writes
    simp only [Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨t, _, uncovered⟩ := Finset.exists_mem_notMem_of_card_lt_card strict
  refine ⟨t, ?_⟩
  intro write member width address destination
  by_contra within
  apply uncovered
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨write, member, by
    simp only [lm1WriteCover, destination]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa using within⟩⟩⟩

/-! ## 3. The value kernel at `A = 1.0, B = 0` -/

/-- **The width kernel for `1.a-b`.**  A one-line `.pe` program whose PE 0 file
at `A = 1.0, B = 0` is the commit of a write list of total `.lm1` width below
`16` is incorrect: the uncovered observed word keeps its initial `0` while the
target is `0x3F800000`. -/
theorem ab_not_correct_of_lm1TotalWidth (expressions : List NormalizedExpr)
    (next : State)
    (step : abSealedMachine.step (.pe expressions) (abInitialState abOneLeftInput) = some next)
    (writes : List PreparedParsedMaskedWrite)
    (committed : next.peRegisters abPE =
      commitParsedMaskedWrites ((abInitialState abOneLeftInput).peRegisters abPE) writes)
    (total : lm1WriteWords writes < 16) :
    ¬ ProofsLean.Correct abSealedMachine abSpec
      ([InstructionLine.pe expressions] : List InstructionLine) := by
  obtain ⟨word, untouched⟩ := exists_uncovered_of_totalWidth writes total
  intro correct
  obtain ⟨result, executed, post⟩ := correct.2 abOneLeftInput (abSpec_admissible _)
  have executed' : ProofsLean.execute abSealedMachine
      [InstructionLine.pe expressions] (abInitialState abOneLeftInput) = some result := by
    have h := executed
    rw [abSpec_initial] at h
    exact h
  have stepResult : abSealedMachine.step (InstructionLine.pe expressions)
      (abInitialState abOneLeftInput) = some result := by
    simpa [ProofsLean.execute] using executed'
  rw [step] at stepResult
  have resultEq : result = next := (Option.some.inj stepResult).symm
  subst result
  have zero : (next.peRegisters abPE).lm1 (lm1Target word) = 0 := by
    rw [committed]
    apply commitParsedMaskedWrites_lm1_word_zero
      ((abInitialState abOneLeftInput).peRegisters abPE) writes (lm1Target word)
    · intro write writeMem width address data selection destination dataEq selectionEq
      subst dataEq selectionEq
      exact Or.inl (untouched write writeMem width address destination)
    · exact abInitialPERegisters_lm1 abOneLeftInput (lm1Target word)
  have wordZero : (next.peRegisters abPE).lm1
      ⟨word.val, by have := word.isLt; change word.val < 4096; omega⟩ = 0 := by
    simpa [lm1Target] using zero
  have wanted := post word
  rw [wordZero, abTarget_oneLeft] at wanted
  exact absurd wanted.symm (by decide)

/-- **The narrow shape also gives the width bound** (four `.lm1` writes and at
most four two-word windows), so the width kernel generalises
`ab_not_correct_of_narrowAtOnes`. -/
theorem lm1WriteWords_le_eight_of_narrow (writes : List PreparedParsedMaskedWrite)
    (countLe : lm1WriteCount writes ≤ 4)
    (narrow : Lm1WritesNarrow writes) : lm1WriteWords writes ≤ 8 := by
  obtain ⟨windows, covers, bound, sizes⟩ := narrow
  have perWrite : ∀ write ∈ writes, lm1WidthOfDestination write.destination ≤
      lm1CountOfDestination write.destination * 2 := by
    intro write member
    cases destination : write.destination with
    | none => simp [lm1WidthOfDestination, destination, PreparedParsedMaskedWrite.isLm1Write]
    | some access =>
        obtain ⟨bank, width, address⟩ := access
        by_cases lm1 : bank = PEMemory.Bank.lm1
        · subst lm1
          have windowMem := covers write member width address destination
          have size := sizes (address, count PEMemory.Bank.lm1 width) windowMem
          simp only [destination, lm1WidthOfDestination_lm1, lm1CountOfDestination_lm1]
          simpa using size
        · simp [lm1WidthOfDestination, destination, PreparedParsedMaskedWrite.isLm1Write, lm1]
  have budget := lm1WriteWords_le_count_mul_entry writes 2 perWrite
  calc lm1WriteWords writes ≤ lm1WriteCount writes * 2 := budget
    _ ≤ 4 * 2 := Nat.mul_le_mul_right _ countLe
    _ = 8 := by decide

/-- **The usable form of the width kernel.**  A one-line `.pe` program whose
PE 0 write list at `A = 1.0, B = 0` has at most four `.lm1` writes of one static
non-`.double` width is incorrect.  This is the whole non-`.double` branch: the
only per-family inputs are the count bound and the static width, both already
proved in the tree (see the module docstring), and no copy/destination analysis
at the non-zero input is needed. -/
theorem ab_not_correct_of_lm1WidthNotDouble (expressions : List NormalizedExpr)
    (next : State)
    (step : abSealedMachine.step (.pe expressions) (abInitialState abOneLeftInput) = some next)
    (writes : List PreparedParsedMaskedWrite)
    (committed : next.peRegisters abPE =
      commitParsedMaskedWrites ((abInitialState abOneLeftInput).peRegisters abPE) writes)
    (w : PEMemory.Width) (countLe : lm1WriteCount writes ≤ 4)
    (widths : ∀ write ∈ writes, ∀ (width : PEMemory.Width)
      (address : Fin Bank.lm1.capacity),
      write.destination = some ⟨PEMemory.Bank.lm1, width, address⟩ → width = w)
    (notDouble : w ≠ PEMemory.Width.double) :
    ¬ ProofsLean.Correct abSealedMachine abSpec
      ([InstructionLine.pe expressions] : List InstructionLine) := by
  apply ab_not_correct_of_lm1TotalWidth expressions next step writes committed
  have budget := lm1WriteWords_le_count_mul writes w countLe widths
  have small := (four_mul_count_le_eight w).mpr notDouble
  omega

/-! ## 4. The witness: a `.double` destination writes all sixteen words -/

/-- The `.double` (two-long-word) `LM1` destination at the four aligned
addresses `0, 4, 8, 12`; four cycles of the all-ones long-long selection write
the words `0..15`. -/
def abWidthDoubleAccess : Issue.Access :=
  ⟨.lm1, ⟨4, 0, 4, 8, 12, false, none⟩⟩

/-- The `iinc $lm0v ...` row of `ProofsLean/WelcomeComplete.lean` with a
`.double` `LM1` destination: the 2LW IALU form of the ISA measurements. -/
def abWidthDoubleExpr : NormalizedExpr where
  op := .alu .inc (some .i) false none
  sources := [Issue.plusOneReadAt 0]
  destinations := [.mem abWidthDoubleAccess false false false none]
  flush := none

/-- **The witness's prepared write list, computed by the kernel.**  The one-row
line's integer-stage preparation (`prepareParsedIntegerMatrixReadLineCycles`,
i.e. the executor's own list, with the line's own flags) is exactly four
`.lm1 .double` writes at `0, 4, 8, 12`. -/
theorem abWidthDouble_linePrepDestinations :
    (match prepareParsedIntegerMatrixReadLineCycles welcomeZeroFiles welcomeZeroSlots
        welcomeZeroMatrixStore [abWidthDoubleExpr.toParsed] welcomeZeroControl false with
      | .ok (writes, _, _) => writes.map (fun write => write.destination)
      | _ => []) =
      [some ⟨PEMemory.Bank.lm1, PEMemory.Width.double, ⟨0, by decide⟩⟩,
       some ⟨PEMemory.Bank.lm1, PEMemory.Width.double, ⟨4, by decide⟩⟩,
       some ⟨PEMemory.Bank.lm1, PEMemory.Width.double, ⟨8, by decide⟩⟩,
       some ⟨PEMemory.Bank.lm1, PEMemory.Width.double, ⟨12, by decide⟩⟩] := by
  decide

/-- **The witness's write selections, computed by the kernel.**  Every one of
the four writes carries the all-ones long-long selection, so all four words of
each `.double` block are written. -/
theorem abWidthDouble_linePrepSelections :
    (match prepareParsedIntegerMatrixReadLineCycles welcomeZeroFiles welcomeZeroSlots
        welcomeZeroMatrixStore [abWidthDoubleExpr.toParsed] welcomeZeroControl false with
      | .ok (writes, _, _) => writes.map (fun write => write.selection)
      | _ => []) =
      [⟨0xf, true⟩, ⟨0xf, true⟩, ⟨0xf, true⟩, ⟨0xf, true⟩] := by
  decide

/-- **The witness's word budget.**  The line's integer-stage list is four
`.lm1 .double` writes: sixteen words at PE 0, four `.lm1` writes — the bound `8`
is exceeded. -/
theorem abWidthDouble_linePrepWrites :
    ∃ (writes : List PreparedParsedMaskedWrite)
      (slots : ProofsLean.MNCore.Forwarding.Slots) (bars : List (Bool × BitVec 12)),
      prepareParsedIntegerMatrixReadLineCycles welcomeZeroFiles welcomeZeroSlots
          welcomeZeroMatrixStore [abWidthDoubleExpr.toParsed] welcomeZeroControl false =
        .ok (writes, slots, bars) ∧
      writes.map (fun write => write.destination) =
        [some ⟨PEMemory.Bank.lm1, PEMemory.Width.double, ⟨0, by decide⟩⟩,
         some ⟨PEMemory.Bank.lm1, PEMemory.Width.double, ⟨4, by decide⟩⟩,
         some ⟨PEMemory.Bank.lm1, PEMemory.Width.double, ⟨8, by decide⟩⟩,
         some ⟨PEMemory.Bank.lm1, PEMemory.Width.double, ⟨12, by decide⟩⟩] ∧
      writes.map (fun write => write.selection) =
        [⟨0xf, true⟩, ⟨0xf, true⟩, ⟨0xf, true⟩, ⟨0xf, true⟩] ∧
      lm1WriteCount writes = 4 ∧ lm1WriteWords writes = 16 := by
  have destinations := abWidthDouble_linePrepDestinations
  have selections := abWidthDouble_linePrepSelections
  cases prepared : prepareParsedIntegerMatrixReadLineCycles welcomeZeroFiles welcomeZeroSlots
      welcomeZeroMatrixStore [abWidthDoubleExpr.toParsed] welcomeZeroControl false with
  | failure => rw [prepared] at destinations; simp at destinations
  | unknown => rw [prepared] at destinations; simp at destinations
  | ok result =>
      obtain ⟨writes, slots, bars⟩ := result
      rw [prepared] at destinations
      rw [prepared] at selections
      have destinations' : writes.map (fun write => write.destination) =
          [some ⟨PEMemory.Bank.lm1, PEMemory.Width.double, ⟨0, by decide⟩⟩,
           some ⟨PEMemory.Bank.lm1, PEMemory.Width.double, ⟨4, by decide⟩⟩,
           some ⟨PEMemory.Bank.lm1, PEMemory.Width.double, ⟨8, by decide⟩⟩,
           some ⟨PEMemory.Bank.lm1, PEMemory.Width.double, ⟨12, by decide⟩⟩] := by
        simpa using destinations
      have selections' : writes.map (fun write => write.selection) =
          [⟨0xf, true⟩, ⟨0xf, true⟩, ⟨0xf, true⟩, ⟨0xf, true⟩] := by
        simpa using selections
      refine ⟨writes, slots, bars, rfl, destinations', selections', ?_, ?_⟩
      · rw [lm1WriteCount_map_destinations, destinations']
        decide
      · rw [lm1WriteWords_map_destinations, destinations']
        decide

/-- **The witness covers every observed word.**  The four `.double` windows at
`0, 4, 8, 12` cover the words `0..15`. -/
theorem abWidthDouble_covers_all (word : Fin 16) :
    distance .lm1 ⟨4 * (word.val / 4), by
      have := word.isLt
      change 4 * (word.val / 4) < 4096
      omega⟩ (lm1Target word) < 4 := by
  have bounded := word.isLt
  have startVal : (⟨4 * (word.val / 4),
      by have := word.isLt; change 4 * (word.val / 4) < 4096; omega⟩ :
        Fin Bank.lm1.capacity).val = 4 * (word.val / 4) := rfl
  have targetVal : (lm1Target word).val = word.val := rfl
  unfold distance
  rw [startVal, targetVal]
  change (word.val + 4096 - 4 * (word.val / 4)) % 4096 < 4
  have split : word.val + 4096 - 4 * (word.val / 4) = word.val % 4 + 4096 := by
    have := Nat.mod_add_div word.val 4
    omega
  rw [split, Nat.add_mod_right]
  have small : word.val % 4 < 4096 := by omega
  rw [Nat.mod_eq_of_lt small]
  have := Nat.mod_lt word.val (by decide : 0 < 4)
  omega

/-- **The same `16` for the L1BM→PE family, by construction.**  The L1BM
broadcast writes exactly four `.lm1` writes of the broadcast width. -/
theorem l1ToPEWrites_budget_eq (w : PEMemory.Width)
    (addresses : Fin 4 → Fin PEMemory.Bank.lm1.capacity)
    (selections : Fin 4 → PEWordSelection) :
    lm1WriteCount (l1ToPEWrites w addresses selections) = 4 ∧
      lm1WriteWords (l1ToPEWrites w addresses selections) = 4 * count PEMemory.Bank.lm1 w := by
  have length := l1ToPEWrites_length w addresses selections
  have allLm1 : ∀ write ∈ l1ToPEWrites w addresses selections,
      PreparedParsedMaskedWrite.isLm1Write write = true := by
    intro write member
    obtain ⟨cycle, destination, data, selection⟩ :=
      l1ToPEWrites_mem w addresses selections write member
    simp [PreparedParsedMaskedWrite.isLm1Write, destination]
  have widthEq : ∀ write ∈ l1ToPEWrites w addresses selections,
      lm1WidthOfDestination write.destination = count PEMemory.Bank.lm1 w := by
    intro write member
    obtain ⟨cycle, destination, data, selection⟩ :=
      l1ToPEWrites_mem w addresses selections write member
    rw [destination, lm1WidthOfDestination_lm1]
  have sumEq : ∀ (list : List PreparedParsedMaskedWrite) (c : Nat),
      (list.map (fun _ => c)).sum = c * list.length := by
    intro list c
    induction list with
    | nil => simp
    | cons head tail ih =>
        simp only [List.map_cons, List.sum_cons, List.length_cons, ih]
        rw [Nat.mul_add, Nat.mul_one]
        omega
  constructor
  · rw [lm1WriteCount_eq_filter_length, List.filter_eq_self.mpr allLm1, length]
  · rw [lm1WriteWords]
    have mapEq : (l1ToPEWrites w addresses selections).map
        (fun write => lm1WidthOfDestination write.destination) =
        (l1ToPEWrites w addresses selections).map (fun _ => count PEMemory.Bank.lm1 w) :=
      List.map_congr_left widthEq
    rw [mapEq, sumEq, length]
    omega

/-- The `.double` instance: sixteen words at PE 0 from four `.lm1 .double`
writes. -/
theorem l1ToPEWrites_double_budget (addresses : Fin 4 → Fin PEMemory.Bank.lm1.capacity)
    (selections : Fin 4 → PEWordSelection) :
    lm1WriteCount (l1ToPEWrites PEMemory.Width.double addresses selections) = 4 ∧
      lm1WriteWords (l1ToPEWrites PEMemory.Width.double addresses selections) = 16 := by
  have budget := l1ToPEWrites_budget_eq PEMemory.Width.double addresses selections
  rw [budget.1, budget.2]
  decide


/-- **The width/count hypothesis is false.**  There is a one-row `.pe` line
whose own integer-stage preparation writes sixteen `.lm1` words with four
`.lm1` writes: the `iinc` row with a `.double` (2LW) destination.  So no
`total written words < 16` argument can refute that line. -/
theorem abWidthBound_eight_false :
    ∃ (writes : List PreparedParsedMaskedWrite)
      (slots : ProofsLean.MNCore.Forwarding.Slots) (bars : List (Bool × BitVec 12)),
      prepareParsedIntegerMatrixReadLineCycles welcomeZeroFiles welcomeZeroSlots
          welcomeZeroMatrixStore [abWidthDoubleExpr.toParsed] welcomeZeroControl false =
        .ok (writes, slots, bars) ∧
      lm1WriteCount writes = 4 ∧ lm1WriteWords writes = 16 := by
  obtain ⟨writes, slots, bars, prepared, destinations, selections, count, words⟩ :=
    abWidthDouble_linePrepWrites
  exact ⟨writes, slots, bars, prepared, count, words⟩

end ProofsLean.MNCore

-- End of module: no sorry, no admit, no native_decide, no new axioms.
