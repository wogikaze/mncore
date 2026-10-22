import ProofsLean.CendPlainWitness
import ProofsLean.WelcomePlainStep
import ProofsLean.PlainALUDestination

/-! # `12.convert-endian`: the wide (both-halves) family beyond the collision argument

`ProofsLean/CendPlainWitness.lean` refuted every plain line whose read set misses
one of the two LM0 input words and reduced the rest to
`CendPlainALUBothHalvesRefuted`: the plain lines whose read set contains **both**
LM0 word `0` (the high input half) and LM0 word `1` (the low half).  The
collision argument cannot reach that class, because two inputs the line cannot
distinguish from its reads must agree on the whole input.

This module attacks the both-halves class with the *finite-range* argument of
`ProofsLean/ProgramWitness.lean` (`not_mem_of_range_subset`,
`exists_ne_of_range_subset_of_surjective`) and with the executor's own
destination analysis.

## 1. The finite-range kernel

A line whose observed LM1 pair, at **every** input on which it steps, lies in a
finite set `S` of `BitVec 64` is incorrect as soon as `S` misses one value of the
target: the target `byteSwap64` is surjective
(`ByteSwapKernel.byteSwap64_surjective_kernel` is axiom-free), so some input
asks for the missed value while the line can only produce members of `S`.

The kernel is stated for a line that may be **stuck** on some inputs: if it is
stuck the line is already incorrect (`cend_not_correct_of_step_stuck`), and
otherwise the observed pair is a genuine function of the input.  This is the
form a value analysis can fill: it only has to bound the pair *at the successful
steps*, not to prove the line total.

`cendPE_not_correct_of_eventually_smallRange` replaces the explicit missed value
by the cardinality bound `S.card < 2 ^ 64`, the route for value sets too large to
enumerate (`exists_not_mem_of_card_lt`, proved here from the injection
`Fin (2 ^ 64) → BitVec 64`).

## 2. The one-word hyperplane

The concrete finite set of the one-observed-word case is the set of pairs
`(v, 0)` — one arbitrary observed word and a zero second word.  It has `2 ^ 32`
members (`cendZeroLowPairs_card_le`) and misses e.g. `(0, 1) = 1`, so
`cendPE_not_correct_of_lm1_word_one_free` refutes any line whose every successful
step leaves LM1 word `1` untouched.  The untouched-word hypothesis is written on
the executor's prepared write list (`PreparedParsedMaskedWrite.destination` and
its window), which is the form the destination analysis of §3 produces.  The
dual `cendPE_not_correct_of_lm1_word_zero_free` covers a free LM1 word `0`.

## 3. What is closed unconditionally: lines with no LM1 destination

`CendAvoidsLm1` is the syntactic condition that no destination operand of a row
has static bank `LM1` (`ParsedOperand.directDestinationBankWidth?`).  §3 proves
`prepareParsedIntegerALUExprCycle_noLm1`: every branch of the executor's plain
ALU cycle either writes the lowered destination — hence a destination operand —
or has no memory destination at all, so the cycle can only write LM1 through a
destination operand with static LM1 bank.  The four-cycle and line-level folds
give `cendPE_plain_not_correct_of_avoidsLm1`: a plain line whose rows all avoid
LM1 destinations leaves the whole LM1 bank at its initial zero at every input,
and the observed pair `0` disagrees with the non-zero target at `cendWitness`.

This is an **unconditional** refutation of a genuine part of the both-halves
class (its sources may read both input words).

## 4. The narrowed residual, and the plain family

`CendHasLm1Destination` is the part of the both-halves class that §3 does not
cover: a line with at least one destination operand whose static bank/width is
`(.lm1, _)`.  `CendPlainALUBothHalvesRefutedLm1` is the narrowed residual: the
both-halves lines with an LM1 destination are incorrect.
`cendPlainALUBothHalvesRefuted_of_lm1Destination` proves the full
`CendPlainALUBothHalvesRefuted` from it (using §3 for the lines without an LM1
destination), and `cendPE_plain_not_correct_of_lm1Destination` /
`cendPE_plainLines_not_correct_of_lm1Destination` refute every plain line — and
the whole plain family — from the narrowed residual.

The narrowed residual itself is **not** proved here.  It is exactly the
finite-range value analysis of §1/§2: for a plain line with an LM1 destination,
exhibit either a finite set `S` of observed pairs with `byteSwap64 x ∉ S` for
some input, or show that one of the two observed words is untouched (so §2
applies).  `CendPlainALUWideWitness` in `ProofsLean/ProgramWitness.lean` records
the same obligation in the per-row `probe`/`table` form; this module supplies the
`f x`-range kernel and the fully proved one-word instance that such an analysis
feeds.

## Trust

No `sorry`, no `admit`, no `native_decide`, no `bv_decide`, no new axioms, and
no existing module is edited.  Every theorem below depends only on `propext`,
`Classical.choice` and `Quot.sound`; in particular the finite-range kernels and
the no-LM1-destination refutation are free of `ByteSwap`'s pre-existing
`_native.bv_decide` axiom.
-/

namespace ProofsLean.MNCore

open Issue
open PEMemory

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false

/-! ## 1. The finite-range kernel -/

/-- **A finite set smaller than `BitVec 64` misses a value.**  The enumeration of
`Fin (2 ^ 64)` through `BitVec.ofFin` is injective, so a set containing every
value has at least `2 ^ 64` members. -/
theorem exists_not_mem_of_card_lt (S : Finset (BitVec 64)) (small : S.card < 2 ^ 64) :
    ∃ value, value ∉ S := by
  by_contra hall
  push Not at hall
  have subset : (Finset.univ.image (fun i : Fin (2 ^ 64) => BitVec.ofFin i)) ⊆ S := by
    intro value _
    exact hall value
  have cardImage :
      (Finset.univ.image (fun i : Fin (2 ^ 64) => BitVec.ofFin i)).card = 2 ^ 64 := by
    rw [Finset.card_image_of_injective]
    · simp
    · intro first second same
      simpa using congrArg BitVec.toFin same
  have bound := Finset.card_le_card subset
  omega

/-- **Finite-range refutation, table form.**  If every successful step of the line
at every input produces an observed pair in `S`, and `S` misses some value, then
the line is incorrect: the target is surjective, so some input asks for the
missed value. -/
theorem cendPE_not_correct_of_eventually_range (expressions : List NormalizedExpr)
    (S : Finset (BitVec 64))
    (range : ∀ (x : BitVec 64) (next : State), cendStep expressions x = some next →
      cendOutputPair next ∈ S)
    (outside : ∃ value, value ∉ S) :
    ¬ ProofsLean.Correct cendSealedMachine cendSpec
      ([InstructionLine.pe expressions] : List InstructionLine) := by
  classical
  by_cases stuck : ∃ x, cendStep expressions x = none
  · obtain ⟨x, hx⟩ := stuck
    exact cend_not_correct_of_step_stuck expressions x hx
  · push Not at stuck
    have nonempty : ∀ x : BitVec 64, ∃ next : State, cendStep expressions x = some next := by
      intro x
      cases step : cendStep expressions x with
      | none => exact absurd step (stuck x)
      | some next => exact ⟨next, rfl⟩
    choose next stepped using nonempty
    have output : ∀ (x : BitVec 64) (state : State),
        cendStep expressions x = some state → cendOutputPair state = cendOutputPair (next x) := by
      intro x state step
      have same : cendStep expressions x = some (next x) := stepped x
      rw [step] at same
      exact congrArg cendOutputPair (Option.some.inj same)
    have rangeFun : ∀ x, cendOutputPair (next x) ∈ S := fun x => range x (next x) (stepped x)
    obtain ⟨x, different⟩ :=
      exists_ne_of_range_subset_of_surjective (fun x => cendOutputPair (next x)) byteSwap64 S
        rangeFun outside byteSwap64_surjective_kernel
    exact cend_not_correct_of_output_ne expressions x (next x) (stepped x) different

/-- **Finite-range refutation, cardinality form.**  The value set may be too large
to enumerate (a single 32-bit observed word already gives `2 ^ 32` values); the
only thing needed is that it is smaller than the `2 ^ 64` target values. -/
theorem cendPE_not_correct_of_eventually_smallRange (expressions : List NormalizedExpr)
    (S : Finset (BitVec 64))
    (range : ∀ (x : BitVec 64) (next : State), cendStep expressions x = some next →
      cendOutputPair next ∈ S)
    (small : S.card < 2 ^ 64) :
    ¬ ProofsLean.Correct cendSealedMachine cendSpec
      ([InstructionLine.pe expressions] : List InstructionLine) :=
  cendPE_not_correct_of_eventually_range expressions S range
    (exists_not_mem_of_card_lt S small)


/-! ## 2. The one-word hyperplane -/

/-- The 64-bit word with observed high word `high` and low word `low`. -/
def cendPair (high low : BitVec 32) : BitVec 64 := high ++ low

/-- The observed pairs whose low word is zero: the value set of a `.word` store
into LM1 word `0`. -/
def cendZeroLowPairs : Finset (BitVec 64) :=
  Finset.univ.image (fun i : Fin (2 ^ 32) => cendPair (BitVec.ofFin i) (0 : BitVec 32))

/-- The observed pairs whose high word is zero: the value set of a `.word` store
into LM1 word `1`. -/
def cendZeroHighPairs : Finset (BitVec 64) :=
  Finset.univ.image (fun i : Fin (2 ^ 32) => cendPair (0 : BitVec 32) (BitVec.ofFin i))

theorem cendZeroLowPairs_mem (low : BitVec 32) : cendPair low 0 ∈ cendZeroLowPairs := by
  refine Finset.mem_image.mpr ⟨low.toFin, Finset.mem_univ _, ?_⟩
  show cendPair (BitVec.ofFin low.toFin) (0 : BitVec 32) = cendPair low 0
  rfl

theorem cendZeroHighPairs_mem (high : BitVec 32) : cendPair 0 high ∈ cendZeroHighPairs := by
  refine Finset.mem_image.mpr ⟨high.toFin, Finset.mem_univ _, ?_⟩
  show cendPair (0 : BitVec 32) (BitVec.ofFin high.toFin) = cendPair 0 high
  rfl

/-- The zero-low value set has at most `2 ^ 32` members: the cardinality route of
`cendPE_not_correct_of_eventually_smallRange`. -/
theorem cendZeroLowPairs_card_le : cendZeroLowPairs.card ≤ 2 ^ 32 := by
  unfold cendZeroLowPairs
  calc (Finset.univ.image (fun i : Fin (2 ^ 32) => cendPair (BitVec.ofFin i) 0)).card
      ≤ (Finset.univ : Finset (Fin (2 ^ 32))).card := Finset.card_image_le
    _ = 2 ^ 32 := by simp

/-- The zero-high value set has at most `2 ^ 32` members. -/
theorem cendZeroHighPairs_card_le : cendZeroHighPairs.card ≤ 2 ^ 32 := by
  unfold cendZeroHighPairs
  calc (Finset.univ.image (fun i : Fin (2 ^ 32) => cendPair 0 (BitVec.ofFin i))).card
      ≤ (Finset.univ : Finset (Fin (2 ^ 32))).card := Finset.card_image_le
    _ = 2 ^ 32 := by simp

/-- The target `1 = (0, 1)` has a non-zero low word, so it is not a zero-low
observed pair. -/
theorem cendZeroLowPairs_one_not_mem : (1 : BitVec 64) ∉ cendZeroLowPairs := by
  intro member
  obtain ⟨i, -, equality⟩ := Finset.mem_image.mp member
  have low := congrArg (fun value : BitVec 64 => value.extractLsb' 0 32) equality
  simp only [cendPair] at low
  rw [BitVec.extractLsb'_append_eq_right] at low
  have one : (1 : BitVec 64).extractLsb' 0 32 = (1 : BitVec 32) := by decide
  rw [one] at low
  exact absurd low (by decide)

/-- The target `0x0000000100000000 = (1, 0)` has a non-zero high word, so it is
not a zero-high observed pair. -/
theorem cendZeroHighPairs_witness_not_mem :
    (0x0000000100000000 : BitVec 64) ∉ cendZeroHighPairs := by
  intro member
  obtain ⟨i, -, equality⟩ := Finset.mem_image.mp member
  have high := congrArg (fun value : BitVec 64 => value.extractLsb' 32 32) equality
  simp only [cendPair] at high
  rw [BitVec.extractLsb'_append_eq_left] at high
  have one : (0x0000000100000000 : BitVec 64).extractLsb' 32 32 = (1 : BitVec 32) := by decide
  rw [one] at high
  exact absurd high (by decide)

/-- **A line that leaves LM1 word `1` untouched is incorrect.**  The observed pair
is then `(v, 0)` for some 32-bit `v`, a set of `2 ^ 32` values that misses the
target `1`; surjectivity of `byteSwap64` supplies an input asking for it.

The hypothesis is on the executor's prepared write list: no `.lm1` destination
window covers word `1` (`count .lm1 width ≤ distance .lm1 address ⟨1⟩`). -/
theorem cendPE_not_correct_of_lm1_word_one_free (expressions : List NormalizedExpr)
    (free : ∀ (x : BitVec 64) (next : State), cendStep expressions x = some next →
      ∃ writes, next.peRegisters cendPE =
          commitParsedMaskedWrites ((cendInitialState x).peRegisters cendPE) writes ∧
        ∀ write ∈ writes, ∀ (width : PEMemory.Width)
            (address : Fin PEMemory.Bank.lm1.capacity),
          write.destination = some ⟨PEMemory.Bank.lm1, width, address⟩ →
            PEMemory.count PEMemory.Bank.lm1 width ≤
              PEMemory.distance PEMemory.Bank.lm1 address ⟨1, by decide⟩) :
    ¬ ProofsLean.Correct cendSealedMachine cendSpec
      ([InstructionLine.pe expressions] : List InstructionLine) := by
  refine cendPE_not_correct_of_eventually_range expressions cendZeroLowPairs ?_
    ⟨1, cendZeroLowPairs_one_not_mem⟩
  intro x next step
  obtain ⟨writes, committed, keeps⟩ := free x next step
  have wordOne : (next.peRegisters cendPE).lm1 ⟨1, by decide⟩ = 0 := by
    rw [committed]
    apply commitParsedMaskedWrites_lm1_word_zero _ writes ⟨1, by decide⟩
    · intro write member width address data selection destination dataEq selectionEq
      exact Or.inl (keeps write member width address destination)
    · exact cendInitialPERegisters_lm1 x ⟨1, by decide⟩
  have outputOne : cendOutputWord1 next = 0 := wordOne
  rw [cendOutputPair_eq_append, outputOne]
  exact cendZeroLowPairs_mem (cendOutputWord0 next)

/-- **A line that leaves LM1 word `0` untouched is incorrect**, by the dual
hyperplane `(0, v)` and the target `0x0000000100000000`. -/
theorem cendPE_not_correct_of_lm1_word_zero_free (expressions : List NormalizedExpr)
    (free : ∀ (x : BitVec 64) (next : State), cendStep expressions x = some next →
      ∃ writes, next.peRegisters cendPE =
          commitParsedMaskedWrites ((cendInitialState x).peRegisters cendPE) writes ∧
        ∀ write ∈ writes, ∀ (width : PEMemory.Width)
            (address : Fin PEMemory.Bank.lm1.capacity),
          write.destination = some ⟨PEMemory.Bank.lm1, width, address⟩ →
            PEMemory.count PEMemory.Bank.lm1 width ≤
              PEMemory.distance PEMemory.Bank.lm1 address ⟨0, by decide⟩) :
    ¬ ProofsLean.Correct cendSealedMachine cendSpec
      ([InstructionLine.pe expressions] : List InstructionLine) := by
  refine cendPE_not_correct_of_eventually_range expressions cendZeroHighPairs ?_
    ⟨0x0000000100000000, cendZeroHighPairs_witness_not_mem⟩
  intro x next step
  obtain ⟨writes, committed, keeps⟩ := free x next step
  have wordZero : (next.peRegisters cendPE).lm1 ⟨0, by decide⟩ = 0 := by
    rw [committed]
    apply commitParsedMaskedWrites_lm1_word_zero _ writes ⟨0, by decide⟩
    · intro write member width address data selection destination dataEq selectionEq
      exact Or.inl (keeps write member width address destination)
    · exact cendInitialPERegisters_lm1 x ⟨0, by decide⟩
  have outputZero : cendOutputWord0 next = 0 := wordZero
  rw [cendOutputPair_eq_append, outputZero]
  exact cendZeroHighPairs_mem (cendOutputWord1 next)


/-! ## 3. The destination analysis: no LM1 destination at all -/

def CendDestResolvesAt (pe : Fin 4) (cycle : Fin 4) (bar0 bar1 : BitVec 12) (tWord : BitVec 32)
    (expression : ParsedExpr) (access : DirectMemoryAccess) : Prop :=
  ∃ destination : ParsedOperand,
    ParsedOperand.toDirectMemoryDestination? destination pe cycle bar0 bar1 tWord = some access ∧
      destination ∈ expression.destinations

def CendAvoidsLm1 (expression : ParsedExpr) : Prop :=
  ∀ destination ∈ expression.destinations, ∀ width : PEMemory.Width,
    ParsedOperand.directDestinationBankWidth? destination ≠
      some (PEMemory.Bank.lm1, width)

theorem CendDestResolvesAt.bank_ne_lm1 {pe cycle : Fin 4} {bar0 bar1 : BitVec 12}
    {tWord : BitVec 32} {expression : ParsedExpr} {access : DirectMemoryAccess}
    (resolves : CendDestResolvesAt pe cycle bar0 bar1 tWord expression access)
    (avoids : CendAvoidsLm1 expression) :
    access.bank ≠ PEMemory.Bank.lm1 := by
  obtain ⟨destination, resolved, member⟩ := resolves
  intro bank
  have static := ParsedOperand.toDirectMemoryDestination?_bankWidth destination
    pe cycle bar0 bar1 tWord
  rw [resolved] at static
  simp only [Option.map_some] at static
  exact avoids destination member access.width (by rw [← static, bank])

theorem replicatePreparedIntegerResult_destination_mem
    (accesses : List ParsedMaskedIntegerAccesses) (result : PreparedParsedMaskedWrite)
    {item : PreparedParsedMaskedWrite} (member : item ∈ replicatePreparedIntegerResult accesses result) :
    ∃ access ∈ accesses, item.destination = some access.destination := by
  obtain ⟨access, accessMem, itemEq⟩ := List.mem_map.mp member
  refine ⟨access, accessMem, ?_⟩
  rw [← itemEq]

/-- The direct branch: one write at the lowered destination. -/
theorem noLm1_direct
    (files : IntegerRegisterFiles)
    (oldSlots : ProofsLean.MNCore.Forwarding.Slots)
    (expression : ParsedExpr) (control : ParsedMaskExecutionControl)
    (hsm nf reduced : Bool) (cycle : Fin 4)
    (accesses : ParsedMaskedIntegerAccesses) (write : PreparedParsedMaskedWrite)
    (avoids : CendAvoidsLm1 expression)
    (lowered : ParsedExpr.toDirectMaskedIntegerAccessesInLine? expression files.maskRegisters
      control.directive hsm control.context.group control.context.l2b control.context.l1b
      control.context.mab control.context.pe cycle control.context.bar0 control.context.bar1
      control.context.tWord = some accesses)
    (prepared : prepareParsedMaskedWriteWithForwarding files oldSlots cycle accesses reduced
      = .ok write) :
    ∀ item ∈ [write], ∀ (width : PEMemory.Width)
      (address : Fin PEMemory.Bank.lm1.capacity),
      item.destination ≠ some ⟨PEMemory.Bank.lm1, width, address⟩ := by
  intro item member width address destination
  rw [List.mem_singleton] at member
  subst item
  have destinationEq := prepareParsedMaskedWriteWithForwarding_destination files oldSlots cycle
    accesses reduced write prepared
  obtain ⟨target, targetMem, resolved⟩ :=
    ParsedExpr.toDirectMaskedIntegerAccessesInLine?_destination_provenance expression
      files.maskRegisters control.directive hsm control.context.group control.context.l2b
      control.context.l1b control.context.mab control.context.pe cycle control.context.bar0
      control.context.bar1 control.context.tWord accesses lowered
  have bankNe := CendDestResolvesAt.bank_ne_lm1
    ⟨target, resolved, targetMem⟩ avoids
  rw [destinationEq] at destination
  exact bankNe (by rw [Option.some.inj destination])

/-- The multiple-destination branch: the head write plus the replication. -/
theorem noLm1_multiple
    (files : IntegerRegisterFiles)
    (oldSlots : ProofsLean.MNCore.Forwarding.Slots)
    (expression : ParsedExpr) (control : ParsedMaskExecutionControl)
    (hsm nf reduced : Bool) (cycle : Fin 4)
    (access : ParsedMaskedIntegerAccesses) (rest : List ParsedMaskedIntegerAccesses)
    (write : PreparedParsedMaskedWrite)
    (avoids : CendAvoidsLm1 expression)
    (lowered : ParsedExpr.toDirectMaskedIntegerWritesInLine? expression files.maskRegisters
      control.directive hsm control.context.group control.context.l2b control.context.l1b
      control.context.mab control.context.pe cycle control.context.bar0 control.context.bar1
      control.context.tWord = some (access :: rest))
    (prepared : prepareParsedMaskedWriteWithForwarding files oldSlots cycle access reduced
      = .ok write) :
    ∀ item ∈ write :: replicatePreparedIntegerResult rest write, ∀ (width : PEMemory.Width)
      (address : Fin PEMemory.Bank.lm1.capacity),
      item.destination ≠ some ⟨PEMemory.Bank.lm1, width, address⟩ := by
  intro item member width address destination
  have provenance : ∀ other ∈ access :: rest, CendDestResolvesAt control.context.pe cycle
      control.context.bar0 control.context.bar1 control.context.tWord expression
      other.destination := by
    intro other otherMem
    obtain ⟨destination, memberDestination, resolved⟩ :=
      toDirectMaskedIntegerWritesInLine?_mem_provenance expression files.maskRegisters
        control.directive hsm control.context.group control.context.l2b control.context.l1b
        control.context.mab control.context.pe cycle control.context.bar0 control.context.bar1
        control.context.tWord (access :: rest) lowered other otherMem
    exact ⟨destination, resolved, memberDestination⟩
  have key : ∃ other ∈ access :: rest, item.destination = some other.destination := by
    rcases List.mem_cons.mp member with same | later
    · subst item
      exact ⟨access, by simp, prepareParsedMaskedWriteWithForwarding_destination files oldSlots
        cycle access reduced write prepared⟩
    · obtain ⟨other, otherMem, itemDestination⟩ :=
        replicatePreparedIntegerResult_destination_mem rest write later
      exact ⟨other, List.mem_cons_of_mem _ otherMem, itemDestination⟩
  obtain ⟨other, otherMem, itemDestination⟩ := key
  have bankNe := CendDestResolvesAt.bank_ne_lm1 (provenance other otherMem) avoids
  rw [itemDestination] at destination
  exact bankNe (by rw [Option.some.inj destination])

/-- The OMR / no-write / BAR / mask-input branches: no memory destination at all. -/
theorem noLm1_singleton_none (write : PreparedParsedMaskedWrite)
    (isNone : write.destination = none) :
    ∀ item ∈ [write], ∀ (width : PEMemory.Width)
      (address : Fin PEMemory.Bank.lm1.capacity),
      item.destination ≠ some ⟨PEMemory.Bank.lm1, width, address⟩ := by
  intro item member width address destination
  rw [List.mem_singleton] at member
  subst item
  rw [isNone] at destination
  exact absurd destination (by simp)

/-- The memory-then-input branch: its memory write resolves a destination operand,
its OMR write has no destination. -/
theorem noLm1_memoryThenInput
    (files : IntegerRegisterFiles)
    (oldSlots : ProofsLean.MNCore.Forwarding.Slots)
    (control : ParsedMaskExecutionControl) (cycle : Fin 4)
    (expression : ParsedExpr)
    (accesses : ParsedIntegerMaskMemoryThenInputAccesses)
    (flushSelection : Option PEWordSelection) (reduced : Bool)
    (memoryWrites : List PreparedParsedMaskedWrite)
    (omrWrite : PreparedParsedMaskedWrite)
    (avoids : CendAvoidsLm1 expression)
    (resolves : CendDestResolvesAt control.context.pe cycle control.context.bar0
      control.context.bar1 control.context.tWord expression accesses.memory)
    (prepared : prepareParsedIntegerMaskMemoryThenInputALUWritesWithForwarding files oldSlots
      cycle accesses flushSelection reduced = .ok (memoryWrites, omrWrite)) :
    ∀ item ∈ memoryWrites ++ [omrWrite], ∀ (width : PEMemory.Width)
      (address : Fin PEMemory.Bank.lm1.capacity),
      item.destination ≠ some ⟨PEMemory.Bank.lm1, width, address⟩ := by
  obtain ⟨bus, flags, writesEq, omrEq⟩ :=
    prepareParsedIntegerMaskMemoryThenInputALUWritesWithForwarding_shape files oldSlots cycle
      accesses flushSelection reduced memoryWrites omrWrite prepared
  rw [writesEq]
  intro item member width address destination
  rcases List.mem_append.mp member with earlier | later
  · rw [List.mem_singleton] at earlier
    subst item
    have bankNe := CendDestResolvesAt.bank_ne_lm1 resolves avoids
    exact bankNe (by rw [Option.some.inj destination])
  · rw [List.mem_singleton] at later
    subst item
    rw [omrEq] at destination
    exact absurd destination (by simp)

/-- The input-then-memory branch: same as the memory-then-input branch, with the
two writes in the other order. -/
theorem noLm1_inputThenMemory
    (files : IntegerRegisterFiles)
    (oldSlots : ProofsLean.MNCore.Forwarding.Slots)
    (control : ParsedMaskExecutionControl) (cycle : Fin 4)
    (expression : ParsedExpr)
    (accesses : ParsedIntegerMaskInputThenMemoryAccesses)
    (directive : ParsedMaskDirective) (hasSingleLineMask : Bool)
    (flushSelection : Option PEWordSelection) (reduced : Bool)
    (memoryWrites : List PreparedParsedMaskedWrite)
    (omrWrite : PreparedParsedMaskedWrite)
    (avoids : CendAvoidsLm1 expression)
    (resolves : CendDestResolvesAt control.context.pe cycle control.context.bar0
      control.context.bar1 control.context.tWord expression accesses.memory)
    (prepared : prepareParsedIntegerMaskInputThenMemoryALUWritesWithForwarding files oldSlots
      cycle accesses directive hasSingleLineMask flushSelection reduced
      = .ok (memoryWrites, omrWrite)) :
    ∀ item ∈ memoryWrites ++ [omrWrite], ∀ (width : PEMemory.Width)
      (address : Fin PEMemory.Bank.lm1.capacity),
      item.destination ≠ some ⟨PEMemory.Bank.lm1, width, address⟩ := by
  obtain ⟨bus, flags, memorySelection, writesEq, omrEq⟩ :=
    prepareParsedIntegerMaskInputThenMemoryALUWritesWithForwarding_shape files oldSlots cycle
      accesses directive hasSingleLineMask flushSelection reduced memoryWrites omrWrite prepared
  rw [writesEq]
  intro item member width address destination
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at member
  rcases member with first | second | third
  · subst item
    exact absurd destination (by simp)
  · subst item
    have bankNe := CendDestResolvesAt.bank_ne_lm1 resolves avoids
    exact bankNe (by rw [Option.some.inj destination])
  · subst item
    rw [omrEq] at destination
    exact absurd destination (by simp)



theorem memoryThenInput_memory_provenance
    (op : ParsedOp) (sources destinations : List ParsedOperand) (flush : Option ParsedMask)
    (text : String) (registers : ProofsLean.MNCore.Masks.RegisterFile)
    (directive : ParsedMaskDirective) (hasSingleLineMask : Bool)
    (group : Fin 4) (l2b : Fin 2) (l1b : Fin 8) (mab : Fin 16)
    (pe cycle : Fin 4) (bar0 bar1 : BitVec 12) (tWord : BitVec 32)
    (name : ParsedAluName) (precision : ParsedPrecision) (unsigned : Bool)
    (arg : Option (Fin 256))
    (operation : op = .alu name (some precision) unsigned arg)
    (accesses : ParsedIntegerMaskMemoryThenInputAccesses)
    (lowered : parsedIntegerMaskMemoryThenInputExprAccessesInLine?
      ⟨op, sources, destinations, flush, text⟩ registers directive
      hasSingleLineMask group l2b l1b mab pe cycle bar0 bar1 tWord = some accesses) :
    CendDestResolvesAt pe cycle bar0 bar1 tWord ⟨op, sources, destinations, flush, text⟩
      accesses.memory := by
  subst operation
  simp only [parsedIntegerMaskMemoryThenInputExprAccessesInLine?] at lowered
  repeat' split at lowered
  all_goals (try simp_all)
  all_goals
    (subst accesses
     exact ⟨_, by assumption, by simp⟩)

theorem inputThenMemory_memory_provenance
    (op : ParsedOp) (sources destinations : List ParsedOperand) (flush : Option ParsedMask)
    (text : String) (registers : ProofsLean.MNCore.Masks.RegisterFile)
    (directive : ParsedMaskDirective) (hasSingleLineMask : Bool)
    (group : Fin 4) (l2b : Fin 2) (l1b : Fin 8) (mab : Fin 16)
    (pe cycle : Fin 4) (bar0 bar1 : BitVec 12) (tWord : BitVec 32)
    (name : ParsedAluName) (precision : ParsedPrecision) (unsigned : Bool)
    (arg : Option (Fin 256))
    (operation : op = .alu name (some precision) unsigned arg)
    (accesses : ParsedIntegerMaskInputThenMemoryAccesses)
    (lowered : parsedIntegerMaskInputThenMemoryExprAccessesInLine?
      ⟨op, sources, destinations, flush, text⟩ registers directive
      hasSingleLineMask group l2b l1b mab pe cycle bar0 bar1 tWord = some accesses) :
    ParsedOperand.toDirectMemoryDestination? accesses.memoryOperand pe cycle bar0 bar1 tWord =
        some accesses.memory ∧ accesses.memoryOperand ∈ destinations := by
  subst operation
  simp only [parsedIntegerMaskInputThenMemoryExprAccessesInLine?] at lowered
  repeat' split at lowered
  all_goals (try simp_all)
  all_goals
    (subst accesses
     dsimp only
     exact ⟨by assumption, by simp⟩)


theorem bindMemory_resolves
    (op : ParsedOp) (sources : List ParsedOperand) (flush : Option ParsedMask) (text : String)
    (destination : ParsedOperand) (registers : ProofsLean.MNCore.Masks.RegisterFile)
    (directive : ParsedMaskDirective) (hasSingleLineMask : Bool)
    (group : Fin 4) (l2b : Fin 2) (l1b : Fin 8) (mab : Fin 16)
    (pe cycle : Fin 4) (bar0 bar1 : BitVec 12) (tWord : BitVec 32)
    (accesses : ParsedMaskedIntegerAccesses)
    (lowered : (ParsedExpr.toDirectMaskedIntegerAccessesInLine?
        { op := op, sources := sources, destinations := [destination], flush := flush, text := text }
        registers directive hasSingleLineMask group l2b l1b mab pe cycle bar0 bar1 tWord).bind
        (fun l => some (ParsedConstantDestination.memory l)) = some (.memory accesses)) :
    ParsedOperand.toDirectMemoryDestination? destination pe cycle bar0 bar1 tWord =
      some accesses.destination := by
  cases hl : ParsedExpr.toDirectMaskedIntegerAccessesInLine?
      { op := op, sources := sources, destinations := [destination], flush := flush, text := text }
      registers directive hasSingleLineMask group l2b l1b mab pe cycle bar0 bar1 tWord with
  | none => simp [hl] at lowered
  | some l =>
      simp only [hl, Option.bind_some] at lowered
      have lEq : l = accesses := by
        injection lowered with same
        injection same
      subst l
      obtain ⟨target, targetMem, targetResolved⟩ :=
        ParsedExpr.toDirectMaskedIntegerAccessesInLine?_destination_provenance
          { op := op, sources := sources, destinations := [destination], flush := flush,
            text := text } registers directive hasSingleLineMask group l2b l1b mab pe cycle
          bar0 bar1 tWord accesses hl
      simp only [List.mem_singleton] at targetMem
      rw [← targetMem]
      exact targetResolved

/-- The constant-destination lowering of a `.memory` target originates in a
destination operand, which resolves the same access. -/
theorem constantDestination_memory_provenance
    (op : ParsedOp) (sources destinations : List ParsedOperand) (flush : Option ParsedMask)
    (text : String) (registers : ProofsLean.MNCore.Masks.RegisterFile)
    (directive : ParsedMaskDirective) (hasSingleLineMask : Bool)
    (group : Fin 4) (l2b : Fin 2) (l1b : Fin 8) (mab : Fin 16)
    (pe cycle : Fin 4) (bar0 bar1 : BitVec 12) (tWord : BitVec 32)
    (destination : ParsedOperand) (accesses : ParsedMaskedIntegerAccesses)
    (lowered : ParsedExpr.toDirectMaskedConstantDestination?
      ⟨op, sources, destinations, flush, text⟩ registers directive
      hasSingleLineMask group l2b l1b mab pe cycle bar0 bar1 tWord destination =
        some (.memory accesses)) :
    ParsedOperand.toDirectMemoryDestination? destination pe cycle bar0 bar1 tWord =
      some accesses.destination := by
  cases destination with
  | nowrite => simp [ParsedExpr.toDirectMaskedConstantDestination?] at lowered
  | omr entry mask =>
      cases h : ParsedOperand.toMaskRegisterEntry? (.omr entry mask) with
      | none => simp [ParsedExpr.toDirectMaskedConstantDestination?, h] at lowered
      | some e =>
          cases h2 : ParsedOperand.resolveOmrWriteSelection? (.omr entry mask) registers cycle
              directive hasSingleLineMask with
          | none => simp [ParsedExpr.toDirectMaskedConstantDestination?, h, h2] at lowered
          | some s => simp [ParsedExpr.toDirectMaskedConstantDestination?, h, h2] at lowered
  | mem access neg ext rnd mask =>
      simp only [ParsedExpr.toDirectMaskedConstantDestination?] at lowered
      exact bindMemory_resolves op sources flush text _ registers directive hasSingleLineMask
        group l2b l1b mab pe cycle bar0 bar1 tWord accesses lowered
  | bar lm1 width mask =>
      simp only [ParsedExpr.toDirectMaskedConstantDestination?] at lowered
      exact bindMemory_resolves op sources flush text _ registers directive hasSingleLineMask
        group l2b l1b mab pe cycle bar0 bar1 tWord accesses lowered
  | forward kind neg ext rnd =>
      simp only [ParsedExpr.toDirectMaskedConstantDestination?] at lowered
      exact bindMemory_resolves op sources flush text _ registers directive hasSingleLineMask
        group l2b l1b mab pe cycle bar0 bar1 tWord accesses lowered
  | fixed kind =>
      simp only [ParsedExpr.toDirectMaskedConstantDestination?] at lowered
      exact bindMemory_resolves op sources flush text _ registers directive hasSingleLineMask
        group l2b l1b mab pe cycle bar0 bar1 tWord accesses lowered
  | matrix group_ width row =>
      simp only [ParsedExpr.toDirectMaskedConstantDestination?] at lowered
      exact bindMemory_resolves op sources flush text _ registers directive hasSingleLineMask
        group l2b l1b mab pe cycle bar0 bar1 tWord accesses lowered
  | l1bm width address =>
      simp only [ParsedExpr.toDirectMaskedConstantDestination?] at lowered
      exact bindMemory_resolves op sources flush text _ registers directive hasSingleLineMask
        group l2b l1b mab pe cycle bar0 bar1 tWord accesses lowered
  | l2bm address l2b_ =>
      simp only [ParsedExpr.toDirectMaskedConstantDestination?] at lowered
      exact bindMemory_resolves op sources flush text _ registers directive hasSingleLineMask
        group l2b l1b mab pe cycle bar0 bar1 tWord accesses lowered
  | dar address =>
      simp only [ParsedExpr.toDirectMaskedConstantDestination?] at lowered
      exact bindMemory_resolves op sources flush text _ registers directive hasSingleLineMask
        group l2b l1b mab pe cycle bar0 bar1 tWord accesses lowered


theorem noLm1_constant
    (op : ParsedOp) (sources destinations : List ParsedOperand) (flush : Option ParsedMask)
    (text : String) (files : IntegerRegisterFiles) (cycle : Fin 4)
    (registers : ProofsLean.MNCore.Masks.RegisterFile) (directive : ParsedMaskDirective)
    (hasSingleLineMask : Bool) (group : Fin 4) (l2b : Fin 2) (l1b : Fin 8) (mab : Fin 16)
    (pe : Fin 4) (bar0 bar1 : BitVec 12) (tWord : BitVec 32)
    (targets : List ParsedConstantDestination)
    (destinationWrites : List PreparedParsedMaskedWrite)
    (producerWrite : PreparedParsedMaskedWrite)
    (avoids : CendAvoidsLm1 ⟨op, sources, destinations, flush, text⟩)
    (lowered : ParsedExpr.toDirectMaskedConstantWrites?
      ⟨op, sources, destinations, flush, text⟩ registers directive hasSingleLineMask group l2b
      l1b mab pe cycle bar0 bar1 tWord = some targets)
    (prepared : prepareParsedMaskedConstantWrites files cycle targets = .ok destinationWrites)
    (producerNone : producerWrite.destination = none) :
    ∀ item ∈ destinationWrites ++ [producerWrite], ∀ (width : PEMemory.Width)
      (address : Fin PEMemory.Bank.lm1.capacity),
      item.destination ≠ some ⟨PEMemory.Bank.lm1, width, address⟩ := by
  have destinationMap := prepareParsedMaskedConstantWrites_destination_map files cycle targets
    destinationWrites prepared
  intro item member width address destination
  rcases List.mem_append.mp member with earlier | later
  · have mapMem : item.destination ∈ destinationWrites.map (fun w => w.destination) :=
      List.mem_map.mpr ⟨item, earlier, rfl⟩
    rw [destinationMap] at mapMem
    obtain ⟨target, targetMem, targetEq⟩ := List.mem_map.mp mapMem
    cases target with
    | memory access =>
        have itemEq : item.destination = some access.destination := targetEq.symm
        obtain ⟨source, sourceMem, sourceLowered⟩ :=
          toDirectMaskedConstantWrites?_mem_provenance
            ⟨op, sources, destinations, flush, text⟩ registers directive hasSingleLineMask
            group l2b l1b mab pe cycle bar0 bar1 tWord targets lowered (.memory access) targetMem
        have resolved := constantDestination_memory_provenance op sources destinations flush text
          registers directive hasSingleLineMask group l2b l1b mab pe cycle bar0 bar1 tWord
          source access sourceLowered
        have bankNe := CendDestResolvesAt.bank_ne_lm1
          ⟨source, resolved, sourceMem⟩ avoids
        rw [itemEq] at destination
        exact bankNe (by rw [Option.some.inj destination])
    | maskRegister entry =>
        simp only [ParsedConstantDestination.destinationOption] at targetEq
        rw [← targetEq] at destination
        exact absurd destination (by simp)
    | noWrite =>
        simp only [ParsedConstantDestination.destinationOption] at targetEq
        rw [← targetEq] at destination
        exact absurd destination (by simp)
  · rw [List.mem_singleton] at later
    subst item
    rw [producerNone] at destination
    exact absurd destination (by simp)



theorem prepareParsedIntegerALUExprCycle_noLm1
    (files : IntegerRegisterFiles)
    (oldSlots nextSlots : ProofsLean.MNCore.Forwarding.Slots)
    (op : ParsedOp) (sources destinations : List ParsedOperand) (flush : Option ParsedMask)
    (text : String) (control : ParsedMaskExecutionControl)
    (hsm nf reduced : Bool) (cycle : Fin 4)
    (avoids : CendAvoidsLm1 ⟨op, sources, destinations, flush, text⟩)
    (writes : List PreparedParsedMaskedWrite)
    (slots : ProofsLean.MNCore.Forwarding.Slots)
    (prep : prepareParsedIntegerALUExprCycle files oldSlots nextSlots
      ⟨op, sources, destinations, flush, text⟩ control hsm nf reduced cycle = .ok (writes, slots)) :
    ∀ write ∈ writes, ∀ (width : PEMemory.Width)
      (address : Fin PEMemory.Bank.lm1.capacity),
      write.destination ≠ some ⟨PEMemory.Bank.lm1, width, address⟩ := by
  cases op with
  | alu name precision unsigned arg =>
      cases precision with
      | none =>
          unfold prepareParsedIntegerALUExprCycle at prep
          dsimp only at prep
          simp only [ParsedExpr.toDirectMaskedIntegerAccessesInLine?,
            ParsedExpr.toDirectMaskedIntegerWritesInLine?,
            parsedIntegerMaskExprAccessesInLine?,
            parsedIntegerNoWriteExprAccessesInLine?,
            parsedIntegerBarExprAccessesInLine?,
            parsedIntegerMaskInputExprAccessesInLine?,
            parsedIntegerMaskMemoryThenInputExprAccessesInLine?,
            parsedIntegerMaskInputThenMemoryExprAccessesInLine?,
            ParsedOp.integerRequest, ParsedOp.executionRequest] at prep
          cases destinations with
          | nil => simp at prep
          | cons destination rest =>
              cases destination with
              | omr entry mask =>
                  cases rest with
                  | nil =>
                      cases entry with
                      | mk value valueLt => cases value <;> simp at prep
                  | cons item items => simp at prep
              | mem access negated extended rounded mask => simp at prep
              | bar lm1 width mask => simp at prep
              | forward kind negated extended rounded => simp at prep
              | fixed kind => simp at prep
              | matrix group width row => simp at prep
              | nowrite => simp at prep
              | l1bm width address => simp at prep
              | l2bm address l2b => simp at prep
              | dar address => simp at prep
      | some parsedPrecision =>
          unfold prepareParsedIntegerALUExprCycle at prep
          dsimp only at prep
          cases hdirect : ParsedExpr.toDirectMaskedIntegerAccessesInLine?
              ⟨.alu name (some parsedPrecision) unsigned arg, sources, destinations, flush, text⟩
              files.maskRegisters control.directive hsm control.context.group
              control.context.l2b control.context.l1b control.context.mab
              control.context.pe cycle control.context.bar0 control.context.bar1
              control.context.tWord with
          | some accesses =>
              rw [hdirect] at prep
              dsimp only at prep
              cases hprepared : prepareParsedMaskedWriteWithForwarding files oldSlots cycle
                  accesses reduced with
              | failure => rw [hprepared] at prep; cases prep
              | unknown => rw [hprepared] at prep; cases prep
              | ok write =>
                  rw [hprepared] at prep
                  dsimp only at prep
                  cases hupdated : updateParsedIntegerALUForwardingCycle nextSlots cycle
                      (.ok write) nf with
                  | failure => rw [hupdated] at prep; cases prep
                  | unknown => rw [hupdated] at prep; cases prep
                  | ok slots' =>
                      rw [hupdated] at prep
                      dsimp only at prep
                      simp only [StepResult.ok.injEq, Prod.mk.injEq] at prep
                      rw [← prep.1]
                      exact noLm1_direct files oldSlots _ control hsm nf reduced cycle accesses
                        write avoids hdirect hprepared
          | none =>
              rw [hdirect] at prep
              dsimp only at prep
              cases hmultiple : ParsedExpr.toDirectMaskedIntegerWritesInLine?
                  ⟨.alu name (some parsedPrecision) unsigned arg, sources, destinations, flush,
                    text⟩ files.maskRegisters control.directive hsm control.context.group
                  control.context.l2b control.context.l1b control.context.mab
                  control.context.pe cycle control.context.bar0 control.context.bar1
                  control.context.tWord with
              | some accessList =>
                  cases accessList with
                  | nil => rw [hmultiple] at prep; cases prep
                  | cons access rest =>
                      rw [hmultiple] at prep
                      dsimp only at prep
                      cases hprepared : prepareParsedMaskedWriteWithForwarding files oldSlots
                          cycle access reduced with
                      | failure => rw [hprepared] at prep; cases prep
                      | unknown => rw [hprepared] at prep; cases prep
                      | ok write =>
                          rw [hprepared] at prep
                          dsimp only at prep
                          cases hupdated : updateParsedIntegerALUForwardingCycle nextSlots
                              cycle (.ok write) nf with
                          | failure => rw [hupdated] at prep; cases prep
                          | unknown => rw [hupdated] at prep; cases prep
                          | ok slots' =>
                              rw [hupdated] at prep
                              dsimp only at prep
                              simp only [StepResult.ok.injEq, Prod.mk.injEq] at prep
                              rw [← prep.1]
                              exact noLm1_multiple files oldSlots _ control hsm nf reduced cycle
                                access rest write avoids hmultiple hprepared
              | none =>
                  rw [hmultiple] at prep
                  dsimp only at prep
                  cases homr : parsedIntegerMaskExprAccessesInLine?
                      ⟨.alu name (some parsedPrecision) unsigned arg, sources, destinations,
                        flush, text⟩ files.maskRegisters control.directive hsm
                      control.context.pe cycle control.context.bar0 control.context.bar1
                      control.context.tWord with
                  | some accesses =>
                      rw [homr] at prep
                      dsimp only at prep
                      cases hflush : resolveFlushSelection? flush files.maskRegisters cycle with
                      | none => rw [hflush] at prep; cases prep
                      | some flushSelection =>
                          rw [hflush] at prep
                          dsimp only at prep
                          cases hprepared : prepareParsedIntegerMaskALUWriteWithForwarding files
                              oldSlots cycle accesses flushSelection reduced with
                          | failure => rw [hprepared] at prep; cases prep
                          | unknown => rw [hprepared] at prep; cases prep
                          | ok write =>
                              rw [hprepared] at prep
                              dsimp only at prep
                              cases hupdated : updateParsedIntegerALUForwardingCycle nextSlots
                                  cycle (.ok write) nf with
                              | failure =>
                                  rw [hupdated] at prep; cases prep
                              | unknown =>
                                  rw [hupdated] at prep; cases prep
                              | ok slots' =>
                                  rw [hupdated] at prep
                                  dsimp only at prep
                                  simp only [StepResult.ok.injEq, Prod.mk.injEq] at prep
                                  rw [← prep.1]
                                  exact noLm1_singleton_none write
                                    (prepareParsedIntegerMaskALUWriteWithForwarding_destination_none
                                      files oldSlots cycle accesses flushSelection reduced write
                                      hprepared)
                  | none =>
                      rw [homr] at prep
                      dsimp only at prep
                      cases hnoWrite : parsedIntegerNoWriteExprAccessesInLine?
                          ⟨.alu name (some parsedPrecision) unsigned arg, sources, destinations,
                            flush, text⟩ files.maskRegisters control.context.pe cycle
                          control.context.group control.context.l2b control.context.l1b
                          control.context.mab control.context.bar0 control.context.bar1
                          control.context.tWord with
                      | some accesses =>
                          rw [hnoWrite] at prep
                          dsimp only at prep
                          cases hprepared : prepareParsedIntegerNoWriteALUWithForwarding files
                              oldSlots cycle accesses reduced with
                          | failure => rw [hprepared] at prep; cases prep
                          | unknown => rw [hprepared] at prep; cases prep
                          | ok write =>
                              rw [hprepared] at prep
                              dsimp only at prep
                              cases hupdated : updateParsedIntegerALUForwardingCycle nextSlots
                                  cycle (.ok write) nf with
                              | failure =>
                                  rw [hupdated] at prep; cases prep
                              | unknown =>
                                  rw [hupdated] at prep; cases prep
                              | ok slots' =>
                                  rw [hupdated] at prep
                                  dsimp only at prep
                                  simp only [StepResult.ok.injEq, Prod.mk.injEq] at prep
                                  rw [← prep.1]
                                  exact noLm1_singleton_none write
                                    (prepareParsedIntegerNoWriteALUWithForwarding_destination_none
                                      files oldSlots cycle accesses reduced write hprepared)
                      | none =>
                          rw [hnoWrite] at prep
                          dsimp only at prep
                          cases hbar : parsedIntegerBarExprAccessesInLine?
                              ⟨.alu name (some parsedPrecision) unsigned arg, sources,
                                destinations, flush, text⟩ files.maskRegisters
                              control.directive hsm control.context.group control.context.l2b
                              control.context.l1b control.context.mab control.context.pe cycle
                              control.context.bar0 control.context.bar1 control.context.tWord with
                          | some accesses =>
                              rw [hbar] at prep
                              dsimp only at prep
                              cases hprepared : prepareParsedIntegerBarALUWithForwarding files
                                  oldSlots cycle accesses reduced with
                              | failure => rw [hprepared] at prep; cases prep
                              | unknown => rw [hprepared] at prep; cases prep
                              | ok write =>
                                  rw [hprepared] at prep
                                  dsimp only at prep
                                  cases hupdated : updateParsedIntegerALUForwardingCycle
                                      nextSlots cycle (.ok write) nf with
                                  | failure =>
                                      rw [hupdated] at prep; cases prep
                                  | unknown =>
                                      rw [hupdated] at prep; cases prep
                                  | ok slots' =>
                                      rw [hupdated] at prep
                                      dsimp only at prep
                                      simp only [StepResult.ok.injEq, Prod.mk.injEq] at prep
                                      rw [← prep.1]
                                      exact noLm1_singleton_none write
                                        (prepareParsedIntegerBarALUWithForwarding_destination_none
                                          files oldSlots cycle accesses reduced write hprepared)
                          | none =>
                              rw [hbar] at prep
                              dsimp only at prep
                              cases hinput : parsedIntegerMaskInputExprAccessesInLine?
                                  ⟨.alu name (some parsedPrecision) unsigned arg, sources,
                                    destinations, flush, text⟩ files.maskRegisters
                                  control.directive hsm control.context.group
                                  control.context.l2b control.context.l1b control.context.mab
                                  control.context.pe cycle control.context.bar0
                                  control.context.bar1 control.context.tWord with
                              | some accesses =>
                                  rw [hinput] at prep
                                  dsimp only at prep
                                  cases hflush : resolveFlushSelection? flush
                                      files.maskRegisters cycle with
                                  | none => rw [hflush] at prep; cases prep
                                  | some flushSelection =>
                                      rw [hflush] at prep
                                      dsimp only at prep
                                      cases hprepared :
                                          prepareParsedIntegerMaskInputALUWriteWithForwarding
                                            files oldSlots cycle accesses flushSelection reduced with
                                      | failure =>
                                          rw [hprepared] at prep; cases prep
                                      | unknown =>
                                          rw [hprepared] at prep; cases prep
                                      | ok write =>
                                          rw [hprepared] at prep
                                          dsimp only at prep
                                          cases hupdated :
                                              updateParsedIntegerALUForwardingCycle nextSlots
                                                cycle (.ok write) nf with
                                          | failure =>
                                              rw [hupdated] at prep; cases prep
                                          | unknown =>
                                              rw [hupdated] at prep; cases prep
                                          | ok slots' =>
                                              rw [hupdated] at prep
                                              dsimp only at prep
                                              simp only [StepResult.ok.injEq, Prod.mk.injEq] at prep
                                              rw [← prep.1]
                                              exact noLm1_singleton_none write
                                                (prepareParsedIntegerMaskInputALUWriteWithForwarding_destination_none
                                                  files oldSlots cycle accesses flushSelection
                                                  reduced write hprepared)
                              | none =>
                                  rw [hinput] at prep
                                  dsimp only at prep
                                  cases hmixed :
                                      parsedIntegerMaskMemoryThenInputExprAccessesInLine?
                                        ⟨.alu name (some parsedPrecision) unsigned arg, sources,
                                          destinations, flush, text⟩ files.maskRegisters
                                        control.directive hsm control.context.group
                                        control.context.l2b control.context.l1b
                                        control.context.mab control.context.pe cycle
                                        control.context.bar0 control.context.bar1
                                        control.context.tWord with
                                  | some accesses =>
                                      rw [hmixed] at prep
                                      dsimp only at prep
                                      cases hflush : resolveFlushSelection? flush
                                          files.maskRegisters cycle with
                                      | none => rw [hflush] at prep; cases prep
                                      | some flushSelection =>
                                          rw [hflush] at prep
                                          dsimp only at prep
                                          cases hprepared :
                                              prepareParsedIntegerMaskMemoryThenInputALUWritesWithForwarding
                                                files oldSlots cycle accesses flushSelection
                                                reduced with
                                          | failure =>
                                              rw [hprepared] at prep; cases prep
                                          | unknown =>
                                              rw [hprepared] at prep; cases prep
                                          | ok pair =>
                                              obtain ⟨memoryWrites, omrWrite⟩ := pair
                                              rw [hprepared] at prep
                                              dsimp only at prep
                                              cases hupdated :
                                                  updateParsedIntegerALUForwardingCycle
                                                    nextSlots cycle (.ok omrWrite) nf with
                                              | failure =>
                                                  rw [hupdated] at prep; cases prep
                                              | unknown =>
                                                  rw [hupdated] at prep; cases prep
                                              | ok slots' =>
                                                  rw [hupdated] at prep
                                                  dsimp only at prep
                                                  simp only [StepResult.ok.injEq,
                                                    Prod.mk.injEq] at prep
                                                  rw [← prep.1]
                                                  exact noLm1_memoryThenInput files oldSlots
                                                    control cycle _ accesses flushSelection
                                                    reduced memoryWrites omrWrite avoids
                                                    (memoryThenInput_memory_provenance _ sources _
                                                      flush text files.maskRegisters
                                                      control.directive hsm control.context.group
                                                      control.context.l2b control.context.l1b
                                                      control.context.mab control.context.pe
                                                      cycle control.context.bar0
                                                      control.context.bar1 control.context.tWord
                                                      name parsedPrecision unsigned arg rfl
                                                      accesses hmixed)
                                                    hprepared
                                  | none =>
                                      rw [hmixed] at prep
                                      dsimp only at prep
                                      cases hreverse :
                                          parsedIntegerMaskInputThenMemoryExprAccessesInLine?
                                            ⟨.alu name (some parsedPrecision) unsigned arg,
                                              sources, destinations, flush, text⟩
                                            files.maskRegisters control.directive hsm
                                            control.context.group control.context.l2b
                                            control.context.l1b control.context.mab
                                            control.context.pe cycle control.context.bar0
                                            control.context.bar1 control.context.tWord with
                                      | some accesses =>
                                          rw [hreverse] at prep
                                          dsimp only at prep
                                          cases hflush : resolveFlushSelection? flush
                                              files.maskRegisters cycle with
                                          | none =>
                                              rw [hflush] at prep; cases prep
                                          | some flushSelection =>
                                              rw [hflush] at prep
                                              dsimp only at prep
                                              cases hprepared :
                                                  prepareParsedIntegerMaskInputThenMemoryALUWritesWithForwarding
                                                    files oldSlots cycle accesses
                                                    control.directive hsm flushSelection
                                                    reduced with
                                              | failure =>
                                                  rw [hprepared] at prep; cases prep
                                              | unknown =>
                                                  rw [hprepared] at prep; cases prep
                                              | ok pair =>
                                                  obtain ⟨memoryWrites, omrWrite⟩ := pair
                                                  rw [hprepared] at prep
                                                  dsimp only at prep
                                                  cases hupdated :
                                                      updateParsedIntegerALUForwardingCycle
                                                        nextSlots cycle (.ok omrWrite) nf with
                                                  | failure =>
                                                      rw [hupdated] at prep; cases prep
                                                  | unknown =>
                                                      rw [hupdated] at prep; cases prep
                                                  | ok slots' =>
                                                      rw [hupdated] at prep
                                                      dsimp only at prep
                                                      simp only [StepResult.ok.injEq,
                                                        Prod.mk.injEq] at prep
                                                      rw [← prep.1]
                                                      intro item member
                                                      exact noLm1_inputThenMemory files oldSlots
                                                        control cycle _ accesses
                                                        control.directive hsm flushSelection
                                                        reduced memoryWrites omrWrite avoids
                                                        (let provenance :=
                                                          inputThenMemory_memory_provenance _
                                                            sources _ flush text
                                                            files.maskRegisters
                                                            control.directive hsm
                                                            control.context.group
                                                            control.context.l2b
                                                            control.context.l1b
                                                            control.context.mab
                                                            control.context.pe cycle
                                                            control.context.bar0
                                                            control.context.bar1
                                                            control.context.tWord name
                                                            parsedPrecision unsigned arg rfl
                                                            accesses hreverse
                                                         ⟨accesses.memoryOperand,
                                                           provenance.1, provenance.2⟩)
                                                        hprepared item
                                                        (List.mem_append_left _ member)
                                      | none =>
                                          rw [hreverse] at prep
                                          dsimp only at prep
                                          split at prep
                                          · cases prep
                                          · cases prep
  | zero =>
      unfold prepareParsedIntegerALUExprCycle at prep
      dsimp only at prep
      cases hlowered : ParsedExpr.toDirectMaskedConstantWrites?
          ⟨.zero, sources, destinations, flush, text⟩ files.maskRegisters control.directive
          hsm control.context.group control.context.l2b control.context.l1b control.context.mab
          control.context.pe cycle control.context.bar0 control.context.bar1
          control.context.tWord with
      | none => rw [hlowered] at prep; cases prep
      | some targets =>
          rw [hlowered] at prep
          dsimp only at prep
          cases hprepared : prepareParsedMaskedConstantWrites files cycle targets with
          | failure => rw [hprepared] at prep; cases prep
          | unknown => rw [hprepared] at prep; cases prep
          | ok destinationWrites =>
              rw [hprepared] at prep
              dsimp only at prep
              rw [zero_has_execution_request] at prep
              dsimp only at prep
              cases hflush : resolveFlushSelection? flush files.maskRegisters cycle with
              | none => rw [hflush] at prep; cases prep
              | some flushSelection =>
                  rw [hflush] at prep
                  dsimp only at prep
                  cases hupdated : updateParsedIntegerALUForwardingCycle nextSlots cycle
                      (.ok ⟨none, none, unpackALUBus (parsedOutputAfterFlush flushSelection
                        (evaluateParsedExecutionRequest ParsedExecutionRequest.zero
                          ⟨0, 0⟩ ⟨0, 0⟩ reduced).value), ⟨BitVec.allOnes 4, true⟩⟩) nf with
                  | failure => rw [hupdated] at prep; cases prep
                  | unknown => rw [hupdated] at prep; cases prep
                  | ok slots' =>
                      rw [hupdated] at prep
                      dsimp only at prep
                      simp only [StepResult.ok.injEq, Prod.mk.injEq] at prep
                      rw [← prep.1]
                      exact noLm1_constant _ sources destinations flush text files cycle
                        files.maskRegisters control.directive hsm control.context.group
                        control.context.l2b control.context.l1b control.context.mab
                        control.context.pe control.context.bar0 control.context.bar1
                        control.context.tWord targets destinationWrites _ avoids hlowered
                        hprepared rfl
  | immediate payload sparse =>
      unfold prepareParsedIntegerALUExprCycle at prep
      dsimp only at prep
      cases hlowered : ParsedExpr.toDirectMaskedConstantWrites?
          ⟨.immediate payload sparse, sources, destinations, flush, text⟩ files.maskRegisters
          control.directive hsm control.context.group control.context.l2b control.context.l1b
          control.context.mab control.context.pe cycle control.context.bar0 control.context.bar1
          control.context.tWord with
      | none => rw [hlowered] at prep; cases prep
      | some targets =>
          rw [hlowered] at prep
          dsimp only at prep
          cases hprepared : prepareParsedMaskedConstantWrites files cycle targets with
          | failure => rw [hprepared] at prep; cases prep
          | unknown => rw [hprepared] at prep; cases prep
          | ok destinationWrites =>
              rw [hprepared] at prep
              dsimp only at prep
              rw [immediate_has_execution_request] at prep
              dsimp only at prep
              cases hflush : resolveFlushSelection? flush files.maskRegisters cycle with
              | none => rw [hflush] at prep; cases prep
              | some flushSelection =>
                  rw [hflush] at prep
                  dsimp only at prep
                  cases hupdated : updateParsedIntegerALUForwardingCycle nextSlots cycle
                      (.ok ⟨none, none, unpackALUBus (parsedOutputAfterFlush flushSelection
                        (evaluateParsedExecutionRequest
                          (ParsedExecutionRequest.immediate payload sparse)
                          ⟨0, 0⟩ ⟨0, 0⟩ reduced).value), ⟨BitVec.allOnes 4, true⟩⟩) nf with
                  | failure => rw [hupdated] at prep; cases prep
                  | unknown => rw [hupdated] at prep; cases prep
                  | ok slots' =>
                      rw [hupdated] at prep
                      dsimp only at prep
                      simp only [StepResult.ok.injEq, Prod.mk.injEq] at prep
                      rw [← prep.1]
                      exact noLm1_constant _ sources destinations flush text files cycle
                        files.maskRegisters control.directive hsm control.context.group
                        control.context.l2b control.context.l1b control.context.mab
                        control.context.pe control.context.bar0 control.context.bar1
                        control.context.tWord targets destinationWrites _ avoids hlowered
                        hprepared rfl
  | mau precision matrix kind half round =>
      unfold prepareParsedIntegerALUExprCycle at prep
      simp at prep
  | matrixWrite precision =>
      unfold prepareParsedIntegerALUExprCycle at prep
      simp at prep
  | matrixRead precision =>
      unfold prepareParsedIntegerALUExprCycle at prep
      simp at prep
  | wait tag =>
      unfold prepareParsedIntegerALUExprCycle at prep
      simp at prep
  | noforward =>
      unfold prepareParsedIntegerALUExprCycle at prep
      simp at prep
  | l1bm operation =>
      unfold prepareParsedIntegerALUExprCycle at prep
      simp at prep
  | l2bm operation =>
      unfold prepareParsedIntegerALUExprCycle at prep
      simp at prep


theorem prepareParsedIntegerALUExprCycles_four_general
    (files : IntegerRegisterFiles) (oldSlots initialOutputSlots : ProofsLean.MNCore.Forwarding.Slots)
    (e : ParsedExpr) (control : ParsedMaskExecutionControl) (hsm nf r : Bool)
    (writes : List PreparedParsedMaskedWrite) (slots : ProofsLean.MNCore.Forwarding.Slots)
    (prep : prepareParsedIntegerALUExprCycles files oldSlots initialOutputSlots e control hsm nf r =
      .ok (writes, slots)) :
    ∃ (w0 w1 w2 w3 : List PreparedParsedMaskedWrite)
      (s1 s2 s3 : ProofsLean.MNCore.Forwarding.Slots),
      prepareParsedIntegerALUExprCycle files oldSlots initialOutputSlots e control hsm nf r
          (0 : Fin 4) = .ok (w0, s1) ∧
      prepareParsedIntegerALUExprCycle files oldSlots s1 e control hsm nf r
          (1 : Fin 4) = .ok (w1, s2) ∧
      prepareParsedIntegerALUExprCycle files oldSlots s2 e control hsm nf r
          (2 : Fin 4) = .ok (w2, s3) ∧
      prepareParsedIntegerALUExprCycle files oldSlots s3 e control hsm nf r
          (3 : Fin 4) = .ok (w3, slots) ∧
      writes = w0 ++ w1 ++ w2 ++ w3 := by
  unfold prepareParsedIntegerALUExprCycles at prep
  simp only [parsedIntegerALUCycles] at prep
  unfold prepareParsedIntegerALUCycles at prep
  cases h0 : prepareParsedIntegerALUExprCycle files oldSlots initialOutputSlots e control hsm nf r
      (0 : Fin 4) with
  | failure => simp [h0] at prep
  | unknown => simp [h0] at prep
  | ok result =>
      obtain ⟨w0, s1⟩ := result
      simp only [h0] at prep
      unfold prepareParsedIntegerALUCycles at prep
      cases h1 : prepareParsedIntegerALUExprCycle files oldSlots s1 e control hsm nf r
          (1 : Fin 4) with
      | failure => simp [h1] at prep
      | unknown => simp [h1] at prep
      | ok result =>
          obtain ⟨w1, s2⟩ := result
          simp only [h1] at prep
          unfold prepareParsedIntegerALUCycles at prep
          cases h2 : prepareParsedIntegerALUExprCycle files oldSlots s2 e control hsm nf r
              (2 : Fin 4) with
          | failure => simp [h2] at prep
          | unknown => simp [h2] at prep
          | ok result =>
              obtain ⟨w2, s3⟩ := result
              simp only [h2] at prep
              unfold prepareParsedIntegerALUCycles at prep
              cases h3 : prepareParsedIntegerALUExprCycle files oldSlots s3 e control hsm nf r
                  (3 : Fin 4) with
              | failure => simp [h3] at prep
              | unknown => simp [h3] at prep
              | ok result =>
                  obtain ⟨w3, s4⟩ := result
                  simp only [h3, List.nil_append, StepResult.ok.injEq, Prod.mk.injEq] at prep
                  obtain ⟨rfl, rfl⟩ := prep
                  exact ⟨w0, w1, w2, w3, s1, s2, s3, rfl, h1, h2, h3, rfl⟩

theorem prepareParsedIntegerALUExprCycles_noLm1
    (files : IntegerRegisterFiles) (oldSlots initialOutputSlots : ProofsLean.MNCore.Forwarding.Slots)
    (op : ParsedOp) (sources destinations : List ParsedOperand) (flush : Option ParsedMask)
    (text : String) (control : ParsedMaskExecutionControl) (hsm nf reduced : Bool)
    (avoids : CendAvoidsLm1 ⟨op, sources, destinations, flush, text⟩)
    (writes : List PreparedParsedMaskedWrite)
    (slots : ProofsLean.MNCore.Forwarding.Slots)
    (prep : prepareParsedIntegerALUExprCycles files oldSlots initialOutputSlots
      ⟨op, sources, destinations, flush, text⟩ control hsm nf reduced = .ok (writes, slots)) :
    ∀ write ∈ writes, ∀ (width : PEMemory.Width)
      (address : Fin PEMemory.Bank.lm1.capacity),
      write.destination ≠ some ⟨PEMemory.Bank.lm1, width, address⟩ := by
  obtain ⟨w0, w1, w2, w3, s1, s2, s3, h0, h1, h2, h3, writesEq⟩ :=
    prepareParsedIntegerALUExprCycles_four_general files oldSlots initialOutputSlots _ control
      hsm nf reduced writes slots prep
  subst writesEq
  intro write member width address destination
  rcases List.mem_append.mp member with earlier | later
  · rcases List.mem_append.mp earlier with earlier | inW2
    · rcases List.mem_append.mp earlier with inW0 | inW1
      · exact prepareParsedIntegerALUExprCycle_noLm1 files oldSlots initialOutputSlots op sources
          destinations flush text control hsm nf reduced _ avoids w0 s1 h0 write inW0 width
          address destination
      · exact prepareParsedIntegerALUExprCycle_noLm1 files oldSlots s1 op sources destinations
          flush text control hsm nf reduced _ avoids w1 s2 h1 write inW1 width address destination
    · exact prepareParsedIntegerALUExprCycle_noLm1 files oldSlots s2 op sources destinations
        flush text control hsm nf reduced _ avoids w2 s3 h2 write inW2 width address destination
  · exact prepareParsedIntegerALUExprCycle_noLm1 files oldSlots s3 op sources destinations flush
      text control hsm nf reduced _ avoids w3 slots h3 write later width address destination

theorem prepareParsedIntegerMatrixReadLineExpression_noLm1
    (files : IntegerRegisterFiles) (oldSlots nextSlots : ProofsLean.MNCore.Forwarding.Slots)
    (store : ParsedMatrixReadStore) (expression : ParsedExpr)
    (control : ParsedMaskExecutionControl) (hsm nf reduced : Bool)
    (plain : parsedExprIsPlainIntegerALU expression = true)
    (avoids : CendAvoidsLm1 expression)
    (writes : List PreparedParsedMaskedWrite) (slots : ProofsLean.MNCore.Forwarding.Slots)
    (bars : List (Bool × BitVec 12))
    (prep : prepareParsedIntegerMatrixReadLineExpression files oldSlots nextSlots store expression
      control hsm nf reduced = .ok (writes, slots, bars)) :
    ∀ write ∈ writes, ∀ (width : PEMemory.Width)
      (address : Fin PEMemory.Bank.lm1.capacity),
      write.destination ≠ some ⟨PEMemory.Bank.lm1, width, address⟩ := by
  obtain ⟨op, sources, destinations, flush, text⟩ := expression
  cases op with
  | alu name precision unsigned arg =>
      unfold prepareParsedIntegerMatrixReadLineExpression at prep
      cases h : prepareParsedIntegerALUExprCycles files oldSlots nextSlots
          ⟨.alu name precision unsigned arg, sources, destinations, flush, text⟩ control
          hsm nf reduced with
      | failure => simp [h] at prep
      | unknown => simp [h] at prep
      | ok result =>
          obtain ⟨writes', slots'⟩ := result
          simp only [h, StepResult.ok.injEq, Prod.mk.injEq] at prep
          obtain ⟨writesEq, -, -⟩ := prep
          subst writesEq
          exact prepareParsedIntegerALUExprCycles_noLm1 files oldSlots nextSlots _ sources
            destinations flush text control hsm nf reduced avoids _ _ h
  | zero =>
      unfold prepareParsedIntegerMatrixReadLineExpression at prep
      cases h : prepareParsedIntegerALUExprCycles files oldSlots nextSlots
          ⟨.zero, sources, destinations, flush, text⟩ control hsm nf reduced with
      | failure => simp [h] at prep
      | unknown => simp [h] at prep
      | ok result =>
          obtain ⟨writes', slots'⟩ := result
          simp only [h, StepResult.ok.injEq, Prod.mk.injEq] at prep
          obtain ⟨writesEq, -, -⟩ := prep
          subst writesEq
          exact prepareParsedIntegerALUExprCycles_noLm1 files oldSlots nextSlots _ sources
            destinations flush text control hsm nf reduced avoids _ _ h
  | immediate payload sparse =>
      unfold prepareParsedIntegerMatrixReadLineExpression at prep
      cases h : prepareParsedIntegerALUExprCycles files oldSlots nextSlots
          ⟨.immediate payload sparse, sources, destinations, flush, text⟩ control hsm nf reduced with
      | failure => simp [h] at prep
      | unknown => simp [h] at prep
      | ok result =>
          obtain ⟨writes', slots'⟩ := result
          simp only [h, StepResult.ok.injEq, Prod.mk.injEq] at prep
          obtain ⟨writesEq, -, -⟩ := prep
          subst writesEq
          exact prepareParsedIntegerALUExprCycles_noLm1 files oldSlots nextSlots _ sources
            destinations flush text control hsm nf reduced avoids _ _ h
  | mau precision matrix kind half round =>
      simp [parsedExprIsPlainIntegerALU, parsedExprIsIntegerProducer] at plain
  | matrixWrite precision =>
      simp [parsedExprIsPlainIntegerALU, parsedExprIsIntegerProducer] at plain
  | matrixRead precision =>
      simp [parsedExprIsPlainIntegerALU, parsedExprIsIntegerProducer] at plain
  | wait tag => simp [parsedExprIsPlainIntegerALU, parsedExprIsIntegerProducer] at plain
  | noforward => simp [parsedExprIsPlainIntegerALU, parsedExprIsIntegerProducer] at plain
  | l1bm operation => simp [parsedExprIsPlainIntegerALU, parsedExprIsIntegerProducer] at plain
  | l2bm operation => simp [parsedExprIsPlainIntegerALU, parsedExprIsIntegerProducer] at plain

theorem prepareParsedIntegerMatrixReadLineExpressions_noLm1
    (files : IntegerRegisterFiles) (oldSlots : ProofsLean.MNCore.Forwarding.Slots)
    (store : ParsedMatrixReadStore) (control : ParsedMaskExecutionControl)
    (hsm nf reduced : Bool) :
    ∀ (expressions : List ParsedExpr) (writes0 : List PreparedParsedMaskedWrite)
      (startSlots : ProofsLean.MNCore.Forwarding.Slots)
      (barUpdates0 : List (Bool × BitVec 12))
      (writes : List PreparedParsedMaskedWrite)
      (nextSlots : ProofsLean.MNCore.Forwarding.Slots)
      (barUpdates : List (Bool × BitVec 12)),
      expressions.all parsedExprIsPlainIntegerALU = true →
      (∀ expression ∈ expressions, CendAvoidsLm1 expression) →
      (∀ write ∈ writes0, ∀ (width : PEMemory.Width)
        (address : Fin PEMemory.Bank.lm1.capacity),
        write.destination ≠ some ⟨PEMemory.Bank.lm1, width, address⟩) →
      prepareParsedIntegerMatrixReadLineExpressions files oldSlots store control hsm nf
        reduced expressions writes0 startSlots barUpdates0 = .ok (writes, nextSlots, barUpdates) →
      ∀ write ∈ writes, ∀ (width : PEMemory.Width)
        (address : Fin PEMemory.Bank.lm1.capacity),
        write.destination ≠ some ⟨PEMemory.Bank.lm1, width, address⟩ := by
  intro expressions
  induction expressions with
  | nil =>
      intro writes0 startSlots barUpdates0 writes nextSlots barUpdates _plain _avoids kept prep
      simp only [prepareParsedIntegerMatrixReadLineExpressions, StepResult.ok.injEq,
        Prod.mk.injEq] at prep
      obtain ⟨writesEq, -, -⟩ := prep
      subst writesEq
      exact kept
  | cons expression rest ih =>
      intro writes0 startSlots barUpdates0 writes nextSlots barUpdates plain avoids kept prep
      have expressionPlain : parsedExprIsPlainIntegerALU expression = true :=
        List.all_eq_true.mp plain expression (by simp)
      have restPlain : rest.all parsedExprIsPlainIntegerALU = true := by
        rw [List.all_eq_true]
        intro item member
        exact List.all_eq_true.mp plain item (List.mem_cons_of_mem _ member)
      have expressionAvoids : CendAvoidsLm1 expression := avoids expression (by simp)
      have restAvoids : ∀ item ∈ rest, CendAvoidsLm1 item :=
        fun item member => avoids item (List.mem_cons_of_mem _ member)
      unfold prepareParsedIntegerMatrixReadLineExpressions at prep
      cases head : prepareParsedIntegerMatrixReadLineExpression files oldSlots startSlots store
          expression control hsm nf reduced with
      | failure => rw [head] at prep; cases prep
      | unknown => rw [head] at prep; cases prep
      | ok headResult =>
          obtain ⟨headWrites, headSlots, headBars⟩ := headResult
          rw [head] at prep
          dsimp only at prep
          cases tail : prepareParsedIntegerMatrixReadLineExpressions files oldSlots store
              control hsm nf reduced rest (writes0 ++ headWrites) headSlots
              (barUpdates0 ++ headBars) with
          | failure => rw [tail] at prep; cases prep
          | unknown => rw [tail] at prep; cases prep
          | ok tailResult =>
              obtain ⟨tailWrites, tailSlots, tailBars⟩ := tailResult
              rw [tail] at prep
              simp only [StepResult.ok.injEq, Prod.mk.injEq] at prep
              obtain ⟨writesEq, -, -⟩ := prep
              subst writesEq
              have headKept : ∀ write ∈ headWrites, ∀ (width : PEMemory.Width)
                  (address : Fin PEMemory.Bank.lm1.capacity),
                  write.destination ≠ some ⟨PEMemory.Bank.lm1, width, address⟩ :=
                prepareParsedIntegerMatrixReadLineExpression_noLm1 files oldSlots startSlots
                  store expression control hsm nf reduced expressionPlain expressionAvoids
                  headWrites headSlots headBars head
              have accumulated : ∀ write ∈ writes0 ++ headWrites, ∀ (width : PEMemory.Width)
                  (address : Fin PEMemory.Bank.lm1.capacity),
                  write.destination ≠ some ⟨PEMemory.Bank.lm1, width, address⟩ := by
                intro write member width address destination
                rcases List.mem_append.mp member with earlier | later
                · exact kept write earlier width address destination
                · exact headKept write later width address destination
              exact ih (writes0 ++ headWrites) headSlots (barUpdates0 ++ headBars)
                tailWrites tailSlots tailBars restPlain restAvoids accumulated tail


theorem prepareParsedIntegerMatrixReadLineExpression_destination_state_general
    (filesA filesB : IntegerRegisterFiles)
    (oldSlotsA oldSlotsB nextSlotsA nextSlotsB : ProofsLean.MNCore.Forwarding.Slots)
    (store : ParsedMatrixReadStore) (expression : ParsedExpr)
    (control : ParsedMaskExecutionControl) (hsm nf reduced : Bool)
    (plain : parsedExprIsPlainIntegerALU expression = true)
    (maskEq : filesA.maskRegisters = filesB.maskRegisters)
    (writesA : List PreparedParsedMaskedWrite) (slotsA : ProofsLean.MNCore.Forwarding.Slots)
    (barsA : List (Bool × BitVec 12))
    (writesB : List PreparedParsedMaskedWrite) (slotsB : ProofsLean.MNCore.Forwarding.Slots)
    (barsB : List (Bool × BitVec 12))
    (hA : prepareParsedIntegerMatrixReadLineExpression filesA oldSlotsA nextSlotsA store expression
      control hsm nf reduced = .ok (writesA, slotsA, barsA))
    (hB : prepareParsedIntegerMatrixReadLineExpression filesB oldSlotsB nextSlotsB store expression
      control hsm nf reduced = .ok (writesB, slotsB, barsB)) :
    writesA.map (fun write => write.destination) =
      writesB.map (fun write => write.destination) := by
  obtain ⟨op, sources, destinations, flush, text⟩ := expression
  cases op with
  | alu name precision unsigned arg =>
      unfold prepareParsedIntegerMatrixReadLineExpression at hA hB
      cases runA : prepareParsedIntegerALUExprCycles filesA oldSlotsA nextSlotsA
          ⟨.alu name precision unsigned arg, sources, destinations, flush, text⟩ control hsm
          nf reduced with
      | failure => rw [runA] at hA; cases hA
      | unknown => rw [runA] at hA; cases hA
      | ok resultA =>
          obtain ⟨cycleWritesA, cycleSlotsA⟩ := resultA
          rw [runA] at hA
          simp only [StepResult.ok.injEq, Prod.mk.injEq] at hA
          obtain ⟨writesEqA, -, -⟩ := hA
          subst writesEqA
          cases runB : prepareParsedIntegerALUExprCycles filesB oldSlotsB nextSlotsB
              ⟨.alu name precision unsigned arg, sources, destinations, flush, text⟩ control
              hsm nf reduced with
          | failure => rw [runB] at hB; cases hB
          | unknown => rw [runB] at hB; cases hB
          | ok resultB =>
              obtain ⟨cycleWritesB, cycleSlotsB⟩ := resultB
              rw [runB] at hB
              simp only [StepResult.ok.injEq, Prod.mk.injEq] at hB
              obtain ⟨writesEqB, -, -⟩ := hB
              subst writesEqB
              unfold prepareParsedIntegerALUExprCycles at runA runB
              exact prepareParsedIntegerALUCycles_destination_state_general filesA filesB
                oldSlotsA oldSlotsB _ control hsm nf reduced maskEq parsedIntegerALUCycles
                [] nextSlotsA [] nextSlotsB (cycleWritesA, cycleSlotsA)
                (cycleWritesB, cycleSlotsB) rfl runA runB
  | zero =>
      unfold prepareParsedIntegerMatrixReadLineExpression at hA hB
      cases runA : prepareParsedIntegerALUExprCycles filesA oldSlotsA nextSlotsA
          ⟨.zero, sources, destinations, flush, text⟩ control hsm nf reduced with
      | failure => rw [runA] at hA; cases hA
      | unknown => rw [runA] at hA; cases hA
      | ok resultA =>
          obtain ⟨cycleWritesA, cycleSlotsA⟩ := resultA
          rw [runA] at hA
          simp only [StepResult.ok.injEq, Prod.mk.injEq] at hA
          obtain ⟨writesEqA, -, -⟩ := hA
          subst writesEqA
          cases runB : prepareParsedIntegerALUExprCycles filesB oldSlotsB nextSlotsB
              ⟨.zero, sources, destinations, flush, text⟩ control hsm nf reduced with
          | failure => rw [runB] at hB; cases hB
          | unknown => rw [runB] at hB; cases hB
          | ok resultB =>
              obtain ⟨cycleWritesB, cycleSlotsB⟩ := resultB
              rw [runB] at hB
              simp only [StepResult.ok.injEq, Prod.mk.injEq] at hB
              obtain ⟨writesEqB, -, -⟩ := hB
              subst writesEqB
              unfold prepareParsedIntegerALUExprCycles at runA runB
              exact prepareParsedIntegerALUCycles_destination_state_general filesA filesB
                oldSlotsA oldSlotsB _ control hsm nf reduced maskEq parsedIntegerALUCycles
                [] nextSlotsA [] nextSlotsB (cycleWritesA, cycleSlotsA)
                (cycleWritesB, cycleSlotsB) rfl runA runB
  | immediate payload sparse =>
      unfold prepareParsedIntegerMatrixReadLineExpression at hA hB
      cases runA : prepareParsedIntegerALUExprCycles filesA oldSlotsA nextSlotsA
          ⟨.immediate payload sparse, sources, destinations, flush, text⟩ control hsm nf
          reduced with
      | failure => rw [runA] at hA; cases hA
      | unknown => rw [runA] at hA; cases hA
      | ok resultA =>
          obtain ⟨cycleWritesA, cycleSlotsA⟩ := resultA
          rw [runA] at hA
          simp only [StepResult.ok.injEq, Prod.mk.injEq] at hA
          obtain ⟨writesEqA, -, -⟩ := hA
          subst writesEqA
          cases runB : prepareParsedIntegerALUExprCycles filesB oldSlotsB nextSlotsB
              ⟨.immediate payload sparse, sources, destinations, flush, text⟩ control hsm
              nf reduced with
          | failure => rw [runB] at hB; cases hB
          | unknown => rw [runB] at hB; cases hB
          | ok resultB =>
              obtain ⟨cycleWritesB, cycleSlotsB⟩ := resultB
              rw [runB] at hB
              simp only [StepResult.ok.injEq, Prod.mk.injEq] at hB
              obtain ⟨writesEqB, -, -⟩ := hB
              subst writesEqB
              unfold prepareParsedIntegerALUExprCycles at runA runB
              exact prepareParsedIntegerALUCycles_destination_state_general filesA filesB
                oldSlotsA oldSlotsB _ control hsm nf reduced maskEq parsedIntegerALUCycles
                [] nextSlotsA [] nextSlotsB (cycleWritesA, cycleSlotsA)
                (cycleWritesB, cycleSlotsB) rfl runA runB
  | mau precision matrix kind half round =>
      simp [parsedExprIsPlainIntegerALU, parsedExprIsIntegerProducer] at plain
  | matrixWrite precision =>
      simp [parsedExprIsPlainIntegerALU, parsedExprIsIntegerProducer] at plain
  | matrixRead precision =>
      simp [parsedExprIsPlainIntegerALU, parsedExprIsIntegerProducer] at plain
  | wait tag => simp [parsedExprIsPlainIntegerALU, parsedExprIsIntegerProducer] at plain
  | noforward => simp [parsedExprIsPlainIntegerALU, parsedExprIsIntegerProducer] at plain
  | l1bm operation => simp [parsedExprIsPlainIntegerALU, parsedExprIsIntegerProducer] at plain
  | l2bm operation => simp [parsedExprIsPlainIntegerALU, parsedExprIsIntegerProducer] at plain


theorem prepareParsedIntegerMatrixReadLineCycles_noLm1
    (files : IntegerRegisterFiles) (oldSlots : ProofsLean.MNCore.Forwarding.Slots)
    (store : ParsedMatrixReadStore) (expressions : List ParsedExpr)
    (control : ParsedMaskExecutionControl) (reduced : Bool)
    (plain : expressions.all parsedExprIsPlainIntegerALU = true)
    (avoids : ∀ expression ∈ expressions, CendAvoidsLm1 expression)
    (writes : List PreparedParsedMaskedWrite)
    (slots : ProofsLean.MNCore.Forwarding.Slots)
    (bars : List (Bool × BitVec 12))
    (prep : prepareParsedIntegerMatrixReadLineCycles files oldSlots store expressions control
      reduced = .ok (writes, slots, bars)) :
    ∀ write ∈ writes, ∀ (width : PEMemory.Width)
      (address : Fin PEMemory.Bank.lm1.capacity),
      write.destination ≠ some ⟨PEMemory.Bank.lm1, width, address⟩ := by
  unfold prepareParsedIntegerMatrixReadLineCycles at prep
  exact prepareParsedIntegerMatrixReadLineExpressions_noLm1 files oldSlots store control
    (expressions.any parsedExprHasSingleLineWriteMask)
    (expressions.any fun expression =>
      match expression.op with
      | ParsedOp.noforward => true
      | x => false)
    reduced expressions [] oldSlots [] writes slots bars plain avoids
    (fun write member => by cases member) prep

theorem welcomeIntegerPrep_noLm1 (state : State) (pe : PEId)
    (expressions : List ParsedExpr)
    (plain : expressions.all parsedExprIsPlainIntegerALU = true)
    (avoids : ∀ expression ∈ expressions, CendAvoidsLm1 expression)
    (writes : List PreparedParsedMaskedWrite)
    (slots : ProofsLean.MNCore.Forwarding.Slots)
    (bars : List (Bool × BitVec 12))
    (prep : welcomeIntegerPrep state pe expressions = .ok (writes, slots, bars)) :
    ∀ write ∈ writes, ∀ (width : PEMemory.Width)
      (address : Fin PEMemory.Bank.lm1.capacity),
      write.destination ≠ some ⟨PEMemory.Bank.lm1, width, address⟩ := by
  unfold welcomeIntegerPrep at prep
  have filteredPlain : (expressions.filter parsedExprIsIntegerMatrixReadStageInput).all
      parsedExprIsPlainIntegerALU = true := by
    rw [List.all_eq_true]
    intro expression member
    exact List.all_eq_true.mp plain expression (List.mem_filter.mp member).1
  have filteredAvoids : ∀ expression ∈
      expressions.filter parsedExprIsIntegerMatrixReadStageInput, CendAvoidsLm1 expression := by
    intro expression member
    exact avoids expression (List.mem_filter.mp member).1
  exact prepareParsedIntegerMatrixReadLineCycles_noLm1 (state.peRegisters pe)
    (stateForwardingSlots state pe)
    (state.matrixRegisters (ParsedIntegerContext.ofLinearIndex pe).group
      (ParsedIntegerContext.ofLinearIndex pe).l2b
      (ParsedIntegerContext.ofLinearIndex pe).l1b)
    (expressions.filter parsedExprIsIntegerMatrixReadStageInput)
    (parsedPEHazardControl state pe) false filteredPlain filteredAvoids writes slots bars prep

theorem welcomeCommitStep_lm1_eq_of_noLm1 (files : IntegerRegisterFiles)
    (write : PreparedParsedMaskedWrite)
    (noLm1 : ∀ (width : PEMemory.Width) (address : Fin PEMemory.Bank.lm1.capacity),
      write.destination ≠ some ⟨PEMemory.Bank.lm1, width, address⟩) :
    (welcomeCommitStep files write).lm1 = files.lm1 := by
  cases write with
  | mk destination maskUpdate data selection =>
    cases maskUpdate with
    | some update =>
        simp only [welcomeCommitStep]
    | none =>
        cases destination with
        | none =>
            simp only [welcomeCommitStep]
        | some access =>
            obtain ⟨bank, width, address⟩ := access
            cases bank with
            | lm1 => exact absurd rfl (noLm1 width address)
            | lm0 =>
                simp only [welcomeCommitStep]
                exact writeDirectAccessMasked_lm1_eq _ _ _ _ _ _ (by simp)
            | grf0 =>
                simp only [welcomeCommitStep]
                exact writeDirectAccessMasked_lm1_eq _ _ _ _ _ _ (by simp)
            | grf1 =>
                simp only [welcomeCommitStep]
                exact writeDirectAccessMasked_lm1_eq _ _ _ _ _ _ (by simp)
            | t =>
                simp only [welcomeCommitStep]
                exact writeDirectAccessMasked_lm1_eq _ _ _ _ _ _ (by simp)

theorem commitParsedMaskedWrites_lm1_eq_of_noLm1 (files : IntegerRegisterFiles)
    (writes : List PreparedParsedMaskedWrite)
    (noLm1 : ∀ write ∈ writes, ∀ (width : PEMemory.Width)
      (address : Fin PEMemory.Bank.lm1.capacity),
      write.destination ≠ some ⟨PEMemory.Bank.lm1, width, address⟩) :
    (commitParsedMaskedWrites files writes).lm1 = files.lm1 := by
  induction writes generalizing files with
  | nil => simp [commitParsedMaskedWrites]
  | cons write rest ih =>
      rw [commitParsedMaskedWrites_cons]
      rw [ih (welcomeCommitStep files write)
        (fun item member => noLm1 item (List.mem_cons_of_mem _ member))]
      exact welcomeCommitStep_lm1_eq_of_noLm1 files write (noLm1 write (by simp))

theorem prepareParsedIntegerMatrixReadLineExpressions_destination_state_general
    (filesA filesB : IntegerRegisterFiles)
    (oldSlotsA oldSlotsB : ProofsLean.MNCore.Forwarding.Slots)
    (store : ParsedMatrixReadStore) (control : ParsedMaskExecutionControl)
    (hsm nf reduced : Bool)
    (maskEq : filesA.maskRegisters = filesB.maskRegisters) :
    ∀ (expressions : List ParsedExpr),
      expressions.all parsedExprIsPlainIntegerALU = true →
    ∀ (writesA0 : List PreparedParsedMaskedWrite)
      (startSlotsA : ProofsLean.MNCore.Forwarding.Slots)
      (barUpdatesA0 : List (Bool × BitVec 12))
      (writesB0 : List PreparedParsedMaskedWrite)
      (startSlotsB : ProofsLean.MNCore.Forwarding.Slots)
      (barUpdatesB0 : List (Bool × BitVec 12))
      (writesA : List PreparedParsedMaskedWrite)
      (slotsA : ProofsLean.MNCore.Forwarding.Slots)
      (barsA : List (Bool × BitVec 12))
      (writesB : List PreparedParsedMaskedWrite)
      (slotsB : ProofsLean.MNCore.Forwarding.Slots)
      (barsB : List (Bool × BitVec 12)),
      writesA0.map (fun write => write.destination) =
        writesB0.map (fun write => write.destination) →
      prepareParsedIntegerMatrixReadLineExpressions filesA oldSlotsA store control hsm nf
        reduced expressions writesA0 startSlotsA barUpdatesA0 = .ok (writesA, slotsA, barsA) →
      prepareParsedIntegerMatrixReadLineExpressions filesB oldSlotsB store control hsm nf
        reduced expressions writesB0 startSlotsB barUpdatesB0 = .ok (writesB, slotsB, barsB) →
      writesA.map (fun write => write.destination) =
        writesB.map (fun write => write.destination) := by
  intro expressions
  induction expressions with
  | nil =>
      intro _plain writesA0 startSlotsA barUpdatesA0 writesB0 startSlotsB barUpdatesB0
        writesA slotsA barsA writesB slotsB barsB writesEq hA hB
      simp only [prepareParsedIntegerMatrixReadLineExpressions, StepResult.ok.injEq,
        Prod.mk.injEq] at hA hB
      obtain ⟨writesEqA, -, -⟩ := hA
      obtain ⟨writesEqB, -, -⟩ := hB
      subst writesEqA
      subst writesEqB
      exact writesEq
  | cons expression rest ih =>
      intro plain writesA0 startSlotsA barUpdatesA0 writesB0 startSlotsB barUpdatesB0
        writesA slotsA barsA writesB slotsB barsB writesEq hA hB
      unfold prepareParsedIntegerMatrixReadLineExpressions at hA hB
      cases headA : prepareParsedIntegerMatrixReadLineExpression filesA oldSlotsA startSlotsA
          store expression control hsm nf reduced with
      | failure => rw [headA] at hA; cases hA
      | unknown => rw [headA] at hA; cases hA
      | ok headResultA =>
          obtain ⟨headWritesA, headSlotsA, headBarsA⟩ := headResultA
          rw [headA] at hA
          dsimp only at hA
          cases headB : prepareParsedIntegerMatrixReadLineExpression filesB oldSlotsB startSlotsB
              store expression control hsm nf reduced with
          | failure => rw [headB] at hB; cases hB
          | unknown => rw [headB] at hB; cases hB
          | ok headResultB =>
              obtain ⟨headWritesB, headSlotsB, headBarsB⟩ := headResultB
              rw [headB] at hB
              dsimp only at hB
              cases tailA : prepareParsedIntegerMatrixReadLineExpressions filesA oldSlotsA
                  store control hsm nf reduced rest (writesA0 ++ headWritesA) headSlotsA
                  (barUpdatesA0 ++ headBarsA) with
              | failure => rw [tailA] at hA; cases hA
              | unknown => rw [tailA] at hA; cases hA
              | ok tailResultA =>
                  obtain ⟨tailWritesA, tailSlotsA, tailBarsA⟩ := tailResultA
                  rw [tailA] at hA
                  simp only [StepResult.ok.injEq, Prod.mk.injEq] at hA
                  obtain ⟨writesEqA, -, -⟩ := hA
                  subst writesEqA
                  cases tailB : prepareParsedIntegerMatrixReadLineExpressions filesB oldSlotsB
                      store control hsm nf reduced rest (writesB0 ++ headWritesB) headSlotsB
                      (barUpdatesB0 ++ headBarsB) with
                  | failure => rw [tailB] at hB; cases hB
                  | unknown => rw [tailB] at hB; cases hB
                  | ok tailResultB =>
                      obtain ⟨tailWritesB, tailSlotsB, tailBarsB⟩ := tailResultB
                      rw [tailB] at hB
                      simp only [StepResult.ok.injEq, Prod.mk.injEq] at hB
                      obtain ⟨writesEqB, -, -⟩ := hB
                      subst writesEqB
                      have plainExpression : parsedExprIsPlainIntegerALU expression = true :=
                        List.all_eq_true.mp plain expression (by simp)
                      have restPlain : rest.all parsedExprIsPlainIntegerALU = true := by
                        rw [List.all_eq_true]
                        intro item member
                        exact List.all_eq_true.mp plain item (List.mem_cons_of_mem _ member)
                      exact ih restPlain (writesA0 ++ headWritesA) headSlotsA
                        (barUpdatesA0 ++ headBarsA)
                        (writesB0 ++ headWritesB) headSlotsB (barUpdatesB0 ++ headBarsB)
                        tailWritesA tailSlotsA tailBarsA tailWritesB tailSlotsB tailBarsB
                        (by
                          rw [List.map_append, List.map_append,
                            prepareParsedIntegerMatrixReadLineExpression_destination_state_general
                              filesA filesB oldSlotsA oldSlotsB startSlotsA startSlotsB store
                              expression control hsm nf reduced plainExpression maskEq
                              headWritesA headSlotsA
                              headBarsA headWritesB headSlotsB headBarsB headA headB,
                            writesEq])
                        tailA tailB


theorem prepareParsedIntegerMatrixReadLineCycles_destination_state_general
    (filesA filesB : IntegerRegisterFiles)
    (oldSlotsA oldSlotsB : ProofsLean.MNCore.Forwarding.Slots)
    (store : ParsedMatrixReadStore) (expressions : List ParsedExpr)
    (control : ParsedMaskExecutionControl) (reduced : Bool)
    (plain : expressions.all parsedExprIsPlainIntegerALU = true)
    (maskEq : filesA.maskRegisters = filesB.maskRegisters)
    (writesA : List PreparedParsedMaskedWrite)
    (slotsA : ProofsLean.MNCore.Forwarding.Slots)
    (barsA : List (Bool × BitVec 12))
    (writesB : List PreparedParsedMaskedWrite)
    (slotsB : ProofsLean.MNCore.Forwarding.Slots)
    (barsB : List (Bool × BitVec 12))
    (hA : prepareParsedIntegerMatrixReadLineCycles filesA oldSlotsA store expressions control
      reduced = .ok (writesA, slotsA, barsA))
    (hB : prepareParsedIntegerMatrixReadLineCycles filesB oldSlotsB store expressions control
      reduced = .ok (writesB, slotsB, barsB)) :
    writesA.map (fun write => write.destination) =
      writesB.map (fun write => write.destination) := by
  unfold prepareParsedIntegerMatrixReadLineCycles at hA hB
  exact prepareParsedIntegerMatrixReadLineExpressions_destination_state_general filesA filesB
    oldSlotsA oldSlotsB store control
    (expressions.any parsedExprHasSingleLineWriteMask)
    (expressions.any fun expression =>
      match expression.op with
      | ParsedOp.noforward => true
      | x => false)
    reduced maskEq expressions plain [] oldSlotsA [] [] oldSlotsB []
    writesA slotsA barsA writesB slotsB barsB rfl hA hB

theorem cendPE_plain_not_correct_of_avoidsLm1 (expressions : List NormalizedExpr)
    (plain : (expressions.map NormalizedExpr.toParsed).all
      parsedExprIsPlainIntegerALU = true)
    (avoids : ∀ expression ∈ expressions, CendAvoidsLm1 expression.toParsed) :
    ¬ ProofsLean.Correct cendSealedMachine cendSpec
      ([InstructionLine.pe expressions] : List InstructionLine) := by
  cases step0 : cendStep expressions 0 with
  | none => exact cend_not_correct_of_step_stuck expressions 0 step0
  | some next0 =>
      cases stepW : cendStep expressions cendWitness with
      | none => exact cend_not_correct_of_step_stuck expressions cendWitness stepW
      | some nextW =>
          obtain ⟨writes0, slots0, bars0, prep0, commit0⟩ :=
            cendSealed_pe_prepared expressions (cendInitialState 0) plain step0
          obtain ⟨writesW, slotsW, barsW, prepW, commitW⟩ :=
            cendSealed_pe_prepared expressions (cendInitialState cendWitness) plain stepW
          have filteredPlain : ((expressions.map NormalizedExpr.toParsed).filter
              parsedExprIsIntegerMatrixReadStageInput).all parsedExprIsPlainIntegerALU = true := by
            rw [List.all_eq_true]
            intro expression member
            exact List.all_eq_true.mp plain expression (List.mem_filter.mp member).1
          have filteredAvoids : ∀ expression ∈
              (expressions.map NormalizedExpr.toParsed).filter
                parsedExprIsIntegerMatrixReadStageInput, CendAvoidsLm1 expression := by
            intro expression member
            obtain ⟨original, originalMem, rfl⟩ :=
              List.mem_map.mp (List.mem_filter.mp member).1
            exact avoids original originalMem
          have noLm1Zero : ∀ write ∈ writes0, ∀ (width : PEMemory.Width)
              (address : Fin PEMemory.Bank.lm1.capacity),
              write.destination ≠ some ⟨PEMemory.Bank.lm1, width, address⟩ :=
            welcomeIntegerPrep_noLm1 (cendInitialState 0) welcomePE
              (expressions.map NormalizedExpr.toParsed) plain
              (fun expression member => by
                obtain ⟨item, itemMem, itemEq⟩ := List.mem_map.mp member
                rw [← itemEq]
                exact avoids item itemMem)
              writes0 slots0 bars0 prep0
          have runZero : prepareParsedIntegerMatrixReadLineCycles
              ((cendInitialState 0).peRegisters welcomePE)
              (stateForwardingSlots (cendInitialState 0) welcomePE)
              ((cendInitialState 0).matrixRegisters
                (ParsedIntegerContext.ofLinearIndex welcomePE).group
                (ParsedIntegerContext.ofLinearIndex welcomePE).l2b
                (ParsedIntegerContext.ofLinearIndex welcomePE).l1b)
              ((expressions.map NormalizedExpr.toParsed).filter
                parsedExprIsIntegerMatrixReadStageInput)
              (parsedPEHazardControl (cendInitialState 0) welcomePE) false =
                .ok (writes0, slots0, bars0) := by
            simpa [welcomeIntegerPrep] using prep0
          have runW : prepareParsedIntegerMatrixReadLineCycles
              ((cendInitialState cendWitness).peRegisters welcomePE)
              (stateForwardingSlots (cendInitialState cendWitness) welcomePE)
              ((cendInitialState cendWitness).matrixRegisters
                (ParsedIntegerContext.ofLinearIndex welcomePE).group
                (ParsedIntegerContext.ofLinearIndex welcomePE).l2b
                (ParsedIntegerContext.ofLinearIndex welcomePE).l1b)
              ((expressions.map NormalizedExpr.toParsed).filter
                parsedExprIsIntegerMatrixReadStageInput)
              (parsedPEHazardControl (cendInitialState cendWitness) welcomePE) false =
                .ok (writesW, slotsW, barsW) := by
            simpa [welcomeIntegerPrep] using prepW
          have maskEq : ((cendInitialState 0).peRegisters welcomePE).maskRegisters =
              ((cendInitialState cendWitness).peRegisters welcomePE).maskRegisters := rfl
          have destinationsEq :=
            prepareParsedIntegerMatrixReadLineCycles_destination_state_general
              ((cendInitialState 0).peRegisters welcomePE)
              ((cendInitialState cendWitness).peRegisters welcomePE)
              (stateForwardingSlots (cendInitialState 0) welcomePE)
              (stateForwardingSlots (cendInitialState cendWitness) welcomePE)
              ((cendInitialState 0).matrixRegisters
                (ParsedIntegerContext.ofLinearIndex welcomePE).group
                (ParsedIntegerContext.ofLinearIndex welcomePE).l2b
                (ParsedIntegerContext.ofLinearIndex welcomePE).l1b)
              ((expressions.map NormalizedExpr.toParsed).filter
                parsedExprIsIntegerMatrixReadStageInput)
              (parsedPEHazardControl (cendInitialState 0) welcomePE) false
              filteredPlain maskEq writes0 slots0 bars0 writesW slotsW barsW runZero runW
          have noLm1Witness : ∀ write ∈ writesW, ∀ (width : PEMemory.Width)
              (address : Fin PEMemory.Bank.lm1.capacity),
              write.destination ≠ some ⟨PEMemory.Bank.lm1, width, address⟩ := by
            intro write member width address destination
            have mapped : write.destination ∈ writesW.map (fun item => item.destination) :=
              List.mem_map.mpr ⟨write, member, rfl⟩
            rw [← destinationsEq] at mapped
            obtain ⟨zeroWrite, zeroMem, zeroDestination⟩ := List.mem_map.mp mapped
            exact noLm1Zero zeroWrite zeroMem width address (by rw [zeroDestination]; exact destination)
          have lm1Eq := commitParsedMaskedWrites_lm1_eq_of_noLm1
            ((cendInitialState cendWitness).peRegisters cendPE) writesW noLm1Witness
          have pairZero : cendOutputPair nextW = 0 := by
            rw [cendOutputPair_eq_append]
            have wordZero : cendOutputWord0 nextW = 0 := by
              show (nextW.peRegisters cendPE).lm1 ⟨0, by decide⟩ = 0
              rw [commitW, lm1Eq]
              exact cendInitialPERegisters_lm1 cendWitness ⟨0, by decide⟩
            have wordOne : cendOutputWord1 nextW = 0 := by
              show (nextW.peRegisters cendPE).lm1 ⟨1, by decide⟩ = 0
              rw [commitW, lm1Eq]
              exact cendInitialPERegisters_lm1 cendWitness ⟨1, by decide⟩
            rw [wordZero, wordOne]
            rfl
          exact cend_not_correct_of_output_ne expressions cendWitness nextW stepW
            (fun same => cendWitness_target_ne_zero (pairZero.symm.trans same).symm)



/-- A line with at least one destination operand whose static bank is LM1. -/
def CendHasLm1Destination (expressions : List NormalizedExpr) : Prop :=
  ∃ expression ∈ expressions, ∃ destination ∈ expression.toParsed.destinations,
    ∃ width : PEMemory.Width,
      ParsedOperand.directDestinationBankWidth? destination =
        some (PEMemory.Bank.lm1, width)

/-- **The narrowed residual.**  The both-halves plain lines that have an LM1
destination are incorrect.  This is the part of `CendPlainALUBothHalvesRefuted`
left open by the no-LM1-destination theorem: a value analysis has to show that
one of the two observed words is untouched (then §2 applies) or that the
observed pair misses a value of the target (§1). -/
def CendPlainALUBothHalvesRefutedLm1 : Prop :=
  ∀ expressions : List NormalizedExpr,
    (expressions.map NormalizedExpr.toParsed).all parsedExprIsPlainIntegerALU = true →
    CendPlainALUBothHalves expressions →
    CendHasLm1Destination expressions →
    ¬ ProofsLean.Correct cendSealedMachine cendSpec
      ([InstructionLine.pe expressions] : List InstructionLine)

/-- **The full both-halves residual from the narrowed one.**  A both-halves plain
line either has an LM1 destination (the narrowed residual) or none at all (the
LM1 bank stays at its initial zero, §3). -/
theorem cendPlainALUBothHalvesRefuted_of_lm1Destination
    (narrowed : CendPlainALUBothHalvesRefutedLm1) :
    CendPlainALUBothHalvesRefuted := by
  intro expressions plain both
  by_cases hasLm1 : CendHasLm1Destination expressions
  · exact narrowed expressions plain both hasLm1
  · rw [CendHasLm1Destination] at hasLm1
    push Not at hasLm1
    exact cendPE_plain_not_correct_of_avoidsLm1 expressions plain
      (fun expression expressionMem destination destinationMem width =>
        hasLm1 expression expressionMem destination destinationMem width)

/-- **Every plain line is refuted from the narrowed residual.** -/
theorem cendPE_plain_not_correct_of_lm1Destination
    (narrowed : CendPlainALUBothHalvesRefutedLm1) (expressions : List NormalizedExpr)
    (plain : (expressions.map NormalizedExpr.toParsed).all
      parsedExprIsPlainIntegerALU = true) :
    ¬ ProofsLean.Correct cendSealedMachine cendSpec
      ([InstructionLine.pe expressions] : List InstructionLine) :=
  cendPE_plain_not_correct (cendPlainALUBothHalvesRefuted_of_lm1Destination narrowed)
    expressions plain

/-- **The unconditional plain line family, from the narrowed residual.** -/
theorem cendPE_plainLines_not_correct_of_lm1Destination
    (narrowed : CendPlainALUBothHalvesRefutedLm1) (expressions : List NormalizedExpr)
    (plain : CendPlainLines expressions) :
    ¬ ProofsLean.Correct cendSealedMachine cendSpec
      ([InstructionLine.pe expressions] : List InstructionLine) :=
  cendPE_plainLines_not_correct (cendPlainALUBothHalvesRefuted_of_lm1Destination narrowed)
    expressions plain




/-! ## Trust report -/

#print axioms exists_not_mem_of_card_lt
#print axioms cendPE_not_correct_of_eventually_range
#print axioms cendPE_not_correct_of_eventually_smallRange
#print axioms cendZeroLowPairs_one_not_mem
#print axioms cendPE_not_correct_of_lm1_word_one_free
#print axioms cendPE_not_correct_of_lm1_word_zero_free
#print axioms prepareParsedIntegerALUExprCycle_noLm1
#print axioms prepareParsedIntegerALUExprCycles_noLm1
#print axioms commitParsedMaskedWrites_lm1_eq_of_noLm1
#print axioms cendPE_plain_not_correct_of_avoidsLm1
#print axioms cendPlainALUBothHalvesRefuted_of_lm1Destination
#print axioms cendPE_plain_not_correct_of_lm1Destination
#print axioms cendPE_plainLines_not_correct_of_lm1Destination



/-! ## 5. A concrete line in the no-LM1-destination class

The no-LM1-destination theorem is not vacuous: the line below has a single plain
`.passa` row reading the LM0 `.long` window at address `0` (a source window that
contains both input words) and writing `GRF0`, so its destination analysis gives
`CendAvoidsLm1` and the line is refuted unconditionally by
`cendPE_plain_not_correct_of_avoidsLm1`. -/

/-- A plain row reading LM0 `.long` (both input words are in this window) and
writing GRF0, not LM1. -/
def cendNoLm1Line : NormalizedExpr where
  op := .alu .passa (some .i) false none
  sources := [.mem ⟨.lm0, ⟨2, 0, 0, 0, 0, false, none⟩⟩ false false false none]
  destinations := [.mem ⟨.grf0, ⟨1, 0, 0, 0, 0, false, none⟩⟩ false false false
    (some (.entry false 0))]
  flush := none

theorem cendNoLm1Line_plain : parsedExprIsPlainIntegerALU cendNoLm1Line.toParsed = true := rfl

theorem cendNoLm1Line_avoids : CendAvoidsLm1 cendNoLm1Line.toParsed := by
  intro destination member width
  simp only [cendNoLm1Line, NormalizedExpr.toParsed, List.mem_singleton] at member
  subst member
  cases width <;> decide

/-- The concrete line is refuted unconditionally by the no-LM1-destination
theorem. -/
theorem cendNoLm1Line_not_correct :
    ¬ ProofsLean.Correct cendSealedMachine cendSpec
      ([InstructionLine.pe [cendNoLm1Line]] : List InstructionLine) :=
  cendPE_plain_not_correct_of_avoidsLm1 [cendNoLm1Line] rfl
    (fun expression member => by
      simp only [List.mem_singleton] at member
      subst member
      exact cendNoLm1Line_avoids)

end ProofsLean.MNCore
