import ProofsLean.WelcomeWriterPackages
import ProofsLean.WelcomeL1PEShape

/-! # The `.l1bm` broadcast row with an arbitrary destination list

`WelcomeL1PEShape.lean` proves the broadcast row shape
(`executeParsedL1ToPEProducer_mem_lm1_shape`) for a destination list that is a
**single** `.mem` operand of static bank `.lm1`.  That restriction is not a
consequence of the issue checker, and `WelcomeWriterPackages.lean` proved it is
not even true of the executor's reachable lines: the accepted, unrefuted
two-destination witness `l1ToPETwoDestinationWitness` writes `.lm1` and `.lm0`
from one `.pbcast` row (`l1ToPETwoDestination_weakPackage_false`).  This module
removes the restriction.

## What this module proves

* **§1** the destination-list decomposition: a list containing at most one
  `.mem` destination of bank `.lm1` splits as `pre ++ d :: post` with `d` that
  destination and `pre`/`post` free of `.lm1` destinations
  (`lm1Destination_split`), plus the two facts that make "free" usable:
  `lm1DestCount_holds` (a destination whose *static* bank is `.lm1` is a
  syntactic `.lm1` memory destination — proved unconditionally, not assumed)
  and `lm1FreeDestination_of_not_mem`.
* **§2** the `.lm1`-filter characterisations of the two shapes: both
  `Lm1WritesDoubleCopy` and `Lm1WritesNarrow` are exactly statements about the
  `.lm1` writes of the list, so they are invariant under adding or removing
  `.lm1`-free writes (`lm1WritesDoubleCopy_iff_filter`,
  `lm1WritesNarrow_iff_filter`), and both hold of an `.lm1`-free list.
* **§3** the destination loop with one `.lm1` destination: an append law for
  `writeDestinations` (`executeParsedL1ToPE_writeDestinations_append`) and the
  split-run form `executeParsedL1ToPE_writeDestinations_lm1_split_run`, which
  exposes the
  cycle's writes as `preWrites ++ [single .lm1 write] ++ postWrites` with the
  two free blocks.
* **§4** the four-cycle shape
  `executeParsedL1ToPE_writeCycles_lm1_shape_atMostOne`: if the destination list
  has at most one `.mem` destination of bank `.lm1` and the read state's
  broadcast bus is zero (in particular the all-zero Welcome state), the four
  cycle writes are `Lm1WritesDoubleCopy` or `Lm1WritesNarrow`.  The four `.lm1`
  writes are exactly the singleton shape's four writes; the free blocks are
  inserted through §2.
* **§5** the PE-walk, producer and stage forms
  (`executeParsedL1ToPEAtPEs_lm1_shape_atMostOne`,
  `executeParsedL1ToPEProducer_lm1_shape_atMostOne`,
  `executeParsedL1ToPEProducers_lm1_shape_atMostOne`).
* **§5.5** the count is not an assumption: a legal row's `writeBanks` is
  `Nodup` (`writesUnique`), so a legal row has **at most one** `.mem`
  destination of bank `.lm1` (`filter_isLm1_le_one_of_legal`,
  `filter_isLm1_le_one_of_accepted`, `nodup_count_le_one`).
* **§6** the package `WelcomePEL1BMWriterDataMultiDest` — proved
  **unconditionally** on every unrefuted line
  (`welcomePEL1BMWriterDataMultiDest_holds`), the line-level dispatch
  `welcomePEWriteShape_of_l1bmWriter_dataMultiDest` and the conservative
  direction from the singleton package
  (`welcomePEL1BMWriterDataForMultiDest_of_noSingleton`).  The dispatch does not
  need the writer's lowering: a broadcast row whose lowering fails makes the
  L1BM-to-PE stage fail, so the step is not reached (the vacuous case).
* **§7** the assembly with only the plain and `.matrixRead` packages
  (`welcomePELm1WriteShapeObligation_of_plainReadL1MultiDest`,
  `welcomeLowerBound_two_of_plainReadL1MultiDest`,
  `welcomeAnswer_optimal_of_plainReadL1MultiDest`).  The `.l1bm` component of
  `welcomePELm1WriteShapeObligation_of_plainReadL1` — refuted in round 50 — is
  discharged, so these are **conditional on the plain and `.matrixRead`
  packages only**.
* **§8** the refuted two-destination witness satisfies the new package
  (`welcomePEL1BMWriterDataForMultiDest_witness`,
  `welcomePEL1BMWriterDataForMultiDest_witness_strict`): the generalisation is
  not vacuous on the line the old packages lost.

## What is not proved (and is not claimed)

No unconditional `LowerBound 2` and no unconditional `Optimal` is proved here:
§7's two corollaries take the plain and `.matrixRead` packages as hypotheses.
The `.l1bm` obstruction is gone, but the plain `notDouble`/flag-free package and
the `.matrixRead` package are still open (see `WelcomeWriterPackages.lean`).

No `sorry`, no `admit`, no `native_decide`, no new axioms, and no existing
module is edited by this file.
-/

namespace ProofsLean.MNCore

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open Issue
open PEMemory

/-! ## 1. Splitting off the (at most one) `.lm1` destination

The static test `ParsedOperand.directDestinationBankWidth?` and the syntactic
test `ParsedOperand.isLm1MemoryDestination` agree on `.mem` operands: the static
bank is `.lm1` exactly when the operand's `Issue.Bank` is `.lm1`.  Only the
first implication is needed below, and it is proved unconditionally
(`lm1DestCount_holds`), so "at most one `.lm1` destination" can be counted with
the syntactic test. -/

/-- The image of a bank under `issueBankToRegisterBank` identifies `.lm1`. -/
theorem issueBank_eq_lm1_of_registerBank_lm1 (bank : Issue.Bank)
    (mapped : issueBankToRegisterBank bank = some PEMemory.Bank.lm1) :
    bank = Issue.Bank.lm1 := by
  cases bank <;> simp [issueBankToRegisterBank] at mapped ⊢

/-- **The static bank-width of a `.mem` operand resolves the bank mapping.** -/
theorem issueBankToRegisterBank_of_directDestinationBankWidth
    (memoryAccess : Access) (negated extended rounded : Bool) (mask : Option ParsedMask)
    (bank : PEMemory.Bank) (width : PEMemory.Width)
    (static : ParsedOperand.directDestinationBankWidth?
      (ParsedOperand.mem memoryAccess negated extended rounded mask) = some (bank, width)) :
    issueBankToRegisterBank memoryAccess.bank = some bank := by
  simp only [ParsedOperand.directDestinationBankWidth?] at static
  by_cases guard : (negated || extended || rounded) = true
  · simp [guard] at static
  · rw [if_neg (by simpa using guard)] at static
    cases hbk : issueBankToRegisterBank memoryAccess.bank with
    | none => simp [hbk] at static
    | some found =>
        cases hw : parsedWidth? memoryAccess.region.width with
        | none => simp [hbk, hw] at static
        | some wd =>
            have reduced : (if ((memoryAccess.region.tIndirect && found != PEMemory.Bank.lm0) ||
                (memoryAccess.region.madpe.isSome && found != PEMemory.Bank.lm0 &&
                  found != PEMemory.Bank.lm1)) = true then none
                else some (found, wd)) = some (bank, width) := by
              simpa only [hbk, hw] using static
            by_cases blocked : ((memoryAccess.region.tIndirect && found != PEMemory.Bank.lm0) ||
                (memoryAccess.region.madpe.isSome && found != PEMemory.Bank.lm0 &&
                  found != PEMemory.Bank.lm1)) = true
            · rw [if_pos blocked] at reduced
              simp at reduced
            · rw [if_neg blocked] at reduced
              simp only [Option.some.injEq, Prod.mk.injEq] at reduced
              exact congrArg some reduced.1

/-- **The static bank `.lm1` of a `.mem` operand is the syntactic `.lm1` bank.**
If the operand's bank is `.lm1` and its static `(bank, width)` pair is
`(bank, width)`, then `bank = .lm1`. -/
theorem directDestinationBankWidth?_mem_lm1_bank
    (memoryAccess : Access) (negated extended rounded : Bool) (mask : Option ParsedMask)
    (bankLm1 : memoryAccess.bank = Issue.Bank.lm1) (bank : PEMemory.Bank)
    (width : PEMemory.Width)
    (static : ParsedOperand.directDestinationBankWidth?
      (ParsedOperand.mem memoryAccess negated extended rounded mask) = some (bank, width)) :
    bank = PEMemory.Bank.lm1 := by
  have mapped := issueBankToRegisterBank_of_directDestinationBankWidth memoryAccess negated
    extended rounded mask bank width static
  rw [bankLm1, issueBankToRegisterBank] at mapped
  exact (Option.some.inj mapped).symm

/-- **A `.mem` operand with static bank `.lm1` has `Issue.Bank.lm1`.**  This is
the direction that lets "at most one `.mem` `.lm1` destination" be counted with
`ParsedOperand.isLm1MemoryDestination`. -/
theorem mem_issueBank_eq_lm1_of_directDestinationBankWidth
    (memoryAccess : Access) (negated extended rounded : Bool) (mask : Option ParsedMask)
    (width : PEMemory.Width)
    (static : ParsedOperand.directDestinationBankWidth?
      (ParsedOperand.mem memoryAccess negated extended rounded mask) =
        some (PEMemory.Bank.lm1, width)) :
    memoryAccess.bank = Issue.Bank.lm1 :=
  issueBank_eq_lm1_of_registerBank_lm1 memoryAccess.bank
    (issueBankToRegisterBank_of_directDestinationBankWidth memoryAccess negated extended
      rounded mask PEMemory.Bank.lm1 width static)

/-- **A destination whose static bank is `.lm1` is a `.mem` `.lm1`
destination.**  Proved unconditionally (it is a consequence of the two
resolvers, not an assumption). -/
theorem lm1DestCount_holds (destinations : List ParsedOperand) :
    Lm1DestCount destinations := by
  intro d _ bank width static bankLm1
  subst bankLm1
  cases d with
  | mem memoryAccess negated extended rounded mask =>
      have bankEq := mem_issueBank_eq_lm1_of_directDestinationBankWidth memoryAccess negated
        extended rounded mask width static
      simp [ParsedOperand.isLm1MemoryDestination, bankEq]
  | bar lm1 width mask => simp [ParsedOperand.directDestinationBankWidth?] at static
  | forward kind negated extended rounded =>
      simp [ParsedOperand.directDestinationBankWidth?] at static
  | fixed kind => simp [ParsedOperand.directDestinationBankWidth?] at static
  | omr entry mask => simp [ParsedOperand.directDestinationBankWidth?] at static
  | matrix y width row => simp [ParsedOperand.directDestinationBankWidth?] at static
  | nowrite => simp [ParsedOperand.directDestinationBankWidth?] at static
  | l1bm width address => simp [ParsedOperand.directDestinationBankWidth?] at static
  | l2bm address l2b => simp [ParsedOperand.directDestinationBankWidth?] at static
  | dar address => simp [ParsedOperand.directDestinationBankWidth?] at static

/-- **A non-`.lm1` destination is `.lm1`-free in the static sense** (the
hypothesis that `executeParsedL1ToPE_writeDestinations_clean` consumes). -/
theorem lm1FreeDestination_of_not_mem (destinations : List ParsedOperand)
    (count : Lm1DestCount destinations) (destination : ParsedOperand)
    (member : destination ∈ destinations)
    (notLm1 : ParsedOperand.isLm1MemoryDestination destination = false) :
    ∀ (bank : PEMemory.Bank) (width : PEMemory.Width),
      ParsedOperand.directDestinationBankWidth? destination = some (bank, width) →
        bank ≠ PEMemory.Bank.lm1 := by
  intro bank width static bankLm1
  have isLm1 : ParsedOperand.isLm1MemoryDestination destination = true :=
    count destination member bank width static bankLm1
  rw [notLm1] at isLm1
  exact absurd isLm1 (by simp)

/-- **The destination list splits around its unique `.lm1` memory
destination.**  If exactly one element of the list is a `.mem` operand of bank
`.lm1`, then the list is `pre ++ d :: post` with `d` that operand and every
element of `pre` and `post` a non-`.lm1` destination. -/
theorem lm1Destination_split (destinations : List ParsedOperand)
    (count : (destinations.filter ParsedOperand.isLm1MemoryDestination).length = 1) :
    ∃ (pre : List ParsedOperand) (destination : ParsedOperand) (post : List ParsedOperand),
      destinations = pre ++ destination :: post ∧
      ParsedOperand.isLm1MemoryDestination destination = true ∧
      (∀ item ∈ pre, ParsedOperand.isLm1MemoryDestination item = false) ∧
      (∀ item ∈ post, ParsedOperand.isLm1MemoryDestination item = false) := by
  induction destinations with
  | nil => simp at count
  | cons head rest ih =>
      by_cases isLm1 : ParsedOperand.isLm1MemoryDestination head = true
      · have restNil : rest.filter ParsedOperand.isLm1MemoryDestination = [] := by
          have hlen : (rest.filter ParsedOperand.isLm1MemoryDestination).length = 0 := by
            simp only [List.filter_cons_of_pos isLm1] at count
            simpa using count
          exact List.eq_nil_of_length_eq_zero hlen
        have restFree : ∀ item ∈ rest, ParsedOperand.isLm1MemoryDestination item = false := by
          intro item member
          cases test : ParsedOperand.isLm1MemoryDestination item with
          | false => rfl
          | true =>
              have inFilter : item ∈ rest.filter ParsedOperand.isLm1MemoryDestination :=
                List.mem_filter.mpr ⟨member, test⟩
              rw [restNil] at inFilter
              simp at inFilter
        exact ⟨[], head, rest, rfl, isLm1, by simp, restFree⟩
      · have headFalse : ParsedOperand.isLm1MemoryDestination head = false := by
          cases test : ParsedOperand.isLm1MemoryDestination head <;> simp_all
        have restCount : (rest.filter ParsedOperand.isLm1MemoryDestination).length = 1 := by
          simp only [List.filter_cons_of_neg (by simpa using headFalse)] at count
          exact count
        obtain ⟨pre, destination, post, split, destLm1, preFree, postFree⟩ := ih restCount
        exact ⟨head :: pre, destination, post, by rw [split]; rfl, destLm1,
          by
            intro item member
            rcases List.mem_cons.mp member with rfl | member
            · exact headFalse
            · exact preFree item member,
          postFree⟩

/-! ## 2. The two shapes only see the `.lm1` writes

`Lm1WritesDoubleCopy` and `Lm1WritesNarrow` quantify over all members of a write
list but constrain only those whose destination is an `.lm1` access.  Hence both
are statements about `writes.filter PreparedParsedMaskedWrite.isLm1Write`:

* adding or removing `.lm1`-free writes changes neither the filter nor the
  shape (`lm1WritesDoubleCopy_iff_filter`, `lm1WritesNarrow_iff_filter`);
* an `.lm1`-free list satisfies both shapes vacuously.

This is what lets the free blocks of a split destination list be inserted
between the four `.lm1` writes without disturbing the singleton row shape. -/

/-- A write whose destination is `some ⟨.lm1, …⟩` passes the `.lm1` test. -/
theorem isLm1Write_of_destination_lm1 (write : PreparedParsedMaskedWrite)
    (width : PEMemory.Width) (address : Fin PEMemory.Bank.lm1.capacity)
    (destination : write.destination = some ⟨PEMemory.Bank.lm1, width, address⟩) :
    PreparedParsedMaskedWrite.isLm1Write write = true := by
  rcases write with ⟨destination', update, data, selection⟩
  simp only at destination
  subst destination
  simp [PreparedParsedMaskedWrite.isLm1Write]

/-- A list of `.lm1`-free writes satisfies `Lm1WritesDoubleCopy` vacuously. -/
theorem lm1WritesDoubleCopy_of_free (writes : List PreparedParsedMaskedWrite)
    (free : Lm1FreePreparedWrites writes) : Lm1WritesDoubleCopy writes := by
  intro write member width address data selection destination dataEq selectionEq
  have notLm1 : PreparedParsedMaskedWrite.isLm1Write write = false :=
    (lm1FreePreparedWrites_iff writes).mp free write member
  have bankNe := isLm1Write_false_bank write notLm1 ⟨PEMemory.Bank.lm1, width, address⟩
    destination
  exact absurd rfl bankNe

/-- A list of `.lm1`-free writes satisfies `Lm1WritesNarrow` vacuously. -/
theorem lm1WritesNarrow_of_free (writes : List PreparedParsedMaskedWrite)
    (free : Lm1FreePreparedWrites writes) : Lm1WritesNarrow writes := by
  refine ⟨[], ?_, by simp, by simp⟩
  intro write member width address destination
  have notLm1 : PreparedParsedMaskedWrite.isLm1Write write = false :=
    (lm1FreePreparedWrites_iff writes).mp free write member
  have bankNe := isLm1Write_false_bank write notLm1 ⟨PEMemory.Bank.lm1, width, address⟩
    destination
  exact absurd rfl bankNe

theorem lm1WritesDoubleCopy_filter (writes : List PreparedParsedMaskedWrite)
    (shape : Lm1WritesDoubleCopy writes) :
    Lm1WritesDoubleCopy (writes.filter PreparedParsedMaskedWrite.isLm1Write) := by
  intro write member width address data selection destination dataEq selectionEq
  exact shape write (List.mem_of_mem_filter member) width address data selection destination
    dataEq selectionEq

theorem lm1WritesDoubleCopy_of_filter (writes : List PreparedParsedMaskedWrite)
    (shape : Lm1WritesDoubleCopy (writes.filter PreparedParsedMaskedWrite.isLm1Write)) :
    Lm1WritesDoubleCopy writes := by
  intro write member width address data selection destination dataEq selectionEq
  have filtered : write ∈ writes.filter PreparedParsedMaskedWrite.isLm1Write :=
    List.mem_filter.mpr ⟨member, isLm1Write_of_destination_lm1 write width address destination⟩
  exact shape write filtered width address data selection destination dataEq selectionEq

theorem lm1WritesNarrow_filter (writes : List PreparedParsedMaskedWrite)
    (shape : Lm1WritesNarrow writes) :
    Lm1WritesNarrow (writes.filter PreparedParsedMaskedWrite.isLm1Write) := by
  obtain ⟨windows, covers, bound, sizes⟩ := shape
  exact ⟨windows, fun write member width address destination =>
    covers write (List.mem_of_mem_filter member) width address destination, bound, sizes⟩

theorem lm1WritesNarrow_of_filter (writes : List PreparedParsedMaskedWrite)
    (shape : Lm1WritesNarrow (writes.filter PreparedParsedMaskedWrite.isLm1Write)) :
    Lm1WritesNarrow writes := by
  obtain ⟨windows, covers, bound, sizes⟩ := shape
  refine ⟨windows, ?_, bound, sizes⟩
  intro write member width address destination
  have filtered : write ∈ writes.filter PreparedParsedMaskedWrite.isLm1Write :=
    List.mem_filter.mpr ⟨member, isLm1Write_of_destination_lm1 write width address destination⟩
  exact covers write filtered width address destination

theorem lm1WritesDoubleCopy_iff_filter (writes : List PreparedParsedMaskedWrite) :
    Lm1WritesDoubleCopy writes ↔
      Lm1WritesDoubleCopy (writes.filter PreparedParsedMaskedWrite.isLm1Write) :=
  ⟨lm1WritesDoubleCopy_filter writes, lm1WritesDoubleCopy_of_filter writes⟩

theorem lm1WritesNarrow_iff_filter (writes : List PreparedParsedMaskedWrite) :
    Lm1WritesNarrow writes ↔
      Lm1WritesNarrow (writes.filter PreparedParsedMaskedWrite.isLm1Write) :=
  ⟨lm1WritesNarrow_filter writes, lm1WritesNarrow_of_filter writes⟩

/-! ## 3. The destination loop with one `.lm1` destination

The destination loop of one cycle (`executeParsedL1ToPEAtPEs.writeCycles.writeDestinations`)
is a local recursive definition; its equations are named
(`executeParsedL1ToPE_writeDestinations_cons_*`).  The two ingredients here are:

* `executeParsedL1ToPE_writeDestinations_append`: running the loop on
  `first ++ second` is running it on `first` and then on `second` from the
  resulting register file and BARs;
* `executeParsedL1ToPE_writeDestinations_lm1_split_run`: if the destination list
  is `pre ++ d :: post` with `d` the unique `.mem` `.lm1` destination and
  `pre`/`post` `.lm1`-free, the loop commits
  `preWrites ++ [single .lm1 write] ++ postWrites` with the two free blocks.
  The `.lm1` write is the singleton store of `WelcomeL1PEShape.lean`; the free
  blocks are `executeParsedL1ToPE_writeDestinations_clean`. -/

/-- **The destination loop is associative.**  Running it on `first ++ second` is
running it on `first` and then on `second` from the resulting state. -/
theorem executeParsedL1ToPE_writeDestinations_append
    (currentState : State) (hasSingleLineMask : Bool) (maskRegisters : Masks.RegisterFile)
    (cycle : Fin 4) (context : ParsedIntegerContext) (output : IntegerALU.Bus) :
    ∀ (first second : List ParsedOperand) (files : IntegerRegisterFiles) (bar0 bar1 : BitVec 12),
      executeParsedL1ToPEAtPEs.writeCycles.writeDestinations currentState hasSingleLineMask
          maskRegisters cycle context output (first ++ second) files bar0 bar1 =
        match executeParsedL1ToPEAtPEs.writeCycles.writeDestinations currentState hasSingleLineMask
            maskRegisters cycle context output first files bar0 bar1 with
        | none => none
        | some (midFiles, midBar0, midBar1) =>
            executeParsedL1ToPEAtPEs.writeCycles.writeDestinations currentState hasSingleLineMask
              maskRegisters cycle context output second midFiles midBar0 midBar1 := by
  intro first
  induction first with
  | nil =>
      intro second files bar0 bar1
      rw [List.nil_append, executeParsedL1ToPEAtPEs.writeCycles.writeDestinations]
  | cons head rest ih =>
      intro second files bar0 bar1
      rw [List.cons_append]
      cases lowered : writeParsedL1ToPEDestination? files maskRegisters head
          { context with bar0 := bar0, bar1 := bar1 } output cycle
          currentState.maskDirective hasSingleLineMask with
      | none =>
          rw [executeParsedL1ToPE_writeDestinations_cons_none currentState hasSingleLineMask
            maskRegisters cycle context output head (rest ++ second) files bar0 bar1 lowered]
          rw [executeParsedL1ToPE_writeDestinations_cons_none currentState hasSingleLineMask
            maskRegisters cycle context output head rest files bar0 bar1 lowered]
      | some pair =>
          obtain ⟨writeFiles, barUpdate⟩ := pair
          cases barUpdate with
          | none =>
              rw [executeParsedL1ToPE_writeDestinations_cons_some_none currentState
                hasSingleLineMask maskRegisters cycle context output head (rest ++ second) files
                bar0 bar1 writeFiles lowered]
              rw [executeParsedL1ToPE_writeDestinations_cons_some_none currentState
                hasSingleLineMask maskRegisters cycle context output head rest files bar0 bar1
                writeFiles lowered]
              exact ih second writeFiles bar0 bar1
          | some update =>
              obtain ⟨lm1, value⟩ := update
              cases lm1 with
              | false =>
                  rw [executeParsedL1ToPE_writeDestinations_cons_some_false currentState
                    hasSingleLineMask maskRegisters cycle context output head (rest ++ second)
                    files bar0 bar1 writeFiles value lowered]
                  rw [executeParsedL1ToPE_writeDestinations_cons_some_false currentState
                    hasSingleLineMask maskRegisters cycle context output head rest files bar0
                    bar1 writeFiles value lowered]
                  exact ih second writeFiles value bar1
              | true =>
                  rw [executeParsedL1ToPE_writeDestinations_cons_some_true currentState
                    hasSingleLineMask maskRegisters cycle context output head (rest ++ second)
                    files bar0 bar1 writeFiles value lowered]
                  rw [executeParsedL1ToPE_writeDestinations_cons_some_true currentState
                    hasSingleLineMask maskRegisters cycle context output head rest files bar0
                    bar1 writeFiles value lowered]
                  exact ih second writeFiles bar0 value

/-- The singleton `.lm1` write of a cycle is the commit of its one-element list. -/
theorem commitParsedMaskedWrites_singleton_direct (files : IntegerRegisterFiles)
    (access : DirectMemoryAccess) (data : WordBus) (selection : PEWordSelection) :
    commitParsedMaskedWrites files [⟨some access, none, data, selection⟩] =
      writeDirectAccessMasked files access data selection := by
  rw [commitParsedMaskedWrites_singleton]
  rfl

/-- **The destination loop with one `.lm1` `.mem` destination.**  If the loop
succeeds on `pre ++ d :: post`, where `d` is the `.mem` operand of bank `.lm1`
and `pre`/`post` are `.lm1`-free, then it commits

`preWrites ++ [single .lm1 write] ++ postWrites`

with `preWrites`/`postWrites` `.lm1`-free.  The single write's static width `w`
comes from `d`'s own static pair (so it is the same for every cycle), and it is
4-aligned whenever `w = .double`. -/
theorem executeParsedL1ToPE_writeDestinations_lm1_split_run
    (currentState : State) (hasSingleLineMask : Bool) (maskRegisters : Masks.RegisterFile)
    (cycle : Fin 4) (context : ParsedIntegerContext) (output : IntegerALU.Bus)
    (pre post : List ParsedOperand)
    (memoryAccess : Access) (negated extended rounded : Bool) (mask : Option ParsedMask)
    (bankLm1 : memoryAccess.bank = Issue.Bank.lm1)
    (preFree : ∀ d ∈ pre, ∀ (bank : PEMemory.Bank) (width : PEMemory.Width),
      ParsedOperand.directDestinationBankWidth? d = some (bank, width) →
        bank ≠ PEMemory.Bank.lm1)
    (postFree : ∀ d ∈ post, ∀ (bank : PEMemory.Bank) (width : PEMemory.Width),
      ParsedOperand.directDestinationBankWidth? d = some (bank, width) →
        bank ≠ PEMemory.Bank.lm1)
    (files : IntegerRegisterFiles) (bar0 bar1 : BitVec 12)
    (nextFiles : IntegerRegisterFiles) (nextBar0 nextBar1 : BitVec 12)
    (executed : executeParsedL1ToPEAtPEs.writeCycles.writeDestinations currentState
      hasSingleLineMask maskRegisters cycle context output
      (pre ++ ParsedOperand.mem memoryAccess negated extended rounded mask :: post)
      files bar0 bar1 = some (nextFiles, nextBar0, nextBar1)) :
    ∃ (preWrites postWrites : List PreparedParsedMaskedWrite) (w : PEMemory.Width)
      (address : Fin PEMemory.Bank.lm1.capacity) (selection : PEWordSelection),
      nextFiles = commitParsedMaskedWrites files
        (preWrites ++
          [⟨some ⟨PEMemory.Bank.lm1, w, address⟩, none, PEMemory.unpackALUBus output,
            selection⟩] ++ postWrites) ∧
      Lm1FreePreparedWrites preWrites ∧ Lm1FreePreparedWrites postWrites ∧
      ParsedOperand.directDestinationBankWidth?
        (ParsedOperand.mem memoryAccess negated extended rounded mask) =
          some (PEMemory.Bank.lm1, w) ∧
      (w = PEMemory.Width.double → address.val % 4 = 0) := by
  have splitEq : pre ++ ParsedOperand.mem memoryAccess negated extended rounded mask :: post =
      (pre ++ [ParsedOperand.mem memoryAccess negated extended rounded mask]) ++ post :=
    (List.append_assoc pre [ParsedOperand.mem memoryAccess negated extended rounded mask] post).symm
  rw [splitEq] at executed
  rw [executeParsedL1ToPE_writeDestinations_append] at executed
  cases hmid : executeParsedL1ToPEAtPEs.writeCycles.writeDestinations currentState
      hasSingleLineMask maskRegisters cycle context output
      (pre ++ [ParsedOperand.mem memoryAccess negated extended rounded mask]) files bar0 bar1 with
  | none =>
      rw [hmid] at executed
      simp at executed
  | some triple =>
      obtain ⟨midFiles, midBar0, midBar1⟩ := triple
      rw [hmid] at executed
      simp only [] at executed
      rw [executeParsedL1ToPE_writeDestinations_append] at hmid
      cases hpre : executeParsedL1ToPEAtPEs.writeCycles.writeDestinations currentState
          hasSingleLineMask maskRegisters cycle context output pre files bar0 bar1 with
      | none =>
          rw [hpre] at hmid
          simp at hmid
      | some preTriple =>
          obtain ⟨preFiles, preBar0, preBar1⟩ := preTriple
          rw [hpre] at hmid
          simp only [] at hmid
          obtain ⟨access, selection, resolved, _resolvedSelection, filesEq, bar0Eq, bar1Eq⟩ :=
            writeDestinations_mem_singleton_resolves currentState hasSingleLineMask maskRegisters
              cycle context output memoryAccess negated extended rounded mask preFiles preBar0
              preBar1 midFiles midBar0 midBar1 hmid
          obtain ⟨preWrites, preCommit, preWritesFree⟩ :=
            executeParsedL1ToPE_writeDestinations_clean currentState hasSingleLineMask
              maskRegisters cycle context output pre files bar0 bar1 preFiles preBar0 preBar1
              preFree hpre
          obtain ⟨postWrites, postCommit, postWritesFree⟩ :=
            executeParsedL1ToPE_writeDestinations_clean currentState hasSingleLineMask
              maskRegisters cycle context output post midFiles midBar0 midBar1 nextFiles nextBar0
              nextBar1 postFree executed
          have staticAt : ParsedOperand.directDestinationBankWidth?
              (ParsedOperand.mem memoryAccess negated extended rounded mask) =
              some (access.bank, access.width) := by
            have pair := ParsedOperand.toDirectMemoryDestination?_bankWidth
              (ParsedOperand.mem memoryAccess negated extended rounded mask) context.pe cycle
              preBar0 preBar1 context.tWord
            rw [resolved] at pair
            exact pair.symm
          have bankEq : access.bank = PEMemory.Bank.lm1 :=
            directDestinationBankWidth?_mem_lm1_bank memoryAccess negated extended rounded mask
              bankLm1 access.bank access.width staticAt
          have staticLm1 : ParsedOperand.directDestinationBankWidth?
              (ParsedOperand.mem memoryAccess negated extended rounded mask) =
              some (PEMemory.Bank.lm1, access.width) := by
            rw [staticAt, bankEq]
          have accessEq : access = ⟨PEMemory.Bank.lm1, access.width,
              Fin.cast (by rw [bankEq]) access.address⟩ := by
            cases access with
            | mk bank width address =>
                simp only at bankEq
                subst bankEq
                rfl
          rw [accessEq] at filesEq
          refine ⟨preWrites, postWrites, access.width,
            Fin.cast (by rw [bankEq]) access.address, selection, ?_, preWritesFree,
            postWritesFree, staticLm1, ?_⟩
          · rw [postCommit, filesEq, preCommit]
            rw [← commitParsedMaskedWrites_singleton_direct]
            rw [← commitParsedMaskedWrites_append, ← commitParsedMaskedWrites_append]
            rw [← List.append_assoc]
          · intro double
            have aligned := toDirectMemoryDestination_address_mod_four
              (ParsedOperand.mem memoryAccess negated extended rounded mask) context.pe cycle
              preBar0 preBar1 context.tWord access resolved double
            simpa using aligned

/-! ## 4. The four-cycle shape with at most one `.lm1` destination

The four cycles produce the write lists `B c = preWrites c ++ [single c] ++
postWrites c` of §3.  The `.lm1` filter of the whole run is the four-element
list of single writes, so §2 reduces the shape of the run to the shape of the
singleton list of `WelcomeL1PEShape.lean`.  The four single writes share the
static width `w` of the unique `.lm1` destination, and each is 4-aligned when
`w = .double`; the data word is the zero bus (`zeroBus`).  Hence the run is
`Lm1WritesDoubleCopy` or `Lm1WritesNarrow`. -/

/-- The `.lm1` filter of an `.lm1`-free write list is empty. -/
theorem filter_isLm1Write_eq_nil (writes : List PreparedParsedMaskedWrite)
    (free : Lm1FreePreparedWrites writes) :
    writes.filter PreparedParsedMaskedWrite.isLm1Write = [] := by
  rw [List.filter_eq_nil_iff]
  intro write member
  rw [(lm1FreePreparedWrites_iff writes).mp free write member]
  simp

/-- The `.lm1` filter of `pre ++ [write] ++ post` is `[write]` when `write` is an
`.lm1` write and `pre`/`post` are `.lm1`-free. -/
theorem filter_isLm1Write_split (pre post : List PreparedParsedMaskedWrite)
    (write : PreparedParsedMaskedWrite)
    (writeLm1 : PreparedParsedMaskedWrite.isLm1Write write = true)
    (preFree : Lm1FreePreparedWrites pre) (postFree : Lm1FreePreparedWrites post) :
    (pre ++ [write] ++ post).filter PreparedParsedMaskedWrite.isLm1Write = [write] := by
  rw [List.filter_append, List.filter_append, filter_isLm1Write_eq_nil pre preFree,
    filter_isLm1Write_eq_nil post postFree, List.filter_cons_of_pos writeLm1, List.filter_nil,
    List.append_nil, List.nil_append]

/-- **The four-cycle broadcast shape with at most one `.lm1` destination.**
If the destination list of a `.l1bm` broadcast row contains at most one `.mem`
destination of bank `.lm1` (the others being `.bar`, `.nowrite` or non-`.lm1`
`.mem`), and the read state's broadcast bus is zero — in particular the all-zero
Welcome state — then the four cycle writes commit at the visited PE and are
`Lm1WritesDoubleCopy` or `Lm1WritesNarrow`. -/
theorem executeParsedL1ToPE_writeCycles_lm1_shape_atMostOne
    (readState currentState : State) (expression : ParsedExpr) (access : ParsedL1ToPEAccess)
    (hasSingleLineMask : Bool) (pe : PEId) (coordinates readContext : ParsedIntegerContext)
    (maskRegisters : Masks.RegisterFile)
    (atMostOne : (access.destinations.filter ParsedOperand.isLm1MemoryDestination).length ≤ 1)
    (zeroBus : ∀ cycle : Fin 4, l1ToPEBusAt readState expression access pe cycle = ⟨0, 0⟩)
    (files0 : IntegerRegisterFiles) (bar0 bar1 : BitVec 12)
    (nextFiles : IntegerRegisterFiles) (nextBar0 nextBar1 : BitVec 12)
    (executed : executeParsedL1ToPEAtPEs.writeCycles readState currentState expression access
      hasSingleLineMask pe coordinates readContext maskRegisters [0, 1, 2, 3] files0 bar0 bar1 =
      .ok (nextFiles, nextBar0, nextBar1)) :
    ∃ writes, nextFiles = commitParsedMaskedWrites files0 writes ∧
      (Lm1WritesDoubleCopy writes ∨ Lm1WritesNarrow writes) := by
  by_cases hzero : (access.destinations.filter ParsedOperand.isLm1MemoryDestination).length = 0
  · have noLm1 : ∀ d ∈ access.destinations, ∀ (bank : PEMemory.Bank) (width : PEMemory.Width),
        ParsedOperand.directDestinationBankWidth? d = some (bank, width) →
          bank ≠ PEMemory.Bank.lm1 := by
      intro d member bank width static bankLm1
      have isLm1 := lm1DestCount_holds access.destinations d member bank width static bankLm1
      have inFilter : d ∈ access.destinations.filter ParsedOperand.isLm1MemoryDestination :=
        List.mem_filter.mpr ⟨member, isLm1⟩
      rw [List.eq_nil_of_length_eq_zero hzero] at inFilter
      simp at inFilter
    obtain ⟨writes, commitEq, free⟩ :=
      executeParsedL1ToPE_writeCycles_clean readState currentState expression access
        hasSingleLineMask pe coordinates readContext maskRegisters noLm1 [0, 1, 2, 3] files0 bar0
        bar1 nextFiles nextBar0 nextBar1 executed
    exact ⟨writes, commitEq, Or.inr (lm1WritesNarrow_of_free writes free)⟩
  · have count1 : (access.destinations.filter ParsedOperand.isLm1MemoryDestination).length = 1 := by
      omega
    obtain ⟨preD, d, postD, destEq, dLm1, preFalse, postFalse⟩ :=
      lm1Destination_split access.destinations count1
    have countAll := lm1DestCount_holds access.destinations
    cases d with
    | mem memoryAccess negated extended rounded mask =>
      have bankLm1 : memoryAccess.bank = Issue.Bank.lm1 := by
        simpa [ParsedOperand.isLm1MemoryDestination, beq_iff_eq] using dLm1
      have preFree : ∀ item ∈ preD, ∀ (bank : PEMemory.Bank) (width : PEMemory.Width),
          ParsedOperand.directDestinationBankWidth? item = some (bank, width) →
            bank ≠ PEMemory.Bank.lm1 := by
        intro item member bank width static bankLm1'
        have itemMember : item ∈ access.destinations := by
          rw [destEq]
          exact List.mem_append_left _ member
        have isLm1 := countAll item itemMember bank width static bankLm1'
        have notLm1 := preFalse item member
        rw [notLm1] at isLm1
        exact absurd isLm1 (by simp)
      have postFree : ∀ item ∈ postD, ∀ (bank : PEMemory.Bank) (width : PEMemory.Width),
          ParsedOperand.directDestinationBankWidth? item = some (bank, width) →
            bank ≠ PEMemory.Bank.lm1 := by
        intro item member bank width static bankLm1'
        have itemMember : item ∈ access.destinations := by
          rw [destEq]
          exact List.mem_append_right _ (List.mem_cons_of_mem _ member)
        have isLm1 := countAll item itemMember bank width static bankLm1'
        have notLm1 := postFalse item member
        rw [notLm1] at isLm1
        exact absurd isLm1 (by simp)
      -- the four cycles
      obtain ⟨sel0, f1, m10, m11, _flush0, wrote0, rest1⟩ :=
        writeCycles_cons_exists readState currentState expression access hasSingleLineMask pe
          coordinates readContext maskRegisters 0 [1, 2, 3] files0 bar0 bar1 nextFiles nextBar0
          nextBar1 executed
      rw [destEq] at wrote0
      obtain ⟨preW0, postW0, w0, add0, wsel0, commit0, freePre0, freePost0, static0,
        align0⟩ :=
        executeParsedL1ToPE_writeDestinations_lm1_split_run currentState hasSingleLineMask
          maskRegisters 0 _ _ preD postD memoryAccess negated extended rounded mask bankLm1
          preFree postFree files0 bar0 bar1 f1 m10 m11 wrote0
      obtain ⟨sel1, f2, m20, m21, _flush1, wrote1, rest2⟩ :=
        writeCycles_cons_exists readState currentState expression access hasSingleLineMask pe
          coordinates readContext maskRegisters 1 [2, 3] f1 m10 m11 nextFiles nextBar0 nextBar1
          rest1
      rw [destEq] at wrote1
      obtain ⟨preW1, postW1, w1, add1, wsel1, commit1, freePre1, freePost1, static1,
        align1⟩ :=
        executeParsedL1ToPE_writeDestinations_lm1_split_run currentState hasSingleLineMask
          maskRegisters 1 _ _ preD postD memoryAccess negated extended rounded mask bankLm1
          preFree postFree f1 m10 m11 f2 m20 m21 wrote1
      obtain ⟨sel2, f3, m30, m31, _flush2, wrote2, rest3⟩ :=
        writeCycles_cons_exists readState currentState expression access hasSingleLineMask pe
          coordinates readContext maskRegisters 2 [3] f2 m20 m21 nextFiles nextBar0 nextBar1
          rest2
      rw [destEq] at wrote2
      obtain ⟨preW2, postW2, w2, add2, wsel2, commit2, freePre2, freePost2, static2,
        align2⟩ :=
        executeParsedL1ToPE_writeDestinations_lm1_split_run currentState hasSingleLineMask
          maskRegisters 2 _ _ preD postD memoryAccess negated extended rounded mask bankLm1
          preFree postFree f2 m20 m21 f3 m30 m31 wrote2
      obtain ⟨sel3, f4, m40, m41, _flush3, wrote3, rest4⟩ :=
        writeCycles_cons_exists readState currentState expression access hasSingleLineMask pe
          coordinates readContext maskRegisters 3 [] f3 m30 m31 nextFiles nextBar0 nextBar1 rest3
      rw [destEq] at wrote3
      obtain ⟨preW3, postW3, w3, add3, wsel3, commit3, freePre3, freePost3, static3,
        align3⟩ :=
        executeParsedL1ToPE_writeDestinations_lm1_split_run currentState hasSingleLineMask
          maskRegisters 3 _ _ preD postD memoryAccess negated extended rounded mask bankLm1
          preFree postFree f3 m30 m31 f4 m40 m41 wrote3
      rw [executeParsedL1ToPEAtPEs.writeCycles] at rest4
      have hfiles : nextFiles = f4 := by
        have h := StepResult.ok.inj rest4
        exact (congrArg Prod.fst h).symm
      -- the four widths agree
      have wEq1 : w1 = w0 := by
        have pairEq : (some (PEMemory.Bank.lm1, w1) : Option (PEMemory.Bank × PEMemory.Width)) =
            some (PEMemory.Bank.lm1, w0) := by
          rw [← static1, static0]
        exact congrArg Prod.snd (Option.some.inj pairEq)
      have wEq2 : w2 = w0 := by
        have pairEq : (some (PEMemory.Bank.lm1, w2) : Option (PEMemory.Bank × PEMemory.Width)) =
            some (PEMemory.Bank.lm1, w0) := by
          rw [← static2, static0]
        exact congrArg Prod.snd (Option.some.inj pairEq)
      have wEq3 : w3 = w0 := by
        have pairEq : (some (PEMemory.Bank.lm1, w3) : Option (PEMemory.Bank × PEMemory.Width)) =
            some (PEMemory.Bank.lm1, w0) := by
          rw [← static3, static0]
        exact congrArg Prod.snd (Option.some.inj pairEq)
      -- the written data are the zero bus
      have data0 : PEMemory.unpackALUBus (parsedOutputAfterFlush sel0
          (l1ToPEBusAt readState expression access pe 0)) = (fun _ => 0) := by
        rw [zeroBus 0, parsedOutputAfterFlush_zero, unpackALUBus_zero]
      have data1 : PEMemory.unpackALUBus (parsedOutputAfterFlush sel1
          (l1ToPEBusAt readState expression access pe 1)) = (fun _ => 0) := by
        rw [zeroBus 1, parsedOutputAfterFlush_zero, unpackALUBus_zero]
      have data2 : PEMemory.unpackALUBus (parsedOutputAfterFlush sel2
          (l1ToPEBusAt readState expression access pe 2)) = (fun _ => 0) := by
        rw [zeroBus 2, parsedOutputAfterFlush_zero, unpackALUBus_zero]
      have data3 : PEMemory.unpackALUBus (parsedOutputAfterFlush sel3
          (l1ToPEBusAt readState expression access pe 3)) = (fun _ => 0) := by
        rw [zeroBus 3, parsedOutputAfterFlush_zero, unpackALUBus_zero]
      -- the single writes, with the zero data bus
      rw [data0] at commit0
      rw [data1] at commit1
      rw [data2] at commit2
      rw [data3] at commit3
      let write0 : PreparedParsedMaskedWrite :=
        ⟨some ⟨PEMemory.Bank.lm1, w0, add0⟩, none, (fun _ => 0 : WordBus), wsel0⟩
      let write1 : PreparedParsedMaskedWrite :=
        ⟨some ⟨PEMemory.Bank.lm1, w1, add1⟩, none, (fun _ => 0 : WordBus), wsel1⟩
      let write2 : PreparedParsedMaskedWrite :=
        ⟨some ⟨PEMemory.Bank.lm1, w2, add2⟩, none, (fun _ => 0 : WordBus), wsel2⟩
      let write3 : PreparedParsedMaskedWrite :=
        ⟨some ⟨PEMemory.Bank.lm1, w3, add3⟩, none, (fun _ => 0 : WordBus), wsel3⟩
      let addresses : Fin 4 → Fin PEMemory.Bank.lm1.capacity := fourCases add0 add1 add2 add3
      let selections : Fin 4 → PEWordSelection := fourCases wsel0 wsel1 wsel2 wsel3
      -- the four-element shaped list
      have coreEq : [write0, write1, write2, write3] = l1ToPEWrites w0 addresses selections := by
        simp only [write0, write1, write2, write3, wEq1, wEq2, wEq3]
        rw [l1ToPEWrites_eq_four]
        rfl
      -- the `.lm1` filters of the four blocks
      have nilPre0 : preW0.filter PreparedParsedMaskedWrite.isLm1Write = [] :=
        filter_isLm1Write_eq_nil preW0 freePre0
      have nilPost0 : postW0.filter PreparedParsedMaskedWrite.isLm1Write = [] :=
        filter_isLm1Write_eq_nil postW0 freePost0
      have nilPre1 : preW1.filter PreparedParsedMaskedWrite.isLm1Write = [] :=
        filter_isLm1Write_eq_nil preW1 freePre1
      have nilPost1 : postW1.filter PreparedParsedMaskedWrite.isLm1Write = [] :=
        filter_isLm1Write_eq_nil postW1 freePost1
      have nilPre2 : preW2.filter PreparedParsedMaskedWrite.isLm1Write = [] :=
        filter_isLm1Write_eq_nil preW2 freePre2
      have nilPost2 : postW2.filter PreparedParsedMaskedWrite.isLm1Write = [] :=
        filter_isLm1Write_eq_nil postW2 freePost2
      have nilPre3 : preW3.filter PreparedParsedMaskedWrite.isLm1Write = [] :=
        filter_isLm1Write_eq_nil preW3 freePre3
      have nilPost3 : postW3.filter PreparedParsedMaskedWrite.isLm1Write = [] :=
        filter_isLm1Write_eq_nil postW3 freePost3
      have single0 : [write0].filter PreparedParsedMaskedWrite.isLm1Write = [write0] := by
        rw [List.filter_cons_of_pos (isLm1Write_of_destination_lm1 write0 w0 add0 rfl)]
        rfl
      have single1 : [write1].filter PreparedParsedMaskedWrite.isLm1Write = [write1] := by
        rw [List.filter_cons_of_pos (isLm1Write_of_destination_lm1 write1 w1 add1 rfl)]
        rfl
      have single2 : [write2].filter PreparedParsedMaskedWrite.isLm1Write = [write2] := by
        rw [List.filter_cons_of_pos (isLm1Write_of_destination_lm1 write2 w2 add2 rfl)]
        rfl
      have single3 : [write3].filter PreparedParsedMaskedWrite.isLm1Write = [write3] := by
        rw [List.filter_cons_of_pos (isLm1Write_of_destination_lm1 write3 w3 add3 rfl)]
        rfl
      have totalFilter :
          ((preW0 ++ [write0] ++ postW0) ++
            ((preW1 ++ [write1] ++ postW1) ++
              ((preW2 ++ [write2] ++ postW2) ++ (preW3 ++ [write3] ++ postW3)))).filter
            PreparedParsedMaskedWrite.isLm1Write = [write0, write1, write2, write3] := by
        simp only [List.filter_append, nilPre0, nilPost0, nilPre1, nilPost1, nilPre2, nilPost2,
          nilPre3, nilPost3, single0, single1, single2, single3, List.nil_append,
          List.append_nil]
        rfl
      refine ⟨(preW0 ++ [write0] ++ postW0) ++ ((preW1 ++ [write1] ++ postW1) ++
          ((preW2 ++ [write2] ++ postW2) ++ (preW3 ++ [write3] ++ postW3))), ?_, ?_⟩
      · rw [hfiles, commit3, commit2, commit1, commit0]
        rw [← commitParsedMaskedWrites_append, ← commitParsedMaskedWrites_append,
          ← commitParsedMaskedWrites_append]
      · by_cases double : w0 = PEMemory.Width.double
        · left
          have aligned : ∀ cycle, (addresses cycle).val % 4 = 0 := by
            intro cycle
            rcases fin_four_eq cycle with rfl | rfl | rfl | rfl
            · show add0.val % 4 = 0
              exact align0 double
            · show add1.val % 4 = 0
              exact align1 (by rw [wEq1]; exact double)
            · show add2.val % 4 = 0
              exact align2 (by rw [wEq2]; exact double)
            · show add3.val % 4 = 0
              exact align3 (by rw [wEq3]; exact double)
          have core : Lm1WritesDoubleCopy [write0, write1, write2, write3] := by
            rw [coreEq, double]
            exact l1ToPEWrites_doubleCopy addresses selections aligned
          exact (lm1WritesDoubleCopy_iff_filter _).mpr (by rw [totalFilter]; exact core)
        · right
          have core : Lm1WritesNarrow [write0, write1, write2, write3] := by
            rw [coreEq]
            exact l1ToPEWrites_narrow w0 addresses selections double
          exact (lm1WritesNarrow_iff_filter _).mpr (by rw [totalFilter]; exact core)
    | bar lm1 width mask => simp [ParsedOperand.isLm1MemoryDestination] at dLm1
    | forward kind negated extended rounded =>
        simp [ParsedOperand.isLm1MemoryDestination] at dLm1
    | fixed kind => simp [ParsedOperand.isLm1MemoryDestination] at dLm1
    | omr entry mask => simp [ParsedOperand.isLm1MemoryDestination] at dLm1
    | matrix y width row => simp [ParsedOperand.isLm1MemoryDestination] at dLm1
    | nowrite => simp [ParsedOperand.isLm1MemoryDestination] at dLm1
    | l1bm width address => simp [ParsedOperand.isLm1MemoryDestination] at dLm1
    | l2bm address l2b => simp [ParsedOperand.isLm1MemoryDestination] at dLm1
    | dar address => simp [ParsedOperand.isLm1MemoryDestination] at dLm1

/-! ## 5. The PE walk, producer and stage forms

`executeParsedL1ToPEAtPEs` walks `List.finRange 4096`; only the visit to PE 0
matters for the observed PE, and the walk's tail never touches PE 0
(`executeParsedL1ToPEAtPEs_peRegisters_not_mem`).  The induction below is the
one of `WelcomeL1PEShape.lean` §5 with the singleton cycle shape replaced by
§4. -/

/-- **The broadcast row's shape at PE 0, along an arbitrary PE walk.** -/
theorem executeParsedL1ToPEAtPEs_lm1_shape_atMostOne
    (readState : State) (expression : ParsedExpr) (access : ParsedL1ToPEAccess)
    (hasSingleLineMask usePreIssueMask noForward : Bool)
    (atMostOne : (access.destinations.filter ParsedOperand.isLm1MemoryDestination).length ≤ 1)
    (zeroBus : ∀ (pe : PEId) (cycle : Fin 4),
      l1ToPEBusAt readState expression access pe cycle = ⟨0, 0⟩) :
    ∀ (pes : List PEId), pes.Nodup → welcomePE ∈ pes → ∀ (currentState next : State),
      executeParsedL1ToPEAtPEs readState currentState expression access pes noForward
        hasSingleLineMask usePreIssueMask = .ok next →
      ∃ writes, next.peRegisters welcomePE =
          commitParsedMaskedWrites (currentState.peRegisters welcomePE) writes ∧
        (Lm1WritesDoubleCopy writes ∨ Lm1WritesNarrow writes) := by
  intro pes
  induction pes with
  | nil =>
      intro _ member _ _ _
      simp at member
  | cons pe rest ih =>
      intro nodup member currentState next executed
      rw [executeParsedL1ToPEAtPEs.eq_2] at executed
      split at executed
      · simp at executed
      · simp only [] at executed
        split at executed
        · simp at executed
        · simp at executed
        · rename_i files bar0 bar1 ran
          have nodupParts := List.nodup_cons.mp nodup
          by_cases same : pe = welcomePE
          · subst same
            have tailFrame : next.peRegisters welcomePE = _ :=
              executeParsedL1ToPEAtPEs_peRegisters_not_mem readState expression access
                noForward hasSingleLineMask usePreIssueMask rest _ next welcomePE executed
                nodupParts.1
            obtain ⟨writes, commitFiles, shape⟩ :=
              executeParsedL1ToPE_writeCycles_lm1_shape_atMostOne readState currentState
                expression access hasSingleLineMask welcomePE
                (ParsedIntegerContext.ofLinearIndex welcomePE) (readState.peContext welcomePE) _
                atMostOne (fun cycle => zeroBus welcomePE cycle)
                (currentState.peRegisters welcomePE) (currentState.peContext welcomePE).bar0
                (currentState.peContext welcomePE).bar1 files bar0 bar1 ran
            have headFiles : next.peRegisters welcomePE = files := by
              rw [tailFrame]
              simp
            exact ⟨writes, by rw [headFiles, commitFiles], shape⟩
          · have ne : welcomePE ≠ pe := fun h => same h.symm
            have memberRest : welcomePE ∈ rest := by
              rcases List.mem_cons.mp member with h | h
              · exact absurd h.symm same
              · exact h
            obtain ⟨writes, commitTail, shape⟩ := ih nodupParts.2 memberRest _ next executed
            refine ⟨writes, ?_, shape⟩
            rw [commitTail]
            congr 1
            simp [ne]

/-- **The `.l1bm` broadcast row is a `double`-copy or narrow writer at PE 0, for
an arbitrary destination list.**  At the all-zero Welcome initial state, a
`.l1bm` broadcast row (`pbcast` / `mbcast` / `m4bcast` / `distrib`) whose
destination list contains at most one `.mem` destination of bank `.lm1` prepares
a write list at PE 0 that is either `Lm1WritesDoubleCopy` (`w = .double`) or
`Lm1WritesNarrow`, and PE 0's register file after the producer is that list's
commit. -/
theorem executeParsedL1ToPEProducer_lm1_shape_atMostOne
    (input : ProofsLean.MNCore.PlusOne.Words) (currentState next : State)
    (expression : ParsedExpr) (access : ParsedL1ToPEAccess)
    (noForward hasSingleLineMask usePreIssueMask : Bool)
    (atMostOne : (access.destinations.filter ParsedOperand.isLm1MemoryDestination).length ≤ 1)
    (lowered : lowerParsedL1ToPE? expression = some access)
    (executed : executeParsedL1ToPEProducer (welcomeInitialState input) currentState expression
      noForward hasSingleLineMask usePreIssueMask = .ok next) :
    ∃ writes, next.peRegisters welcomePE =
        commitParsedMaskedWrites (currentState.peRegisters welcomePE) writes ∧
      (Lm1WritesDoubleCopy writes ∨ Lm1WritesNarrow writes) := by
  rw [executeParsedL1ToPEProducer, lowered] at executed
  exact executeParsedL1ToPEAtPEs_lm1_shape_atMostOne (welcomeInitialState input) expression
    access hasSingleLineMask usePreIssueMask noForward atMostOne
    (fun pe cycle => l1ToPEBusAt_welcomeInitialState input expression access pe cycle)
    (List.finRange 4096) (List.nodup_finRange 4096) (List.mem_finRange welcomePE)
    currentState next executed

/-- **The stage-level form.**  The L1BM-to-PE stage of a line with exactly one
L1ToPE producer row is that row's producer, so the multi-destination shape
applies. -/
theorem executeParsedL1ToPEProducers_lm1_shape_atMostOne
    (input : ProofsLean.MNCore.PlusOne.Words) (currentState next : State)
    (expressions : List ParsedExpr) (expression : ParsedExpr) (access : ParsedL1ToPEAccess)
    (noForward hasSingleLineMask usePreIssueMask : Bool)
    (atMostOne : (access.destinations.filter ParsedOperand.isLm1MemoryDestination).length ≤ 1)
    (lowered : lowerParsedL1ToPE? expression = some access)
    (filtered : expressions.filter parsedExprIsL1ToPEProducer = [expression])
    (executed : executeParsedL1ToPEProducers (welcomeInitialState input) currentState expressions
      noForward hasSingleLineMask usePreIssueMask = .ok next) :
    ∃ writes, next.peRegisters welcomePE =
        commitParsedMaskedWrites (currentState.peRegisters welcomePE) writes ∧
      (Lm1WritesDoubleCopy writes ∨ Lm1WritesNarrow writes) := by
  rw [executeParsedL1ToPEProducers, filtered] at executed
  dsimp only at executed
  exact executeParsedL1ToPEProducer_lm1_shape_atMostOne input currentState next expression
    access noForward hasSingleLineMask usePreIssueMask atMostOne lowered executed

/-! ## 5.5 "At most one `.lm1` memory destination" is a consequence of legality

The issue checker's `writesUnique` requires every row's `writeBanks` to be
`Nodup`, and `writeBanks` is the row's `.mem` write banks followed by its BAR
writes.  Two `.mem` destinations of bank `.lm1` in one row would therefore
repeat `.lm1` in that list, so a legal row has **at most one** `.mem`
destination of bank `.lm1`.  This is proved here, so the count hypothesis of the
row shape is not an assumption on legal lines. -/

/-- A `Nodup` list contains any element at most once. -/
theorem nodup_count_le_one {α : Type} [BEq α] [LawfulBEq α] (a : α) :
    ∀ {l : List α}, l.Nodup → l.count a ≤ 1 := by
  intro l
  induction l with
  | nil => simp
  | cons b rest ih =>
      intro nodup
      have parts := List.nodup_cons.mp nodup
      rw [List.count_cons]
      by_cases heq : (b == a) = true
      · have hb : b = a := LawfulBEq.eq_of_beq heq
        have hnotin : a ∉ rest := by rw [← hb]; exact parts.1
        have hcount : rest.count a = 0 := by rw [List.count_eq_zero]; exact hnotin
        rw [hcount]
        simp [heq]
      · rw [if_neg heq]
        simpa using ih parts.2

/-- Every parsed expression of the line occurs in `projectFrom` at some id. -/
theorem exists_toIssueExpr_mem_projectFrom (nextId : Nat) (expressions : List ParsedExpr)
    (expression : ParsedExpr) (member : expression ∈ expressions) :
    ∃ id, expression.toIssueExpr id ∈ projectFrom nextId expressions := by
  induction expressions generalizing nextId with
  | nil => simp at member
  | cons head rest ih =>
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨nextId, by simp [projectFrom]⟩
      · obtain ⟨id, hid⟩ := ih (nextId + 1) member
        exact ⟨id, by simp only [projectFrom, List.mem_cons]; exact Or.inr hid⟩

/-- **Every row of a legal line has distinct write banks.** -/
theorem writeBanks_nodup_of_legal (expressions : List ParsedExpr)
    (legal : LegalParsedLine expressions) (expression : ParsedExpr)
    (member : expression ∈ expressions) :
    ((ParsedOperand.accesses expression.destinations).map Issue.Access.bank).Nodup := by
  obtain ⟨id, hid⟩ := exists_toIssueExpr_mem_projectFrom 0 expressions expression member
  have nodupAll := (show Legal (projectLine expressions) from legal).2.2.2.2.2.2.1.1
  have h := nodupAll (expression.toIssueExpr id) hid
  have hb : (expression.toIssueExpr id).writeBanks =
      (ParsedOperand.accesses expression.destinations).map Issue.Access.bank ++
        (expression.toIssueExpr id).barWrites := rfl
  rw [hb] at h
  exact h.of_append_left

/-- **A legal row has at most one `.mem` destination of bank `.lm1`.** -/
theorem filter_isLm1_le_one_of_legal (expressions : List ParsedExpr)
    (legal : LegalParsedLine expressions) (expression : ParsedExpr)
    (member : expression ∈ expressions) :
    (expression.destinations.filter ParsedOperand.isLm1MemoryDestination).length ≤ 1 := by
  rw [filter_isLm1_length_bankList, ← accesses_map_bank_eq_bankList]
  exact nodup_count_le_one Issue.Bank.lm1
    (writeBanks_nodup_of_legal expressions legal expression member)

/-- **An accepted line has at most one `.mem` destination of bank `.lm1` per
row.** -/
theorem filter_isLm1_le_one_of_accepted (expressions : List NormalizedExpr)
    (unrefuted : WelcomePEUnrefuted expressions) (expression : ParsedExpr)
    (member : expression ∈ expressions.map NormalizedExpr.toParsed) :
    (expression.destinations.filter ParsedOperand.isLm1MemoryDestination).length ≤ 1 := by
  have legal : LegalParsedLine (expressions.map NormalizedExpr.toParsed) :=
    parsed_topline_check_sound (InstructionLine.pe expressions).toParsed unrefuted.1.1
  exact filter_isLm1_le_one_of_legal _ legal expression member

/-! ## 6. The multi-destination `.l1bm` writer package

`WelcomePEL1BMWriterDataForNoSingleton` asks the writer's lowering to have a
*single* `.mem` `.lm1` destination.  §4/§5 show that the only thing the row
shape needs is the *count*: at most one `.mem` destination of bank `.lm1`, and
§5.5 shows that count is a consequence of the issue checker.  The package below
records exactly that, and is proved for every unrefuted line
(`welcomePEL1BMWriterDataMultiDest_holds`).

The conservative direction from the singleton package is
`welcomePEL1BMWriterDataForMultiDest_of_noSingleton`: a single `.mem` `.lm1`
destination has one-element `.lm1` filter, so every line covered by the
singleton package is covered by this one. -/

/-- **The `.l1bm`-broadcast-writer data of one line, with an arbitrary
destination list.**  The only restriction is that the writer's destination list
contains at most one `.mem` destination of bank `.lm1`; the rest may be `.bar`,
`.nowrite` or non-`.lm1` `.mem`.

The count is stated on the *parsed* destination list, not on the lowering's
copy: requiring the lowering to exist is not a consequence of acceptance (a
broadcast row with a memory source has the right operation but does not lower),
and such a row simply fails in the L1BM-to-PE stage, which the dispatch below
handles as the vacuous case. -/
def WelcomePEL1BMWriterDataForMultiDest (expressions : List NormalizedExpr) : Prop :=
  ∀ (e : ParsedExpr),
    e ∈ expressions.map NormalizedExpr.toParsed →
      parsedExprIsL1ToPEProducer e = true →
      Issue.Bank.lm1 ∈ (e.toIssueExpr 0).writeBanks →
      (e.destinations.filter ParsedOperand.isLm1MemoryDestination).length ≤ 1

/-- The global multi-destination `.l1bm`-writer data package. -/
def WelcomePEL1BMWriterDataMultiDest : Prop :=
  ∀ expressions, WelcomePEUnrefuted expressions →
    WelcomePEL1BMWriterDataForMultiDest expressions

/-- **The multi-destination package holds on every unrefuted line.**  The count
is a consequence of `writesUnique` (§5.5), not a hypothesis. -/
theorem welcomePEL1BMWriterDataForMultiDest_holds (expressions : List NormalizedExpr)
    (unrefuted : WelcomePEUnrefuted expressions) :
    WelcomePEL1BMWriterDataForMultiDest expressions :=
  fun expression member _ _ =>
    filter_isLm1_le_one_of_accepted expressions unrefuted expression member

/-- **The global multi-destination package is unconditional.** -/
theorem welcomePEL1BMWriterDataMultiDest_holds : WelcomePEL1BMWriterDataMultiDest :=
  fun expressions unrefuted =>
    welcomePEL1BMWriterDataForMultiDest_holds expressions unrefuted

/-- **Conservative direction: the singleton package implies the
multi-destination one.**  A single `.mem` `.lm1` destination has a one-element
`.lm1` filter, so "at most one" holds. -/
theorem welcomePEL1BMWriterDataForMultiDest_of_noSingleton
    (expressions : List NormalizedExpr)
    (data : WelcomePEL1BMWriterDataForNoSingleton expressions) :
    WelcomePEL1BMWriterDataForMultiDest expressions := by
  intro e eMem l1 writer
  obtain ⟨access, memoryAccess, negated, extended, rounded, mask, w, lowered, destinations,
    static⟩ := data e eMem l1 writer
  rw [← lowerParsedL1ToPE?_destinations_eq e access lowered, destinations]
  simpa using List.length_filter_le ParsedOperand.isLm1MemoryDestination
    [ParsedOperand.mem memoryAccess negated extended rounded mask]

/-- **Global conservative direction for the multi-destination package.** -/
theorem welcomePEL1BMWriterDataMultiDest_of_noSingleton
    (data : WelcomePEL1BMWriterDataNoSingleton) : WelcomePEL1BMWriterDataMultiDest :=
  fun expressions unrefuted =>
    welcomePEL1BMWriterDataForMultiDest_of_noSingleton expressions
      (data expressions unrefuted)

/-- **Conservative direction from the round-49 `.l1bm` package** (through the
singleton weakened package). -/
theorem welcomePEL1BMWriterDataForMultiDest_of_strong
    (expressions : List NormalizedExpr) (data : WelcomePEL1BMWriterDataFor expressions) :
    WelcomePEL1BMWriterDataForMultiDest expressions :=
  welcomePEL1BMWriterDataForMultiDest_of_noSingleton expressions
    (welcomePEL1BMWriterDataFor_noSingleton_of_strong expressions data)

/-- **The `.l1bm`-writer dispatch with an arbitrary destination list.**  This is
`welcomePEWriteShape_of_l1bmWriter_dispatch_noSingleton` with the singleton
destination-list hypothesis replaced by "at most one `.lm1` memory destination"
and the stage shape of §5. -/
theorem welcomePEWriteShape_of_l1bmWriter_dispatch_multiDest
    (expressions : List NormalizedExpr)
    (e : ParsedExpr)
    (atMostOne : (e.destinations.filter ParsedOperand.isLm1MemoryDestination).length ≤ 1)
    (eMem : e ∈ expressions.map NormalizedExpr.toParsed)
    (l1Kind : parsedExprIsL1ToPEProducer e = true)
    (intFree : ∀ expression ∈ (expressions.map NormalizedExpr.toParsed).filter
        parsedExprIsIntegerMatrixReadStageInput, WelcomeRowHasNoLm1Destination expression)
    (floatFreeRows : ∀ expression ∈ (expressions.map NormalizedExpr.toParsed).filter
        parsedExprIsSupportedFloatMAUProducer, WelcomeRowHasNoLm1Destination expression)
    (middleFree : WelcomePEMiddleStageLm1Free expressions)
    (matrixFreeRows : WelcomePEMatrixMAUStageLm1Free expressions) :
    WelcomePEWriteShape expressions := by
  apply welcomePEWriteShape_of_commit_shape
  intro next step
  have executed := welcomeSealed_step_ok step
  simp only [executeNormalizedLine, NormalizedLine.toInstruction?,
    Issue.InstructionLine.toNormalizedLine] at executed
  obtain ⟨accepted, waits, unsupported, supported⟩ :=
    executeIntegerProducerInstructionLine_pe_conditions expressions
      (welcomeInitialState welcomeZeroWords) next executed
  obtain ⟨nextPEs, nextMsl, nextRelu, nextBlockFloat, afterMatrix, nextShared, nextBroadcast,
    walkExecuted, mslExecuted, reluExecuted, blockExecuted, matrixExecuted, sharedExecuted,
    l1Executed, nextEq⟩ :=
    executeIntegerProducerInstructionLine_pe_stages_exists expressions
      (welcomeInitialState welcomeZeroWords) next accepted waits unsupported supported executed
  have l1Filter : (expressions.map NormalizedExpr.toParsed).filter
      parsedExprIsL1ToPEProducer = [e] :=
    l1ToPEProducers_filter_eq_singleton_of_ok (welcomeInitialState welcomeZeroWords) nextShared
      (expressions.map NormalizedExpr.toParsed)
      (expressions.any (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed))
      (expressions.any (parsedExprHasSingleLineWriteMask ∘ NormalizedExpr.toParsed))
      (parsedL1ToPEPrecedesOMRWriter (expressions.map NormalizedExpr.toParsed))
      nextBroadcast e (List.mem_filter.mpr ⟨eMem, l1Kind⟩) l1Executed
  have floatFreeWalk : ∀ expression ∈ (welcomePEWalkFilter expressions).filter
      parsedExprIsSupportedFloatMAUProducer, WelcomeRowHasNoLm1Destination expression := by
    intro expression member
    exact floatFreeRows expression (by rw [welcomePEWalkFilter_float] at member; exact member)
  obtain ⟨intWrites, floatWrites, intSlots, intBars, intPrep, intCommit, floatFree⟩ :=
    executeIntegerProducerLineAtPEs_zero_prepared_float_clean (welcomePEWalkFilter expressions)
      nextPEs floatFreeWalk walkExecuted
  have intWritesFree : Lm1FreePreparedWrites intWrites :=
    welcomeIntegerPrep_lm1_free (welcomeInitialState welcomeZeroWords) welcomePE
      (welcomePEWalkFilter expressions) intWrites intSlots intBars intPrep (by
        intro expression member
        exact intFree expression (by rw [welcomePEWalkFilter_integer] at member; exact member))
  have combinedFree : Lm1FreePreparedWrites (intWrites ++ floatWrites) :=
    lm1FreePreparedWrites_append intWritesFree floatFree
  obtain ⟨mslWrites, mslCommit, mslFree⟩ :=
    welcomePEMslMsrStageLm1Provenance (welcomeInitialState welcomeZeroWords) nextPEs nextMsl
      (expressions.map NormalizedExpr.toParsed)
      (expressions.any (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed))
      (expressions.any (parsedExprHasSingleLineWriteMask ∘ NormalizedExpr.toParsed))
      (welcomePEMiddleStageLm1Free_msl expressions middleFree) mslExecuted
  obtain ⟨reluWrites, reluCommit, reluFree⟩ :=
    welcomePEFloatReluStageLm1Provenance (welcomeInitialState welcomeZeroWords) nextMsl nextRelu
      (expressions.map NormalizedExpr.toParsed)
      (expressions.any (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed))
      (expressions.any (parsedExprHasSingleLineWriteMask ∘ NormalizedExpr.toParsed))
      (welcomePEMiddleStageLm1Free_relu expressions middleFree) reluExecuted
  obtain ⟨blockWrites, blockCommit, blockFree⟩ :=
    welcomePEBlockFloatStageLm1Provenance (welcomeInitialState welcomeZeroWords) nextRelu
      nextBlockFloat (expressions.map NormalizedExpr.toParsed)
      (expressions.any (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed))
      (expressions.any (parsedExprHasSingleLineWriteMask ∘ NormalizedExpr.toParsed))
      (welcomePEMiddleStageLm1Free_block expressions middleFree) blockExecuted
  obtain ⟨matrixWrites, matrixCommit, matrixFree⟩ :=
    welcomePEMatrixMAUStageLm1Provenance (welcomeInitialState welcomeZeroWords) nextBlockFloat
      afterMatrix (expressions.map NormalizedExpr.toParsed)
      (expressions.any (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed))
      (expressions.any (parsedExprHasSingleLineWriteMask ∘ NormalizedExpr.toParsed))
      (welcomePEMiddleStageLm1Free_matrixMAU expressions matrixFreeRows) matrixExecuted
  -- the writer must lower: otherwise the L1BM-to-PE stage fails, contradicting
  -- the successful step
  cases lowered : lowerParsedL1ToPE? e with
  | none =>
      exfalso
      rw [executeParsedL1ToPEProducers, l1Filter] at l1Executed
      dsimp only at l1Executed
      rw [executeParsedL1ToPEProducer, lowered] at l1Executed
      simp at l1Executed
  | some access =>
  have accessCount : (access.destinations.filter ParsedOperand.isLm1MemoryDestination).length ≤ 1 := by
    rw [lowerParsedL1ToPE?_destinations_eq e access lowered]
    exact atMostOne
  obtain ⟨l1Writes, l1Commit, l1Shape⟩ :=
    executeParsedL1ToPEProducers_lm1_shape_atMostOne welcomeZeroWords nextShared nextBroadcast
      (expressions.map NormalizedExpr.toParsed) e access
      (expressions.any (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed))
      (expressions.any (parsedExprHasSingleLineWriteMask ∘ NormalizedExpr.toParsed))
      (parsedL1ToPEPrecedesOMRWriter (expressions.map NormalizedExpr.toParsed))
      accessCount lowered l1Filter l1Executed
  have sharedFrame : nextShared.peRegisters welcomePE = afterMatrix.peRegisters welcomePE :=
    congrFun (executeParsedSharedBlockProducers_peRegisters (welcomeInitialState welcomeZeroWords)
      afterMatrix nextShared (expressions.map NormalizedExpr.toParsed)
      (!(expressions.any (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed)))
      sharedExecuted) welcomePE
  have peEq : next.peRegisters welcomePE = nextBroadcast.peRegisters welcomePE := by
    rw [nextEq]
  refine ⟨(intWrites ++ floatWrites) ++ mslWrites ++ reluWrites ++ blockWrites ++ matrixWrites
      ++ l1Writes,
    executeIntegerProducerInstructionLine_pe_commit_split nextPEs nextMsl nextRelu
      nextBlockFloat afterMatrix nextShared nextBroadcast next peEq (intWrites ++ floatWrites)
      mslWrites reluWrites blockWrites matrixWrites l1Writes intCommit mslCommit reluCommit
      blockCommit matrixCommit sharedFrame l1Commit, ?_⟩
  exact lm1WritesShape_of_six_sixth (intWrites ++ floatWrites) mslWrites reluWrites blockWrites
    matrixWrites l1Writes combinedFree mslFree reluFree blockFree matrixFree l1Shape

/-- **A broadcast row is not a producer of any other family** — from its
operation alone (the lowering is not needed). -/
theorem l1bmBroadcast_parsedExpr_predicates_of_kind (expression : ParsedExpr)
    (kind : parsedExprIsL1ToPEProducer expression = true) :
    parsedExprIsIntegerMatrixReadStageInput expression = false ∧
    parsedExprIsSupportedFloatMAUProducer expression = false ∧
    parsedExprIsL2BMProducer expression = false ∧
    parsedExprIsMslMsrProducer expression = false ∧
    parsedExprIsFloatReluProducer expression = false ∧
    parsedExprIsBlockFloatProducer expression = false ∧
    parsedExprIsMatrixMAUProducer expression = false ∧
    parsedExprIsMatrixWriteProducer expression = false := by
  cases expression with
  | mk op sources destinations flush text =>
      cases op <;>
        simp_all [parsedExprIsL1ToPEProducer, parsedExprIsIntegerMatrixReadStageInput,
          parsedExprIsSupportedFloatMAUProducer, parsedExprIsL2BMProducer,
          parsedExprIsMslMsrProducer, parsedExprIsFloatReluProducer,
          parsedExprIsBlockFloatProducer, parsedExprIsMatrixMAUProducer,
          parsedExprIsMatrixWriteProducer]

/-- **The `.l1bm`-writer line shape, from the multi-destination package data.** -/
theorem welcomePEWriteShape_of_l1bmWriter_dataMultiDest
    (expressions : List NormalizedExpr)
    (data : WelcomePEL1BMWriterDataForMultiDest expressions)
    (unrefuted : WelcomePEUnrefuted expressions) (e : ParsedExpr)
    (eMem : e ∈ expressions.map NormalizedExpr.toParsed)
    (l1 : parsedExprIsL1ToPEProducer e = true)
    (writer : Issue.Bank.lm1 ∈ (e.toIssueExpr 0).writeBanks) :
    WelcomePEWriteShape expressions := by
  obtain ⟨intStageFalse, floatFalse, -, mslFalse, reluFalse, blockFalse, matrixMAUFalse, -⟩ :=
    l1bmBroadcast_parsedExpr_predicates_of_kind e l1
  have rows := welcomeLm1Writer_rows expressions unrefuted e eMem writer
  exact welcomePEWriteShape_of_l1bmWriter_dispatch_multiDest expressions e
    (data e eMem l1 writer) eMem l1
    (fun expression member => rows expression (List.mem_of_mem_filter member) (by
      intro same
      subst same
      have keeps := (List.mem_filter.mp member).2
      rw [intStageFalse] at keeps
      exact absurd keeps (by simp)))
    (floatFilter_lm1Free_of_rows expressions e rows floatFalse)
    (welcomePEMiddleStageLm1Free_of_rows expressions e rows mslFalse reluFalse blockFalse)
    (welcomePEMatrixMAUStageLm1Free_of_rows expressions e rows matrixMAUFalse)

/-! ## 7. The assembly with the `.l1bm` obstruction discharged

This is `welcomePELm1WriteShapeObligation_of_plainReadL1` of
`WelcomeWriterPackages.lean` with the refutable singleton `.l1bm` component
replaced by the multi-destination package of §6 — which is now a **theorem**
(§5.5 shows the count is a consequence of `writesUnique`).  The float-MAU case
needs no hypothesis (`welcomePEWriteShape_of_floatMAUWriter`), so only the plain
and `.matrixRead` packages remain as hypotheses; the resulting
`LowerBound`/`Optimal` corollaries are therefore **conditional on those two
packages** and are not unconditional claims. -/

/-- **`WelcomePELm1WriteShapeObligation` from the plain and `.matrixRead`
packages.**  This is `welcomePELm1WriteShapeObligation_of_plainReadL1` with the
refuted `.l1bm` package removed entirely: the broadcast row's shape is §4/§5 and
the count hypothesis is a consequence of the issue checker (§5.5), so no
`.l1bm` hypothesis remains. -/
theorem welcomePELm1WriteShapeObligation_of_plainReadL1MultiDest
    (plain : WelcomePEPlainWriterDataFlagFree)
    (read : WelcomePEMatrixReadWriterDataSlotFree) :
    WelcomePELm1WriteShapeObligation := by
  intro expressions unrefuted
  by_cases hasWriter : ∃ e ∈ expressions.map NormalizedExpr.toParsed,
      Issue.Bank.lm1 ∈ (e.toIssueExpr 0).writeBanks
  · obtain ⟨e, eMem, eWriter⟩ := hasWriter
    have supported := List.all_eq_true.mp unrefuted.1.2.2.2 e eMem
    have notUnsupported : parsedExprIsUnsupportedRustAlu e = false := by
      simpa using (List.any_eq_false.mp unrefuted.1.2.2.1) e eMem
    rcases supportedProducer_partition e supported with
      isPlain | isFamily | isSpecial | isInert | isUnsupported
    · exact welcomePEWriteShape_of_plainWriter_data_flagFree expressions
        (plain expressions unrefuted) unrefuted e eMem isPlain eWriter
    · rcases parsedExprIsFamilyProducer_cases e isFamily with
        readKind | mauKind | floatKind | writeKind | toPEKind | l2Kind
      · exact welcomePEWriteShape_of_matrixReadWriter_data_slotFree expressions
          (read expressions unrefuted) unrefuted e eMem readKind eWriter
      · exact welcomePEWriteShape_of_matrixMAUWriter expressions unrefuted e eMem mauKind eWriter
      · exact welcomePEWriteShape_of_floatMAUWriter expressions unrefuted e eMem floatKind eWriter
      · have hphantom : ∀ x ∈ expressions.map NormalizedExpr.toParsed,
            Issue.Bank.lm1 ∈ (x.toIssueExpr 0).writeBanks → welcomePhantomWriterKind x := by
          intro x xMem xWriter
          have same : x = e :=
            welcomeLm1Writer_eq_of_two expressions unrefuted xMem eMem xWriter eWriter
          rw [same]
          exact Or.inr (Or.inr (Or.inr (Or.inl writeKind)))
        exact welcomePEWriteShape_of_freeStageCommit expressions
          (welcomePELm1PhantomWriterProvenance expressions unrefuted hphantom)
      · exact welcomePEWriteShape_of_l1bmWriter_dataMultiDest expressions
          (welcomePEL1BMWriterDataForMultiDest_holds expressions unrefuted)
          unrefuted e eMem toPEKind eWriter
      · have hphantom : ∀ x ∈ expressions.map NormalizedExpr.toParsed,
            Issue.Bank.lm1 ∈ (x.toIssueExpr 0).writeBanks → welcomePhantomWriterKind x := by
          intro x xMem xWriter
          have same : x = e :=
            welcomeLm1Writer_eq_of_two expressions unrefuted xMem eMem xWriter eWriter
          rw [same]
          exact Or.inr (Or.inr (Or.inr (Or.inr l2Kind)))
        exact welcomePEWriteShape_of_freeStageCommit expressions
          (welcomePELm1PhantomWriterProvenance expressions unrefuted hphantom)
    · exact welcomePESpecialALUWriterShapeObligation expressions unrefuted
        ⟨e, eMem, eWriter, isSpecial⟩
    · have hphantom : ∀ x ∈ expressions.map NormalizedExpr.toParsed,
          Issue.Bank.lm1 ∈ (x.toIssueExpr 0).writeBanks → welcomePhantomWriterKind x := by
        intro x xMem xWriter
        have same : x = e :=
          welcomeLm1Writer_eq_of_two expressions unrefuted xMem eMem xWriter eWriter
        rw [same]
        rcases parsedExprIsPEInertProducer_cases e isInert with forward | wait | shared
        · exact Or.inl forward
        · exact Or.inr (Or.inl wait)
        · exact Or.inr (Or.inr (Or.inl shared))
      exact welcomePEWriteShape_of_freeStageCommit expressions
        (welcomePELm1PhantomWriterProvenance expressions unrefuted hphantom)
    · rw [notUnsupported] at isUnsupported
      cases isUnsupported
  · have hphantom : ∀ x ∈ expressions.map NormalizedExpr.toParsed,
        Issue.Bank.lm1 ∈ (x.toIssueExpr 0).writeBanks → welcomePhantomWriterKind x := by
      intro x xMem xWriter
      exact absurd ⟨x, xMem, xWriter⟩ hasWriter
    exact welcomePEWriteShape_of_freeStageCommit expressions
      (welcomePELm1PhantomWriterProvenance expressions unrefuted hphantom)

/-- **The conservative direction of the assembly.**  The multi-destination
package is implied by the singleton one (§6), and is in fact a theorem, so the
new assembly subsumes `welcomePELm1WriteShapeObligation_of_plainReadL1`: on every
line the old package covered, the old theorem's conclusion is recovered.  The
singleton hypothesis is kept only to record the implication. -/
theorem welcomePELm1WriteShapeObligation_of_plainReadL1_of_singleton
    (plain : WelcomePEPlainWriterDataFlagFree)
    (read : WelcomePEMatrixReadWriterDataSlotFree)
    (l1 : WelcomePEL1BMWriterDataNoSingleton) :
    WelcomePELm1WriteShapeObligation :=
  welcomePELm1WriteShapeObligation_of_plainReadL1MultiDest plain read

/-- **The residual bundle of the multi-destination assembly.**  Only the plain
and `.matrixRead` packages remain: the `.l1bm` component is a theorem (§5.5, §6),
not a hypothesis.  Unlike `WelcomePEWriterKindDataResidualsThree` this bundle has
no refuted component. -/
def WelcomePEWriterKindDataResidualsMultiDest : Prop :=
  WelcomePEPlainWriterDataFlagFree ∧ WelcomePEMatrixReadWriterDataSlotFree

/-- **The residual bundle form** of
`welcomePELm1WriteShapeObligation_of_plainReadL1MultiDest`. -/
theorem welcomePELm1WriteShapeObligation_of_residualsMultiDest
    (residuals : WelcomePEWriterKindDataResidualsMultiDest) :
    WelcomePELm1WriteShapeObligation := by
  obtain ⟨plain, read⟩ := residuals
  exact welcomePELm1WriteShapeObligation_of_plainReadL1MultiDest plain read

/-- **The old three-package bundle implies the multi-destination bundle.** -/
theorem welcomePEWriterKindDataResidualsMultiDest_of_residualsThree
    (residuals : WelcomePEWriterKindDataResidualsThree) :
    WelcomePEWriterKindDataResidualsMultiDest :=
  ⟨residuals.1, residuals.2.1⟩

/-- **`LowerBound welcomeSealedMachine welcomeSpec 2` from the plain and
`.matrixRead` packages** (conditional; this is a reduction of the remaining
plain/`.matrixRead` obligations, not an unconditional lower bound).  The
`.l1bm` obstruction of rounds 49-50 is discharged. -/
theorem welcomeLowerBound_two_of_plainReadL1MultiDest
    (plain : WelcomePEPlainWriterDataFlagFree)
    (read : WelcomePEMatrixReadWriterDataSlotFree) :
    ProofsLean.LowerBound welcomeSealedMachine welcomeSpec 2 :=
  welcomeLowerBound_two_of_lm1WriteShapes
    (welcomePELm1WriteShapeObligation_of_plainReadL1MultiDest plain read)

/-- **`Optimal welcomeSealedMachine welcomeSpec welcomeAnswer` from the plain and
`.matrixRead` packages** (conditional; not an unconditional optimality claim). -/
theorem welcomeAnswer_optimal_of_plainReadL1MultiDest
    (plain : WelcomePEPlainWriterDataFlagFree)
    (read : WelcomePEMatrixReadWriterDataSlotFree) :
    ProofsLean.Optimal welcomeSealedMachine welcomeSpec welcomeAnswer :=
  welcomeAnswer_optimal_of_lm1WriteShapes
    (welcomePELm1WriteShapeObligation_of_plainReadL1MultiDest plain read)

/-! ## 8. The refuted witness satisfies the new package

`l1ToPETwoDestination_weakPackage_false` and `l1ToPETwoDestination_noSingleShape`
show that the accepted, unrefuted two-destination broadcast writer is outside
both the round-49 package and its weakened single-destination form.  That row is
inside the multi-destination package: its `.lm1` filter has length one.  Hence
the generalisation of §6 is not vacuous on the very line the old packages lost. -/

/-- The two-destination witness lowers successfully. -/
theorem l1ToPETwoDestination_lowering :
    ∃ access : ParsedL1ToPEAccess,
      lowerParsedL1ToPE? l1ToPETwoDestinationWitnessParsed = some access :=
  ⟨_, rfl⟩

/-- **The two-destination witness satisfies the multi-destination package.** -/
theorem welcomePEL1BMWriterDataForMultiDest_witness :
    WelcomePEL1BMWriterDataForMultiDest [l1ToPETwoDestinationWitness] := by
  intro e eMem _ _
  have same : e = l1ToPETwoDestinationWitnessParsed := by
    simpa [l1ToPETwoDestinationWitnessParsed] using eMem
  subst same
  simp [l1ToPETwoDestinationWitnessParsed, l1ToPETwoDestinationWitness,
    NormalizedExpr.toParsed, ParsedOperand.isLm1MemoryDestination, Issue.plusOneAccess]

/-- **The multi-destination package is strictly weaker than the refuted
single-destination one on the witness line**: the two-destination broadcast
writer satisfies the former and not the latter. -/
theorem welcomePEL1BMWriterDataForMultiDest_witness_strict :
    WelcomePEL1BMWriterDataForMultiDest [l1ToPETwoDestinationWitness] ∧
      ¬ WelcomePEL1BMWriterDataForNoSingleton [l1ToPETwoDestinationWitness] :=
  ⟨welcomePEL1BMWriterDataForMultiDest_witness, l1ToPETwoDestination_noSingleShape⟩

/-! ## 9. Why the package must not require the writer's lowering

The natural-looking strengthening of the package — also ask for the lowering
`lowerParsedL1ToPE? e = some access` — is **false** on an accepted unrefuted
line.  The witness below is a `.pbcast` row (so `parsedExprIsL1ToPEProducer` is
true) with a memory *source* and an `.lm1` memory destination: it writes `.lm1`
and is the line's writer, but `lowerParsedL1ToPE?` is `none` because the
broadcast lowering requires a `[.l1bm width address]` source.  The executor then
fails the L1BM-to-PE stage, so the line's step fails and its write shape is
vacuous — which is exactly why §6's package states the count on the parsed
destination list and leaves the lowering to the dispatch. -/

/-- A `.pbcast` row with a memory source: a syntactic L1ToPE producer that does
not lower. -/
def l1ToPEMemorySourceWitness : NormalizedExpr where
  op := .l1bm .pbcast
  sources := [.mem (plusOneAccess .lm0 0) false false false none]
  destinations := [.mem (plusOneAccess .lm1 0) false false false none]
  flush := none

/-- The memory-source witness's parsed view. -/
def l1ToPEMemorySourceWitnessParsed : ParsedExpr := l1ToPEMemorySourceWitness.toParsed

/-- **The memory-source witness is issue-legal.** -/
theorem l1ToPEMemorySource_line_legal :
    LegalParsedLine [l1ToPEMemorySourceWitnessParsed] := by
  unfold LegalParsedLine projectLine projectFrom ParsedExpr.toIssueExpr
    ParsedExpr.issueGroup ParsedExpr.issueMau ParsedOperand.accesses
    ParsedOperand.matrixUseCount ParsedExpr.hasTurnaround
    ParsedExpr.maskApplications ParsedOperand.writeMask?
    ParsedExpr.maskRegisterWrites ParsedOperand.maskRegisterWrite?
    ParsedExpr.barWrites ParsedOperand.barWriteBank?
    ParsedExpr.writesLbf ParsedExpr.nowriteOutputValid
  simp [l1ToPEMemorySourceWitnessParsed, l1ToPEMemorySourceWitness, Legal, idsUnique,
    groupsUnique, mauCountBounded, mauExpressions, mauPrecisionsAgree, matrixWritePairAgrees,
    matrixRegistersUnique, writesUnique, Expr.writeBanks, barWritesExcludeReads, readsAgree,
    localReadWriteAgree, immediateExcludesLm0, zeroFlushUnique, maskWidthsAgree,
    maskEntriesAgree, nowriteOutputsUnique, lbfWritesUnique, maskRegisterWritesUnique,
    projectFrom, Issue.plusOneAccess, NormalizedExpr.toParsed, ParsedExpr.toIssueExpr,
    ParsedExpr.maskApplications, ParsedExpr.maskRegisterWrites, ParsedExpr.barWrites,
    ParsedExpr.writesLbf, ParsedExpr.nowriteOutputValid, ParsedExpr.issueGroup,
    ParsedExpr.issueMau, ParsedExpr.hasTurnaround, ParsedOperand.matrixUseCount,
    ParsedOperand.accesses, ParsedOperand.barWriteBank?, ParsedOperand.writeMask?,
    ParsedOperand.maskRegisterWrite?, Expr.writeBanks, mauExpressions,
    List.any_cons, List.any_nil, List.filter_cons, List.filter_nil,
    List.filterMap_cons, List.filterMap_nil, Bool.true_and, Bool.false_and]

/-- The memory-source witness is a syntactic L1ToPE producer. -/
theorem l1ToPEMemorySource_l1Kind :
    parsedExprIsL1ToPEProducer l1ToPEMemorySourceWitnessParsed = true := by
  decide

/-- The memory-source witness is the line's `.lm1` writer. -/
theorem l1ToPEMemorySource_writer :
    Issue.Bank.lm1 ∈ (l1ToPEMemorySourceWitnessParsed.toIssueExpr 0).writeBanks := by
  simp [l1ToPEMemorySourceWitnessParsed, NormalizedExpr.toParsed,
    l1ToPEMemorySourceWitness, ParsedExpr.toIssueExpr, Expr.writeBanks,
    ParsedOperand.accesses, ParsedExpr.barWrites, ParsedOperand.barWriteBank?,
    Issue.plusOneAccess]

/-- **The memory-source witness does not lower.** -/
theorem l1ToPEMemorySource_lowering :
    lowerParsedL1ToPE? l1ToPEMemorySourceWitnessParsed = none := rfl

/-- The strengthening of the package that also asks for the lowering. -/
def WelcomePEL1BMWriterDataForMultiDestWithLowering
    (expressions : List NormalizedExpr) : Prop :=
  ∀ (e : ParsedExpr),
    e ∈ expressions.map NormalizedExpr.toParsed →
      parsedExprIsL1ToPEProducer e = true →
      Issue.Bank.lm1 ∈ (e.toIssueExpr 0).writeBanks →
      ∃ (access : ParsedL1ToPEAccess),
        lowerParsedL1ToPE? e = some access ∧
          (access.destinations.filter ParsedOperand.isLm1MemoryDestination).length ≤ 1

/-- **Requiring the lowering makes the package false.**  The memory-source
witness is an accepted, `.lm1`-writing L1ToPE producer with no lowering. -/
theorem l1ToPEMemorySource_withLowering_false :
    ¬ WelcomePEL1BMWriterDataForMultiDestWithLowering [l1ToPEMemorySourceWitness] := by
  intro data
  obtain ⟨access, lowered, _⟩ := data l1ToPEMemorySourceWitnessParsed
    (by simp [l1ToPEMemorySourceWitnessParsed, NormalizedExpr.toParsed,
      l1ToPEMemorySourceWitness])
    l1ToPEMemorySource_l1Kind l1ToPEMemorySource_writer
  rw [l1ToPEMemorySource_lowering] at lowered
  simp at lowered

end ProofsLean.MNCore
