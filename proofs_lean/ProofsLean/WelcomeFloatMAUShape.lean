import ProofsLean.WelcomeStageCommit

/-! # The float-MAU row shape at the all-zero state

`WelcomeStageCommit.lean` proves that a float-MAU row
(`executeParsedFloatMAUsAtPE`) *commits* a prepared write list on the PE 0
register file it was given.  This module proves the **shape** of that list at
the all-zero initial state, in the form consumed by the line-level assembly of
`WelcomeMAUShape.lean`: the `.lm1` part is either a set of copied `.double`
blocks (`Lm1WritesDoubleCopy`) or fits in four narrow windows
(`Lm1WritesNarrow`).

## What is proved

* **Destination layer (unconditional).**  The shared per-destination writer
  `writeParsedMslMsrDestination?` emits at most one prepared write, and only for
  a `.mem` destination
  (`writeParsedMslMsrDestination?_mem_shape`,
  `writeParsedMslMsrDestination?_widthCount`,
  `writeParsedMslMsrDestination?_copyFacts`).  That write's bank/width is the
  *static* `directDestinationBankWidth?` of the operand
  (`ParsedOperand.toDirectMemoryDestination?_bankWidth`), and its address is
  4-aligned for a `.double` width
  (`parsedOperand_toDirectMemoryAccessMode_aligned`).  Hence every `.lm1` write
  of a row has the row's static width, and there is at most one `.lm1` write per
  cycle (`lm1Destinations_count_le_one`).

* **Loop layer (unconditional for width and count).**  The destination loop
  (`writeParsedMAUDestinations?_writeAll_widthCount`) and the four-cycle loop
  (`executeParsedFloatMAUCyclesAtPE_widthCount`) carry the static width and the
  count bound `≤ cycles.length`.  The copy facts are carried separately
  (`..._writeAll_copy`, `..._shape`) so that the narrow half stays
  datapath-free.

* **Narrow half (unconditional).**  `executeParsedFloatMAUsAtPE_zeroNarrow`: if
  the row's static `.lm1` width is not `.double`, the prepared write list is a
  commit and satisfies `Lm1WritesNarrow` — with no datapath hypothesis at all.

* **The copy/datapath half.**  The only remaining datapath fact is
  `WelcomePEFloatMAUCycleCopy`: a successful float-MAU cycle at the all-zero
  register file (every forwarding slot still poison) has a copied third data
  word.  It is reduced by a complete case analysis over the cycle's op dispatch
  to `WelcomePEFloatMAUHalfCycleCopy`, the same statement for the four `.h`
  (half-precision) branches (`welcomePEFloatMAUCycleCopy_of_half`): every `.f`
  and `.d` branch, and the legacy float-memory fallback, returns a bus whose low
  half is literally `0` (`doubleMAUVectorBus_low`), so the third data word is
  `0`; only the `.h` branches compute the low half from the source lanes.

* **Row shape.**  `executeParsedFloatMAUsAtPE_zeroShape` (and
  `..._of_half`, with the hypothesis in its reduced half-precision form): the
  prepared write list of one float-MAU row at the all-zero state is a commit and
  is either `Lm1WritesDoubleCopy` or `Lm1WritesNarrow`.

## Remainder

The precise remaining hypothesis is `WelcomePEFloatMAUHalfCycleCopy` — the four
`.h` (`mau .h ...`) branches of `executeParsedFloatMAUCycleAtPE`.  Their source
buses can only come from `parsedFloatMAUSourceAttrs?` (which accepts only `.mem`
and `.forward` operands), so at the all-zero state they read `⟨0,0⟩` and the
half computations (`prepareHalfMultiplyBus`, `prepareHalfFmaBus`,
`prepareHalfPassa`) return a copied word; making that formal needs the
source-shape inversion of `lowerParsedHalfMultiply?`,
`lowerParsedHalfAdd?`, `lowerParsedHalfFma?` and `lowerParsedHalfPassa?`.

No `sorry`, no `admit`, no `native_decide`, no new axioms, and no existing
module is edited by this file.
-/

namespace ProofsLean.MNCore

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

open Issue
open PEMemory

/-! ## 1. `Lm1WriteFacts` split into a width half and a copy half -/

/-- Every `.lm1` destination of the list is a `w`-wide write and its `.double`
case is 4-aligned. -/
def Lm1WidthFacts (w : PEMemory.Width) (writes : List PreparedParsedMaskedWrite) : Prop :=
  ∀ write ∈ writes, ∀ (width : PEMemory.Width) (address : Fin PEMemory.Bank.lm1.capacity),
    write.destination = some ⟨PEMemory.Bank.lm1, width, address⟩ →
      width = w ∧ (width = PEMemory.Width.double → address.val % 4 = 0)

/-- Every `.lm1` destination of the list has a copied third data word. -/
def Lm1CopyFacts (writes : List PreparedParsedMaskedWrite) : Prop :=
  ∀ write ∈ writes, ∀ (width : PEMemory.Width) (address : Fin PEMemory.Bank.lm1.capacity),
    write.destination = some ⟨PEMemory.Bank.lm1, width, address⟩ →
      ∀ bound : 2 < 4, IsWelcomeCopy (write.data ⟨2, bound⟩)

theorem lm1WriteFacts_of_parts (w : PEMemory.Width) (writes : List PreparedParsedMaskedWrite)
    (widths : Lm1WidthFacts w writes) (copies : Lm1CopyFacts writes) :
    Lm1WriteFacts w writes := by
  intro write member width address destination
  obtain ⟨widthEq, aligned⟩ := widths write member width address destination
  exact ⟨widthEq, aligned, copies write member width address destination⟩

theorem lm1WidthFacts_nil (w : PEMemory.Width) : Lm1WidthFacts w [] := by
  intro write member
  simp at member

theorem lm1CopyFacts_nil : Lm1CopyFacts [] := by
  intro write member
  simp at member

theorem lm1WidthFacts_append (w : PEMemory.Width) (a b : List PreparedParsedMaskedWrite)
    (ha : Lm1WidthFacts w a) (hb : Lm1WidthFacts w b) : Lm1WidthFacts w (a ++ b) := by
  intro write member width address destination
  rcases List.mem_append.mp member with earlier | later
  · exact ha write earlier width address destination
  · exact hb write later width address destination

theorem lm1CopyFacts_append (a b : List PreparedParsedMaskedWrite)
    (ha : Lm1CopyFacts a) (hb : Lm1CopyFacts b) : Lm1CopyFacts (a ++ b) := by
  intro write member width address destination
  rcases List.mem_append.mp member with earlier | later
  · exact ha write earlier width address destination
  · exact hb write later width address destination

/-! ## 2. The prepared write of a `.mem` destination -/

/-- **A `.mem` destination's prepared write.**  The single-destination writer,
applied to a `.mem` operand, emits exactly the one-element list whose access is
the resolved direct-memory destination and whose data is the unpacked bus. -/
theorem writeParsedMslMsrDestination?_mem_shape
    (files : IntegerRegisterFiles) (access : Access) (negated extended rounded : Bool)
    (mask : Option ParsedMask) (context : ParsedIntegerContext) (output : IntegerALU.Bus)
    (flags : BitVec 4) (cycle : Fin 4) (directive : ParsedMaskDirective)
    (hasSingleLineMask : Bool) (write : ParsedMslMsrDestinationWrite)
    (lowered : writeParsedMslMsrDestination? files
      (ParsedOperand.mem access negated extended rounded mask) context output flags cycle
      directive hasSingleLineMask = some write) :
    ∃ (resolved : DirectMemoryAccess) (selection : PEWordSelection),
      ParsedOperand.toDirectMemoryDestination?
        (ParsedOperand.mem access negated extended rounded mask) context.pe cycle
        context.bar0 context.bar1 context.tWord = some resolved ∧
      commitParsedMaskedWrites files
        [⟨some resolved, none, PEMemory.unpackALUBus output, selection⟩] = write.files := by
  simp only [writeParsedMslMsrDestination?] at lowered
  cases h : ParsedOperand.toDirectMemoryDestination?
      (ParsedOperand.mem access negated extended rounded mask) context.pe cycle
      context.bar0 context.bar1 context.tWord with
  | none => simp [h] at lowered
  | some resolved =>
      cases h2 : ParsedOperand.resolveMemoryWriteSelection?
          (ParsedOperand.mem access negated extended rounded mask) resolved.bank
          files.maskRegisters cycle directive hasSingleLineMask with
      | none => simp [h, h2] at lowered
      | some selection =>
          simp [h, h2] at lowered
          refine ⟨resolved, selection, rfl, ?_⟩
          rw [← lowered]; simp [commitParsedMaskedWrites]

/-- **The static width and alignment of a resolved direct destination.** -/
theorem directDestination_static_width
    (destination : ParsedOperand) (pe cycle : Fin 4) (bar0 bar1 : BitVec 12)
    (tWord : BitVec 32) (resolved : DirectMemoryAccess)
    (resolvedEq : ParsedOperand.toDirectMemoryDestination? destination pe cycle bar0 bar1 tWord =
      some resolved)
    (w : PEMemory.Width)
    (staticWidth : ∀ v : PEMemory.Width,
      ParsedOperand.directDestinationBankWidth? destination = some (PEMemory.Bank.lm1, v) → v = w)
    (bank : resolved.bank = PEMemory.Bank.lm1) :
    resolved.width = w ∧ (resolved.width = PEMemory.Width.double →
      resolved.address.val % 4 = 0) := by
  have staticEq := ParsedOperand.toDirectMemoryDestination?_bankWidth destination pe cycle
    bar0 bar1 tWord
  rw [resolvedEq] at staticEq
  simp only [Option.map_some, bank] at staticEq
  refine ⟨staticWidth resolved.width ?_, ?_⟩
  · rw [staticEq]
  · intro isDouble
    have aligned := parsedOperand_toDirectMemoryAccessMode_aligned destination true pe cycle
      bar0 bar1 tWord resolved resolvedEq
    rw [isDouble] at aligned
    simpa [PEMemory.Width.words] using aligned

/-! ## 3. One destination of the float-MAU writer -/

/-- **The prepared-write facts of one destination.**  At most one prepared write
is emitted, it is `.lm1`-shaped only for a `.mem` destination whose static bank
is `.lm1` (so the width is the static width, the address is aligned, and the
third data word is a copy), and at most one `.lm1` write is emitted. -/
theorem floatMAU_writeParsedMslMsrDestination_facts
    (files : IntegerRegisterFiles) (destination : ParsedOperand)
    (context : ParsedIntegerContext) (output : IntegerALU.Bus) (flags : BitVec 4)
    (cycle : Fin 4) (directive : ParsedMaskDirective) (hasSingleLineMask : Bool)
    (write : ParsedMslMsrDestinationWrite) (w : PEMemory.Width)
    (lowered : writeParsedMslMsrDestination? files destination context output flags cycle
      directive hasSingleLineMask = some write)
    (staticWidth : ∀ v : PEMemory.Width,
      ParsedOperand.directDestinationBankWidth? destination = some (PEMemory.Bank.lm1, v) → v = w)
    (copies : ∀ bound : 2 < 4, IsWelcomeCopy ((unpackALUBus output) ⟨2, bound⟩))
    (countOk : ∀ (bank : PEMemory.Bank) (width : PEMemory.Width),
      ParsedOperand.directDestinationBankWidth? destination = some (bank, width) →
        bank = PEMemory.Bank.lm1 → ParsedOperand.isLm1MemoryDestination destination = true) :
    ∃ headWrites, write.files = commitParsedMaskedWrites files headWrites ∧
      Lm1WidthFacts w headWrites ∧ Lm1CopyFacts headWrites ∧
      (headWrites.filter PreparedParsedMaskedWrite.isLm1Write).length ≤
        (if ParsedOperand.isLm1MemoryDestination destination then 1 else 0) := by
  cases destination with
  | mem access negated extended rounded mask =>
      obtain ⟨resolved, selection, resolvedEq, commitEq⟩ :=
        writeParsedMslMsrDestination?_mem_shape files access negated extended rounded mask
          context output flags cycle directive hasSingleLineMask write lowered
      refine ⟨[⟨some resolved, none, PEMemory.unpackALUBus output, selection⟩], commitEq.symm,
        ?_, ?_, ?_⟩
      · intro write' member width address destinationEq
        simp only [List.mem_singleton] at member
        subst member
        simp only [Option.some.injEq] at destinationEq
        subst destinationEq
        have facts := directDestination_static_width
          (ParsedOperand.mem access negated extended rounded mask) context.pe cycle
          context.bar0 context.bar1 context.tWord
          ⟨PEMemory.Bank.lm1, width, address⟩ resolvedEq w staticWidth rfl
        exact facts
      · intro write' member width address destinationEq bound
        simp only [List.mem_singleton] at member
        subst member
        exact copies bound
      · by_cases bank : resolved.bank = PEMemory.Bank.lm1
        · have isLm1 : ParsedOperand.isLm1MemoryDestination
              (ParsedOperand.mem access negated extended rounded mask) = true := by
            apply countOk resolved.bank resolved.width _ bank
            have staticEq := ParsedOperand.toDirectMemoryDestination?_bankWidth
              (ParsedOperand.mem access negated extended rounded mask) context.pe cycle
              context.bar0 context.bar1 context.tWord
            rw [resolvedEq] at staticEq
            simpa [bank] using staticEq.symm
          have yes : (resolved.bank == PEMemory.Bank.lm1) = true := by
            simpa [beq_iff_eq] using bank
          simp [PreparedParsedMaskedWrite.isLm1Write, yes, isLm1]
        · have notEq : (resolved.bank == PEMemory.Bank.lm1) = false := by
            simpa using bank
          simp [PreparedParsedMaskedWrite.isLm1Write, notEq]
  | omr entry mask =>
      simp only [writeParsedMslMsrDestination?] at lowered
      cases h : ParsedOperand.toMaskRegisterEntry? (ParsedOperand.omr entry mask) with
      | none => simp [h] at lowered
      | some found =>
          cases h2 : ParsedOperand.resolveOmrWriteSelection? (ParsedOperand.omr entry mask)
              files.maskRegisters cycle directive hasSingleLineMask with
          | none => simp [h, h2] at lowered
          | some selection =>
              simp [h, h2] at lowered
              refine ⟨[⟨none, some (found, cycle, flags), PEMemory.unpackALUBus output,
                ⟨selection, false⟩⟩], ?_, ?_, ?_, ?_⟩
              · rw [← lowered]
                simp [commitParsedMaskedWrites]
              · intro write' member width address destinationEq
                simp only [List.mem_singleton] at member
                subst member
                simp at destinationEq
              · intro write' member width address destinationEq bound
                simp only [List.mem_singleton] at member
                subst member
                simp at destinationEq
              · simp [ParsedOperand.isLm1MemoryDestination,
                  PreparedParsedMaskedWrite.isLm1Write]
  | bar lm1 width mask =>
      refine ⟨[], ?_, lm1WidthFacts_nil w, lm1CopyFacts_nil, ?_⟩
      · simp only [writeParsedMslMsrDestination?] at lowered
        cases h : ParsedOperand.resolveMemoryWriteSelection? (ParsedOperand.bar lm1 width mask)
            (if lm1 = true then PEMemory.Bank.lm1 else PEMemory.Bank.lm0) files.maskRegisters
            cycle directive hasSingleLineMask with
        | none => simp [h] at lowered
        | some selection =>
            simp [h] at lowered
            rw [← lowered]
            simp [commitParsedMaskedWrites]
      · simp [ParsedOperand.isLm1MemoryDestination]
  | nowrite =>
      refine ⟨[], ?_, lm1WidthFacts_nil w, lm1CopyFacts_nil, ?_⟩
      · simp only [writeParsedMslMsrDestination?] at lowered
        rw [← Option.some.inj lowered]
        simp [commitParsedMaskedWrites]
      · simp [ParsedOperand.isLm1MemoryDestination]
  | forward kind negated extended rounded => simp [writeParsedMslMsrDestination?] at lowered
  | fixed kind => simp [writeParsedMslMsrDestination?] at lowered
  | matrix side width row => simp [writeParsedMslMsrDestination?] at lowered
  | l1bm width address => simp [writeParsedMslMsrDestination?] at lowered
  | l2bm address l2b => simp [writeParsedMslMsrDestination?] at lowered
  | dar address => simp [writeParsedMslMsrDestination?] at lowered

/-! ## 4. The destination loop of one cycle -/

theorem filter_length_cons_add {α : Type} (p : α → Bool) (a : α) (l : List α) :
    (List.filter p (a :: l)).length = (if p a then 1 else 0) + (List.filter p l).length := by
  rw [List.filter_cons]
  split
  · simp only [List.length_cons]
    omega
  · simp

/-- Every destination with static `.lm1` bank has static width `w`. -/
def Lm1DestWidths (w : PEMemory.Width) (destinations : List ParsedOperand) : Prop :=
  ∀ d ∈ destinations, ∀ v : PEMemory.Width,
    ParsedOperand.directDestinationBankWidth? d = some (PEMemory.Bank.lm1, v) → v = w

/-- A destination whose static bank is `.lm1` is an `.lm1` memory destination. -/
def Lm1DestCount (destinations : List ParsedOperand) : Prop :=
  ∀ d ∈ destinations, ∀ (bank : PEMemory.Bank) (width : PEMemory.Width),
    ParsedOperand.directDestinationBankWidth? d = some (bank, width) →
      bank = PEMemory.Bank.lm1 → ParsedOperand.isLm1MemoryDestination d = true

/-- **The destination loop of the float-MAU writer is a shaped commit.** -/
theorem writeParsedMAUDestinations?_writeAll_shape
    (context : ParsedIntegerContext) (output : IntegerALU.Bus) (flags : BitVec 4)
    (cycle : Fin 4) (directive : ParsedMaskDirective) (hasSingleLineMask : Bool)
    (w : PEMemory.Width)
    (copies : ∀ bound : 2 < 4, IsWelcomeCopy ((unpackALUBus output) ⟨2, bound⟩)) :
    ∀ (destinations : List ParsedOperand) (files : IntegerRegisterFiles) (bar0 bar1 : BitVec 12)
      (next : ParsedMAUDestinationWrites),
      Lm1DestWidths w destinations →
      Lm1DestCount destinations →
      writeParsedMAUDestinations?.writeAll context output flags cycle directive hasSingleLineMask
        destinations files bar0 bar1 = some next →
      ∃ writes, next.files = commitParsedMaskedWrites files writes ∧
        Lm1WidthFacts w writes ∧ Lm1CopyFacts writes ∧
        (writes.filter PreparedParsedMaskedWrite.isLm1Write).length ≤
          (destinations.filter ParsedOperand.isLm1MemoryDestination).length := by
  intro destinations
  induction destinations with
  | nil =>
      intro files bar0 bar1 next widths count executed
      rw [writeParsedMAUDestinations?.writeAll] at executed
      obtain rfl := Option.some.inj executed
      exact ⟨[], rfl, lm1WidthFacts_nil w, lm1CopyFacts_nil, by simp⟩
  | cons destination rest ih =>
      intro files bar0 bar1 next widths count executed
      rw [writeParsedMAUDestinations?.writeAll] at executed
      dsimp only at executed
      cases lowered : writeParsedMslMsrDestination? files destination
          { context with bar0 := bar0, bar1 := bar1 } output flags cycle directive
          hasSingleLineMask with
      | none =>
          rw [lowered] at executed
          simp at executed
      | some write =>
          rw [lowered] at executed
          obtain ⟨headWrites, headCommit, headWidth, headCopy, headCount⟩ :=
            floatMAU_writeParsedMslMsrDestination_facts files destination
              { context with bar0 := bar0, bar1 := bar1 } output flags cycle directive
              hasSingleLineMask write w lowered
              (fun v hv => widths destination (by simp) v hv) copies
              (fun bank width hv bankEq => count destination (by simp) bank width hv bankEq)
          obtain ⟨tailWrites, tailCommit, tailWidth, tailCopy, tailCount⟩ :=
            ih write.files
              (match write.barUpdate with
                | some (false, value) => value
                | _ => bar0)
              (match write.barUpdate with
                | some (true, value) => value
                | _ => bar1)
              next
              (fun d mem => widths d (List.mem_cons_of_mem _ mem))
              (fun d mem => count d (List.mem_cons_of_mem _ mem))
              executed
          refine ⟨headWrites ++ tailWrites, ?_, ?_, ?_, ?_⟩
          · rw [tailCommit, headCommit, commitParsedMaskedWrites_append]
          · exact lm1WidthFacts_append w headWrites tailWrites headWidth tailWidth
          · exact lm1CopyFacts_append headWrites tailWrites headCopy tailCopy
          · rw [List.filter_append, List.length_append]
            have h1 := headCount
            have h2 := tailCount
            rw [filter_length_cons_add]
            omega

/-- **The float-MAU destination writer is a shaped commit.** -/
theorem writeParsedMAUDestinations?_shape
    (files : IntegerRegisterFiles) (destinations : List ParsedOperand)
    (context : ParsedIntegerContext) (output : IntegerALU.Bus) (flags : BitVec 4)
    (cycle : Fin 4) (directive : ParsedMaskDirective) (hasSingleLineMask : Bool)
    (w : PEMemory.Width)
    (copies : ∀ bound : 2 < 4, IsWelcomeCopy ((unpackALUBus output) ⟨2, bound⟩))
    (widths : Lm1DestWidths w destinations) (count : Lm1DestCount destinations)
    (next : ParsedMAUDestinationWrites)
    (executed : writeParsedMAUDestinations? files destinations context output flags cycle
      directive hasSingleLineMask = some next) :
    ∃ writes, next.files = commitParsedMaskedWrites files writes ∧
      Lm1WidthFacts w writes ∧ Lm1CopyFacts writes ∧
      (writes.filter PreparedParsedMaskedWrite.isLm1Write).length ≤
        (destinations.filter ParsedOperand.isLm1MemoryDestination).length := by
  rw [writeParsedMAUDestinations?.eq_1] at executed
  exact writeParsedMAUDestinations?_writeAll_shape context output flags cycle directive
    hasSingleLineMask w copies destinations files context.bar0 context.bar1 next widths count
    executed

/-! ## 5. The copy-free destination facts

The narrow half of the row shape needs only the static width and the count
bound; neither depends on the datapath.  The copy half is carried separately so
that `Lm1WritesNarrow` stays unconditional. -/

/-- **The static-width facts of one destination, without any datapath input.** -/
theorem writeParsedMslMsrDestination?_widthCount
    (files : IntegerRegisterFiles) (destination : ParsedOperand)
    (context : ParsedIntegerContext) (output : IntegerALU.Bus) (flags : BitVec 4)
    (cycle : Fin 4) (directive : ParsedMaskDirective) (hasSingleLineMask : Bool)
    (write : ParsedMslMsrDestinationWrite) (w : PEMemory.Width)
    (lowered : writeParsedMslMsrDestination? files destination context output flags cycle
      directive hasSingleLineMask = some write)
    (staticWidth : ∀ v : PEMemory.Width,
      ParsedOperand.directDestinationBankWidth? destination = some (PEMemory.Bank.lm1, v) → v = w)
    (countOk : ∀ (bank : PEMemory.Bank) (width : PEMemory.Width),
      ParsedOperand.directDestinationBankWidth? destination = some (bank, width) →
        bank = PEMemory.Bank.lm1 → ParsedOperand.isLm1MemoryDestination destination = true) :
    ∃ headWrites, write.files = commitParsedMaskedWrites files headWrites ∧
      Lm1WidthFacts w headWrites ∧
      (headWrites.filter PreparedParsedMaskedWrite.isLm1Write).length ≤
        (if ParsedOperand.isLm1MemoryDestination destination then 1 else 0) := by
  cases destination with
  | mem access negated extended rounded mask =>
      obtain ⟨resolved, selection, resolvedEq, commitEq⟩ :=
        writeParsedMslMsrDestination?_mem_shape files access negated extended rounded mask
          context output flags cycle directive hasSingleLineMask write lowered
      refine ⟨[⟨some resolved, none, PEMemory.unpackALUBus output, selection⟩], commitEq.symm,
        ?_, ?_⟩
      · intro write' member width address destinationEq
        simp only [List.mem_singleton] at member
        subst member
        simp only [Option.some.injEq] at destinationEq
        subst destinationEq
        exact directDestination_static_width
          (ParsedOperand.mem access negated extended rounded mask) context.pe cycle
          context.bar0 context.bar1 context.tWord
          ⟨PEMemory.Bank.lm1, width, address⟩ resolvedEq w staticWidth rfl
      · by_cases bank : resolved.bank = PEMemory.Bank.lm1
        · have isLm1 : ParsedOperand.isLm1MemoryDestination
              (ParsedOperand.mem access negated extended rounded mask) = true := by
            apply countOk resolved.bank resolved.width _ bank
            have staticEq := ParsedOperand.toDirectMemoryDestination?_bankWidth
              (ParsedOperand.mem access negated extended rounded mask) context.pe cycle
              context.bar0 context.bar1 context.tWord
            rw [resolvedEq] at staticEq
            simpa [bank] using staticEq.symm
          have yes : (resolved.bank == PEMemory.Bank.lm1) = true := by
            simpa [beq_iff_eq] using bank
          simp [PreparedParsedMaskedWrite.isLm1Write, yes, isLm1]
        · have notEq : (resolved.bank == PEMemory.Bank.lm1) = false := by
            simpa using bank
          simp [PreparedParsedMaskedWrite.isLm1Write, notEq]
  | omr entry mask =>
      simp only [writeParsedMslMsrDestination?] at lowered
      cases h : ParsedOperand.toMaskRegisterEntry? (ParsedOperand.omr entry mask) with
      | none => simp [h] at lowered
      | some found =>
          cases h2 : ParsedOperand.resolveOmrWriteSelection? (ParsedOperand.omr entry mask)
              files.maskRegisters cycle directive hasSingleLineMask with
          | none => simp [h, h2] at lowered
          | some selection =>
              simp [h, h2] at lowered
              refine ⟨[⟨none, some (found, cycle, flags), PEMemory.unpackALUBus output,
                ⟨selection, false⟩⟩], ?_, ?_, ?_⟩
              · rw [← lowered]
                simp [commitParsedMaskedWrites]
              · intro write' member width address destinationEq
                simp only [List.mem_singleton] at member
                subst member
                simp at destinationEq
              · simp [ParsedOperand.isLm1MemoryDestination,
                  PreparedParsedMaskedWrite.isLm1Write]
  | bar lm1 width mask =>
      refine ⟨[], ?_, lm1WidthFacts_nil w, ?_⟩
      · simp only [writeParsedMslMsrDestination?] at lowered
        cases h : ParsedOperand.resolveMemoryWriteSelection? (ParsedOperand.bar lm1 width mask)
            (if lm1 = true then PEMemory.Bank.lm1 else PEMemory.Bank.lm0) files.maskRegisters
            cycle directive hasSingleLineMask with
        | none => simp [h] at lowered
        | some selection =>
            simp [h] at lowered
            rw [← lowered]
            simp [commitParsedMaskedWrites]
      · simp [ParsedOperand.isLm1MemoryDestination]
  | nowrite =>
      refine ⟨[], ?_, lm1WidthFacts_nil w, ?_⟩
      · simp only [writeParsedMslMsrDestination?] at lowered
        rw [← Option.some.inj lowered]
        simp [commitParsedMaskedWrites]
      · simp [ParsedOperand.isLm1MemoryDestination]
  | forward kind negated extended rounded => simp [writeParsedMslMsrDestination?] at lowered
  | fixed kind => simp [writeParsedMslMsrDestination?] at lowered
  | matrix side width row => simp [writeParsedMslMsrDestination?] at lowered
  | l1bm width address => simp [writeParsedMslMsrDestination?] at lowered
  | l2bm address l2b => simp [writeParsedMslMsrDestination?] at lowered
  | dar address => simp [writeParsedMslMsrDestination?] at lowered

/-- **The destination loop: static width and count, without any datapath input.** -/
theorem writeParsedMAUDestinations?_writeAll_widthCount
    (context : ParsedIntegerContext) (output : IntegerALU.Bus) (flags : BitVec 4)
    (cycle : Fin 4) (directive : ParsedMaskDirective) (hasSingleLineMask : Bool)
    (w : PEMemory.Width) :
    ∀ (destinations : List ParsedOperand) (files : IntegerRegisterFiles) (bar0 bar1 : BitVec 12)
      (next : ParsedMAUDestinationWrites),
      Lm1DestWidths w destinations →
      Lm1DestCount destinations →
      writeParsedMAUDestinations?.writeAll context output flags cycle directive hasSingleLineMask
        destinations files bar0 bar1 = some next →
      ∃ writes, next.files = commitParsedMaskedWrites files writes ∧
        Lm1WidthFacts w writes ∧
        (writes.filter PreparedParsedMaskedWrite.isLm1Write).length ≤
          (destinations.filter ParsedOperand.isLm1MemoryDestination).length := by
  intro destinations
  induction destinations with
  | nil =>
      intro files bar0 bar1 next widths count executed
      rw [writeParsedMAUDestinations?.writeAll] at executed
      obtain rfl := Option.some.inj executed
      exact ⟨[], rfl, lm1WidthFacts_nil w, by simp⟩
  | cons destination rest ih =>
      intro files bar0 bar1 next widths count executed
      rw [writeParsedMAUDestinations?.writeAll] at executed
      dsimp only at executed
      cases lowered : writeParsedMslMsrDestination? files destination
          { context with bar0 := bar0, bar1 := bar1 } output flags cycle directive
          hasSingleLineMask with
      | none =>
          rw [lowered] at executed
          simp at executed
      | some write =>
          rw [lowered] at executed
          obtain ⟨headWrites, headCommit, headWidth, headCount⟩ :=
            writeParsedMslMsrDestination?_widthCount files destination
              { context with bar0 := bar0, bar1 := bar1 } output flags cycle directive
              hasSingleLineMask write w lowered
              (fun v hv => widths destination (by simp) v hv)
              (fun bank width hv bankEq => count destination (by simp) bank width hv bankEq)
          obtain ⟨tailWrites, tailCommit, tailWidth, tailCount⟩ :=
            ih write.files
              (match write.barUpdate with
                | some (false, value) => value
                | _ => bar0)
              (match write.barUpdate with
                | some (true, value) => value
                | _ => bar1)
              next
              (fun d mem => widths d (List.mem_cons_of_mem _ mem))
              (fun d mem => count d (List.mem_cons_of_mem _ mem))
              executed
          refine ⟨headWrites ++ tailWrites, ?_, ?_, ?_⟩
          · rw [tailCommit, headCommit, commitParsedMaskedWrites_append]
          · exact lm1WidthFacts_append w headWrites tailWrites headWidth tailWidth
          · rw [List.filter_append, List.length_append, filter_length_cons_add]
            omega

/-- **The float-MAU destination writer: static width and count.** -/
theorem writeParsedMAUDestinations?_widthCount
    (files : IntegerRegisterFiles) (destinations : List ParsedOperand)
    (context : ParsedIntegerContext) (output : IntegerALU.Bus) (flags : BitVec 4)
    (cycle : Fin 4) (directive : ParsedMaskDirective) (hasSingleLineMask : Bool)
    (w : PEMemory.Width)
    (widths : Lm1DestWidths w destinations) (count : Lm1DestCount destinations)
    (next : ParsedMAUDestinationWrites)
    (executed : writeParsedMAUDestinations? files destinations context output flags cycle
      directive hasSingleLineMask = some next) :
    ∃ writes, next.files = commitParsedMaskedWrites files writes ∧ Lm1WidthFacts w writes ∧
      (writes.filter PreparedParsedMaskedWrite.isLm1Write).length ≤
        (destinations.filter ParsedOperand.isLm1MemoryDestination).length := by
  rw [writeParsedMAUDestinations?.eq_1] at executed
  exact writeParsedMAUDestinations?_writeAll_widthCount context output flags cycle directive
    hasSingleLineMask w destinations files context.bar0 context.bar1 next widths count executed

/-! ## 6. The copy-only destination facts -/

/-- **The copy facts of one destination.** -/
theorem writeParsedMslMsrDestination?_copyFacts
    (files : IntegerRegisterFiles) (destination : ParsedOperand)
    (context : ParsedIntegerContext) (output : IntegerALU.Bus) (flags : BitVec 4)
    (cycle : Fin 4) (directive : ParsedMaskDirective) (hasSingleLineMask : Bool)
    (write : ParsedMslMsrDestinationWrite)
    (copies : ∀ bound : 2 < 4, IsWelcomeCopy ((unpackALUBus output) ⟨2, bound⟩))
    (lowered : writeParsedMslMsrDestination? files destination context output flags cycle
      directive hasSingleLineMask = some write) :
    ∃ headWrites, write.files = commitParsedMaskedWrites files headWrites ∧
      Lm1CopyFacts headWrites := by
  cases destination with
  | mem access negated extended rounded mask =>
      obtain ⟨resolved, selection, resolvedEq, commitEq⟩ :=
        writeParsedMslMsrDestination?_mem_shape files access negated extended rounded mask
          context output flags cycle directive hasSingleLineMask write lowered
      refine ⟨[⟨some resolved, none, PEMemory.unpackALUBus output, selection⟩], commitEq.symm, ?_⟩
      intro write' member width address destinationEq bound
      simp only [List.mem_singleton] at member
      subst member
      exact copies bound
  | omr entry mask =>
      simp only [writeParsedMslMsrDestination?] at lowered
      cases h : ParsedOperand.toMaskRegisterEntry? (ParsedOperand.omr entry mask) with
      | none => simp [h] at lowered
      | some found =>
          cases h2 : ParsedOperand.resolveOmrWriteSelection? (ParsedOperand.omr entry mask)
              files.maskRegisters cycle directive hasSingleLineMask with
          | none => simp [h, h2] at lowered
          | some selection =>
              simp [h, h2] at lowered
              refine ⟨[⟨none, some (found, cycle, flags), PEMemory.unpackALUBus output,
                ⟨selection, false⟩⟩], ?_, ?_⟩
              · rw [← lowered]
                simp [commitParsedMaskedWrites]
              · intro write' member width address destinationEq
                simp only [List.mem_singleton] at member
                subst member
                simp at destinationEq
  | bar lm1 width mask =>
      refine ⟨[], ?_, lm1CopyFacts_nil⟩
      simp only [writeParsedMslMsrDestination?] at lowered
      cases h : ParsedOperand.resolveMemoryWriteSelection? (ParsedOperand.bar lm1 width mask)
          (if lm1 = true then PEMemory.Bank.lm1 else PEMemory.Bank.lm0) files.maskRegisters
          cycle directive hasSingleLineMask with
      | none => simp [h] at lowered
      | some selection =>
          simp [h] at lowered
          rw [← lowered]
          simp [commitParsedMaskedWrites]
  | nowrite =>
      refine ⟨[], ?_, lm1CopyFacts_nil⟩
      simp only [writeParsedMslMsrDestination?] at lowered
      rw [← Option.some.inj lowered]
      simp [commitParsedMaskedWrites]
  | forward kind negated extended rounded => simp [writeParsedMslMsrDestination?] at lowered
  | fixed kind => simp [writeParsedMslMsrDestination?] at lowered
  | matrix side width row => simp [writeParsedMslMsrDestination?] at lowered
  | l1bm width address => simp [writeParsedMslMsrDestination?] at lowered
  | l2bm address l2b => simp [writeParsedMslMsrDestination?] at lowered
  | dar address => simp [writeParsedMslMsrDestination?] at lowered

/-- **The copy facts of the destination loop.**  Every prepared write carries the
same flushed bus, so it suffices that the bus's third data word is a copy. -/
theorem writeParsedMAUDestinations?_writeAll_copy
    (context : ParsedIntegerContext) (output : IntegerALU.Bus) (flags : BitVec 4)
    (cycle : Fin 4) (directive : ParsedMaskDirective) (hasSingleLineMask : Bool)
    (copies : ∀ bound : 2 < 4, IsWelcomeCopy ((unpackALUBus output) ⟨2, bound⟩)) :
    ∀ (destinations : List ParsedOperand) (files : IntegerRegisterFiles) (bar0 bar1 : BitVec 12)
      (next : ParsedMAUDestinationWrites),
      writeParsedMAUDestinations?.writeAll context output flags cycle directive hasSingleLineMask
        destinations files bar0 bar1 = some next →
      ∃ writes, next.files = commitParsedMaskedWrites files writes ∧ Lm1CopyFacts writes := by
  intro destinations
  induction destinations with
  | nil =>
      intro files bar0 bar1 next executed
      rw [writeParsedMAUDestinations?.writeAll] at executed
      obtain rfl := Option.some.inj executed
      exact ⟨[], rfl, lm1CopyFacts_nil⟩
  | cons destination rest ih =>
      intro files bar0 bar1 next executed
      rw [writeParsedMAUDestinations?.writeAll] at executed
      dsimp only at executed
      cases lowered : writeParsedMslMsrDestination? files destination
          { context with bar0 := bar0, bar1 := bar1 } output flags cycle directive
          hasSingleLineMask with
      | none =>
          rw [lowered] at executed
          simp at executed
      | some write =>
          rw [lowered] at executed
          obtain ⟨headWrites, headCommit, headCopy⟩ :=
            writeParsedMslMsrDestination?_copyFacts files destination
              { context with bar0 := bar0, bar1 := bar1 } output flags cycle directive
              hasSingleLineMask write copies lowered
          obtain ⟨tailWrites, tailCommit, tailCopy⟩ :=
            ih write.files
              (match write.barUpdate with
                | some (false, value) => value
                | _ => bar0)
              (match write.barUpdate with
                | some (true, value) => value
                | _ => bar1)
              next executed
          exact ⟨headWrites ++ tailWrites, by
            rw [tailCommit, headCommit, commitParsedMaskedWrites_append],
            lm1CopyFacts_append headWrites tailWrites headCopy tailCopy⟩

/-- **The float-MAU destination writer: copy facts.** -/
theorem writeParsedMAUDestinations?_copyFacts
    (files : IntegerRegisterFiles) (destinations : List ParsedOperand)
    (context : ParsedIntegerContext) (output : IntegerALU.Bus) (flags : BitVec 4)
    (cycle : Fin 4) (directive : ParsedMaskDirective) (hasSingleLineMask : Bool)
    (copies : ∀ bound : 2 < 4, IsWelcomeCopy ((unpackALUBus output) ⟨2, bound⟩))
    (next : ParsedMAUDestinationWrites)
    (executed : writeParsedMAUDestinations? files destinations context output flags cycle
      directive hasSingleLineMask = some next) :
    ∃ writes, next.files = commitParsedMaskedWrites files writes ∧ Lm1CopyFacts writes := by
  rw [writeParsedMAUDestinations?.eq_1] at executed
  exact writeParsedMAUDestinations?_writeAll_copy context output flags cycle directive
    hasSingleLineMask copies destinations files context.bar0 context.bar1 next executed

/-! ## 7. The datapath hypothesis

Everything below this point is independent of the float-MAU datapath except for
one fact: at the all-zero state a *successful* float-MAU cycle produces a bus
whose low half's high word is a copy.  Every `.f` and `.d` branch of
`executeParsedFloatMAUCycleAtPE` returns a bus whose low half is literally
`0` (`⟨output, 0⟩`), so the fact is immediate there; the `.h` (half) branches
compute the low half from the source lanes, which the all-zero read makes zero.
The fact is stated on its own so that the window/width half of the row shape
(`Lm1WritesNarrow`) does not depend on it. -/

/-- **The remaining datapath hypothesis.**  A successful float-MAU cycle at the
all-zero register file (with every forwarding slot still poison) has a copied
third data word. -/
def WelcomePEFloatMAUCycleCopy : Prop :=
  ∀ (readFiles currentFiles : IntegerRegisterFiles) (oldSlots : Forwarding.Slots)
    (expression : ParsedExpr) (context : ParsedIntegerContext) (cycle : Fin 4)
    (files : IntegerRegisterFiles) (output : IntegerALU.Bus) (flags : BitVec 4),
    readFiles = welcomeZeroFiles →
    (∀ (unit : Forwarding.Unit) (c : Fin 4), oldSlots unit c = .poison) →
    executeParsedFloatMAUCycleAtPE readFiles currentFiles oldSlots expression context cycle =
      .ok (files, output, flags) →
    IsWelcomeCopy (output.low.extractLsb' 32 32)

/-! ## 8. The four-cycle loop -/

/-- **The four-cycle loop: static width and count.** -/
theorem executeParsedFloatMAUCyclesAtPE_widthCount
    (readFiles : IntegerRegisterFiles) (oldSlots : Forwarding.Slots) (expression : ParsedExpr)
    (context : ParsedIntegerContext) (directive : ParsedMaskDirective)
    (hasSingleLineMask : Bool) (w : PEMemory.Width)
    (widths : Lm1DestWidths w expression.destinations)
    (count : Lm1DestCount expression.destinations)
    (budget : (expression.destinations.filter ParsedOperand.isLm1MemoryDestination).length ≤ 1) :
    ∀ (cycles : List (Fin 4)) (files : IntegerRegisterFiles) (bar0 bar1 : BitVec 12)
      (outputs : Fin 4 → IntegerALU.Bus) (nextFiles : IntegerRegisterFiles)
      (nextBar0 nextBar1 : BitVec 12) (nextOutputs : Fin 4 → IntegerALU.Bus),
      executeParsedFloatMAUCyclesAtPE readFiles oldSlots expression context directive
        hasSingleLineMask cycles files bar0 bar1 outputs =
        .ok (nextFiles, nextBar0, nextBar1, nextOutputs) →
      ∃ writes, nextFiles = commitParsedMaskedWrites files writes ∧
        Lm1WidthFacts w writes ∧
        (writes.filter PreparedParsedMaskedWrite.isLm1Write).length ≤ cycles.length := by
  intro cycles
  induction cycles with
  | nil =>
      intro files bar0 bar1 outputs nextFiles nextBar0 nextBar1 nextOutputs executed
      rw [executeParsedFloatMAUCyclesAtPE.eq_1] at executed
      obtain ⟨rfl, rfl, rfl, rfl⟩ := StepResult.ok.inj executed
      exact ⟨[], rfl, lm1WidthFacts_nil w, by simp⟩
  | cons cycle rest ih =>
      intro files bar0 bar1 outputs nextFiles nextBar0 nextBar1 nextOutputs executed
      rw [executeParsedFloatMAUCyclesAtPE.eq_2] at executed
      dsimp only at executed
      cases cycleStep : executeParsedFloatMAUCycleAtPE readFiles files oldSlots expression
          { context with cycle := cycle, bar0 := bar0, bar1 := bar1 } cycle with
      | failure =>
          rw [cycleStep] at executed
          dsimp only at executed
          simp at executed
      | unknown =>
          rw [cycleStep] at executed
          dsimp only at executed
          simp at executed
      | ok result =>
          obtain ⟨ignored, output, flags⟩ := result
          rw [cycleStep] at executed
          dsimp only at executed
          cases flush : resolveFlushSelection? expression.flush files.maskRegisters cycle with
          | none =>
              rw [flush] at executed
              dsimp only at executed
              simp at executed
          | some flushSelection =>
              rw [flush] at executed
              dsimp only at executed
              cases wrote : writeParsedMAUDestinations? files expression.destinations
                  { context with cycle := cycle, bar0 := bar0, bar1 := bar1 }
                  (parsedOutputAfterFlush flushSelection output) flags cycle directive
                  hasSingleLineMask with
              | none =>
                  rw [wrote] at executed
                  dsimp only at executed
                  simp at executed
              | some writes =>
                  rw [wrote] at executed
                  obtain ⟨headWrites, headCommit, headWidth, headCount⟩ :=
                    writeParsedMAUDestinations?_widthCount files expression.destinations
                      { context with cycle := cycle, bar0 := bar0, bar1 := bar1 }
                      (parsedOutputAfterFlush flushSelection output) flags cycle directive
                      hasSingleLineMask w widths count writes wrote
                  obtain ⟨tailWrites, tailCommit, tailWidth, tailCount⟩ :=
                    ih writes.files writes.bar0 writes.bar1 _
                      nextFiles nextBar0 nextBar1 nextOutputs executed
                  refine ⟨headWrites ++ tailWrites, ?_, ?_, ?_⟩
                  · rw [tailCommit, headCommit, commitParsedMaskedWrites_append]
                  · exact lm1WidthFacts_append w headWrites tailWrites headWidth tailWidth
                  · rw [List.filter_append, List.length_append, List.length_cons]
                    omega

/-- **The four-cycle loop: static width, copies and count.** -/
theorem executeParsedFloatMAUCyclesAtPE_shape
    (readFiles : IntegerRegisterFiles) (oldSlots : Forwarding.Slots) (expression : ParsedExpr)
    (context : ParsedIntegerContext) (directive : ParsedMaskDirective)
    (hasSingleLineMask : Bool) (w : PEMemory.Width)
    (cycleCopy : WelcomePEFloatMAUCycleCopy)
    (zeroRead : readFiles = welcomeZeroFiles)
    (poisoned : ∀ (unit : Forwarding.Unit) (c : Fin 4), oldSlots unit c = .poison)
    (widths : Lm1DestWidths w expression.destinations)
    (count : Lm1DestCount expression.destinations)
    (budget : (expression.destinations.filter ParsedOperand.isLm1MemoryDestination).length ≤ 1) :
    ∀ (cycles : List (Fin 4)) (files : IntegerRegisterFiles) (bar0 bar1 : BitVec 12)
      (outputs : Fin 4 → IntegerALU.Bus) (nextFiles : IntegerRegisterFiles)
      (nextBar0 nextBar1 : BitVec 12) (nextOutputs : Fin 4 → IntegerALU.Bus),
      executeParsedFloatMAUCyclesAtPE readFiles oldSlots expression context directive
        hasSingleLineMask cycles files bar0 bar1 outputs =
        .ok (nextFiles, nextBar0, nextBar1, nextOutputs) →
      ∃ writes, nextFiles = commitParsedMaskedWrites files writes ∧
        Lm1WidthFacts w writes ∧ Lm1CopyFacts writes ∧
        (writes.filter PreparedParsedMaskedWrite.isLm1Write).length ≤ cycles.length := by
  intro cycles
  induction cycles with
  | nil =>
      intro files bar0 bar1 outputs nextFiles nextBar0 nextBar1 nextOutputs executed
      rw [executeParsedFloatMAUCyclesAtPE.eq_1] at executed
      obtain ⟨rfl, rfl, rfl, rfl⟩ := StepResult.ok.inj executed
      exact ⟨[], rfl, lm1WidthFacts_nil w, lm1CopyFacts_nil, by simp⟩
  | cons cycle rest ih =>
      intro files bar0 bar1 outputs nextFiles nextBar0 nextBar1 nextOutputs executed
      rw [executeParsedFloatMAUCyclesAtPE.eq_2] at executed
      dsimp only at executed
      cases cycleStep : executeParsedFloatMAUCycleAtPE readFiles files oldSlots expression
          { context with cycle := cycle, bar0 := bar0, bar1 := bar1 } cycle with
      | failure =>
          rw [cycleStep] at executed
          dsimp only at executed
          simp at executed
      | unknown =>
          rw [cycleStep] at executed
          dsimp only at executed
          simp at executed
      | ok result =>
          obtain ⟨ignored, output, flags⟩ := result
          rw [cycleStep] at executed
          dsimp only at executed
          cases flush : resolveFlushSelection? expression.flush files.maskRegisters cycle with
          | none =>
              rw [flush] at executed
              dsimp only at executed
              simp at executed
          | some flushSelection =>
              rw [flush] at executed
              dsimp only at executed
              cases wrote : writeParsedMAUDestinations? files expression.destinations
                  { context with cycle := cycle, bar0 := bar0, bar1 := bar1 }
                  (parsedOutputAfterFlush flushSelection output) flags cycle directive
                  hasSingleLineMask with
              | none =>
                  rw [wrote] at executed
                  dsimp only at executed
                  simp at executed
              | some writes =>
                  rw [wrote] at executed
                  have copyLow : IsWelcomeCopy (output.low.extractLsb' 32 32) :=
                    cycleCopy readFiles files oldSlots expression
                      { context with cycle := cycle, bar0 := bar0, bar1 := bar1 } cycle
                      ignored output flags zeroRead poisoned cycleStep
                  have dataCopy : ∀ bound : 2 < 4,
                      IsWelcomeCopy ((unpackALUBus (parsedOutputAfterFlush flushSelection output))
                        ⟨2, bound⟩) := by
                    intro bound
                    rw [unpackALUBus_of_val_eq_two _ _ rfl]
                    exact parsedOutputAfterFlush_word_two_isWelcomeCopy flushSelection output copyLow
                  obtain ⟨headWrites, headCommit, headWidth, headCopy, headCount⟩ :=
                    writeParsedMAUDestinations?_shape files expression.destinations
                      { context with cycle := cycle, bar0 := bar0, bar1 := bar1 }
                      (parsedOutputAfterFlush flushSelection output) flags cycle directive
                      hasSingleLineMask w dataCopy widths count writes wrote
                  obtain ⟨tailWrites, tailCommit, tailWidth, tailCopy, tailCount⟩ :=
                    ih writes.files writes.bar0 writes.bar1 _
                      nextFiles nextBar0 nextBar1 nextOutputs executed
                  refine ⟨headWrites ++ tailWrites, ?_, ?_, ?_, ?_⟩
                  · rw [tailCommit, headCommit, commitParsedMaskedWrites_append]
                  · exact lm1WidthFacts_append w headWrites tailWrites headWidth tailWidth
                  · exact lm1CopyFacts_append headWrites tailWrites headCopy tailCopy
                  · rw [List.filter_append, List.length_append, List.length_cons]
                    omega

/-! ## 9. The narrow half of `Lm1WriteFacts` suffices -/

theorem lm1WidthFacts_narrow (writes : List PreparedParsedMaskedWrite) (w : PEMemory.Width)
    (facts : Lm1WidthFacts w writes) (notDouble : w ≠ PEMemory.Width.double)
    (count : (writes.filter PreparedParsedMaskedWrite.isLm1Write).length ≤ 4) :
    Lm1WritesNarrow writes := by
  refine ⟨lm1WindowsOfWrites writes, ?_, ?_, ?_⟩
  · intro write member width address destination
    exact mem_lm1WindowsOfWrites_of_write writes write member width address destination
  · rw [lm1Windows_length_eq_count]
    exact count
  · intro window member
    obtain ⟨write, writeMem, width, address, destination, windowEq⟩ :=
      mem_lm1WindowsOfWrites writes window member
    obtain ⟨widthEq, _⟩ := facts write writeMem width address destination
    rw [windowEq]
    have widthNotDouble : width ≠ PEMemory.Width.double := by
      intro same
      exact notDouble (by rw [← widthEq]; exact same)
    cases width with
    | word =>
        show PEMemory.count PEMemory.Bank.lm1 PEMemory.Width.word ≤ 2
        decide
    | long =>
        show PEMemory.count PEMemory.Bank.lm1 PEMemory.Width.long ≤ 2
        decide
    | double => exact absurd rfl widthNotDouble

/-! ## 10. The float-MAU row at the all-zero state -/

/-- **The float-MAU row: static width, copies and count.**  The four cycles of a
single float-MAU row at the all-zero state commit and are shaped by the row's
static `.lm1` width. -/
theorem executeParsedFloatMAUsAtPE_zeroWidthCount
    (expression : ParsedExpr) (context : ParsedIntegerContext) (directive : ParsedMaskDirective)
    (hasSingleLineMask : Bool) (w : PEMemory.Width) (cycleCopy : WelcomePEFloatMAUCycleCopy)
    (widths : Lm1DestWidths w expression.destinations)
    (count : Lm1DestCount expression.destinations)
    (budget : (expression.destinations.filter ParsedOperand.isLm1MemoryDestination).length ≤ 1)
    (nextFiles : IntegerRegisterFiles) (nextBar0 nextBar1 : BitVec 12)
    (nextOutputs : Fin 4 → IntegerALU.Bus) (hasMAUProducer : Bool)
    (executed : executeParsedFloatMAUsAtPE welcomeZeroFiles welcomeZeroFiles welcomeZeroSlots context
      [expression] directive hasSingleLineMask =
      .ok (nextFiles, nextBar0, nextBar1, nextOutputs, hasMAUProducer)) :
    ∃ writes, nextFiles = commitParsedMaskedWrites welcomeZeroFiles writes ∧
      Lm1WidthFacts w writes ∧ Lm1CopyFacts writes ∧
      (writes.filter PreparedParsedMaskedWrite.isLm1Write).length ≤ 4 := by
  rw [executeParsedFloatMAUsAtPE.eq_1] at executed
  by_cases supported : parsedExprIsSupportedFloatMAUProducer expression = true
  · rw [show List.filter parsedExprIsSupportedFloatMAUProducer [expression] = [expression] by
      simp [supported]] at executed
    split at executed
    · simp at executed
    · simp at executed
    · rename_i files bar0 bar1 outputs ran
      rw [executeParsedFloatMAUsAtPE.run] at ran
      cases cycleStep : executeParsedFloatMAUCyclesAtPE welcomeZeroFiles welcomeZeroSlots expression
          context directive hasSingleLineMask [0, 1, 2, 3] welcomeZeroFiles context.bar0 context.bar1
          (fun _ => (⟨0, 0⟩ : IntegerALU.Bus)) with
      | failure => rw [cycleStep] at ran; simp at ran
      | unknown => rw [cycleStep] at ran; simp at ran
      | ok result =>
        obtain ⟨middleFiles, middleBar0, middleBar1, middleOutputs⟩ := result
        rw [cycleStep] at ran
        dsimp only at ran
        rw [executeParsedFloatMAUsAtPE.run.eq_1] at ran
        obtain ⟨rfl, rfl, rfl, rfl⟩ := StepResult.ok.inj ran
        obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := StepResult.ok.inj executed
        obtain ⟨writes, commit, widthFacts, copyFacts, countLe⟩ :=
          executeParsedFloatMAUCyclesAtPE_shape welcomeZeroFiles welcomeZeroSlots expression context
            directive hasSingleLineMask w cycleCopy rfl
            (fun unit c => welcomeZeroSlots_poison unit c) widths count budget
            [0, 1, 2, 3] welcomeZeroFiles context.bar0 context.bar1 (fun _ => ⟨0, 0⟩)
            nextFiles nextBar0 nextBar1 nextOutputs cycleStep
        exact ⟨writes, commit, widthFacts, copyFacts, by simpa using countLe⟩
  · rw [show List.filter parsedExprIsSupportedFloatMAUProducer [expression] = [] by
      simp [supported]] at executed
    split at executed
    · simp at executed
    · simp at executed
    · rename_i files bar0 bar1 outputs ran
      rw [executeParsedFloatMAUsAtPE.run.eq_1] at ran
      obtain ⟨rfl, rfl, rfl, rfl⟩ := StepResult.ok.inj ran
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := StepResult.ok.inj executed
      exact ⟨[], by simp [commitParsedMaskedWrites], lm1WidthFacts_nil w, lm1CopyFacts_nil,
        by simp⟩

/-- **The float-MAU row, width and count only (no datapath input).** -/
theorem executeParsedFloatMAUsAtPE_zeroWidthOnly
    (expression : ParsedExpr) (context : ParsedIntegerContext) (directive : ParsedMaskDirective)
    (hasSingleLineMask : Bool) (w : PEMemory.Width)
    (widths : Lm1DestWidths w expression.destinations)
    (count : Lm1DestCount expression.destinations)
    (budget : (expression.destinations.filter ParsedOperand.isLm1MemoryDestination).length ≤ 1)
    (nextFiles : IntegerRegisterFiles) (nextBar0 nextBar1 : BitVec 12)
    (nextOutputs : Fin 4 → IntegerALU.Bus) (hasMAUProducer : Bool)
    (executed : executeParsedFloatMAUsAtPE welcomeZeroFiles welcomeZeroFiles welcomeZeroSlots context
      [expression] directive hasSingleLineMask =
      .ok (nextFiles, nextBar0, nextBar1, nextOutputs, hasMAUProducer)) :
    ∃ writes, nextFiles = commitParsedMaskedWrites welcomeZeroFiles writes ∧
      Lm1WidthFacts w writes ∧
      (writes.filter PreparedParsedMaskedWrite.isLm1Write).length ≤ 4 := by
  rw [executeParsedFloatMAUsAtPE.eq_1] at executed
  by_cases supported : parsedExprIsSupportedFloatMAUProducer expression = true
  · rw [show List.filter parsedExprIsSupportedFloatMAUProducer [expression] = [expression] by
      simp [supported]] at executed
    split at executed
    · simp at executed
    · simp at executed
    · rename_i files bar0 bar1 outputs ran
      rw [executeParsedFloatMAUsAtPE.run] at ran
      cases cycleStep : executeParsedFloatMAUCyclesAtPE welcomeZeroFiles welcomeZeroSlots expression
          context directive hasSingleLineMask [0, 1, 2, 3] welcomeZeroFiles context.bar0 context.bar1
          (fun _ => (⟨0, 0⟩ : IntegerALU.Bus)) with
      | failure => rw [cycleStep] at ran; simp at ran
      | unknown => rw [cycleStep] at ran; simp at ran
      | ok result =>
        obtain ⟨middleFiles, middleBar0, middleBar1, middleOutputs⟩ := result
        rw [cycleStep] at ran
        dsimp only at ran
        rw [executeParsedFloatMAUsAtPE.run.eq_1] at ran
        obtain ⟨rfl, rfl, rfl, rfl⟩ := StepResult.ok.inj ran
        obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := StepResult.ok.inj executed
        obtain ⟨writes, commit, widthFacts, countLe⟩ :=
          executeParsedFloatMAUCyclesAtPE_widthCount welcomeZeroFiles welcomeZeroSlots expression
            context directive hasSingleLineMask w widths count budget
            [0, 1, 2, 3] welcomeZeroFiles context.bar0 context.bar1 (fun _ => ⟨0, 0⟩)
            nextFiles nextBar0 nextBar1 nextOutputs cycleStep
        exact ⟨writes, commit, widthFacts, by simpa using countLe⟩
  · rw [show List.filter parsedExprIsSupportedFloatMAUProducer [expression] = [] by
      simp [supported]] at executed
    split at executed
    · simp at executed
    · simp at executed
    · rename_i files bar0 bar1 outputs ran
      rw [executeParsedFloatMAUsAtPE.run.eq_1] at ran
      obtain ⟨rfl, rfl, rfl, rfl⟩ := StepResult.ok.inj ran
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := StepResult.ok.inj executed
      exact ⟨[], by simp [commitParsedMaskedWrites], lm1WidthFacts_nil w, by simp⟩

/-- **The float-MAU row shape at the all-zero state.**  A float-MAU row's
prepared write list is committed at the all-zero register file and is either all
copied `.double` blocks or fits in four narrow windows.  The only input is the
datapath fact `WelcomePEFloatMAUCycleCopy`. -/
theorem executeParsedFloatMAUsAtPE_zeroShape
    (expression : ParsedExpr) (context : ParsedIntegerContext) (directive : ParsedMaskDirective)
    (hasSingleLineMask : Bool) (w : PEMemory.Width) (cycleCopy : WelcomePEFloatMAUCycleCopy)
    (widths : Lm1DestWidths w expression.destinations)
    (count : Lm1DestCount expression.destinations)
    (budget : (expression.destinations.filter ParsedOperand.isLm1MemoryDestination).length ≤ 1)
    (nextFiles : IntegerRegisterFiles) (nextBar0 nextBar1 : BitVec 12)
    (nextOutputs : Fin 4 → IntegerALU.Bus) (hasMAUProducer : Bool)
    (executed : executeParsedFloatMAUsAtPE welcomeZeroFiles welcomeZeroFiles welcomeZeroSlots context
      [expression] directive hasSingleLineMask =
      .ok (nextFiles, nextBar0, nextBar1, nextOutputs, hasMAUProducer)) :
    ∃ writes, nextFiles = commitParsedMaskedWrites welcomeZeroFiles writes ∧
      (Lm1WritesDoubleCopy writes ∨ Lm1WritesNarrow writes) := by
  obtain ⟨writes, commit, widthFacts, copyFacts, countLe⟩ :=
    executeParsedFloatMAUsAtPE_zeroWidthCount expression context directive hasSingleLineMask w
      cycleCopy widths count budget nextFiles nextBar0 nextBar1 nextOutputs hasMAUProducer executed
  refine ⟨writes, commit, ?_⟩
  by_cases isDouble : w = PEMemory.Width.double
  · left
    have facts : Lm1WriteFacts w writes := lm1WriteFacts_of_parts w writes widthFacts copyFacts
    rw [isDouble] at facts
    exact lm1WriteFacts_doubleCopy writes facts
  · exact Or.inr (lm1WidthFacts_narrow writes w widthFacts isDouble countLe)

/-- **The unconditional narrow half.**  When the row's static `.lm1` width is
not `.double`, the prepared write list fits in four narrow windows — with no
datapath input at all. -/
theorem executeParsedFloatMAUsAtPE_zeroNarrow
    (expression : ParsedExpr) (context : ParsedIntegerContext) (directive : ParsedMaskDirective)
    (hasSingleLineMask : Bool) (w : PEMemory.Width)
    (widths : Lm1DestWidths w expression.destinations)
    (count : Lm1DestCount expression.destinations)
    (budget : (expression.destinations.filter ParsedOperand.isLm1MemoryDestination).length ≤ 1)
    (notDouble : w ≠ PEMemory.Width.double)
    (nextFiles : IntegerRegisterFiles) (nextBar0 nextBar1 : BitVec 12)
    (nextOutputs : Fin 4 → IntegerALU.Bus) (hasMAUProducer : Bool)
    (executed : executeParsedFloatMAUsAtPE welcomeZeroFiles welcomeZeroFiles welcomeZeroSlots context
      [expression] directive hasSingleLineMask =
      .ok (nextFiles, nextBar0, nextBar1, nextOutputs, hasMAUProducer)) :
    ∃ writes, nextFiles = commitParsedMaskedWrites welcomeZeroFiles writes ∧
      Lm1WritesNarrow writes := by
  obtain ⟨writes, commit, widthFacts, countLe⟩ :=
    executeParsedFloatMAUsAtPE_zeroWidthOnly expression context directive hasSingleLineMask w
      widths count budget nextFiles nextBar0 nextBar1 nextOutputs hasMAUProducer executed
  exact ⟨writes, commit, lm1WidthFacts_narrow writes w widthFacts notDouble countLe⟩

end ProofsLean.MNCore


namespace ProofsLean.MNCore

open Issue
open PEMemory

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

/-- The double-arithmetic MAU bus always has a zero low half. -/
theorem doubleMAUVectorBus_low (kind : CalcKind) (roundOutput : Bool)
    (values : List (BitVec 64)) : (doubleMAUVectorBus kind roundOutput values).low = 0 := by
  cases roundOutput <;> rfl

/-! ## 11. The datapath hypothesis, reduced to half precision -/

/-- **The half-precision part of the datapath hypothesis.**  Only the `.h`
(`.mau .h ...`) branches of `executeParsedFloatMAUCycleAtPE` compute the low half
of the bus from the source lanes; every other branch returns a bus whose low
half is literally zero. -/
def WelcomePEFloatMAUHalfCycleCopy : Prop :=
  ∀ (readFiles currentFiles : IntegerRegisterFiles) (oldSlots : Forwarding.Slots)
    (expression : ParsedExpr) (context : ParsedIntegerContext) (cycle : Fin 4)
    (files : IntegerRegisterFiles) (output : IntegerALU.Bus) (flags : BitVec 4)
    (kind : CalcKind) (half : Option Char) (round : Bool),
    expression.op = .mau .h false kind half round →
    readFiles = welcomeZeroFiles →
    (∀ (unit : Forwarding.Unit) (c : Fin 4), oldSlots unit c = .poison) →
    executeParsedFloatMAUCycleAtPE readFiles currentFiles oldSlots expression context cycle =
      .ok (files, output, flags) →
    IsWelcomeCopy (output.low.extractLsb' 32 32)

end ProofsLean.MNCore

namespace ProofsLean.MNCore

open Issue
open PEMemory

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

/-- **The datapath hypothesis from its half-precision part.**  Every `.f` and
`.d` branch, and the legacy float-memory fallback, returns `⟨output, 0⟩`: the low
half is `0`, so the third data word is `0`.  Only the four `.h` branches need
`WelcomePEFloatMAUHalfCycleCopy`. -/
theorem welcomePEFloatMAUCycleCopy_of_half (halfCopy : WelcomePEFloatMAUHalfCycleCopy) :
    WelcomePEFloatMAUCycleCopy := by
  intro readFiles currentFiles oldSlots expression context cycle files output flags zeroRead poisoned executed
  rcases expression with ⟨op, sources, destinations, flush, text⟩
  have original := executed
  unfold executeParsedFloatMAUCycleAtPE at executed
  split at executed
  -- the four half-precision branches
  case h_7 =>
    exact halfCopy readFiles currentFiles oldSlots ⟨op, sources, destinations, flush, text⟩ context
      cycle files output flags .mul _ _ (by assumption) zeroRead poisoned original
  case h_8 =>
    exact halfCopy readFiles currentFiles oldSlots ⟨op, sources, destinations, flush, text⟩ context
      cycle files output flags .add _ _ (by assumption) zeroRead poisoned original
  case h_9 =>
    exact halfCopy readFiles currentFiles oldSlots ⟨op, sources, destinations, flush, text⟩ context
      cycle files output flags .fma _ _ (by assumption) zeroRead poisoned original
  case h_10 =>
    exact halfCopy readFiles currentFiles oldSlots ⟨op, sources, destinations, flush, text⟩ context
      cycle files output flags .passa _ _ (by assumption) zeroRead poisoned original
  all_goals
    try dsimp only at executed
    try simp only [parsedFloatMAULoweringMiss] at executed
    repeat' (split at executed)
    all_goals (try simp at executed)
    all_goals (try (rcases executed with ⟨_, hout, _⟩
                    subst hout
                    exact isWelcomeCopy_extractLsb_zero))
    all_goals (try (rcases executed with ⟨_, hout, _⟩
                    subst hout
                    rw [doubleMAUVectorBus_low]
                    exact isWelcomeCopy_extractLsb_zero))

end ProofsLean.MNCore

namespace ProofsLean.MNCore

open Issue
open PEMemory

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

/-! ## 12. The row shape with the half-precision hypothesis -/

/-- **The float-MAU row shape at the all-zero state**, with the datapath
hypothesis reduced to its half-precision part.  The prepared write list of one
float-MAU row is committed at the all-zero register file and is either all
copied `.double` blocks or fits in four narrow windows. -/
theorem executeParsedFloatMAUsAtPE_zeroShape_of_half
    (halfCopy : WelcomePEFloatMAUHalfCycleCopy)
    (expression : ParsedExpr) (context : ParsedIntegerContext) (directive : ParsedMaskDirective)
    (hasSingleLineMask : Bool) (w : PEMemory.Width)
    (widths : Lm1DestWidths w expression.destinations)
    (count : Lm1DestCount expression.destinations)
    (budget : (expression.destinations.filter ParsedOperand.isLm1MemoryDestination).length ≤ 1)
    (nextFiles : IntegerRegisterFiles) (nextBar0 nextBar1 : BitVec 12)
    (nextOutputs : Fin 4 → IntegerALU.Bus) (hasMAUProducer : Bool)
    (executed : executeParsedFloatMAUsAtPE welcomeZeroFiles welcomeZeroFiles welcomeZeroSlots context
      [expression] directive hasSingleLineMask =
      .ok (nextFiles, nextBar0, nextBar1, nextOutputs, hasMAUProducer)) :
    ∃ writes, nextFiles = commitParsedMaskedWrites welcomeZeroFiles writes ∧
      (Lm1WritesDoubleCopy writes ∨ Lm1WritesNarrow writes) :=
  executeParsedFloatMAUsAtPE_zeroShape expression context directive hasSingleLineMask w
    (welcomePEFloatMAUCycleCopy_of_half halfCopy) widths count budget nextFiles nextBar0 nextBar1
    nextOutputs hasMAUProducer executed

end ProofsLean.MNCore

namespace ProofsLean.MNCore

open Issue
open PEMemory

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

/-! ## 13. Instantiated with the row's static width -/

/-- The count link is unconditional: a destination whose static bank is `.lm1`
is an `.lm1` memory destination. -/
theorem lm1DestCount_any (destinations : List ParsedOperand) : Lm1DestCount destinations := by
  intro d member bank width pair bankEq
  have lm1Pair : ParsedOperand.directDestinationBankWidth? d =
      some (PEMemory.Bank.lm1, width) := by
    rw [bankEq] at pair
    exact pair
  exact directDestinationBankWidth_isLm1 d width lm1Pair

/-- **The narrow half with the static width instantiated.**  The width is the
row's unique `.lm1` destination width `lm1StaticWidth expression`; the only
remaining hypotheses are the row's own no-duplicate-write condition and that
this width is not `.double`. -/
theorem executeParsedFloatMAUsAtPE_zeroNarrow_static
    (expression : ParsedExpr) (context : ParsedIntegerContext) (directive : ParsedMaskDirective)
    (hasSingleLineMask : Bool)
    (nodup : (expression.toIssueExpr 0).writeBanks.Nodup)
    (notDouble : (lm1StaticWidth expression).getD PEMemory.Width.word ≠
      PEMemory.Width.double)
    (nextFiles : IntegerRegisterFiles) (nextBar0 nextBar1 : BitVec 12)
    (nextOutputs : Fin 4 → IntegerALU.Bus) (hasMAUProducer : Bool)
    (executed : executeParsedFloatMAUsAtPE welcomeZeroFiles welcomeZeroFiles welcomeZeroSlots context
      [expression] directive hasSingleLineMask =
      .ok (nextFiles, nextBar0, nextBar1, nextOutputs, hasMAUProducer)) :
    ∃ writes, nextFiles = commitParsedMaskedWrites welcomeZeroFiles writes ∧
      Lm1WritesNarrow writes :=
  executeParsedFloatMAUsAtPE_zeroNarrow expression context directive hasSingleLineMask
    ((lm1StaticWidth expression).getD PEMemory.Width.word)
    (lm1StaticWidth_spec expression nodup) (lm1DestCount_any expression.destinations)
    (lm1Destinations_count_le_one expression 0 nodup) notDouble
    nextFiles nextBar0 nextBar1 nextOutputs hasMAUProducer executed

/-- **The full row shape with the static width instantiated.**  Same statement as
`executeParsedFloatMAUsAtPE_zeroShape_of_half`, with the width fixed to
`lm1StaticWidth expression` and the count link discharged. -/
theorem executeParsedFloatMAUsAtPE_zeroShape_static
    (halfCopy : WelcomePEFloatMAUHalfCycleCopy)
    (expression : ParsedExpr) (context : ParsedIntegerContext) (directive : ParsedMaskDirective)
    (hasSingleLineMask : Bool)
    (nodup : (expression.toIssueExpr 0).writeBanks.Nodup)
    (nextFiles : IntegerRegisterFiles) (nextBar0 nextBar1 : BitVec 12)
    (nextOutputs : Fin 4 → IntegerALU.Bus) (hasMAUProducer : Bool)
    (executed : executeParsedFloatMAUsAtPE welcomeZeroFiles welcomeZeroFiles welcomeZeroSlots context
      [expression] directive hasSingleLineMask =
      .ok (nextFiles, nextBar0, nextBar1, nextOutputs, hasMAUProducer)) :
    ∃ writes, nextFiles = commitParsedMaskedWrites welcomeZeroFiles writes ∧
      (Lm1WritesDoubleCopy writes ∨ Lm1WritesNarrow writes) :=
  executeParsedFloatMAUsAtPE_zeroShape_of_half halfCopy expression context directive
    hasSingleLineMask ((lm1StaticWidth expression).getD PEMemory.Width.word)
    (lm1StaticWidth_spec expression nodup) (lm1DestCount_any expression.destinations)
    (lm1Destinations_count_le_one expression 0 nodup)
    nextFiles nextBar0 nextBar1 nextOutputs hasMAUProducer executed

end ProofsLean.MNCore
