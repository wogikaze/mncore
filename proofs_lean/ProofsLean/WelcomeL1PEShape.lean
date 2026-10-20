import ProofsLean.WelcomeMixedStructure
import ProofsLean.WelcomeL12Shape

/-! # The L1BM-to-PE broadcast row: 4-alignment and the `.lm1` write shape

`WelcomeL12Shape.lean` proves the value half of the L1BM-to-PE family at the
all-zero initial state: the broadcast bus is zero
(`l1ToPEBusAt_welcomeInitialState`), the third data word of a broadcast write is
a copy (`l1ToPE_data_word_two_isWelcomeCopy`), and the four cycle writes of a
broadcast are a `Lm1WritesDoubleCopy` list when the destination width is
`.double` and a `Lm1WritesNarrow` list otherwise (`l1ToPEWrites_doubleCopy`,
`l1ToPEWrites_narrow`).  Two facts were still missing:

* the **4-alignment divisibility lemma**: the two shape lemmas take
  `address.val % 4 = 0` for `.double` writes as a hypothesis, but the executor
  computes the address as `(raw / width.words * width.words) % capacity`, so the
  alignment has to be derived from the definition of
  `ParsedOperand.toDirectMemoryAccessMode?`;
* the **row half**: the shape lemmas talk about the abstract list
  `l1ToPEWrites`, while the executor `executeParsedL1ToPEAtPEs` directly commits
  one masked store per cycle.  The row theorem has to extract the four writes
  from the executor run and show that its commit is the shape list.

## What this module proves

* **§1** the `Nat` divisibility cancellation
  `(n / words * words) % capacity % words = 0` (`nat_mod_align`, its `4`/`4096`
  specialisation `nat_mod_align_four`), and its consequence for the executor's
  address resolver:
  `toDirectMemoryAccessMode_address_mod_four` and
  `toDirectMemoryDestination_address_mod_four` — every `.double` destination
  resolved by `ParsedOperand.toDirectMemoryDestination?` is 4-aligned.
* **§2** the concrete four-element form of `l1ToPEWrites`
  (`l1ToPEWrites_eq_four`) and the commit algebra for it
  (`commitParsedMaskedWrites_l1ToPEWrites_four`).
* **§3** two eliminations that expose the executor's per-cycle data:
  `writeDestinations_mem_singleton_resolves` (one `.mem` destination of one
  cycle) and `writeCycles_cons_exists` (one cycle of the four-cycle loop).
* **§4** `executeParsedL1ToPE_writeCycles_mem_lm1_shape`: at a read state whose
  broadcast bus is zero (in particular the all-zero Welcome state), a
  broadcast expression whose destination list is a single `.mem` operand of
  static bank `.lm1` and width `w` commits, at the visited PE, a write list that
  is either `Lm1WritesDoubleCopy` (when `w = .double`, using the 4-alignment of
  §1 and the copied third data word of `WelcomeL12Shape`) or `Lm1WritesNarrow`
  (otherwise).
* **§5** the producer-level form
  `executeParsedL1ToPEProducer_mem_lm1_shape`: the same statement for the whole
  4096-PE walk of `executeParsedL1ToPEProducer`, at PE 0.  The walk's tail never
  visits PE 0 (`executeParsedL1ToPEAtPEs_peRegisters_not_mem`), and the head of
  `List.finRange 4096` is PE 0.  The walk induction is
  `executeParsedL1ToPEAtPEs_mem_lm1_shape`.
* **§5 (stage form)** `executeParsedL1ToPEProducers_mem_lm1_shape`: the same for
  the L1BM-to-PE *stage* of a line with exactly one L1ToPE producer row.
  `executeParsedL1ToPEProducers` fails outright on two L1ToPE rows
  (`executeParsedL1ToPEProducers_multiple_fail`), so every successful line's
  L1ToPE stage is in this single-row case (or is empty).

## What is not proved (and is not claimed)

Neither `WelcomePEL1ToPEShapeObligation` nor `LowerBound 2` nor `Optimal` is
proved here.  §6 records exactly what the line-level `Prop` still needs: the
obligation quantifies over lines in which the `.l1bm` broadcast row can be a
*non*-writer, and the line's `LM1` writer can be an arbitrary other row.  The
module also does not prove the single-row line instance
`WelcomePEWriteShape [e]`: that needs the stage pipeline of
`executeIntegerProducerInstructionLine` to be composed with the row shape (the
integer stage and the four middle stages are already known to be frames for a
broadcast row, but their filter/identity bookkeeping is not wired here).

No `sorry`, no `admit`, no `native_decide`, no new axioms, and no existing
module is edited by this file.
-/

namespace ProofsLean.MNCore

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

open Issue
open PEMemory

/-! ## 1. The 4-alignment divisibility lemma and its executor consequence

The address resolver computes `(raw / width.words * width.words) % capacity`.
The first factor is a multiple of `width.words`, and `width.words` divides the
capacity of every register bank, so the residue modulo `width.words` is zero.
For `width = .double` this is exactly `address.val % 4 = 0`. -/

/-- **The divisibility cancellation behind the alignment.**  If `words` divides
the capacity, then rounding `n` down to a multiple of `words` and wrapping
modulo the capacity preserves divisibility by `words`. -/
theorem nat_mod_align (n words capacity : Nat) (divides : words ∣ capacity) :
    (n / words * words) % capacity % words = 0 := by
  rw [Nat.mod_mod_of_dvd _ divides]
  exact Nat.mul_mod_left _ _

/-- The `.double`/`.lm1` instance: `(n / 4 * 4) % 4096` is a multiple of `4`. -/
theorem nat_mod_align_four (n : Nat) : (n / 4 * 4) % 4096 % 4 = 0 :=
  nat_mod_align n 4 4096 (by decide)

/-- **Every `.double` destination resolved by `toDirectMemoryAccessMode?` is
4-aligned.**  This is the hypothesis that `l1ToPEWrites_doubleCopy` needs,
derived from the resolver's own definition. -/
theorem toDirectMemoryAccessMode_address_mod_four
    (operand : ParsedOperand) (allowDestinationMask : Bool) (pe cycle : Fin 4)
    (bar0 bar1 : BitVec 12) (tWord : BitVec 32) (access : DirectMemoryAccess)
    (lowered : ParsedOperand.toDirectMemoryAccessMode? operand allowDestinationMask pe cycle
      bar0 bar1 tWord = some access)
    (isDouble : access.width = PEMemory.Width.double) :
    access.address.val % 4 = 0 := by
  cases operand with
  | mem memoryAccess negated extended rounded mask =>
      simp only [ParsedOperand.toDirectMemoryAccessMode?] at lowered
      split at lowered
      · simp at lowered
      · cases hb : issueBankToRegisterBank memoryAccess.bank with
        | none => simp [hb] at lowered
        | some bank =>
            cases hw : parsedWidth? memoryAccess.region.width with
            | none => simp [hb, hw] at lowered
            | some width =>
                simp only [hb, hw] at lowered
                split at lowered
                · simp at lowered
                · simp only [Option.some.injEq] at lowered
                  subst lowered
                  have widthDouble : width = PEMemory.Width.double := isDouble
                  subst widthDouble
                  show (if (bank == PEMemory.Bank.t) = true then cycle.val * 4 else
                    ((((if (bank == PEMemory.Bank.lm0) = true then bar0.toNat
                         else if (bank == PEMemory.Bank.lm1) = true then bar1.toNat else 0) +
                        (if memoryAccess.region.tIndirect = true then tWord.toNat else 0)) +
                      parsedRegionAddressAt memoryAccess.region cycle +
                      (match memoryAccess.region.madpe with
                       | some threshold =>
                           if (pe.val ≤ threshold) then PEMemory.Width.double.words else 0
                       | none => 0)) / PEMemory.Width.double.words *
                        PEMemory.Width.double.words % bank.capacity)) % 4 = 0
                  by_cases isT : bank = PEMemory.Bank.t
                  · rw [if_pos (by simp [isT])]
                    omega
                  · rw [if_neg (by simp [isT])]
                    have dvd : PEMemory.Width.double.words ∣ bank.capacity := by
                      cases bank <;> decide
                    have res := nat_mod_align
                      (((if (bank == PEMemory.Bank.lm0) = true then bar0.toNat
                         else if (bank == PEMemory.Bank.lm1) = true then bar1.toNat else 0) +
                        (if memoryAccess.region.tIndirect = true then tWord.toNat else 0)) +
                      parsedRegionAddressAt memoryAccess.region cycle +
                      (match memoryAccess.region.madpe with
                       | some threshold =>
                           if (pe.val ≤ threshold) then PEMemory.Width.double.words else 0
                       | none => 0))
                      PEMemory.Width.double.words bank.capacity dvd
                    simpa [PEMemory.Width.words] using res
  | bar _ _ mask => simp [ParsedOperand.toDirectMemoryAccessMode?] at lowered
  | forward _ _ _ _ => simp [ParsedOperand.toDirectMemoryAccessMode?] at lowered
  | fixed kind => simp [ParsedOperand.toDirectMemoryAccessMode?] at lowered
  | omr _ _ => simp [ParsedOperand.toDirectMemoryAccessMode?] at lowered
  | matrix _ _ _ => simp [ParsedOperand.toDirectMemoryAccessMode?] at lowered
  | nowrite => simp [ParsedOperand.toDirectMemoryAccessMode?] at lowered
  | l1bm _ _ => simp [ParsedOperand.toDirectMemoryAccessMode?] at lowered
  | l2bm _ _ => simp [ParsedOperand.toDirectMemoryAccessMode?] at lowered
  | dar _ => simp [ParsedOperand.toDirectMemoryAccessMode?] at lowered

/-- The destination form: `ParsedOperand.toDirectMemoryDestination?` is
`toDirectMemoryAccessMode?` at `allowDestinationMask = true`. -/
theorem toDirectMemoryDestination_address_mod_four
    (operand : ParsedOperand) (pe cycle : Fin 4) (bar0 bar1 : BitVec 12)
    (tWord : BitVec 32) (access : DirectMemoryAccess)
    (lowered : ParsedOperand.toDirectMemoryDestination? operand pe cycle bar0 bar1 tWord =
      some access)
    (isDouble : access.width = PEMemory.Width.double) :
    access.address.val % 4 = 0 :=
  toDirectMemoryAccessMode_address_mod_four operand true pe cycle bar0 bar1 tWord access
    lowered isDouble

/-! ## 2. The four-cycle list of `l1ToPEWrites`, and its commit

`l1ToPEWrites` is a `List.map` over `List.finRange 4`; the executor's cycle loop
uses the literal list `[0, 1, 2, 3]`.  The two lemmas below bridge the list
notation and the commit algebra, so that a run of the cycle loop can be
identified with the commit of the abstract write list of `WelcomeL12Shape`. -/

/-- `l1ToPEWrites` written out as the four cycle writes, with the zero data bus
of the all-zero initial state. -/
theorem l1ToPEWrites_eq_four (w : PEMemory.Width)
    (addresses : Fin 4 → Fin PEMemory.Bank.lm1.capacity)
    (selections : Fin 4 → PEWordSelection) :
    l1ToPEWrites w addresses selections =
      [⟨some ⟨PEMemory.Bank.lm1, w, addresses 0⟩, none,
          (fun _ => 0 : PEMemory.WordBus), selections 0⟩,
       ⟨some ⟨PEMemory.Bank.lm1, w, addresses 1⟩, none,
          (fun _ => 0 : PEMemory.WordBus), selections 1⟩,
       ⟨some ⟨PEMemory.Bank.lm1, w, addresses 2⟩, none,
          (fun _ => 0 : PEMemory.WordBus), selections 2⟩,
       ⟨some ⟨PEMemory.Bank.lm1, w, addresses 3⟩, none,
          (fun _ => 0 : PEMemory.WordBus), selections 3⟩] := by
  rw [l1ToPEWrites, show List.finRange 4 = [0, 1, 2, 3] from rfl]
  rfl

/-- **The commit of the four cycle writes.**  Four successive masked stores at
the (aligned) cycle addresses are the commit of `l1ToPEWrites`. -/
theorem commitParsedMaskedWrites_l1ToPEWrites_four
    (files0 files1 files2 files3 files4 : IntegerRegisterFiles)
    (w : PEMemory.Width) (addresses : Fin 4 → Fin PEMemory.Bank.lm1.capacity)
    (selections : Fin 4 → PEWordSelection)
    (h0 : files1 = PEMemory.writeDirectAccessMasked files0
      ⟨PEMemory.Bank.lm1, w, addresses 0⟩ (fun _ => 0) (selections 0))
    (h1 : files2 = PEMemory.writeDirectAccessMasked files1
      ⟨PEMemory.Bank.lm1, w, addresses 1⟩ (fun _ => 0) (selections 1))
    (h2 : files3 = PEMemory.writeDirectAccessMasked files2
      ⟨PEMemory.Bank.lm1, w, addresses 2⟩ (fun _ => 0) (selections 2))
    (h3 : files4 = PEMemory.writeDirectAccessMasked files3
      ⟨PEMemory.Bank.lm1, w, addresses 3⟩ (fun _ => 0) (selections 3)) :
    files4 = commitParsedMaskedWrites files0 (l1ToPEWrites w addresses selections) := by
  rw [l1ToPEWrites_eq_four, commitParsedMaskedWrites_cons, commitParsedMaskedWrites_cons,
    commitParsedMaskedWrites_cons, commitParsedMaskedWrites_cons]
  simp only [commitParsedMaskedWrites, List.foldl_nil, welcomeCommitStep]
  rw [← h0, ← h1, ← h2, ← h3]

/-! ## 3. Eliminating the executor's destination loop and one cycle

Both loops of `executeParsedL1ToPEAtPEs` are local recursive definitions, so
their equations are named lemmas (`writeDestinations`, `writeCycles`).  The two
eliminations below run them in the *forward* direction on the concrete
destinations and use `Option.some.inj` on the resulting equation; this avoids
reducing the `do` blocks by hand. -/

/-- **One `.mem` destination of one cycle is one masked store.**  Conversely, a
successful destination loop with the singleton list `[.mem ...]` exposes the
resolved access, the write selection, and the stored register file. -/
theorem writeDestinations_mem_singleton_resolves
    (currentState : State) (hasSingleLineMask : Bool) (maskRegisters : Masks.RegisterFile)
    (cycle : Fin 4) (context : ParsedIntegerContext) (output : IntegerALU.Bus)
    (memoryAccess : Access) (negated extended rounded : Bool) (mask : Option ParsedMask)
    (files : IntegerRegisterFiles) (bar0 bar1 : BitVec 12)
    (nextFiles : IntegerRegisterFiles) (nextBar0 nextBar1 : BitVec 12)
    (executed : executeParsedL1ToPEAtPEs.writeCycles.writeDestinations currentState
      hasSingleLineMask maskRegisters cycle context output
      [.mem memoryAccess negated extended rounded mask] files bar0 bar1 =
      some (nextFiles, nextBar0, nextBar1)) :
    ∃ (access : DirectMemoryAccess) (selection : PEWordSelection),
      ParsedOperand.toDirectMemoryDestination? (.mem memoryAccess negated extended rounded mask)
        context.pe cycle bar0 bar1 context.tWord = some access ∧
      ParsedOperand.resolveMemoryWriteSelection? (.mem memoryAccess negated extended rounded mask)
        access.bank maskRegisters cycle currentState.maskDirective hasSingleLineMask =
          some selection ∧
      nextFiles = PEMemory.writeDirectAccessMasked files access
        (PEMemory.unpackALUBus output) selection ∧
      nextBar0 = bar0 ∧ nextBar1 = bar1 := by
  cases h : ParsedOperand.toDirectMemoryDestination?
      (.mem memoryAccess negated extended rounded mask)
      context.pe cycle bar0 bar1 context.tWord with
  | none =>
      have noneLoop : executeParsedL1ToPEAtPEs.writeCycles.writeDestinations currentState
          hasSingleLineMask maskRegisters cycle context output
          [.mem memoryAccess negated extended rounded mask] files bar0 bar1 = none := by
        rw [executeParsedL1ToPEAtPEs.writeCycles.writeDestinations]
        simp [writeParsedL1ToPEDestination?, h]
      rw [noneLoop] at executed
      simp at executed
  | some access =>
      cases h2 : ParsedOperand.resolveMemoryWriteSelection?
          (.mem memoryAccess negated extended rounded mask) access.bank maskRegisters cycle
          currentState.maskDirective hasSingleLineMask with
      | none =>
          have noneLoop : executeParsedL1ToPEAtPEs.writeCycles.writeDestinations currentState
              hasSingleLineMask maskRegisters cycle context output
              [.mem memoryAccess negated extended rounded mask] files bar0 bar1 = none := by
            rw [executeParsedL1ToPEAtPEs.writeCycles.writeDestinations]
            simp [writeParsedL1ToPEDestination?, h, h2]
          rw [noneLoop] at executed
          simp at executed
      | some selection =>
          have forward := writeDestinations_mem_singleton currentState hasSingleLineMask
            maskRegisters cycle context output memoryAccess negated extended rounded mask
            files bar0 bar1 access selection h h2
          rw [forward] at executed
          obtain ⟨rfl, rfl, rfl⟩ := Option.some.inj executed
          exact ⟨access, selection, rfl, h2, rfl, rfl, rfl⟩

/-- **One cycle of the four-cycle loop.**  A successful `cycle :: cycles` run
exposes the flush selection, the destination-loop result and the tail run. -/
theorem writeCycles_cons_exists
    (readState currentState : State) (expression : ParsedExpr) (access : ParsedL1ToPEAccess)
    (hasSingleLineMask : Bool) (pe : PEId) (coordinates readContext : ParsedIntegerContext)
    (maskRegisters : Masks.RegisterFile) (cycle : Fin 4) (cycles : List (Fin 4))
    (files : IntegerRegisterFiles) (bar0 bar1 : BitVec 12)
    (nextFiles : IntegerRegisterFiles) (nextBar0 nextBar1 : BitVec 12)
    (executed : executeParsedL1ToPEAtPEs.writeCycles readState currentState expression access
      hasSingleLineMask pe coordinates readContext maskRegisters (cycle :: cycles) files bar0 bar1 =
      .ok (nextFiles, nextBar0, nextBar1)) :
    ∃ (selection : Option PEWordSelection) (middleFiles : IntegerRegisterFiles)
      (middleBar0 middleBar1 : BitVec 12),
      resolveFlushSelection? expression.flush maskRegisters cycle = some selection ∧
      executeParsedL1ToPEAtPEs.writeCycles.writeDestinations currentState hasSingleLineMask
        maskRegisters cycle
        ({ coordinates with cycle := cycle, bar0 := bar0, bar1 := bar1, tWord := readContext.tWord })
        (parsedOutputAfterFlush selection (l1ToPEBusAt readState expression access pe cycle))
        access.destinations files bar0 bar1 = some (middleFiles, middleBar0, middleBar1) ∧
      executeParsedL1ToPEAtPEs.writeCycles readState currentState expression access
        hasSingleLineMask pe coordinates readContext maskRegisters cycles middleFiles
        middleBar0 middleBar1 = .ok (nextFiles, nextBar0, nextBar1) := by
  rw [executeParsedL1ToPEAtPEs.writeCycles] at executed
  dsimp only at executed
  cases flush : resolveFlushSelection? expression.flush maskRegisters cycle with
  | none => rw [flush] at executed; simp at executed
  | some selection =>
      rw [flush] at executed
      dsimp only at executed
      split at executed
      · simp at executed
      · rename_i middleFiles middleBar0 middleBar1 wrote
        exact ⟨selection, middleFiles, middleBar0, middleBar1, rfl, wrote, executed⟩

/-! ## 4. The broadcast row shape at the cycle-loop level -/

/-- The four values `c = 0, 1, 2, 3`, as a function on `Fin 4`. -/
def fourCases {α : Type} (a0 a1 a2 a3 : α) : Fin 4 → α :=
  fun c => match c.val with
    | 0 => a0
    | 1 => a1
    | 2 => a2
    | _ => a3

/-- The four elements of `Fin 4`. -/
theorem fin_four_eq (c : Fin 4) : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 := by
  have := c.isLt
  have h : c.val = 0 ∨ c.val = 1 ∨ c.val = 2 ∨ c.val = 3 := by omega
  rcases h with h | h | h | h
  · exact Or.inl (Fin.ext (by simpa using h))
  · exact Or.inr (Or.inl (Fin.ext (by simpa using h)))
  · exact Or.inr (Or.inr (Or.inl (Fin.ext (by simpa using h))))
  · exact Or.inr (Or.inr (Or.inr (Fin.ext (by simpa using h))))

/-- **The `.l1bm` broadcast row's four cycle writes are double-copy or
narrow.**  The destination list is the singleton `.mem` operand
`memoryAccess negated extended rounded mask`, whose static bank and width are
`.lm1` and `w`; the read state's broadcast bus is zero.  Then the register file
that the four-cycle loop returns is the commit of a write list which is
`Lm1WritesDoubleCopy` when `w = .double` and `Lm1WritesNarrow` otherwise.

The `.double` half uses §1's 4-alignment and
`l1ToPE_data_word_two_isWelcomeCopy`; the non-`.double` half uses
`l1ToPEWrites_narrow`.  Both go through the abstract list `l1ToPEWrites`, the
four-element form of §2 and the executor eliminations of §3. -/
theorem executeParsedL1ToPE_writeCycles_mem_lm1_shape
    (readState currentState : State) (expression : ParsedExpr) (access : ParsedL1ToPEAccess)
    (hasSingleLineMask : Bool) (pe : PEId) (coordinates readContext : ParsedIntegerContext)
    (maskRegisters : Masks.RegisterFile)
    (memoryAccess : Access) (negated extended rounded : Bool) (mask : Option ParsedMask)
    (w : PEMemory.Width)
    (destinations : access.destinations =
      [ParsedOperand.mem memoryAccess negated extended rounded mask])
    (static : ParsedOperand.directDestinationBankWidth?
      (ParsedOperand.mem memoryAccess negated extended rounded mask) = some (PEMemory.Bank.lm1, w))
    (zeroBus : ∀ cycle : Fin 4, l1ToPEBusAt readState expression access pe cycle = ⟨0, 0⟩)
    (files0 : IntegerRegisterFiles) (bar0 bar1 : BitVec 12)
    (nextFiles : IntegerRegisterFiles) (nextBar0 nextBar1 : BitVec 12)
    (executed : executeParsedL1ToPEAtPEs.writeCycles readState currentState expression access
      hasSingleLineMask pe coordinates readContext maskRegisters [0, 1, 2, 3] files0 bar0 bar1 =
      .ok (nextFiles, nextBar0, nextBar1)) :
    ∃ writes, nextFiles = commitParsedMaskedWrites files0 writes ∧
      (Lm1WritesDoubleCopy writes ∨ Lm1WritesNarrow writes) := by
  -- cycle 0
  obtain ⟨sel0, files1, m10, m11, _flush0, wrote0, rest1⟩ :=
    writeCycles_cons_exists readState currentState expression access hasSingleLineMask pe
      coordinates readContext maskRegisters 0 [1, 2, 3] files0 bar0 bar1 nextFiles nextBar0
      nextBar1 executed
  rw [destinations] at wrote0
  obtain ⟨acc0, wsel0, lower0, _resolved0, files1eq, b10, b11⟩ :=
    writeDestinations_mem_singleton_resolves currentState hasSingleLineMask maskRegisters 0
      ({ coordinates with cycle := 0, bar0 := bar0, bar1 := bar1, tWord := readContext.tWord })
      (parsedOutputAfterFlush sel0 (l1ToPEBusAt readState expression access pe 0))
      memoryAccess negated extended rounded mask files0 bar0 bar1 files1 m10 m11 wrote0
  rw [b10, b11] at rest1
  -- cycle 1
  obtain ⟨sel1, files2, m20, m21, _flush1, wrote1, rest2⟩ :=
    writeCycles_cons_exists readState currentState expression access hasSingleLineMask pe
      coordinates readContext maskRegisters 1 [2, 3] files1 bar0 bar1 nextFiles nextBar0
      nextBar1 rest1
  rw [destinations] at wrote1
  obtain ⟨acc1, wsel1, lower1, _resolved1, files2eq, b20, b21⟩ :=
    writeDestinations_mem_singleton_resolves currentState hasSingleLineMask maskRegisters 1
      ({ coordinates with cycle := 1, bar0 := bar0, bar1 := bar1, tWord := readContext.tWord })
      (parsedOutputAfterFlush sel1 (l1ToPEBusAt readState expression access pe 1))
      memoryAccess negated extended rounded mask files1 bar0 bar1 files2 m20 m21 wrote1
  rw [b20, b21] at rest2
  -- cycle 2
  obtain ⟨sel2, files3, m30, m31, _flush2, wrote2, rest3⟩ :=
    writeCycles_cons_exists readState currentState expression access hasSingleLineMask pe
      coordinates readContext maskRegisters 2 [3] files2 bar0 bar1 nextFiles nextBar0
      nextBar1 rest2
  rw [destinations] at wrote2
  obtain ⟨acc2, wsel2, lower2, _resolved2, files3eq, b30, b31⟩ :=
    writeDestinations_mem_singleton_resolves currentState hasSingleLineMask maskRegisters 2
      ({ coordinates with cycle := 2, bar0 := bar0, bar1 := bar1, tWord := readContext.tWord })
      (parsedOutputAfterFlush sel2 (l1ToPEBusAt readState expression access pe 2))
      memoryAccess negated extended rounded mask files2 bar0 bar1 files3 m30 m31 wrote2
  rw [b30, b31] at rest3
  -- cycle 3
  obtain ⟨sel3, files4, m40, m41, _flush3, wrote3, rest4⟩ :=
    writeCycles_cons_exists readState currentState expression access hasSingleLineMask pe
      coordinates readContext maskRegisters 3 [] files3 bar0 bar1 nextFiles nextBar0
      nextBar1 rest3
  rw [destinations] at wrote3
  obtain ⟨acc3, wsel3, lower3, _resolved3, files4eq, b40, b41⟩ :=
    writeDestinations_mem_singleton_resolves currentState hasSingleLineMask maskRegisters 3
      ({ coordinates with cycle := 3, bar0 := bar0, bar1 := bar1, tWord := readContext.tWord })
      (parsedOutputAfterFlush sel3 (l1ToPEBusAt readState expression access pe 3))
      memoryAccess negated extended rounded mask files3 bar0 bar1 files4 m40 m41 wrote3
  rw [b40, b41] at rest4
  rw [executeParsedL1ToPEAtPEs.writeCycles] at rest4
  have hfiles : nextFiles = files4 := by
    have h := StepResult.ok.inj rest4
    exact (congrArg Prod.fst h).symm
  rw [hfiles]
  -- the written data is the zero bus
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
  -- the static bank and width of every cycle
  have staticAt (cycle : Fin 4) (acc : DirectMemoryAccess)
      (lowered : ParsedOperand.toDirectMemoryDestination?
        (ParsedOperand.mem memoryAccess negated extended rounded mask)
        coordinates.pe cycle bar0 bar1 readContext.tWord = some acc) :
      acc.bank = PEMemory.Bank.lm1 ∧ acc.width = w := by
    have pair := ParsedOperand.toDirectMemoryDestination?_bankWidth
      (ParsedOperand.mem memoryAccess negated extended rounded mask) coordinates.pe cycle
      bar0 bar1 readContext.tWord
    rw [lowered, static] at pair
    simp only [Option.map_some] at pair
    have pairEq : (acc.bank, acc.width) = (PEMemory.Bank.lm1, w) := Option.some.inj pair
    exact ⟨by simpa using congrArg Prod.fst pairEq,
      by simpa using congrArg Prod.snd pairEq⟩
  obtain ⟨bank0, width0⟩ := staticAt 0 acc0 lower0
  obtain ⟨bank1, width1⟩ := staticAt 1 acc1 lower1
  obtain ⟨bank2, width2⟩ := staticAt 2 acc2 lower2
  obtain ⟨bank3, width3⟩ := staticAt 3 acc3 lower3
  have acc0eq : acc0 = ⟨PEMemory.Bank.lm1, w, Fin.cast (by rw [bank0]) acc0.address⟩ := by
    cases acc0 with
    | mk bank width address =>
        simp only at bank0 width0
        subst bank0
        subst width0
        rfl
  have acc1eq : acc1 = ⟨PEMemory.Bank.lm1, w, Fin.cast (by rw [bank1]) acc1.address⟩ := by
    cases acc1 with
    | mk bank width address =>
        simp only at bank1 width1
        subst bank1
        subst width1
        rfl
  have acc2eq : acc2 = ⟨PEMemory.Bank.lm1, w, Fin.cast (by rw [bank2]) acc2.address⟩ := by
    cases acc2 with
    | mk bank width address =>
        simp only at bank2 width2
        subst bank2
        subst width2
        rfl
  have acc3eq : acc3 = ⟨PEMemory.Bank.lm1, w, Fin.cast (by rw [bank3]) acc3.address⟩ := by
    cases acc3 with
    | mk bank width address =>
        simp only at bank3 width3
        subst bank3
        subst width3
        rfl
  let addresses : Fin 4 → Fin PEMemory.Bank.lm1.capacity :=
    fourCases (Fin.cast (by rw [bank0]) acc0.address)
      (Fin.cast (by rw [bank1]) acc1.address)
      (Fin.cast (by rw [bank2]) acc2.address)
      (Fin.cast (by rw [bank3]) acc3.address)
  let selections : Fin 4 → PEWordSelection := fourCases wsel0 wsel1 wsel2 wsel3
  have store0 : files1 = PEMemory.writeDirectAccessMasked files0
      ⟨PEMemory.Bank.lm1, w, addresses 0⟩ (fun _ => 0) (selections 0) := by
    rw [files1eq, acc0eq, data0]
    rfl
  have store1 : files2 = PEMemory.writeDirectAccessMasked files1
      ⟨PEMemory.Bank.lm1, w, addresses 1⟩ (fun _ => 0) (selections 1) := by
    rw [files2eq, acc1eq, data1]
    rfl
  have store2 : files3 = PEMemory.writeDirectAccessMasked files2
      ⟨PEMemory.Bank.lm1, w, addresses 2⟩ (fun _ => 0) (selections 2) := by
    rw [files3eq, acc2eq, data2]
    rfl
  have store3 : files4 = PEMemory.writeDirectAccessMasked files3
      ⟨PEMemory.Bank.lm1, w, addresses 3⟩ (fun _ => 0) (selections 3) := by
    rw [files4eq, acc3eq, data3]
    rfl
  have commitEq := commitParsedMaskedWrites_l1ToPEWrites_four files0 files1 files2 files3
    files4 w addresses selections store0 store1 store2 store3
  refine ⟨l1ToPEWrites w addresses selections, commitEq, ?_⟩
  by_cases double : w = PEMemory.Width.double
  · left
    subst double
    refine l1ToPEWrites_doubleCopy addresses selections ?_
    intro c
    rcases fin_four_eq c with rfl | rfl | rfl | rfl
    · simp only [addresses, fourCases]
      exact toDirectMemoryDestination_address_mod_four
        (ParsedOperand.mem memoryAccess negated extended rounded mask) coordinates.pe 0 bar0
        bar1 readContext.tWord acc0 lower0 width0
    · simp only [addresses, fourCases]
      exact toDirectMemoryDestination_address_mod_four
        (ParsedOperand.mem memoryAccess negated extended rounded mask) coordinates.pe 1 bar0
        bar1 readContext.tWord acc1 lower1 width1
    · simp only [addresses, fourCases]
      exact toDirectMemoryDestination_address_mod_four
        (ParsedOperand.mem memoryAccess negated extended rounded mask) coordinates.pe 2 bar0
        bar1 readContext.tWord acc2 lower2 width2
    · simp only [addresses, fourCases]
      exact toDirectMemoryDestination_address_mod_four
        (ParsedOperand.mem memoryAccess negated extended rounded mask) coordinates.pe 3 bar0
        bar1 readContext.tWord acc3 lower3 width3
  · exact Or.inr (l1ToPEWrites_narrow w addresses selections double)

/-! ## 5. The broadcast row at the producer and L1ToPE-stage level

`executeParsedL1ToPEProducer` runs the cycle loop at every PE of
`List.finRange 4096`.  Only the visit to PE 0 matters for the observed PE, and
`0` is the head of that list, so the shape of the head's commit is the shape of
the producer's PE 0 file.  The induction below is stated for an arbitrary
duplicate-free PE list containing PE 0: if the visited PE is PE 0 the head's
commit is kept, and otherwise the head only rewrites another PE's register file
and the tail carries the induction. -/

/-- **The broadcast row's shape at PE 0, along an arbitrary PE walk.** -/
theorem executeParsedL1ToPEAtPEs_mem_lm1_shape
    (readState : State) (expression : ParsedExpr) (access : ParsedL1ToPEAccess)
    (hasSingleLineMask usePreIssueMask noForward : Bool)
    (memoryAccess : Access) (negated extended rounded : Bool) (mask : Option ParsedMask)
    (w : PEMemory.Width)
    (destinations : access.destinations =
      [ParsedOperand.mem memoryAccess negated extended rounded mask])
    (static : ParsedOperand.directDestinationBankWidth?
      (ParsedOperand.mem memoryAccess negated extended rounded mask) = some (PEMemory.Bank.lm1, w))
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
            have hcycle := executeParsedL1ToPE_writeCycles_mem_lm1_shape readState currentState
              expression access hasSingleLineMask welcomePE
              (ParsedIntegerContext.ofLinearIndex welcomePE) (readState.peContext welcomePE) _
              memoryAccess negated extended rounded mask w destinations static
              (fun cycle => zeroBus welcomePE cycle) (currentState.peRegisters welcomePE)
              (currentState.peContext welcomePE).bar0 (currentState.peContext welcomePE).bar1
              files bar0 bar1 ran
            obtain ⟨writes, commitFiles, shape⟩ := hcycle
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

/-- **The `.l1bm` broadcast row is a `double`-copy or narrow writer at PE 0.**
At the all-zero Welcome initial state, a `.l1bm` broadcast row (`pbcast` /
`mbcast` / `m4bcast` / `distrib`) whose destination list is a single `.mem`
operand of static bank `.lm1` and width `w` prepares a write list at PE 0 that
is either `Lm1WritesDoubleCopy` (`w = .double`) or `Lm1WritesNarrow`, and PE 0's
register file after the producer is that list's commit.

This is the row-local half of `WelcomePEL1ToPEShapeObligation`; see §6 for the
line-level remainder. -/
theorem executeParsedL1ToPEProducer_mem_lm1_shape
    (input : ProofsLean.MNCore.PlusOne.Words) (currentState next : State)
    (expression : ParsedExpr) (access : ParsedL1ToPEAccess)
    (noForward hasSingleLineMask usePreIssueMask : Bool)
    (memoryAccess : Access) (negated extended rounded : Bool) (mask : Option ParsedMask)
    (w : PEMemory.Width)
    (lowered : lowerParsedL1ToPE? expression = some access)
    (destinations : access.destinations =
      [ParsedOperand.mem memoryAccess negated extended rounded mask])
    (static : ParsedOperand.directDestinationBankWidth?
      (ParsedOperand.mem memoryAccess negated extended rounded mask) = some (PEMemory.Bank.lm1, w))
    (executed : executeParsedL1ToPEProducer (welcomeInitialState input) currentState expression
      noForward hasSingleLineMask usePreIssueMask = .ok next) :
    ∃ writes, next.peRegisters welcomePE =
        commitParsedMaskedWrites (currentState.peRegisters welcomePE) writes ∧
      (Lm1WritesDoubleCopy writes ∨ Lm1WritesNarrow writes) := by
  rw [executeParsedL1ToPEProducer, lowered] at executed
  exact executeParsedL1ToPEAtPEs_mem_lm1_shape (welcomeInitialState input) expression access
    hasSingleLineMask usePreIssueMask noForward memoryAccess negated extended rounded mask w
    destinations static
    (fun pe cycle => l1ToPEBusAt_welcomeInitialState input expression access pe cycle)
    (List.finRange 4096) (List.nodup_finRange 4096) (List.mem_finRange welcomePE)
    currentState next executed


/-- **The stage-level form.**  The L1BM-to-PE stage of a line with exactly one
L1ToPE producer row is that row's producer; hence the PE 0 shape of the stage is
the row shape of §5.  `executeParsedL1ToPEProducers_multiple_fail` shows that a
line with two L1ToPE rows cannot reach this stage successfully, so every
successful line falls into this single-row case or into the empty case. -/
theorem executeParsedL1ToPEProducers_mem_lm1_shape
    (input : ProofsLean.MNCore.PlusOne.Words) (currentState next : State)
    (expressions : List ParsedExpr) (expression : ParsedExpr) (access : ParsedL1ToPEAccess)
    (noForward hasSingleLineMask usePreIssueMask : Bool)
    (memoryAccess : Access) (negated extended rounded : Bool) (mask : Option ParsedMask)
    (w : PEMemory.Width)
    (lowered : lowerParsedL1ToPE? expression = some access)
    (destinations : access.destinations =
      [ParsedOperand.mem memoryAccess negated extended rounded mask])
    (static : ParsedOperand.directDestinationBankWidth?
      (ParsedOperand.mem memoryAccess negated extended rounded mask) = some (PEMemory.Bank.lm1, w))
    (filtered : expressions.filter parsedExprIsL1ToPEProducer = [expression])
    (executed : executeParsedL1ToPEProducers (welcomeInitialState input) currentState expressions
      noForward hasSingleLineMask usePreIssueMask = .ok next) :
    ∃ writes, next.peRegisters welcomePE =
        commitParsedMaskedWrites (currentState.peRegisters welcomePE) writes ∧
      (Lm1WritesDoubleCopy writes ∨ Lm1WritesNarrow writes) := by
  rw [executeParsedL1ToPEProducers, filtered] at executed
  dsimp only at executed
  exact executeParsedL1ToPEProducer_mem_lm1_shape input currentState next expression access
    noForward hasSingleLineMask usePreIssueMask memoryAccess negated extended rounded mask w
    lowered destinations static executed

/-! ## 6. What the line level still needs

`WelcomePEL1ToPEShapeObligation` is

```
∀ expressions, WelcomePEUnrefuted expressions →
  (expressions.map NormalizedExpr.toParsed).any parsedExprIsL1ToPEProducer = true →
  WelcomePEWriteShape expressions
```

and `WelcomePEWriteShape` is `double-copy ∨ narrow ∨ input-independent` for the
*whole line's* PE 0 file.  The row theorem above closes neither of the two
line-level gaps:

1. **The writer may be another row.**  `welcomeLm1Writer_unique` only forbids
   *two* `.lm1` writers.  A broadcast row can have no `.lm1` destination at all
   (only `.mem lm0` / `.bar` / `.nowrite`), in which case the line's `.lm1`
   writer is one of its other rows.  The obligation then has to analyse that
   other row (plain, immediate, matrix-read, MAU, ...), which is exactly the
   eight-family decomposition of `WelcomeWriterShape.lean`, not the broadcast
   row.  Conversely, when the broadcast row *does* have a `.lm1` destination it
   is the unique writer, and the remaining line-level step is the assembly:
   show that the four middle stages and the integer stage contribute no `.lm1`
   write, so that the line's commit is the broadcast row's commit.  The stage
   `.lm1` frames exist (`welcomePEStageLm1Frame`), but the integer stage's
   list-level `.lm1` provenance for a row list with no `.lm1` destination
   operand is still unproved (it is item (b) of `WelcomeL12Shape.lean` §10);
   with it, `welcomePEWriteShape_of_commit_shape` and the present row theorem
   would give the "broadcast row is the writer" case.
2. **The line-level decomposition.**  Even with (1), the obligation quantifies
   over the whole expression list; one needs the syntactic split
   `l1ToPE row :: other rows`, the stage filters, and the `writesUnique` bridge
   to identify the line's `.lm1` writes with the row's four writes.  The
   assembly skeleton exists (`welcomePE_line_stage_commit_unconditional`,
   `welcomePEWriteShape_of_commit_shape`), but its conclusion only exposes the
   concatenated write list, not the components needed to apply the row shape.

The `.l2bm` family is in the same position (its rows never write a PE bank), and
the remaining six family `Prop`s are unaffected by this module.

No `LowerBound 2` and no `Optimal` is claimed.
-/

end ProofsLean.MNCore
