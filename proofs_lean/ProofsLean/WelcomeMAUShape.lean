import ProofsLean.WelcomePlainStep

/-! # Row-level and line-level write shapes for the non-plain producer families

The plain integer-ALU class is discharged in `WelcomePlainStep.lean`.  This
module starts the non-plain half of `WelcomeValueBound.lean` §7.

## Why the per-family Props reduce to one row analysis

`WelcomePEWriteShape` constrains **every** `.lm1` destination of the whole
line's commit list.  A legal line has at most one `.lm1`-writing row
(`LegalParsedLine.writesUnique` through `welcomeLm1Writer_unique`), but the
family hypothesis of a Prop only says that *some* row of the family occurs; it
does not say that this row is the `.lm1` writer.  For example a
`matrixWrite` row never writes a PE register file at all
(`executeParsedMatrixWritesAtMABs_preserves_pe_state`), so in
`[matrixWrite .d src, alu ... → lm1 word]` the unique `.lm1` writer is the
ALU row.  A `.matrixRead` row may write `.mem lm1`, `.bar` or `.nowrite`, a
float `.mau` row may write `.mem lm1`, and a matrix `.mau` row writes PE
register files through `commitParsedMatrixMAUPEState`.

So all four family Props (and `WelcomePEOtherShapeObligation` itself) share one
missing library:

* **(row)** for every kind of unique `.lm1`-writing row, the shape of that row's
  prepared write list at the all-zero state;
* **(line)** the assembly that the whole line's `.lm1` commit is exactly the
  unique writer's `.lm1` part.

This module proves

* the zero-state matrix facts (`welcomeZeroMatrixStore`, `parsedMatrixReadBus`
  and `parsedOutputAfterFlush` are zero);
* the **row-level matrix-read shape**: the `.matrixRead` row's prepared writes
  at the all-zero state satisfy `Lm1WriteFacts w` for the row's static `.lm1`
  width and contain at most four `.lm1` writes, hence (with the count bound)
  either `Lm1WritesDoubleCopy` or `Lm1WritesNarrow`;
* the **matrix-write/matrix-MAU stage frames** needed by the line assembly.

The line-level assembly itself and the row shapes of the remaining kinds are
stated as named `Prop`s at the end of the file.  No `sorry`, no `admit`, no
`native_decide`, no new axioms.
-/

namespace ProofsLean.MNCore

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

open Issue
open PEMemory

/-! ## 0. The all-zero matrix store -/

/-- The matrix-register store at the all-zero initial state. -/
abbrev welcomeZeroMatrixStore : ParsedMatrixReadStore := fun _ _ _ _ => 0

theorem welcomeZero_matrixStore (group : Fin 4) (l2b : Fin 2) (l1b : Fin 8) :
    (welcomeInitialState welcomeZeroWords).matrixRegisters group l2b l1b =
      welcomeZeroMatrixStore := rfl

/-! ## 1. A zero matrix read bus -/

theorem doubleMatrixFaceFromPhysicalWords_zero :
    doubleMatrixFaceFromPhysicalWords (fun _ _ => (0 : BitVec 32)) = fun _ _ => 0 := by
  funext row column
  simp [doubleMatrixFaceFromPhysicalWords]

theorem doubleMatrixReadBus_zero (base pe cycle : Fin 4) :
    doubleMatrixReadBus (fun _ _ => 0) base pe cycle = (⟨0, 0⟩ : IntegerALU.Bus) := by
  simp [doubleMatrixReadBus]

theorem singleMatrixReadBus_zero (base : Fin 8) (pe cycle : Fin 4) :
    singleMatrixReadBus (fun _ _ => 0) base pe cycle = (⟨0, 0⟩ : IntegerALU.Bus) := by
  simp [singleMatrixReadBus]

theorem halfMatrixReadBus_zero (base : Fin 16) (pe cycle : Fin 4) :
    halfMatrixReadBus (fun _ _ => 0) base pe cycle = (⟨0, 0⟩ : IntegerALU.Bus) := by
  simp [halfMatrixReadBus, halfMatrixPhysicalElement]

theorem parsedMatrixReadBus_zero (accesses : ParsedMatrixReadAccesses)
    (context : ParsedIntegerContext) :
    parsedMatrixReadBus welcomeZeroMatrixStore accesses context = (⟨0, 0⟩ : IntegerALU.Bus) := by
  cases accesses with
  | mk precision sideY row targets =>
      cases precision <;>
        simp [parsedMatrixReadBus, welcomeZeroMatrixStore,
          doubleMatrixFaceFromPhysicalWords_zero, doubleMatrixReadBus,
          singleMatrixReadBus, halfMatrixReadBus, halfMatrixPhysicalElement]

theorem flushBus_zero (width : ProofsLean.MNCore.Masks.Width) (flags : BitVec 4) :
    ProofsLean.MNCore.Masks.flushBus width flags (⟨0, 0⟩ : IntegerALU.Bus) =
      (⟨0, 0⟩ : IntegerALU.Bus) := by
  cases width <;>
    simp [ProofsLean.MNCore.Masks.flushBus, ProofsLean.MNCore.Masks.halfMask,
      ProofsLean.MNCore.Masks.doubleMask]

theorem parsedOutputAfterFlush_zero (selection : Option PEWordSelection) :
    parsedOutputAfterFlush selection (⟨0, 0⟩ : IntegerALU.Bus) = (⟨0, 0⟩ : IntegerALU.Bus) := by
  cases selection with
  | none => rfl
  | some selected =>
      simp only [parsedOutputAfterFlush, parsedMaskLongLong]
      exact flushBus_zero _ _

theorem unpackALUBus_zero :
    unpackALUBus (⟨0, 0⟩ : IntegerALU.Bus) = fun _ => (0 : BitVec 32) := by
  funext index
  simp [unpackALUBus]

theorem unpackALUBus_zero_word_two (bound : 2 < 4) :
    (unpackALUBus (⟨0, 0⟩ : IntegerALU.Bus)) ⟨2, bound⟩ = 0 := by
  simp [unpackALUBus]

theorem isWelcomeCopy_zero_data (bus : WordBus) (zero : bus = fun _ => (0 : BitVec 32))
    (bound : 2 < 4) : IsWelcomeCopy (bus ⟨2, bound⟩) := by
  subst zero
  simpa using isWelcomeCopy_zero

/-! ## 2. The per-destination matrix-read target -/

/-- The matrix-read target of one destination operand.  This is the lambda of
`ParsedExpr.toDirectMatrixReadAccesses?` factored out, so that the positional
form of `List.mapM` can be applied to it. -/
def parsedMatrixReadTargetAt? (registers : ProofsLean.MNCore.Masks.RegisterFile)
    (directive : ParsedMaskDirective) (hasSingleLineMask : Bool)
    (context : ParsedIntegerContext) (target : ParsedOperand) : Option ParsedMatrixReadTarget :=
  match target with
  | .nowrite => some .noWrite
  | .mem .. => do
      let access ← ParsedOperand.toDirectMemoryDestination? target context.pe
        context.cycle context.bar0 context.bar1 context.tWord
      let selection ← ParsedOperand.resolveMemoryWriteSelection? target access.bank
        registers context.cycle directive hasSingleLineMask
      some (.memory access selection)
  | .bar lm1 .. => do
      let bank := if lm1 then PEMemory.Bank.lm1 else PEMemory.Bank.lm0
      let selection ← ParsedOperand.resolveMemoryWriteSelection? target bank
        registers context.cycle directive hasSingleLineMask
      some (.bar lm1 selection)
  | _ => none

theorem toDirectMatrixReadAccesses?_eq (expression : ParsedExpr)
    (precision : ParsedPrecision) (sideY : Bool) (width : Fin 5) (row : Fin (2 ^ 32))
    (op : expression.op = .matrixRead precision)
    (sources : expression.sources = [.matrix sideY width (some row)])
    (registers : ProofsLean.MNCore.Masks.RegisterFile)
    (directive : ParsedMaskDirective) (hasSingleLineMask : Bool)
    (context : ParsedIntegerContext) :
    ParsedExpr.toDirectMatrixReadAccesses? expression registers directive hasSingleLineMask context =
      (do
        let targets ← List.mapM (fun target => parsedMatrixReadTargetAt? registers directive
          hasSingleLineMask context target) expression.destinations
        some ⟨precision, sideY, row.val, targets⟩) := by
  rw [ParsedExpr.toDirectMatrixReadAccesses?, op, sources]
  rfl

theorem parsedMatrixReadTargetAt?_memory
    (registers : ProofsLean.MNCore.Masks.RegisterFile) (directive : ParsedMaskDirective)
    (hasSingleLineMask : Bool) (context : ParsedIntegerContext) (target : ParsedOperand)
    (access : DirectMemoryAccess) (selection : PEWordSelection)
    (lowered : parsedMatrixReadTargetAt? registers directive hasSingleLineMask context target =
      some (.memory access selection)) :
    ParsedOperand.toDirectMemoryDestination? target context.pe context.cycle context.bar0
      context.bar1 context.tWord = some access := by
  cases target with
  | mem access' neg ext rnd mask =>
      simp only [parsedMatrixReadTargetAt?] at lowered
      cases h : ParsedOperand.toDirectMemoryDestination?
        (ParsedOperand.mem access' neg ext rnd mask)
        context.pe context.cycle context.bar0 context.bar1 context.tWord with
      | none => simp [h] at lowered
      | some found =>
          simp only [h] at lowered
          cases h2 : ParsedOperand.resolveMemoryWriteSelection?
            (ParsedOperand.mem access' neg ext rnd mask) found.bank registers context.cycle
            directive hasSingleLineMask with
          | none => simp [h2] at lowered
          | some sel =>
              simp [h2] at lowered
              rw [lowered.1]
  | nowrite => simp [parsedMatrixReadTargetAt?] at lowered
  | bar lm1 width mask =>
      simp only [parsedMatrixReadTargetAt?] at lowered
      cases h : ParsedOperand.resolveMemoryWriteSelection? (ParsedOperand.bar lm1 width mask)
        (if lm1 = true then PEMemory.Bank.lm1 else PEMemory.Bank.lm0) registers context.cycle
        directive hasSingleLineMask <;> simp [h] at lowered
  | forward kind neg ext rnd => simp [parsedMatrixReadTargetAt?] at lowered
  | fixed value => simp [parsedMatrixReadTargetAt?] at lowered
  | omr entry mask => simp [parsedMatrixReadTargetAt?] at lowered
  | matrix side width row => simp [parsedMatrixReadTargetAt?] at lowered
  | l1bm width address => simp [parsedMatrixReadTargetAt?] at lowered
  | l2bm address l2b => simp [parsedMatrixReadTargetAt?] at lowered
  | dar value => simp [parsedMatrixReadTargetAt?] at lowered

theorem parsedMatrixReadTargetAt?_aligned
    (registers : ProofsLean.MNCore.Masks.RegisterFile) (directive : ParsedMaskDirective)
    (hasSingleLineMask : Bool) (context : ParsedIntegerContext) (target : ParsedOperand)
    (access : DirectMemoryAccess) (selection : PEWordSelection)
    (lowered : parsedMatrixReadTargetAt? registers directive hasSingleLineMask context target =
      some (.memory access selection)) :
    access.address.val % access.width.words = 0 := by
  have resolved := parsedMatrixReadTargetAt?_memory registers directive hasSingleLineMask
    context target access selection lowered
  exact parsedOperand_toDirectMemoryAccessMode_aligned target true context.pe context.cycle
    context.bar0 context.bar1 context.tWord access resolved

theorem parsedMatrixReadTargetAt?_width
    (registers : ProofsLean.MNCore.Masks.RegisterFile) (directive : ParsedMaskDirective)
    (hasSingleLineMask : Bool) (context : ParsedIntegerContext) (target : ParsedOperand)
    (access : DirectMemoryAccess) (selection : PEWordSelection)
    (lowered : parsedMatrixReadTargetAt? registers directive hasSingleLineMask context target =
      some (.memory access selection)) :
    ParsedOperand.directDestinationBankWidth? target = some (access.bank, access.width) := by
  have resolved := parsedMatrixReadTargetAt?_memory registers directive hasSingleLineMask
    context target access selection lowered
  have static := ParsedOperand.toDirectMemoryDestination?_bankWidth target context.pe
    context.cycle context.bar0 context.bar1 context.tWord
  rw [resolved] at static
  simpa using static.symm

/-! ## 3. `List.mapM` inversion over the destination list -/

theorem mapM_cons_inv {α β : Type} (f : α → Option β) (a : α) (rest : List α)
    (out : List β) (mapped : (a :: rest).mapM f = some out) :
    ∃ b bs, f a = some b ∧ rest.mapM f = some bs ∧ out = b :: bs := by
  simp only [List.mapM_cons] at mapped
  cases h : f a with
  | none => simp [h] at mapped
  | some b =>
      cases h2 : rest.mapM f with
      | none => simp [h, h2] at mapped
      | some bs =>
          simp [h, h2] at mapped
          exact ⟨b, bs, rfl, rfl, mapped.symm⟩

theorem mapM_cons_some {α β : Type} (f : α → Option β) (a : α) (rest : List α)
    (b : β) (bs : List β) (head : f a = some b) (tail : rest.mapM f = some bs) :
    (a :: rest).mapM f = some (b :: bs) := by
  simp [List.mapM_cons, head, tail]


/-! ## 4. The `LM1` facts of a prepared write list -/

/-- Every `.lm1` destination of the list is a `w`-wide write, its `.double` case
is 4-aligned, and its third data word is a copy. -/
def Lm1WriteFacts (w : PEMemory.Width) (writes : List PreparedParsedMaskedWrite) : Prop :=
  ∀ write ∈ writes, ∀ (width : PEMemory.Width) (address : Fin PEMemory.Bank.lm1.capacity),
    write.destination = some ⟨PEMemory.Bank.lm1, width, address⟩ →
      width = w ∧
        (width = PEMemory.Width.double → address.val % 4 = 0) ∧
        (∀ bound : 2 < 4, IsWelcomeCopy (write.data ⟨2, bound⟩))

theorem lm1WriteFacts_nil (w : PEMemory.Width) : Lm1WriteFacts w [] := by
  intro write member
  simp at member

theorem lm1WriteFacts_append (w : PEMemory.Width) (a b : List PreparedParsedMaskedWrite)
    (ha : Lm1WriteFacts w a) (hb : Lm1WriteFacts w b) : Lm1WriteFacts w (a ++ b) := by
  intro write member width address destination
  rcases List.mem_append.mp member with earlier | later
  · exact ha write earlier width address destination
  · exact hb write later width address destination

theorem lm1WriteFacts_doubleCopy (writes : List PreparedParsedMaskedWrite)
    (facts : Lm1WriteFacts PEMemory.Width.double writes) : Lm1WritesDoubleCopy writes := by
  intro write member width address data selection destination dataEq selectionEq
  subst dataEq
  subst selectionEq
  obtain ⟨widthEq, aligned, copy⟩ := facts write member width address destination
  subst widthEq
  exact ⟨rfl, aligned rfl, copy⟩

theorem lm1WriteFacts_narrow (writes : List PreparedParsedMaskedWrite) (w : PEMemory.Width)
    (facts : Lm1WriteFacts w writes) (notDouble : w ≠ PEMemory.Width.double)
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
    obtain ⟨widthEq, _, _⟩ := facts write writeMem width address destination
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

/-! ## 5. The writes prepared from a target list -/

def parsedMatrixReadTargetIsLm1Memory : ParsedMatrixReadTarget → Bool
  | .memory access _ => access.bank == PEMemory.Bank.lm1
  | _ => false

theorem isLm1Memory_true (target : ParsedMatrixReadTarget)
    (isLm1 : parsedMatrixReadTargetIsLm1Memory target = true) :
    ∃ (access : DirectMemoryAccess) (selection : PEWordSelection),
      target = .memory access selection ∧ access.bank = PEMemory.Bank.lm1 := by
  cases target with
  | memory access selection =>
      refine ⟨access, selection, rfl, ?_⟩
      simpa [parsedMatrixReadTargetIsLm1Memory] using isLm1
  | noWrite => simp [parsedMatrixReadTargetIsLm1Memory] at isLm1
  | bar lm1 selection => simp [parsedMatrixReadTargetIsLm1Memory] at isLm1

theorem prepareParsedMatrixReadTargets_lm1Count (targets : List ParsedMatrixReadTarget)
    (output : IntegerALU.Bus) :
    ∀ (writes : List PreparedParsedMaskedWrite) (barUpdates : List (Bool × BitVec 12)),
      prepareParsedMatrixReadTargets targets output = .ok (writes, barUpdates) →
      (writes.filter PreparedParsedMaskedWrite.isLm1Write).length =
        (targets.filter parsedMatrixReadTargetIsLm1Memory).length := by
  induction targets with
  | nil =>
      intro writes bars prepared
      simp only [prepareParsedMatrixReadTargets, StepResult.ok.injEq, Prod.mk.injEq] at prepared
      obtain ⟨rfl, rfl⟩ := prepared
      rfl
  | cons target rest ih =>
      intro writes bars prepared
      cases target with
      | noWrite =>
          simp only [prepareParsedMatrixReadTargets] at prepared
          cases h : prepareParsedMatrixReadTargets rest output with
          | failure => simp [h] at prepared
          | unknown => simp [h] at prepared
          | ok result =>
              obtain ⟨restWrites, restBars⟩ := result
              simp only [h, StepResult.ok.injEq, Prod.mk.injEq] at prepared
              obtain ⟨rfl, rfl⟩ := prepared
              have ih' := ih restWrites restBars h
              simp [PreparedParsedMaskedWrite.isLm1Write, parsedMatrixReadTargetIsLm1Memory, ih']
      | memory access selection =>
          simp only [prepareParsedMatrixReadTargets] at prepared
          cases h : prepareParsedMatrixReadTargets rest output with
          | failure => simp [h] at prepared
          | unknown => simp [h] at prepared
          | ok result =>
              obtain ⟨restWrites, restBars⟩ := result
              simp only [h, StepResult.ok.injEq, Prod.mk.injEq] at prepared
              obtain ⟨rfl, rfl⟩ := prepared
              have ih' := ih restWrites restBars h
              by_cases bank : access.bank = PEMemory.Bank.lm1
              · simp [PreparedParsedMaskedWrite.isLm1Write,
                  parsedMatrixReadTargetIsLm1Memory, bank, ih']
              · simp [PreparedParsedMaskedWrite.isLm1Write,
                  parsedMatrixReadTargetIsLm1Memory, bank, ih']
      | bar lm1 selection =>
          simp only [prepareParsedMatrixReadTargets] at prepared
          cases h : prepareParsedMatrixReadTargets rest output with
          | failure => simp [h] at prepared
          | unknown => simp [h] at prepared
          | ok result =>
              obtain ⟨restWrites, restBars⟩ := result
              simp only [h, StepResult.ok.injEq, Prod.mk.injEq] at prepared
              obtain ⟨rfl, rfl⟩ := prepared
              have ih' := ih restWrites restBars h
              simp [parsedMatrixReadTargetIsLm1Memory, ih']

theorem prepareParsedMatrixReadTargets_data (targets : List ParsedMatrixReadTarget)
    (output : IntegerALU.Bus) :
    ∀ (writes : List PreparedParsedMaskedWrite) (barUpdates : List (Bool × BitVec 12)),
      prepareParsedMatrixReadTargets targets output = .ok (writes, barUpdates) →
      ∀ write ∈ writes, write.data = unpackALUBus output := by
  induction targets with
  | nil =>
      intro writes bars prepared
      simp only [prepareParsedMatrixReadTargets, StepResult.ok.injEq, Prod.mk.injEq] at prepared
      obtain ⟨rfl, rfl⟩ := prepared
      intro write member
      simp at member
  | cons target rest ih =>
      intro writes bars prepared
      cases target with
      | noWrite =>
          simp only [prepareParsedMatrixReadTargets] at prepared
          cases h : prepareParsedMatrixReadTargets rest output with
          | failure => simp [h] at prepared
          | unknown => simp [h] at prepared
          | ok result =>
              obtain ⟨restWrites, restBars⟩ := result
              simp only [h, StepResult.ok.injEq, Prod.mk.injEq] at prepared
              obtain ⟨rfl, rfl⟩ := prepared
              intro write member
              rcases List.mem_cons.mp member with rfl | later
              · rfl
              · exact ih restWrites restBars h write later
      | memory access selection =>
          simp only [prepareParsedMatrixReadTargets] at prepared
          cases h : prepareParsedMatrixReadTargets rest output with
          | failure => simp [h] at prepared
          | unknown => simp [h] at prepared
          | ok result =>
              obtain ⟨restWrites, restBars⟩ := result
              simp only [h, StepResult.ok.injEq, Prod.mk.injEq] at prepared
              obtain ⟨rfl, rfl⟩ := prepared
              intro write member
              rcases List.mem_cons.mp member with rfl | later
              · rfl
              · exact ih restWrites restBars h write later
      | bar lm1 selection =>
          simp only [prepareParsedMatrixReadTargets] at prepared
          cases h : prepareParsedMatrixReadTargets rest output with
          | failure => simp [h] at prepared
          | unknown => simp [h] at prepared
          | ok result =>
              obtain ⟨restWrites, restBars⟩ := result
              simp only [h, StepResult.ok.injEq, Prod.mk.injEq] at prepared
              obtain ⟨rfl, rfl⟩ := prepared
              intro write member
              exact ih restWrites restBars h write member


theorem prepareParsedMatrixReadTargets_lm1Facts (targets : List ParsedMatrixReadTarget)
    (output : IntegerALU.Bus) (w : PEMemory.Width)
    (targetFacts : ∀ target ∈ targets, ∀ (access : DirectMemoryAccess)
      (selection : PEWordSelection), target = .memory access selection →
      access.bank = PEMemory.Bank.lm1 →
        access.width = w ∧ (access.width = PEMemory.Width.double →
          access.address.val % 4 = 0))
    (dataCopy : ∀ bound : 2 < 4, IsWelcomeCopy ((unpackALUBus output) ⟨2, bound⟩)) :
    ∀ (writes : List PreparedParsedMaskedWrite) (barUpdates : List (Bool × BitVec 12)),
      prepareParsedMatrixReadTargets targets output = .ok (writes, barUpdates) →
      Lm1WriteFacts w writes := by
  induction targets with
  | nil =>
      intro writes bars prepared
      simp only [prepareParsedMatrixReadTargets, StepResult.ok.injEq, Prod.mk.injEq] at prepared
      obtain ⟨rfl, rfl⟩ := prepared
      exact lm1WriteFacts_nil w
  | cons target rest ih =>
      intro writes bars prepared
      cases target with
      | noWrite =>
          simp only [prepareParsedMatrixReadTargets] at prepared
          cases h : prepareParsedMatrixReadTargets rest output with
          | failure => simp [h] at prepared
          | unknown => simp [h] at prepared
          | ok result =>
              obtain ⟨restWrites, restBars⟩ := result
              simp only [h, StepResult.ok.injEq, Prod.mk.injEq] at prepared
              obtain ⟨rfl, rfl⟩ := prepared
              have ih' := ih (fun t mem => targetFacts t (List.mem_cons_of_mem _ mem))
                restWrites restBars h
              intro write member width address destination
              rcases List.mem_cons.mp member with rfl | later
              · simp at destination
              · exact ih' write later width address destination
      | memory access selection =>
          simp only [prepareParsedMatrixReadTargets] at prepared
          cases h : prepareParsedMatrixReadTargets rest output with
          | failure => simp [h] at prepared
          | unknown => simp [h] at prepared
          | ok result =>
              obtain ⟨restWrites, restBars⟩ := result
              simp only [h, StepResult.ok.injEq, Prod.mk.injEq] at prepared
              obtain ⟨rfl, rfl⟩ := prepared
              have ih' := ih (fun t mem => targetFacts t (List.mem_cons_of_mem _ mem))
                restWrites restBars h
              intro write member width address destination
              rcases List.mem_cons.mp member with rfl | later
              · simp only [Option.some.injEq] at destination
                cases destination
                obtain ⟨widthEq, aligned⟩ := targetFacts
                  (.memory ⟨PEMemory.Bank.lm1, width, address⟩ selection) (by simp)
                  ⟨PEMemory.Bank.lm1, width, address⟩ selection rfl rfl
                refine ⟨widthEq, aligned, ?_⟩
                exact dataCopy
              · exact ih' write later width address destination
      | bar lm1 selection =>
          simp only [prepareParsedMatrixReadTargets] at prepared
          cases h : prepareParsedMatrixReadTargets rest output with
          | failure => simp [h] at prepared
          | unknown => simp [h] at prepared
          | ok result =>
              obtain ⟨restWrites, restBars⟩ := result
              simp only [h, StepResult.ok.injEq, Prod.mk.injEq] at prepared
              obtain ⟨rfl, rfl⟩ := prepared
              have ih' := ih (fun t mem => targetFacts t (List.mem_cons_of_mem _ mem))
                restWrites restBars h
              exact ih'

/-! ## 6. `List.mapM` transport from destinations to targets -/

theorem mapM_targets_lm1Facts (f : ParsedOperand → Option ParsedMatrixReadTarget)
    (P : DirectMemoryAccess → Prop) :
    ∀ (destinations : List ParsedOperand) (targets : List ParsedMatrixReadTarget),
      destinations.mapM f = some targets →
      (∀ d ∈ destinations, ∀ (access : DirectMemoryAccess) (selection : PEWordSelection),
        f d = some (.memory access selection) → access.bank = PEMemory.Bank.lm1 → P access) →
      ∀ target ∈ targets, ∀ (access : DirectMemoryAccess) (selection : PEWordSelection),
        target = .memory access selection → access.bank = PEMemory.Bank.lm1 → P access := by
  intro destinations
  induction destinations with
  | nil =>
      intro targets mapped facts target member
      simp only [List.mapM_nil] at mapped
      cases mapped
      simp at member
  | cons d rest ih =>
      intro targets mapped facts target member
      obtain ⟨b, bs, head, tail, rfl⟩ := mapM_cons_inv f d rest targets mapped
      rcases List.mem_cons.mp member with same | later
      · subst same
        intro access selection targetEq bank
        exact facts d (by simp) access selection (by rw [head, targetEq]) bank
      · exact ih bs tail (fun d' mem' => facts d' (List.mem_cons_of_mem _ mem'))
          target later

theorem mapM_targets_lm1Count (f : ParsedOperand → Option ParsedMatrixReadTarget) :
    ∀ (destinations : List ParsedOperand) (targets : List ParsedMatrixReadTarget),
      destinations.mapM f = some targets →
      (∀ d ∈ destinations, ∀ (access : DirectMemoryAccess) (selection : PEWordSelection),
        f d = some (.memory access selection) → access.bank = PEMemory.Bank.lm1 →
          ParsedOperand.isLm1MemoryDestination d = true) →
      (targets.filter parsedMatrixReadTargetIsLm1Memory).length ≤
        (destinations.filter ParsedOperand.isLm1MemoryDestination).length := by
  intro destinations
  induction destinations with
  | nil =>
      intro targets mapped facts
      simp only [List.mapM_nil] at mapped
      cases mapped
      simp
  | cons d rest ih =>
      intro targets mapped facts
      obtain ⟨b, bs, head, tail, rfl⟩ := mapM_cons_inv f d rest targets mapped
      have ih' := ih bs tail (fun d' mem' => facts d' (List.mem_cons_of_mem _ mem'))
      cases hb : parsedMatrixReadTargetIsLm1Memory b with
      | false =>
          simp only [List.filter_cons, hb, Bool.false_eq_true, ite_false]
          refine le_trans ih' ?_
          cases hd : ParsedOperand.isLm1MemoryDestination d <;> simp
      | true =>
          obtain ⟨access, selection, rfl, bank⟩ := isLm1Memory_true b hb
          have dLm1 := facts d (by simp) access selection (by rw [head]) bank
          have leftEq : (List.filter parsedMatrixReadTargetIsLm1Memory
              (ParsedMatrixReadTarget.memory access selection :: bs)).length =
              (List.filter parsedMatrixReadTargetIsLm1Memory bs).length + 1 := by
            simp [List.filter_cons, hb]
          have rightEq : (List.filter ParsedOperand.isLm1MemoryDestination
              (d :: rest)).length =
              (List.filter ParsedOperand.isLm1MemoryDestination rest).length + 1 := by
            simp [List.filter_cons, dLm1]
          rw [leftEq, rightEq]
          omega


/-! ## 7. One cycle of a matrix-read row -/

theorem prepareParsedMatrixReadCycle_lm1Facts
    (files : IntegerRegisterFiles) (slots : ProofsLean.MNCore.Forwarding.Slots)
    (store : ParsedMatrixReadStore) (expression : ParsedExpr) (directive : ParsedMaskDirective)
    (hasSingleLineMask noForward : Bool) (context : ParsedIntegerContext)
    (precision : ParsedPrecision) (sideY : Bool) (width : Fin 5) (row : Fin (2 ^ 32))
    (op : expression.op = .matrixRead precision)
    (sources : expression.sources = [.matrix sideY width (some row)])
    (accesses : ParsedMatrixReadAccesses) (flushSelection : Option PEWordSelection)
    (w : PEMemory.Width)
    (nodup : (expression.toIssueExpr 0).writeBanks.Nodup)
    (zeroStore : store = welcomeZeroMatrixStore)
    (staticWidth : ∀ (d : ParsedOperand), d ∈ expression.destinations →
      ∀ v : PEMemory.Width, ParsedOperand.directDestinationBankWidth? d =
        some (PEMemory.Bank.lm1, v) → v = w)
    (lowered : ParsedExpr.toDirectMatrixReadAccesses? expression files.maskRegisters directive
      hasSingleLineMask context = some accesses)
    (flushResolved : resolveFlushSelection? expression.flush files.maskRegisters context.cycle =
      some flushSelection)
    (writes : List PreparedParsedMaskedWrite)
    (nextSlots : ProofsLean.MNCore.Forwarding.Slots)
    (bars : List (Bool × BitVec 12))
    (prepared : prepareParsedMatrixReadCycle files slots store expression directive
      hasSingleLineMask noForward context = .ok (writes, nextSlots, bars)) :
    Lm1WriteFacts w writes ∧
      (writes.filter PreparedParsedMaskedWrite.isLm1Write).length ≤ 1 := by
  have targetsEq : expression.destinations.mapM (fun target =>
      parsedMatrixReadTargetAt? files.maskRegisters directive hasSingleLineMask context target) =
        some accesses.targets := by
    have bridge := (toDirectMatrixReadAccesses?_eq expression precision sideY width row op
      sources files.maskRegisters directive hasSingleLineMask context).symm
    rw [lowered] at bridge
    have bridge' : Option.bind
        (List.mapM (fun target => parsedMatrixReadTargetAt? files.maskRegisters directive
          hasSingleLineMask context target) expression.destinations)
        (fun targets => some (⟨precision, sideY, row.val, targets⟩ : ParsedMatrixReadAccesses)) =
          some accesses := bridge
    simp only [Option.bind_eq_some_iff, Option.some.injEq] at bridge'
    obtain ⟨targets, targetsMapped, accessesEq⟩ := bridge'
    rw [← accessesEq]
    exact targetsMapped
  have prepared' : prepareParsedMatrixReadTargets accesses.targets
      (parsedOutputAfterFlush flushSelection
        (parsedMatrixReadBus store accesses context)) = .ok (writes, bars) := by
    unfold prepareParsedMatrixReadCycle at prepared
    rw [lowered, flushResolved] at prepared
    simp only at prepared
    cases h : prepareParsedMatrixReadTargets accesses.targets
        (parsedOutputAfterFlush flushSelection
          (parsedMatrixReadBus store accesses context)) with
    | failure => simp [h] at prepared
    | unknown => simp [h] at prepared
    | ok result =>
        obtain ⟨doneWrites, doneBars⟩ := result
        rw [h] at prepared
        simp only [StepResult.ok.injEq, Prod.mk.injEq] at prepared ⊢
        exact ⟨prepared.1, prepared.2.2⟩
  have dataZero : unpackALUBus (parsedOutputAfterFlush flushSelection
      (parsedMatrixReadBus store accesses context)) = fun _ => (0 : BitVec 32) := by
    rw [zeroStore, parsedMatrixReadBus_zero, parsedOutputAfterFlush_zero, unpackALUBus_zero]
  have dataCopy : ∀ bound : 2 < 4,
      IsWelcomeCopy ((unpackALUBus (parsedOutputAfterFlush flushSelection
        (parsedMatrixReadBus store accesses context))) ⟨2, bound⟩) := by
    rw [dataZero]
    intro bound
    exact isWelcomeCopy_zero
  have destFacts : ∀ d ∈ expression.destinations, ∀ (access : DirectMemoryAccess)
      (selection : PEWordSelection),
      parsedMatrixReadTargetAt? files.maskRegisters directive hasSingleLineMask context d =
        some (.memory access selection) →
      access.bank = PEMemory.Bank.lm1 →
        access.width = w ∧ (access.width = PEMemory.Width.double →
          access.address.val % 4 = 0) := by
    intro d hd access selection targetLowered bank
    have widthPair := parsedMatrixReadTargetAt?_width files.maskRegisters directive
      hasSingleLineMask context d access selection targetLowered
    rw [bank] at widthPair
    refine ⟨staticWidth d hd access.width widthPair, ?_⟩
    intro isDouble
    have aligned := parsedMatrixReadTargetAt?_aligned files.maskRegisters directive
      hasSingleLineMask context d access selection targetLowered
    rw [isDouble] at aligned
    simpa [PEMemory.Width.words] using aligned
  have targetFacts := mapM_targets_lm1Facts
    (fun target => parsedMatrixReadTargetAt? files.maskRegisters directive hasSingleLineMask
      context target)
    (fun access => access.width = w ∧ (access.width = PEMemory.Width.double →
      access.address.val % 4 = 0))
    expression.destinations accesses.targets targetsEq destFacts
  have facts := prepareParsedMatrixReadTargets_lm1Facts accesses.targets
    (parsedOutputAfterFlush flushSelection (parsedMatrixReadBus store accesses context))
    w targetFacts dataCopy writes bars prepared'
  have countEq := prepareParsedMatrixReadTargets_lm1Count accesses.targets
    (parsedOutputAfterFlush flushSelection (parsedMatrixReadBus store accesses context))
    writes bars prepared'
  have inverse : ∀ d ∈ expression.destinations, ∀ (access : DirectMemoryAccess)
      (selection : PEWordSelection),
      parsedMatrixReadTargetAt? files.maskRegisters directive hasSingleLineMask context d =
        some (.memory access selection) → access.bank = PEMemory.Bank.lm1 →
        ParsedOperand.isLm1MemoryDestination d = true := by
    intro d hd access selection targetLowered bank
    have widthPair := parsedMatrixReadTargetAt?_width files.maskRegisters directive
      hasSingleLineMask context d access selection targetLowered
    rw [bank] at widthPair
    exact directDestinationBankWidth_isLm1 d access.width widthPair
  have countLe := mapM_targets_lm1Count
    (fun target => parsedMatrixReadTargetAt? files.maskRegisters directive hasSingleLineMask
      context target)
    expression.destinations accesses.targets targetsEq inverse
  have bound := lm1Destinations_count_le_one expression 0 nodup
  refine ⟨facts, ?_⟩
  omega


theorem prepareParsedMatrixReadCycle_ok_inv
    (files : IntegerRegisterFiles) (slots : ProofsLean.MNCore.Forwarding.Slots)
    (store : ParsedMatrixReadStore) (expression : ParsedExpr) (directive : ParsedMaskDirective)
    (hasSingleLineMask noForward : Bool) (context : ParsedIntegerContext)
    (writes : List PreparedParsedMaskedWrite)
    (nextSlots : ProofsLean.MNCore.Forwarding.Slots) (bars : List (Bool × BitVec 12))
    (prepared : prepareParsedMatrixReadCycle files slots store expression directive
      hasSingleLineMask noForward context = .ok (writes, nextSlots, bars)) :
    ∃ (accesses : ParsedMatrixReadAccesses) (flushSelection : Option PEWordSelection),
      ParsedExpr.toDirectMatrixReadAccesses? expression files.maskRegisters directive
        hasSingleLineMask context = some accesses ∧
      resolveFlushSelection? expression.flush files.maskRegisters context.cycle =
        some flushSelection := by
  unfold prepareParsedMatrixReadCycle at prepared
  split at prepared
  · simp at prepared
  · rename_i lowered
    split at prepared
    · simp at prepared
    · rename_i flushResolved
      simp only at prepared
      split at prepared
      · simp at prepared
      · simp at prepared
      · simp only [StepResult.ok.injEq, Prod.mk.injEq] at prepared
        obtain ⟨rfl, _, rfl⟩ := prepared
        exact ⟨_, _, lowered, flushResolved⟩

/-! ## 8. The four-cycle fold -/

theorem prepareParsedMatrixReadCycles_lm1Facts
    (files : IntegerRegisterFiles) (store : ParsedMatrixReadStore) (expression : ParsedExpr)
    (directive : ParsedMaskDirective) (hasSingleLineMask noForward : Bool)
    (context : ParsedIntegerContext) (cycles : List (Fin 4)) (w : PEMemory.Width)
    (stepFacts : ∀ (cycle : Fin 4), cycle ∈ cycles →
      ∀ (slots : ProofsLean.MNCore.Forwarding.Slots)
        (cycleWrites : List PreparedParsedMaskedWrite)
        (cycleSlots : ProofsLean.MNCore.Forwarding.Slots)
        (cycleBars : List (Bool × BitVec 12)),
        prepareParsedMatrixReadCycle files slots store expression directive hasSingleLineMask
          noForward { context with cycle := cycle } = .ok (cycleWrites, cycleSlots, cycleBars) →
        Lm1WriteFacts w cycleWrites ∧
          (cycleWrites.filter PreparedParsedMaskedWrite.isLm1Write).length ≤ 1) :
    ∀ (writes : List PreparedParsedMaskedWrite)
      (slots : ProofsLean.MNCore.Forwarding.Slots) (bars : List (Bool × BitVec 12))
      (final : List PreparedParsedMaskedWrite)
      (finalSlots : ProofsLean.MNCore.Forwarding.Slots)
      (finalBars : List (Bool × BitVec 12)),
      (writes.filter PreparedParsedMaskedWrite.isLm1Write).length + cycles.length ≤ 4 →
      Lm1WriteFacts w writes →
      prepareParsedMatrixReadCycles files store expression directive hasSingleLineMask
        noForward context cycles writes slots bars = .ok (final, finalSlots, finalBars) →
      Lm1WriteFacts w final ∧
        (final.filter PreparedParsedMaskedWrite.isLm1Write).length ≤ 4 := by
  induction cycles with
  | nil =>
      intro writes slots bars final finalSlots finalBars bound facts prepared
      simp only [prepareParsedMatrixReadCycles, StepResult.ok.injEq, Prod.mk.injEq] at prepared
      obtain ⟨rfl, rfl, rfl⟩ := prepared
      refine ⟨facts, ?_⟩
      simpa using bound
  | cons cycle rest ih =>
      intro writes slots bars final finalSlots finalBars bound facts prepared
      have cycleBound : cycle ∈ (cycle :: rest) := by simp
      have restBound : ∀ c, c ∈ rest → c ∈ (cycle :: rest) := fun c mem =>
        List.mem_cons_of_mem _ mem
      simp only [prepareParsedMatrixReadCycles] at prepared
      cases head : prepareParsedMatrixReadCycle files slots store expression directive
          hasSingleLineMask noForward { context with cycle := cycle } with
      | failure => simp [head] at prepared
      | unknown => simp [head] at prepared
      | ok result =>
          obtain ⟨cycleWrites, cycleSlots, cycleBars⟩ := result
          simp only [head] at prepared
          obtain ⟨cycleFacts, cycleCount⟩ := stepFacts cycle cycleBound slots cycleWrites
            cycleSlots cycleBars head
          have nextFacts : Lm1WriteFacts w (writes ++ cycleWrites) :=
            lm1WriteFacts_append w writes cycleWrites facts cycleFacts
          have nextBound : ((writes ++ cycleWrites).filter
              PreparedParsedMaskedWrite.isLm1Write).length + rest.length ≤ 4 := by
            rw [List.filter_append, List.length_append]
            have : (cycleWrites.filter PreparedParsedMaskedWrite.isLm1Write).length ≤ 1 :=
              cycleCount
            simp only [List.length_cons] at bound
            omega
          exact ih (fun c mem => stepFacts c (restBound c mem)) (writes ++ cycleWrites)
            cycleSlots (bars ++ cycleBars) final finalSlots finalBars nextBound nextFacts prepared


/-! ## 9. The row-level shape of a `.matrixRead` row at the all-zero state -/

theorem prepareParsedMatrixReadExprCycles_lm1Facts
    (expression : ParsedExpr) (precision : ParsedPrecision) (sideY : Bool)
    (width : Fin 5) (row : Fin (2 ^ 32))
    (op : expression.op = .matrixRead precision)
    (sources : expression.sources = [.matrix sideY width (some row)])
    (directive : ParsedMaskDirective) (hasSingleLineMask noForward : Bool)
    (initialSlots : ProofsLean.MNCore.Forwarding.Slots)
    (context : ParsedIntegerContext) (w : PEMemory.Width)
    (nodup : (expression.toIssueExpr 0).writeBanks.Nodup)
    (staticWidth : ∀ (d : ParsedOperand), d ∈ expression.destinations →
      ∀ v : PEMemory.Width, ParsedOperand.directDestinationBankWidth? d =
        some (PEMemory.Bank.lm1, v) → v = w)
    (writes : List PreparedParsedMaskedWrite)
    (slots : ProofsLean.MNCore.Forwarding.Slots) (bars : List (Bool × BitVec 12))
    (prepared : prepareParsedMatrixReadExprCycles welcomeZeroFiles initialSlots
      welcomeZeroMatrixStore expression directive hasSingleLineMask noForward context =
        .ok (writes, slots, bars)) :
    Lm1WriteFacts w writes ∧
      (writes.filter PreparedParsedMaskedWrite.isLm1Write).length ≤ 4 := by
  refine prepareParsedMatrixReadCycles_lm1Facts welcomeZeroFiles welcomeZeroMatrixStore
    expression directive hasSingleLineMask noForward context parsedMatrixReadCycles w
    ?stepFacts [] initialSlots [] writes slots bars ?bound (lm1WriteFacts_nil w) ?prepared
  · intro cycle member slots cycleWrites cycleSlots cycleBars head
    obtain ⟨accesses, flushSelection, lowered, flushResolved⟩ :=
      prepareParsedMatrixReadCycle_ok_inv welcomeZeroFiles slots welcomeZeroMatrixStore
        expression directive hasSingleLineMask noForward { context with cycle := cycle }
        cycleWrites cycleSlots cycleBars head
    exact prepareParsedMatrixReadCycle_lm1Facts welcomeZeroFiles slots welcomeZeroMatrixStore
      expression directive hasSingleLineMask noForward { context with cycle := cycle }
      precision sideY width row op sources accesses flushSelection w nodup rfl staticWidth
      lowered flushResolved cycleWrites cycleSlots cycleBars head
  · simp [parsedMatrixReadCycles]
  · simpa [prepareParsedMatrixReadExprCycles] using prepared

/-- **The row-level shape of a `.matrixRead` row at the all-zero state.**  The
four cycle writes of the row either are all copied `.double` blocks or fit in
four narrow windows. -/
theorem prepareParsedMatrixReadExprCycles_zeroShape
    (expression : ParsedExpr) (precision : ParsedPrecision) (sideY : Bool)
    (width : Fin 5) (row : Fin (2 ^ 32))
    (op : expression.op = .matrixRead precision)
    (sources : expression.sources = [.matrix sideY width (some row)])
    (directive : ParsedMaskDirective) (hasSingleLineMask noForward : Bool)
    (initialSlots : ProofsLean.MNCore.Forwarding.Slots)
    (context : ParsedIntegerContext) (w : PEMemory.Width)
    (nodup : (expression.toIssueExpr 0).writeBanks.Nodup)
    (staticWidth : ∀ (d : ParsedOperand), d ∈ expression.destinations →
      ∀ v : PEMemory.Width, ParsedOperand.directDestinationBankWidth? d =
        some (PEMemory.Bank.lm1, v) → v = w)
    (writes : List PreparedParsedMaskedWrite)
    (slots : ProofsLean.MNCore.Forwarding.Slots) (bars : List (Bool × BitVec 12))
    (prepared : prepareParsedMatrixReadExprCycles welcomeZeroFiles initialSlots
      welcomeZeroMatrixStore expression directive hasSingleLineMask noForward context =
        .ok (writes, slots, bars)) :
    Lm1WritesDoubleCopy writes ∨ Lm1WritesNarrow writes := by
  obtain ⟨facts, count⟩ := prepareParsedMatrixReadExprCycles_lm1Facts expression precision
    sideY width row op sources directive hasSingleLineMask noForward initialSlots context w
    nodup staticWidth writes slots bars prepared
  by_cases isDouble : w = PEMemory.Width.double
  · left
    rw [isDouble] at facts
    exact lm1WriteFacts_doubleCopy writes facts
  · right
    exact lm1WriteFacts_narrow writes w facts isDouble count

/-! ## 10. The static `.lm1` width of a row -/

def lm1StaticWidth (expression : ParsedExpr) : Option PEMemory.Width :=
  ((expression.destinations.filter ParsedOperand.isLm1MemoryDestination).filterMap
    (fun d => (ParsedOperand.directDestinationBankWidth? d).map (fun pair => pair.2))).head?

theorem filterMap_length_le {α β : Type} (f : α → Option β) (l : List α) :
    (l.filterMap f).length ≤ l.length := by
  induction l with
  | nil => simp
  | cons a rest ih =>
      simp only [List.filterMap_cons]
      cases f a <;> simp <;> omega

theorem lm1StaticWidth_eq (expression : ParsedExpr)
    (nodup : (expression.toIssueExpr 0).writeBanks.Nodup)
    (d : ParsedOperand) (hd : d ∈ expression.destinations)
    (v : PEMemory.Width)
    (pair : ParsedOperand.directDestinationBankWidth? d = some (PEMemory.Bank.lm1, v)) :
    lm1StaticWidth expression = some v := by
  have isLm1 := directDestinationBankWidth_isLm1 d v pair
  have member : d ∈ expression.destinations.filter ParsedOperand.isLm1MemoryDestination :=
    List.mem_filter.mpr ⟨hd, isLm1⟩
  have valueMem : v ∈ (expression.destinations.filter
      ParsedOperand.isLm1MemoryDestination).filterMap
        (fun item => (ParsedOperand.directDestinationBankWidth? item).map
          (fun pair => pair.2)) :=
    List.mem_filterMap.mpr ⟨d, member, by rw [pair]; rfl⟩
  have countLe := lm1Destinations_count_le_one expression 0 nodup
  have lengthLe : ((expression.destinations.filter
      ParsedOperand.isLm1MemoryDestination).filterMap
        (fun item => (ParsedOperand.directDestinationBankWidth? item).map
          (fun pair => pair.2))).length ≤ 1 :=
    le_trans (filterMap_length_le _ _) countLe
  obtain ⟨w, singleton⟩ := List.length_eq_one_iff.mp
    (le_antisymm lengthLe (List.length_pos_iff_exists_mem.mpr ⟨v, valueMem⟩))
  have same : w = v := by
    rw [singleton] at valueMem
    have vw : v = w := by simpa using valueMem
    exact vw.symm
  unfold lm1StaticWidth
  rw [singleton]
  simp [same]

theorem lm1StaticWidth_spec (expression : ParsedExpr)
    (nodup : (expression.toIssueExpr 0).writeBanks.Nodup) :
    ∀ (d : ParsedOperand), d ∈ expression.destinations → ∀ v : PEMemory.Width,
      ParsedOperand.directDestinationBankWidth? d = some (PEMemory.Bank.lm1, v) →
        v = (lm1StaticWidth expression).getD PEMemory.Width.word := by
  intro d hd v pair
  rw [lm1StaticWidth_eq expression nodup d hd v pair]
  rfl


/-! ## 11. The matrix-write stage never writes a PE register file -/

/-- **A `.matrixWrite` row is never the unique `.lm1` writer.**  The whole
matrix-write stage preserves every PE register file, so a line whose only
non-plain row is a `.matrixWrite` row has its `.lm1` writes decided by its other
rows. -/
theorem matrixWriteStage_lm1_frame (readState currentState next : State)
    (coordinates : List MABCoordinate) (expressions : List ParsedExpr)
    (executed : executeParsedMatrixWritesAtMABs readState coordinates expressions
      currentState = .ok next) (pe : PEId) :
    next.peRegisters pe = currentState.peRegisters pe := by
  have preserved := executeParsedMatrixWritesAtMABs_preserves_pe_state readState
    currentState next coordinates expressions executed
  rw [preserved.1]

/-- Hence the `.lm1` file of PE 0 is unchanged by the matrix-write stage. -/
theorem matrixWriteStage_lm1_zero_frame (readState currentState next : State)
    (coordinates : List MABCoordinate) (expressions : List ParsedExpr)
    (executed : executeParsedMatrixWritesAtMABs readState coordinates expressions
      currentState = .ok next) (address : Fin PEMemory.Bank.lm1.capacity) :
    (next.peRegisters welcomePE).lm1 address =
      (currentState.peRegisters welcomePE).lm1 address := by
  rw [matrixWriteStage_lm1_frame readState currentState next coordinates expressions
    executed welcomePE]

/-! ## 12. What remains for the unified line-shape reduction

The four family obligations of `WelcomeValueBound.lean` §7 are all instances of
one reduction.  The facts still missing are the following; each is stated here
as a `Prop` and **nothing in this module assumes any of them**.

* `WelcomePEIntegerRowShapeFromWriter` — the integer stage's list-level
  provenance: if the unique `.lm1` writer row is the matrix-read row, the whole
  line's `.lm1` writes are exactly that row's; if the writer is an
  `.alu`/`.zero`/`.immediate` row, they are the four-cycle write list of
  `prepareParsedIntegerALUExprCycles`.  The `.matrixRead` *row* half of this is
  proved above (`prepareParsedMatrixReadExprCycles_zeroShape`).
* `WelcomePEFloatMAURowShape` — the float-MAU row shape at the all-zero state
  (`executeParsedFloatMAUsAtPE` through `writeParsedMAUDestinations?`).
* `WelcomePEMatrixMAURowShape` — the matrix-MAU row shape at the all-zero state
  (`commitParsedMatrixMAUPEState` writes four PE register files per MAB
  coordinate, so a matrix-MAU row *can* be the unique `.lm1` writer).
* `WelcomePELineStageAssembly` — the line-level assembly across
  `executeIntegerProducerLineAtPEs`, `executeParsedMslMsrProducers`,
  `executeParsedFloatReluProducers`, `executeParsedBlockFloatProducer`,
  `executeParsedMatrixMAUAndWrites`, `executeParsedSharedBlockProducers` and
  `executeParsedL1ToPEProducers`.
* `WelcomePENoForwardRowShape` — a line with a `.noforward` row is *not* all
  plain and contains no family row, so none of the six family specialisations
  covers it; it needs its own case (the `.noforward` row contributes no write,
  but it flips the line-level `noForward` flag passed to the integer stage).
-/


/-- **The stage-1 row interface.**  A `.matrixRead` row of the integer /
matrix-read stage, prepared at the all-zero state, has one of the two `.lm1`
shapes.  This is the form in which the line-level assembly consumes the row
analysis: `prepareParsedIntegerMatrixReadLineExpression` is exactly the
per-expression step of `prepareParsedIntegerMatrixReadLineExpressions`. -/
theorem prepareParsedIntegerMatrixReadLineExpression_matrixRead_shape
    (expression : ParsedExpr) (precision : ParsedPrecision) (sideY : Bool)
    (width : Fin 5) (row : Fin (2 ^ 32))
    (op : expression.op = .matrixRead precision)
    (sources : expression.sources = [.matrix sideY width (some row)])
    (nextSlots : ProofsLean.MNCore.Forwarding.Slots)
    (control : ParsedMaskExecutionControl)
    (hasSingleLineMask noForward reduced : Bool)
    (w : PEMemory.Width)
    (nodup : (expression.toIssueExpr 0).writeBanks.Nodup)
    (staticWidth : ∀ (d : ParsedOperand), d ∈ expression.destinations →
      ∀ v : PEMemory.Width, ParsedOperand.directDestinationBankWidth? d =
        some (PEMemory.Bank.lm1, v) → v = w)
    (writes : List PreparedParsedMaskedWrite)
    (slots : ProofsLean.MNCore.Forwarding.Slots) (bars : List (Bool × BitVec 12))
    (prepared : prepareParsedIntegerMatrixReadLineExpression welcomeZeroFiles welcomeZeroSlots
      nextSlots welcomeZeroMatrixStore expression control hasSingleLineMask noForward reduced =
        .ok (writes, slots, bars)) :
    Lm1WritesDoubleCopy writes ∨ Lm1WritesNarrow writes := by
  unfold prepareParsedIntegerMatrixReadLineExpression at prepared
  rw [op] at prepared
  simp only at prepared
  have reduced : prepareParsedMatrixReadExprCycles welcomeZeroFiles nextSlots
      welcomeZeroMatrixStore expression control.directive hasSingleLineMask noForward
      control.context = .ok (writes, slots, bars) := by
    cases h : prepareParsedMatrixReadExprCycles welcomeZeroFiles nextSlots
        welcomeZeroMatrixStore expression control.directive hasSingleLineMask noForward
        control.context with
    | failure => simp [h] at prepared
    | unknown => simp [h] at prepared
    | ok result =>
        obtain ⟨doneWrites, doneSlots, doneBars⟩ := result
        rw [h] at prepared
        simp only [StepResult.ok.injEq, Prod.mk.injEq] at prepared ⊢
        exact ⟨prepared.1, prepared.2⟩
  exact prepareParsedMatrixReadExprCycles_zeroShape expression precision sideY width row op
    sources control.directive hasSingleLineMask noForward nextSlots control.context w nodup
    staticWidth writes slots bars reduced


/-- **The row-level matrix-read shape, with the static width instantiated.**  No
width hypothesis remains: the width is `lm1StaticWidth expression`, the width of
the row's unique `.lm1` destination operand. -/
theorem prepareParsedMatrixReadExprCycles_zeroShapeStatic
    (expression : ParsedExpr) (precision : ParsedPrecision) (sideY : Bool)
    (width : Fin 5) (row : Fin (2 ^ 32))
    (op : expression.op = .matrixRead precision)
    (sources : expression.sources = [.matrix sideY width (some row)])
    (directive : ParsedMaskDirective) (hasSingleLineMask noForward : Bool)
    (initialSlots : ProofsLean.MNCore.Forwarding.Slots)
    (context : ParsedIntegerContext)
    (nodup : (expression.toIssueExpr 0).writeBanks.Nodup)
    (writes : List PreparedParsedMaskedWrite)
    (slots : ProofsLean.MNCore.Forwarding.Slots) (bars : List (Bool × BitVec 12))
    (prepared : prepareParsedMatrixReadExprCycles welcomeZeroFiles initialSlots
      welcomeZeroMatrixStore expression directive hasSingleLineMask noForward context =
        .ok (writes, slots, bars)) :
    Lm1WritesDoubleCopy writes ∨ Lm1WritesNarrow writes :=
  prepareParsedMatrixReadExprCycles_zeroShape expression precision sideY width row op
    sources directive hasSingleLineMask noForward initialSlots context
    ((lm1StaticWidth expression).getD PEMemory.Width.word) nodup
    (lm1StaticWidth_spec expression nodup) writes slots bars prepared


/-- **The matrix-MAU/write stage preserves PE register files when the line has no
matrix-MAU row.**  This is the precise sense in which a `.matrixWrite` row is
never the unique `.lm1` writer: its stage is a pure state update of the matrix
registers. -/
theorem executeParsedMatrixMAUAndWrites_peRegisters_frame_of_noMatrixMAU
    (readState currentState next : State) (expressions : List ParsedExpr)
    (noForward hasSingleLineMask : Bool)
    (noMatrixMAU : expressions.filter parsedExprIsMatrixMAUProducer = [])
    (executed : executeParsedMatrixMAUAndWrites readState currentState expressions
      noForward hasSingleLineMask = .ok next) (pe : PEId) :
    next.peRegisters pe = currentState.peRegisters pe := by
  unfold executeParsedMatrixMAUAndWrites at executed
  have mauIdentity : executeParsedMatrixMAUProducer readState currentState expressions
      noForward hasSingleLineMask = .ok currentState := by
    simp [executeParsedMatrixMAUProducer, noMatrixMAU]
  rw [mauIdentity] at executed
  have preserved := executeParsedMatrixWritesAtMABs_preserves_pe_state readState
    currentState next allMABCoordinates expressions executed
  rw [preserved.1]

/-- **The matrix-MAU/write stage leaves the `.lm1` file of PE 0 unchanged when
the line has no matrix-MAU row.** -/
theorem executeParsedMatrixMAUAndWrites_lm1_frame_of_noMatrixMAU
    (readState currentState next : State) (expressions : List ParsedExpr)
    (noForward hasSingleLineMask : Bool)
    (noMatrixMAU : expressions.filter parsedExprIsMatrixMAUProducer = [])
    (executed : executeParsedMatrixMAUAndWrites readState currentState expressions
      noForward hasSingleLineMask = .ok next) (address : Fin PEMemory.Bank.lm1.capacity) :
    (next.peRegisters welcomePE).lm1 address =
      (currentState.peRegisters welcomePE).lm1 address := by
  rw [executeParsedMatrixMAUAndWrites_peRegisters_frame_of_noMatrixMAU readState
    currentState next expressions noForward hasSingleLineMask noMatrixMAU executed welcomePE]

end ProofsLean.MNCore
