import ProofsLean.WelcomeValueBound

/-! # Destination analysis for the plain integer-ALU class

This module works at the level of `WelcomePEPlainShapeTarget`
(`WelcomeValueBound.lean`), not at the level of the whole-machine step, and
supplies the **destination analysis** that `WelcomePEPlainShapeObligation` was
missing.  Everything up to section 9 is unconditional.

## What is proved here

* **The static destination of a direct-memory operand** (§1).  A destination
  operand resolves through `ParsedOperand.toDirectMemoryDestination?` to the
  `(bank, width)` pair returned by `ParsedOperand.directDestinationBankWidth?`,
  which does not mention the cycle; only the address depends on the cycle
  (`ParsedOperand.toDirectMemoryDestination?_bankWidth`,
  `..._width_cycle_independent`).  This is the reason the four cycles of one
  expression can never disagree about the *width* of an `LM1` write — link 2 of
  the plan.
* **The eight non-direct branches of `prepareParsedIntegerALUExprCycle`** (§2):
  for the multiple-destination, OMR-mask, no-write, BAR, mask-input,
  memory-then-OMR, OMR-then-memory and constant branches the returned prepared
  write list is pinned down exactly (`..._alu_multiple`, `..._alu_omr`,
  `..._alu_nowrite`, `..._alu_bar`, `..._alu_mask_input`,
  `..._alu_memory_then_input`, `..._alu_input_then_memory`,
  `..._zero`, `..._immediate`).  This is the destination analysis of link 1.
* **Where each prepared write's destination comes from** (§3–6): the forwarded
  and unforwarded memory writes keep `accesses.destination` / `accesses.memory`
  and their selection and data are recorded; the OMR / no-write / BAR /
  mask-input writes have `destination = none`; the constant stage's memory
  targets keep `accesses.destination` and its mask/no-write targets have
  `destination = none`.
* **The data half** (§7): the third bus word of any prepared memory write is a
  copy as soon as the first source's read has a copied low-half high word —
  `evaluateBus` only copies the first operand's low half and the flush only ANDs
  it.  This covers memory, `.fixed` and (failed) forwarding sources uniformly.
* **`LM1` windows** (§8) and the per-branch window facts (§9): a branch with
  `destination = none` contributes no window, and the direct branch contributes
  exactly the static window of its lowered destination operand.
* **The lowering's destination is a static destination operand** (§9b): the
  direct-access lowerer's destination access is the resolution of one of the
  expression's own destination operands
  (`ParsedExpr.toDirectMaskedIntegerAccessesInLine?_destination_provenance`), so
  an `.lm1` write of width `w` always has a destination operand whose static
  pair is `(.lm1, w)` (`..._lm1_width`,
  `prepareParsedIntegerALUExprCycle_alu_direct_lm1_width`).  This is the link
  from the prepared write back to the static operand, i.e. the remaining half of
  link 2 for the direct branch.

## What is *not* proved here — the exact remaining obligations

Section 10 states the two remaining `Prop`s and proves
`WelcomePEPlainShapeTarget` (hence `WelcomePEPlainShapeObligation`) from them:

1. `WelcomePEPlainStepShapeExceptImmediate` — the assembly of the per-cycle facts
   into the line's write list: the four-cycle fold over
   `prepareParsedIntegerALUCycles`, the `writesUnique` bridge that makes at most
   one expression write `LM1`, and the 4096-PE lift from the per-PE prepared
   list to `next.peRegisters welcomePE` (links 1/2's assembly and link 3).
2. `WelcomePEPlainImmediateDoubleObligation` — the one value case that leaves
   both shapes: an `.immediate` row with an `.lm1` `.double` destination.  Its
   third data word is the immediate payload (verified: for both sparse values
   `unpackALUBus (evaluateParsedExecutionRequest (.immediate payload sparse) ..) 2
   = payload`), which is not a copy, and a `.double` window is wider than the
   narrow bound, so only input-independence can refute such a line.

Neither `Prop` is assumed anywhere without being named, and no `LowerBound` or
`Optimal` statement is claimed.  The six other producer families
(`.matrixRead`, the `.mau` family, `.matrixWrite`, `.l1bm`, `.l2bm`) remain the
separate obligations of `WelcomeValueBound.lean`
(`WelcomePEOtherShapeObligation` and its specialisations); this module does not
touch them.

No `sorry`, no `admit`, no `native_decide`, no new axioms.
-/

namespace ProofsLean.MNCore

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

open Issue
open PEMemory

/-! ## 1. The static `(bank, width)` of a direct-memory destination

The cycle enters `ParsedOperand.toDirectMemoryAccessMode?` only through
`parsedRegionAddressAt`; the bank, the width and every guard are functions of the
operand alone.  We record that as a static projection. -/

/-- The static `(bank, width)` pair of a direct-memory *destination* operand
(`allowDestinationMask = true`).  The cycle is deliberately absent. -/
def ParsedOperand.directDestinationBankWidth? :
    ParsedOperand → Option (PEMemory.Bank × PEMemory.Width)
  | .mem access negated extended rounded _ =>
      if negated || extended || rounded then none
      else
        match issueBankToRegisterBank access.bank, parsedWidth? access.region.width with
        | some bank, some width =>
            if (access.region.tIndirect && bank != PEMemory.Bank.lm0) ||
                (access.region.madpe.isSome && bank != PEMemory.Bank.lm0 && bank != PEMemory.Bank.lm1) then none
            else some (bank, width)
        | _, _ => none
  | _ => none

/-- **Cycle independence of the destination bank and width.**  Resolving a
direct-memory destination at any cycle always yields the same static
`(bank, width)` pair. -/
theorem ParsedOperand.toDirectMemoryDestination?_bankWidth
    (operand : ParsedOperand) (pe cycle : Fin 4) (bar0 bar1 : BitVec 12)
    (tWord : BitVec 32) :
    (ParsedOperand.toDirectMemoryDestination? operand pe cycle bar0 bar1 tWord).map
      (fun access => (access.bank, access.width)) =
      ParsedOperand.directDestinationBankWidth? operand := by
  cases operand with
  | mem access negated extended rounded mask =>
      simp only [ParsedOperand.toDirectMemoryDestination?,
        ParsedOperand.toDirectMemoryAccessMode?, ParsedOperand.directDestinationBankWidth?,
        Bool.not_true, Bool.false_and, Bool.or_false]
      by_cases guard : (negated || extended || rounded) = true
      · simp [guard]
      · rw [if_neg (by simpa using guard)]
        cases bankEq : issueBankToRegisterBank access.bank with
        | none => simp [bankEq]
        | some bank =>
            cases widthEq : parsedWidth? access.region.width with
            | none => simp [bankEq, widthEq]
            | some width =>
                by_cases blocked : ((access.region.tIndirect && bank != PEMemory.Bank.lm0) ||
                    (access.region.madpe.isSome && bank != PEMemory.Bank.lm0 &&
                      bank != PEMemory.Bank.lm1)) = true
                · simp [bankEq, widthEq, blocked, guard]
                · simp [bankEq, widthEq, blocked, guard]
  | bar lm1 width mask => rfl
  | forward kind neg ext rnd => rfl
  | fixed kind => rfl
  | omr entry mask => rfl
  | matrix y width row => rfl
  | nowrite => rfl
  | l1bm width address => rfl
  | l2bm address l2b => rfl
  | dar address => rfl

/-- Two cycles of the same operand resolve to the same bank and width. -/
theorem ParsedOperand.toDirectMemoryDestination?_width_cycle_independent
    (operand : ParsedOperand) (pe first second : Fin 4) (bar0 bar1 : BitVec 12)
    (tWord : BitVec 32) (firstAccess secondAccess : DirectMemoryAccess)
    (firstResolved : ParsedOperand.toDirectMemoryDestination? operand pe first bar0 bar1 tWord =
      some firstAccess)
    (secondResolved : ParsedOperand.toDirectMemoryDestination? operand pe second bar0 bar1 tWord =
      some secondAccess) :
    firstAccess.bank = secondAccess.bank ∧ firstAccess.width = secondAccess.width := by
  have firstEq := ParsedOperand.toDirectMemoryDestination?_bankWidth operand pe first bar0 bar1 tWord
  have secondEq := ParsedOperand.toDirectMemoryDestination?_bankWidth operand pe second bar0 bar1 tWord
  rw [firstResolved] at firstEq
  rw [secondResolved] at secondEq
  simp only [Option.map_some] at firstEq secondEq
  have pairs : (some (firstAccess.bank, firstAccess.width) : Option (PEMemory.Bank × PEMemory.Width)) =
      some (secondAccess.bank, secondAccess.width) := by
    rw [firstEq, secondEq]
  have components := Option.some.inj pairs
  exact ⟨congrArg Prod.fst components, congrArg Prod.snd components⟩

/-! ## 2. The eight non-direct branches of `prepareParsedIntegerALUExprCycle`

Each lemma pins the returned write list down exactly.  The branches are named as
in the executor's `match` ladder; the direct branch is
`prepareParsedIntegerALUExprCycle_alu_direct` in `WelcomeProvenance.lean`. -/

/-- The multiple-destination branch: the head destination's prepared write,
replicated over the remaining lowered destinations. -/
theorem prepareParsedIntegerALUExprCycle_alu_multiple
    (files : IntegerRegisterFiles) (oldSlots nextSlots : ProofsLean.MNCore.Forwarding.Slots)
    (expression : ParsedExpr) (control : ParsedMaskExecutionControl)
    (hasSingleLineMask noForward reduced : Bool) (cycle : Fin 4)
    (access : ParsedMaskedIntegerAccesses) (rest : List ParsedMaskedIntegerAccesses)
    (write : PreparedParsedMaskedWrite) (slots : ProofsLean.MNCore.Forwarding.Slots)
    (isAlu : ∃ name precision unsigned arg, expression.op = .alu name precision unsigned arg)
    (singleFailed : ParsedExpr.toDirectMaskedIntegerAccessesInLine? expression
      files.maskRegisters control.directive hasSingleLineMask control.context.group
      control.context.l2b control.context.l1b control.context.mab control.context.pe cycle
      control.context.bar0 control.context.bar1 control.context.tWord = none)
    (multipleLowered : ParsedExpr.toDirectMaskedIntegerWritesInLine? expression
      files.maskRegisters control.directive hasSingleLineMask control.context.group
      control.context.l2b control.context.l1b control.context.mab control.context.pe cycle
      control.context.bar0 control.context.bar1 control.context.tWord = some (access :: rest))
    (prepared : prepareParsedMaskedWriteWithForwarding files oldSlots cycle access reduced
      = .ok write)
    (updated : updateParsedIntegerALUForwardingCycle nextSlots cycle (.ok write) noForward
      = .ok slots) :
    prepareParsedIntegerALUExprCycle files oldSlots nextSlots expression control
        hasSingleLineMask noForward reduced cycle =
      .ok (write :: replicatePreparedIntegerResult rest write, slots) := by
  obtain ⟨name, precision, unsigned, arg, operation⟩ := isAlu
  unfold prepareParsedIntegerALUExprCycle
  rw [operation]
  dsimp only
  rw [singleFailed]
  dsimp only
  rw [multipleLowered]
  dsimp only
  rw [prepared]
  dsimp only
  rw [updated]

/-- The OMR-mask branch: one write with no memory destination. -/
theorem prepareParsedIntegerALUExprCycle_alu_omr
    (files : IntegerRegisterFiles) (oldSlots nextSlots : ProofsLean.MNCore.Forwarding.Slots)
    (expression : ParsedExpr) (control : ParsedMaskExecutionControl)
    (hasSingleLineMask noForward reduced : Bool) (cycle : Fin 4)
    (accesses : ParsedIntegerMaskAccesses) (flushSelection : Option PEWordSelection)
    (write : PreparedParsedMaskedWrite) (slots : ProofsLean.MNCore.Forwarding.Slots)
    (isAlu : ∃ name precision unsigned arg, expression.op = .alu name precision unsigned arg)
    (singleFailed : ParsedExpr.toDirectMaskedIntegerAccessesInLine? expression
      files.maskRegisters control.directive hasSingleLineMask control.context.group
      control.context.l2b control.context.l1b control.context.mab control.context.pe cycle
      control.context.bar0 control.context.bar1 control.context.tWord = none)
    (multipleFailed : ParsedExpr.toDirectMaskedIntegerWritesInLine? expression
      files.maskRegisters control.directive hasSingleLineMask control.context.group
      control.context.l2b control.context.l1b control.context.mab control.context.pe cycle
      control.context.bar0 control.context.bar1 control.context.tWord = none)
    (omrLowered : parsedIntegerMaskExprAccessesInLine? expression files.maskRegisters
      control.directive hasSingleLineMask control.context.pe cycle
      control.context.bar0 control.context.bar1 control.context.tWord = some accesses)
    (flushResolved : resolveFlushSelection? expression.flush files.maskRegisters cycle =
      some flushSelection)
    (prepared : prepareParsedIntegerMaskALUWriteWithForwarding files oldSlots cycle accesses
      flushSelection reduced = .ok write)
    (updated : updateParsedIntegerALUForwardingCycle nextSlots cycle (.ok write) noForward
      = .ok slots) :
    prepareParsedIntegerALUExprCycle files oldSlots nextSlots expression control
        hasSingleLineMask noForward reduced cycle = .ok ([write], slots) := by
  obtain ⟨name, precision, unsigned, arg, operation⟩ := isAlu
  unfold prepareParsedIntegerALUExprCycle
  rw [operation]
  dsimp only
  rw [singleFailed]
  dsimp only
  rw [multipleFailed]
  dsimp only
  rw [omrLowered]
  dsimp only
  rw [flushResolved]
  dsimp only
  rw [prepared]
  dsimp only
  rw [updated]

/-- The no-write branch: one write with no memory destination. -/
theorem prepareParsedIntegerALUExprCycle_alu_nowrite
    (files : IntegerRegisterFiles) (oldSlots nextSlots : ProofsLean.MNCore.Forwarding.Slots)
    (expression : ParsedExpr) (control : ParsedMaskExecutionControl)
    (hasSingleLineMask noForward reduced : Bool) (cycle : Fin 4)
    (accesses : ParsedIntegerNoWriteAccesses)
    (write : PreparedParsedMaskedWrite) (slots : ProofsLean.MNCore.Forwarding.Slots)
    (isAlu : ∃ name precision unsigned arg, expression.op = .alu name precision unsigned arg)
    (singleFailed : ParsedExpr.toDirectMaskedIntegerAccessesInLine? expression
      files.maskRegisters control.directive hasSingleLineMask control.context.group
      control.context.l2b control.context.l1b control.context.mab control.context.pe cycle
      control.context.bar0 control.context.bar1 control.context.tWord = none)
    (multipleFailed : ParsedExpr.toDirectMaskedIntegerWritesInLine? expression
      files.maskRegisters control.directive hasSingleLineMask control.context.group
      control.context.l2b control.context.l1b control.context.mab control.context.pe cycle
      control.context.bar0 control.context.bar1 control.context.tWord = none)
    (omrFailed : parsedIntegerMaskExprAccessesInLine? expression files.maskRegisters
      control.directive hasSingleLineMask control.context.pe cycle control.context.bar0
      control.context.bar1 control.context.tWord = none)
    (noWriteLowered : parsedIntegerNoWriteExprAccessesInLine? expression files.maskRegisters
      control.context.pe cycle control.context.group control.context.l2b control.context.l1b
      control.context.mab control.context.bar0 control.context.bar1 control.context.tWord =
        some accesses)
    (prepared : prepareParsedIntegerNoWriteALUWithForwarding files oldSlots cycle accesses
      reduced = .ok write)
    (updated : updateParsedIntegerALUForwardingCycle nextSlots cycle (.ok write) noForward
      = .ok slots) :
    prepareParsedIntegerALUExprCycle files oldSlots nextSlots expression control
        hasSingleLineMask noForward reduced cycle = .ok ([write], slots) := by
  obtain ⟨name, precision, unsigned, arg, operation⟩ := isAlu
  unfold prepareParsedIntegerALUExprCycle
  rw [operation]
  dsimp only
  rw [singleFailed]
  dsimp only
  rw [multipleFailed]
  dsimp only
  rw [omrFailed]
  dsimp only
  rw [noWriteLowered]
  dsimp only
  rw [prepared]
  dsimp only
  rw [updated]

/-- The BAR branch: one write with no memory destination. -/
theorem prepareParsedIntegerALUExprCycle_alu_bar
    (files : IntegerRegisterFiles) (oldSlots nextSlots : ProofsLean.MNCore.Forwarding.Slots)
    (expression : ParsedExpr) (control : ParsedMaskExecutionControl)
    (hasSingleLineMask noForward reduced : Bool) (cycle : Fin 4)
    (accesses : ParsedIntegerBarAccesses)
    (write : PreparedParsedMaskedWrite) (slots : ProofsLean.MNCore.Forwarding.Slots)
    (isAlu : ∃ name precision unsigned arg, expression.op = .alu name precision unsigned arg)
    (singleFailed : ParsedExpr.toDirectMaskedIntegerAccessesInLine? expression
      files.maskRegisters control.directive hasSingleLineMask control.context.group
      control.context.l2b control.context.l1b control.context.mab control.context.pe cycle
      control.context.bar0 control.context.bar1 control.context.tWord = none)
    (multipleFailed : ParsedExpr.toDirectMaskedIntegerWritesInLine? expression
      files.maskRegisters control.directive hasSingleLineMask control.context.group
      control.context.l2b control.context.l1b control.context.mab control.context.pe cycle
      control.context.bar0 control.context.bar1 control.context.tWord = none)
    (omrFailed : parsedIntegerMaskExprAccessesInLine? expression files.maskRegisters
      control.directive hasSingleLineMask control.context.pe cycle control.context.bar0
      control.context.bar1 control.context.tWord = none)
    (noWriteFailed : parsedIntegerNoWriteExprAccessesInLine? expression files.maskRegisters
      control.context.pe cycle control.context.group control.context.l2b control.context.l1b
      control.context.mab control.context.bar0 control.context.bar1 control.context.tWord =
        none)
    (barLowered : parsedIntegerBarExprAccessesInLine? expression files.maskRegisters
      control.directive hasSingleLineMask control.context.group control.context.l2b
      control.context.l1b control.context.mab control.context.pe cycle control.context.bar0
      control.context.bar1 control.context.tWord = some accesses)
    (prepared : prepareParsedIntegerBarALUWithForwarding files oldSlots cycle accesses reduced
      = .ok write)
    (updated : updateParsedIntegerALUForwardingCycle nextSlots cycle (.ok write) noForward
      = .ok slots) :
    prepareParsedIntegerALUExprCycle files oldSlots nextSlots expression control
        hasSingleLineMask noForward reduced cycle = .ok ([write], slots) := by
  obtain ⟨name, precision, unsigned, arg, operation⟩ := isAlu
  unfold prepareParsedIntegerALUExprCycle
  rw [operation]
  dsimp only
  rw [singleFailed]
  dsimp only
  rw [multipleFailed]
  dsimp only
  rw [omrFailed]
  dsimp only
  rw [noWriteFailed]
  dsimp only
  rw [barLowered]
  dsimp only
  rw [prepared]
  dsimp only
  rw [updated]

/-- The mask-input branch: one write with no memory destination. -/
theorem prepareParsedIntegerALUExprCycle_alu_mask_input
    (files : IntegerRegisterFiles) (oldSlots nextSlots : ProofsLean.MNCore.Forwarding.Slots)
    (expression : ParsedExpr) (control : ParsedMaskExecutionControl)
    (hasSingleLineMask noForward reduced : Bool) (cycle : Fin 4)
    (accesses : ParsedIntegerMaskInputAccesses) (flushSelection : Option PEWordSelection)
    (write : PreparedParsedMaskedWrite) (slots : ProofsLean.MNCore.Forwarding.Slots)
    (isAlu : ∃ name precision unsigned arg, expression.op = .alu name precision unsigned arg)
    (singleFailed : ParsedExpr.toDirectMaskedIntegerAccessesInLine? expression
      files.maskRegisters control.directive hasSingleLineMask control.context.group
      control.context.l2b control.context.l1b control.context.mab control.context.pe cycle
      control.context.bar0 control.context.bar1 control.context.tWord = none)
    (multipleFailed : ParsedExpr.toDirectMaskedIntegerWritesInLine? expression
      files.maskRegisters control.directive hasSingleLineMask control.context.group
      control.context.l2b control.context.l1b control.context.mab control.context.pe cycle
      control.context.bar0 control.context.bar1 control.context.tWord = none)
    (omrFailed : parsedIntegerMaskExprAccessesInLine? expression files.maskRegisters
      control.directive hasSingleLineMask control.context.pe cycle control.context.bar0
      control.context.bar1 control.context.tWord = none)
    (noWriteFailed : parsedIntegerNoWriteExprAccessesInLine? expression files.maskRegisters
      control.context.pe cycle control.context.group control.context.l2b control.context.l1b
      control.context.mab control.context.bar0 control.context.bar1 control.context.tWord =
        none)
    (barFailed : parsedIntegerBarExprAccessesInLine? expression files.maskRegisters
      control.directive hasSingleLineMask control.context.group control.context.l2b
      control.context.l1b control.context.mab control.context.pe cycle control.context.bar0
      control.context.bar1 control.context.tWord = none)
    (inputLowered : parsedIntegerMaskInputExprAccessesInLine? expression files.maskRegisters
      control.directive hasSingleLineMask control.context.group control.context.l2b
      control.context.l1b control.context.mab control.context.pe cycle control.context.bar0
      control.context.bar1 control.context.tWord = some accesses)
    (flushResolved : resolveFlushSelection? expression.flush files.maskRegisters cycle =
      some flushSelection)
    (prepared : prepareParsedIntegerMaskInputALUWriteWithForwarding files oldSlots cycle
      accesses flushSelection reduced = .ok write)
    (updated : updateParsedIntegerALUForwardingCycle nextSlots cycle (.ok write) noForward
      = .ok slots) :
    prepareParsedIntegerALUExprCycle files oldSlots nextSlots expression control
        hasSingleLineMask noForward reduced cycle = .ok ([write], slots) := by
  obtain ⟨name, precision, unsigned, arg, operation⟩ := isAlu
  unfold prepareParsedIntegerALUExprCycle
  rw [operation]
  dsimp only
  rw [singleFailed]
  dsimp only
  rw [multipleFailed]
  dsimp only
  rw [omrFailed]
  dsimp only
  rw [noWriteFailed]
  dsimp only
  rw [barFailed]
  dsimp only
  rw [inputLowered]
  dsimp only
  rw [flushResolved]
  dsimp only
  rw [prepared]
  dsimp only
  rw [updated]

/-- The memory-then-OMR branch: the memory write followed by the OMR write (which
has no memory destination). -/
theorem prepareParsedIntegerALUExprCycle_alu_memory_then_input
    (files : IntegerRegisterFiles) (oldSlots nextSlots : ProofsLean.MNCore.Forwarding.Slots)
    (expression : ParsedExpr) (control : ParsedMaskExecutionControl)
    (hasSingleLineMask noForward reduced : Bool) (cycle : Fin 4)
    (accesses : ParsedIntegerMaskMemoryThenInputAccesses)
    (flushSelection : Option PEWordSelection)
    (memoryWrites : List PreparedParsedMaskedWrite) (omrWrite : PreparedParsedMaskedWrite)
    (slots : ProofsLean.MNCore.Forwarding.Slots)
    (isAlu : ∃ name precision unsigned arg, expression.op = .alu name precision unsigned arg)
    (singleFailed : ParsedExpr.toDirectMaskedIntegerAccessesInLine? expression
      files.maskRegisters control.directive hasSingleLineMask control.context.group
      control.context.l2b control.context.l1b control.context.mab control.context.pe cycle
      control.context.bar0 control.context.bar1 control.context.tWord = none)
    (multipleFailed : ParsedExpr.toDirectMaskedIntegerWritesInLine? expression
      files.maskRegisters control.directive hasSingleLineMask control.context.group
      control.context.l2b control.context.l1b control.context.mab control.context.pe cycle
      control.context.bar0 control.context.bar1 control.context.tWord = none)
    (omrFailed : parsedIntegerMaskExprAccessesInLine? expression files.maskRegisters
      control.directive hasSingleLineMask control.context.pe cycle control.context.bar0
      control.context.bar1 control.context.tWord = none)
    (noWriteFailed : parsedIntegerNoWriteExprAccessesInLine? expression files.maskRegisters
      control.context.pe cycle control.context.group control.context.l2b control.context.l1b
      control.context.mab control.context.bar0 control.context.bar1 control.context.tWord =
        none)
    (barFailed : parsedIntegerBarExprAccessesInLine? expression files.maskRegisters
      control.directive hasSingleLineMask control.context.group control.context.l2b
      control.context.l1b control.context.mab control.context.pe cycle control.context.bar0
      control.context.bar1 control.context.tWord = none)
    (inputFailed : parsedIntegerMaskInputExprAccessesInLine? expression files.maskRegisters
      control.directive hasSingleLineMask control.context.group control.context.l2b
      control.context.l1b control.context.mab control.context.pe cycle control.context.bar0
      control.context.bar1 control.context.tWord = none)
    (mixedLowered : parsedIntegerMaskMemoryThenInputExprAccessesInLine? expression
      files.maskRegisters control.directive hasSingleLineMask control.context.group
      control.context.l2b control.context.l1b control.context.mab control.context.pe cycle
      control.context.bar0 control.context.bar1 control.context.tWord = some accesses)
    (flushResolved : resolveFlushSelection? expression.flush files.maskRegisters cycle =
      some flushSelection)
    (prepared : prepareParsedIntegerMaskMemoryThenInputALUWritesWithForwarding files oldSlots
      cycle accesses flushSelection reduced = .ok (memoryWrites, omrWrite))
    (updated : updateParsedIntegerALUForwardingCycle nextSlots cycle (.ok omrWrite) noForward
      = .ok slots) :
    prepareParsedIntegerALUExprCycle files oldSlots nextSlots expression control
        hasSingleLineMask noForward reduced cycle = .ok (memoryWrites ++ [omrWrite], slots) := by
  obtain ⟨name, precision, unsigned, arg, operation⟩ := isAlu
  unfold prepareParsedIntegerALUExprCycle
  rw [operation]
  dsimp only
  rw [singleFailed]
  dsimp only
  rw [multipleFailed]
  dsimp only
  rw [omrFailed]
  dsimp only
  rw [noWriteFailed]
  dsimp only
  rw [barFailed]
  dsimp only
  rw [inputFailed]
  dsimp only
  rw [mixedLowered]
  dsimp only
  rw [flushResolved]
  dsimp only
  rw [prepared]
  dsimp only
  rw [updated]

/-- The OMR-then-memory branch: the memory write is the second entry. -/
theorem prepareParsedIntegerALUExprCycle_alu_input_then_memory
    (files : IntegerRegisterFiles) (oldSlots nextSlots : ProofsLean.MNCore.Forwarding.Slots)
    (expression : ParsedExpr) (control : ParsedMaskExecutionControl)
    (hasSingleLineMask noForward reduced : Bool) (cycle : Fin 4)
    (accesses : ParsedIntegerMaskInputThenMemoryAccesses)
    (flushSelection : Option PEWordSelection)
    (memoryWrites : List PreparedParsedMaskedWrite) (omrWrite : PreparedParsedMaskedWrite)
    (slots : ProofsLean.MNCore.Forwarding.Slots)
    (isAlu : ∃ name precision unsigned arg, expression.op = .alu name precision unsigned arg)
    (singleFailed : ParsedExpr.toDirectMaskedIntegerAccessesInLine? expression
      files.maskRegisters control.directive hasSingleLineMask control.context.group
      control.context.l2b control.context.l1b control.context.mab control.context.pe cycle
      control.context.bar0 control.context.bar1 control.context.tWord = none)
    (multipleFailed : ParsedExpr.toDirectMaskedIntegerWritesInLine? expression
      files.maskRegisters control.directive hasSingleLineMask control.context.group
      control.context.l2b control.context.l1b control.context.mab control.context.pe cycle
      control.context.bar0 control.context.bar1 control.context.tWord = none)
    (omrFailed : parsedIntegerMaskExprAccessesInLine? expression files.maskRegisters
      control.directive hasSingleLineMask control.context.pe cycle control.context.bar0
      control.context.bar1 control.context.tWord = none)
    (noWriteFailed : parsedIntegerNoWriteExprAccessesInLine? expression files.maskRegisters
      control.context.pe cycle control.context.group control.context.l2b control.context.l1b
      control.context.mab control.context.bar0 control.context.bar1 control.context.tWord =
        none)
    (barFailed : parsedIntegerBarExprAccessesInLine? expression files.maskRegisters
      control.directive hasSingleLineMask control.context.group control.context.l2b
      control.context.l1b control.context.mab control.context.pe cycle control.context.bar0
      control.context.bar1 control.context.tWord = none)
    (inputFailed : parsedIntegerMaskInputExprAccessesInLine? expression files.maskRegisters
      control.directive hasSingleLineMask control.context.group control.context.l2b
      control.context.l1b control.context.mab control.context.pe cycle control.context.bar0
      control.context.bar1 control.context.tWord = none)
    (memoryThenInputFailed : parsedIntegerMaskMemoryThenInputExprAccessesInLine? expression
      files.maskRegisters control.directive hasSingleLineMask control.context.group
      control.context.l2b control.context.l1b control.context.mab control.context.pe cycle
      control.context.bar0 control.context.bar1 control.context.tWord = none)
    (memoryLowered : parsedIntegerMaskInputThenMemoryExprAccessesInLine? expression
      files.maskRegisters control.directive hasSingleLineMask control.context.group
      control.context.l2b control.context.l1b control.context.mab control.context.pe cycle
      control.context.bar0 control.context.bar1 control.context.tWord = some accesses)
    (flushResolved : resolveFlushSelection? expression.flush files.maskRegisters cycle =
      some flushSelection)
    (prepared : prepareParsedIntegerMaskInputThenMemoryALUWritesWithForwarding files oldSlots
      cycle accesses control.directive hasSingleLineMask flushSelection reduced
      = .ok (memoryWrites, omrWrite))
    (updated : updateParsedIntegerALUForwardingCycle nextSlots cycle (.ok omrWrite) noForward
      = .ok slots) :
    prepareParsedIntegerALUExprCycle files oldSlots nextSlots expression control
        hasSingleLineMask noForward reduced cycle = .ok (memoryWrites, slots) := by
  obtain ⟨name, precision, unsigned, arg, operation⟩ := isAlu
  unfold prepareParsedIntegerALUExprCycle
  rw [operation]
  dsimp only
  rw [singleFailed]
  dsimp only
  rw [multipleFailed]
  dsimp only
  rw [omrFailed]
  dsimp only
  rw [noWriteFailed]
  dsimp only
  rw [barFailed]
  dsimp only
  rw [inputFailed]
  dsimp only
  rw [memoryThenInputFailed]
  dsimp only
  rw [memoryLowered]
  dsimp only
  rw [flushResolved]
  dsimp only
  rw [prepared]
  dsimp only
  rw [updated]

/-- The `.zero` constant branch: the destination writes followed by the
destination-free producer write, whose bus is the zero request's evaluation. -/
theorem prepareParsedIntegerALUExprCycle_zero
    (files : IntegerRegisterFiles) (oldSlots nextSlots : ProofsLean.MNCore.Forwarding.Slots)
    (expression : ParsedExpr) (control : ParsedMaskExecutionControl)
    (hasSingleLineMask noForward reduced : Bool) (cycle : Fin 4)
    (targets : List ParsedConstantDestination)
    (destinationWrites : List PreparedParsedMaskedWrite)
    (flushSelection : Option PEWordSelection)
    (slots : ProofsLean.MNCore.Forwarding.Slots)
    (isZero : expression.op = .zero)
    (lowered : ParsedExpr.toDirectMaskedConstantWrites? expression files.maskRegisters
      control.directive hasSingleLineMask control.context.group control.context.l2b
      control.context.l1b control.context.mab control.context.pe cycle
      control.context.bar0 control.context.bar1 control.context.tWord = some targets)
    (prepared : prepareParsedMaskedConstantWrites files cycle targets
      = .ok destinationWrites)
    (flushResolved : resolveFlushSelection? expression.flush files.maskRegisters cycle =
      some flushSelection)
    (updated : updateParsedIntegerALUForwardingCycle nextSlots cycle
      (.ok ⟨none, none,
        unpackALUBus (parsedOutputAfterFlush flushSelection
          (evaluateParsedExecutionRequest .zero ⟨0, 0⟩ ⟨0, 0⟩ reduced).value),
        ⟨BitVec.allOnes 4, true⟩⟩) noForward = .ok slots) :
    prepareParsedIntegerALUExprCycle files oldSlots nextSlots expression control
        hasSingleLineMask noForward reduced cycle =
      .ok (destinationWrites ++
        [⟨none, none,
          unpackALUBus (parsedOutputAfterFlush flushSelection
            (evaluateParsedExecutionRequest .zero ⟨0, 0⟩ ⟨0, 0⟩ reduced).value),
          ⟨BitVec.allOnes 4, true⟩⟩], slots) := by
  unfold prepareParsedIntegerALUExprCycle
  rw [isZero]
  dsimp only
  rw [lowered]
  dsimp only
  rw [prepared]
  dsimp only
  rw [zero_has_execution_request]
  dsimp only
  rw [flushResolved]
  dsimp only
  rw [updated]
  try rfl

/-- The `.immediate` constant branch. -/
theorem prepareParsedIntegerALUExprCycle_immediate
    (files : IntegerRegisterFiles) (oldSlots nextSlots : ProofsLean.MNCore.Forwarding.Slots)
    (expression : ParsedExpr) (control : ParsedMaskExecutionControl)
    (hasSingleLineMask noForward reduced : Bool) (cycle : Fin 4)
    (targets : List ParsedConstantDestination)
    (destinationWrites : List PreparedParsedMaskedWrite)
    (flushSelection : Option PEWordSelection)
    (slots : ProofsLean.MNCore.Forwarding.Slots)
    (payload : BitVec 32) (sparse : Bool)
    (isImmediate : expression.op = .immediate payload sparse)
    (lowered : ParsedExpr.toDirectMaskedConstantWrites? expression files.maskRegisters
      control.directive hasSingleLineMask control.context.group control.context.l2b
      control.context.l1b control.context.mab control.context.pe cycle
      control.context.bar0 control.context.bar1 control.context.tWord = some targets)
    (prepared : prepareParsedMaskedConstantWrites files cycle targets
      = .ok destinationWrites)
    (flushResolved : resolveFlushSelection? expression.flush files.maskRegisters cycle =
      some flushSelection)
    (updated : updateParsedIntegerALUForwardingCycle nextSlots cycle
      (.ok ⟨none, none,
        unpackALUBus (parsedOutputAfterFlush flushSelection
          (evaluateParsedExecutionRequest (.immediate payload sparse) ⟨0, 0⟩ ⟨0, 0⟩
            reduced).value),
        ⟨BitVec.allOnes 4, true⟩⟩) noForward = .ok slots) :
    prepareParsedIntegerALUExprCycle files oldSlots nextSlots expression control
        hasSingleLineMask noForward reduced cycle =
      .ok (destinationWrites ++
        [⟨none, none,
          unpackALUBus (parsedOutputAfterFlush flushSelection
            (evaluateParsedExecutionRequest (.immediate payload sparse) ⟨0, 0⟩ ⟨0, 0⟩
              reduced).value),
          ⟨BitVec.allOnes 4, true⟩⟩], slots) := by
  unfold prepareParsedIntegerALUExprCycle
  rw [isImmediate]
  dsimp only
  rw [lowered]
  dsimp only
  rw [prepared]
  dsimp only
  rw [immediate_has_execution_request]
  dsimp only
  rw [flushResolved]
  dsimp only
  rw [updated]
  try rfl


/-! ## 3. The destinations of the prepared writes

The prepared-write constructors are the only place where a `PreparedParsedMaskedWrite`
acquires a memory destination: `prepareParsedMaskedWrite{,WithForwarding}` sets it
to `accesses.destination`, the memory-then-input / input-then-memory stages use
`accesses.memory`, and every OMR / no-write / BAR / producer write has
`destination = none`. -/

/-- The general equation of a forwarded prepared memory write. -/
theorem prepareParsedMaskedWriteWithForwarding_eq
    (files : IntegerRegisterFiles) (slots : ProofsLean.MNCore.Forwarding.Slots)
    (cycle : Fin 4) (accesses : ParsedMaskedIntegerAccesses) (reduced : Bool)
    (x y : IntegerALU.Bus) (output : IntegerALU.BusResult)
    (readX : ParsedIntegerInput.readWithForwarding files slots cycle accesses.sourceX = .ok x)
    (readY : ParsedIntegerInput.readWithForwarding files slots cycle accesses.sourceY = .ok y)
    (evaluated : evaluateParsedIntegerAlu accesses.op x y reduced = .ok output) :
    prepareParsedMaskedWriteWithForwarding files slots cycle accesses reduced =
      .ok { destination := some accesses.destination
            maskUpdate := none
            data := unpackALUBus (parsedOutputAfterFlush accesses.flushSelection output.value)
            selection := accesses.writeSelection } := by
  simp [prepareParsedMaskedWriteWithForwarding, readX, readY, evaluated]

/-- Every forwarded prepared memory write keeps the access destination. -/
theorem prepareParsedMaskedWriteWithForwarding_destination
    (files : IntegerRegisterFiles) (slots : ProofsLean.MNCore.Forwarding.Slots)
    (cycle : Fin 4) (accesses : ParsedMaskedIntegerAccesses) (reduced : Bool)
    (write : PreparedParsedMaskedWrite)
    (prepared : prepareParsedMaskedWriteWithForwarding files slots cycle accesses reduced
      = .ok write) :
    write.destination = some accesses.destination := by
  unfold prepareParsedMaskedWriteWithForwarding at prepared
  cases hx : ParsedIntegerInput.readWithForwarding files slots cycle accesses.sourceX with
  | failure => simp only [hx] at prepared; simp at prepared
  | unknown => simp only [hx] at prepared; simp at prepared
  | ok x =>
      cases hy : ParsedIntegerInput.readWithForwarding files slots cycle accesses.sourceY with
      | failure => simp only [hx, hy] at prepared; simp at prepared
      | unknown => simp only [hx, hy] at prepared; simp at prepared
      | ok y =>
          cases he : evaluateParsedIntegerAlu accesses.op x y reduced with
          | failure => simp only [hx, hy, he] at prepared; simp at prepared
          | unknown => simp only [hx, hy, he] at prepared; simp at prepared
          | ok output =>
              simp only [hx, hy, he, StepResult.ok.injEq] at prepared
              subst prepared
              rfl

/-- Every forwarded prepared memory write keeps the access selection. -/
theorem prepareParsedMaskedWriteWithForwarding_selection
    (files : IntegerRegisterFiles) (slots : ProofsLean.MNCore.Forwarding.Slots)
    (cycle : Fin 4) (accesses : ParsedMaskedIntegerAccesses) (reduced : Bool)
    (write : PreparedParsedMaskedWrite)
    (prepared : prepareParsedMaskedWriteWithForwarding files slots cycle accesses reduced
      = .ok write) :
    write.selection = accesses.writeSelection := by
  unfold prepareParsedMaskedWriteWithForwarding at prepared
  cases hx : ParsedIntegerInput.readWithForwarding files slots cycle accesses.sourceX with
  | failure => simp only [hx] at prepared; simp at prepared
  | unknown => simp only [hx] at prepared; simp at prepared
  | ok x =>
      cases hy : ParsedIntegerInput.readWithForwarding files slots cycle accesses.sourceY with
      | failure => simp only [hx, hy] at prepared; simp at prepared
      | unknown => simp only [hx, hy] at prepared; simp at prepared
      | ok y =>
          cases he : evaluateParsedIntegerAlu accesses.op x y reduced with
          | failure => simp only [hx, hy, he] at prepared; simp at prepared
          | unknown => simp only [hx, hy, he] at prepared; simp at prepared
          | ok output =>
              simp only [hx, hy, he, StepResult.ok.injEq] at prepared
              subst prepared
              rfl

/-- The general equation of an unforwarded prepared memory write (the constant
target stage). -/
theorem prepareParsedMaskedWrite_eq
    (files : IntegerRegisterFiles) (accesses : ParsedMaskedIntegerAccesses) (reduced : Bool)
    (x y : IntegerALU.Bus) (output : IntegerALU.BusResult)
    (readX : ParsedIntegerInput.read files accesses.sourceX = .ok x)
    (readY : ParsedIntegerInput.read files accesses.sourceY = .ok y)
    (evaluated : evaluateParsedIntegerAlu accesses.op x y reduced = .ok output) :
    prepareParsedMaskedWrite files accesses reduced =
      .ok { destination := some accesses.destination
            maskUpdate := none
            data := unpackALUBus (parsedOutputAfterFlush accesses.flushSelection output.value)
            selection := accesses.writeSelection } := by
  simp [prepareParsedMaskedWrite, readX, readY, evaluated]

/-- The unforwarded prepared memory write keeps the access destination. -/
theorem prepareParsedMaskedWrite_destination
    (files : IntegerRegisterFiles) (accesses : ParsedMaskedIntegerAccesses) (reduced : Bool)
    (write : PreparedParsedMaskedWrite)
    (prepared : prepareParsedMaskedWrite files accesses reduced = .ok write) :
    write.destination = some accesses.destination := by
  unfold prepareParsedMaskedWrite at prepared
  cases hx : ParsedIntegerInput.read files accesses.sourceX with
  | failure => simp only [hx] at prepared; simp at prepared
  | unknown => simp only [hx] at prepared; simp at prepared
  | ok x =>
      cases hy : ParsedIntegerInput.read files accesses.sourceY with
      | failure => simp only [hx, hy] at prepared; simp at prepared
      | unknown => simp only [hx, hy] at prepared; simp at prepared
      | ok y =>
          cases he : evaluateParsedIntegerAlu accesses.op x y reduced with
          | failure => simp only [hx, hy, he] at prepared; simp at prepared
          | unknown => simp only [hx, hy, he] at prepared; simp at prepared
          | ok output =>
              simp only [hx, hy, he, StepResult.ok.injEq] at prepared
              subst prepared
              rfl

/-- The unforwarded prepared memory write's data is the flushed bus. -/
theorem prepareParsedMaskedWrite_data
    (files : IntegerRegisterFiles) (accesses : ParsedMaskedIntegerAccesses) (reduced : Bool)
    (write : PreparedParsedMaskedWrite)
    (prepared : prepareParsedMaskedWrite files accesses reduced = .ok write) :
    ∃ (x y : IntegerALU.Bus) (output : IntegerALU.BusResult),
      ParsedIntegerInput.read files accesses.sourceX = .ok x ∧
      ParsedIntegerInput.read files accesses.sourceY = .ok y ∧
      evaluateParsedIntegerAlu accesses.op x y reduced = .ok output ∧
      write.data = unpackALUBus (parsedOutputAfterFlush accesses.flushSelection output.value) := by
  unfold prepareParsedMaskedWrite at prepared
  cases hx : ParsedIntegerInput.read files accesses.sourceX with
  | failure => simp only [hx] at prepared; simp at prepared
  | unknown => simp only [hx] at prepared; simp at prepared
  | ok x =>
      cases hy : ParsedIntegerInput.read files accesses.sourceY with
      | failure => simp only [hx, hy] at prepared; simp at prepared
      | unknown => simp only [hx, hy] at prepared; simp at prepared
      | ok y =>
          cases he : evaluateParsedIntegerAlu accesses.op x y reduced with
          | failure => simp only [hx, hy, he] at prepared; simp at prepared
          | unknown => simp only [hx, hy, he] at prepared; simp at prepared
          | ok output =>
              simp only [hx, hy, he, StepResult.ok.injEq] at prepared
              subst prepared
              exact ⟨x, y, output, rfl, rfl, he, rfl⟩


/-! ## 4. Branches whose prepared write has no memory destination -/

theorem prepareParsedIntegerMaskALUWriteWithForwarding_destination_none
    (files : IntegerRegisterFiles) (slots : ProofsLean.MNCore.Forwarding.Slots)
    (cycle : Fin 4) (accesses : ParsedIntegerMaskAccesses)
    (flushSelection : Option PEWordSelection) (reduced : Bool)
    (write : PreparedParsedMaskedWrite)
    (prepared : prepareParsedIntegerMaskALUWriteWithForwarding files slots cycle accesses
      flushSelection reduced = .ok write) :
    write.destination = none := by
  unfold prepareParsedIntegerMaskALUWriteWithForwarding at prepared
  cases hx : ParsedIntegerInput.readWithForwarding files slots cycle
      (.memory accesses.sourceX accesses.sourceXRounded) with
  | failure => simp only [hx] at prepared; simp at prepared
  | unknown => simp only [hx] at prepared; simp at prepared
  | ok x =>
      cases hy : ParsedIntegerInput.readWithForwarding files slots cycle
          (.memory accesses.sourceY accesses.sourceYRounded) with
      | failure => simp only [hx, hy] at prepared; simp at prepared
      | unknown => simp only [hx, hy] at prepared; simp at prepared
      | ok y =>
          cases he : evaluateParsedIntegerAlu accesses.op x y reduced with
          | failure => simp only [hx, hy, he] at prepared; simp at prepared
          | unknown => simp only [hx, hy, he] at prepared; simp at prepared
          | ok output =>
              simp only [hx, hy, he, StepResult.ok.injEq] at prepared
              subst prepared
              rfl

theorem prepareParsedIntegerMaskInputALUWriteWithForwarding_destination_none
    (files : IntegerRegisterFiles) (slots : ProofsLean.MNCore.Forwarding.Slots)
    (cycle : Fin 4) (accesses : ParsedIntegerMaskInputAccesses)
    (flushSelection : Option PEWordSelection) (reduced : Bool)
    (write : PreparedParsedMaskedWrite)
    (prepared : prepareParsedIntegerMaskInputALUWriteWithForwarding files slots cycle accesses
      flushSelection reduced = .ok write) :
    write.destination = none := by
  unfold prepareParsedIntegerMaskInputALUWriteWithForwarding at prepared
  cases hx : ParsedIntegerInput.readWithForwarding files slots cycle accesses.sourceX with
  | failure => simp only [hx] at prepared; simp at prepared
  | unknown => simp only [hx] at prepared; simp at prepared
  | ok x =>
      cases hy : ParsedIntegerInput.readWithForwarding files slots cycle accesses.sourceY with
      | failure => simp only [hx, hy] at prepared; simp at prepared
      | unknown => simp only [hx, hy] at prepared; simp at prepared
      | ok y =>
          cases he : evaluateParsedIntegerAlu accesses.op x y reduced with
          | failure => simp only [hx, hy, he] at prepared; simp at prepared
          | unknown => simp only [hx, hy, he] at prepared; simp at prepared
          | ok output =>
              simp only [hx, hy, he, StepResult.ok.injEq] at prepared
              subst prepared
              rfl

theorem prepareParsedIntegerNoWriteALUWithForwarding_destination_none
    (files : IntegerRegisterFiles) (slots : ProofsLean.MNCore.Forwarding.Slots)
    (cycle : Fin 4) (accesses : ParsedIntegerNoWriteAccesses) (reduced : Bool)
    (write : PreparedParsedMaskedWrite)
    (prepared : prepareParsedIntegerNoWriteALUWithForwarding files slots cycle accesses reduced
      = .ok write) :
    write.destination = none := by
  unfold prepareParsedIntegerNoWriteALUWithForwarding at prepared
  cases hx : ParsedIntegerInput.readWithForwarding files slots cycle accesses.sourceX with
  | failure => simp only [hx] at prepared; simp at prepared
  | unknown => simp only [hx] at prepared; simp at prepared
  | ok x =>
      cases hy : ParsedIntegerInput.readWithForwarding files slots cycle accesses.sourceY with
      | failure => simp only [hx, hy] at prepared; simp at prepared
      | unknown => simp only [hx, hy] at prepared; simp at prepared
      | ok y =>
          cases he : evaluateParsedIntegerAlu accesses.op x y reduced with
          | failure => simp only [hx, hy, he] at prepared; simp at prepared
          | unknown => simp only [hx, hy, he] at prepared; simp at prepared
          | ok output =>
              simp only [hx, hy, he, StepResult.ok.injEq] at prepared
              subst prepared
              rfl

theorem prepareParsedIntegerBarALUWithForwarding_destination_none
    (files : IntegerRegisterFiles) (slots : ProofsLean.MNCore.Forwarding.Slots)
    (cycle : Fin 4) (accesses : ParsedIntegerBarAccesses) (reduced : Bool)
    (write : PreparedParsedMaskedWrite)
    (prepared : prepareParsedIntegerBarALUWithForwarding files slots cycle accesses reduced
      = .ok write) :
    write.destination = none := by
  unfold prepareParsedIntegerBarALUWithForwarding at prepared
  cases hx : ParsedIntegerInput.readWithForwarding files slots cycle accesses.sourceX with
  | failure => simp only [hx] at prepared; simp at prepared
  | unknown => simp only [hx] at prepared; simp at prepared
  | ok x =>
      cases hy : ParsedIntegerInput.readWithForwarding files slots cycle accesses.sourceY with
      | failure => simp only [hx, hy] at prepared; simp at prepared
      | unknown => simp only [hx, hy] at prepared; simp at prepared
      | ok y =>
          cases he : evaluateParsedIntegerAlu accesses.op x y reduced with
          | failure => simp only [hx, hy, he] at prepared; simp at prepared
          | unknown => simp only [hx, hy, he] at prepared; simp at prepared
          | ok output =>
              simp only [hx, hy, he, StepResult.ok.injEq] at prepared
              subst prepared
              rfl

/-! ## 5. The two mixed memory/OMR stages -/

theorem prepareParsedIntegerMaskMemoryThenInputALUWritesWithForwarding_shape
    (files : IntegerRegisterFiles) (slots : ProofsLean.MNCore.Forwarding.Slots)
    (cycle : Fin 4) (accesses : ParsedIntegerMaskMemoryThenInputAccesses)
    (flushSelection : Option PEWordSelection) (reduced : Bool)
    (writes : List PreparedParsedMaskedWrite) (producerWrite : PreparedParsedMaskedWrite)
    (prepared : prepareParsedIntegerMaskMemoryThenInputALUWritesWithForwarding files slots
      cycle accesses flushSelection reduced = .ok (writes, producerWrite)) :
    ∃ (bus : WordBus) (flags : BitVec 4),
      writes = [⟨some accesses.memory, none, bus, accesses.memorySelection⟩] ∧
      producerWrite = ⟨none, some (accesses.destination, cycle, flags), bus,
        ⟨accesses.omrSelection, true⟩⟩ := by
  unfold prepareParsedIntegerMaskMemoryThenInputALUWritesWithForwarding at prepared
  cases hx : ParsedIntegerInput.readWithForwarding files slots cycle accesses.sourceX with
  | failure => simp only [hx] at prepared; simp at prepared
  | unknown => simp only [hx] at prepared; simp at prepared
  | ok x =>
      cases hy : ParsedIntegerInput.readWithForwarding files slots cycle accesses.sourceY with
      | failure => simp only [hx, hy] at prepared; simp at prepared
      | unknown => simp only [hx, hy] at prepared; simp at prepared
      | ok y =>
          cases he : evaluateParsedIntegerAlu accesses.op x y reduced with
          | failure => simp only [hx, hy, he] at prepared; simp at prepared
          | unknown => simp only [hx, hy, he] at prepared; simp at prepared
          | ok output =>
              simp only [hx, hy, he, StepResult.ok.injEq, Prod.mk.injEq] at prepared
              obtain ⟨writesEq, producerEq⟩ := prepared
              subst writesEq
              subst producerEq
              exact ⟨_, _, rfl, rfl⟩

theorem prepareParsedIntegerMaskInputThenMemoryALUWritesWithForwarding_shape
    (files : IntegerRegisterFiles) (slots : ProofsLean.MNCore.Forwarding.Slots)
    (cycle : Fin 4) (accesses : ParsedIntegerMaskInputThenMemoryAccesses)
    (directive : ParsedMaskDirective) (hasSingleLineMask : Bool)
    (flushSelection : Option PEWordSelection) (reduced : Bool)
    (writes : List PreparedParsedMaskedWrite) (producerWrite : PreparedParsedMaskedWrite)
    (prepared : prepareParsedIntegerMaskInputThenMemoryALUWritesWithForwarding files slots
      cycle accesses directive hasSingleLineMask flushSelection reduced
      = .ok (writes, producerWrite)) :
    ∃ (bus : WordBus) (flags : BitVec 4) (memorySelection : PEWordSelection),
      writes = [⟨none, some (accesses.destination, cycle, flags), bus,
          ⟨accesses.omrSelection, true⟩⟩,
        ⟨some accesses.memory, none, bus, memorySelection⟩] ∧
      producerWrite = ⟨none, some (accesses.destination, cycle, flags), bus,
        ⟨accesses.omrSelection, true⟩⟩ := by
  unfold prepareParsedIntegerMaskInputThenMemoryALUWritesWithForwarding at prepared
  cases hx : ParsedIntegerInput.readWithForwarding files slots cycle accesses.sourceX with
  | failure => simp only [hx] at prepared; simp at prepared
  | unknown => simp only [hx] at prepared; simp at prepared
  | ok x =>
      cases hy : ParsedIntegerInput.readWithForwarding files slots cycle accesses.sourceY with
      | failure => simp only [hx, hy] at prepared; simp at prepared
      | unknown => simp only [hx, hy] at prepared; simp at prepared
      | ok y =>
          cases he : evaluateParsedIntegerAlu accesses.op x y reduced with
          | failure => simp only [hx, hy, he] at prepared; simp at prepared
          | unknown => simp only [hx, hy, he] at prepared; simp at prepared
          | ok output =>
              cases hm : ParsedOperand.resolveMemoryWriteSelection? accesses.memoryOperand
                  accesses.memory.bank
                  (ProofsLean.MNCore.Masks.writeRegister files.maskRegisters
                    accesses.destination cycle
                    (BitVec.ofBoolListLE
                      [output.flags 0, output.flags 1, output.flags 2, output.flags 3])
                    accesses.omrSelection)
                  cycle directive hasSingleLineMask with
              | none => simp only [hx, hy, he, hm] at prepared; simp at prepared
              | some memorySelection =>
                  simp only [hx, hy, he, hm, StepResult.ok.injEq, Prod.mk.injEq] at prepared
                  obtain ⟨writesEq, producerEq⟩ := prepared
                  subst writesEq
                  subst producerEq
                  exact ⟨_, _, _, rfl, rfl⟩

/-! ## 6. The constant destinations -/

theorem prepareParsedConstantTarget_destination
    (files : IntegerRegisterFiles) (cycle : Fin 4)
    (target : ParsedConstantDestination) (write : PreparedParsedMaskedWrite)
    (prepared : prepareParsedConstantTarget files cycle target = .ok write) :
    write.destination = none ∨
      ∃ accesses, target = .memory accesses ∧ write.destination = some accesses.destination := by
  cases target with
  | memory accesses =>
      exact Or.inr ⟨accesses, rfl,
        prepareParsedMaskedWrite_destination files accesses false write prepared⟩
  | maskRegister entry =>
      simp [prepareParsedConstantTarget] at prepared
      subst prepared
      exact Or.inl rfl
  | noWrite =>
      simp [prepareParsedConstantTarget] at prepared
      subst prepared
      exact Or.inl rfl

theorem prepareParsedMaskedConstantWrites_destinations
    (files : IntegerRegisterFiles) (cycle : Fin 4)
    (targets : List ParsedConstantDestination) (writes : List PreparedParsedMaskedWrite)
    (prepared : prepareParsedMaskedConstantWrites files cycle targets = .ok writes) :
    ∀ write ∈ writes, write.destination = none ∨
      ∃ target ∈ targets, ∃ accesses, target = .memory accesses ∧
        write.destination = some accesses.destination := by
  induction targets generalizing writes with
  | nil =>
      simp [prepareParsedMaskedConstantWrites] at prepared
      subst prepared
      simp
  | cons target rest ih =>
      cases head : prepareParsedConstantTarget files cycle target with
      | failure => simp [prepareParsedMaskedConstantWrites, head] at prepared
      | unknown => simp [prepareParsedMaskedConstantWrites, head] at prepared
      | ok headWrite =>
          cases tail : prepareParsedMaskedConstantWrites files cycle rest with
          | failure => simp [prepareParsedMaskedConstantWrites, head, tail] at prepared
          | unknown => simp [prepareParsedMaskedConstantWrites, head, tail] at prepared
          | ok writes' =>
              simp only [prepareParsedMaskedConstantWrites, head, tail, StepResult.ok.injEq]
                at prepared
              subst prepared
              intro item member
              rcases List.mem_cons.mp member with same | later
              · subst same
                rcases prepareParsedConstantTarget_destination files cycle target item head with
                  isNone | ⟨accesses, isMemory, destination⟩
                · exact Or.inl isNone
                · exact Or.inr ⟨target, by simp, accesses, isMemory, destination⟩
              · rcases ih writes' tail item later with isNone | ⟨other, otherMem, accesses,
                  isMemory, destination⟩
                · exact Or.inl isNone
                · exact Or.inr ⟨other, List.mem_cons_of_mem _ otherMem, accesses, isMemory,
                    destination⟩


/-! ## 7. The data half: the third bus word of a forwarded memory write -/

/-- The third bus word of `evaluateBus` is a copy whenever the first operand's
low-half high word is one. -/
theorem evaluateBus_word_two_isWelcomeCopy (precision : IntegerALU.Precision)
    (aluOp : IntegerALU.Op) (x y : IntegerALU.Bus) (reduced : Bool)
    (copy : IsWelcomeCopy (x.low.extractLsb' 32 32)) (bound : 2 < 4) :
    IsWelcomeCopy
      ((IntegerALU.evaluateBus precision aluOp x y reduced).value.low.extractLsb' 32 32) := by
  rw [evaluateBus_value_low]
  split
  · exact copy
  · split
    · have zero : BitVec.extractLsb' 32 32 (0 : BitVec 64) = (0 : BitVec 32) := by decide
      rw [zero]
      exact isWelcomeCopy_zero
    · exact copy

/-- **The prepared-write third data word is a copy** as soon as the first
source's read has a copied low-half high word.  No hypothesis on the second
source or on the flush selection is needed: `evaluateBus` copies the first
operand's low half, and a flush only ANDs it. -/
theorem prepareParsedMaskedWriteWithForwarding_data_two_isWelcomeCopy_of_read_copy
    (files : IntegerRegisterFiles) (slots : ProofsLean.MNCore.Forwarding.Slots)
    (cycle : Fin 4) (accesses : ParsedMaskedIntegerAccesses) (reduced : Bool)
    (write : PreparedParsedMaskedWrite) (x : IntegerALU.Bus)
    (prepared : prepareParsedMaskedWriteWithForwarding files slots cycle accesses reduced
      = .ok write)
    (readX : ParsedIntegerInput.readWithForwarding files slots cycle accesses.sourceX = .ok x)
    (copy : IsWelcomeCopy (x.low.extractLsb' 32 32))
    (precision : IntegerALU.Precision) (aluOp : IntegerALU.Op)
    (request : accesses.op.executionRequest = .ok (.integer precision aluOp)) :
    ∀ bound : 2 < 4, IsWelcomeCopy (write.data ⟨2, bound⟩) := by
  unfold prepareParsedMaskedWriteWithForwarding at prepared
  simp only [readX] at prepared
  cases hy : ParsedIntegerInput.readWithForwarding files slots cycle accesses.sourceY with
  | failure => simp only [hy] at prepared; simp at prepared
  | unknown => simp only [hy] at prepared; simp at prepared
  | ok y =>
      cases he : evaluateParsedIntegerAlu accesses.op x y reduced with
      | failure => simp only [hy, he] at prepared; simp at prepared
      | unknown => simp only [hy, he] at prepared; simp at prepared
      | ok output =>
          simp only [hy, he, StepResult.ok.injEq] at prepared
          subst prepared
          have evaluated := parsed_integer_evaluation_uses_requested_semantics accesses.op
            precision aluOp request x y reduced
          rw [evaluated] at he
          obtain rfl := StepResult.ok.inj he
          intro bound
          dsimp only
          rw [unpackALUBus_word_two]
          exact parsedOutputAfterFlush_word_two_isWelcomeCopy _ _
            (evaluateBus_word_two_isWelcomeCopy precision aluOp x y reduced copy bound)

/-! ## 8. The `LM1` windows of a prepared write list -/

/-- The `LM1` destinations of a prepared write list, as `(address, words)` windows. -/
def lm1WindowsOfWrites : List PreparedParsedMaskedWrite →
    List (Fin Bank.lm1.capacity × Nat)
  | [] => []
  | write :: rest =>
      (match write.destination with
        | none => []
        | some ⟨bank, width, address⟩ =>
            match bank with
            | .lm1 => [(address, count .lm1 width)]
            | _ => []) ++ lm1WindowsOfWrites rest

theorem lm1WindowsOfWrites_nil : lm1WindowsOfWrites [] = [] := rfl

theorem lm1WindowsOfWrites_eq_nil_of_all_destination_none
    (writes : List PreparedParsedMaskedWrite)
    (allNone : ∀ write ∈ writes, write.destination = none) :
    lm1WindowsOfWrites writes = [] := by
  induction writes with
  | nil => rfl
  | cons write rest ih =>
      simp only [lm1WindowsOfWrites, allNone write (by simp)]
      exact ih (fun item member => allNone item (List.mem_cons_of_mem _ member))

theorem lm1WindowsOfWrites_eq_nil_of_singleton_destination_none
    (write : PreparedParsedMaskedWrite) (isNone : write.destination = none) :
    lm1WindowsOfWrites [write] = [] :=
  lm1WindowsOfWrites_eq_nil_of_all_destination_none [write] (by
    intro item member
    rcases List.mem_singleton.mp member with rfl
    exact isNone)

theorem lm1WindowsOfWrites_eq_nil_of_append_destination_none
    (writes : List PreparedParsedMaskedWrite) (write : PreparedParsedMaskedWrite)
    (isNone : write.destination = none) (allNone : ∀ item ∈ writes, item.destination = none) :
    lm1WindowsOfWrites (writes ++ [write]) = [] := by
  rw [lm1WindowsOfWrites_eq_nil_of_all_destination_none]
  intro item member
  rcases List.mem_append.mp member with earlier | later
  · exact allNone item earlier
  · rcases List.mem_singleton.mp later with rfl
    exact isNone


/-! ## 9. The per-branch window facts

The two lemmas below show that the per-branch destination analysis of sections
2–5 is usable directly: a branch whose prepared write has no destination
contributes no `LM1` window at all, and the direct branch contributes exactly the
window of the lowered destination operand, whose `(bank, width)` is the static
one by `ParsedOperand.toDirectMemoryDestination?_bankWidth`. -/

theorem prepareParsedIntegerALUExprCycle_alu_omr_windows
    (files : IntegerRegisterFiles) (oldSlots nextSlots : ProofsLean.MNCore.Forwarding.Slots)
    (expression : ParsedExpr) (control : ParsedMaskExecutionControl)
    (hasSingleLineMask noForward reduced : Bool) (cycle : Fin 4)
    (accesses : ParsedIntegerMaskAccesses) (flushSelection : Option PEWordSelection)
    (write : PreparedParsedMaskedWrite) (slots : ProofsLean.MNCore.Forwarding.Slots)
    (singleFailed : ParsedExpr.toDirectMaskedIntegerAccessesInLine? expression
      files.maskRegisters control.directive hasSingleLineMask control.context.group
      control.context.l2b control.context.l1b control.context.mab control.context.pe cycle
      control.context.bar0 control.context.bar1 control.context.tWord = none)
    (multipleFailed : ParsedExpr.toDirectMaskedIntegerWritesInLine? expression
      files.maskRegisters control.directive hasSingleLineMask control.context.group
      control.context.l2b control.context.l1b control.context.mab control.context.pe cycle
      control.context.bar0 control.context.bar1 control.context.tWord = none)
    (omrLowered : parsedIntegerMaskExprAccessesInLine? expression files.maskRegisters
      control.directive hasSingleLineMask control.context.pe cycle control.context.bar0
      control.context.bar1 control.context.tWord = some accesses)
    (prepared : prepareParsedIntegerMaskALUWriteWithForwarding files oldSlots cycle accesses
      flushSelection reduced = .ok write) :
    lm1WindowsOfWrites [write] = [] := by
  have destination := prepareParsedIntegerMaskALUWriteWithForwarding_destination_none
    files oldSlots cycle accesses flushSelection reduced write prepared
  exact lm1WindowsOfWrites_eq_nil_of_singleton_destination_none write destination

/-- **The direct branch's single window.**  The direct-access branch prepares one
write at the lowered destination, so its window list is the singleton static
window of that destination operand. -/
theorem prepareParsedIntegerALUExprCycle_alu_direct_windows
    (files : IntegerRegisterFiles) (oldSlots nextSlots : ProofsLean.MNCore.Forwarding.Slots)
    (expression : ParsedExpr) (control : ParsedMaskExecutionControl)
    (hasSingleLineMask noForward reduced : Bool) (cycle : Fin 4)
    (accesses : ParsedMaskedIntegerAccesses) (write : PreparedParsedMaskedWrite)
    (slots : ProofsLean.MNCore.Forwarding.Slots)
    (width : PEMemory.Width) (address : Fin Bank.lm1.capacity)
    (destination : accesses.destination = ⟨PEMemory.Bank.lm1, width, address⟩)
    (prepared : prepareParsedMaskedWriteWithForwarding files oldSlots cycle accesses reduced
      = .ok write) :
    lm1WindowsOfWrites [write] = [(address, count .lm1 width)] := by
  have destinationEq : write.destination =
      some ⟨PEMemory.Bank.lm1, width, address⟩ := by
    rw [prepareParsedMaskedWriteWithForwarding_destination files oldSlots cycle accesses
      reduced write prepared, destination]
  simp [lm1WindowsOfWrites, destinationEq]


/-! ## 9b. The lowering's destination is a static destination operand

The direct-access lowerer keeps the lowered destination access, and that access
is the resolution of one of the expression's own destination operands.  Combined
with `ParsedOperand.toDirectMemoryDestination?_bankWidth` this makes the `LM1`
width of every `LM1` write the static width of a destination operand. -/

theorem ParsedExpr.toDirectMaskedIntegerAccessesInLine?_destination_provenance
    (expression : ParsedExpr) (registers : ProofsLean.MNCore.Masks.RegisterFile)
    (directive : ParsedMaskDirective) (hasSingleLineMask : Bool)
    (group : Fin 4) (l2b : Fin 2) (l1b : Fin 8) (mab : Fin 16)
    (pe cycle : Fin 4) (bar0 bar1 : BitVec 12) (tWord : BitVec 32)
    (accesses : ParsedMaskedIntegerAccesses)
    (lowered : ParsedExpr.toDirectMaskedIntegerAccessesInLine? expression registers directive
      hasSingleLineMask group l2b l1b mab pe cycle bar0 bar1 tWord = some accesses) :
    ∃ destination ∈ expression.destinations,
      ParsedOperand.toDirectMemoryDestination? destination pe cycle bar0 bar1 tWord =
        some accesses.destination := by
  obtain ⟨op, sources, destinations, flush, text⟩ := expression
  simp only [ParsedExpr.toDirectMaskedIntegerAccessesInLine?] at lowered
  repeat' split at lowered
  all_goals simp_all
  all_goals rw [← lowered]

/-- **The `LM1` width of a lowered destination is static.**  If the lowered access
is an `.lm1` block of width `w`, then some destination operand of the expression
has static pair `(.lm1, w)`: the width cannot change between cycles or between
the branches that use this lowering. -/
theorem ParsedExpr.toDirectMaskedIntegerAccessesInLine?_lm1_width
    (expression : ParsedExpr) (registers : ProofsLean.MNCore.Masks.RegisterFile)
    (directive : ParsedMaskDirective) (hasSingleLineMask : Bool)
    (group : Fin 4) (l2b : Fin 2) (l1b : Fin 8) (mab : Fin 16)
    (pe cycle : Fin 4) (bar0 bar1 : BitVec 12) (tWord : BitVec 32)
    (accesses : ParsedMaskedIntegerAccesses) (width : PEMemory.Width)
    (lowered : ParsedExpr.toDirectMaskedIntegerAccessesInLine? expression registers directive
      hasSingleLineMask group l2b l1b mab pe cycle bar0 bar1 tWord = some accesses)
    (bank : accesses.destination.bank = PEMemory.Bank.lm1)
    (widthEq : accesses.destination.width = width) :
    ∃ destination ∈ expression.destinations,
      ParsedOperand.directDestinationBankWidth? destination =
        some (PEMemory.Bank.lm1, width) := by
  obtain ⟨destination, member, resolved⟩ :=
    ParsedExpr.toDirectMaskedIntegerAccessesInLine?_destination_provenance expression registers
      directive hasSingleLineMask group l2b l1b mab pe cycle bar0 bar1 tWord accesses lowered
  refine ⟨destination, member, ?_⟩
  have static := ParsedOperand.toDirectMemoryDestination?_bankWidth destination pe cycle bar0
    bar1 tWord
  rw [resolved] at static
  simp only [Option.map_some] at static
  rw [← static, bank, widthEq]


/-- **The direct branch's `LM1` width is a static destination width.** -/
theorem prepareParsedIntegerALUExprCycle_alu_direct_lm1_width
    (files : IntegerRegisterFiles) (oldSlots : ProofsLean.MNCore.Forwarding.Slots)
    (expression : ParsedExpr) (control : ParsedMaskExecutionControl)
    (hasSingleLineMask reduced : Bool) (cycle : Fin 4)
    (accesses : ParsedMaskedIntegerAccesses) (width : PEMemory.Width)
    (address : Fin Bank.lm1.capacity)
    (lowered : ParsedExpr.toDirectMaskedIntegerAccessesInLine? expression files.maskRegisters
      control.directive hasSingleLineMask control.context.group control.context.l2b
      control.context.l1b control.context.mab control.context.pe cycle control.context.bar0
      control.context.bar1 control.context.tWord = some accesses)
    (destination : accesses.destination = ⟨PEMemory.Bank.lm1, width, address⟩) :
    ∃ operand ∈ expression.destinations,
      ParsedOperand.directDestinationBankWidth? operand =
        some (PEMemory.Bank.lm1, width) := by
  have bank : accesses.destination.bank = PEMemory.Bank.lm1 := by rw [destination]
  have widthEq : accesses.destination.width = width := by rw [destination]
  exact ParsedExpr.toDirectMaskedIntegerAccessesInLine?_lm1_width expression files.maskRegisters
    control.directive hasSingleLineMask control.context.group control.context.l2b
    control.context.l1b control.context.mab control.context.pe cycle control.context.bar0
    control.context.bar1 control.context.tWord accesses width lowered bank widthEq

/-! ## 10. The remaining obligations, as exact `Prop`s

The per-branch destination analysis (sections 1–8) is unconditional.  What is
still missing for `WelcomePEPlainShapeTarget` is the *assembly* of those
per-cycle facts into the line's write list: the four-cycle fold, the
`writesUnique` bridge that makes at most one expression write `LM1`, and the
4096-PE lift from the prepared list to `next.peRegisters welcomePE`.  That is
`WelcomePEPlainStepShapeExceptImmediate`.  The single remaining *value* case is the `.immediate` row with an
`.lm1 .double` destination: its third data word is the immediate payload (for
both sparse values), a non-copy, and a `.double` window is wider than the narrow
bound, so only input-independence can refute such a line.  That is
`WelcomePEPlainImmediateDoubleObligation`. -/

/-- The static escaping case: a row of the line is an `.immediate` row with an
`.lm1` `.double` destination operand.  Its prepared data words are the payload
(§ `evaluateParsedExecutionRequest`), so neither the copy shape nor the narrow
bound applies. -/
def WelcomePEImmediateDoubleDestination (expressions : List NormalizedExpr) : Prop :=
  ∃ expression ∈ expressions.map NormalizedExpr.toParsed,
    (∃ payload sparse, expression.op = .immediate payload sparse) ∧
      ∃ destination ∈ expression.destinations,
        ParsedOperand.directDestinationBankWidth? destination =
          some (PEMemory.Bank.lm1, PEMemory.Width.double)

/-- **Remaining obligation 1 (links 1–3 assembled at the step level).**  For a
plain unrefuted line that is not in the immediate-double case, a successful step
commits the executor's write list and that list is all copied `.double` blocks or
fits four narrow windows.  The per-cycle half of this is sections 1–9; what is
left inside it is the four-cycle fold (`prepareParsedIntegerALUCycles`), the
`writesUnique` bridge (`welcomeLm1Writer_unique` plus the `writeBanks` projection)
and the per-PE lift (`executeIntegerProducerLineAtPECore` at PE 0). -/
def WelcomePEPlainStepShapeExceptImmediate : Prop :=
  ∀ expressions : List NormalizedExpr, WelcomePEUnrefuted expressions →
    (expressions.map NormalizedExpr.toParsed).all parsedExprIsPlainIntegerALU = true →
    ¬ WelcomePEImmediateDoubleDestination expressions →
    ∀ next, welcomeSealedMachine.step (.pe expressions)
        (welcomeInitialState welcomeZeroWords) = some next →
      ∃ writes, next.peRegisters welcomePE =
          commitParsedMaskedWrites
            ((welcomeInitialState welcomeZeroWords).peRegisters welcomePE) writes ∧
        (Lm1WritesDoubleCopy writes ∨ Lm1WritesNarrow writes)

/-- **Remaining obligation 2 (the immediate-double value case).**  A plain
unrefuted line with an `.immediate` row whose destination operand is an `.lm1`
`.double` block has input-independent PE 0 `LM1` output: the prepared data is the
immediate payload, which does not depend on the input
(`immediate_execution_ignores_inputs`), and `welcomeLm1Writer_unique` bounds the
`LM1` writers.  What is missing is the two-run comparison of the commit, not the
per-cycle value shape. -/
def WelcomePEPlainImmediateDoubleObligation : Prop :=
  ∀ expressions : List NormalizedExpr, WelcomePEUnrefuted expressions →
    (expressions.map NormalizedExpr.toParsed).all parsedExprIsPlainIntegerALU = true →
    WelcomePEImmediateDoubleDestination expressions →
    WelcomePEInputIndependent expressions

/-- **The plain-shape target from the two remaining obligations.** -/
theorem welcomePEPlainShapeTarget_of_two
    (shape : WelcomePEPlainStepShapeExceptImmediate)
    (immediate : WelcomePEPlainImmediateDoubleObligation) :
    WelcomePEPlainShapeTarget := by
  intro expressions unrefuted plain
  by_cases escaping : WelcomePEImmediateDoubleDestination expressions
  · exact Or.inl (immediate expressions unrefuted plain escaping)
  · refine Or.inr ?_
    intro next step
    exact shape expressions unrefuted plain escaping next step

/-- **The plain-class shape obligation from the two remaining obligations.** -/
theorem welcomePEPlainShapeObligation_of_two
    (shape : WelcomePEPlainStepShapeExceptImmediate)
    (immediate : WelcomePEPlainImmediateDoubleObligation) :
    WelcomePEPlainShapeObligation :=
  welcomePEPlainShapeObligation_of_target (welcomePEPlainShapeTarget_of_two shape immediate)

end ProofsLean.MNCore
