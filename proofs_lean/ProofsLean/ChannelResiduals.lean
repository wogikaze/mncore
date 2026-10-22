import ProofsLean.InputDependenceChannels
import ProofsLean.FootprintReconciled
import ProofsLean.PlainALUDestination
import ProofsLean.WelcomeWholeMachineOptimal

/-! # The two residuals of the channel-aware input-dependence contract

`ProofsLean/InputDependenceChannels.lean` reduces the plain-ALU `.pe` contract to
two Props, `PEPreparedListCongruent footprint expressions` (the executor's
prepared write list is a function of the channels plus the footprint words) and
`PEChannelFrame pe line` (the step preserves channel agreement).  This module
closes the first and repairs and closes the second.

## 1. The prepared-list congruence (closed, modulo footprint coverage)

The executor's integer-stage preparation is proved to be a function of

* the mask-register file (the branch selection of the nine-way lowering),
* the prepared-write reads (the two source operands of every branch), and
* the forwarding slots (only their initial value is read; the evolved slots are
  written, not read).

The proof proceeds exactly through the executor:

* §1: the per-branch read regions of the nine lowerings.
* §2: congruence of every prepared-write helper as a function of its two source
  reads and the mask-register file.
* §3: the nine-branch congruence of `prepareParsedIntegerALUExprCycle`, by the
  same `cases`/`split` analysis as `FamilyDestinationCongruence.lean` and
  `ALURequestProvenance.lean`.
* §4-§5: the lift over the four cycles, the expression list and
  `prepareParsedIntegerMatrixReadLineCycles`.
* §6: `pepreparedListCongruent_plain` — `PEPreparedListCongruent` for the
  plain-ALU family from a footprint-coverage hypothesis — and the strong form
  `PEPreparedListCongruentStrong` that also pins the prepared slots and BAR
  updates (needed by the channel frame).
* `pepreparedListCongruent_concrete_of_covers`: the same at the concrete
  footprint `plusTwoLineFootprint`, from the named residual
  `PlusTwoLineFootprintCoversPreparedReads` (the reconciliation between the
  hazard-event lowering and the executor's nine-way lowering).

## 2. The channel frame (the stated `PEChannelFrame` is *false*; its repair is closed)

The executor's forwarding update installs `pack write.data` into the `.alu`
cycle slot and marks it valid
(`updateParsedIntegerALUForwardingCycle_installs_data`).  A `.pe` line that reads
a register word therefore changes a channel in a way that depends on the bank
word it read.  `PEChannelFrame` assumes channel agreement but **no** bank-word
agreement, so channel agreement alone does not determine its conclusion for a
reading line; a *concrete* counterexample would additionally need a forward
step-existence proof for such a line (two successful steps with different reads
but equal channels), which is not attempted here.  What is proved is that the
frame's obligation is discharged by the correct hypothesis, i.e. with the
line's bank-word agreement as well:

`PEChannelFrameOn footprint pe line`.

`PEChannelFrameOn` is proved for plain-ALU `.pe` lines
(`plain_pe_channelFrameOn_of_prepared`, `plain_pe_channelFrameOn_concrete`) by
the walk frame (unvisited PEs are untouched), the per-PE core extraction
(`executeIntegerProducerLineAtPECore_plain_fields`) and the forwarding-channel
formula `lineForwardingChannel`.  `nop` and `mv` satisfy it unconditionally, and
`PEChannelFrame` implies it.

## 3. The plus-two kernel

`plain_pe_lineDeterminedAtChan_of_preparedOn` redoes the whole `.pe` reduction
with the repaired frame, and `plain_pe_lineDeterminedAtChan_concrete` discharges
plain-ALU lines at the concrete footprint from the coverage residual alone.
`plusTwoWriteDeterminationChan_of_all_discharged` gives
`PlusTwoWriteDeterminationChan` — the channel-aware replacement of the old false
`PlusTwoWriteDetermination` — for programs whose lines are `nop`, `mv` or plain
`.pe`, and
`plusTwo_not_correct_of_concrete_footprint_avoids_chan_of_discharged` is the
end-to-end "a program that never reads input `j` is incorrect" theorem at the
concrete footprint and the channel-aware contract.

## 4. The exact remaining residual

```
def PlusTwoLineFootprintCoversPreparedReads : Prop :=
  ∀ expressions, (map toParsed expressions).all parsedExprIsPlainIntegerALU = true →
    ∀ state,
      preparedListReadSet (state.peRegisters plusTwoPE).maskRegisters
        ((map toParsed expressions).filter parsedExprIsIntegerMatrixReadStageInput)
        (parsedPEHazardControl state plusTwoPE)
      ⊆ plusTwoLineFootprint (.pe expressions) state
```

i.e. the hazard-event read footprint covers every word the executor's nine-way
lowering reads.  This is the only statement not discharged here (beyond the
line classes that are not analysed at all, e.g. float/matrix families).

No `sorry`, no `admit`, no `native_decide`, no new axioms, no existing module is
edited. -/

namespace ProofsLean.MNCore

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open Issue
open PEMemory

/-! ## 1. Read regions of the lowerings

Every helper of `ParsedIntegerStep` reads its operands through
`ParsedIntegerInput.readWithForwarding` (a `.memory` source consults exactly
`accessRegion`) or through `ParsedIntegerInput.read` (the constant writers).
The predicates below name the region a lowering reads, so that the footprint
coverage hypothesis can quantify over all nine branch resolvers at once. -/

/-- The register words a source operand reads. -/
def inputReadsWithin (R : Set WordRef) (input : ParsedIntegerInput) : Prop :=
  ParsedIntegerInput.readsRegion input ⊆ R

theorem inputReadsWithin_of_memory {R : Set WordRef} {access : DirectMemoryAccess}
    {rounded : Bool} (h : accessRegion access ⊆ R) :
    inputReadsWithin R (.memory access rounded) := h

/-- The read region of a `ParsedMaskedIntegerAccesses` pair. -/
def maskedIntegerReads (accesses : ParsedMaskedIntegerAccesses) : Set WordRef :=
  ParsedIntegerInput.readsRegion accesses.sourceX ∪
    ParsedIntegerInput.readsRegion accesses.sourceY

/-- The read region of a mask-register writer. -/
def maskAccessesReads (accesses : ParsedIntegerMaskAccesses) : Set WordRef :=
  accessRegion accesses.sourceX ∪ accessRegion accesses.sourceY

/-- The read region of a no-write writer. -/
def noWriteAccessesReads (accesses : ParsedIntegerNoWriteAccesses) : Set WordRef :=
  ParsedIntegerInput.readsRegion accesses.sourceX ∪
    ParsedIntegerInput.readsRegion accesses.sourceY

/-- The read region of a BAR writer. -/
def barAccessesReads (accesses : ParsedIntegerBarAccesses) : Set WordRef :=
  ParsedIntegerInput.readsRegion accesses.sourceX ∪
    ParsedIntegerInput.readsRegion accesses.sourceY

/-- The read region of an input-mask writer. -/
def maskInputAccessesReads (accesses : ParsedIntegerMaskInputAccesses) : Set WordRef :=
  ParsedIntegerInput.readsRegion accesses.sourceX ∪
    ParsedIntegerInput.readsRegion accesses.sourceY

/-- The read region of a memory-then-input writer. -/
def maskMemoryThenInputReads (accesses : ParsedIntegerMaskMemoryThenInputAccesses) :
    Set WordRef :=
  ParsedIntegerInput.readsRegion accesses.sourceX ∪
    ParsedIntegerInput.readsRegion accesses.sourceY

/-- The read region of an input-then-memory writer. -/
def maskInputThenMemoryReads (accesses : ParsedIntegerMaskInputThenMemoryAccesses) :
    Set WordRef :=
  ParsedIntegerInput.readsRegion accesses.sourceX ∪
    ParsedIntegerInput.readsRegion accesses.sourceY

/-! ## 2. Prepared writes are functions of the reads and the mask registers -/

theorem prepareParsedMaskedWrite_congr
    (files files' : IntegerRegisterFiles) (accesses : ParsedMaskedIntegerAccesses)
    (reduced : Bool)
    (hX : ParsedIntegerInput.read files accesses.sourceX =
      ParsedIntegerInput.read files' accesses.sourceX)
    (hY : ParsedIntegerInput.read files accesses.sourceY =
      ParsedIntegerInput.read files' accesses.sourceY) :
    prepareParsedMaskedWrite files accesses reduced =
      prepareParsedMaskedWrite files' accesses reduced := by
  unfold prepareParsedMaskedWrite
  dsimp only
  rw [hX, hY]

/-- **Read locality of one source operand.**  Agreement on the source's read
region makes the plain read the same on both files. -/
theorem ParsedIntegerInput.read_congr_of_agree
    (files files' : IntegerRegisterFiles) (input : ParsedIntegerInput)
    (h : FilesAgreeOn (ParsedIntegerInput.readsRegion input) files files') :
    ParsedIntegerInput.read files input = ParsedIntegerInput.read files' input := by
  cases input with
  | memory access rounded =>
      exact ParsedIntegerInput.read_congr_memory files files' access rounded h
  | fixed value => rfl
  | forward kind rounded => rfl

theorem prepareParsedMaskedWrite_congr_of_agree
    (files files' : IntegerRegisterFiles) (accesses : ParsedMaskedIntegerAccesses)
    (reduced : Bool)
    (h : FilesAgreeOn (maskedIntegerReads accesses) files files') :
    prepareParsedMaskedWrite files accesses reduced =
      prepareParsedMaskedWrite files' accesses reduced := by
  apply prepareParsedMaskedWrite_congr
  · exact ParsedIntegerInput.read_congr_of_agree files files' accesses.sourceX
      (fun w hw => h w (Or.inl hw))
  · exact ParsedIntegerInput.read_congr_of_agree files files' accesses.sourceY
      (fun w hw => h w (Or.inr hw))

theorem prepareParsedIntegerMaskALUWriteWithForwarding_congr
    (files files' : IntegerRegisterFiles) (slots : ProofsLean.MNCore.Forwarding.Slots)
    (cycle : Fin 4) (accesses : ParsedIntegerMaskAccesses)
    (flushSelection : Option PEWordSelection) (reduced : Bool)
    (hX : ParsedIntegerInput.readWithForwarding files slots cycle
        (.memory accesses.sourceX accesses.sourceXRounded) =
      ParsedIntegerInput.readWithForwarding files' slots cycle
        (.memory accesses.sourceX accesses.sourceXRounded))
    (hY : ParsedIntegerInput.readWithForwarding files slots cycle
        (.memory accesses.sourceY accesses.sourceYRounded) =
      ParsedIntegerInput.readWithForwarding files' slots cycle
        (.memory accesses.sourceY accesses.sourceYRounded)) :
    prepareParsedIntegerMaskALUWriteWithForwarding files slots cycle accesses
        flushSelection reduced =
      prepareParsedIntegerMaskALUWriteWithForwarding files' slots cycle accesses
        flushSelection reduced := by
  unfold prepareParsedIntegerMaskALUWriteWithForwarding
  dsimp only
  rw [hX, hY]

theorem prepareParsedIntegerMaskALUWriteWithForwarding_congr_of_agree
    (files files' : IntegerRegisterFiles) (slots : ProofsLean.MNCore.Forwarding.Slots)
    (cycle : Fin 4) (accesses : ParsedIntegerMaskAccesses)
    (flushSelection : Option PEWordSelection) (reduced : Bool)
    (h : FilesAgreeOn (maskAccessesReads accesses) files files') :
    prepareParsedIntegerMaskALUWriteWithForwarding files slots cycle accesses
        flushSelection reduced =
      prepareParsedIntegerMaskALUWriteWithForwarding files' slots cycle accesses
        flushSelection reduced := by
  apply prepareParsedIntegerMaskALUWriteWithForwarding_congr
  · exact ParsedIntegerInput.readWithForwarding_memory_congr files files' slots cycle
      accesses.sourceX accesses.sourceXRounded (fun w hw => h w (Or.inl hw))
  · exact ParsedIntegerInput.readWithForwarding_memory_congr files files' slots cycle
      accesses.sourceY accesses.sourceYRounded (fun w hw => h w (Or.inr hw))

theorem prepareParsedIntegerMaskInputALUWriteWithForwarding_congr
    (files files' : IntegerRegisterFiles) (slots : ProofsLean.MNCore.Forwarding.Slots)
    (cycle : Fin 4) (accesses : ParsedIntegerMaskInputAccesses)
    (flushSelection : Option PEWordSelection) (reduced : Bool)
    (hX : ParsedIntegerInput.readWithForwarding files slots cycle accesses.sourceX =
      ParsedIntegerInput.readWithForwarding files' slots cycle accesses.sourceX)
    (hY : ParsedIntegerInput.readWithForwarding files slots cycle accesses.sourceY =
      ParsedIntegerInput.readWithForwarding files' slots cycle accesses.sourceY) :
    prepareParsedIntegerMaskInputALUWriteWithForwarding files slots cycle accesses
        flushSelection reduced =
      prepareParsedIntegerMaskInputALUWriteWithForwarding files' slots cycle accesses
        flushSelection reduced := by
  unfold prepareParsedIntegerMaskInputALUWriteWithForwarding
  dsimp only
  rw [hX, hY]

theorem prepareParsedIntegerMaskInputALUWriteWithForwarding_congr_of_agree
    (files files' : IntegerRegisterFiles) (slots : ProofsLean.MNCore.Forwarding.Slots)
    (cycle : Fin 4) (accesses : ParsedIntegerMaskInputAccesses)
    (flushSelection : Option PEWordSelection) (reduced : Bool)
    (h : FilesAgreeOn (maskInputAccessesReads accesses) files files') :
    prepareParsedIntegerMaskInputALUWriteWithForwarding files slots cycle accesses
        flushSelection reduced =
      prepareParsedIntegerMaskInputALUWriteWithForwarding files' slots cycle accesses
        flushSelection reduced := by
  apply prepareParsedIntegerMaskInputALUWriteWithForwarding_congr
  · exact ParsedIntegerInput.readWithForwarding_congr_of_agree files files' slots cycle
      accesses.sourceX (fun w hw => h w (Or.inl hw))
  · exact ParsedIntegerInput.readWithForwarding_congr_of_agree files files' slots cycle
      accesses.sourceY (fun w hw => h w (Or.inr hw))

theorem prepareParsedIntegerNoWriteALUWithForwarding_congr
    (files files' : IntegerRegisterFiles) (slots : ProofsLean.MNCore.Forwarding.Slots)
    (cycle : Fin 4) (accesses : ParsedIntegerNoWriteAccesses) (reduced : Bool)
    (hX : ParsedIntegerInput.readWithForwarding files slots cycle accesses.sourceX =
      ParsedIntegerInput.readWithForwarding files' slots cycle accesses.sourceX)
    (hY : ParsedIntegerInput.readWithForwarding files slots cycle accesses.sourceY =
      ParsedIntegerInput.readWithForwarding files' slots cycle accesses.sourceY) :
    prepareParsedIntegerNoWriteALUWithForwarding files slots cycle accesses reduced =
      prepareParsedIntegerNoWriteALUWithForwarding files' slots cycle accesses reduced := by
  unfold prepareParsedIntegerNoWriteALUWithForwarding
  dsimp only
  rw [hX, hY]

theorem prepareParsedIntegerNoWriteALUWithForwarding_congr_of_agree
    (files files' : IntegerRegisterFiles) (slots : ProofsLean.MNCore.Forwarding.Slots)
    (cycle : Fin 4) (accesses : ParsedIntegerNoWriteAccesses) (reduced : Bool)
    (h : FilesAgreeOn (noWriteAccessesReads accesses) files files') :
    prepareParsedIntegerNoWriteALUWithForwarding files slots cycle accesses reduced =
      prepareParsedIntegerNoWriteALUWithForwarding files' slots cycle accesses reduced := by
  apply prepareParsedIntegerNoWriteALUWithForwarding_congr
  · exact ParsedIntegerInput.readWithForwarding_congr_of_agree files files' slots cycle
      accesses.sourceX (fun w hw => h w (Or.inl hw))
  · exact ParsedIntegerInput.readWithForwarding_congr_of_agree files files' slots cycle
      accesses.sourceY (fun w hw => h w (Or.inr hw))

theorem prepareParsedIntegerBarALUWithForwarding_congr
    (files files' : IntegerRegisterFiles) (slots : ProofsLean.MNCore.Forwarding.Slots)
    (cycle : Fin 4) (accesses : ParsedIntegerBarAccesses) (reduced : Bool)
    (hX : ParsedIntegerInput.readWithForwarding files slots cycle accesses.sourceX =
      ParsedIntegerInput.readWithForwarding files' slots cycle accesses.sourceX)
    (hY : ParsedIntegerInput.readWithForwarding files slots cycle accesses.sourceY =
      ParsedIntegerInput.readWithForwarding files' slots cycle accesses.sourceY) :
    prepareParsedIntegerBarALUWithForwarding files slots cycle accesses reduced =
      prepareParsedIntegerBarALUWithForwarding files' slots cycle accesses reduced := by
  unfold prepareParsedIntegerBarALUWithForwarding
  dsimp only
  rw [hX, hY]

theorem prepareParsedIntegerBarALUWithForwarding_congr_of_agree
    (files files' : IntegerRegisterFiles) (slots : ProofsLean.MNCore.Forwarding.Slots)
    (cycle : Fin 4) (accesses : ParsedIntegerBarAccesses) (reduced : Bool)
    (h : FilesAgreeOn (barAccessesReads accesses) files files') :
    prepareParsedIntegerBarALUWithForwarding files slots cycle accesses reduced =
      prepareParsedIntegerBarALUWithForwarding files' slots cycle accesses reduced := by
  apply prepareParsedIntegerBarALUWithForwarding_congr
  · exact ParsedIntegerInput.readWithForwarding_congr_of_agree files files' slots cycle
      accesses.sourceX (fun w hw => h w (Or.inl hw))
  · exact ParsedIntegerInput.readWithForwarding_congr_of_agree files files' slots cycle
      accesses.sourceY (fun w hw => h w (Or.inr hw))

theorem prepareParsedIntegerMaskMemoryThenInputALUWritesWithForwarding_congr
    (files files' : IntegerRegisterFiles) (slots : ProofsLean.MNCore.Forwarding.Slots)
    (cycle : Fin 4) (accesses : ParsedIntegerMaskMemoryThenInputAccesses)
    (flushSelection : Option PEWordSelection) (reduced : Bool)
    (hX : ParsedIntegerInput.readWithForwarding files slots cycle accesses.sourceX =
      ParsedIntegerInput.readWithForwarding files' slots cycle accesses.sourceX)
    (hY : ParsedIntegerInput.readWithForwarding files slots cycle accesses.sourceY =
      ParsedIntegerInput.readWithForwarding files' slots cycle accesses.sourceY) :
    prepareParsedIntegerMaskMemoryThenInputALUWritesWithForwarding files slots cycle accesses
        flushSelection reduced =
      prepareParsedIntegerMaskMemoryThenInputALUWritesWithForwarding files' slots cycle accesses
        flushSelection reduced := by
  unfold prepareParsedIntegerMaskMemoryThenInputALUWritesWithForwarding
  dsimp only
  rw [hX, hY]

theorem prepareParsedIntegerMaskMemoryThenInputALUWritesWithForwarding_congr_of_agree
    (files files' : IntegerRegisterFiles) (slots : ProofsLean.MNCore.Forwarding.Slots)
    (cycle : Fin 4) (accesses : ParsedIntegerMaskMemoryThenInputAccesses)
    (flushSelection : Option PEWordSelection) (reduced : Bool)
    (h : FilesAgreeOn (maskMemoryThenInputReads accesses) files files') :
    prepareParsedIntegerMaskMemoryThenInputALUWritesWithForwarding files slots cycle accesses
        flushSelection reduced =
      prepareParsedIntegerMaskMemoryThenInputALUWritesWithForwarding files' slots cycle accesses
        flushSelection reduced := by
  apply prepareParsedIntegerMaskMemoryThenInputALUWritesWithForwarding_congr
  · exact ParsedIntegerInput.readWithForwarding_congr_of_agree files files' slots cycle
      accesses.sourceX (fun w hw => h w (Or.inl hw))
  · exact ParsedIntegerInput.readWithForwarding_congr_of_agree files files' slots cycle
      accesses.sourceY (fun w hw => h w (Or.inr hw))

theorem prepareParsedIntegerMaskInputThenMemoryALUWritesWithForwarding_congr
    (files files' : IntegerRegisterFiles) (slots : ProofsLean.MNCore.Forwarding.Slots)
    (cycle : Fin 4) (accesses : ParsedIntegerMaskInputThenMemoryAccesses)
    (directive : ParsedMaskDirective) (hasSingleLineMask : Bool)
    (flushSelection : Option PEWordSelection) (reduced : Bool)
    (hMask : files.maskRegisters = files'.maskRegisters)
    (hX : ParsedIntegerInput.readWithForwarding files slots cycle accesses.sourceX =
      ParsedIntegerInput.readWithForwarding files' slots cycle accesses.sourceX)
    (hY : ParsedIntegerInput.readWithForwarding files slots cycle accesses.sourceY =
      ParsedIntegerInput.readWithForwarding files' slots cycle accesses.sourceY) :
    prepareParsedIntegerMaskInputThenMemoryALUWritesWithForwarding files slots cycle accesses
        directive hasSingleLineMask flushSelection reduced =
      prepareParsedIntegerMaskInputThenMemoryALUWritesWithForwarding files' slots cycle accesses
        directive hasSingleLineMask flushSelection reduced := by
  unfold prepareParsedIntegerMaskInputThenMemoryALUWritesWithForwarding
  dsimp only
  rw [hX, hY, hMask]

theorem prepareParsedIntegerMaskInputThenMemoryALUWritesWithForwarding_congr_of_agree
    (files files' : IntegerRegisterFiles) (slots : ProofsLean.MNCore.Forwarding.Slots)
    (cycle : Fin 4) (accesses : ParsedIntegerMaskInputThenMemoryAccesses)
    (directive : ParsedMaskDirective) (hasSingleLineMask : Bool)
    (flushSelection : Option PEWordSelection) (reduced : Bool)
    (hMask : files.maskRegisters = files'.maskRegisters)
    (h : FilesAgreeOn (maskInputThenMemoryReads accesses) files files') :
    prepareParsedIntegerMaskInputThenMemoryALUWritesWithForwarding files slots cycle accesses
        directive hasSingleLineMask flushSelection reduced =
      prepareParsedIntegerMaskInputThenMemoryALUWritesWithForwarding files' slots cycle accesses
        directive hasSingleLineMask flushSelection reduced := by
  apply prepareParsedIntegerMaskInputThenMemoryALUWritesWithForwarding_congr files files'
    slots cycle accesses directive hasSingleLineMask flushSelection reduced hMask
  · exact ParsedIntegerInput.readWithForwarding_congr_of_agree files files' slots cycle
      accesses.sourceX (fun w hw => h w (Or.inl hw))
  · exact ParsedIntegerInput.readWithForwarding_congr_of_agree files files' slots cycle
      accesses.sourceY (fun w hw => h w (Or.inr hw))

theorem prepareParsedConstantTarget_congr
    (files files' : IntegerRegisterFiles) (cycle : Fin 4)
    (target : ParsedConstantDestination)
    (h : ∀ accesses, target = .memory accesses →
      FilesAgreeOn (maskedIntegerReads accesses) files files') :
    prepareParsedConstantTarget files cycle target =
      prepareParsedConstantTarget files' cycle target := by
  cases target with
  | memory accesses =>
      exact prepareParsedMaskedWrite_congr_of_agree files files' accesses false
        (h accesses rfl)
  | maskRegister entry => rfl
  | noWrite => rfl

theorem prepareParsedMaskedConstantWrites_congr
    (files files' : IntegerRegisterFiles) (cycle : Fin 4)
    (targets : List ParsedConstantDestination)
    (h : ∀ target, target ∈ targets → ∀ accesses, target = .memory accesses →
      FilesAgreeOn (maskedIntegerReads accesses) files files') :
    prepareParsedMaskedConstantWrites files cycle targets =
      prepareParsedMaskedConstantWrites files' cycle targets := by
  induction targets with
  | nil => rfl
  | cons target rest ih =>
      have head := prepareParsedConstantTarget_congr files files' cycle target
        (fun accesses same => h target (by simp) accesses same)
      have ih' := ih (fun item member accesses same =>
        h item (by simp [member]) accesses same)
      unfold prepareParsedMaskedConstantWrites
      rw [head]
      cases result : prepareParsedConstantTarget files' cycle target with
      | failure => rfl
      | unknown => rfl
      | ok write => dsimp only; rw [ih']


/-! ## 3. The read set of one lowered ALU cycle -/

/-- The words a `ParsedMaskedIntegerAccesses` pair reads, as an option. -/
def optionMaskedReads : Option ParsedMaskedIntegerAccesses → Set WordRef
  | none => ∅
  | some accesses => maskedIntegerReads accesses

/-- The words a list-lowering reads: only its head is ever read. -/
def optionMaskedListReads : Option (List ParsedMaskedIntegerAccesses) → Set WordRef
  | none => ∅
  | some [] => ∅
  | some (access :: _) => maskedIntegerReads access

def optionMaskReads : Option ParsedIntegerMaskAccesses → Set WordRef
  | none => ∅
  | some accesses => maskAccessesReads accesses

def optionNoWriteReads : Option ParsedIntegerNoWriteAccesses → Set WordRef
  | none => ∅
  | some accesses => noWriteAccessesReads accesses

def optionBarReads : Option ParsedIntegerBarAccesses → Set WordRef
  | none => ∅
  | some accesses => barAccessesReads accesses

def optionMaskInputReads : Option ParsedIntegerMaskInputAccesses → Set WordRef
  | none => ∅
  | some accesses => maskInputAccessesReads accesses

def optionMaskMemoryThenInputReads :
    Option ParsedIntegerMaskMemoryThenInputAccesses → Set WordRef
  | none => ∅
  | some accesses => maskMemoryThenInputReads accesses

def optionMaskInputThenMemoryReads :
    Option ParsedIntegerMaskInputThenMemoryAccesses → Set WordRef
  | none => ∅
  | some accesses => maskInputThenMemoryReads accesses

/-- The words one constant destination reads (only a memory destination reads,
through the constant producer's source slots). -/
def constantTargetReads : ParsedConstantDestination → Set WordRef
  | .memory accesses => maskedIntegerReads accesses
  | .maskRegister _ => ∅
  | .noWrite => ∅

def optionConstantReads : Option (List ParsedConstantDestination) → Set WordRef
  | none => ∅
  | some targets => {w | ∃ target ∈ targets, w ∈ constantTargetReads target}

/-- **The words one lowered ALU cycle reads.**  In the `.alu` case this is the
union of the read regions of the eight branch resolvers of
`prepareParsedIntegerALUExprCycle`; in the `.zero` / `.immediate` case it is the
union of the constant destinations' regions; every other op reads nothing. -/
def aluCycleReadSet (registers : ProofsLean.MNCore.Masks.RegisterFile)
    (expression : ParsedExpr) (control : ParsedMaskExecutionControl)
    (hasSingleLineMask : Bool) (cycle : Fin 4) : Set WordRef :=
  let directive := control.directive
  let c := control.context
  match expression.op with
  | .alu .. =>
      optionMaskedReads (ParsedExpr.toDirectMaskedIntegerAccessesInLine? expression registers
          directive hasSingleLineMask c.group c.l2b c.l1b c.mab c.pe cycle c.bar0 c.bar1
          c.tWord)
        ∪ optionMaskedListReads (ParsedExpr.toDirectMaskedIntegerWritesInLine? expression
            registers directive hasSingleLineMask c.group c.l2b c.l1b c.mab c.pe cycle c.bar0
            c.bar1 c.tWord)
        ∪ optionMaskReads (parsedIntegerMaskExprAccessesInLine? expression registers
            directive hasSingleLineMask c.pe cycle c.bar0 c.bar1 c.tWord)
        ∪ optionNoWriteReads (parsedIntegerNoWriteExprAccessesInLine? expression registers
            c.pe cycle c.group c.l2b c.l1b c.mab c.bar0 c.bar1 c.tWord)
        ∪ optionBarReads (parsedIntegerBarExprAccessesInLine? expression registers
            directive hasSingleLineMask c.group c.l2b c.l1b c.mab c.pe cycle c.bar0 c.bar1
            c.tWord)
        ∪ optionMaskInputReads (parsedIntegerMaskInputExprAccessesInLine? expression
            registers directive hasSingleLineMask c.group c.l2b c.l1b c.mab c.pe cycle
            c.bar0 c.bar1 c.tWord)
        ∪ optionMaskMemoryThenInputReads
            (parsedIntegerMaskMemoryThenInputExprAccessesInLine? expression registers
              directive hasSingleLineMask c.group c.l2b c.l1b c.mab c.pe cycle c.bar0 c.bar1
              c.tWord)
        ∪ optionMaskInputThenMemoryReads
            (parsedIntegerMaskInputThenMemoryExprAccessesInLine? expression registers
              directive hasSingleLineMask c.group c.l2b c.l1b c.mab c.pe cycle c.bar0 c.bar1
              c.tWord)
  | .zero | .immediate .. =>
      optionConstantReads (ParsedExpr.toDirectMaskedConstantWrites? expression registers
        directive hasSingleLineMask c.group c.l2b c.l1b c.mab c.pe cycle c.bar0 c.bar1 c.tWord)
  | _ => ∅



/-! ## 4. One lowered ALU cycle is a function of its reads -/

/-- **The `.zero` / `.immediate` branch.**  The constant-producer preparation
reads its destination regions (the lowering gives the constant write that
destination as both of its sources) and otherwise only the mask-register file;
two runs with the same mask registers and read agreement prepare the same write
list and the same output slots. -/
theorem prepareParsedIntegerALUExprCycle_congr_constant
    (filesA filesB : IntegerRegisterFiles)
    (oldSlotsA oldSlotsB nextSlotsA nextSlotsB : ProofsLean.MNCore.Forwarding.Slots)
    (expression : ParsedExpr) (control : ParsedMaskExecutionControl)
    (hasSingleLineMask noForward reduced : Bool) (cycle : Fin 4) (R : Set WordRef)
    (constant : expression.op = .zero ∨
      ∃ payload sparse, expression.op = .immediate payload sparse)
    (maskEq : filesA.maskRegisters = filesB.maskRegisters)
    (nextEq : nextSlotsA = nextSlotsB)
    (readsWithin : aluCycleReadSet filesA.maskRegisters expression control hasSingleLineMask
      cycle ⊆ R)
    (agree : FilesAgreeOn R filesA filesB)
    (writesA : List PreparedParsedMaskedWrite) (slotsA : ProofsLean.MNCore.Forwarding.Slots)
    (writesB : List PreparedParsedMaskedWrite) (slotsB : ProofsLean.MNCore.Forwarding.Slots)
    (hA : prepareParsedIntegerALUExprCycle filesA oldSlotsA nextSlotsA expression control
        hasSingleLineMask noForward reduced cycle = .ok (writesA, slotsA))
    (hB : prepareParsedIntegerALUExprCycle filesB oldSlotsB nextSlotsB expression control
        hasSingleLineMask noForward reduced cycle = .ok (writesB, slotsB)) :
    writesA = writesB ∧ slotsA = slotsB := by
  unfold prepareParsedIntegerALUExprCycle at hA hB
  rw [← maskEq] at hB
  rw [← nextEq] at hB
  rcases constant with hz | ⟨payload, sparse, hi⟩
  · simp only [hz] at hA hB
    cases dc : ParsedExpr.toDirectMaskedConstantWrites? expression filesA.maskRegisters
        control.directive hasSingleLineMask control.context.group control.context.l2b
        control.context.l1b control.context.mab control.context.pe cycle control.context.bar0
        control.context.bar1 control.context.tWord with
    | none => simp_all
    | some targets =>
        simp only [dc] at hA hB
        cases cA : prepareParsedMaskedConstantWrites filesA cycle targets with
        | failure => simp_all
        | unknown => simp_all
        | ok destinationWritesA =>
            cases cB : prepareParsedMaskedConstantWrites filesB cycle targets with
            | failure => simp_all
            | unknown => simp_all
            | ok destinationWritesB =>
                simp only [cA, cB] at hA hB
                have same := prepareParsedMaskedConstantWrites_congr filesA filesB cycle targets
                  (fun target member accesses same => fun w hw => agree w (readsWithin (by
                    simp only [aluCycleReadSet, hz, dc, optionConstantReads, Set.mem_union]
                    exact ⟨target, member, by simpa [constantTargetReads, same] using hw⟩)))
                rw [cA, cB] at same
                have writesEq : destinationWritesA = destinationWritesB :=
                  StepResult.ok.inj same
                rw [writesEq] at hA
                exact Prod.mk.inj (StepResult.ok.inj (hA.symm.trans hB))
  · simp only [hi] at hA hB
    cases dc : ParsedExpr.toDirectMaskedConstantWrites? expression filesA.maskRegisters
        control.directive hasSingleLineMask control.context.group control.context.l2b
        control.context.l1b control.context.mab control.context.pe cycle control.context.bar0
        control.context.bar1 control.context.tWord with
    | none => simp_all
    | some targets =>
        simp only [dc] at hA hB
        cases cA : prepareParsedMaskedConstantWrites filesA cycle targets with
        | failure => simp_all
        | unknown => simp_all
        | ok destinationWritesA =>
            cases cB : prepareParsedMaskedConstantWrites filesB cycle targets with
            | failure => simp_all
            | unknown => simp_all
            | ok destinationWritesB =>
                simp only [cA, cB] at hA hB
                have same := prepareParsedMaskedConstantWrites_congr filesA filesB cycle targets
                  (fun target member accesses same => fun w hw => agree w (readsWithin (by
                    simp only [aluCycleReadSet, hi, dc, optionConstantReads, Set.mem_union]
                    exact ⟨target, member, by simpa [constantTargetReads, same] using hw⟩)))
                rw [cA, cB] at same
                have writesEq : destinationWritesA = destinationWritesB :=
                  StepResult.ok.inj same
                rw [writesEq] at hA
                exact Prod.mk.inj (StepResult.ok.inj (hA.symm.trans hB))


/-- **One lowered ALU cycle is a function of its reads.**  Two successful runs
of `prepareParsedIntegerALUExprCycle` on files that agree on the mask-register
file and on every word of the cycle's read set prepare the same write list and
the same output forwarding slots.

The nine branches of the lowering are closed with the `cases`/`split` analysis
of `PlainALUDestination.lean` §4, but with full write-record congruence (not
just destinations): every branch's writes are a function of the branch's two
source reads, and the branch selection itself only reads `files.maskRegisters`. -/
theorem prepareParsedIntegerALUExprCycle_congr
    (filesA filesB : IntegerRegisterFiles)
    (oldSlotsA oldSlotsB nextSlotsA nextSlotsB : ProofsLean.MNCore.Forwarding.Slots)
    (expression : ParsedExpr) (control : ParsedMaskExecutionControl)
    (hasSingleLineMask noForward reduced : Bool) (cycle : Fin 4) (R : Set WordRef)
    (maskEq : filesA.maskRegisters = filesB.maskRegisters)
    (slotsEq : oldSlotsA = oldSlotsB)
    (nextEq : nextSlotsA = nextSlotsB)
    (readsWithin : aluCycleReadSet filesA.maskRegisters expression control hasSingleLineMask
      cycle ⊆ R)
    (agree : FilesAgreeOn R filesA filesB)
    (writesA : List PreparedParsedMaskedWrite) (slotsA : ProofsLean.MNCore.Forwarding.Slots)
    (writesB : List PreparedParsedMaskedWrite) (slotsB : ProofsLean.MNCore.Forwarding.Slots)
    (hA : prepareParsedIntegerALUExprCycle filesA oldSlotsA nextSlotsA expression control
        hasSingleLineMask noForward reduced cycle = .ok (writesA, slotsA))
    (hB : prepareParsedIntegerALUExprCycle filesB oldSlotsB nextSlotsB expression control
        hasSingleLineMask noForward reduced cycle = .ok (writesB, slotsB)) :
    writesA = writesB ∧ slotsA = slotsB := by
  unfold prepareParsedIntegerALUExprCycle at hA hB
  cases hop : expression.op with
  | «alu» name precision unsigned arg =>
      simp only [hop] at hA hB
      rw [← maskEq] at hB
      rw [← slotsEq] at hB
      rw [← nextEq] at hB
      cases d1 : ParsedExpr.toDirectMaskedIntegerAccessesInLine? expression filesA.maskRegisters
          control.directive hasSingleLineMask control.context.group control.context.l2b
          control.context.l1b control.context.mab control.context.pe cycle control.context.bar0
          control.context.bar1 control.context.tWord with
      | some accesses =>
          simp only [d1] at hA hB
          cases pA : prepareParsedMaskedWriteWithForwarding filesA oldSlotsA cycle accesses reduced with
          | failure => simp_all
          | unknown => simp_all
          | ok writeA =>
              cases pB : prepareParsedMaskedWriteWithForwarding filesB oldSlotsA cycle accesses reduced with
              | failure => simp_all
              | unknown => simp_all
              | ok writeB =>
                  have covered : ∀ w, w ∈ maskedIntegerReads accesses → w ∈ R :=
                    fun w hw => readsWithin (by
                      simp only [aluCycleReadSet, hop, d1, optionMaskedReads, Set.mem_union]
                      tauto)
                  have same :=
                    prepareParsedMaskedWriteWithForwarding_congr_of_agree filesA filesB oldSlotsA
                      cycle accesses reduced
                      (fun w hw => agree w (covered w (Or.inl hw)))
                      (fun w hw => agree w (covered w (Or.inr hw)))
                  rw [pA, pB] at same
                  have writeEq : writeA = writeB := StepResult.ok.inj same
                  obtain ⟨slotsA', hupdA⟩ :=
                    updateParsedIntegerALUForwardingCycle_ok_exists nextSlotsA cycle writeA noForward
                  obtain ⟨slotsB', hupdB⟩ :=
                    updateParsedIntegerALUForwardingCycle_ok_exists nextSlotsA cycle writeB noForward
                  simp only [pA, pB, hupdA, hupdB, StepResult.ok.injEq, Prod.mk.injEq] at hA hB
                  refine ⟨?_, ?_⟩
                  · rw [← hA.1, ← hB.1, writeEq]
                  · rw [← hA.2, ← hB.2]
                    rw [← writeEq] at hupdB
                    rw [hupdA] at hupdB
                    exact StepResult.ok.inj hupdB
      | none =>
          simp only [d1] at hA hB
          cases d2 : ParsedExpr.toDirectMaskedIntegerWritesInLine? expression filesA.maskRegisters
              control.directive hasSingleLineMask control.context.group control.context.l2b
              control.context.l1b control.context.mab control.context.pe cycle
              control.context.bar0 control.context.bar1 control.context.tWord with
          | some accesses =>
              rcases accesses with _ | ⟨access, rest⟩
              · simp_all
              · simp only [d2] at hA hB
                cases pA : prepareParsedMaskedWriteWithForwarding filesA oldSlotsA cycle access reduced with
                | failure => simp_all
                | unknown => simp_all
                | ok writeA =>
                    cases pB : prepareParsedMaskedWriteWithForwarding filesB oldSlotsA cycle access reduced with
                    | failure => simp_all
                    | unknown => simp_all
                    | ok writeB =>
                        have covered : ∀ w, w ∈ maskedIntegerReads access → w ∈ R :=
                          fun w hw => readsWithin (by
                            simp only [aluCycleReadSet, hop, d1, d2, optionMaskedListReads,
                              Set.mem_union]
                            tauto)
                        have same :=
                          prepareParsedMaskedWriteWithForwarding_congr_of_agree filesA filesB
                            oldSlotsA cycle access reduced
                            (fun w hw => agree w (covered w (Or.inl hw)))
                            (fun w hw => agree w (covered w (Or.inr hw)))
                        rw [pA, pB] at same
                        have writeEq : writeA = writeB := StepResult.ok.inj same
                        obtain ⟨slotsA', hupdA⟩ :=
                          updateParsedIntegerALUForwardingCycle_ok_exists nextSlotsA cycle writeA
                            noForward
                        obtain ⟨slotsB', hupdB⟩ :=
                          updateParsedIntegerALUForwardingCycle_ok_exists nextSlotsA cycle writeB
                            noForward
                        simp only [pA, pB, hupdA, hupdB, StepResult.ok.injEq, Prod.mk.injEq]
                          at hA hB
                        refine ⟨?_, ?_⟩
                        · rw [← hA.1, ← hB.1, writeEq]
                        · rw [← hA.2, ← hB.2]
                          rw [← writeEq] at hupdB
                          rw [hupdA] at hupdB
                          exact StepResult.ok.inj hupdB
          | none =>
              simp only [d2] at hA hB
              cases d3 : parsedIntegerMaskExprAccessesInLine? expression filesA.maskRegisters
                  control.directive hasSingleLineMask control.context.pe cycle
                  control.context.bar0 control.context.bar1 control.context.tWord with
              | some accesses =>
                  simp only [d3] at hA hB
                  cases rf : resolveFlushSelection? expression.flush filesA.maskRegisters cycle with
                  | none => simp_all
                  | some flushSelection =>
                      simp only [rf] at hA hB
                      cases pA : prepareParsedIntegerMaskALUWriteWithForwarding filesA oldSlotsA
                          cycle accesses flushSelection reduced with
                      | failure => simp_all
                      | unknown => simp_all
                      | ok writeA =>
                          cases pB : prepareParsedIntegerMaskALUWriteWithForwarding filesB oldSlotsA
                              cycle accesses flushSelection reduced with
                          | failure => simp_all
                          | unknown => simp_all
                          | ok writeB =>
                              have same :=
                                prepareParsedIntegerMaskALUWriteWithForwarding_congr_of_agree
                                  filesA filesB oldSlotsA cycle accesses flushSelection reduced
                                  (fun w hw => agree w (readsWithin (by
                                    simp only [aluCycleReadSet, hop, d1, d2, d3, optionMaskReads,
                                      Set.mem_union]
                                    tauto)))
                              rw [pA, pB] at same
                              have writeEq : writeA = writeB := StepResult.ok.inj same
                              obtain ⟨slotsA', hupdA⟩ :=
                                updateParsedIntegerALUForwardingCycle_ok_exists nextSlotsA cycle
                                  writeA noForward
                              obtain ⟨slotsB', hupdB⟩ :=
                                updateParsedIntegerALUForwardingCycle_ok_exists nextSlotsA cycle
                                  writeB noForward
                              simp only [pA, pB, hupdA, hupdB, StepResult.ok.injEq, Prod.mk.injEq]
                                at hA hB
                              refine ⟨?_, ?_⟩
                              · rw [← hA.1, ← hB.1, writeEq]
                              · rw [← hA.2, ← hB.2]
                                rw [← writeEq] at hupdB
                                rw [hupdA] at hupdB
                                exact StepResult.ok.inj hupdB
              | none =>
                  simp only [d3] at hA hB
                  cases d4 : parsedIntegerNoWriteExprAccessesInLine? expression filesA.maskRegisters
                      control.context.pe cycle control.context.group control.context.l2b
                      control.context.l1b control.context.mab control.context.bar0
                      control.context.bar1 control.context.tWord with
                  | some accesses =>
                      simp only [d4] at hA hB
                      cases pA : prepareParsedIntegerNoWriteALUWithForwarding filesA oldSlotsA
                          cycle accesses reduced with
                      | failure => simp_all
                      | unknown => simp_all
                      | ok writeA =>
                          cases pB : prepareParsedIntegerNoWriteALUWithForwarding filesB oldSlotsA
                              cycle accesses reduced with
                          | failure => simp_all
                          | unknown => simp_all
                          | ok writeB =>
                              have same :=
                                prepareParsedIntegerNoWriteALUWithForwarding_congr_of_agree
                                  filesA filesB oldSlotsA cycle accesses reduced
                                  (fun w hw => agree w (readsWithin (by
                                    simp only [aluCycleReadSet, hop, d1, d2, d3, d4,
                                      optionNoWriteReads, Set.mem_union]
                                    tauto)))
                              rw [pA, pB] at same
                              have writeEq : writeA = writeB := StepResult.ok.inj same
                              obtain ⟨slotsA', hupdA⟩ :=
                                updateParsedIntegerALUForwardingCycle_ok_exists nextSlotsA cycle
                                  writeA noForward
                              obtain ⟨slotsB', hupdB⟩ :=
                                updateParsedIntegerALUForwardingCycle_ok_exists nextSlotsA cycle
                                  writeB noForward
                              simp only [pA, pB, hupdA, hupdB, StepResult.ok.injEq, Prod.mk.injEq]
                                at hA hB
                              refine ⟨?_, ?_⟩
                              · rw [← hA.1, ← hB.1, writeEq]
                              · rw [← hA.2, ← hB.2]
                                rw [← writeEq] at hupdB
                                rw [hupdA] at hupdB
                                exact StepResult.ok.inj hupdB
                  | none =>
                      simp only [d4] at hA hB
                      cases d5 : parsedIntegerBarExprAccessesInLine? expression filesA.maskRegisters
                          control.directive hasSingleLineMask control.context.group
                          control.context.l2b control.context.l1b control.context.mab
                          control.context.pe cycle control.context.bar0 control.context.bar1
                          control.context.tWord with
                      | some accesses =>
                          simp only [d5] at hA hB
                          cases pA : prepareParsedIntegerBarALUWithForwarding filesA oldSlotsA
                              cycle accesses reduced with
                          | failure => simp_all
                          | unknown => simp_all
                          | ok writeA =>
                              cases pB : prepareParsedIntegerBarALUWithForwarding filesB oldSlotsA
                                  cycle accesses reduced with
                              | failure => simp_all
                              | unknown => simp_all
                              | ok writeB =>
                                  have same :=
                                    prepareParsedIntegerBarALUWithForwarding_congr_of_agree
                                      filesA filesB oldSlotsA cycle accesses reduced
                                      (fun w hw => agree w (readsWithin (by
                                        simp only [aluCycleReadSet, hop, d1, d2, d3, d4, d5,
                                          optionBarReads, Set.mem_union]
                                        tauto)))
                                  rw [pA, pB] at same
                                  have writeEq : writeA = writeB := StepResult.ok.inj same
                                  obtain ⟨slotsA', hupdA⟩ :=
                                    updateParsedIntegerALUForwardingCycle_ok_exists nextSlotsA cycle
                                      writeA noForward
                                  obtain ⟨slotsB', hupdB⟩ :=
                                    updateParsedIntegerALUForwardingCycle_ok_exists nextSlotsA cycle
                                      writeB noForward
                                  simp only [pA, pB, hupdA, hupdB, StepResult.ok.injEq,
                                    Prod.mk.injEq] at hA hB
                                  refine ⟨?_, ?_⟩
                                  · rw [← hA.1, ← hB.1, writeEq]
                                  · rw [← hA.2, ← hB.2]
                                    rw [← writeEq] at hupdB
                                    rw [hupdA] at hupdB
                                    exact StepResult.ok.inj hupdB
                      | none =>
                          simp only [d5] at hA hB
                          cases d6 : parsedIntegerMaskInputExprAccessesInLine? expression
                              filesA.maskRegisters control.directive hasSingleLineMask
                              control.context.group control.context.l2b control.context.l1b
                              control.context.mab control.context.pe cycle control.context.bar0
                              control.context.bar1 control.context.tWord with
                          | some accesses =>
                              simp only [d6] at hA hB
                              cases rf : resolveFlushSelection? expression.flush filesA.maskRegisters
                                  cycle with
                              | none => simp_all
                              | some flushSelection =>
                                  simp only [rf] at hA hB
                                  cases pA : prepareParsedIntegerMaskInputALUWriteWithForwarding
                                      filesA oldSlotsA cycle accesses flushSelection reduced with
                                  | failure => simp_all
                                  | unknown => simp_all
                                  | ok writeA =>
                                      cases pB : prepareParsedIntegerMaskInputALUWriteWithForwarding
                                          filesB oldSlotsA cycle accesses flushSelection reduced with
                                      | failure => simp_all
                                      | unknown => simp_all
                                      | ok writeB =>
                                          have same :=
                                            prepareParsedIntegerMaskInputALUWriteWithForwarding_congr_of_agree
                                              filesA filesB oldSlotsA cycle accesses flushSelection
                                              reduced
                                              (fun w hw => agree w (readsWithin (by
                                                simp only [aluCycleReadSet, hop, d1, d2, d3, d4,
                                                  d5, d6, optionMaskInputReads, Set.mem_union]
                                                tauto)))
                                          rw [pA, pB] at same
                                          have writeEq : writeA = writeB := StepResult.ok.inj same
                                          obtain ⟨slotsA', hupdA⟩ :=
                                            updateParsedIntegerALUForwardingCycle_ok_exists
                                              nextSlotsA cycle writeA noForward
                                          obtain ⟨slotsB', hupdB⟩ :=
                                            updateParsedIntegerALUForwardingCycle_ok_exists
                                              nextSlotsA cycle writeB noForward
                                          simp only [pA, pB, hupdA, hupdB, StepResult.ok.injEq,
                                            Prod.mk.injEq] at hA hB
                                          refine ⟨?_, ?_⟩
                                          · rw [← hA.1, ← hB.1, writeEq]
                                          · rw [← hA.2, ← hB.2]
                                            rw [← writeEq] at hupdB
                                            rw [hupdA] at hupdB
                                            exact StepResult.ok.inj hupdB
                          | none =>
                              simp only [d6] at hA hB
                              cases d7 : parsedIntegerMaskMemoryThenInputExprAccessesInLine?
                                  expression filesA.maskRegisters control.directive
                                  hasSingleLineMask control.context.group control.context.l2b
                                  control.context.l1b control.context.mab control.context.pe cycle
                                  control.context.bar0 control.context.bar1 control.context.tWord with
                              | some accesses =>
                                  simp only [d7] at hA hB
                                  cases rf : resolveFlushSelection? expression.flush
                                      filesA.maskRegisters cycle with
                                  | none => simp_all
                                  | some flushSelection =>
                                      simp only [rf] at hA hB
                                      cases pA : prepareParsedIntegerMaskMemoryThenInputALUWritesWithForwarding
                                          filesA oldSlotsA cycle accesses flushSelection reduced with
                                      | failure => simp_all
                                      | unknown => simp_all
                                      | ok resultA =>
                                          obtain ⟨memoryWritesA, omrWriteA⟩ := resultA
                                          cases pB : prepareParsedIntegerMaskMemoryThenInputALUWritesWithForwarding
                                              filesB oldSlotsA cycle accesses flushSelection reduced with
                                          | failure => simp_all
                                          | unknown => simp_all
                                          | ok resultB =>
                                              obtain ⟨memoryWritesB, omrWriteB⟩ := resultB
                                              have same :=
                                                prepareParsedIntegerMaskMemoryThenInputALUWritesWithForwarding_congr_of_agree
                                                  filesA filesB oldSlotsA cycle accesses
                                                  flushSelection reduced
                                                  (fun w hw => agree w (readsWithin (by
                                                    simp only [aluCycleReadSet, hop, d1, d2, d3,
                                                      d4, d5, d6, d7,
                                                      optionMaskMemoryThenInputReads,
                                                      Set.mem_union]
                                                    tauto)))
                                              rw [pA, pB] at same
                                              obtain ⟨memoryEq, omrEq⟩ :=
                                                Prod.mk.inj (StepResult.ok.inj same)
                                              obtain ⟨slotsA', hupdA⟩ :=
                                                updateParsedIntegerALUForwardingCycle_ok_exists
                                                  nextSlotsA cycle omrWriteA noForward
                                              obtain ⟨slotsB', hupdB⟩ :=
                                                updateParsedIntegerALUForwardingCycle_ok_exists
                                                  nextSlotsA cycle omrWriteB noForward
                                              simp only [pA, pB, hupdA, hupdB, StepResult.ok.injEq,
                                                Prod.mk.injEq] at hA hB
                                              refine ⟨?_, ?_⟩
                                              · rw [← hA.1, ← hB.1, memoryEq, omrEq]
                                              · rw [← hA.2, ← hB.2]
                                                rw [← omrEq] at hupdB
                                                rw [hupdA] at hupdB
                                                exact StepResult.ok.inj hupdB
                              | none =>
                                  simp only [d7] at hA hB
                                  cases d8 : parsedIntegerMaskInputThenMemoryExprAccessesInLine?
                                      expression filesA.maskRegisters control.directive
                                      hasSingleLineMask control.context.group control.context.l2b
                                      control.context.l1b control.context.mab control.context.pe
                                      cycle control.context.bar0 control.context.bar1
                                      control.context.tWord with
                                  | some accesses =>
                                      simp only [d8] at hA hB
                                      cases rf : resolveFlushSelection? expression.flush
                                          filesA.maskRegisters cycle with
                                      | none => simp_all
                                      | some flushSelection =>
                                          simp only [rf] at hA hB
                                          cases pA : prepareParsedIntegerMaskInputThenMemoryALUWritesWithForwarding
                                              filesA oldSlotsA cycle accesses control.directive
                                              hasSingleLineMask flushSelection reduced with
                                          | failure => simp_all
                                          | unknown => simp_all
                                          | ok resultA =>
                                              obtain ⟨writesA', producerA⟩ := resultA
                                              cases pB : prepareParsedIntegerMaskInputThenMemoryALUWritesWithForwarding
                                                  filesB oldSlotsA cycle accesses control.directive
                                                  hasSingleLineMask flushSelection reduced with
                                              | failure => simp_all
                                              | unknown => simp_all
                                              | ok resultB =>
                                                  obtain ⟨writesB', producerB⟩ := resultB
                                                  have same :=
                                                    prepareParsedIntegerMaskInputThenMemoryALUWritesWithForwarding_congr_of_agree
                                                      filesA filesB oldSlotsA cycle accesses
                                                      control.directive hasSingleLineMask
                                                      flushSelection reduced maskEq
                                                      (fun w hw => agree w (readsWithin (by
                                                        simp only [aluCycleReadSet, hop, d1, d2,
                                                          d3, d4, d5, d6, d7, d8,
                                                          optionMaskInputThenMemoryReads,
                                                          Set.mem_union]
                                                        tauto)))
                                                  rw [pA, pB] at same
                                                  obtain ⟨writesEq, producerEq⟩ :=
                                                    Prod.mk.inj (StepResult.ok.inj same)
                                                  obtain ⟨slotsA', hupdA⟩ :=
                                                    updateParsedIntegerALUForwardingCycle_ok_exists
                                                      nextSlotsA cycle producerA noForward
                                                  obtain ⟨slotsB', hupdB⟩ :=
                                                    updateParsedIntegerALUForwardingCycle_ok_exists
                                                      nextSlotsA cycle producerB noForward
                                                  simp only [pA, pB, hupdA, hupdB,
                                                    StepResult.ok.injEq, Prod.mk.injEq] at hA hB
                                                  refine ⟨?_, ?_⟩
                                                  · rw [← hA.1, ← hB.1, writesEq]
                                                  · rw [← hA.2, ← hB.2]
                                                    rw [← producerEq] at hupdB
                                                    rw [hupdA] at hupdB
                                                    exact StepResult.ok.inj hupdB
                                  | none =>
                                      simp only [d8] at hA hB
                                      split at hA <;> simp_all
  | zero =>
      exact prepareParsedIntegerALUExprCycle_congr_constant filesA filesB oldSlotsA oldSlotsB
        nextSlotsA nextSlotsB expression control hasSingleLineMask noForward reduced cycle R
        (Or.inl hop) maskEq nextEq readsWithin agree writesA slotsA writesB slotsB hA hB
  | immediate value unsigned =>
      exact prepareParsedIntegerALUExprCycle_congr_constant filesA filesB oldSlotsA oldSlotsB
        nextSlotsA nextSlotsB expression control hasSingleLineMask noForward reduced cycle R
        (Or.inr ⟨value, unsigned, hop⟩) maskEq nextEq readsWithin agree writesA slotsA
        writesB slotsB hA hB
  | mau precision matrix kind half round => simp only [hop] at hA; simp at hA
  | matrixWrite precision => simp only [hop] at hA; simp at hA
  | matrixRead precision => simp only [hop] at hA; simp at hA
  | wait tag => simp only [hop] at hA; simp at hA
  | noforward => simp only [hop] at hA; simp at hA
  | l1bm op => simp only [hop] at hA; simp at hA
  | l2bm op => simp only [hop] at hA; simp at hA


/-! ## 5. The four-cycle accumulation and the expression / list lift -/

/-- A plain row is one of the three plain op shapes. -/
theorem plain_op_cases' (e : ParsedExpr) (h : parsedExprIsPlainIntegerALU e = true) :
    (∃ name precision unsigned arg, e.op = .alu name precision unsigned arg) ∨ e.op = .zero ∨
      ∃ value unsigned, e.op = .immediate value unsigned := by
  obtain ⟨integer, _, _, _, _, _, _, _, _, _, _, _, _⟩ :=
    parsedExprIsPlainIntegerALU_facts e h
  cases op : e.op with
  | alu name precision unsigned arg => exact Or.inl ⟨name, precision, unsigned, arg, rfl⟩
  | zero => exact Or.inr (Or.inl rfl)
  | immediate value unsigned => exact Or.inr (Or.inr ⟨value, unsigned, rfl⟩)
  | matrixRead precision => simp [parsedExprIsIntegerProducer, op] at integer
  | mau precision matrix kind half round => simp [parsedExprIsIntegerProducer, op] at integer
  | matrixWrite precision => simp [parsedExprIsIntegerProducer, op] at integer
  | wait tag => simp [parsedExprIsIntegerProducer, op] at integer
  | noforward => simp [parsedExprIsIntegerProducer, op] at integer
  | l1bm operation => simp [parsedExprIsIntegerProducer, op] at integer
  | l2bm operation => simp [parsedExprIsIntegerProducer, op] at integer

/-- **The four-cycle accumulation is a function of its reads.**  Every cycle is
covered by `prepareParsedIntegerALUExprCycle_congr`; the write lists are
appended and the slots threaded, so equal starting accumulators and slots give
equal results. -/
theorem prepareParsedIntegerALUCycles_congr
    (filesA filesB : IntegerRegisterFiles)
    (oldSlotsA oldSlotsB : ProofsLean.MNCore.Forwarding.Slots)
    (expression : ParsedExpr) (control : ParsedMaskExecutionControl)
    (hasSingleLineMask noForward reduced : Bool) (R : Set WordRef)
    (maskEq : filesA.maskRegisters = filesB.maskRegisters)
    (slotsEq : oldSlotsA = oldSlotsB)
    (readsWithin : ∀ cycle ∈ parsedIntegerALUCycles,
      aluCycleReadSet filesA.maskRegisters expression control hasSingleLineMask cycle ⊆ R)
    (agree : FilesAgreeOn R filesA filesB) :
    ∀ (cycles : List (Fin 4)) (sub : ∀ cycle ∈ cycles, cycle ∈ parsedIntegerALUCycles)
      (writesA : List PreparedParsedMaskedWrite)
      (startSlotsA : ProofsLean.MNCore.Forwarding.Slots)
      (writesB : List PreparedParsedMaskedWrite)
      (startSlotsB : ProofsLean.MNCore.Forwarding.Slots)
      (resultA resultB : List PreparedParsedMaskedWrite ×
        ProofsLean.MNCore.Forwarding.Slots),
      writesA = writesB →
      startSlotsA = startSlotsB →
      prepareParsedIntegerALUCycles filesA oldSlotsA expression control hasSingleLineMask
        noForward reduced cycles writesA startSlotsA = .ok resultA →
      prepareParsedIntegerALUCycles filesB oldSlotsB expression control hasSingleLineMask
        noForward reduced cycles writesB startSlotsB = .ok resultB →
      resultA = resultB := by
  intro cycles
  induction cycles with
  | nil =>
      intro sub writesA startSlotsA writesB startSlotsB resultA resultB writesEq slotsEq' hA hB
      simp only [prepareParsedIntegerALUCycles, StepResult.ok.injEq] at hA hB
      rw [← hA, ← hB, writesEq, slotsEq']
  | cons c rest ih =>
      intro sub writesA startSlotsA writesB startSlotsB resultA resultB writesEq slotsEq' hA hB
      have cycleReads : aluCycleReadSet filesA.maskRegisters expression control
          hasSingleLineMask c ⊆ R := readsWithin c (sub c (by simp))
      simp only [prepareParsedIntegerALUCycles] at hA hB
      cases cA : prepareParsedIntegerALUExprCycle filesA oldSlotsA startSlotsA expression control
          hasSingleLineMask noForward reduced c with
      | failure => simp only [cA] at hA; simp at hA
      | unknown => simp only [cA] at hA; simp at hA
      | ok cycleResultA =>
          obtain ⟨cycleWritesA, cycleSlotsA⟩ := cycleResultA
          cases cB : prepareParsedIntegerALUExprCycle filesB oldSlotsB startSlotsB expression control
              hasSingleLineMask noForward reduced c with
          | failure => simp only [cB] at hB; simp at hB
          | unknown => simp only [cB] at hB; simp at hB
          | ok cycleResultB =>
              obtain ⟨cycleWritesB, cycleSlotsB⟩ := cycleResultB
              simp only [cA] at hA
              simp only [cB] at hB
              have same := prepareParsedIntegerALUExprCycle_congr filesA filesB oldSlotsA oldSlotsB
                startSlotsA startSlotsB expression control hasSingleLineMask noForward reduced c R
                maskEq slotsEq slotsEq' cycleReads agree cycleWritesA cycleSlotsA cycleWritesB
                cycleSlotsB cA cB
              obtain ⟨cycleWritesEq, cycleSlotsEq⟩ := same
              refine ih (fun cycle member => sub cycle (by simp [member]))
                (writesA ++ cycleWritesA) cycleSlotsA (writesB ++ cycleWritesB) cycleSlotsB
                resultA resultB ?_ cycleSlotsEq hA hB
              rw [writesEq, cycleWritesEq]

/-- **The four-cycle expression preparation is a function of its reads.** -/
theorem prepareParsedIntegerALUExprCycles_congr
    (filesA filesB : IntegerRegisterFiles)
    (oldSlotsA oldSlotsB initialSlotsA initialSlotsB : ProofsLean.MNCore.Forwarding.Slots)
    (expression : ParsedExpr) (control : ParsedMaskExecutionControl)
    (hasSingleLineMask noForward reduced : Bool) (R : Set WordRef)
    (maskEq : filesA.maskRegisters = filesB.maskRegisters)
    (slotsEq : oldSlotsA = oldSlotsB)
    (initialEq : initialSlotsA = initialSlotsB)
    (readsWithin : ∀ cycle ∈ parsedIntegerALUCycles,
      aluCycleReadSet filesA.maskRegisters expression control hasSingleLineMask cycle ⊆ R)
    (agree : FilesAgreeOn R filesA filesB)
    (writesA : List PreparedParsedMaskedWrite)
    (outSlotsA : ProofsLean.MNCore.Forwarding.Slots)
    (writesB : List PreparedParsedMaskedWrite)
    (outSlotsB : ProofsLean.MNCore.Forwarding.Slots)
    (hA : prepareParsedIntegerALUExprCycles filesA oldSlotsA initialSlotsA expression control
        hasSingleLineMask noForward reduced = .ok (writesA, outSlotsA))
    (hB : prepareParsedIntegerALUExprCycles filesB oldSlotsB initialSlotsB expression control
        hasSingleLineMask noForward reduced = .ok (writesB, outSlotsB)) :
    writesA = writesB ∧ outSlotsA = outSlotsB := by
  have same := prepareParsedIntegerALUCycles_congr filesA filesB oldSlotsA oldSlotsB expression
    control hasSingleLineMask noForward reduced R maskEq slotsEq readsWithin agree
    parsedIntegerALUCycles (fun cycle member => member) [] initialSlotsA [] initialSlotsB
    (writesA, outSlotsA) (writesB, outSlotsB) rfl initialEq hA hB
  exact Prod.mk.inj same

/-- **One plain row's line preparation is a function of its reads.**  The `.alu`,
`.zero` and `.immediate` rows all run the four-cycle ALU preparation; the BAR
update list is a function of the prepared writes. -/
theorem prepareParsedIntegerMatrixReadLineExpression_congr_plain
    (filesA filesB : IntegerRegisterFiles)
    (oldSlotsA oldSlotsB nextSlotsA nextSlotsB : ProofsLean.MNCore.Forwarding.Slots)
    (store : ParsedMatrixReadStore) (expression : ParsedExpr)
    (control : ParsedMaskExecutionControl) (hasSingleLineMask noForward reduced : Bool)
    (R : Set WordRef)
    (plain : parsedExprIsPlainIntegerALU expression = true)
    (maskEq : filesA.maskRegisters = filesB.maskRegisters)
    (slotsEq : oldSlotsA = oldSlotsB)
    (nextEq : nextSlotsA = nextSlotsB)
    (readsWithin : ∀ cycle ∈ parsedIntegerALUCycles,
      aluCycleReadSet filesA.maskRegisters expression control hasSingleLineMask cycle ⊆ R)
    (agree : FilesAgreeOn R filesA filesB)
    (writesA : List PreparedParsedMaskedWrite)
    (outSlotsA : ProofsLean.MNCore.Forwarding.Slots)
    (barsA : List (Bool × BitVec 12))
    (writesB : List PreparedParsedMaskedWrite)
    (outSlotsB : ProofsLean.MNCore.Forwarding.Slots)
    (barsB : List (Bool × BitVec 12))
    (hA : prepareParsedIntegerMatrixReadLineExpression filesA oldSlotsA nextSlotsA store
        expression control hasSingleLineMask noForward reduced = .ok (writesA, outSlotsA, barsA))
    (hB : prepareParsedIntegerMatrixReadLineExpression filesB oldSlotsB nextSlotsB store
        expression control hasSingleLineMask noForward reduced = .ok (writesB, outSlotsB, barsB)) :
    writesA = writesB ∧ outSlotsA = outSlotsB ∧ barsA = barsB := by
  unfold prepareParsedIntegerMatrixReadLineExpression at hA hB
  rcases plain_op_cases' expression plain with ⟨name, precision, unsigned, arg, hop⟩ |
    hop | ⟨value, unsigned, hop⟩
  · simp only [hop] at hA hB
    cases cA : prepareParsedIntegerALUExprCycles filesA oldSlotsA nextSlotsA expression control
        hasSingleLineMask noForward reduced with
    | failure => simp_all
    | unknown => simp_all
    | ok resultA =>
        obtain ⟨cycleWritesA, cycleSlotsA⟩ := resultA
        cases cB : prepareParsedIntegerALUExprCycles filesB oldSlotsB nextSlotsB expression control
            hasSingleLineMask noForward reduced with
        | failure => simp_all
        | unknown => simp_all
        | ok resultB =>
            obtain ⟨cycleWritesB, cycleSlotsB⟩ := resultB
            simp only [cA, cB, StepResult.ok.injEq, Prod.mk.injEq] at hA hB
            have same := prepareParsedIntegerALUExprCycles_congr filesA filesB oldSlotsA oldSlotsB
              nextSlotsA nextSlotsB expression control hasSingleLineMask noForward reduced R
              maskEq slotsEq nextEq readsWithin agree cycleWritesA cycleSlotsA cycleWritesB
              cycleSlotsB cA cB
            obtain ⟨writesEq, slotsEq'⟩ := same
            refine ⟨?_, ?_, ?_⟩
            · rw [← hA.1, ← hB.1, writesEq]
            · rw [← hA.2.1, ← hB.2.1, slotsEq']
            · rw [← hA.2.2, ← hB.2.2, writesEq]
  · simp only [hop] at hA hB
    cases cA : prepareParsedIntegerALUExprCycles filesA oldSlotsA nextSlotsA expression control
        hasSingleLineMask noForward reduced with
    | failure => simp_all
    | unknown => simp_all
    | ok resultA =>
        obtain ⟨cycleWritesA, cycleSlotsA⟩ := resultA
        cases cB : prepareParsedIntegerALUExprCycles filesB oldSlotsB nextSlotsB expression control
            hasSingleLineMask noForward reduced with
        | failure => simp_all
        | unknown => simp_all
        | ok resultB =>
            obtain ⟨cycleWritesB, cycleSlotsB⟩ := resultB
            simp only [cA, cB, StepResult.ok.injEq, Prod.mk.injEq] at hA hB
            have same := prepareParsedIntegerALUExprCycles_congr filesA filesB oldSlotsA oldSlotsB
              nextSlotsA nextSlotsB expression control hasSingleLineMask noForward reduced R
              maskEq slotsEq nextEq readsWithin agree cycleWritesA cycleSlotsA cycleWritesB
              cycleSlotsB cA cB
            obtain ⟨writesEq, slotsEq'⟩ := same
            refine ⟨?_, ?_, ?_⟩
            · rw [← hA.1, ← hB.1, writesEq]
            · rw [← hA.2.1, ← hB.2.1, slotsEq']
            · rw [← hA.2.2, ← hB.2.2, writesEq]
  · simp only [hop] at hA hB
    cases cA : prepareParsedIntegerALUExprCycles filesA oldSlotsA nextSlotsA expression control
        hasSingleLineMask noForward reduced with
    | failure => simp_all
    | unknown => simp_all
    | ok resultA =>
        obtain ⟨cycleWritesA, cycleSlotsA⟩ := resultA
        cases cB : prepareParsedIntegerALUExprCycles filesB oldSlotsB nextSlotsB expression control
            hasSingleLineMask noForward reduced with
        | failure => simp_all
        | unknown => simp_all
        | ok resultB =>
            obtain ⟨cycleWritesB, cycleSlotsB⟩ := resultB
            simp only [cA, cB, StepResult.ok.injEq, Prod.mk.injEq] at hA hB
            have same := prepareParsedIntegerALUExprCycles_congr filesA filesB oldSlotsA oldSlotsB
              nextSlotsA nextSlotsB expression control hasSingleLineMask noForward reduced R
              maskEq slotsEq nextEq readsWithin agree cycleWritesA cycleSlotsA cycleWritesB
              cycleSlotsB cA cB
            obtain ⟨writesEq, slotsEq'⟩ := same
            refine ⟨?_, ?_, ?_⟩
            · rw [← hA.1, ← hB.1, writesEq]
            · rw [← hA.2.1, ← hB.2.1, slotsEq']
            · rw [← hA.2.2, ← hB.2.2, writesEq]


/-! ### The line-level read set -/

/-- The words one plain row reads: the union of its four cycles' read sets. -/
def parsedExpressionReadSet (registers : ProofsLean.MNCore.Masks.RegisterFile)
    (expression : ParsedExpr) (control : ParsedMaskExecutionControl)
    (hasSingleLineMask : Bool) : Set WordRef :=
  {w | ∃ cycle ∈ parsedIntegerALUCycles,
    w ∈ aluCycleReadSet registers expression control hasSingleLineMask cycle}

/-- The words a line's integer-stage preparation reads. -/
def preparedListReadSet (registers : ProofsLean.MNCore.Masks.RegisterFile)
    (expressions : List ParsedExpr) (control : ParsedMaskExecutionControl) : Set WordRef :=
  let hasSingleLineMask := expressions.any parsedExprHasSingleLineWriteMask
  {w | ∃ expression ∈ expressions,
    w ∈ parsedExpressionReadSet registers expression control hasSingleLineMask}

/-- **The expression-list preparation is a function of its reads.** -/
theorem prepareParsedIntegerMatrixReadLineExpressions_congr_plain
    (filesA filesB : IntegerRegisterFiles)
    (oldSlotsA oldSlotsB : ProofsLean.MNCore.Forwarding.Slots)
    (store : ParsedMatrixReadStore) (control : ParsedMaskExecutionControl)
    (hasSingleLineMask noForward reduced : Bool) (R : Set WordRef)
    (maskEq : filesA.maskRegisters = filesB.maskRegisters)
    (slotsEq : oldSlotsA = oldSlotsB)
    (agree : FilesAgreeOn R filesA filesB) :
    ∀ (expressions : List ParsedExpr)
      (writesA : List PreparedParsedMaskedWrite)
      (nextSlotsA : ProofsLean.MNCore.Forwarding.Slots)
      (barsA : List (Bool × BitVec 12))
      (writesB : List PreparedParsedMaskedWrite)
      (nextSlotsB : ProofsLean.MNCore.Forwarding.Slots)
      (barsB : List (Bool × BitVec 12))
      (resultA resultB : List PreparedParsedMaskedWrite ×
        ProofsLean.MNCore.Forwarding.Slots × List (Bool × BitVec 12)),
      (∀ expression ∈ expressions, parsedExprIsPlainIntegerALU expression = true) →
      (∀ expression ∈ expressions, ∀ cycle ∈ parsedIntegerALUCycles,
        aluCycleReadSet filesA.maskRegisters expression control hasSingleLineMask cycle ⊆ R) →
      writesA = writesB →
      nextSlotsA = nextSlotsB →
      barsA = barsB →
      prepareParsedIntegerMatrixReadLineExpressions filesA oldSlotsA store control
        hasSingleLineMask noForward reduced expressions writesA nextSlotsA barsA = .ok resultA →
      prepareParsedIntegerMatrixReadLineExpressions filesB oldSlotsB store control
        hasSingleLineMask noForward reduced expressions writesB nextSlotsB barsB = .ok resultB →
      resultA = resultB := by
  intro expressions
  induction expressions with
  | nil =>
      intro writesA nextSlotsA barsA writesB nextSlotsB barsB resultA resultB plain reads
        writesEq slotsEq' barsEq hA hB
      simp only [prepareParsedIntegerMatrixReadLineExpressions, StepResult.ok.injEq] at hA hB
      rw [← hA, ← hB, writesEq, slotsEq', barsEq]
  | cons expression rest ih =>
      intro writesA nextSlotsA barsA writesB nextSlotsB barsB resultA resultB plain reads
        writesEq slotsEq' barsEq hA hB
      have plainHead : parsedExprIsPlainIntegerALU expression = true := plain expression (by simp)
      have plainRest : ∀ item ∈ rest, parsedExprIsPlainIntegerALU item = true :=
        fun item member => plain item (by simp [member])
      have readsHead : ∀ cycle ∈ parsedIntegerALUCycles,
          aluCycleReadSet filesA.maskRegisters expression control hasSingleLineMask cycle ⊆ R :=
        fun cycle member => reads expression (by simp) cycle member
      have readsRest : ∀ item ∈ rest, ∀ cycle ∈ parsedIntegerALUCycles,
          aluCycleReadSet filesA.maskRegisters item control hasSingleLineMask cycle ⊆ R :=
        fun item member cycle hcycle => reads item (by simp [member]) cycle hcycle
      simp only [prepareParsedIntegerMatrixReadLineExpressions] at hA hB
      cases eA : prepareParsedIntegerMatrixReadLineExpression filesA oldSlotsA nextSlotsA store
          expression control hasSingleLineMask noForward reduced with
      | failure => simp only [eA] at hA; simp at hA
      | unknown => simp only [eA] at hA; simp at hA
      | ok expressionResultA =>
          obtain ⟨expressionWritesA, expressionSlotsA, expressionBarsA⟩ := expressionResultA
          cases eB : prepareParsedIntegerMatrixReadLineExpression filesB oldSlotsB nextSlotsB store
              expression control hasSingleLineMask noForward reduced with
          | failure => simp only [eB] at hB; simp at hB
          | unknown => simp only [eB] at hB; simp at hB
          | ok expressionResultB =>
              obtain ⟨expressionWritesB, expressionSlotsB, expressionBarsB⟩ := expressionResultB
              simp only [eA] at hA
              simp only [eB] at hB
              have same := prepareParsedIntegerMatrixReadLineExpression_congr_plain filesA filesB
                oldSlotsA oldSlotsB nextSlotsA nextSlotsB store expression control
                hasSingleLineMask noForward reduced R plainHead maskEq slotsEq slotsEq' readsHead
                agree expressionWritesA expressionSlotsA expressionBarsA expressionWritesB
                expressionSlotsB expressionBarsB eA eB
              obtain ⟨expressionWritesEq, expressionSlotsEq, expressionBarsEq⟩ := same
              refine ih (writesA ++ expressionWritesA) expressionSlotsA
                (barsA ++ expressionBarsA) (writesB ++ expressionWritesB) expressionSlotsB
                (barsB ++ expressionBarsB) resultA resultB plainRest readsRest ?_
                expressionSlotsEq ?_ hA hB
              · rw [writesEq, expressionWritesEq]
              · rw [barsEq, expressionBarsEq]

/-- **The line-level preparation is a function of its reads.** -/
theorem prepareParsedIntegerMatrixReadLineCycles_congr_plain
    (filesA filesB : IntegerRegisterFiles)
    (oldSlotsA oldSlotsB : ProofsLean.MNCore.Forwarding.Slots)
    (store : ParsedMatrixReadStore)
    (expressions : List ParsedExpr) (control : ParsedMaskExecutionControl) (reduced : Bool)
    (R : Set WordRef)
    (plain : ∀ expression ∈ expressions, parsedExprIsPlainIntegerALU expression = true)
    (readsWithin : preparedListReadSet filesA.maskRegisters expressions control ⊆ R)
    (maskEq : filesA.maskRegisters = filesB.maskRegisters)
    (slotsEq : oldSlotsA = oldSlotsB)
    (agree : FilesAgreeOn R filesA filesB)
    (writesA : List PreparedParsedMaskedWrite)
    (outSlotsA : ProofsLean.MNCore.Forwarding.Slots)
    (barsA : List (Bool × BitVec 12))
    (writesB : List PreparedParsedMaskedWrite)
    (outSlotsB : ProofsLean.MNCore.Forwarding.Slots)
    (barsB : List (Bool × BitVec 12))
    (hA : prepareParsedIntegerMatrixReadLineCycles filesA oldSlotsA store expressions control
        reduced = .ok (writesA, outSlotsA, barsA))
    (hB : prepareParsedIntegerMatrixReadLineCycles filesB oldSlotsB store expressions control
        reduced = .ok (writesB, outSlotsB, barsB)) :
    writesA = writesB ∧ outSlotsA = outSlotsB ∧ barsA = barsB := by
  unfold prepareParsedIntegerMatrixReadLineCycles at hA hB
  have same := prepareParsedIntegerMatrixReadLineExpressions_congr_plain filesA filesB
    oldSlotsA oldSlotsB store control (expressions.any parsedExprHasSingleLineWriteMask)
    (expressions.any fun expression => match expression.op with
      | .noforward => true | _ => false) reduced R maskEq slotsEq agree expressions [] oldSlotsA []
    [] oldSlotsB [] (writesA, outSlotsA, barsA) (writesB, outSlotsB, barsB) plain
    (fun expression member cycle hcycle w hw => readsWithin ⟨expression, member, cycle, hcycle, hw⟩)
    rfl slotsEq rfl hA hB
  exact ⟨(Prod.mk.inj same).1, (Prod.mk.inj (Prod.mk.inj same).2).1,
    (Prod.mk.inj (Prod.mk.inj same).2).2⟩


/-! ## 6. `PEPreparedListCongruent` for the plain-ALU family -/

/-- Plainness survives the integer-stage filter. -/
theorem plain_of_filter_stageInput (expressions : List ParsedExpr)
    (plain : expressions.all parsedExprIsPlainIntegerALU = true) :
    ∀ expression ∈ expressions.filter parsedExprIsIntegerMatrixReadStageInput,
      parsedExprIsPlainIntegerALU expression = true := by
  intro expression member
  exact List.all_eq_true.mp plain expression (List.mem_of_mem_filter member)

/-- **`PEPreparedListCongruent` for the plain-ALU family**, from coverage of the
preparation's lowered reads by the line's footprint.  The channel hypothesis
supplies the mask-register file, the forwarding slots, the matrix store, the
mask directive, the context and the clock; the footprint hypothesis supplies
the bank words the prepared writes read. -/
theorem pepreparedListCongruent_plain
    (footprint : InstructionLine → State → Set WordRef)
    (expressions : List NormalizedExpr)
    (plain : (expressions.map NormalizedExpr.toParsed).all
      parsedExprIsPlainIntegerALU = true)
    (covers : ∀ (s s' : State), ChanAgree plusTwoPE s s' →
      preparedListReadSet ((s.peRegisters plusTwoPE)).maskRegisters
          ((expressions.map NormalizedExpr.toParsed).filter
            parsedExprIsIntegerMatrixReadStageInput)
          (parsedPEHazardControl s plusTwoPE) ⊆
        footprint (.pe expressions) s ∪ footprint (.pe expressions) s') :
    PEPreparedListCongruent footprint expressions := by
  intro s s' w w' slots slots' bars bars' chan agree prep prep'
  have maskEq : (s.peRegisters plusTwoPE).maskRegisters =
      (s'.peRegisters plusTwoPE).maskRegisters := chanAgree_maskRegisters chan
  have slotEq : stateForwardingSlots s plusTwoPE = stateForwardingSlots s' plusTwoPE :=
    chanAgree_forwardingSlots chan
  have storeEq :
      s.matrixRegisters (ParsedIntegerContext.ofLinearIndex plusTwoPE).group
          (ParsedIntegerContext.ofLinearIndex plusTwoPE).l2b
          (ParsedIntegerContext.ofLinearIndex plusTwoPE).l1b =
        s'.matrixRegisters (ParsedIntegerContext.ofLinearIndex plusTwoPE).group
          (ParsedIntegerContext.ofLinearIndex plusTwoPE).l2b
          (ParsedIntegerContext.ofLinearIndex plusTwoPE).l1b :=
    chanAgree_matrix chan
  have contextEq : s.peContext plusTwoPE = s'.peContext plusTwoPE := chanAgree_context chan
  have directiveEq : s.maskDirective = s'.maskDirective := chanAgree_maskDirective chan
  have clockEq : s.hazardClock = s'.hazardClock := chanAgree_clock chan
  have controlEq : parsedPEHazardControl s plusTwoPE = parsedPEHazardControl s' plusTwoPE := by
    simp only [parsedPEHazardControl]
    rw [contextEq, directiveEq, clockEq]
  unfold welcomeIntegerPrep at prep prep'
  rw [← controlEq, ← storeEq] at prep'
  have filteredPlain : ∀ expression ∈
      (expressions.map NormalizedExpr.toParsed).filter
        parsedExprIsIntegerMatrixReadStageInput,
      parsedExprIsPlainIntegerALU expression = true := by
    intro expression member
    exact List.all_eq_true.mp plain expression (List.mem_of_mem_filter member)
  have coverage := covers s s' chan
  have agreement : FilesAgreeOn
      (preparedListReadSet (s.peRegisters plusTwoPE).maskRegisters
        ((expressions.map NormalizedExpr.toParsed).filter
          parsedExprIsIntegerMatrixReadStageInput)
        (parsedPEHazardControl s plusTwoPE))
      (s.peRegisters plusTwoPE) (s'.peRegisters plusTwoPE) :=
    agree.mono coverage
  have same := prepareParsedIntegerMatrixReadLineCycles_congr_plain
    (s.peRegisters plusTwoPE) (s'.peRegisters plusTwoPE)
    (stateForwardingSlots s plusTwoPE) (stateForwardingSlots s' plusTwoPE)
    (s.matrixRegisters (ParsedIntegerContext.ofLinearIndex plusTwoPE).group
      (ParsedIntegerContext.ofLinearIndex plusTwoPE).l2b
      (ParsedIntegerContext.ofLinearIndex plusTwoPE).l1b)
    ((expressions.map NormalizedExpr.toParsed).filter
      parsedExprIsIntegerMatrixReadStageInput)
    (parsedPEHazardControl s plusTwoPE) false
    (preparedListReadSet (s.peRegisters plusTwoPE).maskRegisters
      ((expressions.map NormalizedExpr.toParsed).filter
        parsedExprIsIntegerMatrixReadStageInput)
      (parsedPEHazardControl s plusTwoPE))
    filteredPlain (fun w hw => hw) maskEq slotEq agreement
    w slots bars w' slots' bars' prep prep'
  exact same.1

/-- **The concrete footprint-coverage residual.**  The hazard-event read
footprint `plusTwoLineFootprint` of a plain `.pe` line covers every word the
integer-stage preparation lowers to, at every state.  This is the reconciliation
between the hazard-event lowering (`ParsedExpr.toTimedPEHazardEvents?`) and the
nine-way executor lowering, and it is the only remaining premise needed to
transfer `pepreparedListCongruent_plain` to the concrete footprint. -/
def PlusTwoLineFootprintCoversPreparedReads : Prop :=
  ∀ (expressions : List NormalizedExpr),
    (expressions.map NormalizedExpr.toParsed).all parsedExprIsPlainIntegerALU = true →
      ∀ state : State,
        preparedListReadSet (state.peRegisters plusTwoPE).maskRegisters
          ((expressions.map NormalizedExpr.toParsed).filter
            parsedExprIsIntegerMatrixReadStageInput)
          (parsedPEHazardControl state plusTwoPE) ⊆
          plusTwoLineFootprint (.pe expressions) state

/-- **`PEPreparedListCongruent` at the concrete footprint**, from the
reconciliation residual. -/
theorem pepreparedListCongruent_concrete_of_covers
    (covers : PlusTwoLineFootprintCoversPreparedReads)
    (expressions : List NormalizedExpr)
    (plain : (expressions.map NormalizedExpr.toParsed).all
      parsedExprIsPlainIntegerALU = true) :
    PEPreparedListCongruent plusTwoLineFootprint expressions :=
  pepreparedListCongruent_plain plusTwoLineFootprint expressions plain
    (fun s s' _chan w hw =>
      Or.inl (covers expressions plain s hw))

/-- **The plain-ALU `.pe` line satisfies the channel contract** once the
prepared list is a function of the channels plus the footprint. -/
theorem plain_pe_lineDeterminedAtChan_of_covers
    (footprint : InstructionLine → State → Set WordRef)
    (expressions : List NormalizedExpr)
    (plain : (expressions.map NormalizedExpr.toParsed).all
      parsedExprIsPlainIntegerALU = true)
    (covers : ∀ (s s' : State), ChanAgree plusTwoPE s s' →
      preparedListReadSet ((s.peRegisters plusTwoPE)).maskRegisters
          ((expressions.map NormalizedExpr.toParsed).filter
            parsedExprIsIntegerMatrixReadStageInput)
          (parsedPEHazardControl s plusTwoPE) ⊆
        footprint (.pe expressions) s ∪ footprint (.pe expressions) s')
    (frame : PEChannelFrame plusTwoPE (.pe expressions)) :
    LineDeterminedAtChan footprint plusTwoPE (.pe expressions) :=
  plain_pe_lineDeterminedAtChan_of_prepared footprint expressions plain
    (pepreparedListCongruent_plain footprint expressions plain covers) frame

/-- The concrete-footprint form of the same reduction. -/
theorem plain_pe_lineDeterminedAtChan_concrete_of_covers
    (covers : PlusTwoLineFootprintCoversPreparedReads)
    (expressions : List NormalizedExpr)
    (plain : (expressions.map NormalizedExpr.toParsed).all
      parsedExprIsPlainIntegerALU = true)
    (frame : PEChannelFrame plusTwoPE (.pe expressions)) :
    LineDeterminedAtChan plusTwoLineFootprint plusTwoPE (.pe expressions) :=
  plain_pe_lineDeterminedAtChan_of_prepared plusTwoLineFootprint expressions plain
    (pepreparedListCongruent_concrete_of_covers covers expressions plain) frame


/-! ## 7. The channel frame: mask registers, forwarding and context -/

theorem welcomeCommitStep_maskRegisters_congr (files files' : IntegerRegisterFiles)
    (write : PreparedParsedMaskedWrite)
    (h : files.maskRegisters = files'.maskRegisters) :
    (welcomeCommitStep files write).maskRegisters =
      (welcomeCommitStep files' write).maskRegisters := by
  obtain ⟨destination, maskUpdate, data, selection⟩ := write
  cases maskUpdate with
  | some update =>
      obtain ⟨entry, cycle, flags⟩ := update
      simp [welcomeCommitStep, h]
  | none =>
      cases destination with
      | none => simpa [welcomeCommitStep] using h
      | some access =>
          obtain ⟨bank, width, address⟩ := access
          cases bank <;>
            simp [welcomeCommitStep, writeDirectAccessMasked, writeRegisterBankMasked, h]

theorem commitParsedMaskedWrites_maskRegisters_congr (files files' : IntegerRegisterFiles)
    (writes : List PreparedParsedMaskedWrite)
    (h : files.maskRegisters = files'.maskRegisters) :
    (commitParsedMaskedWrites files writes).maskRegisters =
      (commitParsedMaskedWrites files' writes).maskRegisters := by
  induction writes generalizing files files' with
  | nil => simpa [commitParsedMaskedWrites] using h
  | cons write rest ih =>
      rw [commitParsedMaskedWrites_cons, commitParsedMaskedWrites_cons]
      exact ih _ _ (welcomeCommitStep_maskRegisters_congr files files' write h)

theorem parsedIntegerMatrixReadLineFourCycleStep_ok_of_prepared
    (files : IntegerRegisterFiles) (slots : ProofsLean.MNCore.Forwarding.Slots)
    (store : ParsedMatrixReadStore) (expressions : List ParsedExpr)
    (control : ParsedMaskExecutionControl) (reduced : Bool)
    (writes : List PreparedParsedMaskedWrite)
    (outSlots : ProofsLean.MNCore.Forwarding.Slots)
    (bars : List (Bool × BitVec 12))
    (prepared : prepareParsedIntegerMatrixReadLineCycles files slots store expressions control
      reduced = .ok (writes, outSlots, bars)) :
    parsedIntegerMatrixReadLineFourCycleStep files slots store expressions control reduced =
      .ok (commitParsedMaskedWrites files writes, outSlots, bars) := by
  unfold parsedIntegerMatrixReadLineFourCycleStep
  rw [prepared]


/-- For a plain row, the float-MAU producer filter is empty. -/
theorem plain_floatMAUProducer_false (expression : ParsedExpr)
    (plain : parsedExprIsPlainIntegerALU expression = true) :
    parsedExprIsSupportedFloatMAUProducer expression = false := by
  obtain ⟨integer, _, _, _, _, _, _, _, _, _, _, _, _⟩ :=
    parsedExprIsPlainIntegerALU_facts expression plain
  cases op : expression.op <;>
    simp_all [parsedExprIsIntegerProducer, parsedExprIsSupportedFloatMAUProducer]

theorem plain_floatMAU_filter_empty (expressions : List ParsedExpr)
    (plain : expressions.all parsedExprIsPlainIntegerALU = true) :
    expressions.filter parsedExprIsSupportedFloatMAUProducer = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro expression member
  rw [plain_floatMAUProducer_false expression
    (List.all_eq_true.mp plain expression member)]
  simp

theorem plain_floatMAU_any_writesBAR_false (expressions : List ParsedExpr)
    (plain : expressions.all parsedExprIsPlainIntegerALU = true) (lm1 : Bool) :
    expressions.any (parsedFloatMAUWritesBAR lm1) = false := by
  apply List.any_eq_false.mpr
  intro expression member
  rw [parsedFloatMAUWritesBAR]
  rw [plain_floatMAUProducer_false expression (List.all_eq_true.mp plain expression member)]
  simp

/-- **The per-PE plain core, field by field.**  A successful plain integer-ALU
per-PE core exposes its four write-side channels: the committed register file,
the new forwarding slots (fed by the integer stage's prepared slots), the new
forwarding validity, and the new BAR context (fed by the prepared BAR updates). -/
theorem executeIntegerProducerLineAtPECore_plain_fields
    (expressions : List ParsedExpr) (state next : State) (pe : PEId)
    (plain : expressions.all parsedExprIsPlainIntegerALU = true)
    (executed : executeIntegerProducerLineAtPECore expressions state pe = .ok next) :
    ∃ (writes : List PreparedParsedMaskedWrite)
      (slots : ProofsLean.MNCore.Forwarding.Slots)
      (bars : List (Bool × BitVec 12))
      (forwarding : ProofsLean.MNCore.Forwarding.Slots),
      welcomeIntegerPrep state pe expressions = .ok (writes, slots, bars) ∧
      next.peRegisters pe = commitParsedMaskedWrites (state.peRegisters pe) writes ∧
      next.forwarding pe = forwarding ∧
      next.forwardingValid pe =
        updateIntegerLineForwardingValid (state.forwardingValid pe) forwarding
          (expressions.any fun expression => match expression.op with
            | .noforward => true | _ => false) ∧
      next.peContext pe =
        { state.peContext pe with
          bar0 := (bars.foldl (fun (bar0, bar1) update => match update with
            | (false, value) => (value, bar1)
            | (true, value) => (bar0, value))
            ((state.peContext pe).bar0, (state.peContext pe).bar1)).1,
          bar1 := (bars.foldl (fun (bar0, bar1) update => match update with
            | (false, value) => (value, bar1)
            | (true, value) => (bar0, value))
            ((state.peContext pe).bar0, (state.peContext pe).bar1)).2 } ∧
      updateSupportedPELineForwarding (stateForwardingSlots state pe)
        (fun unit cycle =>
          if unit = ProofsLean.MNCore.Forwarding.Unit.mau && false then
            .known (⟨0, 0⟩ : IntegerALU.Bus)
          else slots unit cycle)
        (expressions.any fun expression => match expression.op with
          | .noforward => true | _ => false)
        (expressions.any parsedExprIsIntegerProducer) false
        (expressions.any parsedExprIsMatrixReadProducer) = .ok forwarding := by
  have floatEmpty := plain_floatMAU_filter_empty expressions plain
  have barFalse := plain_floatMAU_any_writesBAR_false expressions plain false
  have barTrue := plain_floatMAU_any_writesBAR_false expressions plain true
  rw [executeIntegerProducerLineAtPECore.eq_1] at executed
  dsimp only at executed
  split at executed
  · simp at executed
  · simp at executed
  · rename_i registers integerSlots barUpdates fourCycle
    rw [executeParsedFloatMAUsAtPE_noforward (floatEmpty := floatEmpty)] at executed
    dsimp only at executed
    simp only [updateSupportedPELineForwarding] at executed
    split at executed
    · simp at executed
    · simp at executed
    · rename_i forwarding forwardingEq
      rw [barFalse, barTrue] at executed
      simp only [Bool.false_eq_true, ite_false] at executed
      simp only [StepResult.ok.injEq] at executed
      unfold parsedIntegerMatrixReadLineFourCycleStep at fourCycle
      split at fourCycle
      · simp at fourCycle
      · simp at fourCycle
      · rename_i writes preparedSlots preparedBars prepared
        simp only [StepResult.ok.injEq, Prod.mk.injEq] at fourCycle
        obtain ⟨rfl, rfl, rfl⟩ := fourCycle
        have h1 : welcomeIntegerPrep state pe expressions =
            .ok (writes, preparedSlots, preparedBars) := prepared
        have h2 : next.peRegisters pe =
            commitParsedMaskedWrites (state.peRegisters pe) writes := by
          rw [← executed]
          simp
        have h3 : next.forwarding pe = forwarding := by
          rw [← executed]
          simp
        have h4 : next.forwardingValid pe =
            updateIntegerLineForwardingValid (state.forwardingValid pe) forwarding
              (expressions.any fun expression => match expression.op with
                | .noforward => true | _ => false) := by
          rw [← executed]
          simp
          rfl
        have h5 : next.peContext pe =
            { state.peContext pe with
              bar0 := (preparedBars.foldl
                (fun (bar0, bar1) update => match update with
                  | (false, value) => (value, bar1)
                  | (true, value) => (bar0, value))
                ((state.peContext pe).bar0, (state.peContext pe).bar1)).1,
              bar1 := (preparedBars.foldl
                (fun (bar0, bar1) update => match update with
                  | (false, value) => (value, bar1)
                  | (true, value) => (bar0, value))
                ((state.peContext pe).bar0, (state.peContext pe).bar1)).2 } := by
          rw [← executed]
          simp
          exact ⟨rfl, rfl⟩
        have h6 : updateSupportedPELineForwarding (stateForwardingSlots state pe)
            (fun unit cycle =>
              if unit = ProofsLean.MNCore.Forwarding.Unit.mau && false then
                .known (⟨0, 0⟩ : IntegerALU.Bus)
              else preparedSlots unit cycle)
            (expressions.any fun expression => match expression.op with
              | .noforward => true | _ => false)
            (expressions.any parsedExprIsIntegerProducer) false
            (expressions.any parsedExprIsMatrixReadProducer) = .ok forwarding := by
          rw [updateSupportedPELineForwarding]
          exact forwardingEq
        exact ⟨writes, preparedSlots, preparedBars, forwarding, h1, h2, h3, h4, h5, h6⟩


/-! ## 8. The channel frame repaired

The executor writes the prepared write's *data* into the forwarding slots
(`updateSupportedPELineForwarding` installs `pack write.data` and
`updateIntegerLineForwardingValid` enables it), so `PEChannelFrame` — which
assumes channel agreement but **no** bank-word agreement — cannot hold for a
`.pe` line that reads register words: two channel-agreeing states whose read
words differ prepare different data and therefore different forwarding
channels.  The correct frame carries the line's bank-word hypothesis as well. -/

/-- **The bank-aware channel frame.**  A line's two successful steps keep the
channels agreed, given also that the two states agree on the line's read
footprint.  For `nop`/`mv`/inert lines the extra hypothesis is redundant; for a
reading `.pe` line it is exactly what pins down the produced data. -/
def PEChannelFrameOn (footprint : InstructionLine → State → Set WordRef) (pe : PEId)
    (line : InstructionLine) : Prop :=
  ∀ (s s' next next' : State), ChanAgree pe s s' →
    FilesAgreeOn (footprint line s ∪ footprint line s')
      (s.peRegisters pe) (s'.peRegisters pe) →
    StepTo line s next → StepTo line s' next' → ChanAgree pe next next'

/-- The unconditional frame implies the bank-aware one. -/
theorem peChannelFrameOn_of_frame (footprint : InstructionLine → State → Set WordRef)
    (pe : PEId) (line : InstructionLine) (frame : PEChannelFrame pe line) :
    PEChannelFrameOn footprint pe line :=
  fun s s' next next' chan _agree step step' => frame s s' next next' chan step step'

theorem nop_channelFrameOn (footprint : InstructionLine → State → Set WordRef)
    (count : {n : Nat // 0 < n}) (wait : Option (Fin 256)) :
    PEChannelFrameOn footprint plusTwoPE (.nop count wait) :=
  peChannelFrameOn_of_frame footprint plusTwoPE (.nop count wait)
    (nop_channelFrame count wait)

theorem mv_channelFrameOn (footprint : InstructionLine → State → Set WordRef)
    (transfer : NormalizedMv) :
    PEChannelFrameOn footprint plusTwoPE (.mv transfer) :=
  peChannelFrameOn_of_frame footprint plusTwoPE (.mv transfer) (mv_channelFrame transfer)

/-- The walk leaves unvisited PEs' forwarding and validity untouched, together
with their register files and contexts. -/
theorem executeIntegerProducerLineAtPEs_peFields_of_not_mem
    (expressions : List ParsedExpr) (pes : List PEId) (state next : State) (pe : PEId)
    (absent : pe ∉ pes)
    (executed : executeIntegerProducerLineAtPEs expressions pes state = .ok next) :
    next.peRegisters pe = state.peRegisters pe ∧
      next.forwarding pe = state.forwarding pe ∧
      next.forwardingValid pe = state.forwardingValid pe ∧
      next.peContext pe = state.peContext pe := by
  induction pes generalizing state with
  | nil =>
      simp only [executeIntegerProducerLineAtPEs, StepResult.ok.injEq] at executed
      subst executed
      exact ⟨rfl, rfl, rfl, rfl⟩
  | cons head rest ih =>
      simp only [List.mem_cons, not_or] at absent
      obtain ⟨headNe, absent⟩ := absent
      simp only [executeIntegerProducerLineAtPEs] at executed
      split at executed
      · simp at executed
      · simp at executed
      · rename_i middle stepMiddle
        have tail := ih middle absent executed
        have headFrame := executeIntegerProducerLineAtPE_peFields_other expressions state
          middle head pe headNe stepMiddle
        exact ⟨tail.1.trans headFrame.1, tail.2.1.trans headFrame.2.1,
          tail.2.2.1.trans headFrame.2.2.1, tail.2.2.2.trans headFrame.2.2.2⟩


/-! ## 9. Plainness facts for the outer and stage filters -/

theorem plain_stageInput_true (expression : ParsedExpr)
    (plain : parsedExprIsPlainIntegerALU expression = true) :
    parsedExprIsIntegerMatrixReadStageInput expression = true := by
  obtain ⟨integer, unsup, msl, relu, block, supported, waitTag, mau, mwrite, l1tope,
    l2bm, nofwd, turn⟩ := parsedExprIsPlainIntegerALU_facts expression plain
  cases op : expression.op <;>
    simp_all [parsedExprIsIntegerMatrixReadStageInput, parsedExprWaitTag?,
      parsedExprIsL2BMProducer, parsedExprIsMatrixWriteProducer,
      parsedExprIsL1MwriteProducer, parsedExprIsL1GatherProducer,
      parsedExprIsL1ReduceProducer, parsedExprIsL1ToPEProducer,
      parsedExprIsMatrixMAUProducer, parsedExprIsSupportedFloatMAUProducer,
      parsedExprIsMslMsrProducer, parsedExprIsBlockFloatProducer,
      parsedExprIsFloatReluProducer, parsedExprIsIntegerProducer]

theorem plain_outerFilter (expression : ParsedExpr)
    (plain : parsedExprIsPlainIntegerALU expression = true) :
    (!parsedExprIsL2BMProducer expression && !parsedExprIsMslMsrProducer expression &&
      !parsedExprIsMatrixMAUProducer expression && !parsedExprIsBlockFloatProducer expression &&
      !parsedExprIsFloatReluProducer expression) = true := by
  obtain ⟨integer, unsup, msl, relu, block, supported, waitTag, mau, mwrite, l1tope,
    l2bm, nofwd, turn⟩ := parsedExprIsPlainIntegerALU_facts expression plain
  simp [l2bm, msl, mau, block, relu]

theorem plain_stageFilter_eq (expressions : List ParsedExpr)
    (plain : expressions.all parsedExprIsPlainIntegerALU = true) :
    expressions.filter parsedExprIsIntegerMatrixReadStageInput = expressions := by
  apply List.filter_eq_self.mpr
  intro expression member
  exact plain_stageInput_true expression (List.all_eq_true.mp plain expression member)

theorem plain_outerFilter_eq (expressions : List ParsedExpr)
    (plain : expressions.all parsedExprIsPlainIntegerALU = true) :
    expressions.filter (fun expression =>
      !parsedExprIsL2BMProducer expression && !parsedExprIsMslMsrProducer expression &&
        !parsedExprIsMatrixMAUProducer expression && !parsedExprIsBlockFloatProducer expression &&
        !parsedExprIsFloatReluProducer expression) = expressions := by
  apply List.filter_eq_self.mpr
  intro expression member
  exact plain_outerFilter expression (List.all_eq_true.mp plain expression member)

theorem plain_noForward_any (expressions : List ParsedExpr)
    (plain : expressions.all parsedExprIsPlainIntegerALU = true) :
    expressions.any (fun expression => match expression.op with
      | .noforward => true | _ => false) = false := by
  apply List.any_eq_false.mpr
  intro expression member
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, nofwd, _⟩ :=
    parsedExprIsPlainIntegerALU_facts expression (List.all_eq_true.mp plain expression member)
  intro same
  rw [← show parsedExprIsNoForwardProducer expression =
    (match expression.op with | .noforward => true | _ => false) from rfl] at same
  rw [nofwd] at same
  exact Bool.noConfusion same

theorem updateSupportedPELineForwarding_value
    (old prepared : ProofsLean.MNCore.Forwarding.Slots)
    (hasALUProducer hasMatrixReadProducer : Bool) :
    updateSupportedPELineForwarding old prepared false hasALUProducer false hasMatrixReadProducer =
      .ok (fun unit cycle => match unit with
        | .alu => if hasALUProducer then prepared .alu cycle else .poison
        | .mau => .poison
        | .matrixRead => if hasMatrixReadProducer then prepared .matrixRead cycle
            else .known (⟨0, 0⟩ : IntegerALU.Bus)
        | .l1ToPE => old unit cycle) := by
  unfold updateSupportedPELineForwarding
  simp only [Forwarding.advanceReference]
  cases hasALUProducer <;> cases hasMatrixReadProducer <;>
    (congr 1; funext unit cycle; cases unit <;> rfl)

theorem updateIntegerLineForwardingValid_value
    (old : ProofsLean.MNCore.Forwarding.Unit → Fin 4 → Bool)
    (slots : ProofsLean.MNCore.Forwarding.Slots) (noForward : Bool) :
    updateIntegerLineForwardingValid old slots noForward =
      fun unit cycle =>
        if noForward then old unit cycle
        else if unit = .l1ToPE then old unit cycle
        else forwardingValueValid (slots unit cycle) := rfl


/-! ## 10. The forwarding channel after a plain line -/

/-- The forwarding channel one plain line leaves at the observed PE: the `.alu`
cycles carry the prepared slots (enabled when they are resolvable), `.matrixRead`
carries the zero slot, and `.l1ToPE` is preserved. -/
def lineForwardingChannel (oldL1 : Fin 4 → ProofsLean.MNCore.Forwarding.Value IntegerALU.Bus)
    (slots : ProofsLean.MNCore.Forwarding.Slots) (hasALU hasMatrixRead : Bool) :
    ProofsLean.MNCore.Forwarding.Unit → Fin 4 → ProofsLean.MNCore.Forwarding.Value IntegerALU.Bus :=
  fun unit cycle => match unit with
    | .alu => if hasALU then
        (if forwardingValueValid (slots .alu cycle) then slots .alu cycle else .poison)
      else .poison
    | .mau => .poison
    | .matrixRead => if hasMatrixRead then
        (if forwardingValueValid (slots .matrixRead cycle) then slots .matrixRead cycle
          else .poison)
      else .known (⟨0, 0⟩ : IntegerALU.Bus)
    | .l1ToPE => oldL1 cycle

/-- **The masked forwarding channel of a successful plain per-PE core** is the
line's forwarding channel: the payload installed by the forwarding update,
masked by the validity the update derives from it. -/
theorem stateForwardingSlots_after_plain
    (state : State) (pe : PEId) (slots : ProofsLean.MNCore.Forwarding.Slots)
    (forwarding : ProofsLean.MNCore.Forwarding.Slots) (noForward : Bool)
    (hasALU hasMatrixRead : Bool)
    (noForwardFalse : noForward = false)
    (forwardingEq : forwarding = fun unit cycle => match unit with
      | .alu => if hasALU then slots .alu cycle else .poison
      | .mau => .poison
      | .matrixRead => if hasMatrixRead then slots .matrixRead cycle
          else .known (⟨0, 0⟩ : IntegerALU.Bus)
      | .l1ToPE => stateForwardingSlots state pe .l1ToPE cycle) :
    (fun unit cycle =>
        if updateIntegerLineForwardingValid (state.forwardingValid pe) forwarding noForward
            unit cycle
        then forwarding unit cycle else .poison) =
      lineForwardingChannel (fun cycle => stateForwardingSlots state pe .l1ToPE cycle)
        slots hasALU hasMatrixRead := by
  funext unit cycle
  rw [noForwardFalse]
  cases unit with
  | alu =>
      rw [forwardingEq]
      by_cases h : hasALU
      · simp [lineForwardingChannel, updateIntegerLineForwardingValid, h]
      · simp [lineForwardingChannel, updateIntegerLineForwardingValid, h]
  | mau =>
      rw [forwardingEq]
      simp [lineForwardingChannel, updateIntegerLineForwardingValid, forwardingValueValid]
  | matrixRead =>
      rw [forwardingEq]
      by_cases matrix : hasMatrixRead
      · simp [lineForwardingChannel, updateIntegerLineForwardingValid, matrix]
      · simp [lineForwardingChannel, updateIntegerLineForwardingValid, matrix,
          forwardingValueValid]
  | l1ToPE =>
      rw [forwardingEq]
      simp only [lineForwardingChannel, updateIntegerLineForwardingValid]
      simp only [Bool.false_eq_true, ite_false, ite_true]
      by_cases valid : state.forwardingValid pe .l1ToPE cycle
      · simp [stateForwardingSlots, valid]
      · simp [stateForwardingSlots, valid]

/-- The same channel is equal for two runs with equal inputs. -/
theorem lineForwardingChannel_congr
    (oldL1 oldL1' : Fin 4 → ProofsLean.MNCore.Forwarding.Value IntegerALU.Bus)
    (slots slots' : ProofsLean.MNCore.Forwarding.Slots) (hasALU hasALU' hasMatrixRead
      hasMatrixRead' : Bool)
    (oldEq : oldL1 = oldL1') (slotsEq : slots = slots')
    (aluEq : hasALU = hasALU') (matrixEq : hasMatrixRead = hasMatrixRead') :
    lineForwardingChannel oldL1 slots hasALU hasMatrixRead =
      lineForwardingChannel oldL1' slots' hasALU' hasMatrixRead' := by
  rw [oldEq, slotsEq, aluEq, matrixEq]


/-! ## 11. The strong prepared-list congruence (writes, slots and BAR updates) -/

/-- Strong form of `PEPreparedListCongruent`: the whole triple of the integer
stage's preparation is a function of the channels plus the footprint words.  The
forwarding slots and the BAR updates are needed by the channel frame, because the
executor installs the prepared data into the forwarding channel. -/
def PEPreparedListCongruentStrong (footprint : InstructionLine → State → Set WordRef)
    (expressions : List NormalizedExpr) : Prop :=
  ∀ (s s' : State) (w w' : List PreparedParsedMaskedWrite)
      (slots slots' : Forwarding.Slots) (bars bars' : List (Bool × BitVec 12)),
    ChanAgree plusTwoPE s s' →
    FilesAgreeOn (footprint (.pe expressions) s ∪ footprint (.pe expressions) s')
      (s.peRegisters plusTwoPE) (s'.peRegisters plusTwoPE) →
    welcomeIntegerPrep s plusTwoPE (peWalkExpressions expressions) = .ok (w, slots, bars) →
    welcomeIntegerPrep s' plusTwoPE (peWalkExpressions expressions) = .ok (w', slots', bars') →
    w = w' ∧ slots = slots' ∧ bars = bars'

theorem pepreparedListCongruentStrong_plain
    (footprint : InstructionLine → State → Set WordRef)
    (expressions : List NormalizedExpr)
    (plain : (expressions.map NormalizedExpr.toParsed).all
      parsedExprIsPlainIntegerALU = true)
    (covers : ∀ (s s' : State), ChanAgree plusTwoPE s s' →
      preparedListReadSet ((s.peRegisters plusTwoPE)).maskRegisters
          ((expressions.map NormalizedExpr.toParsed).filter
            parsedExprIsIntegerMatrixReadStageInput)
          (parsedPEHazardControl s plusTwoPE) ⊆
        footprint (.pe expressions) s ∪ footprint (.pe expressions) s') :
    PEPreparedListCongruentStrong footprint expressions := by
  intro s s' w w' slots slots' bars bars' chan agree prep prep'
  have maskEq : (s.peRegisters plusTwoPE).maskRegisters =
      (s'.peRegisters plusTwoPE).maskRegisters := chanAgree_maskRegisters chan
  have slotEq : stateForwardingSlots s plusTwoPE = stateForwardingSlots s' plusTwoPE :=
    chanAgree_forwardingSlots chan
  have storeEq := chanAgree_matrix chan
  have contextEq : s.peContext plusTwoPE = s'.peContext plusTwoPE := chanAgree_context chan
  have directiveEq : s.maskDirective = s'.maskDirective := chanAgree_maskDirective chan
  have clockEq : s.hazardClock = s'.hazardClock := chanAgree_clock chan
  have controlEq : parsedPEHazardControl s plusTwoPE = parsedPEHazardControl s' plusTwoPE := by
    simp only [parsedPEHazardControl]
    rw [contextEq, directiveEq, clockEq]
  unfold welcomeIntegerPrep at prep prep'
  rw [← controlEq, ← storeEq] at prep'
  have filteredPlain : ∀ expression ∈
      (expressions.map NormalizedExpr.toParsed).filter
        parsedExprIsIntegerMatrixReadStageInput,
      parsedExprIsPlainIntegerALU expression = true := by
    intro expression member
    exact List.all_eq_true.mp plain expression (List.mem_of_mem_filter member)
  have coverage := covers s s' chan
  have agreement : FilesAgreeOn
      (preparedListReadSet (s.peRegisters plusTwoPE).maskRegisters
        ((expressions.map NormalizedExpr.toParsed).filter
          parsedExprIsIntegerMatrixReadStageInput)
        (parsedPEHazardControl s plusTwoPE))
      (s.peRegisters plusTwoPE) (s'.peRegisters plusTwoPE) :=
    agree.mono coverage
  exact prepareParsedIntegerMatrixReadLineCycles_congr_plain
    (s.peRegisters plusTwoPE) (s'.peRegisters plusTwoPE)
    (stateForwardingSlots s plusTwoPE) (stateForwardingSlots s' plusTwoPE)
    (s.matrixRegisters (ParsedIntegerContext.ofLinearIndex plusTwoPE).group
      (ParsedIntegerContext.ofLinearIndex plusTwoPE).l2b
      (ParsedIntegerContext.ofLinearIndex plusTwoPE).l1b)
    ((expressions.map NormalizedExpr.toParsed).filter
      parsedExprIsIntegerMatrixReadStageInput)
    (parsedPEHazardControl s plusTwoPE) false
    (preparedListReadSet (s.peRegisters plusTwoPE).maskRegisters
      ((expressions.map NormalizedExpr.toParsed).filter
        parsedExprIsIntegerMatrixReadStageInput)
      (parsedPEHazardControl s plusTwoPE))
    filteredPlain (fun w hw => hw) maskEq slotEq agreement
    w slots bars w' slots' bars' prep prep'

theorem pepreparedListCongruent_of_strong
    (footprint : InstructionLine → State → Set WordRef)
    (expressions : List NormalizedExpr)
    (strong : PEPreparedListCongruentStrong footprint expressions) :
    PEPreparedListCongruent footprint expressions := by
  intro s s' w w' slots slots' bars bars' chan agree prep prep'
  exact (strong s s' w w' slots slots' bars bars' chan agree prep prep').1


/-! ## 12. The bank-aware channel frame for plain `.pe` lines -/

theorem plain_pe_channelFrameOn_of_prepared
    (footprint : InstructionLine → State → Set WordRef)
    (expressions : List NormalizedExpr)
    (plain : (expressions.map NormalizedExpr.toParsed).all
      parsedExprIsPlainIntegerALU = true)
    (prepared : PEPreparedListCongruentStrong footprint expressions)
    (covers : ∀ (s s' : State), ChanAgree plusTwoPE s s' →
      preparedListReadSet ((s.peRegisters plusTwoPE)).maskRegisters
          ((expressions.map NormalizedExpr.toParsed).filter
            parsedExprIsIntegerMatrixReadStageInput)
          (parsedPEHazardControl s plusTwoPE) ⊆
        footprint (.pe expressions) s ∪ footprint (.pe expressions) s') :
    PEChannelFrameOn footprint plusTwoPE (.pe expressions) := by
  intro s s' next next' chan agree step step'
  have executed := stepTo_pe expressions s next step
  have executed' := stepTo_pe expressions s' next' step'
  have accepted := executeIntegerProducerInstructionLine_accepted_of_ok
    (.pe expressions) s next executed
  have accepted' := executeIntegerProducerInstructionLine_accepted_of_ok
    (.pe expressions) s' next' executed'
  obtain ⟨nextPEs, walk, nextEq⟩ :=
    executeIntegerProducerInstructionLine_pe_plainIntegerALU_exists expressions s next
      accepted plain executed
  obtain ⟨nextPEs', walk', nextEq'⟩ :=
    executeIntegerProducerInstructionLine_pe_plainIntegerALU_exists expressions s' next'
      accepted' plain executed'
  let stageList := ((expressions.map NormalizedExpr.toParsed).filter (fun expression =>
    !parsedExprIsL2BMProducer expression && !parsedExprIsMslMsrProducer expression &&
      !parsedExprIsMatrixMAUProducer expression && !parsedExprIsBlockFloatProducer expression &&
      !parsedExprIsFloatReluProducer expression))
  have walkNamed : executeIntegerProducerLineAtPEs stageList (List.finRange 4096) s =
      .ok nextPEs := walk
  have walkNamed' : executeIntegerProducerLineAtPEs stageList (List.finRange 4096) s' =
      .ok nextPEs' := walk'
  have stageMap : stageList = expressions.map NormalizedExpr.toParsed :=
    plain_outerFilter_eq _ plain
  have stageEq : stageList = (expressions.map NormalizedExpr.toParsed).filter
      parsedExprIsIntegerMatrixReadStageInput := by
    rw [stageMap]
    exact (plain_stageFilter_eq _ plain).symm
  rw [plusTwoFinRange_split.1] at walkNamed walkNamed'
  obtain ⟨middle, headStep⟩ :=
    executeIntegerProducerLineAtPEs_head_ok stageList plusTwoPE _ s nextPEs walkNamed
  obtain ⟨middle', headStep'⟩ :=
    executeIntegerProducerLineAtPEs_head_ok stageList plusTwoPE _ s' nextPEs' walkNamed'
  have walkTail : executeIntegerProducerLineAtPEs stageList (List.map Fin.succ (List.finRange 4095))
      middle = .ok nextPEs := by
    simpa only [executeIntegerProducerLineAtPEs, headStep] using walkNamed
  have walkTail' : executeIntegerProducerLineAtPEs stageList (List.map Fin.succ (List.finRange 4095))
      middle' = .ok nextPEs' := by
    simpa only [executeIntegerProducerLineAtPEs, headStep'] using walkNamed'
  have plainStage : stageList.all parsedExprIsPlainIntegerALU = true := by
    rw [stageMap]; exact plain
  have coreStep : executeIntegerProducerLineAtPECore stageList s plusTwoPE = .ok middle := by
    unfold executeIntegerProducerLineAtPE at headStep
    split at headStep
    · simp at headStep
    · exact headStep
  have coreStep' : executeIntegerProducerLineAtPECore stageList s' plusTwoPE = .ok middle' := by
    unfold executeIntegerProducerLineAtPE at headStep'
    split at headStep'
    · simp at headStep'
    · exact headStep'
  obtain ⟨w, slots, bars, forwarding, prepA, regsA, fwdA, validA, ctxA, updA⟩ :=
    executeIntegerProducerLineAtPECore_plain_fields stageList s middle plusTwoPE
      plainStage coreStep
  obtain ⟨w', slots', bars', forwarding', prepB, regsB, fwdB, validB, ctxB, updB⟩ :=
    executeIntegerProducerLineAtPECore_plain_fields stageList s' middle' plusTwoPE
      plainStage coreStep'
  rw [stageMap] at prepA prepB
  have prepA' : welcomeIntegerPrep s plusTwoPE (peWalkExpressions expressions) =
      .ok (w, slots, bars) := by
    rw [peWalkExpressions]
    exact prepA
  have prepB' : welcomeIntegerPrep s' plusTwoPE (peWalkExpressions expressions) =
      .ok (w', slots', bars') := by
    rw [peWalkExpressions]
    exact prepB
  obtain ⟨writesEq, slotsEq, barsEq⟩ :=
    prepared s s' w w' slots slots' bars bars' chan agree prepA' prepB'
  -- field frames of the walk tail
  obtain ⟨regsTail, fwdTail, validTail, ctxTail⟩ :=
    executeIntegerProducerLineAtPEs_peFields_of_not_mem stageList
      (List.map Fin.succ (List.finRange 4095)) middle nextPEs plusTwoPE
      plusTwoFinRange_split.2 walkTail
  obtain ⟨regsTail', fwdTail', validTail', ctxTail'⟩ :=
    executeIntegerProducerLineAtPEs_peFields_of_not_mem stageList
      (List.map Fin.succ (List.finRange 4095)) middle' nextPEs' plusTwoPE
      plusTwoFinRange_split.2 walkTail'
  have sameOtherA := executeIntegerProducerLineAtPEs_sameOther stageList
    (plusTwoPE :: List.map Fin.succ (List.finRange 4095)) s nextPEs walkNamed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hMatrixA, hDirectiveA, hClockA⟩ := sameOtherA
  have sameOtherB := executeIntegerProducerLineAtPEs_sameOther stageList
    (plusTwoPE :: List.map Fin.succ (List.finRange 4095)) s' nextPEs' walkNamed'
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hMatrixB, hDirectiveB, hClockB⟩ := sameOtherB
  -- the payload of the forwarding update
  have noForwardFalse : (stageList.any fun expression => match expression.op with
      | .noforward => true | _ => false) = false := by
    rw [stageMap]; exact plain_noForward_any _ plain
  have preparedFnEq : (fun unit cycle =>
      if unit = ProofsLean.MNCore.Forwarding.Unit.mau && false then
        .known (⟨0, 0⟩ : IntegerALU.Bus)
      else slots unit cycle) = slots := by
    funext unit cycle
    simp
  have forwardingValue : forwarding = fun unit cycle => match unit with
      | .alu => if stageList.any parsedExprIsIntegerProducer then slots .alu cycle else .poison
      | .mau => .poison
      | .matrixRead => if stageList.any parsedExprIsMatrixReadProducer then
          slots .matrixRead cycle else .known (⟨0, 0⟩ : IntegerALU.Bus)
      | .l1ToPE => stateForwardingSlots s plusTwoPE .l1ToPE cycle := by
    have value := updateSupportedPELineForwarding_value (stateForwardingSlots s plusTwoPE)
      slots (stageList.any parsedExprIsIntegerProducer)
      (stageList.any parsedExprIsMatrixReadProducer)
    rw [preparedFnEq, noForwardFalse] at updA
    rw [value] at updA
    have h := (StepResult.ok.inj updA).symm
    rw [h]
    funext unit cycle
    cases unit <;> rfl
  have preparedFnEq' : (fun unit cycle =>
      if unit = ProofsLean.MNCore.Forwarding.Unit.mau && false then
        .known (⟨0, 0⟩ : IntegerALU.Bus)
      else slots' unit cycle) = slots' := by
    funext unit cycle
    simp
  have forwardingValue' : forwarding' = fun unit cycle => match unit with
      | .alu => if stageList.any parsedExprIsIntegerProducer then slots' .alu cycle else .poison
      | .mau => .poison
      | .matrixRead => if stageList.any parsedExprIsMatrixReadProducer then
          slots' .matrixRead cycle else .known (⟨0, 0⟩ : IntegerALU.Bus)
      | .l1ToPE => stateForwardingSlots s' plusTwoPE .l1ToPE cycle := by
    have value := updateSupportedPELineForwarding_value (stateForwardingSlots s' plusTwoPE)
      slots' (stageList.any parsedExprIsIntegerProducer)
      (stageList.any parsedExprIsMatrixReadProducer)
    rw [preparedFnEq', noForwardFalse] at updB
    rw [value] at updB
    have h := (StepResult.ok.inj updB).symm
    rw [h]
    funext unit cycle
    cases unit <;> rfl
  -- the channel equalities at the observed PE of the walk result
  have channelA : stateForwardingSlots nextPEs plusTwoPE =
      lineForwardingChannel (fun cycle => stateForwardingSlots s plusTwoPE .l1ToPE cycle)
        slots (stageList.any parsedExprIsIntegerProducer)
        (stageList.any parsedExprIsMatrixReadProducer) := by
    show (fun unit cycle => if nextPEs.forwardingValid plusTwoPE unit cycle
      then nextPEs.forwarding plusTwoPE unit cycle else .poison) = _
    rw [fwdTail, validTail, fwdA, validA]
    exact stateForwardingSlots_after_plain s plusTwoPE slots forwarding
      (stageList.any fun expression => match expression.op with | .noforward => true | _ => false)
      (stageList.any parsedExprIsIntegerProducer) (stageList.any parsedExprIsMatrixReadProducer)
      noForwardFalse forwardingValue
  have channelB : stateForwardingSlots nextPEs' plusTwoPE =
      lineForwardingChannel (fun cycle => stateForwardingSlots s' plusTwoPE .l1ToPE cycle)
        slots' (stageList.any parsedExprIsIntegerProducer)
        (stageList.any parsedExprIsMatrixReadProducer) := by
    show (fun unit cycle => if nextPEs'.forwardingValid plusTwoPE unit cycle
      then nextPEs'.forwarding plusTwoPE unit cycle else .poison) = _
    rw [fwdTail', validTail', fwdB, validB]
    exact stateForwardingSlots_after_plain s' plusTwoPE slots' forwarding'
      (stageList.any fun expression => match expression.op with | .noforward => true | _ => false)
      (stageList.any parsedExprIsIntegerProducer) (stageList.any parsedExprIsMatrixReadProducer)
      noForwardFalse forwardingValue'
  have maskEq : (nextPEs.peRegisters plusTwoPE).maskRegisters =
      (nextPEs'.peRegisters plusTwoPE).maskRegisters := by
    rw [regsTail, regsTail', regsA, regsB, writesEq]
    exact commitParsedMaskedWrites_maskRegisters_congr _ _ w' (chanAgree_maskRegisters chan)
  have contextEq : nextPEs.peContext plusTwoPE = nextPEs'.peContext plusTwoPE := by
    rw [ctxTail, ctxTail', ctxA, ctxB, barsEq, chanAgree_context chan]
  have matrixEq : nextPEs.matrixRegisters
      (ParsedIntegerContext.ofLinearIndex plusTwoPE).group
      (ParsedIntegerContext.ofLinearIndex plusTwoPE).l2b
      (ParsedIntegerContext.ofLinearIndex plusTwoPE).l1b =
      nextPEs'.matrixRegisters
      (ParsedIntegerContext.ofLinearIndex plusTwoPE).group
      (ParsedIntegerContext.ofLinearIndex plusTwoPE).l2b
      (ParsedIntegerContext.ofLinearIndex plusTwoPE).l1b := by
    rw [← hMatrixA, chanAgree_matrix chan, hMatrixB]
  have directiveEq : nextPEs.maskDirective = nextPEs'.maskDirective := by
    rw [← hDirectiveA, chanAgree_maskDirective chan, hDirectiveB]
  have clockEq : nextPEs.hazardClock = nextPEs'.hazardClock := by
    rw [← hClockA, chanAgree_clock chan, hClockB]
  have slotsEq' : stateForwardingSlots nextPEs plusTwoPE = stateForwardingSlots nextPEs' plusTwoPE := by
    rw [channelA, channelB]
    exact lineForwardingChannel_congr _ _ _ _ _ _ _ _
      (congrFun (chanAgree_forwardingSlots chan) .l1ToPE) slotsEq rfl rfl
  -- assemble the channel tuple
  show stateChannels plusTwoPE next = stateChannels plusTwoPE next'
  rw [nextEq, nextEq']
  simp only [stateChannels]
  change (⟨stateForwardingSlots nextPEs plusTwoPE,
      (nextPEs.peRegisters plusTwoPE).maskRegisters,
      nextPEs.matrixRegisters (ParsedIntegerContext.ofLinearIndex plusTwoPE).group
        (ParsedIntegerContext.ofLinearIndex plusTwoPE).l2b
        (ParsedIntegerContext.ofLinearIndex plusTwoPE).l1b,
      nextPEs.maskDirective, nextPEs.peContext plusTwoPE,
      nextPEs.hazardClock + InstructionLine.cost (.pe expressions)⟩ : NonBankChannels) =
    ⟨stateForwardingSlots nextPEs' plusTwoPE,
      (nextPEs'.peRegisters plusTwoPE).maskRegisters,
      nextPEs'.matrixRegisters (ParsedIntegerContext.ofLinearIndex plusTwoPE).group
        (ParsedIntegerContext.ofLinearIndex plusTwoPE).l2b
        (ParsedIntegerContext.ofLinearIndex plusTwoPE).l1b,
      nextPEs'.maskDirective, nextPEs'.peContext plusTwoPE,
      nextPEs'.hazardClock + InstructionLine.cost (.pe expressions)⟩
  rw [slotsEq', maskEq, matrixEq, directiveEq, contextEq, clockEq]


/-! ## 13. The concrete residuals and the end-to-end theorem -/

theorem pepreparedListCongruentStrong_concrete_of_covers
    (covers : PlusTwoLineFootprintCoversPreparedReads)
    (expressions : List NormalizedExpr)
    (plain : (expressions.map NormalizedExpr.toParsed).all
      parsedExprIsPlainIntegerALU = true) :
    PEPreparedListCongruentStrong plusTwoLineFootprint expressions :=
  pepreparedListCongruentStrong_plain plusTwoLineFootprint expressions plain
    (fun s s' _chan w hw => Or.inl (covers expressions plain s hw))

/-- **The bank-aware frame at the concrete footprint.** -/
theorem plain_pe_channelFrameOn_concrete
    (covers : PlusTwoLineFootprintCoversPreparedReads)
    (expressions : List NormalizedExpr)
    (plain : (expressions.map NormalizedExpr.toParsed).all
      parsedExprIsPlainIntegerALU = true) :
    PEChannelFrameOn plusTwoLineFootprint plusTwoPE (.pe expressions) :=
  plain_pe_channelFrameOn_of_prepared plusTwoLineFootprint expressions plain
    (pepreparedListCongruentStrong_concrete_of_covers covers expressions plain)
    (fun s s' _chan w hw => Or.inl (covers expressions plain s hw))

/-- **The `.pe` reduction for plain-ALU lines at the bank-aware frame.**  This is
`plain_pe_lineDeterminedAtChan_of_prepared` with the frame repaired: the frame
gets the line's bank-word hypothesis, which is exactly what the executor's
forwarding update needs (it installs the prepared data into the forwarding
channel). -/
theorem plain_pe_lineDeterminedAtChan_of_preparedOn
    (footprint : InstructionLine → State → Set WordRef)
    (expressions : List NormalizedExpr)
    (plain : (expressions.map NormalizedExpr.toParsed).all
      parsedExprIsPlainIntegerALU = true)
    (prepared : PEPreparedListCongruent footprint expressions)
    (frame : PEChannelFrameOn footprint plusTwoPE (.pe expressions)) :
    LineDeterminedAtChan footprint plusTwoPE (.pe expressions) := by
  intro s s' next next' agree chan step step'
  have executed := stepTo_pe expressions s next step
  have executed' := stepTo_pe expressions s' next' step'
  have accepted := executeIntegerProducerInstructionLine_accepted_of_ok
    (.pe expressions) s next executed
  have accepted' := executeIntegerProducerInstructionLine_accepted_of_ok
    (.pe expressions) s' next' executed'
  obtain ⟨nextPEs, walk, nextEq⟩ :=
    executeIntegerProducerInstructionLine_pe_plainIntegerALU_exists expressions s next
      accepted plain executed
  obtain ⟨nextPEs', walk', nextEq'⟩ :=
    executeIntegerProducerInstructionLine_pe_plainIntegerALU_exists expressions s' next'
      accepted' plain executed'
  rw [plain_peFilter_eq_self (expressions.map NormalizedExpr.toParsed) plain] at walk walk'
  have floatEmpty := plain_floatFilter_eq_nil (expressions.map NormalizedExpr.toParsed) plain
  obtain ⟨w, slots, bars, prep, commit⟩ :=
    executeIntegerProducerLineAtPEs_prepared (peWalkExpressions expressions)
      (List.finRange 4096) s nextPEs floatEmpty walk (List.nodup_finRange 4096)
      plusTwoPE (by simp [plusTwoPE, welcomePE])
  obtain ⟨w', slots', bars', prep', commit'⟩ :=
    executeIntegerProducerLineAtPEs_prepared (peWalkExpressions expressions)
      (List.finRange 4096) s' nextPEs' floatEmpty walk' (List.nodup_finRange 4096)
      plusTwoPE (by simp [plusTwoPE, welcomePE])
  have same : w = w' := prepared s s' w w' slots slots' bars bars' chan agree prep prep'
  refine ⟨w, ?_, ?_, frame s s' next next' chan agree step step'⟩
  · show next.peRegisters plusTwoPE = commitParsedMaskedWrites (s.peRegisters plusTwoPE) w
    rw [nextEq]
    exact commit
  · show next'.peRegisters plusTwoPE = commitParsedMaskedWrites (s'.peRegisters plusTwoPE) w
    rw [nextEq', same]
    exact commit'

/-- **The plain-ALU `.pe` line satisfies the channel contract at the concrete
footprint**, from the coverage residual alone. -/
theorem plain_pe_lineDeterminedAtChan_concrete
    (covers : PlusTwoLineFootprintCoversPreparedReads)
    (expressions : List NormalizedExpr)
    (plain : (expressions.map NormalizedExpr.toParsed).all
      parsedExprIsPlainIntegerALU = true) :
    LineDeterminedAtChan plusTwoLineFootprint plusTwoPE (.pe expressions) :=
  plain_pe_lineDeterminedAtChan_of_preparedOn plusTwoLineFootprint expressions plain
    (pepreparedListCongruent_concrete_of_covers covers expressions plain)
    (plain_pe_channelFrameOn_concrete covers expressions plain)

/-- The line classes discharged without further executor analysis: `nop`, `mv`,
and plain-ALU `.pe` lines. -/
def DischargedLine (line : InstructionLine) : Prop :=
  (∃ (count : {n : Nat // 0 < n}) (wait : Option (Fin 256)),
      line = .nop count wait) ∨
  (∃ transfer : NormalizedMv, line = .mv transfer) ∨
  (∃ expressions : List NormalizedExpr,
      line = .pe expressions ∧
        (expressions.map NormalizedExpr.toParsed).all parsedExprIsPlainIntegerALU = true)

theorem lineDeterminedAtChan_of_discharged
    (covers : PlusTwoLineFootprintCoversPreparedReads)
    (line : InstructionLine) (discharged : DischargedLine line) :
    LineDeterminedAtChan plusTwoLineFootprint plusTwoPE line := by
  rcases discharged with ⟨count, wait, rfl⟩ | ⟨transfer, rfl⟩ | ⟨expressions, rfl, plain⟩
  · exact nop_lineDeterminedAtChan plusTwoLineFootprint count wait
  · exact mv_lineDeterminedAtChan plusTwoLineFootprint transfer
  · exact plain_pe_lineDeterminedAtChan_concrete covers expressions plain

/-- **The channel version of the old false `PlusTwoWriteDetermination`**, for
programs whose lines are all in the discharged classes. -/
theorem plusTwoWriteDeterminationChan_of_discharged
    (covers : PlusTwoLineFootprintCoversPreparedReads)
    (program : List InstructionLine)
    (discharged : ∀ line ∈ program, DischargedLine line) :
    ∀ line ∈ program, LineDeterminedAtChan plusTwoLineFootprint plusTwoPE line :=
  fun line member => lineDeterminedAtChan_of_discharged covers line (discharged line member)

/-- **End-to-end: a program that never reads input `j` is incorrect**, at the
concrete footprint and the channel-aware contract, for programs built from the
discharged line classes.  The only remaining premise is the footprint-coverage
residual `PlusTwoLineFootprintCoversPreparedReads`. -/
theorem plusTwo_not_correct_of_concrete_footprint_avoids_chan_of_discharged
    (covers : PlusTwoLineFootprintCoversPreparedReads)
    (program : List InstructionLine)
    (discharged : ∀ line ∈ program, DischargedLine line)
    (j : Fin 20)
    (avoids : ∀ line ∈ program, ∀ s s' : State,
      plusTwoInputWord j ∉ plusTwoLineFootprint line s ∧
        plusTwoInputWord j ∉ plusTwoLineFootprint line s') :
    ¬ ProofsLean.Correct plusTwoSealedMachine plusTwoSpec program :=
  plusTwo_not_correct_of_concrete_footprint_avoids_chan program
    (plusTwoWriteDeterminationChan_of_discharged covers program discharged) j avoids


/-! ## 14. The machine-checked obstruction to the unconditional frame -/

/-- **The forwarding channel is fed by the prepared data.**  A successful
integer-ALU cycle installs `pack write.data` into the `.alu` slot of its cycle
and leaves every other slot alone.  Together with
`forwardingValueValid (.known _) = true` this is why `PEChannelFrame` — which
assumes channel agreement but *no* bank-word agreement — is not a theorem for a
`.pe` line that reads register words: two channel-agreeing states with different
read words prepare different data and therefore different forwarding channels.
The bank-aware `PEChannelFrameOn` above is the correct frame, and it is proved
for all plain-ALU lines. -/
theorem updateParsedIntegerALUForwardingCycle_installs_data
    (old : ProofsLean.MNCore.Forwarding.Slots) (cycle : Fin 4)
    (write : PreparedParsedMaskedWrite) :
    updateParsedIntegerALUForwardingCycle old cycle (.ok write) false =
      .ok (fun unit slotCycle =>
        if unit = ProofsLean.MNCore.Forwarding.Unit.alu ∧ slotCycle = cycle then
          .known (pack write.data)
        else old unit slotCycle) := by
  rw [updateParsedIntegerALUForwardingCycle_semantics]
  rfl

/-! ## 15. The channel version of `PlusTwoWriteDetermination` -/

/-- **The channel-aware replacement of the old false `PlusTwoWriteDetermination`:**
every line commits the same PE-0 write list at two states that agree on its
footprint *and* on the six non-bank channels, and the channels still agree
afterwards. -/
def PlusTwoWriteDeterminationChan : Prop :=
  ∀ line, LineDeterminedAtChan plusTwoLineFootprint plusTwoPE line

/-- The single-residual form of the program-level determination. -/
theorem lineDeterminedAtChan_of_determinationChan
    (determination : PlusTwoWriteDeterminationChan) (line : InstructionLine) :
    LineDeterminedAtChan plusTwoLineFootprint plusTwoPE line :=
  determination line

/-- **The usable end-to-end form at the channel contract.**  If the channel
version of write determination holds and a program never reads input `j`, the
program is incorrect. -/
theorem plusTwo_not_correct_of_determinationChan
    (determination : PlusTwoWriteDeterminationChan)
    (program : List InstructionLine) (j : Fin 20)
    (avoids : ∀ line ∈ program, ∀ s s' : State,
      plusTwoInputWord j ∉ plusTwoLineFootprint line s ∧
        plusTwoInputWord j ∉ plusTwoLineFootprint line s') :
    ¬ ProofsLean.Correct plusTwoSealedMachine plusTwoSpec program :=
  plusTwo_not_correct_of_concrete_footprint_avoids_chan program
    (fun line _ => determination line) j avoids

/-- **`PlusTwoWriteDeterminationChan` for programs in the discharged classes**,
from the footprint-coverage residual. -/
theorem plusTwoWriteDeterminationChan_of_all_discharged
    (covers : PlusTwoLineFootprintCoversPreparedReads)
    (all : ∀ line, DischargedLine line) :
    PlusTwoWriteDeterminationChan :=
  fun line => lineDeterminedAtChan_of_discharged covers line (all line)

/-- **The headline reduction for programs in the discharged classes.**  Such a
program is correct only if, for every input index `j`, some line's concrete
hazard-event footprint contains the LM0 word of input `j` — at the channel-aware
contract, from the coverage residual alone. -/
theorem plusTwo_output_forces_footprint_meets_chan_of_discharged
    (covers : PlusTwoLineFootprintCoversPreparedReads)
    (program : List InstructionLine)
    (discharged : ∀ line ∈ program, DischargedLine line)
    (correct : ProofsLean.Correct plusTwoSealedMachine plusTwoSpec program)
    (j : Fin 20) :
    ∃ line ∈ program, ∃ s s' : State,
      plusTwoInputWord j ∈ plusTwoLineFootprint line s ∨
        plusTwoInputWord j ∈ plusTwoLineFootprint line s' :=
  plusTwo_output_forces_footprint_meets_chan plusTwoLineFootprint program
    (plusTwoWriteDeterminationChan_of_discharged covers program discharged) correct j

end ProofsLean.MNCore
