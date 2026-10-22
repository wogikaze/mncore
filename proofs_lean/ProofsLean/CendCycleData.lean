import ProofsLean.CendHalfMixLink

/-! # `12.convert-endian`: the executor-assembly half-mix data of the plain family

`ProofsLean/CendFinal.lean` reduced the plain both-halves family to the single
executor link `CendPlainCycleHalfMixData`: every prepared write of a plain
integer ALU cycle at the initial state carries data words `0` and `1` in the
half-mix value set `cendHalfMixWords x`.  This module discharges that link
together with the per-cycle LM1-destination alignment and the four-cycle lift
(`cendPlainCycleHalfMixData`, `cendPlainCycleLm1Aligned_general`,
`cendPlainALURow_dataAndAligned`).  `ProofsLean/CendCycleClose.lean` then
performs the row/line dispatch and derives the unconditional plain-family
refutations.

## 1. Value algebra: flushing cannot leave the half-mix set

The initial mask file is zero, so the write selection and the output flush of
every lowered write have flags `0` or `allOnes` (`resolveMaskSelection_zero_flags`
/ `resolveFlushSelection_zero_flags`).  For the two observed word indices a
`flushBus` with such flags either zeroes the word or keeps the evaluated ALU
word.  Both alternatives are data words: `0` and the datapath table word of
`cendALU_dataWord_mem`.  A data word is a half-mix of itself
(`cendHalfMix_self`), so every flushed word lies in `cendHalfMixWords`.

## 2. Source provenance of the eight lowerings

The §4 data equations of `CendLm1Obligation` express a prepared write's data as
the flushed evaluation of the two lowered reads.  We extract, from each of the
eight lowering functions, that those reads are `toParsedIntegerInput?` /
`toIntegerMaskSourceAccess?` images of operands, hence initial buses by
`cendSourceOk_toParsedIntegerInput` / `cendSourceOk_toIntegerMaskSourceAccess`.

## 3. The per-cycle theorem

`cendPlainCycleHalfMixData` follows by the nine-branch case ladder of
`prepareParsedIntegerALUExprCycle` (the skeleton of
`CendWideWitness.prepareParsedIntegerALUExprCycle_noLm1`), each branch closed by
the corresponding §4 data equation and the source provenance above.

## 4. The half-mix commit and the four-cycle lift

`mergeSelectedWord_halfMix_mem_halfMix` closes the commit over data that is
itself a half-mix (the OMR→memory feedback data), and
`commitParsedMaskedWrites_lm1_halfMix_halfMix` is the corresponding commit
induction.  The singleton-line inversion
(`prepareParsedIntegerMatrixReadLineCycles_singleton_plain_inv`) plus the
four-cycle decomposition (`prepareParsedIntegerALUExprCycles_four_general`)
turns the per-cycle theorems into `cendPlainALURow_dataAndAligned`: a single
plain `.alu` row prepares half-mix data and aligned LM1 destinations.

## 5. What remains here

Nothing of the plain family: `ProofsLean/CendCycleClose.lean` proves the
per-word obligation `CendHalfMixWordObligation`, the unconditional
`CendPlainALUBothHalvesRefuted`, and the plain-family refutations.  The
non-plain families (`CendPENonClosedRefuted`) are unchanged and are not
addressed by this module.

No `sorry`, no `admit`, no `native_decide`, no new axioms.
-/

namespace ProofsLean.MNCore

open Issue
open PEMemory

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false

/-! ## 1. Value algebra: flushing keeps the first two data words in the value set -/

/-- Every data word is a half-mix (of itself with itself). -/
theorem cendDataWords_mem_halfMix (x : BitVec 64) (word : BitVec 32)
    (member : word ∈ cendDataWords x) : word ∈ cendHalfMixWords x := by
  rw [← cendHalfMix_self word]
  exact cendHalfMixWords_mem x word word member member

theorem cendInitialPERegisters_maskRegisters_fun (x : BitVec 64) :
    (cendInitialPERegisters x).maskRegisters = zeroInitialPERegisterFiles.maskRegisters := by
  funext entry cycle
  simp [cendInitialPERegisters]

/-- `halfMask` of a zero/`allOnes` flag vector is zero or `allOnes`. -/
theorem cendHalfMask_zero_or_allOnes (flags : BitVec 4)
    (h : flags = 0 ∨ flags = BitVec.allOnes 4) :
    Masks.halfMask flags = 0 ∨ Masks.halfMask flags = BitVec.allOnes 64 := by
  rcases h with rfl | rfl
  · exact Or.inl (by decide)
  · exact Or.inr (by decide)

theorem cendDoubleMask_high_zero_or_allOnes (flags : BitVec 4)
    (h : flags = 0 ∨ flags = BitVec.allOnes 4) :
    (Masks.doubleMask flags).high = 0 ∨
      (Masks.doubleMask flags).high = BitVec.allOnes 64 := by
  rcases h with rfl | rfl
  · exact Or.inl (by decide)
  · exact Or.inr (by decide)

theorem cendDoubleMask_low_zero_or_allOnes (flags : BitVec 4)
    (h : flags = 0 ∨ flags = BitVec.allOnes 4) :
    (Masks.doubleMask flags).low = 0 ∨
      (Masks.doubleMask flags).low = BitVec.allOnes 64 := by
  rcases h with rfl | rfl
  · exact Or.inl (by decide)
  · exact Or.inr (by decide)

/-- The high-word half of a bus after a zero/`allOnes` flush of either width. -/
theorem cendFlushBus_high (width : Masks.Width) (flags : BitVec 4)
    (bus : IntegerALU.Bus) (hflags : flags = 0 ∨ flags = BitVec.allOnes 4) :
    (Masks.flushBus width flags bus).high = 0 ∨
      (Masks.flushBus width flags bus).high = bus.high := by
  cases width
  · -- long
    rcases cendHalfMask_zero_or_allOnes flags hflags with hf | hf
    · left
      simp [Masks.flushBus, hf]
    · right
      simp only [Masks.flushBus, hf]
      exact BitVec.and_allOnes
  · -- double
    rcases cendDoubleMask_high_zero_or_allOnes flags hflags with hf | hf
    · left
      simp [Masks.flushBus, hf]
    · right
      simp only [Masks.flushBus, hf]
      exact BitVec.and_allOnes

/-- **A zero/`allOnes` flush either zeroes or keeps the first two data words.** -/
theorem cendFlushBus_data_lt_two (width : Masks.Width) (flags : BitVec 4)
    (bus : IntegerALU.Bus) (hflags : flags = 0 ∨ flags = BitVec.allOnes 4)
    (i : Fin 4) (hi : i.val < 2) :
    unpackALUBus (Masks.flushBus width flags bus) i = 0 ∨
      unpackALUBus (Masks.flushBus width flags bus) i = unpackALUBus bus i := by
  have h01 : i.val = 0 ∨ i.val = 1 := by omega
  rcases h01 with h | h
  · have hi' : i = (⟨0, by decide⟩ : Fin 4) := Fin.ext h
    subst hi'
    have goalEq : unpackALUBus (Masks.flushBus width flags bus)
        (⟨0, by decide⟩ : Fin 4) =
        (Masks.flushBus width flags bus).high.extractLsb' 32 32 := rfl
    rw [goalEq]
    rcases cendFlushBus_high width flags bus hflags with hh | hh
    · left; rw [hh]; simp
    · right; rw [hh]; rfl
  · have hi' : i = (⟨1, by decide⟩ : Fin 4) := Fin.ext h
    subst hi'
    have goalEq : unpackALUBus (Masks.flushBus width flags bus)
        (⟨1, by decide⟩ : Fin 4) =
        (Masks.flushBus width flags bus).high.extractLsb' 0 32 := rfl
    rw [goalEq]
    rcases cendFlushBus_high width flags bus hflags with hh | hh
    · left; rw [hh]; simp
    · right; rw [hh]; rfl

/-- **The first two flushed data words are data words.**  The raw bus words are
datapath words of the initial input, and a zero/`allOnes` flush either zeroes a
word or keeps it. -/
theorem parsedOutputAfterFlush_data_mem (x : BitVec 64)
    (selection : Option PEWordSelection)
    (hflags : selection = none ∨ ∃ s, selection = some s ∧
      (s.flags = 0 ∨ s.flags = BitVec.allOnes 4))
    (output : IntegerALU.Bus)
    (hout : ∀ j : Fin 4, j.val < 2 → unpackALUBus output j ∈ cendDatapathWords x)
    (i : Fin 4) (hi : i.val < 2) :
    unpackALUBus (parsedOutputAfterFlush selection output) i ∈ cendDataWords x := by
  rcases hflags with rfl | ⟨s, rfl, hflags⟩
  · simpa [parsedOutputAfterFlush] using
      cendDataWords_of_datapath x _ (hout i hi)
  · have flushed := cendFlushBus_data_lt_two
      (if s.longLong then Masks.Width.double else Masks.Width.long) s.flags output hflags i hi
    rcases flushed with zero | same
    · rw [parsedOutputAfterFlush, zero]
      exact cendDataWords_zero x
    · rw [parsedOutputAfterFlush, same]
      exact cendDataWords_of_datapath x _ (hout i hi)

/-- **The workhorse: any flushed integer ALU cycle word is a half-mix.**  The two
operand buses are initial buses; the request is the plain integer ALU request of
the expression's own opcode. -/
theorem cendALU_flushed_data_halfMix (x : BitVec 64) (name : ParsedAluName)
    (precision : ParsedPrecision) (unsigned : Bool) (arg : Option (Fin 256))
    (sx sy : IntegerALU.Bus) (hx : sx ∈ cendInitialBuses x)
    (hy : sy ∈ cendInitialBuses x) (reduced : Bool)
    (output : IntegerALU.BusResult)
    (evaluated : evaluateParsedIntegerAlu (.alu name (some precision) unsigned arg)
      sx sy reduced = .ok output)
    (selection : Option PEWordSelection)
    (hflags : selection = none ∨ ∃ s, selection = some s ∧
      (s.flags = 0 ∨ s.flags = BitVec.allOnes 4))
    (i : Fin 4) (hi : i.val < 2) :
    unpackALUBus (parsedOutputAfterFlush selection output.value) i ∈
      cendHalfMixWords x := by
  have mem : unpackALUBus (parsedOutputAfterFlush selection output.value) i ∈
      cendDataWords x :=
    parsedOutputAfterFlush_data_mem x selection hflags output.value
      (fun j hj => cendALU_dataWord_mem x name precision unsigned arg sx sy hx hy
        reduced output evaluated j hj) i hi
  exact cendDataWords_mem_halfMix x _ mem

/-- A resolved flush selection at the `12.convert-endian` initial mask file has a
zero or `allOnes` flag vector (or is absent). -/
theorem cendFlushSelection_zero_flags (x : BitVec 64) (flush : Option ParsedMask)
    (cycle : Fin 4) (sel : Option PEWordSelection)
    (resolved : resolveFlushSelection? flush (cendInitialPERegisters x).maskRegisters cycle =
      some sel) :
    sel = none ∨ ∃ s, sel = some s ∧
      (s.flags = 0 ∨ s.flags = BitVec.allOnes 4) := by
  apply resolveFlushSelection_zero_flags flush cycle sel
  rw [cendInitialPERegisters_maskRegisters_fun] at resolved
  exact resolved

/-! ## 2. Source provenance of the eight lowerings

Each lowering produces its reads either by `ParsedOperand.toParsedIntegerInput?`
(unmasked integer sources) or by `ParsedOperand.toIntegerMaskSourceAccess?` (the
OMR mask-source form).  The following inversions expose those equations, so the
`CendSourceOk` closure lemmas of `CendLm1Obligation` apply. -/

/-- The direct and multiple-destination lowerings read two lowered integer inputs. -/
theorem toDirectMaskedIntegerAccessesInLine?_source_eqs
    (expression : ParsedExpr) (registers : ProofsLean.MNCore.Masks.RegisterFile)
    (directive : ParsedMaskDirective) (hasSingleLineMask : Bool)
    (group : Fin 4) (l2b : Fin 2) (l1b : Fin 8) (mab : Fin 16)
    (pe cycle : Fin 4) (bar0 bar1 : BitVec 12) (tWord : BitVec 32)
    (name : ParsedAluName) (parsedPrecision : ParsedPrecision) (unsigned : Bool)
    (arg : Option (Fin 256))
    (operation : expression.op = .alu name (some parsedPrecision) unsigned arg)
    (accesses : ParsedMaskedIntegerAccesses)
    (lowered : ParsedExpr.toDirectMaskedIntegerAccessesInLine? expression registers directive
      hasSingleLineMask group l2b l1b mab pe cycle bar0 bar1 tWord = some accesses) :
    (∃ sourceX, ParsedOperand.toParsedIntegerInput? sourceX parsedPrecision.laneWidth group l2b
        l1b mab pe cycle bar0 bar1 tWord = some accesses.sourceX) ∧
      (∃ sourceY, ParsedOperand.toParsedIntegerInput? sourceY parsedPrecision.laneWidth group l2b
        l1b mab pe cycle bar0 bar1 tWord = some accesses.sourceY) := by
  obtain ⟨op, sources, destinations, flush, text⟩ := expression
  subst operation
  simp only [ParsedExpr.toDirectMaskedIntegerAccessesInLine?] at lowered
  repeat' split at lowered
  all_goals (try simp_all)
  all_goals
    (subst accesses
     exact ⟨⟨_, by assumption⟩, ⟨_, by assumption⟩⟩)

/-- The OMR mask branch reads two mask-source accesses. -/
theorem parsedIntegerMaskExprAccessesInLine?_source_eqs
    (expression : ParsedExpr) (registers : ProofsLean.MNCore.Masks.RegisterFile)
    (directive : ParsedMaskDirective) (hasSingleLineMask : Bool)
    (pe cycle : Fin 4) (bar0 bar1 : BitVec 12) (tWord : BitVec 32)
    (name : ParsedAluName) (parsedPrecision : ParsedPrecision) (unsigned : Bool)
    (arg : Option (Fin 256))
    (operation : expression.op = .alu name (some parsedPrecision) unsigned arg)
    (accesses : ParsedIntegerMaskAccesses)
    (lowered : parsedIntegerMaskExprAccessesInLine? expression registers directive
      hasSingleLineMask pe cycle bar0 bar1 tWord = some accesses) :
    (∃ sourceX, ParsedOperand.toIntegerMaskSourceAccess? sourceX pe cycle bar0 bar1 tWord =
        some (accesses.sourceX, accesses.sourceXRounded)) ∧
      (∃ sourceY, ParsedOperand.toIntegerMaskSourceAccess? sourceY pe cycle bar0 bar1 tWord =
        some (accesses.sourceY, accesses.sourceYRounded)) := by
  obtain ⟨op, sources, destinations, flush, text⟩ := expression
  subst operation
  simp only [parsedIntegerMaskExprAccessesInLine?] at lowered
  repeat' split at lowered
  all_goals (try simp_all)
  all_goals
    (subst accesses
     exact ⟨⟨_, by assumption⟩, ⟨_, by assumption⟩⟩)

/-- The mask-input branch reads two lowered integer inputs. -/
theorem parsedIntegerMaskInputExprAccessesInLine?_source_eqs
    (expression : ParsedExpr) (registers : ProofsLean.MNCore.Masks.RegisterFile)
    (directive : ParsedMaskDirective) (hasSingleLineMask : Bool)
    (group : Fin 4) (l2b : Fin 2) (l1b : Fin 8) (mab : Fin 16)
    (pe cycle : Fin 4) (bar0 bar1 : BitVec 12) (tWord : BitVec 32)
    (name : ParsedAluName) (parsedPrecision : ParsedPrecision) (unsigned : Bool)
    (arg : Option (Fin 256))
    (operation : expression.op = .alu name (some parsedPrecision) unsigned arg)
    (accesses : ParsedIntegerMaskInputAccesses)
    (lowered : parsedIntegerMaskInputExprAccessesInLine? expression registers directive
      hasSingleLineMask group l2b l1b mab pe cycle bar0 bar1 tWord = some accesses) :
    (∃ sourceX, ParsedOperand.toParsedIntegerInput? sourceX parsedPrecision.laneWidth group l2b
        l1b mab pe cycle bar0 bar1 tWord = some accesses.sourceX) ∧
      (∃ sourceY, ParsedOperand.toParsedIntegerInput? sourceY parsedPrecision.laneWidth group l2b
        l1b mab pe cycle bar0 bar1 tWord = some accesses.sourceY) := by
  obtain ⟨op, sources, destinations, flush, text⟩ := expression
  subst operation
  simp only [parsedIntegerMaskInputExprAccessesInLine?] at lowered
  repeat' split at lowered
  all_goals (try simp_all)
  all_goals
    (subst accesses
     exact ⟨⟨_, by assumption⟩, ⟨_, by assumption⟩⟩)

/-- The no-write branch reads two lowered integer inputs. -/
theorem parsedIntegerNoWriteExprAccessesInLine?_source_eqs
    (expression : ParsedExpr) (registers : ProofsLean.MNCore.Masks.RegisterFile)
    (pe cycle : Fin 4) (group : Fin 4) (l2b : Fin 2) (l1b : Fin 8)
    (mab : Fin 16) (bar0 bar1 : BitVec 12) (tWord : BitVec 32)
    (name : ParsedAluName) (parsedPrecision : ParsedPrecision) (unsigned : Bool)
    (arg : Option (Fin 256))
    (operation : expression.op = .alu name (some parsedPrecision) unsigned arg)
    (accesses : ParsedIntegerNoWriteAccesses)
    (lowered : parsedIntegerNoWriteExprAccessesInLine? expression registers pe cycle group l2b
      l1b mab bar0 bar1 tWord = some accesses) :
    (∃ sourceX, ParsedOperand.toParsedIntegerInput? sourceX parsedPrecision.laneWidth group l2b
        l1b mab pe cycle bar0 bar1 tWord = some accesses.sourceX) ∧
      (∃ sourceY, ParsedOperand.toParsedIntegerInput? sourceY parsedPrecision.laneWidth group l2b
        l1b mab pe cycle bar0 bar1 tWord = some accesses.sourceY) := by
  obtain ⟨op, sources, destinations, flush, text⟩ := expression
  subst operation
  simp only [parsedIntegerNoWriteExprAccessesInLine?] at lowered
  repeat' split at lowered
  all_goals (try simp_all)
  all_goals
    (subst accesses
     exact ⟨⟨_, by assumption⟩, ⟨_, by assumption⟩⟩)

/-- The BAR branch reads two lowered integer inputs. -/
theorem parsedIntegerBarExprAccessesInLine?_source_eqs
    (expression : ParsedExpr) (registers : ProofsLean.MNCore.Masks.RegisterFile)
    (directive : ParsedMaskDirective) (hasSingleLineMask : Bool)
    (group : Fin 4) (l2b : Fin 2) (l1b : Fin 8) (mab : Fin 16)
    (pe cycle : Fin 4) (bar0 bar1 : BitVec 12) (tWord : BitVec 32)
    (name : ParsedAluName) (parsedPrecision : ParsedPrecision) (unsigned : Bool)
    (arg : Option (Fin 256))
    (operation : expression.op = .alu name (some parsedPrecision) unsigned arg)
    (accesses : ParsedIntegerBarAccesses)
    (lowered : parsedIntegerBarExprAccessesInLine? expression registers directive
      hasSingleLineMask group l2b l1b mab pe cycle bar0 bar1 tWord = some accesses) :
    (∃ sourceX, ParsedOperand.toParsedIntegerInput? sourceX parsedPrecision.laneWidth group l2b
        l1b mab pe cycle bar0 bar1 tWord = some accesses.sourceX) ∧
      (∃ sourceY, ParsedOperand.toParsedIntegerInput? sourceY parsedPrecision.laneWidth group l2b
        l1b mab pe cycle bar0 bar1 tWord = some accesses.sourceY) := by
  obtain ⟨op, sources, destinations, flush, text⟩ := expression
  subst operation
  simp only [parsedIntegerBarExprAccessesInLine?] at lowered
  repeat' split at lowered
  all_goals (try simp_all)
  all_goals
    (subst accesses
     exact ⟨⟨_, by assumption⟩, ⟨_, by assumption⟩⟩)

/-- The memory-then-OMR branch reads two lowered integer inputs. -/
theorem parsedIntegerMaskMemoryThenInputExprAccessesInLine?_source_eqs
    (expression : ParsedExpr) (registers : ProofsLean.MNCore.Masks.RegisterFile)
    (directive : ParsedMaskDirective) (hasSingleLineMask : Bool)
    (group : Fin 4) (l2b : Fin 2) (l1b : Fin 8) (mab : Fin 16)
    (pe cycle : Fin 4) (bar0 bar1 : BitVec 12) (tWord : BitVec 32)
    (name : ParsedAluName) (parsedPrecision : ParsedPrecision) (unsigned : Bool)
    (arg : Option (Fin 256))
    (operation : expression.op = .alu name (some parsedPrecision) unsigned arg)
    (accesses : ParsedIntegerMaskMemoryThenInputAccesses)
    (lowered : parsedIntegerMaskMemoryThenInputExprAccessesInLine? expression registers
      directive hasSingleLineMask group l2b l1b mab pe cycle bar0 bar1 tWord = some accesses) :
    (∃ sourceX, ParsedOperand.toParsedIntegerInput? sourceX parsedPrecision.laneWidth group l2b
        l1b mab pe cycle bar0 bar1 tWord = some accesses.sourceX) ∧
      (∃ sourceY, ParsedOperand.toParsedIntegerInput? sourceY parsedPrecision.laneWidth group l2b
        l1b mab pe cycle bar0 bar1 tWord = some accesses.sourceY) := by
  obtain ⟨op, sources, destinations, flush, text⟩ := expression
  subst operation
  simp only [parsedIntegerMaskMemoryThenInputExprAccessesInLine?] at lowered
  repeat' split at lowered
  all_goals (try simp_all)
  all_goals
    (subst accesses
     exact ⟨⟨_, by assumption⟩, ⟨_, by assumption⟩⟩)

/-- The OMR-then-memory branch reads two lowered integer inputs. -/
theorem parsedIntegerMaskInputThenMemoryExprAccessesInLine?_source_eqs
    (expression : ParsedExpr) (registers : ProofsLean.MNCore.Masks.RegisterFile)
    (directive : ParsedMaskDirective) (hasSingleLineMask : Bool)
    (group : Fin 4) (l2b : Fin 2) (l1b : Fin 8) (mab : Fin 16)
    (pe cycle : Fin 4) (bar0 bar1 : BitVec 12) (tWord : BitVec 32)
    (name : ParsedAluName) (parsedPrecision : ParsedPrecision) (unsigned : Bool)
    (arg : Option (Fin 256))
    (operation : expression.op = .alu name (some parsedPrecision) unsigned arg)
    (accesses : ParsedIntegerMaskInputThenMemoryAccesses)
    (lowered : parsedIntegerMaskInputThenMemoryExprAccessesInLine? expression registers
      directive hasSingleLineMask group l2b l1b mab pe cycle bar0 bar1 tWord = some accesses) :
    (∃ sourceX, ParsedOperand.toParsedIntegerInput? sourceX parsedPrecision.laneWidth group l2b
        l1b mab pe cycle bar0 bar1 tWord = some accesses.sourceX) ∧
      (∃ sourceY, ParsedOperand.toParsedIntegerInput? sourceY parsedPrecision.laneWidth group l2b
        l1b mab pe cycle bar0 bar1 tWord = some accesses.sourceY) := by
  obtain ⟨op, sources, destinations, flush, text⟩ := expression
  subst operation
  simp only [parsedIntegerMaskInputThenMemoryExprAccessesInLine?] at lowered
  repeat' split at lowered
  all_goals (try simp_all)
  all_goals
    (subst accesses
     exact ⟨⟨_, by assumption⟩, ⟨_, by assumption⟩⟩)

/-! ### Operation and flush-selection provenance

Every lowering stores the row's own operation and the flush selection resolved
from the row's flush operand.  Together with the source provenance above this
lets each §4 data equation be read at the row's own `.alu` operation and with a
zero/`allOnes` flush. -/

theorem toDirectMaskedIntegerAccessesInLine?_op_provenance
    (expression : ParsedExpr) (registers : ProofsLean.MNCore.Masks.RegisterFile)
    (directive : ParsedMaskDirective) (hasSingleLineMask : Bool)
    (group : Fin 4) (l2b : Fin 2) (l1b : Fin 8) (mab : Fin 16)
    (pe cycle : Fin 4) (bar0 bar1 : BitVec 12) (tWord : BitVec 32)
    (name : ParsedAluName) (parsedPrecision : ParsedPrecision) (unsigned : Bool)
    (arg : Option (Fin 256))
    (operation : expression.op = .alu name (some parsedPrecision) unsigned arg)
    (accesses : ParsedMaskedIntegerAccesses)
    (lowered : ParsedExpr.toDirectMaskedIntegerAccessesInLine? expression registers directive
      hasSingleLineMask group l2b l1b mab pe cycle bar0 bar1 tWord = some accesses) :
    accesses.op = expression.op := by
  obtain ⟨op, sources, destinations, flush, text⟩ := expression
  subst operation
  simp only [ParsedExpr.toDirectMaskedIntegerAccessesInLine?] at lowered
  repeat' split at lowered
  all_goals (try simp_all)
  all_goals (subst accesses; rfl)

theorem toDirectMaskedIntegerAccessesInLine?_flushSelection
    (expression : ParsedExpr) (registers : ProofsLean.MNCore.Masks.RegisterFile)
    (directive : ParsedMaskDirective) (hasSingleLineMask : Bool)
    (group : Fin 4) (l2b : Fin 2) (l1b : Fin 8) (mab : Fin 16)
    (pe cycle : Fin 4) (bar0 bar1 : BitVec 12) (tWord : BitVec 32)
    (name : ParsedAluName) (parsedPrecision : ParsedPrecision) (unsigned : Bool)
    (arg : Option (Fin 256))
    (operation : expression.op = .alu name (some parsedPrecision) unsigned arg)
    (accesses : ParsedMaskedIntegerAccesses)
    (lowered : ParsedExpr.toDirectMaskedIntegerAccessesInLine? expression registers directive
      hasSingleLineMask group l2b l1b mab pe cycle bar0 bar1 tWord = some accesses) :
    ∃ sel : Option PEWordSelection,
      resolveFlushSelection? expression.flush registers cycle = some sel ∧
        accesses.flushSelection = sel := by
  obtain ⟨op, sources, destinations, flush, text⟩ := expression
  subst operation
  simp only [ParsedExpr.toDirectMaskedIntegerAccessesInLine?] at lowered
  repeat' split at lowered
  all_goals (try simp_all)
  all_goals (subst accesses; rfl)

theorem toDirectMaskedIntegerWritesInLine?_mapM_general
    (expression : ParsedExpr) (registers : ProofsLean.MNCore.Masks.RegisterFile)
    (directive : ParsedMaskDirective) (hasSingleLineMask : Bool)
    (group : Fin 4) (l2b : Fin 2) (l1b : Fin 8) (mab : Fin 16)
    (pe cycle : Fin 4) (bar0 bar1 : BitVec 12) (tWord : BitVec 32)
    (name : ParsedAluName) (parsedPrecision : ParsedPrecision) (unsigned : Bool)
    (arg : Option (Fin 256))
    (operation : expression.op = .alu name (some parsedPrecision) unsigned arg)
    (accesses : List ParsedMaskedIntegerAccesses)
    (lowered : ParsedExpr.toDirectMaskedIntegerWritesInLine? expression registers directive
      hasSingleLineMask group l2b l1b mab pe cycle bar0 bar1 tWord = some accesses) :
    expression.destinations.mapM (fun destination =>
      ParsedExpr.toDirectMaskedIntegerAccessesInLine?
        { expression with destinations := [destination] } registers directive hasSingleLineMask
        group l2b l1b mab pe cycle bar0 bar1 tWord) = some accesses := by
  obtain ⟨op, sources, destinations, flush, text⟩ := expression
  subst operation
  unfold ParsedExpr.toDirectMaskedIntegerWritesInLine? at lowered
  dsimp only at lowered
  cases destinations with
  | nil => simp at lowered
  | cons destination rest => exact lowered

theorem parsedIntegerMaskExprAccessesInLine?_op_provenance
    (expression : ParsedExpr) (registers : ProofsLean.MNCore.Masks.RegisterFile)
    (directive : ParsedMaskDirective) (hasSingleLineMask : Bool)
    (pe cycle : Fin 4) (bar0 bar1 : BitVec 12) (tWord : BitVec 32)
    (name : ParsedAluName) (parsedPrecision : ParsedPrecision) (unsigned : Bool)
    (arg : Option (Fin 256))
    (operation : expression.op = .alu name (some parsedPrecision) unsigned arg)
    (accesses : ParsedIntegerMaskAccesses)
    (lowered : parsedIntegerMaskExprAccessesInLine? expression registers directive
      hasSingleLineMask pe cycle bar0 bar1 tWord = some accesses) :
    accesses.op = expression.op := by
  obtain ⟨op, sources, destinations, flush, text⟩ := expression
  subst operation
  simp only [parsedIntegerMaskExprAccessesInLine?] at lowered
  repeat' split at lowered
  all_goals (try simp_all)
  all_goals (subst accesses; rfl)

theorem parsedIntegerMaskInputExprAccessesInLine?_op_provenance
    (expression : ParsedExpr) (registers : ProofsLean.MNCore.Masks.RegisterFile)
    (directive : ParsedMaskDirective) (hasSingleLineMask : Bool)
    (group : Fin 4) (l2b : Fin 2) (l1b : Fin 8) (mab : Fin 16)
    (pe cycle : Fin 4) (bar0 bar1 : BitVec 12) (tWord : BitVec 32)
    (name : ParsedAluName) (parsedPrecision : ParsedPrecision) (unsigned : Bool)
    (arg : Option (Fin 256))
    (operation : expression.op = .alu name (some parsedPrecision) unsigned arg)
    (accesses : ParsedIntegerMaskInputAccesses)
    (lowered : parsedIntegerMaskInputExprAccessesInLine? expression registers directive
      hasSingleLineMask group l2b l1b mab pe cycle bar0 bar1 tWord = some accesses) :
    accesses.op = expression.op := by
  obtain ⟨op, sources, destinations, flush, text⟩ := expression
  subst operation
  simp only [parsedIntegerMaskInputExprAccessesInLine?] at lowered
  repeat' split at lowered
  all_goals (try simp_all)
  all_goals (subst accesses; rfl)

theorem parsedIntegerNoWriteExprAccessesInLine?_op_provenance
    (expression : ParsedExpr) (registers : ProofsLean.MNCore.Masks.RegisterFile)
    (pe cycle : Fin 4) (group : Fin 4) (l2b : Fin 2) (l1b : Fin 8)
    (mab : Fin 16) (bar0 bar1 : BitVec 12) (tWord : BitVec 32)
    (name : ParsedAluName) (parsedPrecision : ParsedPrecision) (unsigned : Bool)
    (arg : Option (Fin 256))
    (operation : expression.op = .alu name (some parsedPrecision) unsigned arg)
    (accesses : ParsedIntegerNoWriteAccesses)
    (lowered : parsedIntegerNoWriteExprAccessesInLine? expression registers pe cycle group l2b
      l1b mab bar0 bar1 tWord = some accesses) :
    accesses.op = expression.op := by
  obtain ⟨op, sources, destinations, flush, text⟩ := expression
  subst operation
  simp only [parsedIntegerNoWriteExprAccessesInLine?] at lowered
  repeat' split at lowered
  all_goals (try simp_all)
  all_goals (subst accesses; rfl)

theorem parsedIntegerBarExprAccessesInLine?_op_provenance
    (expression : ParsedExpr) (registers : ProofsLean.MNCore.Masks.RegisterFile)
    (directive : ParsedMaskDirective) (hasSingleLineMask : Bool)
    (group : Fin 4) (l2b : Fin 2) (l1b : Fin 8) (mab : Fin 16)
    (pe cycle : Fin 4) (bar0 bar1 : BitVec 12) (tWord : BitVec 32)
    (name : ParsedAluName) (parsedPrecision : ParsedPrecision) (unsigned : Bool)
    (arg : Option (Fin 256))
    (operation : expression.op = .alu name (some parsedPrecision) unsigned arg)
    (accesses : ParsedIntegerBarAccesses)
    (lowered : parsedIntegerBarExprAccessesInLine? expression registers directive
      hasSingleLineMask group l2b l1b mab pe cycle bar0 bar1 tWord = some accesses) :
    accesses.op = expression.op := by
  obtain ⟨op, sources, destinations, flush, text⟩ := expression
  subst operation
  simp only [parsedIntegerBarExprAccessesInLine?] at lowered
  repeat' split at lowered
  all_goals (try simp_all)
  all_goals (subst accesses; rfl)

theorem parsedIntegerMaskMemoryThenInputExprAccessesInLine?_op_provenance
    (expression : ParsedExpr) (registers : ProofsLean.MNCore.Masks.RegisterFile)
    (directive : ParsedMaskDirective) (hasSingleLineMask : Bool)
    (group : Fin 4) (l2b : Fin 2) (l1b : Fin 8) (mab : Fin 16)
    (pe cycle : Fin 4) (bar0 bar1 : BitVec 12) (tWord : BitVec 32)
    (name : ParsedAluName) (parsedPrecision : ParsedPrecision) (unsigned : Bool)
    (arg : Option (Fin 256))
    (operation : expression.op = .alu name (some parsedPrecision) unsigned arg)
    (accesses : ParsedIntegerMaskMemoryThenInputAccesses)
    (lowered : parsedIntegerMaskMemoryThenInputExprAccessesInLine? expression registers
      directive hasSingleLineMask group l2b l1b mab pe cycle bar0 bar1 tWord = some accesses) :
    accesses.op = expression.op := by
  obtain ⟨op, sources, destinations, flush, text⟩ := expression
  subst operation
  simp only [parsedIntegerMaskMemoryThenInputExprAccessesInLine?] at lowered
  repeat' split at lowered
  all_goals (try simp_all)
  all_goals (subst accesses; rfl)

theorem parsedIntegerMaskInputThenMemoryExprAccessesInLine?_op_provenance
    (expression : ParsedExpr) (registers : ProofsLean.MNCore.Masks.RegisterFile)
    (directive : ParsedMaskDirective) (hasSingleLineMask : Bool)
    (group : Fin 4) (l2b : Fin 2) (l1b : Fin 8) (mab : Fin 16)
    (pe cycle : Fin 4) (bar0 bar1 : BitVec 12) (tWord : BitVec 32)
    (name : ParsedAluName) (parsedPrecision : ParsedPrecision) (unsigned : Bool)
    (arg : Option (Fin 256))
    (operation : expression.op = .alu name (some parsedPrecision) unsigned arg)
    (accesses : ParsedIntegerMaskInputThenMemoryAccesses)
    (lowered : parsedIntegerMaskInputThenMemoryExprAccessesInLine? expression registers
      directive hasSingleLineMask group l2b l1b mab pe cycle bar0 bar1 tWord = some accesses) :
    accesses.op = expression.op := by
  obtain ⟨op, sources, destinations, flush, text⟩ := expression
  subst operation
  simp only [parsedIntegerMaskInputThenMemoryExprAccessesInLine?] at lowered
  repeat' split at lowered
  all_goals (try simp_all)
  all_goals (subst accesses; rfl)

/-! ### Per-branch data lemmas -/

/-- The direct-access branch: the single prepared write's first two data words are
half-mixes. -/
theorem cendDirectPreparedWrite_data_halfMix
    (x : BitVec 64) (name : ParsedAluName) (precision : ParsedPrecision) (unsigned : Bool)
    (arg : Option (Fin 256)) (cycle : Fin 4)
    (expression : ParsedExpr) (control : ParsedMaskExecutionControl)
    (hsm nf reduced : Bool) (accesses : ParsedMaskedIntegerAccesses)
    (write : PreparedParsedMaskedWrite)
    (operation : expression.op = .alu name (some precision) unsigned arg)
    (hcontext : control.context = ParsedIntegerContext.ofLinearIndex cendPE)
    (lowered : ParsedExpr.toDirectMaskedIntegerAccessesInLine? expression
      (cendInitialPERegisters x).maskRegisters control.directive hsm control.context.group
      control.context.l2b control.context.l1b control.context.mab control.context.pe cycle
      control.context.bar0 control.context.bar1 control.context.tWord = some accesses)
    (prepared : prepareParsedMaskedWriteWithForwarding (cendInitialPERegisters x)
      cendPoisonSlots cycle accesses reduced = .ok write) :
    ∀ i : Fin 4, i.val < 2 → write.data i ∈ cendHalfMixWords x := by
  intro i hi
  obtain ⟨sx, sy, output, readX, readY, evaluated, dataEq⟩ :=
    prepareParsedMaskedWriteWithForwarding_data_eq (cendInitialPERegisters x) cendPoisonSlots
      cycle accesses reduced write prepared
  have sources := toDirectMaskedIntegerAccessesInLine?_source_eqs expression
    (cendInitialPERegisters x).maskRegisters control.directive hsm control.context.group
    control.context.l2b control.context.l1b control.context.mab control.context.pe cycle
    control.context.bar0 control.context.bar1 control.context.tWord name precision unsigned
    arg operation accesses lowered
  obtain ⟨sourceX, sourceXEq⟩ := sources.1
  obtain ⟨sourceY, sourceYEq⟩ := sources.2
  have sourceXEq' : ParsedOperand.toParsedIntegerInput? sourceX precision.laneWidth
      (ParsedIntegerContext.ofLinearIndex cendPE).group
      (ParsedIntegerContext.ofLinearIndex cendPE).l2b
      (ParsedIntegerContext.ofLinearIndex cendPE).l1b
      (ParsedIntegerContext.ofLinearIndex cendPE).mab
      (ParsedIntegerContext.ofLinearIndex cendPE).pe cycle
      control.context.bar0 control.context.bar1 control.context.tWord =
        some accesses.sourceX := by
    rw [← hcontext]
    exact sourceXEq
  have sourceYEq' : ParsedOperand.toParsedIntegerInput? sourceY precision.laneWidth
      (ParsedIntegerContext.ofLinearIndex cendPE).group
      (ParsedIntegerContext.ofLinearIndex cendPE).l2b
      (ParsedIntegerContext.ofLinearIndex cendPE).l1b
      (ParsedIntegerContext.ofLinearIndex cendPE).mab
      (ParsedIntegerContext.ofLinearIndex cendPE).pe cycle
      control.context.bar0 control.context.bar1 control.context.tWord =
        some accesses.sourceY := by
    rw [← hcontext]
    exact sourceYEq
  have sourceXOk : CendSourceOk x cycle accesses.sourceX :=
    cendSourceOk_toParsedIntegerInput x sourceX precision.laneWidth cycle
      control.context.bar0 control.context.bar1 control.context.tWord accesses.sourceX sourceXEq'
  have sourceYOk : CendSourceOk x cycle accesses.sourceY :=
    cendSourceOk_toParsedIntegerInput x sourceY precision.laneWidth cycle
      control.context.bar0 control.context.bar1 control.context.tWord accesses.sourceY sourceYEq'
  have hx : sx ∈ cendInitialBuses x := sourceXOk sx readX
  have hy : sy ∈ cendInitialBuses x := sourceYOk sy readY
  have opEq := toDirectMaskedIntegerAccessesInLine?_op_provenance expression
    (cendInitialPERegisters x).maskRegisters control.directive hsm control.context.group
    control.context.l2b control.context.l1b control.context.mab control.context.pe cycle
    control.context.bar0 control.context.bar1 control.context.tWord name precision unsigned
    arg operation accesses lowered
  have evaluated' : evaluateParsedIntegerAlu (.alu name (some precision) unsigned arg)
      sx sy reduced = .ok output := by
    rwa [opEq, operation] at evaluated
  obtain ⟨sel, hsel, hselEq⟩ := toDirectMaskedIntegerAccessesInLine?_flushSelection expression
    (cendInitialPERegisters x).maskRegisters control.directive hsm control.context.group
    control.context.l2b control.context.l1b control.context.mab control.context.pe cycle
    control.context.bar0 control.context.bar1 control.context.tWord name precision unsigned
    arg operation accesses lowered
  have flags : sel = none ∨ ∃ s, sel = some s ∧
      (s.flags = 0 ∨ s.flags = BitVec.allOnes 4) :=
    cendFlushSelection_zero_flags x expression.flush (cycle := cycle) (sel := sel) hsel
  rw [dataEq, hselEq]
  exact cendALU_flushed_data_halfMix x name precision unsigned arg sx sy hx hy reduced
    output evaluated' sel flags i hi

/-- The multiple-destination branch: the head write and every replicated copy
carry the same data. -/
theorem cendMultiplePreparedWrites_data_halfMix
    (x : BitVec 64) (name : ParsedAluName) (precision : ParsedPrecision) (unsigned : Bool)
    (arg : Option (Fin 256)) (cycle : Fin 4)
    (expression : ParsedExpr) (control : ParsedMaskExecutionControl)
    (hsm nf reduced : Bool)
    (access : ParsedMaskedIntegerAccesses) (rest : List ParsedMaskedIntegerAccesses)
    (write : PreparedParsedMaskedWrite)
    (operation : expression.op = .alu name (some precision) unsigned arg)
    (hcontext : control.context = ParsedIntegerContext.ofLinearIndex cendPE)
    (lowered : ParsedExpr.toDirectMaskedIntegerWritesInLine? expression
      (cendInitialPERegisters x).maskRegisters control.directive hsm control.context.group
      control.context.l2b control.context.l1b control.context.mab control.context.pe cycle
      control.context.bar0 control.context.bar1 control.context.tWord = some (access :: rest))
    (prepared : prepareParsedMaskedWriteWithForwarding (cendInitialPERegisters x)
      cendPoisonSlots cycle access reduced = .ok write) :
    ∀ item ∈ write :: replicatePreparedIntegerResult rest write,
      ∀ i : Fin 4, i.val < 2 → item.data i ∈ cendHalfMixWords x := by
  have head : ∀ i : Fin 4, i.val < 2 → write.data i ∈ cendHalfMixWords x := by
    intro i hi
    have mapped := toDirectMaskedIntegerWritesInLine?_mapM_general expression
      (cendInitialPERegisters x).maskRegisters control.directive hsm control.context.group
      control.context.l2b control.context.l1b control.context.mab control.context.pe cycle
      control.context.bar0 control.context.bar1 control.context.tWord name precision unsigned
      arg operation (access :: rest) lowered
    cases hdest : expression.destinations with
    | nil => rw [hdest] at mapped; simp at mapped
    | cons destination restDestinations =>
        rw [hdest] at mapped
        obtain ⟨-, getEq⟩ := list_mapM_getElem (fun destination =>
          ParsedExpr.toDirectMaskedIntegerAccessesInLine?
            { expression with destinations := [destination] }
            (cendInitialPERegisters x).maskRegisters control.directive hsm
            control.context.group control.context.l2b control.context.l1b control.context.mab
            control.context.pe cycle control.context.bar0 control.context.bar1
            control.context.tWord) (destination :: restDestinations) (access :: rest) mapped
        have hd : ParsedExpr.toDirectMaskedIntegerAccessesInLine?
            { expression with destinations := [destination] }
            (cendInitialPERegisters x).maskRegisters control.directive hsm
            control.context.group control.context.l2b control.context.l1b control.context.mab
            control.context.pe cycle control.context.bar0 control.context.bar1
            control.context.tWord = some access := by
          have := getEq 0 (by simp) (by simp)
          simpa using this
        have operation' : ({ expression with destinations := [destination] } : ParsedExpr).op =
            .alu name (some precision) unsigned arg := by
          simpa using operation
        exact cendDirectPreparedWrite_data_halfMix x name precision unsigned arg cycle
          { expression with destinations := [destination] } control hsm nf reduced access
          write operation' hcontext hd prepared i hi
  intro item member i hi
  rcases List.mem_cons.mp member with rfl | later
  · exact head i hi
  · rw [replicatePreparedIntegerResult_preserves_data rest write item later]
    exact head i hi

theorem parsedIntegerNoWriteExprAccessesInLine?_flushSelection
    (expression : ParsedExpr) (registers : ProofsLean.MNCore.Masks.RegisterFile)
    (pe cycle : Fin 4) (group : Fin 4) (l2b : Fin 2) (l1b : Fin 8)
    (mab : Fin 16) (bar0 bar1 : BitVec 12) (tWord : BitVec 32)
    (name : ParsedAluName) (parsedPrecision : ParsedPrecision) (unsigned : Bool)
    (arg : Option (Fin 256))
    (operation : expression.op = .alu name (some parsedPrecision) unsigned arg)
    (accesses : ParsedIntegerNoWriteAccesses)
    (lowered : parsedIntegerNoWriteExprAccessesInLine? expression registers pe cycle group l2b
      l1b mab bar0 bar1 tWord = some accesses) :
    ∃ sel : Option PEWordSelection,
      resolveFlushSelection? expression.flush registers cycle = some sel ∧
        accesses.flushSelection = sel := by
  obtain ⟨op, sources, destinations, flush, text⟩ := expression
  subst operation
  simp only [parsedIntegerNoWriteExprAccessesInLine?] at lowered
  repeat' split at lowered
  all_goals (try simp_all)
  all_goals (subst accesses; rfl)

theorem parsedIntegerBarExprAccessesInLine?_flushSelection
    (expression : ParsedExpr) (registers : ProofsLean.MNCore.Masks.RegisterFile)
    (directive : ParsedMaskDirective) (hasSingleLineMask : Bool)
    (group : Fin 4) (l2b : Fin 2) (l1b : Fin 8) (mab : Fin 16)
    (pe cycle : Fin 4) (bar0 bar1 : BitVec 12) (tWord : BitVec 32)
    (name : ParsedAluName) (parsedPrecision : ParsedPrecision) (unsigned : Bool)
    (arg : Option (Fin 256))
    (operation : expression.op = .alu name (some parsedPrecision) unsigned arg)
    (accesses : ParsedIntegerBarAccesses)
    (lowered : parsedIntegerBarExprAccessesInLine? expression registers directive
      hasSingleLineMask group l2b l1b mab pe cycle bar0 bar1 tWord = some accesses) :
    ∃ sel : Option PEWordSelection,
      resolveFlushSelection? expression.flush registers cycle = some sel ∧
        accesses.flushSelection = sel := by
  obtain ⟨op, sources, destinations, flush, text⟩ := expression
  subst operation
  simp only [parsedIntegerBarExprAccessesInLine?] at lowered
  repeat' split at lowered
  all_goals (try simp_all)
  all_goals (subst accesses; rfl)

/-- The OMR-mask branch: the single prepared write's first two data words are
half-mixes. -/
theorem cendOmrPreparedWrite_data_halfMix
    (x : BitVec 64) (name : ParsedAluName) (precision : ParsedPrecision) (unsigned : Bool)
    (arg : Option (Fin 256)) (cycle : Fin 4)
    (expression : ParsedExpr) (control : ParsedMaskExecutionControl)
    (hsm nf reduced : Bool) (accesses : ParsedIntegerMaskAccesses)
    (flushSelection : Option PEWordSelection) (write : PreparedParsedMaskedWrite)
    (operation : expression.op = .alu name (some precision) unsigned arg)
    (lowered : parsedIntegerMaskExprAccessesInLine? expression
      (cendInitialPERegisters x).maskRegisters control.directive hsm control.context.pe cycle
      control.context.bar0 control.context.bar1 control.context.tWord = some accesses)
    (hflush : resolveFlushSelection? expression.flush
      (cendInitialPERegisters x).maskRegisters cycle = some flushSelection)
    (prepared : prepareParsedIntegerMaskALUWriteWithForwarding (cendInitialPERegisters x)
      cendPoisonSlots cycle accesses flushSelection reduced = .ok write) :
    ∀ i : Fin 4, i.val < 2 → write.data i ∈ cendHalfMixWords x := by
  intro i hi
  obtain ⟨sx, sy, output, readX, readY, evaluated, dataEq⟩ :=
    prepareParsedIntegerMaskALUWriteWithForwarding_data (cendInitialPERegisters x)
      cendPoisonSlots cycle accesses flushSelection reduced write prepared
  obtain ⟨sourceX, sourceXEq⟩ := (parsedIntegerMaskExprAccessesInLine?_source_eqs expression
    (cendInitialPERegisters x).maskRegisters control.directive hsm control.context.pe cycle
    control.context.bar0 control.context.bar1 control.context.tWord name precision unsigned arg
    operation accesses lowered).1
  obtain ⟨sourceY, sourceYEq⟩ := (parsedIntegerMaskExprAccessesInLine?_source_eqs expression
    (cendInitialPERegisters x).maskRegisters control.directive hsm control.context.pe cycle
    control.context.bar0 control.context.bar1 control.context.tWord name precision unsigned arg
    operation accesses lowered).2
  have sourceXOk : CendSourceOk x cycle (.memory accesses.sourceX accesses.sourceXRounded) :=
    cendSourceOk_toIntegerMaskSourceAccess x sourceX control.context.pe cycle
      control.context.bar0 control.context.bar1 control.context.tWord accesses.sourceX
      accesses.sourceXRounded sourceXEq
  have sourceYOk : CendSourceOk x cycle (.memory accesses.sourceY accesses.sourceYRounded) :=
    cendSourceOk_toIntegerMaskSourceAccess x sourceY control.context.pe cycle
      control.context.bar0 control.context.bar1 control.context.tWord accesses.sourceY
      accesses.sourceYRounded sourceYEq
  have hx : sx ∈ cendInitialBuses x := sourceXOk sx readX
  have hy : sy ∈ cendInitialBuses x := sourceYOk sy readY
  have opEq := parsedIntegerMaskExprAccessesInLine?_op_provenance expression
    (cendInitialPERegisters x).maskRegisters control.directive hsm control.context.pe cycle
    control.context.bar0 control.context.bar1 control.context.tWord name precision unsigned arg
    operation accesses lowered
  have evaluated' : evaluateParsedIntegerAlu (.alu name (some precision) unsigned arg)
      sx sy reduced = .ok output := by
    rwa [opEq, operation] at evaluated
  have flags : flushSelection = none ∨ ∃ s, flushSelection = some s ∧
      (s.flags = 0 ∨ s.flags = BitVec.allOnes 4) :=
    cendFlushSelection_zero_flags x expression.flush (cycle := cycle) (sel := flushSelection) hflush
  rw [dataEq]
  exact cendALU_flushed_data_halfMix x name precision unsigned arg sx sy hx hy reduced
    output evaluated' flushSelection flags i hi

/-- The no-write branch: the single prepared write's first two data words are
half-mixes. -/
theorem cendNoWritePreparedWrite_data_halfMix
    (x : BitVec 64) (name : ParsedAluName) (precision : ParsedPrecision) (unsigned : Bool)
    (arg : Option (Fin 256)) (cycle : Fin 4)
    (expression : ParsedExpr) (control : ParsedMaskExecutionControl)
    (hsm nf reduced : Bool) (accesses : ParsedIntegerNoWriteAccesses)
    (write : PreparedParsedMaskedWrite)
    (operation : expression.op = .alu name (some precision) unsigned arg)
    (hcontext : control.context = ParsedIntegerContext.ofLinearIndex cendPE)
    (lowered : parsedIntegerNoWriteExprAccessesInLine? expression
      (cendInitialPERegisters x).maskRegisters control.context.pe cycle control.context.group
      control.context.l2b control.context.l1b control.context.mab control.context.bar0
      control.context.bar1 control.context.tWord = some accesses)
    (prepared : prepareParsedIntegerNoWriteALUWithForwarding (cendInitialPERegisters x)
      cendPoisonSlots cycle accesses reduced = .ok write) :
    ∀ i : Fin 4, i.val < 2 → write.data i ∈ cendHalfMixWords x := by
  intro i hi
  obtain ⟨sx, sy, output, readX, readY, evaluated, dataEq⟩ :=
    prepareParsedIntegerNoWriteALUWithForwarding_data (cendInitialPERegisters x)
      cendPoisonSlots cycle accesses reduced write prepared
  have sources := parsedIntegerNoWriteExprAccessesInLine?_source_eqs expression
    (cendInitialPERegisters x).maskRegisters control.context.pe cycle control.context.group
    control.context.l2b control.context.l1b control.context.mab control.context.bar0
    control.context.bar1 control.context.tWord name precision unsigned arg operation accesses
    lowered
  obtain ⟨sourceX, sourceXEq⟩ := sources.1
  obtain ⟨sourceY, sourceYEq⟩ := sources.2
  have sourceXEq' : ParsedOperand.toParsedIntegerInput? sourceX precision.laneWidth
      (ParsedIntegerContext.ofLinearIndex cendPE).group
      (ParsedIntegerContext.ofLinearIndex cendPE).l2b
      (ParsedIntegerContext.ofLinearIndex cendPE).l1b
      (ParsedIntegerContext.ofLinearIndex cendPE).mab
      (ParsedIntegerContext.ofLinearIndex cendPE).pe cycle control.context.bar0
      control.context.bar1 control.context.tWord = some accesses.sourceX := by
    rw [← hcontext]
    exact sourceXEq
  have sourceYEq' : ParsedOperand.toParsedIntegerInput? sourceY precision.laneWidth
      (ParsedIntegerContext.ofLinearIndex cendPE).group
      (ParsedIntegerContext.ofLinearIndex cendPE).l2b
      (ParsedIntegerContext.ofLinearIndex cendPE).l1b
      (ParsedIntegerContext.ofLinearIndex cendPE).mab
      (ParsedIntegerContext.ofLinearIndex cendPE).pe cycle control.context.bar0
      control.context.bar1 control.context.tWord = some accesses.sourceY := by
    rw [← hcontext]
    exact sourceYEq
  have sourceXOk : CendSourceOk x cycle accesses.sourceX :=
    cendSourceOk_toParsedIntegerInput x sourceX precision.laneWidth cycle
      control.context.bar0 control.context.bar1 control.context.tWord accesses.sourceX sourceXEq'
  have sourceYOk : CendSourceOk x cycle accesses.sourceY :=
    cendSourceOk_toParsedIntegerInput x sourceY precision.laneWidth cycle
      control.context.bar0 control.context.bar1 control.context.tWord accesses.sourceY sourceYEq'
  have hx : sx ∈ cendInitialBuses x := sourceXOk sx readX
  have hy : sy ∈ cendInitialBuses x := sourceYOk sy readY
  have opEq := parsedIntegerNoWriteExprAccessesInLine?_op_provenance expression
    (cendInitialPERegisters x).maskRegisters control.context.pe cycle control.context.group
    control.context.l2b control.context.l1b control.context.mab control.context.bar0
    control.context.bar1 control.context.tWord name precision unsigned arg operation accesses
    lowered
  have evaluated' : evaluateParsedIntegerAlu (.alu name (some precision) unsigned arg)
      sx sy reduced = .ok output := by
    rwa [opEq, operation] at evaluated
  obtain ⟨sel, hsel, hselEq⟩ := parsedIntegerNoWriteExprAccessesInLine?_flushSelection expression
    (cendInitialPERegisters x).maskRegisters control.context.pe cycle control.context.group
    control.context.l2b control.context.l1b control.context.mab control.context.bar0
    control.context.bar1 control.context.tWord name precision unsigned arg operation accesses
    lowered
  have flags : sel = none ∨ ∃ s, sel = some s ∧
      (s.flags = 0 ∨ s.flags = BitVec.allOnes 4) :=
    cendFlushSelection_zero_flags x expression.flush (cycle := cycle) (sel := sel) hsel
  rw [dataEq, hselEq]
  exact cendALU_flushed_data_halfMix x name precision unsigned arg sx sy hx hy reduced
    output evaluated' sel flags i hi

/-- The BAR branch: the single prepared write's first two data words are
half-mixes. -/
theorem cendBarPreparedWrite_data_halfMix
    (x : BitVec 64) (name : ParsedAluName) (precision : ParsedPrecision) (unsigned : Bool)
    (arg : Option (Fin 256)) (cycle : Fin 4)
    (expression : ParsedExpr) (control : ParsedMaskExecutionControl)
    (hsm nf reduced : Bool) (accesses : ParsedIntegerBarAccesses)
    (write : PreparedParsedMaskedWrite)
    (operation : expression.op = .alu name (some precision) unsigned arg)
    (hcontext : control.context = ParsedIntegerContext.ofLinearIndex cendPE)
    (lowered : parsedIntegerBarExprAccessesInLine? expression
      (cendInitialPERegisters x).maskRegisters control.directive hsm control.context.group
      control.context.l2b control.context.l1b control.context.mab control.context.pe cycle
      control.context.bar0 control.context.bar1 control.context.tWord = some accesses)
    (prepared : prepareParsedIntegerBarALUWithForwarding (cendInitialPERegisters x)
      cendPoisonSlots cycle accesses reduced = .ok write) :
    ∀ i : Fin 4, i.val < 2 → write.data i ∈ cendHalfMixWords x := by
  intro i hi
  obtain ⟨sx, sy, output, readX, readY, evaluated, dataEq⟩ :=
    prepareParsedIntegerBarALUWithForwarding_data (cendInitialPERegisters x)
      cendPoisonSlots cycle accesses reduced write prepared
  have sources := parsedIntegerBarExprAccessesInLine?_source_eqs expression
    (cendInitialPERegisters x).maskRegisters control.directive hsm control.context.group
    control.context.l2b control.context.l1b control.context.mab control.context.pe cycle
    control.context.bar0 control.context.bar1 control.context.tWord name precision unsigned
    arg operation accesses lowered
  obtain ⟨sourceX, sourceXEq⟩ := sources.1
  obtain ⟨sourceY, sourceYEq⟩ := sources.2
  have sourceXEq' : ParsedOperand.toParsedIntegerInput? sourceX precision.laneWidth
      (ParsedIntegerContext.ofLinearIndex cendPE).group
      (ParsedIntegerContext.ofLinearIndex cendPE).l2b
      (ParsedIntegerContext.ofLinearIndex cendPE).l1b
      (ParsedIntegerContext.ofLinearIndex cendPE).mab
      (ParsedIntegerContext.ofLinearIndex cendPE).pe cycle control.context.bar0
      control.context.bar1 control.context.tWord = some accesses.sourceX := by
    rw [← hcontext]
    exact sourceXEq
  have sourceYEq' : ParsedOperand.toParsedIntegerInput? sourceY precision.laneWidth
      (ParsedIntegerContext.ofLinearIndex cendPE).group
      (ParsedIntegerContext.ofLinearIndex cendPE).l2b
      (ParsedIntegerContext.ofLinearIndex cendPE).l1b
      (ParsedIntegerContext.ofLinearIndex cendPE).mab
      (ParsedIntegerContext.ofLinearIndex cendPE).pe cycle control.context.bar0
      control.context.bar1 control.context.tWord = some accesses.sourceY := by
    rw [← hcontext]
    exact sourceYEq
  have sourceXOk : CendSourceOk x cycle accesses.sourceX :=
    cendSourceOk_toParsedIntegerInput x sourceX precision.laneWidth cycle
      control.context.bar0 control.context.bar1 control.context.tWord accesses.sourceX sourceXEq'
  have sourceYOk : CendSourceOk x cycle accesses.sourceY :=
    cendSourceOk_toParsedIntegerInput x sourceY precision.laneWidth cycle
      control.context.bar0 control.context.bar1 control.context.tWord accesses.sourceY sourceYEq'
  have hx : sx ∈ cendInitialBuses x := sourceXOk sx readX
  have hy : sy ∈ cendInitialBuses x := sourceYOk sy readY
  have opEq := parsedIntegerBarExprAccessesInLine?_op_provenance expression
    (cendInitialPERegisters x).maskRegisters control.directive hsm control.context.group
    control.context.l2b control.context.l1b control.context.mab control.context.pe cycle
    control.context.bar0 control.context.bar1 control.context.tWord name precision unsigned
    arg operation accesses lowered
  have evaluated' : evaluateParsedIntegerAlu (.alu name (some precision) unsigned arg)
      sx sy reduced = .ok output := by
    rwa [opEq, operation] at evaluated
  obtain ⟨sel, hsel, hselEq⟩ := parsedIntegerBarExprAccessesInLine?_flushSelection expression
    (cendInitialPERegisters x).maskRegisters control.directive hsm control.context.group
    control.context.l2b control.context.l1b control.context.mab control.context.pe cycle
    control.context.bar0 control.context.bar1 control.context.tWord name precision unsigned
    arg operation accesses lowered
  have flags : sel = none ∨ ∃ s, sel = some s ∧
      (s.flags = 0 ∨ s.flags = BitVec.allOnes 4) :=
    cendFlushSelection_zero_flags x expression.flush (cycle := cycle) (sel := sel) hsel
  rw [dataEq, hselEq]
  exact cendALU_flushed_data_halfMix x name precision unsigned arg sx sy hx hy reduced
    output evaluated' sel flags i hi

/-- The mask-input branch: the single prepared write's first two data words are
half-mixes. -/
theorem cendMaskInputPreparedWrite_data_halfMix
    (x : BitVec 64) (name : ParsedAluName) (precision : ParsedPrecision) (unsigned : Bool)
    (arg : Option (Fin 256)) (cycle : Fin 4)
    (expression : ParsedExpr) (control : ParsedMaskExecutionControl)
    (hsm nf reduced : Bool) (accesses : ParsedIntegerMaskInputAccesses)
    (flushSelection : Option PEWordSelection) (write : PreparedParsedMaskedWrite)
    (operation : expression.op = .alu name (some precision) unsigned arg)
    (hcontext : control.context = ParsedIntegerContext.ofLinearIndex cendPE)
    (lowered : parsedIntegerMaskInputExprAccessesInLine? expression
      (cendInitialPERegisters x).maskRegisters control.directive hsm control.context.group
      control.context.l2b control.context.l1b control.context.mab control.context.pe cycle
      control.context.bar0 control.context.bar1 control.context.tWord = some accesses)
    (hflush : resolveFlushSelection? expression.flush
      (cendInitialPERegisters x).maskRegisters cycle = some flushSelection)
    (prepared : prepareParsedIntegerMaskInputALUWriteWithForwarding (cendInitialPERegisters x)
      cendPoisonSlots cycle accesses flushSelection reduced = .ok write) :
    ∀ i : Fin 4, i.val < 2 → write.data i ∈ cendHalfMixWords x := by
  intro i hi
  obtain ⟨sx, sy, output, readX, readY, evaluated, dataEq⟩ :=
    prepareParsedIntegerMaskInputALUWriteWithForwarding_data (cendInitialPERegisters x)
      cendPoisonSlots cycle accesses flushSelection reduced write prepared
  have sources := parsedIntegerMaskInputExprAccessesInLine?_source_eqs expression
    (cendInitialPERegisters x).maskRegisters control.directive hsm control.context.group
    control.context.l2b control.context.l1b control.context.mab control.context.pe cycle
    control.context.bar0 control.context.bar1 control.context.tWord name precision unsigned
    arg operation accesses lowered
  obtain ⟨sourceX, sourceXEq⟩ := sources.1
  obtain ⟨sourceY, sourceYEq⟩ := sources.2
  have sourceXEq' : ParsedOperand.toParsedIntegerInput? sourceX precision.laneWidth
      (ParsedIntegerContext.ofLinearIndex cendPE).group
      (ParsedIntegerContext.ofLinearIndex cendPE).l2b
      (ParsedIntegerContext.ofLinearIndex cendPE).l1b
      (ParsedIntegerContext.ofLinearIndex cendPE).mab
      (ParsedIntegerContext.ofLinearIndex cendPE).pe cycle control.context.bar0
      control.context.bar1 control.context.tWord = some accesses.sourceX := by
    rw [← hcontext]
    exact sourceXEq
  have sourceYEq' : ParsedOperand.toParsedIntegerInput? sourceY precision.laneWidth
      (ParsedIntegerContext.ofLinearIndex cendPE).group
      (ParsedIntegerContext.ofLinearIndex cendPE).l2b
      (ParsedIntegerContext.ofLinearIndex cendPE).l1b
      (ParsedIntegerContext.ofLinearIndex cendPE).mab
      (ParsedIntegerContext.ofLinearIndex cendPE).pe cycle control.context.bar0
      control.context.bar1 control.context.tWord = some accesses.sourceY := by
    rw [← hcontext]
    exact sourceYEq
  have sourceXOk : CendSourceOk x cycle accesses.sourceX :=
    cendSourceOk_toParsedIntegerInput x sourceX precision.laneWidth cycle
      control.context.bar0 control.context.bar1 control.context.tWord accesses.sourceX sourceXEq'
  have sourceYOk : CendSourceOk x cycle accesses.sourceY :=
    cendSourceOk_toParsedIntegerInput x sourceY precision.laneWidth cycle
      control.context.bar0 control.context.bar1 control.context.tWord accesses.sourceY sourceYEq'
  have hx : sx ∈ cendInitialBuses x := sourceXOk sx readX
  have hy : sy ∈ cendInitialBuses x := sourceYOk sy readY
  have opEq := parsedIntegerMaskInputExprAccessesInLine?_op_provenance expression
    (cendInitialPERegisters x).maskRegisters control.directive hsm control.context.group
    control.context.l2b control.context.l1b control.context.mab control.context.pe cycle
    control.context.bar0 control.context.bar1 control.context.tWord name precision unsigned
    arg operation accesses lowered
  have evaluated' : evaluateParsedIntegerAlu (.alu name (some precision) unsigned arg)
      sx sy reduced = .ok output := by
    rwa [opEq, operation] at evaluated
  have flags : flushSelection = none ∨ ∃ s, flushSelection = some s ∧
      (s.flags = 0 ∨ s.flags = BitVec.allOnes 4) :=
    cendFlushSelection_zero_flags x expression.flush (cycle := cycle) (sel := flushSelection) hflush
  rw [dataEq]
  exact cendALU_flushed_data_halfMix x name precision unsigned arg sx sy hx hy reduced
    output evaluated' flushSelection flags i hi

/-- The memory-then-OMR branch: the memory write and the OMR write both carry
the same flushed bus. -/
theorem cendMemoryThenInputPreparedWrites_data_halfMix
    (x : BitVec 64) (name : ParsedAluName) (precision : ParsedPrecision) (unsigned : Bool)
    (arg : Option (Fin 256)) (cycle : Fin 4)
    (expression : ParsedExpr) (control : ParsedMaskExecutionControl)
    (hsm nf reduced : Bool) (accesses : ParsedIntegerMaskMemoryThenInputAccesses)
    (flushSelection : Option PEWordSelection)
    (memoryWrites : List PreparedParsedMaskedWrite) (omrWrite : PreparedParsedMaskedWrite)
    (operation : expression.op = .alu name (some precision) unsigned arg)
    (hcontext : control.context = ParsedIntegerContext.ofLinearIndex cendPE)
    (lowered : parsedIntegerMaskMemoryThenInputExprAccessesInLine? expression
      (cendInitialPERegisters x).maskRegisters control.directive hsm control.context.group
      control.context.l2b control.context.l1b control.context.mab control.context.pe cycle
      control.context.bar0 control.context.bar1 control.context.tWord = some accesses)
    (hflush : resolveFlushSelection? expression.flush
      (cendInitialPERegisters x).maskRegisters cycle = some flushSelection)
    (prepared : prepareParsedIntegerMaskMemoryThenInputALUWritesWithForwarding
      (cendInitialPERegisters x) cendPoisonSlots cycle accesses flushSelection reduced
      = .ok (memoryWrites, omrWrite)) :
    ∀ item ∈ memoryWrites ++ [omrWrite], ∀ i : Fin 4, i.val < 2 →
      item.data i ∈ cendHalfMixWords x := by
  obtain ⟨sx, sy, output, readX, readY, evaluated, mapEq, omrEq, -⟩ :=
    prepareParsedIntegerMaskMemoryThenInputALUWritesWithForwarding_data
      (cendInitialPERegisters x) cendPoisonSlots cycle accesses flushSelection reduced
      memoryWrites omrWrite prepared
  have sources := parsedIntegerMaskMemoryThenInputExprAccessesInLine?_source_eqs expression
    (cendInitialPERegisters x).maskRegisters control.directive hsm control.context.group
    control.context.l2b control.context.l1b control.context.mab control.context.pe cycle
    control.context.bar0 control.context.bar1 control.context.tWord name precision unsigned
    arg operation accesses lowered
  obtain ⟨sourceX, sourceXEq⟩ := sources.1
  obtain ⟨sourceY, sourceYEq⟩ := sources.2
  have sourceXEq' : ParsedOperand.toParsedIntegerInput? sourceX precision.laneWidth
      (ParsedIntegerContext.ofLinearIndex cendPE).group
      (ParsedIntegerContext.ofLinearIndex cendPE).l2b
      (ParsedIntegerContext.ofLinearIndex cendPE).l1b
      (ParsedIntegerContext.ofLinearIndex cendPE).mab
      (ParsedIntegerContext.ofLinearIndex cendPE).pe cycle control.context.bar0
      control.context.bar1 control.context.tWord = some accesses.sourceX := by
    rw [← hcontext]
    exact sourceXEq
  have sourceYEq' : ParsedOperand.toParsedIntegerInput? sourceY precision.laneWidth
      (ParsedIntegerContext.ofLinearIndex cendPE).group
      (ParsedIntegerContext.ofLinearIndex cendPE).l2b
      (ParsedIntegerContext.ofLinearIndex cendPE).l1b
      (ParsedIntegerContext.ofLinearIndex cendPE).mab
      (ParsedIntegerContext.ofLinearIndex cendPE).pe cycle control.context.bar0
      control.context.bar1 control.context.tWord = some accesses.sourceY := by
    rw [← hcontext]
    exact sourceYEq
  have sourceXOk : CendSourceOk x cycle accesses.sourceX :=
    cendSourceOk_toParsedIntegerInput x sourceX precision.laneWidth cycle
      control.context.bar0 control.context.bar1 control.context.tWord accesses.sourceX sourceXEq'
  have sourceYOk : CendSourceOk x cycle accesses.sourceY :=
    cendSourceOk_toParsedIntegerInput x sourceY precision.laneWidth cycle
      control.context.bar0 control.context.bar1 control.context.tWord accesses.sourceY sourceYEq'
  have hx : sx ∈ cendInitialBuses x := sourceXOk sx readX
  have hy : sy ∈ cendInitialBuses x := sourceYOk sy readY
  have opEq := parsedIntegerMaskMemoryThenInputExprAccessesInLine?_op_provenance expression
    (cendInitialPERegisters x).maskRegisters control.directive hsm control.context.group
    control.context.l2b control.context.l1b control.context.mab control.context.pe cycle
    control.context.bar0 control.context.bar1 control.context.tWord name precision unsigned
    arg operation accesses lowered
  have evaluated' : evaluateParsedIntegerAlu (.alu name (some precision) unsigned arg)
      sx sy reduced = .ok output := by
    rwa [opEq, operation] at evaluated
  have flags : flushSelection = none ∨ ∃ s, flushSelection = some s ∧
      (s.flags = 0 ∨ s.flags = BitVec.allOnes 4) :=
    cendFlushSelection_zero_flags x expression.flush (cycle := cycle) (sel := flushSelection) hflush
  have flushed : ∀ w ∈ memoryWrites,
      w.data = unpackALUBus (parsedOutputAfterFlush flushSelection output.value) := by
    intro w hw
    have member : w.data ∈ memoryWrites.map (fun w => w.data) :=
      List.mem_map.mpr ⟨w, hw, rfl⟩
    rw [mapEq] at member
    simpa using member
  intro item member i hi
  rcases List.mem_append.mp member with earlier | later
  · rw [flushed item earlier]
    exact cendALU_flushed_data_halfMix x name precision unsigned arg sx sy hx hy reduced
      output evaluated' flushSelection flags i hi
  · rw [List.mem_singleton] at later
    subst item
    rw [omrEq]
    exact cendALU_flushed_data_halfMix x name precision unsigned arg sx sy hx hy reduced
      output evaluated' flushSelection flags i hi

/-- The OMR-then-memory branch: the OMR write and the memory write both carry
the same flushed bus. -/
theorem cendInputThenMemoryPreparedWrites_data_halfMix
    (x : BitVec 64) (name : ParsedAluName) (precision : ParsedPrecision) (unsigned : Bool)
    (arg : Option (Fin 256)) (cycle : Fin 4)
    (expression : ParsedExpr) (control : ParsedMaskExecutionControl)
    (hsm nf reduced : Bool) (accesses : ParsedIntegerMaskInputThenMemoryAccesses)
    (flushSelection : Option PEWordSelection)
    (memoryWrites : List PreparedParsedMaskedWrite) (omrWrite : PreparedParsedMaskedWrite)
    (operation : expression.op = .alu name (some precision) unsigned arg)
    (hcontext : control.context = ParsedIntegerContext.ofLinearIndex cendPE)
    (lowered : parsedIntegerMaskInputThenMemoryExprAccessesInLine? expression
      (cendInitialPERegisters x).maskRegisters control.directive hsm control.context.group
      control.context.l2b control.context.l1b control.context.mab control.context.pe cycle
      control.context.bar0 control.context.bar1 control.context.tWord = some accesses)
    (hflush : resolveFlushSelection? expression.flush
      (cendInitialPERegisters x).maskRegisters cycle = some flushSelection)
    (prepared : prepareParsedIntegerMaskInputThenMemoryALUWritesWithForwarding
      (cendInitialPERegisters x) cendPoisonSlots cycle accesses control.directive hsm
      flushSelection reduced = .ok (memoryWrites, omrWrite)) :
    ∀ item ∈ memoryWrites, ∀ i : Fin 4, i.val < 2 →
      item.data i ∈ cendHalfMixWords x := by
  obtain ⟨bus, flagsMask, memorySelection, writesEq, producerEq⟩ :=
    prepareParsedIntegerMaskInputThenMemoryALUWritesWithForwarding_shape
      (cendInitialPERegisters x) cendPoisonSlots cycle accesses control.directive hsm
      flushSelection reduced memoryWrites omrWrite prepared
  obtain ⟨sx, sy, output, readX, readY, evaluated, omrEq, -⟩ :=
    prepareParsedIntegerMaskInputThenMemoryALUWritesWithForwarding_data
      (cendInitialPERegisters x) cendPoisonSlots cycle accesses control.directive hsm
      flushSelection reduced memoryWrites omrWrite prepared
  have sources := parsedIntegerMaskInputThenMemoryExprAccessesInLine?_source_eqs expression
    (cendInitialPERegisters x).maskRegisters control.directive hsm control.context.group
    control.context.l2b control.context.l1b control.context.mab control.context.pe cycle
    control.context.bar0 control.context.bar1 control.context.tWord name precision unsigned
    arg operation accesses lowered
  obtain ⟨sourceX, sourceXEq⟩ := sources.1
  obtain ⟨sourceY, sourceYEq⟩ := sources.2
  have sourceXEq' : ParsedOperand.toParsedIntegerInput? sourceX precision.laneWidth
      (ParsedIntegerContext.ofLinearIndex cendPE).group
      (ParsedIntegerContext.ofLinearIndex cendPE).l2b
      (ParsedIntegerContext.ofLinearIndex cendPE).l1b
      (ParsedIntegerContext.ofLinearIndex cendPE).mab
      (ParsedIntegerContext.ofLinearIndex cendPE).pe cycle control.context.bar0
      control.context.bar1 control.context.tWord = some accesses.sourceX := by
    rw [← hcontext]
    exact sourceXEq
  have sourceYEq' : ParsedOperand.toParsedIntegerInput? sourceY precision.laneWidth
      (ParsedIntegerContext.ofLinearIndex cendPE).group
      (ParsedIntegerContext.ofLinearIndex cendPE).l2b
      (ParsedIntegerContext.ofLinearIndex cendPE).l1b
      (ParsedIntegerContext.ofLinearIndex cendPE).mab
      (ParsedIntegerContext.ofLinearIndex cendPE).pe cycle control.context.bar0
      control.context.bar1 control.context.tWord = some accesses.sourceY := by
    rw [← hcontext]
    exact sourceYEq
  have sourceXOk : CendSourceOk x cycle accesses.sourceX :=
    cendSourceOk_toParsedIntegerInput x sourceX precision.laneWidth cycle
      control.context.bar0 control.context.bar1 control.context.tWord accesses.sourceX sourceXEq'
  have sourceYOk : CendSourceOk x cycle accesses.sourceY :=
    cendSourceOk_toParsedIntegerInput x sourceY precision.laneWidth cycle
      control.context.bar0 control.context.bar1 control.context.tWord accesses.sourceY sourceYEq'
  have hx : sx ∈ cendInitialBuses x := sourceXOk sx readX
  have hy : sy ∈ cendInitialBuses x := sourceYOk sy readY
  have opEq := parsedIntegerMaskInputThenMemoryExprAccessesInLine?_op_provenance expression
    (cendInitialPERegisters x).maskRegisters control.directive hsm control.context.group
    control.context.l2b control.context.l1b control.context.mab control.context.pe cycle
    control.context.bar0 control.context.bar1 control.context.tWord name precision unsigned
    arg operation accesses lowered
  have evaluated' : evaluateParsedIntegerAlu (.alu name (some precision) unsigned arg)
      sx sy reduced = .ok output := by
    rwa [opEq, operation] at evaluated
  have flags : flushSelection = none ∨ ∃ s, flushSelection = some s ∧
      (s.flags = 0 ∨ s.flags = BitVec.allOnes 4) :=
    cendFlushSelection_zero_flags x expression.flush (cycle := cycle) (sel := flushSelection) hflush
  have busEq : bus = unpackALUBus (parsedOutputAfterFlush flushSelection output.value) := by
    have hdata : omrWrite.data = bus := by
      rw [producerEq]
    rw [omrEq] at hdata
    exact hdata.symm
  intro item member i hi
  rw [writesEq] at member
  rcases List.mem_cons.mp member with rfl | later
  · rw [busEq]
    exact cendALU_flushed_data_halfMix x name precision unsigned arg sx sy hx hy reduced
      output evaluated' flushSelection flags i hi
  · rw [List.mem_singleton] at later
    subst item
    rw [busEq]
    exact cendALU_flushed_data_halfMix x name precision unsigned arg sx sy hx hy reduced
      output evaluated' flushSelection flags i hi

/-! ## 3. The per-cycle data dispatch -/

/-- **The general per-cycle data dispatch.**  The cycle is stated for an opaque
expression and control whose operation is the plain `.alu` one and whose context
is the observed PE's linear-index context, so that the nine-branch ladder can be
carried out. -/
theorem cendPlainCycleHalfMixData_general
    (x : BitVec 64) (name : ParsedAluName) (precision : ParsedPrecision) (unsigned : Bool)
    (arg : Option (Fin 256)) (sources destinations : List ParsedOperand)
    (flush : Option ParsedMask) (text : String) (directive : ParsedMaskDirective)
    (elapsed : Nat) (hsm noForward reduced : Bool) (cycle : Fin 4)
    (nextSlots : ProofsLean.MNCore.Forwarding.Slots)
    (writes : List PreparedParsedMaskedWrite)
    (slots : ProofsLean.MNCore.Forwarding.Slots)
    (expression : ParsedExpr) (control : ParsedMaskExecutionControl)
    (operation : expression.op = .alu name (some precision) unsigned arg)
    (hcontext : control.context = ParsedIntegerContext.ofLinearIndex cendPE)
    (prep : prepareParsedIntegerALUExprCycle (cendInitialPERegisters x) cendPoisonSlots
      nextSlots expression control hsm noForward reduced cycle = .ok (writes, slots)) :
    ∀ write ∈ writes, ∀ i : Fin 4, i.val < 2 → write.data i ∈ cendHalfMixWords x := by
  unfold prepareParsedIntegerALUExprCycle at prep
  rw [operation] at prep
  dsimp only at prep
  cases hdirect : ParsedExpr.toDirectMaskedIntegerAccessesInLine? expression
      (cendInitialPERegisters x).maskRegisters control.directive hsm control.context.group
      control.context.l2b control.context.l1b control.context.mab control.context.pe cycle
      control.context.bar0 control.context.bar1 control.context.tWord with
  | some accesses =>
      rw [hdirect] at prep
      dsimp only at prep
      cases hprepared : prepareParsedMaskedWriteWithForwarding (cendInitialPERegisters x)
          cendPoisonSlots cycle accesses reduced with
      | failure => rw [hprepared] at prep; exact absurd prep (by simp)
      | unknown => rw [hprepared] at prep; exact absurd prep (by simp)
      | ok write =>
          rw [hprepared] at prep
          dsimp only at prep
          cases hupdated : updateParsedIntegerALUForwardingCycle nextSlots cycle (.ok write)
              noForward with
          | failure => rw [hupdated] at prep; exact absurd prep (by simp)
          | unknown => rw [hupdated] at prep; exact absurd prep (by simp)
          | ok slots' =>
              rw [hupdated] at prep
              dsimp only at prep
              simp only [StepResult.ok.injEq, Prod.mk.injEq] at prep
              rw [← prep.1]
              intro item member i hi
              rw [List.mem_singleton] at member
              subst item
              exact cendDirectPreparedWrite_data_halfMix x name precision unsigned arg cycle
                expression control hsm noForward reduced accesses write operation hcontext
                hdirect hprepared i hi
  | none =>
      rw [hdirect] at prep
      dsimp only at prep
      cases hmultiple : ParsedExpr.toDirectMaskedIntegerWritesInLine? expression
          (cendInitialPERegisters x).maskRegisters control.directive hsm control.context.group
          control.context.l2b control.context.l1b control.context.mab control.context.pe cycle
          control.context.bar0 control.context.bar1 control.context.tWord with
      | some accessList =>
          cases accessList with
          | nil => rw [hmultiple] at prep; exact absurd prep (by simp)
          | cons access rest =>
              rw [hmultiple] at prep
              dsimp only at prep
              cases hprepared : prepareParsedMaskedWriteWithForwarding (cendInitialPERegisters x)
                  cendPoisonSlots cycle access reduced with
              | failure => rw [hprepared] at prep; exact absurd prep (by simp)
              | unknown => rw [hprepared] at prep; exact absurd prep (by simp)
              | ok write =>
                  rw [hprepared] at prep
                  dsimp only at prep
                  cases hupdated : updateParsedIntegerALUForwardingCycle nextSlots cycle
                      (.ok write) noForward with
                  | failure => rw [hupdated] at prep; exact absurd prep (by simp)
                  | unknown => rw [hupdated] at prep; exact absurd prep (by simp)
                  | ok slots' =>
                      rw [hupdated] at prep
                      dsimp only at prep
                      simp only [StepResult.ok.injEq, Prod.mk.injEq] at prep
                      rw [← prep.1]
                      exact cendMultiplePreparedWrites_data_halfMix x name precision unsigned
                        arg cycle expression control hsm noForward reduced access rest write
                        operation hcontext hmultiple hprepared
      | none =>
          rw [hmultiple] at prep
          dsimp only at prep
          cases homr : parsedIntegerMaskExprAccessesInLine? expression
              (cendInitialPERegisters x).maskRegisters control.directive hsm
              control.context.pe cycle control.context.bar0 control.context.bar1
              control.context.tWord with
          | some accesses =>
              rw [homr] at prep
              dsimp only at prep
              cases hflush : resolveFlushSelection? expression.flush
                  (cendInitialPERegisters x).maskRegisters cycle with
              | none => rw [hflush] at prep; exact absurd prep (by simp)
              | some flushSelection =>
                  rw [hflush] at prep
                  dsimp only at prep
                  cases hprepared : prepareParsedIntegerMaskALUWriteWithForwarding
                      (cendInitialPERegisters x) cendPoisonSlots cycle accesses flushSelection
                      reduced with
                  | failure => rw [hprepared] at prep; exact absurd prep (by simp)
                  | unknown => rw [hprepared] at prep; exact absurd prep (by simp)
                  | ok write =>
                      rw [hprepared] at prep
                      dsimp only at prep
                      cases hupdated : updateParsedIntegerALUForwardingCycle nextSlots cycle
                          (.ok write) noForward with
                      | failure => rw [hupdated] at prep; exact absurd prep (by simp)
                      | unknown => rw [hupdated] at prep; exact absurd prep (by simp)
                      | ok slots' =>
                          rw [hupdated] at prep
                          dsimp only at prep
                          simp only [StepResult.ok.injEq, Prod.mk.injEq] at prep
                          rw [← prep.1]
                          intro item member i hi
                          rw [List.mem_singleton] at member
                          subst item
                          exact cendOmrPreparedWrite_data_halfMix x name precision unsigned
                            arg cycle expression control hsm noForward reduced accesses
                            flushSelection write operation homr hflush hprepared i hi
          | none =>
              rw [homr] at prep
              dsimp only at prep
              cases hnoWrite : parsedIntegerNoWriteExprAccessesInLine? expression
                  (cendInitialPERegisters x).maskRegisters control.context.pe cycle
                  control.context.group control.context.l2b control.context.l1b
                  control.context.mab control.context.bar0 control.context.bar1
                  control.context.tWord with
              | some accesses =>
                  rw [hnoWrite] at prep
                  dsimp only at prep
                  cases hprepared : prepareParsedIntegerNoWriteALUWithForwarding
                      (cendInitialPERegisters x) cendPoisonSlots cycle accesses reduced with
                  | failure => rw [hprepared] at prep; exact absurd prep (by simp)
                  | unknown => rw [hprepared] at prep; exact absurd prep (by simp)
                  | ok write =>
                      rw [hprepared] at prep
                      dsimp only at prep
                      cases hupdated : updateParsedIntegerALUForwardingCycle nextSlots cycle
                          (.ok write) noForward with
                      | failure => rw [hupdated] at prep; exact absurd prep (by simp)
                      | unknown => rw [hupdated] at prep; exact absurd prep (by simp)
                      | ok slots' =>
                          rw [hupdated] at prep
                          dsimp only at prep
                          simp only [StepResult.ok.injEq, Prod.mk.injEq] at prep
                          rw [← prep.1]
                          intro item member i hi
                          rw [List.mem_singleton] at member
                          subst item
                          exact cendNoWritePreparedWrite_data_halfMix x name precision
                            unsigned arg cycle expression control hsm noForward reduced
                            accesses write operation hcontext hnoWrite hprepared i hi
              | none =>
                  rw [hnoWrite] at prep
                  dsimp only at prep
                  cases hbar : parsedIntegerBarExprAccessesInLine? expression
                      (cendInitialPERegisters x).maskRegisters control.directive hsm
                      control.context.group control.context.l2b control.context.l1b
                      control.context.mab control.context.pe cycle control.context.bar0
                      control.context.bar1 control.context.tWord with
                  | some accesses =>
                      rw [hbar] at prep
                      dsimp only at prep
                      cases hprepared : prepareParsedIntegerBarALUWithForwarding
                          (cendInitialPERegisters x) cendPoisonSlots cycle accesses reduced with
                      | failure => rw [hprepared] at prep; exact absurd prep (by simp)
                      | unknown => rw [hprepared] at prep; exact absurd prep (by simp)
                      | ok write =>
                          rw [hprepared] at prep
                          dsimp only at prep
                          cases hupdated : updateParsedIntegerALUForwardingCycle nextSlots
                              cycle (.ok write) noForward with
                          | failure => rw [hupdated] at prep; exact absurd prep (by simp)
                          | unknown => rw [hupdated] at prep; exact absurd prep (by simp)
                          | ok slots' =>
                              rw [hupdated] at prep
                              dsimp only at prep
                              simp only [StepResult.ok.injEq, Prod.mk.injEq] at prep
                              rw [← prep.1]
                              intro item member i hi
                              rw [List.mem_singleton] at member
                              subst item
                              exact cendBarPreparedWrite_data_halfMix x name precision
                                unsigned arg cycle expression control hsm noForward reduced
                                accesses write operation hcontext hbar hprepared i hi
                  | none =>
                      rw [hbar] at prep
                      dsimp only at prep
                      cases hinput : parsedIntegerMaskInputExprAccessesInLine? expression
                          (cendInitialPERegisters x).maskRegisters control.directive hsm
                          control.context.group control.context.l2b control.context.l1b
                          control.context.mab control.context.pe cycle control.context.bar0
                          control.context.bar1 control.context.tWord with
                      | some accesses =>
                          rw [hinput] at prep
                          dsimp only at prep
                          cases hflush : resolveFlushSelection? expression.flush
                              (cendInitialPERegisters x).maskRegisters cycle with
                          | none => rw [hflush] at prep; exact absurd prep (by simp)
                          | some flushSelection =>
                              rw [hflush] at prep
                              dsimp only at prep
                              cases hprepared :
                                  prepareParsedIntegerMaskInputALUWriteWithForwarding
                                    (cendInitialPERegisters x) cendPoisonSlots cycle accesses
                                    flushSelection reduced with
                              | failure => rw [hprepared] at prep; exact absurd prep (by simp)
                              | unknown => rw [hprepared] at prep; exact absurd prep (by simp)
                              | ok write =>
                                  rw [hprepared] at prep
                                  dsimp only at prep
                                  cases hupdated :
                                      updateParsedIntegerALUForwardingCycle nextSlots cycle
                                        (.ok write) noForward with
                                  | failure => rw [hupdated] at prep; exact absurd prep (by simp)
                                  | unknown => rw [hupdated] at prep; exact absurd prep (by simp)
                                  | ok slots' =>
                                      rw [hupdated] at prep
                                      dsimp only at prep
                                      simp only [StepResult.ok.injEq, Prod.mk.injEq] at prep
                                      rw [← prep.1]
                                      intro item member i hi
                                      rw [List.mem_singleton] at member
                                      subst item
                                      exact cendMaskInputPreparedWrite_data_halfMix x name
                                        precision unsigned arg cycle expression control hsm
                                        noForward reduced accesses flushSelection write
                                        operation hcontext hinput hflush hprepared i hi
                      | none =>
                          rw [hinput] at prep
                          dsimp only at prep
                          cases hmixed :
                              parsedIntegerMaskMemoryThenInputExprAccessesInLine? expression
                                (cendInitialPERegisters x).maskRegisters control.directive
                                hsm control.context.group control.context.l2b
                                control.context.l1b control.context.mab control.context.pe
                                cycle control.context.bar0 control.context.bar1
                                control.context.tWord with
                          | some accesses =>
                              rw [hmixed] at prep
                              dsimp only at prep
                              cases hflush : resolveFlushSelection? expression.flush
                                  (cendInitialPERegisters x).maskRegisters cycle with
                              | none => rw [hflush] at prep; exact absurd prep (by simp)
                              | some flushSelection =>
                                  rw [hflush] at prep
                                  dsimp only at prep
                                  cases hprepared :
                                      prepareParsedIntegerMaskMemoryThenInputALUWritesWithForwarding
                                        (cendInitialPERegisters x) cendPoisonSlots cycle
                                        accesses flushSelection reduced with
                                  | failure => rw [hprepared] at prep; exact absurd prep (by simp)
                                  | unknown => rw [hprepared] at prep; exact absurd prep (by simp)
                                  | ok pair =>
                                      obtain ⟨memoryWrites, omrWrite⟩ := pair
                                      rw [hprepared] at prep
                                      dsimp only at prep
                                      cases hupdated :
                                          updateParsedIntegerALUForwardingCycle nextSlots
                                            cycle (.ok omrWrite) noForward with
                                      | failure => rw [hupdated] at prep; exact absurd prep (by simp)
                                      | unknown => rw [hupdated] at prep; exact absurd prep (by simp)
                                      | ok slots' =>
                                          rw [hupdated] at prep
                                          dsimp only at prep
                                          simp only [StepResult.ok.injEq, Prod.mk.injEq]
                                            at prep
                                          rw [← prep.1]
                                          exact
                                            cendMemoryThenInputPreparedWrites_data_halfMix
                                              x name precision unsigned arg cycle expression
                                              control hsm noForward reduced accesses
                                              flushSelection memoryWrites omrWrite operation
                                              hcontext hmixed hflush hprepared
                          | none =>
                              rw [hmixed] at prep
                              dsimp only at prep
                              cases hreverse :
                                  parsedIntegerMaskInputThenMemoryExprAccessesInLine?
                                    expression (cendInitialPERegisters x).maskRegisters
                                    control.directive hsm control.context.group
                                    control.context.l2b control.context.l1b
                                    control.context.mab control.context.pe cycle
                                    control.context.bar0 control.context.bar1
                                    control.context.tWord with
                              | some accesses =>
                                  rw [hreverse] at prep
                                  dsimp only at prep
                                  cases hflush : resolveFlushSelection? expression.flush
                                      (cendInitialPERegisters x).maskRegisters cycle with
                                  | none => rw [hflush] at prep; exact absurd prep (by simp)
                                  | some flushSelection =>
                                      rw [hflush] at prep
                                      dsimp only at prep
                                      cases hprepared :
                                          prepareParsedIntegerMaskInputThenMemoryALUWritesWithForwarding
                                            (cendInitialPERegisters x) cendPoisonSlots cycle
                                            accesses control.directive hsm flushSelection
                                            reduced with
                                      | failure => rw [hprepared] at prep; exact absurd prep (by simp)
                                      | unknown => rw [hprepared] at prep; exact absurd prep (by simp)
                                      | ok pair =>
                                          obtain ⟨memoryWrites, omrWrite⟩ := pair
                                          rw [hprepared] at prep
                                          dsimp only at prep
                                          cases hupdated :
                                              updateParsedIntegerALUForwardingCycle
                                                nextSlots cycle (.ok omrWrite) noForward with
                                          | failure => rw [hupdated] at prep; exact absurd prep (by simp)
                                          | unknown => rw [hupdated] at prep; exact absurd prep (by simp)
                                          | ok slots' =>
                                              rw [hupdated] at prep
                                              dsimp only at prep
                                              simp only [StepResult.ok.injEq,
                                                Prod.mk.injEq] at prep
                                              rw [← prep.1]
                                              exact
                                                cendInputThenMemoryPreparedWrites_data_halfMix
                                                  x name precision unsigned arg cycle
                                                  expression control hsm noForward reduced
                                                  accesses flushSelection memoryWrites
                                                  omrWrite operation hcontext hreverse hflush
                                                  hprepared
                              | none =>
                                  rw [hreverse] at prep
                                  dsimp only at prep
                                  split at prep
                                  · exact absurd prep (by simp)
                                  · exact absurd prep (by simp)

/-- **The nine-branch executor data dispatch.**  Every prepared write of a
successful plain integer ALU cycle at the `12.convert-endian` initial state has
its first two data words in the half-mix value set. -/
theorem cendPlainCycleHalfMixData : CendPlainCycleHalfMixData := by
  intro x name precision unsigned arg sources destinations flush text directive elapsed
    hsm noForward reduced cycle nextSlots writes slots prep
  exact cendPlainCycleHalfMixData_general x name precision unsigned arg sources destinations
    flush text directive elapsed hsm noForward reduced cycle nextSlots writes slots
    ⟨.alu name (some precision) unsigned arg, sources, destinations, flush, text⟩
    ⟨directive, ParsedIntegerContext.ofLinearIndex cendPE, elapsed⟩ rfl rfl prep

/-! ## 3b. Per-cycle alignment of the LM1 destinations -/

/-- The aligned-destination projection of a direct prepared write. -/
theorem prepareParsedMaskedWriteWithForwarding_destination_aligned
    (files : IntegerRegisterFiles) (slots : ProofsLean.MNCore.Forwarding.Slots)
    (cycle : Fin 4) (accesses : ParsedMaskedIntegerAccesses) (reduced : Bool)
    (write : PreparedParsedMaskedWrite)
    (prepared : prepareParsedMaskedWriteWithForwarding files slots cycle accesses reduced
      = .ok write)
    (aligned : accesses.destination.address.val %
      PEMemory.count accesses.destination.bank accesses.destination.width = 0) :
    ∀ (width : PEMemory.Width) (address : Fin Bank.lm1.capacity),
      write.destination = some ⟨Bank.lm1, width, address⟩ →
        address.val % PEMemory.count Bank.lm1 width = 0 := by
  intro width address destination
  rw [prepareParsedMaskedWriteWithForwarding_destination files slots cycle accesses reduced
    write prepared] at destination
  have same : accesses.destination = ⟨Bank.lm1, width, address⟩ :=
    Option.some.inj destination
  rw [same] at aligned
  exact aligned

/-- **Alignment of the resolved destination for its bank's word count.**  The
`.t` bank always addresses `cycle * 4` and has count `4`; every other bank's count
is the access width in words, for which the resolver's down-alignment applies. -/
theorem parsedOperand_toDirectMemoryAccessMode_count_aligned
    (operand : ParsedOperand) (allowDestinationMask : Bool) (pe cycle : Fin 4)
    (bar0 bar1 : BitVec 12) (tWord : BitVec 32) (access : DirectMemoryAccess)
    (lowered : ParsedOperand.toDirectMemoryAccessMode? operand allowDestinationMask pe cycle
      bar0 bar1 tWord = some access) :
    access.address.val % PEMemory.count access.bank access.width = 0 := by
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
                  show (if (bank == PEMemory.Bank.t) = true then cycle.val * 4 else
                    ((((if (bank == PEMemory.Bank.lm0) = true then bar0.toNat
                         else if (bank == PEMemory.Bank.lm1) = true then bar1.toNat else 0) +
                        (if memoryAccess.region.tIndirect = true then tWord.toNat else 0)) +
                      parsedRegionAddressAt memoryAccess.region cycle +
                      (match memoryAccess.region.madpe with
                       | some threshold => if (pe.val ≤ threshold) then width.words else 0
                       | none => 0)) / width.words * width.words % bank.capacity)) %
                    PEMemory.count bank width = 0
                  by_cases isT : bank = PEMemory.Bank.t
                  · rw [if_pos (by simp [isT])]
                    rw [isT]
                    simp [PEMemory.count]
                  · rw [if_neg (by simp [isT])]
                    have hcount : PEMemory.count bank width = width.words := by
                      simp [PEMemory.count, isT]
                    rw [hcount]
                    have dvd : width.words ∣ bank.capacity := by
                      cases width <;> cases bank <;> decide
                    rw [Nat.mod_mod_of_dvd _ dvd]
                    exact Nat.mod_eq_zero_of_dvd ⟨_, by rw [Nat.mul_comm]⟩
  | bar _ _ mask => simp [ParsedOperand.toDirectMemoryAccessMode?] at lowered
  | forward _ _ _ _ => simp [ParsedOperand.toDirectMemoryAccessMode?] at lowered
  | fixed kind => simp [ParsedOperand.toDirectMemoryAccessMode?] at lowered
  | omr _ _ => simp [ParsedOperand.toDirectMemoryAccessMode?] at lowered
  | matrix _ _ _ => simp [ParsedOperand.toDirectMemoryAccessMode?] at lowered
  | nowrite => simp [ParsedOperand.toDirectMemoryAccessMode?] at lowered
  | l1bm _ _ => simp [ParsedOperand.toDirectMemoryAccessMode?] at lowered
  | l2bm _ _ => simp [ParsedOperand.toDirectMemoryAccessMode?] at lowered
  | dar _ => simp [ParsedOperand.toDirectMemoryAccessMode?] at lowered

/-- The resolved destination of a lowering is aligned for its bank's word count. -/
theorem cendResolvedDestination_count_aligned
    (operand : ParsedOperand) (pe cycle : Fin 4) (bar0 bar1 : BitVec 12)
    (tWord : BitVec 32) (access : DirectMemoryAccess)
    (resolved : ParsedOperand.toDirectMemoryDestination? operand pe cycle bar0 bar1 tWord =
      some access) :
    access.address.val % PEMemory.count access.bank access.width = 0 :=
  parsedOperand_toDirectMemoryAccessMode_count_aligned operand true pe cycle bar0 bar1 tWord
    access resolved

/-- A write with no destination has no LM1 destination. -/
theorem cendNoDestination_lm1Aligned (write : PreparedParsedMaskedWrite)
    (isNone : write.destination = none) :
    ∀ (width : PEMemory.Width) (address : Fin Bank.lm1.capacity),
      write.destination = some ⟨Bank.lm1, width, address⟩ →
        address.val % PEMemory.count Bank.lm1 width = 0 := by
  intro width address destination
  rw [isNone] at destination
  exact absurd destination (by simp)

/-- The direct-access branch: the prepared write's LM1 destination is aligned. -/
theorem cendDirectPreparedWrite_lm1Aligned
    (x : BitVec 64) (cycle : Fin 4) (expression : ParsedExpr)
    (control : ParsedMaskExecutionControl) (hsm nf reduced : Bool)
    (accesses : ParsedMaskedIntegerAccesses) (write : PreparedParsedMaskedWrite)
    (lowered : ParsedExpr.toDirectMaskedIntegerAccessesInLine? expression
      (cendInitialPERegisters x).maskRegisters control.directive hsm control.context.group
      control.context.l2b control.context.l1b control.context.mab control.context.pe cycle
      control.context.bar0 control.context.bar1 control.context.tWord = some accesses)
    (prepared : prepareParsedMaskedWriteWithForwarding (cendInitialPERegisters x)
      cendPoisonSlots cycle accesses reduced = .ok write) :
    ∀ (width : PEMemory.Width) (address : Fin Bank.lm1.capacity),
      write.destination = some ⟨Bank.lm1, width, address⟩ →
        address.val % PEMemory.count Bank.lm1 width = 0 := by
  obtain ⟨operand, -, resolved⟩ :=
    ParsedExpr.toDirectMaskedIntegerAccessesInLine?_destination_provenance expression
      (cendInitialPERegisters x).maskRegisters control.directive hsm control.context.group
      control.context.l2b control.context.l1b control.context.mab control.context.pe cycle
      control.context.bar0 control.context.bar1 control.context.tWord accesses lowered
  exact prepareParsedMaskedWriteWithForwarding_destination_aligned
    (cendInitialPERegisters x) cendPoisonSlots cycle accesses reduced write prepared
    (cendResolvedDestination_count_aligned operand control.context.pe cycle
      control.context.bar0 control.context.bar1 control.context.tWord accesses.destination
      resolved)

/-- The multiple-destination branch: the head write and every replicated copy have
aligned LM1 destinations. -/
theorem cendMultiplePreparedWrites_lm1Aligned
    (x : BitVec 64) (cycle : Fin 4) (expression : ParsedExpr)
    (control : ParsedMaskExecutionControl) (hsm nf reduced : Bool)
    (access : ParsedMaskedIntegerAccesses) (rest : List ParsedMaskedIntegerAccesses)
    (write : PreparedParsedMaskedWrite)
    (lowered : ParsedExpr.toDirectMaskedIntegerWritesInLine? expression
      (cendInitialPERegisters x).maskRegisters control.directive hsm control.context.group
      control.context.l2b control.context.l1b control.context.mab control.context.pe cycle
      control.context.bar0 control.context.bar1 control.context.tWord = some (access :: rest))
    (prepared : prepareParsedMaskedWriteWithForwarding (cendInitialPERegisters x)
      cendPoisonSlots cycle access reduced = .ok write) :
    ∀ item ∈ write :: replicatePreparedIntegerResult rest write,
      ∀ (width : PEMemory.Width) (address : Fin Bank.lm1.capacity),
        item.destination = some ⟨Bank.lm1, width, address⟩ →
          address.val % PEMemory.count Bank.lm1 width = 0 := by
  have provenance := toDirectMaskedIntegerWritesInLine?_mem_provenance expression
    (cendInitialPERegisters x).maskRegisters control.directive hsm control.context.group
    control.context.l2b control.context.l1b control.context.mab control.context.pe cycle
    control.context.bar0 control.context.bar1 control.context.tWord (access :: rest) lowered
  have aligned : ∀ other ∈ access :: rest,
      other.destination.address.val %
        PEMemory.count other.destination.bank other.destination.width = 0 := by
    intro other member
    obtain ⟨operand, -, resolved⟩ := provenance other member
    exact cendResolvedDestination_count_aligned operand control.context.pe cycle
      control.context.bar0 control.context.bar1 control.context.tWord other.destination resolved
  intro item member width address destination
  rcases List.mem_cons.mp member with same | later
  · subst item
    exact prepareParsedMaskedWriteWithForwarding_destination_aligned
      (cendInitialPERegisters x) cendPoisonSlots cycle access reduced write prepared
      (aligned access (by simp)) width address destination
  · obtain ⟨other, otherMem, itemDestination⟩ :=
      replicatePreparedIntegerResult_destination_mem rest write later
    rw [itemDestination] at destination
    have same : other.destination = ⟨Bank.lm1, width, address⟩ := Option.some.inj destination
    have otherAligned := aligned other (List.mem_cons_of_mem _ otherMem)
    rw [same] at otherAligned
    exact otherAligned

/-- The memory-then-OMR branch: the memory write's LM1 destination is aligned and
the OMR write has no destination. -/
theorem cendMemoryThenInputPreparedWrites_lm1Aligned
    (x : BitVec 64) (cycle : Fin 4) (expression : ParsedExpr)
    (control : ParsedMaskExecutionControl) (hsm nf reduced : Bool)
    (accesses : ParsedIntegerMaskMemoryThenInputAccesses)
    (flushSelection : Option PEWordSelection)
    (memoryWrites : List PreparedParsedMaskedWrite) (omrWrite : PreparedParsedMaskedWrite)
    (resolvedMemory : CendDestResolvesAt control.context.pe cycle control.context.bar0
      control.context.bar1 control.context.tWord expression accesses.memory)
    (prepared : prepareParsedIntegerMaskMemoryThenInputALUWritesWithForwarding
      (cendInitialPERegisters x) cendPoisonSlots cycle accesses flushSelection reduced
      = .ok (memoryWrites, omrWrite)) :
    ∀ item ∈ memoryWrites ++ [omrWrite],
      ∀ (width : PEMemory.Width) (address : Fin Bank.lm1.capacity),
        item.destination = some ⟨Bank.lm1, width, address⟩ →
          address.val % PEMemory.count Bank.lm1 width = 0 := by
  obtain ⟨bus, flags, writesEq, omrEq⟩ :=
    prepareParsedIntegerMaskMemoryThenInputALUWritesWithForwarding_shape
      (cendInitialPERegisters x) cendPoisonSlots cycle accesses flushSelection reduced
      memoryWrites omrWrite prepared
  obtain ⟨operand, resolved, -⟩ := resolvedMemory
  rw [writesEq]
  intro item member width address destination
  rcases List.mem_append.mp member with earlier | later
  · rw [List.mem_singleton] at earlier
    subst item
    have same : accesses.memory = ⟨Bank.lm1, width, address⟩ := Option.some.inj destination
    have align := parsedOperand_toDirectMemoryAccessMode_count_aligned operand true
      control.context.pe cycle control.context.bar0 control.context.bar1 control.context.tWord
      accesses.memory resolved
    rw [same] at align
    exact align
  · rw [List.mem_singleton] at later
    subst item
    rw [omrEq] at destination
    exact absurd destination (by simp)

/-- The OMR-then-memory branch: the memory write's LM1 destination is aligned and
the OMR write has no destination. -/
theorem cendInputThenMemoryPreparedWrites_lm1Aligned
    (x : BitVec 64) (cycle : Fin 4) (expression : ParsedExpr)
    (control : ParsedMaskExecutionControl) (hsm nf reduced : Bool)
    (accesses : ParsedIntegerMaskInputThenMemoryAccesses)
    (flushSelection : Option PEWordSelection)
    (memoryWrites : List PreparedParsedMaskedWrite) (omrWrite : PreparedParsedMaskedWrite)
    (resolvedMemory : CendDestResolvesAt control.context.pe cycle control.context.bar0
      control.context.bar1 control.context.tWord expression accesses.memory)
    (prepared : prepareParsedIntegerMaskInputThenMemoryALUWritesWithForwarding
      (cendInitialPERegisters x) cendPoisonSlots cycle accesses control.directive hsm
      flushSelection reduced = .ok (memoryWrites, omrWrite)) :
    ∀ item ∈ memoryWrites,
      ∀ (width : PEMemory.Width) (address : Fin Bank.lm1.capacity),
        item.destination = some ⟨Bank.lm1, width, address⟩ →
          address.val % PEMemory.count Bank.lm1 width = 0 := by
  obtain ⟨bus, flags, memorySelection, writesEq, producerEq⟩ :=
    prepareParsedIntegerMaskInputThenMemoryALUWritesWithForwarding_shape
      (cendInitialPERegisters x) cendPoisonSlots cycle accesses control.directive hsm
      flushSelection reduced memoryWrites omrWrite prepared
  obtain ⟨operand, resolved, -⟩ := resolvedMemory
  rw [writesEq]
  intro item member width address destination
  rcases List.mem_cons.mp member with rfl | later
  · have hnone : (⟨none, some (accesses.destination, cycle, flags), bus,
        ⟨accesses.omrSelection, true⟩⟩ : PreparedParsedMaskedWrite).destination = none := rfl
    rw [hnone] at destination
    exact absurd destination (by simp)
  · rw [List.mem_singleton] at later
    subst item
    have same : accesses.memory = ⟨Bank.lm1, width, address⟩ := Option.some.inj destination
    have align := parsedOperand_toDirectMemoryAccessMode_count_aligned operand true
      control.context.pe cycle control.context.bar0 control.context.bar1 control.context.tWord
      accesses.memory resolved
    rw [same] at align
    exact align

theorem cendMemoryThenInput_memory_provenance_opaque
    (expression : ParsedExpr) (registers : ProofsLean.MNCore.Masks.RegisterFile)
    (directive : ParsedMaskDirective) (hasSingleLineMask : Bool)
    (group : Fin 4) (l2b : Fin 2) (l1b : Fin 8) (mab : Fin 16)
    (pe cycle : Fin 4) (bar0 bar1 : BitVec 12) (tWord : BitVec 32)
    (name : ParsedAluName) (precision : ParsedPrecision) (unsigned : Bool)
    (arg : Option (Fin 256))
    (operation : expression.op = .alu name (some precision) unsigned arg)
    (accesses : ParsedIntegerMaskMemoryThenInputAccesses)
    (lowered : parsedIntegerMaskMemoryThenInputExprAccessesInLine? expression registers
      directive hasSingleLineMask group l2b l1b mab pe cycle bar0 bar1 tWord = some accesses) :
    CendDestResolvesAt pe cycle bar0 bar1 tWord expression accesses.memory := by
  obtain ⟨op, sources, destinations, flush, text⟩ := expression
  exact memoryThenInput_memory_provenance op sources destinations flush text registers directive
    hasSingleLineMask group l2b l1b mab pe cycle bar0 bar1 tWord name precision unsigned arg
    operation accesses lowered

theorem cendInputThenMemory_memory_provenance_opaque
    (expression : ParsedExpr) (registers : ProofsLean.MNCore.Masks.RegisterFile)
    (directive : ParsedMaskDirective) (hasSingleLineMask : Bool)
    (group : Fin 4) (l2b : Fin 2) (l1b : Fin 8) (mab : Fin 16)
    (pe cycle : Fin 4) (bar0 bar1 : BitVec 12) (tWord : BitVec 32)
    (name : ParsedAluName) (precision : ParsedPrecision) (unsigned : Bool)
    (arg : Option (Fin 256))
    (operation : expression.op = .alu name (some precision) unsigned arg)
    (accesses : ParsedIntegerMaskInputThenMemoryAccesses)
    (lowered : parsedIntegerMaskInputThenMemoryExprAccessesInLine? expression registers
      directive hasSingleLineMask group l2b l1b mab pe cycle bar0 bar1 tWord = some accesses) :
    CendDestResolvesAt pe cycle bar0 bar1 tWord expression accesses.memory := by
  obtain ⟨op, sources, destinations, flush, text⟩ := expression
  obtain ⟨resolved, member⟩ := inputThenMemory_memory_provenance op sources destinations flush
    text registers directive hasSingleLineMask group l2b l1b mab pe cycle bar0 bar1 tWord
    name precision unsigned arg operation accesses lowered
  exact ⟨accesses.memoryOperand, resolved, member⟩

theorem cendPlainCycleLm1Aligned_general
    (x : BitVec 64) (name : ParsedAluName) (precision : ParsedPrecision) (unsigned : Bool)
    (arg : Option (Fin 256)) (sources destinations : List ParsedOperand)
    (flush : Option ParsedMask) (text : String) (directive : ParsedMaskDirective)
    (elapsed : Nat) (hsm noForward reduced : Bool) (cycle : Fin 4)
    (nextSlots : ProofsLean.MNCore.Forwarding.Slots)
    (writes : List PreparedParsedMaskedWrite)
    (slots : ProofsLean.MNCore.Forwarding.Slots)
    (expression : ParsedExpr) (control : ParsedMaskExecutionControl)
    (operation : expression.op = .alu name (some precision) unsigned arg)
    (hcontext : control.context = ParsedIntegerContext.ofLinearIndex cendPE)
    (prep : prepareParsedIntegerALUExprCycle (cendInitialPERegisters x) cendPoisonSlots
      nextSlots expression control hsm noForward reduced cycle = .ok (writes, slots)) :
    ∀ write ∈ writes, ∀ (width : PEMemory.Width) (address : Fin Bank.lm1.capacity),
      write.destination = some ⟨Bank.lm1, width, address⟩ →
        address.val % PEMemory.count Bank.lm1 width = 0 := by
  unfold prepareParsedIntegerALUExprCycle at prep
  rw [operation] at prep
  dsimp only at prep
  cases hdirect : ParsedExpr.toDirectMaskedIntegerAccessesInLine? expression
      (cendInitialPERegisters x).maskRegisters control.directive hsm control.context.group
      control.context.l2b control.context.l1b control.context.mab control.context.pe cycle
      control.context.bar0 control.context.bar1 control.context.tWord with
  | some accesses =>
      rw [hdirect] at prep
      dsimp only at prep
      cases hprepared : prepareParsedMaskedWriteWithForwarding (cendInitialPERegisters x)
          cendPoisonSlots cycle accesses reduced with
      | failure => rw [hprepared] at prep; exact absurd prep (by simp)
      | unknown => rw [hprepared] at prep; exact absurd prep (by simp)
      | ok write =>
          rw [hprepared] at prep
          dsimp only at prep
          cases hupdated : updateParsedIntegerALUForwardingCycle nextSlots cycle (.ok write)
              noForward with
          | failure => rw [hupdated] at prep; exact absurd prep (by simp)
          | unknown => rw [hupdated] at prep; exact absurd prep (by simp)
          | ok slots' =>
              rw [hupdated] at prep
              dsimp only at prep
              simp only [StepResult.ok.injEq, Prod.mk.injEq] at prep
              rw [← prep.1]
              intro item member width address destination
              rw [List.mem_singleton] at member
              subst item
              exact cendDirectPreparedWrite_lm1Aligned x cycle expression control hsm
                noForward reduced accesses write hdirect hprepared width address destination
  | none =>
      rw [hdirect] at prep
      dsimp only at prep
      cases hmultiple : ParsedExpr.toDirectMaskedIntegerWritesInLine? expression
          (cendInitialPERegisters x).maskRegisters control.directive hsm control.context.group
          control.context.l2b control.context.l1b control.context.mab control.context.pe cycle
          control.context.bar0 control.context.bar1 control.context.tWord with
      | some accessList =>
          cases accessList with
          | nil => rw [hmultiple] at prep; exact absurd prep (by simp)
          | cons access rest =>
              rw [hmultiple] at prep
              dsimp only at prep
              cases hprepared : prepareParsedMaskedWriteWithForwarding
                  (cendInitialPERegisters x) cendPoisonSlots cycle access reduced with
              | failure => rw [hprepared] at prep; exact absurd prep (by simp)
              | unknown => rw [hprepared] at prep; exact absurd prep (by simp)
              | ok write =>
                  rw [hprepared] at prep
                  dsimp only at prep
                  cases hupdated : updateParsedIntegerALUForwardingCycle nextSlots cycle
                      (.ok write) noForward with
                  | failure => rw [hupdated] at prep; exact absurd prep (by simp)
                  | unknown => rw [hupdated] at prep; exact absurd prep (by simp)
                  | ok slots' =>
                      rw [hupdated] at prep
                      dsimp only at prep
                      simp only [StepResult.ok.injEq, Prod.mk.injEq] at prep
                      rw [← prep.1]
                      exact cendMultiplePreparedWrites_lm1Aligned x cycle expression control
                        hsm noForward reduced access rest write hmultiple hprepared
      | none =>
          rw [hmultiple] at prep
          dsimp only at prep
          cases homr : parsedIntegerMaskExprAccessesInLine? expression
              (cendInitialPERegisters x).maskRegisters control.directive hsm
              control.context.pe cycle control.context.bar0 control.context.bar1
              control.context.tWord with
          | some accesses =>
              rw [homr] at prep
              dsimp only at prep
              cases hflush : resolveFlushSelection? expression.flush
                  (cendInitialPERegisters x).maskRegisters cycle with
              | none => rw [hflush] at prep; exact absurd prep (by simp)
              | some flushSelection =>
                  rw [hflush] at prep
                  dsimp only at prep
                  cases hprepared : prepareParsedIntegerMaskALUWriteWithForwarding
                      (cendInitialPERegisters x) cendPoisonSlots cycle accesses
                      flushSelection reduced with
                  | failure => rw [hprepared] at prep; exact absurd prep (by simp)
                  | unknown => rw [hprepared] at prep; exact absurd prep (by simp)
                  | ok write =>
                      rw [hprepared] at prep
                      dsimp only at prep
                      cases hupdated : updateParsedIntegerALUForwardingCycle nextSlots cycle
                          (.ok write) noForward with
                      | failure => rw [hupdated] at prep; exact absurd prep (by simp)
                      | unknown => rw [hupdated] at prep; exact absurd prep (by simp)
                      | ok slots' =>
                          rw [hupdated] at prep
                          dsimp only at prep
                          simp only [StepResult.ok.injEq, Prod.mk.injEq] at prep
                          rw [← prep.1]
                          intro item member width address destination
                          rw [List.mem_singleton] at member
                          subst item
                          exact cendNoDestination_lm1Aligned write
                            (prepareParsedIntegerMaskALUWriteWithForwarding_destination_none
                              (cendInitialPERegisters x) cendPoisonSlots cycle accesses
                              flushSelection reduced write hprepared)
                            width address destination
          | none =>
              rw [homr] at prep
              dsimp only at prep
              cases hnoWrite : parsedIntegerNoWriteExprAccessesInLine? expression
                  (cendInitialPERegisters x).maskRegisters control.context.pe cycle
                  control.context.group control.context.l2b control.context.l1b
                  control.context.mab control.context.bar0 control.context.bar1
                  control.context.tWord with
              | some accesses =>
                  rw [hnoWrite] at prep
                  dsimp only at prep
                  cases hprepared : prepareParsedIntegerNoWriteALUWithForwarding
                      (cendInitialPERegisters x) cendPoisonSlots cycle accesses reduced with
                  | failure => rw [hprepared] at prep; exact absurd prep (by simp)
                  | unknown => rw [hprepared] at prep; exact absurd prep (by simp)
                  | ok write =>
                      rw [hprepared] at prep
                      dsimp only at prep
                      cases hupdated : updateParsedIntegerALUForwardingCycle nextSlots cycle
                          (.ok write) noForward with
                      | failure => rw [hupdated] at prep; exact absurd prep (by simp)
                      | unknown => rw [hupdated] at prep; exact absurd prep (by simp)
                      | ok slots' =>
                          rw [hupdated] at prep
                          dsimp only at prep
                          simp only [StepResult.ok.injEq, Prod.mk.injEq] at prep
                          rw [← prep.1]
                          intro item member width address destination
                          rw [List.mem_singleton] at member
                          subst item
                          exact cendNoDestination_lm1Aligned write
                            (prepareParsedIntegerNoWriteALUWithForwarding_destination_none
                              (cendInitialPERegisters x) cendPoisonSlots cycle accesses reduced
                              write hprepared)
                            width address destination
              | none =>
                  rw [hnoWrite] at prep
                  dsimp only at prep
                  cases hbar : parsedIntegerBarExprAccessesInLine? expression
                      (cendInitialPERegisters x).maskRegisters control.directive hsm
                      control.context.group control.context.l2b control.context.l1b
                      control.context.mab control.context.pe cycle control.context.bar0
                      control.context.bar1 control.context.tWord with
                  | some accesses =>
                      rw [hbar] at prep
                      dsimp only at prep
                      cases hprepared : prepareParsedIntegerBarALUWithForwarding
                          (cendInitialPERegisters x) cendPoisonSlots cycle accesses reduced with
                      | failure => rw [hprepared] at prep; exact absurd prep (by simp)
                      | unknown => rw [hprepared] at prep; exact absurd prep (by simp)
                      | ok write =>
                          rw [hprepared] at prep
                          dsimp only at prep
                          cases hupdated : updateParsedIntegerALUForwardingCycle nextSlots
                              cycle (.ok write) noForward with
                          | failure => rw [hupdated] at prep; exact absurd prep (by simp)
                          | unknown => rw [hupdated] at prep; exact absurd prep (by simp)
                          | ok slots' =>
                              rw [hupdated] at prep
                              dsimp only at prep
                              simp only [StepResult.ok.injEq, Prod.mk.injEq] at prep
                              rw [← prep.1]
                              intro item member width address destination
                              rw [List.mem_singleton] at member
                              subst item
                              exact cendNoDestination_lm1Aligned write
                                (prepareParsedIntegerBarALUWithForwarding_destination_none
                                  (cendInitialPERegisters x) cendPoisonSlots cycle accesses
                                  reduced write hprepared)
                                width address destination
                  | none =>
                      rw [hbar] at prep
                      dsimp only at prep
                      cases hinput : parsedIntegerMaskInputExprAccessesInLine? expression
                          (cendInitialPERegisters x).maskRegisters control.directive hsm
                          control.context.group control.context.l2b control.context.l1b
                          control.context.mab control.context.pe cycle control.context.bar0
                          control.context.bar1 control.context.tWord with
                      | some accesses =>
                          rw [hinput] at prep
                          dsimp only at prep
                          cases hflush : resolveFlushSelection? expression.flush
                              (cendInitialPERegisters x).maskRegisters cycle with
                          | none => rw [hflush] at prep; exact absurd prep (by simp)
                          | some flushSelection =>
                              rw [hflush] at prep
                              dsimp only at prep
                              cases hprepared :
                                  prepareParsedIntegerMaskInputALUWriteWithForwarding
                                    (cendInitialPERegisters x) cendPoisonSlots cycle accesses
                                    flushSelection reduced with
                              | failure => rw [hprepared] at prep; exact absurd prep (by simp)
                              | unknown => rw [hprepared] at prep; exact absurd prep (by simp)
                              | ok write =>
                                  rw [hprepared] at prep
                                  dsimp only at prep
                                  cases hupdated :
                                      updateParsedIntegerALUForwardingCycle nextSlots cycle
                                        (.ok write) noForward with
                                  | failure => rw [hupdated] at prep; exact absurd prep (by simp)
                                  | unknown => rw [hupdated] at prep; exact absurd prep (by simp)
                                  | ok slots' =>
                                      rw [hupdated] at prep
                                      dsimp only at prep
                                      simp only [StepResult.ok.injEq, Prod.mk.injEq] at prep
                                      rw [← prep.1]
                                      intro item member width address destination
                                      rw [List.mem_singleton] at member
                                      subst item
                                      exact cendNoDestination_lm1Aligned write
                                        (prepareParsedIntegerMaskInputALUWriteWithForwarding_destination_none
                                          (cendInitialPERegisters x) cendPoisonSlots cycle
                                          accesses flushSelection reduced write hprepared)
                                        width address destination
                      | none =>
                          rw [hinput] at prep
                          dsimp only at prep
                          cases hmixed :
                              parsedIntegerMaskMemoryThenInputExprAccessesInLine? expression
                                (cendInitialPERegisters x).maskRegisters control.directive
                                hsm control.context.group control.context.l2b
                                control.context.l1b control.context.mab control.context.pe
                                cycle control.context.bar0 control.context.bar1
                                control.context.tWord with
                          | some accesses =>
                              rw [hmixed] at prep
                              dsimp only at prep
                              cases hflush : resolveFlushSelection? expression.flush
                                  (cendInitialPERegisters x).maskRegisters cycle with
                              | none => rw [hflush] at prep; exact absurd prep (by simp)
                              | some flushSelection =>
                                  rw [hflush] at prep
                                  dsimp only at prep
                                  cases hprepared :
                                      prepareParsedIntegerMaskMemoryThenInputALUWritesWithForwarding
                                        (cendInitialPERegisters x) cendPoisonSlots cycle
                                        accesses flushSelection reduced with
                                  | failure => rw [hprepared] at prep; exact absurd prep (by simp)
                                  | unknown => rw [hprepared] at prep; exact absurd prep (by simp)
                                  | ok pair =>
                                      obtain ⟨memoryWrites, omrWrite⟩ := pair
                                      rw [hprepared] at prep
                                      dsimp only at prep
                                      cases hupdated :
                                          updateParsedIntegerALUForwardingCycle nextSlots
                                            cycle (.ok omrWrite) noForward with
                                      | failure => rw [hupdated] at prep; exact absurd prep (by simp)
                                      | unknown => rw [hupdated] at prep; exact absurd prep (by simp)
                                      | ok slots' =>
                                          rw [hupdated] at prep
                                          dsimp only at prep
                                          simp only [StepResult.ok.injEq, Prod.mk.injEq]
                                            at prep
                                          rw [← prep.1]
                                          exact cendMemoryThenInputPreparedWrites_lm1Aligned
                                            x cycle expression control hsm noForward reduced
                                            accesses flushSelection memoryWrites omrWrite
                                            (cendMemoryThenInput_memory_provenance_opaque
                                              expression (cendInitialPERegisters x).maskRegisters
                                              control.directive hsm control.context.group
                                              control.context.l2b control.context.l1b
                                              control.context.mab control.context.pe cycle
                                              control.context.bar0 control.context.bar1
                                              control.context.tWord name precision unsigned
                                              arg operation accesses hmixed)
                                            hprepared
                          | none =>
                              rw [hmixed] at prep
                              dsimp only at prep
                              cases hreverse :
                                  parsedIntegerMaskInputThenMemoryExprAccessesInLine?
                                    expression (cendInitialPERegisters x).maskRegisters
                                    control.directive hsm control.context.group
                                    control.context.l2b control.context.l1b
                                    control.context.mab control.context.pe cycle
                                    control.context.bar0 control.context.bar1
                                    control.context.tWord with
                              | some accesses =>
                                  rw [hreverse] at prep
                                  dsimp only at prep
                                  cases hflush : resolveFlushSelection? expression.flush
                                      (cendInitialPERegisters x).maskRegisters cycle with
                                  | none => rw [hflush] at prep; exact absurd prep (by simp)
                                  | some flushSelection =>
                                      rw [hflush] at prep
                                      dsimp only at prep
                                      cases hprepared :
                                          prepareParsedIntegerMaskInputThenMemoryALUWritesWithForwarding
                                            (cendInitialPERegisters x) cendPoisonSlots cycle
                                            accesses control.directive hsm flushSelection
                                            reduced with
                                      | failure => rw [hprepared] at prep; exact absurd prep (by simp)
                                      | unknown => rw [hprepared] at prep; exact absurd prep (by simp)
                                      | ok pair =>
                                          obtain ⟨memoryWrites, omrWrite⟩ := pair
                                          rw [hprepared] at prep
                                          dsimp only at prep
                                          cases hupdated :
                                              updateParsedIntegerALUForwardingCycle
                                                nextSlots cycle (.ok omrWrite) noForward with
                                          | failure => rw [hupdated] at prep; exact absurd prep (by simp)
                                          | unknown => rw [hupdated] at prep; exact absurd prep (by simp)
                                          | ok slots' =>
                                              rw [hupdated] at prep
                                              dsimp only at prep
                                              simp only [StepResult.ok.injEq,
                                                Prod.mk.injEq] at prep
                                              rw [← prep.1]
                                              exact cendInputThenMemoryPreparedWrites_lm1Aligned
                                                x cycle expression control hsm noForward
                                                reduced accesses flushSelection memoryWrites
                                                omrWrite
                                                (cendInputThenMemory_memory_provenance_opaque
                                                  expression
                                                  (cendInitialPERegisters x).maskRegisters
                                                  control.directive hsm control.context.group
                                                  control.context.l2b control.context.l1b
                                                  control.context.mab control.context.pe cycle
                                                  control.context.bar0 control.context.bar1
                                                  control.context.tWord name precision
                                                  unsigned arg operation accesses hreverse)
                                                hprepared
                              | none =>
                                  rw [hreverse] at prep
                                  dsimp only at prep
                                  split at prep
                                  · exact absurd prep (by simp)
                                  · exact absurd prep (by simp)

/-! ## 4. The half-mix commit, the four-cycle lift and the plain-family obligation -/

/-- The high-half projection of a nested half-mix. -/
theorem cendHalfMix_assoc_high (hi lo lo' : BitVec 32) :
    cendHalfMix (cendHalfMix hi lo) lo' = cendHalfMix hi lo' := by
  unfold cendHalfMix
  have h : ((hi &&& 0xffff0000) ||| (lo &&& 0x0000ffff)) &&& 0xffff0000 =
      hi &&& 0xffff0000 := by
    rw [BitVec.and_or_distrib_right, BitVec.and_assoc, BitVec.and_assoc]
    rw [show (0xffff0000 : BitVec 32) &&& 0xffff0000 = 0xffff0000 from by decide,
      show (0x0000ffff : BitVec 32) &&& 0xffff0000 = 0 from by decide]
    simp
  exact congrArg (fun word => word ||| (lo' &&& 0x0000ffff)) h

/-- The low-half projection of a nested half-mix. -/
theorem cendHalfMix_assoc_low (hi hi' lo : BitVec 32) :
    cendHalfMix hi (cendHalfMix hi' lo) = cendHalfMix hi lo := by
  unfold cendHalfMix
  have h : ((hi' &&& 0xffff0000) ||| (lo &&& 0x0000ffff)) &&& 0x0000ffff =
      lo &&& 0x0000ffff := by
    rw [BitVec.and_or_distrib_right, BitVec.and_assoc, BitVec.and_assoc]
    rw [show (0xffff0000 : BitVec 32) &&& 0x0000ffff = 0 from by decide,
      show (0x0000ffff : BitVec 32) &&& 0x0000ffff = 0x0000ffff from by decide]
    simp
  exact congrArg (fun word => (hi &&& 0xffff0000) ||| word) h

/-- **The merge of two half-mixes with a half mask is a half-mix.** -/
theorem mergeSelectedWord_halfMix_mem_halfMix (x : BitVec 64) (old data mask : BitVec 32)
    (hold : old ∈ cendHalfMixWords x) (hdata : data ∈ cendHalfMixWords x)
    (hmask : mask = 0 ∨ mask = BitVec.allOnes 32 ∨
      mask = 0xffff0000 ∨ mask = 0x0000ffff) :
    mergeSelectedWord old data mask ∈ cendHalfMixWords x := by
  obtain ⟨hi, hhi, lo, hlo, rfl⟩ := cendHalfMixWords_exists x old hold
  obtain ⟨hi', hhi', lo', hlo', hdataEq⟩ := cendHalfMixWords_exists x data hdata
  rcases hmask with rfl | rfl | rfl | rfl
  · rw [show mergeSelectedWord (cendHalfMix hi lo) data 0 = cendHalfMix hi lo from by
      unfold mergeSelectedWord
      rw [show ~~~(0 : BitVec 32) = BitVec.allOnes 32 from by decide]
      rw [show cendHalfMix hi lo &&& (BitVec.allOnes 32) = cendHalfMix hi lo from
        BitVec.and_allOnes]
      rw [show data &&& (0 : BitVec 32) = 0 from BitVec.and_zero]
      rw [show (cendHalfMix hi lo) ||| (0 : BitVec 32) = cendHalfMix hi lo from BitVec.or_zero]]
    exact cendHalfMixWords_mem x hi lo hhi hlo
  · rw [show mergeSelectedWord (cendHalfMix hi lo) data (BitVec.allOnes 32) =
        cendHalfMix data data from by
      unfold mergeSelectedWord
      rw [show ~~~(BitVec.allOnes 32 : BitVec 32) = 0 from by decide]
      rw [show cendHalfMix hi lo &&& (0 : BitVec 32) = 0 from BitVec.and_zero]
      rw [show data &&& (BitVec.allOnes 32) = data from BitVec.and_allOnes]
      rw [show (0 : BitVec 32) ||| data = data from BitVec.zero_or]
      unfold cendHalfMix
      rw [← BitVec.and_or_distrib_left,
        show (0xffff0000 : BitVec 32) ||| 0x0000ffff = BitVec.allOnes 32 from by decide]
      exact (BitVec.and_allOnes).symm]
    rw [cendHalfMix_self]
    exact hdata
  · rw [show mergeSelectedWord (cendHalfMix hi lo) data 0xffff0000 =
        cendHalfMix data lo from by
      unfold mergeSelectedWord
      rw [show ~~~(0xffff0000 : BitVec 32) = 0x0000ffff from by decide,
        cendHalfMix_low]
      unfold cendHalfMix
      exact BitVec.or_comm _ _]
    rw [hdataEq, cendHalfMix_assoc_high]
    exact cendHalfMixWords_mem x hi' lo hhi' hlo
  · rw [show mergeSelectedWord (cendHalfMix hi lo) data 0x0000ffff =
        cendHalfMix hi data from by
      unfold mergeSelectedWord
      rw [show ~~~(0x0000ffff : BitVec 32) = 0xffff0000 from by decide,
        cendHalfMix_high]
      unfold cendHalfMix
      rfl]
    rw [hdataEq, cendHalfMix_assoc_low]
    exact cendHalfMixWords_mem x hi lo' hhi hlo'

/-- **The commit preserves the half-mix value set at word `0`/`1`**, for data
arguments that are themselves half-mixes. -/
theorem commitParsedMaskedWrites_lm1_halfMix_halfMix
    (x : BitVec 64) (writes : List PreparedParsedMaskedWrite)
    (target : Fin Bank.lm1.capacity) (targetLt : target.val < 2)
    (dataOk : ∀ write ∈ writes, ∀ i : Fin 4, i.val < 2 →
      write.data i ∈ cendHalfMixWords x)
    (destAligned : ∀ write ∈ writes, ∀ (width : PEMemory.Width)
      (address : Fin Bank.lm1.capacity),
      write.destination = some ⟨Bank.lm1, width, address⟩ →
        address.val % PEMemory.count Bank.lm1 width = 0) :
    ∀ files : IntegerRegisterFiles, files.lm1 target ∈ cendHalfMixWords x →
      (commitParsedMaskedWrites files writes).lm1 target ∈ cendHalfMixWords x := by
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
                cendHalfMixWords x
            simp only [welcomeCommitStep]
            exact hold
        | none =>
            cases destination with
            | none =>
                show (welcomeCommitStep files
                  ⟨none, none, data, selection⟩).lm1 target ∈ cendHalfMixWords x
                simp only [welcomeCommitStep]
                exact hold
            | some access =>
                obtain ⟨bank, width, address⟩ := access
                cases bank with
                | lm1 =>
                    show (welcomeCommitStep files
                      ⟨some ⟨Bank.lm1, width, address⟩, none, data, selection⟩).lm1
                        target ∈ cendHalfMixWords x
                    simp only [welcomeCommitStep]
                    rw [writeDirectAccessMasked_lm1_apply]
                    by_cases within : PEMemory.distance Bank.lm1 address target <
                        PEMemory.count Bank.lm1 width
                    · rw [PEMemory.writeWordsMasked_at _ width files.lm1 address target data
                        selection.flags selection.longLong within]
                      apply mergeSelectedWord_halfMix_mem_halfMix
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
                        target ∈ cendHalfMixWords x
                    simp only [welcomeCommitStep]
                    rw [writeDirectAccessMasked_lm1_eq _ _ _ _ _ _ (by decide)]
                    exact hold
                | grf0 =>
                    show (welcomeCommitStep files
                      ⟨some ⟨Bank.grf0, width, address⟩, none, data, selection⟩).lm1
                        target ∈ cendHalfMixWords x
                    simp only [welcomeCommitStep]
                    rw [writeDirectAccessMasked_lm1_eq _ _ _ _ _ _ (by decide)]
                    exact hold
                | grf1 =>
                    show (welcomeCommitStep files
                      ⟨some ⟨Bank.grf1, width, address⟩, none, data, selection⟩).lm1
                        target ∈ cendHalfMixWords x
                    simp only [welcomeCommitStep]
                    rw [writeDirectAccessMasked_lm1_eq _ _ _ _ _ _ (by decide)]
                    exact hold
                | t =>
                    show (welcomeCommitStep files
                      ⟨some ⟨Bank.t, width, address⟩, none, data, selection⟩).lm1
                        target ∈ cendHalfMixWords x
                    simp only [welcomeCommitStep]
                    rw [writeDirectAccessMasked_lm1_eq _ _ _ _ _ _ (by decide)]
                    exact hold

/-- The initial-state corollary of the half-mix commit. -/
theorem commitParsedMaskedWrites_lm1_halfMix_halfMix_zero
    (x : BitVec 64) (writes : List PreparedParsedMaskedWrite)
    (target : Fin Bank.lm1.capacity) (targetLt : target.val < 2)
    (dataOk : ∀ write ∈ writes, ∀ i : Fin 4, i.val < 2 →
      write.data i ∈ cendHalfMixWords x)
    (destAligned : ∀ write ∈ writes, ∀ (width : PEMemory.Width)
      (address : Fin Bank.lm1.capacity),
      write.destination = some ⟨Bank.lm1, width, address⟩ →
        address.val % PEMemory.count Bank.lm1 width = 0)
    (files : IntegerRegisterFiles) (zero : ∀ address, files.lm1 address = 0) :
    (commitParsedMaskedWrites files writes).lm1 target ∈ cendHalfMixWords x :=
  commitParsedMaskedWrites_lm1_halfMix_halfMix x writes target targetLt dataOk destAligned
    files (by rw [zero]; exact cendHalfMixWords_zero x)

/-- **The committed observed word is a half-mix**, given the half-mix data shape
and the alignment of the prepared write list. -/
theorem cendOutputWord0_mem_halfMix_of_commit_halfMix
    (x : BitVec 64) (next : State) (writes : List PreparedParsedMaskedWrite)
    (committed : next.peRegisters cendPE =
      commitParsedMaskedWrites (cendInitialPERegisters x) writes)
    (dataOk : ∀ write ∈ writes, ∀ i : Fin 4, i.val < 2 →
      write.data i ∈ cendHalfMixWords x)
    (destAligned : ∀ write ∈ writes, ∀ (width : PEMemory.Width)
      (address : Fin Bank.lm1.capacity),
      write.destination = some ⟨Bank.lm1, width, address⟩ →
        address.val % PEMemory.count Bank.lm1 width = 0) :
    cendOutputWord0 next ∈ cendHalfMixWords x := by
  unfold cendOutputWord0
  rw [committed]
  exact commitParsedMaskedWrites_lm1_halfMix_halfMix_zero x writes ⟨0, by decide⟩ (by decide)
    dataOk destAligned _ (fun address => cendInitialPERegisters_lm1 x address)

/-- A `.alu` cycle whose precision is not established never succeeds. -/
theorem prepareParsedIntegerALUExprCycle_alu_none_not_ok
    (files : IntegerRegisterFiles) (oldSlots nextSlots : ProofsLean.MNCore.Forwarding.Slots)
    (expression : ParsedExpr) (control : ParsedMaskExecutionControl)
    (hsm nf reduced : Bool) (cycle : Fin 4) (name : ParsedAluName) (unsigned : Bool)
    (arg : Option (Fin 256))
    (operation : expression.op = .alu name none unsigned arg)
    (writes : List PreparedParsedMaskedWrite)
    (slots : ProofsLean.MNCore.Forwarding.Slots) :
    prepareParsedIntegerALUExprCycle files oldSlots nextSlots expression control hsm nf reduced
      cycle ≠ .ok (writes, slots) := by
  unfold prepareParsedIntegerALUExprCycle
  simp only [operation, ParsedExpr.toDirectMaskedIntegerAccessesInLine?,
    ParsedExpr.toDirectMaskedIntegerWritesInLine?, parsedIntegerMaskExprAccessesInLine?,
    parsedIntegerNoWriteExprAccessesInLine?, parsedIntegerBarExprAccessesInLine?,
    parsedIntegerMaskInputExprAccessesInLine?,
    parsedIntegerMaskMemoryThenInputExprAccessesInLine?,
    parsedIntegerMaskInputThenMemoryExprAccessesInLine?]
  cases expression.destinations with
  | nil => simp_all
  | cons head tail =>
      simp_all
      split <;> simp

/-- The four-cycle preparation of a `.alu` row whose precision is not established
never succeeds. -/
theorem prepareParsedIntegerALUExprCycles_alu_none_not_ok
    (files : IntegerRegisterFiles) (oldSlots : ProofsLean.MNCore.Forwarding.Slots)
    (expression : ParsedExpr) (control : ParsedMaskExecutionControl)
    (hsm nf reduced : Bool) (name : ParsedAluName) (unsigned : Bool)
    (arg : Option (Fin 256))
    (operation : expression.op = .alu name none unsigned arg)
    (writes : List PreparedParsedMaskedWrite)
    (slots : ProofsLean.MNCore.Forwarding.Slots) :
    prepareParsedIntegerALUExprCycles files oldSlots oldSlots expression control hsm nf reduced
      ≠ .ok (writes, slots) := by
  intro prep
  obtain ⟨w0, w1, w2, w3, s1, s2, s3, h0, -, -, -, -⟩ :=
    prepareParsedIntegerALUExprCycles_four_general files oldSlots oldSlots expression control
      hsm nf reduced writes slots prep
  exact prepareParsedIntegerALUExprCycle_alu_none_not_ok files oldSlots oldSlots expression
    control hsm nf reduced (0 : Fin 4) name unsigned arg operation w0 s1 h0

/-- **The four-cycle lift of the half-mix data and the LM1 alignment.**  A
singleton plain `.alu` row prepares writes whose first two data words are
half-mixes and whose LM1 destinations are aligned. -/
theorem cendPlainALURow_dataAndAligned
    (x : BitVec 64) (e : NormalizedExpr) (name : ParsedAluName)
    (precision : ParsedPrecision) (unsigned : Bool) (arg : Option (Fin 256))
    (plainE : parsedExprIsPlainIntegerALU e.toParsed = true)
    (operation : e.toParsed.op = .alu name (some precision) unsigned arg)
    (writes : List PreparedParsedMaskedWrite)
    (slots : ProofsLean.MNCore.Forwarding.Slots)
    (bars : List (Bool × BitVec 12))
    (prep : welcomeIntegerPrep (cendInitialState x) cendPE [e.toParsed] =
      .ok (writes, slots, bars)) :
    (∀ write ∈ writes, ∀ i : Fin 4, i.val < 2 → write.data i ∈ cendHalfMixWords x) ∧
      (∀ write ∈ writes, ∀ (width : PEMemory.Width) (address : Fin Bank.lm1.capacity),
        write.destination = some ⟨Bank.lm1, width, address⟩ →
          address.val % PEMemory.count Bank.lm1 width = 0) := by
  have stage : [e.toParsed].filter parsedExprIsIntegerMatrixReadStageInput = [e.toParsed] := by
    rw [List.filter_eq_self]
    intro item member
    rw [List.mem_singleton] at member
    subst member
    exact plain_stageInput e.toParsed plainE
  unfold welcomeIntegerPrep at prep
  rw [stage] at prep
  obtain ⟨outSlots, alu, -⟩ :=
    prepareParsedIntegerMatrixReadLineCycles_singleton_plain_inv
      ((cendInitialState x).peRegisters cendPE)
      (stateForwardingSlots (cendInitialState x) cendPE)
      ((cendInitialState x).matrixRegisters (ParsedIntegerContext.ofLinearIndex cendPE).group
        (ParsedIntegerContext.ofLinearIndex cendPE).l2b
        (ParsedIntegerContext.ofLinearIndex cendPE).l1b)
      e.toParsed (parsedPEHazardControl (cendInitialState x) cendPE) false bars writes slots
      (Or.inl ⟨name, some precision, unsigned, arg, operation⟩) prep
  have slotsEq : stateForwardingSlots (cendInitialState x) cendPE = cendPoisonSlots := by
    funext unit cycleIndex
    exact cendInitialForwardingSlots_poison x cendPE unit cycleIndex
  rw [slotsEq] at alu
  obtain ⟨w0, w1, w2, w3, s1, s2, s3, h0, h1, h2, h3, writesEq⟩ :=
    prepareParsedIntegerALUExprCycles_four_general (cendInitialPERegisters x) cendPoisonSlots
      cendPoisonSlots e.toParsed (parsedPEHazardControl (cendInitialState x) cendPE)
      ([e.toParsed].any parsedExprHasSingleLineWriteMask)
      ([e.toParsed].any fun expression => match expression.op with
        | .noforward => true | _ => false) false writes outSlots alu
  subst writesEq
  have hcontrol : (parsedPEHazardControl (cendInitialState x) cendPE).context =
      ParsedIntegerContext.ofLinearIndex cendPE := rfl
  constructor
  · intro write member i hi
    rcases List.mem_append.mp member with early | late
    · rcases List.mem_append.mp early with early | inTwo
      · rcases List.mem_append.mp early with inZero | inOne
        · exact cendPlainCycleHalfMixData_general x name precision unsigned arg
            e.toParsed.sources e.toParsed.destinations e.toParsed.flush e.toParsed.text
            (cendInitialState x).maskDirective (cendInitialState x).hazardClock
            ([e.toParsed].any parsedExprHasSingleLineWriteMask)
            ([e.toParsed].any fun expression => match expression.op with
              | .noforward => true | _ => false) false (0 : Fin 4) cendPoisonSlots w0 s1 e.toParsed
            (parsedPEHazardControl (cendInitialState x) cendPE) operation hcontrol h0
            write inZero i hi
        · exact cendPlainCycleHalfMixData_general x name precision unsigned arg
            e.toParsed.sources e.toParsed.destinations e.toParsed.flush e.toParsed.text
            (cendInitialState x).maskDirective (cendInitialState x).hazardClock
            ([e.toParsed].any parsedExprHasSingleLineWriteMask)
            ([e.toParsed].any fun expression => match expression.op with
              | .noforward => true | _ => false) false (1 : Fin 4) s1 w1 s2 e.toParsed
            (parsedPEHazardControl (cendInitialState x) cendPE) operation hcontrol h1
            write inOne i hi
      · exact cendPlainCycleHalfMixData_general x name precision unsigned arg
          e.toParsed.sources e.toParsed.destinations e.toParsed.flush e.toParsed.text
          (cendInitialState x).maskDirective (cendInitialState x).hazardClock
          ([e.toParsed].any parsedExprHasSingleLineWriteMask)
          ([e.toParsed].any fun expression => match expression.op with
            | .noforward => true | _ => false) false (2 : Fin 4) s2 w2 s3 e.toParsed
          (parsedPEHazardControl (cendInitialState x) cendPE) operation hcontrol h2
          write inTwo i hi
    · exact cendPlainCycleHalfMixData_general x name precision unsigned arg
        e.toParsed.sources e.toParsed.destinations e.toParsed.flush e.toParsed.text
        (cendInitialState x).maskDirective (cendInitialState x).hazardClock
        ([e.toParsed].any parsedExprHasSingleLineWriteMask)
        ([e.toParsed].any fun expression => match expression.op with
          | .noforward => true | _ => false) false (3 : Fin 4) s3 w3 outSlots e.toParsed
        (parsedPEHazardControl (cendInitialState x) cendPE) operation hcontrol h3
        write late i hi
  · intro write member width address destination
    rcases List.mem_append.mp member with early | late
    · rcases List.mem_append.mp early with early | inTwo
      · rcases List.mem_append.mp early with inZero | inOne
        · exact cendPlainCycleLm1Aligned_general x name precision unsigned arg
            e.toParsed.sources e.toParsed.destinations e.toParsed.flush e.toParsed.text
            (cendInitialState x).maskDirective (cendInitialState x).hazardClock
            ([e.toParsed].any parsedExprHasSingleLineWriteMask)
            ([e.toParsed].any fun expression => match expression.op with
              | .noforward => true | _ => false) false (0 : Fin 4) cendPoisonSlots w0 s1 e.toParsed
            (parsedPEHazardControl (cendInitialState x) cendPE) operation hcontrol h0
            write inZero width address destination
        · exact cendPlainCycleLm1Aligned_general x name precision unsigned arg
            e.toParsed.sources e.toParsed.destinations e.toParsed.flush e.toParsed.text
            (cendInitialState x).maskDirective (cendInitialState x).hazardClock
            ([e.toParsed].any parsedExprHasSingleLineWriteMask)
            ([e.toParsed].any fun expression => match expression.op with
              | .noforward => true | _ => false) false (1 : Fin 4) s1 w1 s2 e.toParsed
            (parsedPEHazardControl (cendInitialState x) cendPE) operation hcontrol h1
            write inOne width address destination
      · exact cendPlainCycleLm1Aligned_general x name precision unsigned arg
          e.toParsed.sources e.toParsed.destinations e.toParsed.flush e.toParsed.text
          (cendInitialState x).maskDirective (cendInitialState x).hazardClock
          ([e.toParsed].any parsedExprHasSingleLineWriteMask)
          ([e.toParsed].any fun expression => match expression.op with
            | .noforward => true | _ => false) false (2 : Fin 4) s2 w2 s3 e.toParsed
          (parsedPEHazardControl (cendInitialState x) cendPE) operation hcontrol h2
          write inTwo width address destination
    · exact cendPlainCycleLm1Aligned_general x name precision unsigned arg
        e.toParsed.sources e.toParsed.destinations e.toParsed.flush e.toParsed.text
        (cendInitialState x).maskDirective (cendInitialState x).hazardClock
        ([e.toParsed].any parsedExprHasSingleLineWriteMask)
        ([e.toParsed].any fun expression => match expression.op with
          | .noforward => true | _ => false) false (3 : Fin 4) s3 w3 outSlots e.toParsed
        (parsedPEHazardControl (cendInitialState x) cendPE) operation hcontrol h3
        write late width address destination


/-! ## 6. Trust report -/

#print axioms cendPlainCycleHalfMixData
#print axioms cendPlainCycleLm1Aligned_general
#print axioms mergeSelectedWord_halfMix_mem_halfMix
#print axioms commitParsedMaskedWrites_lm1_halfMix_halfMix
#print axioms cendPlainALURow_dataAndAligned
