import ProofsLean.ReluOptimal
import ProofsLean.LineExec

/-! # `3.relu`: fold the four per-cycle readbacks and read back the eight words -/

namespace ProofsLean.MNCore

open Issue
open ProofsLean.MNCore.PEMemory

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

/-- Cycle 0 with an arbitrary initial register file.  The read state is fixed
(the executor always reads `readState`), so only the written files change. -/
theorem reluExpr0_cycle0_generic (input : ProofsLean.MNCore.PlusOne.Words)
    (files0 : IntegerRegisterFiles) (outputs : Fin 4 → IntegerALU.Bus) :
    ∃ files bar0 bar1 outputs',
      executeParsedFloatReluAtPE.runCycles (welcomeInitialState input) (welcomeInitialState input)
        reluExpr0 0 false (ParsedIntegerContext.ofLinearIndex 0) (ParsedIntegerContext.ofLinearIndex 0)
        [0] files0 0 0 outputs =
        .ok (files, bar0, bar1, outputs') ∧
      files.lm1 ⟨0, by decide⟩ = reluWord (input ⟨0, by decide⟩) ∧
      files.lm1 ⟨1, by decide⟩ = reluWord (input ⟨1, by decide⟩) ∧
      files.lm0 = files0.lm0 ∧
      bar0 = 0 ∧ bar1 = 0 ∧
      ∀ j : Fin Bank.lm1.capacity, j ≠ ⟨0, by decide⟩ → j ≠ ⟨1, by decide⟩ →
        files.lm1 j = files0.lm1 j := by
  rw [executeParsedFloatReluAtPE.runCycles]
  rw [show ({ (ParsedIntegerContext.ofLinearIndex 0) with cycle := 0 } : ParsedIntegerContext)
      = reluContext 0 0 from rfl]
  rw [reluExpr0_lower_eq_cycle0]
  simp only [reluSrc0]
  rw [reluInitial_readWithForwarding_long0 input]
  have htarget : (welcomeInitialState input).maskDirective.targets.lm1 = false := by
    rw [welcomeInitialState_maskDirective]
    exact welcomeMaskDirective_targets_lm1
  have hentry : (welcomeInitialState input).maskDirective.entry = 0 := rfl
  simp [reluExpr0, reluOp, reluLm1Long0, reluLm0Long0, unpackALUBus,
    parsedOutputAfterFlush, resolveFlushSelection?,
    executeParsedFloatReluAtPE.runCycles.writeDestinations,
    executeParsedFloatReluAtPE.runCycles, writeParsedMslMsrDestination?,
    commitParsedMaskedWrites, ParsedOperand.resolveMemoryWriteSelection?,
    resolveMemoryDirectiveSelection?, welcomeMaskDirective, directiveTargetsBank,
    ParsedIntegerContext.ofLinearIndex, issueBankToRegisterBank,
    ParsedOperand.toDirectMemoryDestination?, ParsedOperand.toDirectMemoryAccess?,
    ParsedOperand.toDirectMemoryAccessMode?, parsedWidth?, parsedRegionAddressAt,
    PEMemory.count, PEMemory.Width.words, PEMemory.Bank.capacity,
    writeDirectAccessMasked, writeRegisterBankMasked, writeWordsMasked, writeWords,
    PEMemory.distance, htarget, hentry,
    mergeSelectedWord, selectedWordMask, Nat.reduceSub, Nat.reduceLT]
  constructor
  · change BitVec.extractLsb' 32 32
      (parsedFloatReluBus .f .relu false
        (⟨input ⟨0, by decide⟩ ++ input ⟨1, by decide⟩, (0 : BitVec 64)⟩ : IntegerALU.Bus)
        (some ⟨input ⟨0, by decide⟩ ++ input ⟨1, by decide⟩, (0 : BitVec 64)⟩)).1.high
      &&& 4294967295#32 = reluWord (input ⟨0, by decide⟩)
    rw [reluBus_high_literal]
    have hff : (4294967295#32 : BitVec 32) = BitVec.allOnes 32 := rfl
    rw [hff]
    simp only [extract_high, extract_low]
    have hx : ∀ x : BitVec 32, x &&& 4294967295#32 = x := by
      intro x
      have hff : (4294967295#32 : BitVec 32) = BitVec.allOnes 32 := by
        apply BitVec.toNat_eq.mpr
        simp [BitVec.toNat_allOnes]
      rw [hff, BitVec.and_allOnes]
    exact hx _
  · constructor
    · change BitVec.extractLsb' 0 32
        (parsedFloatReluBus .f .relu false
          (⟨input ⟨0, by decide⟩ ++ input ⟨1, by decide⟩, (0 : BitVec 64)⟩ : IntegerALU.Bus)
          (some ⟨input ⟨0, by decide⟩ ++ input ⟨1, by decide⟩, (0 : BitVec 64)⟩)).1.high
        &&& 4294967295#32 = reluWord (input ⟨1, by decide⟩)
      rw [reluBus_high_literal]
      have hff : (4294967295#32 : BitVec 32) = BitVec.allOnes 32 := rfl
      rw [hff]
      simp only [extract_high, extract_low]
      have hx : ∀ x : BitVec 32, x &&& 4294967295#32 = x := by
        intro x
        have hff : (4294967295#32 : BitVec 32) = BitVec.allOnes 32 := by
          apply BitVec.toNat_eq.mpr
          simp [BitVec.toNat_allOnes]
        rw [hff, BitVec.and_allOnes]
      exact hx _
    · intro j hj0 hj1 hlt
      omega


/-- Cycle 1 with an arbitrary initial register file.  The read state is fixed
(the executor always reads `readState`), so only the written files change. -/
theorem reluExpr0_cycle1_generic (input : ProofsLean.MNCore.PlusOne.Words)
    (files0 : IntegerRegisterFiles) (outputs : Fin 4 → IntegerALU.Bus) :
    ∃ files bar0 bar1 outputs',
      executeParsedFloatReluAtPE.runCycles (welcomeInitialState input) (welcomeInitialState input)
        reluExpr0 0 false (ParsedIntegerContext.ofLinearIndex 0) (ParsedIntegerContext.ofLinearIndex 0)
        [1] files0 0 0 outputs =
        .ok (files, bar0, bar1, outputs') ∧
      files.lm1 ⟨2, by decide⟩ = reluWord (input ⟨2, by decide⟩) ∧
      files.lm1 ⟨3, by decide⟩ = reluWord (input ⟨3, by decide⟩) ∧
      files.lm0 = files0.lm0 ∧
      bar0 = 0 ∧ bar1 = 0 ∧
      ∀ j : Fin Bank.lm1.capacity, j ≠ ⟨2, by decide⟩ → j ≠ ⟨3, by decide⟩ →
        files.lm1 j = files0.lm1 j := by
  rw [executeParsedFloatReluAtPE.runCycles]
  rw [show ({ (ParsedIntegerContext.ofLinearIndex 0) with cycle := 1 } : ParsedIntegerContext)
      = reluContext 0 1 from rfl]
  rw [reluExpr0_lower_eq_cycle1]
  simp only [reluSrc1]
  rw [reluInitial_readWithForwarding_long1 input]
  have htarget : (welcomeInitialState input).maskDirective.targets.lm1 = false := by
    rw [welcomeInitialState_maskDirective]
    exact welcomeMaskDirective_targets_lm1
  have hentry : (welcomeInitialState input).maskDirective.entry = 0 := rfl
  simp [reluExpr0, reluOp, reluLm1Long0, reluLm0Long0, unpackALUBus,
    parsedOutputAfterFlush, resolveFlushSelection?,
    executeParsedFloatReluAtPE.runCycles.writeDestinations,
    executeParsedFloatReluAtPE.runCycles, writeParsedMslMsrDestination?,
    commitParsedMaskedWrites, ParsedOperand.resolveMemoryWriteSelection?,
    resolveMemoryDirectiveSelection?, welcomeMaskDirective, directiveTargetsBank,
    ParsedIntegerContext.ofLinearIndex, issueBankToRegisterBank,
    ParsedOperand.toDirectMemoryDestination?, ParsedOperand.toDirectMemoryAccess?,
    ParsedOperand.toDirectMemoryAccessMode?, parsedWidth?, parsedRegionAddressAt,
    PEMemory.count, PEMemory.Width.words, PEMemory.Bank.capacity,
    writeDirectAccessMasked, writeRegisterBankMasked, writeWordsMasked, writeWords,
    PEMemory.distance, htarget, hentry,
    mergeSelectedWord, selectedWordMask, Nat.reduceSub, Nat.reduceLT]
  constructor
  · change BitVec.extractLsb' 32 32
      (parsedFloatReluBus .f .relu false
        (⟨input ⟨2, by decide⟩ ++ input ⟨3, by decide⟩, (0 : BitVec 64)⟩ : IntegerALU.Bus)
        (some ⟨input ⟨2, by decide⟩ ++ input ⟨3, by decide⟩, (0 : BitVec 64)⟩)).1.high
      &&& 4294967295#32 = reluWord (input ⟨2, by decide⟩)
    rw [reluBus_high_literal]
    have hff : (4294967295#32 : BitVec 32) = BitVec.allOnes 32 := rfl
    rw [hff]
    simp only [extract_high, extract_low]
    have hx : ∀ x : BitVec 32, x &&& 4294967295#32 = x := by
      intro x
      have hff : (4294967295#32 : BitVec 32) = BitVec.allOnes 32 := by
        apply BitVec.toNat_eq.mpr
        simp [BitVec.toNat_allOnes]
      rw [hff, BitVec.and_allOnes]
    exact hx _
  · constructor
    · change BitVec.extractLsb' 0 32
        (parsedFloatReluBus .f .relu false
          (⟨input ⟨2, by decide⟩ ++ input ⟨3, by decide⟩, (0 : BitVec 64)⟩ : IntegerALU.Bus)
          (some ⟨input ⟨2, by decide⟩ ++ input ⟨3, by decide⟩, (0 : BitVec 64)⟩)).1.high
        &&& 4294967295#32 = reluWord (input ⟨3, by decide⟩)
      rw [reluBus_high_literal]
      have hff : (4294967295#32 : BitVec 32) = BitVec.allOnes 32 := rfl
      rw [hff]
      simp only [extract_high, extract_low]
      have hx : ∀ x : BitVec 32, x &&& 4294967295#32 = x := by
        intro x
        have hff : (4294967295#32 : BitVec 32) = BitVec.allOnes 32 := by
          apply BitVec.toNat_eq.mpr
          simp [BitVec.toNat_allOnes]
        rw [hff, BitVec.and_allOnes]
      exact hx _
    · intro j hj0 hj1 hlt
      omega


/-- Cycle 2 with an arbitrary initial register file.  The read state is fixed
(the executor always reads `readState`), so only the written files change. -/
theorem reluExpr0_cycle2_generic (input : ProofsLean.MNCore.PlusOne.Words)
    (files0 : IntegerRegisterFiles) (outputs : Fin 4 → IntegerALU.Bus) :
    ∃ files bar0 bar1 outputs',
      executeParsedFloatReluAtPE.runCycles (welcomeInitialState input) (welcomeInitialState input)
        reluExpr0 0 false (ParsedIntegerContext.ofLinearIndex 0) (ParsedIntegerContext.ofLinearIndex 0)
        [2] files0 0 0 outputs =
        .ok (files, bar0, bar1, outputs') ∧
      files.lm1 ⟨4, by decide⟩ = reluWord (input ⟨4, by decide⟩) ∧
      files.lm1 ⟨5, by decide⟩ = reluWord (input ⟨5, by decide⟩) ∧
      files.lm0 = files0.lm0 ∧
      bar0 = 0 ∧ bar1 = 0 ∧
      ∀ j : Fin Bank.lm1.capacity, j ≠ ⟨4, by decide⟩ → j ≠ ⟨5, by decide⟩ →
        files.lm1 j = files0.lm1 j := by
  rw [executeParsedFloatReluAtPE.runCycles]
  rw [show ({ (ParsedIntegerContext.ofLinearIndex 0) with cycle := 2 } : ParsedIntegerContext)
      = reluContext 0 2 from rfl]
  rw [reluExpr0_lower_eq_cycle2]
  simp only [reluSrc2]
  rw [reluInitial_readWithForwarding_long2 input]
  have htarget : (welcomeInitialState input).maskDirective.targets.lm1 = false := by
    rw [welcomeInitialState_maskDirective]
    exact welcomeMaskDirective_targets_lm1
  have hentry : (welcomeInitialState input).maskDirective.entry = 0 := rfl
  simp [reluExpr0, reluOp, reluLm1Long0, reluLm0Long0, unpackALUBus,
    parsedOutputAfterFlush, resolveFlushSelection?,
    executeParsedFloatReluAtPE.runCycles.writeDestinations,
    executeParsedFloatReluAtPE.runCycles, writeParsedMslMsrDestination?,
    commitParsedMaskedWrites, ParsedOperand.resolveMemoryWriteSelection?,
    resolveMemoryDirectiveSelection?, welcomeMaskDirective, directiveTargetsBank,
    ParsedIntegerContext.ofLinearIndex, issueBankToRegisterBank,
    ParsedOperand.toDirectMemoryDestination?, ParsedOperand.toDirectMemoryAccess?,
    ParsedOperand.toDirectMemoryAccessMode?, parsedWidth?, parsedRegionAddressAt,
    PEMemory.count, PEMemory.Width.words, PEMemory.Bank.capacity,
    writeDirectAccessMasked, writeRegisterBankMasked, writeWordsMasked, writeWords,
    PEMemory.distance, htarget, hentry,
    mergeSelectedWord, selectedWordMask, Nat.reduceSub, Nat.reduceLT]
  constructor
  · change BitVec.extractLsb' 32 32
      (parsedFloatReluBus .f .relu false
        (⟨input ⟨4, by decide⟩ ++ input ⟨5, by decide⟩, (0 : BitVec 64)⟩ : IntegerALU.Bus)
        (some ⟨input ⟨4, by decide⟩ ++ input ⟨5, by decide⟩, (0 : BitVec 64)⟩)).1.high
      &&& 4294967295#32 = reluWord (input ⟨4, by decide⟩)
    rw [reluBus_high_literal]
    have hff : (4294967295#32 : BitVec 32) = BitVec.allOnes 32 := rfl
    rw [hff]
    simp only [extract_high, extract_low]
    have hx : ∀ x : BitVec 32, x &&& 4294967295#32 = x := by
      intro x
      have hff : (4294967295#32 : BitVec 32) = BitVec.allOnes 32 := by
        apply BitVec.toNat_eq.mpr
        simp [BitVec.toNat_allOnes]
      rw [hff, BitVec.and_allOnes]
    exact hx _
  · constructor
    · change BitVec.extractLsb' 0 32
        (parsedFloatReluBus .f .relu false
          (⟨input ⟨4, by decide⟩ ++ input ⟨5, by decide⟩, (0 : BitVec 64)⟩ : IntegerALU.Bus)
          (some ⟨input ⟨4, by decide⟩ ++ input ⟨5, by decide⟩, (0 : BitVec 64)⟩)).1.high
        &&& 4294967295#32 = reluWord (input ⟨5, by decide⟩)
      rw [reluBus_high_literal]
      have hff : (4294967295#32 : BitVec 32) = BitVec.allOnes 32 := rfl
      rw [hff]
      simp only [extract_high, extract_low]
      have hx : ∀ x : BitVec 32, x &&& 4294967295#32 = x := by
        intro x
        have hff : (4294967295#32 : BitVec 32) = BitVec.allOnes 32 := by
          apply BitVec.toNat_eq.mpr
          simp [BitVec.toNat_allOnes]
        rw [hff, BitVec.and_allOnes]
      exact hx _
    · intro j hj0 hj1 hlt
      omega


/-- Cycle 3 with an arbitrary initial register file.  The read state is fixed
(the executor always reads `readState`), so only the written files change. -/
theorem reluExpr0_cycle3_generic (input : ProofsLean.MNCore.PlusOne.Words)
    (files0 : IntegerRegisterFiles) (outputs : Fin 4 → IntegerALU.Bus) :
    ∃ files bar0 bar1 outputs',
      executeParsedFloatReluAtPE.runCycles (welcomeInitialState input) (welcomeInitialState input)
        reluExpr0 0 false (ParsedIntegerContext.ofLinearIndex 0) (ParsedIntegerContext.ofLinearIndex 0)
        [3] files0 0 0 outputs =
        .ok (files, bar0, bar1, outputs') ∧
      files.lm1 ⟨6, by decide⟩ = reluWord (input ⟨6, by decide⟩) ∧
      files.lm1 ⟨7, by decide⟩ = reluWord (input ⟨7, by decide⟩) ∧
      files.lm0 = files0.lm0 ∧
      bar0 = 0 ∧ bar1 = 0 ∧
      ∀ j : Fin Bank.lm1.capacity, j ≠ ⟨6, by decide⟩ → j ≠ ⟨7, by decide⟩ →
        files.lm1 j = files0.lm1 j := by
  rw [executeParsedFloatReluAtPE.runCycles]
  rw [show ({ (ParsedIntegerContext.ofLinearIndex 0) with cycle := 3 } : ParsedIntegerContext)
      = reluContext 0 3 from rfl]
  rw [reluExpr0_lower_eq_cycle3]
  simp only [reluSrc3]
  rw [reluInitial_readWithForwarding_long3 input]
  have htarget : (welcomeInitialState input).maskDirective.targets.lm1 = false := by
    rw [welcomeInitialState_maskDirective]
    exact welcomeMaskDirective_targets_lm1
  have hentry : (welcomeInitialState input).maskDirective.entry = 0 := rfl
  simp [reluExpr0, reluOp, reluLm1Long0, reluLm0Long0, unpackALUBus,
    parsedOutputAfterFlush, resolveFlushSelection?,
    executeParsedFloatReluAtPE.runCycles.writeDestinations,
    executeParsedFloatReluAtPE.runCycles, writeParsedMslMsrDestination?,
    commitParsedMaskedWrites, ParsedOperand.resolveMemoryWriteSelection?,
    resolveMemoryDirectiveSelection?, welcomeMaskDirective, directiveTargetsBank,
    ParsedIntegerContext.ofLinearIndex, issueBankToRegisterBank,
    ParsedOperand.toDirectMemoryDestination?, ParsedOperand.toDirectMemoryAccess?,
    ParsedOperand.toDirectMemoryAccessMode?, parsedWidth?, parsedRegionAddressAt,
    PEMemory.count, PEMemory.Width.words, PEMemory.Bank.capacity,
    writeDirectAccessMasked, writeRegisterBankMasked, writeWordsMasked, writeWords,
    PEMemory.distance, htarget, hentry,
    mergeSelectedWord, selectedWordMask, Nat.reduceSub, Nat.reduceLT]
  constructor
  · change BitVec.extractLsb' 32 32
      (parsedFloatReluBus .f .relu false
        (⟨input ⟨6, by decide⟩ ++ input ⟨7, by decide⟩, (0 : BitVec 64)⟩ : IntegerALU.Bus)
        (some ⟨input ⟨6, by decide⟩ ++ input ⟨7, by decide⟩, (0 : BitVec 64)⟩)).1.high
      &&& 4294967295#32 = reluWord (input ⟨6, by decide⟩)
    rw [reluBus_high_literal]
    have hff : (4294967295#32 : BitVec 32) = BitVec.allOnes 32 := rfl
    rw [hff]
    simp only [extract_high, extract_low]
    have hx : ∀ x : BitVec 32, x &&& 4294967295#32 = x := by
      intro x
      have hff : (4294967295#32 : BitVec 32) = BitVec.allOnes 32 := by
        apply BitVec.toNat_eq.mpr
        simp [BitVec.toNat_allOnes]
      rw [hff, BitVec.and_allOnes]
    exact hx _
  · constructor
    · change BitVec.extractLsb' 0 32
        (parsedFloatReluBus .f .relu false
          (⟨input ⟨6, by decide⟩ ++ input ⟨7, by decide⟩, (0 : BitVec 64)⟩ : IntegerALU.Bus)
          (some ⟨input ⟨6, by decide⟩ ++ input ⟨7, by decide⟩, (0 : BitVec 64)⟩)).1.high
        &&& 4294967295#32 = reluWord (input ⟨7, by decide⟩)
      rw [reluBus_high_literal]
      have hff : (4294967295#32 : BitVec 32) = BitVec.allOnes 32 := rfl
      rw [hff]
      simp only [extract_high, extract_low]
      have hx : ∀ x : BitVec 32, x &&& 4294967295#32 = x := by
        intro x
        have hff : (4294967295#32 : BitVec 32) = BitVec.allOnes 32 := by
          apply BitVec.toNat_eq.mpr
          simp [BitVec.toNat_allOnes]
        rw [hff, BitVec.and_allOnes]
      exact hx _
    · intro j hj0 hj1 hlt
      omega


/-- Splitting `[0, 1, 2, 3]` into cycle 0 and the rest, for arbitrary initial
register files, BAR values and forwarding outputs. -/
theorem reluSplit0123 (input : ProofsLean.MNCore.PlusOne.Words)
    (files : IntegerRegisterFiles) (bar0 bar1 : BitVec 12)
    (outputs : Fin 4 → IntegerALU.Bus) :
    executeParsedFloatReluAtPE.runCycles (welcomeInitialState input) (welcomeInitialState input)
        reluExpr0 0 false (ParsedIntegerContext.ofLinearIndex 0) (ParsedIntegerContext.ofLinearIndex 0)
        [0, 1, 2, 3] files bar0 bar1 outputs =
      match executeParsedFloatReluAtPE.runCycles (welcomeInitialState input) (welcomeInitialState input)
          reluExpr0 0 false (ParsedIntegerContext.ofLinearIndex 0) (ParsedIntegerContext.ofLinearIndex 0)
          [0] files bar0 bar1 outputs with
      | .ok (nextFiles, nextBar0, nextBar1, nextOutputs) =>
          executeParsedFloatReluAtPE.runCycles (welcomeInitialState input) (welcomeInitialState input)
            reluExpr0 0 false (ParsedIntegerContext.ofLinearIndex 0) (ParsedIntegerContext.ofLinearIndex 0)
            [1, 2, 3] nextFiles nextBar0 nextBar1 nextOutputs
      | .failure => .failure
      | .unknown => .unknown := by
  rw [executeParsedFloatReluAtPE.runCycles]
  conv_rhs => rw [executeParsedFloatReluAtPE.runCycles]
  rfl

/-- Splitting `[1, 2, 3]` into cycle 1 and the rest, for arbitrary initial
register files, BAR values and forwarding outputs. -/
theorem reluSplit123 (input : ProofsLean.MNCore.PlusOne.Words)
    (files : IntegerRegisterFiles) (bar0 bar1 : BitVec 12)
    (outputs : Fin 4 → IntegerALU.Bus) :
    executeParsedFloatReluAtPE.runCycles (welcomeInitialState input) (welcomeInitialState input)
        reluExpr0 0 false (ParsedIntegerContext.ofLinearIndex 0) (ParsedIntegerContext.ofLinearIndex 0)
        [1, 2, 3] files bar0 bar1 outputs =
      match executeParsedFloatReluAtPE.runCycles (welcomeInitialState input) (welcomeInitialState input)
          reluExpr0 0 false (ParsedIntegerContext.ofLinearIndex 0) (ParsedIntegerContext.ofLinearIndex 0)
          [1] files bar0 bar1 outputs with
      | .ok (nextFiles, nextBar0, nextBar1, nextOutputs) =>
          executeParsedFloatReluAtPE.runCycles (welcomeInitialState input) (welcomeInitialState input)
            reluExpr0 0 false (ParsedIntegerContext.ofLinearIndex 0) (ParsedIntegerContext.ofLinearIndex 0)
            [2, 3] nextFiles nextBar0 nextBar1 nextOutputs
      | .failure => .failure
      | .unknown => .unknown := by
  rw [executeParsedFloatReluAtPE.runCycles]
  conv_rhs => rw [executeParsedFloatReluAtPE.runCycles]
  rfl

/-- Splitting `[2, 3]` into cycle 2 and the rest, for arbitrary initial
register files, BAR values and forwarding outputs. -/
theorem reluSplit23 (input : ProofsLean.MNCore.PlusOne.Words)
    (files : IntegerRegisterFiles) (bar0 bar1 : BitVec 12)
    (outputs : Fin 4 → IntegerALU.Bus) :
    executeParsedFloatReluAtPE.runCycles (welcomeInitialState input) (welcomeInitialState input)
        reluExpr0 0 false (ParsedIntegerContext.ofLinearIndex 0) (ParsedIntegerContext.ofLinearIndex 0)
        [2, 3] files bar0 bar1 outputs =
      match executeParsedFloatReluAtPE.runCycles (welcomeInitialState input) (welcomeInitialState input)
          reluExpr0 0 false (ParsedIntegerContext.ofLinearIndex 0) (ParsedIntegerContext.ofLinearIndex 0)
          [2] files bar0 bar1 outputs with
      | .ok (nextFiles, nextBar0, nextBar1, nextOutputs) =>
          executeParsedFloatReluAtPE.runCycles (welcomeInitialState input) (welcomeInitialState input)
            reluExpr0 0 false (ParsedIntegerContext.ofLinearIndex 0) (ParsedIntegerContext.ofLinearIndex 0)
            [3] nextFiles nextBar0 nextBar1 nextOutputs
      | .failure => .failure
      | .unknown => .unknown := by
  rw [executeParsedFloatReluAtPE.runCycles]
  conv_rhs => rw [executeParsedFloatReluAtPE.runCycles]
  rfl

/-- The four-cycle fold of the first accepted line. -/
theorem reluFold (input : ProofsLean.MNCore.PlusOne.Words) :
    ∃ files bar0 bar1 outputs,
      executeParsedFloatReluAtPE.runCycles (welcomeInitialState input) (welcomeInitialState input)
        reluExpr0 0 false (ParsedIntegerContext.ofLinearIndex 0) (ParsedIntegerContext.ofLinearIndex 0)
        [0, 1, 2, 3] (welcomeInitialPERegisters input) 0 0 (fun _ => ⟨0, 0⟩) =
        .ok (files, bar0, bar1, outputs) ∧
      (∀ i : Fin 8, files.lm1 ⟨i.val, by have := i.isLt; change i.val < 4096; omega⟩ =
        reluWord (input ⟨i.val, by have := i.isLt; omega⟩)) ∧
      files.lm0 = (welcomeInitialPERegisters input).lm0 ∧
      bar0 = 0 ∧ bar1 = 0 := by
  obtain ⟨f1, b01, b11, o1, h0, v00, v01, lm0_0, hb01, hb11, fr0⟩ :=
    reluExpr0_cycle0_generic input (welcomeInitialPERegisters input) (fun _ => ⟨0, 0⟩)
  obtain ⟨f2, b02, b12, o2, h1, v12, v13, lm0_1, hb02, hb12, fr1⟩ :=
    reluExpr0_cycle1_generic input f1 o1
  obtain ⟨f3, b03, b13, o3, h2, v24, v25, lm0_2, hb03, hb13, fr2⟩ :=
    reluExpr0_cycle2_generic input f2 o2
  obtain ⟨f4, b04, b14, o4, h3, v36, v37, lm0_3, hb04, hb14, fr3⟩ :=
    reluExpr0_cycle3_generic input f3 o3
  refine ⟨f4, 0, 0, o4, ?_, ?_, ?_, rfl, rfl⟩
  · rw [reluSplit0123, h0]; simp only []
    rw [hb01, hb11]
    rw [reluSplit123, h1]; simp only []
    rw [hb02, hb12]
    rw [reluSplit23, h2]; simp only []
    rw [hb03, hb13]
    rw [h3]
    rw [hb04, hb14]
  · intro i
    have hcases : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 ∨ i.val = 5 ∨ i.val = 6 ∨ i.val = 7 := by omega
    rcases hcases with e0 | e1 | e2 | e3 | e4 | e5 | e6 | e7
    · have hi : i = ⟨0, by decide⟩ := Fin.ext e0
      subst hi
      have h : f4.lm1 ⟨0, by decide⟩ = reluWord (input ⟨0, by decide⟩) := by
        rw [fr3 ⟨0, by decide⟩ (by decide) (by decide), fr2 ⟨0, by decide⟩ (by decide) (by decide), fr1 ⟨0, by decide⟩ (by decide) (by decide), v00]
      simpa using h
    · have hi : i = ⟨1, by decide⟩ := Fin.ext e1
      subst hi
      have h : f4.lm1 ⟨1, by decide⟩ = reluWord (input ⟨1, by decide⟩) := by
        rw [fr3 ⟨1, by decide⟩ (by decide) (by decide), fr2 ⟨1, by decide⟩ (by decide) (by decide), fr1 ⟨1, by decide⟩ (by decide) (by decide), v01]
      simpa using h
    · have hi : i = ⟨2, by decide⟩ := Fin.ext e2
      subst hi
      have h : f4.lm1 ⟨2, by decide⟩ = reluWord (input ⟨2, by decide⟩) := by
        rw [fr3 ⟨2, by decide⟩ (by decide) (by decide), fr2 ⟨2, by decide⟩ (by decide) (by decide), v12]
      simpa using h
    · have hi : i = ⟨3, by decide⟩ := Fin.ext e3
      subst hi
      have h : f4.lm1 ⟨3, by decide⟩ = reluWord (input ⟨3, by decide⟩) := by
        rw [fr3 ⟨3, by decide⟩ (by decide) (by decide), fr2 ⟨3, by decide⟩ (by decide) (by decide), v13]
      simpa using h
    · have hi : i = ⟨4, by decide⟩ := Fin.ext e4
      subst hi
      have h : f4.lm1 ⟨4, by decide⟩ = reluWord (input ⟨4, by decide⟩) := by
        rw [fr3 ⟨4, by decide⟩ (by decide) (by decide), v24]
      simpa using h
    · have hi : i = ⟨5, by decide⟩ := Fin.ext e5
      subst hi
      have h : f4.lm1 ⟨5, by decide⟩ = reluWord (input ⟨5, by decide⟩) := by
        rw [fr3 ⟨5, by decide⟩ (by decide) (by decide), v25]
      simpa using h
    · have hi : i = ⟨6, by decide⟩ := Fin.ext e6
      subst hi
      have h : f4.lm1 ⟨6, by decide⟩ = reluWord (input ⟨6, by decide⟩) := by
        rw [v36]
      simpa using h
    · have hi : i = ⟨7, by decide⟩ := Fin.ext e7
      subst hi
      have h : f4.lm1 ⟨7, by decide⟩ = reluWord (input ⟨7, by decide⟩) := by
        rw [v37]
      simpa using h
  · exact lm0_3.trans (lm0_2.trans (lm0_1.trans lm0_0))

/-- The value readback of the first accepted line at PE 0: after executing
`frelu $lm0v $lm0v $ln0v`, the first eight LM1 words are the ReLU of the first
eight input words. -/
theorem executeParsedFloatReluAtPE_pe_lm1 (input : ProofsLean.MNCore.PlusOne.Words)
    (next : State)
    (executed : executeParsedFloatReluAtPE (welcomeInitialState input) (welcomeInitialState input)
      reluExpr0 0 false false = .ok next) :
    ∀ i : Fin 8,
      (next.peRegisters welcomePE).lm1
        ⟨i.val, by have := i.isLt; change i.val < 4096; omega⟩ =
      reluWord (input ⟨i.val, by have := i.isLt; omega⟩) := by
  obtain ⟨files, fbar0, fbar1, foutputs, hrun, hval, hlm0, hb0, hb1⟩ := reluFold input
  rw [executeParsedFloatReluAtPE.eq_1] at executed
  dsimp only at executed
  split at executed
  · simp at executed
  · simp at executed
  · rename_i registers bar0 bar1 outputs ran
    rw [Id.run_pure] at executed
    simp only [StepResult.ok.injEq] at executed
    have hrun' :
        executeParsedFloatReluAtPE.runCycles (welcomeInitialState input) (welcomeInitialState input)
          reluExpr0 0 false (ParsedIntegerContext.ofLinearIndex 0) (ParsedIntegerContext.ofLinearIndex 0)
          [0, 1, 2, 3] (welcomeInitialPERegisters input) 0 0 (fun _ => ⟨0, 0⟩) =
          .ok (files, fbar0, fbar1, foutputs) := hrun
    change executeParsedFloatReluAtPE.runCycles (welcomeInitialState input) (welcomeInitialState input)
      reluExpr0 0 false (ParsedIntegerContext.ofLinearIndex 0) (ParsedIntegerContext.ofLinearIndex 0)
      [0, 1, 2, 3] (welcomeInitialPERegisters input) 0 0 (fun _ => ⟨0, 0⟩) =
      .ok (registers, bar0, bar1, outputs) at ran
    rw [hrun'] at ran
    simp only [StepResult.ok.injEq] at ran
    obtain ⟨rfl, rfl, rfl, rfl⟩ := ran
    subst executed
    simp only [welcomePE]
    exact hval

/-! ## 5. The second accepted line (base 8) -/

/-- Source operands of the second accepted line at cycles 0..3. -/
def reluSrc8_0 : ProofsLean.MNCore.PEMemory.ParsedIntegerInput :=
  .memory ⟨.lm0, .long, ⟨8, by decide⟩⟩ false
def reluSrc8_1 : ProofsLean.MNCore.PEMemory.ParsedIntegerInput :=
  .memory ⟨.lm0, .long, ⟨10, by decide⟩⟩ false
def reluSrc8_2 : ProofsLean.MNCore.PEMemory.ParsedIntegerInput :=
  .memory ⟨.lm0, .long, ⟨12, by decide⟩⟩ false
def reluSrc8_3 : ProofsLean.MNCore.PEMemory.ParsedIntegerInput :=
  .memory ⟨.lm0, .long, ⟨14, by decide⟩⟩ false

theorem reluExpr8_lower_eq_cycle0 :
    lowerParsedFloatRelu? reluExpr8 (reluContext 0 0) =
    some (ParsedFloatReluAccesses.mk .f .relu false reluSrc8_0 (some reluSrc8_0)
      [reluLm1Long8]) := rfl
theorem reluExpr8_lower_eq_cycle1 :
    lowerParsedFloatRelu? reluExpr8 (reluContext 0 1) =
    some (ParsedFloatReluAccesses.mk .f .relu false reluSrc8_1 (some reluSrc8_1)
      [reluLm1Long8]) := rfl
theorem reluExpr8_lower_eq_cycle2 :
    lowerParsedFloatRelu? reluExpr8 (reluContext 0 2) =
    some (ParsedFloatReluAccesses.mk .f .relu false reluSrc8_2 (some reluSrc8_2)
      [reluLm1Long8]) := rfl
theorem reluExpr8_lower_eq_cycle3 :
    lowerParsedFloatRelu? reluExpr8 (reluContext 0 3) =
    some (ParsedFloatReluAccesses.mk .f .relu false reluSrc8_3 (some reluSrc8_3)
      [reluLm1Long8]) := rfl

theorem reluInitial_readWithForwarding_long8_0 (input : ProofsLean.MNCore.PlusOne.Words) :
    ProofsLean.MNCore.PEMemory.ParsedIntegerInput.readWithForwarding
      ((welcomeInitialState input).peRegisters 0)
      (stateForwardingSlots (welcomeInitialState input) 0) 0
      (.memory ⟨.lm0, .long, ⟨8, by decide⟩⟩ false) =
    .ok ⟨input ⟨8, by decide⟩ ++ input ⟨9, by decide⟩, 0⟩ := by
  have h := reluInitial_readWithForwarding_long input 8 0 (by decide)
  convert h using 2

theorem reluInitial_readWithForwarding_long8_1 (input : ProofsLean.MNCore.PlusOne.Words) :
    ProofsLean.MNCore.PEMemory.ParsedIntegerInput.readWithForwarding
      ((welcomeInitialState input).peRegisters 0)
      (stateForwardingSlots (welcomeInitialState input) 0) 1
      (.memory ⟨.lm0, .long, ⟨10, by decide⟩⟩ false) =
    .ok ⟨input ⟨10, by decide⟩ ++ input ⟨11, by decide⟩, 0⟩ := by
  have h := reluInitial_readWithForwarding_long input 8 1 (by decide)
  convert h using 2

theorem reluInitial_readWithForwarding_long8_2 (input : ProofsLean.MNCore.PlusOne.Words) :
    ProofsLean.MNCore.PEMemory.ParsedIntegerInput.readWithForwarding
      ((welcomeInitialState input).peRegisters 0)
      (stateForwardingSlots (welcomeInitialState input) 0) 2
      (.memory ⟨.lm0, .long, ⟨12, by decide⟩⟩ false) =
    .ok ⟨input ⟨12, by decide⟩ ++ input ⟨13, by decide⟩, 0⟩ := by
  have h := reluInitial_readWithForwarding_long input 8 2 (by decide)
  convert h using 2

theorem reluInitial_readWithForwarding_long8_3 (input : ProofsLean.MNCore.PlusOne.Words) :
    ProofsLean.MNCore.PEMemory.ParsedIntegerInput.readWithForwarding
      ((welcomeInitialState input).peRegisters 0)
      (stateForwardingSlots (welcomeInitialState input) 0) 3
      (.memory ⟨.lm0, .long, ⟨14, by decide⟩⟩ false) =
    .ok ⟨input ⟨14, by decide⟩ ++ input ⟨15, by decide⟩, 0⟩ := by
  have h := reluInitial_readWithForwarding_long input 8 3 (by decide)
  convert h using 2

/-- Cycle 0 (base 8) with an arbitrary initial register file.  The read state is fixed
(the executor always reads `readState`), so only the written files change. -/
theorem reluExpr8_cycle0_generic (input : ProofsLean.MNCore.PlusOne.Words)
    (files0 : IntegerRegisterFiles) (outputs : Fin 4 → IntegerALU.Bus) :
    ∃ files bar0 bar1 outputs',
      executeParsedFloatReluAtPE.runCycles (welcomeInitialState input) (welcomeInitialState input)
        reluExpr8 0 false (ParsedIntegerContext.ofLinearIndex 0) (ParsedIntegerContext.ofLinearIndex 0)
        [0] files0 0 0 outputs =
        .ok (files, bar0, bar1, outputs') ∧
      files.lm1 ⟨8, by decide⟩ = reluWord (input ⟨8, by decide⟩) ∧
      files.lm1 ⟨9, by decide⟩ = reluWord (input ⟨9, by decide⟩) ∧
      files.lm0 = files0.lm0 ∧
      bar0 = 0 ∧ bar1 = 0 ∧
      ∀ j : Fin Bank.lm1.capacity, j ≠ ⟨8, by decide⟩ → j ≠ ⟨9, by decide⟩ →
        files.lm1 j = files0.lm1 j := by
  rw [executeParsedFloatReluAtPE.runCycles]
  rw [show ({ (ParsedIntegerContext.ofLinearIndex 0) with cycle := 0 } : ParsedIntegerContext)
      = reluContext 0 0 from rfl]
  rw [reluExpr8_lower_eq_cycle0]
  simp only [reluSrc8_0]
  rw [reluInitial_readWithForwarding_long8_0 input]
  have htarget : (welcomeInitialState input).maskDirective.targets.lm1 = false := by
    rw [welcomeInitialState_maskDirective]
    exact welcomeMaskDirective_targets_lm1
  have hentry : (welcomeInitialState input).maskDirective.entry = 0 := rfl
  simp [reluExpr8, reluOp, reluLm1Long8, reluLm0Long8, unpackALUBus,
    parsedOutputAfterFlush, resolveFlushSelection?,
    executeParsedFloatReluAtPE.runCycles.writeDestinations,
    executeParsedFloatReluAtPE.runCycles, writeParsedMslMsrDestination?,
    commitParsedMaskedWrites, ParsedOperand.resolveMemoryWriteSelection?,
    resolveMemoryDirectiveSelection?, welcomeMaskDirective, directiveTargetsBank,
    ParsedIntegerContext.ofLinearIndex, issueBankToRegisterBank,
    ParsedOperand.toDirectMemoryDestination?, ParsedOperand.toDirectMemoryAccess?,
    ParsedOperand.toDirectMemoryAccessMode?, parsedWidth?, parsedRegionAddressAt,
    PEMemory.count, PEMemory.Width.words, PEMemory.Bank.capacity,
    writeDirectAccessMasked, writeRegisterBankMasked, writeWordsMasked, writeWords,
    PEMemory.distance, htarget, hentry,
    mergeSelectedWord, selectedWordMask, Nat.reduceSub, Nat.reduceLT]
  constructor
  · change BitVec.extractLsb' 32 32
      (parsedFloatReluBus .f .relu false
        (⟨input ⟨8, by decide⟩ ++ input ⟨9, by decide⟩, (0 : BitVec 64)⟩ : IntegerALU.Bus)
        (some ⟨input ⟨8, by decide⟩ ++ input ⟨9, by decide⟩, (0 : BitVec 64)⟩)).1.high
      &&& 4294967295#32 = reluWord (input ⟨8, by decide⟩)
    rw [reluBus_high_literal]
    have hff : (4294967295#32 : BitVec 32) = BitVec.allOnes 32 := rfl
    rw [hff]
    simp only [extract_high, extract_low]
    have hx : ∀ x : BitVec 32, x &&& 4294967295#32 = x := by
      intro x
      have hff : (4294967295#32 : BitVec 32) = BitVec.allOnes 32 := by
        apply BitVec.toNat_eq.mpr
        simp [BitVec.toNat_allOnes]
      rw [hff, BitVec.and_allOnes]
    exact hx _
  · constructor
    · change BitVec.extractLsb' 0 32
        (parsedFloatReluBus .f .relu false
          (⟨input ⟨8, by decide⟩ ++ input ⟨9, by decide⟩, (0 : BitVec 64)⟩ : IntegerALU.Bus)
          (some ⟨input ⟨8, by decide⟩ ++ input ⟨9, by decide⟩, (0 : BitVec 64)⟩)).1.high
        &&& 4294967295#32 = reluWord (input ⟨9, by decide⟩)
      rw [reluBus_high_literal]
      have hff : (4294967295#32 : BitVec 32) = BitVec.allOnes 32 := rfl
      rw [hff]
      simp only [extract_high, extract_low]
      have hx : ∀ x : BitVec 32, x &&& 4294967295#32 = x := by
        intro x
        have hff : (4294967295#32 : BitVec 32) = BitVec.allOnes 32 := by
          apply BitVec.toNat_eq.mpr
          simp [BitVec.toNat_allOnes]
        rw [hff, BitVec.and_allOnes]
      exact hx _
    · intro j hj0 hj1 hlt
      omega



/-- Cycle 1 (base 8) with an arbitrary initial register file.  The read state is fixed
(the executor always reads `readState`), so only the written files change. -/
theorem reluExpr8_cycle1_generic (input : ProofsLean.MNCore.PlusOne.Words)
    (files0 : IntegerRegisterFiles) (outputs : Fin 4 → IntegerALU.Bus) :
    ∃ files bar0 bar1 outputs',
      executeParsedFloatReluAtPE.runCycles (welcomeInitialState input) (welcomeInitialState input)
        reluExpr8 0 false (ParsedIntegerContext.ofLinearIndex 0) (ParsedIntegerContext.ofLinearIndex 0)
        [1] files0 0 0 outputs =
        .ok (files, bar0, bar1, outputs') ∧
      files.lm1 ⟨10, by decide⟩ = reluWord (input ⟨10, by decide⟩) ∧
      files.lm1 ⟨11, by decide⟩ = reluWord (input ⟨11, by decide⟩) ∧
      files.lm0 = files0.lm0 ∧
      bar0 = 0 ∧ bar1 = 0 ∧
      ∀ j : Fin Bank.lm1.capacity, j ≠ ⟨10, by decide⟩ → j ≠ ⟨11, by decide⟩ →
        files.lm1 j = files0.lm1 j := by
  rw [executeParsedFloatReluAtPE.runCycles]
  rw [show ({ (ParsedIntegerContext.ofLinearIndex 0) with cycle := 1 } : ParsedIntegerContext)
      = reluContext 0 1 from rfl]
  rw [reluExpr8_lower_eq_cycle1]
  simp only [reluSrc8_1]
  rw [reluInitial_readWithForwarding_long8_1 input]
  have htarget : (welcomeInitialState input).maskDirective.targets.lm1 = false := by
    rw [welcomeInitialState_maskDirective]
    exact welcomeMaskDirective_targets_lm1
  have hentry : (welcomeInitialState input).maskDirective.entry = 0 := rfl
  simp [reluExpr8, reluOp, reluLm1Long8, reluLm0Long8, unpackALUBus,
    parsedOutputAfterFlush, resolveFlushSelection?,
    executeParsedFloatReluAtPE.runCycles.writeDestinations,
    executeParsedFloatReluAtPE.runCycles, writeParsedMslMsrDestination?,
    commitParsedMaskedWrites, ParsedOperand.resolveMemoryWriteSelection?,
    resolveMemoryDirectiveSelection?, welcomeMaskDirective, directiveTargetsBank,
    ParsedIntegerContext.ofLinearIndex, issueBankToRegisterBank,
    ParsedOperand.toDirectMemoryDestination?, ParsedOperand.toDirectMemoryAccess?,
    ParsedOperand.toDirectMemoryAccessMode?, parsedWidth?, parsedRegionAddressAt,
    PEMemory.count, PEMemory.Width.words, PEMemory.Bank.capacity,
    writeDirectAccessMasked, writeRegisterBankMasked, writeWordsMasked, writeWords,
    PEMemory.distance, htarget, hentry,
    mergeSelectedWord, selectedWordMask, Nat.reduceSub, Nat.reduceLT]
  constructor
  · change BitVec.extractLsb' 32 32
      (parsedFloatReluBus .f .relu false
        (⟨input ⟨10, by decide⟩ ++ input ⟨11, by decide⟩, (0 : BitVec 64)⟩ : IntegerALU.Bus)
        (some ⟨input ⟨10, by decide⟩ ++ input ⟨11, by decide⟩, (0 : BitVec 64)⟩)).1.high
      &&& 4294967295#32 = reluWord (input ⟨10, by decide⟩)
    rw [reluBus_high_literal]
    have hff : (4294967295#32 : BitVec 32) = BitVec.allOnes 32 := rfl
    rw [hff]
    simp only [extract_high, extract_low]
    have hx : ∀ x : BitVec 32, x &&& 4294967295#32 = x := by
      intro x
      have hff : (4294967295#32 : BitVec 32) = BitVec.allOnes 32 := by
        apply BitVec.toNat_eq.mpr
        simp [BitVec.toNat_allOnes]
      rw [hff, BitVec.and_allOnes]
    exact hx _
  · constructor
    · change BitVec.extractLsb' 0 32
        (parsedFloatReluBus .f .relu false
          (⟨input ⟨10, by decide⟩ ++ input ⟨11, by decide⟩, (0 : BitVec 64)⟩ : IntegerALU.Bus)
          (some ⟨input ⟨10, by decide⟩ ++ input ⟨11, by decide⟩, (0 : BitVec 64)⟩)).1.high
        &&& 4294967295#32 = reluWord (input ⟨11, by decide⟩)
      rw [reluBus_high_literal]
      have hff : (4294967295#32 : BitVec 32) = BitVec.allOnes 32 := rfl
      rw [hff]
      simp only [extract_high, extract_low]
      have hx : ∀ x : BitVec 32, x &&& 4294967295#32 = x := by
        intro x
        have hff : (4294967295#32 : BitVec 32) = BitVec.allOnes 32 := by
          apply BitVec.toNat_eq.mpr
          simp [BitVec.toNat_allOnes]
        rw [hff, BitVec.and_allOnes]
      exact hx _
    · intro j hj0 hj1 hlt
      omega



/-- Cycle 2 (base 8) with an arbitrary initial register file.  The read state is fixed
(the executor always reads `readState`), so only the written files change. -/
theorem reluExpr8_cycle2_generic (input : ProofsLean.MNCore.PlusOne.Words)
    (files0 : IntegerRegisterFiles) (outputs : Fin 4 → IntegerALU.Bus) :
    ∃ files bar0 bar1 outputs',
      executeParsedFloatReluAtPE.runCycles (welcomeInitialState input) (welcomeInitialState input)
        reluExpr8 0 false (ParsedIntegerContext.ofLinearIndex 0) (ParsedIntegerContext.ofLinearIndex 0)
        [2] files0 0 0 outputs =
        .ok (files, bar0, bar1, outputs') ∧
      files.lm1 ⟨12, by decide⟩ = reluWord (input ⟨12, by decide⟩) ∧
      files.lm1 ⟨13, by decide⟩ = reluWord (input ⟨13, by decide⟩) ∧
      files.lm0 = files0.lm0 ∧
      bar0 = 0 ∧ bar1 = 0 ∧
      ∀ j : Fin Bank.lm1.capacity, j ≠ ⟨12, by decide⟩ → j ≠ ⟨13, by decide⟩ →
        files.lm1 j = files0.lm1 j := by
  rw [executeParsedFloatReluAtPE.runCycles]
  rw [show ({ (ParsedIntegerContext.ofLinearIndex 0) with cycle := 2 } : ParsedIntegerContext)
      = reluContext 0 2 from rfl]
  rw [reluExpr8_lower_eq_cycle2]
  simp only [reluSrc8_2]
  rw [reluInitial_readWithForwarding_long8_2 input]
  have htarget : (welcomeInitialState input).maskDirective.targets.lm1 = false := by
    rw [welcomeInitialState_maskDirective]
    exact welcomeMaskDirective_targets_lm1
  have hentry : (welcomeInitialState input).maskDirective.entry = 0 := rfl
  simp [reluExpr8, reluOp, reluLm1Long8, reluLm0Long8, unpackALUBus,
    parsedOutputAfterFlush, resolveFlushSelection?,
    executeParsedFloatReluAtPE.runCycles.writeDestinations,
    executeParsedFloatReluAtPE.runCycles, writeParsedMslMsrDestination?,
    commitParsedMaskedWrites, ParsedOperand.resolveMemoryWriteSelection?,
    resolveMemoryDirectiveSelection?, welcomeMaskDirective, directiveTargetsBank,
    ParsedIntegerContext.ofLinearIndex, issueBankToRegisterBank,
    ParsedOperand.toDirectMemoryDestination?, ParsedOperand.toDirectMemoryAccess?,
    ParsedOperand.toDirectMemoryAccessMode?, parsedWidth?, parsedRegionAddressAt,
    PEMemory.count, PEMemory.Width.words, PEMemory.Bank.capacity,
    writeDirectAccessMasked, writeRegisterBankMasked, writeWordsMasked, writeWords,
    PEMemory.distance, htarget, hentry,
    mergeSelectedWord, selectedWordMask, Nat.reduceSub, Nat.reduceLT]
  constructor
  · change BitVec.extractLsb' 32 32
      (parsedFloatReluBus .f .relu false
        (⟨input ⟨12, by decide⟩ ++ input ⟨13, by decide⟩, (0 : BitVec 64)⟩ : IntegerALU.Bus)
        (some ⟨input ⟨12, by decide⟩ ++ input ⟨13, by decide⟩, (0 : BitVec 64)⟩)).1.high
      &&& 4294967295#32 = reluWord (input ⟨12, by decide⟩)
    rw [reluBus_high_literal]
    have hff : (4294967295#32 : BitVec 32) = BitVec.allOnes 32 := rfl
    rw [hff]
    simp only [extract_high, extract_low]
    have hx : ∀ x : BitVec 32, x &&& 4294967295#32 = x := by
      intro x
      have hff : (4294967295#32 : BitVec 32) = BitVec.allOnes 32 := by
        apply BitVec.toNat_eq.mpr
        simp [BitVec.toNat_allOnes]
      rw [hff, BitVec.and_allOnes]
    exact hx _
  · constructor
    · change BitVec.extractLsb' 0 32
        (parsedFloatReluBus .f .relu false
          (⟨input ⟨12, by decide⟩ ++ input ⟨13, by decide⟩, (0 : BitVec 64)⟩ : IntegerALU.Bus)
          (some ⟨input ⟨12, by decide⟩ ++ input ⟨13, by decide⟩, (0 : BitVec 64)⟩)).1.high
        &&& 4294967295#32 = reluWord (input ⟨13, by decide⟩)
      rw [reluBus_high_literal]
      have hff : (4294967295#32 : BitVec 32) = BitVec.allOnes 32 := rfl
      rw [hff]
      simp only [extract_high, extract_low]
      have hx : ∀ x : BitVec 32, x &&& 4294967295#32 = x := by
        intro x
        have hff : (4294967295#32 : BitVec 32) = BitVec.allOnes 32 := by
          apply BitVec.toNat_eq.mpr
          simp [BitVec.toNat_allOnes]
        rw [hff, BitVec.and_allOnes]
      exact hx _
    · intro j hj0 hj1 hlt
      omega



/-- Cycle 3 (base 8) with an arbitrary initial register file.  The read state is fixed
(the executor always reads `readState`), so only the written files change. -/
theorem reluExpr8_cycle3_generic (input : ProofsLean.MNCore.PlusOne.Words)
    (files0 : IntegerRegisterFiles) (outputs : Fin 4 → IntegerALU.Bus) :
    ∃ files bar0 bar1 outputs',
      executeParsedFloatReluAtPE.runCycles (welcomeInitialState input) (welcomeInitialState input)
        reluExpr8 0 false (ParsedIntegerContext.ofLinearIndex 0) (ParsedIntegerContext.ofLinearIndex 0)
        [3] files0 0 0 outputs =
        .ok (files, bar0, bar1, outputs') ∧
      files.lm1 ⟨14, by decide⟩ = reluWord (input ⟨14, by decide⟩) ∧
      files.lm1 ⟨15, by decide⟩ = reluWord (input ⟨15, by decide⟩) ∧
      files.lm0 = files0.lm0 ∧
      bar0 = 0 ∧ bar1 = 0 ∧
      ∀ j : Fin Bank.lm1.capacity, j ≠ ⟨14, by decide⟩ → j ≠ ⟨15, by decide⟩ →
        files.lm1 j = files0.lm1 j := by
  rw [executeParsedFloatReluAtPE.runCycles]
  rw [show ({ (ParsedIntegerContext.ofLinearIndex 0) with cycle := 3 } : ParsedIntegerContext)
      = reluContext 0 3 from rfl]
  rw [reluExpr8_lower_eq_cycle3]
  simp only [reluSrc8_3]
  rw [reluInitial_readWithForwarding_long8_3 input]
  have htarget : (welcomeInitialState input).maskDirective.targets.lm1 = false := by
    rw [welcomeInitialState_maskDirective]
    exact welcomeMaskDirective_targets_lm1
  have hentry : (welcomeInitialState input).maskDirective.entry = 0 := rfl
  simp [reluExpr8, reluOp, reluLm1Long8, reluLm0Long8, unpackALUBus,
    parsedOutputAfterFlush, resolveFlushSelection?,
    executeParsedFloatReluAtPE.runCycles.writeDestinations,
    executeParsedFloatReluAtPE.runCycles, writeParsedMslMsrDestination?,
    commitParsedMaskedWrites, ParsedOperand.resolveMemoryWriteSelection?,
    resolveMemoryDirectiveSelection?, welcomeMaskDirective, directiveTargetsBank,
    ParsedIntegerContext.ofLinearIndex, issueBankToRegisterBank,
    ParsedOperand.toDirectMemoryDestination?, ParsedOperand.toDirectMemoryAccess?,
    ParsedOperand.toDirectMemoryAccessMode?, parsedWidth?, parsedRegionAddressAt,
    PEMemory.count, PEMemory.Width.words, PEMemory.Bank.capacity,
    writeDirectAccessMasked, writeRegisterBankMasked, writeWordsMasked, writeWords,
    PEMemory.distance, htarget, hentry,
    mergeSelectedWord, selectedWordMask, Nat.reduceSub, Nat.reduceLT]
  constructor
  · change BitVec.extractLsb' 32 32
      (parsedFloatReluBus .f .relu false
        (⟨input ⟨14, by decide⟩ ++ input ⟨15, by decide⟩, (0 : BitVec 64)⟩ : IntegerALU.Bus)
        (some ⟨input ⟨14, by decide⟩ ++ input ⟨15, by decide⟩, (0 : BitVec 64)⟩)).1.high
      &&& 4294967295#32 = reluWord (input ⟨14, by decide⟩)
    rw [reluBus_high_literal]
    have hff : (4294967295#32 : BitVec 32) = BitVec.allOnes 32 := rfl
    rw [hff]
    simp only [extract_high, extract_low]
    have hx : ∀ x : BitVec 32, x &&& 4294967295#32 = x := by
      intro x
      have hff : (4294967295#32 : BitVec 32) = BitVec.allOnes 32 := by
        apply BitVec.toNat_eq.mpr
        simp [BitVec.toNat_allOnes]
      rw [hff, BitVec.and_allOnes]
    exact hx _
  · constructor
    · change BitVec.extractLsb' 0 32
        (parsedFloatReluBus .f .relu false
          (⟨input ⟨14, by decide⟩ ++ input ⟨15, by decide⟩, (0 : BitVec 64)⟩ : IntegerALU.Bus)
          (some ⟨input ⟨14, by decide⟩ ++ input ⟨15, by decide⟩, (0 : BitVec 64)⟩)).1.high
        &&& 4294967295#32 = reluWord (input ⟨15, by decide⟩)
      rw [reluBus_high_literal]
      have hff : (4294967295#32 : BitVec 32) = BitVec.allOnes 32 := rfl
      rw [hff]
      simp only [extract_high, extract_low]
      have hx : ∀ x : BitVec 32, x &&& 4294967295#32 = x := by
        intro x
        have hff : (4294967295#32 : BitVec 32) = BitVec.allOnes 32 := by
          apply BitVec.toNat_eq.mpr
          simp [BitVec.toNat_allOnes]
        rw [hff, BitVec.and_allOnes]
      exact hx _
    · intro j hj0 hj1 hlt
      omega



/-- Base-8 split of `[0, 1, 2, 3]`. -/
theorem reluSplit8_0123 (input : ProofsLean.MNCore.PlusOne.Words)
    (files : IntegerRegisterFiles) (bar0 bar1 : BitVec 12)
    (outputs : Fin 4 → IntegerALU.Bus) :
    executeParsedFloatReluAtPE.runCycles (welcomeInitialState input) (welcomeInitialState input)
        reluExpr8 0 false (ParsedIntegerContext.ofLinearIndex 0) (ParsedIntegerContext.ofLinearIndex 0)
        [0, 1, 2, 3] files bar0 bar1 outputs =
      match executeParsedFloatReluAtPE.runCycles (welcomeInitialState input) (welcomeInitialState input)
          reluExpr8 0 false (ParsedIntegerContext.ofLinearIndex 0) (ParsedIntegerContext.ofLinearIndex 0)
          [0] files bar0 bar1 outputs with
      | .ok (nextFiles, nextBar0, nextBar1, nextOutputs) =>
          executeParsedFloatReluAtPE.runCycles (welcomeInitialState input) (welcomeInitialState input)
            reluExpr8 0 false (ParsedIntegerContext.ofLinearIndex 0) (ParsedIntegerContext.ofLinearIndex 0)
            [1, 2, 3] nextFiles nextBar0 nextBar1 nextOutputs
      | .failure => .failure
      | .unknown => .unknown := by
  rw [executeParsedFloatReluAtPE.runCycles]
  conv_rhs => rw [executeParsedFloatReluAtPE.runCycles]
  rfl

/-- Base-8 split of `[1, 2, 3]`. -/
theorem reluSplit8_123 (input : ProofsLean.MNCore.PlusOne.Words)
    (files : IntegerRegisterFiles) (bar0 bar1 : BitVec 12)
    (outputs : Fin 4 → IntegerALU.Bus) :
    executeParsedFloatReluAtPE.runCycles (welcomeInitialState input) (welcomeInitialState input)
        reluExpr8 0 false (ParsedIntegerContext.ofLinearIndex 0) (ParsedIntegerContext.ofLinearIndex 0)
        [1, 2, 3] files bar0 bar1 outputs =
      match executeParsedFloatReluAtPE.runCycles (welcomeInitialState input) (welcomeInitialState input)
          reluExpr8 0 false (ParsedIntegerContext.ofLinearIndex 0) (ParsedIntegerContext.ofLinearIndex 0)
          [1] files bar0 bar1 outputs with
      | .ok (nextFiles, nextBar0, nextBar1, nextOutputs) =>
          executeParsedFloatReluAtPE.runCycles (welcomeInitialState input) (welcomeInitialState input)
            reluExpr8 0 false (ParsedIntegerContext.ofLinearIndex 0) (ParsedIntegerContext.ofLinearIndex 0)
            [2, 3] nextFiles nextBar0 nextBar1 nextOutputs
      | .failure => .failure
      | .unknown => .unknown := by
  rw [executeParsedFloatReluAtPE.runCycles]
  conv_rhs => rw [executeParsedFloatReluAtPE.runCycles]
  rfl

/-- Base-8 split of `[2, 3]`. -/
theorem reluSplit8_23 (input : ProofsLean.MNCore.PlusOne.Words)
    (files : IntegerRegisterFiles) (bar0 bar1 : BitVec 12)
    (outputs : Fin 4 → IntegerALU.Bus) :
    executeParsedFloatReluAtPE.runCycles (welcomeInitialState input) (welcomeInitialState input)
        reluExpr8 0 false (ParsedIntegerContext.ofLinearIndex 0) (ParsedIntegerContext.ofLinearIndex 0)
        [2, 3] files bar0 bar1 outputs =
      match executeParsedFloatReluAtPE.runCycles (welcomeInitialState input) (welcomeInitialState input)
          reluExpr8 0 false (ParsedIntegerContext.ofLinearIndex 0) (ParsedIntegerContext.ofLinearIndex 0)
          [2] files bar0 bar1 outputs with
      | .ok (nextFiles, nextBar0, nextBar1, nextOutputs) =>
          executeParsedFloatReluAtPE.runCycles (welcomeInitialState input) (welcomeInitialState input)
            reluExpr8 0 false (ParsedIntegerContext.ofLinearIndex 0) (ParsedIntegerContext.ofLinearIndex 0)
            [3] nextFiles nextBar0 nextBar1 nextOutputs
      | .failure => .failure
      | .unknown => .unknown := by
  rw [executeParsedFloatReluAtPE.runCycles]
  conv_rhs => rw [executeParsedFloatReluAtPE.runCycles]
  rfl

/-- The four-cycle fold of the second accepted line (base 8). -/
theorem reluFold8 (input : ProofsLean.MNCore.PlusOne.Words) :
    ∃ files bar0 bar1 outputs,
      executeParsedFloatReluAtPE.runCycles (welcomeInitialState input) (welcomeInitialState input)
        reluExpr8 0 false (ParsedIntegerContext.ofLinearIndex 0) (ParsedIntegerContext.ofLinearIndex 0)
        [0, 1, 2, 3] (welcomeInitialPERegisters input) 0 0 (fun _ => ⟨0, 0⟩) =
        .ok (files, bar0, bar1, outputs) ∧
      (∀ i : Fin 8, files.lm1 ⟨8 + i.val, by have := i.isLt; change 8 + i.val < 4096; omega⟩ =
        reluWord (input ⟨8 + i.val, by have := i.isLt; omega⟩)) ∧
      files.lm0 = (welcomeInitialPERegisters input).lm0 ∧
      bar0 = 0 ∧ bar1 = 0 := by
  obtain ⟨f1, b01, b11, o1, h0, v00, v01, lm0_0, hb01, hb11, fr0⟩ :=
    reluExpr8_cycle0_generic input (welcomeInitialPERegisters input) (fun _ => ⟨0, 0⟩)
  obtain ⟨f2, b02, b12, o2, h1, v12, v13, lm0_1, hb02, hb12, fr1⟩ :=
    reluExpr8_cycle1_generic input f1 o1
  obtain ⟨f3, b03, b13, o3, h2, v24, v25, lm0_2, hb03, hb13, fr2⟩ :=
    reluExpr8_cycle2_generic input f2 o2
  obtain ⟨f4, b04, b14, o4, h3, v36, v37, lm0_3, hb04, hb14, fr3⟩ :=
    reluExpr8_cycle3_generic input f3 o3
  refine ⟨f4, 0, 0, o4, ?_, ?_, ?_, rfl, rfl⟩
  · rw [reluSplit8_0123, h0]; simp only []
    rw [hb01, hb11]
    rw [reluSplit8_123, h1]; simp only []
    rw [hb02, hb12]
    rw [reluSplit8_23, h2]; simp only []
    rw [hb03, hb13]
    rw [h3]
    rw [hb04, hb14]
  · intro i
    have hcases : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 ∨ i.val = 5 ∨ i.val = 6 ∨ i.val = 7 := by omega
    rcases hcases with e0 | e1 | e2 | e3 | e4 | e5 | e6 | e7
    · have hi : i = ⟨0, by decide⟩ := Fin.ext e0
      subst hi
      have h : f4.lm1 ⟨8, by decide⟩ = reluWord (input ⟨8, by decide⟩) := by
        rw [fr3 ⟨8, by decide⟩ (by decide) (by decide), fr2 ⟨8, by decide⟩ (by decide) (by decide), fr1 ⟨8, by decide⟩ (by decide) (by decide), v00]
      simpa using h
    · have hi : i = ⟨1, by decide⟩ := Fin.ext e1
      subst hi
      have h : f4.lm1 ⟨9, by decide⟩ = reluWord (input ⟨9, by decide⟩) := by
        rw [fr3 ⟨9, by decide⟩ (by decide) (by decide), fr2 ⟨9, by decide⟩ (by decide) (by decide), fr1 ⟨9, by decide⟩ (by decide) (by decide), v01]
      simpa using h
    · have hi : i = ⟨2, by decide⟩ := Fin.ext e2
      subst hi
      have h : f4.lm1 ⟨10, by decide⟩ = reluWord (input ⟨10, by decide⟩) := by
        rw [fr3 ⟨10, by decide⟩ (by decide) (by decide), fr2 ⟨10, by decide⟩ (by decide) (by decide), v12]
      simpa using h
    · have hi : i = ⟨3, by decide⟩ := Fin.ext e3
      subst hi
      have h : f4.lm1 ⟨11, by decide⟩ = reluWord (input ⟨11, by decide⟩) := by
        rw [fr3 ⟨11, by decide⟩ (by decide) (by decide), fr2 ⟨11, by decide⟩ (by decide) (by decide), v13]
      simpa using h
    · have hi : i = ⟨4, by decide⟩ := Fin.ext e4
      subst hi
      have h : f4.lm1 ⟨12, by decide⟩ = reluWord (input ⟨12, by decide⟩) := by
        rw [fr3 ⟨12, by decide⟩ (by decide) (by decide), v24]
      simpa using h
    · have hi : i = ⟨5, by decide⟩ := Fin.ext e5
      subst hi
      have h : f4.lm1 ⟨13, by decide⟩ = reluWord (input ⟨13, by decide⟩) := by
        rw [fr3 ⟨13, by decide⟩ (by decide) (by decide), v25]
      simpa using h
    · have hi : i = ⟨6, by decide⟩ := Fin.ext e6
      subst hi
      have h : f4.lm1 ⟨14, by decide⟩ = reluWord (input ⟨14, by decide⟩) := by
        rw [v36]
      simpa using h
    · have hi : i = ⟨7, by decide⟩ := Fin.ext e7
      subst hi
      have h : f4.lm1 ⟨15, by decide⟩ = reluWord (input ⟨15, by decide⟩) := by
        rw [v37]
      simpa using h
  · exact lm0_3.trans (lm0_2.trans (lm0_1.trans lm0_0))

/-- The value readback of the second accepted line at PE 0 (base 8): the words
8..15 are the ReLU of input words 8..15. -/
theorem executeParsedFloatReluAtPE_pe_lm1_8 (input : ProofsLean.MNCore.PlusOne.Words)
    (next : State)
    (executed : executeParsedFloatReluAtPE (welcomeInitialState input) (welcomeInitialState input)
      reluExpr8 0 false false = .ok next) :
    ∀ i : Fin 8,
      (next.peRegisters welcomePE).lm1
        ⟨8 + i.val, by have := i.isLt; change 8 + i.val < 4096; omega⟩ =
      reluWord (input ⟨8 + i.val, by have := i.isLt; omega⟩) := by
  obtain ⟨files, fbar0, fbar1, foutputs, hrun, hval, hlm0, hb0, hb1⟩ := reluFold8 input
  rw [executeParsedFloatReluAtPE.eq_1] at executed
  dsimp only at executed
  split at executed
  · simp at executed
  · simp at executed
  · rename_i registers bar0 bar1 outputs ran
    rw [Id.run_pure] at executed
    simp only [StepResult.ok.injEq] at executed
    have hrun' :
        executeParsedFloatReluAtPE.runCycles (welcomeInitialState input) (welcomeInitialState input)
          reluExpr8 0 false (ParsedIntegerContext.ofLinearIndex 0) (ParsedIntegerContext.ofLinearIndex 0)
          [0, 1, 2, 3] (welcomeInitialPERegisters input) 0 0 (fun _ => ⟨0, 0⟩) =
          .ok (files, fbar0, fbar1, foutputs) := hrun
    change executeParsedFloatReluAtPE.runCycles (welcomeInitialState input) (welcomeInitialState input)
      reluExpr8 0 false (ParsedIntegerContext.ofLinearIndex 0) (ParsedIntegerContext.ofLinearIndex 0)
      [0, 1, 2, 3] (welcomeInitialPERegisters input) 0 0 (fun _ => ⟨0, 0⟩) =
      .ok (registers, bar0, bar1, outputs) at ran
    rw [hrun'] at ran
    simp only [StepResult.ok.injEq] at ran
    obtain ⟨rfl, rfl, rfl, rfl⟩ := ran
    subst executed
    simp only [welcomePE]
    exact hval

/-- PE 0's eight words after the 4096-PE relu walk of the first line. -/
theorem executeParsedFloatReluAtPEs_finRange_pe0_lm1
    (input : ProofsLean.MNCore.PlusOne.Words) (next : State)
    (executed : executeParsedFloatReluAtPEs (welcomeInitialState input) (welcomeInitialState input)
      reluExpr0 (List.finRange 4096) false false = .ok next) :
    ∀ i : Fin 8,
      (next.peRegisters welcomePE).lm1
        ⟨i.val, by have := i.isLt; change i.val < 4096; omega⟩ =
      reluWord (input ⟨i.val, by have := i.isLt; omega⟩) := by
  rw [finRange4096_eq_welcomePE_cons] at executed
  simp only [executeParsedFloatReluAtPEs] at executed
  cases head : executeParsedFloatReluAtPE (welcomeInitialState input) (welcomeInitialState input)
      reluExpr0 welcomePE false false with
  | failure => simp [head] at executed
  | unknown => simp [head] at executed
  | ok middle =>
    simp only [head] at executed
    have hvalues := executeParsedFloatReluAtPE_pe_lm1 input middle head
    have hframe : next.peRegisters welcomePE = middle.peRegisters welcomePE :=
      executeParsedFloatReluAtPEs_peRegisters_not_mem (welcomeInitialState input) reluExpr0
        false false ((List.finRange 4095).map Fin.succ) middle next welcomePE
        (by simp [welcomePE]) executed
    intro i
    rw [hframe]
    exact hvalues i

/-! ## Trust report -/

#print axioms reluFold
#print axioms executeParsedFloatReluAtPE_pe_lm1
#print axioms executeParsedFloatReluAtPE_pe_lm1_8
#print axioms reluFold8
#print axioms executeParsedFloatReluAtPEs_finRange_pe0_lm1
#print axioms reluExpr0_cycle0_generic
#print axioms reluSplit0123

end ProofsLean.MNCore
