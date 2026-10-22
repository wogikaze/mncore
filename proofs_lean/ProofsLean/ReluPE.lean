import ProofsLean.ReluOpt

namespace ProofsLean.MNCore

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

open Issue
open ProofsLean.MNCore.PEMemory

/-- The LM0 long read at an arbitrary PE of a PE-uniform state. -/
theorem reluRead_long_state_pe (input : ProofsLean.MNCore.PlusOne.Words) (readState : State)
    (pe : PEId) (base : Nat) (c : Fin 4) (hbase : base + 2 * c.val + 1 < 16)
    (hreadLm0 : ∀ a, (readState.peRegisters pe).lm0 a = (welcomeInitialPERegisters input).lm0 a) :
    ProofsLean.MNCore.PEMemory.ParsedIntegerInput.readWithForwarding
      (readState.peRegisters pe) (stateForwardingSlots readState pe) c
      (.memory ⟨.lm0, .long,
        ⟨base + 2 * c.val, by have := c.isLt; change base + 2 * c.val < 4096; omega⟩⟩ false) =
    .ok ⟨input ⟨base + 2 * c.val, by omega⟩ ++
         input ⟨base + 2 * c.val + 1, by omega⟩, 0⟩ := by
  rw [read_memory_lm0]
  rw [show (readState.peRegisters pe).lm0 = (welcomeInitialPERegisters input).lm0 from funext hreadLm0]
  simpa [ParsedIntegerInput.readWithForwarding, ParsedIntegerInput.read, ParsedIntegerInput.applyRounding,
    readDirectAccess, readRegisterBank, welcomeInitialState] using
    reluInitial_readWithForwarding_long input base c hbase

/-- The PE-independent lowering of `reluExpr0` at cycle 0. -/
theorem reluExpr0_lower_eq_cycle0_pe (pe : PEId) :
    lowerParsedFloatRelu? reluExpr0
      ({ (ParsedIntegerContext.ofLinearIndex pe) with cycle := 0 } : ParsedIntegerContext) =
    lowerParsedFloatRelu? reluExpr0 (reluContext 0 0) := rfl

theorem reluExpr0_lower_eq_cycle1_pe (pe : PEId) :
    lowerParsedFloatRelu? reluExpr0
      ({ (ParsedIntegerContext.ofLinearIndex pe) with cycle := 1 } : ParsedIntegerContext) =
    lowerParsedFloatRelu? reluExpr0 (reluContext 0 1) := rfl

theorem reluExpr0_lower_eq_cycle2_pe (pe : PEId) :
    lowerParsedFloatRelu? reluExpr0
      ({ (ParsedIntegerContext.ofLinearIndex pe) with cycle := 2 } : ParsedIntegerContext) =
    lowerParsedFloatRelu? reluExpr0 (reluContext 0 2) := rfl

theorem reluExpr0_lower_eq_cycle3_pe (pe : PEId) :
    lowerParsedFloatRelu? reluExpr0
      ({ (ParsedIntegerContext.ofLinearIndex pe) with cycle := 3 } : ParsedIntegerContext) =
    lowerParsedFloatRelu? reluExpr0 (reluContext 0 3) := rfl

/-- Cycle 0 of the first relu line at an arbitrary PE of a PE-uniform state. -/
theorem reluExpr0_cycle0_genericState_pe (input : ProofsLean.MNCore.PlusOne.Words) (pe : PEId)
    (currentState : State) (files0 : IntegerRegisterFiles) (outputs : Fin 4 → IntegerALU.Bus)
    (hmask : currentState.maskDirective = (welcomeInitialState input).maskDirective) :
    ∃ files bar0 bar1 outputs',
      executeParsedFloatReluAtPE.runCycles (welcomeInitialState input) currentState
        reluExpr0 pe false (ParsedIntegerContext.ofLinearIndex pe) (ParsedIntegerContext.ofLinearIndex pe)
        [0] files0 0 0 outputs =
        .ok (files, bar0, bar1, outputs') ∧
      files.lm1 ⟨0, by decide⟩ = reluWord (input ⟨0, by decide⟩) ∧
      files.lm1 ⟨1, by decide⟩ = reluWord (input ⟨1, by decide⟩) ∧
      files.lm0 = files0.lm0 ∧
      bar0 = 0 ∧ bar1 = 0 ∧
      ∀ j : Fin Bank.lm1.capacity, j ≠ ⟨0, by decide⟩ → j ≠ ⟨1, by decide⟩ →
        files.lm1 j = files0.lm1 j := by
  rw [executeParsedFloatReluAtPE.runCycles]
  rw [reluExpr0_lower_eq_cycle0_pe pe]
  rw [reluExpr0_lower_eq_cycle0]
  simp only [reluSrc0]
  have hread : ParsedIntegerInput.readWithForwarding
      ((welcomeInitialState input).peRegisters pe) (stateForwardingSlots (welcomeInitialState input) pe) 0
      (.memory ⟨.lm0, .long, ⟨0, by decide⟩⟩ false) =
      .ok ⟨input ⟨0, by decide⟩ ++ input ⟨1, by decide⟩, 0⟩ := by
    simpa using reluRead_long_state_pe input (welcomeInitialState input) pe 0 0 (by decide) (fun a => rfl)
  rw [hread]
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
    PEMemory.distance, hmask, htarget, hentry,
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

theorem reluExpr0_cycle1_genericState_pe (input : ProofsLean.MNCore.PlusOne.Words) (pe : PEId)
    (currentState : State) (files0 : IntegerRegisterFiles) (outputs : Fin 4 → IntegerALU.Bus)
    (hmask : currentState.maskDirective = (welcomeInitialState input).maskDirective) :
    ∃ files bar0 bar1 outputs',
      executeParsedFloatReluAtPE.runCycles (welcomeInitialState input) currentState
        reluExpr0 pe false (ParsedIntegerContext.ofLinearIndex pe) (ParsedIntegerContext.ofLinearIndex pe)
        [1] files0 0 0 outputs =
        .ok (files, bar0, bar1, outputs') ∧
      files.lm1 ⟨2, by decide⟩ = reluWord (input ⟨2, by decide⟩) ∧
      files.lm1 ⟨3, by decide⟩ = reluWord (input ⟨3, by decide⟩) ∧
      files.lm0 = files0.lm0 ∧
      bar0 = 0 ∧ bar1 = 0 ∧
      ∀ j : Fin Bank.lm1.capacity, j ≠ ⟨2, by decide⟩ → j ≠ ⟨3, by decide⟩ →
        files.lm1 j = files0.lm1 j := by
  rw [executeParsedFloatReluAtPE.runCycles]
  rw [reluExpr0_lower_eq_cycle1_pe pe]
  rw [reluExpr0_lower_eq_cycle1]
  simp only [reluSrc1]
  have hread : ParsedIntegerInput.readWithForwarding
      ((welcomeInitialState input).peRegisters pe) (stateForwardingSlots (welcomeInitialState input) pe) 1
      (.memory ⟨.lm0, .long, ⟨2, by decide⟩⟩ false) =
      .ok ⟨input ⟨2, by decide⟩ ++ input ⟨3, by decide⟩, 0⟩ := by
    simpa using reluRead_long_state_pe input (welcomeInitialState input) pe 0 1 (by decide) (fun a => rfl)
  rw [hread]
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
    PEMemory.distance, hmask, htarget, hentry,
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



theorem reluExpr0_cycle2_genericState_pe (input : ProofsLean.MNCore.PlusOne.Words) (pe : PEId)
    (currentState : State) (files0 : IntegerRegisterFiles) (outputs : Fin 4 → IntegerALU.Bus)
    (hmask : currentState.maskDirective = (welcomeInitialState input).maskDirective) :
    ∃ files bar0 bar1 outputs',
      executeParsedFloatReluAtPE.runCycles (welcomeInitialState input) currentState
        reluExpr0 pe false (ParsedIntegerContext.ofLinearIndex pe) (ParsedIntegerContext.ofLinearIndex pe)
        [2] files0 0 0 outputs =
        .ok (files, bar0, bar1, outputs') ∧
      files.lm1 ⟨4, by decide⟩ = reluWord (input ⟨4, by decide⟩) ∧
      files.lm1 ⟨5, by decide⟩ = reluWord (input ⟨5, by decide⟩) ∧
      files.lm0 = files0.lm0 ∧
      bar0 = 0 ∧ bar1 = 0 ∧
      ∀ j : Fin Bank.lm1.capacity, j ≠ ⟨4, by decide⟩ → j ≠ ⟨5, by decide⟩ →
        files.lm1 j = files0.lm1 j := by
  rw [executeParsedFloatReluAtPE.runCycles]
  rw [reluExpr0_lower_eq_cycle2_pe pe]
  rw [reluExpr0_lower_eq_cycle2]
  simp only [reluSrc2]
  have hread : ParsedIntegerInput.readWithForwarding
      ((welcomeInitialState input).peRegisters pe) (stateForwardingSlots (welcomeInitialState input) pe) 2
      (.memory ⟨.lm0, .long, ⟨4, by decide⟩⟩ false) =
      .ok ⟨input ⟨4, by decide⟩ ++ input ⟨5, by decide⟩, 0⟩ := by
    simpa using reluRead_long_state_pe input (welcomeInitialState input) pe 0 2 (by decide) (fun a => rfl)
  rw [hread]
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
    PEMemory.distance, hmask, htarget, hentry,
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



theorem reluExpr0_cycle3_genericState_pe (input : ProofsLean.MNCore.PlusOne.Words) (pe : PEId)
    (currentState : State) (files0 : IntegerRegisterFiles) (outputs : Fin 4 → IntegerALU.Bus)
    (hmask : currentState.maskDirective = (welcomeInitialState input).maskDirective) :
    ∃ files bar0 bar1 outputs',
      executeParsedFloatReluAtPE.runCycles (welcomeInitialState input) currentState
        reluExpr0 pe false (ParsedIntegerContext.ofLinearIndex pe) (ParsedIntegerContext.ofLinearIndex pe)
        [3] files0 0 0 outputs =
        .ok (files, bar0, bar1, outputs') ∧
      files.lm1 ⟨6, by decide⟩ = reluWord (input ⟨6, by decide⟩) ∧
      files.lm1 ⟨7, by decide⟩ = reluWord (input ⟨7, by decide⟩) ∧
      files.lm0 = files0.lm0 ∧
      bar0 = 0 ∧ bar1 = 0 ∧
      ∀ j : Fin Bank.lm1.capacity, j ≠ ⟨6, by decide⟩ → j ≠ ⟨7, by decide⟩ →
        files.lm1 j = files0.lm1 j := by
  rw [executeParsedFloatReluAtPE.runCycles]
  rw [reluExpr0_lower_eq_cycle3_pe pe]
  rw [reluExpr0_lower_eq_cycle3]
  simp only [reluSrc3]
  have hread : ParsedIntegerInput.readWithForwarding
      ((welcomeInitialState input).peRegisters pe) (stateForwardingSlots (welcomeInitialState input) pe) 3
      (.memory ⟨.lm0, .long, ⟨6, by decide⟩⟩ false) =
      .ok ⟨input ⟨6, by decide⟩ ++ input ⟨7, by decide⟩, 0⟩ := by
    simpa using reluRead_long_state_pe input (welcomeInitialState input) pe 0 3 (by decide) (fun a => rfl)
  rw [hread]
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
    PEMemory.distance, hmask, htarget, hentry,
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


theorem reluSplit0123_state_pe (input : ProofsLean.MNCore.PlusOne.Words) (pe : PEId)
    (currentState : State) (files : IntegerRegisterFiles) (bar0 bar1 : BitVec 12)
    (outputs : Fin 4 → IntegerALU.Bus) :
    executeParsedFloatReluAtPE.runCycles (welcomeInitialState input) currentState
        reluExpr0 pe false (ParsedIntegerContext.ofLinearIndex pe) (ParsedIntegerContext.ofLinearIndex pe)
        [0, 1, 2, 3] files bar0 bar1 outputs =
      match executeParsedFloatReluAtPE.runCycles (welcomeInitialState input) currentState
          reluExpr0 pe false (ParsedIntegerContext.ofLinearIndex pe) (ParsedIntegerContext.ofLinearIndex pe)
          [0] files bar0 bar1 outputs with
      | .ok (nextFiles, nextBar0, nextBar1, nextOutputs) =>
          executeParsedFloatReluAtPE.runCycles (welcomeInitialState input) currentState
            reluExpr0 pe false (ParsedIntegerContext.ofLinearIndex pe) (ParsedIntegerContext.ofLinearIndex pe)
            [1, 2, 3] nextFiles nextBar0 nextBar1 nextOutputs
      | .failure => .failure
      | .unknown => .unknown := by
  rw [executeParsedFloatReluAtPE.runCycles]
  conv_rhs => rw [executeParsedFloatReluAtPE.runCycles]
  rfl



theorem reluSplit123_state_pe (input : ProofsLean.MNCore.PlusOne.Words) (pe : PEId)
    (currentState : State) (files : IntegerRegisterFiles) (bar0 bar1 : BitVec 12)
    (outputs : Fin 4 → IntegerALU.Bus) :
    executeParsedFloatReluAtPE.runCycles (welcomeInitialState input) currentState
        reluExpr0 pe false (ParsedIntegerContext.ofLinearIndex pe) (ParsedIntegerContext.ofLinearIndex pe)
        [1, 2, 3] files bar0 bar1 outputs =
      match executeParsedFloatReluAtPE.runCycles (welcomeInitialState input) currentState
          reluExpr0 pe false (ParsedIntegerContext.ofLinearIndex pe) (ParsedIntegerContext.ofLinearIndex pe)
          [1] files bar0 bar1 outputs with
      | .ok (nextFiles, nextBar0, nextBar1, nextOutputs) =>
          executeParsedFloatReluAtPE.runCycles (welcomeInitialState input) currentState
            reluExpr0 pe false (ParsedIntegerContext.ofLinearIndex pe) (ParsedIntegerContext.ofLinearIndex pe)
            [2, 3] nextFiles nextBar0 nextBar1 nextOutputs
      | .failure => .failure
      | .unknown => .unknown := by
  rw [executeParsedFloatReluAtPE.runCycles]
  conv_rhs => rw [executeParsedFloatReluAtPE.runCycles]
  rfl



theorem reluSplit23_state_pe (input : ProofsLean.MNCore.PlusOne.Words) (pe : PEId)
    (currentState : State) (files : IntegerRegisterFiles) (bar0 bar1 : BitVec 12)
    (outputs : Fin 4 → IntegerALU.Bus) :
    executeParsedFloatReluAtPE.runCycles (welcomeInitialState input) currentState
        reluExpr0 pe false (ParsedIntegerContext.ofLinearIndex pe) (ParsedIntegerContext.ofLinearIndex pe)
        [2, 3] files bar0 bar1 outputs =
      match executeParsedFloatReluAtPE.runCycles (welcomeInitialState input) currentState
          reluExpr0 pe false (ParsedIntegerContext.ofLinearIndex pe) (ParsedIntegerContext.ofLinearIndex pe)
          [2] files bar0 bar1 outputs with
      | .ok (nextFiles, nextBar0, nextBar1, nextOutputs) =>
          executeParsedFloatReluAtPE.runCycles (welcomeInitialState input) currentState
            reluExpr0 pe false (ParsedIntegerContext.ofLinearIndex pe) (ParsedIntegerContext.ofLinearIndex pe)
            [3] nextFiles nextBar0 nextBar1 nextOutputs
      | .failure => .failure
      | .unknown => .unknown := by
  rw [executeParsedFloatReluAtPE.runCycles]
  conv_rhs => rw [executeParsedFloatReluAtPE.runCycles]
  rfl




theorem reluFold_genericState_pe (input : ProofsLean.MNCore.PlusOne.Words) (pe : PEId)
    (currentState : State) (files0 : IntegerRegisterFiles) (outputs0 : Fin 4 → IntegerALU.Bus)
    (hmask : currentState.maskDirective = (welcomeInitialState input).maskDirective) :
    ∃ files bar0 bar1 outputs,
      executeParsedFloatReluAtPE.runCycles (welcomeInitialState input) currentState
        reluExpr0 pe false (ParsedIntegerContext.ofLinearIndex pe) (ParsedIntegerContext.ofLinearIndex pe)
        [0, 1, 2, 3] files0 0 0 outputs0 =
        .ok (files, bar0, bar1, outputs) ∧
      (∀ i : Fin 8, files.lm1 ⟨i.val, by have := i.isLt; change i.val < 4096; omega⟩ =
        reluWord (input ⟨i.val, by have := i.isLt; omega⟩)) ∧
      files.lm0 = files0.lm0 ∧
      bar0 = 0 ∧ bar1 = 0 := by
  obtain ⟨f1, b01, b11, o1, h0, v00, v01, lm0_0, hb01, hb11, fr0⟩ :=
    reluExpr0_cycle0_genericState_pe input pe currentState files0 outputs0 hmask
  obtain ⟨f2, b02, b12, o2, h1, v12, v13, lm0_1, hb02, hb12, fr1⟩ :=
    reluExpr0_cycle1_genericState_pe input pe currentState f1 o1 hmask
  obtain ⟨f3, b03, b13, o3, h2, v24, v25, lm0_2, hb03, hb13, fr2⟩ :=
    reluExpr0_cycle2_genericState_pe input pe currentState f2 o2 hmask
  obtain ⟨f4, b04, b14, o4, h3, v36, v37, lm0_3, hb04, hb14, fr3⟩ :=
    reluExpr0_cycle3_genericState_pe input pe currentState f3 o3 hmask
  refine ⟨f4, 0, 0, o4, ?_, ?_, ?_, rfl, rfl⟩
  · rw [reluSplit0123_state_pe input pe currentState, h0]; simp only []
    rw [hb01, hb11]
    rw [reluSplit123_state_pe input pe currentState, h1]; simp only []
    rw [hb02, hb12]
    rw [reluSplit23_state_pe input pe currentState, h2]; simp only []
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


theorem executeParsedFloatReluAtPE_pe_lm1_generic_pe
    (input : ProofsLean.MNCore.PlusOne.Words) (pe : PEId) (currentState : State)
    (files0 : IntegerRegisterFiles) (next : State)
    (hfiles : currentState.peRegisters pe = files0)
    (hmask : currentState.maskDirective = (welcomeInitialState input).maskDirective)
    (executed : executeParsedFloatReluAtPE (welcomeInitialState input) currentState
      reluExpr0 pe false false = .ok next) :
    ∀ i : Fin 8,
      (next.peRegisters pe).lm1
        ⟨i.val, by have := i.isLt; change i.val < 4096; omega⟩ =
      reluWord (input ⟨i.val, by have := i.isLt; omega⟩) := by
  obtain ⟨files, fbar0, fbar1, foutputs, hrun, hval, hlm0, hb0, hb1⟩ :=
    reluFold_genericState_pe input pe currentState files0 (fun _ => ⟨0, 0⟩) hmask
  rw [executeParsedFloatReluAtPE.eq_1] at executed
  dsimp only at executed
  split at executed
  · simp at executed
  · simp at executed
  · rename_i registers bar0 bar1 outputs ran
    rw [Id.run_pure] at executed
    simp only [StepResult.ok.injEq] at executed
    have hrun' :
        executeParsedFloatReluAtPE.runCycles (welcomeInitialState input) currentState
          reluExpr0 pe false (ParsedIntegerContext.ofLinearIndex pe) (ParsedIntegerContext.ofLinearIndex pe)
          [0, 1, 2, 3] files0 0 0 (fun _ => ⟨0, 0⟩) =
          .ok (files, fbar0, fbar1, foutputs) := hrun
    rw [hfiles] at ran
    change executeParsedFloatReluAtPE.runCycles (welcomeInitialState input) currentState
      reluExpr0 pe false (ParsedIntegerContext.ofLinearIndex pe) (ParsedIntegerContext.ofLinearIndex pe)
      [0, 1, 2, 3] files0 0 0 (fun _ => ⟨0, 0⟩) =
      .ok (registers, bar0, bar1, outputs) at ran
    rw [hrun'] at ran
    simp only [StepResult.ok.injEq] at ran
    obtain ⟨rfl, rfl, rfl, rfl⟩ := ran
    subst executed
    simpa using hval



/-- The first relu line executes at an arbitrary PE for any current write state
with the initial mask.  The read state is the initial (PE-uniform) state, so the
context bars are those of `welcomeInitialState`, i.e. zero. -/
theorem executeParsedFloatReluAtPE_reluExpr0_exists_pe
    (input : ProofsLean.MNCore.PlusOne.Words) (pe : PEId) (currentState : State)
    (hmask : currentState.maskDirective = (welcomeInitialState input).maskDirective) :
    ∃ next, executeParsedFloatReluAtPE (welcomeInitialState input) currentState
      reluExpr0 pe false false = .ok next := by
  obtain ⟨files, bar0, bar1, outputs, hrun, _⟩ :=
    reluFold_genericState_pe input pe currentState (currentState.peRegisters pe) (fun _ => ⟨0, 0⟩) hmask
  unfold executeParsedFloatReluAtPE
  rw [show (welcomeInitialState input).peContext pe = ParsedIntegerContext.ofLinearIndex pe
    from welcomeInitialState_context input pe]
  dsimp only
  generalize hbody : executeParsedFloatReluAtPE.runCycles (welcomeInitialState input) currentState
    reluExpr0 pe false (ParsedIntegerContext.ofLinearIndex pe) _ [0, 1, 2, 3]
    (currentState.peRegisters pe) _ _ (fun _ => ⟨0, 0⟩) = prepared at ⊢
  have hprep : prepared = .ok (files, bar0, bar1, outputs) := by
    rw [← hbody]
    exact hrun
  rw [hprep]
  exact ⟨_, rfl⟩


/-- A relu per-PE step preserves the mask directive. -/
theorem executeParsedFloatReluAtPE_maskDirective
    (input : ProofsLean.MNCore.PlusOne.Words) (pe : PEId) (currentState next : State)
    (executed : executeParsedFloatReluAtPE (welcomeInitialState input) currentState
      reluExpr0 pe false false = .ok next) :
    next.maskDirective = currentState.maskDirective := by
  unfold executeParsedFloatReluAtPE at executed
  dsimp only at executed
  split at executed
  · simp at executed
  · simp at executed
  · rename_i registers bar0 bar1 outputs
    cases executed
    rfl

/-- The 4096-PE walk of the first relu line succeeds for any list of PEs, from
any write state with the initial mask. -/
theorem executeParsedFloatReluAtPEs_reluExpr0_exists
    (input : ProofsLean.MNCore.PlusOne.Words) (pes : List PEId) (currentState : State)
    (hmask : currentState.maskDirective = (welcomeInitialState input).maskDirective) :
    ∃ next, executeParsedFloatReluAtPEs (welcomeInitialState input) currentState
      reluExpr0 pes false false = .ok next := by
  induction pes generalizing currentState with
  | nil => exact ⟨currentState, rfl⟩
  | cons pe rest ih =>
    obtain ⟨middle, hmiddle⟩ :=
      executeParsedFloatReluAtPE_reluExpr0_exists_pe input pe currentState hmask
    have hmask' : middle.maskDirective = (welcomeInitialState input).maskDirective := by
      rw [executeParsedFloatReluAtPE_maskDirective input pe currentState middle hmiddle]
      exact hmask
    obtain ⟨next, hnext⟩ := ih middle hmask'
    refine ⟨next, ?_⟩
    unfold executeParsedFloatReluAtPEs
    rw [hmiddle]
    exact hnext







end ProofsLean.MNCore
