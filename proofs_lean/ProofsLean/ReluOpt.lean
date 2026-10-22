import ProofsLean.ReluSealed
import ProofsLean.PlusTwoSuffixFrame

namespace ProofsLean.MNCore

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

open Issue
open ProofsLean.MNCore.PEMemory

/-- The `.lm0` long memory read only consults `files.lm0`. -/
theorem read_memory_lm0 (files : IntegerRegisterFiles)
    (slots : ProofsLean.MNCore.Forwarding.Slots) (c : Fin 4)
    (addr : Fin PEMemory.Bank.lm0.capacity) :
    ParsedIntegerInput.readWithForwarding files slots c
      (.memory ⟨.lm0, .long, addr⟩ false) =
    .ok (ParsedIntegerInput.applyRounding false
      (pack (readWords PEMemory.Bank.lm0 Width.long files.lm0 addr))) := rfl


/-- The sealed value model of `3.relu`: the same `InstructionLine` and `State`
as the whole machine, with the value transition `executeNormalizedLine`. -/
noncomputable def reluSealedMachine : ProofsLean.Machine where
  Line := InstructionLine
  State := State
  Input := ProofsLean.MNCore.PlusOne.Words
  step := fun line state =>
    match executeNormalizedLine line.toNormalizedLine state with
    | .ok next => some next
    | _ => none
  legal := fun _ => True
  lineCost := InstructionLine.cost
  positiveCost := InstructionLine.cost_positive

/-- The `3.relu` problem on the sealed model, observed at PE 0: LM1 words
`0..15` must be `reluWord input`. -/
noncomputable def reluSealedSpec : ProofsLean.Problem reluSealedMachine where
  admissible := fun _ => True
  initial := fun input => welcomeInitialState input
  post := fun input state => ∀ i : Fin 16,
    (state.peRegisters welcomePE).lm1
      ⟨i.val, by have := i.isLt; change i.val < 4096; omega⟩ =
      reluWord (input i)

/-- The accepted two-line answer. -/
def reluSealedAnswer : ProofsLean.Program reluSealedMachine :=
  [InstructionLine.pe [(reluExpr0).normalize],
   InstructionLine.pe [(reluExpr8).normalize]]

theorem reluSealedAnswer_score :
    ProofsLean.score reluSealedMachine reluSealedAnswer = 2 := rfl

/-- The LM0 long read at an arbitrary state whose PE-0 register file is the
initial one.  The forwarding slots are irrelevant for an `.lm0` memory read. -/
theorem reluRead_long_state (input : ProofsLean.MNCore.PlusOne.Words) (readState : State)
    (base : Nat) (c : Fin 4) (hbase : base + 2 * c.val + 1 < 16)
    (hreadLm0 : ∀ a, (readState.peRegisters 0).lm0 a = (welcomeInitialPERegisters input).lm0 a) :
    ProofsLean.MNCore.PEMemory.ParsedIntegerInput.readWithForwarding
      (readState.peRegisters 0) (stateForwardingSlots readState 0) c
      (.memory ⟨.lm0, .long,
        ⟨base + 2 * c.val, by have := c.isLt; change base + 2 * c.val < 4096; omega⟩⟩ false) =
    .ok ⟨input ⟨base + 2 * c.val, by omega⟩ ++
         input ⟨base + 2 * c.val + 1, by omega⟩, 0⟩ := by
  rw [read_memory_lm0]
  rw [show (readState.peRegisters 0).lm0 = (welcomeInitialPERegisters input).lm0 from funext hreadLm0]
  simpa [ParsedIntegerInput.readWithForwarding, ParsedIntegerInput.read, ParsedIntegerInput.applyRounding,
    readDirectAccess, readRegisterBank, welcomeInitialState] using
    reluInitial_readWithForwarding_long input base c hbase

theorem reluRead_long8_state_0 (input : ProofsLean.MNCore.PlusOne.Words) (readState : State)
    (hreadLm0 : ∀ a, (readState.peRegisters 0).lm0 a = (welcomeInitialPERegisters input).lm0 a) :
    ProofsLean.MNCore.PEMemory.ParsedIntegerInput.readWithForwarding
      (readState.peRegisters 0) (stateForwardingSlots readState 0) 0
      (.memory ⟨.lm0, .long, ⟨8, by decide⟩⟩ false) =
    .ok ⟨input ⟨8, by decide⟩ ++ input ⟨9, by decide⟩, 0⟩ := by
  rw [read_memory_lm0]
  rw [show (readState.peRegisters 0).lm0 = (welcomeInitialPERegisters input).lm0 from funext hreadLm0]
  simpa [ParsedIntegerInput.readWithForwarding, ParsedIntegerInput.read, ParsedIntegerInput.applyRounding,
    readDirectAccess, readRegisterBank, welcomeInitialState] using
    reluInitial_readWithForwarding_long8_0 input

theorem reluRead_long8_state_1 (input : ProofsLean.MNCore.PlusOne.Words) (readState : State)
    (hreadLm0 : ∀ a, (readState.peRegisters 0).lm0 a = (welcomeInitialPERegisters input).lm0 a) :
    ProofsLean.MNCore.PEMemory.ParsedIntegerInput.readWithForwarding
      (readState.peRegisters 0) (stateForwardingSlots readState 0) 1
      (.memory ⟨.lm0, .long, ⟨10, by decide⟩⟩ false) =
    .ok ⟨input ⟨10, by decide⟩ ++ input ⟨11, by decide⟩, 0⟩ := by
  rw [read_memory_lm0]
  rw [show (readState.peRegisters 0).lm0 = (welcomeInitialPERegisters input).lm0 from funext hreadLm0]
  simpa [ParsedIntegerInput.readWithForwarding, ParsedIntegerInput.read, ParsedIntegerInput.applyRounding,
    readDirectAccess, readRegisterBank, welcomeInitialState] using
    reluInitial_readWithForwarding_long8_1 input

theorem reluRead_long8_state_2 (input : ProofsLean.MNCore.PlusOne.Words) (readState : State)
    (hreadLm0 : ∀ a, (readState.peRegisters 0).lm0 a = (welcomeInitialPERegisters input).lm0 a) :
    ProofsLean.MNCore.PEMemory.ParsedIntegerInput.readWithForwarding
      (readState.peRegisters 0) (stateForwardingSlots readState 0) 2
      (.memory ⟨.lm0, .long, ⟨12, by decide⟩⟩ false) =
    .ok ⟨input ⟨12, by decide⟩ ++ input ⟨13, by decide⟩, 0⟩ := by
  rw [read_memory_lm0]
  rw [show (readState.peRegisters 0).lm0 = (welcomeInitialPERegisters input).lm0 from funext hreadLm0]
  simpa [ParsedIntegerInput.readWithForwarding, ParsedIntegerInput.read, ParsedIntegerInput.applyRounding,
    readDirectAccess, readRegisterBank, welcomeInitialState] using
    reluInitial_readWithForwarding_long8_2 input

theorem reluRead_long8_state_3 (input : ProofsLean.MNCore.PlusOne.Words) (readState : State)
    (hreadLm0 : ∀ a, (readState.peRegisters 0).lm0 a = (welcomeInitialPERegisters input).lm0 a) :
    ProofsLean.MNCore.PEMemory.ParsedIntegerInput.readWithForwarding
      (readState.peRegisters 0) (stateForwardingSlots readState 0) 3
      (.memory ⟨.lm0, .long, ⟨14, by decide⟩⟩ false) =
    .ok ⟨input ⟨14, by decide⟩ ++ input ⟨15, by decide⟩, 0⟩ := by
  rw [read_memory_lm0]
  rw [show (readState.peRegisters 0).lm0 = (welcomeInitialPERegisters input).lm0 from funext hreadLm0]
  simpa [ParsedIntegerInput.readWithForwarding, ParsedIntegerInput.read, ParsedIntegerInput.applyRounding,
    readDirectAccess, readRegisterBank, welcomeInitialState] using
    reluInitial_readWithForwarding_long8_3 input

theorem reluExpr8_cycle0_genericStateRead (input : ProofsLean.MNCore.PlusOne.Words)
    (readState : State)
    (hreadLm0 : ∀ a, (readState.peRegisters 0).lm0 a = (welcomeInitialPERegisters input).lm0 a)
    (hreadMask : readState.maskDirective = (welcomeInitialState input).maskDirective)
    (currentState : State) (files0 : IntegerRegisterFiles) (outputs : Fin 4 → IntegerALU.Bus)
    (hmask : currentState.maskDirective = (welcomeInitialState input).maskDirective) :
    ∃ files bar0 bar1 outputs',
      executeParsedFloatReluAtPE.runCycles readState currentState
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
  rw [reluRead_long8_state_0 input readState hreadLm0]
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
    PEMemory.distance, hmask, hreadMask, htarget, hentry,
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


theorem reluExpr8_cycle1_genericStateRead (input : ProofsLean.MNCore.PlusOne.Words)
    (readState : State)
    (hreadLm0 : ∀ a, (readState.peRegisters 0).lm0 a = (welcomeInitialPERegisters input).lm0 a)
    (hreadMask : readState.maskDirective = (welcomeInitialState input).maskDirective)
    (currentState : State) (files0 : IntegerRegisterFiles) (outputs : Fin 4 → IntegerALU.Bus)
    (hmask : currentState.maskDirective = (welcomeInitialState input).maskDirective) :
    ∃ files bar0 bar1 outputs',
      executeParsedFloatReluAtPE.runCycles readState currentState
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
  rw [reluRead_long8_state_1 input readState hreadLm0]
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
    PEMemory.distance, hmask, hreadMask, htarget, hentry,
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


theorem reluExpr8_cycle2_genericStateRead (input : ProofsLean.MNCore.PlusOne.Words)
    (readState : State)
    (hreadLm0 : ∀ a, (readState.peRegisters 0).lm0 a = (welcomeInitialPERegisters input).lm0 a)
    (hreadMask : readState.maskDirective = (welcomeInitialState input).maskDirective)
    (currentState : State) (files0 : IntegerRegisterFiles) (outputs : Fin 4 → IntegerALU.Bus)
    (hmask : currentState.maskDirective = (welcomeInitialState input).maskDirective) :
    ∃ files bar0 bar1 outputs',
      executeParsedFloatReluAtPE.runCycles readState currentState
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
  rw [reluRead_long8_state_2 input readState hreadLm0]
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
    PEMemory.distance, hmask, hreadMask, htarget, hentry,
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


theorem reluExpr8_cycle3_genericStateRead (input : ProofsLean.MNCore.PlusOne.Words)
    (readState : State)
    (hreadLm0 : ∀ a, (readState.peRegisters 0).lm0 a = (welcomeInitialPERegisters input).lm0 a)
    (hreadMask : readState.maskDirective = (welcomeInitialState input).maskDirective)
    (currentState : State) (files0 : IntegerRegisterFiles) (outputs : Fin 4 → IntegerALU.Bus)
    (hmask : currentState.maskDirective = (welcomeInitialState input).maskDirective) :
    ∃ files bar0 bar1 outputs',
      executeParsedFloatReluAtPE.runCycles readState currentState
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
  rw [reluRead_long8_state_3 input readState hreadLm0]
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
    PEMemory.distance, hmask, hreadMask, htarget, hentry,
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

theorem reluSplit8_0123_stateRead (input : ProofsLean.MNCore.PlusOne.Words) (readState : State)
    (currentState : State) (files : IntegerRegisterFiles) (bar0 bar1 : BitVec 12)
    (outputs : Fin 4 → IntegerALU.Bus) :
    executeParsedFloatReluAtPE.runCycles readState currentState
        reluExpr8 0 false (ParsedIntegerContext.ofLinearIndex 0) (ParsedIntegerContext.ofLinearIndex 0)
        [0, 1, 2, 3] files bar0 bar1 outputs =
      match executeParsedFloatReluAtPE.runCycles readState currentState
          reluExpr8 0 false (ParsedIntegerContext.ofLinearIndex 0) (ParsedIntegerContext.ofLinearIndex 0)
          [0] files bar0 bar1 outputs with
      | .ok (nextFiles, nextBar0, nextBar1, nextOutputs) =>
          executeParsedFloatReluAtPE.runCycles readState currentState
            reluExpr8 0 false (ParsedIntegerContext.ofLinearIndex 0) (ParsedIntegerContext.ofLinearIndex 0)
            [1, 2, 3] nextFiles nextBar0 nextBar1 nextOutputs
      | .failure => .failure
      | .unknown => .unknown := by
  rw [executeParsedFloatReluAtPE.runCycles]
  conv_rhs => rw [executeParsedFloatReluAtPE.runCycles]
  rfl


theorem reluSplit8_123_stateRead (input : ProofsLean.MNCore.PlusOne.Words) (readState : State)
    (currentState : State) (files : IntegerRegisterFiles) (bar0 bar1 : BitVec 12)
    (outputs : Fin 4 → IntegerALU.Bus) :
    executeParsedFloatReluAtPE.runCycles readState currentState
        reluExpr8 0 false (ParsedIntegerContext.ofLinearIndex 0) (ParsedIntegerContext.ofLinearIndex 0)
        [1, 2, 3] files bar0 bar1 outputs =
      match executeParsedFloatReluAtPE.runCycles readState currentState
          reluExpr8 0 false (ParsedIntegerContext.ofLinearIndex 0) (ParsedIntegerContext.ofLinearIndex 0)
          [1] files bar0 bar1 outputs with
      | .ok (nextFiles, nextBar0, nextBar1, nextOutputs) =>
          executeParsedFloatReluAtPE.runCycles readState currentState
            reluExpr8 0 false (ParsedIntegerContext.ofLinearIndex 0) (ParsedIntegerContext.ofLinearIndex 0)
            [2, 3] nextFiles nextBar0 nextBar1 nextOutputs
      | .failure => .failure
      | .unknown => .unknown := by
  rw [executeParsedFloatReluAtPE.runCycles]
  conv_rhs => rw [executeParsedFloatReluAtPE.runCycles]
  rfl


theorem reluSplit8_23_stateRead (input : ProofsLean.MNCore.PlusOne.Words) (readState : State)
    (currentState : State) (files : IntegerRegisterFiles) (bar0 bar1 : BitVec 12)
    (outputs : Fin 4 → IntegerALU.Bus) :
    executeParsedFloatReluAtPE.runCycles readState currentState
        reluExpr8 0 false (ParsedIntegerContext.ofLinearIndex 0) (ParsedIntegerContext.ofLinearIndex 0)
        [2, 3] files bar0 bar1 outputs =
      match executeParsedFloatReluAtPE.runCycles readState currentState
          reluExpr8 0 false (ParsedIntegerContext.ofLinearIndex 0) (ParsedIntegerContext.ofLinearIndex 0)
          [2] files bar0 bar1 outputs with
      | .ok (nextFiles, nextBar0, nextBar1, nextOutputs) =>
          executeParsedFloatReluAtPE.runCycles readState currentState
            reluExpr8 0 false (ParsedIntegerContext.ofLinearIndex 0) (ParsedIntegerContext.ofLinearIndex 0)
            [3] nextFiles nextBar0 nextBar1 nextOutputs
      | .failure => .failure
      | .unknown => .unknown := by
  rw [executeParsedFloatReluAtPE.runCycles]
  conv_rhs => rw [executeParsedFloatReluAtPE.runCycles]
  rfl


theorem reluFold8_genericStateRead (input : ProofsLean.MNCore.PlusOne.Words)
    (readState : State)
    (hreadLm0 : ∀ a, (readState.peRegisters 0).lm0 a = (welcomeInitialPERegisters input).lm0 a)
    (hreadMask : readState.maskDirective = (welcomeInitialState input).maskDirective)
    (currentState : State) (files0 : IntegerRegisterFiles) (outputs0 : Fin 4 → IntegerALU.Bus)
    (hmask : currentState.maskDirective = (welcomeInitialState input).maskDirective) :
    ∃ files bar0 bar1 outputs,
      executeParsedFloatReluAtPE.runCycles readState currentState
        reluExpr8 0 false (ParsedIntegerContext.ofLinearIndex 0) (ParsedIntegerContext.ofLinearIndex 0)
        [0, 1, 2, 3] files0 0 0 outputs0 =
        .ok (files, bar0, bar1, outputs) ∧
      (∀ i : Fin 8, files.lm1 ⟨8 + i.val, by have := i.isLt; change 8 + i.val < 4096; omega⟩ =
        reluWord (input ⟨8 + i.val, by have := i.isLt; omega⟩)) ∧
      files.lm0 = files0.lm0 ∧
      bar0 = 0 ∧ bar1 = 0 := by
  obtain ⟨f1, b01, b11, o1, h0, v00, v01, lm0_0, hb01, hb11, fr0⟩ :=
    reluExpr8_cycle0_genericStateRead input readState hreadLm0 hreadMask currentState files0 outputs0 hmask
  obtain ⟨f2, b02, b12, o2, h1, v12, v13, lm0_1, hb02, hb12, fr1⟩ :=
    reluExpr8_cycle1_genericStateRead input readState hreadLm0 hreadMask currentState f1 o1 hmask
  obtain ⟨f3, b03, b13, o3, h2, v24, v25, lm0_2, hb03, hb13, fr2⟩ :=
    reluExpr8_cycle2_genericStateRead input readState hreadLm0 hreadMask currentState f2 o2 hmask
  obtain ⟨f4, b04, b14, o4, h3, v36, v37, lm0_3, hb04, hb14, fr3⟩ :=
    reluExpr8_cycle3_genericStateRead input readState hreadLm0 hreadMask currentState f3 o3 hmask
  refine ⟨f4, 0, 0, o4, ?_, ?_, ?_, rfl, rfl⟩
  · rw [reluSplit8_0123_stateRead input readState currentState, h0]; simp only []
    rw [hb01, hb11]
    rw [reluSplit8_123_stateRead input readState currentState, h1]; simp only []
    rw [hb02, hb12]
    rw [reluSplit8_23_stateRead input readState currentState, h2]; simp only []
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


theorem executeParsedFloatReluAtPE_pe_lm1_8_genericRead
    (input : ProofsLean.MNCore.PlusOne.Words) (readState : State)
    (hreadLm0 : ∀ a, (readState.peRegisters 0).lm0 a = (welcomeInitialPERegisters input).lm0 a)
    (hreadMask : readState.maskDirective = (welcomeInitialState input).maskDirective)
    (hreadCtx : readState.peContext 0 = (welcomeInitialState input).peContext 0)
    (currentState : State)
    (files0 : IntegerRegisterFiles) (next : State)
    (hfiles : currentState.peRegisters 0 = files0)
    (hmask : currentState.maskDirective = (welcomeInitialState input).maskDirective)
    (executed : executeParsedFloatReluAtPE readState currentState
      reluExpr8 0 false false = .ok next) :
    ∀ i : Fin 8,
      (next.peRegisters welcomePE).lm1
        ⟨8 + i.val, by have := i.isLt; change 8 + i.val < 4096; omega⟩ =
      reluWord (input ⟨8 + i.val, by have := i.isLt; omega⟩) := by
  obtain ⟨files, fbar0, fbar1, foutputs, hrun, hval, hlm0, hb0, hb1⟩ :=
    reluFold8_genericStateRead input readState hreadLm0 hreadMask currentState files0 (fun _ => ⟨0, 0⟩) hmask
  rw [executeParsedFloatReluAtPE.eq_1] at executed
  dsimp only at executed
  split at executed
  · simp at executed
  · simp at executed
  · rename_i registers bar0 bar1 outputs ran
    rw [Id.run_pure] at executed
    simp only [StepResult.ok.injEq] at executed
    have hrun' :
        executeParsedFloatReluAtPE.runCycles readState currentState
          reluExpr8 0 false (ParsedIntegerContext.ofLinearIndex 0) (ParsedIntegerContext.ofLinearIndex 0)
          [0, 1, 2, 3] files0 0 0 (fun _ => ⟨0, 0⟩) =
          .ok (files, fbar0, fbar1, foutputs) := hrun
    rw [hfiles] at ran
    rw [hreadCtx] at ran
    change executeParsedFloatReluAtPE.runCycles readState currentState
      reluExpr8 0 false (ParsedIntegerContext.ofLinearIndex 0) (ParsedIntegerContext.ofLinearIndex 0)
      [0, 1, 2, 3] files0 0 0 (fun _ => ⟨0, 0⟩) =
      .ok (registers, bar0, bar1, outputs) at ran
    rw [hrun'] at ran
    simp only [StepResult.ok.injEq] at ran
    obtain ⟨rfl, rfl, rfl, rfl⟩ := ran
    subst executed
    simp only [welcomePE]
    exact hval

#print axioms executeParsedFloatReluAtPE_pe_lm1_8_generic


theorem executeParsedFloatReluAtPEs_finRange_pe0_lm1_8_genericRead
    (input : ProofsLean.MNCore.PlusOne.Words) (readState : State)
    (hreadLm0 : ∀ a, (readState.peRegisters 0).lm0 a = (welcomeInitialPERegisters input).lm0 a)
    (hreadMask : readState.maskDirective = (welcomeInitialState input).maskDirective)
    (hreadCtx : readState.peContext 0 = (welcomeInitialState input).peContext 0)
    (currentState : State)
    (files0 : IntegerRegisterFiles) (next : State)
    (hfiles : currentState.peRegisters 0 = files0)
    (hmask : currentState.maskDirective = (welcomeInitialState input).maskDirective)
    (executed : executeParsedFloatReluAtPEs readState currentState
      reluExpr8 (List.finRange 4096) false false = .ok next) :
    ∀ i : Fin 8,
      (next.peRegisters welcomePE).lm1
        ⟨8 + i.val, by have := i.isLt; change 8 + i.val < 4096; omega⟩ =
      reluWord (input ⟨8 + i.val, by have := i.isLt; omega⟩) := by
  rw [finRange4096_eq_welcomePE_cons] at executed
  simp only [executeParsedFloatReluAtPEs] at executed
  cases head : executeParsedFloatReluAtPE readState currentState
      reluExpr8 welcomePE false false with
  | failure => simp [head] at executed
  | unknown => simp [head] at executed
  | ok middle =>
    simp only [head] at executed
    have hvalues := executeParsedFloatReluAtPE_pe_lm1_8_genericRead input readState hreadLm0 hreadMask hreadCtx
      currentState files0 middle hfiles hmask head
    have hframe : next.peRegisters welcomePE = middle.peRegisters welcomePE :=
      executeParsedFloatReluAtPEs_peRegisters_not_mem readState reluExpr8
        false false ((List.finRange 4095).map Fin.succ) middle next welcomePE
        (by simp [welcomePE]) executed
    intro i
    rw [hframe]
    exact hvalues i


/-- The empty integer-expression core step does not change the PE context. -/
theorem executeIntegerProducerLineAtPECore_nil_peContext (state : State) (pe : PEId) (next : State)
    (h : executeIntegerProducerLineAtPECore [] state pe = .ok next) :
    next.peContext = state.peContext := by
  unfold executeIntegerProducerLineAtPECore at h
  dsimp only at h
  simp only [List.filter_nil, List.any_nil, List.all_nil] at h
  generalize hfour : parsedIntegerMatrixReadLineFourCycleStep (state.peRegisters pe)
    (stateForwardingSlots state pe)
    (state.matrixRegisters (ParsedIntegerContext.ofLinearIndex pe).group
      (ParsedIntegerContext.ofLinearIndex pe).l2b
      (ParsedIntegerContext.ofLinearIndex pe).l1b)
    [] _ false = prepared at h
  have hnil : prepared = .ok (state.peRegisters pe, stateForwardingSlots state pe, []) := by
    rw [← hfour]; rfl
  rw [hnil] at h
  dsimp only at h
  generalize hfloat : executeParsedFloatMAUsAtPE (state.peRegisters pe) (state.peRegisters pe)
    (stateForwardingSlots state pe) _ [] state.maskDirective false = prepared2 at h
  have hfloatNil : prepared2 = .ok (state.peRegisters pe, (state.peContext pe).bar0,
      (state.peContext pe).bar1, (fun _ => ⟨0, 0⟩), false) := by
    rw [← hfloat]; rfl
  rw [hfloatNil] at h
  dsimp only at h
  generalize hfwd : updateSupportedPELineForwarding (stateForwardingSlots state pe)
    (fun unit cycle =>
      if (decide (unit = Forwarding.Unit.mau) && false) = true then
        Forwarding.Value.known ((fun _ => ⟨0, 0⟩) cycle)
      else (stateForwardingSlots state pe) unit cycle)
    false false false false = prepared3 at h
  cases prepared3 with
  | failure => simp at h
  | unknown => simp at h
  | ok forwarding =>
    simp only [StepResult.ok.injEq] at h
    subst h
    funext other
    by_cases same : other = pe
    · subst other
      cases hctx : state.peContext pe
      simp [hctx]
    · simp [same]

/-- The empty integer-expression walk over all 4096 PEs does not change PE 0's
context. -/
theorem executeIntegerProducerLineAtPEs_nil_peContext_welcomePE (state next : State)
    (h : executeIntegerProducerLineAtPEs [] (List.finRange 4096) state = .ok next) :
    next.peContext welcomePE = state.peContext welcomePE := by
  rw [finRange4096_eq_welcomePE_cons] at h
  simp only [executeIntegerProducerLineAtPEs] at h
  split at h
  · simp at h
  · simp at h
  · rename_i middle head
    have hcore : executeIntegerProducerLineAtPECore [] state welcomePE = .ok middle := by
      simpa [executeIntegerProducerLineAtPE] using head
    have hhead : middle.peContext welcomePE = state.peContext welcomePE :=
      congrFun (executeIntegerProducerLineAtPECore_nil_peContext state welcomePE middle hcore) welcomePE
    have htail : next.peContext welcomePE = middle.peContext welcomePE :=
      executeIntegerProducerLineAtPEs_peContext_of_not_mem [] ((List.finRange 4095).map Fin.succ)
        middle next welcomePE (by simp [welcomePE]) h
    rw [htail, hhead]


theorem reluLine8_step_lm1_readState (input : ProofsLean.MNCore.PlusOne.Words)
    (currentState : State) (next : State)
    (hfilesInit : ∀ a, (currentState.peRegisters 0).lm0 a = (welcomeInitialPERegisters input).lm0 a)
    (hmask : currentState.maskDirective = (welcomeInitialState input).maskDirective)
    (hctx : currentState.peContext 0 = (welcomeInitialState input).peContext 0)
    (step : executeNormalizedLine (.pe [(reluExpr8).normalize]) currentState = .ok next) :
    ∀ (j : Fin PEMemory.Bank.lm1.capacity) (hj : j.val < 8),
      (next.peRegisters welcomePE).lm1 ⟨8 + j.val, by have := j.isLt; change 8 + j.val < 4096; omega⟩ =
      reluWord (input ⟨8 + j.val, by have := j.isLt; omega⟩) := by
  unfold executeNormalizedLine at step
  simp only [NormalizedLine.toInstruction?] at step
  have hcheck : checkParsedTopLine (InstructionLine.pe [(reluExpr8).normalize]).toParsed = true := by
    show checkParsedLine [(reluExpr8).normalize.toParsed] = true
    simpa using check_of_legal [reluExpr8] reluExpr8_legal
  have hparsed : ([(reluExpr8).normalize].map NormalizedExpr.toParsed) = [reluExpr8] := rfl
  have hwait : ([(reluExpr8).normalize].map NormalizedExpr.toParsed).any
      (parsedExprWaitPending currentState) = false := by
    rw [hparsed]
    simp [parsedExprWaitPending, parsedExprWaitTag?, reluExpr8, reluOp]
  have hunsup : ([(reluExpr8).normalize].map NormalizedExpr.toParsed).any
      parsedExprIsUnsupportedRustAlu = false := by
    rw [hparsed]
    simp [parsedExprIsUnsupportedRustAlu, reluExpr8, reluOp]
  have hsup : ([(reluExpr8).normalize].map NormalizedExpr.toParsed).all
      parsedExprIsSupportedPELineProducer = true := by
    rw [hparsed]
    simp [parsedExprIsSupportedPELineProducer, reluExpr8, reluOp]
  obtain ⟨nextPEs, nextMsl, nextRelu, nextBlockFloat, afterMatrix, nextShared, nextBroadcast,
    walkExecuted, mslExecuted, reluExecuted, blockExecuted, matrixExecuted, sharedExecuted,
    l1Executed, nextEq⟩ :=
    executeIntegerProducerInstructionLine_pe_stages_exists [(reluExpr8).normalize] currentState
      next hcheck hwait hunsup hsup step
  have hnf : ([(reluExpr8).normalize].any
      (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed)) = false := by
    decide
  have hmaskAny : ([(reluExpr8).normalize].any
      (parsedExprHasSingleLineWriteMask ∘ NormalizedExpr.toParsed)) = false := by
    decide
  have hint : (List.filter (fun expression =>
      !parsedExprIsL2BMProducer expression && !parsedExprIsMslMsrProducer expression &&
        !parsedExprIsMatrixMAUProducer expression && !parsedExprIsBlockFloatProducer expression &&
        !parsedExprIsFloatReluProducer expression)
      ([(reluExpr8).normalize].map NormalizedExpr.toParsed)) = [] := by
    rw [hparsed]
    have h : parsedExprIsFloatReluProducer reluExpr8 = true := rfl
    simp [h]
  rw [hint] at walkExecuted
  have hmslId : executeParsedMslMsrProducers currentState nextPEs
      ([(reluExpr8).normalize].map NormalizedExpr.toParsed)
      (([(reluExpr8).normalize].any
        (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed)))
      (([(reluExpr8).normalize].any
        (parsedExprHasSingleLineWriteMask ∘ NormalizedExpr.toParsed))) = .ok nextPEs := by
    apply executeParsedMslMsrProducers_eq_self
    rw [hparsed]
    have h : parsedExprIsMslMsrProducer reluExpr8 = false := rfl
    simp [h, List.filter]
  rw [hparsed] at hmslId
  rw [hparsed] at mslExecuted
  rw [hmslId] at mslExecuted
  have hmslEq : nextMsl = nextPEs := (StepResult.ok.inj mslExecuted).symm
  have hframeFiles : nextPEs.peRegisters 0 = currentState.peRegisters 0 := by
    obtain ⟨next', hnext', hframe⟩ :=
      executeIntegerProducerLineAtPEs_nil_peRegisters (List.finRange 4096) currentState 0
    rw [walkExecuted] at hnext'
    have hEq : nextPEs = next' := StepResult.ok.inj hnext'
    subst hEq
    exact hframe
  have hframeMask : nextPEs.maskDirective = currentState.maskDirective :=
    (executeIntegerProducerLineAtPEs_maskDirective_hazardClock [] (List.finRange 4096)
      currentState nextPEs walkExecuted).1
  have hframeCtx : nextPEs.peContext welcomePE = currentState.peContext welcomePE :=
    executeIntegerProducerLineAtPEs_nil_peContext_welcomePE currentState nextPEs walkExecuted
  have hmask' : nextPEs.maskDirective = (welcomeInitialState input).maskDirective :=
    hframeMask.trans hmask
  rw [hmslEq] at reluExecuted
  have hreluId : executeParsedFloatReluProducers currentState nextPEs
      ([(reluExpr8).normalize].map NormalizedExpr.toParsed)
      (([(reluExpr8).normalize].any
        (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed)))
      (([(reluExpr8).normalize].any
        (parsedExprHasSingleLineWriteMask ∘ NormalizedExpr.toParsed))) =
      executeParsedFloatReluAtPEs currentState nextPEs reluExpr8
        (List.finRange 4096) false false := by
    rw [hparsed, hnf, hmaskAny]
    simp [executeParsedFloatReluProducers, parsedExprIsFloatReluProducer, reluExpr8, reluOp]
  rw [hreluId] at reluExecuted
  cases hrun : executeParsedFloatReluAtPEs currentState nextPEs reluExpr8
      (List.finRange 4096) false false with
  | failure => simp [hrun] at reluExecuted
  | unknown => simp [hrun] at reluExecuted
  | ok middle =>
    simp only [hrun, StepResult.ok.injEq] at reluExecuted
    subst reluExecuted
    have hblockId : executeParsedBlockFloatProducer currentState middle
        ([(reluExpr8).normalize].map NormalizedExpr.toParsed)
        ([(reluExpr8).normalize].any (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed))
        ([(reluExpr8).normalize].any (parsedExprHasSingleLineWriteMask ∘ NormalizedExpr.toParsed)) =
        .ok middle := by
      apply executeParsedBlockFloatProducer_eq_self
      rw [hparsed]
      simp [parsedExprIsBlockFloatProducer, reluExpr8, reluOp, List.filter]
    rw [hblockId] at blockExecuted
    have hblockEq : nextBlockFloat = middle := (StepResult.ok.inj blockExecuted).symm
    subst nextBlockFloat
    have hmatrixId : executeParsedMatrixMAUAndWrites currentState middle
        ([(reluExpr8).normalize].map NormalizedExpr.toParsed)
        ([(reluExpr8).normalize].any (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed))
        ([(reluExpr8).normalize].any (parsedExprHasSingleLineWriteMask ∘ NormalizedExpr.toParsed)) =
        .ok middle := by
      apply executeParsedMatrixMAUAndWrites_eq_self
      · rw [hparsed]
        simp [parsedExprIsMatrixMAUProducer, reluExpr8, reluOp, List.filter]
      · rw [hparsed]
        simp [parsedExprIsMatrixWriteProducer, reluExpr8, reluOp]
    rw [hmatrixId] at matrixExecuted
    have hmatrixEq : afterMatrix = middle := (StepResult.ok.inj matrixExecuted).symm
    subst afterMatrix
    have hsharedId : executeParsedSharedBlockProducers currentState middle
        ([(reluExpr8).normalize].map NormalizedExpr.toParsed)
        (!([(reluExpr8).normalize].any (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed))) =
        .ok middle := by
      rw [hparsed]
      apply executeParsedSharedBlockProducerList_eq_self
      intro e mem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
      subst e
      simp [executeParsedSharedBlockExpression, reluExpr8, reluOp]
    rw [hsharedId] at sharedExecuted
    have hsharedEq : nextShared = middle := (StepResult.ok.inj sharedExecuted).symm
    subst nextShared
    have hl1Id : executeParsedL1ToPEProducers currentState middle
        ([(reluExpr8).normalize].map NormalizedExpr.toParsed)
        ([(reluExpr8).normalize].any (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed))
        ([(reluExpr8).normalize].any (parsedExprHasSingleLineWriteMask ∘ NormalizedExpr.toParsed))
        (parsedL1ToPEPrecedesOMRWriter ([(reluExpr8).normalize].map NormalizedExpr.toParsed)) =
        .ok middle := by
      apply executeParsedL1ToPEProducers_eq_self
      rw [hparsed]
      simp [parsedExprIsL1ToPEProducer, reluExpr8, reluOp, List.filter]
    rw [hl1Id] at l1Executed
    have hl1Eq : nextBroadcast = middle := (StepResult.ok.inj l1Executed).symm
    subst nextBroadcast
    intro j hj
    have hval := executeParsedFloatReluAtPEs_finRange_pe0_lm1_8_genericRead input currentState
      hfilesInit hmask hctx nextPEs (nextPEs.peRegisters 0) middle rfl hmask' hrun
    rw [nextEq]
    let i : Fin 8 := ⟨j.val, hj⟩
    have hv := hval i
    simpa using hv

/-- The first relu line executes at PE 0 for any current write state with the
initial mask. -/
theorem executeParsedFloatReluAtPE_reluExpr0_exists
    (input : ProofsLean.MNCore.PlusOne.Words) (currentState : State)
    (hmask : currentState.maskDirective = (welcomeInitialState input).maskDirective) :
    ∃ next, executeParsedFloatReluAtPE (welcomeInitialState input) currentState
      reluExpr0 0 false false = .ok next := by
  obtain ⟨files, bar0, bar1, outputs, hrun, hval, hlm0, hbar0, hbar1⟩ :=
    reluFold_genericState input currentState (currentState.peRegisters 0) (fun _ => ⟨0, 0⟩) hmask
  unfold executeParsedFloatReluAtPE
  rw [show (welcomeInitialState input).peContext 0 = ParsedIntegerContext.ofLinearIndex 0
    from welcomeInitialState_context input 0]
  dsimp only
  generalize hbody : executeParsedFloatReluAtPE.runCycles (welcomeInitialState input) currentState
    reluExpr0 0 false (ParsedIntegerContext.ofLinearIndex 0) _ [0, 1, 2, 3]
    (currentState.peRegisters 0) _ _ (fun _ => ⟨0, 0⟩) = prepared at ⊢
  have hprep : prepared = .ok (files, bar0, bar1, outputs) := by
    rw [← hbody]
    exact hrun
  rw [hprep]
  exact ⟨_, rfl⟩

end ProofsLean.MNCore
