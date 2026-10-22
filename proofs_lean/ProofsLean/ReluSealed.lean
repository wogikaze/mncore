import ProofsLean.ReluFold
import ProofsLean.WelcomeAssembly
import ProofsLean.LineExec
import ProofsLean.InputDependence
import ProofsLean.WelcomePlainClose
import ProofsLean.CendAnswerCorrect

/-! # `3.relu`: the empty integer stage and the generic four-cycle fold

This module fixes the two plumbing facts needed to lift `ReluFold` to a line
step whose integer producer filter is empty:

* `executeIntegerProducerLineAtPECore_nil_peRegisters` and
  `executeIntegerProducerLineAtPEs_nil_peRegisters` — the empty integer stage
  preserves the per-PE register files;
* `reluFold_generic` — the four-cycle relu fold for an arbitrary initial
  register file and output bus.

The line-level `Correct` of the sealed machine and `LowerBound 2` are not yet
claimed here.  No `sorry`, no `admit`, no new axioms. -/

namespace ProofsLean.MNCore

open Issue
open ProofsLean.MNCore.PEMemory

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

/-- The empty integer producer stage preserves the whole per-PE register file
function (only forwarding slots change). -/
theorem executeIntegerProducerLineAtPECore_nil_peRegisters (state : State) (pe : PEId) :
    ∃ next, executeIntegerProducerLineAtPECore [] state pe = .ok next ∧
      next.peRegisters = state.peRegisters := by
  unfold executeIntegerProducerLineAtPECore
  simp only [prepareParsedIntegerMatrixReadLineCycles,
    prepareParsedIntegerMatrixReadLineExpressions,
    parsedIntegerMatrixReadLineFourCycleStep,
    executeParsedFloatMAUsAtPE, List.filter_nil, List.any_nil, List.isEmpty_nil,
    Bool.not_true, Bool.false_eq_true, commitParsedMaskedWrites_nil]
  refine ⟨_, rfl, ?_⟩
  funext other
  by_cases h : other = pe
  · simp [h]
  · simp [h]

/-- The 4096-PE walk of the empty integer producer stage preserves the files of
every PE. -/
theorem executeIntegerProducerLineAtPEs_nil_peRegisters (pes : List PEId) (state : State) (p : PEId) :
    ∃ next, executeIntegerProducerLineAtPEs [] pes state = .ok next ∧
      next.peRegisters p = state.peRegisters p := by
  induction pes generalizing state with
  | nil => exact ⟨state, rfl, rfl⟩
  | cons pe rest ih =>
    simp only [executeIntegerProducerLineAtPEs]
    cases h : executeIntegerProducerLineAtPE [] state pe with
    | failure =>
      exfalso
      obtain ⟨next', hnext', _⟩ := executeIntegerProducerLineAtPECore_nil_peRegisters state pe
      have hpe : executeIntegerProducerLineAtPE [] state pe =
          executeIntegerProducerLineAtPECore [] state pe := rfl
      rw [hpe, hnext'] at h
      simp at h
    | unknown =>
      exfalso
      obtain ⟨next', hnext', _⟩ := executeIntegerProducerLineAtPECore_nil_peRegisters state pe
      have hpe : executeIntegerProducerLineAtPE [] state pe =
          executeIntegerProducerLineAtPECore [] state pe := rfl
      rw [hpe, hnext'] at h
      simp at h
    | ok middle =>
      obtain ⟨next, hnext, htail⟩ := ih middle
      refine ⟨next, hnext, ?_⟩
      rw [htail]
      by_cases hp : p = pe
      · subst p
        obtain ⟨next', hnext', hregs⟩ := executeIntegerProducerLineAtPECore_nil_peRegisters state pe
        have hmid : middle = next' := by
          rw [show executeIntegerProducerLineAtPE [] state pe =
            executeIntegerProducerLineAtPECore [] state pe from rfl] at h
          rw [hnext'] at h
          exact (StepResult.ok.inj h).symm
        subst hmid
        exact congrFun hregs pe
      · exact (executeIntegerProducerLineAtPE_peFields_other [] state middle pe p hp h).1

/-- The four-cycle fold of the first accepted line, for an arbitrary initial
register file and output bus. -/
theorem reluFold_generic (input : ProofsLean.MNCore.PlusOne.Words)
    (files0 : IntegerRegisterFiles) (outputs0 : Fin 4 → IntegerALU.Bus) :
    ∃ files bar0 bar1 outputs,
      executeParsedFloatReluAtPE.runCycles (welcomeInitialState input) (welcomeInitialState input)
        reluExpr0 0 false (ParsedIntegerContext.ofLinearIndex 0) (ParsedIntegerContext.ofLinearIndex 0)
        [0, 1, 2, 3] files0 0 0 outputs0 =
        .ok (files, bar0, bar1, outputs) ∧
      (∀ i : Fin 8, files.lm1 ⟨i.val, by have := i.isLt; change i.val < 4096; omega⟩ =
        reluWord (input ⟨i.val, by have := i.isLt; omega⟩)) ∧
      files.lm0 = files0.lm0 ∧
      bar0 = 0 ∧ bar1 = 0 := by
  obtain ⟨f1, b01, b11, o1, h0, v00, v01, lm0_0, hb01, hb11, fr0⟩ :=
    reluExpr0_cycle0_generic input files0 outputs0
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

#print axioms executeIntegerProducerLineAtPECore_nil_peRegisters
#print axioms executeIntegerProducerLineAtPEs_nil_peRegisters
#print axioms reluFold_generic


theorem reluExpr0_cycle0_genericState (input : ProofsLean.MNCore.PlusOne.Words)
    (currentState : State) (files0 : IntegerRegisterFiles) (outputs : Fin 4 → IntegerALU.Bus)
    (hmask : currentState.maskDirective = (welcomeInitialState input).maskDirective) :
    ∃ files bar0 bar1 outputs',
      executeParsedFloatReluAtPE.runCycles (welcomeInitialState input) currentState
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




theorem reluExpr0_cycle1_genericState (input : ProofsLean.MNCore.PlusOne.Words)
    (currentState : State) (files0 : IntegerRegisterFiles) (outputs : Fin 4 → IntegerALU.Bus)
    (hmask : currentState.maskDirective = (welcomeInitialState input).maskDirective) :
    ∃ files bar0 bar1 outputs',
      executeParsedFloatReluAtPE.runCycles (welcomeInitialState input) currentState
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




theorem reluExpr0_cycle2_genericState (input : ProofsLean.MNCore.PlusOne.Words)
    (currentState : State) (files0 : IntegerRegisterFiles) (outputs : Fin 4 → IntegerALU.Bus)
    (hmask : currentState.maskDirective = (welcomeInitialState input).maskDirective) :
    ∃ files bar0 bar1 outputs',
      executeParsedFloatReluAtPE.runCycles (welcomeInitialState input) currentState
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



theorem reluExpr0_cycle3_genericState (input : ProofsLean.MNCore.PlusOne.Words)
    (currentState : State) (files0 : IntegerRegisterFiles) (outputs : Fin 4 → IntegerALU.Bus)
    (hmask : currentState.maskDirective = (welcomeInitialState input).maskDirective) :
    ∃ files bar0 bar1 outputs',
      executeParsedFloatReluAtPE.runCycles (welcomeInitialState input) currentState
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



theorem reluSplit0123_state (input : ProofsLean.MNCore.PlusOne.Words)
    (currentState : State) (files : IntegerRegisterFiles) (bar0 bar1 : BitVec 12)
    (outputs : Fin 4 → IntegerALU.Bus) :
    executeParsedFloatReluAtPE.runCycles (welcomeInitialState input) currentState
        reluExpr0 0 false (ParsedIntegerContext.ofLinearIndex 0) (ParsedIntegerContext.ofLinearIndex 0)
        [0, 1, 2, 3] files bar0 bar1 outputs =
      match executeParsedFloatReluAtPE.runCycles (welcomeInitialState input) currentState
          reluExpr0 0 false (ParsedIntegerContext.ofLinearIndex 0) (ParsedIntegerContext.ofLinearIndex 0)
          [0] files bar0 bar1 outputs with
      | .ok (nextFiles, nextBar0, nextBar1, nextOutputs) =>
          executeParsedFloatReluAtPE.runCycles (welcomeInitialState input) currentState
            reluExpr0 0 false (ParsedIntegerContext.ofLinearIndex 0) (ParsedIntegerContext.ofLinearIndex 0)
            [1, 2, 3] nextFiles nextBar0 nextBar1 nextOutputs
      | .failure => .failure
      | .unknown => .unknown := by
  rw [executeParsedFloatReluAtPE.runCycles]
  conv_rhs => rw [executeParsedFloatReluAtPE.runCycles]
  rfl


theorem reluSplit123_state (input : ProofsLean.MNCore.PlusOne.Words)
    (currentState : State) (files : IntegerRegisterFiles) (bar0 bar1 : BitVec 12)
    (outputs : Fin 4 → IntegerALU.Bus) :
    executeParsedFloatReluAtPE.runCycles (welcomeInitialState input) currentState
        reluExpr0 0 false (ParsedIntegerContext.ofLinearIndex 0) (ParsedIntegerContext.ofLinearIndex 0)
        [1, 2, 3] files bar0 bar1 outputs =
      match executeParsedFloatReluAtPE.runCycles (welcomeInitialState input) currentState
          reluExpr0 0 false (ParsedIntegerContext.ofLinearIndex 0) (ParsedIntegerContext.ofLinearIndex 0)
          [1] files bar0 bar1 outputs with
      | .ok (nextFiles, nextBar0, nextBar1, nextOutputs) =>
          executeParsedFloatReluAtPE.runCycles (welcomeInitialState input) currentState
            reluExpr0 0 false (ParsedIntegerContext.ofLinearIndex 0) (ParsedIntegerContext.ofLinearIndex 0)
            [2, 3] nextFiles nextBar0 nextBar1 nextOutputs
      | .failure => .failure
      | .unknown => .unknown := by
  rw [executeParsedFloatReluAtPE.runCycles]
  conv_rhs => rw [executeParsedFloatReluAtPE.runCycles]
  rfl


theorem reluSplit23_state (input : ProofsLean.MNCore.PlusOne.Words)
    (currentState : State) (files : IntegerRegisterFiles) (bar0 bar1 : BitVec 12)
    (outputs : Fin 4 → IntegerALU.Bus) :
    executeParsedFloatReluAtPE.runCycles (welcomeInitialState input) currentState
        reluExpr0 0 false (ParsedIntegerContext.ofLinearIndex 0) (ParsedIntegerContext.ofLinearIndex 0)
        [2, 3] files bar0 bar1 outputs =
      match executeParsedFloatReluAtPE.runCycles (welcomeInitialState input) currentState
          reluExpr0 0 false (ParsedIntegerContext.ofLinearIndex 0) (ParsedIntegerContext.ofLinearIndex 0)
          [2] files bar0 bar1 outputs with
      | .ok (nextFiles, nextBar0, nextBar1, nextOutputs) =>
          executeParsedFloatReluAtPE.runCycles (welcomeInitialState input) currentState
            reluExpr0 0 false (ParsedIntegerContext.ofLinearIndex 0) (ParsedIntegerContext.ofLinearIndex 0)
            [3] nextFiles nextBar0 nextBar1 nextOutputs
      | .failure => .failure
      | .unknown => .unknown := by
  rw [executeParsedFloatReluAtPE.runCycles]
  conv_rhs => rw [executeParsedFloatReluAtPE.runCycles]
  rfl



theorem reluFold_genericState (input : ProofsLean.MNCore.PlusOne.Words)
    (currentState : State) (files0 : IntegerRegisterFiles) (outputs0 : Fin 4 → IntegerALU.Bus)
    (hmask : currentState.maskDirective = (welcomeInitialState input).maskDirective) :
    ∃ files bar0 bar1 outputs,
      executeParsedFloatReluAtPE.runCycles (welcomeInitialState input) currentState
        reluExpr0 0 false (ParsedIntegerContext.ofLinearIndex 0) (ParsedIntegerContext.ofLinearIndex 0)
        [0, 1, 2, 3] files0 0 0 outputs0 =
        .ok (files, bar0, bar1, outputs) ∧
      (∀ i : Fin 8, files.lm1 ⟨i.val, by have := i.isLt; change i.val < 4096; omega⟩ =
        reluWord (input ⟨i.val, by have := i.isLt; omega⟩)) ∧
      files.lm0 = files0.lm0 ∧
      bar0 = 0 ∧ bar1 = 0 := by
  obtain ⟨f1, b01, b11, o1, h0, v00, v01, lm0_0, hb01, hb11, fr0⟩ :=
    reluExpr0_cycle0_genericState input currentState files0 outputs0 hmask
  obtain ⟨f2, b02, b12, o2, h1, v12, v13, lm0_1, hb02, hb12, fr1⟩ :=
    reluExpr0_cycle1_genericState input currentState f1 o1 hmask
  obtain ⟨f3, b03, b13, o3, h2, v24, v25, lm0_2, hb03, hb13, fr2⟩ :=
    reluExpr0_cycle2_genericState input currentState f2 o2 hmask
  obtain ⟨f4, b04, b14, o4, h3, v36, v37, lm0_3, hb04, hb14, fr3⟩ :=
    reluExpr0_cycle3_genericState input currentState f3 o3 hmask
  refine ⟨f4, 0, 0, o4, ?_, ?_, ?_, rfl, rfl⟩
  · rw [reluSplit0123_state input currentState, h0]; simp only []
    rw [hb01, hb11]
    rw [reluSplit123_state input currentState, h1]; simp only []
    rw [hb02, hb12]
    rw [reluSplit23_state input currentState, h2]; simp only []
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

#print axioms reluFold_genericState




theorem executeParsedFloatReluAtPE_pe_lm1_generic
    (input : ProofsLean.MNCore.PlusOne.Words) (currentState : State)
    (files0 : IntegerRegisterFiles) (next : State)
    (hfiles : currentState.peRegisters 0 = files0)
    (hmask : currentState.maskDirective = (welcomeInitialState input).maskDirective)
    (executed : executeParsedFloatReluAtPE (welcomeInitialState input) currentState
      reluExpr0 0 false false = .ok next) :
    ∀ i : Fin 8,
      (next.peRegisters welcomePE).lm1
        ⟨i.val, by have := i.isLt; change i.val < 4096; omega⟩ =
      reluWord (input ⟨i.val, by have := i.isLt; omega⟩) := by
  obtain ⟨files, fbar0, fbar1, foutputs, hrun, hval, hlm0, hb0, hb1⟩ :=
    reluFold_genericState input currentState files0 (fun _ => ⟨0, 0⟩) hmask
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
          reluExpr0 0 false (ParsedIntegerContext.ofLinearIndex 0) (ParsedIntegerContext.ofLinearIndex 0)
          [0, 1, 2, 3] files0 0 0 (fun _ => ⟨0, 0⟩) =
          .ok (files, fbar0, fbar1, foutputs) := hrun
    rw [hfiles] at ran
    change executeParsedFloatReluAtPE.runCycles (welcomeInitialState input) currentState
      reluExpr0 0 false (ParsedIntegerContext.ofLinearIndex 0) (ParsedIntegerContext.ofLinearIndex 0)
      [0, 1, 2, 3] files0 0 0 (fun _ => ⟨0, 0⟩) =
      .ok (registers, bar0, bar1, outputs) at ran
    rw [hrun'] at ran
    simp only [StepResult.ok.injEq] at ran
    obtain ⟨rfl, rfl, rfl, rfl⟩ := ran
    subst executed
    simp only [welcomePE]
    exact hval

#print axioms executeParsedFloatReluAtPE_pe_lm1_generic


theorem executeParsedFloatReluAtPEs_finRange_pe0_lm1_generic
    (input : ProofsLean.MNCore.PlusOne.Words) (currentState : State)
    (files0 : IntegerRegisterFiles) (next : State)
    (hfiles : currentState.peRegisters 0 = files0)
    (hmask : currentState.maskDirective = (welcomeInitialState input).maskDirective)
    (executed : executeParsedFloatReluAtPEs (welcomeInitialState input) currentState
      reluExpr0 (List.finRange 4096) false false = .ok next) :
    ∀ i : Fin 8,
      (next.peRegisters welcomePE).lm1
        ⟨i.val, by have := i.isLt; change i.val < 4096; omega⟩ =
      reluWord (input ⟨i.val, by have := i.isLt; omega⟩) := by
  rw [finRange4096_eq_welcomePE_cons] at executed
  simp only [executeParsedFloatReluAtPEs] at executed
  cases head : executeParsedFloatReluAtPE (welcomeInitialState input) currentState
      reluExpr0 welcomePE false false with
  | failure => simp [head] at executed
  | unknown => simp [head] at executed
  | ok middle =>
    simp only [head] at executed
    have hvalues := executeParsedFloatReluAtPE_pe_lm1_generic input currentState files0 middle
      hfiles hmask head
    have hframe : next.peRegisters welcomePE = middle.peRegisters welcomePE :=
      executeParsedFloatReluAtPEs_peRegisters_not_mem (welcomeInitialState input) reluExpr0
        false false ((List.finRange 4095).map Fin.succ) middle next welcomePE
        (by simp [welcomePE]) executed
    intro i
    rw [hframe]
    exact hvalues i

#print axioms executeParsedFloatReluAtPEs_finRange_pe0_lm1_generic


open Issue
open ProofsLean.MNCore.PEMemory
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000


open Issue
open ProofsLean.MNCore.PEMemory
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000


open Issue
open ProofsLean.MNCore.PEMemory
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

theorem reluExpr8_cycle0_genericState (input : ProofsLean.MNCore.PlusOne.Words)
    (currentState : State) (files0 : IntegerRegisterFiles) (outputs : Fin 4 → IntegerALU.Bus)
    (hmask : currentState.maskDirective = (welcomeInitialState input).maskDirective) :
    ∃ files bar0 bar1 outputs',
      executeParsedFloatReluAtPE.runCycles (welcomeInitialState input) currentState
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
    PEMemory.distance, hmask, htarget, hentry,
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



theorem reluExpr8_cycle1_genericState (input : ProofsLean.MNCore.PlusOne.Words)
    (currentState : State) (files0 : IntegerRegisterFiles) (outputs : Fin 4 → IntegerALU.Bus)
    (hmask : currentState.maskDirective = (welcomeInitialState input).maskDirective) :
    ∃ files bar0 bar1 outputs',
      executeParsedFloatReluAtPE.runCycles (welcomeInitialState input) currentState
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
    PEMemory.distance, hmask, htarget, hentry,
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



theorem reluExpr8_cycle2_genericState (input : ProofsLean.MNCore.PlusOne.Words)
    (currentState : State) (files0 : IntegerRegisterFiles) (outputs : Fin 4 → IntegerALU.Bus)
    (hmask : currentState.maskDirective = (welcomeInitialState input).maskDirective) :
    ∃ files bar0 bar1 outputs',
      executeParsedFloatReluAtPE.runCycles (welcomeInitialState input) currentState
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
    PEMemory.distance, hmask, htarget, hentry,
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



theorem reluExpr8_cycle3_genericState (input : ProofsLean.MNCore.PlusOne.Words)
    (currentState : State) (files0 : IntegerRegisterFiles) (outputs : Fin 4 → IntegerALU.Bus)
    (hmask : currentState.maskDirective = (welcomeInitialState input).maskDirective) :
    ∃ files bar0 bar1 outputs',
      executeParsedFloatReluAtPE.runCycles (welcomeInitialState input) currentState
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
    PEMemory.distance, hmask, htarget, hentry,
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



theorem reluSplit8_0123_state (input : ProofsLean.MNCore.PlusOne.Words)
    (currentState : State) (files : IntegerRegisterFiles) (bar0 bar1 : BitVec 12)
    (outputs : Fin 4 → IntegerALU.Bus) :
    executeParsedFloatReluAtPE.runCycles (welcomeInitialState input) currentState
        reluExpr8 0 false (ParsedIntegerContext.ofLinearIndex 0) (ParsedIntegerContext.ofLinearIndex 0)
        [0, 1, 2, 3] files bar0 bar1 outputs =
      match executeParsedFloatReluAtPE.runCycles (welcomeInitialState input) currentState
          reluExpr8 0 false (ParsedIntegerContext.ofLinearIndex 0) (ParsedIntegerContext.ofLinearIndex 0)
          [0] files bar0 bar1 outputs with
      | .ok (nextFiles, nextBar0, nextBar1, nextOutputs) =>
          executeParsedFloatReluAtPE.runCycles (welcomeInitialState input) currentState
            reluExpr8 0 false (ParsedIntegerContext.ofLinearIndex 0) (ParsedIntegerContext.ofLinearIndex 0)
            [1, 2, 3] nextFiles nextBar0 nextBar1 nextOutputs
      | .failure => .failure
      | .unknown => .unknown := by
  rw [executeParsedFloatReluAtPE.runCycles]
  conv_rhs => rw [executeParsedFloatReluAtPE.runCycles]
  rfl

theorem reluSplit8_123_state (input : ProofsLean.MNCore.PlusOne.Words)
    (currentState : State) (files : IntegerRegisterFiles) (bar0 bar1 : BitVec 12)
    (outputs : Fin 4 → IntegerALU.Bus) :
    executeParsedFloatReluAtPE.runCycles (welcomeInitialState input) currentState
        reluExpr8 0 false (ParsedIntegerContext.ofLinearIndex 0) (ParsedIntegerContext.ofLinearIndex 0)
        [1, 2, 3] files bar0 bar1 outputs =
      match executeParsedFloatReluAtPE.runCycles (welcomeInitialState input) currentState
          reluExpr8 0 false (ParsedIntegerContext.ofLinearIndex 0) (ParsedIntegerContext.ofLinearIndex 0)
          [1] files bar0 bar1 outputs with
      | .ok (nextFiles, nextBar0, nextBar1, nextOutputs) =>
          executeParsedFloatReluAtPE.runCycles (welcomeInitialState input) currentState
            reluExpr8 0 false (ParsedIntegerContext.ofLinearIndex 0) (ParsedIntegerContext.ofLinearIndex 0)
            [2, 3] nextFiles nextBar0 nextBar1 nextOutputs
      | .failure => .failure
      | .unknown => .unknown := by
  rw [executeParsedFloatReluAtPE.runCycles]
  conv_rhs => rw [executeParsedFloatReluAtPE.runCycles]
  rfl

theorem reluSplit8_23_state (input : ProofsLean.MNCore.PlusOne.Words)
    (currentState : State) (files : IntegerRegisterFiles) (bar0 bar1 : BitVec 12)
    (outputs : Fin 4 → IntegerALU.Bus) :
    executeParsedFloatReluAtPE.runCycles (welcomeInitialState input) currentState
        reluExpr8 0 false (ParsedIntegerContext.ofLinearIndex 0) (ParsedIntegerContext.ofLinearIndex 0)
        [2, 3] files bar0 bar1 outputs =
      match executeParsedFloatReluAtPE.runCycles (welcomeInitialState input) currentState
          reluExpr8 0 false (ParsedIntegerContext.ofLinearIndex 0) (ParsedIntegerContext.ofLinearIndex 0)
          [2] files bar0 bar1 outputs with
      | .ok (nextFiles, nextBar0, nextBar1, nextOutputs) =>
          executeParsedFloatReluAtPE.runCycles (welcomeInitialState input) currentState
            reluExpr8 0 false (ParsedIntegerContext.ofLinearIndex 0) (ParsedIntegerContext.ofLinearIndex 0)
            [3] nextFiles nextBar0 nextBar1 nextOutputs
      | .failure => .failure
      | .unknown => .unknown := by
  rw [executeParsedFloatReluAtPE.runCycles]
  conv_rhs => rw [executeParsedFloatReluAtPE.runCycles]
  rfl


theorem reluFold8_genericState (input : ProofsLean.MNCore.PlusOne.Words)
    (currentState : State) (files0 : IntegerRegisterFiles) (outputs0 : Fin 4 → IntegerALU.Bus)
    (hmask : currentState.maskDirective = (welcomeInitialState input).maskDirective) :
    ∃ files bar0 bar1 outputs,
      executeParsedFloatReluAtPE.runCycles (welcomeInitialState input) currentState
        reluExpr8 0 false (ParsedIntegerContext.ofLinearIndex 0) (ParsedIntegerContext.ofLinearIndex 0)
        [0, 1, 2, 3] files0 0 0 outputs0 =
        .ok (files, bar0, bar1, outputs) ∧
      (∀ i : Fin 8, files.lm1 ⟨8 + i.val, by have := i.isLt; change 8 + i.val < 4096; omega⟩ =
        reluWord (input ⟨8 + i.val, by have := i.isLt; omega⟩)) ∧
      files.lm0 = files0.lm0 ∧
      bar0 = 0 ∧ bar1 = 0 := by
  obtain ⟨f1, b01, b11, o1, h0, v00, v01, lm0_0, hb01, hb11, fr0⟩ :=
    reluExpr8_cycle0_genericState input currentState files0 outputs0 hmask
  obtain ⟨f2, b02, b12, o2, h1, v12, v13, lm0_1, hb02, hb12, fr1⟩ :=
    reluExpr8_cycle1_genericState input currentState f1 o1 hmask
  obtain ⟨f3, b03, b13, o3, h2, v24, v25, lm0_2, hb03, hb13, fr2⟩ :=
    reluExpr8_cycle2_genericState input currentState f2 o2 hmask
  obtain ⟨f4, b04, b14, o4, h3, v36, v37, lm0_3, hb04, hb14, fr3⟩ :=
    reluExpr8_cycle3_genericState input currentState f3 o3 hmask
  refine ⟨f4, 0, 0, o4, ?_, ?_, ?_, rfl, rfl⟩
  · rw [reluSplit8_0123_state input currentState, h0]; simp only []
    rw [hb01, hb11]
    rw [reluSplit8_123_state input currentState, h1]; simp only []
    rw [hb02, hb12]
    rw [reluSplit8_23_state input currentState, h2]; simp only []
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


theorem executeParsedFloatReluAtPE_pe_lm1_8_generic
    (input : ProofsLean.MNCore.PlusOne.Words) (currentState : State)
    (files0 : IntegerRegisterFiles) (next : State)
    (hfiles : currentState.peRegisters 0 = files0)
    (hmask : currentState.maskDirective = (welcomeInitialState input).maskDirective)
    (executed : executeParsedFloatReluAtPE (welcomeInitialState input) currentState
      reluExpr8 0 false false = .ok next) :
    ∀ i : Fin 8,
      (next.peRegisters welcomePE).lm1
        ⟨8 + i.val, by have := i.isLt; change 8 + i.val < 4096; omega⟩ =
      reluWord (input ⟨8 + i.val, by have := i.isLt; omega⟩) := by
  obtain ⟨files, fbar0, fbar1, foutputs, hrun, hval, hlm0, hb0, hb1⟩ :=
    reluFold8_genericState input currentState files0 (fun _ => ⟨0, 0⟩) hmask
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
          reluExpr8 0 false (ParsedIntegerContext.ofLinearIndex 0) (ParsedIntegerContext.ofLinearIndex 0)
          [0, 1, 2, 3] files0 0 0 (fun _ => ⟨0, 0⟩) =
          .ok (files, fbar0, fbar1, foutputs) := hrun
    rw [hfiles] at ran
    change executeParsedFloatReluAtPE.runCycles (welcomeInitialState input) currentState
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



theorem executeParsedFloatReluAtPEs_finRange_pe0_lm1_8_generic
    (input : ProofsLean.MNCore.PlusOne.Words) (currentState : State)
    (files0 : IntegerRegisterFiles) (next : State)
    (hfiles : currentState.peRegisters 0 = files0)
    (hmask : currentState.maskDirective = (welcomeInitialState input).maskDirective)
    (executed : executeParsedFloatReluAtPEs (welcomeInitialState input) currentState
      reluExpr8 (List.finRange 4096) false false = .ok next) :
    ∀ i : Fin 8,
      (next.peRegisters welcomePE).lm1
        ⟨8 + i.val, by have := i.isLt; change 8 + i.val < 4096; omega⟩ =
      reluWord (input ⟨8 + i.val, by have := i.isLt; omega⟩) := by
  rw [finRange4096_eq_welcomePE_cons] at executed
  simp only [executeParsedFloatReluAtPEs] at executed
  cases head : executeParsedFloatReluAtPE (welcomeInitialState input) currentState
      reluExpr8 welcomePE false false with
  | failure => simp [head] at executed
  | unknown => simp [head] at executed
  | ok middle =>
    simp only [head] at executed
    have hvalues := executeParsedFloatReluAtPE_pe_lm1_8_generic input currentState files0 middle
      hfiles hmask head
    have hframe : next.peRegisters welcomePE = middle.peRegisters welcomePE :=
      executeParsedFloatReluAtPEs_peRegisters_not_mem (welcomeInitialState input) reluExpr8
        false false ((List.finRange 4095).map Fin.succ) middle next welcomePE
        (by simp [welcomePE]) executed
    intro i
    rw [hframe]
    exact hvalues i


theorem reluLine8_step_lm1 (input : ProofsLean.MNCore.PlusOne.Words) (next : State)
    (step : executeNormalizedLine (.pe [(reluExpr8).normalize]) (welcomeInitialState input) = .ok next) :
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
      (parsedExprWaitPending (welcomeInitialState input)) = false := by
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
    executeIntegerProducerInstructionLine_pe_stages_exists [(reluExpr8).normalize] (welcomeInitialState input)
      next hcheck hwait hunsup hsup step
  have hnf : ([(reluExpr8).normalize].any
      (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed)) = false := by
    decide
  have hmask : ([(reluExpr8).normalize].any
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
  have hmslId : executeParsedMslMsrProducers (welcomeInitialState input) nextPEs
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
  have hfiles : nextPEs.peRegisters 0 = (welcomeInitialState input).peRegisters 0 := by
    obtain ⟨next', hnext', hframe⟩ :=
      executeIntegerProducerLineAtPEs_nil_peRegisters (List.finRange 4096) (welcomeInitialState input) 0
    rw [walkExecuted] at hnext'
    have hEq : nextPEs = next' := StepResult.ok.inj hnext'
    subst hEq
    exact hframe
  have hmask' : nextPEs.maskDirective = (welcomeInitialState input).maskDirective :=
    (executeIntegerProducerLineAtPEs_maskDirective_hazardClock [] (List.finRange 4096)
      (welcomeInitialState input) nextPEs walkExecuted).1
  rw [hmslEq] at reluExecuted
  have hreluId : executeParsedFloatReluProducers (welcomeInitialState input) nextPEs
      ([(reluExpr8).normalize].map NormalizedExpr.toParsed)
      (([(reluExpr8).normalize].any
        (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed)))
      (([(reluExpr8).normalize].any
        (parsedExprHasSingleLineWriteMask ∘ NormalizedExpr.toParsed))) =
      executeParsedFloatReluAtPEs (welcomeInitialState input) nextPEs reluExpr8
        (List.finRange 4096) false false := by
    rw [hparsed, hnf, hmask]
    simp [executeParsedFloatReluProducers, parsedExprIsFloatReluProducer, reluExpr8, reluOp]
  rw [hreluId] at reluExecuted
  cases hrun : executeParsedFloatReluAtPEs (welcomeInitialState input) nextPEs reluExpr8
      (List.finRange 4096) false false with
  | failure => simp [hrun] at reluExecuted
  | unknown => simp [hrun] at reluExecuted
  | ok middle =>
    simp only [hrun, StepResult.ok.injEq] at reluExecuted
    subst reluExecuted
    have hblockId : executeParsedBlockFloatProducer (welcomeInitialState input) middle
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
    have hmatrixId : executeParsedMatrixMAUAndWrites (welcomeInitialState input) middle
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
    have hsharedId : executeParsedSharedBlockProducers (welcomeInitialState input) middle
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
    have hl1Id : executeParsedL1ToPEProducers (welcomeInitialState input) middle
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
    have hval := executeParsedFloatReluAtPEs_finRange_pe0_lm1_8_generic input nextPEs
      ((welcomeInitialState input).peRegisters 0) middle hfiles hmask' hrun
    rw [nextEq]
    let i : Fin 8 := ⟨j.val, hj⟩
    have hv := hval i
    simpa using hv



theorem reluLine0_step_lm1 (input : ProofsLean.MNCore.PlusOne.Words) (next : State)
    (step : executeNormalizedLine (.pe [(reluExpr0).normalize]) (welcomeInitialState input) = .ok next) :
    ∀ (j : Fin PEMemory.Bank.lm1.capacity) (hj : j.val < 8),
      (next.peRegisters welcomePE).lm1 j =
      reluWord (input ⟨j.val, Nat.lt_of_lt_of_le hj (by decide : 8 ≤ 16)⟩) := by
  unfold executeNormalizedLine at step
  simp only [NormalizedLine.toInstruction?] at step
  have hcheck : checkParsedTopLine (InstructionLine.pe [(reluExpr0).normalize]).toParsed = true := by
    show checkParsedLine [(reluExpr0).normalize.toParsed] = true
    simpa using check_of_legal [reluExpr0] reluExpr0_legal
  have hparsed : ([(reluExpr0).normalize].map NormalizedExpr.toParsed) = [reluExpr0] := rfl
  have hwait : ([(reluExpr0).normalize].map NormalizedExpr.toParsed).any
      (parsedExprWaitPending (welcomeInitialState input)) = false := by
    rw [hparsed]
    simp [parsedExprWaitPending, parsedExprWaitTag?, reluExpr0, reluOp]
  have hunsup : ([(reluExpr0).normalize].map NormalizedExpr.toParsed).any
      parsedExprIsUnsupportedRustAlu = false := by
    rw [hparsed]
    simp [parsedExprIsUnsupportedRustAlu, reluExpr0, reluOp]
  have hsup : ([(reluExpr0).normalize].map NormalizedExpr.toParsed).all
      parsedExprIsSupportedPELineProducer = true := by
    rw [hparsed]
    simp [parsedExprIsSupportedPELineProducer, reluExpr0, reluOp]
  obtain ⟨nextPEs, nextMsl, nextRelu, nextBlockFloat, afterMatrix, nextShared, nextBroadcast,
    walkExecuted, mslExecuted, reluExecuted, blockExecuted, matrixExecuted, sharedExecuted,
    l1Executed, nextEq⟩ :=
    executeIntegerProducerInstructionLine_pe_stages_exists [(reluExpr0).normalize] (welcomeInitialState input)
      next hcheck hwait hunsup hsup step
  have hnf : ([(reluExpr0).normalize].any
      (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed)) = false := by
    decide
  have hmask : ([(reluExpr0).normalize].any
      (parsedExprHasSingleLineWriteMask ∘ NormalizedExpr.toParsed)) = false := by
    decide
  have hint : (List.filter (fun expression =>
      !parsedExprIsL2BMProducer expression && !parsedExprIsMslMsrProducer expression &&
        !parsedExprIsMatrixMAUProducer expression && !parsedExprIsBlockFloatProducer expression &&
        !parsedExprIsFloatReluProducer expression)
      ([(reluExpr0).normalize].map NormalizedExpr.toParsed)) = [] := by
    rw [hparsed]
    have h : parsedExprIsFloatReluProducer reluExpr0 = true := rfl
    simp [h]
  rw [hint] at walkExecuted
  have hmslId : executeParsedMslMsrProducers (welcomeInitialState input) nextPEs
      ([(reluExpr0).normalize].map NormalizedExpr.toParsed)
      (([(reluExpr0).normalize].any
        (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed)))
      (([(reluExpr0).normalize].any
        (parsedExprHasSingleLineWriteMask ∘ NormalizedExpr.toParsed))) = .ok nextPEs := by
    apply executeParsedMslMsrProducers_eq_self
    rw [hparsed]
    have h : parsedExprIsMslMsrProducer reluExpr0 = false := rfl
    simp [h, List.filter]
  rw [hparsed] at hmslId
  rw [hparsed] at mslExecuted
  rw [hmslId] at mslExecuted
  have hmslEq : nextMsl = nextPEs := (StepResult.ok.inj mslExecuted).symm
  have hfiles : nextPEs.peRegisters 0 = (welcomeInitialState input).peRegisters 0 := by
    obtain ⟨next', hnext', hframe⟩ :=
      executeIntegerProducerLineAtPEs_nil_peRegisters (List.finRange 4096) (welcomeInitialState input) 0
    rw [walkExecuted] at hnext'
    have hEq : nextPEs = next' := StepResult.ok.inj hnext'
    subst hEq
    exact hframe
  have hmask' : nextPEs.maskDirective = (welcomeInitialState input).maskDirective :=
    (executeIntegerProducerLineAtPEs_maskDirective_hazardClock [] (List.finRange 4096)
      (welcomeInitialState input) nextPEs walkExecuted).1
  rw [hmslEq] at reluExecuted
  have hreluId : executeParsedFloatReluProducers (welcomeInitialState input) nextPEs
      ([(reluExpr0).normalize].map NormalizedExpr.toParsed)
      (([(reluExpr0).normalize].any
        (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed)))
      (([(reluExpr0).normalize].any
        (parsedExprHasSingleLineWriteMask ∘ NormalizedExpr.toParsed))) =
      executeParsedFloatReluAtPEs (welcomeInitialState input) nextPEs reluExpr0
        (List.finRange 4096) false false := by
    rw [hparsed, hnf, hmask]
    simp [executeParsedFloatReluProducers, parsedExprIsFloatReluProducer, reluExpr0, reluOp]
  rw [hreluId] at reluExecuted
  cases hrun : executeParsedFloatReluAtPEs (welcomeInitialState input) nextPEs reluExpr0
      (List.finRange 4096) false false with
  | failure => simp [hrun] at reluExecuted
  | unknown => simp [hrun] at reluExecuted
  | ok middle =>
    simp only [hrun, StepResult.ok.injEq] at reluExecuted
    subst reluExecuted
    have hblockId : executeParsedBlockFloatProducer (welcomeInitialState input) middle
        ([(reluExpr0).normalize].map NormalizedExpr.toParsed)
        ([(reluExpr0).normalize].any (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed))
        ([(reluExpr0).normalize].any (parsedExprHasSingleLineWriteMask ∘ NormalizedExpr.toParsed)) =
        .ok middle := by
      apply executeParsedBlockFloatProducer_eq_self
      rw [hparsed]
      simp [parsedExprIsBlockFloatProducer, reluExpr0, reluOp, List.filter]
    rw [hblockId] at blockExecuted
    have hblockEq : nextBlockFloat = middle := (StepResult.ok.inj blockExecuted).symm
    subst nextBlockFloat
    have hmatrixId : executeParsedMatrixMAUAndWrites (welcomeInitialState input) middle
        ([(reluExpr0).normalize].map NormalizedExpr.toParsed)
        ([(reluExpr0).normalize].any (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed))
        ([(reluExpr0).normalize].any (parsedExprHasSingleLineWriteMask ∘ NormalizedExpr.toParsed)) =
        .ok middle := by
      apply executeParsedMatrixMAUAndWrites_eq_self
      · rw [hparsed]
        simp [parsedExprIsMatrixMAUProducer, reluExpr0, reluOp, List.filter]
      · rw [hparsed]
        simp [parsedExprIsMatrixWriteProducer, reluExpr0, reluOp]
    rw [hmatrixId] at matrixExecuted
    have hmatrixEq : afterMatrix = middle := (StepResult.ok.inj matrixExecuted).symm
    subst afterMatrix
    have hsharedId : executeParsedSharedBlockProducers (welcomeInitialState input) middle
        ([(reluExpr0).normalize].map NormalizedExpr.toParsed)
        (!([(reluExpr0).normalize].any (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed))) =
        .ok middle := by
      rw [hparsed]
      apply executeParsedSharedBlockProducerList_eq_self
      intro e mem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
      subst e
      simp [executeParsedSharedBlockExpression, reluExpr0, reluOp]
    rw [hsharedId] at sharedExecuted
    have hsharedEq : nextShared = middle := (StepResult.ok.inj sharedExecuted).symm
    subst nextShared
    have hl1Id : executeParsedL1ToPEProducers (welcomeInitialState input) middle
        ([(reluExpr0).normalize].map NormalizedExpr.toParsed)
        ([(reluExpr0).normalize].any (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed))
        ([(reluExpr0).normalize].any (parsedExprHasSingleLineWriteMask ∘ NormalizedExpr.toParsed))
        (parsedL1ToPEPrecedesOMRWriter ([(reluExpr0).normalize].map NormalizedExpr.toParsed)) =
        .ok middle := by
      apply executeParsedL1ToPEProducers_eq_self
      rw [hparsed]
      simp [parsedExprIsL1ToPEProducer, reluExpr0, reluOp, List.filter]
    rw [hl1Id] at l1Executed
    have hl1Eq : nextBroadcast = middle := (StepResult.ok.inj l1Executed).symm
    subst nextBroadcast
    intro j hj
    have hval := executeParsedFloatReluAtPEs_finRange_pe0_lm1_generic input nextPEs
      ((welcomeInitialState input).peRegisters 0) middle hfiles hmask' hrun
    rw [nextEq]
    let i : Fin 8 := ⟨j.val, hj⟩
    have hv := hval i
    simpa using hv


#print axioms reluLine0_step_lm1
#print axioms reluLine8_step_lm1

end ProofsLean.MNCore
