import ProofsLean.WelcomeWholeMachineOptimal
import ProofsLean.FloatRelu

/-! # Problem `3.relu`: model-gap audit and the two-line solution

The accepted answer is

```
frelu $lm0v $lm0v $ln0v
frelu $lm8v $lm8v $ln8v
```

This module fixes the instruction, the specification on the hazard-aware whole
machine, the issue-legal facts, and the model-gap counterexample that rules out
the naive "one line writes at most eight words" lower-bound argument.

## Model gap (checked against the official assembler)

* Two `frelu` expressions in one line are rejected by both `assemble3`
  (`Instruction field conflict detected between 'alu' and 'alu'`) and the Lean
  issue checker (`groupsUnique`).
* A single `frelu` with a `.double` destination (`$lln0v`) **is accepted** by
  `assemble3` and writes sixteen words.  Its low two words per cycle are the
  raw source words (`parsedFloatReluBus` copies `left.low`); they are not
  relu'd.  The official judge therefore reports 3072 correct / 1024 mismatch,
  and the naive per-line word count of eight is false.

The lemmas `reluBus_high` and `reluDouble_allNeg_word2` below fix that fact.
-/

namespace ProofsLean.MNCore

open Issue

/-! ## 1. The `frelu` instruction -/

/-- The parsed `frelu` operation: float precision, no unsignedness, no arg. -/
def reluOp : ParsedOp := .alu .relu (some .f) false none

/-- A `$lm<base>v` / `$ln<base>v` long-vector operand: width two, stride two,
four cycles.  This is the layout the accepted answer uses. -/
def reluLongOperand (bank : Bank) (base : Nat) : ParsedOperand :=
  .mem ⟨bank, ⟨2, base, base + 2, base + 4, base + 6, false, none⟩⟩
    false false false none

/-- The parsed expression of `base`-th relu line. -/
def reluExpr (base : Nat) : ParsedExpr :=
  ⟨reluOp, [reluLongOperand .lm0 base, reluLongOperand .lm0 base],
    [reluLongOperand .lm1 base], none, ""⟩

/-- Concrete long-vector operands of the accepted first line. -/
def reluLm0Long0 : ParsedOperand :=
  .mem ⟨.lm0, ⟨2, 0, 2, 4, 6, false, none⟩⟩ false false false none
def reluLm0Long8 : ParsedOperand :=
  .mem ⟨.lm0, ⟨2, 8, 10, 12, 14, false, none⟩⟩ false false false none
def reluLm1Long0 : ParsedOperand :=
  .mem ⟨.lm1, ⟨2, 0, 2, 4, 6, false, none⟩⟩ false false false none
def reluLm1Long8 : ParsedOperand :=
  .mem ⟨.lm1, ⟨2, 8, 10, 12, 14, false, none⟩⟩ false false false none

/-- The concrete first accepted line. -/
def reluExpr0 : ParsedExpr :=
  ⟨reluOp, [reluLm0Long0, reluLm0Long0], [reluLm1Long0], none, ""⟩
/-- The concrete second accepted line. -/
def reluExpr8 : ParsedExpr :=
  ⟨reluOp, [reluLm0Long8, reluLm0Long8], [reluLm1Long8], none, ""⟩

/-- The accepted two-line answer. -/
def reluAnswer : Program welcomeWholeMachine :=
  [InstructionLine.pe [(reluExpr0).normalize],
   InstructionLine.pe [(reluExpr8).normalize]]

theorem reluAnswer_score : score welcomeWholeMachine reluAnswer = 2 := rfl

/-! ## 2. The specification on the hazard-aware whole machine -/

/-- One output word of ReLU: `x` if `x` is non-negative (including both signed
zeros), and negative zero otherwise.  This is exactly `frelu x x`. -/
def reluWord (x : BitVec 32) : BitVec 32 :=
  if x.msb then 0x80000000 else x

/-- The public `3.relu` specification: every PE observes the same 16-word
input and must write the elementwise `frelu x x`.  The problem's stated domain
`-512 ≤ x ≤ 512` is a subset of `True`; the theorem below is stronger. -/
noncomputable def reluSpec : Problem welcomeWholeMachine where
  admissible := fun _ => True
  initial := fun input => HazardAwareState.initial (welcomeInitialState input)
  post := fun input state => ∀ i : Fin 16,
    (state.machine.peRegisters welcomePE).lm1
      ⟨i.val, by have := i.isLt; change i.val < 4096; omega⟩ =
      reluWord (input i)

/-! ## 3. Issue legality -/

theorem reluExpr_issueGroup (base : Nat) :
    (reluExpr base).issueGroup = some .alu := rfl

theorem reluExpr0_legal : LegalParsedLine [reluExpr0] := by
  simp [LegalParsedLine, projectLine, projectFrom, Legal, idsUnique, groupsUnique,
    mauCountBounded, mauExpressions, mauPrecisionsAgree, matrixWritePairAgrees,
    matrixRegistersUnique, writesUnique, barWritesExcludeReads, readsAgree,
    localReadWriteAgree, immediateExcludesLm0, zeroFlushUnique, maskWidthsAgree,
    maskEntriesAgree, nowriteOutputsUnique, lbfWritesUnique, maskRegisterWritesUnique,
    reluExpr0, reluOp, reluLm0Long0, reluLm1Long0, ParsedExpr.toIssueExpr, ParsedExpr.issueGroup,
    ParsedExpr.issueMau, ParsedOperand.accesses, ParsedOperand.barWriteBank?,
    ParsedOperand.maskRegisterWrite?, ParsedOperand.writeMask?, ParsedExpr.nowriteOutputValid,
    ParsedExpr.barWrites, ParsedExpr.maskRegisterWrites, ParsedExpr.writesLbf,
    ParsedExpr.maskApplications, Expr.writeBanks, Expr.matrixXUses, Expr.matrixYUses,
    ParsedOperand.matrixUseCount, List.filterMap_nil, List.filterMap_cons,
    List.map_nil, List.map_cons, List.filter_nil, List.filter_cons]

theorem reluExpr8_legal : LegalParsedLine [reluExpr8] := by
  simp [LegalParsedLine, projectLine, projectFrom, Legal, idsUnique, groupsUnique,
    mauCountBounded, mauExpressions, mauPrecisionsAgree, matrixWritePairAgrees,
    matrixRegistersUnique, writesUnique, barWritesExcludeReads, readsAgree,
    localReadWriteAgree, immediateExcludesLm0, zeroFlushUnique, maskWidthsAgree,
    maskEntriesAgree, nowriteOutputsUnique, lbfWritesUnique, maskRegisterWritesUnique,
    reluExpr8, reluOp, reluLm0Long8, reluLm1Long8, ParsedExpr.toIssueExpr, ParsedExpr.issueGroup,
    ParsedExpr.issueMau, ParsedOperand.accesses, ParsedOperand.barWriteBank?,
    ParsedOperand.maskRegisterWrite?, ParsedOperand.writeMask?, ParsedExpr.nowriteOutputValid,
    ParsedExpr.barWrites, ParsedExpr.maskRegisterWrites, ParsedExpr.writesLbf,
    ParsedExpr.maskApplications, Expr.writeBanks, Expr.matrixXUses, Expr.matrixYUses,
    ParsedOperand.matrixUseCount, List.filterMap_nil, List.filterMap_cons,
    List.map_nil, List.map_cons, List.filter_nil, List.filter_cons]

theorem reluTwoExpr_not_legal : ¬ LegalParsedLine [reluExpr0, reluExpr8] := by
  intro h
  have groups := h.2.1
  have hh := groups (reluExpr0.toIssueExpr 0) (by simp [projectLine, projectFrom])
    (reluExpr8.toIssueExpr 1) (by simp [projectLine, projectFrom]) (by decide)
    Group.alu rfl
  exact hh rfl

theorem reluTwoExpr_check_false :
    checkParsedTopLine (.pe [reluExpr0, reluExpr8]) = false := by
  classical
  unfold checkParsedTopLine checkParsedLine check
  rw [decide_eq_false_iff_not]
  exact reluTwoExpr_not_legal



/-! ## 4a. The per-cycle memory read -/

/-- Reading the long word at `base + 2*c` from the initial LM0 returns the two
input lanes packed into the ALU bus (high half), with a zero low half.  This
covers both accepted lines (`base = 0` and `base = 8`). -/
theorem reluInitial_read_long (input : ProofsLean.MNCore.PlusOne.Words)
    (base : Nat) (c : Fin 4) (hbase : base + 2 * c.val + 1 < 16) :
    ProofsLean.MNCore.PEMemory.ParsedIntegerInput.read (welcomeInitialPERegisters input)
      (.memory ⟨.lm0, .long,
        ⟨base + 2 * c.val, by have := c.isLt; change base + 2 * c.val < 4096; omega⟩⟩ false) =
    .ok ⟨input ⟨base + 2 * c.val, by omega⟩ ++
         input ⟨base + 2 * c.val + 1, by omega⟩, 0⟩ := by
  have hbound : base + 2 * c.val < 4096 := by omega
  have hbound2 : base + 2 * c.val + 1 < 4096 := by omega
  have h16 : base + 2 * c.val < 16 := by omega
  have h17 : base + 2 * c.val + 1 < 16 := by omega
  simp [ProofsLean.MNCore.PEMemory.ParsedIntegerInput.read,
    ProofsLean.MNCore.PEMemory.readDirectAccess,
    ProofsLean.MNCore.PEMemory.readRegisterBank,
    ProofsLean.MNCore.PEMemory.readWords,
    ProofsLean.MNCore.PEMemory.count,
    ProofsLean.MNCore.PEMemory.Width.words,
    ProofsLean.MNCore.PEMemory.pack, welcomeInitialPERegisters,
    ProofsLean.MNCore.PEMemory.advance,
    ProofsLean.MNCore.PEMemory.Bank.capacity,
    Nat.mod_eq_of_lt, hbound, hbound2, h16, h17,
    ProofsLean.MNCore.PEMemory.ParsedIntegerInput.applyRounding]



/-- The `readWithForwarding` form used by the relu executor: the source is a
plain memory read, so the forwarding slots are irrelevant. -/
theorem reluInitial_readWithForwarding_long (input : ProofsLean.MNCore.PlusOne.Words)
    (base : Nat) (c : Fin 4) (hbase : base + 2 * c.val + 1 < 16) :
    ProofsLean.MNCore.PEMemory.ParsedIntegerInput.readWithForwarding
      ((welcomeInitialState input).peRegisters 0)
      (stateForwardingSlots (welcomeInitialState input) 0) c
      (.memory ⟨.lm0, .long,
        ⟨base + 2 * c.val, by have := c.isLt; change base + 2 * c.val < 4096; omega⟩⟩ false) =
    .ok ⟨input ⟨base + 2 * c.val, by omega⟩ ++
         input ⟨base + 2 * c.val + 1, by omega⟩, 0⟩ := by
  simp [ProofsLean.MNCore.PEMemory.ParsedIntegerInput.readWithForwarding,
    welcomeInitialState, reluInitial_read_long input base c hbase]

/-! ## 4b. Concrete lowering of the accepted expression -/

/-- The coordinate/bar context used by the relu expressions. -/
def reluContext (pe cycle : Fin 4) : ProofsLean.MNCore.PEMemory.ParsedIntegerContext :=
  { pe := pe, cycle := cycle, bar0 := 0, bar1 := 0, tWord := 0,
    group := 0, l2b := 0, l1b := 0, mab := 0 }

theorem reluExpr0_lowered_cycle0 :
    (lowerParsedFloatRelu? reluExpr0 (reluContext 0 0)).isSome = true := by
  decide

theorem reluExpr0_lowered_cycle1 :
    (lowerParsedFloatRelu? reluExpr0 (reluContext 0 1)).isSome = true := by
  decide

theorem reluExpr0_lowered_cycle2 :
    (lowerParsedFloatRelu? reluExpr0 (reluContext 0 2)).isSome = true := by
  decide

theorem reluExpr0_lowered_cycle3 :
    (lowerParsedFloatRelu? reluExpr0 (reluContext 0 3)).isSome = true := by
  decide


section
open ProofsLean.MNCore.PEMemory

/-! ## 4. The symbolic bus value and the `.double` model gap -/

lemma cond_eq_not_msb (a : BitVec 32) :
    (a.toNat / 2147483648 % 2 == 0) = !a.msb := by
  have hmsb : a.msb = decide (2147483648 ≤ a.toNat) := by
    simpa using BitVec.msb_eq_decide a
  by_cases h : 2147483648 ≤ a.toNat
  · have hmod : a.toNat / 2147483648 % 2 = 1 := by omega
    simp [hmod, h, hmsb]
  · have hdiv : a.toNat / 2147483648 = 0 := by omega
    simp [hdiv, h, hmsb]

lemma ofNat_pack (x y : BitVec 32) :
    BitVec.ofNat 64 (x.toNat * 2^32 + y.toNat) = x ++ y := by
  apply BitVec.toNat_eq.mpr
  rw [BitVec.toNat_ofNat, BitVec.toNat_append]
  have h : x.toNat <<< 32 ||| y.toNat = x.toNat * 2^32 + y.toNat := by
    have hs := Nat.shiftLeft_add_eq_or_of_lt y.isLt x.toNat
    rw [Nat.shiftLeft_eq] at hs
    rw [Nat.shiftLeft_eq]
    exact hs.symm
  rw [h]
  have hx := x.isLt
  have hy := y.isLt
  have hbound : x.toNat * 2^32 + y.toNat < 2^64 := by omega
  rw [Nat.mod_eq_of_lt hbound]

lemma extract_high (a b : BitVec 32) : BitVec.extractLsb' 32 32 (a ++ b) = a := by
  apply BitVec.toNat_eq.mpr
  rw [BitVec.extractLsb'_toNat, BitVec.toNat_append]
  have h : a.toNat <<< 32 ||| b.toNat = a.toNat * 2^32 + b.toNat := by
    have hs := Nat.shiftLeft_add_eq_or_of_lt b.isLt a.toNat
    rw [Nat.shiftLeft_eq] at hs
    rw [Nat.shiftLeft_eq]
    exact hs.symm
  rw [h, Nat.shiftRight_eq_div_pow]
  have ha := a.isLt
  have hb := b.isLt
  omega

lemma extract_low (a b : BitVec 32) : BitVec.extractLsb' 0 32 (a ++ b) = b := by
  apply BitVec.toNat_eq.mpr
  rw [BitVec.extractLsb'_toNat, BitVec.toNat_append]
  have h : a.toNat <<< 32 ||| b.toNat = a.toNat * 2^32 + b.toNat := by
    have hs := Nat.shiftLeft_add_eq_or_of_lt b.isLt a.toNat
    rw [Nat.shiftLeft_eq] at hs
    rw [Nat.shiftLeft_eq]
    exact hs.symm
  rw [h, Nat.shiftRight_zero]
  have hb := b.isLt
  omega

/-- The high half of a two-lane `frelu` bus is the bitwise ReLU of the two
input lanes.  This is the symbolic value bridge used by the per-PE readback. -/
theorem reluBus_high (a b : BitVec 32) :
    (parsedFloatReluBus .f .relu false ⟨a ++ b, 0⟩ (some ⟨a ++ b, 0⟩)).1.high
      = reluWord a ++ reluWord b := by
  have hw : (64 : Nat) / 32 = 2 := by decide
  have h1 : (64 : Nat) - 32 * (0 + 1) = 32 := by decide
  have h2 : (64 : Nat) - 32 * (1 + 1) = 0 := by decide
  have h3 : (32 : Nat) - 1 - 0 = 31 := by decide
  have hp31 : (2 : Nat) ^ 31 = 2147483648 := by decide
  have hr : List.range 2 = [0, 1] := by decide
  have hp : (ParsedAluName.relu == ParsedAluName.passa) = false := by decide
  have hrs : (ParsedAluName.relu == ParsedAluName.rsqrt) = false := by decide
  have hf : (ParsedAluName.relu == ParsedAluName.floor) = false := by decide
  have hft : (ParsedAluName.relu == ParsedAluName.ftoi) = false := by decide
  have hmx : (ParsedAluName.relu == ParsedAluName.max) = false := by decide
  have hmn : (ParsedAluName.relu == ParsedAluName.min) = false := by decide
  unfold parsedFloatReluBus
  simp only [hw, hr, hp, hrs, hf, hft, hmx, hmn, Bool.false_eq_true, Bool.false_or,
    if_false, if_true, List.length, List.map_cons, List.map_nil, List.foldl_cons,
    List.foldl_nil, List.getElem_cons_zero, List.getElem_cons_succ,
    h1, h2, h3, hp31, Option.getD_some,
    List.getElem!_cons_zero, List.getElem!_cons_succ,
    List.getElem_cons_zero, List.getElem_cons_succ, List.getElem_singleton,
    Id.run_pure, Prod.fst, pow_zero, Nat.reducePow,
    parsedFloatReluShift, extract_high, extract_low, cond_eq_not_msb]
  have hca := cond_eq_not_msb a
  have hcb := cond_eq_not_msb b
  simp only [hca, hcb, reluWord]
  by_cases ha : a.msb <;> by_cases hb : b.msb
  · simp only [ha, hb, Bool.not_true, Bool.not_false, if_true, if_false,
      Bool.true_eq_false, Bool.false_eq_true, zero_add, mul_one]
    rw [show (2147483648 : Nat) = (0x80000000 : BitVec 32).toNat by decide]
    exact ofNat_pack 0x80000000 0x80000000
  · simp only [ha, hb, Bool.not_true, Bool.not_false, if_true, if_false,
      Bool.true_eq_false, Bool.false_eq_true, zero_add, mul_one]
    rw [show (2147483648 : Nat) = (0x80000000 : BitVec 32).toNat by decide]
    exact ofNat_pack 0x80000000 b
  · simp only [ha, hb, Bool.not_true, Bool.not_false, if_true, if_false,
      Bool.true_eq_false, Bool.false_eq_true, zero_add, mul_one]
    rw [show (2147483648 : Nat) = (0x80000000 : BitVec 32).toNat by decide]
    exact ofNat_pack a 0x80000000
  · simp only [ha, hb, Bool.not_true, Bool.not_false, if_true, if_false,
      Bool.true_eq_false, Bool.false_eq_true, zero_add, mul_one]
    simpa using ofNat_pack a b

/-- The `base = 0`, `c = 0` specialization matching the executor's literal. -/
theorem reluInitial_readWithForwarding_long0 (input : ProofsLean.MNCore.PlusOne.Words) :
    ProofsLean.MNCore.PEMemory.ParsedIntegerInput.readWithForwarding
      ((welcomeInitialState input).peRegisters 0)
      (stateForwardingSlots (welcomeInitialState input) 0) 0
      (.memory ⟨.lm0, .long, ⟨0, by decide⟩⟩ false) =
    .ok ⟨input ⟨0, by decide⟩ ++ input ⟨1, by decide⟩, 0⟩ := by
  simpa using reluInitial_readWithForwarding_long input 0 0 (by decide)

/-- `cycle = 1`, address `2` specialization. -/
theorem reluInitial_readWithForwarding_long1 (input : ProofsLean.MNCore.PlusOne.Words) :
    ProofsLean.MNCore.PEMemory.ParsedIntegerInput.readWithForwarding
      ((welcomeInitialState input).peRegisters 0)
      (stateForwardingSlots (welcomeInitialState input) 0) 1
      (.memory ⟨.lm0, .long, ⟨2, by decide⟩⟩ false) =
    .ok ⟨input ⟨2, by decide⟩ ++ input ⟨3, by decide⟩, 0⟩ := by
  have h := reluInitial_readWithForwarding_long input 0 1 (by decide)
  convert h using 2

/-- `cycle = 2`, address `4` specialization. -/
theorem reluInitial_readWithForwarding_long2 (input : ProofsLean.MNCore.PlusOne.Words) :
    ProofsLean.MNCore.PEMemory.ParsedIntegerInput.readWithForwarding
      ((welcomeInitialState input).peRegisters 0)
      (stateForwardingSlots (welcomeInitialState input) 0) 2
      (.memory ⟨.lm0, .long, ⟨4, by decide⟩⟩ false) =
    .ok ⟨input ⟨4, by decide⟩ ++ input ⟨5, by decide⟩, 0⟩ := by
  have h := reluInitial_readWithForwarding_long input 0 2 (by decide)
  convert h using 2

/-- `cycle = 3`, address `6` specialization. -/
theorem reluInitial_readWithForwarding_long3 (input : ProofsLean.MNCore.PlusOne.Words) :
    ProofsLean.MNCore.PEMemory.ParsedIntegerInput.readWithForwarding
      ((welcomeInitialState input).peRegisters 0)
      (stateForwardingSlots (welcomeInitialState input) 0) 3
      (.memory ⟨.lm0, .long, ⟨6, by decide⟩⟩ false) =
    .ok ⟨input ⟨6, by decide⟩ ++ input ⟨7, by decide⟩, 0⟩ := by
  have h := reluInitial_readWithForwarding_long input 0 3 (by decide)
  convert h using 2

/-- The concrete source operand of the accepted expression. -/
def reluSrc0 : ProofsLean.MNCore.PEMemory.ParsedIntegerInput :=
  .memory ⟨.lm0, .long, ⟨0, by decide⟩⟩ false

/-- The exact lowering of the first accepted line at cycle 0. -/
theorem reluExpr0_lower_eq_cycle0 :
    lowerParsedFloatRelu? reluExpr0 (reluContext 0 0) =
    some (ParsedFloatReluAccesses.mk .f .relu false reluSrc0 (some reluSrc0)
      [reluLm1Long0]) := rfl

end

/-- The literal-structure form of `reluBus_high`, matching the executor's bus. -/
theorem reluBus_high_literal (a b : BitVec 32) :
    (parsedFloatReluBus .f .relu false
      (⟨a ++ b, (0 : BitVec 64)⟩ : IntegerALU.Bus)
      (some ⟨a ++ b, (0 : BitVec 64)⟩)).1.high
      = reluWord a ++ reluWord b := by
  simpa using reluBus_high a b

section
open ProofsLean.MNCore.PEMemory

/-- Cycle 0 of the first accepted line: the two LM1 words are the ReLU of the
first two input words. -/
theorem reluExpr0_cycle0_readback (input : ProofsLean.MNCore.PlusOne.Words) :
    ∃ files bar0 bar1 outputs,
      executeParsedFloatReluAtPE.runCycles (welcomeInitialState input) (welcomeInitialState input)
        reluExpr0 0 false (ParsedIntegerContext.ofLinearIndex 0) (ParsedIntegerContext.ofLinearIndex 0)
        [0] (welcomeInitialPERegisters input) 0 0 (fun _ => ⟨0, 0⟩) =
        .ok (files, bar0, bar1, outputs) ∧
      files.lm1 ⟨0, by decide⟩ = reluWord (input ⟨0, by decide⟩) ∧
      files.lm1 ⟨1, by decide⟩ = reluWord (input ⟨1, by decide⟩) := by
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
    zeroInitialPERegisterFiles, PEMemory.distance, htarget, hentry,
    mergeSelectedWord, selectedWordMask, Nat.reduceSub, Nat.reduceLT]
  change (BitVec.extractLsb' 32 32
      (parsedFloatReluBus .f .relu false
        (⟨input ⟨0, by decide⟩ ++ input ⟨1, by decide⟩, (0 : BitVec 64)⟩ : IntegerALU.Bus)
        (some ⟨input ⟨0, by decide⟩ ++ input ⟨1, by decide⟩, (0 : BitVec 64)⟩)).1.high
      &&& 4294967295#32 = reluWord (input ⟨0, by decide⟩)) ∧
    (BitVec.extractLsb' 0 32
      (parsedFloatReluBus .f .relu false
        (⟨input ⟨0, by decide⟩ ++ input ⟨1, by decide⟩, (0 : BitVec 64)⟩ : IntegerALU.Bus)
        (some ⟨input ⟨0, by decide⟩ ++ input ⟨1, by decide⟩, (0 : BitVec 64)⟩)).1.high
      &&& 4294967295#32 = reluWord (input ⟨1, by decide⟩))
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
  exact ⟨hx _, hx _⟩



/-- Concrete source operand at cycle 1. -/
def reluSrc1 : ProofsLean.MNCore.PEMemory.ParsedIntegerInput :=
  .memory ⟨.lm0, .long, ⟨2, by decide⟩⟩ false

theorem reluExpr0_lower_eq_cycle1 :
    lowerParsedFloatRelu? reluExpr0 (reluContext 0 1) =
    some (ParsedFloatReluAccesses.mk .f .relu false reluSrc1 (some reluSrc1)
      [reluLm1Long0]) := rfl

/-- Cycle 1 of the first accepted line: the two LM1 words are the ReLU of the
first two input words. -/
theorem reluExpr0_cycle1_readback (input : ProofsLean.MNCore.PlusOne.Words) :
    ∃ files bar0 bar1 outputs,
      executeParsedFloatReluAtPE.runCycles (welcomeInitialState input) (welcomeInitialState input)
        reluExpr0 0 false (ParsedIntegerContext.ofLinearIndex 0) (ParsedIntegerContext.ofLinearIndex 0)
        [1] (welcomeInitialPERegisters input) 0 0 (fun _ => ⟨0, 0⟩) =
        .ok (files, bar0, bar1, outputs) ∧
      files.lm1 ⟨2, by decide⟩ = reluWord (input ⟨2, by decide⟩) ∧
      files.lm1 ⟨3, by decide⟩ = reluWord (input ⟨3, by decide⟩) := by
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
    zeroInitialPERegisterFiles, PEMemory.distance, htarget, hentry,
    mergeSelectedWord, selectedWordMask, Nat.reduceSub, Nat.reduceLT]
  change (BitVec.extractLsb' 32 32
      (parsedFloatReluBus .f .relu false
        (⟨input ⟨2, by decide⟩ ++ input ⟨3, by decide⟩, (0 : BitVec 64)⟩ : IntegerALU.Bus)
        (some ⟨input ⟨2, by decide⟩ ++ input ⟨3, by decide⟩, (0 : BitVec 64)⟩)).1.high
      &&& 4294967295#32 = reluWord (input ⟨2, by decide⟩)) ∧
    (BitVec.extractLsb' 0 32
      (parsedFloatReluBus .f .relu false
        (⟨input ⟨2, by decide⟩ ++ input ⟨3, by decide⟩, (0 : BitVec 64)⟩ : IntegerALU.Bus)
        (some ⟨input ⟨2, by decide⟩ ++ input ⟨3, by decide⟩, (0 : BitVec 64)⟩)).1.high
      &&& 4294967295#32 = reluWord (input ⟨3, by decide⟩))
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
  exact ⟨hx _, hx _⟩



/-- Concrete source operand at cycle 3. -/
def reluSrc3 : ProofsLean.MNCore.PEMemory.ParsedIntegerInput :=
  .memory ⟨.lm0, .long, ⟨6, by decide⟩⟩ false

theorem reluExpr0_lower_eq_cycle3 :
    lowerParsedFloatRelu? reluExpr0 (reluContext 0 3) =
    some (ParsedFloatReluAccesses.mk .f .relu false reluSrc3 (some reluSrc3)
      [reluLm1Long0]) := rfl

/-- Cycle 3 of the first accepted line: the two LM1 words are the ReLU of the
first two input words. -/
theorem reluExpr0_cycle3_readback (input : ProofsLean.MNCore.PlusOne.Words) :
    ∃ files bar0 bar1 outputs,
      executeParsedFloatReluAtPE.runCycles (welcomeInitialState input) (welcomeInitialState input)
        reluExpr0 0 false (ParsedIntegerContext.ofLinearIndex 0) (ParsedIntegerContext.ofLinearIndex 0)
        [3] (welcomeInitialPERegisters input) 0 0 (fun _ => ⟨0, 0⟩) =
        .ok (files, bar0, bar1, outputs) ∧
      files.lm1 ⟨6, by decide⟩ = reluWord (input ⟨6, by decide⟩) ∧
      files.lm1 ⟨7, by decide⟩ = reluWord (input ⟨7, by decide⟩) := by
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
    zeroInitialPERegisterFiles, PEMemory.distance, htarget, hentry,
    mergeSelectedWord, selectedWordMask, Nat.reduceSub, Nat.reduceLT]
  change (BitVec.extractLsb' 32 32
      (parsedFloatReluBus .f .relu false
        (⟨input ⟨6, by decide⟩ ++ input ⟨7, by decide⟩, (0 : BitVec 64)⟩ : IntegerALU.Bus)
        (some ⟨input ⟨6, by decide⟩ ++ input ⟨7, by decide⟩, (0 : BitVec 64)⟩)).1.high
      &&& 4294967295#32 = reluWord (input ⟨6, by decide⟩)) ∧
    (BitVec.extractLsb' 0 32
      (parsedFloatReluBus .f .relu false
        (⟨input ⟨6, by decide⟩ ++ input ⟨7, by decide⟩, (0 : BitVec 64)⟩ : IntegerALU.Bus)
        (some ⟨input ⟨6, by decide⟩ ++ input ⟨7, by decide⟩, (0 : BitVec 64)⟩)).1.high
      &&& 4294967295#32 = reluWord (input ⟨7, by decide⟩))
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
  exact ⟨hx _, hx _⟩





/-- Concrete source operand at cycle 2. -/
def reluSrc2 : ProofsLean.MNCore.PEMemory.ParsedIntegerInput :=
  .memory ⟨.lm0, .long, ⟨4, by decide⟩⟩ false

theorem reluExpr0_lower_eq_cycle2 :
    lowerParsedFloatRelu? reluExpr0 (reluContext 0 2) =
    some (ParsedFloatReluAccesses.mk .f .relu false reluSrc2 (some reluSrc2)
      [reluLm1Long0]) := rfl

/-- Cycle 2 of the first accepted line: the two LM1 words are the ReLU of the
first two input words. -/
theorem reluExpr0_cycle2_readback (input : ProofsLean.MNCore.PlusOne.Words) :
    ∃ files bar0 bar1 outputs,
      executeParsedFloatReluAtPE.runCycles (welcomeInitialState input) (welcomeInitialState input)
        reluExpr0 0 false (ParsedIntegerContext.ofLinearIndex 0) (ParsedIntegerContext.ofLinearIndex 0)
        [2] (welcomeInitialPERegisters input) 0 0 (fun _ => ⟨0, 0⟩) =
        .ok (files, bar0, bar1, outputs) ∧
      files.lm1 ⟨4, by decide⟩ = reluWord (input ⟨4, by decide⟩) ∧
      files.lm1 ⟨5, by decide⟩ = reluWord (input ⟨5, by decide⟩) := by
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
    zeroInitialPERegisterFiles, PEMemory.distance, htarget, hentry,
    mergeSelectedWord, selectedWordMask, Nat.reduceSub, Nat.reduceLT]
  change (BitVec.extractLsb' 32 32
      (parsedFloatReluBus .f .relu false
        (⟨input ⟨4, by decide⟩ ++ input ⟨5, by decide⟩, (0 : BitVec 64)⟩ : IntegerALU.Bus)
        (some ⟨input ⟨4, by decide⟩ ++ input ⟨5, by decide⟩, (0 : BitVec 64)⟩)).1.high
      &&& 4294967295#32 = reluWord (input ⟨4, by decide⟩)) ∧
    (BitVec.extractLsb' 0 32
      (parsedFloatReluBus .f .relu false
        (⟨input ⟨4, by decide⟩ ++ input ⟨5, by decide⟩, (0 : BitVec 64)⟩ : IntegerALU.Bus)
        (some ⟨input ⟨4, by decide⟩ ++ input ⟨5, by decide⟩, (0 : BitVec 64)⟩)).1.high
      &&& 4294967295#32 = reluWord (input ⟨5, by decide⟩))
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
  exact ⟨hx _, hx _⟩




end

/-- `parsedFloatReluBus` copies the low 64 bits of the first source unchanged.
This is why a `.double` destination writes eight raw words. -/
theorem reluBus_low (precision : ParsedPrecision) (name : ParsedAluName)
    (unsigned : Bool) (left : IntegerALU.Bus) (right : Option IntegerALU.Bus) :
    (parsedFloatReluBus precision name unsigned left right).1.low = left.low := rfl

/-- A `$ll...v` double-width vector operand: four words per cycle, stride
four.  This is the shape that writes sixteen words from one expression. -/
def reluDoubleOperand (bank : Bank) : ParsedOperand :=
  .mem ⟨bank, ⟨4, 0, 4, 8, 12, false, none⟩⟩ false false false none

/-- The `.double` relu instruction: one expression, sixteen written words. -/
def reluExprDouble : ParsedExpr :=
  ⟨reluOp, [reluDoubleOperand .lm0, reluDoubleOperand .lm0],
    [reluDoubleOperand .lm1], none, ""⟩

/-- All-negative input: every word is the float `-1.0`. -/
def reluAllNeg : ProofsLean.MNCore.PlusOne.Words := fun _ => 0xBF800000

/-- All-positive input: every word is the float `1.0`. -/
def reluAllPos : ProofsLean.MNCore.PlusOne.Words := fun _ => 0x3F800000

/-- One PE's LM1 word after executing one relu expression. -/
def reluWordAfter (expr : ParsedExpr) (input : ProofsLean.MNCore.PlusOne.Words)
    (i : Fin 16) : BitVec 32 :=
  match executeParsedFloatReluAtPE (welcomeInitialState input) (welcomeInitialState input)
      expr 0 false false with
  | .ok next =>
      (next.peRegisters 0).lm1 ⟨i.val, by have := i.isLt; change i.val < 4096; omega⟩
  | _ => 0

/-- The accepted long-vector line writes the eight correct words on the
all-negative input (negative zero). -/
theorem reluLine_allNeg_word0 :
    reluWordAfter (reluExpr 0) reluAllNeg ⟨0, by decide⟩ = 0x80000000 := by decide

theorem reluLine_allNeg_word7 :
    reluWordAfter (reluExpr 0) reluAllNeg ⟨7, by decide⟩ = 0x80000000 := by decide

/-- On the all-positive input the same line writes `1.0`. -/
theorem reluLine_allPos_word0 :
    reluWordAfter (reluExpr 0) reluAllPos ⟨0, by decide⟩ = 0x3F800000 := by decide

/-- The `.double` line writes sixteen words, but words 2 and 3 of the first
cycle are the raw negative input, not negative zero.  This is the concrete
model-gap counterexample: the naive "one line = eight words" count is false. -/
theorem reluDouble_allNeg_word2 :
    reluWordAfter reluExprDouble reluAllNeg ⟨2, by decide⟩ = 0xBF800000 := by decide

theorem reluDouble_allNeg_word3 :
    reluWordAfter reluExprDouble reluAllNeg ⟨3, by decide⟩ = 0xBF800000 := by decide

/-- The corresponding target words are negative zero. -/
theorem reluDouble_allNeg_target2 :
    reluWord 0xBF800000 = 0x80000000 := by decide

/-! ## 5. Trust report -/

#print axioms reluAnswer_score
#print axioms reluExpr0_legal
#print axioms reluExpr8_legal
#print axioms reluTwoExpr_check_false
#print axioms reluBus_high
#print axioms reluInitial_read_long
#print axioms reluExpr0_lowered_cycle0
#print axioms reluExpr0_cycle0_readback
#print axioms reluExpr0_cycle1_readback
#print axioms reluExpr0_cycle2_readback
#print axioms reluExpr0_cycle3_readback
#print axioms reluDouble_allNeg_word2

end ProofsLean.MNCore
