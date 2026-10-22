import ProofsLean.CendCycleData

/-! # `12.convert-endian`: closing the plain family

`ProofsLean/CendCycleData.lean` proves the per-cycle half-mix data dispatch, the
per-cycle LM1 alignment and the four-cycle lift.  This module turns them into the
unconditional plain-family statements: the per-word obligation,
`CendPlainALUBothHalvesRefuted`, and the refutation of every plain line and every
plain-family line.

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

/-- A successful sealed step of a `.pe` line is accepted by the issue checker. -/
theorem cendStep_accepted (expressions : List NormalizedExpr) (x : BitVec 64) (next : State)
    (step : cendStep expressions x = some next) :
    checkParsedTopLine (InstructionLine.pe expressions).toParsed = true := by
  have executed := cendSealed_step_ok step
  have lineExecuted : executeIntegerProducerInstructionLine (.pe expressions)
      (cendInitialState x) = .ok next := by
    unfold executeNormalizedLine at executed
    simp only [Issue.InstructionLine.toNormalizedLine, NormalizedLine.toInstruction?] at executed
    exact executed
  exact executeIntegerProducerInstructionLine_accepted_of_ok _ _ _ lineExecuted

/-- A `.alu` row whose precision is not established can never take a step. -/
theorem cendALURow_none_contradiction (e : NormalizedExpr) (x : BitVec 64) (next : State)
    (name : ParsedAluName) (unsigned : Bool) (arg : Option (Fin 256))
    (plainE : parsedExprIsPlainIntegerALU e.toParsed = true)
    (operation : e.toParsed.op = .alu name none unsigned arg)
    (step : cendStep [e] x = some next) : False := by
  have plainList : ([e].map NormalizedExpr.toParsed).all
      parsedExprIsPlainIntegerALU = true := by
    simpa using plainE
  obtain ⟨writes, slots, bars, prep, committed⟩ :=
    cendSealed_pe_prepared [e] (cendInitialState x) plainList step
  simp only [List.map_cons, List.map_nil] at prep
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
      (Or.inl ⟨name, none, unsigned, arg, operation⟩) prep
  exact absurd alu
    (prepareParsedIntegerALUExprCycles_alu_none_not_ok
      ((cendInitialState x).peRegisters cendPE)
      (stateForwardingSlots (cendInitialState x) cendPE) e.toParsed
      (parsedPEHazardControl (cendInitialState x) cendPE)
      ([e.toParsed].any parsedExprHasSingleLineWriteMask)
      ([e.toParsed].any fun expression => match expression.op with
        | .noforward => true | _ => false) false name unsigned arg operation writes outSlots)

/-- A single plain `.alu` row at the witness commits a half-mix observed word. -/
theorem cendALURow_halfMix (e : NormalizedExpr) (next : State)
    (name : ParsedAluName) (precision : ParsedPrecision) (unsigned : Bool)
    (arg : Option (Fin 256))
    (plainE : parsedExprIsPlainIntegerALU e.toParsed = true)
    (operation : e.toParsed.op = .alu name (some precision) unsigned arg)
    (step : cendStep [e] cendLm1Witness = some next) :
    cendOutputWord0 next ∈ cendHalfMixWords cendLm1Witness := by
  have plainList : ([e].map NormalizedExpr.toParsed).all
      parsedExprIsPlainIntegerALU = true := by
    simpa using plainE
  obtain ⟨writes, slots, bars, prep, committed⟩ :=
    cendSealed_pe_prepared [e] (cendInitialState cendLm1Witness) plainList step
  simp only [List.map_cons, List.map_nil] at prep
  obtain ⟨dataOk, destAligned⟩ :=
    cendPlainALURow_dataAndAligned cendLm1Witness e name precision unsigned arg plainE
      operation writes slots bars prep
  unfold cendOutputWord0
  rw [committed]
  exact commitParsedMaskedWrites_lm1_halfMix_halfMix_zero cendLm1Witness writes
    ⟨0, by decide⟩ (by decide) dataOk destAligned _
    (fun address => cendInitialPERegisters_lm1 cendLm1Witness address)

/-- A single constant row prepares an input-independent write list, so its
observed word is constant. -/
theorem cendConstantRow_constant (e : NormalizedExpr) (next : State)
    (plainE : parsedExprIsPlainIntegerALU e.toParsed = true)
    (constant : e.toParsed.op = .zero ∨
      ∃ payload sparse, e.toParsed.op = .immediate payload sparse)
    (step : cendStep [e] cendLm1Witness = some next) :
    ∃ value, ∀ (y : BitVec 64) (nextY : State),
      cendStep [e] y = some nextY → cendOutputWord0 nextY = value := by
  refine ⟨cendOutputWord0 next, ?_⟩
  intro y nextY stepY
  have plainList : ([e].map NormalizedExpr.toParsed).all
      parsedExprIsPlainIntegerALU = true := by
    simpa using plainE
  obtain ⟨writesY, slotsY, barsY, prepY, committedY⟩ :=
    cendSealed_pe_prepared [e] (cendInitialState y) plainList stepY
  obtain ⟨writesW, slotsW, barsW, prepW, committedW⟩ :=
    cendSealed_pe_prepared [e] (cendInitialState cendLm1Witness) plainList step
  simp only [List.map_cons, List.map_nil] at prepY prepW
  have prepEq : welcomeIntegerPrep (cendInitialState y) cendPE [e.toParsed] =
      welcomeIntegerPrep (cendInitialState cendLm1Witness) cendPE [e.toParsed] := by
    apply welcomeIntegerPrep_constant_eq (stateA := cendInitialState y)
      (stateB := cendInitialState cendLm1Witness) e.toParsed plainE constant
    · rw [cendInitialState_maskRegisters_eq y,
        cendInitialState_maskRegisters_eq cendLm1Witness]
    · funext unit cycle
      rw [cendInitialForwardingSlots_poison y,
        cendInitialForwardingSlots_poison cendLm1Witness]
    · rw [cendInitialState_control_eq y, cendInitialState_control_eq cendLm1Witness]
    · rfl
  rw [prepEq] at prepY
  have writesEq : writesY = writesW :=
    (Prod.mk.inj (StepResult.ok.inj (prepY.symm.trans prepW))).1
  unfold cendOutputWord0
  rw [committedY, committedW, writesEq]
  have hfiles : (cendInitialPERegisters y).lm1 =
      (cendInitialPERegisters cendLm1Witness).lm1 := rfl
  exact congrFun (commitParsedMaskedWrites_lm1_congr (cendInitialPERegisters y)
    (cendInitialPERegisters cendLm1Witness) writesW writesW hfiles rfl)
    ⟨0, by decide⟩

/-- The obligation for a singleton plain row. -/
theorem cendHalfMixWordObligation_singleton (e : NormalizedExpr) (next : State)
    (plainE : parsedExprIsPlainIntegerALU e.toParsed = true)
    (step : cendStep [e] cendLm1Witness = some next) :
    cendOutputWord0 next = 0 ∨
      cendOutputWord0 next ∈ cendHalfMixWords cendLm1Witness ∨
      ∃ value, ∀ (y : BitVec 64) (nextY : State),
        cendStep [e] y = some nextY → cendOutputWord0 nextY = value := by
  rcases plain_op_cases e.toParsed plainE with
    ⟨name, precision, unsigned, arg, hAlu⟩ | hZero | ⟨payload, sparse, hImm⟩
  · cases precision with
    | none =>
        exact False.elim (cendALURow_none_contradiction e cendLm1Witness next name unsigned
          arg plainE hAlu step)
    | some precision =>
        exact Or.inr (Or.inl (cendALURow_halfMix e next name precision unsigned arg plainE
          hAlu step))
  · exact Or.inr (Or.inr (cendConstantRow_constant e next plainE (Or.inl hZero) step))
  · exact Or.inr (Or.inr (cendConstantRow_constant e next plainE
      (Or.inr ⟨payload, sparse, hImm⟩) step))

/-- **Every plain line satisfies the corrected half-mix word obligation.** -/
theorem cendHalfMixWordObligation_of_plain (expressions : List NormalizedExpr)
    (plain : (expressions.map NormalizedExpr.toParsed).all
      parsedExprIsPlainIntegerALU = true) :
    CendHalfMixWordObligation expressions cendOutputWord0 := by
  intro next step
  have accepted := cendStep_accepted expressions cendLm1Witness next step
  have accepted' : checkParsedTopLine (.pe (expressions.map NormalizedExpr.toParsed)) = true := by
    simpa [InstructionLine.toParsed, NormalizedExpr.toParsed] using accepted
  have legal : LegalParsedLine (expressions.map NormalizedExpr.toParsed) :=
    parsed_topline_check_sound (.pe (expressions.map NormalizedExpr.toParsed)) accepted'
  have lengthLe := plain_legal_length_le_one expressions legal plain
  rcases Nat.eq_zero_or_pos expressions.length with zero | pos
  · have empty : expressions = [] := List.length_eq_zero_iff.mp zero
    rw [empty] at step ⊢
    left
    obtain ⟨writes, slots, bars, prep, committed⟩ :=
      cendSealed_pe_prepared [] (cendInitialState cendLm1Witness) (by simp) step
    have writesNil : writes = [] := by
      unfold welcomeIntegerPrep at prep
      simp only [prepareParsedIntegerMatrixReadLineCycles,
        prepareParsedIntegerMatrixReadLineExpressions] at prep
      exact (Prod.mk.inj (StepResult.ok.inj prep)).1.symm
    unfold cendOutputWord0
    rw [committed, writesNil, commitParsedMaskedWrites_nil]
    exact cendInitialPERegisters_lm1 cendLm1Witness ⟨0, by decide⟩
  · have lengthOne : expressions.length = 1 := by omega
    obtain ⟨e, same⟩ := List.length_eq_one_iff.mp lengthOne
    rw [same] at step plain ⊢
    exact cendHalfMixWordObligation_singleton e next (by simpa using plain) step

/-- **The narrowed both-halves residual, unconditionally.** -/
theorem cendPlainALUBothHalvesRefutedLm1 : CendPlainALUBothHalvesRefutedLm1 :=
  cendPlainALUBothHalvesRefutedLm1_of_halfMixObligation
    (fun expressions plain both hasLm1 => cendHalfMixWordObligation_of_plain expressions plain)

/-- **The both-halves plain family is refuted, unconditionally.**  The corrected
half-mix value set closes the OMR→memory feedback branch, so no syntactic side
condition is needed. -/
theorem cendPlainALUBothHalvesRefuted : CendPlainALUBothHalvesRefuted :=
  cendPlainALUBothHalvesRefuted_of_halfMixObligation
    (fun expressions plain both hasLm1 => cendHalfMixWordObligation_of_plain expressions plain)

/-- **Every plain line is refuted, unconditionally.** -/
theorem cendPE_plain_not_correct_unconditional (expressions : List NormalizedExpr)
    (plain : (expressions.map NormalizedExpr.toParsed).all
      parsedExprIsPlainIntegerALU = true) :
    ¬ ProofsLean.Correct cendSealedMachine cendSpec
      ([InstructionLine.pe expressions] : List InstructionLine) :=
  cendPE_plain_not_correct cendPlainALUBothHalvesRefuted expressions plain

/-- **The plain family is refuted, unconditionally.** -/
theorem cendPE_plainLines_not_correct_unconditional (expressions : List NormalizedExpr)
    (plain : CendPlainLines expressions) :
    ¬ ProofsLean.Correct cendSealedMachine cendSpec
      ([InstructionLine.pe expressions] : List InstructionLine) :=
  cendPE_plainLines_not_correct cendPlainALUBothHalvesRefuted expressions plain

/-- **Bound two from the plain family and the recorded non-plain residual.**  The
plain-family hypothesis of `cendLowerBound_two_of_plainHalfMix_and_nonClosed` is
now discharged, so the remaining work for `LowerBound cendSealedMachine cendSpec 2`
is exactly `CendPENonClosedRefuted` (the non-plain families). -/
theorem cendLowerBound_two_of_nonClosed_plainDischarged (nonClosed : CendPENonClosedRefuted) :
    ProofsLean.LowerBound cendSealedMachine cendSpec 2 :=
  cendLowerBound_two_of_plainHalfMix_and_nonClosed
    (fun expressions plain both hasLm1 => cendHalfMixWordObligation_of_plain expressions plain)
    nonClosed

/-! ## Trust report -/

#print axioms cendPlainCycleHalfMixData
#print axioms cendPlainCycleLm1Aligned_general
#print axioms cendPlainALURow_dataAndAligned
#print axioms cendHalfMixWordObligation_of_plain
#print axioms cendPlainALUBothHalvesRefuted
#print axioms cendPE_plain_not_correct_unconditional
#print axioms cendPE_plainLines_not_correct_unconditional
#print axioms cendPlainALUBothHalvesRefutedLm1
#print axioms cendLowerBound_two_of_nonClosed_plainDischarged
