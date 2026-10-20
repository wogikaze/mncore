import ProofsLean.WelcomePlainShape
import ProofsLean.FootprintReconciled

/-! # Closing the plain-class reduction

This module discharges the two remaining `Prop`s of
`WelcomePlainShape.lean` §10, in the order they are stated there:

1. `WelcomePEPlainStepShapeExceptImmediate` — the executor's write list of a
   plain, unrefuted, non-immediate-double line is committed to PE 0's register
   file and is either a list of copied `.double` blocks or fits four narrow
   windows;
2. `WelcomePEPlainImmediateDoubleObligation` — a plain line containing an
   `.immediate` row with an `.lm1 .double` destination has input-independent
   PE 0 `LM1` output.

The proofs rest on one structural observation that the earlier rounds did not
use: the issue checker's `groupsUnique` constraint says that **two distinct
rows of one issue line cannot share an issue group**, and every plain row
(`.alu`, `.zero`, `.immediate`) has issue group `.alu`.  Hence an unrefuted
plain line has **at most one row**.  Since `WelcomePEUnrefuted` also excludes
the all-`.noforward` line, a plain unrefuted line has exactly one row, so the
four-cycle fold of that row is the whole line's prepared write list.  This
removes the `writesUnique` bridge, the multi-expression fold and all
cross-expression forwarding questions in one stroke.

## What is proved here

* **`WelcomePEPlainImmediateDoubleObligation` is discharged** as the theorem
  `welcomePEPlainImmediateDoubleObligation` (section 8).  On a plain unrefuted
  line the issue checker's `groupsUnique` forces a single row, and if that row
  is `.immediate` the whole four-cycle preparation is independent of the
  register file (the mask registers agree, the constant evaluation ignores its
  inputs).  The all-zero and all-five runs therefore produce the identical
  write list, and the two initial files agree on `LM1`, so the committed `LM1`
  halves agree.
* The exact-prepared-list extraction machinery the two obligations needed
  (`welcomeIntegerPrep`, `executeIntegerProducerLineAtPEs_prepared`,
  `welcomeSealed_pe_prepared`, `welcomeIntegerPrep_inv`,
  `prepareParsedIntegerALUExprCycles_four`) is unconditional.
* The `LM1` counting and provenance lemmas for the remaining per-cycle
  destination analysis are unconditional: `lm1Destinations_count_le_one`,
  `lm1Destinations_unique_positions`, `filter_isLm1_length`,
  `mapM_lm1_count_le`, `constantTargets_lm1_count_le`,
  `toDirectMaskedIntegerWritesInLine?_mem_provenance`,
  `toDirectMaskedConstantWrites?_mem_provenance`,
  `lm1Windows_length_eq_count`.

## What remains

`WelcomePEPlainStepShapeExceptImmediate` is **not** proved here.  Its remaining
content is the per-cycle destination/shape analysis of the nine branches of
`prepareParsedIntegerALUExprCycle` (direct, multiple, OMR, no-write, BAR,
mask-input, memory-then-input, input-then-memory, constant), namely for each
cycle chunk: (i) every `.lm1` write resolves a destination operand of the row,
(ii) a `.double` `.lm1` write has a copied third data word, and (iii) at most
one `.lm1` write occurs.  The single-row reduction, the four-cycle fold
(`prepareParsedIntegerALUExprCycles_four`), the slot frame
(`updateParsedIntegerALUForwardingCycle_frame`), and all provenance/counting
lemmas those facts consume are proved above.  Consequently
`WelcomePEPlainShapeObligation` is not yet available from the two obligations,
and neither `welcomeLowerBound_two` nor `Optimal` is claimed.

No `sorry`, no `admit`, no `native_decide`, no new axioms.
-/

namespace ProofsLean.MNCore

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

open Issue
open PEMemory

/-! ## 1. A plain line has at most one row

`groupsUnique` is the second conjunct of `Issue.Legal`.  The issue group of a
plain row is `.alu`, and `projectLine` numbers rows by their position, so two
different plain rows would be two different-id expressions of the same group. -/

/-- The operation of a plain integer-ALU row is `.alu`, `.zero` or
`.immediate`. -/
theorem plainExpr_op_cases (expression : ParsedExpr)
    (plain : parsedExprIsPlainIntegerALU expression = true) :
    (∃ name precision unsigned arg, expression.op = .alu name precision unsigned arg) ∨
      expression.op = .zero ∨
      ∃ payload sparse, expression.op = .immediate payload sparse := by
  cases expression with
  | mk op sources destinations flush text =>
      cases op <;>
        simp_all [parsedExprIsPlainIntegerALU, parsedExprIsIntegerProducer,
          parsedExprIsUnsupportedRustAlu, parsedExprIsMslMsrProducer,
          parsedExprIsFloatReluProducer, parsedExprIsBlockFloatProducer]

/-- Every plain integer-ALU row issues in the `.alu` group. -/
theorem plainExpr_issueGroup (expression : ParsedExpr)
    (plain : parsedExprIsPlainIntegerALU expression = true) :
    expression.issueGroup = some .alu := by
  rcases plainExpr_op_cases expression plain with
    ⟨name, precision, unsigned, arg, op⟩ | op | ⟨payload, sparse, op⟩
  · rw [ParsedExpr.issueGroup, op]
  · rw [ParsedExpr.issueGroup, op]
  · rw [ParsedExpr.issueGroup, op]

theorem projectFrom_length (nextId : Nat) (expressions : List ParsedExpr) :
    (projectFrom nextId expressions).length = expressions.length := by
  induction expressions generalizing nextId with
  | nil => rfl
  | cons expression rest ih =>
      simp only [projectFrom, List.length_cons, ih]

/-- `projectFrom` numbers the rows consecutively from `nextId`. -/
theorem projectFrom_getElem_id (nextId : Nat) (expressions : List ParsedExpr) :
    ∀ (i : Nat) (hi : i < (projectFrom nextId expressions).length),
      ((projectFrom nextId expressions)[i]'hi).id = nextId + i := by
  induction expressions generalizing nextId with
  | nil =>
      intro i hi
      exact absurd hi (by simp [projectFrom])
  | cons expression rest ih =>
      intro i hi
      cases i with
      | zero => simp [projectFrom, ParsedExpr.toIssueExpr]
      | succ i =>
          have hi' : i < (projectFrom (nextId + 1) rest).length := by
            have h := hi
            simp only [projectFrom, List.length_cons] at h
            omega
          have hrec := ih (nextId + 1) i hi'
          have hleft : ((projectFrom nextId (expression :: rest))[i + 1]'hi) =
              ((projectFrom (nextId + 1) rest)[i]'hi') := by
            simp only [projectFrom, List.getElem_cons_succ]
          rw [hleft, hrec]
          omega

/-- The group of the `i`-th projected row is the issue group of the `i`-th
source row. -/
theorem projectFrom_getElem_group (nextId : Nat) (expressions : List ParsedExpr) :
    ∀ (i : Nat) (hi : i < (projectFrom nextId expressions).length)
      (hin : i < expressions.length) (group : Issue.Group),
      (expressions[i]'hin).issueGroup = some group →
      ((projectFrom nextId expressions)[i]'hi).group = some group := by
  induction expressions generalizing nextId with
  | nil =>
      intro i hi hin group _
      simp at hin
  | cons expression rest ih =>
      intro i hi hin group hgroup
      cases i with
      | zero =>
          have hleft : ((projectFrom nextId (expression :: rest))[0]'hi) =
              (expression.toIssueExpr nextId) := by
            simp only [projectFrom]
            rfl
          rw [hleft]
          have hhead : (expression :: rest)[0]'hin = expression := rfl
          rw [hhead] at hgroup
          change expression.issueGroup = some group
          rw [hgroup]
      | succ i =>
          have hi' : i < (projectFrom (nextId + 1) rest).length := by
            have h := hi
            simp only [projectFrom, List.length_cons] at h
            omega
          have hin' : i < rest.length := by
            simp only [List.length_cons] at hin
            omega
          have hleft : ((projectFrom nextId (expression :: rest))[i + 1]'hi) =
              ((projectFrom (nextId + 1) rest)[i]'hi') := by
            simp only [projectFrom, List.getElem_cons_succ]
          have htail : (expression :: rest)[i + 1]'hin = rest[i]'hin' := by
            simp only [List.getElem_cons_succ]
          rw [hleft, htail] at *
          exact ih (nextId + 1) i hi' hin' group hgroup

theorem projectLine_getElem_group (expressions : List ParsedExpr) :
    ∀ (i : Nat) (hi : i < (projectLine expressions).length)
      (hin : i < expressions.length) (group : Issue.Group),
      (expressions[i]'hin).issueGroup = some group →
      ((projectLine expressions)[i]'hi).group = some group :=
  projectFrom_getElem_group 0 expressions

theorem projectLine_getElem_id (expressions : List ParsedExpr) :
    ∀ (i : Nat) (hi : i < (projectLine expressions).length),
      ((projectLine expressions)[i]'hi).id = i := by
  intro i hi
  show ((projectFrom 0 expressions)[i]'hi).id = i
  have := projectFrom_getElem_id 0 expressions i hi
  omega

/-- **A plain accepted line has at most one row.** -/
theorem plain_legal_length_le_one (expressions : List NormalizedExpr)
    (legal : LegalParsedLine (expressions.map NormalizedExpr.toParsed))
    (plain : (expressions.map NormalizedExpr.toParsed).all
      parsedExprIsPlainIntegerALU = true) :
    expressions.length ≤ 1 := by
  let line := expressions.map NormalizedExpr.toParsed
  have projLength : (projectLine line).length = expressions.length := by
    show (projectFrom 0 line).length = expressions.length
    rw [projectFrom_length]
    simp [line]
  by_contra tooLong
  have atLeast : 2 ≤ expressions.length := by omega
  have lineAtLeast : 2 ≤ line.length := by simpa [line] using atLeast
  have h0 : 0 < (projectLine line).length := by omega
  have h1 : 1 < (projectLine line).length := by omega
  have rowLen0 : 0 < line.length := by omega
  have rowLen1 : 1 < line.length := by omega
  have all := List.all_eq_true.mp plain
  have row0Plain : parsedExprIsPlainIntegerALU (line[0]'rowLen0) = true :=
    all _ (List.getElem_mem rowLen0)
  have row1Plain : parsedExprIsPlainIntegerALU (line[1]'rowLen1) = true :=
    all _ (List.getElem_mem rowLen1)
  have group0 : ((projectLine line)[0]'h0).group = some .alu :=
    projectLine_getElem_group line 0 h0 rowLen0 .alu (plainExpr_issueGroup _ row0Plain)
  have group1 : ((projectLine line)[1]'h1).group = some .alu :=
    projectLine_getElem_group line 1 h1 rowLen1 .alu (plainExpr_issueGroup _ row1Plain)
  have ids : ((projectLine line)[0]'h0).id ≠ ((projectLine line)[1]'h1).id := by
    rw [projectLine_getElem_id line 0 h0, projectLine_getElem_id line 1 h1]
    decide
  have unique := legal.2.1
  exact unique ((projectLine line)[0]'h0) (List.getElem_mem h0)
    ((projectLine line)[1]'h1) (List.getElem_mem h1) ids .alu group0
    (by simp [group1])

def welcomeIntegerPrep (state : State) (pe : PEId) (expressions : List ParsedExpr) :
    StepResult (List PreparedParsedMaskedWrite × Forwarding.Slots ×
      List (Bool × BitVec 12)) :=
  prepareParsedIntegerMatrixReadLineCycles (state.peRegisters pe)
    (stateForwardingSlots state pe)
    (state.matrixRegisters (ParsedIntegerContext.ofLinearIndex pe).group
      (ParsedIntegerContext.ofLinearIndex pe).l2b
      (ParsedIntegerContext.ofLinearIndex pe).l1b)
    (expressions.filter parsedExprIsIntegerMatrixReadStageInput)
    (parsedPEHazardControl state pe) false

theorem welcomeIntegerPrep_congr (expressions : List ParsedExpr) {s t : State} (p : PEId)
    (hregs : t.peRegisters p = s.peRegisters p)
    (hforwarding : t.forwarding p = s.forwarding p)
    (hvalid : t.forwardingValid p = s.forwardingValid p)
    (hmatrix : t.matrixRegisters = s.matrixRegisters)
    (hmask : t.maskDirective = s.maskDirective)
    (hcontext : t.peContext p = s.peContext p)
    (hclock : t.hazardClock = s.hazardClock) :
    welcomeIntegerPrep t p expressions = welcomeIntegerPrep s p expressions := by
  unfold welcomeIntegerPrep
  have hslots : stateForwardingSlots t p = stateForwardingSlots s p := by
    funext unit cycle
    simp [stateForwardingSlots, hforwarding, hvalid]
  have hcontrol : parsedPEHazardControl t p = parsedPEHazardControl s p := by
    simp only [parsedPEHazardControl]
    rw [hcontext, hmask, hclock]
  rw [hregs, hslots, hmatrix, hcontrol]

theorem executeIntegerProducerLineAtPECore_prepared
    (expressions : List ParsedExpr) (state next : State) (pe : PEId)
    (floatEmpty : expressions.filter parsedExprIsSupportedFloatMAUProducer = [])
    (executed : executeIntegerProducerLineAtPECore expressions state pe = .ok next) :
    ∃ writes slots bars,
      welcomeIntegerPrep state pe expressions = .ok (writes, slots, bars) ∧
      next.peRegisters pe = commitParsedMaskedWrites (state.peRegisters pe) writes := by
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
    · simp only [StepResult.ok.injEq] at executed
      unfold parsedIntegerMatrixReadLineFourCycleStep at fourCycle
      split at fourCycle
      · simp at fourCycle
      · simp at fourCycle
      · rename_i writes preparedSlots preparedBars prepared
        simp only [StepResult.ok.injEq, Prod.mk.injEq] at fourCycle
        obtain ⟨rfl, rfl, rfl⟩ := fourCycle
        refine ⟨writes, preparedSlots, preparedBars, ?_, ?_⟩
        · exact prepared
        · subst executed
          simp

theorem executeIntegerProducerLineAtPECore_peFields_other
    (expressions : List ParsedExpr) (state next : State) (pe other : PEId)
    (different : other ≠ pe)
    (executed : executeIntegerProducerLineAtPECore expressions state pe = .ok next) :
    next.peRegisters other = state.peRegisters other ∧
      next.forwarding other = state.forwarding other ∧
      next.forwardingValid other = state.forwardingValid other ∧
      next.peContext other = state.peContext other := by
  rw [executeIntegerProducerLineAtPECore.eq_1] at executed
  split at executed
  · simp at executed
  · simp at executed
  · split at executed
    · simp at executed
    · simp at executed
    · simp only [updateSupportedPELineForwarding] at executed
      split at executed
      · simp at executed
      · simp at executed
      · simp only [StepResult.ok.injEq] at executed
        subst executed
        simp [different]

theorem executeIntegerProducerLineAtPE_peFields_other
    (expressions : List ParsedExpr) (state next : State) (pe other : PEId)
    (different : other ≠ pe)
    (executed : executeIntegerProducerLineAtPE expressions state pe = .ok next) :
    next.peRegisters other = state.peRegisters other ∧
      next.forwarding other = state.forwarding other ∧
      next.forwardingValid other = state.forwardingValid other ∧
      next.peContext other = state.peContext other := by
  unfold executeIntegerProducerLineAtPE at executed
  split at executed
  · simp at executed
  · exact executeIntegerProducerLineAtPECore_peFields_other expressions state next pe other
      different executed

theorem executeIntegerProducerLineAtPE_prepared
    (expressions : List ParsedExpr) (state next : State) (pe : PEId)
    (floatEmpty : expressions.filter parsedExprIsSupportedFloatMAUProducer = [])
    (executed : executeIntegerProducerLineAtPE expressions state pe = .ok next) :
    ∃ writes slots bars,
      welcomeIntegerPrep state pe expressions = .ok (writes, slots, bars) ∧
      next.peRegisters pe = commitParsedMaskedWrites (state.peRegisters pe) writes := by
  unfold executeIntegerProducerLineAtPE at executed
  split at executed
  · simp at executed
  · exact executeIntegerProducerLineAtPECore_prepared expressions state next pe floatEmpty executed

theorem executeIntegerProducerLineAtPEs_prepared
    (expressions : List ParsedExpr) (pes : List PEId) (state next : State)
    (floatEmpty : expressions.filter parsedExprIsSupportedFloatMAUProducer = [])
    (executed : executeIntegerProducerLineAtPEs expressions pes state = .ok next)
    (nodup : pes.Nodup) (p : PEId) (mem : p ∈ pes) :
    ∃ writes slots bars,
      welcomeIntegerPrep state p expressions = .ok (writes, slots, bars) ∧
      next.peRegisters p = commitParsedMaskedWrites (state.peRegisters p) writes := by
  induction pes generalizing state with
  | nil => simp at mem
  | cons pe rest ih =>
      obtain ⟨peNotRest, restNodup⟩ := List.nodup_cons.mp nodup
      simp only [executeIntegerProducerLineAtPEs] at executed
      split at executed
      · simp at executed
      · simp at executed
      · rename_i middle headExecuted
        by_cases same : p = pe
        · subst p
          obtain ⟨writes, slots, bars, prep, committed⟩ :=
            executeIntegerProducerLineAtPE_prepared expressions state middle pe floatEmpty headExecuted
          have tailFrame := executeIntegerProducerLineAtPEs_peRegisters_not_mem expressions rest
            middle next executed
            (fun pe other s n he different =>
              (executeIntegerProducerLineAtPE_peFields_other expressions s n pe other different he).1)
            pe peNotRest
          refine ⟨writes, slots, bars, prep, ?_⟩
          rw [tailFrame, committed]
        · have pMem : p ∈ rest := by
            rcases List.mem_cons.mp mem with h | h
            · exact False.elim (same h)
            · exact h
          obtain ⟨writes, slots, bars, prep, committed⟩ := ih middle executed restNodup pMem
          obtain ⟨hregs, hforwarding, hvalid, hcontext⟩ :=
            executeIntegerProducerLineAtPE_peFields_other expressions state middle pe p same headExecuted
          obtain ⟨_, _, _, _, _, _, _, _, _, _, hmatrix, hmask, hclock⟩ :=
            executeIntegerProducerLineAtPE_sameOther expressions state middle pe headExecuted
          have prepState : welcomeIntegerPrep state p expressions = .ok (writes, slots, bars) := by
            rw [← welcomeIntegerPrep_congr expressions p hregs hforwarding hvalid hmatrix.symm hmask.symm
              hcontext hclock.symm]
            exact prep
          exact ⟨writes, slots, bars, prepState, by rw [committed, hregs]⟩

theorem plain_l1Predicates (expression : ParsedExpr)
    (plain : parsedExprIsPlainIntegerALU expression = true) :
    parsedExprIsL1MwriteProducer expression = false ∧
      parsedExprIsL1GatherProducer expression = false ∧
      parsedExprIsL1ReduceProducer expression = false := by
  cases expression with
  | mk op sources destinations flush text =>
    cases op <;>
      simp_all [parsedExprIsPlainIntegerALU, parsedExprIsIntegerProducer,
        parsedExprIsL1MwriteProducer, parsedExprIsL1GatherProducer,
        parsedExprIsL1ReduceProducer]

theorem plain_stageFilter_eq_self (expressions : List ParsedExpr)
    (plain : expressions.all parsedExprIsPlainIntegerALU = true) :
    expressions.filter (fun expression =>
      !parsedExprIsL2BMProducer expression && !parsedExprIsMatrixWriteProducer expression &&
        !parsedExprIsL1MwriteProducer expression && !parsedExprIsL1GatherProducer expression &&
        !parsedExprIsL1ReduceProducer expression && !parsedExprIsL1ToPEProducer expression &&
        !parsedExprIsMatrixMAUProducer expression &&
        !parsedExprIsSupportedFloatMAUProducer expression &&
        !parsedExprIsMslMsrProducer expression && !parsedExprIsBlockFloatProducer expression &&
        !parsedExprIsFloatReluProducer expression) = expressions := by
  apply List.filter_eq_self.mpr
  intro expression member
  have facts := parsedExprIsPlainIntegerALU_facts expression (List.all_eq_true.mp plain expression member)
  obtain ⟨producer, unsupported, msl, relu, block, supported, waitTag, mmau, mwrite,
    l1tope, l2bm, nofwd, turn⟩ := facts
  have floatMau := parsedExprIsPlainIntegerALU_notFloatMAU expression
    (List.all_eq_true.mp plain expression member)
  obtain ⟨l1mwrite, l1gather, l1reduce⟩ := plain_l1Predicates expression
    (List.all_eq_true.mp plain expression member)
  simp [msl, relu, block, mmau, mwrite, l1tope, l2bm, floatMau, l1mwrite, l1gather, l1reduce]

theorem plain_peFilter_eq_self (expressions : List ParsedExpr)
    (plain : expressions.all parsedExprIsPlainIntegerALU = true) :
    expressions.filter (fun expression =>
      !parsedExprIsL2BMProducer expression && !parsedExprIsMslMsrProducer expression &&
        !parsedExprIsMatrixMAUProducer expression &&
        !parsedExprIsBlockFloatProducer expression &&
        !parsedExprIsFloatReluProducer expression) = expressions := by
  apply List.filter_eq_self.mpr
  intro expression member
  have facts := parsedExprIsPlainIntegerALU_facts expression (List.all_eq_true.mp plain expression member)
  obtain ⟨producer, unsupported, msl, relu, block, supported, waitTag, mmau, mwrite,
    l1tope, l2bm, nofwd, turn⟩ := facts
  simp [msl, relu, block, mmau, l2bm]

theorem plain_floatFilter_eq_nil (expressions : List ParsedExpr)
    (plain : expressions.all parsedExprIsPlainIntegerALU = true) :
    expressions.filter parsedExprIsSupportedFloatMAUProducer = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro expression member
  rw [parsedExprIsPlainIntegerALU_notFloatMAU expression
    (List.all_eq_true.mp plain expression member)]
  simp

theorem welcomeSealed_pe_prepared
    (expressions : List NormalizedExpr) (state : State) {next : State}
    (accepted : checkParsedTopLine (InstructionLine.pe expressions).toParsed = true)
    (plain : (expressions.map NormalizedExpr.toParsed).all
      parsedExprIsPlainIntegerALU = true)
    (step : welcomeSealedMachine.step (.pe expressions) state = some next) :
    ∃ writes slots bars,
      welcomeIntegerPrep state welcomePE (expressions.map NormalizedExpr.toParsed)
        = .ok (writes, slots, bars) ∧
      next.peRegisters welcomePE =
        commitParsedMaskedWrites (state.peRegisters welcomePE) writes := by
  have executed := welcomeSealed_step_ok step
  simp only [executeNormalizedLine, NormalizedLine.toInstruction?] at executed
  obtain ⟨nextPEs, walkExecuted, nextEq⟩ :=
    executeIntegerProducerInstructionLine_pe_plainIntegerALU_exists expressions state next
      accepted plain executed
  have filteredEq := plain_peFilter_eq_self (expressions.map NormalizedExpr.toParsed) plain
  rw [filteredEq] at walkExecuted
  have floatEmpty := plain_floatFilter_eq_nil (expressions.map NormalizedExpr.toParsed) plain
  obtain ⟨writes, slots, bars, prep, committed⟩ :=
    executeIntegerProducerLineAtPEs_prepared (expressions.map NormalizedExpr.toParsed)
      (List.finRange 4096) state nextPEs floatEmpty walkExecuted
      (List.nodup_finRange 4096) welcomePE (List.mem_finRange welcomePE)
  refine ⟨writes, slots, bars, prep, ?_⟩
  rw [nextEq]
  simpa using committed

/-- Positional form of `List.mapM`. -/
theorem list_mapM_getElem {α β : Type} (f : α → Option β) :
    ∀ (l : List α) (out : List β), l.mapM f = some out →
      out.length = l.length ∧
        ∀ (k : Nat) (hk : k < out.length) (hk' : k < l.length),
          f (l[k]'hk') = some (out[k]'hk) := by
  intro l
  induction l with
  | nil =>
      intro out mapped
      simp only [List.mapM_nil] at mapped
      cases mapped
      exact ⟨rfl, by intro k hk; simp at hk⟩
  | cons a rest ih =>
      intro out mapped
      simp only [List.mapM_cons] at mapped
      cases head : f a with
      | none => simp [head] at mapped
      | some b =>
          cases tail : rest.mapM f with
          | none => simp [head, tail] at mapped
          | some restOut =>
              simp only [head, tail, Option.some.injEq] at mapped
              injection mapped with mapped
              subst mapped
              obtain ⟨lenEq, getEq⟩ := ih restOut tail
              refine ⟨by simp [lenEq], ?_⟩
              intro k hk hk'
              cases k with
              | zero => simpa [head] using head
              | succ k =>
                  have hkOut : k < restOut.length := by simpa using hk
                  have hkRest : k < rest.length := by simpa using hk'
                  have := getEq k hkOut hkRest
                  simpa [List.getElem_cons_succ] using this

def ParsedOperand.isLm1MemoryDestination : ParsedOperand → Bool
  | .mem access _ _ _ _ => access.bank == Issue.Bank.lm1
  | _ => false

def ParsedOperand.bankList : List ParsedOperand → List Issue.Bank
  | [] => []
  | .mem access _ _ _ _ :: rest => access.bank :: ParsedOperand.bankList rest
  | _ :: rest => ParsedOperand.bankList rest

theorem accesses_map_bank_eq_bankList (destinations : List ParsedOperand) :
    (ParsedOperand.accesses destinations).map Issue.Access.bank =
      ParsedOperand.bankList destinations := by
  induction destinations with
  | nil => rfl
  | cons d rest ih =>
      cases d with
      | mem access neg ext rnd mask =>
          show access.bank :: (ParsedOperand.accesses rest).map Issue.Access.bank =
            access.bank :: ParsedOperand.bankList rest
          rw [ih]
      | bar lm1 width mask => exact ih
      | forward kind neg ext rnd => exact ih
      | fixed kind => exact ih
      | omr entry mask => exact ih
      | matrix y width row => exact ih
      | nowrite => exact ih
      | l1bm width address => exact ih
      | l2bm address l2b => exact ih
      | dar address => exact ih

theorem filter_isLm1_length_bankList (destinations : List ParsedOperand) :
    (destinations.filter ParsedOperand.isLm1MemoryDestination).length =
      (ParsedOperand.bankList destinations).count Issue.Bank.lm1 := by
  induction destinations with
  | nil => rfl
  | cons d rest ih =>
      cases d with
      | mem access neg ext rnd mask =>
          simp only [List.filter_cons, ParsedOperand.isLm1MemoryDestination,
            ParsedOperand.bankList, List.count_cons, ih]
          split <;> simp_all <;> omega
      | bar lm1 width mask =>
          simp [ParsedOperand.isLm1MemoryDestination, ParsedOperand.bankList, ih]
      | forward kind neg ext rnd =>
          simp [ParsedOperand.isLm1MemoryDestination, ParsedOperand.bankList, ih]
      | fixed kind =>
          simp [ParsedOperand.isLm1MemoryDestination, ParsedOperand.bankList, ih]
      | omr entry mask =>
          simp [ParsedOperand.isLm1MemoryDestination, ParsedOperand.bankList, ih]
      | matrix y width row =>
          simp [ParsedOperand.isLm1MemoryDestination, ParsedOperand.bankList, ih]
      | nowrite =>
          simp [ParsedOperand.isLm1MemoryDestination, ParsedOperand.bankList, ih]
      | l1bm width address =>
          simp [ParsedOperand.isLm1MemoryDestination, ParsedOperand.bankList, ih]
      | l2bm address l2b =>
          simp [ParsedOperand.isLm1MemoryDestination, ParsedOperand.bankList, ih]
      | dar address =>
          simp [ParsedOperand.isLm1MemoryDestination, ParsedOperand.bankList, ih]

theorem filter_isLm1_length (destinations : List ParsedOperand) :
    (destinations.filter ParsedOperand.isLm1MemoryDestination).length =
      ((ParsedOperand.accesses destinations).map Issue.Access.bank).count Issue.Bank.lm1 := by
  rw [accesses_map_bank_eq_bankList]
  exact filter_isLm1_length_bankList destinations

theorem count_le_one_of_nodup {α : Type} [BEq α] [LawfulBEq α] :
    ∀ {l : List α}, l.Nodup → ∀ a : α, l.count a ≤ 1 := by
  intro l
  induction l with
  | nil => intro _ a; simp
  | cons b rest ih =>
      intro nodup a
      obtain ⟨notMem, restNodup⟩ := List.nodup_cons.mp nodup
      rw [List.count_cons]
      by_cases same : (b == a) = true
      · have bEqA : b = a := beq_iff_eq.mp same
        have countZero : rest.count a = 0 := List.count_eq_zero.mpr (by rwa [← bEqA])
        simp [same, countZero]
      · have sameFalse : (b == a) = false := by simpa using same
        have le := ih restNodup a
        simp [sameFalse]
        omega

theorem count_append_le_left {α : Type} [BEq α] (a : α) (l₁ l₂ : List α) :
    l₁.count a ≤ (l₁ ++ l₂).count a := by
  rw [List.count_append]
  omega

theorem two_positions_filter_count {α : Type} (p : α → Bool) (l : List α)
    (i j : Fin l.length) (different : i ≠ j)
    (pi : p (l[i]) = true) (pj : p (l[j]) = true) :
    2 ≤ (l.filter p).length := by
  induction l with
  | nil => exact i.elim0
  | cons a rest ih =>
      cases i with
      | mk iv hi =>
      cases j with
      | mk jv hj =>
      cases iv with
      | zero =>
        cases jv with
        | zero => exact absurd rfl different
        | succ jv =>
          have piA : p a = true := by simpa using pi
          have hj' : jv < rest.length := by simpa using hj
          have pjRest : p (rest[jv]'hj') = true := by simpa using pj
          have mem : rest[jv]'hj' ∈ rest.filter p :=
            List.mem_filter.mpr ⟨List.getElem_mem _, pjRest⟩
          have pos : 0 < (rest.filter p).length := List.length_pos_of_mem mem
          rw [List.filter_cons, if_pos piA]
          simp only [List.length_cons]
          omega
      | succ iv =>
        cases jv with
        | zero =>
          have pjA : p a = true := by simpa using pj
          have hi' : iv < rest.length := by simpa using hi
          have piRest : p (rest[iv]'hi') = true := by simpa using pi
          have mem : rest[iv]'hi' ∈ rest.filter p :=
            List.mem_filter.mpr ⟨List.getElem_mem _, piRest⟩
          have pos : 0 < (rest.filter p).length := List.length_pos_of_mem mem
          rw [List.filter_cons]
          split <;> simp only [List.length_cons] <;> omega
        | succ jv =>
          have hi' : iv < rest.length := by simpa using hi
          have hj' : jv < rest.length := by simpa using hj
          have piRest : p (rest[iv]'hi') = true := by simpa using pi
          have pjRest : p (rest[jv]'hj') = true := by simpa using pj
          have different' : (⟨iv, hi'⟩ : Fin rest.length) ≠ ⟨jv, hj'⟩ := by
            intro same
            apply different
            simp only [Fin.ext_iff] at same ⊢
            omega
          have hrec := ih ⟨iv, hi'⟩ ⟨jv, hj'⟩ different' piRest pjRest
          rw [List.filter_cons]
          split
          · simp only [List.length_cons]; omega
          · exact le_trans hrec (by simp)

theorem writeBanks_eq_bankList (e : ParsedExpr) (id : Nat) :
    (e.toIssueExpr id).writeBanks =
      ParsedOperand.bankList e.destinations ++ ParsedExpr.barWrites e := by
  show (ParsedOperand.accesses e.destinations).map Issue.Access.bank ++
      ParsedExpr.barWrites e = _
  rw [accesses_map_bank_eq_bankList]

theorem lm1Destinations_count_le_one (e : ParsedExpr) (id : Nat)
    (nodup : (e.toIssueExpr id).writeBanks.Nodup) :
    (e.destinations.filter ParsedOperand.isLm1MemoryDestination).length ≤ 1 := by
  have total := count_le_one_of_nodup nodup Issue.Bank.lm1
  rw [writeBanks_eq_bankList] at total
  have part := count_append_le_left Issue.Bank.lm1
    (ParsedOperand.bankList e.destinations) e.barWrites
  rw [filter_isLm1_length, accesses_map_bank_eq_bankList]
  omega

theorem directDestinationBankWidth_isLm1 (d : ParsedOperand) (w : PEMemory.Width)
    (h : ParsedOperand.directDestinationBankWidth? d = some (PEMemory.Bank.lm1, w)) :
    ParsedOperand.isLm1MemoryDestination d = true := by
  cases d with
  | mem access neg ext rnd mask =>
      simp only [ParsedOperand.directDestinationBankWidth?] at h
      split at h
      · simp at h
      · rename_i hguard
        cases hb : issueBankToRegisterBank access.bank with
        | none => simp [hb] at h
        | some bank =>
            cases hw : parsedWidth? access.region.width with
            | none => simp [hb, hw] at h
            | some width =>
                simp only [hb, hw] at h
                split at h
                · simp at h
                · simp only [Option.some.injEq, Prod.mk.injEq] at h
                  obtain ⟨bankEq, _⟩ := h
                  have bankLm1 : access.bank = Issue.Bank.lm1 := by
                    rw [bankEq] at hb
                    cases access with
                    | mk accessBank region =>
                        cases accessBank <;> simp_all [issueBankToRegisterBank]
                  simp [ParsedOperand.isLm1MemoryDestination, bankLm1]
  | bar _ _ _ => simp [ParsedOperand.directDestinationBankWidth?] at h
  | forward _ _ _ _ => simp [ParsedOperand.directDestinationBankWidth?] at h
  | fixed _ => simp [ParsedOperand.directDestinationBankWidth?] at h
  | omr _ _ => simp [ParsedOperand.directDestinationBankWidth?] at h
  | matrix _ _ _ => simp [ParsedOperand.directDestinationBankWidth?] at h
  | nowrite => simp [ParsedOperand.directDestinationBankWidth?] at h
  | l1bm _ _ => simp [ParsedOperand.directDestinationBankWidth?] at h
  | l2bm _ _ => simp [ParsedOperand.directDestinationBankWidth?] at h
  | dar _ => simp [ParsedOperand.directDestinationBankWidth?] at h

theorem lm1Destinations_unique_positions (e : ParsedExpr) (id : Nat)
    (nodup : (e.toIssueExpr id).writeBanks.Nodup)
    (i j : Fin e.destinations.length) (wi wj : PEMemory.Width)
    (hi : ParsedOperand.directDestinationBankWidth? (e.destinations[i]) =
      some (PEMemory.Bank.lm1, wi))
    (hj : ParsedOperand.directDestinationBankWidth? (e.destinations[j]) =
      some (PEMemory.Bank.lm1, wj)) :
    i = j := by
  by_contra different
  have countBound := lm1Destinations_count_le_one e id nodup
  have two := two_positions_filter_count ParsedOperand.isLm1MemoryDestination
    e.destinations i j different
    (directDestinationBankWidth_isLm1 _ _ hi)
    (directDestinationBankWidth_isLm1 _ _ hj)
  omega


/-- Positional form of `toDirectMaskedConstantDestinations?`. -/
theorem constantDestinations_getElem
    (expression : ParsedExpr) (registers : ProofsLean.MNCore.Masks.RegisterFile)
    (directive : ParsedMaskDirective) (hasSingleLineMask : Bool)
    (group : Fin 4) (l2b : Fin 2) (l1b : Fin 8) (mab : Fin 16)
    (pe cycle : Fin 4) (bar0 bar1 : BitVec 12) (tWord : BitVec 32) :
    ∀ (destinations : List ParsedOperand) (targets : List ParsedConstantDestination),
      ParsedExpr.toDirectMaskedConstantDestinations? expression registers directive
          hasSingleLineMask group l2b l1b mab pe cycle bar0 bar1 tWord destinations =
        some targets →
      targets.length = destinations.length ∧
        ∀ (k : Nat) (hk : k < targets.length) (hk' : k < destinations.length),
          ParsedExpr.toDirectMaskedConstantDestination? expression registers directive
              hasSingleLineMask group l2b l1b mab pe cycle bar0 bar1 tWord
              (destinations[k]'hk') = some (targets[k]'hk) := by
  intro destinations
  induction destinations with
  | nil =>
      intro targets mapped
      simp only [ParsedExpr.toDirectMaskedConstantDestinations?] at mapped
      cases mapped
      exact ⟨rfl, by intro k hk; simp at hk⟩
  | cons d rest ih =>
      intro targets mapped
      simp only [ParsedExpr.toDirectMaskedConstantDestinations?] at mapped
      cases head : ParsedExpr.toDirectMaskedConstantDestination? expression registers
        directive hasSingleLineMask group l2b l1b mab pe cycle bar0 bar1 tWord d with
      | none => simp [head] at mapped
      | some first =>
          cases tail : ParsedExpr.toDirectMaskedConstantDestinations? expression registers
            directive hasSingleLineMask group l2b l1b mab pe cycle bar0 bar1 tWord rest with
          | none => simp [head, tail] at mapped
          | some restTargets =>
              simp only [head, tail, Option.some.injEq] at mapped
              injection mapped with mapped
              subst mapped
              obtain ⟨lenEq, getEq⟩ := ih restTargets tail
              refine ⟨by simp [lenEq], ?_⟩
              intro k hk hkDest
              cases k with
              | zero => simpa using head
              | succ k =>
                  have hk' : k < restTargets.length := by simpa using hk
                  have hkDest' : k < rest.length := by
                    rw [← lenEq]; exact hk'
                  simpa [List.getElem_cons_succ] using getEq k hk' hkDest'

/-- Membership form of `List.mapM`. -/
theorem list_mapM_mem {α β : Type} (f : α → Option β) :
    ∀ (l : List α) (out : List β), l.mapM f = some out →
      ∀ b ∈ out, ∃ a ∈ l, f a = some b := by
  intro l
  induction l with
  | nil =>
      intro out mapped b member
      simp only [List.mapM_nil] at mapped
      cases mapped
      simp at member
  | cons a rest ih =>
      intro out mapped b member
      simp only [List.mapM_cons] at mapped
      cases hd : f a with
      | none => simp [hd] at mapped
      | some head =>
          cases ht : rest.mapM f with
          | none => simp [hd, ht] at mapped
          | some tail =>
              simp only [hd, ht, Option.some.injEq] at mapped
              injection mapped with mapped
              subst mapped
              simp only [List.mem_cons] at member
              rcases member with same | later
              · exact ⟨a, by simp, by rw [same]; exact hd⟩
              · obtain ⟨a', member', mapped'⟩ := ih tail ht b later
                exact ⟨a', List.mem_cons_of_mem _ member', mapped'⟩

/-- The multiple-destination lowering's accesses resolve destination operands of
the row. -/
theorem toDirectMaskedIntegerWritesInLine?_mem_provenance
    (expression : ParsedExpr) (registers : ProofsLean.MNCore.Masks.RegisterFile)
    (directive : ParsedMaskDirective) (hasSingleLineMask : Bool)
    (group : Fin 4) (l2b : Fin 2) (l1b : Fin 8) (mab : Fin 16)
    (pe cycle : Fin 4) (bar0 bar1 : BitVec 12) (tWord : BitVec 32)
    (accesses : List ParsedMaskedIntegerAccesses)
    (lowered : ParsedExpr.toDirectMaskedIntegerWritesInLine? expression registers directive
      hasSingleLineMask group l2b l1b mab pe cycle bar0 bar1 tWord = some accesses) :
    ∀ access ∈ accesses, ∃ destination ∈ expression.destinations,
      ParsedOperand.toDirectMemoryDestination? destination pe cycle bar0 bar1 tWord =
        some access.destination := by
  intro access member
  unfold ParsedExpr.toDirectMaskedIntegerWritesInLine? at lowered
  split at lowered
  · obtain ⟨destination, destinationMem, loweredHere⟩ :=
      list_mapM_mem _ expression.destinations accesses lowered access member
    obtain ⟨resolved, resolvedMem, resolvedEq⟩ :=
      ParsedExpr.toDirectMaskedIntegerAccessesInLine?_destination_provenance
        { op := expression.op, sources := expression.sources,
          destinations := [destination], flush := expression.flush, text := expression.text }
        registers directive hasSingleLineMask group l2b l1b mab pe cycle bar0 bar1 tWord
        access loweredHere
    simp only [List.mem_singleton] at resolvedMem
    subst resolved
    exact ⟨destination, destinationMem, resolvedEq⟩
  · simp at lowered

/-- Every constant target comes from a destination operand of the row. -/
theorem toDirectMaskedConstantWrites?_mem_provenance
    (expression : ParsedExpr) (registers : ProofsLean.MNCore.Masks.RegisterFile)
    (directive : ParsedMaskDirective) (hasSingleLineMask : Bool)
    (group : Fin 4) (l2b : Fin 2) (l1b : Fin 8) (mab : Fin 16)
    (pe cycle : Fin 4) (bar0 bar1 : BitVec 12) (tWord : BitVec 32)
    (targets : List ParsedConstantDestination)
    (lowered : ParsedExpr.toDirectMaskedConstantWrites? expression registers directive
      hasSingleLineMask group l2b l1b mab pe cycle bar0 bar1 tWord = some targets) :
    ∀ target ∈ targets, ∃ destination ∈ expression.destinations,
      ParsedExpr.toDirectMaskedConstantDestination? expression registers directive
        hasSingleLineMask group l2b l1b mab pe cycle bar0 bar1 tWord destination =
          some target := by
  intro target member
  cases expression with
  | mk op sources destinations flush text =>
    cases op with
    | zero =>
        have destinationsLowered : ParsedExpr.toDirectMaskedConstantDestinations?
            { op := .zero, sources := sources, destinations := destinations, flush := flush,
              text := text } registers directive hasSingleLineMask group l2b l1b mab pe cycle
            bar0 bar1 tWord destinations = some targets := by
          simpa [ParsedExpr.toDirectMaskedConstantWrites?] using lowered
        obtain ⟨lenEq, getTarget⟩ := constantDestinations_getElem
          { op := .zero, sources := sources, destinations := destinations, flush := flush,
            text := text } registers directive hasSingleLineMask group l2b l1b mab pe cycle
          bar0 bar1 tWord destinations targets destinationsLowered
        obtain ⟨k, hk, targetEq⟩ := List.mem_iff_getElem.mp member
        subst targetEq
        have hkDest : k < destinations.length := by rw [← lenEq]; exact hk
        exact ⟨destinations[k]'hkDest, List.getElem_mem hkDest, getTarget k hk hkDest⟩
    | immediate payload sparse =>
        have destinationsLowered : ParsedExpr.toDirectMaskedConstantDestinations?
            { op := .immediate payload sparse, sources := sources,
              destinations := destinations, flush := flush, text := text }
            registers directive hasSingleLineMask group l2b l1b mab pe cycle bar0 bar1 tWord
            destinations = some targets := by
          simpa [ParsedExpr.toDirectMaskedConstantWrites?] using lowered
        obtain ⟨lenEq, getTarget⟩ := constantDestinations_getElem
          { op := .immediate payload sparse, sources := sources,
            destinations := destinations, flush := flush, text := text }
          registers directive hasSingleLineMask group l2b l1b mab pe cycle bar0 bar1 tWord
          destinations targets destinationsLowered
        obtain ⟨k, hk, targetEq⟩ := List.mem_iff_getElem.mp member
        subst targetEq
        have hkDest : k < destinations.length := by rw [← lenEq]; exact hk
        exact ⟨destinations[k]'hkDest, List.getElem_mem hkDest, getTarget k hk hkDest⟩
    | alu name precision unsigned arg =>
        simp [ParsedExpr.toDirectMaskedConstantWrites?] at lowered
    | mau precision matrix kind half round =>
        simp [ParsedExpr.toDirectMaskedConstantWrites?] at lowered
    | matrixWrite precision =>
        simp [ParsedExpr.toDirectMaskedConstantWrites?] at lowered
    | matrixRead precision =>
        simp [ParsedExpr.toDirectMaskedConstantWrites?] at lowered
    | wait tag =>
        simp [ParsedExpr.toDirectMaskedConstantWrites?] at lowered
    | noforward =>
        simp [ParsedExpr.toDirectMaskedConstantWrites?] at lowered
    | l1bm operation =>
        simp [ParsedExpr.toDirectMaskedConstantWrites?] at lowered
    | l2bm operation =>
        simp [ParsedExpr.toDirectMaskedConstantWrites?] at lowered

theorem mapM_lm1_count_le {α : Type} (f : α → Option ParsedMaskedIntegerAccesses)
    (p : α → Bool)
    (sound : ∀ x a, f x = some a → a.destination.bank = PEMemory.Bank.lm1 → p x = true) :
    ∀ (l : List α) (out : List ParsedMaskedIntegerAccesses), l.mapM f = some out →
      (out.filter (fun a => a.destination.bank == PEMemory.Bank.lm1)).length ≤
        (l.filter p).length := by
  intro l
  induction l with
  | nil =>
      intro out mapped
      simp only [List.mapM_nil] at mapped
      cases mapped
      simp
  | cons x rest ih =>
      intro out mapped
      simp only [List.mapM_cons] at mapped
      cases hd : f x with
      | none => simp [hd] at mapped
      | some head =>
          cases ht : rest.mapM f with
          | none => simp [hd, ht] at mapped
          | some tail =>
              simp only [hd, ht, Option.some.injEq] at mapped
              injection mapped with mapped
              subst mapped
              have ihle := ih tail ht
              rw [List.filter_cons, List.filter_cons]
              by_cases isLm1 : head.destination.bank = PEMemory.Bank.lm1
              · have px : p x = true := sound x head hd isLm1
                rw [if_pos px]
                have hif : (head.destination.bank == PEMemory.Bank.lm1) = true := by simp [isLm1]
                rw [if_pos hif]
                simp only [List.length_cons]
                omega
              · have hif : (head.destination.bank == PEMemory.Bank.lm1) = false := by simp [isLm1]
                rw [if_neg (by rw [hif]; simp)]
                by_cases px : p x = true
                · rw [if_pos px]
                  simp only [List.length_cons]
                  omega
                · rw [if_neg px]
                  omega

def ParsedConstantDestination.isLm1Target : ParsedConstantDestination → Bool
  | .memory accesses => accesses.destination.bank == PEMemory.Bank.lm1
  | _ => false

/-- A `.memory` constant target can only come from a non-`.nowrite`,
non-`.omr` destination. -/
theorem toDirectMaskedConstantDestination_memory_destination_guards
    (expression : ParsedExpr) (registers : ProofsLean.MNCore.Masks.RegisterFile)
    (directive : ParsedMaskDirective) (hasSingleLineMask : Bool)
    (group : Fin 4) (l2b : Fin 2) (l1b : Fin 8) (mab : Fin 16)
    (pe cycle : Fin 4) (bar0 bar1 : BitVec 12) (tWord : BitVec 32)
    (destination : ParsedOperand) (accesses : ParsedMaskedIntegerAccesses)
    (lowered : ParsedExpr.toDirectMaskedConstantDestination? expression registers directive
      hasSingleLineMask group l2b l1b mab pe cycle bar0 bar1 tWord destination =
        some (.memory accesses)) :
    destination ≠ .nowrite ∧ ∀ entry mask, destination ≠ .omr entry mask := by
  constructor
  · intro same
    rw [same] at lowered
    simp [ParsedExpr.toDirectMaskedConstantDestination?] at lowered
  · intro entry mask same
    rw [same] at lowered
    cases hEntry : ParsedOperand.toMaskRegisterEntry? (.omr entry mask)
    · simp [ParsedExpr.toDirectMaskedConstantDestination?, hEntry] at lowered
    · cases hSel : ParsedOperand.resolveOmrWriteSelection? (.omr entry mask) registers cycle
          directive hasSingleLineMask
      · simp [ParsedExpr.toDirectMaskedConstantDestination?, hEntry, hSel] at lowered
      · simp [ParsedExpr.toDirectMaskedConstantDestination?, hEntry, hSel] at lowered

theorem toDirectMaskedConstantDestination_memory_provenance
    (expression : ParsedExpr) (registers : ProofsLean.MNCore.Masks.RegisterFile)
    (directive : ParsedMaskDirective) (hasSingleLineMask : Bool)
    (group : Fin 4) (l2b : Fin 2) (l1b : Fin 8) (mab : Fin 16)
    (pe cycle : Fin 4) (bar0 bar1 : BitVec 12) (tWord : BitVec 32)
    (destination : ParsedOperand) (accesses : ParsedMaskedIntegerAccesses)
    (lowered : ParsedExpr.toDirectMaskedConstantDestination? expression registers directive
      hasSingleLineMask group l2b l1b mab pe cycle bar0 bar1 tWord destination =
        some (.memory accesses)) :
    ∃ d ∈ [destination],
      ParsedOperand.toDirectMemoryDestination? d pe cycle bar0 bar1 tWord =
        some accesses.destination := by
  obtain ⟨notNowrite, notOmr⟩ :=
    toDirectMaskedConstantDestination_memory_destination_guards expression registers directive
      hasSingleLineMask group l2b l1b mab pe cycle bar0 bar1 tWord destination accesses lowered
  rw [toDirectMaskedConstantDestination?_eq_bind expression registers directive hasSingleLineMask
    group l2b l1b mab pe cycle bar0 bar1 tWord destination notNowrite notOmr] at lowered
  cases h : ParsedExpr.toDirectMaskedIntegerAccessesInLine?
      { op := expression.op, sources := expression.sources,
        destinations := [destination], flush := expression.flush, text := expression.text }
      registers directive hasSingleLineMask group l2b l1b mab pe cycle bar0 bar1 tWord
  · simp [h] at lowered
  · rename_i val
    simp only [h, Option.bind, Option.some.injEq] at lowered
    injection lowered with sameAccess
    subst accesses
    obtain ⟨d, dMem, dEq⟩ :=
      ParsedExpr.toDirectMaskedIntegerAccessesInLine?_destination_provenance
        { op := expression.op, sources := expression.sources,
          destinations := [destination], flush := expression.flush, text := expression.text }
        registers directive hasSingleLineMask group l2b l1b mab pe cycle bar0 bar1 tWord
        val h
    exact ⟨d, dMem, dEq⟩

theorem toDirectMaskedConstantDestination_isLm1
    (expression : ParsedExpr) (registers : ProofsLean.MNCore.Masks.RegisterFile)
    (directive : ParsedMaskDirective) (hasSingleLineMask : Bool)
    (group : Fin 4) (l2b : Fin 2) (l1b : Fin 8) (mab : Fin 16)
    (pe cycle : Fin 4) (bar0 bar1 : BitVec 12) (tWord : BitVec 32)
    (destination : ParsedOperand) (target : ParsedConstantDestination)
    (lowered : ParsedExpr.toDirectMaskedConstantDestination? expression registers directive
      hasSingleLineMask group l2b l1b mab pe cycle bar0 bar1 tWord destination = some target)
    (isLm1 : ParsedConstantDestination.isLm1Target target = true) :
    ParsedOperand.isLm1MemoryDestination destination = true := by
  cases target with
  | memory accesses =>
      have hmem : (accesses.destination.bank == PEMemory.Bank.lm1) = true := isLm1
      have bankEq : accesses.destination.bank = PEMemory.Bank.lm1 := by
        simpa using hmem
      obtain ⟨d, dMem, dEq⟩ :=
        toDirectMaskedConstantDestination_memory_provenance expression registers directive
          hasSingleLineMask group l2b l1b mab pe cycle bar0 bar1 tWord destination accesses
          lowered
      simp only [List.mem_singleton] at dMem
      subst d
      have static := ParsedOperand.toDirectMemoryDestination?_bankWidth destination pe cycle
        bar0 bar1 tWord
      rw [dEq] at static
      simp only [Option.map_some] at static
      have pair : ParsedOperand.directDestinationBankWidth? destination =
          some (PEMemory.Bank.lm1, accesses.destination.width) := by
        rw [← static, bankEq]
      exact directDestinationBankWidth_isLm1 _ _ pair
  | maskRegister entry => simp [ParsedConstantDestination.isLm1Target] at isLm1
  | noWrite => simp [ParsedConstantDestination.isLm1Target] at isLm1

theorem constantTargets_lm1_count_le
    (expression : ParsedExpr) (registers : ProofsLean.MNCore.Masks.RegisterFile)
    (directive : ParsedMaskDirective) (hasSingleLineMask : Bool)
    (group : Fin 4) (l2b : Fin 2) (l1b : Fin 8) (mab : Fin 16)
    (pe cycle : Fin 4) (bar0 bar1 : BitVec 12) (tWord : BitVec 32) :
    ∀ (destinations : List ParsedOperand) (targets : List ParsedConstantDestination),
      ParsedExpr.toDirectMaskedConstantDestinations? expression registers directive
          hasSingleLineMask group l2b l1b mab pe cycle bar0 bar1 tWord destinations =
        some targets →
      (targets.filter (fun target => ParsedConstantDestination.isLm1Target target)).length ≤
        (destinations.filter ParsedOperand.isLm1MemoryDestination).length := by
  intro destinations
  induction destinations with
  | nil =>
      intro targets mapped
      simp only [ParsedExpr.toDirectMaskedConstantDestinations?] at mapped
      cases mapped
      simp
  | cons d rest ih =>
      intro targets mapped
      simp only [ParsedExpr.toDirectMaskedConstantDestinations?] at mapped
      cases head : ParsedExpr.toDirectMaskedConstantDestination? expression registers directive
        hasSingleLineMask group l2b l1b mab pe cycle bar0 bar1 tWord d with
      | none => simp [head] at mapped
      | some first =>
          cases tail : ParsedExpr.toDirectMaskedConstantDestinations? expression registers
            directive hasSingleLineMask group l2b l1b mab pe cycle bar0 bar1 tWord rest with
          | none => simp [head, tail] at mapped
          | some restTargets =>
              simp only [head, tail, Option.some.injEq] at mapped
              injection mapped with mapped
              subst mapped
              have ihle := ih restTargets tail
              rw [List.filter_cons, List.filter_cons]
              by_cases isLm1 : ParsedConstantDestination.isLm1Target first = true
              · rw [if_pos isLm1]
                have isLm1D :=
                  toDirectMaskedConstantDestination_isLm1 expression registers directive
                    hasSingleLineMask group l2b l1b mab pe cycle bar0 bar1 tWord d first head
                    isLm1
                rw [if_pos isLm1D]
                simp only [List.length_cons]
                omega
              · rw [if_neg isLm1]
                by_cases isLm1D : ParsedOperand.isLm1MemoryDestination d = true
                · rw [if_pos isLm1D]
                  simp only [List.length_cons]
                  omega
                · rw [if_neg isLm1D]
                  omega

def PreparedParsedMaskedWrite.isLm1Write (write : PreparedParsedMaskedWrite) : Bool :=
  match write.destination with
  | some access => access.bank == PEMemory.Bank.lm1
  | none => false

theorem lm1Windows_length_eq_count (writes : List PreparedParsedMaskedWrite) :
    (lm1WindowsOfWrites writes).length =
      (writes.filter PreparedParsedMaskedWrite.isLm1Write).length := by
  induction writes with
  | nil => rfl
  | cons write rest ih =>
      cases hdest : write.destination with
      | none =>
          simp [lm1WindowsOfWrites, PreparedParsedMaskedWrite.isLm1Write, hdest, ih]
      | some access =>
          cases access with
          | mk bank width address =>
              cases bank <;>
                simp [lm1WindowsOfWrites, PreparedParsedMaskedWrite.isLm1Write, hdest, ih]



/-- A plain integer-ALU row passes the integer/matrix-read stage filter. -/
theorem plain_stageInput (expression : ParsedExpr)
    (plain : parsedExprIsPlainIntegerALU expression = true) :
    parsedExprIsIntegerMatrixReadStageInput expression = true := by
  have facts := parsedExprIsPlainIntegerALU_facts expression plain
  obtain ⟨producer, unsupported, msl, relu, block, supported, waitTag, mmau, mwrite,
    l1tope, l2bm, nofwd, turn⟩ := facts
  cases expression with
  | mk op sources destinations flush text =>
    cases op <;>
      simp_all [parsedExprIsIntegerMatrixReadStageInput, parsedExprWaitTag?,
        parsedExprIsL2BMProducer, parsedExprIsMatrixWriteProducer,
        parsedExprIsL1MwriteProducer, parsedExprIsL1GatherProducer,
        parsedExprIsL1ReduceProducer, parsedExprIsL1ToPEProducer,
        parsedExprIsMatrixMAUProducer, parsedExprIsSupportedFloatMAUProducer,
        parsedExprIsMslMsrProducer, parsedExprIsBlockFloatProducer,
        parsedExprIsFloatReluProducer, parsedExprIsPlainIntegerALU,
        parsedExprIsIntegerProducer]

theorem plain_single_expression (expressions : List NormalizedExpr)
    (unrefuted : WelcomePEUnrefuted expressions)
    (plain : (expressions.map NormalizedExpr.toParsed).all
      parsedExprIsPlainIntegerALU = true) :
    ∃ e : NormalizedExpr, expressions = [e] ∧
      parsedExprIsPlainIntegerALU e.toParsed = true := by
  have legal := welcomePEUnrefuted_legal expressions unrefuted
  have lengthLe := plain_legal_length_le_one expressions legal plain
  have nonempty : expressions ≠ [] := by
    intro empty
    apply unrefuted.2.1
    intro expression member
    rw [empty] at member
    simp at member
  have lengthEq : expressions.length = 1 := by
    rcases Nat.eq_zero_or_pos expressions.length with zero | pos
    · exact absurd (List.length_eq_zero_iff.mp zero) nonempty
    · omega
  obtain ⟨e, same⟩ := List.length_eq_one_iff.mp lengthEq
  refine ⟨e, same, ?_⟩
  have all := List.all_eq_true.mp plain
  apply all
  rw [same]
  simp

theorem prepareParsedMaskedConstantWrites_eq_of_shape
    (filesA filesB : IntegerRegisterFiles) (cycle : Fin 4)
    (targets : List ParsedConstantDestination)
    (maskEq : filesA.maskRegisters = filesB.maskRegisters)
    (shape : ∀ target ∈ targets, ∀ accesses, target = .memory accesses →
      WelcomePEConstantOp accesses.op ∧
        ∃ ax ay rx ry, accesses.sourceX = .memory ax rx ∧
          accesses.sourceY = .memory ay ry) :
    prepareParsedMaskedConstantWrites filesA cycle targets =
      prepareParsedMaskedConstantWrites filesB cycle targets := by
  induction targets with
  | nil => rfl
  | cons target rest ih =>
      simp only [prepareParsedMaskedConstantWrites]
      cases target with
      | memory accesses =>
          have targetShape := shape (.memory accesses) (by simp) accesses rfl
          obtain ⟨ax, ay, rx, ry, sourceX, sourceY⟩ := targetShape.2
          have preparedEq : prepareParsedMaskedWrite filesA accesses false =
              prepareParsedMaskedWrite filesB accesses false :=
            prepareParsedMaskedWrite_eq_of_constant_memory filesA filesB accesses false
              targetShape.1 ax ay rx ry sourceX sourceY
          have targetEq : prepareParsedConstantTarget filesA cycle
                (.memory accesses) =
              prepareParsedConstantTarget filesB cycle (.memory accesses) := preparedEq
          rw [targetEq]
          rw [ih (fun target member => shape target (List.mem_cons_of_mem _ member))]
      | maskRegister entry =>
          unfold prepareParsedConstantTarget
          rw [ih (fun target member => shape target (List.mem_cons_of_mem _ member))]
      | noWrite =>
          unfold prepareParsedConstantTarget
          rw [ih (fun target member => shape target (List.mem_cons_of_mem _ member))]

theorem prepareParsedIntegerALUExprCycle_constant_eq
    (filesA filesB : IntegerRegisterFiles)
    (oldSlots nextSlots : ProofsLean.MNCore.Forwarding.Slots)
    (expression : ParsedExpr) (control : ParsedMaskExecutionControl)
    (hasSingleLineMask noForward reduced : Bool) (cycle : Fin 4)
    (constant : expression.op = .zero ∨
      ∃ payload sparse, expression.op = .immediate payload sparse)
    (maskEq : filesA.maskRegisters = filesB.maskRegisters) :
    prepareParsedIntegerALUExprCycle filesA oldSlots nextSlots expression control
        hasSingleLineMask noForward reduced cycle =
      prepareParsedIntegerALUExprCycle filesB oldSlots nextSlots expression control
        hasSingleLineMask noForward reduced cycle := by
  unfold prepareParsedIntegerALUExprCycle
  dsimp only
  rcases constant with isZero | ⟨payload, sparse, isImmediate⟩
  · rw [isZero]
    dsimp only
    rw [maskEq]
    cases h : ParsedExpr.toDirectMaskedConstantWrites? expression filesB.maskRegisters
        control.directive hasSingleLineMask control.context.group control.context.l2b
        control.context.l1b control.context.mab control.context.pe cycle
        control.context.bar0 control.context.bar1 control.context.tWord with
    | none => rfl
    | some targets =>
        simp only [h]
        have shape : ∀ target ∈ targets, ∀ accesses, target = .memory accesses →
            WelcomePEConstantOp accesses.op ∧
              ∃ ax ay rx ry, accesses.sourceX = .memory ax rx ∧
                accesses.sourceY = .memory ay ry := by
          intro target member accesses isMemory
          obtain ⟨destination, _, loweredDest⟩ :=
            toDirectMaskedConstantWrites?_mem_provenance expression
              filesB.maskRegisters control.directive hasSingleLineMask
              control.context.group control.context.l2b control.context.l1b
              control.context.mab control.context.pe cycle control.context.bar0
              control.context.bar1 control.context.tWord targets h target member
          exact toDirectMaskedConstantDestination?_shape expression filesB.maskRegisters
            control.directive hasSingleLineMask control.context.group control.context.l2b
            control.context.l1b control.context.mab control.context.pe cycle
            control.context.bar0 control.context.bar1 control.context.tWord
            (Or.inl isZero) destination target loweredDest accesses isMemory
        rw [prepareParsedMaskedConstantWrites_eq_of_shape filesA filesB cycle targets
          maskEq shape]
  · rw [isImmediate]
    dsimp only
    rw [maskEq]
    cases h : ParsedExpr.toDirectMaskedConstantWrites? expression filesB.maskRegisters
        control.directive hasSingleLineMask control.context.group control.context.l2b
        control.context.l1b control.context.mab control.context.pe cycle
        control.context.bar0 control.context.bar1 control.context.tWord with
    | none => rfl
    | some targets =>
        simp only [h]
        have shape : ∀ target ∈ targets, ∀ accesses, target = .memory accesses →
            WelcomePEConstantOp accesses.op ∧
              ∃ ax ay rx ry, accesses.sourceX = .memory ax rx ∧
                accesses.sourceY = .memory ay ry := by
          intro target member accesses isMemory
          obtain ⟨destination, _, loweredDest⟩ :=
            toDirectMaskedConstantWrites?_mem_provenance expression
              filesB.maskRegisters control.directive hasSingleLineMask
              control.context.group control.context.l2b control.context.l1b
              control.context.mab control.context.pe cycle control.context.bar0
              control.context.bar1 control.context.tWord targets h target member
          exact toDirectMaskedConstantDestination?_shape expression filesB.maskRegisters
            control.directive hasSingleLineMask control.context.group control.context.l2b
            control.context.l1b control.context.mab control.context.pe cycle
            control.context.bar0 control.context.bar1 control.context.tWord
            (Or.inr ⟨payload, sparse, isImmediate⟩) destination target loweredDest
            accesses isMemory
        rw [prepareParsedMaskedConstantWrites_eq_of_shape filesA filesB cycle targets
          maskEq shape]

theorem prepareParsedIntegerALUCycles_constant_eq
    (filesA filesB : IntegerRegisterFiles)
    (oldSlots : ProofsLean.MNCore.Forwarding.Slots)
    (expression : ParsedExpr) (control : ParsedMaskExecutionControl)
    (hasSingleLineMask noForward reduced : Bool)
    (constant : expression.op = .zero ∨
      ∃ payload sparse, expression.op = .immediate payload sparse)
    (maskEq : filesA.maskRegisters = filesB.maskRegisters) :
    ∀ (cycles : List (Fin 4)) (writes : List PreparedParsedMaskedWrite)
      (startSlots : ProofsLean.MNCore.Forwarding.Slots),
      prepareParsedIntegerALUCycles filesA oldSlots expression control hasSingleLineMask
          noForward reduced cycles writes startSlots =
        prepareParsedIntegerALUCycles filesB oldSlots expression control hasSingleLineMask
          noForward reduced cycles writes startSlots := by
  intro cycles
  induction cycles with
  | nil => intro writes startSlots; rfl
  | cons c rest ih =>
      intro writes startSlots
      simp only [prepareParsedIntegerALUCycles]
      rw [prepareParsedIntegerALUExprCycle_constant_eq filesA filesB oldSlots startSlots
        expression control hasSingleLineMask noForward reduced c constant maskEq]
      cases h : prepareParsedIntegerALUExprCycle filesB oldSlots startSlots expression control
          hasSingleLineMask noForward reduced c with
      | failure => rfl
      | unknown => rfl
      | ok result =>
          obtain ⟨cycleWrites, cycleSlots⟩ := result
          simp only [h]
          exact ih (writes ++ cycleWrites) cycleSlots

theorem prepareParsedIntegerALUExprCycles_constant_eq
    (filesA filesB : IntegerRegisterFiles)
    (oldSlots : ProofsLean.MNCore.Forwarding.Slots)
    (expression : ParsedExpr) (control : ParsedMaskExecutionControl)
    (hasSingleLineMask noForward reduced : Bool)
    (constant : expression.op = .zero ∨
      ∃ payload sparse, expression.op = .immediate payload sparse)
    (maskEq : filesA.maskRegisters = filesB.maskRegisters) :
    prepareParsedIntegerALUExprCycles filesA oldSlots oldSlots expression control
        hasSingleLineMask noForward reduced =
      prepareParsedIntegerALUExprCycles filesB oldSlots oldSlots expression control
        hasSingleLineMask noForward reduced :=
  prepareParsedIntegerALUCycles_constant_eq filesA filesB oldSlots expression control
    hasSingleLineMask noForward reduced constant maskEq parsedIntegerALUCycles [] oldSlots

theorem welcomeIntegerPrep_constant_eq
    (stateA stateB : State) (e : ParsedExpr)
    (plain : parsedExprIsPlainIntegerALU e = true)
    (constant : e.op = .zero ∨ ∃ payload sparse, e.op = .immediate payload sparse)
    (hfiles : (stateA.peRegisters welcomePE).maskRegisters =
      (stateB.peRegisters welcomePE).maskRegisters)
    (hslots : stateForwardingSlots stateA welcomePE =
      stateForwardingSlots stateB welcomePE)
    (hcontrol : parsedPEHazardControl stateA welcomePE =
      parsedPEHazardControl stateB welcomePE)
    (hstore : stateA.matrixRegisters = stateB.matrixRegisters) :
    welcomeIntegerPrep stateA welcomePE [e] =
      welcomeIntegerPrep stateB welcomePE [e] := by
  have filterEq : [e].filter parsedExprIsIntegerMatrixReadStageInput = [e] := by
    rw [List.filter_eq_self]
    intro x hx
    rw [List.mem_singleton] at hx
    subst x
    exact plain_stageInput e plain
  unfold welcomeIntegerPrep prepareParsedIntegerMatrixReadLineCycles
  rw [filterEq, hslots, hstore, hcontrol]
  have rowEq : prepareParsedIntegerMatrixReadLineExpression
        (stateA.peRegisters welcomePE) (stateForwardingSlots stateB welcomePE)
        (stateForwardingSlots stateB welcomePE)
        (stateB.matrixRegisters (ParsedIntegerContext.ofLinearIndex welcomePE).group
          (ParsedIntegerContext.ofLinearIndex welcomePE).l2b
          (ParsedIntegerContext.ofLinearIndex welcomePE).l1b)
        e (parsedPEHazardControl stateB welcomePE)
        ([e].any parsedExprHasSingleLineWriteMask)
        ([e].any fun expression =>
          match expression.op with
          | ParsedOp.noforward => true
          | x => false)
        false =
      prepareParsedIntegerMatrixReadLineExpression
        (stateB.peRegisters welcomePE) (stateForwardingSlots stateB welcomePE)
        (stateForwardingSlots stateB welcomePE)
        (stateB.matrixRegisters (ParsedIntegerContext.ofLinearIndex welcomePE).group
          (ParsedIntegerContext.ofLinearIndex welcomePE).l2b
          (ParsedIntegerContext.ofLinearIndex welcomePE).l1b)
        e (parsedPEHazardControl stateB welcomePE)
        ([e].any parsedExprHasSingleLineWriteMask)
        ([e].any fun expression =>
          match expression.op with
          | ParsedOp.noforward => true
          | x => false)
        false := by
    cases e with
    | mk op sources destinations flush text =>
      rcases constant with isZero | ⟨payload, sparse, isImmediate⟩
      · have opEq : op = .zero := isZero
        rw [opEq]
        unfold prepareParsedIntegerMatrixReadLineExpression
        dsimp only
        rw [prepareParsedIntegerALUExprCycles_constant_eq (stateA.peRegisters welcomePE)
          (stateB.peRegisters welcomePE) (stateForwardingSlots stateB welcomePE)
          { op := .zero, sources := sources, destinations := destinations, flush := flush,
            text := text }
          (parsedPEHazardControl stateB welcomePE) _ _ false (Or.inl rfl) hfiles]
      · have opEq : op = .immediate payload sparse := isImmediate
        rw [opEq]
        unfold prepareParsedIntegerMatrixReadLineExpression
        dsimp only
        rw [prepareParsedIntegerALUExprCycles_constant_eq (stateA.peRegisters welcomePE)
          (stateB.peRegisters welcomePE) (stateForwardingSlots stateB welcomePE)
          { op := .immediate payload sparse, sources := sources,
            destinations := destinations, flush := flush, text := text }
          (parsedPEHazardControl stateB welcomePE) _ _ false
          (Or.inr ⟨payload, sparse, rfl⟩) hfiles]

  unfold prepareParsedIntegerMatrixReadLineExpressions
  dsimp only
  exact congrArg (fun row =>
    match row with
    | StepResult.failure => StepResult.failure
    | StepResult.unknown => StepResult.unknown
    | StepResult.ok (expressionWrites, expressionSlots, expressionBarUpdates) =>
        StepResult.ok ([] ++ expressionWrites, expressionSlots,
          [] ++ expressionBarUpdates)) rowEq

theorem welcomeCommitStep_lm1_congr (filesA filesB : IntegerRegisterFiles)
    (write : PreparedParsedMaskedWrite) (h : filesA.lm1 = filesB.lm1) :
    (welcomeCommitStep filesA write).lm1 = (welcomeCommitStep filesB write).lm1 := by
  unfold welcomeCommitStep
  cases hmask : write.maskUpdate with
  | some update =>
      obtain ⟨entry, cycle, flags⟩ := update
      simp [h]
  | none =>
      cases hdest : write.destination with
      | none => exact h
      | some destination =>
          cases destination with
          | mk bank width address =>
              cases bank with
              | lm0 => simp [writeDirectAccessMasked, writeRegisterBankMasked, h]
              | lm1 => simp [writeDirectAccessMasked, writeRegisterBankMasked, h]
              | grf0 => simp [writeDirectAccessMasked, writeRegisterBankMasked, h]
              | grf1 => simp [writeDirectAccessMasked, writeRegisterBankMasked, h]
              | t => simp [writeDirectAccessMasked, writeRegisterBankMasked, h]

theorem commitParsedMaskedWrites_lm1_congr (filesA filesB : IntegerRegisterFiles)
    (writesA writesB : List PreparedParsedMaskedWrite)
    (hfiles : filesA.lm1 = filesB.lm1) (hwrites : writesA = writesB) :
    (commitParsedMaskedWrites filesA writesA).lm1 =
      (commitParsedMaskedWrites filesB writesB).lm1 := by
  subst hwrites
  induction writesA generalizing filesA filesB with
  | nil => exact hfiles
  | cons write rest ih =>
      rw [show commitParsedMaskedWrites filesA (write :: rest) =
            commitParsedMaskedWrites (welcomeCommitStep filesA write) rest from rfl]
      rw [show commitParsedMaskedWrites filesB (write :: rest) =
            commitParsedMaskedWrites (welcomeCommitStep filesB write) rest from rfl]
      exact ih _ _ (welcomeCommitStep_lm1_congr filesA filesB write hfiles)

theorem welcomePEPlainImmediateDoubleObligation :
    WelcomePEPlainImmediateDoubleObligation := by
  intro expressions unrefuted plain escaping
  obtain ⟨e, same, ePlain⟩ := plain_single_expression expressions unrefuted plain
  subst same
  obtain ⟨row, rowMember, immediate, destination, destinationMem, destinationStatic⟩ := escaping
  simp only [List.map_cons, List.map_nil, List.mem_singleton] at rowMember
  subst rowMember
  have constant : e.toParsed.op = .zero ∨
      ∃ payload sparse, e.toParsed.op = .immediate payload sparse := Or.inr immediate
  intro nextA stepA nextB stepB
  have accepted : checkParsedTopLine (InstructionLine.pe [e]).toParsed = true :=
    unrefuted.1.1
  obtain ⟨writesA, slotsA, barsA, prepA, commitA⟩ :=
    welcomeSealed_pe_prepared [e] (welcomeInitialState welcomeZeroWords) accepted
      (by simpa using plain) stepA
  obtain ⟨writesB, slotsB, barsB, prepB, commitB⟩ :=
    welcomeSealed_pe_prepared [e] (welcomeInitialState welcomeAllFiveWords) accepted
      (by simpa using plain) stepB
  have hfiles : ((welcomeInitialState welcomeZeroWords).peRegisters welcomePE).maskRegisters =
      ((welcomeInitialState welcomeAllFiveWords).peRegisters welcomePE).maskRegisters := rfl
  have hslots : stateForwardingSlots (welcomeInitialState welcomeZeroWords) welcomePE =
      stateForwardingSlots (welcomeInitialState welcomeAllFiveWords) welcomePE := rfl
  have hcontrol : parsedPEHazardControl (welcomeInitialState welcomeZeroWords) welcomePE =
      parsedPEHazardControl (welcomeInitialState welcomeAllFiveWords) welcomePE := rfl
  have hstore : (welcomeInitialState welcomeZeroWords).matrixRegisters =
      (welcomeInitialState welcomeAllFiveWords).matrixRegisters := rfl
  have prepEq := welcomeIntegerPrep_constant_eq (welcomeInitialState welcomeZeroWords)
    (welcomeInitialState welcomeAllFiveWords) e.toParsed ePlain constant hfiles hslots hcontrol
    hstore
  simp only [List.map_cons, List.map_nil] at prepA prepB
  have writesEq : writesA = writesB := by
    have := prepEq
    rw [prepA, prepB] at this
    injection this with tripleEq
    exact (Prod.mk.inj tripleEq).1
  rw [commitA, commitB, writesEq]
  exact commitParsedMaskedWrites_lm1_congr _ _ _ _ rfl rfl



/-! ## The forwarding-slot frame of one cycle

The four cycles of one expression are prepared in order and each cycle updates
only its own `.alu` slot.  Since the initial slots are all poison, the slot the
current cycle reads is still the initial one: a forwarding read can never
succeed at the zero initial state. -/

theorem updateParsedIntegerALUForwardingCycle_frame
    (old : ProofsLean.MNCore.Forwarding.Slots) (cycle : Fin 4)
    (prepared : StepResult PreparedParsedMaskedWrite) (noForward : Bool)
    (slots : ProofsLean.MNCore.Forwarding.Slots)
    (updated : updateParsedIntegerALUForwardingCycle old cycle prepared noForward = .ok slots) :
    ∀ unit other, other ≠ cycle → slots unit other = old unit other := by
  intro unit other different
  cases prepared with
  | failure => simp [updateParsedIntegerALUForwardingCycle] at updated
  | unknown => simp [updateParsedIntegerALUForwardingCycle] at updated
  | ok write =>
      cases noForward with
      | true =>
          simp only [updateParsedIntegerALUForwardingCycle, Bool.false_eq_true, if_true,
            StepResult.ok.injEq] at updated
          subst updated
          rfl
      | false =>
          simp only [updateParsedIntegerALUForwardingCycle, Bool.false_eq_true, if_false,
            StepResult.ok.injEq] at updated
          subst updated
          simp [different]

theorem welcomeZeroForwardingSlots_poison (unit : ProofsLean.MNCore.Forwarding.Unit)
    (cycle : Fin 4) :
    stateForwardingSlots (welcomeInitialState welcomeZeroWords) welcomePE unit cycle = .poison := by
  simp [stateForwardingSlots, welcomeInitialState, rustSimulatorInitialState]

theorem welcomeZeroForwardingSlots_poison_all : ∀ unit cycle,
    stateForwardingSlots (welcomeInitialState welcomeZeroWords) welcomePE unit cycle = .poison :=
  fun unit cycle => welcomeZeroForwardingSlots_poison unit cycle


/-- The single-row prepared list of a plain line is the row's four-cycle ALU
preparation, with the bar updates dropped. -/
theorem welcomeIntegerPrep_single_plain_eq (state : State) (e : ParsedExpr)
    (plain : parsedExprIsPlainIntegerALU e = true) :
    welcomeIntegerPrep state welcomePE [e] =
      (match prepareParsedIntegerALUExprCycles (state.peRegisters welcomePE)
          (stateForwardingSlots state welcomePE) (stateForwardingSlots state welcomePE)
          e (parsedPEHazardControl state welcomePE)
          ([e].any parsedExprHasSingleLineWriteMask)
          ([e].any fun expression =>
            match expression.op with
            | ParsedOp.noforward => true
            | x => false)
          false with
        | StepResult.failure => StepResult.failure
        | StepResult.unknown => StepResult.unknown
        | StepResult.ok (writes, slots) =>
            StepResult.ok (writes, slots, parsedIntegerALUBarUpdates e writes)) := by
  have filterEq : [e].filter parsedExprIsIntegerMatrixReadStageInput = [e] := by
    rw [List.filter_eq_self]
    intro x hx
    rw [List.mem_singleton] at hx
    subst x
    exact plain_stageInput e plain
  unfold welcomeIntegerPrep prepareParsedIntegerMatrixReadLineCycles
  rw [filterEq]
  unfold prepareParsedIntegerMatrixReadLineExpressions
  simp only
  cases e with
  | mk op sources destinations flush text =>
    cases op with
    | alu name precision unsigned arg =>
        simp only [prepareParsedIntegerMatrixReadLineExpression]
        cases h : prepareParsedIntegerALUExprCycles
            (state.peRegisters welcomePE) (stateForwardingSlots state welcomePE)
            (stateForwardingSlots state welcomePE)
            { op := .alu name precision unsigned arg, sources := sources,
              destinations := destinations, flush := flush, text := text }
            (parsedPEHazardControl state welcomePE) _ _ false with
        | failure => rfl
        | unknown => rfl
        | ok result => obtain ⟨w, s⟩ := result; rfl
    | zero =>
        simp only [prepareParsedIntegerMatrixReadLineExpression]
        cases h : prepareParsedIntegerALUExprCycles
            (state.peRegisters welcomePE) (stateForwardingSlots state welcomePE)
            (stateForwardingSlots state welcomePE)
            { op := .zero, sources := sources, destinations := destinations,
              flush := flush, text := text }
            (parsedPEHazardControl state welcomePE) _ _ false with
        | failure => rfl
        | unknown => rfl
        | ok result => obtain ⟨w, s⟩ := result; rfl
    | immediate payload sparse =>
        simp only [prepareParsedIntegerMatrixReadLineExpression]
        cases h : prepareParsedIntegerALUExprCycles
            (state.peRegisters welcomePE) (stateForwardingSlots state welcomePE)
            (stateForwardingSlots state welcomePE)
            { op := .immediate payload sparse, sources := sources,
              destinations := destinations, flush := flush, text := text }
            (parsedPEHazardControl state welcomePE) _ _ false with
        | failure => rfl
        | unknown => rfl
        | ok result => obtain ⟨w, s⟩ := result; rfl
    | mau precision matrix kind half round =>
        simp [parsedExprIsPlainIntegerALU, parsedExprIsIntegerProducer] at plain
    | matrixWrite precision =>
        simp [parsedExprIsPlainIntegerALU, parsedExprIsIntegerProducer] at plain
    | matrixRead precision =>
        simp [parsedExprIsPlainIntegerALU, parsedExprIsIntegerProducer] at plain
    | wait tag =>
        simp [parsedExprIsPlainIntegerALU, parsedExprIsIntegerProducer] at plain
    | noforward =>
        simp [parsedExprIsPlainIntegerALU, parsedExprIsIntegerProducer] at plain
    | l1bm operation =>
        simp [parsedExprIsPlainIntegerALU, parsedExprIsIntegerProducer] at plain
    | l2bm operation =>
        simp [parsedExprIsPlainIntegerALU, parsedExprIsIntegerProducer] at plain

theorem welcomeIntegerPrep_inv (state : State) (e : ParsedExpr)
    (plain : parsedExprIsPlainIntegerALU e = true)
    (writes : List PreparedParsedMaskedWrite) (slots : ProofsLean.MNCore.Forwarding.Slots)
    (bars : List (Bool × BitVec 12))
    (prep : welcomeIntegerPrep state welcomePE [e] = .ok (writes, slots, bars)) :
    prepareParsedIntegerALUExprCycles (state.peRegisters welcomePE)
        (stateForwardingSlots state welcomePE) (stateForwardingSlots state welcomePE)
        e (parsedPEHazardControl state welcomePE)
        ([e].any parsedExprHasSingleLineWriteMask)
        ([e].any fun expression =>
          match expression.op with
          | ParsedOp.noforward => true
          | x => false)
        false = .ok (writes, slots) := by
  cases h : prepareParsedIntegerALUExprCycles (state.peRegisters welcomePE)
      (stateForwardingSlots state welcomePE) (stateForwardingSlots state welcomePE)
      e (parsedPEHazardControl state welcomePE)
      ([e].any parsedExprHasSingleLineWriteMask)
      ([e].any fun expression =>
        match expression.op with
        | ParsedOp.noforward => true
        | x => false)
      false with
  | failure =>
      have outer : welcomeIntegerPrep state welcomePE [e] = .failure := by
        rw [welcomeIntegerPrep_single_plain_eq state e plain]
        simp only [h]
      rw [outer] at prep
      cases prep
  | unknown =>
      have outer : welcomeIntegerPrep state welcomePE [e] = .unknown := by
        rw [welcomeIntegerPrep_single_plain_eq state e plain]
        simp only [h]
      rw [outer] at prep
      cases prep
  | ok result =>
      obtain ⟨w, s⟩ := result
      have outer : welcomeIntegerPrep state welcomePE [e] =
          .ok (w, s, parsedIntegerALUBarUpdates e w) := by
        rw [welcomeIntegerPrep_single_plain_eq state e plain]
        simp only [h]
      rw [outer] at prep
      simp only [StepResult.ok.injEq] at prep
      injection prep with hpair hbars
      injection hbars with hslots hrest
      rw [hpair, hslots]


/-- One expression's four-cycle preparation, unrolled into its four cycle chunks.
The chunks are returned together with the intermediate slot states. -/
theorem prepareParsedIntegerALUExprCycles_four
    (files : IntegerRegisterFiles) (oldSlots : ProofsLean.MNCore.Forwarding.Slots)
    (e : ParsedExpr) (control : ParsedMaskExecutionControl) (hsm nf r : Bool)
    (writes : List PreparedParsedMaskedWrite) (slots : ProofsLean.MNCore.Forwarding.Slots)
    (prep : prepareParsedIntegerALUExprCycles files oldSlots oldSlots e control hsm nf r =
      .ok (writes, slots)) :
    ∃ (w0 w1 w2 w3 : List PreparedParsedMaskedWrite)
      (s1 s2 s3 : ProofsLean.MNCore.Forwarding.Slots),
      prepareParsedIntegerALUExprCycle files oldSlots oldSlots e control hsm nf r
          (0 : Fin 4) = .ok (w0, s1) ∧
      prepareParsedIntegerALUExprCycle files oldSlots s1 e control hsm nf r
          (1 : Fin 4) = .ok (w1, s2) ∧
      prepareParsedIntegerALUExprCycle files oldSlots s2 e control hsm nf r
          (2 : Fin 4) = .ok (w2, s3) ∧
      prepareParsedIntegerALUExprCycle files oldSlots s3 e control hsm nf r
          (3 : Fin 4) = .ok (w3, slots) ∧
      writes = w0 ++ w1 ++ w2 ++ w3 := by
  unfold prepareParsedIntegerALUExprCycles at prep
  simp only [parsedIntegerALUCycles] at prep
  unfold prepareParsedIntegerALUCycles at prep
  cases h0 : prepareParsedIntegerALUExprCycle files oldSlots oldSlots e control hsm nf r
      (0 : Fin 4) with
  | failure => simp [h0] at prep
  | unknown => simp [h0] at prep
  | ok result =>
      obtain ⟨w0, s1⟩ := result
      simp only [h0] at prep
      unfold prepareParsedIntegerALUCycles at prep
      cases h1 : prepareParsedIntegerALUExprCycle files oldSlots s1 e control hsm nf r
          (1 : Fin 4) with
      | failure => simp [h1] at prep
      | unknown => simp [h1] at prep
      | ok result =>
          obtain ⟨w1, s2⟩ := result
          simp only [h1] at prep
          unfold prepareParsedIntegerALUCycles at prep
          cases h2 : prepareParsedIntegerALUExprCycle files oldSlots s2 e control hsm nf r
              (2 : Fin 4) with
          | failure => simp [h2] at prep
          | unknown => simp [h2] at prep
          | ok result =>
              obtain ⟨w2, s3⟩ := result
              simp only [h2] at prep
              unfold prepareParsedIntegerALUCycles at prep
              cases h3 : prepareParsedIntegerALUExprCycle files oldSlots s3 e control hsm nf r
                  (3 : Fin 4) with
              | failure => simp [h3] at prep
              | unknown => simp [h3] at prep
              | ok result =>
                  obtain ⟨w3, s4⟩ := result
                  simp only [h3, List.nil_append, StepResult.ok.injEq, Prod.mk.injEq] at prep
                  obtain ⟨rfl, rfl⟩ := prep
                  exact ⟨w0, w1, w2, w3, s1, s2, s3, rfl, h1, h2, h3, rfl⟩

/-- The discharged obligation has exactly the type of the `Prop` stated in
`WelcomePlainShape.lean`. -/
example : WelcomePEPlainImmediateDoubleObligation :=
  welcomePEPlainImmediateDoubleObligation

end ProofsLean.MNCore
