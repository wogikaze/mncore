import ProofsLean.WelcomeWriterShape

/-! # The mixed plain/inert line: the writer split and the immediate-double case

`WelcomeWriterShape.lean` §7 reduces the mixed plain/inert obligation
`WelcomePEMixedPlainInertShapeObligation` to the syntactic structure statement
`WelcomePEMixedPlainInertStructure`, which bundles six components.  Its §8 names
three blockers:

1. the **list split**: the integer stage's row list
   `(line).filter parsedExprIsIntegerMatrixReadStageInput` decomposes as
   `noforward* ++ writer :: noforward*`;
2. the **immediate-double exclusion** in mixed lines: an `.immediate` writer
   with an `.lm1 .double` destination is input-independent rather than
   double-copy (`WelcomePEPlainImmediateDoubleObligation` covers the all-plain
   class only);
3. the **mask-flag agreement**: the integer stage prepares its rows with the
   *line* flag `(filter).any parsedExprHasSingleLineWriteMask`, while
   `plainRow_lm1_shape` is stated at the *row* flag.

This module discharges (1) and (2) and isolates (3) as the single named `Prop`
`WelcomePEMixedPlainInertFlagAgreement`.

* **§1 the rows of a mixed line**: a row that survives the integer-stage filter
  is a `.noforward` row or the plain writer
  (`welcomeMixed_stageInput_eq_noforward_or_plain`), the writer's own write banks
  are duplicate free (`welcomeMixed_writer_writeBanks_nodup`, from the issue
  checker's `writesUnique`), and the filter splits at the writer's position
  (`welcomeMixed_stageInput_split`).
* **§2 the fold over the stage list**: `welcomeIntegerPrep` on a split stage list
  is the writer row's own preparation at the initial forwarding slots — the
  executor-side form of (1) (`welcomeIntegerPrep_single_writer` of
  `WelcomeWriterShape.lean`, restated as an existential over the split).
* **§3 the immediate-double case**: a `.zero`/`.immediate` writer inside a mixed
  line is input-independent.  The two-run comparison (all-zero versus all-five)
  reuses the row-level constant equality, the inert rows' neutrality in the fold
  and the commit's `.lm1` congruence; inert rows prepare nothing and leave the
  forwarding slots untouched, so the writer still sees the initial slots.
* **§4 the reduction**: with (1) and (2) in place, the mixed obligation follows
  from the flag agreement alone.  The revised structure statement
  `WelcomePEMixedPlainInertStructureReduced` replaces the `notDouble` component
  by `notDouble ∨ WelcomePEInputIndependent`; the original
  `WelcomePEMixedPlainInertStructure` is one of its producers, and so is the flag
  agreement.  The replacement is necessary, not cosmetic: a mixed line whose
  plain writer is an `.immediate` row with an `.lm1 .double` destination
  *refutes* the original structure statement
  (`welcomePEMixedPlainInertStructure_forbids_immediateDouble`), because the
  `notDouble` field is then false, while the line is input-independent.

No `sorry`, no `admit`, no `native_decide`, no new axioms.  Nothing here assumes
the obligation it names, and it does not claim `LowerBound 2` or `Optimal`.
-/

namespace ProofsLean.MNCore

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

open Issue
open PEMemory

/-! ## 1. The rows of a mixed line

The integer stage executes
`(line).filter parsedExprIsIntegerMatrixReadStageInput`.  `WelcomeWriterShape.lean`
§7 shows every row of a mixed line is integer-or-inert; the rows that survive the
filter are therefore the integer-stage inputs, and among those the only ones
that are not `.noforward` are plain.  The issue checker then supplies two further
facts: at most one row of a legal line is plain (`plain_rows_at_most_one_eq`), and
each row's own write banks are duplicate free (`writesUnique`). -/

/-- **The `i`-th projected row.**  `projectLine` numbers rows consecutively from
`0`, so the `i`-th projected row is the `i`-th source row's projection at id `i`. -/
theorem projectFrom_getElem_toIssueExpr (nextId : Nat) (expressions : List ParsedExpr) :
    ∀ (i : Nat) (hi : i < (projectFrom nextId expressions).length)
      (hin : i < expressions.length),
      (projectFrom nextId expressions)[i]'hi =
        (expressions[i]'hin).toIssueExpr (nextId + i) := by
  induction expressions generalizing nextId with
  | nil =>
      intro i hi hin
      exact absurd hin (by simp)
  | cons expression rest ih =>
      intro i hi hin
      cases i with
      | zero => rfl
      | succ i =>
          have hi' : i < (projectFrom (nextId + 1) rest).length := by
            simp only [projectFrom, List.length_cons] at hi
            omega
          have hin' : i < rest.length := by
            simp only [List.length_cons] at hin
            omega
          have hleft : (projectFrom nextId (expression :: rest))[i + 1]'hi =
              (projectFrom (nextId + 1) rest)[i]'hi' := by
            simp only [projectFrom, List.getElem_cons_succ]
          rw [hleft, ih (nextId + 1) i hi' hin']
          simp only [List.getElem_cons_succ]
          rw [show nextId + 1 + i = nextId + (i + 1) by omega]

/-- **The writer's own write banks are duplicate free.**  The issue checker's
`writesUnique` gives the `Nodup` of every projected row; `writeBanks` does not
depend on the projection's id (`writeBanks_eq_bankList`), so the row's write banks
are duplicate free at id `0` as required by the row-shape lemmas. -/
theorem welcomeMixed_writer_writeBanks_nodup (expressions : List NormalizedExpr)
    (unrefuted : WelcomePEUnrefuted expressions) (i : Nat)
    (hi : i < (expressions.map NormalizedExpr.toParsed).length) :
    (((expressions.map NormalizedExpr.toParsed)[i]'hi).toIssueExpr 0).writeBanks.Nodup := by
  let line := expressions.map NormalizedExpr.toParsed
  have legal : LegalParsedLine line := welcomePEUnrefuted_legal expressions unrefuted
  have projLength : (projectLine line).length = line.length := projectFrom_length 0 line
  have hiProj : i < (projectLine line).length := by rw [projLength]; exact hi
  have member : (projectLine line)[i]'hiProj ∈ projectLine line := List.getElem_mem hiProj
  have nodup := welcomeLm1WritesNodup expressions legal _ member
  have idEq : (projectLine line)[i]'hiProj = (line[i]'hi).toIssueExpr i := by
    show (projectFrom 0 line)[i]'hiProj = (line[i]'hi).toIssueExpr i
    simpa using projectFrom_getElem_toIssueExpr 0 line i hiProj hi
  have banksEq : ((line[i]'hi).toIssueExpr i).writeBanks =
      ((line[i]'hi).toIssueExpr 0).writeBanks := by
    rw [writeBanks_eq_bankList, writeBanks_eq_bankList]
  rw [idEq, banksEq] at nodup
  exact nodup

/-- **A row of the integer stage of a mixed line is `.noforward` or plain.**
The six-family split leaves four kinds of supported row: plain, family, special
ALU and PE-inert.  The mixed hypotheses kill the family and special-ALU cases;
the inert cases are `.noforward`, a `.wait` row (excluded by the filter, which
requires `parsedExprWaitTag? = none`) and a shared-block `.l1bm` row (excluded by
the filter's `L1Mwrite` / `L1Gather` / `L1Reduce` guards). -/
theorem parsedExprIsL1SharedBlockProducer_stageInput_false (expression : ParsedExpr)
    (shared : parsedExprIsL1SharedBlockProducer expression = true) :
    parsedExprIsIntegerMatrixReadStageInput expression = false := by
  rcases parsedExprIsL1SharedBlockProducer_cases expression shared with
    ⟨mab, op⟩ | ⟨mab, op⟩ | ⟨mabdiff, op⟩ | ⟨rrn, round, op⟩ | ⟨rrn, round, op⟩ <;>
    simp [op, parsedExprIsIntegerMatrixReadStageInput, parsedExprIsL1MwriteProducer,
      parsedExprIsL1GatherProducer, parsedExprIsL1ReduceProducer, parsedExprWaitTag?]

theorem welcomeMixed_stageInput_eq_noforward_or_plain
    (expressions : List NormalizedExpr) (unrefuted : WelcomePEUnrefuted expressions)
    (noFamily : (expressions.map NormalizedExpr.toParsed).any
      parsedExprIsFamilyProducer = false)
    (noSpecial : (expressions.map NormalizedExpr.toParsed).any
      parsedExprIsSpecialALUProducer = false)
    (expression : ParsedExpr)
    (member : expression ∈ expressions.map NormalizedExpr.toParsed)
    (stageInput : parsedExprIsIntegerMatrixReadStageInput expression = true) :
    expression.op = ParsedOp.noforward ∨
      parsedExprIsPlainIntegerALU expression = true := by
  have supported := List.all_eq_true.mp unrefuted.1.2.2.2 expression member
  have notUnsupported : parsedExprIsUnsupportedRustAlu expression = false := by
    simpa using (List.any_eq_false.mp unrefuted.1.2.2.1) expression member
  have notFamily : parsedExprIsFamilyProducer expression = false := by
    simpa using (List.any_eq_false.mp noFamily) expression member
  have notSpecial : parsedExprIsSpecialALUProducer expression = false := by
    simpa using (List.any_eq_false.mp noSpecial) expression member
  rcases supportedProducer_partition expression supported with
    plain | family | special | inert | unsupported
  · exact Or.inr plain
  · rw [notFamily] at family
    cases family
  · rw [notSpecial] at special
    cases special
  · rcases parsedExprIsPEInertProducer_cases expression inert with forward | wait | shared
    · exact Or.inl forward
    · obtain ⟨tag, tagEq⟩ := wait
      exfalso
      have waitNone : parsedExprWaitTag? expression = none :=
        (parsedExprIsIntegerMatrixReadStageInput_spec expression).mp stageInput |>.1
      have someTag : parsedExprWaitTag? expression = some tag := by
        simp [parsedExprWaitTag?, tagEq]
      rw [someTag] at waitNone
      cases waitNone
    · exfalso
      have notStage := parsedExprIsL1SharedBlockProducer_stageInput_false expression shared
      rw [stageInput] at notStage
      cases notStage
  · rw [notUnsupported] at unsupported
    cases unsupported

/-- **The split at the line level.**  If every integer-stage row of `line` is
`.noforward` or the plain row `e`, and `line` is legal, the filtered stage list is
`before ++ e :: after` with `.noforward` rows around `e`.  The split is taken at
the position of `e`; `plain_rows_at_most_one_eq` forbids a second plain row, so
in particular a second occurrence of `e`, which is what makes the two tails
`.noforward`-only. -/
theorem parsedLine_stageInput_split (line : List ParsedExpr) (legal : LegalParsedLine line)
    (stage : ∀ expression ∈ line,
      parsedExprIsIntegerMatrixReadStageInput expression = true →
        expression.op = ParsedOp.noforward ∨
          parsedExprIsPlainIntegerALU expression = true)
    (e : ParsedExpr) (eMem : e ∈ line) (ePlain : parsedExprIsPlainIntegerALU e = true) :
    ∃ before after : List ParsedExpr,
      line.filter parsedExprIsIntegerMatrixReadStageInput = before ++ e :: after ∧
      (∀ expression ∈ before, expression.op = ParsedOp.noforward) ∧
      (∀ expression ∈ after, expression.op = ParsedOp.noforward) := by
  classical
  have eStage : parsedExprIsIntegerMatrixReadStageInput e = true := plain_stageInput e ePlain
  obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp eMem
  refine ⟨(line.take i).filter parsedExprIsIntegerMatrixReadStageInput,
    (line.drop (i + 1)).filter parsedExprIsIntegerMatrixReadStageInput, ?_, ?_, ?_⟩
  · have lineEq : line = line.take i ++ line[i]'hi :: line.drop (i + 1) := by
      conv_lhs => rw [← List.take_append_drop i line]
      rw [List.drop_eq_getElem_cons hi]
    have hStageE : parsedExprIsIntegerMatrixReadStageInput (line[i]'hi) = true := by
      rw [hget]
      exact eStage
    conv_lhs => rw [lineEq]
    rw [List.filter_append, List.filter_cons_of_pos hStageE, hget]
  · intro expression member
    have inTake : expression ∈ line.take i := List.mem_of_mem_filter member
    have stageInput : parsedExprIsIntegerMatrixReadStageInput expression = true :=
      (List.mem_filter.mp member).2
    rcases stage expression (List.mem_of_mem_take inTake) stageInput with forward | plain
    · exact forward
    · exfalso
      obtain ⟨j, hj, hgetj⟩ := List.mem_iff_getElem.mp inTake
      have lenTake : (line.take i).length = i := by
        rw [List.length_take]
        omega
      have jLt : j < i := by rw [lenTake] at hj; exact hj
      have hline : line[j]'(by omega) = expression := by
        rw [← List.getElem_take (xs := line) (j := i) (i := j) (h := hj)]
        exact hgetj
      have sameIndex : j = i := plain_rows_at_most_one_eq line legal j i (by omega) hi
        (by rw [hline]; exact plain) (by rw [hget]; exact ePlain)
      omega
  · intro expression member
    have inDrop : expression ∈ line.drop (i + 1) := List.mem_of_mem_filter member
    have stageInput : parsedExprIsIntegerMatrixReadStageInput expression = true :=
      (List.mem_filter.mp member).2
    rcases stage expression (List.mem_of_mem_drop inDrop) stageInput with forward | plain
    · exact forward
    · exfalso
      obtain ⟨j, hj, hgetj⟩ := List.mem_iff_getElem.mp inDrop
      have lenDrop : (line.drop (i + 1)).length = line.length - (i + 1) := List.length_drop
      have posLt : i + 1 + j < line.length := by
        rw [lenDrop] at hj
        omega
      have hline : line[i + 1 + j]'posLt = expression := by
        rw [← List.getElem_drop (xs := line) (i := i + 1) (j := j) (h := hj)]
        exact hgetj
      have sameIndex : i + 1 + j = i :=
        plain_rows_at_most_one_eq line legal (i + 1 + j) i posLt hi
          (by rw [hline]; exact plain) (by rw [hget]; exact ePlain)
      omega

/-- **The integer stage of a mixed line splits around the writer.** -/
theorem welcomeMixed_stageInput_split
    (expressions : List NormalizedExpr) (unrefuted : WelcomePEUnrefuted expressions)
    (noFamily : (expressions.map NormalizedExpr.toParsed).any
      parsedExprIsFamilyProducer = false)
    (noSpecial : (expressions.map NormalizedExpr.toParsed).any
      parsedExprIsSpecialALUProducer = false)
    (e : ParsedExpr) (eMem : e ∈ expressions.map NormalizedExpr.toParsed)
    (ePlain : parsedExprIsPlainIntegerALU e = true) :
    ∃ before after : List ParsedExpr,
      (expressions.map NormalizedExpr.toParsed).filter
          parsedExprIsIntegerMatrixReadStageInput = before ++ e :: after ∧
      (∀ expression ∈ before, expression.op = ParsedOp.noforward) ∧
      (∀ expression ∈ after, expression.op = ParsedOp.noforward) :=
  parsedLine_stageInput_split (expressions.map NormalizedExpr.toParsed)
    (welcomePEUnrefuted_legal expressions unrefuted)
    (fun expression member stageInput =>
      welcomeMixed_stageInput_eq_noforward_or_plain expressions unrefuted noFamily noSpecial
        expression member stageInput)
    e eMem ePlain

/-! ## 2. The fold over the stage list

`welcomeIntegerPrep` prepares the filtered stage list at the initial forwarding
slots.  On a split stage list the `.noforward` rows around the writer prepare
nothing and leave the slots untouched, so the whole fold is the writer's own row
preparation at the initial slots.  This is the form in which the split meets the
executor; it is `welcomeIntegerPrep_single_writer` of `WelcomeWriterShape.lean`
with the split produced by §1. -/

/-- **The executor's fold over a split stage list.**  The `.noforward` / `.wait`
rows around the writer contribute no write, no slot update and no bar update, so
`prepareParsedIntegerMatrixReadLineExpressions` over `before ++ e :: after` is the
single writer row's step, applied to the incoming accumulator.  This is the
general form of the split's interaction with the fold; §3 uses it through
`welcomeIntegerPrep`. -/
theorem prepareParsedIntegerMatrixReadLineExpressions_split
    (files : IntegerRegisterFiles) (oldSlots : ProofsLean.MNCore.Forwarding.Slots)
    (store : ParsedMatrixReadStore) (control : ParsedMaskExecutionControl)
    (hasSingleLineMask noForward reduced : Bool)
    (before after : List ParsedExpr) (e : ParsedExpr)
    (skipBefore : ∀ expression ∈ before,
      expression.op = ParsedOp.noforward ∨ ∃ tag : Fin 256, expression.op = ParsedOp.wait tag)
    (skipAfter : ∀ expression ∈ after,
      expression.op = ParsedOp.noforward ∨ ∃ tag : Fin 256, expression.op = ParsedOp.wait tag)
    (writes : List PreparedParsedMaskedWrite) (slots : ProofsLean.MNCore.Forwarding.Slots)
    (bars : List (Bool × BitVec 12)) :
    prepareParsedIntegerMatrixReadLineExpressions files oldSlots store control hasSingleLineMask
        noForward reduced (before ++ e :: after) writes slots bars =
      (match prepareParsedIntegerMatrixReadLineExpression files oldSlots slots store e control
          hasSingleLineMask noForward reduced with
       | .failure => .failure
       | .unknown => .unknown
       | .ok (rowWrites, rowSlots, rowBars) =>
           .ok (writes ++ rowWrites, rowSlots, bars ++ rowBars)) := by
  rw [prepareParsedIntegerMatrixReadLineExpressions_skip files oldSlots store control hasSingleLineMask
    noForward reduced (e :: after) before skipBefore writes slots bars]
  simp only [prepareParsedIntegerMatrixReadLineExpressions]
  cases prepareParsedIntegerMatrixReadLineExpression files oldSlots slots store e control
      hasSingleLineMask noForward reduced with
  | failure => rfl
  | unknown => rfl
  | ok row =>
      obtain ⟨rowWrites, rowSlots, rowBars⟩ := row
      simp only
      have tailEq := prepareParsedIntegerMatrixReadLineExpressions_skip files oldSlots store control
        hasSingleLineMask noForward reduced [] after skipAfter (writes ++ rowWrites) rowSlots
        (bars ++ rowBars)
      rw [List.append_nil] at tailEq
      simpa only [prepareParsedIntegerMatrixReadLineExpressions] using tailEq

/-- **The fold of a mixed line is the writer row's preparation.** -/
theorem welcomeMixed_integerPrep_single_writer (expressions : List NormalizedExpr)
    (unrefuted : WelcomePEUnrefuted expressions)
    (noFamily : (expressions.map NormalizedExpr.toParsed).any
      parsedExprIsFamilyProducer = false)
    (noSpecial : (expressions.map NormalizedExpr.toParsed).any
      parsedExprIsSpecialALUProducer = false)
    (e : ParsedExpr) (eMem : e ∈ expressions.map NormalizedExpr.toParsed)
    (ePlain : parsedExprIsPlainIntegerALU e = true) :
    ∃ before after : List ParsedExpr,
      (expressions.map NormalizedExpr.toParsed).filter
          parsedExprIsIntegerMatrixReadStageInput = before ++ e :: after ∧
      (∀ expression ∈ before, expression.op = ParsedOp.noforward ∨
        ∃ tag : Fin 256, expression.op = ParsedOp.wait tag) ∧
      (∀ expression ∈ after, expression.op = ParsedOp.noforward ∨
        ∃ tag : Fin 256, expression.op = ParsedOp.wait tag) ∧
      ∀ (state : State) (writes : List PreparedParsedMaskedWrite)
        (slots : ProofsLean.MNCore.Forwarding.Slots) (bars : List (Bool × BitVec 12)),
        welcomeIntegerPrep state welcomePE (expressions.map NormalizedExpr.toParsed) =
          .ok (writes, slots, bars) →
        ∃ rowWrites rowSlots rowBars,
          prepareParsedIntegerMatrixReadLineExpression (state.peRegisters welcomePE)
            (stateForwardingSlots state welcomePE) (stateForwardingSlots state welcomePE)
            (state.matrixRegisters (ParsedIntegerContext.ofLinearIndex welcomePE).group
              (ParsedIntegerContext.ofLinearIndex welcomePE).l2b
              (ParsedIntegerContext.ofLinearIndex welcomePE).l1b)
            e (parsedPEHazardControl state welcomePE)
            (((expressions.map NormalizedExpr.toParsed).filter
              parsedExprIsIntegerMatrixReadStageInput).any parsedExprHasSingleLineWriteMask)
            (((expressions.map NormalizedExpr.toParsed).filter
              parsedExprIsIntegerMatrixReadStageInput).any fun expression =>
              match expression.op with
              | ParsedOp.noforward => true
              | _ => false)
            false = .ok (rowWrites, rowSlots, rowBars) ∧
          writes = rowWrites := by
  obtain ⟨before, after, split, skipBefore, skipAfter⟩ :=
    welcomeMixed_stageInput_split expressions unrefuted noFamily noSpecial e eMem ePlain
  refine ⟨before, after, split, ?_, ?_, ?_⟩
  · intro expression member
    exact Or.inl (skipBefore expression member)
  · intro expression member
    exact Or.inl (skipAfter expression member)
  · intro state writes slots bars prep
    exact welcomeIntegerPrep_single_writer state _ before after e split
      (fun expression member => Or.inl (skipBefore expression member))
      (fun expression member => Or.inl (skipAfter expression member))
      writes slots bars prep

/-! ## 3. The immediate-double case inside a mixed line

An `.immediate` writer with an `.lm1 .double` destination cannot be refuted by
the copy or the narrow shape: its third data word is the payload, which is not a
copy, and a `.double` window is wider than the narrow bound.  What holds instead
is *input-independence*: the prepared write list of a `.zero`/`.immediate` row
does not depend on the input at all, and the inert rows around it prepare nothing
and leave the forwarding slots untouched.  Comparing the all-zero and the
all-five runs therefore gives equal `.lm1` files.

The comparison is carried out at the level of the *line*, not of a singleton:
`welcomeIntegerPrep_single_writer` turns the stage fold into the writer's row
preparation at the initial slots, and the row preparation of a constant row
depends on the register file only through its mask registers. -/

/-- **A constant row's preparation does not depend on the input registers.**
For a `.zero` or `.immediate` row the only input the preparation reads is the
mask register file. -/
theorem prepareParsedIntegerMatrixReadLineExpression_constant_eq
    (filesA filesB : IntegerRegisterFiles)
    (slots : ProofsLean.MNCore.Forwarding.Slots) (store : ParsedMatrixReadStore)
    (control : ParsedMaskExecutionControl) (hasSingleLineMask noForward reduced : Bool)
    (e : ParsedExpr)
    (constant : e.op = .zero ∨ ∃ payload sparse, e.op = .immediate payload sparse)
    (maskEq : filesA.maskRegisters = filesB.maskRegisters) :
    prepareParsedIntegerMatrixReadLineExpression filesA slots slots store e control
        hasSingleLineMask noForward reduced =
      prepareParsedIntegerMatrixReadLineExpression filesB slots slots store e control
        hasSingleLineMask noForward reduced := by
  cases e with
  | mk op sources destinations flush text =>
      rcases constant with zero | ⟨payload, sparse, immediate⟩
      · have opEq : op = .zero := zero
        rw [opEq]
        simp only [prepareParsedIntegerMatrixReadLineExpression]
        rw [prepareParsedIntegerALUExprCycles_constant_eq filesA filesB slots
          ⟨.zero, sources, destinations, flush, text⟩ control hasSingleLineMask noForward
          reduced (Or.inl rfl) maskEq]
      · have opEq : op = .immediate payload sparse := immediate
        rw [opEq]
        simp only [prepareParsedIntegerMatrixReadLineExpression]
        rw [prepareParsedIntegerALUExprCycles_constant_eq filesA filesB slots
          ⟨.immediate payload sparse, sources, destinations, flush, text⟩ control
          hasSingleLineMask noForward reduced (Or.inr ⟨payload, sparse, rfl⟩) maskEq]

/-- **The stage fold of a constant writer is the same at both inputs.**  The
stage list splits around the writer, the writer's row preparation is
input-independent, and the `.noforward` rows around it prepare no write at all,
so the two folds have the same write list. -/
theorem welcomeIntegerPrep_constant_writer_writes_eq
    (stateA stateB : State) (expressions : List ParsedExpr)
    (before after : List ParsedExpr) (e : ParsedExpr)
    (split : expressions.filter parsedExprIsIntegerMatrixReadStageInput = before ++ e :: after)
    (skipBefore : ∀ expression ∈ before,
      expression.op = ParsedOp.noforward ∨ ∃ tag : Fin 256, expression.op = ParsedOp.wait tag)
    (skipAfter : ∀ expression ∈ after,
      expression.op = ParsedOp.noforward ∨ ∃ tag : Fin 256, expression.op = ParsedOp.wait tag)
    (constant : e.op = .zero ∨ ∃ payload sparse, e.op = .immediate payload sparse)
    (hslots : stateForwardingSlots stateA welcomePE = stateForwardingSlots stateB welcomePE)
    (hmask : (stateA.peRegisters welcomePE).maskRegisters =
      (stateB.peRegisters welcomePE).maskRegisters)
    (hcontrol : parsedPEHazardControl stateA welcomePE = parsedPEHazardControl stateB welcomePE)
    (hstore : stateA.matrixRegisters = stateB.matrixRegisters)
    (writesA : List PreparedParsedMaskedWrite)
    (slotsA : ProofsLean.MNCore.Forwarding.Slots) (barsA : List (Bool × BitVec 12))
    (prepA : welcomeIntegerPrep stateA welcomePE expressions = .ok (writesA, slotsA, barsA))
    (writesB : List PreparedParsedMaskedWrite)
    (slotsB : ProofsLean.MNCore.Forwarding.Slots) (barsB : List (Bool × BitVec 12))
    (prepB : welcomeIntegerPrep stateB welcomePE expressions = .ok (writesB, slotsB, barsB)) :
    writesA = writesB := by
  obtain ⟨rowWritesA, rowSlotsA, rowBarsA, rowPrepA, writesEqA⟩ :=
    welcomeIntegerPrep_single_writer stateA expressions before after e split skipBefore skipAfter
      writesA slotsA barsA prepA
  obtain ⟨rowWritesB, rowSlotsB, rowBarsB, rowPrepB, writesEqB⟩ :=
    welcomeIntegerPrep_single_writer stateB expressions before after e split skipBefore skipAfter
      writesB slotsB barsB prepB
  have storeEq : stateA.matrixRegisters (ParsedIntegerContext.ofLinearIndex welcomePE).group
      (ParsedIntegerContext.ofLinearIndex welcomePE).l2b
      (ParsedIntegerContext.ofLinearIndex welcomePE).l1b =
      stateB.matrixRegisters (ParsedIntegerContext.ofLinearIndex welcomePE).group
      (ParsedIntegerContext.ofLinearIndex welcomePE).l2b
      (ParsedIntegerContext.ofLinearIndex welcomePE).l1b := by
    rw [hstore]
  have rowEq : prepareParsedIntegerMatrixReadLineExpression (stateA.peRegisters welcomePE)
      (stateForwardingSlots stateA welcomePE) (stateForwardingSlots stateA welcomePE)
      (stateA.matrixRegisters (ParsedIntegerContext.ofLinearIndex welcomePE).group
        (ParsedIntegerContext.ofLinearIndex welcomePE).l2b
        (ParsedIntegerContext.ofLinearIndex welcomePE).l1b)
      e (parsedPEHazardControl stateA welcomePE)
      ((expressions.filter parsedExprIsIntegerMatrixReadStageInput).any
        parsedExprHasSingleLineWriteMask)
      ((expressions.filter parsedExprIsIntegerMatrixReadStageInput).any fun expression =>
        match expression.op with
        | ParsedOp.noforward => true
        | _ => false)
      false =
      prepareParsedIntegerMatrixReadLineExpression (stateB.peRegisters welcomePE)
      (stateForwardingSlots stateB welcomePE) (stateForwardingSlots stateB welcomePE)
      (stateB.matrixRegisters (ParsedIntegerContext.ofLinearIndex welcomePE).group
        (ParsedIntegerContext.ofLinearIndex welcomePE).l2b
        (ParsedIntegerContext.ofLinearIndex welcomePE).l1b)
      e (parsedPEHazardControl stateB welcomePE)
      ((expressions.filter parsedExprIsIntegerMatrixReadStageInput).any
        parsedExprHasSingleLineWriteMask)
      ((expressions.filter parsedExprIsIntegerMatrixReadStageInput).any fun expression =>
        match expression.op with
        | ParsedOp.noforward => true
        | _ => false)
      false := by
    rw [hslots, hcontrol, storeEq]
    exact prepareParsedIntegerMatrixReadLineExpression_constant_eq
      (stateA.peRegisters welcomePE) (stateB.peRegisters welcomePE)
      (stateForwardingSlots stateB welcomePE)
      (stateB.matrixRegisters (ParsedIntegerContext.ofLinearIndex welcomePE).group
        (ParsedIntegerContext.ofLinearIndex welcomePE).l2b
        (ParsedIntegerContext.ofLinearIndex welcomePE).l1b)
      (parsedPEHazardControl stateB welcomePE) _ _ _ e constant hmask
  have combined := rowPrepA.symm.trans (rowEq.trans rowPrepB)
  rw [writesEqA, writesEqB]
  exact (Prod.mk.inj (StepResult.ok.inj combined)).1

/-- **A constant writer makes the whole mixed line input-independent.**  The two
runs commit the same write list from the same initial `.lm1` file, so the `.lm1`
output is the same. -/
theorem welcomePEMixedConstantWriter_inputIndependent
    (expressions : List NormalizedExpr) (unrefuted : WelcomePEUnrefuted expressions)
    (intOrInert : (expressions.map NormalizedExpr.toParsed).all welcomeIntegerOrInertLine = true)
    (before after : List ParsedExpr) (e : ParsedExpr)
    (split : (expressions.map NormalizedExpr.toParsed).filter
        parsedExprIsIntegerMatrixReadStageInput = before ++ e :: after)
    (skipBefore : ∀ expression ∈ before,
      expression.op = ParsedOp.noforward ∨ ∃ tag : Fin 256, expression.op = ParsedOp.wait tag)
    (skipAfter : ∀ expression ∈ after,
      expression.op = ParsedOp.noforward ∨ ∃ tag : Fin 256, expression.op = ParsedOp.wait tag)
    (constant : e.op = .zero ∨ ∃ payload sparse, e.op = .immediate payload sparse) :
    WelcomePEInputIndependent expressions := by
  intro nextA stepA nextB stepB
  obtain ⟨writesA, slotsA, barsA, prepA, commitA⟩ :=
    welcomePE_line_commit_of_integerOrInert expressions welcomeZeroWords nextA unrefuted
      intOrInert stepA
  obtain ⟨writesB, slotsB, barsB, prepB, commitB⟩ :=
    welcomePE_line_commit_of_integerOrInert expressions welcomeAllFiveWords nextB unrefuted
      intOrInert stepB
  have writesEq : writesA = writesB :=
    welcomeIntegerPrep_constant_writer_writes_eq (welcomeInitialState welcomeZeroWords)
      (welcomeInitialState welcomeAllFiveWords)
      (expressions.map NormalizedExpr.toParsed) before after e split skipBefore skipAfter
      constant rfl rfl rfl rfl writesA slotsA barsA prepA writesB slotsB barsB prepB
  rw [commitA, commitB, writesEq]
  exact commitParsedMaskedWrites_lm1_congr _ _ _ _ rfl rfl

/-- **The immediate-double case in a mixed line.**  An `.immediate` writer (in
particular one with an `.lm1 .double` destination) makes the line's PE 0 `.lm1`
output input-independent.  This is the mixed-line form of
`WelcomePEPlainImmediateDoubleObligation`; the inert rows of the line are
neutral because they prepare no write and leave the forwarding slots untouched. -/
theorem welcomePEMixedImmediateDouble_inputIndependent
    (expressions : List NormalizedExpr) (unrefuted : WelcomePEUnrefuted expressions)
    (intOrInert : (expressions.map NormalizedExpr.toParsed).all welcomeIntegerOrInertLine = true)
    (before after : List ParsedExpr) (e : ParsedExpr)
    (split : (expressions.map NormalizedExpr.toParsed).filter
        parsedExprIsIntegerMatrixReadStageInput = before ++ e :: after)
    (skipBefore : ∀ expression ∈ before,
      expression.op = ParsedOp.noforward ∨ ∃ tag : Fin 256, expression.op = ParsedOp.wait tag)
    (skipAfter : ∀ expression ∈ after,
      expression.op = ParsedOp.noforward ∨ ∃ tag : Fin 256, expression.op = ParsedOp.wait tag)
    (immediate : ∃ payload sparse, e.op = .immediate payload sparse) :
    WelcomePEInputIndependent expressions :=
  welcomePEMixedConstantWriter_inputIndependent expressions unrefuted intOrInert before after e
    split skipBefore skipAfter (Or.inr immediate)

/-- **The writer is either free of the immediate-double case or the line is
input-independent.**  This is the form consumed by the reduction: the original
structure statement demands the first disjunct, but the second is what actually
holds when the first fails. -/
theorem welcomeMixed_notDouble_or_inputIndependent
    (expressions : List NormalizedExpr) (unrefuted : WelcomePEUnrefuted expressions)
    (intOrInert : (expressions.map NormalizedExpr.toParsed).all welcomeIntegerOrInertLine = true)
    (before after : List ParsedExpr) (e : ParsedExpr)
    (split : (expressions.map NormalizedExpr.toParsed).filter
        parsedExprIsIntegerMatrixReadStageInput = before ++ e :: after)
    (skipBefore : ∀ expression ∈ before,
      expression.op = ParsedOp.noforward ∨ ∃ tag : Fin 256, expression.op = ParsedOp.wait tag)
    (skipAfter : ∀ expression ∈ after,
      expression.op = ParsedOp.noforward ∨ ∃ tag : Fin 256, expression.op = ParsedOp.wait tag) :
    (∀ (payload : BitVec 32) (sparse : Bool), e.op = .immediate payload sparse →
      ∀ destination ∈ e.destinations,
        ParsedOperand.directDestinationBankWidth? destination ≠
          some (PEMemory.Bank.lm1, PEMemory.Width.double)) ∨
    WelcomePEInputIndependent expressions := by
  by_cases notDouble : ∀ (payload : BitVec 32) (sparse : Bool), e.op = .immediate payload sparse →
      ∀ destination ∈ e.destinations,
        ParsedOperand.directDestinationBankWidth? destination ≠
          some (PEMemory.Bank.lm1, PEMemory.Width.double)
  · exact Or.inl notDouble
  · refine Or.inr ?_
    push Not at notDouble
    obtain ⟨payload, sparse, immediate, destination, member, equals⟩ := notDouble
    exact welcomePEMixedImmediateDouble_inputIndependent expressions unrefuted intOrInert
      before after e split skipBefore skipAfter ⟨payload, sparse, immediate⟩

/-! ## 4. The reduction: one residual left

With §1–§3 in place, two of the three components of
`WelcomePEMixedPlainInertStructure` are theorems:

* the split `before ++ writer :: after` is `welcomeMixed_stageInput_split`, and
* the `notDouble` field is not needed: when it fails the line is
  input-independent (`welcomeMixed_notDouble_or_inputIndependent`), which is the
  third disjunct of `WelcomePEWriteShape`.  The field is in fact *false* for an
  immediate-double writer, so the original structure statement is refuted there
  (`welcomePEMixedPlainInertStructure_forbids_immediateDouble`).

What remains is the **mask-flag agreement**: the integer stage prepares its rows
with the *line* flag `(filter).any parsedExprHasSingleLineWriteMask`, while the
plain row shape `plainRow_lm1_shape` is stated at the row's own flag
`parsedExprHasSingleLineWriteMask e`.  By
`welcomeMixed_flagAgreement_fails_iff` they differ exactly when the writer's own
flag is `false` and an inert row of the line carries a masked `.mem` / `.bar` /
`.omr` destination operand (`parsedOperandHasSingleLineWriteMask`), which nothing
in the issue checker forbids.  The flag selects which masked lowering of the plain row fires
(`parsed_issue_line_mask_cancels_unmasked_memory_target`), so the row-shape lemma
cannot be reused at the line flag: closing the gap means repeating the
per-branch analysis of `WelcomePlainStep.lean` with a free flag.  It is isolated
below as `WelcomePEMixedPlainInertFlagAgreement`. -/

/-- **The remaining mask-flag agreement.**  For a mixed line the unique plain
writer exists, and the line mask flag of the integer stage's row list equals the
writer's own flag.  The split and the writer's write-bank nodup are *not* part of
this statement: they are derived in §1. -/
def WelcomePEMixedPlainInertFlagAgreement : Prop :=
  ∀ expressions : List NormalizedExpr, WelcomePEUnrefuted expressions →
    (expressions.map NormalizedExpr.toParsed).all parsedExprIsPlainIntegerALU = false →
    (expressions.map NormalizedExpr.toParsed).any parsedExprIsPlainIntegerALU = true →
    (expressions.map NormalizedExpr.toParsed).any parsedExprIsFamilyProducer = false →
    (expressions.map NormalizedExpr.toParsed).any parsedExprIsSpecialALUProducer = false →
    ∃ e : ParsedExpr, e ∈ expressions.map NormalizedExpr.toParsed ∧
      parsedExprIsPlainIntegerALU e = true ∧
      (((expressions.map NormalizedExpr.toParsed).filter
            parsedExprIsIntegerMatrixReadStageInput).any parsedExprHasSingleLineWriteMask =
        parsedExprHasSingleLineWriteMask e)

/-- **Exactly when the mask-flag agreement fails.**  The line flag is the
disjunction of the stage rows' flags (`List.any`), so it differs from the writer's
own flag exactly when the writer's flag is `false` and some other stage row — by
§1 a `.noforward` row — carries a masked `.mem` / `.bar` / `.omr` destination. -/
theorem welcomeMixed_flagAgreement_fails_iff
    (expressions : List NormalizedExpr)
    (before after : List ParsedExpr) (e : ParsedExpr)
    (split : (expressions.map NormalizedExpr.toParsed).filter
        parsedExprIsIntegerMatrixReadStageInput = before ++ e :: after) :
    ((((expressions.map NormalizedExpr.toParsed).filter
          parsedExprIsIntegerMatrixReadStageInput).any
        parsedExprHasSingleLineWriteMask ≠
      parsedExprHasSingleLineWriteMask e) ↔
    (parsedExprHasSingleLineWriteMask e = false ∧
      (before ++ after).any parsedExprHasSingleLineWriteMask = true)) := by
  rw [split, List.any_append, List.any_cons, List.any_append]
  cases hE : parsedExprHasSingleLineWriteMask e <;>
    cases hB : before.any parsedExprHasSingleLineWriteMask <;>
    cases hA : after.any parsedExprHasSingleLineWriteMask <;>
    simp_all

/-- **A sufficient condition for the mask-flag agreement.**  If no stage row
around the writer carries a masked destination, the line flag is the writer's own
flag.  The failure characterised by `welcomeMixed_flagAgreement_fails_iff` is
therefore not a defect of the plain row: it is a masked destination on an inert
row. -/
theorem welcomeMixed_flagAgreement_of_inertFlags
    (expressions : List NormalizedExpr)
    (before after : List ParsedExpr) (e : ParsedExpr)
    (split : (expressions.map NormalizedExpr.toParsed).filter
        parsedExprIsIntegerMatrixReadStageInput = before ++ e :: after)
    (inert : (before ++ after).any parsedExprHasSingleLineWriteMask = false) :
    ((expressions.map NormalizedExpr.toParsed).filter
        parsedExprIsIntegerMatrixReadStageInput).any parsedExprHasSingleLineWriteMask =
      parsedExprHasSingleLineWriteMask e := by
  by_contra different
  have fails := (welcomeMixed_flagAgreement_fails_iff expressions before after e split).mp different
  rw [fails.2] at inert
  cases inert

/-- **A mixed line has a unique plain row.**  Two plain rows of a legal line have
the same position (`plain_rows_at_most_one_eq`), hence are the same expression. -/
theorem welcomeMixed_plain_writer_unique (expressions : List NormalizedExpr)
    (unrefuted : WelcomePEUnrefuted expressions) (e e' : ParsedExpr)
    (eMem : e ∈ expressions.map NormalizedExpr.toParsed)
    (eMem' : e' ∈ expressions.map NormalizedExpr.toParsed)
    (ePlain : parsedExprIsPlainIntegerALU e = true)
    (ePlain' : parsedExprIsPlainIntegerALU e' = true) :
    e = e' := by
  have legal : LegalParsedLine (expressions.map NormalizedExpr.toParsed) :=
    welcomePEUnrefuted_legal expressions unrefuted
  obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp eMem
  obtain ⟨j, hj, hget'⟩ := List.mem_iff_getElem.mp eMem'
  have same : i = j := plain_rows_at_most_one_eq (expressions.map NormalizedExpr.toParsed)
    legal i j hi hj (by rw [hget]; exact ePlain) (by rw [hget']; exact ePlain')
  subst same
  exact hget.symm.trans hget'

/-- **The original structure statement excludes the immediate-double writer.**
`WelcomePEMixedPlainInertStructure` demands the `notDouble` component for the
(unique) plain writer.  A line whose plain writer is an `.immediate` row with an
`.lm1 .double` destination therefore *refutes* the statement: the `notDouble`
field is not an unproved consequence of the issue checker but a false claim in
this case.  The reduced statement replaces the field by the disjunction with
`WelcomePEInputIndependent`, which is what holds here
(`welcomePEMixedImmediateDouble_inputIndependent`). -/
theorem welcomePEMixedPlainInertStructure_forbids_immediateDouble
    (expressions : List NormalizedExpr) (unrefuted : WelcomePEUnrefuted expressions)
    (notPlain : (expressions.map NormalizedExpr.toParsed).all
      parsedExprIsPlainIntegerALU = false)
    (noFamily : (expressions.map NormalizedExpr.toParsed).any
      parsedExprIsFamilyProducer = false)
    (noSpecial : (expressions.map NormalizedExpr.toParsed).any
      parsedExprIsSpecialALUProducer = false)
    (e : ParsedExpr) (eMem : e ∈ expressions.map NormalizedExpr.toParsed)
    (ePlain : parsedExprIsPlainIntegerALU e = true)
    (immediate : ∃ payload sparse, e.op = .immediate payload sparse)
    (doubleDestination : ∃ destination ∈ e.destinations,
      ParsedOperand.directDestinationBankWidth? destination =
        some (PEMemory.Bank.lm1, PEMemory.Width.double)) :
    ¬ WelcomePEMixedPlainInertStructure := by
  intro skeleton
  have plainAny : (expressions.map NormalizedExpr.toParsed).any
      parsedExprIsPlainIntegerALU = true :=
    List.any_eq_true.mpr ⟨e, eMem, ePlain⟩
  obtain ⟨before, after, writer, split, _, _, writerPlain, _, _, notDouble⟩ :=
    skeleton expressions unrefuted notPlain plainAny noFamily noSpecial
  have writerMem : writer ∈ expressions.map NormalizedExpr.toParsed :=
    List.mem_of_mem_filter (show writer ∈
        (expressions.map NormalizedExpr.toParsed).filter
          parsedExprIsIntegerMatrixReadStageInput from by
      rw [split]
      exact List.mem_append_right before (List.mem_cons_self ..))
  have writerEq : writer = e :=
    welcomeMixed_plain_writer_unique expressions unrefuted writer e writerMem eMem writerPlain
      ePlain
  rw [writerEq] at notDouble
  obtain ⟨payload, sparse, immediateEq⟩ := immediate
  obtain ⟨destination, destinationMem, destinationEq⟩ := doubleDestination
  exact (notDouble payload sparse immediateEq destination destinationMem) destinationEq

/-- **The reduced structure statement.**  Same shape as
`WelcomePEMixedPlainInertStructure`, except that the `notDouble` component is
replaced by the disjunction "the writer is not immediate-double, or the line is
input-independent".  The disjunction is closed by
`welcomeMixed_notDouble_or_inputIndependent`: its second branch always holds when
the first fails. -/
def WelcomePEMixedPlainInertStructureReduced : Prop :=
  ∀ expressions : List NormalizedExpr, WelcomePEUnrefuted expressions →
    (expressions.map NormalizedExpr.toParsed).all parsedExprIsPlainIntegerALU = false →
    (expressions.map NormalizedExpr.toParsed).any parsedExprIsPlainIntegerALU = true →
    (expressions.map NormalizedExpr.toParsed).any parsedExprIsFamilyProducer = false →
    (expressions.map NormalizedExpr.toParsed).any parsedExprIsSpecialALUProducer = false →
    ∃ (before after : List ParsedExpr) (e : ParsedExpr),
      (expressions.map NormalizedExpr.toParsed).filter
          parsedExprIsIntegerMatrixReadStageInput = before ++ e :: after ∧
      (∀ expression ∈ before, expression.op = ParsedOp.noforward ∨
        ∃ tag : Fin 256, expression.op = ParsedOp.wait tag) ∧
      (∀ expression ∈ after, expression.op = ParsedOp.noforward ∨
        ∃ tag : Fin 256, expression.op = ParsedOp.wait tag) ∧
      parsedExprIsPlainIntegerALU e = true ∧
      (e.toIssueExpr 0).writeBanks.Nodup ∧
      (((((expressions.map NormalizedExpr.toParsed).filter
              parsedExprIsIntegerMatrixReadStageInput).any
            parsedExprHasSingleLineWriteMask =
          parsedExprHasSingleLineWriteMask e) ∧
        (∀ (payload : BitVec 32) (sparse : Bool), e.op = .immediate payload sparse →
          ∀ destination ∈ e.destinations,
            ParsedOperand.directDestinationBankWidth? destination ≠
              some (PEMemory.Bank.lm1, PEMemory.Width.double))) ∨
        WelcomePEInputIndependent expressions)

/-- The writer's write banks are duplicate free, from its membership alone. -/
theorem welcomeMixed_writer_writeBanks_nodup_of_mem (expressions : List NormalizedExpr)
    (unrefuted : WelcomePEUnrefuted expressions) (e : ParsedExpr)
    (eMem : e ∈ expressions.map NormalizedExpr.toParsed) :
    (e.toIssueExpr 0).writeBanks.Nodup := by
  obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp eMem
  rw [← hget]
  exact welcomeMixed_writer_writeBanks_nodup expressions unrefuted i hi

/-- **The reduced structure from the flag agreement alone.**  Everything else is
provided by §1 (the split), §2 (the fold) and §3 (the immediate-double case). -/
theorem welcomePEMixedPlainInertStructureReduced_of_flagAgreement
    (flag : WelcomePEMixedPlainInertFlagAgreement) :
    WelcomePEMixedPlainInertStructureReduced := by
  intro expressions unrefuted notPlain plainAny noFamily noSpecial
  obtain ⟨e, eMem, ePlain, flagEq⟩ :=
    flag expressions unrefuted notPlain plainAny noFamily noSpecial
  obtain ⟨before, after, split, skipBefore, skipAfter⟩ :=
    welcomeMixed_stageInput_split expressions unrefuted noFamily noSpecial e eMem ePlain
  have intOrInert := welcomeMixed_rows_integerOrInert expressions unrefuted noFamily noSpecial
  refine ⟨before, after, e, split, ?_, ?_, ePlain,
    welcomeMixed_writer_writeBanks_nodup_of_mem expressions unrefuted e eMem, ?_⟩
  · intro expression member
    exact Or.inl (skipBefore expression member)
  · intro expression member
    exact Or.inl (skipAfter expression member)
  · rcases welcomeMixed_notDouble_or_inputIndependent expressions unrefuted intOrInert before
      after e split
      (fun expression member => Or.inl (skipBefore expression member))
      (fun expression member => Or.inl (skipAfter expression member)) with notDouble | indep
    · exact Or.inl ⟨flagEq, notDouble⟩
    · exact Or.inr indep

/-- **The reduced structure from the original one.**  The revised statement is
weaker: the original `notDouble` component is one of the disjuncts. -/
theorem welcomePEMixedPlainInertStructureReduced_of_structure
    (skeleton : WelcomePEMixedPlainInertStructure) :
    WelcomePEMixedPlainInertStructureReduced := by
  intro expressions unrefuted notPlain plainAny noFamily noSpecial
  obtain ⟨before, after, e, split, skipBefore, skipAfter, ePlain, nodup, flagEq,
    notDouble⟩ := skeleton expressions unrefuted notPlain plainAny noFamily noSpecial
  exact ⟨before, after, e, split, (fun expression member => Or.inl (skipBefore expression member)),
    (fun expression member => Or.inl (skipAfter expression member)), ePlain, nodup,
    Or.inl ⟨flagEq, notDouble⟩⟩

/-- **The mixed obligation from the reduced structure.**  In the immediate-double
branch the line is input-independent, which is the third disjunct of
`WelcomePEWriteShape`; in the other branch the writer row shape applies. -/
theorem welcomePEMixedPlainInertShapeObligation_of_reduced
    (skeleton : WelcomePEMixedPlainInertStructureReduced) :
    WelcomePEMixedPlainInertShapeObligation := by
  intro expressions unrefuted notPlain plainAny noFamily noSpecial
  obtain ⟨before, after, e, split, skipBefore, skipAfter, ePlain, nodup, shape⟩ :=
    skeleton expressions unrefuted notPlain plainAny noFamily noSpecial
  have intOrInert := welcomeMixed_rows_integerOrInert expressions unrefuted noFamily noSpecial
  rcases shape with ⟨flagEq, notDouble⟩ | indep
  · exact welcomePEWriteShape_of_plainWriter expressions unrefuted intOrInert before after e
      split skipBefore skipAfter flagEq notDouble nodup ePlain
  · exact Or.inr (Or.inr indep)

/-- **The flag agreement when inert rows carry no masked destination.**  This is
the exact content of the remaining assumption: the line flag is the writer's flag
unless some `.noforward` row of the stage carries a masked `.mem` / `.bar` /
`.omr` destination. -/
theorem welcomePEMixedPlainInertFlagAgreement_of_inertFlagsClear
    (clear : ∀ expressions : List NormalizedExpr, WelcomePEUnrefuted expressions →
      (expressions.map NormalizedExpr.toParsed).all parsedExprIsPlainIntegerALU = false →
      (expressions.map NormalizedExpr.toParsed).any parsedExprIsPlainIntegerALU = true →
      (expressions.map NormalizedExpr.toParsed).any parsedExprIsFamilyProducer = false →
      (expressions.map NormalizedExpr.toParsed).any parsedExprIsSpecialALUProducer = false →
      ∀ x ∈ (expressions.map NormalizedExpr.toParsed).filter
          parsedExprIsIntegerMatrixReadStageInput,
        x.op = ParsedOp.noforward → parsedExprHasSingleLineWriteMask x = false) :
    WelcomePEMixedPlainInertFlagAgreement := by
  intro expressions unrefuted notPlain plainAny noFamily noSpecial
  obtain ⟨e, eMem, ePlain⟩ := List.any_eq_true.mp plainAny
  obtain ⟨before, after, split, skipBefore, skipAfter⟩ :=
    welcomeMixed_stageInput_split expressions unrefuted noFamily noSpecial e eMem ePlain
  refine ⟨e, eMem, ePlain, ?_⟩
  apply welcomeMixed_flagAgreement_of_inertFlags expressions before after e split
  rw [List.any_eq_false]
  intro x hx
  have memberStage : x ∈ (expressions.map NormalizedExpr.toParsed).filter
      parsedExprIsIntegerMatrixReadStageInput := by
    rcases List.mem_append.mp hx with head | tail
    · rw [split]
      exact List.mem_append_left _ head
    · rw [split]
      exact List.mem_append_right _ (List.mem_cons_of_mem _ tail)
  have noforward : x.op = ParsedOp.noforward := by
    rcases List.mem_append.mp hx with head | tail
    · exact skipBefore x head
    · exact skipAfter x tail
  rw [clear expressions unrefuted notPlain plainAny noFamily noSpecial x memberStage noforward]
  simp

/-- **The mixed obligation from the flag agreement alone.** -/
theorem welcomePEMixedPlainInertShapeObligation_of_flagAgreement
    (flag : WelcomePEMixedPlainInertFlagAgreement) :
    WelcomePEMixedPlainInertShapeObligation :=
  welcomePEMixedPlainInertShapeObligation_of_reduced
    (welcomePEMixedPlainInertStructureReduced_of_flagAgreement flag)

/-- **The mixed obligation when inert rows carry no masked destination.** -/
theorem welcomePEMixedPlainInertShapeObligation_of_inertFlagsClear
    (clear : ∀ expressions : List NormalizedExpr, WelcomePEUnrefuted expressions →
      (expressions.map NormalizedExpr.toParsed).all parsedExprIsPlainIntegerALU = false →
      (expressions.map NormalizedExpr.toParsed).any parsedExprIsPlainIntegerALU = true →
      (expressions.map NormalizedExpr.toParsed).any parsedExprIsFamilyProducer = false →
      (expressions.map NormalizedExpr.toParsed).any parsedExprIsSpecialALUProducer = false →
      ∀ x ∈ (expressions.map NormalizedExpr.toParsed).filter
          parsedExprIsIntegerMatrixReadStageInput,
        x.op = ParsedOp.noforward → parsedExprHasSingleLineWriteMask x = false) :
    WelcomePEMixedPlainInertShapeObligation :=
  welcomePEMixedPlainInertShapeObligation_of_flagAgreement
    (welcomePEMixedPlainInertFlagAgreement_of_inertFlagsClear clear)

/-- **The aggregate after this module: eight `Prop`s plus the mask-flag
agreement imply the per-line write-shape obligation.**  The mixed component is no
longer an assumption beyond the flag agreement. -/
theorem welcomePELm1WriteShapeObligation_of_eight_and_flagAgreement
    (plain : WelcomePEPlainShapeObligation)
    (read : WelcomePEMatrixReadShapeObligation)
    (mau : WelcomePEMatrixMAUShapeObligation)
    (float : WelcomePEFloatMAUShapeObligation)
    (write : WelcomePEMatrixWriteShapeObligation)
    (l1 : WelcomePEL1ToPEShapeObligation)
    (l2 : WelcomePEL2BMShapeObligation)
    (special : WelcomePESpecialALUShapeObligation)
    (flag : WelcomePEMixedPlainInertFlagAgreement) :
    WelcomePELm1WriteShapeObligation :=
  welcomePELm1WriteShapeObligation_of_nine plain read mau float write l1 l2 special
    (welcomePEMixedPlainInertShapeObligation_of_flagAgreement flag)

/-- **The aggregate when the inert rows of mixed lines carry no masked
destination.**  This is the unconditional form of
`welcomePELm1WriteShapeObligation_of_eight_and_flagAgreement`: with the flag
agreement replaced by the (stronger, but syntactic) statement that inert rows do
not carry masked destinations, the mixed component of the aggregate is a
theorem. -/
theorem welcomePELm1WriteShapeObligation_of_eight_and_inertFlagsClear
    (plain : WelcomePEPlainShapeObligation)
    (read : WelcomePEMatrixReadShapeObligation)
    (mau : WelcomePEMatrixMAUShapeObligation)
    (float : WelcomePEFloatMAUShapeObligation)
    (write : WelcomePEMatrixWriteShapeObligation)
    (l1 : WelcomePEL1ToPEShapeObligation)
    (l2 : WelcomePEL2BMShapeObligation)
    (special : WelcomePESpecialALUShapeObligation)
    (clear : ∀ expressions : List NormalizedExpr, WelcomePEUnrefuted expressions →
      (expressions.map NormalizedExpr.toParsed).all parsedExprIsPlainIntegerALU = false →
      (expressions.map NormalizedExpr.toParsed).any parsedExprIsPlainIntegerALU = true →
      (expressions.map NormalizedExpr.toParsed).any parsedExprIsFamilyProducer = false →
      (expressions.map NormalizedExpr.toParsed).any parsedExprIsSpecialALUProducer = false →
      ∀ x ∈ (expressions.map NormalizedExpr.toParsed).filter
          parsedExprIsIntegerMatrixReadStageInput,
        x.op = ParsedOp.noforward → parsedExprHasSingleLineWriteMask x = false) :
    WelcomePELm1WriteShapeObligation :=
  welcomePELm1WriteShapeObligation_of_nine plain read mau float write l1 l2 special
    (welcomePEMixedPlainInertShapeObligation_of_inertFlagsClear clear)

/-! ## 5. What remains

The mixed plain/inert class is, after this module, reduced to exactly one
statement, `WelcomePEMixedPlainInertFlagAgreement`:

```
∀ expressions, unrefuted → not all plain → some plain → no family → no special →
  ∃ e ∈ line, parsedExprIsPlainIntegerALU e = true ∧
    (line.filter parsedExprIsIntegerMatrixReadStageInput).any
        parsedExprHasSingleLineWriteMask =
      parsedExprHasSingleLineWriteMask e
```

The two other blockers of `WelcomeWriterShape.lean` §8 are theorems:

* the **list split** — `welcomeMixed_stageInput_split` (§1), with the executor
  interaction `prepareParsedIntegerMatrixReadLineExpressions_split` and
  `welcomeMixed_integerPrep_single_writer` (§2);
* the **immediate-double case** — `welcomePEMixedImmediateDouble_inputIndependent`
  (§3), which also removes the `notDouble` field of the structure statement
  through `welcomeMixed_notDouble_or_inputIndependent` (§4).  The removal is
  forced: in that case `notDouble` is false, so
  `WelcomePEMixedPlainInertStructure` itself is refuted
  (`welcomePEMixedPlainInertStructure_forbids_immediateDouble`).

By `welcomeMixed_flagAgreement_fails_iff` the flag agreement fails exactly when
the writer's own flag is `false` and an inert row of the line carries a masked
`.mem` / `.bar` / `.omr` destination operand, which the issue checker does not
forbid; when no inert row carries such a destination the mixed obligation is
discharged outright
(`welcomePEMixedPlainInertShapeObligation_of_inertFlagsClear`).  The remaining
case cannot be replaced by a syntactic argument: the flag changes which masked
lowering of the plain row fires.  Closing it means redoing the per-branch
analysis of `WelcomePlainStep.lean` with a free flag (or proving that the
flag-`true` lowering of a plain row with no masked destination of its own still
has the double-copy-or-narrow shape).  This module does not assume it.

No `LowerBound 2` and no `Optimal` is claimed. -/

end ProofsLean.MNCore
