import ProofsLean.WelcomeMixedStructure

/-! # The mixed plain/inert mask-flag agreement is **false**

`WelcomeMixedStructure.lean` §4 isolates the last syntactic blocker of the mixed
plain/inert class as `WelcomePEMixedPlainInertFlagAgreement`:

```
∀ expressions, unrefuted → not all plain → some plain → no family → no special →
  ∃ e ∈ line, parsedExprIsPlainIntegerALU e = true ∧
    (line.filter parsedExprIsIntegerMatrixReadStageInput).any
        parsedExprHasSingleLineWriteMask =
      parsedExprHasSingleLineWriteMask e
```

The statement asks the *line* mask flag of the integer stage's row list to be
the *writer row's own* mask flag.  This module refutes it.

* **§1 the witness line.**  A two-row mixed line, unrefuted under the issue
  checker:
  * `welcomeFlagAgreementPlainWitness` — a plain `.zero` row whose single
    destination is the unmasked `.mem` access
    `Issue.plusOneAccess .lm1 0` (a two-word `.long` LM1 store), so its own flag
    `parsedExprHasSingleLineWriteMask` is `false`;
  * `welcomeFlagAgreementInertWitness` — a `.noforward` row whose destination is
    a masked `.mem` access to `LM0`, so its own flag is `true` and it makes the
    line flag `true` (`welcomeFlagAgreementWitness_lineFlag`).

  Both rows pass the integer-stage filter, so the filtered row list is the whole
  line.  The line is accepted by `checkParsedTopLine`
  (`welcomeFlagAgreementWitness_check`, through `LegalParsedLine`), has no
  pending wait tag, no Rust-unsupported ALU and only supported producers; hence
  `WelcomePEUnrefuted` (`welcomeFlagAgreementWitness_unrefuted`).

* **§2 the structural reason.**  For *any* unrefuted line, a plain row `e` whose
  own flag is `false` together with a line flag of `true` admits no plain row
  satisfying the flag equation: the plain row of a legal line is unique
  (`plain_rows_at_most_one_eq`, packaged as `welcomeMixed_plain_writer_unique`),
  so the only candidate is `e` itself, whose flag is `false`
  (`welcomeMixed_no_plainWriter_flagAgreement`).  The witness instantiates the
  hypotheses of that lemma, which is exactly the failure condition characterised
  by `welcomeMixed_flagAgreement_fails_iff`: the writer's flag is `false` and an
  inert row of the stage carries a masked `.mem` / `.bar` / `.omr` destination.

* **§3 the negation.**  `welcomePEMixedPlainInertFlagAgreement_false`.

* **§4 the witness still satisfies the write shape.**  At the line flag the
  plain writer prepares four `.lm1 .long` writes at addresses `0, 2, 4, 6`
  (`welcomeFlagAgreementWitness_prepDestinations`), i.e. four two-word windows,
  so `Lm1WritesNarrow` holds (`welcomeFlagAgreementWitness_rowNarrow`) and the
  line satisfies `WelcomePEWriteShape` (`welcomeFlagAgreementWitness_writeShape`,
  through `welcomePEWriteShape_of_integerStageWriter`).

* **§5 the witness also satisfies the reduced structure's body.**  The writer is
  a constant `.zero` row, so the line is input-independent
  (`welcomeFlagAgreementWitness_inputIndependent`, through
  `welcomePEMixedConstantWriter_inputIndependent`), which is the second disjunct
  of `WelcomePEMixedPlainInertStructureReduced` at this line
  (`welcomeFlagAgreementWitness_reducedStructureBody`).

The refutation therefore hits the *intermediate* flag equation only: the witness
is a positive instance of `WelcomePEMixedPlainInertShapeObligation` and of the
reduced structure statement, not a counterexample to either.

## Consequences

* `welcomePEMixedPlainInertStructureReduced_of_flagAgreement` and
  `welcomePELm1WriteShapeObligation_of_eight_and_flagAgreement` are *not*
  vacuous theorems, but their hypothesis is unsatisfiable, so they do not
  produce `WelcomePEMixedPlainInertShapeObligation`.  The aggregate
  `welcomePELm1WriteShapeObligation_of_eight_and_inertFlagsClear` (inert rows of
  mixed lines carry no masked destination) is unaffected and remains the usable
  conditional route of `WelcomeMixedStructure.lean`.
* The failure is exactly the gap between the two flags.  On the witness the gap
  is harmless for both the write shape (§4) and the reduced structure (§5); what
  is missing is the *line-flag* plain row shape (below), not a correction of the
  witness.

## What would still close the mixed class

The plain row's shape lemma `plainRow_lm1_shape` of `WelcomeWriterShape.lean` is
stated and proved at the row's own flag (`parsedExprHasSingleLineWriteMask e`,
fixed throughout `prepareParsedIntegerALUExprCycle_lm1_facts`).  Replacing the
flag agreement requires a *line-flag* plain row shape: for a plain row all of
whose destinations are unmasked (own flag `false`), the four-cycle preparation
at `hasSingleLineMask = true` must still satisfy
`Lm1WritesDoubleCopy writes ∨ Lm1WritesNarrow writes`.  The flag enters that
preparation in the lowering predicates and in the selection resolvers: for an
unmasked `.mem` / `.bar` / `.omr` operand,
`resolveMemoryWriteSelection?` / `resolveOmrWriteSelection?` return the
`allOnes`/`true` selection instead of the directive selection.  The missing work
is therefore the per-branch analysis of
`prepareParsedIntegerALUExprCycle_lm1_facts` with the flag free.  This module
does not assume or prove it.

No `sorry`, no `admit`, no `native_decide`, no new axioms.  `LowerBound 2` and
`Optimal` are not claimed.
-/

namespace ProofsLean.MNCore

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

open Issue
open PEMemory

/-! ## 1. The witness line

The two rows are chosen so that every legality field of the issue checker is
immediate: the writer's only write bank is `.lm1`, the inert row's is `.lm0`,
both rows are duplicate-free, and there is at most one mask application (on the
inert row), no bar write, no OMR write, no read and no flush.  The inert row's
masked `.mem` destination is what the issue checker does not forbid. -/

/-- The plain writer of the witness line: a `.zero` row storing to an unmasked
two-word `.long` LM1 destination.  Its own single-line mask flag is `false`. -/
def welcomeFlagAgreementPlainWitness : NormalizedExpr where
  op := .zero
  sources := []
  destinations := [.mem (Issue.plusOneAccess .lm1 0) false false false none]
  flush := none

/-- The inert row of the witness line: a `.noforward` row with a masked `.mem`
destination in `LM0`.  Its own single-line mask flag is `true`, and it survives
the integer-stage filter. -/
def welcomeFlagAgreementInertWitness : NormalizedExpr where
  op := .noforward
  sources := []
  destinations := [.mem (Issue.plusOneAccess .lm0 0) false false false
    (some (.pattern false 0))]
  flush := none

/-- The issue projection of the witness's plain writer. -/
def welcomeFlagAgreementWriterExpr : Issue.Expr :=
  { id := 0, group := some Group.alu, mau := none, secondSource := none,
    matrixWriteSource := none, reads := [],
    writes := [plusOneAccess Issue.Bank.lm1 0], barWrites := [],
    omrWrites := [], lbfWrites := 0, nowriteOutputValid := true,
    matrixXUses := 0, matrixYUses := 0, maskApplications := [],
    immediate := false, zeroFlush := false }

/-- The issue projection of the witness's inert row. -/
def welcomeFlagAgreementInertExpr : Issue.Expr :=
  { id := 1, group := some Group.noforward, mau := none, secondSource := none,
    matrixWriteSource := none, reads := [],
    writes := [plusOneAccess Issue.Bank.lm0 0], barWrites := [],
    omrWrites := [], lbfWrites := 0, nowriteOutputValid := true,
    matrixXUses := 0, matrixYUses := 0,
    maskApplications := [ParsedMask.pattern false 0], immediate := false,
    zeroFlush := false }

/-- The witness expression list, in the exact form used by the issue projection
and by the integer stage. -/
abbrev welcomeFlagAgreementWitnessLine : List NormalizedExpr :=
  [welcomeFlagAgreementPlainWitness, welcomeFlagAgreementInertWitness]

/-- The issue projection of the witness line is the two explicit records. -/
theorem welcomeFlagAgreementWitness_projection :
    projectLine (welcomeFlagAgreementWitnessLine.map NormalizedExpr.toParsed) =
      [welcomeFlagAgreementWriterExpr, welcomeFlagAgreementInertExpr] := by
  rfl

/-- **The witness line is legal under the issue checker.**  This is the full
`Legal` record on the projected line: ids are unique, the groups differ
(`.alu` versus `.noforward`), no row has an MAU or matrix record, the only two
write banks are `.lm1` and `.lm0`, both write lists are duplicate free, and there
is no bar write, no OMR write, no read and no flush. -/
theorem welcomeFlagAgreementWitness_legalExprs :
    Legal [welcomeFlagAgreementWriterExpr, welcomeFlagAgreementInertExpr] := by
  unfold Legal
  simp [idsUnique, groupsUnique, mauExpressions, mauCountBounded, mauPrecisionsAgree,
    matrixWritePairAgrees, matrixRegistersUnique, writesUnique, barWritesExcludeReads,
    readsAgree, localReadWriteAgree, immediateExcludesLm0, zeroFlushUnique,
    maskWidthsAgree, maskEntriesAgree, nowriteOutputsUnique, lbfWritesUnique,
    maskRegisterWritesUnique, welcomeFlagAgreementWriterExpr,
    welcomeFlagAgreementInertExpr, Expr.writeBanks, ParsedMask.variableEntry?,
    List.filterMap_cons, List.filterMap_nil, plusOneAccess]

/-- The witness line is a `LegalParsedLine`. -/
theorem welcomeFlagAgreementWitness_legalParsedLine :
    LegalParsedLine
      (welcomeFlagAgreementWitnessLine.map NormalizedExpr.toParsed) := by
  unfold LegalParsedLine
  rw [welcomeFlagAgreementWitness_projection]
  exact welcomeFlagAgreementWitness_legalExprs

/-- The witness line is accepted by the executable issue checker. -/
theorem welcomeFlagAgreementWitness_check :
    checkParsedTopLine (InstructionLine.pe welcomeFlagAgreementWitnessLine).toParsed =
      true := by
  have accepted := parsed_topline_check_complete
    (.pe (welcomeFlagAgreementWitnessLine.map NormalizedExpr.toParsed))
    welcomeFlagAgreementWitness_legalParsedLine
  simpa [InstructionLine.toParsed, welcomeFlagAgreementWitnessLine] using accepted

/-! ### The flags of the witness -/

/-- The plain writer's own single-line mask flag is `false`: its destination
operand carries no mask. -/
theorem welcomeFlagAgreementWitness_plainFlag :
    parsedExprHasSingleLineWriteMask welcomeFlagAgreementPlainWitness.toParsed =
      false := by
  decide

/-- The inert row's own single-line mask flag is `true`. -/
theorem welcomeFlagAgreementWitness_inertFlag :
    parsedExprHasSingleLineWriteMask welcomeFlagAgreementInertWitness.toParsed =
      true := by
  decide

/-- The plain writer is plain. -/
theorem welcomeFlagAgreementWitness_plain :
    parsedExprIsPlainIntegerALU welcomeFlagAgreementPlainWitness.toParsed = true := by
  decide

/-- The inert row is not plain. -/
theorem welcomeFlagAgreementWitness_inertNotPlain :
    parsedExprIsPlainIntegerALU welcomeFlagAgreementInertWitness.toParsed = false := by
  decide

/-- Both witness rows survive the integer-stage filter, so the stage's row list
is the whole line. -/
theorem welcomeFlagAgreementWitness_stageInput :
    (welcomeFlagAgreementWitnessLine.map NormalizedExpr.toParsed).filter
        parsedExprIsIntegerMatrixReadStageInput =
      welcomeFlagAgreementWitnessLine.map NormalizedExpr.toParsed := by
  decide

/-- **The line flag of the witness is `true`**, because of the inert row's masked
destination, while the writer's own flag is `false`
(`welcomeFlagAgreementWitness_plainFlag`). -/
theorem welcomeFlagAgreementWitness_lineFlag :
    ((welcomeFlagAgreementWitnessLine.map NormalizedExpr.toParsed).filter
        parsedExprIsIntegerMatrixReadStageInput).any
        parsedExprHasSingleLineWriteMask = true := by
  decide

/-! ### The witness line is unrefuted -/

theorem welcomeFlagAgreementWitness_notAllNoForward :
    ¬ WelcomeAllNoForward welcomeFlagAgreementWitnessLine := by
  intro all
  have zero := all welcomeFlagAgreementPlainWitness.toParsed (by simp
    [welcomeFlagAgreementWitnessLine])
  exact absurd zero (by decide)

theorem welcomeFlagAgreementWitness_notSingleWelcome :
    ¬ WelcomeSingleWelcomeLine welcomeFlagAgreementWitnessLine := by
  rintro ⟨base, equal⟩
  have length := congrArg List.length equal
  simp [welcomeFlagAgreementWitnessLine] at length

/-- **The witness line is unrefuted.**  It is accepted by the issue checker, is
not all-`.noforward` (the `.zero` writer) and is not a single Welcome `iinc`
line (it has two rows). -/
theorem welcomeFlagAgreementWitness_unrefuted :
    WelcomePEUnrefuted welcomeFlagAgreementWitnessLine := by
  refine ⟨⟨welcomeFlagAgreementWitness_check, ?_, ?_, ?_⟩,
    welcomeFlagAgreementWitness_notAllNoForward,
    welcomeFlagAgreementWitness_notSingleWelcome⟩
  · decide
  · decide
  · decide

/-! ### The hypotheses of the flag agreement at the witness -/

theorem welcomeFlagAgreementWitness_notAllPlain :
    (welcomeFlagAgreementWitnessLine.map NormalizedExpr.toParsed).all
        parsedExprIsPlainIntegerALU = false := by
  decide

theorem welcomeFlagAgreementWitness_somePlain :
    (welcomeFlagAgreementWitnessLine.map NormalizedExpr.toParsed).any
        parsedExprIsPlainIntegerALU = true := by
  decide

theorem welcomeFlagAgreementWitness_noFamily :
    (welcomeFlagAgreementWitnessLine.map NormalizedExpr.toParsed).any
        parsedExprIsFamilyProducer = false := by
  decide

theorem welcomeFlagAgreementWitness_noSpecial :
    (welcomeFlagAgreementWitnessLine.map NormalizedExpr.toParsed).any
        parsedExprIsSpecialALUProducer = false := by
  decide

/-! ## 2. The structural reason

The failure is not an artefact of the particular witness.  In any unrefuted
line, if the (unique) plain row's own flag is `false` and the line flag is
`true`, no plain row can satisfy the flag equation.  This is precisely the
failure condition of `welcomeMixed_flagAgreement_fails_iff`: a masked
`.mem`/`.bar`/`.omr` destination on an inert row of the stage. -/

/-- **No plain row satisfies the flag equation when the writer's flag is `false`
and the line flag is `true`.**  A legal line has at most one plain row
(`welcomeMixed_plain_writer_unique`), so every plain candidate is `e` itself,
where the two flags are unequal. -/
theorem welcomeMixed_no_plainWriter_flagAgreement
    (expressions : List NormalizedExpr) (unrefuted : WelcomePEUnrefuted expressions)
    (e : ParsedExpr) (eMem : e ∈ expressions.map NormalizedExpr.toParsed)
    (ePlain : parsedExprIsPlainIntegerALU e = true)
    (eFlag : parsedExprHasSingleLineWriteMask e = false)
    (lineFlag : ((expressions.map NormalizedExpr.toParsed).filter
        parsedExprIsIntegerMatrixReadStageInput).any
        parsedExprHasSingleLineWriteMask = true) :
    ¬ ∃ e' : ParsedExpr, e' ∈ expressions.map NormalizedExpr.toParsed ∧
      parsedExprIsPlainIntegerALU e' = true ∧
      ((expressions.map NormalizedExpr.toParsed).filter
          parsedExprIsIntegerMatrixReadStageInput).any
          parsedExprHasSingleLineWriteMask =
        parsedExprHasSingleLineWriteMask e' := by
  rintro ⟨e', e'Mem, e'Plain, flagEq⟩
  have same : e' = e :=
    welcomeMixed_plain_writer_unique expressions unrefuted e' e e'Mem eMem e'Plain ePlain
  subst same
  rw [lineFlag, eFlag] at flagEq
  exact absurd flagEq (by decide)

/-! ## 3. The negation of `WelcomePEMixedPlainInertFlagAgreement` -/

/-- **The mask-flag agreement of `WelcomeMixedStructure.lean` §4 is false.**

The witness line (a plain `.zero` row with an unmasked `.lm1` destination,
followed by a `.noforward` row with a masked `.lm0` `.mem` destination) is
unrefuted, is mixed (one plain row, one inert row), and has no family or
special-ALU row.  Its line flag is `true` (the inert row's masked destination)
while the unique plain row's own flag is `false`, so the existential of the
agreement has no witness. -/
theorem welcomePEMixedPlainInertFlagAgreement_false :
    ¬ WelcomePEMixedPlainInertFlagAgreement := by
  intro agreement
  have body := agreement welcomeFlagAgreementWitnessLine
    welcomeFlagAgreementWitness_unrefuted welcomeFlagAgreementWitness_notAllPlain
    welcomeFlagAgreementWitness_somePlain welcomeFlagAgreementWitness_noFamily
    welcomeFlagAgreementWitness_noSpecial
  exact welcomeMixed_no_plainWriter_flagAgreement welcomeFlagAgreementWitnessLine
    welcomeFlagAgreementWitness_unrefuted welcomeFlagAgreementPlainWitness.toParsed
    (by simp [welcomeFlagAgreementWitnessLine]) welcomeFlagAgreementWitness_plain
    welcomeFlagAgreementWitness_plainFlag welcomeFlagAgreementWitness_lineFlag body

/-! ## 4. The witness still satisfies the write shape

The refuted Prop is only the intermediate flag equation.  At the *line* flag
`true` the plain witness row writes four `.lm1 .long` (two-word) windows at
addresses `0, 2, 4, 6`, so the narrow form holds and the witness line is a
positive instance of `WelcomePEWriteShape`, not a counterexample to
`WelcomePEMixedPlainInertShapeObligation`.  This is the concrete form of the
remark that the flag gap changes the lowering *selection*, not the destination
geometry of a `.zero` row. -/

/-- The prepared write list of the plain witness row at the line flag, at the
all-zero initial state, projected to its destinations.  The four destinationless
entries are the constant branch's producer writes. -/
theorem welcomeFlagAgreementWitness_prepDestinations :
    (match prepareParsedIntegerMatrixReadLineExpression welcomeZeroFiles welcomeZeroSlots
        welcomeZeroSlots welcomeZeroMatrixStore welcomeFlagAgreementPlainWitness.toParsed
        welcomeZeroControl true true false with
      | .ok (writes, _, _) => writes.map (fun write => write.destination)
      | _ => []) =
      [some ⟨PEMemory.Bank.lm1, PEMemory.Width.long, ⟨0, by decide⟩⟩, none,
       some ⟨PEMemory.Bank.lm1, PEMemory.Width.long, ⟨2, by decide⟩⟩, none,
       some ⟨PEMemory.Bank.lm1, PEMemory.Width.long, ⟨4, by decide⟩⟩, none,
       some ⟨PEMemory.Bank.lm1, PEMemory.Width.long, ⟨6, by decide⟩⟩, none] := by
  decide

/-- **The plain witness row is narrow at the line flag.**  Every `.lm1`
destination of the prepared list is one of the four two-word windows
`(0, 2), (2, 2), (4, 2), (6, 2)`. -/
theorem welcomeFlagAgreementWitness_rowNarrow
    (writes : List PreparedParsedMaskedWrite)
    (slots : ProofsLean.MNCore.Forwarding.Slots)
    (bars : List (Bool × BitVec 12))
    (prep : prepareParsedIntegerMatrixReadLineExpression welcomeZeroFiles welcomeZeroSlots
      welcomeZeroSlots welcomeZeroMatrixStore welcomeFlagAgreementPlainWitness.toParsed
      welcomeZeroControl true true false = .ok (writes, slots, bars)) :
    Lm1WritesNarrow writes := by
  have destinations : writes.map (fun write => write.destination) =
      [some ⟨PEMemory.Bank.lm1, PEMemory.Width.long, ⟨0, by decide⟩⟩, none,
       some ⟨PEMemory.Bank.lm1, PEMemory.Width.long, ⟨2, by decide⟩⟩, none,
       some ⟨PEMemory.Bank.lm1, PEMemory.Width.long, ⟨4, by decide⟩⟩, none,
       some ⟨PEMemory.Bank.lm1, PEMemory.Width.long, ⟨6, by decide⟩⟩, none] := by
    have := welcomeFlagAgreementWitness_prepDestinations
    rw [prep] at this
    simpa using this
  refine ⟨[(⟨0, by decide⟩, 2), (⟨2, by decide⟩, 2), (⟨4, by decide⟩, 2),
    (⟨6, by decide⟩, 2)], ?_, by decide, by decide⟩
  intro write member width address destinationEq
  have inDestinations : write.destination ∈
      [some ⟨PEMemory.Bank.lm1, PEMemory.Width.long, ⟨0, by decide⟩⟩, none,
       some ⟨PEMemory.Bank.lm1, PEMemory.Width.long, ⟨2, by decide⟩⟩, none,
       some ⟨PEMemory.Bank.lm1, PEMemory.Width.long, ⟨4, by decide⟩⟩, none,
       some ⟨PEMemory.Bank.lm1, PEMemory.Width.long, ⟨6, by decide⟩⟩, none] := by
    rw [← destinations]
    exact List.mem_map_of_mem member
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at inDestinations
  rcases inDestinations with h | h | h | h | h | h | h | h
  all_goals rw [h] at destinationEq
  all_goals cases destinationEq
  all_goals decide

/-- **The witness line satisfies `WelcomePEWriteShape`.**  Its integer stage is
the whole line and its only prepared write bank is the narrow `.lm1` window of
`welcomeFlagAgreementWitness_rowNarrow`. -/
theorem welcomeFlagAgreementWitness_writeShape :
    WelcomePEWriteShape welcomeFlagAgreementWitnessLine := by
  refine welcomePEWriteShape_of_integerStageWriter welcomeFlagAgreementWitnessLine
    welcomeFlagAgreementWitness_unrefuted ?_ [] [welcomeFlagAgreementInertWitness.toParsed]
    welcomeFlagAgreementPlainWitness.toParsed ?_ ?_ ?_ ?_
  · decide
  · rw [welcomeFlagAgreementWitness_stageInput]
    rfl
  · simp
  · intro expression member
    simp only [List.mem_singleton] at member
    subst member
    exact Or.inl rfl
  · intro writes slots bars prep
    change prepareParsedIntegerMatrixReadLineExpression welcomeZeroFiles welcomeZeroSlots
        welcomeZeroSlots welcomeZeroMatrixStore welcomeFlagAgreementPlainWitness.toParsed
        welcomeZeroControl true true false = StepResult.ok (writes, slots, bars) at prep
    exact Or.inr (welcomeFlagAgreementWitness_rowNarrow writes slots bars prep)

/-! ## 5. The reduced structure's body at the witness

The writer is a constant `.zero` row, so round 40's constant-writer comparison
(`welcomePEMixedConstantWriter_inputIndependent`) applies: the line is
input-independent, which supplies the second disjunct of
`WelcomePEMixedPlainInertStructureReduced` where the (false) flag-equality
disjunct cannot. -/

/-- **The witness line is input-independent.**  A `.zero` writer's output does
not read the operand buses, and the inert row prepares nothing, so the all-zero
and all-five runs commit the same write list. -/
theorem welcomeFlagAgreementWitness_inputIndependent :
    WelcomePEInputIndependent welcomeFlagAgreementWitnessLine := by
  refine welcomePEMixedConstantWriter_inputIndependent welcomeFlagAgreementWitnessLine
    welcomeFlagAgreementWitness_unrefuted ?_ [] [welcomeFlagAgreementInertWitness.toParsed]
    welcomeFlagAgreementPlainWitness.toParsed ?_ ?_ ?_ (Or.inl rfl)
  · decide
  · rw [welcomeFlagAgreementWitness_stageInput]
    rfl
  · simp
  · intro expression member
    simp only [List.mem_singleton] at member
    subst member
    exact Or.inl rfl

/-- **The body of `WelcomePEMixedPlainInertStructureReduced` holds at the
witness line.**  The reduced statement's disjunction is satisfied through
`WelcomePEInputIndependent`, not through the flag equation. -/
theorem welcomeFlagAgreementWitness_reducedStructureBody :
    ∃ (before after : List ParsedExpr) (e : ParsedExpr),
      (welcomeFlagAgreementWitnessLine.map NormalizedExpr.toParsed).filter
          parsedExprIsIntegerMatrixReadStageInput = before ++ e :: after ∧
      (∀ expression ∈ before, expression.op = ParsedOp.noforward ∨
        ∃ tag : Fin 256, expression.op = ParsedOp.wait tag) ∧
      (∀ expression ∈ after, expression.op = ParsedOp.noforward ∨
        ∃ tag : Fin 256, expression.op = ParsedOp.wait tag) ∧
      parsedExprIsPlainIntegerALU e = true ∧
      (e.toIssueExpr 0).writeBanks.Nodup ∧
      (((((welcomeFlagAgreementWitnessLine.map NormalizedExpr.toParsed).filter
              parsedExprIsIntegerMatrixReadStageInput).any
            parsedExprHasSingleLineWriteMask =
          parsedExprHasSingleLineWriteMask e) ∧
        (∀ (payload : BitVec 32) (sparse : Bool), e.op = .immediate payload sparse →
          ∀ destination ∈ e.destinations,
            ParsedOperand.directDestinationBankWidth? destination ≠
              some (PEMemory.Bank.lm1, PEMemory.Width.double))) ∨
        WelcomePEInputIndependent welcomeFlagAgreementWitnessLine) := by
  refine ⟨[], [welcomeFlagAgreementInertWitness.toParsed],
    welcomeFlagAgreementPlainWitness.toParsed, ?_, ?_, ?_,
    welcomeFlagAgreementWitness_plain, ?_,
    Or.inr welcomeFlagAgreementWitness_inputIndependent⟩
  · rw [welcomeFlagAgreementWitness_stageInput]
    rfl
  · simp
  · intro expression member
    simp only [List.mem_singleton] at member
    subst member
    exact Or.inl rfl
  · decide

end ProofsLean.MNCore
