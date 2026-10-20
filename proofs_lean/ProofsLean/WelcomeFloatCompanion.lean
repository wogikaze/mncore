import ProofsLean.WelcomeAssemblyFinal
import ProofsLean.WelcomeFloatProvenance

/-! # Writer packages that tolerate a `.lm1`-free float-MAU companion

Round 49 left four per-line writer-kind data packages as hypotheses of
`WelcomePELm1WriteShapeObligation`.  Three of them — the plain, the `.matrixRead`
and the `.l1bm` broadcast package — demanded that the line have **no** float-MAU
row at all:

```
(expressions.map NormalizedExpr.toParsed).filter
  parsedExprIsSupportedFloatMAUProducer = []
```

That requirement is stronger than the proofs need.  The float-MAU stage is
executed *inside* the integer stage; the PE 0 file it commits is

```
commitParsedMaskedWrites welcomeZeroFiles (intWrites ++ floatWrites)
```

(`executeIntegerProducerLineAtPEs_zero_prepared_float_clean`,
`WelcomeFloatProvenance.lean`), and the shape algebra only needs the float half to
be `.lm1`-free: `lm1WritesShape_append_free_suffix` appends an `.lm1`-free
suffix to the integer half's shape.  This module replaces the empty-float
requirement of the three packages by the row-local statement

```
floatFreeRows : ∀ e ∈ line.filter parsedExprIsSupportedFloatMAUProducer,
  WelcomeRowHasNoLm1Destination e
```

and proves that the old packages imply the new ones (the conservative
direction).  It additionally observes that for these three writer kinds
`floatFreeRows` is *automatic*: the writer `e` is not a float-MAU producer, and
`welcomeLm1Writer_rows` says every other row of an unrefuted line has no `.lm1`
destination operand.  Therefore the new packages can drop the float condition
entirely; the versions with `floatFreeRows` are recorded as the intermediate
form requested by the brief, and the strongest form is
`WelcomePEPlainWriterDataForNoFloat` / `WelcomePEMatrixReadWriterDataForNoFloat` /
`WelcomePEL1BMWriterDataForNoFloat`.

## What this module proves

* §1 one generic assembly lemma `welcomePEWriteShape_of_floatRows_intShape`: an
  `.lm1`-free float half plus the integer half's shape give the line shape;
* §2 the two arbitrary-companion dispatch theorems with `floatFreeRows` in place
  of `floatEmpty`
  (`welcomePEWriteShape_of_plainWriter_arbitrary_floatRows`,
  `welcomePEWriteShape_of_matrixReadWriter_arbitrary_floatRows`), patterned on the
  special-ALU proofs of `WelcomeResiduals.lean` /
  `WelcomeHalfBlockFloat.lean`; the `.l1bm` case reuses
  `welcomePEWriteShape_of_l1bmWriter_unique_of_floatRows`;
* §3 the three row-local packages and their `...NoFloat` forms, the per-line
  shape theorems, and the equivalence of the two forms on an unrefuted line;
* §4 the conservative direction: the round-49 packages imply the row-local ones,
  which imply the `...NoFloat` ones;
* §5 the assembly: the write-shape obligation from the three new packages and
  the unchanged float-MAU package.

## The remainder

The float-MAU writer package of `WelcomeFinalShape.lean`
(`WelcomePEFloatMAUWriterData`: the float filter is the writer alone and every
integer-stage row is `.noforward`) is **not** addressed here.  The plain package
still carries the immediate-`.double` exclusion (or input independence), the
`.matrixRead` package the writer's `.matrixRead` shape, its matrix source and
its static `.lm1` width, and the `.l1bm` package the lowering to one masked
`.mem .lm1` destination together with the singleton L1-to-PE filter.  Therefore
this module does **not** claim
`LowerBound 2` or `Optimal`; the assembled obligation remains conditional on
those packages exactly as in `WelcomeAssemblyFinal.lean`.  The gain is that the
empty-float hypothesis is gone from three of the four packages, and that for
those three it is now derived rather than assumed.

No `sorry`, no `admit`, no `native_decide`, no new axioms, and no existing module
is edited by this file.
-/

namespace ProofsLean.MNCore

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open Issue
open PEMemory

/-! ## 1. The integer half plus an `.lm1`-free float half

`WelcomeFloatProvenance.lean` proves the four `_floatRows` dispatch theorems by
extracting `intWrites ++ floatWrites` from the PE 0 walk and appending the
`.lm1`-free float half to the integer shape.  The integer half's shape is
writer-kind specific; the rest of the assembly (the five middle stages, the L1
stage, the shared-block frame and the commit split) is identical.  The lemma
below factors that common part out: it takes the integer shape as a function of
the prepared list and does everything else. -/

/-- **The line shape from an `.lm1`-free float half and the integer half's
shape.**  `intShape` must prove the shape of `welcomeIntegerPrep`'s write list
(the `.lm1`-free float half is appended by this lemma). -/
theorem welcomePEWriteShape_of_floatRows_intShape
    (expressions : List NormalizedExpr)
    (floatFreeRows : ∀ expression ∈ (expressions.map NormalizedExpr.toParsed).filter
        parsedExprIsSupportedFloatMAUProducer, WelcomeRowHasNoLm1Destination expression)
    (middleFree : WelcomePEMiddleStageLm1Free expressions)
    (matrixFreeRows : WelcomePEMatrixMAUStageLm1Free expressions)
    (l1FreeRows : WelcomePEL1StageLm1Free expressions)
    (intShape : ∀ (intWrites : List PreparedParsedMaskedWrite)
        (intSlots : ProofsLean.MNCore.Forwarding.Slots)
        (intBars : List (Bool × BitVec 12)),
      welcomeIntegerPrep (welcomeInitialState welcomeZeroWords) welcomePE
        (welcomePEWalkFilter expressions) = .ok (intWrites, intSlots, intBars) →
      Lm1WritesShape intWrites) :
    WelcomePEWriteShape expressions := by
  apply welcomePEWriteShape_of_commit_shape
  intro next step
  have executed := welcomeSealed_step_ok step
  simp only [executeNormalizedLine, NormalizedLine.toInstruction?,
    Issue.InstructionLine.toNormalizedLine] at executed
  obtain ⟨accepted, waits, unsupported, supported⟩ :=
    executeIntegerProducerInstructionLine_pe_conditions expressions
      (welcomeInitialState welcomeZeroWords) next executed
  obtain ⟨nextPEs, nextMsl, nextRelu, nextBlockFloat, afterMatrix, nextShared, nextBroadcast,
    walkExecuted, mslExecuted, reluExecuted, blockExecuted, matrixExecuted, sharedExecuted,
    l1Executed, nextEq⟩ :=
    executeIntegerProducerInstructionLine_pe_stages_exists expressions
      (welcomeInitialState welcomeZeroWords) next accepted waits unsupported supported executed
  have floatFreeWalk : ∀ expression ∈ (welcomePEWalkFilter expressions).filter
      parsedExprIsSupportedFloatMAUProducer, WelcomeRowHasNoLm1Destination expression := by
    intro expression member
    exact floatFreeRows expression (by rw [welcomePEWalkFilter_float] at member; exact member)
  obtain ⟨intWrites, floatWrites, intSlots, intBars, intPrep, intCommit, floatFree⟩ :=
    executeIntegerProducerLineAtPEs_zero_prepared_float_clean (welcomePEWalkFilter expressions)
      nextPEs floatFreeWalk walkExecuted
  have combinedShape : Lm1WritesShape (intWrites ++ floatWrites) :=
    lm1WritesShape_append_free_suffix intWrites floatWrites
      (intShape intWrites intSlots intBars intPrep) floatFree
  obtain ⟨mslWrites, mslCommit, mslFree⟩ :=
    welcomePEMslMsrStageLm1Provenance (welcomeInitialState welcomeZeroWords) nextPEs nextMsl
      (expressions.map NormalizedExpr.toParsed)
      (expressions.any (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed))
      (expressions.any (parsedExprHasSingleLineWriteMask ∘ NormalizedExpr.toParsed))
      (welcomePEMiddleStageLm1Free_msl expressions middleFree) mslExecuted
  obtain ⟨reluWrites, reluCommit, reluFree⟩ :=
    welcomePEFloatReluStageLm1Provenance (welcomeInitialState welcomeZeroWords) nextMsl nextRelu
      (expressions.map NormalizedExpr.toParsed)
      (expressions.any (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed))
      (expressions.any (parsedExprHasSingleLineWriteMask ∘ NormalizedExpr.toParsed))
      (welcomePEMiddleStageLm1Free_relu expressions middleFree) reluExecuted
  obtain ⟨blockWrites, blockCommit, blockFree⟩ :=
    welcomePEBlockFloatStageLm1Provenance (welcomeInitialState welcomeZeroWords) nextRelu
      nextBlockFloat (expressions.map NormalizedExpr.toParsed)
      (expressions.any (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed))
      (expressions.any (parsedExprHasSingleLineWriteMask ∘ NormalizedExpr.toParsed))
      (welcomePEMiddleStageLm1Free_block expressions middleFree) blockExecuted
  obtain ⟨matrixWrites, matrixCommit, matrixFree⟩ :=
    welcomePEMatrixMAUStageLm1Provenance (welcomeInitialState welcomeZeroWords) nextBlockFloat
      afterMatrix (expressions.map NormalizedExpr.toParsed)
      (expressions.any (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed))
      (expressions.any (parsedExprHasSingleLineWriteMask ∘ NormalizedExpr.toParsed))
      (welcomePEMiddleStageLm1Free_matrixMAU expressions matrixFreeRows) matrixExecuted
  obtain ⟨l1Writes, l1Commit, l1Free⟩ :=
    welcomePEL1ToPEStageLm1Provenance (welcomeInitialState welcomeZeroWords) nextShared
      nextBroadcast (expressions.map NormalizedExpr.toParsed)
      (expressions.any (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed))
      (expressions.any (parsedExprHasSingleLineWriteMask ∘ NormalizedExpr.toParsed))
      (parsedL1ToPEPrecedesOMRWriter (expressions.map NormalizedExpr.toParsed))
      (welcomePEMiddleStageLm1Free_l1 expressions l1FreeRows) l1Executed
  have sharedFrame : nextShared.peRegisters welcomePE = afterMatrix.peRegisters welcomePE :=
    congrFun (executeParsedSharedBlockProducers_peRegisters (welcomeInitialState welcomeZeroWords)
      afterMatrix nextShared (expressions.map NormalizedExpr.toParsed)
      (!(expressions.any (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed)))
      sharedExecuted) welcomePE
  have peEq : next.peRegisters welcomePE = nextBroadcast.peRegisters welcomePE := by
    rw [nextEq]
  refine ⟨(intWrites ++ floatWrites) ++ mslWrites ++ reluWrites ++ blockWrites ++ matrixWrites
      ++ l1Writes,
    executeIntegerProducerInstructionLine_pe_commit_split nextPEs nextMsl nextRelu
      nextBlockFloat afterMatrix nextShared nextBroadcast next peEq (intWrites ++ floatWrites)
      mslWrites reluWrites blockWrites matrixWrites l1Writes intCommit mslCommit reluCommit
      blockCommit matrixCommit sharedFrame l1Commit, ?_⟩
  exact lm1WritesShape_of_six_first (intWrites ++ floatWrites) mslWrites reluWrites blockWrites
    matrixWrites l1Writes combinedShape mslFree reluFree blockFree matrixFree l1Free

/-! ## 2. The arbitrary-companion dispatch with a `.lm1`-free float half

`WelcomeSlotFree.lean` removed the `.noforward` / `.wait` companion restriction
from the plain and `.matrixRead` dispatches; `WelcomeFloatProvenance.lean`
removed the empty-float restriction from the original dispatch form.  The two
theorems below combine both: the companions are arbitrary preparing rows and
the float-MAU filter only has to be `.lm1`-free, not empty. -/

/-- **The plain-writer line shape with arbitrary companions and a `.lm1`-free
float half.**  `welcomePEWriteShape_of_plainWriter_arbitrary_flagFree` with
`floatEmpty` replaced by the row-local `floatFreeRows`. -/
theorem welcomePEWriteShape_of_plainWriter_arbitrary_floatRows
    (expressions : List NormalizedExpr)
    (unrefuted : WelcomePEUnrefuted expressions)
    (before after : List ParsedExpr) (e : ParsedExpr)
    (split : (expressions.map NormalizedExpr.toParsed).filter
        parsedExprIsIntegerMatrixReadStageInput = before ++ e :: after)
    (eMem : e ∈ expressions.map NormalizedExpr.toParsed)
    (eWriter : Issue.Bank.lm1 ∈ (e.toIssueExpr 0).writeBanks)
    (notInBefore : e ∉ before) (notInAfter : e ∉ after)
    (notDouble : ∀ payload sparse, e.op = .immediate payload sparse →
      ∀ destination ∈ e.destinations,
        ParsedOperand.directDestinationBankWidth? destination ≠
          some (PEMemory.Bank.lm1, PEMemory.Width.double))
    (plain : parsedExprIsPlainIntegerALU e = true)
    (floatFreeRows : ∀ expression ∈ (expressions.map NormalizedExpr.toParsed).filter
        parsedExprIsSupportedFloatMAUProducer, WelcomeRowHasNoLm1Destination expression)
    (middleFree : WelcomePEMiddleStageLm1Free expressions)
    (matrixFreeRows : WelcomePEMatrixMAUStageLm1Free expressions)
    (l1FreeRows : WelcomePEL1StageLm1Free expressions) :
    WelcomePEWriteShape expressions := by
  have rows := welcomeLm1Writer_rows expressions unrefuted e eMem eWriter
  have freeBefore : ∀ expression ∈ before, WelcomeRowHasNoLm1Destination expression := by
    intro expression member
    apply rows expression
    · have inFilter : expression ∈ (expressions.map NormalizedExpr.toParsed).filter
          parsedExprIsIntegerMatrixReadStageInput := by
        rw [split]
        exact List.mem_append_left _ member
      exact (List.mem_filter.mp inFilter).1
    · intro same
      exact notInBefore (same ▸ member)
  have freeAfter : ∀ expression ∈ after, WelcomeRowHasNoLm1Destination expression := by
    intro expression member
    apply rows expression
    · have inFilter : expression ∈ (expressions.map NormalizedExpr.toParsed).filter
          parsedExprIsIntegerMatrixReadStageInput := by
        rw [split]
        exact List.mem_append_right _ (List.mem_cons_of_mem _ member)
      exact (List.mem_filter.mp inFilter).1
    · intro same
      exact notInAfter (same ▸ member)
  refine welcomePEWriteShape_of_floatRows_intShape expressions floatFreeRows middleFree
    matrixFreeRows l1FreeRows ?_
  intro intWrites intSlots intBars intPrep
  have splitWalk : (welcomePEWalkFilter expressions).filter
      parsedExprIsIntegerMatrixReadStageInput = before ++ e :: after := by
    rw [welcomePEWalkFilter_integer]
    exact split
  obtain ⟨beforeWrites, prefixSlots, beforeBars, rowWrites, rowSlots, rowBars, afterWrites,
    afterSlots, afterBars, rowPrep, intWritesEq, beforeFree, afterFree⟩ :=
    welcomeIntegerPrep_split (welcomeInitialState welcomeZeroWords)
      (welcomePEWalkFilter expressions) before after e splitWalk freeBefore freeAfter
      intWrites intSlots intBars intPrep
  rw [intWritesEq]
  exact lm1WritesShape_of_append_split (leading := beforeWrites) (middle := rowWrites)
    (trailing := afterWrites) rfl beforeFree
    ((PlainFlagFree.plainRow_lm1_shape_of_linePrep_anyFlag e plain notDouble
      (welcomeLm1Writer_nodup expressions unrefuted e eMem) _ _ prefixSlots rowWrites rowSlots
      rowBars rowPrep)) afterFree

/-- **The `.matrixRead`-writer line shape with arbitrary companions and a
`.lm1`-free float half.**  `welcomePEWriteShape_of_matrixReadWriter_arbitrary`
with `floatEmpty` replaced by the row-local `floatFreeRows`. -/
theorem welcomePEWriteShape_of_matrixReadWriter_arbitrary_floatRows
    (expressions : List NormalizedExpr)
    (unrefuted : WelcomePEUnrefuted expressions)
    (before after : List ParsedExpr) (e : ParsedExpr)
    (split : (expressions.map NormalizedExpr.toParsed).filter
        parsedExprIsIntegerMatrixReadStageInput = before ++ e :: after)
    (eMem : e ∈ expressions.map NormalizedExpr.toParsed)
    (eWriter : Issue.Bank.lm1 ∈ (e.toIssueExpr 0).writeBanks)
    (notInBefore : e ∉ before) (notInAfter : e ∉ after)
    (precision : ParsedPrecision) (sideY : Bool) (width : Fin 5) (row : Fin (2 ^ 32))
    (op : e.op = .matrixRead precision)
    (sources : e.sources = [.matrix sideY width (some row)])
    (staticW : PEMemory.Width)
    (staticWidth : ∀ destination ∈ e.destinations, ∀ v : PEMemory.Width,
      ParsedOperand.directDestinationBankWidth? destination =
        some (PEMemory.Bank.lm1, v) → v = staticW)
    (floatFreeRows : ∀ expression ∈ (expressions.map NormalizedExpr.toParsed).filter
        parsedExprIsSupportedFloatMAUProducer, WelcomeRowHasNoLm1Destination expression)
    (middleFree : WelcomePEMiddleStageLm1Free expressions)
    (matrixFreeRows : WelcomePEMatrixMAUStageLm1Free expressions)
    (l1FreeRows : WelcomePEL1StageLm1Free expressions) :
    WelcomePEWriteShape expressions := by
  have rows := welcomeLm1Writer_rows expressions unrefuted e eMem eWriter
  have freeBefore : ∀ expression ∈ before, WelcomeRowHasNoLm1Destination expression := by
    intro expression member
    apply rows expression
    · have inFilter : expression ∈ (expressions.map NormalizedExpr.toParsed).filter
          parsedExprIsIntegerMatrixReadStageInput := by
        rw [split]
        exact List.mem_append_left _ member
      exact (List.mem_filter.mp inFilter).1
    · intro same
      exact notInBefore (same ▸ member)
  have freeAfter : ∀ expression ∈ after, WelcomeRowHasNoLm1Destination expression := by
    intro expression member
    apply rows expression
    · have inFilter : expression ∈ (expressions.map NormalizedExpr.toParsed).filter
          parsedExprIsIntegerMatrixReadStageInput := by
        rw [split]
        exact List.mem_append_right _ (List.mem_cons_of_mem _ member)
      exact (List.mem_filter.mp inFilter).1
    · intro same
      exact notInAfter (same ▸ member)
  refine welcomePEWriteShape_of_floatRows_intShape expressions floatFreeRows middleFree
    matrixFreeRows l1FreeRows ?_
  intro intWrites intSlots intBars intPrep
  have splitWalk : (welcomePEWalkFilter expressions).filter
      parsedExprIsIntegerMatrixReadStageInput = before ++ e :: after := by
    rw [welcomePEWalkFilter_integer]
    exact split
  obtain ⟨beforeWrites, prefixSlots, beforeBars, rowWrites, rowSlots, rowBars, afterWrites,
    afterSlots, afterBars, rowPrep, intWritesEq, beforeFree, afterFree⟩ :=
    welcomeIntegerPrep_split (welcomeInitialState welcomeZeroWords)
      (welcomePEWalkFilter expressions) before after e splitWalk freeBefore freeAfter
      intWrites intSlots intBars intPrep
  rw [intWritesEq]
  exact lm1WritesShape_of_append_split (leading := beforeWrites) (middle := rowWrites)
    (trailing := afterWrites) rfl beforeFree
    ((matrixReadRow_lm1_shape_of_startSlots e precision sideY width row op sources
      welcomeZeroControl _ _ false staticW prefixSlots
      (welcomeLm1Writer_nodup expressions unrefuted e eMem) staticWidth rowWrites rowSlots
      rowBars rowPrep)) afterFree

/-! ## 3. The three packages with a `.lm1`-free float half

Each definition is the round-49 package with the empty-float conjunct

```
(expressions.map NormalizedExpr.toParsed).filter
  parsedExprIsSupportedFloatMAUProducer = []
```

replaced by the row-local statement that every float-MAU row of the line has no
`.lm1` destination operand.  The three `...NoFloat` definitions of §3.3 drop
even that: for a plain, `.matrixRead` or `.l1bm` writer it is derivable from the
line's acceptance and the writer's uniqueness. -/

/-- **The plain-writer data with a `.lm1`-free float half.**  As
`WelcomePEPlainWriterDataForFlagFree`, with `floatEmpty` replaced by
`floatFreeRows`. -/
def WelcomePEPlainWriterDataForFloatRows (expressions : List NormalizedExpr) : Prop :=
  ∀ (e : ParsedExpr),
    e ∈ expressions.map NormalizedExpr.toParsed →
      parsedExprIsPlainIntegerALU e = true →
      Issue.Bank.lm1 ∈ (e.toIssueExpr 0).writeBanks →
      ∃ before after : List ParsedExpr,
        (expressions.map NormalizedExpr.toParsed).filter
            parsedExprIsIntegerMatrixReadStageInput = before ++ e :: after ∧
          e ∉ before ∧ e ∉ after ∧
          (∀ expression ∈ (expressions.map NormalizedExpr.toParsed).filter
            parsedExprIsSupportedFloatMAUProducer,
            WelcomeRowHasNoLm1Destination expression) ∧
          ((∀ (payload : BitVec 32) (sparse : Bool), e.op = .immediate payload sparse →
              ∀ destination ∈ e.destinations,
                ParsedOperand.directDestinationBankWidth? destination ≠
                  some (PEMemory.Bank.lm1, PEMemory.Width.double)) ∨
            WelcomePEInputIndependent expressions)

/-- **The `.matrixRead`-writer data with a `.lm1`-free float half.** -/
def WelcomePEMatrixReadWriterDataForFloatRows (expressions : List NormalizedExpr) : Prop :=
  ∀ (e : ParsedExpr),
    e ∈ expressions.map NormalizedExpr.toParsed →
      parsedExprIsMatrixReadProducer e = true →
      Issue.Bank.lm1 ∈ (e.toIssueExpr 0).writeBanks →
      ∃ (before after : List ParsedExpr) (precision : ParsedPrecision) (sideY : Bool)
        (width : Fin 5) (row : Fin (2 ^ 32)) (staticW : PEMemory.Width),
        (expressions.map NormalizedExpr.toParsed).filter
            parsedExprIsIntegerMatrixReadStageInput = before ++ e :: after ∧
          e ∉ before ∧ e ∉ after ∧
          e.op = .matrixRead precision ∧
          e.sources = [.matrix sideY width (some row)] ∧
          (∀ destination ∈ e.destinations, ∀ v : PEMemory.Width,
            ParsedOperand.directDestinationBankWidth? destination =
              some (PEMemory.Bank.lm1, v) → v = staticW) ∧
          (∀ expression ∈ (expressions.map NormalizedExpr.toParsed).filter
            parsedExprIsSupportedFloatMAUProducer,
            WelcomeRowHasNoLm1Destination expression)

/-- **The `.l1bm`-broadcast-writer data with a `.lm1`-free float half.** -/
def WelcomePEL1BMWriterDataForFloatRows (expressions : List NormalizedExpr) : Prop :=
  ∀ (e : ParsedExpr),
    e ∈ expressions.map NormalizedExpr.toParsed →
      parsedExprIsL1ToPEProducer e = true →
      Issue.Bank.lm1 ∈ (e.toIssueExpr 0).writeBanks →
      ∃ (access : ParsedL1ToPEAccess) (memoryAccess : Access)
        (negated extended rounded : Bool) (mask : Option ParsedMask) (w : PEMemory.Width),
        lowerParsedL1ToPE? e = some access ∧
          access.destinations =
            [ParsedOperand.mem memoryAccess negated extended rounded mask] ∧
          ParsedOperand.directDestinationBankWidth?
              (ParsedOperand.mem memoryAccess negated extended rounded mask) =
            some (PEMemory.Bank.lm1, w) ∧
          (expressions.map NormalizedExpr.toParsed).filter
            parsedExprIsL1ToPEProducer = [e] ∧
          (∀ expression ∈ (expressions.map NormalizedExpr.toParsed).filter
            parsedExprIsSupportedFloatMAUProducer,
            WelcomeRowHasNoLm1Destination expression)

/-- The global plain package with a `.lm1`-free float half. -/
def WelcomePEPlainWriterDataFloatRows : Prop :=
  ∀ expressions, WelcomePEUnrefuted expressions →
    WelcomePEPlainWriterDataForFloatRows expressions

/-- The global `.matrixRead` package with a `.lm1`-free float half. -/
def WelcomePEMatrixReadWriterDataFloatRows : Prop :=
  ∀ expressions, WelcomePEUnrefuted expressions →
    WelcomePEMatrixReadWriterDataForFloatRows expressions

/-- The global `.l1bm` package with a `.lm1`-free float half. -/
def WelcomePEL1BMWriterDataFloatRows : Prop :=
  ∀ expressions, WelcomePEUnrefuted expressions →
    WelcomePEL1BMWriterDataForFloatRows expressions

/-- **The per-line shape from the plain package with a `.lm1`-free float half.** -/
theorem welcomePEWriteShape_of_plainWriter_data_floatRows
    (expressions : List NormalizedExpr)
    (data : WelcomePEPlainWriterDataForFloatRows expressions)
    (unrefuted : WelcomePEUnrefuted expressions) (e : ParsedExpr)
    (eMem : e ∈ expressions.map NormalizedExpr.toParsed)
    (plain : parsedExprIsPlainIntegerALU e = true)
    (writer : Issue.Bank.lm1 ∈ (e.toIssueExpr 0).writeBanks) :
    WelcomePEWriteShape expressions := by
  obtain ⟨before, after, split, notBefore, notAfter, floatFreeRows, notDouble | indep⟩ :=
    data e eMem plain writer
  · obtain ⟨-, -, mslFalse, reluFalse, blockFalse, -, -, matrixMAUFalse, -, l1False, -⟩ :=
      parsedExprIsPlainIntegerALU_facts e plain
    exact welcomePEWriteShape_of_plainWriter_arbitrary_floatRows expressions unrefuted before
      after e split eMem writer notBefore notAfter notDouble plain floatFreeRows
      (welcomePEMiddleStageLm1Free_of_rows expressions e
        (welcomeLm1Writer_rows expressions unrefuted e eMem writer) mslFalse reluFalse blockFalse)
      (welcomePEMatrixMAUStageLm1Free_of_rows expressions e
        (welcomeLm1Writer_rows expressions unrefuted e eMem writer) matrixMAUFalse)
      (welcomePEL1StageLm1Free_of_rows expressions e
        (welcomeLm1Writer_rows expressions unrefuted e eMem writer) l1False)
  · exact Or.inr (Or.inr indep)

/-- **The per-line shape from the `.matrixRead` package with a `.lm1`-free float
half.** -/
theorem welcomePEWriteShape_of_matrixReadWriter_data_floatRows
    (expressions : List NormalizedExpr)
    (data : WelcomePEMatrixReadWriterDataForFloatRows expressions)
    (unrefuted : WelcomePEUnrefuted expressions) (e : ParsedExpr)
    (eMem : e ∈ expressions.map NormalizedExpr.toParsed)
    (read : parsedExprIsMatrixReadProducer e = true)
    (writer : Issue.Bank.lm1 ∈ (e.toIssueExpr 0).writeBanks) :
    WelcomePEWriteShape expressions := by
  obtain ⟨before, after, precision, sideY, width, row, staticW, split, notBefore, notAfter,
    op, sources, staticWidth, floatFreeRows⟩ := data e eMem read writer
  obtain ⟨mslFalse, reluFalse, blockFalse, matrixMAUFalse, l1False⟩ :=
    matrixRead_parsedExpr_predicates e precision op
  exact welcomePEWriteShape_of_matrixReadWriter_arbitrary_floatRows expressions unrefuted before
    after e split eMem writer notBefore notAfter precision sideY width row op sources staticW
    staticWidth floatFreeRows
    (welcomePEMiddleStageLm1Free_of_rows expressions e
      (welcomeLm1Writer_rows expressions unrefuted e eMem writer) mslFalse reluFalse blockFalse)
    (welcomePEMatrixMAUStageLm1Free_of_rows expressions e
      (welcomeLm1Writer_rows expressions unrefuted e eMem writer) matrixMAUFalse)
    (welcomePEL1StageLm1Free_of_rows expressions e
      (welcomeLm1Writer_rows expressions unrefuted e eMem writer) l1False)

/-- **The per-line shape from the `.l1bm` package with a `.lm1`-free float half.**
The existing unique-writer theorem `welcomePEWriteShape_of_l1bmWriter_unique_of_floatRows`
derives the float half's freeness from the `.lm1`-writer uniqueness; the package's
own `floatFreeRows` conjunct is therefore not needed in this direction. -/
theorem welcomePEWriteShape_of_l1bmWriter_data_floatRows
    (expressions : List NormalizedExpr)
    (data : WelcomePEL1BMWriterDataForFloatRows expressions)
    (unrefuted : WelcomePEUnrefuted expressions) (e : ParsedExpr)
    (eMem : e ∈ expressions.map NormalizedExpr.toParsed)
    (l1 : parsedExprIsL1ToPEProducer e = true)
    (writer : Issue.Bank.lm1 ∈ (e.toIssueExpr 0).writeBanks) :
    WelcomePEWriteShape expressions := by
  obtain ⟨access, memoryAccess, negated, extended, rounded, mask, w, lowered, destinations,
    static, l1Filter, -⟩ := data e eMem l1 writer
  exact welcomePEWriteShape_of_l1bmWriter_unique_of_floatRows expressions e access memoryAccess
    negated extended rounded mask w lowered destinations static l1Filter
    (welcomeLm1Writer_rows expressions unrefuted e eMem writer)

/-! ### 3.3 The same packages with no float condition at all

For the three writer kinds treated here, the writer `e` is never a float-MAU
producer, and every other row of an unrefuted line has no `.lm1` destination
(`welcomeLm1Writer_rows`).  Hence `floatFreeRows` is automatic:
`floatFilter_lm1Free_of_rows`.  Dropping it leaves the definitions below, which
are therefore the strongest form of the three packages. -/

/-- **The plain-writer data with no float condition.**  This is
`WelcomePEPlainWriterDataForFlagFree` minus the empty-float conjunct. -/
def WelcomePEPlainWriterDataForNoFloat (expressions : List NormalizedExpr) : Prop :=
  ∀ (e : ParsedExpr),
    e ∈ expressions.map NormalizedExpr.toParsed →
      parsedExprIsPlainIntegerALU e = true →
      Issue.Bank.lm1 ∈ (e.toIssueExpr 0).writeBanks →
      ∃ before after : List ParsedExpr,
        (expressions.map NormalizedExpr.toParsed).filter
            parsedExprIsIntegerMatrixReadStageInput = before ++ e :: after ∧
          e ∉ before ∧ e ∉ after ∧
          ((∀ (payload : BitVec 32) (sparse : Bool), e.op = .immediate payload sparse →
              ∀ destination ∈ e.destinations,
                ParsedOperand.directDestinationBankWidth? destination ≠
                  some (PEMemory.Bank.lm1, PEMemory.Width.double)) ∨
            WelcomePEInputIndependent expressions)

/-- **The `.matrixRead`-writer data with no float condition.**  This is
`WelcomePEMatrixReadWriterDataForSlotFree` minus the empty-float conjunct. -/
def WelcomePEMatrixReadWriterDataForNoFloat (expressions : List NormalizedExpr) : Prop :=
  ∀ (e : ParsedExpr),
    e ∈ expressions.map NormalizedExpr.toParsed →
      parsedExprIsMatrixReadProducer e = true →
      Issue.Bank.lm1 ∈ (e.toIssueExpr 0).writeBanks →
      ∃ (before after : List ParsedExpr) (precision : ParsedPrecision) (sideY : Bool)
        (width : Fin 5) (row : Fin (2 ^ 32)) (staticW : PEMemory.Width),
        (expressions.map NormalizedExpr.toParsed).filter
            parsedExprIsIntegerMatrixReadStageInput = before ++ e :: after ∧
          e ∉ before ∧ e ∉ after ∧
          e.op = .matrixRead precision ∧
          e.sources = [.matrix sideY width (some row)] ∧
          (∀ destination ∈ e.destinations, ∀ v : PEMemory.Width,
            ParsedOperand.directDestinationBankWidth? destination =
              some (PEMemory.Bank.lm1, v) → v = staticW)

/-- **The `.l1bm`-broadcast-writer data with no float condition.**  This is
`WelcomePEL1BMWriterDataFor` minus the empty-float conjunct. -/
def WelcomePEL1BMWriterDataForNoFloat (expressions : List NormalizedExpr) : Prop :=
  ∀ (e : ParsedExpr),
    e ∈ expressions.map NormalizedExpr.toParsed →
      parsedExprIsL1ToPEProducer e = true →
      Issue.Bank.lm1 ∈ (e.toIssueExpr 0).writeBanks →
      ∃ (access : ParsedL1ToPEAccess) (memoryAccess : Access)
        (negated extended rounded : Bool) (mask : Option ParsedMask) (w : PEMemory.Width),
        lowerParsedL1ToPE? e = some access ∧
          access.destinations =
            [ParsedOperand.mem memoryAccess negated extended rounded mask] ∧
          ParsedOperand.directDestinationBankWidth?
              (ParsedOperand.mem memoryAccess negated extended rounded mask) =
            some (PEMemory.Bank.lm1, w) ∧
          (expressions.map NormalizedExpr.toParsed).filter
            parsedExprIsL1ToPEProducer = [e]

/-- The global plain package with no float condition. -/
def WelcomePEPlainWriterDataNoFloat : Prop :=
  ∀ expressions, WelcomePEUnrefuted expressions → WelcomePEPlainWriterDataForNoFloat expressions

/-- The global `.matrixRead` package with no float condition. -/
def WelcomePEMatrixReadWriterDataNoFloat : Prop :=
  ∀ expressions, WelcomePEUnrefuted expressions →
    WelcomePEMatrixReadWriterDataForNoFloat expressions

/-- The global `.l1bm` package with no float condition. -/
def WelcomePEL1BMWriterDataNoFloat : Prop :=
  ∀ expressions, WelcomePEUnrefuted expressions → WelcomePEL1BMWriterDataForNoFloat expressions

/-- **Row-locality supplies the float half's `.lm1`-freeness for a plain
writer.** -/
theorem welcomePEPlainWriterDataFor_floatRows_of_noFloat
    (expressions : List NormalizedExpr) (unrefuted : WelcomePEUnrefuted expressions)
    (data : WelcomePEPlainWriterDataForNoFloat expressions) :
    WelcomePEPlainWriterDataForFloatRows expressions := by
  intro e eMem plain writer
  obtain ⟨before, after, split, notBefore, notAfter, rest⟩ := data e eMem plain writer
  have floatFreeRows := floatFilter_lm1Free_of_rows expressions e
    (welcomeLm1Writer_rows expressions unrefuted e eMem writer)
    (parsedExprIsPlainIntegerALU_notFloatMAU e plain)
  exact ⟨before, after, split, notBefore, notAfter, floatFreeRows, rest⟩

/-- **Row-locality supplies the float half's `.lm1`-freeness for a `.matrixRead`
writer.** -/
theorem welcomePEMatrixReadWriterDataFor_floatRows_of_noFloat
    (expressions : List NormalizedExpr) (unrefuted : WelcomePEUnrefuted expressions)
    (data : WelcomePEMatrixReadWriterDataForNoFloat expressions) :
    WelcomePEMatrixReadWriterDataForFloatRows expressions := by
  intro e eMem read writer
  obtain ⟨before, after, precision, sideY, width, row, staticW, split, notBefore, notAfter,
    op, sources, staticWidth⟩ := data e eMem read writer
  have floatFreeRows := floatFilter_lm1Free_of_rows expressions e
    (welcomeLm1Writer_rows expressions unrefuted e eMem writer)
    (matrixRead_notFloatMAU e precision op)
  exact ⟨before, after, precision, sideY, width, row, staticW, split, notBefore, notAfter,
    op, sources, staticWidth, floatFreeRows⟩

/-- **Row-locality supplies the float half's `.lm1`-freeness for a `.l1bm`
writer.** -/
theorem welcomePEL1BMWriterDataFor_floatRows_of_noFloat
    (expressions : List NormalizedExpr) (unrefuted : WelcomePEUnrefuted expressions)
    (data : WelcomePEL1BMWriterDataForNoFloat expressions) :
    WelcomePEL1BMWriterDataForFloatRows expressions := by
  intro e eMem l1 writer
  obtain ⟨access, memoryAccess, negated, extended, rounded, mask, w, lowered, destinations,
    static, l1Filter⟩ := data e eMem l1 writer
  have floatFreeRows := floatFilter_lm1Free_of_rows expressions e
    (welcomeLm1Writer_rows expressions unrefuted e eMem writer)
    ((l1bmBroadcast_parsedExpr_predicates e access lowered).2.1)
  exact ⟨access, memoryAccess, negated, extended, rounded, mask, w, lowered, destinations,
    static, l1Filter, floatFreeRows⟩

/-- **The global no-float plain package gives the global `.lm1`-free one.** -/
theorem welcomePEPlainWriterDataFloatRows_of_noFloat
    (data : WelcomePEPlainWriterDataNoFloat) : WelcomePEPlainWriterDataFloatRows :=
  fun expressions unrefuted =>
    welcomePEPlainWriterDataFor_floatRows_of_noFloat expressions unrefuted (data expressions unrefuted)

/-- **The global no-float `.matrixRead` package gives the global `.lm1`-free
one.** -/
theorem welcomePEMatrixReadWriterDataFloatRows_of_noFloat
    (data : WelcomePEMatrixReadWriterDataNoFloat) : WelcomePEMatrixReadWriterDataFloatRows :=
  fun expressions unrefuted =>
    welcomePEMatrixReadWriterDataFor_floatRows_of_noFloat expressions unrefuted
      (data expressions unrefuted)

/-- **The global no-float `.l1bm` package gives the global `.lm1`-free one.** -/
theorem welcomePEL1BMWriterDataFloatRows_of_noFloat
    (data : WelcomePEL1BMWriterDataNoFloat) : WelcomePEL1BMWriterDataFloatRows :=
  fun expressions unrefuted =>
    welcomePEL1BMWriterDataFor_floatRows_of_noFloat expressions unrefuted (data expressions unrefuted)

/-- **Dropping the float conjunct of the plain package.** -/
theorem welcomePEPlainWriterDataFor_noFloat_of_floatRows
    (expressions : List NormalizedExpr) (data : WelcomePEPlainWriterDataForFloatRows expressions) :
    WelcomePEPlainWriterDataForNoFloat expressions := by
  intro e eMem plain writer
  obtain ⟨before, after, split, notBefore, notAfter, -, rest⟩ := data e eMem plain writer
  exact ⟨before, after, split, notBefore, notAfter, rest⟩

/-- **Dropping the float conjunct of the `.matrixRead` package.** -/
theorem welcomePEMatrixReadWriterDataFor_noFloat_of_floatRows
    (expressions : List NormalizedExpr)
    (data : WelcomePEMatrixReadWriterDataForFloatRows expressions) :
    WelcomePEMatrixReadWriterDataForNoFloat expressions := by
  intro e eMem read writer
  obtain ⟨before, after, precision, sideY, width, row, staticW, split, notBefore, notAfter,
    op, sources, staticWidth, -⟩ := data e eMem read writer
  exact ⟨before, after, precision, sideY, width, row, staticW, split, notBefore, notAfter,
    op, sources, staticWidth⟩

/-- **Dropping the float conjunct of the `.l1bm` package.** -/
theorem welcomePEL1BMWriterDataFor_noFloat_of_floatRows
    (expressions : List NormalizedExpr) (data : WelcomePEL1BMWriterDataForFloatRows expressions) :
    WelcomePEL1BMWriterDataForNoFloat expressions := by
  intro e eMem l1 writer
  obtain ⟨access, memoryAccess, negated, extended, rounded, mask, w, lowered, destinations,
    static, l1Filter, -⟩ := data e eMem l1 writer
  exact ⟨access, memoryAccess, negated, extended, rounded, mask, w, lowered, destinations,
    static, l1Filter⟩

/-- **The global no-float form of the plain package is its strongest form.** -/
theorem welcomePEPlainWriterDataNoFloat_of_floatRows (data : WelcomePEPlainWriterDataFloatRows) :
    WelcomePEPlainWriterDataNoFloat :=
  fun expressions unrefuted =>
    welcomePEPlainWriterDataFor_noFloat_of_floatRows expressions (data expressions unrefuted)

/-- **The global no-float form of the `.matrixRead` package is its strongest
form.** -/
theorem welcomePEMatrixReadWriterDataNoFloat_of_floatRows
    (data : WelcomePEMatrixReadWriterDataFloatRows) : WelcomePEMatrixReadWriterDataNoFloat :=
  fun expressions unrefuted =>
    welcomePEMatrixReadWriterDataFor_noFloat_of_floatRows expressions (data expressions unrefuted)

/-- **The global no-float form of the `.l1bm` package is its strongest form.** -/
theorem welcomePEL1BMWriterDataNoFloat_of_floatRows (data : WelcomePEL1BMWriterDataFloatRows) :
    WelcomePEL1BMWriterDataNoFloat :=
  fun expressions unrefuted =>
    welcomePEL1BMWriterDataFor_noFloat_of_floatRows expressions (data expressions unrefuted)

/-! ### 3.4 The per-line shapes from the no-float packages -/

/-- **The plain-writer line shape from the no-float package.** -/
theorem welcomePEWriteShape_of_plainWriter_data_noFloat
    (expressions : List NormalizedExpr)
    (data : WelcomePEPlainWriterDataForNoFloat expressions)
    (unrefuted : WelcomePEUnrefuted expressions) (e : ParsedExpr)
    (eMem : e ∈ expressions.map NormalizedExpr.toParsed)
    (plain : parsedExprIsPlainIntegerALU e = true)
    (writer : Issue.Bank.lm1 ∈ (e.toIssueExpr 0).writeBanks) :
    WelcomePEWriteShape expressions :=
  welcomePEWriteShape_of_plainWriter_data_floatRows expressions
    (welcomePEPlainWriterDataFor_floatRows_of_noFloat expressions unrefuted data) unrefuted e eMem
    plain writer

/-- **The `.matrixRead`-writer line shape from the no-float package.** -/
theorem welcomePEWriteShape_of_matrixReadWriter_data_noFloat
    (expressions : List NormalizedExpr)
    (data : WelcomePEMatrixReadWriterDataForNoFloat expressions)
    (unrefuted : WelcomePEUnrefuted expressions) (e : ParsedExpr)
    (eMem : e ∈ expressions.map NormalizedExpr.toParsed)
    (read : parsedExprIsMatrixReadProducer e = true)
    (writer : Issue.Bank.lm1 ∈ (e.toIssueExpr 0).writeBanks) :
    WelcomePEWriteShape expressions :=
  welcomePEWriteShape_of_matrixReadWriter_data_floatRows expressions
    (welcomePEMatrixReadWriterDataFor_floatRows_of_noFloat expressions unrefuted data) unrefuted e
    eMem read writer

/-- **The `.l1bm`-writer line shape from the no-float package.** -/
theorem welcomePEWriteShape_of_l1bmWriter_data_noFloat
    (expressions : List NormalizedExpr)
    (data : WelcomePEL1BMWriterDataForNoFloat expressions)
    (unrefuted : WelcomePEUnrefuted expressions) (e : ParsedExpr)
    (eMem : e ∈ expressions.map NormalizedExpr.toParsed)
    (l1 : parsedExprIsL1ToPEProducer e = true)
    (writer : Issue.Bank.lm1 ∈ (e.toIssueExpr 0).writeBanks) :
    WelcomePEWriteShape expressions :=
  welcomePEWriteShape_of_l1bmWriter_data_floatRows expressions
    (welcomePEL1BMWriterDataFor_floatRows_of_noFloat expressions unrefuted data) unrefuted e eMem
    l1 writer

/-! ## 4. The conservative direction

The packages of `WelcomeAssemblyFinal.lean` carry the empty-float conjunct; the
new packages only carry its row-local consequence (or nothing at all).  Every
line that satisfied an old package therefore satisfies the corresponding new
one. -/

/-- **The round-49 plain package implies the `.lm1`-free float one.** -/
theorem welcomePEPlainWriterDataFor_floatRows_of_flagFree
    (expressions : List NormalizedExpr) (data : WelcomePEPlainWriterDataForFlagFree expressions) :
    WelcomePEPlainWriterDataForFloatRows expressions := by
  intro e eMem plain writer
  obtain ⟨before, after, split, notBefore, notAfter, floatEmpty, rest⟩ := data e eMem plain writer
  refine ⟨before, after, split, notBefore, notAfter, ?_, rest⟩
  intro expression member
  rw [floatEmpty] at member
  simp at member

/-- **The round-49 `.matrixRead` package implies the `.lm1`-free float one.** -/
theorem welcomePEMatrixReadWriterDataFor_floatRows_of_slotFree
    (expressions : List NormalizedExpr) (data : WelcomePEMatrixReadWriterDataForSlotFree expressions) :
    WelcomePEMatrixReadWriterDataForFloatRows expressions := by
  intro e eMem read writer
  obtain ⟨before, after, precision, sideY, width, row, staticW, split, notBefore, notAfter,
    op, sources, staticWidth, floatEmpty⟩ := data e eMem read writer
  refine ⟨before, after, precision, sideY, width, row, staticW, split, notBefore, notAfter,
    op, sources, staticWidth, ?_⟩
  intro expression member
  rw [floatEmpty] at member
  simp at member

/-- **The round-49 `.l1bm` package implies the `.lm1`-free float one.** -/
theorem welcomePEL1BMWriterDataFor_floatRows_of_data
    (expressions : List NormalizedExpr) (data : WelcomePEL1BMWriterDataFor expressions) :
    WelcomePEL1BMWriterDataForFloatRows expressions := by
  intro e eMem l1 writer
  obtain ⟨access, memoryAccess, negated, extended, rounded, mask, w, lowered, destinations,
    static, l1Filter, floatEmpty⟩ := data e eMem l1 writer
  refine ⟨access, memoryAccess, negated, extended, rounded, mask, w, lowered, destinations,
    static, l1Filter, ?_⟩
  intro expression member
  rw [floatEmpty] at member
  simp at member

/-- **The global round-49 plain package implies the `.lm1`-free float one.** -/
theorem welcomePEPlainWriterDataFloatRows_of_flagFree
    (data : WelcomePEPlainWriterDataFlagFree) : WelcomePEPlainWriterDataFloatRows :=
  fun expressions unrefuted =>
    welcomePEPlainWriterDataFor_floatRows_of_flagFree expressions (data expressions unrefuted)

/-- **The global round-49 `.matrixRead` package implies the `.lm1`-free float
one.** -/
theorem welcomePEMatrixReadWriterDataFloatRows_of_slotFree
    (data : WelcomePEMatrixReadWriterDataSlotFree) : WelcomePEMatrixReadWriterDataFloatRows :=
  fun expressions unrefuted =>
    welcomePEMatrixReadWriterDataFor_floatRows_of_slotFree expressions (data expressions unrefuted)

/-- **The global round-49 `.l1bm` package implies the `.lm1`-free float one.** -/
theorem welcomePEL1BMWriterDataFloatRows_of_data
    (data : WelcomePEL1BMWriterData) : WelcomePEL1BMWriterDataFloatRows :=
  fun expressions unrefuted =>
    welcomePEL1BMWriterDataFor_floatRows_of_data expressions (data expressions unrefuted)

/-- **The round-49 plain package implies the no-float one.** -/
theorem welcomePEPlainWriterDataFor_noFloat_of_flagFree
    (expressions : List NormalizedExpr) (data : WelcomePEPlainWriterDataForFlagFree expressions) :
    WelcomePEPlainWriterDataForNoFloat expressions :=
  welcomePEPlainWriterDataFor_noFloat_of_floatRows expressions
    (welcomePEPlainWriterDataFor_floatRows_of_flagFree expressions data)

/-- **The round-49 `.matrixRead` package implies the no-float one.** -/
theorem welcomePEMatrixReadWriterDataFor_noFloat_of_slotFree
    (expressions : List NormalizedExpr) (data : WelcomePEMatrixReadWriterDataForSlotFree expressions) :
    WelcomePEMatrixReadWriterDataForNoFloat expressions :=
  welcomePEMatrixReadWriterDataFor_noFloat_of_floatRows expressions
    (welcomePEMatrixReadWriterDataFor_floatRows_of_slotFree expressions data)

/-- **The round-49 `.l1bm` package implies the no-float one.** -/
theorem welcomePEL1BMWriterDataFor_noFloat_of_data
    (expressions : List NormalizedExpr) (data : WelcomePEL1BMWriterDataFor expressions) :
    WelcomePEL1BMWriterDataForNoFloat expressions :=
  welcomePEL1BMWriterDataFor_noFloat_of_floatRows expressions
    (welcomePEL1BMWriterDataFor_floatRows_of_data expressions data)

/-- **The global round-49 plain package implies the global no-float one.** -/
theorem welcomePEPlainWriterDataNoFloat_of_flagFree
    (data : WelcomePEPlainWriterDataFlagFree) : WelcomePEPlainWriterDataNoFloat :=
  fun expressions unrefuted =>
    welcomePEPlainWriterDataFor_noFloat_of_flagFree expressions (data expressions unrefuted)

/-- **The global round-49 `.matrixRead` package implies the global no-float
one.** -/
theorem welcomePEMatrixReadWriterDataNoFloat_of_slotFree
    (data : WelcomePEMatrixReadWriterDataSlotFree) : WelcomePEMatrixReadWriterDataNoFloat :=
  fun expressions unrefuted =>
    welcomePEMatrixReadWriterDataFor_noFloat_of_slotFree expressions (data expressions unrefuted)

/-- **The global round-49 `.l1bm` package implies the global no-float one.** -/
theorem welcomePEL1BMWriterDataNoFloat_of_data
    (data : WelcomePEL1BMWriterData) : WelcomePEL1BMWriterDataNoFloat :=
  fun expressions unrefuted =>
    welcomePEL1BMWriterDataFor_noFloat_of_data expressions (data expressions unrefuted)

/-! ## 5. The assembly

The case split of `welcomePELm1LineDispatchDataFlagFree_of_components` with the
three new packages substituted for the plain, `.matrixRead` and `.l1bm` ones.
The float-MAU package is unchanged, and the phantom, special-ALU and matrix-MAU
cases are still discharged by theorems. -/

/-- **The line shape from the three new packages and the float-MAU package.**

The `.lm1` writer of the line is classified with
`supportedProducer_partition`:

* plain → `welcomePEWriteShape_of_plainWriter_data_floatRows`;
* `.matrixRead` → `welcomePEWriteShape_of_matrixReadWriter_data_floatRows`;
* float MAU → `welcomePEWriteShape_of_floatMAUWriter_data` (the unchanged
  package);
* matrix MAU → `welcomePEMatrixMAUWriterData` (unconditional, round 49);
* `.l1bm` → `welcomePEWriteShape_of_l1bmWriter_data_floatRows`;
* special ALU → `welcomePESpecialALUWriterShapeObligation` (unconditional);
* phantom / no writer → `welcomePELm1PhantomWriterProvenance` (unconditional). -/
theorem welcomePEWriteShape_of_writerKindDataFloatRows
    (plain : WelcomePEPlainWriterDataFloatRows)
    (read : WelcomePEMatrixReadWriterDataFloatRows)
    (float : WelcomePEFloatMAUWriterData) (l1 : WelcomePEL1BMWriterDataFloatRows)
    (expressions : List NormalizedExpr) (unrefuted : WelcomePEUnrefuted expressions) :
    WelcomePEWriteShape expressions := by
  by_cases hasWriter : ∃ e ∈ expressions.map NormalizedExpr.toParsed,
      Issue.Bank.lm1 ∈ (e.toIssueExpr 0).writeBanks
  · obtain ⟨e, eMem, eWriter⟩ := hasWriter
    have supported := List.all_eq_true.mp unrefuted.1.2.2.2 e eMem
    have notUnsupported : parsedExprIsUnsupportedRustAlu e = false := by
      simpa using (List.any_eq_false.mp unrefuted.1.2.2.1) e eMem
    rcases supportedProducer_partition e supported with
      isPlain | isFamily | isSpecial | isInert | isUnsupported
    · exact welcomePEWriteShape_of_plainWriter_data_floatRows expressions
        (plain expressions unrefuted) unrefuted e eMem isPlain eWriter
    · rcases parsedExprIsFamilyProducer_cases e isFamily with
        readKind | mauKind | floatKind | writeKind | toPEKind | l2Kind
      · exact welcomePEWriteShape_of_matrixReadWriter_data_floatRows expressions
          (read expressions unrefuted) unrefuted e eMem readKind eWriter
      · exact welcomePEWriteShape_of_matrixMAUWriter_data expressions
          (welcomePEMatrixMAUWriterData expressions unrefuted) unrefuted e eMem mauKind eWriter
      · exact welcomePEWriteShape_of_floatMAUWriter_data expressions
          (float expressions unrefuted) unrefuted e eMem floatKind eWriter
      · have hphantom : ∀ x ∈ expressions.map NormalizedExpr.toParsed,
            Issue.Bank.lm1 ∈ (x.toIssueExpr 0).writeBanks → welcomePhantomWriterKind x := by
          intro x xMem xWriter
          have same : x = e :=
            welcomeLm1Writer_eq_of_two expressions unrefuted xMem eMem xWriter eWriter
          rw [same]
          exact Or.inr (Or.inr (Or.inr (Or.inl writeKind)))
        exact welcomePEWriteShape_of_freeStageCommit expressions
          (welcomePELm1PhantomWriterProvenance expressions unrefuted hphantom)
      · exact welcomePEWriteShape_of_l1bmWriter_data_floatRows expressions
          (l1 expressions unrefuted) unrefuted e eMem toPEKind eWriter
      · have hphantom : ∀ x ∈ expressions.map NormalizedExpr.toParsed,
            Issue.Bank.lm1 ∈ (x.toIssueExpr 0).writeBanks → welcomePhantomWriterKind x := by
          intro x xMem xWriter
          have same : x = e :=
            welcomeLm1Writer_eq_of_two expressions unrefuted xMem eMem xWriter eWriter
          rw [same]
          exact Or.inr (Or.inr (Or.inr (Or.inr l2Kind)))
        exact welcomePEWriteShape_of_freeStageCommit expressions
          (welcomePELm1PhantomWriterProvenance expressions unrefuted hphantom)
    · exact welcomePESpecialALUWriterShapeObligation expressions unrefuted
        ⟨e, eMem, eWriter, isSpecial⟩
    · have hphantom : ∀ x ∈ expressions.map NormalizedExpr.toParsed,
          Issue.Bank.lm1 ∈ (x.toIssueExpr 0).writeBanks → welcomePhantomWriterKind x := by
        intro x xMem xWriter
        have same : x = e :=
          welcomeLm1Writer_eq_of_two expressions unrefuted xMem eMem xWriter eWriter
        rw [same]
        rcases parsedExprIsPEInertProducer_cases e isInert with forward | wait | shared
        · exact Or.inl forward
        · exact Or.inr (Or.inl wait)
        · exact Or.inr (Or.inr (Or.inl shared))
      exact welcomePEWriteShape_of_freeStageCommit expressions
        (welcomePELm1PhantomWriterProvenance expressions unrefuted hphantom)
    · rw [notUnsupported] at isUnsupported
      cases isUnsupported
  · have hphantom : ∀ x ∈ expressions.map NormalizedExpr.toParsed,
        Issue.Bank.lm1 ∈ (x.toIssueExpr 0).writeBanks → welcomePhantomWriterKind x := by
      intro x xMem xWriter
      exact absurd ⟨x, xMem, xWriter⟩ hasWriter
    exact welcomePEWriteShape_of_freeStageCommit expressions
      (welcomePELm1PhantomWriterProvenance expressions unrefuted hphantom)

/-- **The line shape from the no-float packages and the float-MAU package.** -/
theorem welcomePEWriteShape_of_writerKindDataNoFloat
    (plain : WelcomePEPlainWriterDataNoFloat)
    (read : WelcomePEMatrixReadWriterDataNoFloat)
    (float : WelcomePEFloatMAUWriterData) (l1 : WelcomePEL1BMWriterDataNoFloat)
    (expressions : List NormalizedExpr) (unrefuted : WelcomePEUnrefuted expressions) :
    WelcomePEWriteShape expressions :=
  welcomePEWriteShape_of_writerKindDataFloatRows
    (welcomePEPlainWriterDataFloatRows_of_noFloat plain)
    (welcomePEMatrixReadWriterDataFloatRows_of_noFloat read) float
    (welcomePEL1BMWriterDataFloatRows_of_noFloat l1) expressions unrefuted

/-- **The writer-kind data bundle with the three new packages.**  The float-MAU
component is the unchanged round-49 package. -/
def WelcomePEWriterKindDataFloatRows : Prop :=
  WelcomePEPlainWriterDataFloatRows ∧ WelcomePEMatrixReadWriterDataFloatRows ∧
    WelcomePEFloatMAUWriterData ∧ WelcomePEL1BMWriterDataFloatRows

/-- **The writer-kind data bundle in the no-float form.** -/
def WelcomePEWriterKindDataNoFloat : Prop :=
  WelcomePEPlainWriterDataNoFloat ∧ WelcomePEMatrixReadWriterDataNoFloat ∧
    WelcomePEFloatMAUWriterData ∧ WelcomePEL1BMWriterDataNoFloat

/-- **`WelcomePELm1WriteShapeObligation` from the three new packages and the
float-MAU package.**  This is `welcomePELm1WriteShapeObligation_of_writerKindData`
with the empty-float conjunct removed from the plain, `.matrixRead` and `.l1bm`
packages. -/
theorem welcomePELm1WriteShapeObligation_of_writerKindDataFloatRows
    (plain : WelcomePEPlainWriterDataFloatRows)
    (read : WelcomePEMatrixReadWriterDataFloatRows)
    (float : WelcomePEFloatMAUWriterData) (l1 : WelcomePEL1BMWriterDataFloatRows) :
    WelcomePELm1WriteShapeObligation :=
  fun expressions unrefuted =>
    welcomePEWriteShape_of_writerKindDataFloatRows plain read float l1 expressions unrefuted

/-- **The bundle form** of the obligation theorem above. -/
theorem welcomePELm1WriteShapeObligation_of_writerKindDataFloatRowsBundle
    (residuals : WelcomePEWriterKindDataFloatRows) : WelcomePELm1WriteShapeObligation := by
  obtain ⟨plain, read, float, l1⟩ := residuals
  exact welcomePELm1WriteShapeObligation_of_writerKindDataFloatRows plain read float l1

/-- **`WelcomePELm1WriteShapeObligation` from the no-float packages and the
float-MAU package.**  The strongest form available from this module's route. -/
theorem welcomePELm1WriteShapeObligation_of_writerKindDataNoFloat
    (plain : WelcomePEPlainWriterDataNoFloat)
    (read : WelcomePEMatrixReadWriterDataNoFloat)
    (float : WelcomePEFloatMAUWriterData) (l1 : WelcomePEL1BMWriterDataNoFloat) :
    WelcomePELm1WriteShapeObligation :=
  fun expressions unrefuted =>
    welcomePEWriteShape_of_writerKindDataNoFloat plain read float l1 expressions unrefuted

/-- **The bundle form** of the no-float obligation theorem. -/
theorem welcomePELm1WriteShapeObligation_of_writerKindDataNoFloatBundle
    (residuals : WelcomePEWriterKindDataNoFloat) : WelcomePELm1WriteShapeObligation := by
  obtain ⟨plain, read, float, l1⟩ := residuals
  exact welcomePELm1WriteShapeObligation_of_writerKindDataNoFloat plain read float l1

/-- **The round-49 four-package bundle implies the `.lm1`-free float bundle**
(the conservative direction at the bundle level). -/
theorem welcomePEWriterKindDataFloatRows_of_residuals
    (residuals : WelcomePEWriterKindDataResiduals) : WelcomePEWriterKindDataFloatRows := by
  obtain ⟨plain, read, float, l1⟩ := residuals
  exact ⟨welcomePEPlainWriterDataFloatRows_of_flagFree plain,
    welcomePEMatrixReadWriterDataFloatRows_of_slotFree read, float,
    welcomePEL1BMWriterDataFloatRows_of_data l1⟩

/-- **The round-49 four-package bundle implies the no-float bundle.** -/
theorem welcomePEWriterKindDataNoFloat_of_residuals
    (residuals : WelcomePEWriterKindDataResiduals) : WelcomePEWriterKindDataNoFloat := by
  obtain ⟨plain, read, float, l1⟩ := residuals
  exact ⟨welcomePEPlainWriterDataNoFloat_of_flagFree plain,
    welcomePEMatrixReadWriterDataNoFloat_of_slotFree read, float,
    welcomePEL1BMWriterDataNoFloat_of_data l1⟩

/-- **The round-49 assembly's four packages give the new obligation** — through
the conservative direction and the new assembly.  A consistency check: nothing
proved in `WelcomeAssemblyFinal.lean` is lost by the replacement. -/
theorem welcomePELm1WriteShapeObligation_of_writerKindData_of_old
    (plain : WelcomePEPlainWriterDataFlagFree)
    (read : WelcomePEMatrixReadWriterDataSlotFree)
    (float : WelcomePEFloatMAUWriterData) (l1 : WelcomePEL1BMWriterData) :
    WelcomePELm1WriteShapeObligation :=
  welcomePELm1WriteShapeObligation_of_writerKindDataNoFloat
    (welcomePEPlainWriterDataNoFloat_of_flagFree plain)
    (welcomePEMatrixReadWriterDataNoFloat_of_slotFree read) float
    (welcomePEL1BMWriterDataNoFloat_of_data l1)

end ProofsLean.MNCore

-- End of module: no sorry, no admit, no native_decide, no new axioms.
