import ProofsLean.WelcomeMatrixMAUZero
import ProofsLean.WelcomeFamilyInstances

/-! # Unconditional writer-side shape instances

`WelcomeMatrixMAUShape.lean` and `WelcomeFamilyInstances.lean` state the
matrix-MAU row, stage and writer shapes conditional on the datapath statement
`WelcomePEMatrixMAUZeroBus` (every bus produced by a matrix-MAU cycle at the
all-zero state has a zero low half).  `WelcomeMatrixMAUZero.lean` proves that
statement (`welcomePEMatrixMAUZeroBus`).  This module supplies it, so the
matrix-MAU shapes hold with no datapath hypothesis:

* `WelcomePEMatrixMAUProducer_zeroShape_static` — the row shape at the all-zero
  state, static width instantiated: the PE 0 prepared write list is committed at
  `welcomeZeroFiles` and is all copied `.double` blocks or fits in four narrow
  windows.
* `WelcomePEMatrixMAUAndWrites_zeroShape_static` — the same for the whole
  matrix-MAU/write stage.
* `welcomePEWriteShape_of_matrixMAUWriter_of_inertCompanions_unconditional` —
  the line shape when the matrix-MAU row is the only PE-register writer and all
  companions are PE-inert.
* `welcomePEWriteShape_singleton_of_matrixMAU` — the one-row instance.

Each statement is the conditional statement with `zeroBus` supplied; no other
hypothesis is changed, weakened or strengthened.

## The uniform interface over the writer kinds

The other writer-side instances were already unconditional.  They are
re-exported here under the same `_unconditional` naming so that downstream code
can treat all writer kinds uniformly:

| writer kind    | line-level instance                                                  | one-row instance                                        |
| -------------- | -------------------------------------------------------------------- | ------------------------------------------------------- |
| plain          | `welcomePEWriteShape_of_plainWriter_unconditional`                    | —                                                        |
| `.matrixRead`  | `welcomePEWriteShape_of_matrixReadWriter_unconditional`               | —                                                        |
| float MAU      | `welcomePEWriteShape_of_floatMAUWriter_of_inertCompanions_unconditional` | `welcomePEWriteShape_singleton_of_floatMAU_unconditional` |
| matrix MAU     | `welcomePEWriteShape_of_matrixMAUWriter_of_inertCompanions_unconditional` | `welcomePEWriteShape_singleton_of_matrixMAU`          |
| `.l1bm`        | `welcomePEWriteShape_of_l1bmWriter_of_integerOrInert_unconditional`  | `welcomePEWriteShape_singleton_of_l1bmMemLm1_unconditional` |

The aliases have exactly the statements of the underlying theorems
(`welcomePEWriteShape_of_plainWriter`, `welcomePEWriteShape_of_matrixReadWriter`,
`welcomePEWriteShape_of_floatMAUWriter_of_inertCompanions`,
`welcomePEWriteShape_singleton_of_floatMAU`,
`welcomePEWriteShape_of_l1bmWriter_of_integerOrInert`,
`welcomePEWriteShape_singleton_of_l1bmMemLm1`); the `_unconditional` suffix only
records that no datapath statement is outstanding for these kinds.

## What is still not proved

None of the six family `Prop`s of `WelcomeValueBound.lean` §7 is proved here.
Each of them also quantifies over lines in which the family row is not the
unique `.lm1` writer, and in that case the line shape is decided by another row:
`WelcomeFamilyInstances.lean` §4 records that remainder, as does the round-42
note on write-list-level `.lm1` provenance of the middle stages.  Consequently
neither `LowerBound 2` nor `Optimal` is claimed.

No `sorry`, no `admit`, no `native_decide`, no new axiom, and no existing module
is edited by this file. -/

namespace ProofsLean.MNCore

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false

open Issue
open PEMemory

/-! ## 1. The matrix-MAU datapath statement, supplied -/

/-- **The matrix-MAU row shape at the all-zero state, with the row's static
width instantiated and no datapath hypothesis.**  As
`executeParsedMatrixMAUProducer_zeroShape_static_of_zeroBus`, with
`zeroBus := welcomePEMatrixMAUZeroBus` (`WelcomeMatrixMAUZero.lean`). -/
theorem WelcomePEMatrixMAUProducer_zeroShape_static
    (expressions : List ParsedExpr) (expression : ParsedExpr) (next : State)
    (noForward hasSingleLineMask : Bool)
    (filterResult : expressions.filter parsedExprIsMatrixMAUProducer = [expression])
    (nodup : (expression.toIssueExpr 0).writeBanks.Nodup)
    (executed : executeParsedMatrixMAUProducer (welcomeInitialState welcomeZeroWords)
      (welcomeInitialState welcomeZeroWords) expressions noForward hasSingleLineMask = .ok next) :
    ∃ writes, next.peRegisters welcomePE = commitParsedMaskedWrites welcomeZeroFiles writes ∧
      (Lm1WritesDoubleCopy writes ∨ Lm1WritesNarrow writes) :=
  executeParsedMatrixMAUProducer_zeroShape_static_of_zeroBus welcomePEMatrixMAUZeroBus
    expressions expression next noForward hasSingleLineMask filterResult nodup executed

/-- **The matrix-MAU/write stage shape at the all-zero state, with no datapath
hypothesis.**  As `executeParsedMatrixMAUAndWrites_zeroShape_static_of_zeroBus`,
with `zeroBus := welcomePEMatrixMAUZeroBus`. -/
theorem WelcomePEMatrixMAUAndWrites_zeroShape_static
    (expressions : List ParsedExpr) (expression : ParsedExpr) (next : State)
    (noForward hasSingleLineMask : Bool)
    (filterResult : expressions.filter parsedExprIsMatrixMAUProducer = [expression])
    (nodup : (expression.toIssueExpr 0).writeBanks.Nodup)
    (executed : executeParsedMatrixMAUAndWrites (welcomeInitialState welcomeZeroWords)
      (welcomeInitialState welcomeZeroWords) expressions noForward hasSingleLineMask = .ok next) :
    ∃ writes, next.peRegisters welcomePE = commitParsedMaskedWrites welcomeZeroFiles writes ∧
      (Lm1WritesDoubleCopy writes ∨ Lm1WritesNarrow writes) :=
  executeParsedMatrixMAUAndWrites_zeroShape_static_of_zeroBus welcomePEMatrixMAUZeroBus
    expressions expression next noForward hasSingleLineMask filterResult nodup executed

/-! ## 2. The matrix-MAU writer line instances -/

/-- **The matrix-MAU writer line shape, unconditional.**  As
`welcomePEWriteShape_of_matrixMAUWriter_of_inertCompanions`, with
`zeroBus := welcomePEMatrixMAUZeroBus`. -/
theorem welcomePEWriteShape_of_matrixMAUWriter_of_inertCompanions_unconditional
    (expressions : List NormalizedExpr) (e : ParsedExpr)
    (_mau : parsedExprIsMatrixMAUProducer e = true)
    (nodup : (e.toIssueExpr 0).writeBanks.Nodup)
    (mauFilter : (expressions.map NormalizedExpr.toParsed).filter
      parsedExprIsMatrixMAUProducer = [e])
    (floatNil : (expressions.map NormalizedExpr.toParsed).filter
      parsedExprIsSupportedFloatMAUProducer = [])
    (intAll : ∀ x ∈ (expressions.map NormalizedExpr.toParsed).filter
      parsedExprIsIntegerMatrixReadStageInput, x.op = .noforward)
    (mslNil : (expressions.map NormalizedExpr.toParsed).filter
      parsedExprIsMslMsrProducer = [])
    (reluNil : (expressions.map NormalizedExpr.toParsed).filter
      parsedExprIsFloatReluProducer = [])
    (blockNil : (expressions.map NormalizedExpr.toParsed).filter
      parsedExprIsBlockFloatProducer = [])
    (l1Nil : (expressions.map NormalizedExpr.toParsed).filter
      parsedExprIsL1ToPEProducer = []) :
    WelcomePEWriteShape expressions :=
  welcomePEWriteShape_of_matrixMAUWriter_of_inertCompanions welcomePEMatrixMAUZeroBus
    expressions e _mau nodup mauFilter floatNil intAll mslNil reluNil blockNil l1Nil

/-- **The one-row matrix-MAU writer instance, unconditional.**  As
`welcomePEWriteShape_singleton_of_matrixMAU_of_zeroBus`, with
`zeroBus := welcomePEMatrixMAUZeroBus`. -/
theorem welcomePEWriteShape_singleton_of_matrixMAU (expression : NormalizedExpr)
    (mau : parsedExprIsMatrixMAUProducer expression.toParsed = true)
    (nodup : (expression.toParsed.toIssueExpr 0).writeBanks.Nodup) :
    WelcomePEWriteShape [expression] :=
  welcomePEWriteShape_singleton_of_matrixMAU_of_zeroBus welcomePEMatrixMAUZeroBus
    expression mau nodup

/-! ## 3. The uniform interface over the writer kinds

The instances below were already unconditional; they are restated under the
`_unconditional` suffix with exactly their original statements, so that all
writer kinds expose the same naming. -/

/-- **The plain-writer line shape, unconditional.**  As
`welcomePEWriteShape_of_plainWriter`. -/
theorem welcomePEWriteShape_of_plainWriter_unconditional
    (expressions : List NormalizedExpr) (unrefuted : WelcomePEUnrefuted expressions)
    (intOrInert : (expressions.map NormalizedExpr.toParsed).all
      welcomeIntegerOrInertLine = true)
    (before after : List ParsedExpr) (e : ParsedExpr)
    (split : (expressions.map NormalizedExpr.toParsed).filter
        parsedExprIsIntegerMatrixReadStageInput = before ++ e :: after)
    (skipBefore : ∀ expression ∈ before,
      expression.op = .noforward ∨ ∃ tag : Fin 256, expression.op = .wait tag)
    (skipAfter : ∀ expression ∈ after,
      expression.op = .noforward ∨ ∃ tag : Fin 256, expression.op = .wait tag)
    (flagEq : ((expressions.map NormalizedExpr.toParsed).filter
        parsedExprIsIntegerMatrixReadStageInput).any parsedExprHasSingleLineWriteMask =
        parsedExprHasSingleLineWriteMask e)
    (notDouble : ∀ payload sparse, e.op = .immediate payload sparse →
      ∀ destination ∈ e.destinations,
        ParsedOperand.directDestinationBankWidth? destination ≠
          some (PEMemory.Bank.lm1, PEMemory.Width.double))
    (nodup : (e.toIssueExpr 0).writeBanks.Nodup)
    (plain : parsedExprIsPlainIntegerALU e = true) :
    WelcomePEWriteShape expressions :=
  welcomePEWriteShape_of_plainWriter expressions unrefuted intOrInert before after e split
    skipBefore skipAfter flagEq notDouble nodup plain

/-- **The `.matrixRead`-writer line shape, unconditional.**  As
`welcomePEWriteShape_of_matrixReadWriter`. -/
theorem welcomePEWriteShape_of_matrixReadWriter_unconditional
    (expressions : List NormalizedExpr) (unrefuted : WelcomePEUnrefuted expressions)
    (intOrInert : (expressions.map NormalizedExpr.toParsed).all
      welcomeIntegerOrInertLine = true)
    (before after : List ParsedExpr) (e : ParsedExpr)
    (split : (expressions.map NormalizedExpr.toParsed).filter
        parsedExprIsIntegerMatrixReadStageInput = before ++ e :: after)
    (skipBefore : ∀ expression ∈ before,
      expression.op = .noforward ∨ ∃ tag : Fin 256, expression.op = .wait tag)
    (skipAfter : ∀ expression ∈ after,
      expression.op = .noforward ∨ ∃ tag : Fin 256, expression.op = .wait tag)
    (precision : ParsedPrecision) (sideY : Bool) (width : Fin 5) (row : Fin (2 ^ 32))
    (op : e.op = .matrixRead precision)
    (sources : e.sources = [.matrix sideY width (some row)])
    (staticW : PEMemory.Width)
    (nodup : (e.toIssueExpr 0).writeBanks.Nodup)
    (staticWidth : ∀ destination ∈ e.destinations, ∀ v : PEMemory.Width,
      ParsedOperand.directDestinationBankWidth? destination =
        some (PEMemory.Bank.lm1, v) → v = staticW) :
    WelcomePEWriteShape expressions :=
  welcomePEWriteShape_of_matrixReadWriter expressions unrefuted intOrInert before after e split
    skipBefore skipAfter precision sideY width row op sources staticW nodup staticWidth

/-- **The float-MAU writer line shape, unconditional.**  As
`welcomePEWriteShape_of_floatMAUWriter_of_inertCompanions`. -/
theorem welcomePEWriteShape_of_floatMAUWriter_of_inertCompanions_unconditional
    (expressions : List NormalizedExpr) (e : ParsedExpr)
    (float : parsedExprIsSupportedFloatMAUProducer e = true)
    (nodup : (e.toIssueExpr 0).writeBanks.Nodup)
    (floatFilter : (expressions.map NormalizedExpr.toParsed).filter
      parsedExprIsSupportedFloatMAUProducer = [e])
    (intAll : ∀ x ∈ (expressions.map NormalizedExpr.toParsed).filter
      parsedExprIsIntegerMatrixReadStageInput, x.op = .noforward)
    (mslNil : (expressions.map NormalizedExpr.toParsed).filter
      parsedExprIsMslMsrProducer = [])
    (reluNil : (expressions.map NormalizedExpr.toParsed).filter
      parsedExprIsFloatReluProducer = [])
    (blockNil : (expressions.map NormalizedExpr.toParsed).filter
      parsedExprIsBlockFloatProducer = [])
    (mmauNil : (expressions.map NormalizedExpr.toParsed).filter
      parsedExprIsMatrixMAUProducer = [])
    (l2bmNil : (expressions.map NormalizedExpr.toParsed).filter
      parsedExprIsL2BMProducer = [])
    (l1Nil : (expressions.map NormalizedExpr.toParsed).filter
      parsedExprIsL1ToPEProducer = []) :
    WelcomePEWriteShape expressions :=
  welcomePEWriteShape_of_floatMAUWriter_of_inertCompanions expressions e float nodup
    floatFilter intAll mslNil reluNil blockNil mmauNil l2bmNil l1Nil

/-- **The one-row float-MAU writer instance, unconditional.**  As
`welcomePEWriteShape_singleton_of_floatMAU`. -/
theorem welcomePEWriteShape_singleton_of_floatMAU_unconditional (expression : NormalizedExpr)
    (float : parsedExprIsSupportedFloatMAUProducer expression.toParsed = true)
    (nodup : (expression.toParsed.toIssueExpr 0).writeBanks.Nodup) :
    WelcomePEWriteShape [expression] :=
  welcomePEWriteShape_singleton_of_floatMAU expression float nodup

/-- **The `.l1bm`-broadcast writer line shape, unconditional.**  As
`welcomePEWriteShape_of_l1bmWriter_of_integerOrInert`. -/
theorem welcomePEWriteShape_of_l1bmWriter_of_integerOrInert_unconditional
    (expressions : List NormalizedExpr) (before after : List ParsedExpr) (e : ParsedExpr)
    (access : ParsedL1ToPEAccess) (memoryAccess : Access)
    (negated extended rounded : Bool) (mask : Option ParsedMask) (w : PEMemory.Width)
    (decomposition : expressions.map NormalizedExpr.toParsed = before ++ e :: after)
    (intOrInertBefore : ∀ item ∈ before, welcomeIntegerOrInertLine item = true)
    (intOrInertAfter : ∀ item ∈ after, welcomeIntegerOrInertLine item = true)
    (lowered : lowerParsedL1ToPE? e = some access)
    (destinations : access.destinations =
      [ParsedOperand.mem memoryAccess negated extended rounded mask])
    (static : ParsedOperand.directDestinationBankWidth?
      (ParsedOperand.mem memoryAccess negated extended rounded mask) =
      some (PEMemory.Bank.lm1, w))
    (noLm1 : ∀ item ∈ (before ++ e :: after).filter
      parsedExprIsIntegerMatrixReadStageInput, WelcomeRowHasNoLm1Destination item) :
    WelcomePEWriteShape expressions :=
  welcomePEWriteShape_of_l1bmWriter_of_integerOrInert expressions before after e access
    memoryAccess negated extended rounded mask w decomposition intOrInertBefore intOrInertAfter
    lowered destinations static noLm1

/-- **The one-row `.l1bm`-broadcast writer instance, unconditional.**  As
`welcomePEWriteShape_singleton_of_l1bmMemLm1`. -/
theorem welcomePEWriteShape_singleton_of_l1bmMemLm1_unconditional
    (expression : NormalizedExpr) (access : ParsedL1ToPEAccess)
    (memoryAccess : Access) (negated extended rounded : Bool) (mask : Option ParsedMask)
    (w : PEMemory.Width)
    (lowered : lowerParsedL1ToPE? expression.toParsed = some access)
    (destinations : access.destinations =
      [ParsedOperand.mem memoryAccess negated extended rounded mask])
    (static : ParsedOperand.directDestinationBankWidth?
      (ParsedOperand.mem memoryAccess negated extended rounded mask) =
      some (PEMemory.Bank.lm1, w)) :
    WelcomePEWriteShape [expression] :=
  welcomePEWriteShape_singleton_of_l1bmMemLm1 expression access memoryAccess negated
    extended rounded mask w lowered destinations static

end ProofsLean.MNCore
