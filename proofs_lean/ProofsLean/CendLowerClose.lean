import ProofsLean.CendTailAssembly
import ProofsLean.CendAnswerCorrect
import ProofsLean.CendTwoLinesJoint
import ProofsLean.CendMatrixFamilies

/-! # `12.convert-endian`: the lower bound at three and `Optimal`

The upper bound is unconditional (`CendTailAssembly.cendAnswerCorrect`).  This
file composes the existing one-line reductions down to the smallest named
residuals in the tree and derives `LowerBound 3` and `Optimal` from them.

## What is already closed (unconditional)

* the empty program, `nop` and `mv` lines (`ConvertEndianLowerBound`);
* `CendClosedLines` (`CendUnconditional`);
* PE-inert / `l1ToPE` rows (`CendNonPlain`);
* mixed-read rows (`CendMixedRead`);
* `msl`/`msr` rows (`CendValueFamilies`).

## What remains

* `CendMatrixFamiliesResidual` — the value-carrying rows not in any of the
  classes above, minus block-float and matrix-MAU rows;
* `CendBlockFloatLinesRefuted` and `CendMatrixMAULinesRefuted` — the two
  explicit value-family refutations that `CendMatrixFamilies` keeps as
  hypotheses;
* `CendTwoLineCommitShape` — the joint shape of a two-line candidate
  (`CendTwoLinesJoint`).

This module does **not** claim these residuals.  It proves the exact logical
composition `one-line residuals → CendPELinesRefuted → LowerBound 3`, and
`one-line residuals + two-line shape → Optimal`. -/

namespace ProofsLean.MNCore

/-- The one-line residual after every closed family has been discharged. -/
structure CendOneLineResiduals : Prop where
  matrixFamilies : CendMatrixFamiliesResidual
  blockFloat : CendBlockFloatLinesRefuted
  matrixMAU : CendMatrixMAULinesRefuted

/-- The complete lower-bound residual. -/
structure CendLowerResiduals : Prop where
  oneLine : CendOneLineResiduals
  twoLine : CendTwoLineCommitShape

/-- **`CendPELinesRefuted` from the minimal one-line residual.** -/
theorem cendPELinesRefuted_of_oneLineResiduals (r : CendOneLineResiduals) :
    CendPELinesRefuted :=
  cendPELinesRefuted_of_nonClosed
    (cendPENonClosedRefuted_of_mixedReadResidual
      (cendMixedReadResidual_of_matrixFamiliesResidual
        r.matrixFamilies r.blockFloat r.matrixMAU))

/-- **`LowerBound cendSealedMachine cendSpec 3` from the complete residual.** -/
theorem cendLowerBound_three_of_narrowedResiduals (r : CendLowerResiduals) :
    ProofsLean.LowerBound cendSealedMachine cendSpec 3 :=
  cendLowerBound_three_of_commitShape
    (cendPELinesRefuted_of_oneLineResiduals r.oneLine) r.twoLine

/-- **`Optimal cendSealedMachine cendSpec cendAnswer` from the complete
residual.**  The upper bound is the unconditional `cendAnswerCorrect`. -/
theorem cendOptimal_of_narrowedResiduals (r : CendLowerResiduals) :
    ProofsLean.Optimal cendSealedMachine cendSpec cendAnswer :=
  cendOptimal_of_commitShape
    (cendPELinesRefuted_of_oneLineResiduals r.oneLine) r.twoLine
    cendAnswer cendAnswerCorrect cendAnswer_length cendAnswer_unitCost

#print axioms cendPELinesRefuted_of_oneLineResiduals
#print axioms cendLowerBound_three_of_narrowedResiduals
#print axioms cendOptimal_of_narrowedResiduals

end ProofsLean.MNCore
