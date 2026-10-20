import ProofsLean.WelcomeL1MultiDest
import ProofsLean.WelcomePlainReadPackages

/-! # Welcome optimality, unconditionally

This is the final assembly.  Every writer kind of
`supportedProducer_partition` is now discharged by a theorem, so the per-line
write-shape obligation, the lower bound and the optimality claim carry no
hypotheses.

## The classification

For an unrefuted line with a `.lm1` writer `e`, the issue checker's supported-row
partition gives five top-level cases, and the family case splits into six
producer families.  Each is closed by an unconditional theorem:

| writer kind | theorem |
|---|---|
| plain (`.alu` / `.zero` / `.immediate`) | `welcomePEWriteShape_of_plainWriter_closed` |
| `.matrixRead` | `welcomePEWriteShape_of_matrixReadWriter_closed` |
| matrix MAU | `welcomePEWriteShape_of_matrixMAUWriter` |
| float MAU | `welcomePEWriteShape_of_floatMAUWriter` |
| `.matrixWrite` | phantom case of `welcomePELm1PhantomWriterProvenance` |
| `.l1bm` broadcast (any destination list) | `welcomePEWriteShape_of_l1bmWriter_dataMultiDest` |
| `.l2bm` | phantom case of `welcomePELm1PhantomWriterProvenance` |
| special ALU (`msl`/`msr`, float relu, block float) | `welcomePESpecialALUWriterShapeObligation` |
| PE-inert (`.noforward`, `.wait`, shared-block) | phantom case of `welcomePELm1PhantomWriterProvenance` |
| Rust-unsupported ALU | excluded by `WelcomePEUnrefuted` |
| no `.lm1` writer at all | phantom case of `welcomePELm1PhantomWriterProvenance` |

The plain, `.matrixRead`, matrix-MAU, float-MAU, special-ALU and phantom
components are theorems of `WelcomePlainReadPackages.lean`,
`WelcomeAssemblyFinal.lean`, `WelcomeWriterPackages.lean`,
`WelcomeHalfBlockFloat.lean` and `WelcomeResiduals.lean`; the `.l1bm` component
is `welcomePEL1BMWriterDataMultiDest_holds` of `WelcomeL1MultiDest.lean`, whose
"at most one `.lm1` memory destination" side condition is itself a consequence
of the issue checker's `writesUnique` (`filter_isLm1_le_one_of_accepted`).

## What is proved here

* `welcomePEWriteShape_of_writerKind` — the 7-way writer classification: every
  `.lm1` writer of an unrefuted line yields the line's write shape;
* `welcomePELm1WriteShapeObligation` — the unconditional per-line obligation
  (`weaker` forms of it are `welcomePELm1WriteShapeObligation_of_plainReadL1MultiDest`
  in `WelcomeL1MultiDest.lean` and `welcomePELm1WriteShapeObligation_of_l1NoSingleton`
  in `WelcomePlainReadPackages.lean`, both of which still take package
  hypotheses);
* `welcomeLowerBound_two` — `LowerBound welcomeSealedMachine welcomeSpec 2`;
* `welcomeAnswer_optimal` — `Optimal welcomeSealedMachine welcomeSpec welcomeAnswer`.

No `sorry`, no `admit`, no `native_decide`, no new axioms.  No existing module is
edited.
-/

namespace ProofsLean.MNCore

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

open Issue
open PEMemory

/-! ## 1. The writer-kind classification

The five-way `supportedProducer_partition` case split, with the six family
producers unfolded and every branch closed by its unconditional shape theorem.
This is the "7-way" reading of the writer kinds: plain, `.matrixRead`, float-MAU,
matrix-MAU, `.l1bm`, special-ALU, and phantom (which absorbs `.matrixWrite`,
`.l2bm`, the PE-inert rows and the no-writer case). -/

theorem welcomePEWriteShape_of_writerKind
    (expressions : List NormalizedExpr) (unrefuted : WelcomePEUnrefuted expressions)
    (e : ParsedExpr) (eMem : e ∈ expressions.map NormalizedExpr.toParsed)
    (eWriter : Issue.Bank.lm1 ∈ (e.toIssueExpr 0).writeBanks) :
    WelcomePEWriteShape expressions := by
  have supported := List.all_eq_true.mp unrefuted.1.2.2.2 e eMem
  have notUnsupported : parsedExprIsUnsupportedRustAlu e = false := by
    simpa using (List.any_eq_false.mp unrefuted.1.2.2.1) e eMem
  rcases supportedProducer_partition e supported with
    isPlain | isFamily | isSpecial | isInert | isUnsupported
  · -- plain integer ALU: the closed row shape of `WelcomePlainReadPackages`
    exact welcomePEWriteShape_of_plainWriter_closed expressions unrefuted e eMem isPlain eWriter
  · rcases parsedExprIsFamilyProducer_cases e isFamily with
      readKind | mauKind | floatKind | writeKind | toPEKind | l2Kind
    · -- `.matrixRead`: the closed row shape of `WelcomePlainReadPackages`
      exact welcomePEWriteShape_of_matrixReadWriter_closed expressions unrefuted e eMem
        readKind eWriter
    · -- matrix MAU: unconditional in `WelcomeAssemblyFinal`
      exact welcomePEWriteShape_of_matrixMAUWriter expressions unrefuted e eMem mauKind eWriter
    · -- float MAU: unconditional in `WelcomeWriterPackages`
      exact welcomePEWriteShape_of_floatMAUWriter expressions unrefuted e eMem floatKind eWriter
    · -- `.matrixWrite` is a phantom row
      have hphantom : ∀ x ∈ expressions.map NormalizedExpr.toParsed,
          Issue.Bank.lm1 ∈ (x.toIssueExpr 0).writeBanks → welcomePhantomWriterKind x := by
        intro x xMem xWriter
        have same : x = e :=
          welcomeLm1Writer_eq_of_two expressions unrefuted xMem eMem xWriter eWriter
        rw [same]
        exact Or.inr (Or.inr (Or.inr (Or.inl writeKind)))
      exact welcomePEWriteShape_of_freeStageCommit expressions
        (welcomePELm1PhantomWriterProvenance expressions unrefuted hphantom)
    · -- `.l1bm` broadcast with an arbitrary destination list: multi-dest theorem
      exact welcomePEWriteShape_of_l1bmWriter_dataMultiDest expressions
        (welcomePEL1BMWriterDataForMultiDest_holds expressions unrefuted)
        unrefuted e eMem toPEKind eWriter
    · -- `.l2bm` is a phantom row
      have hphantom : ∀ x ∈ expressions.map NormalizedExpr.toParsed,
          Issue.Bank.lm1 ∈ (x.toIssueExpr 0).writeBanks → welcomePhantomWriterKind x := by
        intro x xMem xWriter
        have same : x = e :=
          welcomeLm1Writer_eq_of_two expressions unrefuted xMem eMem xWriter eWriter
        rw [same]
        exact Or.inr (Or.inr (Or.inr (Or.inr l2Kind)))
      exact welcomePEWriteShape_of_freeStageCommit expressions
        (welcomePELm1PhantomWriterProvenance expressions unrefuted hphantom)
  · -- special ALU: `msl`/`msr`, float relu and block float, all unconditional
    exact welcomePESpecialALUWriterShapeObligation expressions unrefuted
      ⟨e, eMem, eWriter, isSpecial⟩
  · -- PE-inert rows are phantom rows
    have hphantom : ∀ x ∈ expressions.map NormalizedExpr.toParsed,
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
  · -- Rust-unsupported ALU rows are excluded by `WelcomePEUnrefuted`
    rw [notUnsupported] at isUnsupported
    cases isUnsupported

/-! ## 2. The unconditional write-shape obligation -/

/-- **`WelcomePELm1WriteShapeObligation`, with no hypothesis.**  The no-writer
case is vacuous for the phantom provenance (every `.lm1` writer, if any, is
trivially a phantom row), so it needs only `welcomePELm1PhantomWriterProvenance`. -/
theorem welcomePELm1WriteShapeObligation : WelcomePELm1WriteShapeObligation := by
  intro expressions unrefuted
  by_cases hasWriter : ∃ e ∈ expressions.map NormalizedExpr.toParsed,
      Issue.Bank.lm1 ∈ (e.toIssueExpr 0).writeBanks
  · obtain ⟨e, eMem, eWriter⟩ := hasWriter
    exact welcomePEWriteShape_of_writerKind expressions unrefuted e eMem eWriter
  · have hphantom : ∀ x ∈ expressions.map NormalizedExpr.toParsed,
        Issue.Bank.lm1 ∈ (x.toIssueExpr 0).writeBanks → welcomePhantomWriterKind x := by
      intro x xMem xWriter
      exact absurd ⟨x, xMem, xWriter⟩ hasWriter
    exact welcomePEWriteShape_of_freeStageCommit expressions
      (welcomePELm1PhantomWriterProvenance expressions unrefuted hphantom)

/-! ## 3. The lower bound and optimality -/

/-- **`LowerBound welcomeSealedMachine welcomeSpec 2`, unconditionally.**  The
value argument of `WelcomeValueBound.lean` consumes exactly the obligation
above. -/
theorem welcomeLowerBound_two :
    ProofsLean.LowerBound welcomeSealedMachine welcomeSpec 2 :=
  welcomeLowerBound_two_of_lm1WriteShapes welcomePELm1WriteShapeObligation

/-- **`Optimal welcomeSealedMachine welcomeSpec welcomeAnswer`, unconditionally.**
`welcomeAnswer_correct` is already proved, so the lower bound gives optimality. -/
theorem welcomeAnswer_optimal :
    ProofsLean.Optimal welcomeSealedMachine welcomeSpec welcomeAnswer :=
  welcomeAnswer_optimal_of_lm1WriteShapes welcomePELm1WriteShapeObligation

end ProofsLean.MNCore

-- End of module: no sorry, no admit, no native_decide, no new axioms.
