import ProofsLean.WelcomeStageProvenance
import ProofsLean.WelcomeMatrixMAUUnconditional
import ProofsLean.WelcomeWriterShape

/-! # Unique-writer dispatch

`WelcomeAssembly.lean` / `WelcomeMatrixMAUCommit.lean` reduce an unrefuted `.pe`
line to the commit of six stage write lists

```
next.peRegisters welcomePE =
  commitParsedMaskedWrites initial
    (intWrites ++ mslWrites ++ reluWrites ++ blockWrites ++ matrixWrites ++ l1Writes)
```

(`welcomePE_line_stage_commit_unconditional`), and `WelcomeWriterShape.lean`
shows how a *single* shaped block inside such a concatenation decides the line's
`WelcomePEWriteShape`, provided the other blocks write no `.lm1` word at all.
`WelcomeStageProvenance.lean` (round 44) supplies exactly that `.lm1`-freeness
for the five middle-stage lists, and `WelcomeIntegerProvenance.lean`
(`welcomeIntegerPrep_lm1_free`) for the integer stage's list.

This module puts the two halves together: it dispatches on **which stage list
contains the line's unique `.lm1` writer** and derives the line shape from that
row's own shape, with the remaining stage lists `.lm1`-free.

## What is proved

* §1 the block algebra: `Lm1WritesShape` and its stability under prefix/suffix
  `.lm1`-free blocks (`lm1WritesShape_append_free_split`,
  `lm1WritesShape_of_append_split`), plus six positional corollaries
  (`lm1WritesShape_of_six_first` … `_sixth`) matching the order of the stage
  concatenation.
* §2 three `.lm1`-freeness bundles — the four "shared-block" middle stages minus
  matrix-MAU (`WelcomePEMiddleStageLm1Free`), the matrix-MAU/write stage
  (`WelcomePEMatrixMAUStageLm1Free`) and the L1BM-to-PE stage
  (`WelcomePEL1StageLm1Free`) — because the last two are each the *writer's* stage
  for one writer kind — together with their projections and their derivation from
  the row-local statement `∀ x ∈ line, x ≠ e → WelcomeRowHasNoLm1Destination x`
  (`..._of_rows`).
* §3 the two filter bridges: the per-PE walk's outer filter keeps every
  integer-stage row and every float-MAU row, so the walk's integer and float row
  filters are the line's (`welcomePEWalkFilter_integer`,
  `welcomePEWalkFilter_float`).
* §4 the chain replay: six stage lists with their commit equations give the
  line's commit of the concatenation
  (`executeIntegerProducerInstructionLine_pe_commit_split`).
* §5 the integer stage's decomposition into its prepared list plus the float-MAU
  list (`executeIntegerProducerLineAtPECore_prepared_float`,
  `executeIntegerProducerLineAtPEs_zero_prepared_float`), and the
  matrix-MAU/write stage shape at an arbitrary current state
  (`executeParsedMatrixMAUAndWrites_shape_of_filter_singleton`).
* §6 the five stage-level dispatch theorems, one per writer kind:

  | writer kind   | stage / list carrying the writer            |
  | ------------- | ------------------------------------------- |
  | plain         | integer stage (`intWrites`)                  |
  | `.matrixRead` | integer stage (`intWrites`)                  |
  | float MAU     | integer stage (`intWrites`, float component) |
  | matrix MAU    | matrix-MAU/write stage (`matrixWrites`)      |
  | `.l1bm`       | L1BM-to-PE stage (`l1Writes`)                |

  Each concludes `WelcomePEWriteShape expressions` from the six-list commit plus
  the writer's own row shape and the `.lm1`-freeness of every stage list other
  than the writer's.
* §7 the five **unique-writer** corollaries (`..._of_plainWriter_unique`, …): the
  `.lm1`-freeness hypotheses are replaced by the row-local statement that every
  row other than the writer has no `.lm1` destination operand, i.e. that `e` is
  the line's unique `.lm1` row.

### No `WelcomePEUnrefuted` hypothesis

Unlike `welcomePE_line_stage_commit_unconditional` and the writer-side instances of
`WelcomeMatrixMAUUnconditional.lean`, the ten theorems below take **no**
`WelcomePEUnrefuted` argument.  Every condition on the line they need is read off
the step equation itself (`executeIntegerProducerInstructionLine_pe_conditions`:
acceptance, no pending wait, no unsupported Rust ALU, all rows supported), so they
apply to every `.pe` line — a line whose step does not exist satisfies the goal
vacuously through `welcomePEWriteShape_of_commit_shape`.

## The hypotheses that are *not* derived here

The stage-level statements take the stage facts explicitly, exactly in the shape
the round-43/44 notes prescribe; the §7 corollaries reduce them to the writers'
own data:

* the three `.lm1`-freeness bundles — every row of the corresponding stage filter
  has no `.lm1` destination operand.  They are the hypotheses of the round-44
  bundle `welcomePEStageLm1ProvenanceForm`, which is *applied* here (so the write
  lists are produced, not assumed).  In §7 they follow from the row-local
  uniqueness statement plus the writer's "not a producer of the other stages"
  facts.
* the syntactic bridge from `welcomeLm1Writer_unique` (which speaks about
  `writeBanks` and expression ids) to the row-local statement is **not**
  formalised: §7 takes the row-local statement as a hypothesis.  It is weaker
  than `welcomeLm1Writer_unique` plus acceptance only in that it is stated on
  destination operands rather than on the projected `writeBanks`.
* `floatEmpty` — the line has no float-MAU row — for the four writer kinds outside
  the float-MAU one.  Float-MAU rows execute *inside* the integer stage, and their
  write list has no `Lm1FreePreparedWrites` lemma (only the bank-level
  `executeParsedFloatMAUsAtPE_lm1_free`), so a float-MAU companion would need a
  sixth provenance not present in `WelcomeStageProvenance.lean`.  With
  `floatEmpty` the integer stage's list is precisely `welcomeIntegerPrep`'s, which
  is where `intFree`/`welcomeIntegerPrep_lm1_free` apply.  (For the integer-stage
  writer kinds `intFree` is not needed at all: the writer's list is shaped, not
  free.)
* for the three integer-stage writer kinds the companions *inside* the integer
  stage must be `.noforward` / `.wait` rows (`welcomeIntegerPrep_single_writer`),
  and for the float-MAU writer they must all be `.noforward`
  (`welcomeIntegerPrep_noforward`, inside
  `executeIntegerProducerLineAtPEs_floatWriter`).  Rows of the four/five middle
  stages and of the shared-block stage are unrestricted.
* `mauFilter = [e]` / `l1Filter = [e]` — the writer's own middle stage has a
  singleton filter.  (Their executors fail on two rows, so this is exactly the
  non-empty case; the empty case has no writer of that kind.)

No `sorry`, no `admit`, no `native_decide`, no new axioms, and no existing
module is edited by this file.  Neither `LowerBound 2` nor `Optimal` is claimed.
-/

namespace ProofsLean.MNCore

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open Issue
open PEMemory

/-! ## 1. The block algebra of the stage concatenation -/

/-- The `.lm1` shape disjunction used by both `welcomePE*Shape` predicates. -/
def Lm1WritesShape (writes : List PreparedParsedMaskedWrite) : Prop :=
  Lm1WritesDoubleCopy writes ∨ Lm1WritesNarrow writes

theorem lm1WritesShape_of_double {writes : List PreparedParsedMaskedWrite}
    (shape : Lm1WritesDoubleCopy writes) : Lm1WritesShape writes :=
  Or.inl shape

theorem lm1WritesShape_of_narrow {writes : List PreparedParsedMaskedWrite}
    (shape : Lm1WritesNarrow writes) : Lm1WritesShape writes :=
  Or.inr shape

/-- **An `.lm1`-free prefix and suffix leave the shape to the middle block.** -/
theorem lm1WritesShape_append_free_split (leading middle trailing :
    List PreparedParsedMaskedWrite)
    (freeLeading : Lm1FreePreparedWrites leading)
    (shapeMiddle : Lm1WritesShape middle)
    (freeTrailing : Lm1FreePreparedWrites trailing) :
    Lm1WritesShape (leading ++ (middle ++ trailing)) := by
  rcases shapeMiddle with double | narrow
  · exact Or.inl (lm1WritesDoubleCopy_append_of_only_right leading (middle ++ trailing)
      (lm1WritesDoubleCopy_append_of_only middle trailing double freeTrailing) freeLeading)
  · exact Or.inr (lm1WritesNarrow_append_of_only_right leading (middle ++ trailing)
      (lm1WritesNarrow_append_of_only middle trailing narrow freeTrailing) freeLeading)

/-- **The shape of a concatenation from a split into three blocks.** -/
theorem lm1WritesShape_of_append_split {writes leading middle trailing :
    List PreparedParsedMaskedWrite}
    (split : writes = leading ++ (middle ++ trailing))
    (freeLeading : Lm1FreePreparedWrites leading)
    (shapeMiddle : Lm1WritesShape middle)
    (freeTrailing : Lm1FreePreparedWrites trailing) :
    Lm1WritesShape writes := by
  rw [split]
  exact lm1WritesShape_append_free_split leading middle trailing freeLeading shapeMiddle
    freeTrailing

/-- Freeness of a right-associated two-block concatenation. -/
theorem lm1FreePreparedWrites_two (a b : List PreparedParsedMaskedWrite)
    (ha : Lm1FreePreparedWrites a) (hb : Lm1FreePreparedWrites b) :
    Lm1FreePreparedWrites (a ++ b) := by
  intro write member
  rcases List.mem_append.mp member with head | tail
  · exact ha write head
  · exact hb write tail

/-- Freeness of a right-associated three-block concatenation. -/
theorem lm1FreePreparedWrites_three (a b c : List PreparedParsedMaskedWrite)
    (ha : Lm1FreePreparedWrites a) (hb : Lm1FreePreparedWrites b)
    (hc : Lm1FreePreparedWrites c) :
    Lm1FreePreparedWrites (a ++ (b ++ c)) := by
  intro write member
  rcases List.mem_append.mp member with head | tail
  · exact ha write head
  · rcases List.mem_append.mp tail with middle | last
    · exact hb write middle
    · exact hc write last

/-- Freeness of a right-associated four-block concatenation. -/
theorem lm1FreePreparedWrites_four (a b c d : List PreparedParsedMaskedWrite)
    (ha : Lm1FreePreparedWrites a) (hb : Lm1FreePreparedWrites b)
    (hc : Lm1FreePreparedWrites c) (hd : Lm1FreePreparedWrites d) :
    Lm1FreePreparedWrites (a ++ (b ++ (c ++ d))) := by
  intro write member
  rcases List.mem_append.mp member with first | tail
  · exact ha write first
  · rcases List.mem_append.mp tail with second | tail
    · exact hb write second
    · rcases List.mem_append.mp tail with third | last
      · exact hc write third
      · exact hd write last

/-- Freeness of a right-associated five-block concatenation. -/
theorem lm1FreePreparedWrites_five (a b c d e : List PreparedParsedMaskedWrite)
    (ha : Lm1FreePreparedWrites a) (hb : Lm1FreePreparedWrites b)
    (hc : Lm1FreePreparedWrites c) (hd : Lm1FreePreparedWrites d)
    (he : Lm1FreePreparedWrites e) :
    Lm1FreePreparedWrites (a ++ (b ++ (c ++ (d ++ e)))) := by
  intro write member
  rcases List.mem_append.mp member with first | tail
  · exact ha write first
  · rcases List.mem_append.mp tail with second | tail
    · exact hb write second
    · rcases List.mem_append.mp tail with third | tail
      · exact hc write third
      · rcases List.mem_append.mp tail with fourth | last
        · exact hd write fourth
        · exact he write last

/-- The first block (`intWrites`) is the writer's. -/
theorem lm1WritesShape_of_six_first (a b c d e f : List PreparedParsedMaskedWrite)
    (shape : Lm1WritesShape a)
    (hb : Lm1FreePreparedWrites b) (hc : Lm1FreePreparedWrites c)
    (hd : Lm1FreePreparedWrites d) (he : Lm1FreePreparedWrites e)
    (hf : Lm1FreePreparedWrites f) :
    Lm1WritesShape (a ++ b ++ c ++ d ++ e ++ f) := by
  refine lm1WritesShape_of_append_split (leading := []) (middle := a)
    (trailing := b ++ (c ++ (d ++ (e ++ f)))) ?_ lm1FreePreparedWrites_nil shape ?_
  · show a ++ b ++ c ++ d ++ e ++ f = ([] : List PreparedParsedMaskedWrite) ++ (a ++ (b ++ (c ++ (d ++ (e ++ f)))))
    simp
  · exact lm1FreePreparedWrites_five b c d e f hb hc hd he hf

/-- The second block (`mslWrites`) is the writer's. -/
theorem lm1WritesShape_of_six_second (a b c d e f : List PreparedParsedMaskedWrite)
    (ha : Lm1FreePreparedWrites a) (shape : Lm1WritesShape b)
    (hc : Lm1FreePreparedWrites c) (hd : Lm1FreePreparedWrites d)
    (he : Lm1FreePreparedWrites e) (hf : Lm1FreePreparedWrites f) :
    Lm1WritesShape (a ++ b ++ c ++ d ++ e ++ f) := by
  refine lm1WritesShape_of_append_split (leading := a) (middle := b)
    (trailing := c ++ (d ++ (e ++ f))) ?_ ha shape ?_
  · show a ++ b ++ c ++ d ++ e ++ f = a ++ (b ++ (c ++ (d ++ (e ++ f))))
    simp
  · exact lm1FreePreparedWrites_four c d e f hc hd he hf

/-- The third block (`reluWrites`) is the writer's. -/
theorem lm1WritesShape_of_six_third (a b c d e f : List PreparedParsedMaskedWrite)
    (ha : Lm1FreePreparedWrites a) (hb : Lm1FreePreparedWrites b)
    (shape : Lm1WritesShape c)
    (hd : Lm1FreePreparedWrites d) (he : Lm1FreePreparedWrites e)
    (hf : Lm1FreePreparedWrites f) :
    Lm1WritesShape (a ++ b ++ c ++ d ++ e ++ f) := by
  refine lm1WritesShape_of_append_split (leading := a ++ b) (middle := c)
    (trailing := d ++ (e ++ f)) ?_
    (lm1FreePreparedWrites_two a b ha hb) shape ?_
  · show a ++ b ++ c ++ d ++ e ++ f = (a ++ b) ++ (c ++ (d ++ (e ++ f)))
    simp
  · exact lm1FreePreparedWrites_three d e f hd he hf

/-- The fourth block (`blockWrites`) is the writer's. -/
theorem lm1WritesShape_of_six_fourth (a b c d e f : List PreparedParsedMaskedWrite)
    (ha : Lm1FreePreparedWrites a) (hb : Lm1FreePreparedWrites b)
    (hc : Lm1FreePreparedWrites c) (shape : Lm1WritesShape d)
    (he : Lm1FreePreparedWrites e) (hf : Lm1FreePreparedWrites f) :
    Lm1WritesShape (a ++ b ++ c ++ d ++ e ++ f) := by
  refine lm1WritesShape_of_append_split (leading := a ++ (b ++ c)) (middle := d)
    (trailing := e ++ f) ?_
    (lm1FreePreparedWrites_three a b c ha hb hc) shape ?_
  · show a ++ b ++ c ++ d ++ e ++ f = (a ++ (b ++ c)) ++ (d ++ (e ++ f))
    simp
  · exact lm1FreePreparedWrites_two e f he hf

/-- The fifth block (`matrixWrites`) is the writer's. -/
theorem lm1WritesShape_of_six_fifth (a b c d e f : List PreparedParsedMaskedWrite)
    (ha : Lm1FreePreparedWrites a) (hb : Lm1FreePreparedWrites b)
    (hc : Lm1FreePreparedWrites c) (hd : Lm1FreePreparedWrites d)
    (shape : Lm1WritesShape e) (hf : Lm1FreePreparedWrites f) :
    Lm1WritesShape (a ++ b ++ c ++ d ++ e ++ f) := by
  refine lm1WritesShape_of_append_split (leading := a ++ (b ++ (c ++ d))) (middle := e)
    (trailing := f) ?_
    (lm1FreePreparedWrites_four a b c d ha hb hc hd) shape hf
  show a ++ b ++ c ++ d ++ e ++ f = (a ++ (b ++ (c ++ d))) ++ (e ++ f)
  simp

/-- The sixth block (`l1Writes`) is the writer's. -/
theorem lm1WritesShape_of_six_sixth (a b c d e f : List PreparedParsedMaskedWrite)
    (ha : Lm1FreePreparedWrites a) (hb : Lm1FreePreparedWrites b)
    (hc : Lm1FreePreparedWrites c) (hd : Lm1FreePreparedWrites d)
    (he : Lm1FreePreparedWrites e) (shape : Lm1WritesShape f) :
    Lm1WritesShape (a ++ b ++ c ++ d ++ e ++ f) := by
  refine lm1WritesShape_of_append_split (leading := a ++ (b ++ (c ++ (d ++ e))))
    (middle := f) (trailing := []) ?_
    (lm1FreePreparedWrites_five a b c d e ha hb hc hd he) shape
    lm1FreePreparedWrites_nil
  show a ++ b ++ c ++ d ++ e ++ f = (a ++ (b ++ (c ++ (d ++ e)))) ++ (f ++ [])
  simp

/-! ## 2. The middle-stage freeness bundle

Each component is exactly one hypothesis consumed by the round-44 bundle
`welcomePEStageLm1ProvenanceForm`, and says that no row executed by that stage
names bank `.lm1` in a destination operand.  The bundle is split because for the
matrix-MAU writer (resp. the `.l1bm` writer) the matrix-MAU/write stage (resp. the
L1BM-to-PE stage) is the *writer's* stage: then its rows do name `.lm1`, and the
corresponding component must not be demanded. -/

/-- **The three "shared-block" middle stages prepare no `.lm1` word**, row by
row.  The matrix-MAU/write stage and the L1BM-to-PE stage are kept separate
(`WelcomePEMatrixMAUStageLm1Free`, `WelcomePEL1StageLm1Free`) because each of them
is the *writer's* stage for one writer kind, and then its rows do name `.lm1`. -/
def WelcomePEMiddleStageLm1Free (expressions : List NormalizedExpr) : Prop :=
  (∀ expression ∈ (expressions.map NormalizedExpr.toParsed).filter
      parsedExprIsMslMsrProducer, WelcomeRowHasNoLm1Destination expression) ∧
  (∀ expression ∈ (expressions.map NormalizedExpr.toParsed).filter
      parsedExprIsFloatReluProducer, WelcomeRowHasNoLm1Destination expression) ∧
    (∀ expression ∈ (expressions.map NormalizedExpr.toParsed).filter
      parsedExprIsBlockFloatProducer, WelcomeRowHasNoLm1Destination expression)

/-- **The matrix-MAU/write stage prepares no `.lm1` word.** -/
def WelcomePEMatrixMAUStageLm1Free (expressions : List NormalizedExpr) : Prop :=
  ∀ expression ∈ (expressions.map NormalizedExpr.toParsed).filter
    parsedExprIsMatrixMAUProducer, WelcomeRowHasNoLm1Destination expression

/-- **The L1BM-to-PE stage prepares no `.lm1` word**, row by row.  It is kept
apart from `WelcomePEMiddleStageLm1Free` because for the `.l1bm` writer this stage
is the *writer's* stage, and its rows then do name bank `.lm1`. -/
def WelcomePEL1StageLm1Free (expressions : List NormalizedExpr) : Prop :=
  ∀ expression ∈ (expressions.map NormalizedExpr.toParsed).filter
    parsedExprIsL1ToPEProducer, WelcomeRowHasNoLm1Destination expression

theorem welcomePEMiddleStageLm1Free_msl (expressions : List NormalizedExpr)
    (free : WelcomePEMiddleStageLm1Free expressions) :
    ∀ expression ∈ (expressions.map NormalizedExpr.toParsed).filter
      parsedExprIsMslMsrProducer, WelcomeRowHasNoLm1Destination expression :=
  free.1

theorem welcomePEMiddleStageLm1Free_relu (expressions : List NormalizedExpr)
    (free : WelcomePEMiddleStageLm1Free expressions) :
    ∀ expression ∈ (expressions.map NormalizedExpr.toParsed).filter
      parsedExprIsFloatReluProducer, WelcomeRowHasNoLm1Destination expression :=
  free.2.1

theorem welcomePEMiddleStageLm1Free_block (expressions : List NormalizedExpr)
    (free : WelcomePEMiddleStageLm1Free expressions) :
    ∀ expression ∈ (expressions.map NormalizedExpr.toParsed).filter
      parsedExprIsBlockFloatProducer, WelcomeRowHasNoLm1Destination expression :=
  free.2.2

theorem welcomePEMiddleStageLm1Free_matrixMAU (expressions : List NormalizedExpr)
    (free : WelcomePEMatrixMAUStageLm1Free expressions) :
    ∀ expression ∈ (expressions.map NormalizedExpr.toParsed).filter
      parsedExprIsMatrixMAUProducer, WelcomeRowHasNoLm1Destination expression :=
  free

theorem welcomePEMiddleStageLm1Free_l1 (expressions : List NormalizedExpr)
    (free : WelcomePEL1StageLm1Free expressions) :
    ∀ expression ∈ (expressions.map NormalizedExpr.toParsed).filter
      parsedExprIsL1ToPEProducer, WelcomeRowHasNoLm1Destination expression :=
  free

/-- **The middle-stage bundle from row-local freeness.**  If every row of the
line other than `e` has no `.lm1` destination operand and `e` is not a producer of
any of the four middle stages, the four stage filters are `.lm1`-free.  This is
the form produced by "`e` is the unique `.lm1` writer": for a row `x` of a stage
filter either `x = e` (impossible, `e` is not a producer of that stage) or `x` is
a non-writer. -/
theorem welcomePEMiddleStageLm1Free_of_rows
    (expressions : List NormalizedExpr) (e : ParsedExpr)
    (rows : ∀ expression ∈ expressions.map NormalizedExpr.toParsed, expression ≠ e →
      WelcomeRowHasNoLm1Destination expression)
    (notMsl : parsedExprIsMslMsrProducer e = false)
    (notRelu : parsedExprIsFloatReluProducer e = false)
    (notBlock : parsedExprIsBlockFloatProducer e = false) :
    WelcomePEMiddleStageLm1Free expressions := by
  refine ⟨?_, ?_, ?_⟩
  · intro expression member
    have lineMem : expression ∈ expressions.map NormalizedExpr.toParsed :=
      List.mem_of_mem_filter member
    by_cases same : expression = e
    · subst same
      have keeps := (List.mem_filter.mp member).2
      rw [notMsl] at keeps
      exact absurd keeps (by simp)
    · exact rows expression lineMem same
  · intro expression member
    have lineMem : expression ∈ expressions.map NormalizedExpr.toParsed :=
      List.mem_of_mem_filter member
    by_cases same : expression = e
    · subst same
      have keeps := (List.mem_filter.mp member).2
      rw [notRelu] at keeps
      exact absurd keeps (by simp)
    · exact rows expression lineMem same
  · intro expression member
    have lineMem : expression ∈ expressions.map NormalizedExpr.toParsed :=
      List.mem_of_mem_filter member
    by_cases same : expression = e
    · subst same
      have keeps := (List.mem_filter.mp member).2
      rw [notBlock] at keeps
      exact absurd keeps (by simp)
    · exact rows expression lineMem same

/-- **The matrix-MAU/write stage freeness from row-local freeness.** -/
theorem welcomePEMatrixMAUStageLm1Free_of_rows
    (expressions : List NormalizedExpr) (e : ParsedExpr)
    (rows : ∀ expression ∈ expressions.map NormalizedExpr.toParsed, expression ≠ e →
      WelcomeRowHasNoLm1Destination expression)
    (notMatrixMAU : parsedExprIsMatrixMAUProducer e = false) :
    WelcomePEMatrixMAUStageLm1Free expressions := by
  intro expression member
  have lineMem : expression ∈ expressions.map NormalizedExpr.toParsed :=
    List.mem_of_mem_filter member
  by_cases same : expression = e
  · subst same
    have keeps := (List.mem_filter.mp member).2
    rw [notMatrixMAU] at keeps
    exact absurd keeps (by simp)
  · exact rows expression lineMem same

/-- **The L1BM-to-PE stage freeness from row-local freeness.** -/
theorem welcomePEL1StageLm1Free_of_rows
    (expressions : List NormalizedExpr) (e : ParsedExpr)
    (rows : ∀ expression ∈ expressions.map NormalizedExpr.toParsed, expression ≠ e →
      WelcomeRowHasNoLm1Destination expression)
    (notL1 : parsedExprIsL1ToPEProducer e = false) :
    WelcomePEL1StageLm1Free expressions := by
  intro expression member
  have lineMem : expression ∈ expressions.map NormalizedExpr.toParsed :=
    List.mem_of_mem_filter member
  by_cases same : expression = e
  · subst same
    have keeps := (List.mem_filter.mp member).2
    rw [notL1] at keeps
    exact absurd keeps (by simp)
  · exact rows expression lineMem same

/-! ## 3. The two filter bridges

The sealed step runs the integer stage on the line with five producer families
removed (`peExpressions` below).  Its integer and float-MAU row filters are the
same as the line's, because no row of either family is one of the removed
families. -/

/-- The outer filter of the integer stage (the list the per-PE walk sees). -/
abbrev welcomePEWalkFilter (expressions : List NormalizedExpr) : List ParsedExpr :=
  (expressions.map NormalizedExpr.toParsed).filter fun expression =>
    !parsedExprIsL2BMProducer expression && !parsedExprIsMslMsrProducer expression &&
      !parsedExprIsMatrixMAUProducer expression && !parsedExprIsBlockFloatProducer expression &&
      !parsedExprIsFloatReluProducer expression

/-- **A filter of a filter that keeps everything the inner test keeps.** -/
theorem filter_filter_eq_of_implies {α : Type} (outer inner : α → Bool) (items : List α)
    (implies : ∀ item, inner item = true → outer item = true) :
    (items.filter outer).filter inner = items.filter inner := by
  rw [List.filter_filter]
  exact List.filter_congr (fun item _ => by
    by_cases keeps : inner item = true
    · simp [keeps, implies item keeps]
    · simp [keeps])

/-- An integer-stage row survives the outer filter of the walk. -/
theorem welcomeIntegerStageInput_outer (expression : ParsedExpr)
    (stage : parsedExprIsIntegerMatrixReadStageInput expression = true) :
    (!parsedExprIsL2BMProducer expression && !parsedExprIsMslMsrProducer expression &&
      !parsedExprIsMatrixMAUProducer expression && !parsedExprIsBlockFloatProducer expression &&
      !parsedExprIsFloatReluProducer expression) = true := by
  obtain ⟨-, l2bm, -, -, -, -, -, matrixMAU, -, msl, block, relu⟩ :=
    (parsedExprIsIntegerMatrixReadStageInput_spec expression).mp stage
  simp [l2bm, matrixMAU, msl, block, relu]

/-- A float-MAU row survives the outer filter of the walk. -/
theorem welcomeFloatMAU_outer (expression : ParsedExpr)
    (float : parsedExprIsSupportedFloatMAUProducer expression = true) :
    (!parsedExprIsL2BMProducer expression && !parsedExprIsMslMsrProducer expression &&
      !parsedExprIsMatrixMAUProducer expression && !parsedExprIsBlockFloatProducer expression &&
      !parsedExprIsFloatReluProducer expression) = true := by
  obtain ⟨l2bm, msl, matrixMAU, block, relu, -, -, -⟩ :=
    floatMAU_parsedExpr_predicates expression float
  simp [l2bm, msl, matrixMAU, block, relu]

/-- **The walk's integer-stage row filter is the line's.** -/
theorem welcomePEWalkFilter_integer (expressions : List NormalizedExpr) :
    (welcomePEWalkFilter expressions).filter parsedExprIsIntegerMatrixReadStageInput =
      (expressions.map NormalizedExpr.toParsed).filter
        parsedExprIsIntegerMatrixReadStageInput :=
  filter_filter_eq_of_implies _ _ _ (fun expression stage =>
    welcomeIntegerStageInput_outer expression stage)

/-- **The walk's float-MAU row filter is the line's.** -/
theorem welcomePEWalkFilter_float (expressions : List NormalizedExpr) :
    (welcomePEWalkFilter expressions).filter parsedExprIsSupportedFloatMAUProducer =
      (expressions.map NormalizedExpr.toParsed).filter
        parsedExprIsSupportedFloatMAUProducer :=
  filter_filter_eq_of_implies _ _ _ (fun expression float =>
    welcomeFloatMAU_outer expression float)

/-! ## 4. The chain replay

The six stages run in sequence, each committing its own list on the PE 0
register file.  Composition of `commitParsedMaskedWrites` turns the six commits
into one commit of the concatenation, in the order the stage lists appear in
`welcomePE_line_stage_commit_unconditional`. -/

/-- **Six stage commits give the line commit of the concatenation.** -/
theorem executeIntegerProducerInstructionLine_pe_commit_split
    (nextPEs nextMsl nextRelu nextBlockFloat afterMatrix nextShared nextBroadcast next : State)
    (peEq : next.peRegisters welcomePE = nextBroadcast.peRegisters welcomePE)
    (intWrites mslWrites reluWrites blockWrites matrixWrites l1Writes :
      List PreparedParsedMaskedWrite)
    (intCommit : nextPEs.peRegisters welcomePE =
      commitParsedMaskedWrites ((welcomeInitialState welcomeZeroWords).peRegisters welcomePE)
        intWrites)
    (mslCommit : nextMsl.peRegisters welcomePE =
      commitParsedMaskedWrites (nextPEs.peRegisters welcomePE) mslWrites)
    (reluCommit : nextRelu.peRegisters welcomePE =
      commitParsedMaskedWrites (nextMsl.peRegisters welcomePE) reluWrites)
    (blockCommit : nextBlockFloat.peRegisters welcomePE =
      commitParsedMaskedWrites (nextRelu.peRegisters welcomePE) blockWrites)
    (matrixCommit : afterMatrix.peRegisters welcomePE =
      commitParsedMaskedWrites (nextBlockFloat.peRegisters welcomePE) matrixWrites)
    (sharedFrame : nextShared.peRegisters welcomePE = afterMatrix.peRegisters welcomePE)
    (l1Commit : nextBroadcast.peRegisters welcomePE =
      commitParsedMaskedWrites (nextShared.peRegisters welcomePE) l1Writes) :
    next.peRegisters welcomePE =
      commitParsedMaskedWrites ((welcomeInitialState welcomeZeroWords).peRegisters welcomePE)
        (intWrites ++ mslWrites ++ reluWrites ++ blockWrites ++ matrixWrites ++ l1Writes) := by
  rw [peEq, l1Commit, sharedFrame, matrixCommit, blockCommit, reluCommit, mslCommit,
    intCommit]
  simp only [← commitParsedMaskedWrites_append, List.append_assoc]


/-! ## 5. The integer stage's list and the matrix-MAU stage shape -/

/-- **The integer core commits its prepared list and then the float-MAU list.**
This is the float-carrying companion of
`executeIntegerProducerLineAtPECore_prepared`: the prepared list is the one
`welcomeIntegerPrep` returns, so the `.lm1` provenance of the integer stage
applies to it, and the float-MAU writes are appended. -/
theorem executeIntegerProducerLineAtPECore_prepared_float
    (expressions : List ParsedExpr) (state next : State) (pe : PEId)
    (executed : executeIntegerProducerLineAtPECore expressions state pe = .ok next) :
    ∃ intWrites floatWrites slots bars,
      welcomeIntegerPrep state pe expressions = .ok (intWrites, slots, bars) ∧
      next.peRegisters pe =
        commitParsedMaskedWrites (state.peRegisters pe) (intWrites ++ floatWrites) := by
  rw [executeIntegerProducerLineAtPECore.eq_1] at executed
  dsimp only at executed
  split at executed
  · simp at executed
  · simp at executed
  · rename_i registers integerSlots barUpdates fourCycle
    split at executed
    · simp at executed
    · simp at executed
    · rename_i registersWithFloat floatBar0 floatBar1 floatOutputs hasMAUProducer floatMAU
      unfold parsedIntegerMatrixReadLineFourCycleStep at fourCycle
      split at fourCycle
      · simp at fourCycle
      · simp at fourCycle
      · rename_i intWrites preparedSlots preparedBars prepared
        simp only [StepResult.ok.injEq, Prod.mk.injEq] at fourCycle
        obtain ⟨commitRegsEq, -, -⟩ := fourCycle
        obtain ⟨floatWrites, floatCommitEq⟩ :=
          executeParsedFloatMAUsAtPE_commit _ registers _ _ expressions _ _
            registersWithFloat floatBar0 floatBar1 floatOutputs hasMAUProducer floatMAU
        refine ⟨intWrites, floatWrites, preparedSlots, preparedBars, prepared, ?_⟩
        simp only [updateSupportedPELineForwarding] at executed
        split at executed
        · simp at executed
        · simp at executed
        · simp only [StepResult.ok.injEq] at executed
          subst executed
          show (if pe = pe then registersWithFloat else state.peRegisters pe) =
            commitParsedMaskedWrites (state.peRegisters pe) (intWrites ++ floatWrites)
          rw [ite_eq_left rfl, floatCommitEq, ← commitRegsEq,
            ← commitParsedMaskedWrites_append]

/-- **The per-PE walk at PE 0 at the all-zero state.**  The walk's PE 0 file is
the commit of `welcomeIntegerPrep`'s list followed by the row's float-MAU list.
(The other 4095 PEs never revisit PE 0.) -/
theorem executeIntegerProducerLineAtPEs_zero_prepared_float
    (expressions : List ParsedExpr) (next : State)
    (executed : executeIntegerProducerLineAtPEs expressions (List.finRange 4096)
      (welcomeInitialState welcomeZeroWords) = .ok next) :
    ∃ intWrites floatWrites slots bars,
      welcomeIntegerPrep (welcomeInitialState welcomeZeroWords) welcomePE expressions =
        .ok (intWrites, slots, bars) ∧
      next.peRegisters welcomePE =
        commitParsedMaskedWrites welcomeZeroFiles (intWrites ++ floatWrites) := by
  have hrange : List.finRange 4096 =
      welcomePE :: (List.finRange 4095).map Fin.succ := by
    have h := @List.finRange_succ 4095
    simpa [welcomePE] using h
  rw [hrange] at executed
  simp only [executeIntegerProducerLineAtPEs] at executed
  split at executed
  · simp at executed
  · simp at executed
  · rename_i nextPEs headExecuted
    have coreExecuted : executeIntegerProducerLineAtPECore expressions
        (welcomeInitialState welcomeZeroWords) welcomePE = .ok nextPEs := by
      unfold executeIntegerProducerLineAtPE at headExecuted
      split at headExecuted
      · simp at headExecuted
      · exact headExecuted
    obtain ⟨intWrites, floatWrites, slots, bars, intPrep, intCommit⟩ :=
      executeIntegerProducerLineAtPECore_prepared_float expressions
        (welcomeInitialState welcomeZeroWords) nextPEs welcomePE coreExecuted
    have notMem : welcomePE ∉ (List.finRange 4095).map Fin.succ := by
      intro hmem
      simp only [List.mem_map] at hmem
      obtain ⟨i, _, hi⟩ := hmem
      have := congrArg Fin.val hi
      simp [welcomePE] at this
    have tailFrame := executeIntegerProducerLineAtPEs_peRegisters_not_mem expressions
      ((List.finRange 4095).map Fin.succ) nextPEs next executed
      (fun pe p s n he different =>
        executeIntegerProducerLineAtPE_peRegisters_other expressions s n pe p different he)
      welcomePE notMem
    refine ⟨intWrites, floatWrites, slots, bars, intPrep, ?_⟩
    rw [tailFrame]
    exact intCommit


/-- **The matrix-MAU/write stage at an arbitrary current state.**  The row shape
instances of `WelcomeMatrixMAUShape.lean`/`WelcomeMatrixMAUUnconditional.lean` are
stated at the all-zero current state; the producer-level `_shape` and
`_widthCount` lemmas are uniform in the current state, so the stage shape holds
for any incoming PE file.  The only datapath input is
`WelcomePEMatrixMAUZeroBus` (proved in `WelcomeMatrixMAUZero.lean`), and the row's
static `.lm1` width is instantiated. -/
theorem executeParsedMatrixMAUAndWrites_shape_of_filter_singleton
    (currentState next : State) (expressions : List ParsedExpr) (expression : ParsedExpr)
    (noForward hasSingleLineMask : Bool)
    (filterResult : expressions.filter parsedExprIsMatrixMAUProducer = [expression])
    (nodup : (expression.toIssueExpr 0).writeBanks.Nodup)
    (executed : executeParsedMatrixMAUAndWrites (welcomeInitialState welcomeZeroWords)
      currentState expressions noForward hasSingleLineMask = .ok next) :
    ∃ writes, next.peRegisters welcomePE =
      commitParsedMaskedWrites (currentState.peRegisters welcomePE) writes ∧
      Lm1WritesShape writes := by
  rw [executeParsedMatrixMAUAndWrites.eq_1] at executed
  cases producer : executeParsedMatrixMAUProducer (welcomeInitialState welcomeZeroWords)
      currentState expressions noForward hasSingleLineMask with
  | failure =>
      rw [producer] at executed
      simp at executed
  | unknown =>
      rw [producer] at executed
      simp at executed
  | ok afterMAU =>
      rw [producer] at executed
      have frame := executeParsedMatrixWritesAtMABs_preserves_pe_state
        (welcomeInitialState welcomeZeroWords) afterMAU next allMABCoordinates expressions executed
      by_cases isDouble :
          (lm1StaticWidth expression).getD PEMemory.Width.word = PEMemory.Width.double
      · obtain ⟨writes, committed, widths, copies⟩ :=
          executeParsedMatrixMAUProducer_shape currentState afterMAU
            expressions expression noForward hasSingleLineMask PEMemory.Width.double
            filterResult (by rw [← isDouble]; exact lm1StaticWidth_spec expression nodup)
            (lm1DestCount_any expression.destinations) welcomePEMatrixMAUZeroBus producer
        refine ⟨writes, by rw [frame.1]; exact committed, ?_⟩
        exact Or.inl (lm1WriteFacts_doubleCopy writes
          (lm1WriteFacts_of_parts PEMemory.Width.double writes widths copies))
      · obtain ⟨writes, committed, widths, countLe⟩ :=
          executeParsedMatrixMAUProducer_widthCount (welcomeInitialState welcomeZeroWords)
            currentState afterMAU expressions expression noForward hasSingleLineMask
            ((lm1StaticWidth expression).getD PEMemory.Width.word) filterResult
            (lm1StaticWidth_spec expression nodup) (lm1DestCount_any expression.destinations)
            (lm1Destinations_count_le_one expression 0 nodup) producer
        refine ⟨writes, by rw [frame.1]; exact committed, ?_⟩
        exact Or.inr (lm1WidthFacts_narrow writes
          ((lm1StaticWidth expression).getD PEMemory.Width.word) widths isDouble countLe)


/-! ## 6. The five dispatch theorems -/

/-- **The plain-writer dispatch.**  The `.lm1` writer of the line is the plain row
`e` (its own shape is `plainRow_lm1_shape_of_linePrep`); every other row of the
integer stage is `.noforward` / `.wait` and no row of the other stages is a
writer, so by `welcomePEStageLm1ProvenanceForm` those stage lists are `.lm1`-free
and the line's shape is `e`'s. -/
theorem welcomePEWriteShape_of_plainWriter_dispatch
    (expressions : List NormalizedExpr)
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
    (plain : parsedExprIsPlainIntegerALU e = true)
    (floatEmpty : (expressions.map NormalizedExpr.toParsed).filter
        parsedExprIsSupportedFloatMAUProducer = [])
    (middleFree : WelcomePEMiddleStageLm1Free expressions)
    (matrixFreeRows : WelcomePEMatrixMAUStageLm1Free expressions)
    (l1FreeRows : WelcomePEL1StageLm1Free expressions) :
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
  have splitWalk : (welcomePEWalkFilter expressions).filter
      parsedExprIsIntegerMatrixReadStageInput = before ++ e :: after := by
    rw [welcomePEWalkFilter_integer]
    exact split
  have floatEmptyWalk : (welcomePEWalkFilter expressions).filter
      parsedExprIsSupportedFloatMAUProducer = [] := by
    rw [welcomePEWalkFilter_float]
    exact floatEmpty
  obtain ⟨intWrites, intSlots, intBars, intPrep, intCommit⟩ :=
    executeIntegerProducerLineAtPEs_prepared (welcomePEWalkFilter expressions)
      (List.finRange 4096) (welcomeInitialState welcomeZeroWords) nextPEs floatEmptyWalk
      walkExecuted (List.nodup_finRange 4096) welcomePE (List.mem_finRange welcomePE)
  obtain ⟨rowWrites, rowSlots, rowBars, rowPrep, intWritesEq⟩ :=
    welcomeIntegerPrep_single_writer (welcomeInitialState welcomeZeroWords)
      (welcomePEWalkFilter expressions) before after e splitWalk skipBefore skipAfter
      intWrites intSlots intBars intPrep
  have maskEq : ((welcomePEWalkFilter expressions).filter
      parsedExprIsIntegerMatrixReadStageInput).any parsedExprHasSingleLineWriteMask =
      parsedExprHasSingleLineWriteMask e := by
    rw [welcomePEWalkFilter_integer]
    exact flagEq
  rw [maskEq] at rowPrep
  have intShape : Lm1WritesShape intWrites := by
    rw [intWritesEq]
    exact plainRow_lm1_shape_of_linePrep e plain notDouble nodup _
      rowWrites rowSlots rowBars rowPrep
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
  refine ⟨intWrites ++ mslWrites ++ reluWrites ++ blockWrites ++ matrixWrites ++ l1Writes,
    executeIntegerProducerInstructionLine_pe_commit_split nextPEs nextMsl nextRelu
      nextBlockFloat afterMatrix nextShared nextBroadcast next peEq intWrites mslWrites
      reluWrites blockWrites matrixWrites l1Writes intCommit mslCommit reluCommit blockCommit
      matrixCommit sharedFrame l1Commit, ?_⟩
  exact lm1WritesShape_of_six_first intWrites mslWrites reluWrites blockWrites matrixWrites
    l1Writes intShape mslFree reluFree blockFree matrixFree l1Free


/-- **The `.matrixRead`-writer dispatch.**  Same assembly as the plain case, with
the row shape of the `.matrixRead` writer (`matrixReadRow_lm1_shape`), which is
uniform in the line's mask and no-forward flags, so no flag agreement is needed.
The integer stage's companions must again be `.noforward` / `.wait` rows. -/
theorem welcomePEWriteShape_of_matrixReadWriter_dispatch
    (expressions : List NormalizedExpr)
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
        some (PEMemory.Bank.lm1, v) → v = staticW)
    (floatEmpty : (expressions.map NormalizedExpr.toParsed).filter
        parsedExprIsSupportedFloatMAUProducer = [])
    (middleFree : WelcomePEMiddleStageLm1Free expressions)
    (matrixFreeRows : WelcomePEMatrixMAUStageLm1Free expressions)
    (l1FreeRows : WelcomePEL1StageLm1Free expressions) :
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
  have splitWalk : (welcomePEWalkFilter expressions).filter
      parsedExprIsIntegerMatrixReadStageInput = before ++ e :: after := by
    rw [welcomePEWalkFilter_integer]
    exact split
  have floatEmptyWalk : (welcomePEWalkFilter expressions).filter
      parsedExprIsSupportedFloatMAUProducer = [] := by
    rw [welcomePEWalkFilter_float]
    exact floatEmpty
  obtain ⟨intWrites, intSlots, intBars, intPrep, intCommit⟩ :=
    executeIntegerProducerLineAtPEs_prepared (welcomePEWalkFilter expressions)
      (List.finRange 4096) (welcomeInitialState welcomeZeroWords) nextPEs floatEmptyWalk
      walkExecuted (List.nodup_finRange 4096) welcomePE (List.mem_finRange welcomePE)
  obtain ⟨rowWrites, rowSlots, rowBars, rowPrep, intWritesEq⟩ :=
    welcomeIntegerPrep_single_writer (welcomeInitialState welcomeZeroWords)
      (welcomePEWalkFilter expressions) before after e splitWalk skipBefore skipAfter
      intWrites intSlots intBars intPrep
  have intShape : Lm1WritesShape intWrites := by
    rw [intWritesEq]
    exact matrixReadRow_lm1_shape e precision sideY width row op sources welcomeZeroControl
      _ _ false staticW nodup staticWidth rowWrites rowSlots rowBars rowPrep

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
  refine ⟨intWrites ++ mslWrites ++ reluWrites ++ blockWrites ++ matrixWrites ++ l1Writes,
    executeIntegerProducerInstructionLine_pe_commit_split nextPEs nextMsl nextRelu
      nextBlockFloat afterMatrix nextShared nextBroadcast next peEq intWrites mslWrites
      reluWrites blockWrites matrixWrites l1Writes intCommit mslCommit reluCommit blockCommit
      matrixCommit sharedFrame l1Commit, ?_⟩
  exact lm1WritesShape_of_six_first intWrites mslWrites reluWrites blockWrites matrixWrites
    l1Writes intShape mslFree reluFree blockFree matrixFree l1Free


/-- **The `.l1bm`-broadcast-writer dispatch.**  The writer is the L1BM-to-PE
stage's single row (`executeParsedL1ToPEProducers_mem_lm1_shape`); the integer
stage and the other middle stages are non-writers and their lists are `.lm1`-free
(`WelcomePEMiddleStageLm1Free`, `WelcomePEMatrixMAUStageLm1Free`,
`welcomeIntegerPrep_lm1_free`), so the shape of the six-list concatenation is the
broadcast's own row shape. -/
theorem welcomePEWriteShape_of_l1bmWriter_dispatch
    (expressions : List NormalizedExpr)
    (e : ParsedExpr) (access : ParsedL1ToPEAccess) (memoryAccess : Access)
    (negated extended rounded : Bool) (mask : Option ParsedMask) (w : PEMemory.Width)
    (lowered : lowerParsedL1ToPE? e = some access)
    (destinations : access.destinations =
      [ParsedOperand.mem memoryAccess negated extended rounded mask])
    (static : ParsedOperand.directDestinationBankWidth?
      (ParsedOperand.mem memoryAccess negated extended rounded mask) =
      some (PEMemory.Bank.lm1, w))
    (l1Filter : (expressions.map NormalizedExpr.toParsed).filter
      parsedExprIsL1ToPEProducer = [e])
    (intFree : ∀ expression ∈ (expressions.map NormalizedExpr.toParsed).filter
        parsedExprIsIntegerMatrixReadStageInput, WelcomeRowHasNoLm1Destination expression)
    (floatEmpty : (expressions.map NormalizedExpr.toParsed).filter
        parsedExprIsSupportedFloatMAUProducer = [])
    (middleFree : WelcomePEMiddleStageLm1Free expressions)
    (matrixFreeRows : WelcomePEMatrixMAUStageLm1Free expressions) :
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
  have floatEmptyWalk : (welcomePEWalkFilter expressions).filter
      parsedExprIsSupportedFloatMAUProducer = [] := by
    rw [welcomePEWalkFilter_float]
    exact floatEmpty
  obtain ⟨intWrites, intSlots, intBars, intPrep, intCommit⟩ :=
    executeIntegerProducerLineAtPEs_prepared (welcomePEWalkFilter expressions)
      (List.finRange 4096) (welcomeInitialState welcomeZeroWords) nextPEs floatEmptyWalk
      walkExecuted (List.nodup_finRange 4096) welcomePE (List.mem_finRange welcomePE)
  have intWritesFree : Lm1FreePreparedWrites intWrites :=
    welcomeIntegerPrep_lm1_free (welcomeInitialState welcomeZeroWords) welcomePE
      (welcomePEWalkFilter expressions) intWrites intSlots intBars intPrep (by
        intro expression member
        exact intFree expression (by rw [welcomePEWalkFilter_integer] at member; exact member))
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
  obtain ⟨l1Writes, l1Commit, l1Shape⟩ :=
    executeParsedL1ToPEProducers_mem_lm1_shape welcomeZeroWords nextShared nextBroadcast
      (expressions.map NormalizedExpr.toParsed) e access
      (expressions.any (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed))
      (expressions.any (parsedExprHasSingleLineWriteMask ∘ NormalizedExpr.toParsed))
      (parsedL1ToPEPrecedesOMRWriter (expressions.map NormalizedExpr.toParsed))
      memoryAccess negated extended rounded mask w lowered destinations static l1Filter
      l1Executed
  have sharedFrame : nextShared.peRegisters welcomePE = afterMatrix.peRegisters welcomePE :=
    congrFun (executeParsedSharedBlockProducers_peRegisters (welcomeInitialState welcomeZeroWords)
      afterMatrix nextShared (expressions.map NormalizedExpr.toParsed)
      (!(expressions.any (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed)))
      sharedExecuted) welcomePE
  have peEq : next.peRegisters welcomePE = nextBroadcast.peRegisters welcomePE := by
    rw [nextEq]
  refine ⟨intWrites ++ mslWrites ++ reluWrites ++ blockWrites ++ matrixWrites ++ l1Writes,
    executeIntegerProducerInstructionLine_pe_commit_split nextPEs nextMsl nextRelu
      nextBlockFloat afterMatrix nextShared nextBroadcast next peEq intWrites mslWrites
      reluWrites blockWrites matrixWrites l1Writes intCommit mslCommit reluCommit blockCommit
      matrixCommit sharedFrame l1Commit, ?_⟩
  exact lm1WritesShape_of_six_sixth intWrites mslWrites reluWrites blockWrites matrixWrites
    l1Writes intWritesFree mslFree reluFree blockFree matrixFree l1Shape

/-- **The matrix-MAU-writer dispatch.**  The writer is the matrix-MAU/write
stage's single row.  The stage is executed at the running (non-zero) PE file, so
the row shape is the arbitrary-current-state form
`executeParsedMatrixMAUAndWrites_shape_of_filter_singleton`.  The integer stage and
the other four middle stages are non-writers, and the shared-block stage is a
frame. -/
theorem welcomePEWriteShape_of_matrixMAUWriter_dispatch
    (expressions : List NormalizedExpr)
    (e : ParsedExpr)
    (mmau : parsedExprIsMatrixMAUProducer e = true)
    (nodup : (e.toIssueExpr 0).writeBanks.Nodup)
    (mauFilter : (expressions.map NormalizedExpr.toParsed).filter
      parsedExprIsMatrixMAUProducer = [e])
    (intFree : ∀ expression ∈ (expressions.map NormalizedExpr.toParsed).filter
        parsedExprIsIntegerMatrixReadStageInput, WelcomeRowHasNoLm1Destination expression)
    (floatEmpty : (expressions.map NormalizedExpr.toParsed).filter
        parsedExprIsSupportedFloatMAUProducer = [])
    (middleFree : WelcomePEMiddleStageLm1Free expressions)
    (l1FreeRows : WelcomePEL1StageLm1Free expressions) :
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
  have floatEmptyWalk : (welcomePEWalkFilter expressions).filter
      parsedExprIsSupportedFloatMAUProducer = [] := by
    rw [welcomePEWalkFilter_float]
    exact floatEmpty
  obtain ⟨intWrites, intSlots, intBars, intPrep, intCommit⟩ :=
    executeIntegerProducerLineAtPEs_prepared (welcomePEWalkFilter expressions)
      (List.finRange 4096) (welcomeInitialState welcomeZeroWords) nextPEs floatEmptyWalk
      walkExecuted (List.nodup_finRange 4096) welcomePE (List.mem_finRange welcomePE)
  have intWritesFree : Lm1FreePreparedWrites intWrites :=
    welcomeIntegerPrep_lm1_free (welcomeInitialState welcomeZeroWords) welcomePE
      (welcomePEWalkFilter expressions) intWrites intSlots intBars intPrep (by
        intro expression member
        exact intFree expression (by rw [welcomePEWalkFilter_integer] at member; exact member))
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
  obtain ⟨matrixWrites, matrixCommit, matrixShape⟩ :=
    executeParsedMatrixMAUAndWrites_shape_of_filter_singleton nextBlockFloat afterMatrix
      (expressions.map NormalizedExpr.toParsed) e
      (expressions.any (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed))
      (expressions.any (parsedExprHasSingleLineWriteMask ∘ NormalizedExpr.toParsed))
      mauFilter nodup matrixExecuted
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
  refine ⟨intWrites ++ mslWrites ++ reluWrites ++ blockWrites ++ matrixWrites ++ l1Writes,
    executeIntegerProducerInstructionLine_pe_commit_split nextPEs nextMsl nextRelu
      nextBlockFloat afterMatrix nextShared nextBroadcast next peEq intWrites mslWrites
      reluWrites blockWrites matrixWrites l1Writes intCommit mslCommit reluCommit blockCommit
      matrixCommit sharedFrame l1Commit, ?_⟩
  exact lm1WritesShape_of_six_fifth intWrites mslWrites reluWrites blockWrites matrixWrites
    l1Writes intWritesFree mslFree reluFree blockFree matrixShape l1Free

/-- **The float-MAU-writer dispatch.**  Float-MAU rows are executed *inside* the
integer stage, and the integer stage commits the prepared (integer) list followed
by the float list.  When every integer-stage row is `.noforward` the prepared list
is empty (`welcomeIntegerPrep_noforward`), so the integer stage's whole list is the
single float row's list and `executeIntegerProducerLineAtPEs_floatWriter` gives its
shape.  The four middle stages and the L1BM-to-PE stage are non-writers. -/
theorem welcomePEWriteShape_of_floatMAUWriter_dispatch
    (expressions : List NormalizedExpr)
    (e : ParsedExpr)
    (float : parsedExprIsSupportedFloatMAUProducer e = true)
    (nodup : (e.toIssueExpr 0).writeBanks.Nodup)
    (floatFilter : (expressions.map NormalizedExpr.toParsed).filter
      parsedExprIsSupportedFloatMAUProducer = [e])
    (intAll : ∀ expression ∈ (expressions.map NormalizedExpr.toParsed).filter
      parsedExprIsIntegerMatrixReadStageInput, expression.op = .noforward)
    (middleFree : WelcomePEMiddleStageLm1Free expressions)
    (matrixFreeRows : WelcomePEMatrixMAUStageLm1Free expressions)
    (l1FreeRows : WelcomePEL1StageLm1Free expressions) :
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
  have floatFilterWalk : (welcomePEWalkFilter expressions).filter
      parsedExprIsSupportedFloatMAUProducer = [e] := by
    rw [welcomePEWalkFilter_float]
    exact floatFilter
  have intAllWalk : ∀ expression ∈ (welcomePEWalkFilter expressions).filter
      parsedExprIsIntegerMatrixReadStageInput, expression.op = .noforward := by
    intro expression member
    exact intAll expression (by rw [welcomePEWalkFilter_integer] at member; exact member)
  obtain ⟨intWrites, intCommit, intShape⟩ :=
    executeIntegerProducerLineAtPEs_floatWriter (welcomePEWalkFilter expressions) e nextPEs
      float nodup floatFilterWalk intAllWalk walkExecuted
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
  refine ⟨intWrites ++ mslWrites ++ reluWrites ++ blockWrites ++ matrixWrites ++ l1Writes,
    executeIntegerProducerInstructionLine_pe_commit_split nextPEs nextMsl nextRelu
      nextBlockFloat afterMatrix nextShared nextBroadcast next peEq intWrites mslWrites
      reluWrites blockWrites matrixWrites l1Writes intCommit mslCommit reluCommit blockCommit
      matrixCommit sharedFrame l1Commit, ?_⟩
  exact lm1WritesShape_of_six_first intWrites mslWrites reluWrites blockWrites matrixWrites
    l1Writes intShape mslFree reluFree blockFree matrixFree l1Free


/-! ## 7. Unique-writer corollaries

The five theorems above take the `.lm1`-freeness of each non-writer stage's row
filter as a hypothesis.  The corollaries below replace those hypotheses by the
row-local statement that **every row of the line other than the writer has no
`.lm1` destination operand** — i.e. that `e` is the line's unique `.lm1` row — plus
the writer's own "not a producer of the other stages" facts, which follow from the
writer's kind. -/

/-- **The syntactic facts of a `.matrixRead` row.**  Such a row is none of the
four middle-stage producers and not an L1BM-to-PE producer. -/
theorem matrixRead_parsedExpr_predicates (expression : ParsedExpr) (precision : ParsedPrecision)
    (op : expression.op = .matrixRead precision) :
    parsedExprIsMslMsrProducer expression = false ∧
    parsedExprIsFloatReluProducer expression = false ∧
    parsedExprIsBlockFloatProducer expression = false ∧
    parsedExprIsMatrixMAUProducer expression = false ∧
    parsedExprIsL1ToPEProducer expression = false := by
  obtain ⟨operation, sources, destinations, flush, text⟩ := expression
  subst op
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [parsedExprIsMslMsrProducer, parsedExprIsFloatReluProducer,
      parsedExprIsBlockFloatProducer, parsedExprIsMatrixMAUProducer,
      parsedExprIsL1ToPEProducer]

/-- **The unique-writer dispatch for a plain writer.** -/
theorem welcomePEWriteShape_of_plainWriter_unique
    (expressions : List NormalizedExpr)
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
    (plain : parsedExprIsPlainIntegerALU e = true)
    (floatEmpty : (expressions.map NormalizedExpr.toParsed).filter
        parsedExprIsSupportedFloatMAUProducer = [])
    (rows : ∀ expression ∈ expressions.map NormalizedExpr.toParsed, expression ≠ e →
      WelcomeRowHasNoLm1Destination expression) :
    WelcomePEWriteShape expressions := by
  obtain ⟨-, -, mslFalse, reluFalse, blockFalse, -, -, matrixMAUFalse, -, l1False, -, -, -⟩ :=
    parsedExprIsPlainIntegerALU_facts e plain
  exact welcomePEWriteShape_of_plainWriter_dispatch expressions before after e split
    skipBefore skipAfter flagEq notDouble nodup plain floatEmpty
    (welcomePEMiddleStageLm1Free_of_rows expressions e rows mslFalse reluFalse blockFalse)
    (welcomePEMatrixMAUStageLm1Free_of_rows expressions e rows matrixMAUFalse)
    (welcomePEL1StageLm1Free_of_rows expressions e rows l1False)

/-- **The unique-writer dispatch for a `.matrixRead` writer.** -/
theorem welcomePEWriteShape_of_matrixReadWriter_unique
    (expressions : List NormalizedExpr)
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
        some (PEMemory.Bank.lm1, v) → v = staticW)
    (floatEmpty : (expressions.map NormalizedExpr.toParsed).filter
        parsedExprIsSupportedFloatMAUProducer = [])
    (rows : ∀ expression ∈ expressions.map NormalizedExpr.toParsed, expression ≠ e →
      WelcomeRowHasNoLm1Destination expression) :
    WelcomePEWriteShape expressions := by
  obtain ⟨mslFalse, reluFalse, blockFalse, matrixMAUFalse, l1False⟩ :=
    matrixRead_parsedExpr_predicates e precision op
  exact welcomePEWriteShape_of_matrixReadWriter_dispatch expressions before after e
    split skipBefore skipAfter precision sideY width row op sources staticW nodup staticWidth
    floatEmpty
    (welcomePEMiddleStageLm1Free_of_rows expressions e rows mslFalse reluFalse blockFalse)
    (welcomePEMatrixMAUStageLm1Free_of_rows expressions e rows matrixMAUFalse)
    (welcomePEL1StageLm1Free_of_rows expressions e rows l1False)

/-- **The unique-writer dispatch for a float-MAU writer.** -/
theorem welcomePEWriteShape_of_floatMAUWriter_unique
    (expressions : List NormalizedExpr)
    (e : ParsedExpr)
    (float : parsedExprIsSupportedFloatMAUProducer e = true)
    (nodup : (e.toIssueExpr 0).writeBanks.Nodup)
    (floatFilter : (expressions.map NormalizedExpr.toParsed).filter
      parsedExprIsSupportedFloatMAUProducer = [e])
    (intAll : ∀ expression ∈ (expressions.map NormalizedExpr.toParsed).filter
      parsedExprIsIntegerMatrixReadStageInput, expression.op = .noforward)
    (rows : ∀ expression ∈ expressions.map NormalizedExpr.toParsed, expression ≠ e →
      WelcomeRowHasNoLm1Destination expression) :
    WelcomePEWriteShape expressions := by
  obtain ⟨-, mslFalse, matrixMAUFalse, blockFalse, reluFalse, -, l1False, -⟩ :=
    floatMAU_parsedExpr_predicates e float
  exact welcomePEWriteShape_of_floatMAUWriter_dispatch expressions e float nodup
    floatFilter intAll
    (welcomePEMiddleStageLm1Free_of_rows expressions e rows mslFalse reluFalse blockFalse)
    (welcomePEMatrixMAUStageLm1Free_of_rows expressions e rows matrixMAUFalse)
    (welcomePEL1StageLm1Free_of_rows expressions e rows l1False)

/-- **The unique-writer dispatch for a matrix-MAU writer.** -/
theorem welcomePEWriteShape_of_matrixMAUWriter_unique
    (expressions : List NormalizedExpr)
    (e : ParsedExpr)
    (mmau : parsedExprIsMatrixMAUProducer e = true)
    (nodup : (e.toIssueExpr 0).writeBanks.Nodup)
    (mauFilter : (expressions.map NormalizedExpr.toParsed).filter
      parsedExprIsMatrixMAUProducer = [e])
    (floatEmpty : (expressions.map NormalizedExpr.toParsed).filter
        parsedExprIsSupportedFloatMAUProducer = [])
    (rows : ∀ expression ∈ expressions.map NormalizedExpr.toParsed, expression ≠ e →
      WelcomeRowHasNoLm1Destination expression) :
    WelcomePEWriteShape expressions := by
  obtain ⟨-, mslFalse, blockFalse, reluFalse, -, l1False, -, intStageFalse⟩ :=
    matrixMAU_parsedExpr_predicates e mmau
  exact welcomePEWriteShape_of_matrixMAUWriter_dispatch expressions e mmau nodup
    mauFilter (fun expression member => rows expression (List.mem_of_mem_filter member) (by
      intro same
      subst same
      have keeps := (List.mem_filter.mp member).2
      rw [intStageFalse] at keeps
      exact absurd keeps (by simp)))
    floatEmpty
    (welcomePEMiddleStageLm1Free_of_rows expressions e rows mslFalse reluFalse blockFalse)
    (welcomePEL1StageLm1Free_of_rows expressions e rows l1False)

/-- **The unique-writer dispatch for a `.l1bm`-broadcast writer.** -/
theorem welcomePEWriteShape_of_l1bmWriter_unique
    (expressions : List NormalizedExpr)
    (e : ParsedExpr) (access : ParsedL1ToPEAccess) (memoryAccess : Access)
    (negated extended rounded : Bool) (mask : Option ParsedMask) (w : PEMemory.Width)
    (lowered : lowerParsedL1ToPE? e = some access)
    (destinations : access.destinations =
      [ParsedOperand.mem memoryAccess negated extended rounded mask])
    (static : ParsedOperand.directDestinationBankWidth?
      (ParsedOperand.mem memoryAccess negated extended rounded mask) =
      some (PEMemory.Bank.lm1, w))
    (l1Filter : (expressions.map NormalizedExpr.toParsed).filter
      parsedExprIsL1ToPEProducer = [e])
    (floatEmpty : (expressions.map NormalizedExpr.toParsed).filter
        parsedExprIsSupportedFloatMAUProducer = [])
    (rows : ∀ expression ∈ expressions.map NormalizedExpr.toParsed, expression ≠ e →
      WelcomeRowHasNoLm1Destination expression) :
    WelcomePEWriteShape expressions := by
  obtain ⟨intStageFalse, -, -, mslFalse, reluFalse, blockFalse, matrixMAUFalse, -, -⟩ :=
    l1bmBroadcast_parsedExpr_predicates e access lowered
  exact welcomePEWriteShape_of_l1bmWriter_dispatch expressions e access memoryAccess
    negated extended rounded mask w lowered destinations static l1Filter
    (fun expression member => rows expression (List.mem_of_mem_filter member) (by
      intro same
      subst same
      have keeps := (List.mem_filter.mp member).2
      rw [intStageFalse] at keeps
      exact absurd keeps (by simp)))
    floatEmpty
    (welcomePEMiddleStageLm1Free_of_rows expressions e rows mslFalse reluFalse blockFalse)
    (welcomePEMatrixMAUStageLm1Free_of_rows expressions e rows matrixMAUFalse)

end ProofsLean.MNCore
