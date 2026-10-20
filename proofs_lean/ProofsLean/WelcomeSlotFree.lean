import ProofsLean.WelcomeFinalShape
import ProofsLean.WelcomeFloatProvenance

/-! # Slot-free row shapes: an arbitrary preparing row may precede the writer

`WelcomeFinalShape.lean` (round 46) reduces the write-shape obligation to seven
per-line dispatch cases.  For the plain and `.matrixRead` writers the reduction
carries a **companion restriction**: the integer-stage filter must split as

```
noforward* ++ [e] ++ noforward*
```

The reason is that `plainRow_lm1_shape` / `matrixReadRow_lm1_shape`
(`WelcomeWriterShape.lean`) are stated with the incoming forwarding slots of the
writer equal to the *initial* slots `welcomeZeroSlots`.  A line that prepares a
write in a row before the writer (e.g. `[matrixRead (no lm1 destination),
alu -> lm1]`) is legal and unrefuted but has a different slot state at the
writer, so it falls outside the reduction.

This module closes that gap.  The structural facts that make it possible are:

* `prepareParsedIntegerMatrixReadLineExpressions` (the integer stage's fold)
  keeps the register `files` and the read slots `oldSlots` **fixed** across the
  whole row list; only the *output* slots `nextSlots` are threaded.  Hence a
  preceding preparing row never changes what the writer row *reads*: a plain
  writer still reads `welcomeZeroFiles` at `welcomeZeroSlots`, and only its
  forwarding-output slots differ.  The `.matrixRead` branch uses `nextSlots` as
  its slot argument, but its data comes from the matrix store, not from the
  slots.
* consequently both row shapes are independent of the incoming slots.  The
  plain one needs the four-cycle unfolding at an arbitrary *initial output*
  slot (`prepareParsedIntegerALUExprCycles_four_start`); the `.matrixRead` one
  is already proved at arbitrary slots in `WelcomeMAUShape.lean`
  (`prepareParsedIntegerMatrixReadLineExpression_matrixRead_shape`).

## What is proved

* `prepareParsedIntegerALUExprCycles_four_start` — the four-cycle unfolding with
  an arbitrary initial output slot;
* `plainRow_lm1_shape_of_startSlots` and
  `plainRow_lm1_shape_of_linePrep_startSlots` — the plain row shape at an
  arbitrary incoming slot state (full shape, i.e. double-copy **or** narrow: the
  `.double` copy fact does not depend on the slots at all in the plain branch);
* `matrixReadRow_lm1_shape_of_startSlots` — the same for a `.matrixRead` row;
* `welcomeIntegerPrep_split` — the integer stage's write list splits along an
  arbitrary row position into `before ++ (writer ++ after)`, with the
  before/after parts `.lm1`-free whenever those rows have no `.lm1` destination;
* `welcomePEWriteShape_of_plainWriter_arbitrary` and
  `welcomePEWriteShape_of_matrixReadWriter_arbitrary` — the two dispatch
  theorems with the companion restriction removed (the companions may be
  arbitrary preparing rows, the only requirement being that they are not
  `.lm1` writers, which the issue checker supplies through
  `welcomeLm1Writer_rows`);
* `WelcomePEPlainWriterDataForSlotFree` / `WelcomePEMatrixReadWriterDataForSlotFree`
  and the line-shape theorems from them, plus the proof that the round-46
  packages imply the slot-free ones (so nothing is strengthened);
* `WelcomePELm1LineDispatchDataSlotFree` and its aggregate
  `welcomePEWriteShape_of_lineDataSlotFree`, in which the plain and `.matrixRead`
  disjuncts use the slot-free packages.

## What is **not** claimed

The remaining five dispatch kinds (float-MAU, matrix-MAU, `.l1bm`, special ALU,
phantom) keep their round-46 packages.  In particular the singleton middle-stage
filters (`floatFilter = [e]`, `mauFilter = [e]`, `l1Filter = [e]`), the mask-flag
agreement / input-independence disjunction of the plain package and the
special-ALU stage fold are unchanged; `welcomePEWriteShape_of_lineDataSlotFree`
still takes `WelcomePESpecialALUWriterShapeObligation`.  Neither
`LowerBound 2` nor `Optimal` is claimed.

## The precise remainder, and why no slot condition is needed

The brief suggested a split into a slot-independent **narrow** half and a
**double** half that would need a condition on the preceding rows' slots.  For
the integer stage that split is not needed: both halves are slot-independent,
because of the fold's structure.

* The fold passes `files` and `oldSlots` unchanged to *every* row and threads
  only the output-slot state `nextSlots`.  A preceding preparing row therefore
  changes exactly one argument of the writer's preparation:
  - for a plain writer, `nextSlots` (the initial output slot of its four-cycle
    unfolding) — the reads still use `oldSlots = welcomeZeroSlots` and
    `files = welcomeZeroFiles`, so the `.double` copy fact is unaffected;
  - for a `.matrixRead` writer, the slot argument, which the matrix-read branch
    uses only to *install* its own forwarding outputs — its data bus is
    `parsedMatrixReadBus store accesses`, which the slots do not enter.
* Hence **no restriction on the preceding rows is required** beyond "they are
  not `.lm1` writers": the `.double` copy fact and the narrow window counting
  are both preserved.  The preceding rows' own writes are non-`.lm1` and drop
  out of the shape by `Lm1FreePreparedWrites`.
* The register files stay at `welcomeZeroFiles` (the executor commits the whole
  integer-stage write list only after the fold), so the row shapes do not need a
  version at arbitrary files for this reduction.  A row shape at arbitrary
  `files` would have to re-analyse the mask-register-dependent lowering branches
  and the copy fact; it is **not** proved here and is **not** needed by
  `welcomeIntegerPrep_split`.
* The two data packages carry the bookkeeping conjuncts `e ∉ before` and
  `e ∉ after` (the writer does not occur in its own outer blocks).  These are not
  companion restrictions: they hold for a split taken at the writer's own
  occurrence, and the round-46 packages imply the slot-free ones
  (`welcomePEPlainWriterDataFor_slotFree_of_companion`,
  `welcomePEMatrixReadWriterDataFor_slotFree_of_companion`), which is the
  conservative direction.

No `sorry`, no `admit`, no `native_decide`, no new axioms, and no existing
module is edited by this file.
-/

namespace ProofsLean.MNCore

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open Issue
open PEMemory

/-! ## 1. The plain row shape at an arbitrary incoming slot state

The integer stage threads only the *output* slot state from row to row; the read
slots `oldSlots` and the register files are fixed for the whole row list.  A
preparing row before the writer therefore changes exactly one input of
`prepareParsedIntegerALUExprCycles`: its initial output slot.  The per-cycle
chunk facts (`prepareParsedIntegerALUExprCycle_lm1_facts`) are already uniform in
that argument, so the four-cycle unfolding is the only thing to generalise. -/

/-- **The four-cycle unfolding at an arbitrary initial output slot.**  Same as
`prepareParsedIntegerALUExprCycles_four`, but the output slots start from
`startSlots` instead of being tied to the read slots `oldSlots`. -/
theorem prepareParsedIntegerALUExprCycles_four_start
    (files : IntegerRegisterFiles) (oldSlots startSlots : ProofsLean.MNCore.Forwarding.Slots)
    (e : ParsedExpr) (control : ParsedMaskExecutionControl) (hsm nf r : Bool)
    (writes : List PreparedParsedMaskedWrite) (slots : ProofsLean.MNCore.Forwarding.Slots)
    (prep : prepareParsedIntegerALUExprCycles files oldSlots startSlots e control hsm nf r =
      .ok (writes, slots)) :
    ∃ (w0 w1 w2 w3 : List PreparedParsedMaskedWrite)
      (s1 s2 s3 : ProofsLean.MNCore.Forwarding.Slots),
      prepareParsedIntegerALUExprCycle files oldSlots startSlots e control hsm nf r
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
  cases h0 : prepareParsedIntegerALUExprCycle files oldSlots startSlots e control hsm nf r
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

/-- **The plain row's `.lm1` shape at an arbitrary incoming slot state.**  Four
cycles of `prepareParsedIntegerALUExprCycle`, each satisfying `Lm1ChunkFacts`,
give the double-copy or narrow shape of the row's whole write list — whatever
the initial output slots are.  The register files and read slots stay at the
all-zero ones, which is what the integer stage supplies for every row. -/
theorem plainRow_lm1_shape_of_startSlots (e : ParsedExpr)
    (notDouble : ∀ payload sparse, e.op = .immediate payload sparse →
      ∀ destination ∈ e.destinations,
        ParsedOperand.directDestinationBankWidth? destination ≠
          some (PEMemory.Bank.lm1, PEMemory.Width.double))
    (nodup : (e.toIssueExpr 0).writeBanks.Nodup)
    (noForward : Bool)
    (startSlots : ProofsLean.MNCore.Forwarding.Slots)
    (writes : List PreparedParsedMaskedWrite)
    (slots : ProofsLean.MNCore.Forwarding.Slots)
    (prep : prepareParsedIntegerALUExprCycles welcomeZeroFiles welcomeZeroSlots startSlots e
      welcomeZeroControl (parsedExprHasSingleLineWriteMask e) noForward false =
      .ok (writes, slots)) :
    Lm1WritesDoubleCopy writes ∨ Lm1WritesNarrow writes := by
  cases e with
  | mk op sources destinations flush text =>
      obtain ⟨w0, w1, w2, w3, s1, s2, s3, h0, h1, h2, h3, writesEq⟩ :=
        prepareParsedIntegerALUExprCycles_four_start welcomeZeroFiles welcomeZeroSlots
          startSlots ⟨op, sources, destinations, flush, text⟩ welcomeZeroControl
          (parsedExprHasSingleLineWriteMask ⟨op, sources, destinations, flush, text⟩)
          noForward false writes slots prep
      have f0 := prepareParsedIntegerALUExprCycle_lm1_facts op sources destinations flush text
        noForward 0 startSlots w0 s1 notDouble nodup h0
      have f1 := prepareParsedIntegerALUExprCycle_lm1_facts op sources destinations flush text
        noForward 1 s1 w1 s2 notDouble nodup h1
      have f2 := prepareParsedIntegerALUExprCycle_lm1_facts op sources destinations flush text
        noForward 2 s2 w2 s3 notDouble nodup h2
      have f3 := prepareParsedIntegerALUExprCycle_lm1_facts op sources destinations flush text
        noForward 3 s3 w3 slots notDouble nodup h3
      rw [writesEq]
      exact lm1WritesShape_of_chunks ⟨op, sources, destinations, flush, text⟩ nodup
        w0 w1 w2 w3 f0 f1 f2 f3

/-- **The plain row's `.lm1` shape in the line-expression form, at an arbitrary
incoming slot state.**  `prepareParsedIntegerMatrixReadLineExpression` for a
plain op is the four-cycle preparation plus a bar-update component. -/
theorem plainRow_lm1_shape_of_linePrep_startSlots (e : ParsedExpr)
    (plain : parsedExprIsPlainIntegerALU e = true)
    (notDouble : ∀ payload sparse, e.op = .immediate payload sparse →
      ∀ destination ∈ e.destinations,
        ParsedOperand.directDestinationBankWidth? destination ≠
          some (PEMemory.Bank.lm1, PEMemory.Width.double))
    (nodup : (e.toIssueExpr 0).writeBanks.Nodup)
    (noForward : Bool)
    (startSlots : ProofsLean.MNCore.Forwarding.Slots)
    (writes : List PreparedParsedMaskedWrite)
    (slots : ProofsLean.MNCore.Forwarding.Slots) (bars : List (Bool × BitVec 12))
    (prep : prepareParsedIntegerMatrixReadLineExpression welcomeZeroFiles welcomeZeroSlots
      startSlots welcomeZeroMatrixStore e welcomeZeroControl
      (parsedExprHasSingleLineWriteMask e) noForward false = .ok (writes, slots, bars)) :
    Lm1WritesDoubleCopy writes ∨ Lm1WritesNarrow writes := by
  cases e with
  | mk op sources destinations flush text =>
      cases op with
      | alu name precision unsigned arg =>
          simp only [prepareParsedIntegerMatrixReadLineExpression] at prep
          cases cycles : prepareParsedIntegerALUExprCycles welcomeZeroFiles welcomeZeroSlots
              startSlots ⟨.alu name precision unsigned arg, sources, destinations, flush,
                text⟩ welcomeZeroControl
              (parsedExprHasSingleLineWriteMask
                ⟨.alu name precision unsigned arg, sources, destinations, flush, text⟩)
              noForward false with
          | failure => rw [cycles] at prep; simp at prep
          | unknown => rw [cycles] at prep; simp at prep
          | ok result =>
              obtain ⟨rowWrites, rowSlots⟩ := result
              rw [cycles] at prep
              simp only [StepResult.ok.injEq, Prod.mk.injEq] at prep
              rw [← prep.1]
              exact plainRow_lm1_shape_of_startSlots _ notDouble nodup noForward startSlots
                rowWrites rowSlots cycles
      | zero =>
          simp only [prepareParsedIntegerMatrixReadLineExpression] at prep
          cases cycles : prepareParsedIntegerALUExprCycles welcomeZeroFiles welcomeZeroSlots
              startSlots ⟨.zero, sources, destinations, flush, text⟩ welcomeZeroControl
              (parsedExprHasSingleLineWriteMask ⟨.zero, sources, destinations, flush, text⟩)
              noForward false with
          | failure => rw [cycles] at prep; simp at prep
          | unknown => rw [cycles] at prep; simp at prep
          | ok result =>
              obtain ⟨rowWrites, rowSlots⟩ := result
              rw [cycles] at prep
              simp only [StepResult.ok.injEq, Prod.mk.injEq] at prep
              rw [← prep.1]
              exact plainRow_lm1_shape_of_startSlots _ notDouble nodup noForward startSlots
                rowWrites rowSlots cycles
      | immediate value unsigned =>
          simp only [prepareParsedIntegerMatrixReadLineExpression] at prep
          cases cycles : prepareParsedIntegerALUExprCycles welcomeZeroFiles welcomeZeroSlots
              startSlots ⟨.immediate value unsigned, sources, destinations, flush, text⟩
              welcomeZeroControl
              (parsedExprHasSingleLineWriteMask
                ⟨.immediate value unsigned, sources, destinations, flush, text⟩)
              noForward false with
          | failure => rw [cycles] at prep; simp at prep
          | unknown => rw [cycles] at prep; simp at prep
          | ok result =>
              obtain ⟨rowWrites, rowSlots⟩ := result
              rw [cycles] at prep
              simp only [StepResult.ok.injEq, Prod.mk.injEq] at prep
              rw [← prep.1]
              exact plainRow_lm1_shape_of_startSlots _ notDouble nodup noForward startSlots
                rowWrites rowSlots cycles
      | noforward =>
          simp [parsedExprIsPlainIntegerALU, parsedExprIsIntegerProducer,
            parsedExprIsUnsupportedRustAlu, parsedExprIsMslMsrProducer,
            parsedExprIsFloatReluProducer, parsedExprIsBlockFloatProducer] at plain
      | «wait» tag =>
          simp [parsedExprIsPlainIntegerALU, parsedExprIsIntegerProducer,
            parsedExprIsUnsupportedRustAlu, parsedExprIsMslMsrProducer,
            parsedExprIsFloatReluProducer, parsedExprIsBlockFloatProducer] at plain
      | mau precision matrix kind half round =>
          simp [parsedExprIsPlainIntegerALU, parsedExprIsIntegerProducer,
            parsedExprIsUnsupportedRustAlu, parsedExprIsMslMsrProducer,
            parsedExprIsFloatReluProducer, parsedExprIsBlockFloatProducer] at plain
      | matrixWrite precision =>
          simp [parsedExprIsPlainIntegerALU, parsedExprIsIntegerProducer,
            parsedExprIsUnsupportedRustAlu, parsedExprIsMslMsrProducer,
            parsedExprIsFloatReluProducer, parsedExprIsBlockFloatProducer] at plain
      | matrixRead precision =>
          simp [parsedExprIsPlainIntegerALU, parsedExprIsIntegerProducer,
            parsedExprIsUnsupportedRustAlu, parsedExprIsMslMsrProducer,
            parsedExprIsFloatReluProducer, parsedExprIsBlockFloatProducer] at plain
      | l1bm l1op =>
          simp [parsedExprIsPlainIntegerALU, parsedExprIsIntegerProducer,
            parsedExprIsUnsupportedRustAlu, parsedExprIsMslMsrProducer,
            parsedExprIsFloatReluProducer, parsedExprIsBlockFloatProducer] at plain
      | l2bm l2op =>
          simp [parsedExprIsPlainIntegerALU, parsedExprIsIntegerProducer,
            parsedExprIsUnsupportedRustAlu, parsedExprIsMslMsrProducer,
            parsedExprIsFloatReluProducer, parsedExprIsBlockFloatProducer] at plain

/-! ## 2. The `.matrixRead` row shape at an arbitrary incoming slot state

The matrix-read branch of `prepareParsedIntegerMatrixReadLineExpression` passes
its slot argument straight to `prepareParsedMatrixReadExprCycles`, which is
already analysed at an arbitrary slot state by
`prepareParsedMatrixReadExprCycles_zeroShape`: the row's data comes from the
matrix store, not from the forwarding slots, so the `.double` copy fact is
slot-independent.  Only the round-46 wrapper instantiated the slots at
`welcomeZeroSlots`. -/

/-- **The `.matrixRead` row's `.lm1` shape at an arbitrary incoming slot state**,
uniformly in the row's mask / no-forward / reduced flags. -/
theorem matrixReadRow_lm1_shape_of_startSlots (e : ParsedExpr) (precision : ParsedPrecision)
    (sideY : Bool) (width : Fin 5) (row : Fin (2 ^ 32))
    (op : e.op = .matrixRead precision)
    (sources : e.sources = [.matrix sideY width (some row)])
    (control : ParsedMaskExecutionControl) (hasSingleLineMask noForward reduced : Bool)
    (w : PEMemory.Width)
    (startSlots : ProofsLean.MNCore.Forwarding.Slots)
    (nodup : (e.toIssueExpr 0).writeBanks.Nodup)
    (staticWidth : ∀ destination ∈ e.destinations, ∀ v : PEMemory.Width,
      ParsedOperand.directDestinationBankWidth? destination =
        some (PEMemory.Bank.lm1, v) → v = w)
    (writes : List PreparedParsedMaskedWrite)
    (slots : ProofsLean.MNCore.Forwarding.Slots) (bars : List (Bool × BitVec 12))
    (prep : prepareParsedIntegerMatrixReadLineExpression welcomeZeroFiles welcomeZeroSlots
      startSlots welcomeZeroMatrixStore e control hasSingleLineMask noForward reduced =
      .ok (writes, slots, bars)) :
    Lm1WritesDoubleCopy writes ∨ Lm1WritesNarrow writes :=
  prepareParsedIntegerMatrixReadLineExpression_matrixRead_shape e precision sideY width row op
    sources startSlots control hasSingleLineMask noForward reduced w nodup staticWidth
    writes slots bars prep

/-! ## 3. The integer-stage fold along an arbitrary row position

The stage's fold `prepareParsedIntegerMatrixReadLineExpressions` appends each
row's prepared writes to an accumulator, so its result splits at any position of
the row list.  The rows before and after the writer are `.lm1`-free as soon as
they have no `.lm1` destination operand
(`prepareParsedIntegerMatrixReadLineExpression_lm1_free`). -/

/-- **The fold splits at an arbitrary list decomposition.** -/
theorem prepareParsedIntegerMatrixReadLineExpressions_split_run
    (files : IntegerRegisterFiles) (oldSlots : ProofsLean.MNCore.Forwarding.Slots)
    (store : ParsedMatrixReadStore) (control : ParsedMaskExecutionControl)
    (hasSingleLineMask noForward reduced : Bool) (a b : List ParsedExpr) :
    ∀ (writes : List PreparedParsedMaskedWrite)
      (slots : ProofsLean.MNCore.Forwarding.Slots) (bars : List (Bool × BitVec 12))
      (finalWrites : List PreparedParsedMaskedWrite)
      (finalSlots : ProofsLean.MNCore.Forwarding.Slots)
      (finalBars : List (Bool × BitVec 12)),
      prepareParsedIntegerMatrixReadLineExpressions files oldSlots store control
        hasSingleLineMask noForward reduced (a ++ b) writes slots bars =
          .ok (finalWrites, finalSlots, finalBars) →
      ∃ (aw : List PreparedParsedMaskedWrite)
        (as : ProofsLean.MNCore.Forwarding.Slots) (ab : List (Bool × BitVec 12)),
        prepareParsedIntegerMatrixReadLineExpressions files oldSlots store control
          hasSingleLineMask noForward reduced a writes slots bars =
            .ok (writes ++ aw, as, bars ++ ab) ∧
        prepareParsedIntegerMatrixReadLineExpressions files oldSlots store control
          hasSingleLineMask noForward reduced b (writes ++ aw) as (bars ++ ab) =
            .ok (finalWrites, finalSlots, finalBars) := by
  induction a with
  | nil =>
      intro writes slots bars finalWrites finalSlots finalBars prep
      refine ⟨[], slots, [], ?_, ?_⟩
      · simp [prepareParsedIntegerMatrixReadLineExpressions]
      · simpa using prep
  | cons expression rest ih =>
      intro writes slots bars finalWrites finalSlots finalBars prep
      simp only [List.cons_append, prepareParsedIntegerMatrixReadLineExpressions] at prep
      cases head : prepareParsedIntegerMatrixReadLineExpression files oldSlots slots store
          expression control hasSingleLineMask noForward reduced with
      | failure => rw [head] at prep; simp at prep
      | unknown => rw [head] at prep; simp at prep
      | ok result =>
          obtain ⟨expressionWrites, expressionSlots, expressionBars⟩ := result
          rw [head] at prep
          dsimp only at prep
          obtain ⟨aw, as, ab, restRun, tailRun⟩ :=
            ih (writes ++ expressionWrites) expressionSlots (bars ++ expressionBars)
              finalWrites finalSlots finalBars prep
          refine ⟨expressionWrites ++ aw, as, expressionBars ++ ab, ?_, ?_⟩
          · simp only [List.cons_append, prepareParsedIntegerMatrixReadLineExpressions, head]
            simpa only [List.append_assoc] using restRun
          · simpa only [List.append_assoc] using tailRun

/-- **The part of the fold after a point is `.lm1`-free** whenever every row of
it has no `.lm1` destination operand, regardless of what the accumulator already
contains. -/
theorem prepareParsedIntegerMatrixReadLineExpressions_free_suffix
    (files : IntegerRegisterFiles) (oldSlots : ProofsLean.MNCore.Forwarding.Slots)
    (store : ParsedMatrixReadStore) (control : ParsedMaskExecutionControl)
    (hasSingleLineMask noForward reduced : Bool) (expressions : List ParsedExpr)
    (noLm1 : ∀ expression ∈ expressions, WelcomeRowHasNoLm1Destination expression)
    (writes : List PreparedParsedMaskedWrite)
    (slots : ProofsLean.MNCore.Forwarding.Slots) (bars : List (Bool × BitVec 12))
    (finalWrites : List PreparedParsedMaskedWrite)
    (finalSlots : ProofsLean.MNCore.Forwarding.Slots)
    (finalBars : List (Bool × BitVec 12))
    (prep : prepareParsedIntegerMatrixReadLineExpressions files oldSlots store control
      hasSingleLineMask noForward reduced expressions writes slots bars =
        .ok (finalWrites, finalSlots, finalBars)) :
    ∃ newWrites : List PreparedParsedMaskedWrite,
      finalWrites = writes ++ newWrites ∧ Lm1FreePreparedWrites newWrites := by
  induction expressions generalizing writes slots bars with
  | nil =>
      simp only [prepareParsedIntegerMatrixReadLineExpressions, StepResult.ok.injEq,
        Prod.mk.injEq] at prep
      obtain ⟨rfl, rfl, rfl⟩ := prep
      exact ⟨[], (List.append_nil writes).symm, lm1FreePreparedWrites_nil⟩
  | cons expression rest ih =>
      simp only [prepareParsedIntegerMatrixReadLineExpressions] at prep
      cases head : prepareParsedIntegerMatrixReadLineExpression files oldSlots slots store
          expression control hasSingleLineMask noForward reduced with
      | failure => rw [head] at prep; simp at prep
      | unknown => rw [head] at prep; simp at prep
      | ok result =>
          obtain ⟨expressionWrites, expressionSlots, expressionBars⟩ := result
          rw [head] at prep
          dsimp only at prep
          have headFree : Lm1FreePreparedWrites expressionWrites :=
            prepareParsedIntegerMatrixReadLineExpression_lm1_free files oldSlots slots store
              expression control hasSingleLineMask noForward reduced expressionWrites
              expressionSlots expressionBars (noLm1 expression (by simp)) head
          obtain ⟨newWrites, restEq, restFree⟩ :=
            ih (fun item member => noLm1 item (List.mem_cons_of_mem _ member))
              (writes ++ expressionWrites) expressionSlots (bars ++ expressionBars) prep
          exact ⟨expressionWrites ++ newWrites, by
            rw [restEq, List.append_assoc], lm1FreePreparedWrites_append headFree restFree⟩

/-- **The integer stage splits at an arbitrary row position.**  If the stage's
filtered row list is `before ++ e :: after` and the rows of `before` and `after`
have no `.lm1` destination, then the prepared write list is
`beforeWrites ++ (rowWrites ++ afterWrites)`, the row preparation of `e` happens
at whatever slot state the prefix produced, and the two outer blocks are
`.lm1`-free.  This is the slot-free replacement of
`welcomeIntegerPrep_single_writer`, whose companions had to be `.noforward` /
`.wait` rows. -/
theorem welcomeIntegerPrep_split (state : State) (expressions : List ParsedExpr)
    (before after : List ParsedExpr) (e : ParsedExpr)
    (split : expressions.filter parsedExprIsIntegerMatrixReadStageInput = before ++ e :: after)
    (freeBefore : ∀ expression ∈ before, WelcomeRowHasNoLm1Destination expression)
    (freeAfter : ∀ expression ∈ after, WelcomeRowHasNoLm1Destination expression)
    (writes : List PreparedParsedMaskedWrite)
    (slots : ProofsLean.MNCore.Forwarding.Slots) (bars : List (Bool × BitVec 12))
    (prep : welcomeIntegerPrep state welcomePE expressions = .ok (writes, slots, bars)) :
    ∃ (beforeWrites : List PreparedParsedMaskedWrite)
      (prefixSlots : ProofsLean.MNCore.Forwarding.Slots)
      (beforeBars : List (Bool × BitVec 12))
      (rowWrites : List PreparedParsedMaskedWrite)
      (rowSlots : ProofsLean.MNCore.Forwarding.Slots)
      (rowBars : List (Bool × BitVec 12))
      (afterWrites : List PreparedParsedMaskedWrite)
      (afterSlots : ProofsLean.MNCore.Forwarding.Slots)
      (afterBars : List (Bool × BitVec 12)),
      prepareParsedIntegerMatrixReadLineExpression (state.peRegisters welcomePE)
        (stateForwardingSlots state welcomePE) prefixSlots
        (state.matrixRegisters (ParsedIntegerContext.ofLinearIndex welcomePE).group
          (ParsedIntegerContext.ofLinearIndex welcomePE).l2b
          (ParsedIntegerContext.ofLinearIndex welcomePE).l1b)
        e (parsedPEHazardControl state welcomePE)
        ((before ++ e :: after).any parsedExprHasSingleLineWriteMask)
        ((before ++ e :: after).any fun expression =>
          match expression.op with
          | ParsedOp.noforward => true
          | _ => false)
        false = .ok (rowWrites, rowSlots, rowBars) ∧
      writes = beforeWrites ++ (rowWrites ++ afterWrites) ∧
      Lm1FreePreparedWrites beforeWrites ∧ Lm1FreePreparedWrites afterWrites := by
  unfold welcomeIntegerPrep prepareParsedIntegerMatrixReadLineCycles at prep
  dsimp only at prep
  rw [split] at prep
  obtain ⟨beforeWrites, prefixSlots, beforeBars, beforeRun, restRun⟩ :=
    prepareParsedIntegerMatrixReadLineExpressions_split_run (state.peRegisters welcomePE)
      (stateForwardingSlots state welcomePE)
      (state.matrixRegisters (ParsedIntegerContext.ofLinearIndex welcomePE).group
        (ParsedIntegerContext.ofLinearIndex welcomePE).l2b
        (ParsedIntegerContext.ofLinearIndex welcomePE).l1b)
      (parsedPEHazardControl state welcomePE)
      ((before ++ e :: after).any parsedExprHasSingleLineWriteMask)
      ((before ++ e :: after).any fun expression =>
          match expression.op with
          | ParsedOp.noforward => true
          | _ => false)
      false before (e :: after) [] (stateForwardingSlots state welcomePE) [] writes slots bars prep
  simp only [List.nil_append] at beforeRun
  simp only [prepareParsedIntegerMatrixReadLineExpressions] at restRun
  cases rowPrep : prepareParsedIntegerMatrixReadLineExpression (state.peRegisters welcomePE)
      (stateForwardingSlots state welcomePE) prefixSlots
      (state.matrixRegisters (ParsedIntegerContext.ofLinearIndex welcomePE).group
        (ParsedIntegerContext.ofLinearIndex welcomePE).l2b
        (ParsedIntegerContext.ofLinearIndex welcomePE).l1b)
      e (parsedPEHazardControl state welcomePE)
      ((before ++ e :: after).any parsedExprHasSingleLineWriteMask)
      ((before ++ e :: after).any fun expression =>
          match expression.op with
          | ParsedOp.noforward => true
          | _ => false)
      false with
  | failure => rw [rowPrep] at restRun; simp at restRun
  | unknown => rw [rowPrep] at restRun; simp at restRun
  | ok result =>
      obtain ⟨rowWrites, rowSlots, rowBars⟩ := result
      rw [rowPrep] at restRun
      dsimp only at restRun
      obtain ⟨afterWrites, writesEq, afterFree⟩ :=
        prepareParsedIntegerMatrixReadLineExpressions_free_suffix (state.peRegisters welcomePE)
          (stateForwardingSlots state welcomePE)
          (state.matrixRegisters (ParsedIntegerContext.ofLinearIndex welcomePE).group
            (ParsedIntegerContext.ofLinearIndex welcomePE).l2b
            (ParsedIntegerContext.ofLinearIndex welcomePE).l1b)
          (parsedPEHazardControl state welcomePE)
          ((before ++ e :: after).any parsedExprHasSingleLineWriteMask)
          ((before ++ e :: after).any fun expression =>
          match expression.op with
          | ParsedOp.noforward => true
          | _ => false)
          false after freeAfter (beforeWrites ++ rowWrites) rowSlots (beforeBars ++ rowBars)
          writes slots bars restRun
      have beforeFree : Lm1FreePreparedWrites beforeWrites :=
        prepareParsedIntegerMatrixReadLineExpressions_lm1_free (state.peRegisters welcomePE)
          (stateForwardingSlots state welcomePE)
          (state.matrixRegisters (ParsedIntegerContext.ofLinearIndex welcomePE).group
            (ParsedIntegerContext.ofLinearIndex welcomePE).l2b
            (ParsedIntegerContext.ofLinearIndex welcomePE).l1b)
          (parsedPEHazardControl state welcomePE)
          ((before ++ e :: after).any parsedExprHasSingleLineWriteMask)
          ((before ++ e :: after).any fun expression =>
          match expression.op with
          | ParsedOp.noforward => true
          | _ => false)
          false before freeBefore [] (stateForwardingSlots state welcomePE) [] beforeWrites
          prefixSlots beforeBars beforeRun (fun write member => by simp at member)
      refine ⟨beforeWrites, prefixSlots, beforeBars, rowWrites, rowSlots, rowBars,
        afterWrites, slots, bars, rowPrep, ?_, beforeFree, afterFree⟩
      rw [writesEq, List.append_assoc]

/-! ## 4. The dispatch theorems without the companion restriction

`welcomePEWriteShape_of_plainWriter_dispatch` and
`welcomePEWriteShape_of_matrixReadWriter_dispatch` of `WelcomeWriterDispatch.lean`
require the integer stage's row list to split as `noforward* ++ [e] ++
noforward*`, because they extract the writer's preparation from
`welcomeIntegerPrep_single_writer`.  With `welcomeIntegerPrep_split` the writer may
be preceded and followed by *arbitrary* preparing rows: their writes are
`.lm1`-free (they are not `.lm1` writers, which `welcomeLm1Writer_rows` supplies
from the issue checker) and they only alter the slot state at which the writer
prepares, which the slot-free row shapes absorb.

The only additional bookkeeping is that the writer itself must not occur in the
`before` / `after` blocks; this is automatic for a split taken at the writer's
own position, and it is what the `e ∉ before`, `e ∉ after` hypotheses record. -/

/-- The line shape when the `.lm1` writer `e` is a plain row, possibly preceded and
followed by arbitrary preparing rows. -/
theorem welcomePEWriteShape_of_plainWriter_arbitrary
    (expressions : List NormalizedExpr)
    (unrefuted : WelcomePEUnrefuted expressions)
    (before after : List ParsedExpr) (e : ParsedExpr)
    (split : (expressions.map NormalizedExpr.toParsed).filter
        parsedExprIsIntegerMatrixReadStageInput = before ++ e :: after)
    (eMem : e ∈ expressions.map NormalizedExpr.toParsed)
    (eWriter : Issue.Bank.lm1 ∈ (e.toIssueExpr 0).writeBanks)
    (notInBefore : e ∉ before) (notInAfter : e ∉ after)
    (flagEq : ((expressions.map NormalizedExpr.toParsed).filter
        parsedExprIsIntegerMatrixReadStageInput).any parsedExprHasSingleLineWriteMask =
        parsedExprHasSingleLineWriteMask e)
    (notDouble : ∀ payload sparse, e.op = .immediate payload sparse →
      ∀ destination ∈ e.destinations,
        ParsedOperand.directDestinationBankWidth? destination ≠
          some (PEMemory.Bank.lm1, PEMemory.Width.double))
    (plain : parsedExprIsPlainIntegerALU e = true)
    (floatEmpty : (expressions.map NormalizedExpr.toParsed).filter
        parsedExprIsSupportedFloatMAUProducer = [])
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
  obtain ⟨beforeWrites, prefixSlots, beforeBars, rowWrites, rowSlots, rowBars, afterWrites,
    afterSlots, afterBars, rowPrep, intWritesEq, beforeFree, afterFree⟩ :=
    welcomeIntegerPrep_split (welcomeInitialState welcomeZeroWords)
      (welcomePEWalkFilter expressions) before after e splitWalk freeBefore freeAfter
      intWrites intSlots intBars intPrep
  have maskEq : ((before ++ e :: after).any parsedExprHasSingleLineWriteMask) =
      parsedExprHasSingleLineWriteMask e := by
    rw [← split]
    exact flagEq
  rw [maskEq] at rowPrep
  have intShape : Lm1WritesShape intWrites := by
    rw [intWritesEq]
    exact lm1WritesShape_of_append_split (leading := beforeWrites) (middle := rowWrites)
      (trailing := afterWrites) rfl beforeFree
      ((plainRow_lm1_shape_of_linePrep_startSlots e plain notDouble
        (welcomeLm1Writer_nodup expressions unrefuted e eMem) _ prefixSlots rowWrites rowSlots
        rowBars rowPrep)) afterFree
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

/-- The line shape when the `.lm1` writer `e` is a `.matrixRead` row, possibly
preceded and followed by arbitrary preparing rows.  No flag agreement is needed:
the matrix-read row shape is uniform in the mask / no-forward / reduced flags. -/
theorem welcomePEWriteShape_of_matrixReadWriter_arbitrary
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
    (floatEmpty : (expressions.map NormalizedExpr.toParsed).filter
        parsedExprIsSupportedFloatMAUProducer = [])
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
  obtain ⟨beforeWrites, prefixSlots, beforeBars, rowWrites, rowSlots, rowBars, afterWrites,
    afterSlots, afterBars, rowPrep, intWritesEq, beforeFree, afterFree⟩ :=
    welcomeIntegerPrep_split (welcomeInitialState welcomeZeroWords)
      (welcomePEWalkFilter expressions) before after e splitWalk freeBefore freeAfter
      intWrites intSlots intBars intPrep
  have intShape : Lm1WritesShape intWrites := by
    rw [intWritesEq]
    exact lm1WritesShape_of_append_split (leading := beforeWrites) (middle := rowWrites)
      (trailing := afterWrites) rfl beforeFree
      ((matrixReadRow_lm1_shape_of_startSlots e precision sideY width row op sources
        welcomeZeroControl _ _ false staticW prefixSlots
        (welcomeLm1Writer_nodup expressions unrefuted e eMem) staticWidth rowWrites rowSlots
        rowBars rowPrep)) afterFree
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

/-! ## 5. The reduced packages: the companion restriction is gone

The round-46 packages `WelcomePEPlainWriterDataFor` /
`WelcomePEMatrixReadWriterDataFor` demanded a split of the integer-stage filter
into `.noforward` / `.wait` companions around the writer.  The slot-free row
shapes make that restriction unnecessary: the new packages only record the
split position, the fact that the writer does not occur in the outer blocks, and
the remaining genuine side conditions (static width, float-MAU absence, and the
mask-flag / immediate-double disjunction for a plain writer).  The round-46
packages imply the new ones. -/

/-- **The slot-free plain-writer data of one line.**  Compared with
`WelcomePEPlainWriterDataFor`, the companion blocks `before` / `after` may be
*arbitrary* preparing rows; only the split position, the non-repetition of the
writer and the remaining side conditions are recorded. -/
def WelcomePEPlainWriterDataForSlotFree (expressions : List NormalizedExpr) : Prop :=
  ∀ (e : ParsedExpr),
    e ∈ expressions.map NormalizedExpr.toParsed →
      parsedExprIsPlainIntegerALU e = true →
      Issue.Bank.lm1 ∈ (e.toIssueExpr 0).writeBanks →
      ∃ before after : List ParsedExpr,
        (expressions.map NormalizedExpr.toParsed).filter
            parsedExprIsIntegerMatrixReadStageInput = before ++ e :: after ∧
          e ∉ before ∧ e ∉ after ∧
          (expressions.map NormalizedExpr.toParsed).filter
            parsedExprIsSupportedFloatMAUProducer = [] ∧
          (((((expressions.map NormalizedExpr.toParsed).filter
                  parsedExprIsIntegerMatrixReadStageInput).any
                parsedExprHasSingleLineWriteMask =
              parsedExprHasSingleLineWriteMask e) ∧
            (∀ (payload : BitVec 32) (sparse : Bool), e.op = .immediate payload sparse →
              ∀ destination ∈ e.destinations,
                ParsedOperand.directDestinationBankWidth? destination ≠
                  some (PEMemory.Bank.lm1, PEMemory.Width.double))) ∨
            WelcomePEInputIndependent expressions)

/-- **The slot-free `.matrixRead`-writer data of one line.** -/
def WelcomePEMatrixReadWriterDataForSlotFree (expressions : List NormalizedExpr) : Prop :=
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
          (expressions.map NormalizedExpr.toParsed).filter
            parsedExprIsSupportedFloatMAUProducer = []

/-- The global slot-free plain-writer package. -/
def WelcomePEPlainWriterDataSlotFree : Prop :=
  ∀ expressions, WelcomePEUnrefuted expressions → WelcomePEPlainWriterDataForSlotFree expressions

/-- The global slot-free `.matrixRead`-writer package. -/
def WelcomePEMatrixReadWriterDataSlotFree : Prop :=
  ∀ expressions, WelcomePEUnrefuted expressions →
    WelcomePEMatrixReadWriterDataForSlotFree expressions

/-- **A `.noforward` / `.wait` companion is never a plain row**, so it cannot
coincide with the plain writer. -/
theorem plainWriter_ne_of_companion (e : ParsedExpr)
    (plain : parsedExprIsPlainIntegerALU e = true)
    (companion : e.op = .noforward ∨ ∃ tag : Fin 256, e.op = .wait tag) : False := by
  obtain ⟨op, sources, destinations, flush, text⟩ := e
  rcases companion with forward | ⟨tag, wait⟩
  · simp_all [parsedExprIsPlainIntegerALU, parsedExprIsIntegerProducer,
      parsedExprIsUnsupportedRustAlu, parsedExprIsMslMsrProducer,
      parsedExprIsFloatReluProducer, parsedExprIsBlockFloatProducer]
  · simp_all [parsedExprIsPlainIntegerALU, parsedExprIsIntegerProducer,
      parsedExprIsUnsupportedRustAlu, parsedExprIsMslMsrProducer,
      parsedExprIsFloatReluProducer, parsedExprIsBlockFloatProducer]

/-- **A `.noforward` / `.wait` companion is never a `.matrixRead` row.** -/
theorem matrixReadWriter_ne_of_companion (e : ParsedExpr)
    (read : parsedExprIsMatrixReadProducer e = true)
    (companion : e.op = .noforward ∨ ∃ tag : Fin 256, e.op = .wait tag) : False := by
  obtain ⟨op, sources, destinations, flush, text⟩ := e
  rcases companion with forward | ⟨tag, wait⟩
  · simp_all [parsedExprIsMatrixReadProducer]
  · simp_all [parsedExprIsMatrixReadProducer]

/-- **The round-46 plain-writer package implies the slot-free one.** -/
theorem welcomePEPlainWriterDataFor_slotFree_of_companion (expressions : List NormalizedExpr)
    (data : WelcomePEPlainWriterDataFor expressions) :
    WelcomePEPlainWriterDataForSlotFree expressions := by
  intro e eMem plain writer
  obtain ⟨before, after, split, skipBefore, skipAfter, floatEmpty, flagAndDouble | indep⟩ :=
    data e eMem plain writer
  · refine ⟨before, after, split, ?_, ?_, floatEmpty,
      Or.inl ⟨flagAndDouble.1, flagAndDouble.2⟩⟩
    · intro member
      exact plainWriter_ne_of_companion e plain (skipBefore e member)
    · intro member
      exact plainWriter_ne_of_companion e plain (skipAfter e member)
  · exact ⟨before, after, split,
      fun member => plainWriter_ne_of_companion e plain (skipBefore e member),
      fun member => plainWriter_ne_of_companion e plain (skipAfter e member),
      floatEmpty, Or.inr indep⟩

/-- **The round-46 `.matrixRead`-writer package implies the slot-free one.** -/
theorem welcomePEMatrixReadWriterDataFor_slotFree_of_companion
    (expressions : List NormalizedExpr) (data : WelcomePEMatrixReadWriterDataFor expressions) :
    WelcomePEMatrixReadWriterDataForSlotFree expressions := by
  intro e eMem read writer
  obtain ⟨before, after, precision, sideY, width, row, staticW, split, skipBefore, skipAfter,
    op, sources, staticWidth, floatEmpty⟩ := data e eMem read writer
  refine ⟨before, after, precision, sideY, width, row, staticW, split, ?_, ?_, op, sources,
    staticWidth, floatEmpty⟩
  · intro member
    exact matrixReadWriter_ne_of_companion e read (skipBefore e member)
  · intro member
    exact matrixReadWriter_ne_of_companion e read (skipAfter e member)

/-- The global implication: the round-46 plain package gives the slot-free one. -/
theorem welcomePEPlainWriterData_slotFree_of_companion (data : WelcomePEPlainWriterData) :
    WelcomePEPlainWriterDataSlotFree :=
  fun expressions unrefuted => welcomePEPlainWriterDataFor_slotFree_of_companion expressions
    (data expressions unrefuted)

/-- The global implication: the round-46 `.matrixRead` package gives the slot-free
one. -/
theorem welcomePEMatrixReadWriterData_slotFree_of_companion
    (data : WelcomePEMatrixReadWriterData) : WelcomePEMatrixReadWriterDataSlotFree :=
  fun expressions unrefuted => welcomePEMatrixReadWriterDataFor_slotFree_of_companion expressions
    (data expressions unrefuted)

/-- **The plain-writer line shape from the slot-free package.** -/
theorem welcomePEWriteShape_of_plainWriter_data_slotFree (expressions : List NormalizedExpr)
    (data : WelcomePEPlainWriterDataForSlotFree expressions)
    (unrefuted : WelcomePEUnrefuted expressions) (e : ParsedExpr)
    (eMem : e ∈ expressions.map NormalizedExpr.toParsed)
    (plain : parsedExprIsPlainIntegerALU e = true)
    (writer : Issue.Bank.lm1 ∈ (e.toIssueExpr 0).writeBanks) :
    WelcomePEWriteShape expressions := by
  obtain ⟨before, after, split, notBefore, notAfter, floatEmpty, flagAndDouble | indep⟩ :=
    data e eMem plain writer
  · obtain ⟨-, -, mslFalse, reluFalse, blockFalse, -, -, matrixMAUFalse, -, l1False, -⟩ :=
      parsedExprIsPlainIntegerALU_facts e plain
    exact welcomePEWriteShape_of_plainWriter_arbitrary expressions unrefuted before after e split
      eMem writer notBefore notAfter flagAndDouble.1 flagAndDouble.2 plain floatEmpty
      (welcomePEMiddleStageLm1Free_of_rows expressions e
        (welcomeLm1Writer_rows expressions unrefuted e eMem writer) mslFalse reluFalse blockFalse)
      (welcomePEMatrixMAUStageLm1Free_of_rows expressions e
        (welcomeLm1Writer_rows expressions unrefuted e eMem writer) matrixMAUFalse)
      (welcomePEL1StageLm1Free_of_rows expressions e
        (welcomeLm1Writer_rows expressions unrefuted e eMem writer) l1False)
  · exact Or.inr (Or.inr indep)

/-- **The `.matrixRead`-writer line shape from the slot-free package.** -/
theorem welcomePEWriteShape_of_matrixReadWriter_data_slotFree
    (expressions : List NormalizedExpr)
    (data : WelcomePEMatrixReadWriterDataForSlotFree expressions)
    (unrefuted : WelcomePEUnrefuted expressions) (e : ParsedExpr)
    (eMem : e ∈ expressions.map NormalizedExpr.toParsed)
    (read : parsedExprIsMatrixReadProducer e = true)
    (writer : Issue.Bank.lm1 ∈ (e.toIssueExpr 0).writeBanks) :
    WelcomePEWriteShape expressions := by
  obtain ⟨before, after, precision, sideY, width, row, staticW, split, notBefore, notAfter,
    op, sources, staticWidth, floatEmpty⟩ := data e eMem read writer
  obtain ⟨mslFalse, reluFalse, blockFalse, matrixMAUFalse, l1False⟩ :=
    matrixRead_parsedExpr_predicates e precision op
  exact welcomePEWriteShape_of_matrixReadWriter_arbitrary expressions unrefuted before after e
    split eMem writer notBefore notAfter precision sideY width row op sources staticW staticWidth
    floatEmpty
    (welcomePEMiddleStageLm1Free_of_rows expressions e
      (welcomeLm1Writer_rows expressions unrefuted e eMem writer) mslFalse reluFalse blockFalse)
    (welcomePEMatrixMAUStageLm1Free_of_rows expressions e
      (welcomeLm1Writer_rows expressions unrefuted e eMem writer) matrixMAUFalse)
    (welcomePEL1StageLm1Free_of_rows expressions e
      (welcomeLm1Writer_rows expressions unrefuted e eMem writer) l1False)

/-! ## 6. The per-line dispatch data with the slot-free packages -/

/-- **The per-line dispatch data, with the plain and `.matrixRead` companions
unrestricted.**  The five other disjuncts are the round-46 ones. -/
def WelcomePELm1LineDispatchDataSlotFree (expressions : List NormalizedExpr) : Prop :=
  (∃ e ∈ expressions.map NormalizedExpr.toParsed,
      Issue.Bank.lm1 ∈ (e.toIssueExpr 0).writeBanks ∧
        parsedExprIsSpecialALUProducer e = true) ∨
    (WelcomePEPlainWriterDataForSlotFree expressions ∧
      ∃ e ∈ expressions.map NormalizedExpr.toParsed,
        Issue.Bank.lm1 ∈ (e.toIssueExpr 0).writeBanks ∧
          parsedExprIsPlainIntegerALU e = true) ∨
    (WelcomePEMatrixReadWriterDataForSlotFree expressions ∧
      ∃ e ∈ expressions.map NormalizedExpr.toParsed,
        Issue.Bank.lm1 ∈ (e.toIssueExpr 0).writeBanks ∧
          parsedExprIsMatrixReadProducer e = true) ∨
    (WelcomePEFloatMAUWriterDataFor expressions ∧
      ∃ e ∈ expressions.map NormalizedExpr.toParsed,
        Issue.Bank.lm1 ∈ (e.toIssueExpr 0).writeBanks ∧
          parsedExprIsSupportedFloatMAUProducer e = true) ∨
    (WelcomePEMatrixMAUWriterDataFor expressions ∧
      ∃ e ∈ expressions.map NormalizedExpr.toParsed,
        Issue.Bank.lm1 ∈ (e.toIssueExpr 0).writeBanks ∧
          parsedExprIsMatrixMAUProducer e = true) ∨
    (WelcomePEL1BMWriterDataFor expressions ∧
      ∃ e ∈ expressions.map NormalizedExpr.toParsed,
        Issue.Bank.lm1 ∈ (e.toIssueExpr 0).writeBanks ∧
          parsedExprIsL1ToPEProducer e = true) ∨
    ((∀ e ∈ expressions.map NormalizedExpr.toParsed,
        Issue.Bank.lm1 ∈ (e.toIssueExpr 0).writeBanks → welcomePhantomWriterKind e) ∧
      WelcomePELm1FreeStageCommit expressions)

/-- The special-ALU writer selects the first disjunct of the slot-free data. -/
theorem welcomePELm1LineDispatchDataSlotFree_special (expressions : List NormalizedExpr)
    (e : ParsedExpr) (eMem : e ∈ expressions.map NormalizedExpr.toParsed)
    (eWriter : Issue.Bank.lm1 ∈ (e.toIssueExpr 0).writeBanks)
    (special : parsedExprIsSpecialALUProducer e = true) :
    WelcomePELm1LineDispatchDataSlotFree expressions :=
  Or.inl ⟨e, eMem, eWriter, special⟩

/-- A plain writer with its slot-free line data selects the second disjunct. -/
theorem welcomePELm1LineDispatchDataSlotFree_plain (expressions : List NormalizedExpr)
    (data : WelcomePEPlainWriterDataForSlotFree expressions) (e : ParsedExpr)
    (eMem : e ∈ expressions.map NormalizedExpr.toParsed)
    (eWriter : Issue.Bank.lm1 ∈ (e.toIssueExpr 0).writeBanks)
    (plain : parsedExprIsPlainIntegerALU e = true) :
    WelcomePELm1LineDispatchDataSlotFree expressions :=
  Or.inr (Or.inl ⟨data, e, eMem, eWriter, plain⟩)

/-- A `.matrixRead` writer with its slot-free line data selects the third
disjunct. -/
theorem welcomePELm1LineDispatchDataSlotFree_matrixRead (expressions : List NormalizedExpr)
    (data : WelcomePEMatrixReadWriterDataForSlotFree expressions) (e : ParsedExpr)
    (eMem : e ∈ expressions.map NormalizedExpr.toParsed)
    (eWriter : Issue.Bank.lm1 ∈ (e.toIssueExpr 0).writeBanks)
    (read : parsedExprIsMatrixReadProducer e = true) :
    WelcomePELm1LineDispatchDataSlotFree expressions :=
  Or.inr (Or.inr (Or.inl ⟨data, e, eMem, eWriter, read⟩))

/-- A float-MAU writer with its line data selects the fourth disjunct. -/
theorem welcomePELm1LineDispatchDataSlotFree_floatMAU (expressions : List NormalizedExpr)
    (data : WelcomePEFloatMAUWriterDataFor expressions) (e : ParsedExpr)
    (eMem : e ∈ expressions.map NormalizedExpr.toParsed)
    (eWriter : Issue.Bank.lm1 ∈ (e.toIssueExpr 0).writeBanks)
    (float : parsedExprIsSupportedFloatMAUProducer e = true) :
    WelcomePELm1LineDispatchDataSlotFree expressions :=
  Or.inr (Or.inr (Or.inr (Or.inl ⟨data, e, eMem, eWriter, float⟩)))

/-- A matrix-MAU writer with its line data selects the fifth disjunct. -/
theorem welcomePELm1LineDispatchDataSlotFree_matrixMAU (expressions : List NormalizedExpr)
    (data : WelcomePEMatrixMAUWriterDataFor expressions) (e : ParsedExpr)
    (eMem : e ∈ expressions.map NormalizedExpr.toParsed)
    (eWriter : Issue.Bank.lm1 ∈ (e.toIssueExpr 0).writeBanks)
    (mau : parsedExprIsMatrixMAUProducer e = true) :
    WelcomePELm1LineDispatchDataSlotFree expressions :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨data, e, eMem, eWriter, mau⟩))))

/-- A `.l1bm` writer with its line data selects the sixth disjunct. -/
theorem welcomePELm1LineDispatchDataSlotFree_l1bm (expressions : List NormalizedExpr)
    (data : WelcomePEL1BMWriterDataFor expressions) (e : ParsedExpr)
    (eMem : e ∈ expressions.map NormalizedExpr.toParsed)
    (eWriter : Issue.Bank.lm1 ∈ (e.toIssueExpr 0).writeBanks)
    (l1 : parsedExprIsL1ToPEProducer e = true) :
    WelcomePELm1LineDispatchDataSlotFree expressions :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨data, e, eMem, eWriter, l1⟩)))))

/-- The phantom/no-writer case selects the seventh disjunct. -/
theorem welcomePELm1LineDispatchDataSlotFree_phantom (expressions : List NormalizedExpr)
    (h : ∀ e ∈ expressions.map NormalizedExpr.toParsed,
      Issue.Bank.lm1 ∈ (e.toIssueExpr 0).writeBanks → welcomePhantomWriterKind e)
    (free : WelcomePELm1FreeStageCommit expressions) :
    WelcomePELm1LineDispatchDataSlotFree expressions :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h, free⟩)))))

/-- **A round-46 per-line dispatch datum gives a slot-free one.** -/
theorem welcomePELm1LineDispatchDataSlotFree_of_old (expressions : List NormalizedExpr)
    (data : WelcomePELm1LineDispatchData expressions) :
    WelcomePELm1LineDispatchDataSlotFree expressions := by
  rcases data with ⟨e, eMem, eWriter, kind⟩ | ⟨plainData, e, eMem, eWriter, kind⟩ |
    ⟨readData, e, eMem, eWriter, kind⟩ | ⟨floatData, e, eMem, eWriter, kind⟩ |
    ⟨mauData, e, eMem, eWriter, kind⟩ | ⟨l1Data, e, eMem, eWriter, kind⟩ | ⟨phantom, free⟩
  · exact Or.inl ⟨e, eMem, eWriter, kind⟩
  · exact Or.inr (Or.inl ⟨welcomePEPlainWriterDataFor_slotFree_of_companion expressions plainData,
      e, eMem, eWriter, kind⟩)
  · exact Or.inr (Or.inr (Or.inl
      ⟨welcomePEMatrixReadWriterDataFor_slotFree_of_companion expressions readData,
        e, eMem, eWriter, kind⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨floatData, e, eMem, eWriter, kind⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨mauData, e, eMem, eWriter, kind⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨l1Data, e, eMem, eWriter, kind⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨phantom, free⟩)))))

/-- **The per-line write shape from the slot-free dispatch data.** -/
theorem welcomePEWriteShape_of_lineDataSlotFree (expressions : List NormalizedExpr)
    (unrefuted : WelcomePEUnrefuted expressions)
    (special : WelcomePESpecialALUWriterShapeObligation)
    (data : WelcomePELm1LineDispatchDataSlotFree expressions) :
    WelcomePEWriteShape expressions := by
  rcases data with ⟨e, eMem, eWriter, kind⟩ | ⟨plainData, e, eMem, eWriter, kind⟩ |
    ⟨readData, e, eMem, eWriter, kind⟩ | ⟨floatData, e, eMem, eWriter, kind⟩ |
    ⟨mauData, e, eMem, eWriter, kind⟩ | ⟨l1Data, e, eMem, eWriter, kind⟩ |
    ⟨-, free⟩
  · exact special expressions unrefuted ⟨e, eMem, eWriter, kind⟩
  · exact welcomePEWriteShape_of_plainWriter_data_slotFree expressions plainData unrefuted e eMem
      kind eWriter
  · exact welcomePEWriteShape_of_matrixReadWriter_data_slotFree expressions readData unrefuted e
      eMem kind eWriter
  · exact welcomePEWriteShape_of_floatMAUWriter_data expressions floatData unrefuted e eMem
      kind eWriter
  · exact welcomePEWriteShape_of_matrixMAUWriter_data expressions mauData unrefuted e eMem
      kind eWriter
  · exact welcomePEWriteShape_of_l1bmWriter_data expressions l1Data unrefuted e eMem
      kind eWriter
  · exact welcomePEWriteShape_of_freeStageCommit expressions free

/-- **The slot-free per-line dispatch data from the slot-free global packages.** -/
theorem welcomePELm1LineDispatchDataSlotFree_of_components
    (phantom : WelcomePELm1PhantomWriterProvenance)
    (plain : WelcomePEPlainWriterDataSlotFree)
    (read : WelcomePEMatrixReadWriterDataSlotFree)
    (float : WelcomePEFloatMAUWriterData) (mau : WelcomePEMatrixMAUWriterData)
    (l1 : WelcomePEL1BMWriterData)
    (expressions : List NormalizedExpr) (unrefuted : WelcomePEUnrefuted expressions) :
    WelcomePELm1LineDispatchDataSlotFree expressions := by
  by_cases hasWriter : ∃ e ∈ expressions.map NormalizedExpr.toParsed,
      Issue.Bank.lm1 ∈ (e.toIssueExpr 0).writeBanks
  · obtain ⟨e, eMem, eWriter⟩ := hasWriter
    have supported := List.all_eq_true.mp unrefuted.1.2.2.2 e eMem
    have notUnsupported : parsedExprIsUnsupportedRustAlu e = false := by
      simpa using (List.any_eq_false.mp unrefuted.1.2.2.1) e eMem
    rcases supportedProducer_partition e supported with
      isPlain | isFamily | isSpecial | isInert | isUnsupported
    · exact welcomePELm1LineDispatchDataSlotFree_plain expressions
        (plain expressions unrefuted) e eMem eWriter isPlain
    · rcases parsedExprIsFamilyProducer_cases e isFamily with
        readKind | mauKind | floatKind | writeKind | toPEKind | l2Kind
      · exact welcomePELm1LineDispatchDataSlotFree_matrixRead expressions
          (read expressions unrefuted) e eMem eWriter readKind
      · exact welcomePELm1LineDispatchDataSlotFree_matrixMAU expressions
          (mau expressions unrefuted) e eMem eWriter mauKind
      · exact welcomePELm1LineDispatchDataSlotFree_floatMAU expressions
          (float expressions unrefuted) e eMem eWriter floatKind
      · have hphantom : ∀ x ∈ expressions.map NormalizedExpr.toParsed,
            Issue.Bank.lm1 ∈ (x.toIssueExpr 0).writeBanks → welcomePhantomWriterKind x := by
          intro x xMem xWriter
          have same : x = e :=
            welcomeLm1Writer_eq_of_two expressions unrefuted xMem eMem xWriter eWriter
          rw [same]
          exact Or.inr (Or.inr (Or.inr (Or.inl writeKind)))
        exact welcomePELm1LineDispatchDataSlotFree_phantom expressions hphantom
          (phantom expressions unrefuted hphantom)
      · exact welcomePELm1LineDispatchDataSlotFree_l1bm expressions
          (l1 expressions unrefuted) e eMem eWriter toPEKind
      · have hphantom : ∀ x ∈ expressions.map NormalizedExpr.toParsed,
            Issue.Bank.lm1 ∈ (x.toIssueExpr 0).writeBanks → welcomePhantomWriterKind x := by
          intro x xMem xWriter
          have same : x = e :=
            welcomeLm1Writer_eq_of_two expressions unrefuted xMem eMem xWriter eWriter
          rw [same]
          exact Or.inr (Or.inr (Or.inr (Or.inr l2Kind)))
        exact welcomePELm1LineDispatchDataSlotFree_phantom expressions hphantom
          (phantom expressions unrefuted hphantom)
    · exact welcomePELm1LineDispatchDataSlotFree_special expressions e eMem eWriter isSpecial
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
      exact welcomePELm1LineDispatchDataSlotFree_phantom expressions hphantom
        (phantom expressions unrefuted hphantom)
    · rw [notUnsupported] at isUnsupported
      cases isUnsupported
  · have hphantom : ∀ x ∈ expressions.map NormalizedExpr.toParsed,
        Issue.Bank.lm1 ∈ (x.toIssueExpr 0).writeBanks → welcomePhantomWriterKind x := by
      intro x xMem xWriter
      exact absurd ⟨x, xMem, xWriter⟩ hasWriter
    exact welcomePELm1LineDispatchDataSlotFree_phantom expressions hphantom
      (phantom expressions unrefuted hphantom)

/-- **The slot-free line-dispatch bundle.** -/
def WelcomePEDispatchResidualsSlotFree : Prop :=
  WelcomePESpecialALUWriterShapeObligation ∧
    ∀ expressions, WelcomePEUnrefuted expressions →
      WelcomePELm1LineDispatchDataSlotFree expressions

/-- **`WelcomePELm1WriteShapeObligation` from the slot-free dispatch bundle.**
This is the round-46 reduction with the `noforward* ++ [writer] ++ noforward*`
companion restriction removed from the plain and `.matrixRead` cases. -/
theorem welcomePELm1WriteShapeObligation_of_dispatchSlotFree
    (residuals : WelcomePEDispatchResidualsSlotFree) :
    WelcomePELm1WriteShapeObligation := by
  obtain ⟨special, data⟩ := residuals
  intro expressions unrefuted
  exact welcomePEWriteShape_of_lineDataSlotFree expressions unrefuted special
    (data expressions unrefuted)

/-- **The slot-free obligation from the slot-free components.**  The three
special-ALU writer cases and the phantom provenance are unchanged; the plain and
`.matrixRead` writer data are the weakened packages. -/
theorem welcomePELm1WriteShapeObligation_of_componentsSlotFree
    (phantom : WelcomePELm1PhantomWriterProvenance)
    (plain : WelcomePEPlainWriterDataSlotFree)
    (read : WelcomePEMatrixReadWriterDataSlotFree)
    (float : WelcomePEFloatMAUWriterData) (mau : WelcomePEMatrixMAUWriterData)
    (l1 : WelcomePEL1BMWriterData)
    (msl : WelcomePEMslMsrWriterShapeObligation)
    (relu : WelcomePEFloatReluWriterShapeObligation)
    (block : WelcomePEBlockFloatWriterShapeObligation) :
    WelcomePELm1WriteShapeObligation :=
  welcomePELm1WriteShapeObligation_of_dispatchSlotFree
    ⟨welcomePESpecialALUWriterShapeObligation_of_three msl relu block,
      fun expressions unrefuted =>
        welcomePELm1LineDispatchDataSlotFree_of_components phantom plain read float mau l1
          expressions unrefuted⟩

/-- **The round-46 nine components give the same obligation through the slot-free
reduction** — the weakening is conservative: the round-46 packages are instances
of the slot-free ones. -/
theorem welcomePELm1WriteShapeObligation_of_components_viaSlotFree
    (phantom : WelcomePELm1PhantomWriterProvenance)
    (plain : WelcomePEPlainWriterData) (read : WelcomePEMatrixReadWriterData)
    (float : WelcomePEFloatMAUWriterData) (mau : WelcomePEMatrixMAUWriterData)
    (l1 : WelcomePEL1BMWriterData)
    (msl : WelcomePEMslMsrWriterShapeObligation)
    (relu : WelcomePEFloatReluWriterShapeObligation)
    (block : WelcomePEBlockFloatWriterShapeObligation) :
    WelcomePELm1WriteShapeObligation :=
  welcomePELm1WriteShapeObligation_of_componentsSlotFree phantom
    (welcomePEPlainWriterData_slotFree_of_companion plain)
    (welcomePEMatrixReadWriterData_slotFree_of_companion read)
    float mau l1 msl relu block

end ProofsLean.MNCore
