import ProofsLean.FootprintCoverage

/-!
# The eight integer-ALU resolvers read only the row's source reads

`ProofsLean/FootprintCoverage.lean` reduces the plain-ALU `.pe` line contract to
the residual `PlusTwoLineFootprintCoversPreparedReads`, proves the per-row
reconciliation `sourceReadUpperBound_subset_hazardAccesses` between the hazard
lowering and the executor's source lowerings, and machine-checks that the
residual *as stated* is false (a `.zero` row's prepared read set contains its
own destination, which its hazard footprint never reports).

This module completes the missing link.  The residual was only missing the
eight-resolver read-set bound
`aluCycleReadSet registers expression control hasSingleLineMask cycle ⊆
 sourceReadUpperBound expression control.context.group ... control.context.tWord`
for `op = .alu` rows; the `.zero` / `.immediate` rows are exactly the ones the
residual cannot include.

## 1. The eight resolvers

Every branch resolver of `prepareParsedIntegerALUExprCycle` computes its reads
from the *source operands of the row*:

* `maskedIntegerReads_subset_sourceReadUpperBound` — resolver 1,
  `ParsedExpr.toDirectMaskedIntegerAccessesInLine?` (masked memory write);
* `maskedListReads_subset_sourceReadUpperBound` — resolver 2,
  `ParsedExpr.toDirectMaskedIntegerWritesInLine?` (multi-destination write);
* `maskAccessesReads_subset_sourceReadUpperBound` — resolver 3,
  `parsedIntegerMaskExprAccessesInLine?` (mask-register / OMR write), whose
  sources are read through `ParsedOperand.toIntegerMaskSourceAccess?`
  (`accessRegion_toIntegerMaskSourceAccess_subset_sourceReadUpperBound`);
* `noWriteAccessesReads_subset_sourceReadUpperBound` — resolver 4,
  `parsedIntegerNoWriteExprAccessesInLine?` (`.nowrite` destination);
* `barAccessesReads_subset_sourceReadUpperBound` — resolver 5,
  `parsedIntegerBarExprAccessesInLine?` (BAR destination);
* `maskInputAccessesReads_subset_sourceReadUpperBound` — resolver 6,
  `parsedIntegerMaskInputExprAccessesInLine?` (OMR destination);
* `maskMemoryThenInputReads_subset_sourceReadUpperBound` — resolver 7,
  `parsedIntegerMaskMemoryThenInputExprAccessesInLine?` (memory + OMR);
* `maskInputThenMemoryReads_subset_sourceReadUpperBound` — resolver 8,
  `parsedIntegerMaskInputThenMemoryExprAccessesInLine?` (OMR + memory).

Their union over the cycle is
`aluCycleReadSet_subset_sourceReadUpperBound`.  Each proof eliminates the
expression structure first (so the op-shape equation can be substituted), then
the source/destination shapes and the per-branch resolutions (resolvers 1-6 by
explicit `cases`; resolvers 7-8 by naming the source shapes and splitting the
remaining matches, which avoids re-elaborating the bank term embedded in the
definition).  The destination resolutions only select the branch, and every read
is one of the two `toParsedIntegerInput?` / `toIntegerMaskSourceAccess?` results
on a member of `expression.sources`.

## 2. The repaired residual

`preparedListReadSet_subset_plusTwoLineFootprint` composes the cycle bound with
`sourceReadUpperBound_subset_hazardAccesses` and
`hazardAccesses_subset_lineSourceAccesses` to obtain

```
preparedListReadSet ... ⊆ plusTwoLineFootprint (.pe expressions) state
```

for every `.pe` line whose rows are all `.alu` rows with addressable
`expression.sources ++ expression.destinations`.  The plainness hypothesis
`(map toParsed expressions).all parsedExprIsPlainIntegerALU = true` is carried
along, as in `PlusTwoLineFootprintCoversPreparedReads`.
`PlusTwoALULineFootprintCoversPreparedReads` packages the statement and is
proved unconditionally in `plusTwoALULineFootprintCoversPreparedReads`.

## 3. The unconditional plus-two chain

`plain_pe_lineDeterminedAtChan_concrete_of_aluRows` feeds the repaired residual
into `pepreparedListCongruent_plain`, `pepreparedListCongruentStrong_plain` and
`plain_pe_channelFrameOn_of_prepared`, giving the `.pe` line contract at the
concrete footprint.  Together with the unconditional `nop` / `mv` leaves this
discharges the new line class `DischargedALULine`, and yields

* `plusTwoWriteDeterminationChan_of_aluRows : PlusTwoWriteDeterminationChan`
  for programs all of whose lines are `nop`, `mv`, or plain-ALU `.pe` lines with
  `.alu` rows and addressable operands (no residual premise), and
* `plusTwo_not_correct_of_concrete_footprint_avoids_chan_of_aluRows`:
  such a program is incorrect whenever it never reads input `j`.

No `sorry`, no `admit`, no `native_decide`, no new axioms, no existing module
edited.
-/

namespace ProofsLean.MNCore

open Issue
open PEMemory

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- A mask-register writer's source access reads only its access region, and
that region is inside the expression's source-read bound. -/
theorem accessRegion_toIntegerMaskSourceAccess_subset_sourceReadUpperBound
    (expression : ParsedExpr) (group : Fin 4) (l2b : Fin 2) (l1b : Fin 8)
    (mab : Fin 16) (pe cycle : Fin 4) (bar0 bar1 : BitVec 12) (tWord : BitVec 32)
    (oper : ParsedOperand) (member : oper ∈ expression.sources)
    (access : DirectMemoryAccess) (rounded : Bool)
    (resolved : ParsedOperand.toIntegerMaskSourceAccess? oper pe cycle bar0 bar1 tWord
      = some (access, rounded)) :
    accessRegion access ⊆
      sourceReadUpperBound expression group l2b l1b mab pe bar0 bar1 tWord := by
  cases oper with
  | mem acc neg ext rnd mask =>
      simp only [ParsedOperand.toIntegerMaskSourceAccess?] at resolved
      obtain ⟨direct, hdirect, hpair⟩ := Option.map_eq_some_iff.mp resolved
      obtain ⟨haccess, _hrounded⟩ := Prod.mk.injEq .. ▸ hpair
      subst haccess
      refine readsRegion_subset_sourceReadUpperBound expression group l2b l1b mab pe bar0 bar1
        tWord (.mem acc neg ext rnd mask) member .long cycle (.memory direct rnd) ?_
      simp only [ParsedOperand.toParsedIntegerInput?]
      rw [hdirect]
      rfl
  | bar lm1 width mask => simp [ParsedOperand.toIntegerMaskSourceAccess?] at resolved
  | forward kind neg ext rnd => simp [ParsedOperand.toIntegerMaskSourceAccess?] at resolved
  | fixed kind => simp [ParsedOperand.toIntegerMaskSourceAccess?] at resolved
  | omr entry mask => simp [ParsedOperand.toIntegerMaskSourceAccess?] at resolved
  | matrix y width row => simp [ParsedOperand.toIntegerMaskSourceAccess?] at resolved
  | nowrite => simp [ParsedOperand.toIntegerMaskSourceAccess?] at resolved
  | l1bm width address => simp [ParsedOperand.toIntegerMaskSourceAccess?] at resolved
  | l2bm address l2b => simp [ParsedOperand.toIntegerMaskSourceAccess?] at resolved
  | dar address => simp [ParsedOperand.toIntegerMaskSourceAccess?] at resolved

/-- The union of two source reads of the row into the source-read bound. -/
theorem union_readsRegion_subset_sourceReadUpperBound
    (expression : ParsedExpr) (group : Fin 4) (l2b : Fin 2) (l1b : Fin 8)
    (mab : Fin 16) (pe cycle : Fin 4) (bar0 bar1 : BitVec 12) (tWord : BitVec 32)
    (operX operY : ParsedOperand) (mX : operX ∈ expression.sources)
    (mY : operY ∈ expression.sources)
    (precisionX precisionY : IntegerALU.Precision)
    (inputX inputY : ParsedIntegerInput)
    (hX : ParsedOperand.toParsedIntegerInput? operX precisionX group l2b l1b mab pe cycle
      bar0 bar1 tWord = some inputX)
    (hY : ParsedOperand.toParsedIntegerInput? operY precisionY group l2b l1b mab pe cycle
      bar0 bar1 tWord = some inputY) :
    (ParsedIntegerInput.readsRegion inputX ∪ ParsedIntegerInput.readsRegion inputY) ⊆
      sourceReadUpperBound expression group l2b l1b mab pe bar0 bar1 tWord :=
  Set.union_subset
    (readsRegion_subset_sourceReadUpperBound expression group l2b l1b mab pe bar0 bar1 tWord
      operX mX precisionX cycle inputX hX)
    (readsRegion_subset_sourceReadUpperBound expression group l2b l1b mab pe bar0 bar1 tWord
      operY mY precisionY cycle inputY hY)

/-- **Resolver 1** (`toDirectMaskedIntegerAccessesInLine?`, the masked memory
write): its two sources are `toParsedIntegerInput?` results on members of
`expression.sources`, so its read region lies in the source-read bound. -/
theorem maskedIntegerReads_subset_sourceReadUpperBound
    (expression : ParsedExpr) (registers : Masks.RegisterFile)
    (directive : ParsedMaskDirective) (hasSingleLineMask : Bool)
    (group : Fin 4) (l2b : Fin 2) (l1b : Fin 8) (mab : Fin 16)
    (pe cycle : Fin 4) (bar0 bar1 : BitVec 12) (tWord : BitVec 32)
    (name : ParsedAluName) (parsedPrecision : ParsedPrecision) (f : Bool) (g : Option (Fin 256))
    (opShape : expression.op = .alu name (some parsedPrecision) f g)
    (accesses : ParsedMaskedIntegerAccesses)
    (lowered : ParsedExpr.toDirectMaskedIntegerAccessesInLine? expression registers directive
      hasSingleLineMask group l2b l1b mab pe cycle bar0 bar1 tWord = some accesses) :
    maskedIntegerReads accesses ⊆
      sourceReadUpperBound expression group l2b l1b mab pe bar0 bar1 tWord := by
  obtain ⟨op, sources, destinations, flush, text⟩ := expression
  simp only at opShape
  subst opShape
  simp only [ParsedExpr.toDirectMaskedIntegerAccessesInLine?] at lowered
  cases sources with
  | cons a rest =>
    cases rest with
    | nil =>
      cases destinations with
      | cons d ds =>
        cases ds with
        | nil =>
          dsimp only at lowered
          split at lowered
          · rename_i precision aluOp hreq
            split at lowered
            · simp at lowered
            · cases hi : ParsedOperand.toParsedIntegerInput? a parsedPrecision.laneWidth
                  group l2b l1b mab pe cycle bar0 bar1 tWord with
              | none => simp only [hi] at lowered; cases lowered
              | some input =>
                cases hd : ParsedOperand.toDirectMemoryDestination? d pe cycle bar0 bar1 tWord with
                | none => simp only [hi, hd] at lowered; cases lowered
                | some destinationAccess =>
                  cases hw : ParsedOperand.resolveMemoryWriteSelection? d destinationAccess.bank
                      registers cycle directive hasSingleLineMask with
                  | none => simp only [hi, hd, hw] at lowered; cases lowered
                  | some writeSelection =>
                    cases hf : resolveFlushSelection? flush registers cycle with
                    | none => simp only [hi, hd, hw, hf] at lowered; cases lowered
                    | some flushSelection =>
                      simp only [hi, hd, hw, hf] at lowered
                      have ha : accesses = ⟨ParsedOp.alu name (some parsedPrecision) f g, input,
                          input, destinationAccess, writeSelection, flushSelection,
                          ⟨.integer precision aluOp, hreq⟩⟩ :=
                        (Option.some.inj lowered).symm
                      subst ha
                      exact Set.union_subset
                        (readsRegion_subset_sourceReadUpperBound
                          ⟨ParsedOp.alu name (some parsedPrecision) f g, [a], [d], flush, text⟩
                          group l2b l1b mab pe bar0 bar1 tWord a (by simp)
                          parsedPrecision.laneWidth cycle input hi)
                        (readsRegion_subset_sourceReadUpperBound
                          ⟨ParsedOp.alu name (some parsedPrecision) f g, [a], [d], flush, text⟩
                          group l2b l1b mab pe bar0 bar1 tWord a (by simp)
                          parsedPrecision.laneWidth cycle input hi)
          · simp at lowered
        | cons d' ds' => dsimp only at lowered; split at lowered <;> simp_all
      | nil => dsimp only at lowered; split at lowered <;> simp_all
    | cons b rest' =>
      cases rest' with
      | nil =>
        cases destinations with
        | cons d ds =>
          cases ds with
          | nil =>
            dsimp only at lowered
            split at lowered
            · rename_i precision aluOp hreq
              split at lowered
              · simp at lowered
              · cases hi : ParsedOperand.toParsedIntegerInput? a parsedPrecision.laneWidth
                    group l2b l1b mab pe cycle bar0 bar1 tWord with
                | none => simp only [hi] at lowered; cases lowered
                | some inputX =>
                  cases hj : ParsedOperand.toParsedIntegerInput? b parsedPrecision.laneWidth
                      group l2b l1b mab pe cycle bar0 bar1 tWord with
                  | none => simp only [hi, hj] at lowered; cases lowered
                  | some inputY =>
                    cases hd : ParsedOperand.toDirectMemoryDestination? d pe cycle bar0 bar1
                        tWord with
                    | none => simp only [hi, hj, hd] at lowered; cases lowered
                    | some destinationAccess =>
                      cases hw : ParsedOperand.resolveMemoryWriteSelection? d
                          destinationAccess.bank registers cycle directive hasSingleLineMask with
                      | none => simp only [hi, hj, hd, hw] at lowered; cases lowered
                      | some writeSelection =>
                        cases hf : resolveFlushSelection? flush registers cycle with
                        | none =>
                          simp only [hi, hj, hd, hw, hf] at lowered; cases lowered
                        | some flushSelection =>
                          simp only [hi, hj, hd, hw, hf] at lowered
                          have ha : accesses = ⟨ParsedOp.alu name (some parsedPrecision) f g,
                              inputX, inputY, destinationAccess, writeSelection, flushSelection,
                              ⟨.integer precision aluOp, hreq⟩⟩ :=
                            (Option.some.inj lowered).symm
                          subst ha
                          exact union_readsRegion_subset_sourceReadUpperBound
                            ⟨ParsedOp.alu name (some parsedPrecision) f g, [a, b], [d], flush,
                              text⟩ group l2b l1b mab pe cycle bar0 bar1 tWord a b (by simp)
                            (by simp) parsedPrecision.laneWidth parsedPrecision.laneWidth inputX
                            inputY hi hj
            · simp at lowered
          | cons d' ds' => dsimp only at lowered; split at lowered <;> simp_all
        | nil => dsimp only at lowered; split at lowered <;> simp_all
      | cons c rest'' => dsimp only at lowered; split at lowered <;> simp_all
  | nil => dsimp only at lowered; split at lowered <;> simp_all

/-- **Resolver 2** (`toDirectMaskedIntegerWritesInLine?`, the multi-destination
masked memory write): the list lowering reads only the head accesses entry,
which is resolver 1 on the same sources. -/
theorem maskedListReads_subset_sourceReadUpperBound
    (expression : ParsedExpr) (registers : Masks.RegisterFile)
    (directive : ParsedMaskDirective) (hasSingleLineMask : Bool)
    (group : Fin 4) (l2b : Fin 2) (l1b : Fin 8) (mab : Fin 16)
    (pe cycle : Fin 4) (bar0 bar1 : BitVec 12) (tWord : BitVec 32)
    (name : ParsedAluName) (parsedPrecision : ParsedPrecision) (f : Bool) (g : Option (Fin 256))
    (opShape : expression.op = .alu name (some parsedPrecision) f g)
    (accesses : List ParsedMaskedIntegerAccesses)
    (lowered : ParsedExpr.toDirectMaskedIntegerWritesInLine? expression registers directive
      hasSingleLineMask group l2b l1b mab pe cycle bar0 bar1 tWord = some accesses) :
    optionMaskedListReads (some accesses) ⊆
      sourceReadUpperBound expression group l2b l1b mab pe bar0 bar1 tWord := by
  obtain ⟨op, sources, destinations, flush, text⟩ := expression
  simp only at opShape
  subst opShape
  simp only [ParsedExpr.toDirectMaskedIntegerWritesInLine?] at lowered
  cases destinations with
  | nil => simp at lowered
  | cons d ds =>
      rw [List.mapM_cons] at lowered
      cases hd : ParsedExpr.toDirectMaskedIntegerAccessesInLine?
          { op := ParsedOp.alu name (some parsedPrecision) f g, sources := sources,
            destinations := [d], flush := flush, text := text }
          registers directive hasSingleLineMask group l2b l1b mab pe cycle bar0 bar1 tWord with
      | none => simp only [hd] at lowered; cases lowered
      | some head =>
          cases hm : List.mapM (fun destination =>
              ParsedExpr.toDirectMaskedIntegerAccessesInLine?
                { op := ParsedOp.alu name (some parsedPrecision) f g, sources := sources,
                  destinations := [destination], flush := flush, text := text }
                registers directive hasSingleLineMask group l2b l1b mab pe cycle bar0 bar1 tWord)
              ds with
          | none => simp only [hd, hm] at lowered; cases lowered
          | some tail =>
              simp only [hd, hm] at lowered
              have ha : accesses = head :: tail := (Option.some.inj lowered).symm
              subst ha
              exact maskedIntegerReads_subset_sourceReadUpperBound
                { op := ParsedOp.alu name (some parsedPrecision) f g, sources := sources,
                  destinations := [d], flush := flush, text := text }
                registers directive hasSingleLineMask group l2b l1b mab pe cycle bar0 bar1
                tWord name parsedPrecision f g rfl head hd


/-- **Resolver 3** (`parsedIntegerMaskExprAccessesInLine?`, the mask-register
write): its two sources are `toIntegerMaskSourceAccess?` results on members of
`expression.sources`. -/
theorem maskAccessesReads_subset_sourceReadUpperBound
    (expression : ParsedExpr) (registers : Masks.RegisterFile)
    (directive : ParsedMaskDirective) (hasSingleLineMask : Bool)
    (group : Fin 4) (l2b : Fin 2) (l1b : Fin 8) (mab : Fin 16)
    (pe cycle : Fin 4) (bar0 bar1 : BitVec 12) (tWord : BitVec 32)
    (name : ParsedAluName) (parsedPrecision : ParsedPrecision) (f : Bool) (g : Option (Fin 256))
    (opShape : expression.op = .alu name (some parsedPrecision) f g)
    (accesses : ParsedIntegerMaskAccesses)
    (lowered : parsedIntegerMaskExprAccessesInLine? expression registers directive
      hasSingleLineMask pe cycle bar0 bar1 tWord = some accesses) :
    maskAccessesReads accesses ⊆
      sourceReadUpperBound expression group l2b l1b mab pe bar0 bar1 tWord := by
  obtain ⟨op, sources, destinations, flush, text⟩ := expression
  simp only at opShape
  subst opShape
  simp only [parsedIntegerMaskExprAccessesInLine?] at lowered
  cases sources with
  | cons a rest =>
    cases rest with
    | nil =>
      cases destinations with
      | cons d ds =>
        cases ds with
        | nil =>
          dsimp only at lowered
          split at lowered
          · rename_i precision aluOp hreq
            split at lowered
            · simp at lowered
            · cases hs : ParsedOperand.toIntegerMaskSourceAccess? a pe cycle bar0 bar1 tWord with
              | none => simp only [hs] at lowered; cases lowered
              | some pair =>
                obtain ⟨sourceAccess, rounded⟩ := pair
                cases he : ParsedOperand.toMaskRegisterEntry? d with
                | none => simp only [hs, he] at lowered; cases lowered
                | some entry =>
                  cases hsel : ParsedOperand.resolveOmrWriteSelection? d registers cycle
                      directive hasSingleLineMask with
                  | none => simp only [hs, he, hsel] at lowered; cases lowered
                  | some selection =>
                    simp only [hs, he, hsel] at lowered
                    have ha : accesses = ⟨ParsedOp.alu name (some parsedPrecision) f g,
                        sourceAccess, sourceAccess, rounded, rounded, entry, selection,
                        ⟨precision, aluOp, hreq⟩⟩ := (Option.some.inj lowered).symm
                    subst ha
                    exact Set.union_subset
                      (accessRegion_toIntegerMaskSourceAccess_subset_sourceReadUpperBound
                        ⟨ParsedOp.alu name (some parsedPrecision) f g, [a], [d], flush, text⟩
                        group l2b l1b mab pe cycle bar0 bar1 tWord a (by simp) sourceAccess
                        rounded hs)
                      (accessRegion_toIntegerMaskSourceAccess_subset_sourceReadUpperBound
                        ⟨ParsedOp.alu name (some parsedPrecision) f g, [a], [d], flush, text⟩
                        group l2b l1b mab pe cycle bar0 bar1 tWord a (by simp) sourceAccess
                        rounded hs)
          · simp at lowered
        | cons d' ds' => dsimp only at lowered; split at lowered <;> simp_all
      | nil => dsimp only at lowered; split at lowered <;> simp_all
    | cons b rest' =>
      cases rest' with
      | nil =>
        cases destinations with
        | cons d ds =>
          cases ds with
          | nil =>
            dsimp only at lowered
            split at lowered
            · rename_i precision aluOp hreq
              split at lowered
              · simp at lowered
              · cases hs : ParsedOperand.toIntegerMaskSourceAccess? a pe cycle bar0 bar1 tWord with
                | none => simp only [hs] at lowered; cases lowered
                | some pairX =>
                  obtain ⟨sourceAccessX, roundedX⟩ := pairX
                  cases hsy : ParsedOperand.toIntegerMaskSourceAccess? b pe cycle bar0 bar1 tWord with
                  | none => simp only [hs, hsy] at lowered; cases lowered
                  | some pairY =>
                    obtain ⟨sourceAccessY, roundedY⟩ := pairY
                    cases he : ParsedOperand.toMaskRegisterEntry? d with
                    | none => simp only [hs, hsy, he] at lowered; cases lowered
                    | some entry =>
                      cases hsel : ParsedOperand.resolveOmrWriteSelection? d registers cycle
                          directive hasSingleLineMask with
                      | none => simp only [hs, hsy, he, hsel] at lowered; cases lowered
                      | some selection =>
                        simp only [hs, hsy, he, hsel] at lowered
                        have ha : accesses = ⟨ParsedOp.alu name (some parsedPrecision) f g,
                            sourceAccessX, sourceAccessY, roundedX, roundedY, entry, selection,
                            ⟨precision, aluOp, hreq⟩⟩ := (Option.some.inj lowered).symm
                        subst ha
                        exact Set.union_subset
                          (accessRegion_toIntegerMaskSourceAccess_subset_sourceReadUpperBound
                            ⟨ParsedOp.alu name (some parsedPrecision) f g, [a, b], [d], flush,
                              text⟩ group l2b l1b mab pe cycle bar0 bar1 tWord a (by simp)
                            sourceAccessX roundedX hs)
                          (accessRegion_toIntegerMaskSourceAccess_subset_sourceReadUpperBound
                            ⟨ParsedOp.alu name (some parsedPrecision) f g, [a, b], [d], flush,
                              text⟩ group l2b l1b mab pe cycle bar0 bar1 tWord b (by simp)
                            sourceAccessY roundedY hsy)
            · simp at lowered
          | cons d' ds' => dsimp only at lowered; split at lowered <;> simp_all
        | nil => dsimp only at lowered; split at lowered <;> simp_all
      | cons c rest'' => dsimp only at lowered; split at lowered <;> simp_all
  | nil => dsimp only at lowered; split at lowered <;> simp_all

/-- **Resolver 4** (`parsedIntegerNoWriteExprAccessesInLine?`, the `.nowrite`
destination). -/
theorem noWriteAccessesReads_subset_sourceReadUpperBound
    (expression : ParsedExpr) (registers : Masks.RegisterFile)
    (pe cycle : Fin 4) (group : Fin 4) (l2b : Fin 2) (l1b : Fin 8)
    (mab : Fin 16) (bar0 bar1 : BitVec 12) (tWord : BitVec 32)
    (name : ParsedAluName) (parsedPrecision : ParsedPrecision) (f : Bool) (g : Option (Fin 256))
    (opShape : expression.op = .alu name (some parsedPrecision) f g)
    (accesses : ParsedIntegerNoWriteAccesses)
    (lowered : parsedIntegerNoWriteExprAccessesInLine? expression registers pe cycle group
      l2b l1b mab bar0 bar1 tWord = some accesses) :
    noWriteAccessesReads accesses ⊆
      sourceReadUpperBound expression group l2b l1b mab pe bar0 bar1 tWord := by
  obtain ⟨op, sources, destinations, flush, text⟩ := expression
  simp only at opShape
  subst opShape
  cases sources with
  | cons a rest =>
    cases rest with
    | nil =>
      cases destinations with
      | cons d ds =>
        cases ds with
        | nil =>
          cases d with
          | nowrite =>
            simp only [parsedIntegerNoWriteExprAccessesInLine?] at lowered
            split at lowered
            · rename_i request hreq
              split at lowered
              · simp at lowered
              · cases hi : ParsedOperand.toParsedIntegerInput? a parsedPrecision.laneWidth
                    group l2b l1b mab pe cycle bar0 bar1 tWord with
                | none => simp only [hi] at lowered; cases lowered
                | some input =>
                  cases hf : resolveFlushSelection? flush registers cycle with
                  | none => simp only [hi, hf] at lowered; cases lowered
                  | some flushSelection =>
                    simp only [hi, hf] at lowered
                    have ha : accesses = ⟨ParsedOp.alu name (some parsedPrecision) f g, input,
                        input, flushSelection, ⟨request, hreq⟩⟩ :=
                      (Option.some.inj lowered).symm
                    subst ha
                    exact Set.union_subset
                      (readsRegion_subset_sourceReadUpperBound
                        ⟨ParsedOp.alu name (some parsedPrecision) f g, [a], [.nowrite], flush,
                          text⟩ group l2b l1b mab pe bar0 bar1 tWord a (by simp)
                        parsedPrecision.laneWidth cycle input hi)
                      (readsRegion_subset_sourceReadUpperBound
                        ⟨ParsedOp.alu name (some parsedPrecision) f g, [a], [.nowrite], flush,
                          text⟩ group l2b l1b mab pe bar0 bar1 tWord a (by simp)
                        parsedPrecision.laneWidth cycle input hi)
            · simp at lowered
          | mem acc neg ext rnd mask =>
            simp only [parsedIntegerNoWriteExprAccessesInLine?] at lowered; split at lowered <;> simp_all
          | bar lm1 width mask =>
            simp only [parsedIntegerNoWriteExprAccessesInLine?] at lowered; split at lowered <;> simp_all
          | forward kind neg ext rnd =>
            simp only [parsedIntegerNoWriteExprAccessesInLine?] at lowered; split at lowered <;> simp_all
          | fixed kind =>
            simp only [parsedIntegerNoWriteExprAccessesInLine?] at lowered; split at lowered <;> simp_all
          | omr entry mask =>
            simp only [parsedIntegerNoWriteExprAccessesInLine?] at lowered; split at lowered <;> simp_all
          | matrix y width row =>
            simp only [parsedIntegerNoWriteExprAccessesInLine?] at lowered; split at lowered <;> simp_all
          | l1bm width address =>
            simp only [parsedIntegerNoWriteExprAccessesInLine?] at lowered; split at lowered <;> simp_all
          | l2bm address l2b =>
            simp only [parsedIntegerNoWriteExprAccessesInLine?] at lowered; split at lowered <;> simp_all
          | dar address =>
            simp only [parsedIntegerNoWriteExprAccessesInLine?] at lowered; split at lowered <;> simp_all
        | cons d' ds' =>
          simp only [parsedIntegerNoWriteExprAccessesInLine?] at lowered; split at lowered <;> simp_all
      | nil => simp only [parsedIntegerNoWriteExprAccessesInLine?] at lowered; split at lowered <;> simp_all
    | cons b rest' =>
      cases rest' with
      | nil =>
        cases destinations with
        | cons d ds =>
          cases ds with
          | nil =>
            cases d with
            | nowrite =>
              simp only [parsedIntegerNoWriteExprAccessesInLine?] at lowered
              split at lowered
              · rename_i request hreq
                split at lowered
                · simp at lowered
                · cases hi : ParsedOperand.toParsedIntegerInput? a parsedPrecision.laneWidth
                      group l2b l1b mab pe cycle bar0 bar1 tWord with
                  | none => simp only [hi] at lowered; cases lowered
                  | some inputX =>
                    cases hj : ParsedOperand.toParsedIntegerInput? b parsedPrecision.laneWidth
                        group l2b l1b mab pe cycle bar0 bar1 tWord with
                    | none => simp only [hi, hj] at lowered; cases lowered
                    | some inputY =>
                      cases hf : resolveFlushSelection? flush registers cycle with
                      | none => simp only [hi, hj, hf] at lowered; cases lowered
                      | some flushSelection =>
                        simp only [hi, hj, hf] at lowered
                        have ha : accesses = ⟨ParsedOp.alu name (some parsedPrecision) f g,
                            inputX, inputY, flushSelection, ⟨request, hreq⟩⟩ :=
                          (Option.some.inj lowered).symm
                        subst ha
                        exact union_readsRegion_subset_sourceReadUpperBound
                          ⟨ParsedOp.alu name (some parsedPrecision) f g, [a, b], [.nowrite],
                            flush, text⟩ group l2b l1b mab pe cycle bar0 bar1 tWord a b
                          (by simp) (by simp) parsedPrecision.laneWidth parsedPrecision.laneWidth
                          inputX inputY hi hj
              · simp at lowered
            | mem acc neg ext rnd mask =>
              simp only [parsedIntegerNoWriteExprAccessesInLine?] at lowered; split at lowered <;> simp_all
            | bar lm1 width mask =>
              simp only [parsedIntegerNoWriteExprAccessesInLine?] at lowered; split at lowered <;> simp_all
            | forward kind neg ext rnd =>
              simp only [parsedIntegerNoWriteExprAccessesInLine?] at lowered; split at lowered <;> simp_all
            | fixed kind =>
              simp only [parsedIntegerNoWriteExprAccessesInLine?] at lowered; split at lowered <;> simp_all
            | omr entry mask =>
              simp only [parsedIntegerNoWriteExprAccessesInLine?] at lowered; split at lowered <;> simp_all
            | matrix y width row =>
              simp only [parsedIntegerNoWriteExprAccessesInLine?] at lowered; split at lowered <;> simp_all
            | l1bm width address =>
              simp only [parsedIntegerNoWriteExprAccessesInLine?] at lowered; split at lowered <;> simp_all
            | l2bm address l2b =>
              simp only [parsedIntegerNoWriteExprAccessesInLine?] at lowered; split at lowered <;> simp_all
            | dar address =>
              simp only [parsedIntegerNoWriteExprAccessesInLine?] at lowered; split at lowered <;> simp_all
          | cons d' ds' =>
            simp only [parsedIntegerNoWriteExprAccessesInLine?] at lowered; split at lowered <;> simp_all
        | nil => simp only [parsedIntegerNoWriteExprAccessesInLine?] at lowered; split at lowered <;> simp_all
      | cons c rest'' =>
        simp only [parsedIntegerNoWriteExprAccessesInLine?] at lowered; split at lowered <;> simp_all
  | nil => simp only [parsedIntegerNoWriteExprAccessesInLine?] at lowered; split at lowered <;> simp_all

/-- **Resolver 5** (`parsedIntegerBarExprAccessesInLine?`, the BAR destination). -/
theorem barAccessesReads_subset_sourceReadUpperBound
    (expression : ParsedExpr) (registers : Masks.RegisterFile)
    (directive : ParsedMaskDirective) (hasSingleLineMask : Bool)
    (group : Fin 4) (l2b : Fin 2) (l1b : Fin 8) (mab : Fin 16)
    (pe cycle : Fin 4) (bar0 bar1 : BitVec 12) (tWord : BitVec 32)
    (name : ParsedAluName) (parsedPrecision : ParsedPrecision) (f : Bool) (g : Option (Fin 256))
    (opShape : expression.op = .alu name (some parsedPrecision) f g)
    (accesses : ParsedIntegerBarAccesses)
    (lowered : parsedIntegerBarExprAccessesInLine? expression registers directive
      hasSingleLineMask group l2b l1b mab pe cycle bar0 bar1 tWord = some accesses) :
    barAccessesReads accesses ⊆
      sourceReadUpperBound expression group l2b l1b mab pe bar0 bar1 tWord := by
  obtain ⟨op, sources, destinations, flush, text⟩ := expression
  simp only at opShape
  subst opShape
  cases sources with
  | cons a rest =>
    cases rest with
    | nil =>
      cases destinations with
      | cons d ds =>
        cases ds with
        | nil =>
          cases d with
          | bar lm1 width mask =>
            simp only [parsedIntegerBarExprAccessesInLine?] at lowered
            split at lowered
            · rename_i request hreq
              split at lowered
              · simp at lowered
              · cases hi : ParsedOperand.toParsedIntegerInput? a parsedPrecision.laneWidth
                    group l2b l1b mab pe cycle bar0 bar1 tWord with
                | none => simp only [hi] at lowered; cases lowered
                | some input =>
                  cases hw : ParsedOperand.resolveMemoryWriteSelection?
                      (.bar lm1 width mask) (if lm1 then Bank.lm1 else Bank.lm0) registers
                      cycle directive hasSingleLineMask with
                  | none => simp only [hi, hw] at lowered; cases lowered
                  | some writeSelection =>
                    cases hf : resolveFlushSelection? flush registers cycle with
                    | none => simp only [hi, hw, hf] at lowered; cases lowered
                    | some flushSelection =>
                      simp only [hi, hw, hf] at lowered
                      have ha : accesses = ⟨ParsedOp.alu name (some parsedPrecision) f g,
                          input, input, lm1, writeSelection, flushSelection,
                          ⟨request, hreq⟩⟩ := (Option.some.inj lowered).symm
                      subst ha
                      exact Set.union_subset
                        (readsRegion_subset_sourceReadUpperBound
                          ⟨ParsedOp.alu name (some parsedPrecision) f g, [a],
                            [.bar lm1 width mask], flush, text⟩ group l2b l1b mab pe bar0 bar1
                          tWord a (by simp) parsedPrecision.laneWidth cycle input hi)
                        (readsRegion_subset_sourceReadUpperBound
                          ⟨ParsedOp.alu name (some parsedPrecision) f g, [a],
                            [.bar lm1 width mask], flush, text⟩ group l2b l1b mab pe bar0 bar1
                          tWord a (by simp) parsedPrecision.laneWidth cycle input hi)
            · simp at lowered
          | mem acc neg ext rnd mask =>
            simp only [parsedIntegerBarExprAccessesInLine?] at lowered; split at lowered <;> simp_all
          | forward kind neg ext rnd =>
            simp only [parsedIntegerBarExprAccessesInLine?] at lowered; split at lowered <;> simp_all
          | fixed kind =>
            simp only [parsedIntegerBarExprAccessesInLine?] at lowered; split at lowered <;> simp_all
          | omr entry mask =>
            simp only [parsedIntegerBarExprAccessesInLine?] at lowered; split at lowered <;> simp_all
          | matrix y width row =>
            simp only [parsedIntegerBarExprAccessesInLine?] at lowered; split at lowered <;> simp_all
          | nowrite =>
            simp only [parsedIntegerBarExprAccessesInLine?] at lowered; split at lowered <;> simp_all
          | l1bm width address =>
            simp only [parsedIntegerBarExprAccessesInLine?] at lowered; split at lowered <;> simp_all
          | l2bm address l2b =>
            simp only [parsedIntegerBarExprAccessesInLine?] at lowered; split at lowered <;> simp_all
          | dar address =>
            simp only [parsedIntegerBarExprAccessesInLine?] at lowered; split at lowered <;> simp_all
        | cons d' ds' =>
          simp only [parsedIntegerBarExprAccessesInLine?] at lowered; split at lowered <;> simp_all
      | nil => simp only [parsedIntegerBarExprAccessesInLine?] at lowered; split at lowered <;> simp_all
    | cons b rest' =>
      cases rest' with
      | nil =>
        cases destinations with
        | cons d ds =>
          cases ds with
          | nil =>
            cases d with
            | bar lm1 width mask =>
              simp only [parsedIntegerBarExprAccessesInLine?] at lowered
              split at lowered
              · rename_i request hreq
                split at lowered
                · simp at lowered
                · cases hi : ParsedOperand.toParsedIntegerInput? a parsedPrecision.laneWidth
                      group l2b l1b mab pe cycle bar0 bar1 tWord with
                  | none => simp only [hi] at lowered; cases lowered
                  | some inputX =>
                    cases hj : ParsedOperand.toParsedIntegerInput? b parsedPrecision.laneWidth
                        group l2b l1b mab pe cycle bar0 bar1 tWord with
                    | none => simp only [hi, hj] at lowered; cases lowered
                    | some inputY =>
                      cases hw : ParsedOperand.resolveMemoryWriteSelection?
                          (.bar lm1 width mask) (if lm1 then Bank.lm1 else Bank.lm0) registers
                          cycle directive hasSingleLineMask with
                      | none => simp only [hi, hj, hw] at lowered; cases lowered
                      | some writeSelection =>
                        cases hf : resolveFlushSelection? flush registers cycle with
                        | none => simp only [hi, hj, hw, hf] at lowered; cases lowered
                        | some flushSelection =>
                          simp only [hi, hj, hw, hf] at lowered
                          have ha : accesses = ⟨ParsedOp.alu name (some parsedPrecision) f g,
                              inputX, inputY, lm1, writeSelection, flushSelection,
                              ⟨request, hreq⟩⟩ := (Option.some.inj lowered).symm
                          subst ha
                          exact union_readsRegion_subset_sourceReadUpperBound
                            ⟨ParsedOp.alu name (some parsedPrecision) f g, [a, b],
                              [.bar lm1 width mask], flush, text⟩ group l2b l1b mab pe cycle
                            bar0 bar1 tWord a b (by simp) (by simp) parsedPrecision.laneWidth
                            parsedPrecision.laneWidth inputX inputY hi hj
              · simp at lowered
            | mem acc neg ext rnd mask =>
              simp only [parsedIntegerBarExprAccessesInLine?] at lowered; split at lowered <;> simp_all
            | forward kind neg ext rnd =>
              simp only [parsedIntegerBarExprAccessesInLine?] at lowered; split at lowered <;> simp_all
            | fixed kind =>
              simp only [parsedIntegerBarExprAccessesInLine?] at lowered; split at lowered <;> simp_all
            | omr entry mask =>
              simp only [parsedIntegerBarExprAccessesInLine?] at lowered; split at lowered <;> simp_all
            | matrix y width row =>
              simp only [parsedIntegerBarExprAccessesInLine?] at lowered; split at lowered <;> simp_all
            | nowrite =>
              simp only [parsedIntegerBarExprAccessesInLine?] at lowered; split at lowered <;> simp_all
            | l1bm width address =>
              simp only [parsedIntegerBarExprAccessesInLine?] at lowered; split at lowered <;> simp_all
            | l2bm address l2b =>
              simp only [parsedIntegerBarExprAccessesInLine?] at lowered; split at lowered <;> simp_all
            | dar address =>
              simp only [parsedIntegerBarExprAccessesInLine?] at lowered; split at lowered <;> simp_all
          | cons d' ds' =>
            simp only [parsedIntegerBarExprAccessesInLine?] at lowered; split at lowered <;> simp_all
        | nil => simp only [parsedIntegerBarExprAccessesInLine?] at lowered; split at lowered <;> simp_all
      | cons c rest'' =>
        simp only [parsedIntegerBarExprAccessesInLine?] at lowered; split at lowered <;> simp_all
  | nil => simp only [parsedIntegerBarExprAccessesInLine?] at lowered; split at lowered <;> simp_all

/-- **Resolver 6** (`parsedIntegerMaskInputExprAccessesInLine?`, the OMR
destination written with the masked ALU result). -/
theorem maskInputAccessesReads_subset_sourceReadUpperBound
    (expression : ParsedExpr) (registers : Masks.RegisterFile)
    (directive : ParsedMaskDirective) (hasSingleLineMask : Bool)
    (group : Fin 4) (l2b : Fin 2) (l1b : Fin 8) (mab : Fin 16)
    (pe cycle : Fin 4) (bar0 bar1 : BitVec 12) (tWord : BitVec 32)
    (name : ParsedAluName) (parsedPrecision : ParsedPrecision) (f : Bool) (g : Option (Fin 256))
    (opShape : expression.op = .alu name (some parsedPrecision) f g)
    (accesses : ParsedIntegerMaskInputAccesses)
    (lowered : parsedIntegerMaskInputExprAccessesInLine? expression registers directive
      hasSingleLineMask group l2b l1b mab pe cycle bar0 bar1 tWord = some accesses) :
    maskInputAccessesReads accesses ⊆
      sourceReadUpperBound expression group l2b l1b mab pe bar0 bar1 tWord := by
  obtain ⟨op, sources, destinations, flush, text⟩ := expression
  simp only at opShape
  subst opShape
  cases sources with
  | cons a rest =>
    cases rest with
    | nil =>
      cases destinations with
      | cons d ds =>
        cases ds with
        | nil =>
          simp only [parsedIntegerMaskInputExprAccessesInLine?] at lowered
          split at lowered
          · rename_i precision aluOp hreq
            split at lowered
            · simp at lowered
            · cases hi : ParsedOperand.toParsedIntegerInput? a parsedPrecision.laneWidth
                  group l2b l1b mab pe cycle bar0 bar1 tWord with
              | none => simp only [hi] at lowered; cases lowered
              | some input =>
                cases he : ParsedOperand.toMaskRegisterEntry? d with
                | none => simp only [hi, he] at lowered; cases lowered
                | some entry =>
                  cases hsel : ParsedOperand.resolveOmrWriteSelection? d registers cycle
                      directive hasSingleLineMask with
                  | none => simp only [hi, he, hsel] at lowered; cases lowered
                  | some selection =>
                    simp only [hi, he, hsel] at lowered
                    have ha : accesses = ⟨ParsedOp.alu name (some parsedPrecision) f g, input,
                        input, entry, selection, ⟨precision, aluOp, hreq⟩⟩ :=
                      (Option.some.inj lowered).symm
                    subst ha
                    exact Set.union_subset
                      (readsRegion_subset_sourceReadUpperBound
                        ⟨ParsedOp.alu name (some parsedPrecision) f g, [a], [d], flush, text⟩
                        group l2b l1b mab pe bar0 bar1 tWord a (by simp)
                        parsedPrecision.laneWidth cycle input hi)
                      (readsRegion_subset_sourceReadUpperBound
                        ⟨ParsedOp.alu name (some parsedPrecision) f g, [a], [d], flush, text⟩
                        group l2b l1b mab pe bar0 bar1 tWord a (by simp)
                        parsedPrecision.laneWidth cycle input hi)
          · simp at lowered
        | cons d' ds' =>
          simp only [parsedIntegerMaskInputExprAccessesInLine?] at lowered
          split at lowered <;> simp_all
      | nil =>
        simp only [parsedIntegerMaskInputExprAccessesInLine?] at lowered
        split at lowered <;> simp_all
    | cons b rest' =>
      cases rest' with
      | nil =>
        cases destinations with
        | cons d ds =>
          cases ds with
          | nil =>
            simp only [parsedIntegerMaskInputExprAccessesInLine?] at lowered
            split at lowered
            · rename_i precision aluOp hreq
              split at lowered
              · simp at lowered
              · cases hi : ParsedOperand.toParsedIntegerInput? a parsedPrecision.laneWidth
                    group l2b l1b mab pe cycle bar0 bar1 tWord with
                | none => simp only [hi] at lowered; cases lowered
                | some inputX =>
                  cases hj : ParsedOperand.toParsedIntegerInput? b parsedPrecision.laneWidth
                      group l2b l1b mab pe cycle bar0 bar1 tWord with
                  | none => simp only [hi, hj] at lowered; cases lowered
                  | some inputY =>
                    cases he : ParsedOperand.toMaskRegisterEntry? d with
                    | none => simp only [hi, hj, he] at lowered; cases lowered
                    | some entry =>
                      cases hsel : ParsedOperand.resolveOmrWriteSelection? d registers cycle
                          directive hasSingleLineMask with
                      | none => simp only [hi, hj, he, hsel] at lowered; cases lowered
                      | some selection =>
                        simp only [hi, hj, he, hsel] at lowered
                        have ha : accesses = ⟨ParsedOp.alu name (some parsedPrecision) f g,
                            inputX, inputY, entry, selection, ⟨precision, aluOp, hreq⟩⟩ :=
                          (Option.some.inj lowered).symm
                        subst ha
                        exact union_readsRegion_subset_sourceReadUpperBound
                          ⟨ParsedOp.alu name (some parsedPrecision) f g, [a, b], [d], flush,
                            text⟩ group l2b l1b mab pe cycle bar0 bar1 tWord a b (by simp)
                          (by simp) parsedPrecision.laneWidth parsedPrecision.laneWidth inputX
                          inputY hi hj
            · simp at lowered
          | cons d' ds' =>
            simp only [parsedIntegerMaskInputExprAccessesInLine?] at lowered
            split at lowered <;> simp_all
        | nil =>
          simp only [parsedIntegerMaskInputExprAccessesInLine?] at lowered
          split at lowered <;> simp_all
      | cons c rest'' =>
        simp only [parsedIntegerMaskInputExprAccessesInLine?] at lowered
        split at lowered <;> simp_all
  | nil =>
    simp only [parsedIntegerMaskInputExprAccessesInLine?] at lowered
    split at lowered <;> simp_all

/-- **Resolver 7** (`parsedIntegerMaskMemoryThenInputExprAccessesInLine?`, a
memory destination followed by an OMR destination).  The destination
resolutions only select the branch; both source accesses are lowered source
operands, so the read region is inside the source-read bound. -/
theorem maskMemoryThenInputReads_subset_sourceReadUpperBound
    (expression : ParsedExpr) (registers : Masks.RegisterFile)
    (directive : ParsedMaskDirective) (hasSingleLineMask : Bool)
    (group : Fin 4) (l2b : Fin 2) (l1b : Fin 8) (mab : Fin 16)
    (pe cycle : Fin 4) (bar0 bar1 : BitVec 12) (tWord : BitVec 32)
    (name : ParsedAluName) (parsedPrecision : ParsedPrecision) (f : Bool) (g : Option (Fin 256))
    (opShape : expression.op = .alu name (some parsedPrecision) f g)
    (accesses : ParsedIntegerMaskMemoryThenInputAccesses)
    (lowered : parsedIntegerMaskMemoryThenInputExprAccessesInLine? expression registers
      directive hasSingleLineMask group l2b l1b mab pe cycle bar0 bar1 tWord = some accesses) :
    maskMemoryThenInputReads accesses ⊆
      sourceReadUpperBound expression group l2b l1b mab pe bar0 bar1 tWord := by
  obtain ⟨op, sources, destinations, flush, text⟩ := expression
  simp only at opShape
  subst opShape
  cases sources with
  | cons a rest =>
    cases rest with
    | nil =>
      simp only [parsedIntegerMaskMemoryThenInputExprAccessesInLine?] at lowered
      repeat' split at lowered
      all_goals (try simp_all)
      all_goals
        (try subst accesses
         intro w hw
         simp only [sourceReadUpperBound, Set.mem_ofPred_eq, Set.mem_union,
           maskMemoryThenInputReads] at hw ⊢
         rcases hw with hw | hw
         · exact ⟨a, by simp_all, cycle, parsedPrecision.laneWidth, _, by simp_all, hw⟩
         · exact ⟨a, by simp_all, cycle, parsedPrecision.laneWidth, _, by simp_all, hw⟩)
    | cons b rest' =>
      cases rest' with
      | nil =>
        simp only [parsedIntegerMaskMemoryThenInputExprAccessesInLine?] at lowered
        repeat' split at lowered
        all_goals (try simp_all)
        all_goals
          (try subst accesses
           intro w hw
           simp only [sourceReadUpperBound, Set.mem_ofPred_eq, Set.mem_union,
             maskMemoryThenInputReads] at hw ⊢
           rcases hw with hw | hw
           · exact ⟨a, by simp_all, cycle, parsedPrecision.laneWidth, _, by simp_all, hw⟩
           · exact ⟨b, by simp_all, cycle, parsedPrecision.laneWidth, _, by simp_all, hw⟩)
      | cons c rest'' =>
        simp only [parsedIntegerMaskMemoryThenInputExprAccessesInLine?] at lowered
        split at lowered <;> simp_all
  | nil =>
    simp only [parsedIntegerMaskMemoryThenInputExprAccessesInLine?] at lowered
    split at lowered <;> simp_all

/-- **Resolver 8** (`parsedIntegerMaskInputThenMemoryExprAccessesInLine?`, an OMR
destination followed by a memory destination). -/
theorem maskInputThenMemoryReads_subset_sourceReadUpperBound
    (expression : ParsedExpr) (registers : Masks.RegisterFile)
    (directive : ParsedMaskDirective) (hasSingleLineMask : Bool)
    (group : Fin 4) (l2b : Fin 2) (l1b : Fin 8) (mab : Fin 16)
    (pe cycle : Fin 4) (bar0 bar1 : BitVec 12) (tWord : BitVec 32)
    (name : ParsedAluName) (parsedPrecision : ParsedPrecision) (f : Bool) (g : Option (Fin 256))
    (opShape : expression.op = .alu name (some parsedPrecision) f g)
    (accesses : ParsedIntegerMaskInputThenMemoryAccesses)
    (lowered : parsedIntegerMaskInputThenMemoryExprAccessesInLine? expression registers
      directive hasSingleLineMask group l2b l1b mab pe cycle bar0 bar1 tWord = some accesses) :
    maskInputThenMemoryReads accesses ⊆
      sourceReadUpperBound expression group l2b l1b mab pe bar0 bar1 tWord := by
  obtain ⟨op, sources, destinations, flush, text⟩ := expression
  simp only at opShape
  subst opShape
  cases sources with
  | cons a rest =>
    cases rest with
    | nil =>
      simp only [parsedIntegerMaskInputThenMemoryExprAccessesInLine?] at lowered
      repeat' split at lowered
      all_goals (try simp_all)
      all_goals
        (try subst accesses
         intro w hw
         simp only [sourceReadUpperBound, Set.mem_ofPred_eq, Set.mem_union,
           maskInputThenMemoryReads] at hw ⊢
         rcases hw with hw | hw
         · exact ⟨a, by simp_all, cycle, parsedPrecision.laneWidth, _, by simp_all, hw⟩
         · exact ⟨a, by simp_all, cycle, parsedPrecision.laneWidth, _, by simp_all, hw⟩)
    | cons b rest' =>
      cases rest' with
      | nil =>
        simp only [parsedIntegerMaskInputThenMemoryExprAccessesInLine?] at lowered
        repeat' split at lowered
        all_goals (try simp_all)
        all_goals
          (try subst accesses
           intro w hw
           simp only [sourceReadUpperBound, Set.mem_ofPred_eq, Set.mem_union,
             maskInputThenMemoryReads] at hw ⊢
           rcases hw with hw | hw
           · exact ⟨a, by simp_all, cycle, parsedPrecision.laneWidth, _, by simp_all, hw⟩
           · exact ⟨b, by simp_all, cycle, parsedPrecision.laneWidth, _, by simp_all, hw⟩)
      | cons c rest'' =>
        simp only [parsedIntegerMaskInputThenMemoryExprAccessesInLine?] at lowered
        split at lowered <;> simp_all
  | nil =>
    simp only [parsedIntegerMaskInputThenMemoryExprAccessesInLine?] at lowered
    split at lowered <;> simp_all

/-- **The read set of one lowered ALU cycle is a source-read bound.**  For an
`.alu` row, the eight resolvers of `prepareParsedIntegerALUExprCycle` only read
the two source operands through `toParsedIntegerInput?` /
`toIntegerMaskSourceAccess?`, so the cycle's read set lies in
`sourceReadUpperBound`. -/
theorem aluCycleReadSet_subset_sourceReadUpperBound
    (registers : Masks.RegisterFile) (expression : ParsedExpr)
    (control : ParsedMaskExecutionControl) (hasSingleLineMask : Bool) (cycle : Fin 4)
    (halu : ∃ name p f g, expression.op = .alu name p f g) :
    aluCycleReadSet registers expression control hasSingleLineMask cycle ⊆
      sourceReadUpperBound expression control.context.group control.context.l2b
        control.context.l1b control.context.mab control.context.pe control.context.bar0
        control.context.bar1 control.context.tWord := by
  obtain ⟨name, p, f, g, h⟩ := halu
  cases p with
  | none =>
      cases hd : expression.destinations with
      | nil =>
        simp [aluCycleReadSet, h, hd, ParsedExpr.toDirectMaskedIntegerAccessesInLine?,
          ParsedExpr.toDirectMaskedIntegerWritesInLine?, parsedIntegerMaskExprAccessesInLine?,
          parsedIntegerNoWriteExprAccessesInLine?, parsedIntegerBarExprAccessesInLine?,
          parsedIntegerMaskInputExprAccessesInLine?,
          parsedIntegerMaskMemoryThenInputExprAccessesInLine?,
          parsedIntegerMaskInputThenMemoryExprAccessesInLine?, optionMaskedReads,
          optionMaskedListReads, optionMaskReads, optionNoWriteReads, optionBarReads,
          optionMaskInputReads, optionMaskMemoryThenInputReads,
          optionMaskInputThenMemoryReads]
      | cons d ds =>
        simp [aluCycleReadSet, h, hd, ParsedExpr.toDirectMaskedIntegerAccessesInLine?,
          ParsedExpr.toDirectMaskedIntegerWritesInLine?, parsedIntegerMaskExprAccessesInLine?,
          parsedIntegerNoWriteExprAccessesInLine?, parsedIntegerBarExprAccessesInLine?,
          parsedIntegerMaskInputExprAccessesInLine?,
          parsedIntegerMaskMemoryThenInputExprAccessesInLine?,
          parsedIntegerMaskInputThenMemoryExprAccessesInLine?, optionMaskedReads,
          optionMaskedListReads, optionMaskReads, optionNoWriteReads, optionBarReads,
          optionMaskInputReads, optionMaskMemoryThenInputReads,
          optionMaskInputThenMemoryReads]
  | some parsedPrecision =>
      intro w hw
      simp only [aluCycleReadSet, h, Set.mem_union, or_assoc, optionMaskedReads,
        optionMaskedListReads, optionMaskReads, optionNoWriteReads, optionBarReads,
        optionMaskInputReads, optionMaskMemoryThenInputReads,
        optionMaskInputThenMemoryReads] at hw
      rcases hw with hw | hw | hw | hw | hw | hw | hw | hw
      · cases h1 : ParsedExpr.toDirectMaskedIntegerAccessesInLine? expression registers
            control.directive hasSingleLineMask control.context.group control.context.l2b
            control.context.l1b control.context.mab control.context.pe cycle
            control.context.bar0 control.context.bar1 control.context.tWord with
        | none => simp [h1] at hw
        | some accesses =>
            simp [h1] at hw
            exact maskedIntegerReads_subset_sourceReadUpperBound expression registers
              control.directive hasSingleLineMask control.context.group control.context.l2b
              control.context.l1b control.context.mab control.context.pe cycle
              control.context.bar0 control.context.bar1 control.context.tWord name
              parsedPrecision f g h accesses h1 hw
      · cases h1 : ParsedExpr.toDirectMaskedIntegerWritesInLine? expression registers
            control.directive hasSingleLineMask control.context.group control.context.l2b
            control.context.l1b control.context.mab control.context.pe cycle
            control.context.bar0 control.context.bar1 control.context.tWord with
        | none => simp [h1] at hw
        | some accesses =>
            simp [h1] at hw
            exact maskedListReads_subset_sourceReadUpperBound expression registers
              control.directive hasSingleLineMask control.context.group control.context.l2b
              control.context.l1b control.context.mab control.context.pe cycle
              control.context.bar0 control.context.bar1 control.context.tWord name
              parsedPrecision f g h accesses h1 hw
      · cases h1 : parsedIntegerMaskExprAccessesInLine? expression registers
            control.directive hasSingleLineMask control.context.pe cycle
            control.context.bar0 control.context.bar1 control.context.tWord with
        | none => simp [h1] at hw
        | some accesses =>
            simp [h1] at hw
            exact maskAccessesReads_subset_sourceReadUpperBound expression registers
              control.directive hasSingleLineMask control.context.group control.context.l2b
              control.context.l1b control.context.mab control.context.pe cycle
              control.context.bar0 control.context.bar1 control.context.tWord name
              parsedPrecision f g h accesses h1 hw
      · cases h1 : parsedIntegerNoWriteExprAccessesInLine? expression registers
            control.context.pe cycle control.context.group control.context.l2b
            control.context.l1b control.context.mab control.context.bar0 control.context.bar1
            control.context.tWord with
        | none => simp [h1] at hw
        | some accesses =>
            simp [h1] at hw
            exact noWriteAccessesReads_subset_sourceReadUpperBound expression registers
              control.context.pe cycle control.context.group control.context.l2b
              control.context.l1b control.context.mab control.context.bar0 control.context.bar1
              control.context.tWord name parsedPrecision f g h accesses h1 hw
      · cases h1 : parsedIntegerBarExprAccessesInLine? expression registers
            control.directive hasSingleLineMask control.context.group control.context.l2b
            control.context.l1b control.context.mab control.context.pe cycle
            control.context.bar0 control.context.bar1 control.context.tWord with
        | none => simp [h1] at hw
        | some accesses =>
            simp [h1] at hw
            exact barAccessesReads_subset_sourceReadUpperBound expression registers
              control.directive hasSingleLineMask control.context.group control.context.l2b
              control.context.l1b control.context.mab control.context.pe cycle
              control.context.bar0 control.context.bar1 control.context.tWord name
              parsedPrecision f g h accesses h1 hw
      · cases h1 : parsedIntegerMaskInputExprAccessesInLine? expression registers
            control.directive hasSingleLineMask control.context.group control.context.l2b
            control.context.l1b control.context.mab control.context.pe cycle
            control.context.bar0 control.context.bar1 control.context.tWord with
        | none => simp [h1] at hw
        | some accesses =>
            simp [h1] at hw
            exact maskInputAccessesReads_subset_sourceReadUpperBound expression registers
              control.directive hasSingleLineMask control.context.group control.context.l2b
              control.context.l1b control.context.mab control.context.pe cycle
              control.context.bar0 control.context.bar1 control.context.tWord name
              parsedPrecision f g h accesses h1 hw
      · cases h1 : parsedIntegerMaskMemoryThenInputExprAccessesInLine? expression registers
            control.directive hasSingleLineMask control.context.group control.context.l2b
            control.context.l1b control.context.mab control.context.pe cycle
            control.context.bar0 control.context.bar1 control.context.tWord with
        | none => simp [h1] at hw
        | some accesses =>
            simp [h1] at hw
            exact maskMemoryThenInputReads_subset_sourceReadUpperBound expression registers
              control.directive hasSingleLineMask control.context.group control.context.l2b
              control.context.l1b control.context.mab control.context.pe cycle
              control.context.bar0 control.context.bar1 control.context.tWord name
              parsedPrecision f g h accesses h1 hw
      · cases h1 : parsedIntegerMaskInputThenMemoryExprAccessesInLine? expression registers
            control.directive hasSingleLineMask control.context.group control.context.l2b
            control.context.l1b control.context.mab control.context.pe cycle
            control.context.bar0 control.context.bar1 control.context.tWord with
        | none => simp [h1] at hw
        | some accesses =>
            simp [h1] at hw
            exact maskInputThenMemoryReads_subset_sourceReadUpperBound expression registers
              control.directive hasSingleLineMask control.context.group control.context.l2b
              control.context.l1b control.context.mab control.context.pe cycle
              control.context.bar0 control.context.bar1 control.context.tWord name
              parsedPrecision f g h accesses h1 hw

/-! ## The repaired residual, and the unconditional plus-two chain -/

/-- **The repaired per-line residual.**  If every row of a `.pe` line is an
`.alu` row whose source and destination operands are all addressable, then the
words the integer-stage preparation reads are covered by the line's concrete
hazard-event footprint.  This is `PlusTwoLineFootprintCoversPreparedReads`
restricted to the rows where it is true: the `.zero` / `.immediate` rows are
excluded, and addressability is what makes the hazard lowering's row-level
`mapM` succeed (`sourceReadUpperBound_subset_hazardAccesses`). -/
theorem preparedListReadSet_subset_plusTwoLineFootprint
    (expressions : List NormalizedExpr)
    (plain : (expressions.map NormalizedExpr.toParsed).all parsedExprIsPlainIntegerALU = true)
    (rows : ∀ expression ∈ expressions.map NormalizedExpr.toParsed,
      (∃ name p f g, expression.op = .alu name p f g) ∧
        (expression.sources ++ expression.destinations).all
          ParsedOperand.directMemoryAddressModeValid = true)
    (state : State) :
    preparedListReadSet (state.peRegisters plusTwoPE).maskRegisters
      ((expressions.map NormalizedExpr.toParsed).filter parsedExprIsIntegerMatrixReadStageInput)
      (parsedPEHazardControl state plusTwoPE) ⊆
    plusTwoLineFootprint (.pe expressions) state := by
  intro w hw
  simp only [preparedListReadSet, Set.mem_ofPred_eq] at hw
  obtain ⟨expression, member, hread⟩ := hw
  have memberAll : expression ∈ expressions.map NormalizedExpr.toParsed :=
    List.mem_of_mem_filter member
  obtain ⟨halu, haddr⟩ := rows expression memberAll
  simp only [parsedExpressionReadSet, Set.mem_ofPred_eq] at hread
  obtain ⟨cycle, _hcycle, hcycleRead⟩ := hread
  have upper := aluCycleReadSet_subset_sourceReadUpperBound
    (state.peRegisters plusTwoPE).maskRegisters expression
    (parsedPEHazardControl state plusTwoPE)
    (((expressions.map NormalizedExpr.toParsed).filter
      parsedExprIsIntegerMatrixReadStageInput).any parsedExprHasSingleLineWriteMask)
    cycle halu
  have hazard := sourceReadUpperBound_subset_hazardAccesses expression
    (parsedPEHazardControl state plusTwoPE) haddr (upper hcycleRead)
  obtain ⟨access, haccess, hwacc⟩ := hazard
  have lineMem : access ∈ lineSourceAccesses (expressions.map NormalizedExpr.toParsed)
      (parsedPEHazardControl state plusTwoPE) :=
    hazardAccesses_subset_lineSourceAccesses _ _ memberAll haccess
  exact (plusTwoLineFootprint_pe expressions state).mpr ⟨access, lineMem, hwacc⟩

/-- **The repaired residual, unconditionally.**  Every plain `.pe` line all of
whose rows are `.alu` rows with addressable operands has its prepared read set
covered by its concrete hazard-event footprint.  This is the statement that
`PlusTwoLineFootprintCoversPreparedReads` was missing. -/
def PlusTwoALULineFootprintCoversPreparedReads : Prop :=
  ∀ (expressions : List NormalizedExpr),
    (expressions.map NormalizedExpr.toParsed).all parsedExprIsPlainIntegerALU = true →
    (∀ expression ∈ expressions.map NormalizedExpr.toParsed,
      (∃ name p f g, expression.op = .alu name p f g) ∧
        (expression.sources ++ expression.destinations).all
          ParsedOperand.directMemoryAddressModeValid = true) →
    ∀ state : State,
      preparedListReadSet (state.peRegisters plusTwoPE).maskRegisters
        ((expressions.map NormalizedExpr.toParsed).filter
          parsedExprIsIntegerMatrixReadStageInput)
        (parsedPEHazardControl state plusTwoPE) ⊆
      plusTwoLineFootprint (.pe expressions) state

/-- **The repaired residual holds unconditionally.** -/
theorem plusTwoALULineFootprintCoversPreparedReads :
    PlusTwoALULineFootprintCoversPreparedReads :=
  fun expressions _plain rows state =>
    preparedListReadSet_subset_plusTwoLineFootprint expressions _plain rows state

/-- **The `.pe` line contract for `alu` rows**, at the concrete footprint,
unconditionally: the coverage part is discharged by
`preparedListReadSet_subset_plusTwoLineFootprint`, the frame by the bank-aware
frame of `ChannelResiduals.lean`. -/
theorem plain_pe_lineDeterminedAtChan_concrete_of_aluRows
    (expressions : List NormalizedExpr)
    (plain : (expressions.map NormalizedExpr.toParsed).all parsedExprIsPlainIntegerALU = true)
    (rows : ∀ expression ∈ expressions.map NormalizedExpr.toParsed,
      (∃ name p f g, expression.op = .alu name p f g) ∧
        (expression.sources ++ expression.destinations).all
          ParsedOperand.directMemoryAddressModeValid = true) :
    LineDeterminedAtChan plusTwoLineFootprint plusTwoPE (.pe expressions) := by
  have covers : ∀ (s s' : State), ChanAgree plusTwoPE s s' →
      preparedListReadSet ((s.peRegisters plusTwoPE)).maskRegisters
        ((expressions.map NormalizedExpr.toParsed).filter
          parsedExprIsIntegerMatrixReadStageInput)
        (parsedPEHazardControl s plusTwoPE) ⊆
      plusTwoLineFootprint (.pe expressions) s ∪ plusTwoLineFootprint (.pe expressions) s' :=
    fun s _s' _chan w hw =>
      Or.inl (preparedListReadSet_subset_plusTwoLineFootprint expressions plain rows s hw)
  exact plain_pe_lineDeterminedAtChan_of_preparedOn plusTwoLineFootprint expressions plain
    (pepreparedListCongruent_plain plusTwoLineFootprint expressions plain covers)
    (plain_pe_channelFrameOn_of_prepared plusTwoLineFootprint expressions plain
      (pepreparedListCongruentStrong_plain plusTwoLineFootprint expressions plain covers)
      covers)

/-- The line classes discharged without further executor analysis and without
any residual: `nop`, `mv`, and plain-ALU `.pe` lines all of whose rows are
`.alu` rows with addressable operands. -/
def DischargedALULine (line : InstructionLine) : Prop :=
  (∃ (count : {n : Nat // 0 < n}) (wait : Option (Fin 256)),
      line = .nop count wait) ∨
  (∃ transfer : NormalizedMv, line = .mv transfer) ∨
  (∃ expressions : List NormalizedExpr,
      line = .pe expressions ∧
        (expressions.map NormalizedExpr.toParsed).all parsedExprIsPlainIntegerALU = true ∧
        (∀ expression ∈ expressions.map NormalizedExpr.toParsed,
          (∃ name p f g, expression.op = .alu name p f g) ∧
            (expression.sources ++ expression.destinations).all
              ParsedOperand.directMemoryAddressModeValid = true))

/-- **Every line in the `alu`-row class satisfies the channel contract**, at the
concrete footprint, with no residual premise. -/
theorem lineDeterminedAtChan_of_aluRows
    (line : InstructionLine) (discharged : DischargedALULine line) :
    LineDeterminedAtChan plusTwoLineFootprint plusTwoPE line := by
  rcases discharged with ⟨count, wait, rfl⟩ | ⟨transfer, rfl⟩ | ⟨expressions, rfl, plain, rows⟩
  · exact nop_lineDeterminedAtChan plusTwoLineFootprint count wait
  · exact mv_lineDeterminedAtChan plusTwoLineFootprint transfer
  · exact plain_pe_lineDeterminedAtChan_concrete_of_aluRows expressions plain rows

/-- **`PlusTwoWriteDeterminationChan` for `alu`-row programs, unconditionally.**
The old coverage residual has been replaced by the discharged residual
`PlusTwoALULineFootprintCoversPreparedReads`. -/
theorem plusTwoWriteDeterminationChan_of_aluRows
    (all : ∀ line, DischargedALULine line) :
    PlusTwoWriteDeterminationChan :=
  fun line => lineDeterminedAtChan_of_aluRows line (all line)

/-- **End-to-end: a program of `nop` / `mv` / `alu`-row `.pe` lines that never
reads input `j` is incorrect**, at the concrete footprint and the channel-aware
contract, with no residual premise. -/
theorem plusTwo_not_correct_of_concrete_footprint_avoids_chan_of_aluRows
    (program : List InstructionLine)
    (discharged : ∀ line ∈ program, DischargedALULine line)
    (j : Fin 20)
    (avoids : ∀ line ∈ program, ∀ s s' : State,
      plusTwoInputWord j ∉ plusTwoLineFootprint line s ∧
        plusTwoInputWord j ∉ plusTwoLineFootprint line s') :
    ¬ ProofsLean.Correct plusTwoSealedMachine plusTwoSpec program :=
  plusTwo_not_correct_of_concrete_footprint_avoids_chan program
    (fun line member => lineDeterminedAtChan_of_aluRows line (discharged line member)) j avoids

end ProofsLean.MNCore
