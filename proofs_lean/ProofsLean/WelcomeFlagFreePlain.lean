import ProofsLean.WelcomeSlotFree
import ProofsLean.WelcomeFlagAgreement

/-! # The flag-free plain row shape: the plain writer package without `flagEq`

`WelcomeFlagAgreement.lean` (round 45) shows that the mask-flag agreement

```
lineFlag = parsedExprHasSingleLineWriteMask e
```

is **false** for the mixed plain/inert class: a plain `.zero` writer with an
unmasked `.lm1` destination has own flag `false`, while an inert `.noforward`
row with a masked `.mem` destination makes the line flag `true`.  The plain row
shape `plainRow_lm1_shape` was stated at the row's own flag, so it did not cover
the writer of such a line.

This module removes the flag from the plain row shape entirely.  The flag enters
`prepareParsedIntegerALUExprCycle` only through the write-selection resolvers
`ParsedOperand.resolveMemoryWriteSelection?` / `resolveOmrWriteSelection?` and
the lowering predicates that call them.  For an unmasked `.mem` / `.bar` /
`.omr` destination, the `false` branch takes the multiline directive selection
(or all-ones when the directive does not target the bank) while the `true`
branch takes all-ones; both are `some`, and the selection value is carried into
the prepared write verbatim — it never influences the destination, the data bus
or the number of `.lm1` writes.  Hence every per-cycle chunk fact proved in
`WelcomePlainStep.lean` is uniform in the flag, and the four-chunk assembly
`lm1WritesShape_of_chunks` applies at *any* flag.

## What is proved

* `PlainFlagFree.prepareParsedIntegerALUExprCycle_lm1_facts` and the whole
  per-branch chain of `WelcomePlainStep.lean` (destination provenance, the copied
  third data word of `.double` writes, the at-most-one-`.lm1`-write count),
  generalised to an arbitrary mask flag `hsm : Bool`;
* `PlainFlagFree.plainRow_lm1_shape_of_startSlots_anyFlag` and
  `PlainFlagFree.plainRow_lm1_shape_of_linePrep_anyFlag` — the plain row's
  four-cycle shape at an arbitrary incoming slot state **and** an arbitrary mask
  flag;
* `PlainFlagFree.plainRow_lm1_shape_of_linePrep_trueFlag` — the line-flag case,
  and `PlainFlagFree.plainRow_lm1_shape_of_linePrep_rowFlagFalse` — the exact
  mixed-class situation (own flag `false`, line flag `true`);
* `welcomePEWriteShape_of_plainWriter_arbitrary_flagFree` — the dispatch
  theorem of `WelcomeSlotFree.lean` with the `flagEq` hypothesis removed;
* `WelcomePEPlainWriterDataForFlagFree` / `WelcomePEPlainWriterDataFlagFree` —
  the slot-free plain package without the flag equation, together with
  `welcomePEPlainWriterDataFor_flagFree_of_slotFree` /
  `welcomePEPlainWriterDataFor_flagFree_of_companion` (the old slot-free and
  round-46 packages imply the new one) and
  `welcomePEWriteShape_of_plainWriter_data_flagFree`;
* `WelcomePELm1LineDispatchDataFlagFree`, its constructors, the per-line shape
  `welcomePEWriteShape_of_lineDataFlagFree`, the components theorem
  `welcomePELm1LineDispatchDataFlagFree_of_components` and the aggregate
  `welcomePELm1WriteShapeObligation_of_dispatchFlagFree` /
  `welcomePELm1WriteShapeObligation_of_componentsFlagFree`, i.e. the
  `WelcomeSlotFree` dispatch with the flag-free plain disjunct.

## What is **not** claimed

The shape proved here is the row-level `Lm1WritesDoubleCopy ∨ Lm1WritesNarrow`;
it is not a lower-bound or optimality statement.  `LowerBound 2` and `Optimal`
are not claimed.  The other five dispatch kinds (float-MAU, matrix-MAU, `.l1bm`,
special ALU, phantom) are unchanged from `WelcomeSlotFree.lean`, and the
remaining special-ALU obligation is still an explicit hypothesis of the
aggregate theorems.

The only side condition kept on a plain writer is the pre-existing
immediate-`.double` exclusion (`notDouble`): an `.immediate` row storing a
`.double` LM1 destination may fail the double-copy data fact, which is exactly
the already-isolated `WelcomePEPlainImmediateDoubleObligation`.  Masked
destinations on the writer itself are *not* a separate case: the generalised
chunk facts cover them as well (a masked destination resolves through the mask,
independently of the flag), so no named Prop is needed for them.

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

namespace PlainFlagFree

/-- The direct lowering's destination resolves a destination operand. -/
theorem destResolves_of_direct (hsm : Bool)
    (expression : ParsedExpr) (cycle : Fin 4) (accesses : ParsedMaskedIntegerAccesses)
    (lowered : ParsedExpr.toDirectMaskedIntegerAccessesInLine? expression
      welcomeZeroFiles.maskRegisters welcomeZeroControl.directive
      hsm welcomeZeroControl.context.group
      welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b
      welcomeZeroControl.context.mab welcomeZeroControl.context.pe cycle
      welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
      welcomeZeroControl.context.tWord = some accesses) :
    DestResolves expression cycle accesses.destination := by
  obtain ⟨destination, member, resolved⟩ :=
    ParsedExpr.toDirectMaskedIntegerAccessesInLine?_destination_provenance expression
      welcomeZeroFiles.maskRegisters welcomeZeroControl.directive
      hsm welcomeZeroControl.context.group
      welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b
      welcomeZeroControl.context.mab welcomeZeroControl.context.pe cycle
      welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
      welcomeZeroControl.context.tWord accesses lowered
  exact ⟨destination, resolved, member⟩

/-- Every destination access of the multiple-destination lowering resolves a
destination operand. -/
theorem destResolves_of_multiple (hsm : Bool)
    (expression : ParsedExpr) (cycle : Fin 4)
    (accesses : List ParsedMaskedIntegerAccesses)
    (lowered : ParsedExpr.toDirectMaskedIntegerWritesInLine? expression
      welcomeZeroFiles.maskRegisters welcomeZeroControl.directive
      hsm welcomeZeroControl.context.group
      welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b
      welcomeZeroControl.context.mab welcomeZeroControl.context.pe cycle
      welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
      welcomeZeroControl.context.tWord = some accesses) :
    ∀ access ∈ accesses, DestResolves expression cycle access.destination := by
  intro access member
  obtain ⟨destination, memberDestination, resolved⟩ :=
    toDirectMaskedIntegerWritesInLine?_mem_provenance expression
      welcomeZeroFiles.maskRegisters welcomeZeroControl.directive
      hsm welcomeZeroControl.context.group
      welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b
      welcomeZeroControl.context.mab welcomeZeroControl.context.pe cycle
      welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
      welcomeZeroControl.context.tWord accesses lowered access member
  exact ⟨destination, resolved, memberDestination⟩

/-- The memory-then-input lowering's memory access resolves the row's memory
destination operand. -/
theorem destResolves_of_memoryThenInput (hsm : Bool)
    (expression : ParsedExpr) (cycle : Fin 4)
    (name : ParsedAluName) (parsedPrecision : ParsedPrecision) (unsigned : Bool)
    (arg : Option (Fin 256))
    (operation : expression.op = .alu name (some parsedPrecision) unsigned arg)
    (accesses : ParsedIntegerMaskMemoryThenInputAccesses)
    (lowered : parsedIntegerMaskMemoryThenInputExprAccessesInLine? expression
      welcomeZeroFiles.maskRegisters welcomeZeroControl.directive
      hsm welcomeZeroControl.context.group
      welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b
      welcomeZeroControl.context.mab welcomeZeroControl.context.pe cycle
      welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
      welcomeZeroControl.context.tWord = some accesses) :
    DestResolves expression cycle accesses.memory := by
  obtain ⟨op, sources, destinations, flush, text⟩ := expression
  subst operation
  simp only [parsedIntegerMaskMemoryThenInputExprAccessesInLine?] at lowered
  repeat' split at lowered
  all_goals (try simp_all)
  all_goals
    (subst accesses
     exact ⟨_, by assumption, by simp⟩)

/-- The input-then-memory lowering's memory access resolves the row's memory
destination operand, which it records. -/
theorem destResolves_of_inputThenMemory (hsm : Bool)
    (expression : ParsedExpr) (cycle : Fin 4)
    (name : ParsedAluName) (parsedPrecision : ParsedPrecision) (unsigned : Bool)
    (arg : Option (Fin 256))
    (operation : expression.op = .alu name (some parsedPrecision) unsigned arg)
    (accesses : ParsedIntegerMaskInputThenMemoryAccesses)
    (lowered : parsedIntegerMaskInputThenMemoryExprAccessesInLine? expression
      welcomeZeroFiles.maskRegisters welcomeZeroControl.directive
      hsm welcomeZeroControl.context.group
      welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b
      welcomeZeroControl.context.mab welcomeZeroControl.context.pe cycle
      welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
      welcomeZeroControl.context.tWord = some accesses) :
    ParsedOperand.toDirectMemoryDestination? accesses.memoryOperand
        welcomeZeroControl.context.pe cycle welcomeZeroControl.context.bar0
        welcomeZeroControl.context.bar1 welcomeZeroControl.context.tWord = some accesses.memory ∧
      accesses.memoryOperand ∈ expression.destinations := by
  obtain ⟨op, sources, destinations, flush, text⟩ := expression
  subst operation
  simp only [parsedIntegerMaskInputThenMemoryExprAccessesInLine?] at lowered
  repeat' split at lowered
  all_goals (try simp_all)
  all_goals
    (subst accesses
     dsimp only
     exact ⟨by assumption, by simp⟩)



/-! ## 5. The multiple-destination lowering as a `mapM` -/

/-- The multiple-destination lowering is a `mapM` of the single-destination
lowering over the row's destinations. -/
theorem toDirectMaskedIntegerWritesInLine?_mapM (hsm : Bool)
    (expression : ParsedExpr) (name : ParsedAluName) (parsedPrecision : ParsedPrecision)
    (unsigned : Bool) (arg : Option (Fin 256))
    (operation : expression.op = .alu name (some parsedPrecision) unsigned arg) (cycle : Fin 4)
    (accesses : List ParsedMaskedIntegerAccesses)
    (lowered : ParsedExpr.toDirectMaskedIntegerWritesInLine? expression
      welcomeZeroFiles.maskRegisters welcomeZeroControl.directive
      hsm welcomeZeroControl.context.group
      welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b
      welcomeZeroControl.context.mab welcomeZeroControl.context.pe cycle
      welcomeZeroControl.context.bar0
      welcomeZeroControl.context.bar1 welcomeZeroControl.context.tWord = some accesses) :
    expression.destinations.mapM (fun destination =>
      ParsedExpr.toDirectMaskedIntegerAccessesInLine?
        { expression with destinations := [destination] } welcomeZeroFiles.maskRegisters
        welcomeZeroControl.directive hsm
        welcomeZeroControl.context.group welcomeZeroControl.context.l2b
        welcomeZeroControl.context.l1b welcomeZeroControl.context.mab
        welcomeZeroControl.context.pe cycle
        welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
        welcomeZeroControl.context.tWord) = some accesses := by
  obtain ⟨op, sources, destinations, flush, text⟩ := expression
  subst operation
  unfold ParsedExpr.toDirectMaskedIntegerWritesInLine? at lowered
  dsimp only at lowered
  cases destinations with
  | nil => simp at lowered
  | cons destination rest => exact lowered

/-- The head access of the multiple-destination lowering has a lowered first
source. -/
theorem toDirectMaskedIntegerWritesInLine?_head_sourceX_eq (hsm : Bool)
    (expression : ParsedExpr) (name : ParsedAluName) (parsedPrecision : ParsedPrecision)
    (unsigned : Bool) (arg : Option (Fin 256)) (cycle : Fin 4)
    (operation : expression.op = .alu name (some parsedPrecision) unsigned arg)
    (access : ParsedMaskedIntegerAccesses) (rest : List ParsedMaskedIntegerAccesses)
    (lowered : ParsedExpr.toDirectMaskedIntegerWritesInLine? expression
      welcomeZeroFiles.maskRegisters welcomeZeroControl.directive
      hsm welcomeZeroControl.context.group
      welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b
      welcomeZeroControl.context.mab welcomeZeroControl.context.pe cycle
      welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
      welcomeZeroControl.context.tWord = some (access :: rest)) :
    ∃ sourceX : ParsedOperand,
      some access.sourceX = ParsedOperand.toParsedIntegerInput? sourceX parsedPrecision.laneWidth
        welcomeZeroControl.context.group welcomeZeroControl.context.l2b
        welcomeZeroControl.context.l1b welcomeZeroControl.context.mab
        welcomeZeroControl.context.pe cycle welcomeZeroControl.context.bar0
        welcomeZeroControl.context.bar1 welcomeZeroControl.context.tWord := by
  have mapped := toDirectMaskedIntegerWritesInLine?_mapM hsm expression name parsedPrecision
    unsigned arg operation cycle (access :: rest) lowered
  cases destinations : expression.destinations with
  | nil => rw [destinations] at mapped; simp at mapped
  | cons destination restDestinations =>
      rw [destinations] at mapped
      obtain ⟨_, getEq⟩ := list_mapM_getElem (fun destination =>
        ParsedExpr.toDirectMaskedIntegerAccessesInLine?
          { expression with destinations := [destination] } welcomeZeroFiles.maskRegisters
          welcomeZeroControl.directive hsm
          welcomeZeroControl.context.group welcomeZeroControl.context.l2b
          welcomeZeroControl.context.l1b welcomeZeroControl.context.mab
          welcomeZeroControl.context.pe cycle welcomeZeroControl.context.bar0
          welcomeZeroControl.context.bar1 welcomeZeroControl.context.tWord)
        (destination :: restDestinations) (access :: rest) mapped
      have hd : ParsedExpr.toDirectMaskedIntegerAccessesInLine?
          { expression with destinations := [destination] } welcomeZeroFiles.maskRegisters
          welcomeZeroControl.directive hsm
          welcomeZeroControl.context.group welcomeZeroControl.context.l2b
          welcomeZeroControl.context.l1b welcomeZeroControl.context.mab
          welcomeZeroControl.context.pe cycle welcomeZeroControl.context.bar0
          welcomeZeroControl.context.bar1 welcomeZeroControl.context.tWord = some access := by
        have := getEq 0 (by simp) (by simp)
        simpa using this
      exact toDirectMaskedIntegerAccessesInLine?_sourceX_eq
        { expression with destinations := [destination] } welcomeZeroFiles.maskRegisters
        welcomeZeroControl.directive hsm
        welcomeZeroControl.context.group welcomeZeroControl.context.l2b
        welcomeZeroControl.context.l1b welcomeZeroControl.context.mab
        welcomeZeroControl.context.pe cycle welcomeZeroControl.context.bar0
        welcomeZeroControl.context.bar1 welcomeZeroControl.context.tWord
        name parsedPrecision unsigned arg operation access hd

/-- The operations of the multiple-destination lowering are the row's operation. -/
theorem toDirectMaskedIntegerWritesInLine?_op (hsm : Bool)
    (expression : ParsedExpr) (name : ParsedAluName) (parsedPrecision : ParsedPrecision)
    (unsigned : Bool) (arg : Option (Fin 256)) (cycle : Fin 4)
    (operation : expression.op = .alu name (some parsedPrecision) unsigned arg)
    (accesses : List ParsedMaskedIntegerAccesses)
    (lowered : ParsedExpr.toDirectMaskedIntegerWritesInLine? expression
      welcomeZeroFiles.maskRegisters welcomeZeroControl.directive
      hsm welcomeZeroControl.context.group
      welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b
      welcomeZeroControl.context.mab welcomeZeroControl.context.pe cycle
      welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
      welcomeZeroControl.context.tWord = some accesses) :
    ∀ access ∈ accesses, access.op = expression.op := by
  have mapped := toDirectMaskedIntegerWritesInLine?_mapM hsm expression name parsedPrecision
    unsigned arg operation cycle accesses lowered
  intro access member
  obtain ⟨destination, _, loweredHere⟩ :=
    list_mapM_mem (fun destination =>
      ParsedExpr.toDirectMaskedIntegerAccessesInLine?
        { expression with destinations := [destination] } welcomeZeroFiles.maskRegisters
        welcomeZeroControl.directive hsm
        welcomeZeroControl.context.group welcomeZeroControl.context.l2b
        welcomeZeroControl.context.l1b welcomeZeroControl.context.mab
        welcomeZeroControl.context.pe cycle welcomeZeroControl.context.bar0
        welcomeZeroControl.context.bar1 welcomeZeroControl.context.tWord)
      expression.destinations accesses mapped access member
  cases loweredHereOne : ParsedExpr.toDirectMaskedIntegerAccessesInLine?
      { expression with destinations := [destination] } welcomeZeroFiles.maskRegisters
      welcomeZeroControl.directive hsm
      welcomeZeroControl.context.group welcomeZeroControl.context.l2b
      welcomeZeroControl.context.l1b welcomeZeroControl.context.mab
      welcomeZeroControl.context.pe cycle welcomeZeroControl.context.bar0
      welcomeZeroControl.context.bar1 welcomeZeroControl.context.tWord with
  | none => rw [loweredHereOne] at loweredHere; simp at loweredHere
  | some first =>
      rw [loweredHereOne] at loweredHere
      obtain rfl := Option.some.inj loweredHere
      exact toDirectMaskedIntegerAccessesInLine?_op
        { expression with destinations := [destination] } welcomeZeroFiles.maskRegisters
        welcomeZeroControl.directive hsm
        welcomeZeroControl.context.group welcomeZeroControl.context.l2b
        welcomeZeroControl.context.l1b welcomeZeroControl.context.mab
        welcomeZeroControl.context.pe cycle welcomeZeroControl.context.bar0
        welcomeZeroControl.context.bar1 welcomeZeroControl.context.tWord first loweredHereOne

/-- At most one `.lm1` access among the multiple-destination lowering's
accesses. -/
theorem toDirectMaskedIntegerWritesInLine?_lm1_count_le (hsm : Bool)
    (expression : ParsedExpr) (name : ParsedAluName) (parsedPrecision : ParsedPrecision)
    (unsigned : Bool) (arg : Option (Fin 256)) (cycle : Fin 4)
    (operation : expression.op = .alu name (some parsedPrecision) unsigned arg)
    (nodup : (expression.toIssueExpr 0).writeBanks.Nodup)
    (accesses : List ParsedMaskedIntegerAccesses)
    (lowered : ParsedExpr.toDirectMaskedIntegerWritesInLine? expression
      welcomeZeroFiles.maskRegisters welcomeZeroControl.directive
      hsm welcomeZeroControl.context.group
      welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b
      welcomeZeroControl.context.mab welcomeZeroControl.context.pe cycle
      welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
      welcomeZeroControl.context.tWord = some accesses) :
    (accesses.filter (fun access => access.destination.bank == PEMemory.Bank.lm1)).length ≤ 1 := by
  have mapped := toDirectMaskedIntegerWritesInLine?_mapM hsm expression name parsedPrecision
    unsigned arg operation cycle accesses lowered
  have sound : ∀ destination access,
      ParsedExpr.toDirectMaskedIntegerAccessesInLine?
        { expression with destinations := [destination] } welcomeZeroFiles.maskRegisters
        welcomeZeroControl.directive hsm
        welcomeZeroControl.context.group welcomeZeroControl.context.l2b
        welcomeZeroControl.context.l1b welcomeZeroControl.context.mab
        welcomeZeroControl.context.pe cycle welcomeZeroControl.context.bar0
        welcomeZeroControl.context.bar1 welcomeZeroControl.context.tWord = some access →
      access.destination.bank = PEMemory.Bank.lm1 →
      ParsedOperand.isLm1MemoryDestination destination = true := by
    intro destination access hLowered hbank
    obtain ⟨resolved, resolvedMem, resolvedEq⟩ :=
      ParsedExpr.toDirectMaskedIntegerAccessesInLine?_destination_provenance
        { expression with destinations := [destination] } welcomeZeroFiles.maskRegisters
        welcomeZeroControl.directive hsm
        welcomeZeroControl.context.group welcomeZeroControl.context.l2b
        welcomeZeroControl.context.l1b welcomeZeroControl.context.mab
        welcomeZeroControl.context.pe cycle welcomeZeroControl.context.bar0
        welcomeZeroControl.context.bar1 welcomeZeroControl.context.tWord access hLowered
    simp only [List.mem_singleton] at resolvedMem
    subst resolved
    have static := ParsedOperand.toDirectMemoryDestination?_bankWidth destination
      welcomeZeroControl.context.pe cycle welcomeZeroControl.context.bar0
      welcomeZeroControl.context.bar1 welcomeZeroControl.context.tWord
    rw [resolvedEq] at static
    simp only [Option.map_some] at static
    have pair : ParsedOperand.directDestinationBankWidth? destination =
        some (PEMemory.Bank.lm1, access.destination.width) := by
      rw [← static, hbank]
    exact directDestinationBankWidth_isLm1 _ _ pair
  have count := mapM_lm1_count_le (fun destination =>
      ParsedExpr.toDirectMaskedIntegerAccessesInLine?
        { expression with destinations := [destination] } welcomeZeroFiles.maskRegisters
        welcomeZeroControl.directive hsm
        welcomeZeroControl.context.group welcomeZeroControl.context.l2b
        welcomeZeroControl.context.l1b welcomeZeroControl.context.mab
        welcomeZeroControl.context.pe cycle welcomeZeroControl.context.bar0
        welcomeZeroControl.context.bar1 welcomeZeroControl.context.tWord)
    ParsedOperand.isLm1MemoryDestination sound expression.destinations accesses mapped
  have one := lm1Destinations_count_le_one expression 0 nodup
  omega

/-- The first source of the memory-then-input lowering is a lowered source
operand. -/
theorem parsedIntegerMaskMemoryThenInputExprAccessesInLine?_sourceX_eq (hsm : Bool)
    (expression : ParsedExpr) (name : ParsedAluName) (parsedPrecision : ParsedPrecision)
    (unsigned : Bool) (arg : Option (Fin 256)) (cycle : Fin 4)
    (operation : expression.op = .alu name (some parsedPrecision) unsigned arg)
    (accesses : ParsedIntegerMaskMemoryThenInputAccesses)
    (lowered : parsedIntegerMaskMemoryThenInputExprAccessesInLine? expression
      welcomeZeroFiles.maskRegisters welcomeZeroControl.directive
      hsm welcomeZeroControl.context.group
      welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b
      welcomeZeroControl.context.mab welcomeZeroControl.context.pe cycle
      welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
      welcomeZeroControl.context.tWord = some accesses) :
    ∃ sourceX : ParsedOperand,
      some accesses.sourceX = ParsedOperand.toParsedIntegerInput? sourceX
        parsedPrecision.laneWidth welcomeZeroControl.context.group welcomeZeroControl.context.l2b
        welcomeZeroControl.context.l1b welcomeZeroControl.context.mab welcomeZeroControl.context.pe
        cycle welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
        welcomeZeroControl.context.tWord := by
  obtain ⟨op, sources, destinations, flush, text⟩ := expression
  subst operation
  simp only [parsedIntegerMaskMemoryThenInputExprAccessesInLine?] at lowered
  repeat' split at lowered
  all_goals (try simp_all)
  all_goals
    (subst accesses
     exact ⟨_, by symm; assumption⟩)

/-- The first source of the input-then-memory lowering is a lowered source
operand. -/
theorem parsedIntegerMaskInputThenMemoryExprAccessesInLine?_sourceX_eq (hsm : Bool)
    (expression : ParsedExpr) (name : ParsedAluName) (parsedPrecision : ParsedPrecision)
    (unsigned : Bool) (arg : Option (Fin 256)) (cycle : Fin 4)
    (operation : expression.op = .alu name (some parsedPrecision) unsigned arg)
    (accesses : ParsedIntegerMaskInputThenMemoryAccesses)
    (lowered : parsedIntegerMaskInputThenMemoryExprAccessesInLine? expression
      welcomeZeroFiles.maskRegisters welcomeZeroControl.directive
      hsm welcomeZeroControl.context.group
      welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b
      welcomeZeroControl.context.mab welcomeZeroControl.context.pe cycle
      welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
      welcomeZeroControl.context.tWord = some accesses) :
    ∃ sourceX : ParsedOperand,
      some accesses.sourceX = ParsedOperand.toParsedIntegerInput? sourceX
        parsedPrecision.laneWidth welcomeZeroControl.context.group welcomeZeroControl.context.l2b
        welcomeZeroControl.context.l1b welcomeZeroControl.context.mab welcomeZeroControl.context.pe
        cycle welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
        welcomeZeroControl.context.tWord := by
  obtain ⟨op, sources, destinations, flush, text⟩ := expression
  subst operation
  simp only [parsedIntegerMaskInputThenMemoryExprAccessesInLine?] at lowered
  repeat' split at lowered
  all_goals (try simp_all)
  all_goals
    (subst accesses
     exact ⟨_, by symm; assumption⟩)

/-! ## 6. The constant stage -/

/-- Every `.memory` constant target resolves a destination operand. -/
theorem destResolves_of_constantTargets (hsm : Bool)
    (expression : ParsedExpr) (cycle : Fin 4) (targets : List ParsedConstantDestination)
    (lowered : ParsedExpr.toDirectMaskedConstantWrites? expression
      welcomeZeroFiles.maskRegisters welcomeZeroControl.directive
      hsm welcomeZeroControl.context.group
      welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b
      welcomeZeroControl.context.mab welcomeZeroControl.context.pe cycle
      welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
      welcomeZeroControl.context.tWord = some targets) :
    ∀ target ∈ targets, ∀ accesses : ParsedMaskedIntegerAccesses, target = .memory accesses →
      DestResolves expression cycle accesses.destination := by
  intro target member accesses isMemory
  obtain ⟨destination, destinationMem, loweredDestination⟩ :=
    toDirectMaskedConstantWrites?_mem_provenance expression welcomeZeroFiles.maskRegisters
      welcomeZeroControl.directive hsm
      welcomeZeroControl.context.group welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b
      welcomeZeroControl.context.mab welcomeZeroControl.context.pe cycle
      welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
      welcomeZeroControl.context.tWord targets lowered target member
  rw [isMemory] at loweredDestination
  obtain ⟨resolved, resolvedMem, resolvedEq⟩ :=
    toDirectMaskedConstantDestination_memory_provenance expression welcomeZeroFiles.maskRegisters
      welcomeZeroControl.directive hsm
      welcomeZeroControl.context.group welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b
      welcomeZeroControl.context.mab welcomeZeroControl.context.pe cycle
      welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
      welcomeZeroControl.context.tWord destination accesses loweredDestination
  simp only [List.mem_singleton] at resolvedMem
  subst resolved
  exact ⟨destination, resolvedEq, destinationMem⟩

/-- **The direct branch.** -/
theorem lm1ChunkFacts_direct (hsm : Bool) (expression : ParsedExpr) (cycle : Fin 4)
    (name : ParsedAluName) (parsedPrecision : ParsedPrecision) (unsigned : Bool)
    (arg : Option (Fin 256))
    (operation : expression.op = .alu name (some parsedPrecision) unsigned arg)
    (accesses : ParsedMaskedIntegerAccesses) (write : PreparedParsedMaskedWrite)
    (lowered : ParsedExpr.toDirectMaskedIntegerAccessesInLine? expression
      welcomeZeroFiles.maskRegisters welcomeZeroControl.directive
      hsm welcomeZeroControl.context.group
      welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b
      welcomeZeroControl.context.mab welcomeZeroControl.context.pe cycle
      welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
      welcomeZeroControl.context.tWord = some accesses)
    (prepared : prepareParsedMaskedWriteWithForwarding welcomeZeroFiles welcomeZeroSlots cycle
      accesses false = .ok write) :
    Lm1ChunkFacts expression cycle [write] := by
  have destinationEq := prepareParsedMaskedWriteWithForwarding_destination welcomeZeroFiles
    welcomeZeroSlots cycle accesses false write prepared
  have provenance := destResolves_of_direct hsm expression cycle accesses lowered
  obtain ⟨x, readX⟩ := prepareParsedMaskedWriteWithForwarding_readX_ok welcomeZeroFiles
    welcomeZeroSlots cycle accesses false write prepared
  obtain ⟨sourceX, sourceEq⟩ := toDirectMaskedIntegerAccessesInLine?_sourceX_eq expression
    welcomeZeroFiles.maskRegisters welcomeZeroControl.directive
    hsm welcomeZeroControl.context.group
    welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b welcomeZeroControl.context.mab
    welcomeZeroControl.context.pe cycle welcomeZeroControl.context.bar0
    welcomeZeroControl.context.bar1 welcomeZeroControl.context.tWord name parsedPrecision
    unsigned arg operation accesses lowered
  have accessesOp := toDirectMaskedIntegerAccessesInLine?_op expression
    welcomeZeroFiles.maskRegisters welcomeZeroControl.directive
    hsm welcomeZeroControl.context.group
    welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b welcomeZeroControl.context.mab
    welcomeZeroControl.context.pe cycle welcomeZeroControl.context.bar0
    welcomeZeroControl.context.bar1 welcomeZeroControl.context.tWord accesses lowered
  have copy := welcomeZero_toParsedIntegerInput_read_copy sourceX parsedPrecision.laneWidth
    cycle accesses.sourceX sourceEq.symm x readX
  have dataCopy := prepareParsedMaskedWriteWithForwarding_data_two_copy name parsedPrecision
    unsigned arg accesses write cycle false x (accessesOp.trans operation) readX copy prepared
  refine ⟨?_, ?_, ?_⟩
  · intro item member access destinationEq' bank
    simp only [List.mem_singleton] at member
    subst member
    rw [destinationEq] at destinationEq'
    obtain rfl := Option.some.inj destinationEq'
    exact provenance
  · intro item member address destinationEq' bound
    simp only [List.mem_singleton] at member
    subst member
    exact dataCopy bound
  · simp only [List.filter_cons, List.filter_nil, List.length_cons, List.length_nil]
    by_cases lm1 : PreparedParsedMaskedWrite.isLm1Write write = true
    · rw [if_pos lm1]; simp
    · rw [if_neg lm1]; simp

/-- **The multiple-destination branch.** -/
theorem lm1ChunkFacts_multiple (hsm : Bool) (expression : ParsedExpr) (cycle : Fin 4)
    (name : ParsedAluName) (parsedPrecision : ParsedPrecision) (unsigned : Bool)
    (arg : Option (Fin 256))
    (operation : expression.op = .alu name (some parsedPrecision) unsigned arg)
    (nodup : (expression.toIssueExpr 0).writeBanks.Nodup)
    (access : ParsedMaskedIntegerAccesses) (rest : List ParsedMaskedIntegerAccesses)
    (write : PreparedParsedMaskedWrite)
    (lowered : ParsedExpr.toDirectMaskedIntegerWritesInLine? expression
      welcomeZeroFiles.maskRegisters welcomeZeroControl.directive
      hsm welcomeZeroControl.context.group
      welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b
      welcomeZeroControl.context.mab welcomeZeroControl.context.pe cycle
      welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
      welcomeZeroControl.context.tWord = some (access :: rest))
    (prepared : prepareParsedMaskedWriteWithForwarding welcomeZeroFiles welcomeZeroSlots cycle
      access false = .ok write) :
    Lm1ChunkFacts expression cycle (write :: replicatePreparedIntegerResult rest write) := by
  have destinationEq := prepareParsedMaskedWriteWithForwarding_destination welcomeZeroFiles
    welcomeZeroSlots cycle access false write prepared
  have headProvenance := destResolves_of_multiple hsm expression cycle (access :: rest) lowered
    access (by simp)
  have tailProvenance : ∀ item ∈ rest, DestResolves expression cycle item.destination := by
    intro item member
    exact destResolves_of_multiple hsm expression cycle (access :: rest) lowered item
      (List.mem_cons_of_mem _ member)
  obtain ⟨x, readX⟩ := prepareParsedMaskedWriteWithForwarding_readX_ok welcomeZeroFiles
    welcomeZeroSlots cycle access false write prepared
  obtain ⟨sourceX, sourceEq⟩ := toDirectMaskedIntegerWritesInLine?_head_sourceX_eq hsm expression
    name parsedPrecision unsigned arg cycle operation access rest lowered
  have accessOp := toDirectMaskedIntegerWritesInLine?_op hsm expression name parsedPrecision
    unsigned arg cycle operation (access :: rest) lowered access (by simp)
  have copy := welcomeZero_toParsedIntegerInput_read_copy sourceX parsedPrecision.laneWidth
    cycle access.sourceX sourceEq.symm x readX
  have dataCopy := prepareParsedMaskedWriteWithForwarding_data_two_copy name parsedPrecision
    unsigned arg access write cycle false x (accessOp.trans operation) readX copy prepared
  have dataPreserved : ∀ item ∈ replicatePreparedIntegerResult rest write,
      item.data = write.data :=
    replicatePreparedIntegerResult_preserves_data rest write
  refine ⟨?_, ?_, ?_⟩
  · intro item member destinationAccess destinationEq' bank
    rcases List.mem_cons.mp member with same | later
    · subst same
      rw [destinationEq] at destinationEq'
      obtain rfl := Option.some.inj destinationEq'
      exact headProvenance
    · rcases List.mem_map.mp later with ⟨other, otherMem, otherEq⟩
      subst otherEq
      have otherDestination :
          ({ write with destination := some other.destination, selection := other.writeSelection } :
            PreparedParsedMaskedWrite).destination = some other.destination := rfl
      rw [otherDestination] at destinationEq'
      obtain rfl := Option.some.inj destinationEq'
      exact tailProvenance other otherMem
  · intro item member address destinationEq' bound
    rcases List.mem_cons.mp member with same | later
    · subst same
      exact dataCopy bound
    · rw [dataPreserved item later]
      exact dataCopy bound
  · have count := toDirectMaskedIntegerWritesInLine?_lm1_count_le hsm expression name
      parsedPrecision unsigned arg cycle operation nodup (access :: rest) lowered
    have bound := replicatePreparedIntegerResult_lm1_count_le access rest write destinationEq
    omega

/-- **The memory-then-input branch.** -/
theorem lm1ChunkFacts_memoryThenInput (hsm : Bool) (expression : ParsedExpr) (cycle : Fin 4)
    (name : ParsedAluName) (parsedPrecision : ParsedPrecision) (unsigned : Bool)
    (arg : Option (Fin 256))
    (operation : expression.op = .alu name (some parsedPrecision) unsigned arg)
    (accesses : ParsedIntegerMaskMemoryThenInputAccesses)
    (flushSelection : Option PEWordSelection)
    (memoryWrites : List PreparedParsedMaskedWrite) (omrWrite : PreparedParsedMaskedWrite)
    (lowered : parsedIntegerMaskMemoryThenInputExprAccessesInLine? expression
      welcomeZeroFiles.maskRegisters welcomeZeroControl.directive
      hsm welcomeZeroControl.context.group
      welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b
      welcomeZeroControl.context.mab welcomeZeroControl.context.pe cycle
      welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
      welcomeZeroControl.context.tWord = some accesses)
    (prepared : prepareParsedIntegerMaskMemoryThenInputALUWritesWithForwarding
      welcomeZeroFiles welcomeZeroSlots cycle accesses flushSelection false
      = .ok (memoryWrites, omrWrite)) :
    Lm1ChunkFacts expression cycle (memoryWrites ++ [omrWrite]) := by
  have provenance := destResolves_of_memoryThenInput hsm expression cycle name parsedPrecision
    unsigned arg operation accesses lowered
  obtain ⟨sourceX, sourceEq⟩ := parsedIntegerMaskMemoryThenInputExprAccessesInLine?_sourceX_eq hsm
    expression name parsedPrecision unsigned arg cycle operation accesses lowered
  unfold prepareParsedIntegerMaskMemoryThenInputALUWritesWithForwarding at prepared
  cases hx : ParsedIntegerInput.readWithForwarding welcomeZeroFiles welcomeZeroSlots cycle
      accesses.sourceX with
  | failure => simp [hx] at prepared
  | unknown => simp [hx] at prepared
  | ok x =>
      cases hy : ParsedIntegerInput.readWithForwarding welcomeZeroFiles welcomeZeroSlots cycle
          accesses.sourceY with
      | failure => simp [hx, hy] at prepared
      | unknown => simp [hx, hy] at prepared
      | ok y =>
          cases he : evaluateParsedIntegerAlu accesses.op x y false with
          | failure => simp [hx, hy, he] at prepared
          | unknown => simp [hx, hy, he] at prepared
          | ok output =>
              simp only [hx, hy, he, StepResult.ok.injEq, Prod.mk.injEq] at prepared
              obtain ⟨writesEq, producerEq⟩ := prepared
              subst writesEq
              have omrNone : omrWrite.destination = none := by rw [← producerEq]
              have copy := welcomeZero_toParsedIntegerInput_read_copy sourceX
                parsedPrecision.laneWidth cycle accesses.sourceX sourceEq.symm x hx
              obtain ⟨precision, aluOp, integerRequest⟩ := accesses.hasIntegerRequest
              have request := integer_request_is_execution_request accesses.op precision aluOp
                integerRequest
              have dataCopy : ∀ bound : 2 < 4,
                  IsWelcomeCopy ((unpackALUBus (parsedOutputAfterFlush flushSelection
                    output.value)) ⟨2, bound⟩) :=
                data_word_two_isWelcomeCopy_of_bus accesses.op x y output false flushSelection
                  copy precision aluOp request he
              refine ⟨?_, ?_, ?_⟩
              · intro item member access destinationEq bank
                rcases List.mem_append.mp member with earlier | later
                · simp only [List.mem_singleton] at earlier
                  subst item
                  simp only [List.mem_singleton] at destinationEq
                  obtain rfl := Option.some.inj destinationEq
                  exact provenance
                · simp only [List.mem_singleton] at later
                  subst item
                  rw [omrNone] at destinationEq
                  simp at destinationEq
              · intro item member address destinationEq bound
                rcases List.mem_append.mp member with earlier | later
                · simp only [List.mem_singleton] at earlier
                  subst item
                  exact dataCopy bound
                · simp only [List.mem_singleton] at later
                  subst item
                  rw [omrNone] at destinationEq
                  simp at destinationEq
              · have omrFilter : [omrWrite].filter PreparedParsedMaskedWrite.isLm1Write = [] := by
                  rw [List.filter_eq_nil_iff]
                  intro item member
                  simp only [List.mem_singleton] at member
                  subst item
                  simp [PreparedParsedMaskedWrite.isLm1Write, omrNone]
                rw [List.filter_append, omrFilter, List.append_nil]
                rw [List.filter_cons, List.filter_nil]
                split <;> simp

/-- **The input-then-memory branch.** -/
theorem lm1ChunkFacts_inputThenMemory (hsm : Bool) (expression : ParsedExpr) (cycle : Fin 4)
    (name : ParsedAluName) (parsedPrecision : ParsedPrecision) (unsigned : Bool)
    (arg : Option (Fin 256))
    (operation : expression.op = .alu name (some parsedPrecision) unsigned arg)
    (accesses : ParsedIntegerMaskInputThenMemoryAccesses)
    (flushSelection : Option PEWordSelection)
    (memoryWrites : List PreparedParsedMaskedWrite) (omrWrite : PreparedParsedMaskedWrite)
    (lowered : parsedIntegerMaskInputThenMemoryExprAccessesInLine? expression
      welcomeZeroFiles.maskRegisters welcomeZeroControl.directive
      hsm welcomeZeroControl.context.group
      welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b
      welcomeZeroControl.context.mab welcomeZeroControl.context.pe cycle
      welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
      welcomeZeroControl.context.tWord = some accesses)
    (prepared : prepareParsedIntegerMaskInputThenMemoryALUWritesWithForwarding
      welcomeZeroFiles welcomeZeroSlots cycle accesses welcomeZeroControl.directive
      hsm flushSelection false
      = .ok (memoryWrites, omrWrite)) :
    Lm1ChunkFacts expression cycle memoryWrites := by
  obtain ⟨memoryResolution, memoryMember⟩ := destResolves_of_inputThenMemory hsm expression cycle
    name parsedPrecision unsigned arg operation accesses lowered
  have memoryProvenance : DestResolves expression cycle accesses.memory :=
    ⟨accesses.memoryOperand, memoryResolution, memoryMember⟩
  obtain ⟨sourceX, sourceEq⟩ := parsedIntegerMaskInputThenMemoryExprAccessesInLine?_sourceX_eq hsm
    expression name parsedPrecision unsigned arg cycle operation accesses lowered
  unfold prepareParsedIntegerMaskInputThenMemoryALUWritesWithForwarding at prepared
  cases hx : ParsedIntegerInput.readWithForwarding welcomeZeroFiles welcomeZeroSlots cycle
      accesses.sourceX with
  | failure => simp [hx] at prepared
  | unknown => simp [hx] at prepared
  | ok x =>
      cases hy : ParsedIntegerInput.readWithForwarding welcomeZeroFiles welcomeZeroSlots cycle
          accesses.sourceY with
      | failure => simp [hx, hy] at prepared
      | unknown => simp [hx, hy] at prepared
      | ok y =>
          cases he : evaluateParsedIntegerAlu accesses.op x y false with
          | failure => simp [hx, hy, he] at prepared
          | unknown => simp [hx, hy, he] at prepared
          | ok output =>
              cases hm : ParsedOperand.resolveMemoryWriteSelection? accesses.memoryOperand
                  accesses.memory.bank
                  (ProofsLean.MNCore.Masks.writeRegister welcomeZeroFiles.maskRegisters
                    accesses.destination cycle
                    (BitVec.ofBoolListLE
                      [output.flags 0, output.flags 1, output.flags 2, output.flags 3])
                    accesses.omrSelection)
                  cycle welcomeZeroControl.directive
                  hsm with
              | none => simp [hx, hy, he, hm] at prepared
              | some memorySelection =>
                  simp only [hx, hy, he, hm, StepResult.ok.injEq, Prod.mk.injEq] at prepared
                  obtain ⟨writesEq, producerEq⟩ := prepared
                  subst writesEq
                  have omrNone : omrWrite.destination = none := by rw [← producerEq]
                  have copy := welcomeZero_toParsedIntegerInput_read_copy sourceX
                    parsedPrecision.laneWidth cycle accesses.sourceX sourceEq.symm x hx
                  obtain ⟨precision, aluOp, integerRequest⟩ := accesses.hasIntegerRequest
                  have request := integer_request_is_execution_request accesses.op precision aluOp
                    integerRequest
                  have dataCopy : ∀ bound : 2 < 4,
                      IsWelcomeCopy ((unpackALUBus (parsedOutputAfterFlush flushSelection
                        output.value)) ⟨2, bound⟩) :=
                    data_word_two_isWelcomeCopy_of_bus accesses.op x y output false flushSelection
                      copy precision aluOp request he
                  refine ⟨?_, ?_, ?_⟩
                  · intro item member access destinationEq bank
                    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false]
                      at member
                    rcases member with same | same
                    · subst item
                      simp at destinationEq
                    · subst item
                      obtain rfl := Option.some.inj destinationEq
                      exact memoryProvenance
                  · intro item member address destinationEq bound
                    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false]
                      at member
                    rcases member with same | same
                    · subst item
                      simp at destinationEq
                    · subst item
                      exact dataCopy bound
                  · rw [List.filter_cons, List.filter_cons, List.filter_nil]
                    simp only [PreparedParsedMaskedWrite.isLm1Write]
                    by_cases h : accesses.memory.bank = PEMemory.Bank.lm1 <;> simp [h]

/-- The destination provenance and count facts shared by the two constant
branches. -/
theorem lm1ChunkFacts_constant_provenance_and_count (hsm : Bool)
    (expression : ParsedExpr) (cycle : Fin 4)
    (targets : List ParsedConstantDestination) (destinationWrites : List PreparedParsedMaskedWrite)
    (producerWrite : PreparedParsedMaskedWrite)
    (lowered : ParsedExpr.toDirectMaskedConstantWrites? expression
      welcomeZeroFiles.maskRegisters welcomeZeroControl.directive
      hsm welcomeZeroControl.context.group
      welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b
      welcomeZeroControl.context.mab welcomeZeroControl.context.pe cycle
      welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
      welcomeZeroControl.context.tWord = some targets)
    (prepared : prepareParsedMaskedConstantWrites welcomeZeroFiles cycle targets
      = .ok destinationWrites)
    (nodup : (expression.toIssueExpr 0).writeBanks.Nodup)
    (producerNone : producerWrite.destination = none)
    (destinationsLowered : ParsedExpr.toDirectMaskedConstantDestinations? expression
      welcomeZeroFiles.maskRegisters welcomeZeroControl.directive
      hsm welcomeZeroControl.context.group
      welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b
      welcomeZeroControl.context.mab welcomeZeroControl.context.pe cycle
      welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
      welcomeZeroControl.context.tWord expression.destinations = some targets) :
    (∀ write ∈ destinationWrites ++ [producerWrite], ∀ access : DirectMemoryAccess,
        write.destination = some access → access.bank = PEMemory.Bank.lm1 →
        DestResolves expression cycle access) ∧
      ((destinationWrites ++ [producerWrite]).filter
        PreparedParsedMaskedWrite.isLm1Write).length ≤ 1 := by
  have targetProvenance := destResolves_of_constantTargets hsm expression cycle targets lowered
  have destinations := prepareParsedMaskedConstantWrites_destinations welcomeZeroFiles cycle
    targets destinationWrites prepared
  refine ⟨?_, ?_⟩
  · intro write member access destinationEq bank
    rcases List.mem_append.mp member with earlier | later
    · rcases destinations write earlier with isNone | ⟨target, targetMem, accesses, isMemory,
        writeDestination⟩
      · rw [isNone] at destinationEq
        simp at destinationEq
      · rw [writeDestination] at destinationEq
        obtain rfl := Option.some.inj destinationEq
        exact targetProvenance target targetMem accesses isMemory
    · simp only [List.mem_singleton] at later
      subst later
      rw [producerNone] at destinationEq
      simp at destinationEq
  · have producerFilter : [producerWrite].filter
        PreparedParsedMaskedWrite.isLm1Write = [] := by
      rw [List.filter_eq_nil_iff]
      intro item member
      simp only [List.mem_singleton] at member
      subst item
      simp [PreparedParsedMaskedWrite.isLm1Write, producerNone]
    have count := prepareParsedMaskedConstantWrites_lm1_count_le cycle targets destinationWrites
      prepared
    have targetBound := constantTargets_lm1_count_le expression welcomeZeroFiles.maskRegisters
      welcomeZeroControl.directive hsm
      welcomeZeroControl.context.group welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b
      welcomeZeroControl.context.mab welcomeZeroControl.context.pe cycle welcomeZeroControl.context.bar0
      welcomeZeroControl.context.bar1 welcomeZeroControl.context.tWord expression.destinations targets
      destinationsLowered
    have targetBound' : (targets.filter ParsedConstantDestination.isLm1Target).length ≤
        (expression.destinations.filter ParsedOperand.isLm1MemoryDestination).length :=
      targetBound
    have one := lm1Destinations_count_le_one expression 0 nodup
    rw [List.filter_append, producerFilter, List.append_nil]
    omega

/-- **The `.zero` constant branch.** -/
theorem lm1ChunkFacts_zero (hsm : Bool) (expression : ParsedExpr) (cycle : Fin 4)
    (targets : List ParsedConstantDestination) (destinationWrites : List PreparedParsedMaskedWrite)
    (producerWrite : PreparedParsedMaskedWrite)
    (isZero : expression.op = .zero)
    (lowered : ParsedExpr.toDirectMaskedConstantWrites? expression
      welcomeZeroFiles.maskRegisters welcomeZeroControl.directive
      hsm welcomeZeroControl.context.group
      welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b
      welcomeZeroControl.context.mab welcomeZeroControl.context.pe cycle
      welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
      welcomeZeroControl.context.tWord = some targets)
    (prepared : prepareParsedMaskedConstantWrites welcomeZeroFiles cycle targets
      = .ok destinationWrites)
    (nodup : (expression.toIssueExpr 0).writeBanks.Nodup)
    (producerNone : producerWrite.destination = none) :
    Lm1ChunkFacts expression cycle (destinationWrites ++ [producerWrite]) := by
  have destinationsLowered : ParsedExpr.toDirectMaskedConstantDestinations? expression
      welcomeZeroFiles.maskRegisters welcomeZeroControl.directive
      hsm welcomeZeroControl.context.group
      welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b
      welcomeZeroControl.context.mab welcomeZeroControl.context.pe cycle
      welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
      welcomeZeroControl.context.tWord expression.destinations = some targets := by
    unfold ParsedExpr.toDirectMaskedConstantWrites? at lowered
    rw [isZero] at lowered
    simpa using lowered
  obtain ⟨provenance, count⟩ := lm1ChunkFacts_constant_provenance_and_count hsm expression cycle
    targets destinationWrites producerWrite lowered prepared nodup producerNone destinationsLowered
  have mem := prepareParsedMaskedConstantWrites_mem cycle targets destinationWrites prepared
  refine ⟨provenance, ?_, count⟩
  intro write member address destinationEq bound
  rcases List.mem_append.mp member with earlier | later
  · obtain ⟨target, targetMem, targetPrepared⟩ := mem write earlier
    cases target with
    | memory accesses' =>
        have preparedWrite : prepareParsedMaskedWrite welcomeZeroFiles accesses' false
            = .ok write := by
          simpa [prepareParsedConstantTarget] using targetPrepared
        obtain ⟨destination, destinationMem, loweredDestination⟩ :=
          toDirectMaskedConstantWrites?_mem_provenance expression welcomeZeroFiles.maskRegisters
            welcomeZeroControl.directive hsm
            welcomeZeroControl.context.group welcomeZeroControl.context.l2b
            welcomeZeroControl.context.l1b welcomeZeroControl.context.mab
            welcomeZeroControl.context.pe cycle welcomeZeroControl.context.bar0
            welcomeZeroControl.context.bar1 welcomeZeroControl.context.tWord targets lowered
            (.memory accesses') targetMem
        have opZero : accesses'.op = .zero := by
          rw [toDirectMaskedConstantDestination?_memory_op expression welcomeZeroFiles.maskRegisters
            welcomeZeroControl.directive hsm
            welcomeZeroControl.context.group welcomeZeroControl.context.l2b
            welcomeZeroControl.context.l1b welcomeZeroControl.context.mab
            welcomeZeroControl.context.pe cycle welcomeZeroControl.context.bar0
            welcomeZeroControl.context.bar1 welcomeZeroControl.context.tWord destination accesses'
            loweredDestination, isZero]
        exact prepareParsedMaskedWrite_zero_data_two_copy accesses' write opZero preparedWrite bound
    | maskRegister entry =>
        simp only [prepareParsedConstantTarget, StepResult.ok.injEq] at targetPrepared
        rw [← targetPrepared] at destinationEq
        simp at destinationEq
    | noWrite =>
        simp only [prepareParsedConstantTarget, StepResult.ok.injEq] at targetPrepared
        rw [← targetPrepared] at destinationEq
        simp at destinationEq
  · simp only [List.mem_singleton] at later
    subst later
    rw [producerNone] at destinationEq
    simp at destinationEq

/-- **The `.immediate` constant branch.**  Here the `LM1 .double` case cannot
arise, because the escaping immediate-double configuration is excluded. -/
theorem lm1ChunkFacts_immediate (hsm : Bool) (expression : ParsedExpr) (cycle : Fin 4)
    (targets : List ParsedConstantDestination) (destinationWrites : List PreparedParsedMaskedWrite)
    (producerWrite : PreparedParsedMaskedWrite)
    (payload : BitVec 32) (sparse : Bool)
    (isImmediate : expression.op = .immediate payload sparse)
    (lowered : ParsedExpr.toDirectMaskedConstantWrites? expression
      welcomeZeroFiles.maskRegisters welcomeZeroControl.directive
      hsm welcomeZeroControl.context.group
      welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b
      welcomeZeroControl.context.mab welcomeZeroControl.context.pe cycle
      welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
      welcomeZeroControl.context.tWord = some targets)
    (prepared : prepareParsedMaskedConstantWrites welcomeZeroFiles cycle targets
      = .ok destinationWrites)
    (nodup : (expression.toIssueExpr 0).writeBanks.Nodup)
    (producerNone : producerWrite.destination = none)
    (notDouble : ∀ d ∈ expression.destinations,
      ParsedOperand.directDestinationBankWidth? d ≠
        some (PEMemory.Bank.lm1, PEMemory.Width.double)) :
    Lm1ChunkFacts expression cycle (destinationWrites ++ [producerWrite]) := by
  have destinationsLowered : ParsedExpr.toDirectMaskedConstantDestinations? expression
      welcomeZeroFiles.maskRegisters welcomeZeroControl.directive
      hsm welcomeZeroControl.context.group
      welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b
      welcomeZeroControl.context.mab welcomeZeroControl.context.pe cycle
      welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
      welcomeZeroControl.context.tWord expression.destinations = some targets := by
    unfold ParsedExpr.toDirectMaskedConstantWrites? at lowered
    rw [isImmediate] at lowered
    simpa using lowered
  obtain ⟨provenance, count⟩ := lm1ChunkFacts_constant_provenance_and_count hsm expression cycle
    targets destinationWrites producerWrite lowered prepared nodup producerNone destinationsLowered
  have mem := prepareParsedMaskedConstantWrites_mem cycle targets destinationWrites prepared
  refine ⟨provenance, ?_, count⟩
  intro write member address destinationEq bound
  rcases List.mem_append.mp member with earlier | later
  · obtain ⟨target, targetMem, targetPrepared⟩ := mem write earlier
    cases target with
    | memory accesses' =>
        have preparedWrite : prepareParsedMaskedWrite welcomeZeroFiles accesses' false
            = .ok write := by
          simpa [prepareParsedConstantTarget] using targetPrepared
        have preparedDestination : write.destination = some accesses'.destination :=
          prepareParsedMaskedWrite_destination welcomeZeroFiles accesses' false write preparedWrite
        have accessesDestination : accesses'.destination =
            ⟨PEMemory.Bank.lm1, PEMemory.Width.double, address⟩ := by
          rw [preparedDestination] at destinationEq
          exact Option.some.inj destinationEq
        obtain ⟨destination, destinationMem, loweredDestination⟩ :=
          toDirectMaskedConstantWrites?_mem_provenance expression welcomeZeroFiles.maskRegisters
            welcomeZeroControl.directive hsm
            welcomeZeroControl.context.group welcomeZeroControl.context.l2b
            welcomeZeroControl.context.l1b welcomeZeroControl.context.mab
            welcomeZeroControl.context.pe cycle welcomeZeroControl.context.bar0
            welcomeZeroControl.context.bar1 welcomeZeroControl.context.tWord targets lowered
            (.memory accesses') targetMem
        obtain ⟨resolved, resolvedMem, resolvedEq⟩ :=
          toDirectMaskedConstantDestination_memory_provenance expression
            welcomeZeroFiles.maskRegisters welcomeZeroControl.directive
            hsm welcomeZeroControl.context.group
            welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b
            welcomeZeroControl.context.mab welcomeZeroControl.context.pe cycle
            welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
            welcomeZeroControl.context.tWord destination accesses' loweredDestination
        simp only [List.mem_singleton] at resolvedMem
        rw [resolvedMem] at resolvedEq
        have static := ParsedOperand.toDirectMemoryDestination?_bankWidth destination
          welcomeZeroControl.context.pe cycle welcomeZeroControl.context.bar0
          welcomeZeroControl.context.bar1 welcomeZeroControl.context.tWord
        rw [resolvedEq] at static
        simp only [Option.map_some] at static
        have pair : ParsedOperand.directDestinationBankWidth? destination =
            some (PEMemory.Bank.lm1, PEMemory.Width.double) := by
          rw [← static, accessesDestination]
        exact absurd pair (notDouble destination destinationMem)
    | maskRegister entry =>
        simp only [prepareParsedConstantTarget, StepResult.ok.injEq] at targetPrepared
        rw [← targetPrepared] at destinationEq
        simp at destinationEq
    | noWrite =>
        simp only [prepareParsedConstantTarget, StepResult.ok.injEq] at targetPrepared
        rw [← targetPrepared] at destinationEq
        simp at destinationEq
  · simp only [List.mem_singleton] at later
    subst later
    rw [producerNone] at destinationEq
    simp at destinationEq




/-! ## 8. Branch inversions of the cycle preparation

Each branch lemma takes the exact lowering that fired and the successful cycle
preparation, extracts the returned write list, and hands over to the per-branch
shape facts of section 7. -/

/-- The direct-access branch. -/
theorem chunkFacts_of_direct (hsm : Bool)
    (expression : ParsedExpr) (name : ParsedAluName) (parsedPrecision : ParsedPrecision)
    (unsigned : Bool) (arg : Option (Fin 256)) (sources destinations : List ParsedOperand)
    (flush : Option ParsedMask) (text : String) (noForward : Bool) (cycle : Fin 4)
    (nextSlots : ProofsLean.MNCore.Forwarding.Slots)
    (accesses : ParsedMaskedIntegerAccesses) (writes : List PreparedParsedMaskedWrite)
    (slots : ProofsLean.MNCore.Forwarding.Slots)
    (components : expression =
      ⟨.alu name (some parsedPrecision) unsigned arg, sources, destinations, flush, text⟩)
    (lowered : ParsedExpr.toDirectMaskedIntegerAccessesInLine? expression
      welcomeZeroFiles.maskRegisters welcomeZeroControl.directive
      hsm welcomeZeroControl.context.group
      welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b
      welcomeZeroControl.context.mab welcomeZeroControl.context.pe cycle
      welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
      welcomeZeroControl.context.tWord = some accesses)
    (prep : prepareParsedIntegerALUExprCycle welcomeZeroFiles welcomeZeroSlots nextSlots expression
      welcomeZeroControl hsm noForward false cycle
      = .ok (writes, slots)) :
    Lm1ChunkFacts expression cycle writes := by
  rw [components] at *
  unfold prepareParsedIntegerALUExprCycle at prep
  dsimp only at prep
  rw [lowered] at prep
  dsimp only at prep
  split at prep
  · simp at prep
  · simp at prep
  · rename_i write preparedWrite
    split at prep
    · simp at prep
    · simp at prep
    · rename_i slots' updated
      simp only [StepResult.ok.injEq, Prod.mk.injEq] at prep
      obtain ⟨writesEq, _⟩ := prep
      subst writesEq
      exact lm1ChunkFacts_direct hsm _ cycle name parsedPrecision unsigned arg rfl accesses write
        lowered preparedWrite

/-- The multiple-destination branch. -/
theorem chunkFacts_of_multiple (hsm : Bool)
    (expression : ParsedExpr) (name : ParsedAluName) (parsedPrecision : ParsedPrecision)
    (unsigned : Bool) (arg : Option (Fin 256)) (sources destinations : List ParsedOperand)
    (flush : Option ParsedMask) (text : String) (noForward : Bool) (cycle : Fin 4)
    (nextSlots : ProofsLean.MNCore.Forwarding.Slots)
    (access : ParsedMaskedIntegerAccesses) (rest : List ParsedMaskedIntegerAccesses)
    (writes : List PreparedParsedMaskedWrite)
    (slots : ProofsLean.MNCore.Forwarding.Slots)
    (components : expression =
      ⟨.alu name (some parsedPrecision) unsigned arg, sources, destinations, flush, text⟩)
    (directFailed : ParsedExpr.toDirectMaskedIntegerAccessesInLine? expression
      welcomeZeroFiles.maskRegisters welcomeZeroControl.directive
      hsm welcomeZeroControl.context.group
      welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b
      welcomeZeroControl.context.mab welcomeZeroControl.context.pe cycle
      welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
      welcomeZeroControl.context.tWord = none)
    (nodup : (expression.toIssueExpr 0).writeBanks.Nodup)
    (lowered : ParsedExpr.toDirectMaskedIntegerWritesInLine? expression
      welcomeZeroFiles.maskRegisters welcomeZeroControl.directive
      hsm welcomeZeroControl.context.group
      welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b
      welcomeZeroControl.context.mab welcomeZeroControl.context.pe cycle
      welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
      welcomeZeroControl.context.tWord = some (access :: rest))
    (prep : prepareParsedIntegerALUExprCycle welcomeZeroFiles welcomeZeroSlots nextSlots expression
      welcomeZeroControl hsm noForward false cycle
      = .ok (writes, slots)) :
    Lm1ChunkFacts expression cycle writes := by
  rw [components] at *
  unfold prepareParsedIntegerALUExprCycle at prep
  dsimp only at prep
  rw [directFailed, lowered] at prep
  dsimp only at prep
  split at prep
  · simp at prep
  · simp at prep
  · rename_i write preparedWrite
    split at prep
    · simp at prep
    · simp at prep
    · rename_i slots' updated
      simp only [StepResult.ok.injEq, Prod.mk.injEq] at prep
      obtain ⟨writesEq, _⟩ := prep
      subst writesEq
      exact lm1ChunkFacts_multiple hsm _ cycle name parsedPrecision unsigned arg rfl nodup access rest
        write lowered preparedWrite

/-- The OMR-mask branch. -/
theorem chunkFacts_of_omr (hsm : Bool)
    (expression : ParsedExpr) (name : ParsedAluName) (parsedPrecision : ParsedPrecision)
    (unsigned : Bool) (arg : Option (Fin 256)) (sources destinations : List ParsedOperand)
    (flush : Option ParsedMask) (text : String) (noForward : Bool) (cycle : Fin 4)
    (nextSlots : ProofsLean.MNCore.Forwarding.Slots)
    (accesses : ParsedIntegerMaskAccesses) (flushSelection : Option PEWordSelection)
    (writes : List PreparedParsedMaskedWrite)
    (slots : ProofsLean.MNCore.Forwarding.Slots)
    (components : expression =
      ⟨.alu name (some parsedPrecision) unsigned arg, sources, destinations, flush, text⟩)
    (directFailed : ParsedExpr.toDirectMaskedIntegerAccessesInLine? expression
      welcomeZeroFiles.maskRegisters welcomeZeroControl.directive
      hsm welcomeZeroControl.context.group
      welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b
      welcomeZeroControl.context.mab welcomeZeroControl.context.pe cycle
      welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
      welcomeZeroControl.context.tWord = none)
    (multipleFailed : ParsedExpr.toDirectMaskedIntegerWritesInLine? expression
      welcomeZeroFiles.maskRegisters welcomeZeroControl.directive
      hsm welcomeZeroControl.context.group
      welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b
      welcomeZeroControl.context.mab welcomeZeroControl.context.pe cycle
      welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
      welcomeZeroControl.context.tWord = none)
    (lowered : parsedIntegerMaskExprAccessesInLine? expression welcomeZeroFiles.maskRegisters
      welcomeZeroControl.directive hsm
      welcomeZeroControl.context.pe cycle welcomeZeroControl.context.bar0
      welcomeZeroControl.context.bar1 welcomeZeroControl.context.tWord = some accesses)
    (flushResolved : resolveFlushSelection? flush welcomeZeroFiles.maskRegisters cycle =
      some flushSelection)
    (prep : prepareParsedIntegerALUExprCycle welcomeZeroFiles welcomeZeroSlots nextSlots expression
      welcomeZeroControl hsm noForward false cycle
      = .ok (writes, slots)) :
    Lm1ChunkFacts expression cycle writes := by
  rw [components] at *
  unfold prepareParsedIntegerALUExprCycle at prep
  dsimp only at prep
  rw [directFailed, multipleFailed, lowered, flushResolved] at prep
  dsimp only at prep
  split at prep
  · simp at prep
  · simp at prep
  · rename_i write preparedWrite
    split at prep
    · simp at prep
    · simp at prep
    · rename_i slots' updated
      simp only [StepResult.ok.injEq, Prod.mk.injEq] at prep
      obtain ⟨writesEq, _⟩ := prep
      subst writesEq
      exact lm1ChunkFacts_singleton_none _ cycle write
        (prepareParsedIntegerMaskALUWriteWithForwarding_destination_none welcomeZeroFiles
          welcomeZeroSlots cycle accesses flushSelection false write preparedWrite)

/-- The no-write branch. -/
theorem chunkFacts_of_noWrite (hsm : Bool)
    (expression : ParsedExpr) (name : ParsedAluName) (parsedPrecision : ParsedPrecision)
    (unsigned : Bool) (arg : Option (Fin 256)) (sources destinations : List ParsedOperand)
    (flush : Option ParsedMask) (text : String) (noForward : Bool) (cycle : Fin 4)
    (nextSlots : ProofsLean.MNCore.Forwarding.Slots)
    (accesses : ParsedIntegerNoWriteAccesses)
    (writes : List PreparedParsedMaskedWrite)
    (slots : ProofsLean.MNCore.Forwarding.Slots)
    (components : expression =
      ⟨.alu name (some parsedPrecision) unsigned arg, sources, destinations, flush, text⟩)
    (directFailed : ParsedExpr.toDirectMaskedIntegerAccessesInLine? expression
      welcomeZeroFiles.maskRegisters welcomeZeroControl.directive
      hsm welcomeZeroControl.context.group
      welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b
      welcomeZeroControl.context.mab welcomeZeroControl.context.pe cycle
      welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
      welcomeZeroControl.context.tWord = none)
    (multipleFailed : ParsedExpr.toDirectMaskedIntegerWritesInLine? expression
      welcomeZeroFiles.maskRegisters welcomeZeroControl.directive
      hsm welcomeZeroControl.context.group
      welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b
      welcomeZeroControl.context.mab welcomeZeroControl.context.pe cycle
      welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
      welcomeZeroControl.context.tWord = none)
    (omrFailed : parsedIntegerMaskExprAccessesInLine? expression welcomeZeroFiles.maskRegisters
      welcomeZeroControl.directive hsm
      welcomeZeroControl.context.pe cycle welcomeZeroControl.context.bar0
      welcomeZeroControl.context.bar1 welcomeZeroControl.context.tWord = none)
    (lowered : parsedIntegerNoWriteExprAccessesInLine? expression welcomeZeroFiles.maskRegisters
      welcomeZeroControl.context.pe cycle welcomeZeroControl.context.group
      welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b
      welcomeZeroControl.context.mab welcomeZeroControl.context.bar0
      welcomeZeroControl.context.bar1 welcomeZeroControl.context.tWord = some accesses)
    (prep : prepareParsedIntegerALUExprCycle welcomeZeroFiles welcomeZeroSlots nextSlots expression
      welcomeZeroControl hsm noForward false cycle
      = .ok (writes, slots)) :
    Lm1ChunkFacts expression cycle writes := by
  rw [components] at *
  unfold prepareParsedIntegerALUExprCycle at prep
  dsimp only at prep
  rw [directFailed, multipleFailed, omrFailed, lowered] at prep
  dsimp only at prep
  split at prep
  · simp at prep
  · simp at prep
  · rename_i write preparedWrite
    split at prep
    · simp at prep
    · simp at prep
    · rename_i slots' updated
      simp only [StepResult.ok.injEq, Prod.mk.injEq] at prep
      obtain ⟨writesEq, _⟩ := prep
      subst writesEq
      exact lm1ChunkFacts_singleton_none _ cycle write
        (prepareParsedIntegerNoWriteALUWithForwarding_destination_none welcomeZeroFiles
          welcomeZeroSlots cycle accesses false write preparedWrite)

/-- The BAR branch. -/
theorem chunkFacts_of_bar (hsm : Bool)
    (expression : ParsedExpr) (name : ParsedAluName) (parsedPrecision : ParsedPrecision)
    (unsigned : Bool) (arg : Option (Fin 256)) (sources destinations : List ParsedOperand)
    (flush : Option ParsedMask) (text : String) (noForward : Bool) (cycle : Fin 4)
    (nextSlots : ProofsLean.MNCore.Forwarding.Slots)
    (accesses : ParsedIntegerBarAccesses)
    (writes : List PreparedParsedMaskedWrite)
    (slots : ProofsLean.MNCore.Forwarding.Slots)
    (components : expression =
      ⟨.alu name (some parsedPrecision) unsigned arg, sources, destinations, flush, text⟩)
    (directFailed : ParsedExpr.toDirectMaskedIntegerAccessesInLine? expression
      welcomeZeroFiles.maskRegisters welcomeZeroControl.directive
      hsm welcomeZeroControl.context.group
      welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b
      welcomeZeroControl.context.mab welcomeZeroControl.context.pe cycle
      welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
      welcomeZeroControl.context.tWord = none)
    (multipleFailed : ParsedExpr.toDirectMaskedIntegerWritesInLine? expression
      welcomeZeroFiles.maskRegisters welcomeZeroControl.directive
      hsm welcomeZeroControl.context.group
      welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b
      welcomeZeroControl.context.mab welcomeZeroControl.context.pe cycle
      welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
      welcomeZeroControl.context.tWord = none)
    (omrFailed : parsedIntegerMaskExprAccessesInLine? expression welcomeZeroFiles.maskRegisters
      welcomeZeroControl.directive hsm
      welcomeZeroControl.context.pe cycle welcomeZeroControl.context.bar0
      welcomeZeroControl.context.bar1 welcomeZeroControl.context.tWord = none)
    (noWriteFailed : parsedIntegerNoWriteExprAccessesInLine? expression
      welcomeZeroFiles.maskRegisters welcomeZeroControl.context.pe cycle
      welcomeZeroControl.context.group welcomeZeroControl.context.l2b
      welcomeZeroControl.context.l1b welcomeZeroControl.context.mab
      welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
      welcomeZeroControl.context.tWord = none)
    (lowered : parsedIntegerBarExprAccessesInLine? expression welcomeZeroFiles.maskRegisters
      welcomeZeroControl.directive hsm
      welcomeZeroControl.context.group welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b
      welcomeZeroControl.context.mab welcomeZeroControl.context.pe cycle
      welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
      welcomeZeroControl.context.tWord = some accesses)
    (prep : prepareParsedIntegerALUExprCycle welcomeZeroFiles welcomeZeroSlots nextSlots expression
      welcomeZeroControl hsm noForward false cycle
      = .ok (writes, slots)) :
    Lm1ChunkFacts expression cycle writes := by
  rw [components] at *
  unfold prepareParsedIntegerALUExprCycle at prep
  dsimp only at prep
  rw [directFailed, multipleFailed, omrFailed, noWriteFailed, lowered] at prep
  dsimp only at prep
  split at prep
  · simp at prep
  · simp at prep
  · rename_i write preparedWrite
    split at prep
    · simp at prep
    · simp at prep
    · rename_i slots' updated
      simp only [StepResult.ok.injEq, Prod.mk.injEq] at prep
      obtain ⟨writesEq, _⟩ := prep
      subst writesEq
      exact lm1ChunkFacts_singleton_none _ cycle write
        (prepareParsedIntegerBarALUWithForwarding_destination_none welcomeZeroFiles welcomeZeroSlots cycle accesses false write
          preparedWrite)

/-- The mask-input branch. -/
theorem chunkFacts_of_maskInput (hsm : Bool)
    (expression : ParsedExpr) (name : ParsedAluName) (parsedPrecision : ParsedPrecision)
    (unsigned : Bool) (arg : Option (Fin 256)) (sources destinations : List ParsedOperand)
    (flush : Option ParsedMask) (text : String) (noForward : Bool) (cycle : Fin 4)
    (nextSlots : ProofsLean.MNCore.Forwarding.Slots)
    (accesses : ParsedIntegerMaskInputAccesses) (flushSelection : Option PEWordSelection)
    (writes : List PreparedParsedMaskedWrite)
    (slots : ProofsLean.MNCore.Forwarding.Slots)
    (components : expression =
      ⟨.alu name (some parsedPrecision) unsigned arg, sources, destinations, flush, text⟩)
    (directFailed : ParsedExpr.toDirectMaskedIntegerAccessesInLine? expression
      welcomeZeroFiles.maskRegisters welcomeZeroControl.directive
      hsm welcomeZeroControl.context.group
      welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b
      welcomeZeroControl.context.mab welcomeZeroControl.context.pe cycle
      welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
      welcomeZeroControl.context.tWord = none)
    (multipleFailed : ParsedExpr.toDirectMaskedIntegerWritesInLine? expression
      welcomeZeroFiles.maskRegisters welcomeZeroControl.directive
      hsm welcomeZeroControl.context.group
      welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b
      welcomeZeroControl.context.mab welcomeZeroControl.context.pe cycle
      welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
      welcomeZeroControl.context.tWord = none)
    (omrFailed : parsedIntegerMaskExprAccessesInLine? expression welcomeZeroFiles.maskRegisters
      welcomeZeroControl.directive hsm
      welcomeZeroControl.context.pe cycle welcomeZeroControl.context.bar0
      welcomeZeroControl.context.bar1 welcomeZeroControl.context.tWord = none)
    (noWriteFailed : parsedIntegerNoWriteExprAccessesInLine? expression
      welcomeZeroFiles.maskRegisters welcomeZeroControl.context.pe cycle
      welcomeZeroControl.context.group welcomeZeroControl.context.l2b
      welcomeZeroControl.context.l1b welcomeZeroControl.context.mab
      welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
      welcomeZeroControl.context.tWord = none)
    (barFailed : parsedIntegerBarExprAccessesInLine? expression
      welcomeZeroFiles.maskRegisters welcomeZeroControl.directive
      hsm welcomeZeroControl.context.group
      welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b
      welcomeZeroControl.context.mab welcomeZeroControl.context.pe cycle
      welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
      welcomeZeroControl.context.tWord = none)
    (flushResolved : resolveFlushSelection? flush welcomeZeroFiles.maskRegisters cycle =
      some flushSelection)
    (lowered : parsedIntegerMaskInputExprAccessesInLine? expression welcomeZeroFiles.maskRegisters
      welcomeZeroControl.directive hsm
      welcomeZeroControl.context.group welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b
      welcomeZeroControl.context.mab welcomeZeroControl.context.pe cycle
      welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
      welcomeZeroControl.context.tWord = some accesses)
    (prep : prepareParsedIntegerALUExprCycle welcomeZeroFiles welcomeZeroSlots nextSlots expression
      welcomeZeroControl hsm noForward false cycle
      = .ok (writes, slots)) :
    Lm1ChunkFacts expression cycle writes := by
  rw [components] at *
  unfold prepareParsedIntegerALUExprCycle at prep
  dsimp only at prep
  rw [directFailed, multipleFailed, omrFailed, noWriteFailed, barFailed, lowered, flushResolved]
    at prep
  dsimp only at prep
  split at prep
  · simp at prep
  · simp at prep
  · rename_i write preparedWrite
    split at prep
    · simp at prep
    · simp at prep
    · rename_i slots' updated
      simp only [StepResult.ok.injEq, Prod.mk.injEq] at prep
      obtain ⟨writesEq, _⟩ := prep
      subst writesEq
      exact lm1ChunkFacts_singleton_none _ cycle write
        (prepareParsedIntegerMaskInputALUWriteWithForwarding_destination_none welcomeZeroFiles
          welcomeZeroSlots cycle accesses flushSelection false write preparedWrite)

/-- The memory-then-input branch. -/
theorem chunkFacts_of_memoryThenInput (hsm : Bool)
    (expression : ParsedExpr) (name : ParsedAluName) (parsedPrecision : ParsedPrecision)
    (unsigned : Bool) (arg : Option (Fin 256)) (sources destinations : List ParsedOperand)
    (flush : Option ParsedMask) (text : String) (noForward : Bool) (cycle : Fin 4)
    (nextSlots : ProofsLean.MNCore.Forwarding.Slots)
    (accesses : ParsedIntegerMaskMemoryThenInputAccesses)
    (flushSelection : Option PEWordSelection)
    (writes : List PreparedParsedMaskedWrite)
    (slots : ProofsLean.MNCore.Forwarding.Slots)
    (components : expression =
      ⟨.alu name (some parsedPrecision) unsigned arg, sources, destinations, flush, text⟩)
    (directFailed : ParsedExpr.toDirectMaskedIntegerAccessesInLine? expression
      welcomeZeroFiles.maskRegisters welcomeZeroControl.directive
      hsm welcomeZeroControl.context.group
      welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b
      welcomeZeroControl.context.mab welcomeZeroControl.context.pe cycle
      welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
      welcomeZeroControl.context.tWord = none)
    (multipleFailed : ParsedExpr.toDirectMaskedIntegerWritesInLine? expression
      welcomeZeroFiles.maskRegisters welcomeZeroControl.directive
      hsm welcomeZeroControl.context.group
      welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b
      welcomeZeroControl.context.mab welcomeZeroControl.context.pe cycle
      welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
      welcomeZeroControl.context.tWord = none)
    (omrFailed : parsedIntegerMaskExprAccessesInLine? expression welcomeZeroFiles.maskRegisters
      welcomeZeroControl.directive hsm
      welcomeZeroControl.context.pe cycle welcomeZeroControl.context.bar0
      welcomeZeroControl.context.bar1 welcomeZeroControl.context.tWord = none)
    (noWriteFailed : parsedIntegerNoWriteExprAccessesInLine? expression
      welcomeZeroFiles.maskRegisters welcomeZeroControl.context.pe cycle
      welcomeZeroControl.context.group welcomeZeroControl.context.l2b
      welcomeZeroControl.context.l1b welcomeZeroControl.context.mab
      welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
      welcomeZeroControl.context.tWord = none)
    (barFailed : parsedIntegerBarExprAccessesInLine? expression
      welcomeZeroFiles.maskRegisters welcomeZeroControl.directive
      hsm welcomeZeroControl.context.group
      welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b
      welcomeZeroControl.context.mab welcomeZeroControl.context.pe cycle
      welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
      welcomeZeroControl.context.tWord = none)
    (inputFailed : parsedIntegerMaskInputExprAccessesInLine? expression
      welcomeZeroFiles.maskRegisters welcomeZeroControl.directive
      hsm welcomeZeroControl.context.group
      welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b
      welcomeZeroControl.context.mab welcomeZeroControl.context.pe cycle
      welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
      welcomeZeroControl.context.tWord = none)
    (lowered : parsedIntegerMaskMemoryThenInputExprAccessesInLine? expression
      welcomeZeroFiles.maskRegisters welcomeZeroControl.directive
      hsm welcomeZeroControl.context.group
      welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b
      welcomeZeroControl.context.mab welcomeZeroControl.context.pe cycle
      welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
      welcomeZeroControl.context.tWord = some accesses)
    (flushResolved : resolveFlushSelection? flush welcomeZeroFiles.maskRegisters cycle =
      some flushSelection)
    (prep : prepareParsedIntegerALUExprCycle welcomeZeroFiles welcomeZeroSlots nextSlots expression
      welcomeZeroControl hsm noForward false cycle
      = .ok (writes, slots)) :
    Lm1ChunkFacts expression cycle writes := by
  rw [components] at *
  unfold prepareParsedIntegerALUExprCycle at prep
  dsimp only at prep
  rw [directFailed, multipleFailed, omrFailed, noWriteFailed, barFailed, inputFailed, lowered,
    flushResolved] at prep
  dsimp only at prep
  split at prep
  · simp at prep
  · simp at prep
  · rename_i memoryWrites omrWrite preparedWrite
    split at prep
    · simp at prep
    · simp at prep
    · rename_i slots' updated
      simp only [StepResult.ok.injEq, Prod.mk.injEq] at prep
      obtain ⟨writesEq, _⟩ := prep
      subst writesEq
      exact lm1ChunkFacts_memoryThenInput hsm _ cycle name parsedPrecision unsigned arg rfl
        accesses flushSelection memoryWrites omrWrite lowered preparedWrite

/-- The input-then-memory branch. -/
theorem chunkFacts_of_inputThenMemory (hsm : Bool)
    (expression : ParsedExpr) (name : ParsedAluName) (parsedPrecision : ParsedPrecision)
    (unsigned : Bool) (arg : Option (Fin 256)) (sources destinations : List ParsedOperand)
    (flush : Option ParsedMask) (text : String) (noForward : Bool) (cycle : Fin 4)
    (nextSlots : ProofsLean.MNCore.Forwarding.Slots)
    (accesses : ParsedIntegerMaskInputThenMemoryAccesses)
    (flushSelection : Option PEWordSelection)
    (writes : List PreparedParsedMaskedWrite)
    (slots : ProofsLean.MNCore.Forwarding.Slots)
    (components : expression =
      ⟨.alu name (some parsedPrecision) unsigned arg, sources, destinations, flush, text⟩)
    (directFailed : ParsedExpr.toDirectMaskedIntegerAccessesInLine? expression
      welcomeZeroFiles.maskRegisters welcomeZeroControl.directive
      hsm welcomeZeroControl.context.group
      welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b
      welcomeZeroControl.context.mab welcomeZeroControl.context.pe cycle
      welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
      welcomeZeroControl.context.tWord = none)
    (multipleFailed : ParsedExpr.toDirectMaskedIntegerWritesInLine? expression
      welcomeZeroFiles.maskRegisters welcomeZeroControl.directive
      hsm welcomeZeroControl.context.group
      welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b
      welcomeZeroControl.context.mab welcomeZeroControl.context.pe cycle
      welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
      welcomeZeroControl.context.tWord = none)
    (omrFailed : parsedIntegerMaskExprAccessesInLine? expression welcomeZeroFiles.maskRegisters
      welcomeZeroControl.directive hsm
      welcomeZeroControl.context.pe cycle welcomeZeroControl.context.bar0
      welcomeZeroControl.context.bar1 welcomeZeroControl.context.tWord = none)
    (noWriteFailed : parsedIntegerNoWriteExprAccessesInLine? expression
      welcomeZeroFiles.maskRegisters welcomeZeroControl.context.pe cycle
      welcomeZeroControl.context.group welcomeZeroControl.context.l2b
      welcomeZeroControl.context.l1b welcomeZeroControl.context.mab
      welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
      welcomeZeroControl.context.tWord = none)
    (barFailed : parsedIntegerBarExprAccessesInLine? expression
      welcomeZeroFiles.maskRegisters welcomeZeroControl.directive
      hsm welcomeZeroControl.context.group
      welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b
      welcomeZeroControl.context.mab welcomeZeroControl.context.pe cycle
      welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
      welcomeZeroControl.context.tWord = none)
    (inputFailed : parsedIntegerMaskInputExprAccessesInLine? expression
      welcomeZeroFiles.maskRegisters welcomeZeroControl.directive
      hsm welcomeZeroControl.context.group
      welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b
      welcomeZeroControl.context.mab welcomeZeroControl.context.pe cycle
      welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
      welcomeZeroControl.context.tWord = none)
    (memoryThenInputFailed : parsedIntegerMaskMemoryThenInputExprAccessesInLine? expression
      welcomeZeroFiles.maskRegisters welcomeZeroControl.directive
      hsm welcomeZeroControl.context.group
      welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b
      welcomeZeroControl.context.mab welcomeZeroControl.context.pe cycle
      welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
      welcomeZeroControl.context.tWord = none)
    (lowered : parsedIntegerMaskInputThenMemoryExprAccessesInLine? expression
      welcomeZeroFiles.maskRegisters welcomeZeroControl.directive
      hsm welcomeZeroControl.context.group
      welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b
      welcomeZeroControl.context.mab welcomeZeroControl.context.pe cycle
      welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
      welcomeZeroControl.context.tWord = some accesses)
    (flushResolved : resolveFlushSelection? flush welcomeZeroFiles.maskRegisters cycle =
      some flushSelection)
    (prep : prepareParsedIntegerALUExprCycle welcomeZeroFiles welcomeZeroSlots nextSlots expression
      welcomeZeroControl hsm noForward false cycle
      = .ok (writes, slots)) :
    Lm1ChunkFacts expression cycle writes := by
  rw [components] at *
  unfold prepareParsedIntegerALUExprCycle at prep
  dsimp only at prep
  rw [directFailed, multipleFailed, omrFailed, noWriteFailed, barFailed, inputFailed,
    memoryThenInputFailed, lowered, flushResolved] at prep
  dsimp only at prep
  split at prep
  · simp at prep
  · simp at prep
  · rename_i memoryWrites omrWrite preparedWrite
    split at prep
    · simp at prep
    · simp at prep
    · rename_i slots' updated
      simp only [StepResult.ok.injEq, Prod.mk.injEq] at prep
      obtain ⟨writesEq, _⟩ := prep
      subst writesEq
      exact lm1ChunkFacts_inputThenMemory hsm _ cycle name parsedPrecision unsigned arg rfl
        accesses flushSelection memoryWrites omrWrite lowered preparedWrite

/-- The `.zero` constant branch. -/
theorem chunkFacts_of_zero (hsm : Bool)
    (expression : ParsedExpr) (sources destinations : List ParsedOperand)
    (flush : Option ParsedMask) (text : String) (noForward : Bool) (cycle : Fin 4)
    (nextSlots : ProofsLean.MNCore.Forwarding.Slots)
    (targets : List ParsedConstantDestination)
    (destinationWrites : List PreparedParsedMaskedWrite)
    (flushSelection : Option PEWordSelection)
    (writes : List PreparedParsedMaskedWrite)
    (slots : ProofsLean.MNCore.Forwarding.Slots)
    (components : expression = ⟨.zero, sources, destinations, flush, text⟩)
    (nodup : (expression.toIssueExpr 0).writeBanks.Nodup)
    (lowered : ParsedExpr.toDirectMaskedConstantWrites? expression
      welcomeZeroFiles.maskRegisters welcomeZeroControl.directive
      hsm welcomeZeroControl.context.group
      welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b
      welcomeZeroControl.context.mab welcomeZeroControl.context.pe cycle
      welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
      welcomeZeroControl.context.tWord = some targets)
    (preparedWrites : prepareParsedMaskedConstantWrites welcomeZeroFiles cycle targets
      = .ok destinationWrites)
    (flushResolved : resolveFlushSelection? flush welcomeZeroFiles.maskRegisters cycle =
      some flushSelection)
    (prep : prepareParsedIntegerALUExprCycle welcomeZeroFiles welcomeZeroSlots nextSlots expression
      welcomeZeroControl hsm noForward false cycle
      = .ok (writes, slots)) :
    Lm1ChunkFacts expression cycle writes := by
  rw [components] at *
  unfold prepareParsedIntegerALUExprCycle at prep
  dsimp only at prep
  rw [lowered] at prep
  dsimp only at prep
  rw [preparedWrites, zero_has_execution_request, flushResolved] at prep
  dsimp only at prep
  split at prep
  · simp at prep
  · simp at prep
  · rename_i slots' updated
    simp only [StepResult.ok.injEq, Prod.mk.injEq] at prep
    obtain ⟨writesEq, _⟩ := prep
    subst writesEq
    exact lm1ChunkFacts_zero hsm _ cycle targets destinationWrites _
      rfl lowered preparedWrites nodup rfl

/-- The `.immediate` constant branch. -/
theorem chunkFacts_of_immediate (hsm : Bool)
    (expression : ParsedExpr) (sources destinations : List ParsedOperand)
    (flush : Option ParsedMask) (text : String) (noForward : Bool) (cycle : Fin 4)
    (nextSlots : ProofsLean.MNCore.Forwarding.Slots)
    (payload : BitVec 32) (sparse : Bool)
    (targets : List ParsedConstantDestination)
    (destinationWrites : List PreparedParsedMaskedWrite)
    (flushSelection : Option PEWordSelection)
    (writes : List PreparedParsedMaskedWrite)
    (slots : ProofsLean.MNCore.Forwarding.Slots)
    (components : expression =
      ⟨.immediate payload sparse, sources, destinations, flush, text⟩)
    (nodup : (expression.toIssueExpr 0).writeBanks.Nodup)
    (notDouble : ∀ d ∈ destinations, ParsedOperand.directDestinationBankWidth? d ≠
      some (PEMemory.Bank.lm1, PEMemory.Width.double))
    (lowered : ParsedExpr.toDirectMaskedConstantWrites? expression
      welcomeZeroFiles.maskRegisters welcomeZeroControl.directive
      hsm welcomeZeroControl.context.group
      welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b
      welcomeZeroControl.context.mab welcomeZeroControl.context.pe cycle
      welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
      welcomeZeroControl.context.tWord = some targets)
    (preparedWrites : prepareParsedMaskedConstantWrites welcomeZeroFiles cycle targets
      = .ok destinationWrites)
    (flushResolved : resolveFlushSelection? flush welcomeZeroFiles.maskRegisters cycle =
      some flushSelection)
    (prep : prepareParsedIntegerALUExprCycle welcomeZeroFiles welcomeZeroSlots nextSlots expression
      welcomeZeroControl hsm noForward false cycle
      = .ok (writes, slots)) :
    Lm1ChunkFacts expression cycle writes := by
  rw [components] at *
  unfold prepareParsedIntegerALUExprCycle at prep
  dsimp only at prep
  rw [lowered] at prep
  dsimp only at prep
  rw [preparedWrites, immediate_has_execution_request, flushResolved] at prep
  dsimp only at prep
  split at prep
  · simp at prep
  · simp at prep
  · rename_i slots' updated
    simp only [StepResult.ok.injEq, Prod.mk.injEq] at prep
    obtain ⟨writesEq, _⟩ := prep
    subst writesEq
    exact lm1ChunkFacts_immediate hsm _ cycle targets destinationWrites _ payload sparse rfl
      lowered preparedWrites nodup rfl (fun d member => notDouble d member)

/-! ## 9. The per-cycle chunk lemma -/

/-- **Every cycle chunk satisfies the three shape facts.**  The branch
inversions above are dispatched by a case analysis on which lowering fires. -/
theorem prepareParsedIntegerALUExprCycle_lm1_facts (hsm : Bool)
    (op : ParsedOp) (sources destinations : List ParsedOperand) (flush : Option ParsedMask)
    (text : String) (noForward : Bool) (cycle : Fin 4)
    (nextSlots : ProofsLean.MNCore.Forwarding.Slots)
    (writes : List PreparedParsedMaskedWrite)
    (slots : ProofsLean.MNCore.Forwarding.Slots)
    (notDouble : ∀ payload sparse, op = .immediate payload sparse → ∀ d ∈ destinations,
      ParsedOperand.directDestinationBankWidth? d ≠
        some (PEMemory.Bank.lm1, PEMemory.Width.double))
    (nodup : ((⟨op, sources, destinations, flush, text⟩ : ParsedExpr).toIssueExpr 0).writeBanks.Nodup)
    (prep : prepareParsedIntegerALUExprCycle welcomeZeroFiles welcomeZeroSlots nextSlots
      ⟨op, sources, destinations, flush, text⟩ welcomeZeroControl
      hsm
      noForward false cycle = .ok (writes, slots)) :
    Lm1ChunkFacts ⟨op, sources, destinations, flush, text⟩ cycle writes := by
  cases op with
  | alu name precision unsigned arg =>
      cases precision with
      | none =>
          cases destinations with
          | nil =>
              simp only [prepareParsedIntegerALUExprCycle,
                ParsedExpr.toDirectMaskedIntegerAccessesInLine?,
                ParsedExpr.toDirectMaskedIntegerWritesInLine?,
                parsedIntegerMaskExprAccessesInLine?,
                parsedIntegerNoWriteExprAccessesInLine?,
                parsedIntegerBarExprAccessesInLine?,
                parsedIntegerMaskInputExprAccessesInLine?,
                parsedIntegerMaskMemoryThenInputExprAccessesInLine?,
                parsedIntegerMaskInputThenMemoryExprAccessesInLine?] at prep
              simp at prep
          | cons destination rest =>
              simp only [prepareParsedIntegerALUExprCycle,
                ParsedExpr.toDirectMaskedIntegerAccessesInLine?,
                ParsedExpr.toDirectMaskedIntegerWritesInLine?,
                parsedIntegerMaskExprAccessesInLine?,
                parsedIntegerNoWriteExprAccessesInLine?,
                parsedIntegerBarExprAccessesInLine?,
                parsedIntegerMaskInputExprAccessesInLine?,
                parsedIntegerMaskMemoryThenInputExprAccessesInLine?,
                parsedIntegerMaskInputThenMemoryExprAccessesInLine?,
                List.mapM_cons] at prep
              cases destination with
              | omr entry mask =>
                  cases rest with
                  | nil =>
                      cases entry with
                      | mk value valueLt => cases value <;> simp at prep
                  | cons item items => simp at prep
              | mem access negated extended rounded mask => simp at prep
              | bar lm1 width mask => simp at prep
              | forward kind negated extended rounded => simp at prep
              | fixed kind => simp at prep
              | matrix group width row => simp at prep
              | nowrite => simp at prep
              | l1bm width address => simp at prep
              | l2bm address l2b => simp at prep
              | dar address => simp at prep
      | some parsedPrecision =>
          cases hdirect : ParsedExpr.toDirectMaskedIntegerAccessesInLine?
              ⟨.alu name (some parsedPrecision) unsigned arg, sources, destinations, flush, text⟩
              welcomeZeroFiles.maskRegisters welcomeZeroControl.directive
              hsm
              welcomeZeroControl.context.group welcomeZeroControl.context.l2b
              welcomeZeroControl.context.l1b welcomeZeroControl.context.mab
              welcomeZeroControl.context.pe cycle welcomeZeroControl.context.bar0
              welcomeZeroControl.context.bar1 welcomeZeroControl.context.tWord with
          | some accesses =>
              exact chunkFacts_of_direct hsm _ name parsedPrecision unsigned arg sources destinations
                flush text noForward cycle nextSlots accesses writes slots rfl hdirect prep
          | none =>
              cases hmultiple : ParsedExpr.toDirectMaskedIntegerWritesInLine?
                  ⟨.alu name (some parsedPrecision) unsigned arg, sources, destinations, flush,
                    text⟩ welcomeZeroFiles.maskRegisters welcomeZeroControl.directive
                  hsm
                  welcomeZeroControl.context.group welcomeZeroControl.context.l2b
                  welcomeZeroControl.context.l1b welcomeZeroControl.context.mab
                  welcomeZeroControl.context.pe cycle welcomeZeroControl.context.bar0
                  welcomeZeroControl.context.bar1 welcomeZeroControl.context.tWord with
              | some accessList =>
                  cases accessList with
                  | nil => simp [prepareParsedIntegerALUExprCycle, hdirect, hmultiple] at prep
                  | cons access rest =>
                      exact chunkFacts_of_multiple hsm _ name parsedPrecision unsigned arg sources
                        destinations flush text noForward cycle nextSlots access rest writes slots
                        rfl hdirect nodup hmultiple prep
              | none =>
                  cases homr : parsedIntegerMaskExprAccessesInLine?
                      ⟨.alu name (some parsedPrecision) unsigned arg, sources, destinations,
                        flush, text⟩ welcomeZeroFiles.maskRegisters welcomeZeroControl.directive
                      hsm
                      welcomeZeroControl.context.pe cycle welcomeZeroControl.context.bar0
                      welcomeZeroControl.context.bar1 welcomeZeroControl.context.tWord with
                  | some omrAccesses =>
                      cases hflush : resolveFlushSelection? flush welcomeZeroFiles.maskRegisters
                          cycle with
                      | none =>
                          simp [prepareParsedIntegerALUExprCycle, hdirect, hmultiple, homr,
                            hflush] at prep
                      | some flushSelection =>
                          exact chunkFacts_of_omr hsm _ name parsedPrecision unsigned arg sources
                            destinations flush text noForward cycle nextSlots omrAccesses
                            flushSelection writes slots rfl hdirect hmultiple homr hflush prep
                  | none =>
                      cases hnoWrite : parsedIntegerNoWriteExprAccessesInLine?
                          ⟨.alu name (some parsedPrecision) unsigned arg, sources, destinations,
                            flush, text⟩ welcomeZeroFiles.maskRegisters
                          welcomeZeroControl.context.pe cycle welcomeZeroControl.context.group
                          welcomeZeroControl.context.l2b welcomeZeroControl.context.l1b
                          welcomeZeroControl.context.mab welcomeZeroControl.context.bar0
                          welcomeZeroControl.context.bar1 welcomeZeroControl.context.tWord with
                      | some noWriteAccesses =>
                          exact chunkFacts_of_noWrite hsm _ name parsedPrecision unsigned arg sources
                            destinations flush text noForward cycle nextSlots noWriteAccesses
                            writes slots rfl hdirect hmultiple homr hnoWrite prep
                      | none =>
                          cases hbar : parsedIntegerBarExprAccessesInLine?
                              ⟨.alu name (some parsedPrecision) unsigned arg, sources,
                                destinations, flush, text⟩ welcomeZeroFiles.maskRegisters
                              welcomeZeroControl.directive
                              hsm
                              welcomeZeroControl.context.group welcomeZeroControl.context.l2b
                              welcomeZeroControl.context.l1b welcomeZeroControl.context.mab
                              welcomeZeroControl.context.pe cycle welcomeZeroControl.context.bar0
                              welcomeZeroControl.context.bar1 welcomeZeroControl.context.tWord with
                          | some barAccesses =>
                              exact chunkFacts_of_bar hsm _ name parsedPrecision unsigned arg
                                sources destinations flush text noForward cycle nextSlots
                                barAccesses writes slots rfl hdirect hmultiple homr hnoWrite hbar
                                prep
                          | none =>
                              cases hinput : parsedIntegerMaskInputExprAccessesInLine?
                                  ⟨.alu name (some parsedPrecision) unsigned arg, sources,
                                    destinations, flush, text⟩ welcomeZeroFiles.maskRegisters
                                  welcomeZeroControl.directive
                                  hsm
                                  welcomeZeroControl.context.group welcomeZeroControl.context.l2b
                                  welcomeZeroControl.context.l1b welcomeZeroControl.context.mab
                                  welcomeZeroControl.context.pe cycle
                                  welcomeZeroControl.context.bar0 welcomeZeroControl.context.bar1
                                  welcomeZeroControl.context.tWord with
                              | some inputAccesses =>
                                  cases hflush : resolveFlushSelection? flush
                                      welcomeZeroFiles.maskRegisters cycle with
                                  | none =>
                                      simp [prepareParsedIntegerALUExprCycle, hdirect,
                                        hmultiple, homr, hnoWrite, hbar, hinput, hflush] at prep
                                  | some flushSelection =>
                                      exact chunkFacts_of_maskInput hsm _ name parsedPrecision
                                        unsigned arg sources destinations flush text noForward
                                        cycle nextSlots inputAccesses flushSelection writes slots
                                        rfl hdirect hmultiple homr hnoWrite hbar hflush hinput
                                        prep
                              | none =>
                                  cases hmixed :
                                      parsedIntegerMaskMemoryThenInputExprAccessesInLine?
                                        ⟨.alu name (some parsedPrecision) unsigned arg, sources,
                                          destinations, flush, text⟩
                                        welcomeZeroFiles.maskRegisters
                                        welcomeZeroControl.directive
                                        hsm
                                        welcomeZeroControl.context.group
                                        welcomeZeroControl.context.l2b
                                        welcomeZeroControl.context.l1b
                                        welcomeZeroControl.context.mab
                                        welcomeZeroControl.context.pe cycle
                                        welcomeZeroControl.context.bar0
                                        welcomeZeroControl.context.bar1
                                        welcomeZeroControl.context.tWord with
                                  | some mixedAccesses =>
                                      cases hflush : resolveFlushSelection? flush
                                          welcomeZeroFiles.maskRegisters cycle with
                                      | none =>
                                          simp [prepareParsedIntegerALUExprCycle, hdirect,
                                            hmultiple, homr, hnoWrite, hbar, hinput, hmixed,
                                            hflush] at prep
                                      | some flushSelection =>
                                          exact chunkFacts_of_memoryThenInput hsm _ name
                                            parsedPrecision unsigned arg sources destinations
                                            flush text noForward cycle nextSlots mixedAccesses
                                            flushSelection writes slots rfl hdirect hmultiple
                                            homr hnoWrite hbar hinput hmixed hflush prep
                                  | none =>
                                      cases hreverse :
                                          parsedIntegerMaskInputThenMemoryExprAccessesInLine?
                                            ⟨.alu name (some parsedPrecision) unsigned arg,
                                              sources, destinations, flush, text⟩
                                            welcomeZeroFiles.maskRegisters
                                            welcomeZeroControl.directive
                                            hsm
                                            welcomeZeroControl.context.group
                                            welcomeZeroControl.context.l2b
                                            welcomeZeroControl.context.l1b
                                            welcomeZeroControl.context.mab
                                            welcomeZeroControl.context.pe cycle
                                            welcomeZeroControl.context.bar0
                                            welcomeZeroControl.context.bar1
                                            welcomeZeroControl.context.tWord with
                                      | some reverseAccesses =>
                                          cases hflush : resolveFlushSelection? flush
                                              welcomeZeroFiles.maskRegisters cycle with
                                          | none =>
                                              simp [prepareParsedIntegerALUExprCycle, hdirect,
                                                hmultiple, homr, hnoWrite, hbar, hinput,
                                                hmixed, hreverse, hflush] at prep
                                          | some flushSelection =>
                                              exact chunkFacts_of_inputThenMemory hsm _ name
                                                parsedPrecision unsigned arg sources
                                                destinations flush text noForward cycle
                                                nextSlots reverseAccesses flushSelection writes
                                                slots rfl hdirect hmultiple homr hnoWrite hbar
                                                hinput hmixed hreverse hflush prep
                                      | none =>
                                          unfold prepareParsedIntegerALUExprCycle at prep
                                          dsimp only at prep
                                          rw [hdirect, hmultiple, homr, hnoWrite, hbar, hinput,
                                            hmixed, hreverse] at prep
                                          dsimp only at prep
                                          cases destinations with
                                          | nil => simp at prep
                                          | cons destination rest =>
                                              cases destination with
                                              | omr entry mask =>
                                                  cases rest with
                                                  | nil =>
                                                      cases entry with
                                                      | mk value valueLt =>
                                                          cases value <;> simp at prep
                                                  | cons item items => simp at prep
                                              | mem access negated extended rounded mask =>
                                                  simp at prep
                                              | bar lm1 width mask => simp at prep
                                              | forward kind negated extended rounded =>
                                                  simp at prep
                                              | fixed kind => simp at prep
                                              | matrix group width row => simp at prep
                                              | nowrite => simp at prep
                                              | l1bm width address => simp at prep
                                              | l2bm address l2b => simp at prep
                                              | dar address => simp at prep
  | zero =>
      cases hlowered : ParsedExpr.toDirectMaskedConstantWrites?
          ⟨.zero, sources, destinations, flush, text⟩ welcomeZeroFiles.maskRegisters
          welcomeZeroControl.directive
          hsm
          welcomeZeroControl.context.group welcomeZeroControl.context.l2b
          welcomeZeroControl.context.l1b welcomeZeroControl.context.mab
          welcomeZeroControl.context.pe cycle welcomeZeroControl.context.bar0
          welcomeZeroControl.context.bar1 welcomeZeroControl.context.tWord with
      | none =>
          simp [prepareParsedIntegerALUExprCycle, hlowered] at prep
      | some targets =>
          cases hprepared : prepareParsedMaskedConstantWrites welcomeZeroFiles cycle targets with
          | failure => simp [prepareParsedIntegerALUExprCycle, hlowered, hprepared] at prep
          | unknown => simp [prepareParsedIntegerALUExprCycle, hlowered, hprepared] at prep
          | ok destinationWrites =>
              cases hflush : resolveFlushSelection? flush welcomeZeroFiles.maskRegisters cycle with
              | none =>
                  unfold prepareParsedIntegerALUExprCycle at prep
                  dsimp only at prep
                  rw [hlowered] at prep
                  dsimp only at prep
                  rw [hprepared, zero_has_execution_request, hflush] at prep
                  simp at prep
              | some flushSelection =>
                  exact chunkFacts_of_zero hsm _ sources destinations flush text noForward cycle
                    nextSlots targets destinationWrites flushSelection writes slots rfl nodup
                    hlowered hprepared hflush prep
  | immediate payload sparse =>
      cases hlowered : ParsedExpr.toDirectMaskedConstantWrites?
          ⟨.immediate payload sparse, sources, destinations, flush, text⟩
          welcomeZeroFiles.maskRegisters welcomeZeroControl.directive
          hsm
          welcomeZeroControl.context.group welcomeZeroControl.context.l2b
          welcomeZeroControl.context.l1b welcomeZeroControl.context.mab
          welcomeZeroControl.context.pe cycle welcomeZeroControl.context.bar0
          welcomeZeroControl.context.bar1 welcomeZeroControl.context.tWord with
      | none =>
          simp [prepareParsedIntegerALUExprCycle, hlowered] at prep
      | some targets =>
          cases hprepared : prepareParsedMaskedConstantWrites welcomeZeroFiles cycle targets with
          | failure => simp [prepareParsedIntegerALUExprCycle, hlowered, hprepared] at prep
          | unknown => simp [prepareParsedIntegerALUExprCycle, hlowered, hprepared] at prep
          | ok destinationWrites =>
              cases hflush : resolveFlushSelection? flush welcomeZeroFiles.maskRegisters cycle with
              | none =>
                  unfold prepareParsedIntegerALUExprCycle at prep
                  dsimp only at prep
                  rw [hlowered] at prep
                  dsimp only at prep
                  rw [hprepared, immediate_has_execution_request, hflush] at prep
                  simp at prep
              | some flushSelection =>
                  exact chunkFacts_of_immediate hsm _ sources destinations flush text noForward cycle
                    nextSlots payload sparse targets destinationWrites flushSelection writes slots
                    rfl nodup (fun d member => notDouble payload sparse rfl d member) hlowered
                    hprepared hflush prep
  | mau precision matrix kind half round => simp [prepareParsedIntegerALUExprCycle] at prep
  | matrixWrite precision => simp [prepareParsedIntegerALUExprCycle] at prep
  | matrixRead precision => simp [prepareParsedIntegerALUExprCycle] at prep
  | wait tag => simp [prepareParsedIntegerALUExprCycle] at prep
  | noforward => simp [prepareParsedIntegerALUExprCycle] at prep
  | l1bm operation => simp [prepareParsedIntegerALUExprCycle] at prep
  | l2bm operation => simp [prepareParsedIntegerALUExprCycle] at prep

/-! ## The four-cycle unfolding at an arbitrary mask flag -/

/-- **The plain row's `.lm1` shape at an arbitrary incoming slot state and an
arbitrary mask flag.**  The per-cycle chunk facts hold whatever the flag is:
the flag only changes the *selection* stored in the prepared writes, never
their destination, data or `.lm1` count. -/
theorem plainRow_lm1_shape_of_startSlots_anyFlag (e : ParsedExpr)
    (notDouble : ∀ payload sparse, e.op = .immediate payload sparse →
      ∀ destination ∈ e.destinations,
        ParsedOperand.directDestinationBankWidth? destination ≠
          some (PEMemory.Bank.lm1, PEMemory.Width.double))
    (nodup : (e.toIssueExpr 0).writeBanks.Nodup)
    (noForward : Bool) (hsm : Bool)
    (startSlots : ProofsLean.MNCore.Forwarding.Slots)
    (writes : List PreparedParsedMaskedWrite)
    (slots : ProofsLean.MNCore.Forwarding.Slots)
    (prep : prepareParsedIntegerALUExprCycles welcomeZeroFiles welcomeZeroSlots startSlots e
      welcomeZeroControl hsm noForward false = .ok (writes, slots)) :
    Lm1WritesDoubleCopy writes ∨ Lm1WritesNarrow writes := by
  cases e with
  | mk op sources destinations flush text =>
      obtain ⟨w0, w1, w2, w3, s1, s2, s3, h0, h1, h2, h3, writesEq⟩ :=
        prepareParsedIntegerALUExprCycles_four_start welcomeZeroFiles welcomeZeroSlots
          startSlots ⟨op, sources, destinations, flush, text⟩ welcomeZeroControl hsm
          noForward false writes slots prep
      have f0 := prepareParsedIntegerALUExprCycle_lm1_facts hsm op sources destinations flush text
        noForward 0 startSlots w0 s1 notDouble nodup h0
      have f1 := prepareParsedIntegerALUExprCycle_lm1_facts hsm op sources destinations flush text
        noForward 1 s1 w1 s2 notDouble nodup h1
      have f2 := prepareParsedIntegerALUExprCycle_lm1_facts hsm op sources destinations flush text
        noForward 2 s2 w2 s3 notDouble nodup h2
      have f3 := prepareParsedIntegerALUExprCycle_lm1_facts hsm op sources destinations flush text
        noForward 3 s3 w3 slots notDouble nodup h3
      rw [writesEq]
      exact lm1WritesShape_of_chunks ⟨op, sources, destinations, flush, text⟩ nodup
        w0 w1 w2 w3 f0 f1 f2 f3

/-- **The plain row's `.lm1` shape in the line-expression form, at an arbitrary
mask flag.** -/
theorem plainRow_lm1_shape_of_linePrep_anyFlag (e : ParsedExpr)
    (plain : parsedExprIsPlainIntegerALU e = true)
    (notDouble : ∀ payload sparse, e.op = .immediate payload sparse →
      ∀ destination ∈ e.destinations,
        ParsedOperand.directDestinationBankWidth? destination ≠
          some (PEMemory.Bank.lm1, PEMemory.Width.double))
    (nodup : (e.toIssueExpr 0).writeBanks.Nodup)
    (noForward : Bool) (hsm : Bool)
    (startSlots : ProofsLean.MNCore.Forwarding.Slots)
    (writes : List PreparedParsedMaskedWrite)
    (slots : ProofsLean.MNCore.Forwarding.Slots) (bars : List (Bool × BitVec 12))
    (prep : prepareParsedIntegerMatrixReadLineExpression welcomeZeroFiles welcomeZeroSlots
      startSlots welcomeZeroMatrixStore e welcomeZeroControl hsm noForward false =
      .ok (writes, slots, bars)) :
    Lm1WritesDoubleCopy writes ∨ Lm1WritesNarrow writes := by
  cases e with
  | mk op sources destinations flush text =>
      cases op with
      | alu name precision unsigned arg =>
          simp only [prepareParsedIntegerMatrixReadLineExpression] at prep
          cases cycles : prepareParsedIntegerALUExprCycles welcomeZeroFiles welcomeZeroSlots
              startSlots ⟨.alu name precision unsigned arg, sources, destinations, flush,
                text⟩ welcomeZeroControl hsm noForward false with
          | failure => rw [cycles] at prep; simp at prep
          | unknown => rw [cycles] at prep; simp at prep
          | ok result =>
              obtain ⟨rowWrites, rowSlots⟩ := result
              rw [cycles] at prep
              simp only [StepResult.ok.injEq, Prod.mk.injEq] at prep
              rw [← prep.1]
              exact plainRow_lm1_shape_of_startSlots_anyFlag _ notDouble nodup noForward hsm
                startSlots rowWrites rowSlots cycles
      | zero =>
          simp only [prepareParsedIntegerMatrixReadLineExpression] at prep
          cases cycles : prepareParsedIntegerALUExprCycles welcomeZeroFiles welcomeZeroSlots
              startSlots ⟨.zero, sources, destinations, flush, text⟩ welcomeZeroControl hsm
              noForward false with
          | failure => rw [cycles] at prep; simp at prep
          | unknown => rw [cycles] at prep; simp at prep
          | ok result =>
              obtain ⟨rowWrites, rowSlots⟩ := result
              rw [cycles] at prep
              simp only [StepResult.ok.injEq, Prod.mk.injEq] at prep
              rw [← prep.1]
              exact plainRow_lm1_shape_of_startSlots_anyFlag _ notDouble nodup noForward hsm
                startSlots rowWrites rowSlots cycles
      | immediate value unsigned =>
          simp only [prepareParsedIntegerMatrixReadLineExpression] at prep
          cases cycles : prepareParsedIntegerALUExprCycles welcomeZeroFiles welcomeZeroSlots
              startSlots ⟨.immediate value unsigned, sources, destinations, flush, text⟩
              welcomeZeroControl hsm noForward false with
          | failure => rw [cycles] at prep; simp at prep
          | unknown => rw [cycles] at prep; simp at prep
          | ok result =>
              obtain ⟨rowWrites, rowSlots⟩ := result
              rw [cycles] at prep
              simp only [StepResult.ok.injEq, Prod.mk.injEq] at prep
              rw [← prep.1]
              exact plainRow_lm1_shape_of_startSlots_anyFlag _ notDouble nodup noForward hsm
                startSlots rowWrites rowSlots cycles
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

/-- **The flag-true plain row shape.**  At the *line* mask flag `true` — the
situation of a mixed line whose inert companion carries a masked `.mem` /
`.bar` / `.omr` destination — a plain row still satisfies the double-copy or
narrow shape. -/
theorem plainRow_lm1_shape_of_linePrep_trueFlag (e : ParsedExpr)
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
      startSlots welcomeZeroMatrixStore e welcomeZeroControl true noForward false =
      .ok (writes, slots, bars)) :
    Lm1WritesDoubleCopy writes ∨ Lm1WritesNarrow writes :=
  plainRow_lm1_shape_of_linePrep_anyFlag e plain notDouble nodup noForward true startSlots
    writes slots bars prep

/-- **The flag-free plain row shape of a row whose own mask flag is `false`.**
This is the statement needed for the mixed plain/inert class: the row writes no
masked destination itself (`parsedExprHasSingleLineWriteMask e = false`), while
the line-level flag is `true` because of a companion row.  The row shape still
holds. -/
theorem plainRow_lm1_shape_of_linePrep_rowFlagFalse (e : ParsedExpr)
    (plain : parsedExprIsPlainIntegerALU e = true)
    (rowFlag : parsedExprHasSingleLineWriteMask e = false)
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
      startSlots welcomeZeroMatrixStore e welcomeZeroControl true noForward false =
      .ok (writes, slots, bars)) :
    Lm1WritesDoubleCopy writes ∨ Lm1WritesNarrow writes :=
  plainRow_lm1_shape_of_linePrep_anyFlag e plain notDouble nodup noForward true startSlots
    writes slots bars prep

end PlainFlagFree

/-- The line shape when the `.lm1` writer `e` is a plain row, possibly preceded and
followed by arbitrary preparing rows. -/
theorem welcomePEWriteShape_of_plainWriter_arbitrary_flagFree
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
      ((PlainFlagFree.plainRow_lm1_shape_of_linePrep_anyFlag e plain notDouble
        (welcomeLm1Writer_nodup expressions unrefuted e eMem) _ _ prefixSlots rowWrites
        rowSlots rowBars rowPrep)) afterFree
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


/-! ## The flag-free plain-writer package

The slot-free package of `WelcomeSlotFree.lean` still carries the flag equation
`lineFlag = ownFlag`.  With the any-flag row shape above that equation is no
longer needed: the package below records the split position, the non-repetition
of the writer, the absence of float-MAU rows and the remaining genuine side
condition (the immediate-`.double` exclusion), and nothing about the mask flag.
Every line that satisfies the old package satisfies this one
(`welcomePEPlainWriterDataFor_flagFree_of_slotFree`), so this is a weakening in
the conservative direction. -/

/-- **The flag-free plain-writer data of one line.**  Same as
`WelcomePEPlainWriterDataForSlotFree`, except that the flag equation
`lineFlag = ownFlag` is removed: the row shape now holds at *whatever* mask flag
the integer stage uses. -/
def WelcomePEPlainWriterDataForFlagFree (expressions : List NormalizedExpr) : Prop :=
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
          ((∀ (payload : BitVec 32) (sparse : Bool), e.op = .immediate payload sparse →
              ∀ destination ∈ e.destinations,
                ParsedOperand.directDestinationBankWidth? destination ≠
                  some (PEMemory.Bank.lm1, PEMemory.Width.double)) ∨
            WelcomePEInputIndependent expressions)

/-- The global flag-free plain-writer package. -/
def WelcomePEPlainWriterDataFlagFree : Prop :=
  ∀ expressions, WelcomePEUnrefuted expressions →
    WelcomePEPlainWriterDataForFlagFree expressions

/-- **The old slot-free package implies the flag-free one** (the conservative
direction: nothing that satisfied the flag equation is excluded). -/
theorem welcomePEPlainWriterDataFor_flagFree_of_slotFree
    (expressions : List NormalizedExpr) (data : WelcomePEPlainWriterDataForSlotFree expressions) :
    WelcomePEPlainWriterDataForFlagFree expressions := by
  intro e eMem plain writer
  obtain ⟨before, after, split, notBefore, notAfter, floatEmpty, flagAndDouble | indep⟩ :=
    data e eMem plain writer
  · exact ⟨before, after, split, notBefore, notAfter, floatEmpty, Or.inl flagAndDouble.2⟩
  · exact ⟨before, after, split, notBefore, notAfter, floatEmpty, Or.inr indep⟩

/-- **The global old package implies the global flag-free one.** -/
theorem welcomePEPlainWriterData_flagFree_of_slotFree (data : WelcomePEPlainWriterDataSlotFree) :
    WelcomePEPlainWriterDataFlagFree :=
  fun expressions unrefuted =>
    welcomePEPlainWriterDataFor_flagFree_of_slotFree expressions (data expressions unrefuted)

/-- **The round-46 companion package implies the flag-free package.** -/
theorem welcomePEPlainWriterDataFor_flagFree_of_companion
    (expressions : List NormalizedExpr) (data : WelcomePEPlainWriterDataFor expressions) :
    WelcomePEPlainWriterDataForFlagFree expressions :=
  welcomePEPlainWriterDataFor_flagFree_of_slotFree expressions
    (welcomePEPlainWriterDataFor_slotFree_of_companion expressions data)

/-- **The global round-46 package implies the global flag-free one.** -/
theorem welcomePEPlainWriterData_flagFree_of_companion (data : WelcomePEPlainWriterData) :
    WelcomePEPlainWriterDataFlagFree :=
  fun expressions unrefuted =>
    welcomePEPlainWriterDataFor_flagFree_of_companion expressions (data expressions unrefuted)

/-- **The plain-writer line shape from the flag-free package.** -/
theorem welcomePEWriteShape_of_plainWriter_data_flagFree
    (expressions : List NormalizedExpr)
    (data : WelcomePEPlainWriterDataForFlagFree expressions)
    (unrefuted : WelcomePEUnrefuted expressions) (e : ParsedExpr)
    (eMem : e ∈ expressions.map NormalizedExpr.toParsed)
    (plain : parsedExprIsPlainIntegerALU e = true)
    (writer : Issue.Bank.lm1 ∈ (e.toIssueExpr 0).writeBanks) :
    WelcomePEWriteShape expressions := by
  obtain ⟨before, after, split, notBefore, notAfter, floatEmpty, notDouble | indep⟩ :=
    data e eMem plain writer
  · obtain ⟨-, -, mslFalse, reluFalse, blockFalse, -, -, matrixMAUFalse, -, l1False, -⟩ :=
      parsedExprIsPlainIntegerALU_facts e plain
    exact welcomePEWriteShape_of_plainWriter_arbitrary_flagFree expressions unrefuted before after
      e split eMem writer notBefore notAfter notDouble plain floatEmpty
      (welcomePEMiddleStageLm1Free_of_rows expressions e
        (welcomeLm1Writer_rows expressions unrefuted e eMem writer) mslFalse reluFalse blockFalse)
      (welcomePEMatrixMAUStageLm1Free_of_rows expressions e
        (welcomeLm1Writer_rows expressions unrefuted e eMem writer) matrixMAUFalse)
      (welcomePEL1StageLm1Free_of_rows expressions e
        (welcomeLm1Writer_rows expressions unrefuted e eMem writer) l1False)
  · exact Or.inr (Or.inr indep)

/-! ## The per-line dispatch data with the flag-free plain package -/

/-- **The per-line dispatch data, with the plain companion unrestricted and the
flag equation dropped.**  The other six disjuncts are the slot-free ones. -/
def WelcomePELm1LineDispatchDataFlagFree (expressions : List NormalizedExpr) : Prop :=
  (∃ e ∈ expressions.map NormalizedExpr.toParsed,
      Issue.Bank.lm1 ∈ (e.toIssueExpr 0).writeBanks ∧
        parsedExprIsSpecialALUProducer e = true) ∨
    (WelcomePEPlainWriterDataForFlagFree expressions ∧
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

/-- A plain writer with its flag-free line data selects the second disjunct. -/
theorem welcomePELm1LineDispatchDataFlagFree_plain (expressions : List NormalizedExpr)
    (data : WelcomePEPlainWriterDataForFlagFree expressions) (e : ParsedExpr)
    (eMem : e ∈ expressions.map NormalizedExpr.toParsed)
    (eWriter : Issue.Bank.lm1 ∈ (e.toIssueExpr 0).writeBanks)
    (plain : parsedExprIsPlainIntegerALU e = true) :
    WelcomePELm1LineDispatchDataFlagFree expressions :=
  Or.inr (Or.inl ⟨data, e, eMem, eWriter, plain⟩)

/-- The special-ALU writer selects the first disjunct. -/
theorem welcomePELm1LineDispatchDataFlagFree_special (expressions : List NormalizedExpr)
    (e : ParsedExpr) (eMem : e ∈ expressions.map NormalizedExpr.toParsed)
    (eWriter : Issue.Bank.lm1 ∈ (e.toIssueExpr 0).writeBanks)
    (special : parsedExprIsSpecialALUProducer e = true) :
    WelcomePELm1LineDispatchDataFlagFree expressions :=
  Or.inl ⟨e, eMem, eWriter, special⟩

/-- A `.matrixRead` writer selects the third disjunct. -/
theorem welcomePELm1LineDispatchDataFlagFree_matrixRead (expressions : List NormalizedExpr)
    (data : WelcomePEMatrixReadWriterDataForSlotFree expressions) (e : ParsedExpr)
    (eMem : e ∈ expressions.map NormalizedExpr.toParsed)
    (eWriter : Issue.Bank.lm1 ∈ (e.toIssueExpr 0).writeBanks)
    (read : parsedExprIsMatrixReadProducer e = true) :
    WelcomePELm1LineDispatchDataFlagFree expressions :=
  Or.inr (Or.inr (Or.inl ⟨data, e, eMem, eWriter, read⟩))

/-- A float-MAU writer selects the fourth disjunct. -/
theorem welcomePELm1LineDispatchDataFlagFree_floatMAU (expressions : List NormalizedExpr)
    (data : WelcomePEFloatMAUWriterDataFor expressions) (e : ParsedExpr)
    (eMem : e ∈ expressions.map NormalizedExpr.toParsed)
    (eWriter : Issue.Bank.lm1 ∈ (e.toIssueExpr 0).writeBanks)
    (float : parsedExprIsSupportedFloatMAUProducer e = true) :
    WelcomePELm1LineDispatchDataFlagFree expressions :=
  Or.inr (Or.inr (Or.inr (Or.inl ⟨data, e, eMem, eWriter, float⟩)))

/-- A matrix-MAU writer selects the fifth disjunct. -/
theorem welcomePELm1LineDispatchDataFlagFree_matrixMAU (expressions : List NormalizedExpr)
    (data : WelcomePEMatrixMAUWriterDataFor expressions) (e : ParsedExpr)
    (eMem : e ∈ expressions.map NormalizedExpr.toParsed)
    (eWriter : Issue.Bank.lm1 ∈ (e.toIssueExpr 0).writeBanks)
    (mau : parsedExprIsMatrixMAUProducer e = true) :
    WelcomePELm1LineDispatchDataFlagFree expressions :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨data, e, eMem, eWriter, mau⟩))))

/-- A `.l1bm` writer selects the sixth disjunct. -/
theorem welcomePELm1LineDispatchDataFlagFree_l1bm (expressions : List NormalizedExpr)
    (data : WelcomePEL1BMWriterDataFor expressions) (e : ParsedExpr)
    (eMem : e ∈ expressions.map NormalizedExpr.toParsed)
    (eWriter : Issue.Bank.lm1 ∈ (e.toIssueExpr 0).writeBanks)
    (l1 : parsedExprIsL1ToPEProducer e = true) :
    WelcomePELm1LineDispatchDataFlagFree expressions :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨data, e, eMem, eWriter, l1⟩)))))

/-- The phantom/no-writer case selects the seventh disjunct. -/
theorem welcomePELm1LineDispatchDataFlagFree_phantom (expressions : List NormalizedExpr)
    (h : ∀ e ∈ expressions.map NormalizedExpr.toParsed,
      Issue.Bank.lm1 ∈ (e.toIssueExpr 0).writeBanks → welcomePhantomWriterKind e)
    (free : WelcomePELm1FreeStageCommit expressions) :
    WelcomePELm1LineDispatchDataFlagFree expressions :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h, free⟩)))))

/-- **A slot-free per-line dispatch datum gives a flag-free one.** -/
theorem welcomePELm1LineDispatchDataFlagFree_of_slotFree (expressions : List NormalizedExpr)
    (data : WelcomePELm1LineDispatchDataSlotFree expressions) :
    WelcomePELm1LineDispatchDataFlagFree expressions := by
  rcases data with ⟨e, eMem, eWriter, kind⟩ | ⟨plainData, e, eMem, eWriter, kind⟩ |
    ⟨readData, e, eMem, eWriter, kind⟩ | ⟨floatData, e, eMem, eWriter, kind⟩ |
    ⟨mauData, e, eMem, eWriter, kind⟩ | ⟨l1Data, e, eMem, eWriter, kind⟩ | ⟨phantom, free⟩
  · exact Or.inl ⟨e, eMem, eWriter, kind⟩
  · exact Or.inr (Or.inl
      ⟨welcomePEPlainWriterDataFor_flagFree_of_slotFree expressions plainData,
        e, eMem, eWriter, kind⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨readData, e, eMem, eWriter, kind⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨floatData, e, eMem, eWriter, kind⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨mauData, e, eMem, eWriter, kind⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨l1Data, e, eMem, eWriter, kind⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨phantom, free⟩)))))

/-- **The per-line write shape from the flag-free dispatch data.** -/
theorem welcomePEWriteShape_of_lineDataFlagFree (expressions : List NormalizedExpr)
    (unrefuted : WelcomePEUnrefuted expressions)
    (special : WelcomePESpecialALUWriterShapeObligation)
    (data : WelcomePELm1LineDispatchDataFlagFree expressions) :
    WelcomePEWriteShape expressions := by
  rcases data with ⟨e, eMem, eWriter, kind⟩ | ⟨plainData, e, eMem, eWriter, kind⟩ |
    ⟨readData, e, eMem, eWriter, kind⟩ | ⟨floatData, e, eMem, eWriter, kind⟩ |
    ⟨mauData, e, eMem, eWriter, kind⟩ | ⟨l1Data, e, eMem, eWriter, kind⟩ |
    ⟨-, free⟩
  · exact special expressions unrefuted ⟨e, eMem, eWriter, kind⟩
  · exact welcomePEWriteShape_of_plainWriter_data_flagFree expressions plainData unrefuted e eMem
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

/-- **The flag-free dispatch data from the components.**  Identical to
`welcomePELm1LineDispatchDataSlotFree_of_components`, except that the plain
component is the flag-free package. -/
theorem welcomePELm1LineDispatchDataFlagFree_of_components
    (phantom : WelcomePELm1PhantomWriterProvenance)
    (plain : WelcomePEPlainWriterDataFlagFree)
    (read : WelcomePEMatrixReadWriterDataSlotFree)
    (float : WelcomePEFloatMAUWriterData) (mau : WelcomePEMatrixMAUWriterData)
    (l1 : WelcomePEL1BMWriterData)
    (expressions : List NormalizedExpr) (unrefuted : WelcomePEUnrefuted expressions) :
    WelcomePELm1LineDispatchDataFlagFree expressions := by
  by_cases hasWriter : ∃ e ∈ expressions.map NormalizedExpr.toParsed,
      Issue.Bank.lm1 ∈ (e.toIssueExpr 0).writeBanks
  · obtain ⟨e, eMem, eWriter⟩ := hasWriter
    have supported := List.all_eq_true.mp unrefuted.1.2.2.2 e eMem
    have notUnsupported : parsedExprIsUnsupportedRustAlu e = false := by
      simpa using (List.any_eq_false.mp unrefuted.1.2.2.1) e eMem
    rcases supportedProducer_partition e supported with
      isPlain | isFamily | isSpecial | isInert | isUnsupported
    · exact welcomePELm1LineDispatchDataFlagFree_plain expressions
        (plain expressions unrefuted) e eMem eWriter isPlain
    · rcases parsedExprIsFamilyProducer_cases e isFamily with
        readKind | mauKind | floatKind | writeKind | toPEKind | l2Kind
      · exact welcomePELm1LineDispatchDataFlagFree_matrixRead expressions
          (read expressions unrefuted) e eMem eWriter readKind
      · exact welcomePELm1LineDispatchDataFlagFree_matrixMAU expressions
          (mau expressions unrefuted) e eMem eWriter mauKind
      · exact welcomePELm1LineDispatchDataFlagFree_floatMAU expressions
          (float expressions unrefuted) e eMem eWriter floatKind
      · have hphantom : ∀ x ∈ expressions.map NormalizedExpr.toParsed,
            Issue.Bank.lm1 ∈ (x.toIssueExpr 0).writeBanks → welcomePhantomWriterKind x := by
          intro x xMem xWriter
          have same : x = e :=
            welcomeLm1Writer_eq_of_two expressions unrefuted xMem eMem xWriter eWriter
          rw [same]
          exact Or.inr (Or.inr (Or.inr (Or.inl writeKind)))
        exact welcomePELm1LineDispatchDataFlagFree_phantom expressions hphantom
          (phantom expressions unrefuted hphantom)
      · exact welcomePELm1LineDispatchDataFlagFree_l1bm expressions
          (l1 expressions unrefuted) e eMem eWriter toPEKind
      · have hphantom : ∀ x ∈ expressions.map NormalizedExpr.toParsed,
            Issue.Bank.lm1 ∈ (x.toIssueExpr 0).writeBanks → welcomePhantomWriterKind x := by
          intro x xMem xWriter
          have same : x = e :=
            welcomeLm1Writer_eq_of_two expressions unrefuted xMem eMem xWriter eWriter
          rw [same]
          exact Or.inr (Or.inr (Or.inr (Or.inr l2Kind)))
        exact welcomePELm1LineDispatchDataFlagFree_phantom expressions hphantom
          (phantom expressions unrefuted hphantom)
    · exact welcomePELm1LineDispatchDataFlagFree_special expressions e eMem eWriter isSpecial
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
      exact welcomePELm1LineDispatchDataFlagFree_phantom expressions hphantom
        (phantom expressions unrefuted hphantom)
    · rw [notUnsupported] at isUnsupported
      cases isUnsupported
  · have hphantom : ∀ x ∈ expressions.map NormalizedExpr.toParsed,
        Issue.Bank.lm1 ∈ (x.toIssueExpr 0).writeBanks → welcomePhantomWriterKind x := by
      intro x xMem xWriter
      exact absurd ⟨x, xMem, xWriter⟩ hasWriter
    exact welcomePELm1LineDispatchDataFlagFree_phantom expressions hphantom
      (phantom expressions unrefuted hphantom)

/-- **The flag-free line-dispatch bundle.** -/
def WelcomePEDispatchResidualsFlagFree : Prop :=
  WelcomePESpecialALUWriterShapeObligation ∧
    ∀ expressions, WelcomePEUnrefuted expressions →
      WelcomePELm1LineDispatchDataFlagFree expressions

/-- **`WelcomePELm1WriteShapeObligation` from the flag-free dispatch bundle.** -/
theorem welcomePELm1WriteShapeObligation_of_dispatchFlagFree
    (residuals : WelcomePEDispatchResidualsFlagFree) :
    WelcomePELm1WriteShapeObligation := by
  obtain ⟨special, data⟩ := residuals
  intro expressions unrefuted
  exact welcomePEWriteShape_of_lineDataFlagFree expressions unrefuted special
    (data expressions unrefuted)

/-- **The slot-free bundle gives the flag-free one** (conservative direction). -/
theorem welcomePEDispatchResidualsFlagFree_of_slotFree
    (residuals : WelcomePEDispatchResidualsSlotFree) : WelcomePEDispatchResidualsFlagFree := by
  obtain ⟨special, data⟩ := residuals
  exact ⟨special, fun expressions unrefuted =>
    welcomePELm1LineDispatchDataFlagFree_of_slotFree expressions (data expressions unrefuted)⟩

/-- **The obligation from the flag-free components.**  The three special-ALU
writer cases and the phantom provenance are unchanged. -/
theorem welcomePELm1WriteShapeObligation_of_componentsFlagFree
    (phantom : WelcomePELm1PhantomWriterProvenance)
    (plain : WelcomePEPlainWriterDataFlagFree)
    (read : WelcomePEMatrixReadWriterDataSlotFree)
    (float : WelcomePEFloatMAUWriterData) (mau : WelcomePEMatrixMAUWriterData)
    (l1 : WelcomePEL1BMWriterData)
    (msl : WelcomePEMslMsrWriterShapeObligation)
    (relu : WelcomePEFloatReluWriterShapeObligation)
    (block : WelcomePEBlockFloatWriterShapeObligation) :
    WelcomePELm1WriteShapeObligation :=
  welcomePELm1WriteShapeObligation_of_dispatchFlagFree
    ⟨welcomePESpecialALUWriterShapeObligation_of_three msl relu block,
      fun expressions unrefuted =>
        welcomePELm1LineDispatchDataFlagFree_of_components phantom plain read float mau l1
          expressions unrefuted⟩

/-- **The slot-free components give the obligation through the flag-free
reduction.**  This is `welcomePELm1WriteShapeObligation_of_componentsSlotFree`
with the flag equation removed from the plain component. -/
theorem welcomePELm1WriteShapeObligation_of_components_slotFree_viaFlagFree
    (phantom : WelcomePELm1PhantomWriterProvenance)
    (plain : WelcomePEPlainWriterDataSlotFree)
    (read : WelcomePEMatrixReadWriterDataSlotFree)
    (float : WelcomePEFloatMAUWriterData) (mau : WelcomePEMatrixMAUWriterData)
    (l1 : WelcomePEL1BMWriterData)
    (msl : WelcomePEMslMsrWriterShapeObligation)
    (relu : WelcomePEFloatReluWriterShapeObligation)
    (block : WelcomePEBlockFloatWriterShapeObligation) :
    WelcomePELm1WriteShapeObligation :=
  welcomePELm1WriteShapeObligation_of_componentsFlagFree phantom
    (welcomePEPlainWriterData_flagFree_of_slotFree plain) read float mau l1 msl relu block

/-! ## The round-45 witness satisfies the flag-free package

`welcomeMixed_no_plainWriter_flagAgreement` shows that at the round-45 witness
line no plain row satisfies the flag equation: the only plain row has own flag
`false` while the line flag is `true`.  The flag-free package does not mention
the equation at all, and the theorem below checks that it holds at that very
line, so the hypothesis of
`welcomePEWriteShape_of_plainWriter_data_flagFree` is satisfiable on the
counterexample of the flag agreement.  (This is a statement about the flag
equation, not about the old package as a whole: that package could still be
satisfied at the witness through its input-independence disjunct.) -/

/-- **The round-45 witness line satisfies the flag-free plain-writer package.** -/
theorem welcomeFlagAgreementWitness_dataFlagFree :
    WelcomePEPlainWriterDataForFlagFree welcomeFlagAgreementWitnessLine := by
  intro e eMem plain writer
  have mem : e ∈ [welcomeFlagAgreementPlainWitness.toParsed,
      welcomeFlagAgreementInertWitness.toParsed] := by
    simpa [welcomeFlagAgreementWitnessLine] using eMem
  rcases List.mem_cons.mp mem with same | later
  · subst same
    refine ⟨[], [welcomeFlagAgreementInertWitness.toParsed], ?_,
      by simp, ?_, by decide, Or.inl ?_⟩
    · simpa using welcomeFlagAgreementWitness_stageInput
    · intro member
      rw [List.mem_singleton] at member
      rw [member] at plain
      rw [welcomeFlagAgreementWitness_inertNotPlain] at plain
      exact absurd plain (by decide)
    · intro payload sparse isImmediate destination member pair
      exact absurd isImmediate
        (by simp [welcomeFlagAgreementPlainWitness, NormalizedExpr.toParsed])
  · simp only [List.mem_singleton] at later
    subst later
    rw [welcomeFlagAgreementWitness_inertNotPlain] at plain
    exact absurd plain (by decide)

/-- **The row shape of the round-45 witness's plain writer at the line flag**,
obtained from the general flag-free row shape (own flag `false`, line flag
`true`). -/
theorem welcomeFlagAgreementWitness_rowShape_flagFree
    (writes : List PreparedParsedMaskedWrite)
    (slots : ProofsLean.MNCore.Forwarding.Slots) (bars : List (Bool × BitVec 12))
    (prep : prepareParsedIntegerMatrixReadLineExpression welcomeZeroFiles welcomeZeroSlots
      welcomeZeroSlots welcomeZeroMatrixStore welcomeFlagAgreementPlainWitness.toParsed
      welcomeZeroControl true true false = .ok (writes, slots, bars)) :
    Lm1WritesDoubleCopy writes ∨ Lm1WritesNarrow writes :=
  PlainFlagFree.plainRow_lm1_shape_of_linePrep_rowFlagFalse
    welcomeFlagAgreementPlainWitness.toParsed welcomeFlagAgreementWitness_plain
    welcomeFlagAgreementWitness_plainFlag
    (by
      intro payload sparse isImmediate
      exact absurd isImmediate
        (by simp [welcomeFlagAgreementPlainWitness, NormalizedExpr.toParsed]))
    (by decide) true welcomeZeroSlots writes slots bars prep

end ProofsLean.MNCore
