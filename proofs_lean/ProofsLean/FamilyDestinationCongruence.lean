import ProofsLean.ABUnconditional
import ProofsLean.WelcomeMAUShape

/-! # State-general destination congruence for the non-plain producer families

`ProofsLean/PlainALUDestination.lean` proves that two successful plain
integer-ALU cycle runs at **arbitrary** register files with the same mask
registers prepare the same list of destinations.  That is the fact that lets a
zero-state write shape be *transferred* to the non-zero witness input of
`1.a-b`.  Every other producer family needs the same fact before its zero-state
width/narrow shape can be moved to a non-zero input, which is exactly the
`ABNonPlainResidual` gap recorded in `ProofsLean/ABUnconditional.lean` §5.

This module supplies that infrastructure.  It is deliberately stated with the
same hypothesis discipline as the plain-ALU lemma:

* the two states are **arbitrary** register files (no state is fixed to zero),
* the only cross-state hypothesis is the equality of the mask registers (the
  register file every destination lowering and every write-selection resolver
  reads), plus, where the executor itself reads them, the equality of the
  context fields `pe`/`cycle`/`bar0`/`bar1`/`tWord`;
* both runs are assumed to succeed.

## The families

| § | family | executor | status |
|---|---|---|---|
| 2 | `.matrixRead` | `prepareParsedMatrixReadExprCycles` | **closed** (list-returning: same statement form as the plain lemma) |
| 3 | payoff | `1.a-b` line for a single `.matrixRead` row | **closed** (`abPE_matrixRead_narrow_not_correct`) |
| 4 | shared destination writer | `writeParsedMslMsrDestination?` / `writeParsedMAUDestinations?` | **closed** |
| 5 | float MAU | `executeParsedFloatMAUCyclesAtPE` / `executeParsedFloatMAUsAtPE` | closed in canonical form |
| 6 | msl/msr | `executeParsedMslMsrAtPE` | closed in canonical form |
| 7 | float relu | `executeParsedFloatReluAtPE` | closed in canonical form |
| 8 | `.matrixWrite`, `.l2bm` | — | closed (`no PE-register write`) |
| — | block float | `executeParsedBlockFloatAtMAB` | **not closed** (see the note at the end) |
| — | L1BM broadcast | `executeParsedL1ToPEProducer` | **not closed** (per-destination writer only; see the note) |
| — | matrix MAU | `executeParsedMatrixMAUAtMAB` / `executeParsedMatrixMAUAndWrites` | **not closed** (see the note at the end) |

## The shared statement form

For an executor that returns its prepared write list (`.matrixRead`), the
statement is literally the plain-ALU form:

```
(filesA.maskRegisters = filesB.maskRegisters) →
prepare… filesA … = .ok (writesA, …) →
prepare… filesB … = .ok (writesB, …) →
writesA.map (fun w => w.destination) = writesB.map (fun w => w.destination)
```

The other family executors do not return their list: they fold
`writeParsedMslMsrDestination?` over the destinations and commit the result
directly into the state.  For those the statement is the **canonical-destination
form**: a successful run commits a list whose destination map is a pure function
of the expression, the context and the mask registers (and, for a destination
list containing `.bar` entries, of the data-dependent BAR updates — so those
lemmas carry the explicit hypothesis that no destination is a `.bar`, which is
what makes the BAR state constant through the fold).  Two successful runs then
commit lists with the *same* destination map, because both equal the same pure
function.

No `sorry`, no `admit`, no `native_decide`, no new axioms, no existing module is
edited.
-/

namespace ProofsLean.MNCore

set_option maxHeartbeats 4000000
set_option maxRecDepth 40000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open Issue
open PEMemory

/-! ## 1. A few shapes used by every family -/

/-- A destination operand that moves the BAR state (used as the hypothesis that
the BAR state does not move inside a destination fold). -/
def parsedOperandIsBar : ParsedOperand → Bool
  | .bar .. => true
  | _ => false

theorem parsedOperandIsBar_mem (access : Access) (negated extended rounded : Bool)
    (mask : Option ParsedMask) :
    parsedOperandIsBar (.mem access negated extended rounded mask) = false := rfl

theorem parsedOperandIsBar_omr (entry : Fin 256) (mask : Option ParsedMask) :
    parsedOperandIsBar (.omr entry mask) = false := rfl

theorem parsedOperandIsBar_nowrite : parsedOperandIsBar .nowrite = false := rfl

theorem parsedOperandIsBar_bar (lm1 : Bool) (width : Fin 5) (mask : Option ParsedMask) :
    parsedOperandIsBar (.bar lm1 width mask) = true := rfl

/-! ## 2. `.matrixRead`: the executor returns its prepared list

`prepareParsedMatrixReadTargets` turns one cycle's lowered targets into prepared
writes.  The data (`output`) only fills the write's data words; the destination
comes from the target constructor, so the destination list is a pure function of
the target list. -/

/-- The destinations of the prepared writes of a matrix-read target list:
`.memory access` emits one write at `access`, `.noWrite` emits one write with
`none`, and a `.bar` target emits no prepared write. -/
def parsedMatrixReadTargetDestinations :
    List ParsedMatrixReadTarget → List (Option DirectMemoryAccess)
  | [] => []
  | .noWrite :: rest => none :: parsedMatrixReadTargetDestinations rest
  | .memory access _ :: rest => some access :: parsedMatrixReadTargetDestinations rest
  | .bar _ _ :: rest => parsedMatrixReadTargetDestinations rest

/-- **The matrix-read target writer's destinations.**  Whatever the output data
is, the prepared writes' destinations are exactly the target list's
destinations. -/
theorem prepareParsedMatrixReadTargets_destination_map :
    ∀ (targets : List ParsedMatrixReadTarget) (output : IntegerALU.Bus)
      (writes : List PreparedParsedMaskedWrite) (bars : List (Bool × BitVec 12)),
      prepareParsedMatrixReadTargets targets output = .ok (writes, bars) →
      writes.map (fun w => w.destination) = parsedMatrixReadTargetDestinations targets := by
  intro targets
  induction targets with
  | nil =>
      intro output writes bars prepared
      simp [prepareParsedMatrixReadTargets] at prepared
      obtain ⟨rfl, rfl⟩ := prepared
      rfl
  | cons target rest ih =>
      intro output writes bars prepared
      cases target with
      | noWrite =>
          simp only [prepareParsedMatrixReadTargets] at prepared
          cases tail : prepareParsedMatrixReadTargets rest output with
          | failure => simp [tail] at prepared
          | unknown => simp [tail] at prepared
          | ok result =>
              obtain ⟨tailWrites, tailBars⟩ := result
              simp only [tail, StepResult.ok.injEq, Prod.mk.injEq] at prepared
              obtain ⟨rfl, rfl⟩ := prepared
              simp only [List.map_cons, parsedMatrixReadTargetDestinations,
                ih output tailWrites tailBars tail]
      | memory access selection =>
          simp only [prepareParsedMatrixReadTargets] at prepared
          cases tail : prepareParsedMatrixReadTargets rest output with
          | failure => simp [tail] at prepared
          | unknown => simp [tail] at prepared
          | ok result =>
              obtain ⟨tailWrites, tailBars⟩ := result
              simp only [tail, StepResult.ok.injEq, Prod.mk.injEq] at prepared
              obtain ⟨rfl, rfl⟩ := prepared
              simp only [List.map_cons, parsedMatrixReadTargetDestinations,
                ih output tailWrites tailBars tail]
      | bar lm1 selection =>
          simp only [prepareParsedMatrixReadTargets] at prepared
          cases tail : prepareParsedMatrixReadTargets rest output with
          | failure => simp [tail] at prepared
          | unknown => simp [tail] at prepared
          | ok result =>
              obtain ⟨tailWrites, tailBars⟩ := result
              simp only [tail, StepResult.ok.injEq, Prod.mk.injEq] at prepared
              obtain ⟨rfl, rfl⟩ := prepared
              simp only [ih output tailWrites tailBars tail,
                parsedMatrixReadTargetDestinations]

/-- **Inversion of one successful matrix-read cycle.**  A successful cycle
exposes the lowered accesses of the row and the fact that the cycle's prepared
writes have exactly the targets' destinations. -/
theorem prepareParsedMatrixReadCycle_destination_inv
    (files : IntegerRegisterFiles) (slots : ProofsLean.MNCore.Forwarding.Slots)
    (store : ParsedMatrixReadStore) (expression : ParsedExpr)
    (directive : ParsedMaskDirective) (hasSingleLineMask noForward : Bool)
    (context : ParsedIntegerContext)
    (writes : List PreparedParsedMaskedWrite)
    (nextSlots : ProofsLean.MNCore.Forwarding.Slots)
    (bars : List (Bool × BitVec 12))
    (prepared : prepareParsedMatrixReadCycle files slots store expression directive
      hasSingleLineMask noForward context = .ok (writes, nextSlots, bars)) :
    ∃ accesses, ParsedExpr.toDirectMatrixReadAccesses? expression files.maskRegisters
        directive hasSingleLineMask context = some accesses ∧
      writes.map (fun w => w.destination) =
        parsedMatrixReadTargetDestinations accesses.targets := by
  unfold prepareParsedMatrixReadCycle at prepared
  generalize loweredEq : ParsedExpr.toDirectMatrixReadAccesses? expression files.maskRegisters
    directive hasSingleLineMask context = loweredResult at prepared
  cases loweredResult with
  | none => simp [loweredEq] at prepared
  | some accesses =>
      simp only [loweredEq] at prepared
      cases flush : resolveFlushSelection? expression.flush files.maskRegisters context.cycle with
      | none => simp [flush] at prepared
      | some flushSelection =>
          simp only [flush] at prepared
          cases targets : prepareParsedMatrixReadTargets accesses.targets
              (parsedOutputAfterFlush flushSelection
                (parsedMatrixReadBus store accesses context)) with
          | failure => simp [targets] at prepared
          | unknown => simp [targets] at prepared
          | ok result =>
              obtain ⟨doneWrites, doneBars⟩ := result
              simp only [targets, StepResult.ok.injEq, Prod.mk.injEq] at prepared
              obtain ⟨rfl, _, rfl⟩ := prepared
              exact ⟨accesses, rfl,
                prepareParsedMatrixReadTargets_destination_map accesses.targets _ _ _ targets⟩

/-- **State-general destination congruence of one matrix-read cycle.**  Two
successful cycles on arbitrary register files with the same mask registers
prepare the same list of destinations.  The store (the data), the forwarding
slots and the flush selection may differ arbitrarily. -/
theorem prepareParsedMatrixReadCycle_destination_state_general
    (filesA filesB : IntegerRegisterFiles)
    (slotsA slotsB : ProofsLean.MNCore.Forwarding.Slots)
    (storeA storeB : ParsedMatrixReadStore)
    (expression : ParsedExpr) (directive : ParsedMaskDirective)
    (hasSingleLineMask noForward : Bool) (context : ParsedIntegerContext)
    (writesA : List PreparedParsedMaskedWrite)
    (nextSlotsA : ProofsLean.MNCore.Forwarding.Slots)
    (barsA : List (Bool × BitVec 12))
    (writesB : List PreparedParsedMaskedWrite)
    (nextSlotsB : ProofsLean.MNCore.Forwarding.Slots)
    (barsB : List (Bool × BitVec 12))
    (maskEq : filesA.maskRegisters = filesB.maskRegisters)
    (preparedA : prepareParsedMatrixReadCycle filesA slotsA storeA expression directive
      hasSingleLineMask noForward context = .ok (writesA, nextSlotsA, barsA))
    (preparedB : prepareParsedMatrixReadCycle filesB slotsB storeB expression directive
      hasSingleLineMask noForward context = .ok (writesB, nextSlotsB, barsB)) :
    writesA.map (fun w => w.destination) = writesB.map (fun w => w.destination) := by
  unfold prepareParsedMatrixReadCycle at preparedA preparedB
  rw [← maskEq] at preparedB
  cases lowered : ParsedExpr.toDirectMatrixReadAccesses? expression filesA.maskRegisters
      directive hasSingleLineMask context with
  | none => simp [lowered] at preparedA
  | some accesses =>
      simp only [lowered] at preparedA preparedB
      cases flush : resolveFlushSelection? expression.flush filesA.maskRegisters context.cycle with
      | none => simp [flush] at preparedA
      | some flushSelection =>
          simp only [flush] at preparedA preparedB
          cases targetsA : prepareParsedMatrixReadTargets accesses.targets
              (parsedOutputAfterFlush flushSelection
                (parsedMatrixReadBus storeA accesses context)) with
          | failure => simp [targetsA] at preparedA
          | unknown => simp [targetsA] at preparedA
          | ok resultA =>
              obtain ⟨doneWritesA, doneBarsA⟩ := resultA
              simp only [targetsA, StepResult.ok.injEq, Prod.mk.injEq] at preparedA
              obtain ⟨rfl, _, rfl⟩ := preparedA
              cases targetsB : prepareParsedMatrixReadTargets accesses.targets
                  (parsedOutputAfterFlush flushSelection
                    (parsedMatrixReadBus storeB accesses context)) with
              | failure => simp [targetsB] at preparedB
              | unknown => simp [targetsB] at preparedB
              | ok resultB =>
                  obtain ⟨doneWritesB, doneBarsB⟩ := resultB
                  simp only [targetsB, StepResult.ok.injEq, Prod.mk.injEq] at preparedB
                  obtain ⟨rfl, _, rfl⟩ := preparedB
                  rw [prepareParsedMatrixReadTargets_destination_map accesses.targets _ _ _
                        targetsA,
                      prepareParsedMatrixReadTargets_destination_map accesses.targets _ _ _
                        targetsB]

/-- **State-general destination congruence of the four-cycle accumulation.** -/
theorem prepareParsedMatrixReadCycles_destination_state_general
    (filesA filesB : IntegerRegisterFiles)
    (maskEq : filesA.maskRegisters = filesB.maskRegisters)
    (storeA storeB : ParsedMatrixReadStore) (expression : ParsedExpr)
    (directive : ParsedMaskDirective) (hasSingleLineMask noForward : Bool)
    (context : ParsedIntegerContext) :
    ∀ (cycles : List (Fin 4))
      (writesA : List PreparedParsedMaskedWrite)
      (slotsA : ProofsLean.MNCore.Forwarding.Slots)
      (barsA : List (Bool × BitVec 12))
      (writesB : List PreparedParsedMaskedWrite)
      (slotsB : ProofsLean.MNCore.Forwarding.Slots)
      (barsB : List (Bool × BitVec 12))
      (resultA : List PreparedParsedMaskedWrite × ProofsLean.MNCore.Forwarding.Slots ×
        List (Bool × BitVec 12))
      (resultB : List PreparedParsedMaskedWrite × ProofsLean.MNCore.Forwarding.Slots ×
        List (Bool × BitVec 12)),
      writesA.map (fun w => w.destination) = writesB.map (fun w => w.destination) →
      prepareParsedMatrixReadCycles filesA storeA expression directive hasSingleLineMask
        noForward context cycles writesA slotsA barsA = .ok resultA →
      prepareParsedMatrixReadCycles filesB storeB expression directive hasSingleLineMask
        noForward context cycles writesB slotsB barsB = .ok resultB →
      resultA.1.map (fun w => w.destination) =
        resultB.1.map (fun w => w.destination) := by
  intro cycles
  induction cycles with
  | nil =>
      intro writesA slotsA barsA writesB slotsB barsB resultA resultB writesEq preparedA preparedB
      simp only [prepareParsedMatrixReadCycles, StepResult.ok.injEq, Prod.mk.injEq] at preparedA
      simp only [prepareParsedMatrixReadCycles, StepResult.ok.injEq, Prod.mk.injEq] at preparedB
      obtain ⟨rfl, rfl, rfl⟩ := preparedA
      obtain ⟨rfl, rfl, rfl⟩ := preparedB
      exact writesEq
  | cons cycle rest ih =>
      intro writesA slotsA barsA writesB slotsB barsB resultA resultB writesEq preparedA preparedB
      simp only [prepareParsedMatrixReadCycles] at preparedA preparedB
      cases headA : prepareParsedMatrixReadCycle filesA slotsA storeA expression directive
          hasSingleLineMask noForward { context with cycle := cycle } with
      | failure => simp [headA] at preparedA
      | unknown => simp [headA] at preparedA
      | ok cycleResultA =>
          obtain ⟨cycleWritesA, cycleSlotsA, cycleBarsA⟩ := cycleResultA
          simp only [headA] at preparedA
          cases headB : prepareParsedMatrixReadCycle filesB slotsB storeB expression directive
              hasSingleLineMask noForward { context with cycle := cycle } with
          | failure => simp [headB] at preparedB
          | unknown => simp [headB] at preparedB
          | ok cycleResultB =>
              obtain ⟨cycleWritesB, cycleSlotsB, cycleBarsB⟩ := cycleResultB
              simp only [headB] at preparedB
              refine ih (writesA ++ cycleWritesA) cycleSlotsA (barsA ++ cycleBarsA)
                (writesB ++ cycleWritesB) cycleSlotsB (barsB ++ cycleBarsB) resultA resultB ?_
                preparedA preparedB
              rw [List.map_append, List.map_append,
                prepareParsedMatrixReadCycle_destination_state_general filesA filesB
                  slotsA slotsB storeA storeB expression directive hasSingleLineMask
                  noForward { context with cycle := cycle } cycleWritesA cycleSlotsA
                  cycleBarsA cycleWritesB cycleSlotsB cycleBarsB maskEq headA headB,
                writesEq]

/-- **State-general destination congruence of the whole `.matrixRead` row.**
Two successful four-cycle preparations of the same `.matrixRead` expression on
any two register files with the same mask registers prepare the same destination
list.  The matrix store, the forwarding slots and the flush selections may
differ arbitrarily: only `maskRegisters` matters. -/
theorem prepareParsedMatrixReadExprCycles_destination_state_general
    (filesA filesB : IntegerRegisterFiles)
    (initialSlotsA initialSlotsB : ProofsLean.MNCore.Forwarding.Slots)
    (storeA storeB : ParsedMatrixReadStore) (expression : ParsedExpr)
    (directive : ParsedMaskDirective) (hasSingleLineMask noForward : Bool)
    (context : ParsedIntegerContext)
    (writesA : List PreparedParsedMaskedWrite)
    (slotsA : ProofsLean.MNCore.Forwarding.Slots)
    (barsA : List (Bool × BitVec 12))
    (writesB : List PreparedParsedMaskedWrite)
    (slotsB : ProofsLean.MNCore.Forwarding.Slots)
    (barsB : List (Bool × BitVec 12))
    (maskEq : filesA.maskRegisters = filesB.maskRegisters)
    (preparedA : prepareParsedMatrixReadExprCycles filesA initialSlotsA storeA expression
      directive hasSingleLineMask noForward context = .ok (writesA, slotsA, barsA))
    (preparedB : prepareParsedMatrixReadExprCycles filesB initialSlotsB storeB expression
      directive hasSingleLineMask noForward context = .ok (writesB, slotsB, barsB)) :
    writesA.map (fun w => w.destination) = writesB.map (fun w => w.destination) := by
  unfold prepareParsedMatrixReadExprCycles at preparedA preparedB
  exact prepareParsedMatrixReadCycles_destination_state_general filesA filesB maskEq storeA
    storeB expression directive hasSingleLineMask noForward context parsedMatrixReadCycles
    [] initialSlotsA [] [] initialSlotsB [] (writesA, slotsA, barsA) (writesB, slotsB, barsB)
    rfl preparedA preparedB


/-! ## 3. Payoff: the `.matrixRead` narrow branch at a non-zero input

This is the family instance of `ABNonPlainResidual` recorded in
`ProofsLean/ABUnconditional.lean`: a single `.matrixRead` row whose zero-state
prepared list is narrow is refuted at the `A = 1.0, B = 0` witness input.  The
zero-state narrowness is transferred along
`prepareParsedMatrixReadExprCycles_destination_state_general` — the *new* lemma
of §2 — and the value argument is the existing
`ab_not_correct_of_narrowAtOnes`.

The proof also shows the line-level pattern the other families need: a
successful sealed step at an **arbitrary** input exposes the executor's own
prepared list (`matrixReadSingleton_prepared`), so the transfer applies between
the zero input and the witness input. -/

/-- A `.matrixRead` row is an integer-stage input: it is not a `.l2bm`, matrix
write, L1 write/gather/reduce/broadcast, matrix-MAU, float-MAU, msl/msr,
block-float or relu producer. -/
theorem matrixRead_stageInput (expression : ParsedExpr) (precision : ParsedPrecision)
    (readOp : expression.op = .matrixRead precision) :
    parsedExprIsIntegerMatrixReadStageInput expression = true := by
  cases expression with
  | mk op sources destinations flush text =>
    simp only at readOp
    subst readOp
    simp [parsedExprIsIntegerMatrixReadStageInput, parsedExprWaitTag?,
      parsedExprIsL2BMProducer, parsedExprIsMatrixWriteProducer,
      parsedExprIsL1MwriteProducer, parsedExprIsL1GatherProducer,
      parsedExprIsL1ReduceProducer, parsedExprIsL1ToPEProducer,
      parsedExprIsMatrixMAUProducer, parsedExprIsSupportedFloatMAUProducer,
      parsedExprIsMslMsrProducer, parsedExprIsBlockFloatProducer,
      parsedExprIsFloatReluProducer]

theorem matrixRead_outerFilter (expression : ParsedExpr) (precision : ParsedPrecision)
    (readOp : expression.op = .matrixRead precision) :
    ([expression].filter (fun item =>
      !parsedExprIsL2BMProducer item && !parsedExprIsMslMsrProducer item &&
        !parsedExprIsMatrixMAUProducer item && !parsedExprIsBlockFloatProducer item &&
        !parsedExprIsFloatReluProducer item)) = [expression] := by
  cases expression with
  | mk op sources destinations flush text =>
    simp only at readOp
    subst readOp
    simp [parsedExprIsL2BMProducer, parsedExprIsMslMsrProducer,
      parsedExprIsMatrixMAUProducer, parsedExprIsBlockFloatProducer,
      parsedExprIsFloatReluProducer]

/-- **A single `.matrixRead` row runs only through the integer stage.**  The six
non-integer stages are the identity (their producer filters are empty), so the
line's PE registers are the per-PE walk's PE registers, and the walk runs on the
matrix-read row alone. -/
theorem executeIntegerProducerInstructionLine_pe_matrixRead_exists
    (expression : NormalizedExpr) (state next : State)
    (precision : ParsedPrecision) (readOp : expression.toParsed.op = .matrixRead precision)
    (executed : executeIntegerProducerInstructionLine (.pe [expression]) state = .ok next) :
    ∃ nextPEs,
      executeIntegerProducerLineAtPEs [expression.toParsed] (List.finRange 4096) state =
        .ok nextPEs ∧
      next.peRegisters = nextPEs.peRegisters := by
  obtain ⟨accepted, waits, unsupported, supported⟩ :=
    executeIntegerProducerInstructionLine_pe_conditions [expression] state next executed
  obtain ⟨nextPEs, nextMsl, nextRelu, nextBlockFloat, afterMatrix, nextShared, nextBroadcast,
    walkExecuted, mslExecuted, reluExecuted, blockExecuted, matrixExecuted, sharedExecuted,
    l1Executed, nextEq⟩ :=
    executeIntegerProducerInstructionLine_pe_stages_exists [expression] state next accepted
      waits unsupported supported executed
  have outer : ([expression].map NormalizedExpr.toParsed).filter (fun item =>
      !parsedExprIsL2BMProducer item && !parsedExprIsMslMsrProducer item &&
        !parsedExprIsMatrixMAUProducer item && !parsedExprIsBlockFloatProducer item &&
        !parsedExprIsFloatReluProducer item) = [expression.toParsed] := by
    simpa using matrixRead_outerFilter expression.toParsed precision readOp
  rw [outer] at walkExecuted
  have parsedRead : expression.toParsed.op = .matrixRead precision := readOp
  have mslNil : ([expression].map NormalizedExpr.toParsed).filter
      parsedExprIsMslMsrProducer = [] := by
    simp [parsedRead, parsedExprIsMslMsrProducer]
  have reluNil : ([expression].map NormalizedExpr.toParsed).filter
      parsedExprIsFloatReluProducer = [] := by
    simp [parsedRead, parsedExprIsFloatReluProducer]
  have blockNil : ([expression].map NormalizedExpr.toParsed).filter
      parsedExprIsBlockFloatProducer = [] := by
    simp [parsedRead, parsedExprIsBlockFloatProducer]
  have mauNil : ([expression].map NormalizedExpr.toParsed).filter
      parsedExprIsMatrixMAUProducer = [] := by
    simp [parsedRead, parsedExprIsMatrixMAUProducer]
  have writeAny : ([expression].map NormalizedExpr.toParsed).any
      parsedExprIsMatrixWriteProducer = false := by
    simp [parsedRead, parsedExprIsMatrixWriteProducer]
  have l1Nil : ([expression].map NormalizedExpr.toParsed).filter
      parsedExprIsL1ToPEProducer = [] := by
    simp [parsedRead, parsedExprIsL1ToPEProducer]
  have mslId : executeParsedMslMsrProducers state nextPEs
      ([expression].map NormalizedExpr.toParsed)
      ([expression].any (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed))
      ([expression].any (parsedExprHasSingleLineWriteMask ∘ NormalizedExpr.toParsed)) = .ok nextPEs :=
    executeParsedMslMsrProducers_eq_self state nextPEs _ _ _ mslNil
  have nextMslEq : nextMsl = nextPEs := by
    rw [mslId] at mslExecuted
    exact (StepResult.ok.inj mslExecuted).symm
  have reluId : executeParsedFloatReluProducers state nextMsl
      ([expression].map NormalizedExpr.toParsed)
      ([expression].any (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed))
      ([expression].any (parsedExprHasSingleLineWriteMask ∘ NormalizedExpr.toParsed)) = .ok nextMsl :=
    executeParsedFloatReluProducers_eq_self state nextMsl _ _ _ reluNil
  have nextReluEq : nextRelu = nextMsl := by
    rw [reluId] at reluExecuted
    exact (StepResult.ok.inj reluExecuted).symm
  have blockId : executeParsedBlockFloatProducer state nextRelu
      ([expression].map NormalizedExpr.toParsed)
      ([expression].any (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed))
      ([expression].any (parsedExprHasSingleLineWriteMask ∘ NormalizedExpr.toParsed)) = .ok nextRelu :=
    executeParsedBlockFloatProducer_eq_self state nextRelu _ _ _ blockNil
  have nextBlockEq : nextBlockFloat = nextRelu := by
    rw [blockId] at blockExecuted
    exact (StepResult.ok.inj blockExecuted).symm
  have matrixId : executeParsedMatrixMAUAndWrites state nextBlockFloat
      ([expression].map NormalizedExpr.toParsed)
      ([expression].any (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed))
      ([expression].any (parsedExprHasSingleLineWriteMask ∘ NormalizedExpr.toParsed)) =
      .ok nextBlockFloat :=
    executeParsedMatrixMAUAndWrites_eq_self state nextBlockFloat _ _ _ mauNil writeAny
  have afterMatrixEq : afterMatrix = nextBlockFloat := by
    rw [matrixId] at matrixExecuted
    exact (StepResult.ok.inj matrixExecuted).symm
  have sharedFrame : nextShared.peRegisters = afterMatrix.peRegisters :=
    executeParsedSharedBlockProducers_peRegisters state afterMatrix nextShared _ _ sharedExecuted
  have l1Id : executeParsedL1ToPEProducers state nextShared
      ([expression].map NormalizedExpr.toParsed)
      ([expression].any (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed))
      ([expression].any (parsedExprHasSingleLineWriteMask ∘ NormalizedExpr.toParsed))
      (parsedL1ToPEPrecedesOMRWriter ([expression].map NormalizedExpr.toParsed)) =
      .ok nextShared :=
    executeParsedL1ToPEProducers_eq_self state nextShared _ _ _ _ l1Nil
  have nextBroadcastEq : nextBroadcast = nextShared := by
    rw [l1Id] at l1Executed
    exact (StepResult.ok.inj l1Executed).symm
  refine ⟨nextPEs, walkExecuted, ?_⟩
  have registersEq : next.peRegisters = nextBroadcast.peRegisters := by
    rw [nextEq]
  rw [registersEq, nextBroadcastEq, sharedFrame, afterMatrixEq, nextBlockEq, nextReluEq,
    nextMslEq]

/-- The identity case analysis on a triple-valued `StepResult` (used when a
definition re-wraps an already computed step result). -/
theorem stepResult_match_triple_self {α β γ : Type}
    (result : ProofsLean.StepResult (α × β × γ)) :
    (match result with
      | .failure => .failure
      | .unknown => .unknown
      | .ok (first, second, third) => .ok (first, second, third)) = result := by
  cases result with
  | failure => rfl
  | unknown => rfl
  | ok value =>
      obtain ⟨first, second, third⟩ := value
      rfl

/-- The identity case analysis on a `StepResult`. -/
theorem stepResult_match_self {α : Type} (result : ProofsLean.StepResult α) :
    (match result with
      | .failure => .failure
      | .unknown => .unknown
      | .ok value => .ok value) = result := by
  cases result <;> rfl

/-- **A successful single `.matrixRead` row exposes the row preparation.**  The
singleton line preparation is the row's own `prepareParsedMatrixReadExprCycles`,
for every state and every register file. -/
theorem prepareParsedIntegerMatrixReadLineCycles_singleton_matrixRead_inv
    (files : IntegerRegisterFiles) (oldSlots : ProofsLean.MNCore.Forwarding.Slots)
    (store : ParsedMatrixReadStore) (expression : ParsedExpr)
    (control : ParsedMaskExecutionControl) (reduced : Bool)
    (precision : ParsedPrecision) (readOp : expression.op = .matrixRead precision)
    (writes : List PreparedParsedMaskedWrite)
    (slots : ProofsLean.MNCore.Forwarding.Slots)
    (bars : List (Bool × BitVec 12))
    (prepared : prepareParsedIntegerMatrixReadLineCycles files oldSlots store [expression]
      control reduced = .ok (writes, slots, bars)) :
    prepareParsedMatrixReadExprCycles files oldSlots store expression control.directive
      (parsedExprHasSingleLineWriteMask expression)
      (match expression.op with | .noforward => true | _ => false) control.context =
      .ok (writes, slots, bars) := by
  rw [prepareParsedIntegerMatrixReadLineCycles.eq_1] at prepared
  simp only [List.any_cons, List.any_nil, Bool.or_false] at prepared
  rw [prepareParsedIntegerMatrixReadLineExpressions.eq_2] at prepared
  generalize headEq : prepareParsedIntegerMatrixReadLineExpression files oldSlots oldSlots store
    expression control (parsedExprHasSingleLineWriteMask expression)
    (match expression.op with | .noforward => true | _ => false) reduced = headResult at prepared
  cases headResult with
  | failure => simp at prepared
  | unknown => simp at prepared
  | ok value =>
      obtain ⟨expressionWrites, expressionSlots, expressionBarUpdates⟩ := value
      dsimp only at prepared
      rw [prepareParsedIntegerMatrixReadLineExpressions.eq_1] at prepared
      simp only [List.nil_append, StepResult.ok.injEq, Prod.mk.injEq] at prepared
      obtain ⟨rfl, rfl, rfl⟩ := prepared
      rw [prepareParsedIntegerMatrixReadLineExpression.eq_1] at headEq
      rw [readOp] at headEq
      generalize rowEq : prepareParsedMatrixReadExprCycles files oldSlots store expression
        control.directive (parsedExprHasSingleLineWriteMask expression) false control.context =
        rowResult at headEq
      cases rowResult with
      | failure => simp at headEq
      | unknown => simp at headEq
      | ok rowValue =>
          obtain ⟨rowWrites, rowSlots, rowBars⟩ := rowValue
          simp only [StepResult.ok.injEq, Prod.mk.injEq] at headEq
          obtain ⟨rfl, rfl, rfl⟩ := headEq
          simpa [readOp] using rowEq

/-- **The line-level extraction for a single `.matrixRead` row at an arbitrary
input.**  A successful sealed step commits the executor's own
`prepareParsedMatrixReadExprCycles` list at that input's PE-0 register file. -/
theorem matrixReadSingleton_prepared
    (expression : NormalizedExpr) (input : ABInput) (next : State)
    (precision : ParsedPrecision) (readOp : expression.toParsed.op = .matrixRead precision)
    (step : abSealedMachine.step (.pe [expression]) (abInitialState input) = some next) :
    ∃ (writes : List PreparedParsedMaskedWrite)
      (slots : ProofsLean.MNCore.Forwarding.Slots)
      (bars : List (Bool × BitVec 12)),
      prepareParsedMatrixReadExprCycles ((abInitialState input).peRegisters abPE)
        (stateForwardingSlots (abInitialState input) abPE)
        ((abInitialState input).matrixRegisters
          (ParsedIntegerContext.ofLinearIndex abPE).group
          (ParsedIntegerContext.ofLinearIndex abPE).l2b
          (ParsedIntegerContext.ofLinearIndex abPE).l1b)
        expression.toParsed (abInitialState input).maskDirective
        (parsedExprHasSingleLineWriteMask expression.toParsed) false
        (parsedPEHazardControl (abInitialState input) abPE).context =
        .ok (writes, slots, bars) ∧
      next.peRegisters abPE =
        commitParsedMaskedWrites ((abInitialState input).peRegisters abPE) writes := by
  have executed : executeNormalizedLine (InstructionLine.pe [expression]).toNormalizedLine
      (abInitialState input) = .ok next := by
    cases h : executeNormalizedLine (InstructionLine.pe [expression]).toNormalizedLine
        (abInitialState input) with
    | ok result => simpa [abSealedMachine, h] using step
    | failure => simp [abSealedMachine, h] at step
    | unknown => simp [abSealedMachine, h] at step
  have lineExecuted : executeIntegerProducerInstructionLine (.pe [expression])
      (abInitialState input) = .ok next := by
    unfold executeNormalizedLine at executed
    simp only [Issue.InstructionLine.toNormalizedLine, NormalizedLine.toInstruction?] at executed
    exact executed
  obtain ⟨nextPEs, walk, registersEq⟩ :=
    executeIntegerProducerInstructionLine_pe_matrixRead_exists expression
      (abInitialState input) next precision readOp lineExecuted
  obtain ⟨split, absent⟩ := plusTwoFinRange_split
  rw [split] at walk
  have floatEmpty : ([expression.toParsed].filter
      parsedExprIsSupportedFloatMAUProducer) = [] := by
    simp [readOp, parsedExprIsSupportedFloatMAUProducer]
  obtain ⟨prepared, prepWelcome, committed⟩ :=
    executeIntegerProducerLineAtPEs_zero_commit_list [expression.toParsed]
      ((List.finRange 4095).map Fin.succ) (abInitialState input) nextPEs absent floatEmpty walk
  obtain ⟨writes, slots, bars⟩ := prepared
  have stage : [expression.toParsed].filter parsedExprIsIntegerMatrixReadStageInput =
      [expression.toParsed] := by
    simp [matrixRead_stageInput expression.toParsed precision readOp]
  rw [stage] at prepWelcome
  have readPrep := prepareParsedIntegerMatrixReadLineCycles_singleton_matrixRead_inv
    ((abInitialState input).peRegisters abPE)
    (stateForwardingSlots (abInitialState input) abPE)
    ((abInitialState input).matrixRegisters
      (ParsedIntegerContext.ofLinearIndex abPE).group
      (ParsedIntegerContext.ofLinearIndex abPE).l2b
      (ParsedIntegerContext.ofLinearIndex abPE).l1b)
    expression.toParsed
    { directive := (abInitialState input).maskDirective
      context :=
        { (ParsedIntegerContext.ofLinearIndex abPE) with
          bar0 := ((abInitialState input).peContext abPE).bar0
          bar1 := ((abInitialState input).peContext abPE).bar1
          tWord := ((abInitialState input).peContext abPE).tWord }
      elapsedWords := (abInitialState input).hazardClock } false
    precision readOp writes slots bars prepWelcome
  refine ⟨writes, slots, bars, ?_, ?_⟩
  · simpa [parsedPEHazardControl, readOp] using readPrep
  · rw [registersEq]
    exact committed

/-- **The `.matrixRead` narrow branch, transferred to the witness input.**
If a single `.matrixRead` row's zero-state preparation list is narrow, then the
row is incorrect at `A = 1.0, B = 0`: the destinations transfer along
`prepareParsedMatrixReadExprCycles_destination_state_general`, four two-word
windows cover at most eight of the sixteen observed words, and an uncovered word
keeps the initial `0` while the target is `0x3F800000`. -/
theorem abPE_matrixRead_narrow_not_correct
    (expression : NormalizedExpr) (nextZero : State)
    (precision : ParsedPrecision) (readOp : expression.toParsed.op = .matrixRead precision)
    (stepZero : abSealedMachine.step (.pe [expression]) (abInitialState abZeroInput) =
      some nextZero)
    (narrowZero : ∀ (writes : List PreparedParsedMaskedWrite)
      (slots : ProofsLean.MNCore.Forwarding.Slots)
      (bars : List (Bool × BitVec 12)),
      prepareParsedMatrixReadExprCycles welcomeZeroFiles welcomeZeroSlots
        welcomeZeroMatrixStore expression.toParsed welcomeZeroControl.directive
        (parsedExprHasSingleLineWriteMask expression.toParsed) false
        welcomeZeroControl.context = .ok (writes, slots, bars) →
      Lm1WritesNarrow writes) :
    ¬ ProofsLean.Correct abSealedMachine abSpec
      ([InstructionLine.pe [expression]] : List InstructionLine) := by
  obtain ⟨writes0, slots0, bars0, prep0, _commit0⟩ :=
    matrixReadSingleton_prepared expression abZeroInput nextZero precision readOp stepZero
  have prep0' : prepareParsedMatrixReadExprCycles welcomeZeroFiles welcomeZeroSlots
      welcomeZeroMatrixStore expression.toParsed welcomeZeroControl.directive
      (parsedExprHasSingleLineWriteMask expression.toParsed) false
      welcomeZeroControl.context = .ok (writes0, slots0, bars0) := by
    rw [abZeroInput_initialState] at prep0
    exact prep0
  have narrow0 := narrowZero writes0 slots0 bars0 prep0'
  refine ab_not_correct_of_narrowAtOnes [expression] ?_
  intro next stepLeft
  obtain ⟨writesL, slotsL, barsL, prepL, commitL⟩ :=
    matrixReadSingleton_prepared expression abOneLeftInput next precision readOp stepLeft
  have controlEq : welcomeZeroControl =
      parsedPEHazardControl (abInitialState abOneLeftInput) abPE := by
    unfold welcomeZeroControl parsedPEHazardControl abInitialState welcomeInitialState
    rfl
  have prep0'' : prepareParsedMatrixReadExprCycles welcomeZeroFiles welcomeZeroSlots
      welcomeZeroMatrixStore expression.toParsed
      (parsedPEHazardControl (abInitialState abOneLeftInput) abPE).directive
      (parsedExprHasSingleLineWriteMask expression.toParsed) false
      (parsedPEHazardControl (abInitialState abOneLeftInput) abPE).context =
      .ok (writes0, slots0, bars0) := by
    rw [← controlEq]
    exact prep0'
  have mapEq := prepareParsedMatrixReadExprCycles_destination_state_general
    welcomeZeroFiles ((abInitialState abOneLeftInput).peRegisters abPE)
    welcomeZeroSlots (stateForwardingSlots (abInitialState abOneLeftInput) abPE)
    welcomeZeroMatrixStore
    ((abInitialState abOneLeftInput).matrixRegisters
      (ParsedIntegerContext.ofLinearIndex abPE).group
      (ParsedIntegerContext.ofLinearIndex abPE).l2b
      (ParsedIntegerContext.ofLinearIndex abPE).l1b)
    expression.toParsed
    (parsedPEHazardControl (abInitialState abOneLeftInput) abPE).directive
    (parsedExprHasSingleLineWriteMask expression.toParsed) false
    (parsedPEHazardControl (abInitialState abOneLeftInput) abPE).context
    writes0 slots0 bars0 writesL slotsL barsL rfl prep0'' prepL
  have narrowL : Lm1WritesNarrow writesL :=
    lm1WritesNarrow_of_destination_map_eq writesL writes0 mapEq.symm narrow0
  obtain ⟨windows, covers, bound, sizes⟩ := narrowL
  exact ⟨writesL, windows, commitL, covers, bound, sizes⟩

/-- **The same branch from the width kernel.**  If the row is a `.matrixRead`
row with a single `.matrix` source, no duplicated write banks and a statically
non-`.double` `.lm1` destination width, the existing width/count kernel
(`prepareParsedMatrixReadExprCycles_zeroShape`) supplies the zero-state
narrowness, so the row is refuted with no shape hypothesis. -/
theorem abPE_matrixRead_not_correct_of_staticWidth
    (expression : NormalizedExpr) (nextZero : State)
    (precision : ParsedPrecision) (sideY : Bool) (width : Fin 5) (row : Fin (2 ^ 32))
    (staticW : PEMemory.Width)
    (readOp : expression.toParsed.op = .matrixRead precision)
    (sources : expression.toParsed.sources = [.matrix sideY width (some row)])
    (nodup : (expression.toParsed.toIssueExpr 0).writeBanks.Nodup)
    (staticWidth : ∀ (d : ParsedOperand), d ∈ expression.toParsed.destinations →
      ∀ v : PEMemory.Width, ParsedOperand.directDestinationBankWidth? d =
        some (PEMemory.Bank.lm1, v) → v = staticW)
    (notDouble : staticW ≠ PEMemory.Width.double)
    (stepZero : abSealedMachine.step (.pe [expression]) (abInitialState abZeroInput) =
      some nextZero) :
    ¬ ProofsLean.Correct abSealedMachine abSpec
      ([InstructionLine.pe [expression]] : List InstructionLine) := by
  refine abPE_matrixRead_narrow_not_correct expression nextZero precision readOp stepZero ?_
  intro writes slots bars prepared
  obtain ⟨facts, count⟩ := prepareParsedMatrixReadExprCycles_lm1Facts expression.toParsed
    precision sideY width row readOp sources welcomeZeroControl.directive
    (parsedExprHasSingleLineWriteMask expression.toParsed) false welcomeZeroSlots
    welcomeZeroControl.context staticW nodup staticWidth writes slots bars prepared
  exact lm1WriteFacts_narrow writes staticW facts notDouble count

/-- The lines this section closes: a single `.matrixRead` row whose zero-state
prepared list is narrow. -/
def ABMatrixReadNarrowClosed (expressions : List NormalizedExpr) : Prop :=
  ∃ (expression : NormalizedExpr) (precision : ParsedPrecision),
    expressions = [expression] ∧ expression.toParsed.op = .matrixRead precision ∧
      ∀ (writes : List PreparedParsedMaskedWrite)
        (slots : ProofsLean.MNCore.Forwarding.Slots)
        (bars : List (Bool × BitVec 12)),
        prepareParsedMatrixReadExprCycles welcomeZeroFiles welcomeZeroSlots
          welcomeZeroMatrixStore expression.toParsed welcomeZeroControl.directive
          (parsedExprHasSingleLineWriteMask expression.toParsed) false
          welcomeZeroControl.context = .ok (writes, slots, bars) →
        Lm1WritesNarrow writes

/-- **The `.matrixRead` family instance of the residual.**  Every unrefuted line
that is a single `.matrixRead` row with a narrow zero-state write list is
refuted — the `ABNonPlainResidual` conclusion for that family. -/
theorem abPE_not_correct_of_matrixReadNarrowClosed
    (expressions : List NormalizedExpr) (unrefuted : AbPEUnrefuted expressions)
    (closed : ABMatrixReadNarrowClosed expressions) :
    ¬ ProofsLean.Correct abSealedMachine abSpec
      ([InstructionLine.pe expressions] : List InstructionLine) := by
  obtain ⟨expression, precision, rfl, readOp, narrow⟩ := closed
  cases stepZero : abSealedMachine.step (.pe [expression]) (abInitialState abZeroInput) with
  | none => exact ab_not_correct_of_step_none _ _ stepZero
  | some nextZero =>
      exact abPE_matrixRead_narrow_not_correct expression nextZero precision readOp
        stepZero narrow

/-- **`ABNonPlainResidual` decomposes along the `.matrixRead` family.**  If every
other non-plain line is refuted, then `ABNonPlainResidual` holds *provided only*
the `.matrixRead` rows with narrow zero-state lists, which §3 proves.  This is
the exact plug-in point of the new congruence lemma for this family; the same
decomposition is available for the other families of §4–§10 with their own
`closed` predicate. -/
theorem abNonPlainResidual_of_matrixReadFamily
    (rest : ∀ expressions : List NormalizedExpr, AbPEUnrefuted expressions →
      ¬ ABPlainLine expressions → ¬ ABMatrixReadNarrowClosed expressions →
      ¬ ProofsLean.Correct abSealedMachine abSpec
        ([InstructionLine.pe expressions] : List InstructionLine)) :
    ABNonPlainResidual := by
  intro expressions unrefuted notPlain
  by_cases closed : ABMatrixReadNarrowClosed expressions
  · exact abPE_not_correct_of_matrixReadNarrowClosed expressions unrefuted closed
  · exact rest expressions unrefuted notPlain closed


/-! ## 4. The shared destination writer of the MAU/msl/relu/block-float families

Those executors do not return a prepared list: they fold
`writeParsedMslMsrDestination?` over the expression's destinations and commit
the result directly into the state.  The per-step writer's **destination** is
never data-dependent: for a `.mem` destination it is the resolved direct-memory
access (a function of the operand and the context only), for an `.omr`
destination it is `none` (the write updates the mask register file instead), and
`.bar`/`.nowrite` destinations emit no prepared write at all.  Only the write's
data and selection depend on the state and on the bus.

So the whole fold's destination list is a pure function of the destinations, the
context and the initial `bar0`/`bar1` — provided no destination is a `.bar`
(whose data-dependent BAR update would move the address base for later
destinations). -/

/-- The canonical destination of one `writeParsedMslMsrDestination?` step. -/
def parsedStepDestination (destination : ParsedOperand) (pe cycle : Fin 4)
    (bar0 bar1 : BitVec 12) (tWord : BitVec 32) : Option DirectMemoryAccess :=
  match destination with
  | .mem .. => ParsedOperand.toDirectMemoryDestination? destination pe cycle bar0 bar1 tWord
  | _ => none

/-- The canonical destination **list** of one `writeParsedMslMsrDestination?`
step: a successful `.mem` destination emits one prepared write at the resolved
access, an `.omr` destination emits one prepared write with `none` (the mask
register update is not a memory write), and `.bar`/`.nowrite` emit no prepared
write. -/
def parsedStepDestinations (destination : ParsedOperand) (pe cycle : Fin 4)
    (bar0 bar1 : BitVec 12) (tWord : BitVec 32) : List (Option DirectMemoryAccess) :=
  match destination with
  | .mem .. =>
      match ParsedOperand.toDirectMemoryDestination? destination pe cycle bar0 bar1 tWord with
      | some access => [some access]
      | none => []
  | .omr .. => [none]
  | _ => []

theorem parsedStepDestinations_omr (entry : Fin 256) (mask : Option ParsedMask)
    (pe cycle : Fin 4) (bar0 bar1 : BitVec 12) (tWord : BitVec 32) :
    parsedStepDestinations (.omr entry mask) pe cycle bar0 bar1 tWord = [none] := rfl

theorem parsedStepDestinations_mem (access : Access) (negated extended rounded : Bool)
    (mask : Option ParsedMask) (pe cycle : Fin 4) (bar0 bar1 : BitVec 12) (tWord : BitVec 32) :
    parsedStepDestinations (.mem access negated extended rounded mask) pe cycle bar0 bar1 tWord =
      match ParsedOperand.toDirectMemoryDestination?
        (.mem access negated extended rounded mask) pe cycle bar0 bar1 tWord with
      | some destination => [some destination]
      | none => [] := rfl

theorem parsedStepDestinations_nowrite (pe cycle : Fin 4) (bar0 bar1 : BitVec 12)
    (tWord : BitVec 32) :
    parsedStepDestinations .nowrite pe cycle bar0 bar1 tWord = [] := rfl

theorem parsedStepDestinations_bar (lm1 : Bool) (width : Fin 5) (mask : Option ParsedMask)
    (pe cycle : Fin 4) (bar0 bar1 : BitVec 12) (tWord : BitVec 32) :
    parsedStepDestinations (.bar lm1 width mask) pe cycle bar0 bar1 tWord = [] := rfl

/-- **The per-step destination canonical form.**  A successful
`writeParsedMslMsrDestination?` call commits a list whose destination map is the
canonical step list — independent of the register file, the bus, the flags and
the mask state. -/
theorem writeParsedMslMsrDestination?_destinations
    (files : IntegerRegisterFiles) (destination : ParsedOperand)
    (context : ParsedIntegerContext) (output : IntegerALU.Bus) (flags : BitVec 4)
    (cycle : Fin 4) (directive : ParsedMaskDirective) (hasSingleLineMask : Bool)
    (write : ParsedMslMsrDestinationWrite)
    (lowered : writeParsedMslMsrDestination? files destination context output flags cycle
      directive hasSingleLineMask = some write) :
    ∃ writes, write.files = commitParsedMaskedWrites files writes ∧
      writes.map (fun w => w.destination) =
        parsedStepDestinations destination context.pe cycle context.bar0 context.bar1
          context.tWord := by
  cases destination with
  | mem access negated extended rounded mask =>
      obtain ⟨resolved, selection, resolvedEq, commitEq⟩ :=
        writeParsedMslMsrDestination?_mem_shape files access negated extended rounded mask
          context output flags cycle directive hasSingleLineMask write lowered
      refine ⟨[⟨some resolved, none, PEMemory.unpackALUBus output, selection⟩],
        commitEq.symm, ?_⟩
      simp [parsedStepDestinations, resolvedEq]
  | omr entry mask =>
      simp only [writeParsedMslMsrDestination?] at lowered
      cases h : ParsedOperand.toMaskRegisterEntry? (.omr entry mask) with
      | none => simp [h] at lowered
      | some found =>
          cases h2 : ParsedOperand.resolveOmrWriteSelection? (.omr entry mask)
              files.maskRegisters cycle directive hasSingleLineMask with
          | none => simp [h, h2] at lowered
          | some selection =>
              simp [h, h2] at lowered
              refine ⟨[⟨none, some (found, cycle, flags), PEMemory.unpackALUBus output,
                ⟨selection, false⟩⟩], ?_, ?_⟩
              · rw [← lowered]
                simp [commitParsedMaskedWrites]
              · rw [parsedStepDestinations_omr]
                simp
  | bar lm1 width mask =>
      simp only [writeParsedMslMsrDestination?] at lowered
      cases h : ParsedOperand.resolveMemoryWriteSelection? (.bar lm1 width mask)
          (if lm1 = true then PEMemory.Bank.lm1 else PEMemory.Bank.lm0) files.maskRegisters
          cycle directive hasSingleLineMask with
      | none => simp [h] at lowered
      | some selection =>
          simp [h] at lowered
          refine ⟨[], ?_, ?_⟩
          · rw [← lowered]
            simp [commitParsedMaskedWrites]
          · rw [parsedStepDestinations_bar]
            simp
  | nowrite =>
      simp only [writeParsedMslMsrDestination?] at lowered
      refine ⟨[], ?_, ?_⟩
      · rw [← Option.some.inj lowered]
        simp [commitParsedMaskedWrites]
      · rw [parsedStepDestinations_nowrite]
        simp
  | forward kind negated extended rounded => simp [writeParsedMslMsrDestination?] at lowered
  | fixed kind => simp [writeParsedMslMsrDestination?] at lowered
  | matrix side width row => simp [writeParsedMslMsrDestination?] at lowered
  | l1bm width address => simp [writeParsedMslMsrDestination?] at lowered
  | l2bm address l2b => simp [writeParsedMslMsrDestination?] at lowered
  | dar address => simp [writeParsedMslMsrDestination?] at lowered

/-- A non-`.bar` destination never moves the BAR state. -/
theorem writeParsedMslMsrDestination?_barUpdate_none_of_not_bar
    (files : IntegerRegisterFiles) (destination : ParsedOperand)
    (context : ParsedIntegerContext) (output : IntegerALU.Bus) (flags : BitVec 4)
    (cycle : Fin 4) (directive : ParsedMaskDirective) (hasSingleLineMask : Bool)
    (write : ParsedMslMsrDestinationWrite)
    (notBar : parsedOperandIsBar destination = false)
    (lowered : writeParsedMslMsrDestination? files destination context output flags cycle
      directive hasSingleLineMask = some write) :
    write.barUpdate = none := by
  cases destination with
  | mem access negated extended rounded mask =>
      simp only [writeParsedMslMsrDestination?] at lowered
      cases h : ParsedOperand.toDirectMemoryDestination?
          (.mem access negated extended rounded mask) context.pe cycle context.bar0
          context.bar1 context.tWord with
      | none => simp [h] at lowered
      | some resolved =>
          cases h2 : ParsedOperand.resolveMemoryWriteSelection?
              (.mem access negated extended rounded mask) resolved.bank files.maskRegisters
              cycle directive hasSingleLineMask with
          | none => simp [h, h2] at lowered
          | some selection =>
              simp [h, h2] at lowered
              cases lowered
              rfl
  | omr entry mask =>
      simp only [writeParsedMslMsrDestination?] at lowered
      cases h : ParsedOperand.toMaskRegisterEntry? (.omr entry mask) with
      | none => simp [h] at lowered
      | some found =>
          cases h2 : ParsedOperand.resolveOmrWriteSelection? (.omr entry mask)
              files.maskRegisters cycle directive hasSingleLineMask with
          | none => simp [h, h2] at lowered
          | some selection =>
              simp [h, h2] at lowered
              cases lowered
              rfl
  | nowrite =>
      simp only [writeParsedMslMsrDestination?] at lowered
      obtain rfl := Option.some.inj lowered
      rfl
  | bar lm1 width mask => simp [parsedOperandIsBar] at notBar
  | forward kind negated extended rounded => simp [writeParsedMslMsrDestination?] at lowered
  | fixed kind => simp [writeParsedMslMsrDestination?] at lowered
  | matrix side width row => simp [writeParsedMslMsrDestination?] at lowered
  | l1bm width address => simp [writeParsedMslMsrDestination?] at lowered
  | l2bm address l2b => simp [writeParsedMslMsrDestination?] at lowered
  | dar address => simp [writeParsedMslMsrDestination?] at lowered

/-- The monadic one-step transition of a destination fold. -/
def parsedDestinationStep (files : IntegerRegisterFiles) (destination : ParsedOperand)
    (context : ParsedIntegerContext) (output : IntegerALU.Bus) (flags : BitVec 4)
    (cycle : Fin 4) (directive : ParsedMaskDirective) (hasSingleLineMask : Bool) :
    Option (IntegerRegisterFiles × BitVec 12 × BitVec 12) :=
  match writeParsedMslMsrDestination? files destination context output flags cycle directive
      hasSingleLineMask with
  | none => none
  | some write =>
      some (write.files,
        (match write.barUpdate with
          | some (false, value) => value
          | _ => context.bar0),
        (match write.barUpdate with
          | some (true, value) => value
          | _ => context.bar1))

/-- **The per-step destination canonical form, in fold form.** -/
theorem parsedDestinationStep_destinations
    (files : IntegerRegisterFiles) (destination : ParsedOperand)
    (context : ParsedIntegerContext) (output : IntegerALU.Bus) (flags : BitVec 4)
    (cycle : Fin 4) (directive : ParsedMaskDirective) (hasSingleLineMask : Bool)
    (nextFiles : IntegerRegisterFiles) (nextBar0 nextBar1 : BitVec 12)
    (notBar : parsedOperandIsBar destination = false)
    (executed : parsedDestinationStep files destination context output flags cycle
      directive hasSingleLineMask = some (nextFiles, nextBar0, nextBar1)) :
    ∃ writes, nextFiles = commitParsedMaskedWrites files writes ∧
      writes.map (fun w => w.destination) =
        parsedStepDestinations destination context.pe cycle context.bar0 context.bar1
          context.tWord ∧
      nextBar0 = context.bar0 ∧ nextBar1 = context.bar1 := by
  unfold parsedDestinationStep at executed
  cases lowered : writeParsedMslMsrDestination? files destination context output flags cycle
      directive hasSingleLineMask with
  | none => simp [lowered] at executed
  | some write =>
      simp only [lowered, Option.some.injEq, Prod.mk.injEq] at executed
      obtain ⟨rfl, rfl, rfl⟩ := executed
      obtain ⟨writes, committed, destinations⟩ :=
        writeParsedMslMsrDestination?_destinations files destination context output flags
          cycle directive hasSingleLineMask write lowered
      have barNone := writeParsedMslMsrDestination?_barUpdate_none_of_not_bar files destination
        context output flags cycle directive hasSingleLineMask write notBar lowered
      refine ⟨writes, committed, destinations, ?_, ?_⟩ <;> simp [barNone]

/-- **The destination list of a `writeParsedMslMsrDestination?` fold.**  Every
fold with the same step and the same nil/cons equations commits a list whose
destination map is the flat map of the canonical step lists.  No register-file
hypothesis is needed: the destination is a function of the operands and the
context only. -/
theorem parsedDestinationFold_destinations
    (fold : List ParsedOperand → IntegerRegisterFiles → BitVec 12 → BitVec 12 →
      Option (IntegerRegisterFiles × BitVec 12 × BitVec 12))
    (context : ParsedIntegerContext) (output : IntegerALU.Bus) (flags : BitVec 4)
    (cycle : Fin 4) (directive : ParsedMaskDirective) (hasSingleLineMask : Bool)
    (foldNil : ∀ (files : IntegerRegisterFiles) (bar0 bar1 : BitVec 12),
      fold [] files bar0 bar1 = some (files, bar0, bar1))
    (foldCons : ∀ (destination : ParsedOperand) (rest : List ParsedOperand)
        (files : IntegerRegisterFiles) (bar0 bar1 : BitVec 12),
      fold (destination :: rest) files bar0 bar1 =
        match parsedDestinationStep files destination
          { context with bar0 := bar0, bar1 := bar1 } output flags cycle directive
          hasSingleLineMask with
        | none => none
        | some (nextFiles, nextBar0, nextBar1) => fold rest nextFiles nextBar0 nextBar1) :
    ∀ (destinations : List ParsedOperand) (files : IntegerRegisterFiles)
      (bar0 bar1 : BitVec 12) (next : IntegerRegisterFiles × BitVec 12 × BitVec 12),
      (∀ destination ∈ destinations, parsedOperandIsBar destination = false) →
      fold destinations files bar0 bar1 = some next →
      ∃ writes, next.1 = commitParsedMaskedWrites files writes ∧
        writes.map (fun w => w.destination) =
          destinations.flatMap (fun destination =>
            parsedStepDestinations destination context.pe cycle bar0 bar1 context.tWord) ∧
        next.2.1 = bar0 ∧ next.2.2 = bar1 := by
  intro destinations
  induction destinations with
  | nil =>
      intro files bar0 bar1 next _ executed
      rw [foldNil] at executed
      obtain rfl := Option.some.inj executed
      exact ⟨[], rfl, by simp, rfl, rfl⟩
  | cons destination rest ih =>
      intro files bar0 bar1 next noBar executed
      rw [foldCons] at executed
      cases step : parsedDestinationStep files destination
          { context with bar0 := bar0, bar1 := bar1 } output flags cycle directive
          hasSingleLineMask with
      | none => simp [step] at executed
      | some result =>
          obtain ⟨nextFiles, nextBar0, nextBar1⟩ := result
          simp only [step] at executed
          have notBar : parsedOperandIsBar destination = false := noBar destination (by simp)
          obtain ⟨headWrites, headCommit, headDest, barEq0, barEq1⟩ :=
            parsedDestinationStep_destinations files destination
              { context with bar0 := bar0, bar1 := bar1 } output flags cycle directive
              hasSingleLineMask nextFiles nextBar0 nextBar1 notBar step
          rw [barEq0, barEq1] at executed
          obtain ⟨tailWrites, tailCommit, tailDest, tailBar0, tailBar1⟩ :=
            ih nextFiles bar0 bar1 next
              (fun item member => noBar item (List.mem_cons_of_mem _ member)) executed
          refine ⟨headWrites ++ tailWrites, ?_, ?_, ?_, ?_⟩
          · rw [tailCommit, headCommit, commitParsedMaskedWrites_append]
          · rw [List.map_append, headDest, tailDest]
            simp [List.flatMap_cons]
          · exact tailBar0
          · exact tailBar1

/-- The global float-MAU destination loop is such a fold. -/
theorem writeParsedMAUDestinations?_writeAll_destinations
    (context : ParsedIntegerContext) (output : IntegerALU.Bus) (flags : BitVec 4)
    (cycle : Fin 4) (directive : ParsedMaskDirective) (hasSingleLineMask : Bool) :
    ∀ (destinations : List ParsedOperand) (files : IntegerRegisterFiles)
      (bar0 bar1 : BitVec 12) (next : ParsedMAUDestinationWrites),
      (∀ destination ∈ destinations, parsedOperandIsBar destination = false) →
      writeParsedMAUDestinations?.writeAll context output flags cycle directive
        hasSingleLineMask destinations files bar0 bar1 = some next →
      ∃ writes, next.files = commitParsedMaskedWrites files writes ∧
        writes.map (fun w => w.destination) =
          destinations.flatMap (fun destination =>
            parsedStepDestinations destination context.pe cycle bar0 bar1 context.tWord) ∧
        next.bar0 = bar0 ∧ next.bar1 = bar1 := by
  intro destinations
  have folded := parsedDestinationFold_destinations
    (fun destinations files bar0 bar1 =>
      (writeParsedMAUDestinations?.writeAll context output flags cycle directive
        hasSingleLineMask destinations files bar0 bar1).map
        (fun next => (next.files, next.bar0, next.bar1)))
    context output flags cycle directive hasSingleLineMask ?_ ?_ destinations
  · intro files bar0 bar1 next noBar executed
    obtain ⟨writes, committed, destinationMap, barEq0, barEq1⟩ :=
      folded files bar0 bar1 (next.files, next.bar0, next.bar1) noBar (by
        rw [executed]
        rfl)
    exact ⟨writes, committed, destinationMap, barEq0, barEq1⟩
  · intro files bar0 bar1
    rw [writeParsedMAUDestinations?.writeAll.eq_1]
    rfl
  · intro destination rest files bar0 bar1
    rw [writeParsedMAUDestinations?.writeAll.eq_2]
    dsimp only
    unfold parsedDestinationStep
    cases writeParsedMslMsrDestination? files destination
        { context with bar0 := bar0, bar1 := bar1 } output flags cycle directive
        hasSingleLineMask <;> rfl

/-- **The float-MAU destination loop, in the writer's own form.** -/
theorem writeParsedMAUDestinations?_destinations
    (files : IntegerRegisterFiles) (destinations : List ParsedOperand)
    (context : ParsedIntegerContext) (output : IntegerALU.Bus) (flags : BitVec 4)
    (cycle : Fin 4) (directive : ParsedMaskDirective) (hasSingleLineMask : Bool)
    (noBar : ∀ destination ∈ destinations, parsedOperandIsBar destination = false)
    (next : ParsedMAUDestinationWrites)
    (executed : writeParsedMAUDestinations? files destinations context output flags cycle
      directive hasSingleLineMask = some next) :
    ∃ writes, next.files = commitParsedMaskedWrites files writes ∧
      writes.map (fun w => w.destination) =
        destinations.flatMap (fun destination =>
          parsedStepDestinations destination context.pe cycle context.bar0 context.bar1
            context.tWord) ∧
      next.bar0 = context.bar0 ∧ next.bar1 = context.bar1 := by
  rw [writeParsedMAUDestinations?.eq_1] at executed
  exact writeParsedMAUDestinations?_writeAll_destinations context output flags cycle directive
    hasSingleLineMask destinations files context.bar0 context.bar1 next noBar executed


/-! ## 5. Float MAU: `executeParsedFloatMAUCyclesAtPE` / `executeParsedFloatMAUsAtPE`

The float-MAU cycle loop commits `writeParsedMAUDestinations?` per cycle.  By
§4 each cycle's commit has the canonical destination list, and a `.bar`-free
destination list keeps the BAR state fixed, so the whole loop's destination list
is a pure function of the expression, the context and the initial `bar0`/`bar1`.

As for every executor that does not return its prepared list, the congruence is
stated in the canonical form: a successful run commits a list whose destination
map is that pure function, hence two successful runs commit lists with the same
destination map. -/

theorem executeParsedFloatMAUCyclesAtPE_destinations
    (readFiles : IntegerRegisterFiles) (oldSlots : ProofsLean.MNCore.Forwarding.Slots)
    (expression : ParsedExpr) (context : ParsedIntegerContext)
    (directive : ParsedMaskDirective) (hasSingleLineMask : Bool)
    (noBar : ∀ destination ∈ expression.destinations,
      parsedOperandIsBar destination = false) :
    ∀ (cycles : List (Fin 4)) (files : IntegerRegisterFiles) (bar0 bar1 : BitVec 12)
      (outputs : Fin 4 → IntegerALU.Bus) (nextFiles : IntegerRegisterFiles)
      (nextBar0 nextBar1 : BitVec 12) (nextOutputs : Fin 4 → IntegerALU.Bus),
      executeParsedFloatMAUCyclesAtPE readFiles oldSlots expression context directive
        hasSingleLineMask cycles files bar0 bar1 outputs =
        .ok (nextFiles, nextBar0, nextBar1, nextOutputs) →
      ∃ writes, nextFiles = commitParsedMaskedWrites files writes ∧
        writes.map (fun w => w.destination) =
          cycles.flatMap (fun cycle =>
            expression.destinations.flatMap (fun destination =>
              parsedStepDestinations destination context.pe cycle bar0 bar1 context.tWord)) ∧
        nextBar0 = bar0 ∧ nextBar1 = bar1 := by
  intro cycles
  induction cycles with
  | nil =>
      intro files bar0 bar1 outputs nextFiles nextBar0 nextBar1 nextOutputs executed
      rw [executeParsedFloatMAUCyclesAtPE.eq_1] at executed
      obtain ⟨rfl, rfl, rfl, rfl⟩ := StepResult.ok.inj executed
      exact ⟨[], rfl, by simp, rfl, rfl⟩
  | cons cycle rest ih =>
      intro files bar0 bar1 outputs nextFiles nextBar0 nextBar1 nextOutputs executed
      rw [executeParsedFloatMAUCyclesAtPE.eq_2] at executed
      dsimp only at executed
      cases cycleStep : executeParsedFloatMAUCycleAtPE readFiles files oldSlots expression
          { context with cycle := cycle, bar0 := bar0, bar1 := bar1 } cycle with
      | failure =>
          rw [cycleStep] at executed
          dsimp only at executed
          simp at executed
      | unknown =>
          rw [cycleStep] at executed
          dsimp only at executed
          simp at executed
      | ok result =>
          obtain ⟨ignored, output, flags⟩ := result
          rw [cycleStep] at executed
          dsimp only at executed
          cases flush : resolveFlushSelection? expression.flush files.maskRegisters cycle with
          | none =>
              rw [flush] at executed
              dsimp only at executed
              simp at executed
          | some flushSelection =>
              rw [flush] at executed
              dsimp only at executed
              cases wrote : writeParsedMAUDestinations? files expression.destinations
                  { context with cycle := cycle, bar0 := bar0, bar1 := bar1 }
                  (parsedOutputAfterFlush flushSelection output) flags cycle directive
                  hasSingleLineMask with
              | none =>
                  rw [wrote] at executed
                  dsimp only at executed
                  simp at executed
              | some writes =>
                  rw [wrote] at executed
                  dsimp only at executed
                  obtain ⟨headWrites, headCommit, headDest, headBar0, headBar1⟩ :=
                    writeParsedMAUDestinations?_destinations files expression.destinations
                      { context with cycle := cycle, bar0 := bar0, bar1 := bar1 }
                      (parsedOutputAfterFlush flushSelection output) flags cycle directive
                      hasSingleLineMask noBar writes wrote
                  rw [headBar0, headBar1] at executed
                  obtain ⟨tailWrites, tailCommit, tailDest, tailBar0, tailBar1⟩ :=
                    ih writes.files bar0 bar1 _ nextFiles nextBar0 nextBar1 nextOutputs executed
                  refine ⟨headWrites ++ tailWrites, ?_, ?_, ?_, ?_⟩
                  · rw [tailCommit, headCommit, commitParsedMaskedWrites_append]
                  · rw [List.map_append, headDest, tailDest]
                    simp [List.flatMap_cons]
                  · exact tailBar0
                  · exact tailBar1

/-- **Float-MAU cycle congruence at arbitrary states.**  Two successful runs of
the same cycle list on any two register files (with the same mask registers, as
in the plain-ALU lemma) commit lists with the same destination map.  The
destination is in fact independent of the mask registers; the hypothesis is kept
to match the plain-ALU statement form. -/
theorem executeParsedFloatMAUCyclesAtPE_destination_congruence
    (readFilesA readFilesB : IntegerRegisterFiles)
    (oldSlotsA oldSlotsB : ProofsLean.MNCore.Forwarding.Slots)
    (expression : ParsedExpr) (context : ParsedIntegerContext)
    (directive : ParsedMaskDirective) (hasSingleLineMask : Bool)
    (noBar : ∀ destination ∈ expression.destinations,
      parsedOperandIsBar destination = false)
    (cycles : List (Fin 4))
    (filesA filesB : IntegerRegisterFiles) (bar0 bar1 : BitVec 12)
    (outputsA outputsB : Fin 4 → IntegerALU.Bus)
    (nextFilesA : IntegerRegisterFiles) (nextBar0A nextBar1A : BitVec 12)
    (nextOutputsA : Fin 4 → IntegerALU.Bus)
    (nextFilesB : IntegerRegisterFiles) (nextBar0B nextBar1B : BitVec 12)
    (nextOutputsB : Fin 4 → IntegerALU.Bus)
    (maskEq : filesA.maskRegisters = filesB.maskRegisters)
    (runA : executeParsedFloatMAUCyclesAtPE readFilesA oldSlotsA expression context directive
      hasSingleLineMask cycles filesA bar0 bar1 outputsA =
      .ok (nextFilesA, nextBar0A, nextBar1A, nextOutputsA))
    (runB : executeParsedFloatMAUCyclesAtPE readFilesB oldSlotsB expression context directive
      hasSingleLineMask cycles filesB bar0 bar1 outputsB =
      .ok (nextFilesB, nextBar0B, nextBar1B, nextOutputsB)) :
    ∃ (writesA writesB : List PreparedParsedMaskedWrite),
      nextFilesA = commitParsedMaskedWrites filesA writesA ∧
      nextFilesB = commitParsedMaskedWrites filesB writesB ∧
      writesA.map (fun w => w.destination) = writesB.map (fun w => w.destination) := by
  obtain ⟨writesA, commitA, destA, _, _⟩ :=
    executeParsedFloatMAUCyclesAtPE_destinations readFilesA oldSlotsA expression context
      directive hasSingleLineMask noBar cycles filesA bar0 bar1 outputsA nextFilesA
      nextBar0A nextBar1A nextOutputsA runA
  obtain ⟨writesB, commitB, destB, _, _⟩ :=
    executeParsedFloatMAUCyclesAtPE_destinations readFilesB oldSlotsB expression context
      directive hasSingleLineMask noBar cycles filesB bar0 bar1 outputsB nextFilesB
      nextBar0B nextBar1B nextOutputsB runB
  exact ⟨writesA, writesB, commitA, commitB, by rw [destA, destB]⟩

/-- **The float-MAU expression loop.**  Same statement for the per-expression
loop `executeParsedFloatMAUsAtPE.run`. -/
theorem executeParsedFloatMAUsAtPE_run_destinations
    (readState : IntegerRegisterFiles) (oldSlots : ProofsLean.MNCore.Forwarding.Slots)
    (context : ParsedIntegerContext) (directive : ParsedMaskDirective)
    (hasSingleLineMask : Bool) :
    ∀ (remaining : List ParsedExpr) (files : IntegerRegisterFiles) (bar0 bar1 : BitVec 12)
      (outputs : Fin 4 → IntegerALU.Bus) (nextFiles : IntegerRegisterFiles)
      (nextBar0 nextBar1 : BitVec 12) (nextOutputs : Fin 4 → IntegerALU.Bus),
      (∀ expression ∈ remaining, ∀ destination ∈ expression.destinations,
        parsedOperandIsBar destination = false) →
      executeParsedFloatMAUsAtPE.run readState oldSlots context directive hasSingleLineMask
        remaining files bar0 bar1 outputs = .ok (nextFiles, nextBar0, nextBar1, nextOutputs) →
      ∃ writes, nextFiles = commitParsedMaskedWrites files writes ∧
        writes.map (fun w => w.destination) =
          remaining.flatMap (fun expression =>
            [0, 1, 2, 3].flatMap (fun cycle =>
              expression.destinations.flatMap (fun destination =>
                parsedStepDestinations destination context.pe cycle bar0 bar1
                  context.tWord))) ∧
        nextBar0 = bar0 ∧ nextBar1 = bar1 := by
  intro remaining
  induction remaining with
  | nil =>
      intro files bar0 bar1 outputs nextFiles nextBar0 nextBar1 nextOutputs _ executed
      rw [executeParsedFloatMAUsAtPE.run.eq_1] at executed
      obtain ⟨rfl, rfl, rfl, rfl⟩ := StepResult.ok.inj executed
      exact ⟨[], rfl, by simp, rfl, rfl⟩
  | cons expression rest ih =>
      intro files bar0 bar1 outputs nextFiles nextBar0 nextBar1 nextOutputs noBar executed
      rw [executeParsedFloatMAUsAtPE.run.eq_2] at executed
      split at executed
      · simp at executed
      · simp at executed
      · rename_i middleFiles middleBar0 middleBar1 middleOutputs ran
        obtain ⟨headWrites, headCommit, headDest, headBar0, headBar1⟩ :=
          executeParsedFloatMAUCyclesAtPE_destinations readState oldSlots expression context
            directive hasSingleLineMask
            (noBar expression (by simp)) [0, 1, 2, 3] files bar0 bar1 _ middleFiles
            middleBar0 middleBar1 middleOutputs ran
        rw [headBar0, headBar1] at executed
        obtain ⟨tailWrites, tailCommit, tailDest, tailBar0, tailBar1⟩ :=
          ih middleFiles bar0 bar1 middleOutputs nextFiles nextBar0 nextBar1 nextOutputs
            (fun item member destination destinationMem =>
              noBar item (List.mem_cons_of_mem _ member) destination destinationMem)
            executed
        refine ⟨headWrites ++ tailWrites, ?_, ?_, ?_, ?_⟩
        · rw [tailCommit, headCommit, commitParsedMaskedWrites_append]
        · rw [List.map_append, headDest, tailDest]
          simp [List.flatMap_cons]
        · exact tailBar0
        · exact tailBar1


/-! ## 6. MSL/MSR: `executeParsedMslMsrAtPE`

The per-PE msl/msr executor folds the shared destination writer over the
expression's destination list for each of the four cycles and commits the result
directly into the PE file.  The fold is an instance of
`parsedDestinationFold_destinations`, so the destination list is canonical. -/

theorem executeParsedMslMsrAtPE_writeDestinations_destinations
    (currentState : State) (hasSingleLineMask : Bool) (context : ParsedIntegerContext)
    (cycle : Fin 4) (output : IntegerALU.Bus) (destinations : List ParsedOperand)
    (noBar : ∀ destination ∈ destinations, parsedOperandIsBar destination = false)
    (files : IntegerRegisterFiles) (bar0 bar1 : BitVec 12)
    (nextFiles : IntegerRegisterFiles) (nextBar0 nextBar1 : BitVec 12)
    (executed : executeParsedMslMsrAtPE.runCycles.writeDestinations currentState
      hasSingleLineMask context cycle output destinations
      files bar0 bar1 = some (nextFiles, nextBar0, nextBar1)) :
    ∃ writes, nextFiles = commitParsedMaskedWrites files writes ∧
      writes.map (fun w => w.destination) =
        destinations.flatMap (fun destination =>
          parsedStepDestinations destination context.pe cycle bar0 bar1 context.tWord) ∧
      nextBar0 = bar0 ∧ nextBar1 = bar1 := by
  have folded := parsedDestinationFold_destinations
    (fun destinations files bar0 bar1 =>
      executeParsedMslMsrAtPE.runCycles.writeDestinations currentState hasSingleLineMask
        context cycle output destinations files bar0 bar1)
    { context with cycle := cycle } output 0 cycle currentState.maskDirective
    hasSingleLineMask ?_ ?_ destinations files bar0 bar1 (nextFiles, nextBar0, nextBar1) noBar
    executed
  · exact folded
  · intro files bar0 bar1
    rw [executeParsedMslMsrAtPE.runCycles.writeDestinations.eq_1]
  · intro destination rest files bar0 bar1
    rw [executeParsedMslMsrAtPE.runCycles.writeDestinations.eq_2]
    dsimp only
    unfold parsedDestinationStep
    cases writeParsedMslMsrDestination? files destination
        { context with cycle := cycle, bar0 := bar0, bar1 := bar1 } output 0 cycle
        currentState.maskDirective hasSingleLineMask with
    | none => rfl
    | some write =>
        simp only [Option.bind_some]
        rfl

theorem executeParsedMslMsrAtPE_runCycles_destinations
    (readState currentState : State) (expression : ParsedExpr)
    (hasSingleLineMask : Bool) (context : ParsedIntegerContext)
    (destinations : List ParsedOperand) (pe sourcePE : PEId)
    (sourceAt : Fin 4 → Option ParsedIntegerInput)
    (noBar : ∀ destination ∈ destinations, parsedOperandIsBar destination = false) :
    ∀ (cycles : List (Fin 4)) (files : IntegerRegisterFiles) (bar0 bar1 : BitVec 12)
      (outputs : Fin 4 → IntegerALU.Bus) (nextFiles : IntegerRegisterFiles)
      (nextBar0 nextBar1 : BitVec 12) (nextOutputs : Fin 4 → IntegerALU.Bus),
      executeParsedMslMsrAtPE.runCycles readState currentState expression hasSingleLineMask
        context destinations sourcePE sourceAt cycles files bar0 bar1 outputs =
        .ok (nextFiles, nextBar0, nextBar1, nextOutputs) →
      ∃ writes, nextFiles = commitParsedMaskedWrites files writes ∧
        writes.map (fun w => w.destination) =
          cycles.flatMap (fun cycle =>
            destinations.flatMap (fun destination =>
              parsedStepDestinations destination context.pe cycle bar0 bar1 context.tWord)) ∧
        nextBar0 = bar0 ∧ nextBar1 = bar1 := by
  intro cycles
  induction cycles with
  | nil =>
      intro files bar0 bar1 outputs nextFiles nextBar0 nextBar1 nextOutputs executed
      rw [executeParsedMslMsrAtPE.runCycles.eq_1] at executed
      obtain ⟨rfl, rfl, rfl, rfl⟩ := StepResult.ok.inj executed
      exact ⟨[], rfl, by simp, rfl, rfl⟩
  | cons cycle rest ih =>
      intro files bar0 bar1 outputs nextFiles nextBar0 nextBar1 nextOutputs executed
      rw [executeParsedMslMsrAtPE.runCycles.eq_2] at executed
      dsimp only at executed
      cases source : sourceAt cycle with
      | none =>
          rw [source] at executed
          dsimp only at executed
          simp at executed
      | some value =>
          rw [source] at executed
          dsimp only at executed
          cases read : ParsedIntegerInput.readWithForwarding (readState.peRegisters sourcePE)
              (stateForwardingSlots readState sourcePE) cycle value with
          | failure =>
              rw [read] at executed
              dsimp only at executed
              simp at executed
          | unknown =>
              rw [read] at executed
              dsimp only at executed
              simp at executed
          | ok sourceBus =>
              rw [read] at executed
              dsimp only at executed
              cases flush : resolveFlushSelection? expression.flush files.maskRegisters cycle with
              | none =>
                  rw [flush] at executed
                  dsimp only at executed
                  simp at executed
              | some flushSelection =>
                  rw [flush] at executed
                  dsimp only at executed
                  cases wrote : executeParsedMslMsrAtPE.runCycles.writeDestinations
                      currentState hasSingleLineMask context cycle
                      (parsedOutputAfterFlush flushSelection (mslMsrOutputBus sourceBus))
                      destinations files bar0 bar1 with
                  | none =>
                      rw [wrote] at executed
                      dsimp only at executed
                      simp at executed
                  | some result =>
                      rw [wrote] at executed
                      dsimp only at executed
                      obtain ⟨middleFiles, middleBar0, middleBar1⟩ := result
                      obtain ⟨headWrites, headCommit, headDest, headBar0, headBar1⟩ :=
                        executeParsedMslMsrAtPE_writeDestinations_destinations currentState
                          hasSingleLineMask context cycle
                          (parsedOutputAfterFlush flushSelection (mslMsrOutputBus sourceBus))
                          destinations noBar files bar0 bar1 middleFiles middleBar0
                          middleBar1 wrote
                      rw [headBar0, headBar1] at executed
                      obtain ⟨tailWrites, tailCommit, tailDest, tailBar0, tailBar1⟩ :=
                        ih middleFiles bar0 bar1 _ nextFiles nextBar0 nextBar1 nextOutputs
                          executed
                      refine ⟨headWrites ++ tailWrites, ?_, ?_, ?_, ?_⟩
                      · rw [tailCommit, headCommit, commitParsedMaskedWrites_append]
                      · rw [List.map_append, headDest, tailDest]
                        simp [List.flatMap_cons]
                      · exact tailBar0
                      · exact tailBar1

/-- **The msl/msr per-PE step commits a canonical destination list.** -/
theorem executeParsedMslMsrAtPE_destinations
    (readState currentState next : State) (expression : ParsedExpr) (pe : PEId)
    (noForward hasSingleLineMask : Bool) (isMsl : Bool)
    (destinations : List ParsedOperand)
    (lowered : lowerParsedMslMsr? expression = some (isMsl, destinations))
    (noBar : ∀ destination ∈ destinations, parsedOperandIsBar destination = false)
    (executed : executeParsedMslMsrAtPE readState currentState expression pe noForward
      hasSingleLineMask = .ok next) :
    ∃ writes, next.peRegisters pe =
        commitParsedMaskedWrites (currentState.peRegisters pe) writes ∧
      writes.map (fun w => w.destination) =
        [0, 1, 2, 3].flatMap (fun cycle =>
          destinations.flatMap (fun destination =>
            parsedStepDestinations destination
              (ParsedIntegerContext.ofLinearIndex pe).pe cycle
              ((parsedPEHazardControl readState pe).context.bar0)
              ((parsedPEHazardControl readState pe).context.bar1)
              (readState.peContext pe).tWord)) := by
  rw [executeParsedMslMsrAtPE.eq_1] at executed
  rw [lowered] at executed
  dsimp only at executed
  split at executed
  · simp at executed
  · simp at executed
  · rename_i registers bar0Out bar1Out outputs ran
    rw [Id.run_pure] at executed
    simp only [StepResult.ok.injEq] at executed
    obtain ⟨writes, committed, destinationMap, _, _⟩ :=
      executeParsedMslMsrAtPE_runCycles_destinations readState currentState expression
        hasSingleLineMask _ destinations pe _ _ noBar [0, 1, 2, 3]
        (currentState.peRegisters pe) _ _ _ registers bar0Out bar1Out outputs ran
    refine ⟨writes, ?_, ?_⟩
    · rw [← executed]
      simpa using committed
    · simpa [parsedPEHazardControl] using destinationMap

/-- **MSL/MSR congruence at arbitrary states.**  Two successful per-PE steps on
any two write states with the same read state and the same mask registers commit
lists with the same destination map. -/
theorem executeParsedMslMsrAtPE_destination_congruence
    (readState : State) (currentStateA currentStateB nextA nextB : State)
    (expression : ParsedExpr) (pe : PEId) (noForward hasSingleLineMask : Bool)
    (isMsl : Bool) (destinations : List ParsedOperand)
    (lowered : lowerParsedMslMsr? expression = some (isMsl, destinations))
    (noBar : ∀ destination ∈ destinations, parsedOperandIsBar destination = false)
    (maskEq : (currentStateA.peRegisters pe).maskRegisters =
      (currentStateB.peRegisters pe).maskRegisters)
    (runA : executeParsedMslMsrAtPE readState currentStateA expression pe noForward
      hasSingleLineMask = .ok nextA)
    (runB : executeParsedMslMsrAtPE readState currentStateB expression pe noForward
      hasSingleLineMask = .ok nextB) :
    ∃ (writesA writesB : List PreparedParsedMaskedWrite),
      nextA.peRegisters pe = commitParsedMaskedWrites (currentStateA.peRegisters pe) writesA ∧
      nextB.peRegisters pe = commitParsedMaskedWrites (currentStateB.peRegisters pe) writesB ∧
      writesA.map (fun w => w.destination) = writesB.map (fun w => w.destination) := by
  obtain ⟨writesA, commitA, destA⟩ :=
    executeParsedMslMsrAtPE_destinations readState currentStateA nextA expression pe
      noForward hasSingleLineMask isMsl destinations lowered noBar runA
  obtain ⟨writesB, commitB, destB⟩ :=
    executeParsedMslMsrAtPE_destinations readState currentStateB nextB expression pe
      noForward hasSingleLineMask isMsl destinations lowered noBar runB
  exact ⟨writesA, writesB, commitA, commitB, by rw [destA, destB]⟩


/-! ## 7. Float relu: `executeParsedFloatReluAtPE`

The relu executor lowers the expression per cycle (`lowerParsedFloatRelu?`), then
folds the shared destination writer over the lowered destinations.  The lowered
destination list is a function of the expression and the context only, so the
canonical destination list is the flat map of §4's `parsedStepDestinations` over
the four cycles' lowered destinations. -/

/-- The canonical destination list of one relu cycle.  The lowering reads the
source context (including its `tWord`), while the destination addresses read the
coordinate context `coordinates` — exactly the two contexts the executor passes
to `lowerParsedFloatRelu?` and to `writeParsedMslMsrDestination?`. -/
def reluCycleDestinations (expression : ParsedExpr) (coordinates sourceContext :
    ParsedIntegerContext) (bar0 bar1 : BitVec 12) (cycle : Fin 4) :
    List (Option DirectMemoryAccess) :=
  match lowerParsedFloatRelu? expression { sourceContext with cycle := cycle } with
  | none => []
  | some accesses =>
      accesses.destinations.flatMap (fun destination =>
        parsedStepDestinations destination coordinates.pe cycle bar0 bar1
          coordinates.tWord)

theorem executeParsedFloatReluAtPE_writeDestinations_destinations
    (currentState : State) (hasSingleLineMask : Bool) (coordinates : ParsedIntegerContext)
    (cycle : Fin 4) (flags : BitVec 4) (output : IntegerALU.Bus)
    (destinations : List ParsedOperand)
    (noBar : ∀ destination ∈ destinations, parsedOperandIsBar destination = false)
    (files : IntegerRegisterFiles) (bar0 bar1 : BitVec 12)
    (nextFiles : IntegerRegisterFiles) (nextBar0 nextBar1 : BitVec 12)
    (executed : executeParsedFloatReluAtPE.runCycles.writeDestinations currentState
      hasSingleLineMask coordinates cycle flags output destinations files bar0 bar1 =
      some (nextFiles, nextBar0, nextBar1)) :
    ∃ writes, nextFiles = commitParsedMaskedWrites files writes ∧
      writes.map (fun w => w.destination) =
        destinations.flatMap (fun destination =>
          parsedStepDestinations destination coordinates.pe cycle bar0 bar1
            coordinates.tWord) ∧
      nextBar0 = bar0 ∧ nextBar1 = bar1 := by
  have folded := parsedDestinationFold_destinations
    (fun destinations files bar0 bar1 =>
      executeParsedFloatReluAtPE.runCycles.writeDestinations currentState hasSingleLineMask
        coordinates cycle flags output destinations files bar0 bar1)
    { coordinates with cycle := cycle } output flags cycle currentState.maskDirective
    hasSingleLineMask ?_ ?_ destinations files bar0 bar1 (nextFiles, nextBar0, nextBar1)
    noBar executed
  · exact folded
  · intro files bar0 bar1
    rw [executeParsedFloatReluAtPE.runCycles.writeDestinations.eq_1]
  · intro destination rest files bar0 bar1
    rw [executeParsedFloatReluAtPE.runCycles.writeDestinations.eq_2]
    dsimp only
    unfold parsedDestinationStep
    cases writeParsedMslMsrDestination? files destination
        { coordinates with cycle := cycle, bar0 := bar0, bar1 := bar1 } output flags cycle
        currentState.maskDirective hasSingleLineMask with
    | none => rfl
    | some write =>
        simp only [Option.bind_some]
        rfl

theorem executeParsedFloatReluAtPE_runCycles_destinations
    (readState currentState : State) (expression : ParsedExpr) (pe : PEId)
    (hasSingleLineMask : Bool) (coordinates sourceContext : ParsedIntegerContext)
    (noBar : ∀ cycle, ∃ accesses,
      lowerParsedFloatRelu? expression { sourceContext with cycle := cycle } = some accesses ∧
        ∀ destination ∈ accesses.destinations, parsedOperandIsBar destination = false) :
    ∀ (cycles : List (Fin 4)) (files : IntegerRegisterFiles) (bar0 bar1 : BitVec 12)
      (outputs : Fin 4 → IntegerALU.Bus) (nextFiles : IntegerRegisterFiles)
      (nextBar0 nextBar1 : BitVec 12) (nextOutputs : Fin 4 → IntegerALU.Bus),
      executeParsedFloatReluAtPE.runCycles readState currentState expression pe
        hasSingleLineMask coordinates sourceContext cycles files bar0 bar1 outputs =
        .ok (nextFiles, nextBar0, nextBar1, nextOutputs) →
      ∃ writes, nextFiles = commitParsedMaskedWrites files writes ∧
        writes.map (fun w => w.destination) =
          cycles.flatMap (reluCycleDestinations expression coordinates sourceContext bar0 bar1) ∧
        nextBar0 = bar0 ∧ nextBar1 = bar1 := by
  intro cycles
  induction cycles with
  | nil =>
      intro files bar0 bar1 outputs nextFiles nextBar0 nextBar1 nextOutputs executed
      rw [executeParsedFloatReluAtPE.runCycles.eq_1] at executed
      obtain ⟨rfl, rfl, rfl, rfl⟩ := StepResult.ok.inj executed
      exact ⟨[], rfl, by simp, rfl, rfl⟩
  | cons cycle rest ih =>
      intro files bar0 bar1 outputs nextFiles nextBar0 nextBar1 nextOutputs executed
      rw [executeParsedFloatReluAtPE.runCycles.eq_2] at executed
      dsimp only at executed
      cases lower : lowerParsedFloatRelu? expression { sourceContext with cycle := cycle } with
      | none =>
          rw [lower] at executed
          dsimp only at executed
          simp at executed
      | some accesses =>
          rw [lower] at executed
          dsimp only at executed
          obtain ⟨precision, name, unsigned, sourceAInput, sourceBOption, destinations⟩ :=
            accesses
          cases readA : ParsedIntegerInput.readWithForwarding (readState.peRegisters pe)
              (stateForwardingSlots readState pe) cycle sourceAInput with
          | failure =>
              rw [readA] at executed
              dsimp only at executed
              simp at executed
          | unknown =>
              rw [readA] at executed
              dsimp only at executed
              simp at executed
          | ok sourceA =>
              rw [readA] at executed
              dsimp only at executed
              cases sourceB? : sourceBOption with
              | none =>
                  rw [sourceB?] at executed
                  dsimp only at executed
                  cases flush : resolveFlushSelection? expression.flush files.maskRegisters cycle with
                  | none =>
                      rw [flush] at executed
                      dsimp only at executed
                      simp at executed
                  | some flushSelection =>
                      rw [flush] at executed
                      dsimp only at executed
                      split at executed
                      · simp at executed
                      · rename_i middleFiles middleBar0 middleBar1 wrote
                        have noBarDestinations : ∀ destination ∈ destinations,
                            parsedOperandIsBar destination = false := by
                          obtain ⟨cycleAccesses, cycleLower, cycleNoBar⟩ := noBar cycle
                          rw [lower] at cycleLower
                          simp only [Option.some.injEq] at cycleLower
                          rw [← cycleLower] at cycleNoBar
                          exact cycleNoBar
                        obtain ⟨headWrites, headCommit, headDest, headBar0, headBar1⟩ :=
                          executeParsedFloatReluAtPE_writeDestinations_destinations
                            currentState hasSingleLineMask coordinates cycle _ _
                            destinations noBarDestinations files bar0 bar1 middleFiles
                            middleBar0 middleBar1 wrote
                        rw [headBar0, headBar1] at executed
                        obtain ⟨tailWrites, tailCommit, tailDest, tailBar0, tailBar1⟩ :=
                          ih middleFiles bar0 bar1 _ nextFiles nextBar0 nextBar1
                            nextOutputs executed
                        refine ⟨headWrites ++ tailWrites, ?_, ?_, ?_, ?_⟩
                        · rw [tailCommit, headCommit, commitParsedMaskedWrites_append]
                        · rw [List.map_append, headDest, tailDest]
                          simp only [List.flatMap_cons, reluCycleDestinations, lower]
                        · exact tailBar0
                        · exact tailBar1
              | some sourceBInput =>
                  rw [sourceB?] at executed
                  dsimp only at executed
                  cases readB : ParsedIntegerInput.readWithForwarding (readState.peRegisters pe)
                      (stateForwardingSlots readState pe) cycle sourceBInput with
                  | failure =>
                      rw [readB] at executed
                      dsimp only at executed
                      simp at executed
                  | unknown =>
                      rw [readB] at executed
                      dsimp only at executed
                      simp at executed
                  | ok sourceB =>
                      rw [readB] at executed
                      dsimp only at executed
                      cases flush : resolveFlushSelection? expression.flush files.maskRegisters cycle with
                      | none =>
                          rw [flush] at executed
                          dsimp only at executed
                          simp at executed
                      | some flushSelection =>
                          rw [flush] at executed
                          dsimp only at executed
                          split at executed
                          · simp at executed
                          · rename_i middleFiles middleBar0 middleBar1 wrote
                            have noBarDestinations : ∀ destination ∈ destinations,
                                parsedOperandIsBar destination = false := by
                              obtain ⟨cycleAccesses, cycleLower, cycleNoBar⟩ := noBar cycle
                              rw [lower] at cycleLower
                              simp only [Option.some.injEq] at cycleLower
                              rw [← cycleLower] at cycleNoBar
                              exact cycleNoBar
                            obtain ⟨headWrites, headCommit, headDest, headBar0, headBar1⟩ :=
                              executeParsedFloatReluAtPE_writeDestinations_destinations
                                currentState hasSingleLineMask coordinates cycle _ _
                                destinations noBarDestinations files bar0 bar1 middleFiles
                                middleBar0 middleBar1 wrote
                            rw [headBar0, headBar1] at executed
                            obtain ⟨tailWrites, tailCommit, tailDest, tailBar0, tailBar1⟩ :=
                              ih middleFiles bar0 bar1 _ nextFiles nextBar0 nextBar1
                                nextOutputs executed
                            refine ⟨headWrites ++ tailWrites, ?_, ?_, ?_, ?_⟩
                            · rw [tailCommit, headCommit, commitParsedMaskedWrites_append]
                            · rw [List.map_append, headDest, tailDest]
                              simp only [List.flatMap_cons, reluCycleDestinations, lower]
                            · exact tailBar0
                            · exact tailBar1

/-- **The relu per-PE step commits a canonical destination list.** -/
theorem executeParsedFloatReluAtPE_destinations
    (readState currentState next : State) (expression : ParsedExpr) (pe : PEId)
    (noForward hasSingleLineMask : Bool)
    (noBar : ∀ cycle, ∃ accesses,
      lowerParsedFloatRelu? expression
        { (parsedPEHazardControl readState pe).context with cycle := cycle } = some accesses ∧
        ∀ destination ∈ accesses.destinations, parsedOperandIsBar destination = false)
    (executed : executeParsedFloatReluAtPE readState currentState expression pe noForward
      hasSingleLineMask = .ok next) :
    ∃ writes, next.peRegisters pe =
        commitParsedMaskedWrites (currentState.peRegisters pe) writes ∧
      writes.map (fun w => w.destination) =
        [0, 1, 2, 3].flatMap (reluCycleDestinations expression
          (ParsedIntegerContext.ofLinearIndex pe)
          (parsedPEHazardControl readState pe).context
          (parsedPEHazardControl readState pe).context.bar0
          (parsedPEHazardControl readState pe).context.bar1) := by
  rw [executeParsedFloatReluAtPE.eq_1] at executed
  dsimp only at executed
  split at executed
  · simp at executed
  · simp at executed
  · rename_i registers bar0Out bar1Out outputs ran
    rw [Id.run_pure] at executed
    simp only [StepResult.ok.injEq] at executed
    obtain ⟨writes, committed, destinationMap, _, _⟩ :=
      executeParsedFloatReluAtPE_runCycles_destinations readState currentState expression pe
        hasSingleLineMask (ParsedIntegerContext.ofLinearIndex pe)
        (parsedPEHazardControl readState pe).context noBar [0, 1, 2, 3]
        (currentState.peRegisters pe) _ _ _ registers bar0Out bar1Out outputs ran
    refine ⟨writes, ?_, ?_⟩
    · rw [← executed]
      simpa using committed
    · simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil,
        parsedPEHazardControl] using destinationMap

/-- **Float-relu congruence at arbitrary states.** -/
theorem executeParsedFloatReluAtPE_destination_congruence
    (readState : State) (currentStateA currentStateB nextA nextB : State)
    (expression : ParsedExpr) (pe : PEId) (noForward hasSingleLineMask : Bool)
    (noBar : ∀ cycle, ∃ accesses,
      lowerParsedFloatRelu? expression
        { (parsedPEHazardControl readState pe).context with cycle := cycle } = some accesses ∧
        ∀ destination ∈ accesses.destinations, parsedOperandIsBar destination = false)
    (maskEq : (currentStateA.peRegisters pe).maskRegisters =
      (currentStateB.peRegisters pe).maskRegisters)
    (runA : executeParsedFloatReluAtPE readState currentStateA expression pe noForward
      hasSingleLineMask = .ok nextA)
    (runB : executeParsedFloatReluAtPE readState currentStateB expression pe noForward
      hasSingleLineMask = .ok nextB) :
    ∃ (writesA writesB : List PreparedParsedMaskedWrite),
      nextA.peRegisters pe = commitParsedMaskedWrites (currentStateA.peRegisters pe) writesA ∧
      nextB.peRegisters pe = commitParsedMaskedWrites (currentStateB.peRegisters pe) writesB ∧
      writesA.map (fun w => w.destination) = writesB.map (fun w => w.destination) := by
  obtain ⟨writesA, commitA, destA⟩ :=
    executeParsedFloatReluAtPE_destinations readState currentStateA nextA expression pe
      noForward hasSingleLineMask noBar runA
  obtain ⟨writesB, commitB, destB⟩ :=
    executeParsedFloatReluAtPE_destinations readState currentStateB nextB expression pe
      noForward hasSingleLineMask noBar runB
  exact ⟨writesA, writesB, commitA, commitB, by rw [destA, destB]⟩


/-! ## 8. `.matrixWrite` and `.l2bm`: no PE-register write at all

A `.matrixWrite` row is executed by the matrix-write stage
(`executeParsedMatrixWritesAtMABs`, inside `executeParsedMatrixMAUAndWrites`),
which only updates the matrix store.  A `.l2bm` row is executed by the shared
block stage (`executeParsedSharedBlockProducers`), which only updates block
memory / DAR state.  Neither writes a PE register file, so their prepared list
is empty: the PE file is the commit of `[]`. -/

/-- **A `.matrixWrite` row does not write any PE register file.**  The
matrix-write stage leaves the PE files exactly where the (possibly absent)
matrix-MAU producer left them. -/
theorem executeParsedMatrixWrite_line_peRegisters_frame
    (readState currentState next : State) (expression : ParsedExpr)
    (noForward hasSingleLineMask : Bool)
    (mauEmpty : [expression].filter parsedExprIsMatrixMAUProducer = [])
    (executed : executeParsedMatrixMAUAndWrites readState currentState [expression]
      noForward hasSingleLineMask = .ok next) :
    next.peRegisters = currentState.peRegisters := by
  have mauId : executeParsedMatrixMAUProducer readState currentState [expression]
      noForward hasSingleLineMask = .ok currentState := by
    simp [executeParsedMatrixMAUProducer, mauEmpty]
  exact (executeParsedMatrixMAUAndWrites_preserves_post_mau_pe_state readState currentState
    currentState next [expression] noForward hasSingleLineMask mauId executed).1

/-- **The `.matrixWrite` family's prepared list is empty.** -/
theorem executeParsedMatrixWrite_line_destinations_empty
    (readState currentState next : State) (expression : ParsedExpr) (pe : PEId)
    (noForward hasSingleLineMask : Bool)
    (mauEmpty : [expression].filter parsedExprIsMatrixMAUProducer = [])
    (executed : executeParsedMatrixMAUAndWrites readState currentState [expression]
      noForward hasSingleLineMask = .ok next) :
    ∃ writes : List PreparedParsedMaskedWrite,
      next.peRegisters pe = commitParsedMaskedWrites (currentState.peRegisters pe) writes ∧
      writes.map (fun w => w.destination) = [] := by
  refine ⟨[], ?_, rfl⟩
  rw [executeParsedMatrixWrite_line_peRegisters_frame readState currentState next expression
    noForward hasSingleLineMask mauEmpty executed]
  rfl

/-- **A `.l2bm` row does not write any PE register file.**  The shared-block
stage preserves every PE file, for any turnaround argument. -/
theorem executeParsedL2BMLine_peRegisters_frame
    (readState currentState next : State) (expression : ParsedExpr)
    (updateTurnaround : Bool)
    (executed : executeParsedSharedBlockProducers readState currentState [expression]
      updateTurnaround = .ok next) :
    next.peRegisters = currentState.peRegisters :=
  executeParsedSharedBlockProducers_peRegisters readState currentState next [expression]
    updateTurnaround executed

/-- **The `.l2bm` family's prepared list is empty.** -/
theorem executeParsedL2BMLine_destinations_empty
    (readState currentState next : State) (expression : ParsedExpr) (pe : PEId)
    (updateTurnaround : Bool)
    (executed : executeParsedSharedBlockProducers readState currentState [expression]
      updateTurnaround = .ok next) :
    ∃ writes : List PreparedParsedMaskedWrite,
      next.peRegisters pe = commitParsedMaskedWrites (currentState.peRegisters pe) writes ∧
      writes.map (fun w => w.destination) = [] := by
  refine ⟨[], ?_, rfl⟩
  rw [executeParsedL2BMLine_peRegisters_frame readState currentState next expression
    updateTurnaround executed]
  rfl


/-! ## 9. The families this module does **not** close, and why

Three families are not closed here.  The obstruction is not the destination
congruence hypothesis discipline (arbitrary states, mask/context equality): it is
either extra loop engineering over the same shared writer, or a genuine extra
data dependence of the executor.  The exact remaining statements are recorded
here so the next step is unambiguous.

* **Block float** (`executeParsedBlockFloatAtMAB`, with the outer
  `executeParsedBlockFloatAtMABs` and the line stage
  `executeParsedBlockFloatProducer`).  Its `writeDestinations` fold is the same
  shared-writer fold as §4, but it is nested inside a four-PE loop and a
  four-cycle loop, and the per-cycle flush resolution reads `(files pe)` before
  the fold.  The destination argument is therefore *the same*:
  `parsedStepDestinations destination coordinates.pe cycle bar0 bar1
  oldContext.tWord`, flat-mapped over the four cycles and the four PEs, with the
  same `parsedOperandIsBar destination = false` side condition.  Lifting §4's
  fold lemma through the two vector loops is mechanical but was not carried out
  here; no data dependence obstructs it.

* **L1BM broadcast** (`executeParsedL1ToPEProducer`, via
  `executeParsedL1ToPEAtPEs`).  The per-destination writer
  `writeParsedL1ToPEDestination?` has exactly the §4 destination semantics
  (`.mem` → the resolved direct access, `.bar`/`.nowrite` → no memory write,
  other operands → failure), and both of its resolution steps are data
  independent.  The PE walk (`executeParsedL1ToPEAtPEs`) and the producer
  wrapper are not restated with the destination map here; note that the L1BM
  destination *list* also depends on the lowered `access`
  (`lowerParsedL1ToPE?` reads only the expression), which is state independent,
  so the congruence statement is expected to need no extra hypothesis beyond the
  `.bar`-freeness of `access.destinations`.  The statement to prove is the
  head-PE form of `executeParsedL1ToPEAtPEs_commit` with the destination map
  `[0, 1, 2, 3].flatMap (fun cycle => access.destinations.flatMap (fun d =>
  parsedStepDestinations d coordinates.pe cycle bar0 bar1 readContext.tWord))`
  added, then `executeParsedL1ToPEProducer` by unfolding the lowering.

* **Matrix MAU** (`executeParsedMatrixMAUAtMAB`,
  `executeParsedMatrixMAUAndWrites`).  This one is *principled*:
  `writeParsedMatrixMAUDestinationsAtPE` gates each destination on the
  per-cycle `poison` flag and on `parsedMatrixMAUDestinationEnabled?`.  With
  `poison = true` and the destination enabled it fails; with `poison = false`
  it writes; and `parsedMatrixMAUDestinationEnabled?` reads the mask registers.
  Two successful runs at states with the same mask registers but different
  poison flags can therefore prepare *different* destination lists (one skips a
  destination the other writes).  Any congruence statement for this family must
  carry an explicit poison/gate-agreement hypothesis, not only mask/context
  equality.  `writeParsedMslMsrDestination?`-level facts (the `.mem` destination
  of a matrix-MAU step) are still covered by §4.

* **`.matrixWrite` / `.l2bm`** write no PE register at all: §8 records that
  their committed list is empty. -/

end ProofsLean.MNCore

-- End of module: no sorry, no admit, no native_decide, no new axioms.
