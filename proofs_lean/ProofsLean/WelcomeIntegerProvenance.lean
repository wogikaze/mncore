import ProofsLean.WelcomeL1PEShape
import ProofsLean.WelcomeWriterShape

/-! # Integer-stage `.lm1` provenance and the single-row L1BM broadcast line

This module closes the two remainders recorded in `WelcomeL1PEShape.lean` §6:

* **§1 the integer stage's list-level `.lm1` provenance.**  If every row the
  integer stage prepares (`expressions.filter
  parsedExprIsIntegerMatrixReadStageInput`) has no `.lm1` destination operand
  (`WelcomeRowHasNoLm1Destination`), then `welcomeIntegerPrep` produces a write
  list with no `.lm1` destination, and committing it leaves the `.lm1` bank
  unchanged.  The per-cycle halves (`prepareParsedIntegerALUExprCycle_lm1_free`,
  `prepareParsedMatrixReadCycle_lm1_free`, …) and the expression/list folds
  (`prepareParsedIntegerMatrixReadLineExpression_lm1_free`,
  `prepareParsedIntegerMatrixReadLineExpressions_lm1_free`,
  `prepareParsedIntegerMatrixReadLineCycles_lm1_free`) live in
  `WelcomeLm1Frame.lean`; they are unconditionally folded into
  `welcomePEIntegerStageLm1Provenance` there.  This module does not duplicate
  that fold: it states the exact consumer forms (write level, destination level,
  commit level) and proves them from the existing unconditional theorem, so the
  "no `.lm1` writer" line instantiation
  (`welcomePEWriteShape_of_noLm1Rows`, `WelcomeWriterShape.lean` §6) and the
  single-row broadcast instance below share one source of truth.
* **§2/§3 the single-row line instance for the L1BM broadcast writer.**  For one
  expression `e` whose parsed form is a `.l1bm` broadcast (`pbcast` / `mbcast` /
  `m4bcast` / `distrib`) with a destination list of the single `.mem` operand
  `o`, lowered by `lowerParsedL1ToPE?`, with `o` of static bank `.lm1` and width
  `w`, the line `[e]` satisfies `WelcomePEWriteShape`.  This discharges the
  single-row form of the "broadcast row is the writer" case of
  `WelcomeL1PEShape.lean` §6: the broadcast is the only row, so it is trivially
  the unique `.lm1` writer, and the rest of the line's stages are empty.
* **§4 the multi-row form with integer-or-inert companions.**
  `welcomePEWriteShape_of_l1bmWriter_of_integerOrInert` extends §3: if the parsed
  line splits as `before ++ e :: after`, `e` is the broadcast writer above, and
  every companion row is an integer/matrix-read stage input or a PE-inert
  producer with no `.lm1` destination in the integer-filtered list, the line
  still satisfies `WelcomePEWriteShape`.  This is the case where §1 is consumed:
  the companion rows' prepared writes are `.lm1`-free, the middle stages have
  empty filters, and the two shapes compose.

What is **not** claimed: a multi-row line whose companion rows belong to the
middle producer families (MSL/MSR, float-relu, block-float, matrix-MAU,
`.matrixWrite`, `.l2bm`, shared `.l1bm` writers), and a line whose `.lm1` writer
is a row other than the broadcast.  In both cases the line shape is decided by
another row's stage list; the stage `.lm1` bank frames exist
(`welcomePEStageLm1Frame`) but no write-list-level `.lm1` provenance is proved
here for the middle stages.  See the final section for the exact remainder.

## How §2 is assembled

The sealed step is peeled into the seven stages by
`executeIntegerProducerInstructionLine_pe_stages_exists`
(`WelcomeAssembly.lean` §2).  The singleton broadcast row

* is not an integer/matrix-read stage input, so the integer stage receives the
  empty list and prepares no write (its commit is the identity; §1 is the
  general statement of this provenance, and here the prepared list is literally
  empty);
* is none of MSL/MSR, float-relu, block-float, matrix-MAU or `.matrixWrite`, so
  the four middle stages are `.ok state` by the empty-filter identities of
  `WelcomeAssembly.lean` §1, and the shared-block stage is a frame for every row
  (`executeParsedSharedBlockProducers_peRegisters`);
* is the L1BM-to-PE producer, so that stage has exactly one row and
  `executeParsedL1ToPEProducers_mem_lm1_shape` (`WelcomeL1PEShape.lean` §5)
  gives the broadcast's PE 0 write list, its commit equation, and the
  `Lm1WritesDoubleCopy ∨ Lm1WritesNarrow` shape.

Composing the commits along the stage chain identifies the line's PE 0 file
with the broadcast's own write-list commit, and
`welcomePEWriteShape_of_commit_shape` (`WelcomeWriterShape.lean` §2) turns that
into `WelcomePEWriteShape [e]`.  The stage conditions needed to peel the line
(issue acceptance, no pending wait, no unsupported Rust ALU row, all rows
supported) are **derived from the successful step itself**
(`executeIntegerProducerInstructionLine_pe_conditions`), not assumed: the
instance therefore holds for every expression of this syntactic class, with the
non-executing cases vacuous.

§4 reuses the same peeling with the decomposition `before ++ e :: after`: the
outer five-predicate filter keeps every row (`welcomeIntegerOrInertLine` rows by
their stage facts, the broadcast by its lowered op), `executeIntegerProducerLineAtPEs_prepared`
exposes the integer stage's list, and §1 shows it is `.lm1`-free.  The commits
concatenate through `commitParsedMaskedWrites_append` and the shapes through
`lm1WritesDoubleCopy_append_of_only_right` / `lm1WritesNarrow_append_of_only_right`.

## Remainder

1. **Companion rows of the middle families.**  When a non-broadcast row is an
   MSL/MSR, float-relu, block-float, matrix-MAU, `.matrixWrite`, `.l2bm` or
   shared `.l1bm` producer, the corresponding stage is no longer empty.  The
   line shape then needs a write-list-level `.lm1` provenance for that stage
   (the bank frame `welcomePEStageLm1Frame` only preserves the bank, which is
   not enough to exclude an `.lm1` write list).
2. **The broadcast is not the `.lm1` writer.**  When the broadcast's
   destinations are all `.mem lm0` / `.bar` / `.nowrite`, the line's `.lm1`
   writer is another row and its shape has to be analysed by the eight-family
   decomposition of `WelcomeWriterShape.lean` §7.
3. **The full `WelcomePEL1ToPEShapeObligation`.**  It quantifies over the whole
   family class and remains unproved; items 1–2 are its open cases.

No `sorry`, no `admit`, no `native_decide`, no new axioms, and no existing
module is edited.  Neither `LowerBound 2` nor `Optimal` is claimed.
-/

namespace ProofsLean.MNCore

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

open Issue
open PEMemory

/-! ## 1. The integer stage's list-level `.lm1` provenance

`WelcomeLm1Frame.lean` proves the per-cycle statements and folds them over the
expression list and the four-cycle schedule.  The unconditional result is
`welcomePEIntegerStageLm1Provenance`; the three theorems below are its consumer
forms: the prepared list has no `.lm1` *write*, no `.lm1` *destination*, and the
commit of the list does not move the `.lm1` bank. -/

/-- **The integer stage prepares no `.lm1` write from `.lm1`-free rows.**  This
is the list-level `.lm1` provenance for `welcomeIntegerPrep`: if every row of
the integer/matrix-read stage's filter carries no `.lm1` destination operand,
none of the prepared writes targets bank `.lm1`. -/
theorem welcomeIntegerPrep_lm1_free (state : State) (pe : PEId)
    (expressions : List ParsedExpr) (writes : List PreparedParsedMaskedWrite)
    (slots : ProofsLean.MNCore.Forwarding.Slots)
    (bars : List (Bool × BitVec 12))
    (prep : welcomeIntegerPrep state pe expressions = .ok (writes, slots, bars))
    (noLm1 : ∀ expression ∈ expressions.filter parsedExprIsIntegerMatrixReadStageInput,
      WelcomeRowHasNoLm1Destination expression) :
    ∀ write ∈ writes, PreparedParsedMaskedWrite.isLm1Write write = false :=
  welcomePEIntegerStageLm1Provenance expressions state pe writes slots bars prep noLm1

/-- **The destination-level form.**  Every prepared write resolves either no
destination or a destination outside bank `.lm1`. -/
theorem welcomeIntegerPrep_lm1_destination_free (state : State) (pe : PEId)
    (expressions : List ParsedExpr) (writes : List PreparedParsedMaskedWrite)
    (slots : ProofsLean.MNCore.Forwarding.Slots)
    (bars : List (Bool × BitVec 12))
    (prep : welcomeIntegerPrep state pe expressions = .ok (writes, slots, bars))
    (noLm1 : ∀ expression ∈ expressions.filter parsedExprIsIntegerMatrixReadStageInput,
      WelcomeRowHasNoLm1Destination expression) :
    ∀ write ∈ writes, ∀ access : DirectMemoryAccess,
      write.destination = some access → access.bank ≠ PEMemory.Bank.lm1 := by
  intro write member access resolved
  exact isLm1Write_false_bank write (welcomeIntegerPrep_lm1_free state pe expressions writes
    slots bars prep noLm1 write member) access resolved

/-- **The integer stage's `.lm1` bank frame.**  With no `.lm1` destination in any
prepared row, the integer stage's commit leaves PE 0's `.lm1` bank unchanged.
This is the integer-stage half consumed by the unique-writer reduction: the
middle stages' frames are `welcomePEStageLm1Frame` (`WelcomeLm1Frame.lean`). -/
theorem welcomeIntegerPrep_lm1_commit_eq (state : State) (pe : PEId)
    (expressions : List ParsedExpr) (writes : List PreparedParsedMaskedWrite)
    (slots : ProofsLean.MNCore.Forwarding.Slots)
    (bars : List (Bool × BitVec 12))
    (prep : welcomeIntegerPrep state pe expressions = .ok (writes, slots, bars))
    (noLm1 : ∀ expression ∈ expressions.filter parsedExprIsIntegerMatrixReadStageInput,
      WelcomeRowHasNoLm1Destination expression) :
    (commitParsedMaskedWrites (state.peRegisters pe) writes).lm1 =
      (state.peRegisters pe).lm1 :=
  commitParsedMaskedWrites_lm1_of_no_lm1 writes (state.peRegisters pe)
    (welcomeIntegerPrep_lm1_destination_free state pe expressions writes slots bars prep noLm1)

/-! ## 2. The syntactic facts of a lowered L1BM broadcast row

`lowerParsedL1ToPE?` succeeds only on the four broadcast operations of `.l1bm`.
On those operations every other stage's producer test is false, and the line
executor's integer-stage filter (which mentions `parsedExprIsL1ToPEProducer`)
drops the row. -/

/-- **A lowered broadcast row belongs to no other stage.**  The four broadcast
operations are not integer/matrix-read stage inputs (in particular the integer
filter, which subtracts `parsedExprIsL1ToPEProducer`, drops the row), carry no
float-MAU producer, are none of `.l2bm`, MSL/MSR, float-relu, block-float,
matrix-MAU or `.matrixWrite`, and are exactly the L1BM-to-PE producers. -/
theorem l1bmBroadcast_parsedExpr_predicates (expression : ParsedExpr)
    (access : ParsedL1ToPEAccess)
    (lowered : lowerParsedL1ToPE? expression = some access) :
    parsedExprIsIntegerMatrixReadStageInput expression = false ∧
    parsedExprIsSupportedFloatMAUProducer expression = false ∧
    parsedExprIsL2BMProducer expression = false ∧
    parsedExprIsMslMsrProducer expression = false ∧
    parsedExprIsFloatReluProducer expression = false ∧
    parsedExprIsBlockFloatProducer expression = false ∧
    parsedExprIsMatrixMAUProducer expression = false ∧
    parsedExprIsMatrixWriteProducer expression = false ∧
    parsedExprIsL1ToPEProducer expression = true := by
  cases expression with
  | mk op sources destinations flush text =>
      cases op with
      | alu name precision unsigned arg =>
          simp [lowerParsedL1ToPE?] at lowered
      | immediate value unsigned =>
          simp [lowerParsedL1ToPE?] at lowered
      | zero =>
          simp [lowerParsedL1ToPE?] at lowered
      | mau precision matrix kind half round =>
          simp [lowerParsedL1ToPE?] at lowered
      | matrixWrite precision =>
          simp [lowerParsedL1ToPE?] at lowered
      | matrixRead precision =>
          simp [lowerParsedL1ToPE?] at lowered
      | wait tag =>
          simp [lowerParsedL1ToPE?] at lowered
      | noforward =>
          simp [lowerParsedL1ToPE?] at lowered
      | l1bm operation =>
          cases operation with
          | mwrite mab =>
              simp [lowerParsedL1ToPE?] at lowered
          | m4write mab =>
              simp [lowerParsedL1ToPE?] at lowered
          | gather mabdiff =>
              simp [lowerParsedL1ToPE?] at lowered
          | reduce rrn round =>
              simp [lowerParsedL1ToPE?] at lowered
          | reduce4 rrn round =>
              simp [lowerParsedL1ToPE?] at lowered
          | pbcast =>
              simp [parsedExprIsIntegerMatrixReadStageInput, parsedExprWaitTag?,
                parsedExprIsL2BMProducer, parsedExprIsMatrixWriteProducer,
                parsedExprIsL1MwriteProducer, parsedExprIsL1GatherProducer,
                parsedExprIsL1ReduceProducer, parsedExprIsL1ToPEProducer,
                parsedExprIsMatrixMAUProducer, parsedExprIsSupportedFloatMAUProducer,
                parsedExprIsMslMsrProducer, parsedExprIsBlockFloatProducer,
                parsedExprIsFloatReluProducer]
          | mbcast =>
              simp [parsedExprIsIntegerMatrixReadStageInput, parsedExprWaitTag?,
                parsedExprIsL2BMProducer, parsedExprIsMatrixWriteProducer,
                parsedExprIsL1MwriteProducer, parsedExprIsL1GatherProducer,
                parsedExprIsL1ReduceProducer, parsedExprIsL1ToPEProducer,
                parsedExprIsMatrixMAUProducer, parsedExprIsSupportedFloatMAUProducer,
                parsedExprIsMslMsrProducer, parsedExprIsBlockFloatProducer,
                parsedExprIsFloatReluProducer]
          | m4bcast =>
              simp [parsedExprIsIntegerMatrixReadStageInput, parsedExprWaitTag?,
                parsedExprIsL2BMProducer, parsedExprIsMatrixWriteProducer,
                parsedExprIsL1MwriteProducer, parsedExprIsL1GatherProducer,
                parsedExprIsL1ReduceProducer, parsedExprIsL1ToPEProducer,
                parsedExprIsMatrixMAUProducer, parsedExprIsSupportedFloatMAUProducer,
                parsedExprIsMslMsrProducer, parsedExprIsBlockFloatProducer,
                parsedExprIsFloatReluProducer]
          | distrib mabdiff =>
              simp [parsedExprIsIntegerMatrixReadStageInput, parsedExprWaitTag?,
                parsedExprIsL2BMProducer, parsedExprIsMatrixWriteProducer,
                parsedExprIsL1MwriteProducer, parsedExprIsL1GatherProducer,
                parsedExprIsL1ReduceProducer, parsedExprIsL1ToPEProducer,
                parsedExprIsMatrixMAUProducer, parsedExprIsSupportedFloatMAUProducer,
                parsedExprIsMslMsrProducer, parsedExprIsBlockFloatProducer,
                parsedExprIsFloatReluProducer]
      | l2bm operation =>
          simp [lowerParsedL1ToPE?] at lowered

/-- The row-predicate facts in the normalized-expression form used by the
single-row instance. -/
theorem l1bmBroadcast_row_predicates (expression : NormalizedExpr)
    (access : ParsedL1ToPEAccess)
    (lowered : lowerParsedL1ToPE? expression.toParsed = some access) :
    parsedExprIsIntegerMatrixReadStageInput expression.toParsed = false ∧
    parsedExprIsSupportedFloatMAUProducer expression.toParsed = false ∧
    parsedExprIsL2BMProducer expression.toParsed = false ∧
    parsedExprIsMslMsrProducer expression.toParsed = false ∧
    parsedExprIsFloatReluProducer expression.toParsed = false ∧
    parsedExprIsBlockFloatProducer expression.toParsed = false ∧
    parsedExprIsMatrixMAUProducer expression.toParsed = false ∧
    parsedExprIsMatrixWriteProducer expression.toParsed = false ∧
    parsedExprIsL1ToPEProducer expression.toParsed = true :=
  l1bmBroadcast_parsedExpr_predicates expression.toParsed access lowered

/-- **The stage conditions are consequences of a successful line step.**  The
line executor rejects (or stalls) before the stage pipeline unless the issue
checker accepts, no `wait` tag is pending, no Rust-unsupported ALU row is
present, and every row is a supported PE line producer.  Deriving them from the
step (rather than assuming them) lets the row instances below hold for every
expression of their syntactic class, with the non-executing cases vacuous. -/
theorem executeIntegerProducerInstructionLine_pe_conditions
    (expressions : List NormalizedExpr) (state next : State)
    (executed : executeIntegerProducerInstructionLine (.pe expressions) state = .ok next) :
    checkParsedTopLine (InstructionLine.pe expressions).toParsed = true ∧
    (expressions.map NormalizedExpr.toParsed).any (parsedExprWaitPending state) = false ∧
    (expressions.map NormalizedExpr.toParsed).any parsedExprIsUnsupportedRustAlu = false ∧
    (expressions.map NormalizedExpr.toParsed).all parsedExprIsSupportedPELineProducer = true := by
  rw [← executeNormalizedLine_pe_eq] at executed
  by_cases accepted : checkParsedTopLine (InstructionLine.pe expressions).toParsed = true
  · by_cases waits : (expressions.map NormalizedExpr.toParsed).any
        (parsedExprWaitPending state) = true
    · rw [executeNormalizedLine_pe_waitPending expressions state accepted waits] at executed
      simp at executed
    · have waitsFalse : (expressions.map NormalizedExpr.toParsed).any
          (parsedExprWaitPending state) = false := by
        cases h : (expressions.map NormalizedExpr.toParsed).any
          (parsedExprWaitPending state) <;> simp_all
      by_cases unsupported : (expressions.map NormalizedExpr.toParsed).any
          parsedExprIsUnsupportedRustAlu = true
      · rw [executeNormalizedLine_pe_unsupported expressions state accepted waitsFalse
          unsupported] at executed
        simp at executed
      · have unsupportedFalse : (expressions.map NormalizedExpr.toParsed).any
            parsedExprIsUnsupportedRustAlu = false := by
          cases h : (expressions.map NormalizedExpr.toParsed).any
            parsedExprIsUnsupportedRustAlu <;> simp_all
        by_cases supported : (expressions.map NormalizedExpr.toParsed).all
            parsedExprIsSupportedPELineProducer = true
        · exact ⟨accepted, waitsFalse, unsupportedFalse, supported⟩
        · have supportedFalse : (expressions.map NormalizedExpr.toParsed).all
              parsedExprIsSupportedPELineProducer = false := by
            cases h : (expressions.map NormalizedExpr.toParsed).all
              parsedExprIsSupportedPELineProducer <;> simp_all
          rw [executeNormalizedLine_pe_notSupported expressions state accepted waitsFalse
            unsupportedFalse supportedFalse] at executed
          simp at executed
  · have acceptedFalse : checkParsedTopLine (InstructionLine.pe expressions).toParsed = false := by
      cases h : checkParsedTopLine (InstructionLine.pe expressions).toParsed <;> simp_all
    rw [executeNormalizedLine_pe_checkFalse expressions state acceptedFalse] at executed
    simp at executed

/-! ## 3. The single-row L1BM broadcast line

The line has one row, the broadcast.  Its integer-stage filter is empty, its
middle-stage filters are empty, its shared-block stage is a frame, and its
L1BM-to-PE stage is the single broadcast producer whose PE 0 commit and shape
are `executeParsedL1ToPEProducers_mem_lm1_shape`. -/

/-- **`WelcomePEWriteShape` for a one-row broadcast line.**  If the line's only
expression is a `.l1bm` broadcast whose lowered destination list is the single
`.mem` operand `ParsedOperand.mem memoryAccess negated extended rounded mask`,
and that operand has static bank `.lm1` and width `w`, then the line's PE 0
write shape is the broadcast's own row shape: `Lm1WritesDoubleCopy` when
`w = .double` and `Lm1WritesNarrow` otherwise.

This is the "broadcast row is the writer" instance of
`WelcomePEL1ToPEShapeObligation`'s remaining case: with a single row the
broadcast is trivially the unique `.lm1` writer, and no other stage contributes
a write. -/
theorem welcomePEWriteShape_singleton_of_l1bmMemLm1
    (expression : NormalizedExpr) (access : ParsedL1ToPEAccess)
    (memoryAccess : Access) (negated extended rounded : Bool) (mask : Option ParsedMask)
    (w : PEMemory.Width)
    (lowered : lowerParsedL1ToPE? expression.toParsed = some access)
    (destinations : access.destinations =
      [ParsedOperand.mem memoryAccess negated extended rounded mask])
    (static : ParsedOperand.directDestinationBankWidth?
      (ParsedOperand.mem memoryAccess negated extended rounded mask) =
      some (PEMemory.Bank.lm1, w)) :
    WelcomePEWriteShape [expression] := by
  apply welcomePEWriteShape_of_commit_shape
  intro next step
  have executed := welcomeSealed_step_ok step
  simp only [executeNormalizedLine, NormalizedLine.toInstruction?,
    Issue.InstructionLine.toNormalizedLine] at executed
  obtain ⟨accepted, waits, unsupported, supported⟩ :=
    executeIntegerProducerInstructionLine_pe_conditions [expression]
      (welcomeInitialState welcomeZeroWords) next executed
  obtain ⟨intFalse, floatFalse, l2bmFalse, mslFalse, reluFalse, blockFalse, mmauFalse,
    mwriteFalse, l1True⟩ := l1bmBroadcast_row_predicates expression access lowered
  -- filter identities for the singleton line
  have outerFilter : ([expression].map NormalizedExpr.toParsed).filter (fun expression =>
      !parsedExprIsL2BMProducer expression && !parsedExprIsMslMsrProducer expression &&
        !parsedExprIsMatrixMAUProducer expression &&
        !parsedExprIsBlockFloatProducer expression &&
        !parsedExprIsFloatReluProducer expression) = [expression.toParsed] := by
    simp [l2bmFalse, mslFalse, mmauFalse, blockFalse, reluFalse]
  have floatFilter : ([expression].map NormalizedExpr.toParsed).filter
      parsedExprIsSupportedFloatMAUProducer = [] := by
    simp [floatFalse]
  have mslFilter : ([expression].map NormalizedExpr.toParsed).filter
      parsedExprIsMslMsrProducer = [] := by
    simp [mslFalse]
  have reluFilter : ([expression].map NormalizedExpr.toParsed).filter
      parsedExprIsFloatReluProducer = [] := by
    simp [reluFalse]
  have blockFilter : ([expression].map NormalizedExpr.toParsed).filter
      parsedExprIsBlockFloatProducer = [] := by
    simp [blockFalse]
  have matrixFilter : ([expression].map NormalizedExpr.toParsed).filter
      parsedExprIsMatrixMAUProducer = [] := by
    simp [mmauFalse]
  have matrixWrite : ([expression].map NormalizedExpr.toParsed).any
      parsedExprIsMatrixWriteProducer = false := by
    simp [mwriteFalse]
  have l1Filter : ([expression].map NormalizedExpr.toParsed).filter
      parsedExprIsL1ToPEProducer = [expression.toParsed] := by
    simp [l1True]
  -- peel the successful sealed step into its seven stages
  obtain ⟨nextPEs, nextMsl, nextRelu, nextBlockFloat, afterMatrix, nextShared, nextBroadcast,
    walkExecuted, mslExecuted, reluExecuted, blockExecuted, matrixExecuted, sharedExecuted,
    l1Executed, nextEq⟩ :=
    executeIntegerProducerInstructionLine_pe_stages_exists [expression]
      (welcomeInitialState welcomeZeroWords) next accepted waits unsupported supported
      executed
  -- the outer stage filter keeps the row, but the integer filter drops it: the
  -- integer stage prepares the empty list
  rw [outerFilter] at walkExecuted
  obtain ⟨intWrites, intSlots, intBars, intPrep, intCommit⟩ :=
    executeIntegerProducerLineAtPEs_prepared [expression.toParsed] (List.finRange 4096)
      (welcomeInitialState welcomeZeroWords) nextPEs floatFilter walkExecuted
      (List.nodup_finRange 4096) welcomePE (List.mem_finRange welcomePE)
  have intEmpty : welcomeIntegerPrep (welcomeInitialState welcomeZeroWords) welcomePE
      [expression.toParsed] =
      .ok ([], stateForwardingSlots (welcomeInitialState welcomeZeroWords) welcomePE, []) := by
    simp [welcomeIntegerPrep, intFalse, prepareParsedIntegerMatrixReadLineCycles,
      prepareParsedIntegerMatrixReadLineExpressions]
  rw [intEmpty] at intPrep
  simp only [StepResult.ok.injEq, Prod.mk.injEq] at intPrep
  obtain ⟨rfl, rfl, rfl⟩ := intPrep
  have intIdentity : nextPEs.peRegisters welcomePE =
      (welcomeInitialState welcomeZeroWords).peRegisters welcomePE := by
    simpa only [commitParsedMaskedWrites, List.foldl_nil] using intCommit
  -- the four middle stages are the identity on an empty filter
  have mslId : executeParsedMslMsrProducers (welcomeInitialState welcomeZeroWords) nextPEs
      ([expression].map NormalizedExpr.toParsed)
      ([expression].any (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed))
      ([expression].any (parsedExprHasSingleLineWriteMask ∘ NormalizedExpr.toParsed)) =
      .ok nextPEs :=
    executeParsedMslMsrProducers_eq_self _ _ _ _ _ mslFilter
  have nextMslEq : nextMsl = nextPEs := by
    rw [mslId] at mslExecuted
    exact (StepResult.ok.inj mslExecuted).symm
  have reluId : executeParsedFloatReluProducers (welcomeInitialState welcomeZeroWords) nextMsl
      ([expression].map NormalizedExpr.toParsed)
      ([expression].any (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed))
      ([expression].any (parsedExprHasSingleLineWriteMask ∘ NormalizedExpr.toParsed)) =
      .ok nextMsl :=
    executeParsedFloatReluProducers_eq_self _ _ _ _ _ reluFilter
  have nextReluEq : nextRelu = nextMsl := by
    rw [reluId] at reluExecuted
    exact (StepResult.ok.inj reluExecuted).symm
  have blockId : executeParsedBlockFloatProducer (welcomeInitialState welcomeZeroWords) nextRelu
      ([expression].map NormalizedExpr.toParsed)
      ([expression].any (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed))
      ([expression].any (parsedExprHasSingleLineWriteMask ∘ NormalizedExpr.toParsed)) =
      .ok nextRelu :=
    executeParsedBlockFloatProducer_eq_self _ _ _ _ _ blockFilter
  have nextBlockFloatEq : nextBlockFloat = nextRelu := by
    rw [blockId] at blockExecuted
    exact (StepResult.ok.inj blockExecuted).symm
  have matrixId : executeParsedMatrixMAUAndWrites (welcomeInitialState welcomeZeroWords)
      nextBlockFloat ([expression].map NormalizedExpr.toParsed)
      ([expression].any (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed))
      ([expression].any (parsedExprHasSingleLineWriteMask ∘ NormalizedExpr.toParsed)) =
      .ok nextBlockFloat :=
    executeParsedMatrixMAUAndWrites_eq_self _ _ _ _ _ matrixFilter matrixWrite
  have afterMatrixEq : afterMatrix = nextBlockFloat := by
    rw [matrixId] at matrixExecuted
    exact (StepResult.ok.inj matrixExecuted).symm
  -- the shared-block stage is a frame for every row
  have sharedFrame : nextShared.peRegisters = afterMatrix.peRegisters :=
    executeParsedSharedBlockProducers_peRegisters (welcomeInitialState welcomeZeroWords)
      afterMatrix nextShared _ _ sharedExecuted
  -- the L1BM-to-PE stage is the single broadcast producer
  obtain ⟨l1Writes, l1Commit, l1Shape⟩ :=
    executeParsedL1ToPEProducers_mem_lm1_shape welcomeZeroWords nextShared nextBroadcast
      ([expression].map NormalizedExpr.toParsed) expression.toParsed access
      ([expression].any (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed))
      ([expression].any (parsedExprHasSingleLineWriteMask ∘ NormalizedExpr.toParsed))
      (parsedL1ToPEPrecedesOMRWriter ([expression].map NormalizedExpr.toParsed))
      memoryAccess negated extended rounded mask w lowered destinations static l1Filter l1Executed
  refine ⟨l1Writes, ?_, l1Shape⟩
  have peRegistersNext : next.peRegisters = nextBroadcast.peRegisters := by rw [nextEq]
  rw [peRegistersNext, l1Commit, sharedFrame, afterMatrixEq, nextBlockFloatEq, nextReluEq,
    nextMslEq, intIdentity]

/-- **The unrefuted-line form.**  The instance is stated for every expression of
the class; this corollary records that it applies in particular under the
`WelcomePEUnrefuted` hypothesis of `WelcomePEL1ToPEShapeObligation`. -/
theorem welcomePEWriteShape_singleton_of_l1bmMemLm1_of_unrefuted
    (expression : NormalizedExpr) (access : ParsedL1ToPEAccess)
    (memoryAccess : Access) (negated extended rounded : Bool) (mask : Option ParsedMask)
    (w : PEMemory.Width)
    (_unrefuted : WelcomePEUnrefuted [expression])
    (lowered : lowerParsedL1ToPE? expression.toParsed = some access)
    (destinations : access.destinations =
      [ParsedOperand.mem memoryAccess negated extended rounded mask])
    (static : ParsedOperand.directDestinationBankWidth?
      (ParsedOperand.mem memoryAccess negated extended rounded mask) =
      some (PEMemory.Bank.lm1, w)) :
    WelcomePEWriteShape [expression] :=
  welcomePEWriteShape_singleton_of_l1bmMemLm1 expression access memoryAccess negated extended
    rounded mask w lowered destinations static

/-! ## 4. A broadcast writer with integer-or-inert companion rows

The single-row instance of §3 uses the fact that the integer stage's list is
empty.  With §1 the argument extends to any line whose *other* rows are
integer/matrix-read stage inputs or PE-inert producers: the middle stages then
have empty producer filters, the shared-block stage is a frame, and the integer
stage's prepared list is `.lm1`-free, so the line's `.lm1` commit is the
broadcast's own and the two shapes compose
(`lm1WritesDoubleCopy_append_of_only_right`).

The companion rows must avoid bank `.lm1` only *after* the integer filter, i.e.
on the rows the integer stage actually prepares; `.noforward` / `.wait` rows
are dropped by that filter and may carry arbitrary destination operands. -/

/-- A predicate that is false on every row of `before` and `after` and on the
distinguished row `e` filters `before ++ e :: after` to the empty list. -/
theorem filter_append_broadcast_nil (before after : List ParsedExpr) (e : ParsedExpr)
    (predicate : ParsedExpr → Bool)
    (beforeFalse : ∀ item ∈ before, predicate item = false)
    (afterFalse : ∀ item ∈ after, predicate item = false)
    (eFalse : predicate e = false) :
    (before ++ e :: after).filter predicate = [] := by
  have beforeNil : before.filter predicate = [] :=
    List.filter_eq_nil_iff.mpr (fun item mem => by rw [beforeFalse item mem]; simp)
  have afterNil : after.filter predicate = [] :=
    List.filter_eq_nil_iff.mpr (fun item mem => by rw [afterFalse item mem]; simp)
  rw [List.filter_append, beforeNil, List.nil_append]
  simp [eFalse, afterNil]

/-- A predicate that is false on every row of `before` and `after` and true on
the distinguished row `e` filters `before ++ e :: after` to `[e]`. -/
theorem filter_append_broadcast_singleton (before after : List ParsedExpr) (e : ParsedExpr)
    (predicate : ParsedExpr → Bool)
    (beforeFalse : ∀ item ∈ before, predicate item = false)
    (afterFalse : ∀ item ∈ after, predicate item = false)
    (eTrue : predicate e = true) :
    (before ++ e :: after).filter predicate = [e] := by
  have beforeNil : before.filter predicate = [] :=
    List.filter_eq_nil_iff.mpr (fun item mem => by rw [beforeFalse item mem]; simp)
  have afterNil : after.filter predicate = [] :=
    List.filter_eq_nil_iff.mpr (fun item mem => by rw [afterFalse item mem]; simp)
  rw [List.filter_append, beforeNil, List.nil_append]
  simp [eTrue, afterNil]

/-- **A broadcast writer plus integer-or-inert companion rows.**  If the parsed
line splits as `before ++ e :: after`, the distinguished row `e` is a `.l1bm`
broadcast with a single `.mem` destination of static bank `.lm1` and width `w`,
and every companion row is an integer/matrix-read stage input or a PE-inert
producer, then the line satisfies `WelcomePEWriteShape`.  The integer stage
prepares the companion rows only (the broadcast is not an integer-stage input),
and those prepared writes are `.lm1`-free by §1; the four middle stages and the
L1BM-to-PE stage are then the empty-filter identities, so the line's write list
is the concatenation of the companions' and the broadcast's lists. -/
theorem welcomePEWriteShape_of_l1bmWriter_of_integerOrInert
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
    WelcomePEWriteShape expressions := by
  apply welcomePEWriteShape_of_commit_shape
  intro next step
  have executed := welcomeSealed_step_ok step
  simp only [executeNormalizedLine, NormalizedLine.toInstruction?,
    Issue.InstructionLine.toNormalizedLine] at executed
  obtain ⟨accepted, waits, unsupported, supported⟩ :=
    executeIntegerProducerInstructionLine_pe_conditions expressions
      (welcomeInitialState welcomeZeroWords) next executed
  obtain ⟨eIntFalse, eFloatFalse, eL2bmFalse, eMslFalse, eReluFalse, eBlockFalse,
    eMmauFalse, eMwriteFalse, eL1True⟩ := l1bmBroadcast_parsedExpr_predicates e access lowered
  -- the companion rows are not producers of the four middle stages, of the
  -- float-MAU stage, or of the L1BM-to-PE stage
  have mslNil : (before ++ e :: after).filter parsedExprIsMslMsrProducer = [] :=
    filter_append_broadcast_nil before after e _
      (fun item mem =>
        (welcomeIntegerOrInertLine_stageFacts item (intOrInertBefore item mem)).2.1)
      (fun item mem =>
        (welcomeIntegerOrInertLine_stageFacts item (intOrInertAfter item mem)).2.1)
      eMslFalse
  have reluNil : (before ++ e :: after).filter parsedExprIsFloatReluProducer = [] :=
    filter_append_broadcast_nil before after e _
      (fun item mem =>
        (welcomeIntegerOrInertLine_stageFacts item (intOrInertBefore item mem)).2.2.2.2.1)
      (fun item mem =>
        (welcomeIntegerOrInertLine_stageFacts item (intOrInertAfter item mem)).2.2.2.2.1)
      eReluFalse
  have blockNil : (before ++ e :: after).filter parsedExprIsBlockFloatProducer = [] :=
    filter_append_broadcast_nil before after e _
      (fun item mem =>
        (welcomeIntegerOrInertLine_stageFacts item (intOrInertBefore item mem)).2.2.2.1)
      (fun item mem =>
        (welcomeIntegerOrInertLine_stageFacts item (intOrInertAfter item mem)).2.2.2.1)
      eBlockFalse
  have mmauNil : (before ++ e :: after).filter parsedExprIsMatrixMAUProducer = [] :=
    filter_append_broadcast_nil before after e _
      (fun item mem =>
        (welcomeIntegerOrInertLine_stageFacts item (intOrInertBefore item mem)).2.2.1)
      (fun item mem =>
        (welcomeIntegerOrInertLine_stageFacts item (intOrInertAfter item mem)).2.2.1)
      eMmauFalse
  have floatNil : (before ++ e :: after).filter
      parsedExprIsSupportedFloatMAUProducer = [] :=
    filter_append_broadcast_nil before after e _
      (fun item mem =>
        (welcomeIntegerOrInertLine_stageFacts item (intOrInertBefore item mem)).2.2.2.2.2.2)
      (fun item mem =>
        (welcomeIntegerOrInertLine_stageFacts item (intOrInertAfter item mem)).2.2.2.2.2.2)
      eFloatFalse
  have l1Filter : (before ++ e :: after).filter parsedExprIsL1ToPEProducer = [e] :=
    filter_append_broadcast_singleton before after e _
      (fun item mem =>
        (welcomeIntegerOrInertLine_stageFacts item (intOrInertBefore item mem)).2.2.2.2.2.1)
      (fun item mem =>
        (welcomeIntegerOrInertLine_stageFacts item (intOrInertAfter item mem)).2.2.2.2.2.1)
      eL1True
  -- peel the successful sealed step into its seven stages
  obtain ⟨nextPEs, nextMsl, nextRelu, nextBlockFloat, afterMatrix, nextShared, nextBroadcast,
    walkExecuted, mslExecuted, reluExecuted, blockExecuted, matrixExecuted, sharedExecuted,
    l1Executed, nextEq⟩ :=
    executeIntegerProducerInstructionLine_pe_stages_exists expressions
      (welcomeInitialState welcomeZeroWords) next accepted waits unsupported supported executed
  rw [decomposition] at walkExecuted
  rw [decomposition] at mslExecuted
  rw [decomposition] at reluExecuted
  rw [decomposition] at blockExecuted
  rw [decomposition] at matrixExecuted
  rw [decomposition] at sharedExecuted
  rw [decomposition] at l1Executed
  -- the outer stage filter keeps every row: companions are integer-or-inert and
  -- the broadcast is none of the five producer families
  have outerId : (before ++ e :: after).filter (fun item =>
      !parsedExprIsL2BMProducer item && !parsedExprIsMslMsrProducer item &&
        !parsedExprIsMatrixMAUProducer item && !parsedExprIsBlockFloatProducer item &&
        !parsedExprIsFloatReluProducer item) = before ++ e :: after := by
    rw [List.filter_eq_self]
    intro item mem
    rcases List.mem_append.mp mem with head | tail
    · exact welcomeIntegerOrInertLine_outerFilter item (intOrInertBefore item head)
    · rcases List.mem_cons.mp tail with rfl | tailMem
      · simp [eL2bmFalse, eMslFalse, eMmauFalse, eBlockFalse, eReluFalse]
      · exact welcomeIntegerOrInertLine_outerFilter item (intOrInertAfter item tailMem)
  rw [outerId] at walkExecuted
  -- the integer stage prepares the companion rows; the broadcast is dropped by
  -- the integer-stage input test
  obtain ⟨intWrites, intSlots, intBars, intPrep, intCommit⟩ :=
    executeIntegerProducerLineAtPEs_prepared (before ++ e :: after) (List.finRange 4096)
      (welcomeInitialState welcomeZeroWords) nextPEs floatNil walkExecuted
      (List.nodup_finRange 4096) welcomePE (List.mem_finRange welcomePE)
  have intFree : ∀ write ∈ intWrites,
      PreparedParsedMaskedWrite.isLm1Write write = false :=
    welcomeIntegerPrep_lm1_free (welcomeInitialState welcomeZeroWords) welcomePE
      (before ++ e :: after) intWrites intSlots intBars intPrep noLm1
  -- the four middle stages are identities on an empty producer filter
  have mslId : executeParsedMslMsrProducers (welcomeInitialState welcomeZeroWords) nextPEs
      (before ++ e :: after)
      (expressions.any (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed))
      (expressions.any (parsedExprHasSingleLineWriteMask ∘ NormalizedExpr.toParsed)) =
      .ok nextPEs :=
    executeParsedMslMsrProducers_eq_self _ _ _ _ _ mslNil
  have nextMslEq : nextMsl = nextPEs := by
    rw [mslId] at mslExecuted
    exact (StepResult.ok.inj mslExecuted).symm
  have reluId : executeParsedFloatReluProducers (welcomeInitialState welcomeZeroWords) nextMsl
      (before ++ e :: after)
      (expressions.any (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed))
      (expressions.any (parsedExprHasSingleLineWriteMask ∘ NormalizedExpr.toParsed)) =
      .ok nextMsl :=
    executeParsedFloatReluProducers_eq_self _ _ _ _ _ reluNil
  have nextReluEq : nextRelu = nextMsl := by
    rw [reluId] at reluExecuted
    exact (StepResult.ok.inj reluExecuted).symm
  have blockId : executeParsedBlockFloatProducer (welcomeInitialState welcomeZeroWords) nextRelu
      (before ++ e :: after)
      (expressions.any (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed))
      (expressions.any (parsedExprHasSingleLineWriteMask ∘ NormalizedExpr.toParsed)) =
      .ok nextRelu :=
    executeParsedBlockFloatProducer_eq_self _ _ _ _ _ blockNil
  have nextBlockFloatEq : nextBlockFloat = nextRelu := by
    rw [blockId] at blockExecuted
    exact (StepResult.ok.inj blockExecuted).symm
  -- the matrix-MAU/write stage preserves every PE register file
  have matrixFrame : afterMatrix.peRegisters welcomePE =
      nextBlockFloat.peRegisters welcomePE :=
    executeParsedMatrixMAUAndWrites_peRegisters_frame_of_noMatrixMAU
      (welcomeInitialState welcomeZeroWords) nextBlockFloat afterMatrix
      (before ++ e :: after)
      (expressions.any (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed))
      (expressions.any (parsedExprHasSingleLineWriteMask ∘ NormalizedExpr.toParsed))
      mmauNil matrixExecuted welcomePE
  -- the shared-block stage is a frame for every row
  have sharedFrame : nextShared.peRegisters = afterMatrix.peRegisters :=
    executeParsedSharedBlockProducers_peRegisters (welcomeInitialState welcomeZeroWords)
      afterMatrix nextShared _ _ sharedExecuted
  -- the L1BM-to-PE stage is the single broadcast producer
  obtain ⟨l1Writes, l1Commit, l1Shape⟩ :=
    executeParsedL1ToPEProducers_mem_lm1_shape welcomeZeroWords nextShared nextBroadcast
      (before ++ e :: after) e access
      (expressions.any (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed))
      (expressions.any (parsedExprHasSingleLineWriteMask ∘ NormalizedExpr.toParsed))
      (parsedL1ToPEPrecedesOMRWriter (before ++ e :: after))
      memoryAccess negated extended rounded mask w lowered destinations static l1Filter l1Executed
  refine ⟨intWrites ++ l1Writes, ?_, ?_⟩
  · have peRegistersNext : next.peRegisters = nextBroadcast.peRegisters := by rw [nextEq]
    rw [peRegistersNext, l1Commit, sharedFrame, matrixFrame, nextBlockFloatEq, nextReluEq,
      nextMslEq, intCommit, ← commitParsedMaskedWrites_append]
  · rcases l1Shape with double | narrow
    · exact Or.inl (lm1WritesDoubleCopy_append_of_only_right intWrites l1Writes double intFree)
    · exact Or.inr (lm1WritesNarrow_append_of_only_right intWrites l1Writes narrow intFree)

end ProofsLean.MNCore
