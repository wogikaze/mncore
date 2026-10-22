import ProofsLean.StageCommitWalk
import ProofsLean.FrameStep

/-! # Line execution algebra for a single-row `.pe` line

The whole-project bottleneck is that no theorem computes
`executeNormalizedLine` on a *concrete* line.  This module builds the generic
algebra that any such computation needs, without mentioning a machine, a
problem, an input or a state predicate:

1. `executeIntegerProducerLineAtPECore_peRegisters_eq` — the per-PE core step
   at an arbitrary state commits exactly `intWrites ++ floatWrites`, where
   `intWrites` is the first component of the integer four-cycle preparation's
   own result (`prepareParsedIntegerMatrixReadLineCycles`, named by an
   equation) and `floatWrites` is the float-MAU stage's own write list, pinned
   by the float stage's own result equation plus the float commit
   (`executeParsedFloatMAUsAtPE_commit`).  Both halves are explicit; no
   existential hides the integer stage's list any more.
2. `executeIntegerProducerLineAtPEs_cons_commit_list` and
   `executeIntegerProducerLineAtPEs_peRegisters_eq` — the same list survives
   the PE walk: when the observed PE is visited first (as `0` is in
   `List.finRange 4096`), the walk's PE-0 file is the commit of the *initial*
   state's prepared list.  Later PEs cannot disturb it
   (`executeIntegerProducerLineAtPEs_peRegisters_of_not_mem`).
3. `executeIntegerProducerInstructionLine_pe_lineExec` and
   `executeNormalizedLine_pe_registers` — the whole line: for a single-row
   `.pe` line whose row is an integer ALU / zero / immediate / matrix-read row
   (or one of the supported float-MAU rows), the six non-integer stages are the
   identity, so the line step is `nextPEs` with only the clock advanced.  The
   line-level statement pins PE 0's commit and gives the frame facts.
4. `executeIntegerProducerLineAtPECore_stateForwardingSlots_eq` and
   `executeNormalizedLine_pe_forwardingSlots` — the post-step forwarding slots
   (`$aluf` / `$mauf` on the next line) in terms of the prepared slots.
5. `executeNormalizedLine_immediate_aluf` — the two-line specialisation: after
   an `imm … $r0v` line, the ALU forwarding slot at PE 0 holds the immediate
   bus, so the next line's `$aluf` read is computed.

No `sorry`, no `admit`, no `native_decide`, no new axioms.
-/

namespace ProofsLean.MNCore

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

open Issue
open PEMemory

/-! ## 1. The per-PE core step commits `intWrites ++ floatWrites`, both pinned -/

/-- **The per-PE core step's register file is the commit of the integer stage's
own preparation list followed by the float-MAU stage's own write list.**

`intWrites` is fixed by the integer four-cycle preparation equation at the
*initial* state, `floatWrites` is fixed by the float-MAU stage's result
equation together with the float commit
(`executeParsedFloatMAUsAtPE_commit`).  The state is arbitrary and the only
assumption is that the step succeeds. -/
theorem executeIntegerProducerLineAtPECore_peRegisters_eq
    (expressions : List ParsedExpr) (state next : State) (pe : PEId)
    (executed : executeIntegerProducerLineAtPECore expressions state pe = .ok next) :
    ∃ (intWrites : List PreparedParsedMaskedWrite)
      (intSlots : ProofsLean.MNCore.Forwarding.Slots)
      (intBars : List (Bool × BitVec 12))
      (floatFiles : IntegerRegisterFiles)
      (floatBar0 floatBar1 : BitVec 12)
      (floatOutputs : Fin 4 → IntegerALU.Bus)
      (hasMAUProducer : Bool)
      (floatWrites : List PreparedParsedMaskedWrite),
      prepareParsedIntegerMatrixReadLineCycles (state.peRegisters pe)
          (stateForwardingSlots state pe)
          (state.matrixRegisters (ParsedIntegerContext.ofLinearIndex pe).group
            (ParsedIntegerContext.ofLinearIndex pe).l2b
            (ParsedIntegerContext.ofLinearIndex pe).l1b)
          (expressions.filter parsedExprIsIntegerMatrixReadStageInput)
          { directive := state.maskDirective
            context :=
              { (ParsedIntegerContext.ofLinearIndex pe) with
                bar0 := (state.peContext pe).bar0
                bar1 := (state.peContext pe).bar1
                tWord := (state.peContext pe).tWord }
            elapsedWords := state.hazardClock } false = .ok (intWrites, intSlots, intBars) ∧
      executeParsedFloatMAUsAtPE (state.peRegisters pe)
          (commitParsedMaskedWrites (state.peRegisters pe) intWrites)
          (stateForwardingSlots state pe)
          { (ParsedIntegerContext.ofLinearIndex pe) with
            bar0 := (state.peContext pe).bar0
            bar1 := (state.peContext pe).bar1
            tWord := (state.peContext pe).tWord }
          expressions state.maskDirective
          (expressions.any parsedExprHasSingleLineWriteMask) =
        .ok (floatFiles, floatBar0, floatBar1, floatOutputs, hasMAUProducer) ∧
      floatFiles =
        commitParsedMaskedWrites
          (commitParsedMaskedWrites (state.peRegisters pe) intWrites) floatWrites ∧
      next.peRegisters pe =
        commitParsedMaskedWrites (state.peRegisters pe) (intWrites ++ floatWrites) := by
  unfold executeIntegerProducerLineAtPECore parsedIntegerMatrixReadLineFourCycleStep at executed
  dsimp only at executed
  cases preparedEq : prepareParsedIntegerMatrixReadLineCycles (state.peRegisters pe)
      (stateForwardingSlots state pe)
      (state.matrixRegisters (ParsedIntegerContext.ofLinearIndex pe).group
        (ParsedIntegerContext.ofLinearIndex pe).l2b
        (ParsedIntegerContext.ofLinearIndex pe).l1b)
      (expressions.filter parsedExprIsIntegerMatrixReadStageInput)
      { directive := state.maskDirective
        context :=
          { (ParsedIntegerContext.ofLinearIndex pe) with
            bar0 := (state.peContext pe).bar0
            bar1 := (state.peContext pe).bar1
            tWord := (state.peContext pe).tWord }
        elapsedWords := state.hazardClock } false with
  | failure =>
      simp only [preparedEq] at executed
      simp at executed
  | unknown =>
      simp only [preparedEq] at executed
      simp at executed
  | ok prepared =>
      obtain ⟨intWrites, intSlots, intBars⟩ := prepared
      simp only [preparedEq] at executed
      cases floatEq : executeParsedFloatMAUsAtPE (state.peRegisters pe)
          (commitParsedMaskedWrites (state.peRegisters pe) intWrites)
          (stateForwardingSlots state pe)
          { (ParsedIntegerContext.ofLinearIndex pe) with
            bar0 := (state.peContext pe).bar0
            bar1 := (state.peContext pe).bar1
            tWord := (state.peContext pe).tWord }
          expressions state.maskDirective
          (expressions.any parsedExprHasSingleLineWriteMask) with
      | failure =>
          simp only [floatEq] at executed
          simp at executed
      | unknown =>
          simp only [floatEq] at executed
          simp at executed
      | ok floatResult =>
          obtain ⟨floatFiles, floatBar0, floatBar1, floatOutputs, hasMAUProducer⟩ := floatResult
          have floatEq' : executeParsedFloatMAUsAtPE (state.peRegisters pe)
              (commitParsedMaskedWrites (state.peRegisters pe) intWrites)
              (stateForwardingSlots state pe)
              { (ParsedIntegerContext.ofLinearIndex pe) with
                bar0 := (state.peContext pe).bar0
                bar1 := (state.peContext pe).bar1
                tWord := (state.peContext pe).tWord }
              expressions state.maskDirective
              (expressions.any parsedExprHasSingleLineWriteMask) =
              .ok (floatFiles, floatBar0, floatBar1, floatOutputs, hasMAUProducer) := floatEq
          obtain ⟨floatWrites, floatCommitted⟩ :=
            executeParsedFloatMAUsAtPE_commit (state.peRegisters pe)
              (commitParsedMaskedWrites (state.peRegisters pe) intWrites)
              (stateForwardingSlots state pe)
              { (ParsedIntegerContext.ofLinearIndex pe) with
                bar0 := (state.peContext pe).bar0
                bar1 := (state.peContext pe).bar1
                tWord := (state.peContext pe).tWord }
              expressions state.maskDirective (expressions.any parsedExprHasSingleLineWriteMask)
              floatFiles floatBar0 floatBar1 floatOutputs hasMAUProducer floatEq
          simp only [floatEq] at executed
          split at executed
          · simp at executed
          · simp at executed
          · refine ⟨intWrites, intSlots, intBars, floatFiles, floatBar0, floatBar1,
              floatOutputs, hasMAUProducer, floatWrites, rfl, floatEq', floatCommitted, ?_⟩
            simp only [StepResult.ok.injEq] at executed
            subst executed
            simpa [commitParsedMaskedWrites_append] using floatCommitted

/-- **The per-PE core step's committed list, with the integer stage's own list
named.**  A compact form of `executeIntegerProducerLineAtPECore_peRegisters_eq`:
`intWrites` is fixed by the integer stage's preparation equation. -/
theorem executeIntegerProducerLineAtPECore_peRegisters_commit_list_explicit
    (expressions : List ParsedExpr) (state next : State) (pe : PEId)
    (executed : executeIntegerProducerLineAtPECore expressions state pe = .ok next) :
    ∃ (intWrites floatWrites : List PreparedParsedMaskedWrite)
      (intSlots : ProofsLean.MNCore.Forwarding.Slots)
      (intBars : List (Bool × BitVec 12)),
      prepareParsedIntegerMatrixReadLineCycles (state.peRegisters pe)
          (stateForwardingSlots state pe)
          (state.matrixRegisters (ParsedIntegerContext.ofLinearIndex pe).group
            (ParsedIntegerContext.ofLinearIndex pe).l2b
            (ParsedIntegerContext.ofLinearIndex pe).l1b)
          (expressions.filter parsedExprIsIntegerMatrixReadStageInput)
          { directive := state.maskDirective
            context :=
              { (ParsedIntegerContext.ofLinearIndex pe) with
                bar0 := (state.peContext pe).bar0
                bar1 := (state.peContext pe).bar1
                tWord := (state.peContext pe).tWord }
            elapsedWords := state.hazardClock } false = .ok (intWrites, intSlots, intBars) ∧
      next.peRegisters pe =
        commitParsedMaskedWrites (state.peRegisters pe) (intWrites ++ floatWrites) := by
  obtain ⟨intWrites, intSlots, intBars, floatFiles, floatBar0, floatBar1, floatOutputs,
    hasMAUProducer, floatWrites, preparedEq, floatEq, floatCommit, committed⟩ :=
    executeIntegerProducerLineAtPECore_peRegisters_eq expressions state next pe executed
  exact ⟨intWrites, floatWrites, intSlots, intBars, preparedEq, committed⟩

/-! ## 2. The PE walk keeps the committed list at a PE visited first -/

/-- **The walk-level pinned commit, for a PE visited first.**  If the observed
PE heads the walked list (and is not revisited), the resulting file at that PE
is the commit of the *initial* state's prepared list. -/
theorem executeIntegerProducerLineAtPEs_cons_commit_list
    (expressions : List ParsedExpr) (pe : PEId) (rest : List PEId)
    (state next : State)
    (absent : pe ∉ rest)
    (executed : executeIntegerProducerLineAtPEs expressions (pe :: rest) state = .ok next) :
    ∃ (intWrites floatWrites : List PreparedParsedMaskedWrite)
      (intSlots : ProofsLean.MNCore.Forwarding.Slots)
      (intBars : List (Bool × BitVec 12)),
      prepareParsedIntegerMatrixReadLineCycles (state.peRegisters pe)
          (stateForwardingSlots state pe)
          (state.matrixRegisters (ParsedIntegerContext.ofLinearIndex pe).group
            (ParsedIntegerContext.ofLinearIndex pe).l2b
            (ParsedIntegerContext.ofLinearIndex pe).l1b)
          (expressions.filter parsedExprIsIntegerMatrixReadStageInput)
          { directive := state.maskDirective
            context :=
              { (ParsedIntegerContext.ofLinearIndex pe) with
                bar0 := (state.peContext pe).bar0
                bar1 := (state.peContext pe).bar1
                tWord := (state.peContext pe).tWord }
            elapsedWords := state.hazardClock } false = .ok (intWrites, intSlots, intBars) ∧
      next.peRegisters pe =
        commitParsedMaskedWrites (state.peRegisters pe) (intWrites ++ floatWrites) := by
  simp only [executeIntegerProducerLineAtPEs] at executed
  split at executed
  · simp at executed
  · simp at executed
  · rename_i middle stepMiddle
    obtain ⟨intWrites, floatWrites, intSlots, intBars, preparedEq, committed⟩ :=
      executeIntegerProducerLineAtPECore_peRegisters_commit_list_explicit expressions state
        middle pe (by
          unfold executeIntegerProducerLineAtPE at stepMiddle
          split at stepMiddle
          · simp at stepMiddle
          · exact stepMiddle)
    refine ⟨intWrites, floatWrites, intSlots, intBars, preparedEq, ?_⟩
    rw [executeIntegerProducerLineAtPEs_peRegisters_of_not_mem expressions rest middle next
      pe absent executed]
    exact committed

/-- `List.finRange 4096` starts with PE 0. -/
theorem finRange4096_eq_welcomePE_cons :
    List.finRange 4096 = welcomePE :: (List.finRange 4095).map Fin.succ := by
  have h : List.finRange (4095 + 1) =
      (0 : Fin (4095 + 1)) :: (List.finRange 4095).map Fin.succ := List.finRange_succ
  have h' : List.finRange 4096 =
      (0 : Fin 4096) :: (List.finRange 4095).map Fin.succ := h
  rw [h']
  rw [show (0 : Fin 4096) = welcomePE from Fin.ext rfl]

/-- PE 0 is not revisited by the tail of `List.finRange 4096`. -/
theorem welcomePE_not_mem_finRange4095_map_succ :
    welcomePE ∉ (List.finRange 4095).map Fin.succ := by
  intro member
  obtain ⟨index, _, equation⟩ := List.mem_map.mp member
  have value := congrArg Fin.val equation
  have zero : welcomePE.val = 0 := rfl
  have succ : (Fin.succ index).val = index.val + 1 := rfl
  omega

/-- **The walk over `List.finRange 4096` commits the pinned list at PE 0.** -/
theorem executeIntegerProducerLineAtPEs_peRegisters_eq
    (expressions : List ParsedExpr) (state next : State)
    (executed : executeIntegerProducerLineAtPEs expressions (List.finRange 4096) state
      = .ok next) :
    ∃ (intWrites floatWrites : List PreparedParsedMaskedWrite)
      (intSlots : ProofsLean.MNCore.Forwarding.Slots)
      (intBars : List (Bool × BitVec 12)),
      prepareParsedIntegerMatrixReadLineCycles (state.peRegisters welcomePE)
          (stateForwardingSlots state welcomePE)
          (state.matrixRegisters (ParsedIntegerContext.ofLinearIndex welcomePE).group
            (ParsedIntegerContext.ofLinearIndex welcomePE).l2b
            (ParsedIntegerContext.ofLinearIndex welcomePE).l1b)
          (expressions.filter parsedExprIsIntegerMatrixReadStageInput)
          { directive := state.maskDirective
            context :=
              { (ParsedIntegerContext.ofLinearIndex welcomePE) with
                bar0 := (state.peContext welcomePE).bar0
                bar1 := (state.peContext welcomePE).bar1
                tWord := (state.peContext welcomePE).tWord }
            elapsedWords := state.hazardClock } false = .ok (intWrites, intSlots, intBars) ∧
      next.peRegisters welcomePE =
        commitParsedMaskedWrites (state.peRegisters welcomePE) (intWrites ++ floatWrites) := by
  rw [finRange4096_eq_welcomePE_cons] at executed
  exact executeIntegerProducerLineAtPEs_cons_commit_list expressions welcomePE
    ((List.finRange 4095).map Fin.succ) state next welcomePE_not_mem_finRange4095_map_succ
    executed

/-! ## 3. The line level: a single row whose only stages are integer + float MAU -/

/-- **The rows this module executes end to end.**  An `.alu` / `.zero` /
`.immediate` / `.matrixRead` row (with no legacy Rust-unsupported ALU name, no
MSL/MSR, no float-relu and no block-float operation), or a supported float-MAU
row.  For every such row all six non-integer stages of
`executeIntegerProducerInstructionLine` are the identity, so the line step is
the PE walk plus a clock advance. -/
def parsedExprIsLineExecRow (expression : ParsedExpr) : Bool :=
  (match expression.op with
    | .alu .. | .zero | .immediate .. | .matrixRead .. => true
    | _ => parsedExprIsSupportedFloatMAUProducer expression) &&
    !parsedExprIsUnsupportedRustAlu expression &&
    !parsedExprIsMslMsrProducer expression &&
    !parsedExprIsFloatReluProducer expression &&
    !parsedExprIsBlockFloatProducer expression

/-- A line-exec row is supported and is none of the special families. -/
theorem parsedExprIsLineExecRow_facts (expression : ParsedExpr)
    (row : parsedExprIsLineExecRow expression = true) :
    parsedExprIsSupportedPELineProducer expression = true ∧
    parsedExprIsUnsupportedRustAlu expression = false ∧
    parsedExprWaitTag? expression = none ∧
    parsedExprIsMatrixMAUProducer expression = false ∧
    parsedExprIsMatrixWriteProducer expression = false ∧
    parsedExprIsMslMsrProducer expression = false ∧
    parsedExprIsFloatReluProducer expression = false ∧
    parsedExprIsBlockFloatProducer expression = false ∧
    parsedExprIsL1ToPEProducer expression = false ∧
    parsedExprIsL2BMProducer expression = false ∧
    parsedExprIsNoForwardProducer expression = false ∧
    parsedExprMayWriteL1BMTurnaround expression = false := by
  cases expression with
  | mk op sources destinations flush text =>
      simp only [parsedExprIsLineExecRow, Bool.and_eq_true] at *
      cases op with
      | alu name precision unsigned arg =>
          exact ⟨rfl, by simpa using row.1.1.1.2, rfl, rfl, rfl, by simpa using row.1.1.2,
            by simpa using row.1.2, by simpa using row.2, rfl, rfl, rfl, rfl⟩
      | zero =>
          exact ⟨rfl, by simpa using row.1.1.1.2, rfl, rfl, rfl, by simpa using row.1.1.2,
            by simpa using row.1.2, by simpa using row.2, rfl, rfl, rfl, rfl⟩
      | immediate value unsigned =>
          exact ⟨rfl, by simpa using row.1.1.1.2, rfl, rfl, rfl, by simpa using row.1.1.2,
            by simpa using row.1.2, by simpa using row.2, rfl, rfl, rfl, rfl⟩
      | matrixRead precision => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      | matrixWrite precision =>
          exact absurd row.1.1.1.1 (by simp [parsedExprIsSupportedFloatMAUProducer])
      | wait tag =>
          exact absurd row.1.1.1.1 (by simp [parsedExprIsSupportedFloatMAUProducer])
      | noforward =>
          exact absurd row.1.1.1.1 (by simp [parsedExprIsSupportedFloatMAUProducer])
      | l1bm operation =>
          exact absurd row.1.1.1.1 (by simp [parsedExprIsSupportedFloatMAUProducer])
      | l2bm operation =>
          exact absurd row.1.1.1.1 (by simp [parsedExprIsSupportedFloatMAUProducer])
      | mau precision matrix kind half round =>
          cases precision <;> cases matrix <;> cases kind <;> cases half <;> cases round <;>
            simp_all only [parsedExprIsLineExecRow, parsedExprIsSupportedFloatMAUProducer,
              parsedExprIsSupportedPELineProducer, parsedExprIsUnsupportedRustAlu,
              parsedExprWaitTag?, parsedExprIsMatrixMAUProducer,
              parsedExprIsMatrixWriteProducer, parsedExprIsMslMsrProducer,
              parsedExprIsFloatReluProducer, parsedExprIsBlockFloatProducer,
              parsedExprIsL1ToPEProducer, parsedExprIsL2BMProducer,
              parsedExprIsNoForwardProducer, parsedExprMayWriteL1BMTurnaround,
              parsedOpMayWriteL1BMTurnaround, true_and, and_true]

/-- A line-exec row's shared-block stage is the identity at any state. -/
theorem executeParsedSharedBlockExpression_lineExecRow
    (readState currentState : State) (expression : ParsedExpr) (updateTurnaround : Bool)
    (row : parsedExprIsLineExecRow expression = true) :
    executeParsedSharedBlockExpression readState currentState expression updateTurnaround =
      .ok currentState := by
  cases expression with
  | mk op sources destinations flush text =>
      simp only [parsedExprIsLineExecRow, Bool.and_eq_true] at *
      cases op with
      | alu name precision unsigned arg => rfl
      | zero => rfl
      | immediate value unsigned => rfl
      | mau precision matrix kind half round => rfl
      | matrixWrite precision => rfl
      | matrixRead precision => rfl
      | wait tag => rfl
      | noforward => rfl
      | l1bm operation =>
          exact absurd row.1.1.1.1 (by simp [parsedExprIsSupportedFloatMAUProducer])
      | l2bm operation =>
          exact absurd row.1.1.1.1 (by simp [parsedExprIsSupportedFloatMAUProducer])

/-- **The six non-integer stages of a line-exec row are the identity.** -/
theorem lineExecRow_stage_identities (normalizedExpressions : List NormalizedExpr)
    (state : State)
    (rows : (normalizedExpressions.map NormalizedExpr.toParsed).all
      parsedExprIsLineExecRow = true) :
    (∀ currentState noForward hasSingleLineMask,
      executeParsedMslMsrProducers state currentState
        (normalizedExpressions.map NormalizedExpr.toParsed) noForward hasSingleLineMask
        = .ok currentState) ∧
    (∀ currentState noForward hasSingleLineMask,
      executeParsedFloatReluProducers state currentState
        (normalizedExpressions.map NormalizedExpr.toParsed) noForward hasSingleLineMask
        = .ok currentState) ∧
    (∀ currentState noForward hasSingleLineMask,
      executeParsedBlockFloatProducer state currentState
        (normalizedExpressions.map NormalizedExpr.toParsed) noForward hasSingleLineMask
        = .ok currentState) ∧
    (∀ currentState noForward hasSingleLineMask,
      executeParsedMatrixMAUAndWrites state currentState
        (normalizedExpressions.map NormalizedExpr.toParsed) noForward hasSingleLineMask
        = .ok currentState) ∧
    (∀ currentState updateTurnaround,
      executeParsedSharedBlockProducers state currentState
        (normalizedExpressions.map NormalizedExpr.toParsed) updateTurnaround
        = .ok currentState) ∧
    (∀ currentState noForward hasSingleLineMask usePreIssueMask,
      executeParsedL1ToPEProducers state currentState
        (normalizedExpressions.map NormalizedExpr.toParsed) noForward hasSingleLineMask
        usePreIssueMask = .ok currentState) ∧
    (normalizedExpressions.map NormalizedExpr.toParsed).all
      parsedExprIsSupportedPELineProducer = true ∧
    (normalizedExpressions.map NormalizedExpr.toParsed).any
      parsedExprIsUnsupportedRustAlu = false ∧
    (normalizedExpressions.map NormalizedExpr.toParsed).any
      (parsedExprWaitPending state) = false ∧
    (normalizedExpressions.map NormalizedExpr.toParsed).any
      parsedExprIsNoForwardProducer = false ∧
    (normalizedExpressions.map NormalizedExpr.toParsed).any
      parsedExprMayWriteL1BMTurnaround = false ∧
    (normalizedExpressions.map NormalizedExpr.toParsed).filter (fun expression =>
      !parsedExprIsL2BMProducer expression && !parsedExprIsMslMsrProducer expression &&
        !parsedExprIsMatrixMAUProducer expression &&
        !parsedExprIsBlockFloatProducer expression &&
        !parsedExprIsFloatReluProducer expression) =
      normalizedExpressions.map NormalizedExpr.toParsed := by
  let expressions := normalizedExpressions.map NormalizedExpr.toParsed
  have all := List.all_eq_true.mp rows
  have facts : ∀ expression ∈ expressions, parsedExprIsLineExecRow expression = true :=
    fun expression member => all expression member
  have supported : expressions.all parsedExprIsSupportedPELineProducer = true :=
    List.all_eq_true.mpr fun expression member =>
      (parsedExprIsLineExecRow_facts expression (facts expression member)).1
  have notUnsupported : expressions.any parsedExprIsUnsupportedRustAlu = false :=
    List.any_eq_false.mpr fun expression member => by
      simpa using (parsedExprIsLineExecRow_facts expression (facts expression member)).2.1
  have noWait : expressions.any (parsedExprWaitPending state) = false :=
    List.any_eq_false.mpr fun expression member => by
      simp [parsedExprWaitPending,
        (parsedExprIsLineExecRow_facts expression (facts expression member)).2.2.1]
  have noForward : expressions.any parsedExprIsNoForwardProducer = false :=
    List.any_eq_false.mpr fun expression member => by
      simpa using (parsedExprIsLineExecRow_facts expression (facts expression member)).2.2.2.2.2.2.2.2.2.2.1
  have noTurnaround : expressions.any parsedExprMayWriteL1BMTurnaround = false :=
    List.any_eq_false.mpr fun expression member => by
      simpa using (parsedExprIsLineExecRow_facts expression (facts expression member)).2.2.2.2.2.2.2.2.2.2.2
  have mslEmpty : expressions.filter parsedExprIsMslMsrProducer = [] :=
    List.filter_eq_nil_iff.mpr fun expression member => by
      simpa using (parsedExprIsLineExecRow_facts expression (facts expression member)).2.2.2.2.2.1
  have reluEmpty : expressions.filter parsedExprIsFloatReluProducer = [] :=
    List.filter_eq_nil_iff.mpr fun expression member => by
      simpa using (parsedExprIsLineExecRow_facts expression (facts expression member)).2.2.2.2.2.2.1
  have blockEmpty : expressions.filter parsedExprIsBlockFloatProducer = [] :=
    List.filter_eq_nil_iff.mpr fun expression member => by
      simpa using (parsedExprIsLineExecRow_facts expression (facts expression member)).2.2.2.2.2.2.2.1
  have mauEmpty : expressions.filter parsedExprIsMatrixMAUProducer = [] :=
    List.filter_eq_nil_iff.mpr fun expression member => by
      simpa using (parsedExprIsLineExecRow_facts expression (facts expression member)).2.2.2.1
  have noWrite : expressions.any parsedExprIsMatrixWriteProducer = false :=
    List.any_eq_false.mpr fun expression member => by
      simpa using (parsedExprIsLineExecRow_facts expression (facts expression member)).2.2.2.2.1
  have l1ToPEEmpty : expressions.filter parsedExprIsL1ToPEProducer = [] :=
    List.filter_eq_nil_iff.mpr fun expression member => by
      simpa using (parsedExprIsLineExecRow_facts expression (facts expression member)).2.2.2.2.2.2.2.2.1
  have l2bmEmpty : (expressions.filter (fun expression =>
      !parsedExprIsL2BMProducer expression && !parsedExprIsMslMsrProducer expression &&
        !parsedExprIsMatrixMAUProducer expression &&
        !parsedExprIsBlockFloatProducer expression &&
        !parsedExprIsFloatReluProducer expression)) = expressions := by
    apply List.filter_eq_self.mpr
    intro expression member
    have h1 : parsedExprIsL2BMProducer expression = false :=
      (parsedExprIsLineExecRow_facts expression (facts expression member)).2.2.2.2.2.2.2.2.2.1
    have h2 : parsedExprIsMslMsrProducer expression = false :=
      (parsedExprIsLineExecRow_facts expression (facts expression member)).2.2.2.2.2.1
    have h3 : parsedExprIsMatrixMAUProducer expression = false :=
      (parsedExprIsLineExecRow_facts expression (facts expression member)).2.2.2.1
    have h4 : parsedExprIsBlockFloatProducer expression = false :=
      (parsedExprIsLineExecRow_facts expression (facts expression member)).2.2.2.2.2.2.2.1
    have h5 : parsedExprIsFloatReluProducer expression = false :=
      (parsedExprIsLineExecRow_facts expression (facts expression member)).2.2.2.2.2.2.1
    simp [h1, h2, h3, h4, h5]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro currentState noForward hasSingleLineMask
    exact executeParsedMslMsrProducers_nil state currentState expressions noForward _
      mslEmpty
  · intro currentState noForward hasSingleLineMask
    exact executeParsedFloatReluProducers_nil state currentState expressions noForward _
      reluEmpty
  · intro currentState noForward hasSingleLineMask
    exact executeParsedBlockFloatProducer_nil state currentState expressions noForward _
      blockEmpty
  · intro currentState noForward hasSingleLineMask
    exact executeParsedMatrixMAUAndWrites_id state currentState expressions noForward _
      mauEmpty noWrite
  · intro currentState updateTurnaround
    exact executeParsedSharedBlockProducerList_eq_self state updateTurnaround expressions
      currentState (fun expression member =>
        executeParsedSharedBlockExpression_lineExecRow state currentState expression
          updateTurnaround (facts expression member))
  · intro currentState noForward hasSingleLineMask usePreIssueMask
    exact executeParsedL1ToPEProducers_nil state currentState expressions noForward _
      usePreIssueMask l1ToPEEmpty
  · exact supported
  · exact notUnsupported
  · exact noWait
  · exact noForward
  · exact noTurnaround
  · exact l2bmEmpty

/-- **The line step of a single-row `.pe` line with only line-exec rows.**  All
six non-integer stages are the identity, so the resulting state is the walk's
result with only the clock advanced and the L1BM turnaround valid bit cleared. -/
theorem executeIntegerProducerInstructionLine_pe_lineExec
    (normalizedExpressions : List NormalizedExpr) (state nextPEs : State)
    (accepted : checkParsedTopLine
      (InstructionLine.pe normalizedExpressions).toParsed = true)
    (rows : (normalizedExpressions.map NormalizedExpr.toParsed).all
      parsedExprIsLineExecRow = true)
    (executed : executeIntegerProducerLineAtPEs
      ((normalizedExpressions.map NormalizedExpr.toParsed).filter (fun expression =>
        !parsedExprIsL2BMProducer expression && !parsedExprIsMslMsrProducer expression &&
          !parsedExprIsMatrixMAUProducer expression &&
          !parsedExprIsBlockFloatProducer expression &&
          !parsedExprIsFloatReluProducer expression))
      (List.finRange 4096) state = .ok nextPEs) :
    executeIntegerProducerInstructionLine (.pe normalizedExpressions) state =
      .ok { nextPEs with
        hazardClock := nextPEs.hazardClock + InstructionLine.cost (.pe normalizedExpressions)
        l1bmTurnaroundValid := false } := by
  obtain ⟨mslId, reluId, blockId, matrixId, sharedId, l1ToPEId, supportedAny,
    noUnsupportedAny, waitsAny, noForwardAny, noTurnaroundAny, _⟩ :=
    lineExecRow_stage_identities normalizedExpressions state rows
  simp [executeIntegerProducerInstructionLine, accepted, supportedAny, noUnsupportedAny,
    waitsAny, mslId, reluId, blockId, matrixId, sharedId, l1ToPEId, noForwardAny,
    noTurnaroundAny]
  rw [executed]

/-- **Extraction: a successful step yields the walk result.** -/
theorem executeIntegerProducerInstructionLine_pe_lineExec_exists
    (normalizedExpressions : List NormalizedExpr) (state next : State)
    (accepted : checkParsedTopLine
      (InstructionLine.pe normalizedExpressions).toParsed = true)
    (rows : (normalizedExpressions.map NormalizedExpr.toParsed).all
      parsedExprIsLineExecRow = true)
    (success : executeIntegerProducerInstructionLine (.pe normalizedExpressions) state
      = .ok next) :
    ∃ nextPEs,
      executeIntegerProducerLineAtPEs
        ((normalizedExpressions.map NormalizedExpr.toParsed).filter (fun expression =>
          !parsedExprIsL2BMProducer expression && !parsedExprIsMslMsrProducer expression &&
            !parsedExprIsMatrixMAUProducer expression &&
            !parsedExprIsBlockFloatProducer expression &&
            !parsedExprIsFloatReluProducer expression))
        (List.finRange 4096) state = .ok nextPEs ∧
      next = { nextPEs with
        hazardClock := nextPEs.hazardClock + InstructionLine.cost (.pe normalizedExpressions)
        l1bmTurnaroundValid := false } := by
  obtain ⟨mslId, reluId, blockId, matrixId, sharedId, l1ToPEId, supportedAny,
    noUnsupportedAny, waitsAny, noForwardAny, noTurnaroundAny, _⟩ :=
    lineExecRow_stage_identities normalizedExpressions state rows
  unfold executeIntegerProducerInstructionLine at success
  simp [accepted, supportedAny, noUnsupportedAny, waitsAny, mslId, reluId, blockId,
    matrixId, sharedId, l1ToPEId, noForwardAny, noTurnaroundAny] at success
  split at success
  · simp at success
  · simp at success
  · rename_i nextPEs walked
    refine ⟨nextPEs, walked, ?_⟩
    simp only [StepResult.ok.injEq] at success
    exact success.symm

/-! ### Frame facts of the walk and of the line step -/

/-- The per-PE core step preserves the mask directive and the hazard clock. -/
theorem executeIntegerProducerLineAtPECore_maskDirective_hazardClock
    (expressions : List ParsedExpr) (state next : State) (pe : PEId)
    (executed : executeIntegerProducerLineAtPECore expressions state pe = .ok next) :
    next.maskDirective = state.maskDirective ∧ next.hazardClock = state.hazardClock := by
  rw [executeIntegerProducerLineAtPECore.eq_1] at executed
  split at executed
  · simp at executed
  · simp at executed
  · split at executed
    · simp at executed
    · simp at executed
    · simp only [updateSupportedPELineForwarding] at executed
      split at executed
      · simp at executed
      · simp at executed
      · simp only [StepResult.ok.injEq] at executed
        subst executed
        exact ⟨rfl, rfl⟩

/-- The per-PE step preserves the mask directive and the hazard clock. -/
theorem executeIntegerProducerLineAtPE_maskDirective_hazardClock
    (expressions : List ParsedExpr) (state next : State) (pe : PEId)
    (executed : executeIntegerProducerLineAtPE expressions state pe = .ok next) :
    next.maskDirective = state.maskDirective ∧ next.hazardClock = state.hazardClock := by
  unfold executeIntegerProducerLineAtPE at executed
  split at executed
  · simp at executed
  · exact executeIntegerProducerLineAtPECore_maskDirective_hazardClock expressions state next
      pe executed

/-- The walk preserves the mask directive and the hazard clock. -/
theorem executeIntegerProducerLineAtPEs_maskDirective_hazardClock
    (expressions : List ParsedExpr) (pes : List PEId) (state next : State)
    (executed : executeIntegerProducerLineAtPEs expressions pes state = .ok next) :
    next.maskDirective = state.maskDirective ∧ next.hazardClock = state.hazardClock := by
  induction pes generalizing state with
  | nil =>
      simp only [executeIntegerProducerLineAtPEs, StepResult.ok.injEq] at executed
      subst executed
      exact ⟨rfl, rfl⟩
  | cons pe rest ih =>
      simp only [executeIntegerProducerLineAtPEs] at executed
      split at executed
      · simp at executed
      · simp at executed
      · rename_i middle headExecuted
        have head := executeIntegerProducerLineAtPE_maskDirective_hazardClock expressions
          state middle pe headExecuted
        have tail := ih middle executed
        exact ⟨tail.1.trans head.1, tail.2.trans head.2⟩

/-- **Frame facts of a line-exec walk**: the mask directive and the clock. -/
theorem executeIntegerProducerInstructionLine_pe_lineExec_frame
    (normalizedExpressions : List NormalizedExpr) (state nextPEs : State)
    (executed : executeIntegerProducerLineAtPEs
      ((normalizedExpressions.map NormalizedExpr.toParsed).filter (fun expression =>
        !parsedExprIsL2BMProducer expression && !parsedExprIsMslMsrProducer expression &&
          !parsedExprIsMatrixMAUProducer expression &&
          !parsedExprIsBlockFloatProducer expression &&
          !parsedExprIsFloatReluProducer expression))
      (List.finRange 4096) state = .ok nextPEs) :
    nextPEs.maskDirective = state.maskDirective ∧
    nextPEs.hazardClock = state.hazardClock :=
  executeIntegerProducerLineAtPEs_maskDirective_hazardClock _ (List.finRange 4096) state
    nextPEs executed

/-- A successful walk commits a write list at every PE it visits. -/
theorem executeIntegerProducerLineAtPEs_peRegisters_commit_all
    (expressions : List ParsedExpr) (pes : List PEId) (state next : State)
    (executed : executeIntegerProducerLineAtPEs expressions pes state = .ok next)
    (nodup : pes.Nodup) (p : PEId) (mem : p ∈ pes) :
    ∃ writes, next.peRegisters p =
      commitParsedMaskedWrites (state.peRegisters p) writes := by
  induction pes generalizing state with
  | nil => simp at mem
  | cons pe rest ih =>
      obtain ⟨peNotRest, restNodup⟩ := List.nodup_cons.mp nodup
      simp only [executeIntegerProducerLineAtPEs] at executed
      split at executed
      · simp at executed
      · simp at executed
      · rename_i middle headExecuted
        by_cases same : p = pe
        · have headCommit : ∃ writes, middle.peRegisters pe =
              commitParsedMaskedWrites (state.peRegisters pe) writes := by
            unfold executeIntegerProducerLineAtPE at headExecuted
            split at headExecuted
            · simp at headExecuted
            · exact executeIntegerProducerLineAtPECore_peRegisters_commit_float
                expressions state middle pe headExecuted
          have pNotRest : p ∉ rest := by
            rw [same]
            exact peNotRest
          have tailFrame := executeIntegerProducerLineAtPEs_peRegisters_of_not_mem
            expressions rest middle next p pNotRest executed
          obtain ⟨writes, committed⟩ := headCommit
          refine ⟨writes, ?_⟩
          rw [tailFrame, same]
          exact committed
        · have pMem : p ∈ rest := by
            rcases List.mem_cons.mp mem with h | h
            · exact False.elim (same h)
            · exact h
          obtain ⟨writes, tailCommit⟩ := ih middle executed restNodup pMem
          have headFrame := executeIntegerProducerLineAtPE_peRegisters_other expressions
            state middle pe p same headExecuted
          exact ⟨writes, by rw [tailCommit, headFrame]⟩

/-- **The line-level register statement.**  For a successful `.pe` step of a
single-row line whose row is a line-exec row:

* PE 0's register file is the commit of the pinned list `intWrites ++
  floatWrites` prepared from the *initial* state at PE 0 — `intWrites` by the
  integer stage's own preparation equation, `floatWrites` by the float-MAU
  stage's own commit;
* every PE's file is a commit of that PE's own entry file, so the step never
  invents register data;
* the mask directive, L1BM, block memory, DAR state and matrix registers are
  untouched. -/
theorem executeNormalizedLine_pe_registers
    (normalizedExpressions : List NormalizedExpr) (state next : State)
    (accepted : checkParsedTopLine
      (InstructionLine.pe normalizedExpressions).toParsed = true)
    (rows : (normalizedExpressions.map NormalizedExpr.toParsed).all
      parsedExprIsLineExecRow = true)
    (executed : executeNormalizedLine (.pe normalizedExpressions) state = .ok next) :
    (∃ (intWrites floatWrites : List PreparedParsedMaskedWrite)
        (intSlots : ProofsLean.MNCore.Forwarding.Slots)
        (intBars : List (Bool × BitVec 12)),
        prepareParsedIntegerMatrixReadLineCycles (state.peRegisters welcomePE)
            (stateForwardingSlots state welcomePE)
            (state.matrixRegisters (ParsedIntegerContext.ofLinearIndex welcomePE).group
              (ParsedIntegerContext.ofLinearIndex welcomePE).l2b
              (ParsedIntegerContext.ofLinearIndex welcomePE).l1b)
            ((normalizedExpressions.map NormalizedExpr.toParsed).filter
              parsedExprIsIntegerMatrixReadStageInput)
            { directive := state.maskDirective
              context :=
                { (ParsedIntegerContext.ofLinearIndex welcomePE) with
                  bar0 := (state.peContext welcomePE).bar0
                  bar1 := (state.peContext welcomePE).bar1
                  tWord := (state.peContext welcomePE).tWord }
              elapsedWords := state.hazardClock } false = .ok (intWrites, intSlots, intBars) ∧
        next.peRegisters welcomePE =
          commitParsedMaskedWrites (state.peRegisters welcomePE) (intWrites ++ floatWrites)) ∧
    (∀ p : PEId, ∃ writes, next.peRegisters p =
      commitParsedMaskedWrites (state.peRegisters p) writes) ∧
    next.maskDirective = state.maskDirective ∧
    next.l1bm = state.l1bm ∧ next.blockMemory = state.blockMemory ∧
    next.dar = state.dar ∧ next.matrixRegisters = state.matrixRegisters := by
  have stepSuccess : executeIntegerProducerInstructionLine (.pe normalizedExpressions) state
      = .ok next := by
    simpa only [executeNormalizedLine, NormalizedLine.toInstruction?] using executed
  obtain ⟨nextPEs, walkExecuted, nextEq⟩ :=
    executeIntegerProducerInstructionLine_pe_lineExec_exists normalizedExpressions state next
      accepted rows stepSuccess
  obtain ⟨mslId, reluId, blockId, matrixId, sharedId, l1ToPEId, supportedAny,
    noUnsupportedAny, waitsAny, noForwardAny, noTurnaroundAny, outerFilter⟩ :=
    lineExecRow_stage_identities normalizedExpressions state rows
  have walkOnFull : executeIntegerProducerLineAtPEs
      (normalizedExpressions.map NormalizedExpr.toParsed) (List.finRange 4096) state
      = .ok nextPEs := by
    rw [← outerFilter]
    exact walkExecuted
  have walkFrame := executeIntegerProducerLineAtPEs_maskDirective_hazardClock
    (normalizedExpressions.map NormalizedExpr.toParsed) (List.finRange 4096) state nextPEs
    walkOnFull
  have memoryFrame := executeIntegerProducerLineAtPEs_frame
    (normalizedExpressions.map NormalizedExpr.toParsed) (List.finRange 4096) state nextPEs
    walkOnFull
  obtain ⟨intWrites, floatWrites, intSlots, intBars, preparedEq, committed⟩ :=
    executeIntegerProducerLineAtPEs_peRegisters_eq
      (normalizedExpressions.map NormalizedExpr.toParsed) state nextPEs walkOnFull
  subst nextEq
  refine ⟨⟨intWrites, floatWrites, intSlots, intBars, preparedEq, committed⟩, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · intro p
    exact executeIntegerProducerLineAtPEs_peRegisters_commit_all _ (List.finRange 4096) state
      nextPEs walkOnFull (List.nodup_finRange 4096) p (List.mem_finRange p)
  · exact walkFrame.1
  · exact memoryFrame.1
  · exact memoryFrame.2.1
  · exact memoryFrame.2.2.1
  · exact memoryFrame.2.2.2

/-! ## 4. The forwarding slots installed by a `.pe` line step -/

/-- The slots a `.pe` line prepares at one PE (the `preparedSlots` of
`executeIntegerProducerLineAtPECore`): the integer stage's slots, except that
the MAU unit carries the float-MAU stage's outputs when that stage ran. -/
def linePreparedSlots (intSlots : ProofsLean.MNCore.Forwarding.Slots)
    (floatOutputs : Fin 4 → IntegerALU.Bus) (hasMAUProducer : Bool) :
    ProofsLean.MNCore.Forwarding.Slots :=
  fun unit cycle =>
    if (decide (unit = ProofsLean.MNCore.Forwarding.Unit.mau) && hasMAUProducer) = true then
      .known (floatOutputs cycle)
    else intSlots unit cycle

/-- The slot function `updateSupportedPELineForwarding` installs for a line with
no `noforward` row (the `.issue false` branch of `Forwarding.advanceReference`). -/
def lineIssuedSlots (old prepared : ProofsLean.MNCore.Forwarding.Slots)
    (hasALUProducer hasMAUProducer hasMatrixReadProducer : Bool) :
    ProofsLean.MNCore.Forwarding.Slots :=
  fun unit cycle =>
    match unit with
    | .alu => if hasALUProducer then prepared .alu cycle else .poison
    | .mau => if hasMAUProducer then prepared .mau cycle else .poison
    | .matrixRead =>
        if hasMatrixReadProducer then prepared .matrixRead cycle else .known ⟨0, 0⟩
    | .l1ToPE => old .l1ToPE cycle

/-- **The forwarding update in closed form.** -/
theorem updateSupportedPELineForwarding_eq (old prepared : ProofsLean.MNCore.Forwarding.Slots)
    (noForward hasALUProducer hasMAUProducer hasMatrixReadProducer : Bool) :
    updateSupportedPELineForwarding old prepared noForward hasALUProducer hasMAUProducer
        hasMatrixReadProducer =
      .ok (if noForward then old
        else lineIssuedSlots old prepared hasALUProducer hasMAUProducer hasMatrixReadProducer) := by
  cases noForward
  · unfold updateSupportedPELineForwarding Forwarding.advanceReference lineIssuedSlots
    simp only [Bool.false_eq_true, if_false]
    apply congrArg StepResult.ok
    funext unit cycle
    cases unit with
    | alu => cases hasALUProducer <;> rfl
    | mau => cases hasMAUProducer <;> rfl
    | matrixRead => cases hasMatrixReadProducer <;> rfl
    | l1ToPE => rfl
  · unfold updateSupportedPELineForwarding Forwarding.advanceReference
    simp

/-- Folding a validity bit into its own payload is the identity. -/
theorem forwardingValueValid_self (value : ProofsLean.MNCore.Forwarding.Value IntegerALU.Bus) :
    (if forwardingValueValid value = true then value else .poison) = value := by
  cases value <;> rfl

/-- **Folding `forwardingValid` into the installed slots recovers them.**  For a
line without `noforward`, the whole-machine slot view of the installed slots is
the installed slot function itself, except on the L1-to-PE unit, which keeps the
old (state-level) view. -/
theorem stateForwardingSlots_installed (state : State) (pe : PEId)
    (prepared : ProofsLean.MNCore.Forwarding.Slots)
    (hasALUProducer hasMAUProducer hasMatrixReadProducer : Bool) :
    (fun unit cycle =>
      if updateIntegerLineForwardingValid (state.forwardingValid pe)
          (lineIssuedSlots (stateForwardingSlots state pe) prepared hasALUProducer
            hasMAUProducer hasMatrixReadProducer) false unit cycle
        then lineIssuedSlots (stateForwardingSlots state pe) prepared hasALUProducer
          hasMAUProducer hasMatrixReadProducer unit cycle
        else .poison) =
      fun unit cycle =>
        if unit = ProofsLean.MNCore.Forwarding.Unit.l1ToPE
        then stateForwardingSlots state pe unit cycle
        else lineIssuedSlots (stateForwardingSlots state pe) prepared hasALUProducer
          hasMAUProducer hasMatrixReadProducer unit cycle := by
  funext unit cycle
  cases unit with
  | alu =>
      simp [updateIntegerLineForwardingValid, lineIssuedSlots, forwardingValueValid_self]
  | mau =>
      simp [updateIntegerLineForwardingValid, lineIssuedSlots, forwardingValueValid_self]
  | matrixRead =>
      simp [updateIntegerLineForwardingValid, lineIssuedSlots, forwardingValueValid_self]
  | l1ToPE =>
      simp only [updateIntegerLineForwardingValid, lineIssuedSlots, stateForwardingSlots]
      split <;> simp_all

/-- The per-PE core step leaves every other PE's forwarding state untouched. -/
theorem executeIntegerProducerLineAtPECore_forwarding_other
    (expressions : List ParsedExpr) (state next : State) (pe other : PEId)
    (different : other ≠ pe)
    (executed : executeIntegerProducerLineAtPECore expressions state pe = .ok next) :
    next.forwarding other = state.forwarding other ∧
    next.forwardingValid other = state.forwardingValid other := by
  rw [executeIntegerProducerLineAtPECore.eq_1] at executed
  split at executed
  · simp at executed
  · simp at executed
  · split at executed
    · simp at executed
    · simp at executed
    · simp only [updateSupportedPELineForwarding] at executed
      split at executed
      · simp at executed
      · simp at executed
      · simp only [StepResult.ok.injEq] at executed
        subst executed
        simp [different]

/-- The per-PE step leaves every other PE's forwarding state untouched. -/
theorem executeIntegerProducerLineAtPE_forwarding_other
    (expressions : List ParsedExpr) (state next : State) (pe other : PEId)
    (different : other ≠ pe)
    (executed : executeIntegerProducerLineAtPE expressions state pe = .ok next) :
    next.forwarding other = state.forwarding other ∧
    next.forwardingValid other = state.forwardingValid other := by
  unfold executeIntegerProducerLineAtPE at executed
  split at executed
  · simp at executed
  · exact executeIntegerProducerLineAtPECore_forwarding_other expressions state next pe other
      different executed

/-- The walk leaves an unvisited PE's forwarding state untouched. -/
theorem executeIntegerProducerLineAtPEs_forwarding_of_not_mem
    (expressions : List ParsedExpr) (pes : List PEId) (state next : State) (pe : PEId)
    (absent : pe ∉ pes)
    (executed : executeIntegerProducerLineAtPEs expressions pes state = .ok next) :
    next.forwarding pe = state.forwarding pe ∧
    next.forwardingValid pe = state.forwardingValid pe := by
  induction pes generalizing state with
  | nil =>
      simp only [executeIntegerProducerLineAtPEs, StepResult.ok.injEq] at executed
      subst executed
      exact ⟨rfl, rfl⟩
  | cons head rest ih =>
      simp only [List.mem_cons, not_or] at absent
      obtain ⟨headNe, absent⟩ := absent
      simp only [executeIntegerProducerLineAtPEs] at executed
      split at executed
      · simp at executed
      · simp at executed
      · rename_i middle stepMiddle
        have head := executeIntegerProducerLineAtPE_forwarding_other expressions state
          middle head pe headNe stepMiddle
        have tail := ih middle absent executed
        exact ⟨tail.1.trans head.1, tail.2.trans head.2⟩

/-- **The slots installed by a successful per-PE core step.**  The installed
slot function is fixed by the (closed) forwarding update of the line's own
prepared slots `linePreparedSlots intSlots floatOutputs hasMAUProducer`, where
`intSlots` is the integer four-cycle stage's own output slot function (named by
the preparation equation) and `floatOutputs` the MAU stage's own outputs.  The
state-level slot view after the step is that installed function with its
validity bit folded in. -/
theorem executeIntegerProducerLineAtPECore_stateForwardingSlots_eq
    (expressions : List ParsedExpr) (state next : State) (pe : PEId)
    (executed : executeIntegerProducerLineAtPECore expressions state pe = .ok next) :
    ∃ (intWrites : List PreparedParsedMaskedWrite)
      (intSlots : ProofsLean.MNCore.Forwarding.Slots)
      (intBars : List (Bool × BitVec 12))
      (floatFiles : IntegerRegisterFiles)
      (floatBar0 floatBar1 : BitVec 12)
      (floatOutputs : Fin 4 → IntegerALU.Bus)
      (hasMAUProducer : Bool)
      (installed : ProofsLean.MNCore.Forwarding.Slots),
      prepareParsedIntegerMatrixReadLineCycles (state.peRegisters pe)
          (stateForwardingSlots state pe)
          (state.matrixRegisters (ParsedIntegerContext.ofLinearIndex pe).group
            (ParsedIntegerContext.ofLinearIndex pe).l2b
            (ParsedIntegerContext.ofLinearIndex pe).l1b)
          (expressions.filter parsedExprIsIntegerMatrixReadStageInput)
          { directive := state.maskDirective
            context :=
              { (ParsedIntegerContext.ofLinearIndex pe) with
                bar0 := (state.peContext pe).bar0
                bar1 := (state.peContext pe).bar1
                tWord := (state.peContext pe).tWord }
            elapsedWords := state.hazardClock } false = .ok (intWrites, intSlots, intBars) ∧
      executeParsedFloatMAUsAtPE (state.peRegisters pe)
          (commitParsedMaskedWrites (state.peRegisters pe) intWrites)
          (stateForwardingSlots state pe)
          { (ParsedIntegerContext.ofLinearIndex pe) with
            bar0 := (state.peContext pe).bar0
            bar1 := (state.peContext pe).bar1
            tWord := (state.peContext pe).tWord }
          expressions state.maskDirective
          (expressions.any parsedExprHasSingleLineWriteMask) =
        .ok (floatFiles, floatBar0, floatBar1, floatOutputs, hasMAUProducer) ∧
      updateSupportedPELineForwarding (stateForwardingSlots state pe)
          (linePreparedSlots intSlots floatOutputs hasMAUProducer)
          (expressions.any fun expression =>
            match expression.op with
            | .noforward => true
            | _ => false)
          (expressions.any parsedExprIsIntegerProducer) hasMAUProducer
          (expressions.any parsedExprIsMatrixReadProducer) = .ok installed ∧
      stateForwardingSlots next pe = fun unit cycle =>
        if updateIntegerLineForwardingValid (state.forwardingValid pe) installed
            (expressions.any fun expression =>
              match expression.op with
              | .noforward => true
              | _ => false) unit cycle
        then installed unit cycle
        else .poison := by
  unfold executeIntegerProducerLineAtPECore parsedIntegerMatrixReadLineFourCycleStep at executed
  dsimp only at executed
  cases preparedEq : prepareParsedIntegerMatrixReadLineCycles (state.peRegisters pe)
      (stateForwardingSlots state pe)
      (state.matrixRegisters (ParsedIntegerContext.ofLinearIndex pe).group
        (ParsedIntegerContext.ofLinearIndex pe).l2b
        (ParsedIntegerContext.ofLinearIndex pe).l1b)
      (expressions.filter parsedExprIsIntegerMatrixReadStageInput)
      { directive := state.maskDirective
        context :=
          { (ParsedIntegerContext.ofLinearIndex pe) with
            bar0 := (state.peContext pe).bar0
            bar1 := (state.peContext pe).bar1
            tWord := (state.peContext pe).tWord }
        elapsedWords := state.hazardClock } false with
  | failure =>
      simp only [preparedEq] at executed
      simp at executed
  | unknown =>
      simp only [preparedEq] at executed
      simp at executed
  | ok prepared =>
      obtain ⟨intWrites, intSlots, intBars⟩ := prepared
      simp only [preparedEq] at executed
      cases floatEq : executeParsedFloatMAUsAtPE (state.peRegisters pe)
          (commitParsedMaskedWrites (state.peRegisters pe) intWrites)
          (stateForwardingSlots state pe)
          { (ParsedIntegerContext.ofLinearIndex pe) with
            bar0 := (state.peContext pe).bar0
            bar1 := (state.peContext pe).bar1
            tWord := (state.peContext pe).tWord }
          expressions state.maskDirective
          (expressions.any parsedExprHasSingleLineWriteMask) with
      | failure =>
          simp only [floatEq] at executed
          simp at executed
      | unknown =>
          simp only [floatEq] at executed
          simp at executed
      | ok floatResult =>
          obtain ⟨floatFiles, floatBar0, floatBar1, floatOutputs, hasMAUProducer⟩ := floatResult
          have floatEq' : executeParsedFloatMAUsAtPE (state.peRegisters pe)
              (commitParsedMaskedWrites (state.peRegisters pe) intWrites)
              (stateForwardingSlots state pe)
              { (ParsedIntegerContext.ofLinearIndex pe) with
                bar0 := (state.peContext pe).bar0
                bar1 := (state.peContext pe).bar1
                tWord := (state.peContext pe).tWord }
              expressions state.maskDirective
              (expressions.any parsedExprHasSingleLineWriteMask) =
              .ok (floatFiles, floatBar0, floatBar1, floatOutputs, hasMAUProducer) := floatEq
          simp only [floatEq] at executed
          split at executed
          · simp at executed
          · simp at executed
          · rename_i forwarding forwardEq
            have forwardEq' : updateSupportedPELineForwarding (stateForwardingSlots state pe)
                (linePreparedSlots intSlots floatOutputs hasMAUProducer)
                (expressions.any fun expression =>
                  match expression.op with
                  | .noforward => true
                  | _ => false)
                (expressions.any parsedExprIsIntegerProducer) hasMAUProducer
                (expressions.any parsedExprIsMatrixReadProducer) = .ok forwarding := forwardEq
            refine ⟨intWrites, intSlots, intBars, floatFiles, floatBar0, floatBar1,
              floatOutputs, hasMAUProducer, forwarding, rfl, floatEq', forwardEq', ?_⟩
            simp only [StepResult.ok.injEq] at executed
            subst executed
            funext unit cycle
            simp only [stateForwardingSlots]
            rfl

/-- A forwarding payload whose validity bit is false is poison. -/
theorem eq_poison_of_forwardingValueValid_false
    (value : ProofsLean.MNCore.Forwarding.Value IntegerALU.Bus)
    (invalid : forwardingValueValid value = false) : value = .poison := by
  cases value <;> simp_all [forwardingValueValid]

/-- A forwarding payload whose validity bit is false is poison (symmetric form). -/
theorem poison_eq_of_forwardingValueValid_false
    (value : ProofsLean.MNCore.Forwarding.Value IntegerALU.Bus)
    (invalid : forwardingValueValid value = false) : .poison = value :=
  (eq_poison_of_forwardingValueValid_false value invalid).symm

/-- The float-MAU stage's `hasMAUProducer` flag is the non-emptiness of its
filtered float-MAU row list. -/
theorem executeParsedFloatMAUsAtPE_hasMAUProducer
    (readFiles currentFiles : IntegerRegisterFiles) (oldSlots : Forwarding.Slots)
    (context : ParsedIntegerContext) (expressions : List ParsedExpr)
    (directive : ParsedMaskDirective) (hasSingleLineMask : Bool)
    (nextFiles : IntegerRegisterFiles) (nextBar0 nextBar1 : BitVec 12)
    (nextOutputs : Fin 4 → IntegerALU.Bus) (hasMAUProducer : Bool)
    (executed : executeParsedFloatMAUsAtPE readFiles currentFiles oldSlots context expressions
      directive hasSingleLineMask =
      .ok (nextFiles, nextBar0, nextBar1, nextOutputs, hasMAUProducer)) :
    hasMAUProducer = !(expressions.filter parsedExprIsSupportedFloatMAUProducer).isEmpty := by
  rw [executeParsedFloatMAUsAtPE.eq_1] at executed
  split at executed
  · simp at executed
  · simp at executed
  · rename_i files bar0 bar1 outputs ran
    simp only [StepResult.ok.injEq] at executed
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := executed
    rfl

/-- **The ALU forwarding slot after a per-PE core step.**  When the line has an
integer ALU producer and no `noforward` row, the `.alu` unit's state-level slot
is exactly the integer stage's own prepared slot (this is what `$aluf` reads on
the next line). -/
theorem executeIntegerProducerLineAtPECore_alu_slot
    (expressions : List ParsedExpr) (state next : State) (pe : PEId)
    (hasALUProducer : expressions.any parsedExprIsIntegerProducer = true)
    (noForward : (expressions.any fun expression =>
      match expression.op with
      | .noforward => true
      | _ => false) = false)
    (executed : executeIntegerProducerLineAtPECore expressions state pe = .ok next) :
    ∃ (intWrites : List PreparedParsedMaskedWrite)
      (intSlots : ProofsLean.MNCore.Forwarding.Slots)
      (intBars : List (Bool × BitVec 12)),
      prepareParsedIntegerMatrixReadLineCycles (state.peRegisters pe)
          (stateForwardingSlots state pe)
          (state.matrixRegisters (ParsedIntegerContext.ofLinearIndex pe).group
            (ParsedIntegerContext.ofLinearIndex pe).l2b
            (ParsedIntegerContext.ofLinearIndex pe).l1b)
          (expressions.filter parsedExprIsIntegerMatrixReadStageInput)
          { directive := state.maskDirective
            context :=
              { (ParsedIntegerContext.ofLinearIndex pe) with
                bar0 := (state.peContext pe).bar0
                bar1 := (state.peContext pe).bar1
                tWord := (state.peContext pe).tWord }
            elapsedWords := state.hazardClock } false = .ok (intWrites, intSlots, intBars) ∧
      (∀ cycle : Fin 4,
        stateForwardingSlots next pe .alu cycle = intSlots .alu cycle) := by
  obtain ⟨intWrites, intSlots, intBars, floatFiles, floatBar0, floatBar1, floatOutputs,
    hasMAUProducer, installed, preparedEq, floatEq, forwardEq, slotsEq⟩ :=
    executeIntegerProducerLineAtPECore_stateForwardingSlots_eq expressions state next pe executed
  refine ⟨intWrites, intSlots, intBars, preparedEq, ?_⟩
  have installedEq : installed =
      lineIssuedSlots (stateForwardingSlots state pe)
        (linePreparedSlots intSlots floatOutputs hasMAUProducer)
        (expressions.any parsedExprIsIntegerProducer) hasMAUProducer
        (expressions.any parsedExprIsMatrixReadProducer) := by
    have key := updateSupportedPELineForwarding_eq (stateForwardingSlots state pe)
      (linePreparedSlots intSlots floatOutputs hasMAUProducer)
      (expressions.any fun expression =>
        match expression.op with
        | .noforward => true
        | _ => false)
      (expressions.any parsedExprIsIntegerProducer) hasMAUProducer
      (expressions.any parsedExprIsMatrixReadProducer)
    rw [key] at forwardEq
    have notTrue : ¬ ((expressions.any fun expression =>
        match expression.op with
        | .noforward => true
        | _ => false) = true) := by
      rw [noForward]
      simp
    rw [if_neg notTrue] at forwardEq
    exact (StepResult.ok.inj forwardEq).symm
  have foldAll := stateForwardingSlots_installed state pe
    (linePreparedSlots intSlots floatOutputs hasMAUProducer)
    (expressions.any parsedExprIsIntegerProducer) hasMAUProducer
    (expressions.any parsedExprIsMatrixReadProducer)
  intro cycle
  subst installedEq
  rw [slotsEq, noForward]
  simp [stateForwardingSlots, lineIssuedSlots, linePreparedSlots, hasALUProducer,
    updateIntegerLineForwardingValid,
    eq_poison_of_forwardingValueValid_false, poison_eq_of_forwardingValueValid_false]
  intro h
  exact poison_eq_of_forwardingValueValid_false _ h


/-- **The MAU forwarding slot after a per-PE core step.**  When the line has a
supported float-MAU producer and no `noforward` row, the `.mau` unit's
state-level slot at every cycle is the MAU stage's own output (this is what
`$mauf` reads on the next line). -/
theorem executeIntegerProducerLineAtPECore_mau_slot
    (expressions : List ParsedExpr) (state next : State) (pe : PEId)
    (hasMAUProducer : (expressions.filter parsedExprIsSupportedFloatMAUProducer).isEmpty = false)
    (noForward : (expressions.any fun expression =>
      match expression.op with
      | .noforward => true
      | _ => false) = false)
    (executed : executeIntegerProducerLineAtPECore expressions state pe = .ok next) :
    ∃ (intWrites : List PreparedParsedMaskedWrite)
      (intSlots : ProofsLean.MNCore.Forwarding.Slots)
      (intBars : List (Bool × BitVec 12))
      (floatOutputs : Fin 4 → IntegerALU.Bus),
      prepareParsedIntegerMatrixReadLineCycles (state.peRegisters pe)
          (stateForwardingSlots state pe)
          (state.matrixRegisters (ParsedIntegerContext.ofLinearIndex pe).group
            (ParsedIntegerContext.ofLinearIndex pe).l2b
            (ParsedIntegerContext.ofLinearIndex pe).l1b)
          (expressions.filter parsedExprIsIntegerMatrixReadStageInput)
          { directive := state.maskDirective
            context :=
              { (ParsedIntegerContext.ofLinearIndex pe) with
                bar0 := (state.peContext pe).bar0
                bar1 := (state.peContext pe).bar1
                tWord := (state.peContext pe).tWord }
            elapsedWords := state.hazardClock } false = .ok (intWrites, intSlots, intBars) ∧
      (∀ cycle : Fin 4,
        stateForwardingSlots next pe .mau cycle = .known (floatOutputs cycle)) := by
  obtain ⟨intWrites, intSlots, intBars, floatFiles, floatBar0, floatBar1, floatOutputs,
    mauRan, installed, preparedEq, floatEq, forwardEq, slotsEq⟩ :=
    executeIntegerProducerLineAtPECore_stateForwardingSlots_eq expressions state next pe executed
  refine ⟨intWrites, intSlots, intBars, floatOutputs, preparedEq, ?_⟩
  have installedEq : installed =
      lineIssuedSlots (stateForwardingSlots state pe)
        (linePreparedSlots intSlots floatOutputs mauRan)
        (expressions.any parsedExprIsIntegerProducer) mauRan
        (expressions.any parsedExprIsMatrixReadProducer) := by
    have key := updateSupportedPELineForwarding_eq (stateForwardingSlots state pe)
      (linePreparedSlots intSlots floatOutputs mauRan)
      (expressions.any fun expression =>
        match expression.op with
        | .noforward => true
        | _ => false)
      (expressions.any parsedExprIsIntegerProducer) mauRan
      (expressions.any parsedExprIsMatrixReadProducer)
    rw [key] at forwardEq
    have notTrue : ¬ ((expressions.any fun expression =>
        match expression.op with
        | .noforward => true
        | _ => false) = true) := by
      rw [noForward]
      simp
    rw [if_neg notTrue] at forwardEq
    exact (StepResult.ok.inj forwardEq).symm
  have foldAll := stateForwardingSlots_installed state pe
    (linePreparedSlots intSlots floatOutputs mauRan)
    (expressions.any parsedExprIsIntegerProducer) mauRan
    (expressions.any parsedExprIsMatrixReadProducer)
  have mauRanEq : mauRan =
      !(expressions.filter parsedExprIsSupportedFloatMAUProducer).isEmpty :=
    executeParsedFloatMAUsAtPE_hasMAUProducer (state.peRegisters pe)
      (commitParsedMaskedWrites (state.peRegisters pe) intWrites)
      (stateForwardingSlots state pe)
      { (ParsedIntegerContext.ofLinearIndex pe) with
        bar0 := (state.peContext pe).bar0
        bar1 := (state.peContext pe).bar1
        tWord := (state.peContext pe).tWord }
      expressions state.maskDirective (expressions.any parsedExprHasSingleLineWriteMask)
      floatFiles floatBar0 floatBar1 floatOutputs mauRan floatEq
  intro cycle
  subst installedEq
  rw [slotsEq, noForward]
  have mauTrue : mauRan = true := by
    rw [mauRanEq, hasMAUProducer]
    rfl
  rw [mauTrue]
  simp [stateForwardingSlots, lineIssuedSlots, linePreparedSlots,
    updateIntegerLineForwardingValid,
    eq_poison_of_forwardingValueValid_false]
  rfl



/-- **The forwarding slots installed by a successful `.pe` line step at PE 0.**
The line has only line-exec rows, so the six non-integer stages are the
identity and the walk leaves PE 0's forwarding alone after its first visit; the
installed slot function is therefore exactly the per-PE installation computed at
the *initial* state, and the post-step state-level slot view is that function
with its validity bit folded in.

This is the statement any next line's `$aluf` / `$mauf` read consumes. -/
theorem executeNormalizedLine_pe_forwardingSlots
    (normalizedExpressions : List NormalizedExpr) (state next : State)
    (accepted : checkParsedTopLine
      (InstructionLine.pe normalizedExpressions).toParsed = true)
    (rows : (normalizedExpressions.map NormalizedExpr.toParsed).all
      parsedExprIsLineExecRow = true)
    (executed : executeNormalizedLine (.pe normalizedExpressions) state = .ok next) :
    ∃ (intWrites : List PreparedParsedMaskedWrite)
      (intSlots : ProofsLean.MNCore.Forwarding.Slots)
      (intBars : List (Bool × BitVec 12))
      (floatFiles : IntegerRegisterFiles)
      (floatBar0 floatBar1 : BitVec 12)
      (floatOutputs : Fin 4 → IntegerALU.Bus)
      (hasMAUProducer : Bool)
      (installed : ProofsLean.MNCore.Forwarding.Slots),
      prepareParsedIntegerMatrixReadLineCycles (state.peRegisters welcomePE)
          (stateForwardingSlots state welcomePE)
          (state.matrixRegisters (ParsedIntegerContext.ofLinearIndex welcomePE).group
            (ParsedIntegerContext.ofLinearIndex welcomePE).l2b
            (ParsedIntegerContext.ofLinearIndex welcomePE).l1b)
          ((normalizedExpressions.map NormalizedExpr.toParsed).filter
            parsedExprIsIntegerMatrixReadStageInput)
          { directive := state.maskDirective
            context :=
              { (ParsedIntegerContext.ofLinearIndex welcomePE) with
                bar0 := (state.peContext welcomePE).bar0
                bar1 := (state.peContext welcomePE).bar1
                tWord := (state.peContext welcomePE).tWord }
            elapsedWords := state.hazardClock } false = .ok (intWrites, intSlots, intBars) ∧
      executeParsedFloatMAUsAtPE (state.peRegisters welcomePE)
          (commitParsedMaskedWrites (state.peRegisters welcomePE) intWrites)
          (stateForwardingSlots state welcomePE)
          { (ParsedIntegerContext.ofLinearIndex welcomePE) with
            bar0 := (state.peContext welcomePE).bar0
            bar1 := (state.peContext welcomePE).bar1
            tWord := (state.peContext welcomePE).tWord }
          (normalizedExpressions.map NormalizedExpr.toParsed) state.maskDirective
          ((normalizedExpressions.map NormalizedExpr.toParsed).any
            parsedExprHasSingleLineWriteMask) =
        .ok (floatFiles, floatBar0, floatBar1, floatOutputs, hasMAUProducer) ∧
      updateSupportedPELineForwarding (stateForwardingSlots state welcomePE)
          (linePreparedSlots intSlots floatOutputs hasMAUProducer)
          ((normalizedExpressions.map NormalizedExpr.toParsed).any fun expression =>
            match expression.op with
            | .noforward => true
            | _ => false)
          ((normalizedExpressions.map NormalizedExpr.toParsed).any
            parsedExprIsIntegerProducer) hasMAUProducer
          ((normalizedExpressions.map NormalizedExpr.toParsed).any
            parsedExprIsMatrixReadProducer) = .ok installed ∧
      stateForwardingSlots next welcomePE = fun unit cycle =>
        if updateIntegerLineForwardingValid (state.forwardingValid welcomePE) installed
            ((normalizedExpressions.map NormalizedExpr.toParsed).any fun expression =>
              match expression.op with
              | .noforward => true
              | _ => false) unit cycle
        then installed unit cycle
        else .poison := by
  have stepSuccess : executeIntegerProducerInstructionLine (.pe normalizedExpressions) state
      = .ok next := by
    simpa only [executeNormalizedLine, NormalizedLine.toInstruction?] using executed
  obtain ⟨nextPEs, walkExecuted, nextEq⟩ :=
    executeIntegerProducerInstructionLine_pe_lineExec_exists normalizedExpressions state next
      accepted rows stepSuccess
  obtain ⟨mslId, reluId, blockId, matrixId, sharedId, l1ToPEId, supportedAny,
    noUnsupportedAny, waitsAny, noForwardAny, noTurnaroundAny, outerFilter⟩ :=
    lineExecRow_stage_identities normalizedExpressions state rows
  have walkOnFull : executeIntegerProducerLineAtPEs
      (normalizedExpressions.map NormalizedExpr.toParsed) (List.finRange 4096) state
      = .ok nextPEs := by
    rw [← outerFilter]
    exact walkExecuted
  -- peel the first visited PE (PE 0) out of the walk
  rw [finRange4096_eq_welcomePE_cons] at walkOnFull
  have notMem : welcomePE ∉ (List.finRange 4095).map Fin.succ :=
    welcomePE_not_mem_finRange4095_map_succ
  simp only [executeIntegerProducerLineAtPEs] at walkOnFull
  split at walkOnFull
  · simp at walkOnFull
  · simp at walkOnFull
  · rename_i middle headExecuted
    -- the tail leaves PE 0's forwarding alone
    have tailFrame := executeIntegerProducerLineAtPEs_forwarding_of_not_mem
      (normalizedExpressions.map NormalizedExpr.toParsed) ((List.finRange 4095).map Fin.succ)
      middle nextPEs welcomePE notMem walkOnFull
    -- the first step's core
    have coreExecuted : executeIntegerProducerLineAtPECore
        (normalizedExpressions.map NormalizedExpr.toParsed) state welcomePE = .ok middle := by
      unfold executeIntegerProducerLineAtPE at headExecuted
      split at headExecuted
      · simp at headExecuted
      · exact headExecuted
    obtain ⟨intWrites, intSlots, intBars, floatFiles, floatBar0, floatBar1, floatOutputs,
      hasMAUProducer, installed, preparedEq, floatEq, forwardEq, slotsEq⟩ :=
      executeIntegerProducerLineAtPECore_stateForwardingSlots_eq
        (normalizedExpressions.map NormalizedExpr.toParsed) state middle welcomePE coreExecuted
    refine ⟨intWrites, intSlots, intBars, floatFiles, floatBar0, floatBar1, floatOutputs,
      hasMAUProducer, installed, preparedEq, floatEq, forwardEq, ?_⟩
    rw [nextEq]
    have hnext : stateForwardingSlots { nextPEs with
        hazardClock := nextPEs.hazardClock + InstructionLine.cost (.pe normalizedExpressions)
        l1bmTurnaroundValid := false } welcomePE = stateForwardingSlots nextPEs welcomePE := rfl
    rw [hnext]
    have hmiddle : stateForwardingSlots nextPEs welcomePE =
        stateForwardingSlots middle welcomePE := by
      funext unit cycle
      simp only [stateForwardingSlots, tailFrame.1, tailFrame.2]
    rw [hmiddle]
    exact slotsEq

/-- **Reading `$aluf` from a slot function with a `known` ALU slot.** -/
theorem readWithForwarding_aluf_known (files : IntegerRegisterFiles)
    (slots : ProofsLean.MNCore.Forwarding.Slots) (cycle : Fin 4)
    (value : IntegerALU.Bus)
    (known : slots .alu cycle = .known value) :
    ParsedIntegerInput.readWithForwarding files slots cycle (.forward .aluf false) = .ok value := by
  simp [ParsedIntegerInput.readWithForwarding, ParsedIntegerInput.forwardUnit, known,
    ParsedIntegerInput.applyRounding]

/-- A non-float line-exec row is an integer four-cycle stage input. -/
theorem parsedExprIsIntegerMatrixReadStageInput_of_lineExecRow (expression : ParsedExpr)
    (row : parsedExprIsLineExecRow expression = true)
    (notFloat : parsedExprIsSupportedFloatMAUProducer expression = false) :
    parsedExprIsIntegerMatrixReadStageInput expression = true := by
  obtain ⟨supported, notUnsupported, notWait, notMatrixMAU, notMatrixWrite, notMsl,
    notRelu, notBlock, notL1ToPE, notL2BM, notNoforward, notTurnaround⟩ :=
    parsedExprIsLineExecRow_facts expression row
  cases expression with
  | mk op sources destinations flush text =>
      cases op <;>
        simp_all [parsedExprIsLineExecRow, parsedExprIsIntegerMatrixReadStageInput,
          parsedExprIsSupportedPELineProducer, parsedExprIsSupportedFloatMAUProducer,
          parsedExprWaitTag?, parsedExprIsMatrixMAUProducer,
          parsedExprIsMatrixWriteProducer, parsedExprIsL1MwriteProducer,
          parsedExprIsL1GatherProducer, parsedExprIsL1ReduceProducer,
          parsedExprIsL1ToPEProducer, parsedExprIsMslMsrProducer,
          parsedExprIsFloatReluProducer, parsedExprIsBlockFloatProducer,
          parsedExprIsL2BMProducer]

/-- **The second line's `$aluf` read after a `.pe` line 1.**  After a successful
`.pe` step of a single-row line-exec line with an integer-ALU producer and no
`noforward` row, every `.alu` forwarding slot at PE 0 is the integer stage's own
prepared slot, so reading `$aluf` at cycle `c` returns that slot's payload. -/
theorem executeNormalizedLine_pe_aluf_read
    (normalizedExpressions : List NormalizedExpr) (state next : State)
    (accepted : checkParsedTopLine
      (InstructionLine.pe normalizedExpressions).toParsed = true)
    (rows : (normalizedExpressions.map NormalizedExpr.toParsed).all
      parsedExprIsLineExecRow = true)
    (hasALU : (normalizedExpressions.map NormalizedExpr.toParsed).any
      parsedExprIsIntegerProducer = true)
    (noForward : (normalizedExpressions.map NormalizedExpr.toParsed).any (fun expression =>
      match expression.op with
      | .noforward => true
      | _ => false) = false)
    (executed : executeNormalizedLine (.pe normalizedExpressions) state = .ok next) :
    ∃ (intWrites : List PreparedParsedMaskedWrite)
      (intSlots : ProofsLean.MNCore.Forwarding.Slots)
      (intBars : List (Bool × BitVec 12)),
      prepareParsedIntegerMatrixReadLineCycles (state.peRegisters welcomePE)
          (stateForwardingSlots state welcomePE)
          (state.matrixRegisters (ParsedIntegerContext.ofLinearIndex welcomePE).group
            (ParsedIntegerContext.ofLinearIndex welcomePE).l2b
            (ParsedIntegerContext.ofLinearIndex welcomePE).l1b)
          ((normalizedExpressions.map NormalizedExpr.toParsed).filter
            parsedExprIsIntegerMatrixReadStageInput)
          { directive := state.maskDirective
            context :=
              { (ParsedIntegerContext.ofLinearIndex welcomePE) with
                bar0 := (state.peContext welcomePE).bar0
                bar1 := (state.peContext welcomePE).bar1
                tWord := (state.peContext welcomePE).tWord }
            elapsedWords := state.hazardClock } false = .ok (intWrites, intSlots, intBars) ∧
      (∀ cycle : Fin 4,
        stateForwardingSlots next welcomePE .alu cycle = intSlots .alu cycle) ∧
      (∀ (cycle : Fin 4) (value : IntegerALU.Bus), intSlots .alu cycle = .known value →
        ParsedIntegerInput.readWithForwarding (next.peRegisters welcomePE)
          (stateForwardingSlots next welcomePE) cycle (.forward .aluf false) = .ok value) := by
  have stepSuccess : executeIntegerProducerInstructionLine (.pe normalizedExpressions) state
      = .ok next := by
    simpa only [executeNormalizedLine, NormalizedLine.toInstruction?] using executed
  obtain ⟨nextPEs, walkExecuted, nextEq⟩ :=
    executeIntegerProducerInstructionLine_pe_lineExec_exists normalizedExpressions state next
      accepted rows stepSuccess
  obtain ⟨mslId, reluId, blockId, matrixId, sharedId, l1ToPEId, supportedAny,
    noUnsupportedAny, waitsAny, noForwardAny, noTurnaroundAny, outerFilter⟩ :=
    lineExecRow_stage_identities normalizedExpressions state rows
  have walkOnFull : executeIntegerProducerLineAtPEs
      (normalizedExpressions.map NormalizedExpr.toParsed) (List.finRange 4096) state
      = .ok nextPEs := by
    rw [← outerFilter]
    exact walkExecuted
  rw [finRange4096_eq_welcomePE_cons] at walkOnFull
  have notMem : welcomePE ∉ (List.finRange 4095).map Fin.succ :=
    welcomePE_not_mem_finRange4095_map_succ
  simp only [executeIntegerProducerLineAtPEs] at walkOnFull
  split at walkOnFull
  · simp at walkOnFull
  · simp at walkOnFull
  · rename_i middle headExecuted
    have tailFrame := executeIntegerProducerLineAtPEs_forwarding_of_not_mem
      (normalizedExpressions.map NormalizedExpr.toParsed) ((List.finRange 4095).map Fin.succ)
      middle nextPEs welcomePE notMem walkOnFull
    have coreExecuted : executeIntegerProducerLineAtPECore
        (normalizedExpressions.map NormalizedExpr.toParsed) state welcomePE = .ok middle := by
      unfold executeIntegerProducerLineAtPE at headExecuted
      split at headExecuted
      · simp at headExecuted
      · exact headExecuted
    obtain ⟨intWrites, intSlots, intBars, preparedEq, slotValues⟩ :=
      executeIntegerProducerLineAtPECore_alu_slot
        (normalizedExpressions.map NormalizedExpr.toParsed) state middle welcomePE
        hasALU noForward coreExecuted
    have slotsFrame : stateForwardingSlots next welcomePE =
        stateForwardingSlots middle welcomePE := by
      rw [nextEq]
      have hnext : stateForwardingSlots { nextPEs with
          hazardClock := nextPEs.hazardClock + InstructionLine.cost (.pe normalizedExpressions)
          l1bmTurnaroundValid := false } welcomePE = stateForwardingSlots nextPEs welcomePE := rfl
      rw [hnext]
      funext unit cycle
      simp only [stateForwardingSlots, tailFrame.1, tailFrame.2]
    refine ⟨intWrites, intSlots, intBars, preparedEq, ?_, ?_⟩
    · intro cycle
      rw [slotsFrame]
      exact slotValues cycle
    · intro cycle value known
      rw [slotsFrame]
      have known' : stateForwardingSlots middle welcomePE .alu cycle = .known value := by
        rw [slotValues cycle]
        exact known
      exact readWithForwarding_aluf_known (next.peRegisters welcomePE)
        (stateForwardingSlots middle welcomePE) cycle value known'

/-- The `$aluf` payload a `.immediate` row prepares for one cycle. -/
def immediateALUWrite (payload : BitVec 32) (sparse reduced : Bool)
    (flushSelection : Option PEWordSelection) : PreparedParsedMaskedWrite where
  destination := none
  maskUpdate := none
  data := unpackALUBus (parsedOutputAfterFlush flushSelection
    (evaluateParsedExecutionRequest (.immediate payload sparse) ⟨0, 0⟩ ⟨0, 0⟩ reduced).value)
  selection := ⟨BitVec.allOnes 4, true⟩

/-- The ALU forwarding slots after preparing one `.immediate` row: cycle `c`
carries the row's own prepared `$aluf` payload. -/
def immediateALUSlots (old : ProofsLean.MNCore.Forwarding.Slots) (payload : BitVec 32)
    (sparse reduced : Bool) (flush : Fin 4 → Option PEWordSelection) :
    ProofsLean.MNCore.Forwarding.Slots :=
  fun unit cycle =>
    if unit = ProofsLean.MNCore.Forwarding.Unit.alu then
      .known (pack (immediateALUWrite payload sparse reduced (flush cycle)).data)
    else old unit cycle

/-- With no flush selection the `.immediate` payload is the raw immediate bus. -/
theorem immediateALUWrite_data_none (payload : BitVec 32) (sparse reduced : Bool) :
    (immediateALUWrite payload sparse reduced none).data =
      unpackALUBus
        (evaluateParsedExecutionRequest (.immediate payload sparse) ⟨0, 0⟩ ⟨0, 0⟩ reduced).value := by
  simp [immediateALUWrite, parsedOutputAfterFlush]

/-- The forwarded `$aluf` value of an `imm` row is the immediate's own bus. -/
theorem immediateALUWrite_forwarded_none (payload : BitVec 32) (sparse reduced : Bool) :
    pack (immediateALUWrite payload sparse reduced none).data =
      ⟨payload ++ (if sparse then 0 else payload),
        payload ++ (if sparse then 0 else payload)⟩ := by
  simp [immediateALUWrite, parsedOutputAfterFlush, evaluateParsedExecutionRequest,
    pack_unpackALUBus]

/-- **One `.immediate` cycle updates the ALU slot only.** -/
theorem updateParsedIntegerALUForwardingCycle_immediate (old : ProofsLean.MNCore.Forwarding.Slots)
    (cycle : Fin 4) (payload : BitVec 32) (sparse reduced : Bool)
    (flushSelection : Option PEWordSelection) :
    updateParsedIntegerALUForwardingCycle old cycle
        (.ok (immediateALUWrite payload sparse reduced flushSelection)) false =
      .ok (fun unit slotCycle =>
        if unit = ProofsLean.MNCore.Forwarding.Unit.alu ∧ slotCycle = cycle then
          .known (pack (immediateALUWrite payload sparse reduced flushSelection).data)
        else old unit slotCycle) := by
  simpa using updateParsedIntegerALUForwardingCycle_semantics old cycle
    (immediateALUWrite payload sparse reduced flushSelection) false

/-- **Four-cycle preparation of one `.immediate` row: exactly the per-cycle
`$aluf` payloads.**  `intSlots` is the accumulated slot function
`immediateALUSlots`, so every `.alu` cycle of the row's own line carries its own
prepared bus. -/
theorem immediate_prepareParsedIntegerALUExprCycles
    (files : IntegerRegisterFiles) (oldSlots : ProofsLean.MNCore.Forwarding.Slots)
    (expression : ParsedExpr) (control : ParsedMaskExecutionControl)
    (hasSingleLineMask noForward reduced : Bool)
    (targets : Fin 4 → List ParsedConstantDestination)
    (destinationWrites : Fin 4 → List PreparedParsedMaskedWrite)
    (flush : Fin 4 → Option PEWordSelection)
    (payload : BitVec 32) (sparse : Bool)
    (isImmediate : expression.op = .immediate payload sparse)
    (lowered : ∀ cycle, ParsedExpr.toDirectMaskedConstantWrites? expression files.maskRegisters
      control.directive hasSingleLineMask control.context.group control.context.l2b
      control.context.l1b control.context.mab control.context.pe cycle
      control.context.bar0 control.context.bar1 control.context.tWord = some (targets cycle))
    (prepared : ∀ cycle, prepareParsedMaskedConstantWrites files cycle (targets cycle)
      = .ok (destinationWrites cycle))
    (flushResolved : ∀ cycle, resolveFlushSelection? expression.flush files.maskRegisters cycle
      = some (flush cycle))
    (noForwardFalse : noForward = false) :
    ∃ writes,
      prepareParsedIntegerALUExprCycles files oldSlots oldSlots expression control
        hasSingleLineMask noForward reduced =
        .ok (writes, immediateALUSlots oldSlots payload sparse reduced flush) := by
  let w0 := immediateALUWrite payload sparse reduced (flush 0)
  let w1 := immediateALUWrite payload sparse reduced (flush 1)
  let w2 := immediateALUWrite payload sparse reduced (flush 2)
  let w3 := immediateALUWrite payload sparse reduced (flush 3)
  let s0 : ProofsLean.MNCore.Forwarding.Slots := oldSlots
  let s1 : ProofsLean.MNCore.Forwarding.Slots := fun unit cycle =>
    if unit = ProofsLean.MNCore.Forwarding.Unit.alu ∧ cycle = (0 : Fin 4) then .known (pack w0.data)
    else s0 unit cycle
  let s2 : ProofsLean.MNCore.Forwarding.Slots := fun unit cycle =>
    if unit = ProofsLean.MNCore.Forwarding.Unit.alu ∧ cycle = (1 : Fin 4) then .known (pack w1.data)
    else s1 unit cycle
  let s3 : ProofsLean.MNCore.Forwarding.Slots := fun unit cycle =>
    if unit = ProofsLean.MNCore.Forwarding.Unit.alu ∧ cycle = (2 : Fin 4) then .known (pack w2.data)
    else s2 unit cycle
  let s4 : ProofsLean.MNCore.Forwarding.Slots := fun unit cycle =>
    if unit = ProofsLean.MNCore.Forwarding.Unit.alu ∧ cycle = (3 : Fin 4) then .known (pack w3.data)
    else s3 unit cycle
  have step0 : prepareParsedIntegerALUExprCycle files oldSlots s0 expression control
      hasSingleLineMask noForward reduced 0 = .ok (destinationWrites 0 ++ [w0], s1) := by
    have updated : updateParsedIntegerALUForwardingCycle s0 0
        (.ok ⟨none, none, w0.data, w0.selection⟩) noForward = .ok s1 := by
      rw [noForwardFalse]
      exact updateParsedIntegerALUForwardingCycle_immediate s0 0 payload sparse reduced (flush 0)
    exact prepareParsedIntegerALUExprCycle_immediate files oldSlots s0 expression control
      hasSingleLineMask noForward reduced 0 (targets 0) (destinationWrites 0) (flush 0) s1
      payload sparse isImmediate (lowered 0) (prepared 0) (flushResolved 0) updated
  have step1 : prepareParsedIntegerALUExprCycle files oldSlots s1 expression control
      hasSingleLineMask noForward reduced 1 = .ok (destinationWrites 1 ++ [w1], s2) := by
    have updated : updateParsedIntegerALUForwardingCycle s1 1
        (.ok ⟨none, none, w1.data, w1.selection⟩) noForward = .ok s2 := by
      rw [noForwardFalse]
      exact updateParsedIntegerALUForwardingCycle_immediate s1 1 payload sparse reduced (flush 1)
    exact prepareParsedIntegerALUExprCycle_immediate files oldSlots s1 expression control
      hasSingleLineMask noForward reduced 1 (targets 1) (destinationWrites 1) (flush 1) s2
      payload sparse isImmediate (lowered 1) (prepared 1) (flushResolved 1) updated
  have step2 : prepareParsedIntegerALUExprCycle files oldSlots s2 expression control
      hasSingleLineMask noForward reduced 2 = .ok (destinationWrites 2 ++ [w2], s3) := by
    have updated : updateParsedIntegerALUForwardingCycle s2 2
        (.ok ⟨none, none, w2.data, w2.selection⟩) noForward = .ok s3 := by
      rw [noForwardFalse]
      exact updateParsedIntegerALUForwardingCycle_immediate s2 2 payload sparse reduced (flush 2)
    exact prepareParsedIntegerALUExprCycle_immediate files oldSlots s2 expression control
      hasSingleLineMask noForward reduced 2 (targets 2) (destinationWrites 2) (flush 2) s3
      payload sparse isImmediate (lowered 2) (prepared 2) (flushResolved 2) updated
  have step3 : prepareParsedIntegerALUExprCycle files oldSlots s3 expression control
      hasSingleLineMask noForward reduced 3 = .ok (destinationWrites 3 ++ [w3], s4) := by
    have updated : updateParsedIntegerALUForwardingCycle s3 3
        (.ok ⟨none, none, w3.data, w3.selection⟩) noForward = .ok s4 := by
      rw [noForwardFalse]
      exact updateParsedIntegerALUForwardingCycle_immediate s3 3 payload sparse reduced (flush 3)
    exact prepareParsedIntegerALUExprCycle_immediate files oldSlots s3 expression control
      hasSingleLineMask noForward reduced 3 (targets 3) (destinationWrites 3) (flush 3) s4
      payload sparse isImmediate (lowered 3) (prepared 3) (flushResolved 3) updated
  refine ⟨destinationWrites 0 ++ [w0] ++ destinationWrites 1 ++ [w1] ++
    destinationWrites 2 ++ [w2] ++ destinationWrites 3 ++ [w3], ?_⟩
  unfold prepareParsedIntegerALUExprCycles
  simp only [parsedIntegerALUCycles]
  rw [prepareParsedIntegerALUCycles.eq_2, step0]
  dsimp only
  rw [List.nil_append]
  rw [prepareParsedIntegerALUCycles.eq_2, step1]
  dsimp only
  rw [prepareParsedIntegerALUCycles.eq_2, step2]
  dsimp only
  rw [prepareParsedIntegerALUCycles.eq_2, step3]
  dsimp only
  rw [prepareParsedIntegerALUCycles.eq_1]
  simp only [StepResult.ok.injEq]
  refine Prod.ext ?_ ?_
  · simp [List.append_assoc]
  · funext unit cycle
    have hsmall : cycle.val = 0 ∨ cycle.val = 1 ∨ cycle.val = 2 ∨ cycle.val = 3 := by
      have := cycle.isLt
      omega
    rcases hsmall with h | h | h | h
    · have hc : cycle = 0 := Fin.ext (by simpa using h)
      rw [hc]
      cases unit <;> simp [s0, s1, s2, s3, s4, immediateALUSlots, w0, w1, w2, w3]
    · have hc : cycle = 1 := Fin.ext (by simpa using h)
      rw [hc]
      cases unit <;> simp [s0, s1, s2, s3, s4, immediateALUSlots, w0, w1, w2, w3]
    · have hc : cycle = 2 := Fin.ext (by simpa using h)
      rw [hc]
      cases unit <;> simp [s0, s1, s2, s3, s4, immediateALUSlots, w0, w1, w2, w3]
    · have hc : cycle = 3 := Fin.ext (by simpa using h)
      rw [hc]
      cases unit <;> simp [s0, s1, s2, s3, s4, immediateALUSlots, w0, w1, w2, w3]

/-- A row with no `.bar` destination has no ALU BAR updates. -/
theorem parsedIntegerALUBarUpdates_eq_nil (expression : ParsedExpr)
    (writes : List PreparedParsedMaskedWrite)
    (noBar : ∀ (lm1 : Bool) (width : Fin 5) (mask : Option ParsedMask),
      expression.destinations ≠ [.bar lm1 width mask]) :
    parsedIntegerALUBarUpdates expression writes = [] := by
  unfold parsedIntegerALUBarUpdates
  cases hd : expression.destinations with
  | nil => rfl
  | cons d rest =>
      cases rest with
      | nil =>
          cases d with
          | bar lm1 width mask => exact absurd hd (noBar lm1 width mask)
          | mem access neg ext rnd mask => rfl
          | forward kind neg ext rnd => rfl
          | fixed kind => rfl
          | omr entry mask => rfl
          | matrix y width row => rfl
          | nowrite => rfl
          | l1bm width address => rfl
          | l2bm address l2b => rfl
          | dar address => rfl
      | cons e rest2 => simp [parsedIntegerALUBarUpdates]

/-- **The two-line specialisation (convert-endian's first two lines).**

Line 1 is the single-row `.pe` line whose only row is `imm … ` (an
`.immediate`).  `lowering` is that row's own integer four-cycle preparation
(an explicit lowering: its prepared slot function is `immediateALUSlots`, which
`immediate_prepareParsedIntegerALUExprCycles` computes cycle by cycle).

Then, after line 1:

* every `.alu` forwarding slot at PE 0 holds the immediate's own prepared
  `$aluf` bus;
* consequently line 2's `$aluf` read — `readWithForwarding _ _ cycle
  (.forward .aluf false)` — returns that bus.

This is exactly the read convert-endian's second line performs. -/
theorem executeNormalizedLine_immediate_aluf_read
    (normalized : NormalizedExpr) (state next : State)
    (payload : BitVec 32) (sparse : Bool)
    (isImmediate : normalized.toParsed.op = .immediate payload sparse)
    (accepted : checkParsedTopLine
      (InstructionLine.pe [normalized]).toParsed = true)
    (flush : Fin 4 → Option PEWordSelection)
    (intWrites : List PreparedParsedMaskedWrite)
    (intBars : List (Bool × BitVec 12))
    (lowering : prepareParsedIntegerMatrixReadLineCycles (state.peRegisters welcomePE)
        (stateForwardingSlots state welcomePE)
        (state.matrixRegisters (ParsedIntegerContext.ofLinearIndex welcomePE).group
          (ParsedIntegerContext.ofLinearIndex welcomePE).l2b
          (ParsedIntegerContext.ofLinearIndex welcomePE).l1b)
        [normalized.toParsed]
        { directive := state.maskDirective
          context :=
            { (ParsedIntegerContext.ofLinearIndex welcomePE) with
              bar0 := (state.peContext welcomePE).bar0
              bar1 := (state.peContext welcomePE).bar1
              tWord := (state.peContext welcomePE).tWord }
          elapsedWords := state.hazardClock } false =
        .ok (intWrites,
          immediateALUSlots (stateForwardingSlots state welcomePE) payload sparse false flush,
          intBars))
    (executed : executeNormalizedLine (.pe [normalized]) state = .ok next) :
    (∀ cycle : Fin 4,
      stateForwardingSlots next welcomePE .alu cycle =
        .known (pack (immediateALUWrite payload sparse false (flush cycle)).data)) ∧
    (∀ cycle : Fin 4,
      ParsedIntegerInput.readWithForwarding (next.peRegisters welcomePE)
        (stateForwardingSlots next welcomePE) cycle (.forward .aluf false) =
        .ok (pack (immediateALUWrite payload sparse false (flush cycle)).data)) := by
  have rows : ([normalized].map NormalizedExpr.toParsed).all
      parsedExprIsLineExecRow = true := by
    simp [parsedExprIsLineExecRow, isImmediate, parsedExprIsUnsupportedRustAlu,
      parsedExprIsMslMsrProducer, parsedExprIsFloatReluProducer,
      parsedExprIsBlockFloatProducer]
  have hasALU : ([normalized].map NormalizedExpr.toParsed).any
      parsedExprIsIntegerProducer = true := by
    simp [parsedExprIsIntegerProducer, isImmediate]
  have noForward : ([normalized].map NormalizedExpr.toParsed).any (fun expression =>
      match expression.op with
      | .noforward => true
      | _ => false) = false := by
    simp [isImmediate]
  have noFloat : parsedExprIsSupportedFloatMAUProducer normalized.toParsed = false := by
    simp [parsedExprIsSupportedFloatMAUProducer, isImmediate]
  have stageInput : parsedExprIsIntegerMatrixReadStageInput normalized.toParsed = true :=
    parsedExprIsIntegerMatrixReadStageInput_of_lineExecRow normalized.toParsed
      (List.all_eq_true.mp rows normalized.toParsed (by simp)) noFloat
  have filterEq : List.filter parsedExprIsIntegerMatrixReadStageInput
      [normalized.toParsed] = [normalized.toParsed] := by
    simp [stageInput]
  obtain ⟨intWrites', intSlots', intBars', preparedEq, slotValues, reads⟩ :=
    executeNormalizedLine_pe_aluf_read [normalized] state next accepted rows hasALU noForward
      executed
  have preparedEq' : prepareParsedIntegerMatrixReadLineCycles (state.peRegisters welcomePE)
      (stateForwardingSlots state welcomePE)
      (state.matrixRegisters (ParsedIntegerContext.ofLinearIndex welcomePE).group
        (ParsedIntegerContext.ofLinearIndex welcomePE).l2b
        (ParsedIntegerContext.ofLinearIndex welcomePE).l1b)
      [normalized.toParsed]
      { directive := state.maskDirective
        context :=
          { (ParsedIntegerContext.ofLinearIndex welcomePE) with
            bar0 := (state.peContext welcomePE).bar0
            bar1 := (state.peContext welcomePE).bar1
            tWord := (state.peContext welcomePE).tWord }
        elapsedWords := state.hazardClock } false =
      .ok (intWrites', intSlots', intBars') := by
    simpa [stageInput, List.map_cons, List.map_nil] using preparedEq
  have slotsEq : intSlots' = immediateALUSlots (stateForwardingSlots state welcomePE)
      payload sparse false flush := by
    rw [preparedEq'] at lowering
    exact congrArg (fun triple => triple.2.1) (StepResult.ok.inj lowering)
  refine ⟨?_, ?_⟩
  · intro cycle
    rw [slotValues cycle, slotsEq]
    simp [immediateALUSlots]
  · intro cycle
    exact reads cycle _ (by
      rw [slotsEq]
      simp [immediateALUSlots])

end ProofsLean.MNCore

-- End of module: no sorry, no admit, no native_decide, no new axioms.
