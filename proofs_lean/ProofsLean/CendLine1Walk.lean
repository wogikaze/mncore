import ProofsLean.CendAnswerExec

/-! # `12.convert-endian` — line 1's 4096-PE walk

`ProofsLean.CendAnswerExec.cendImm_pecore` proves the *per-PE* core step of
line 1 (`imm i"0x34f80010" $r0v`) at an arbitrary PE: from the initial register
file, invalid forwarding, the linear-index context and the initial mask
directive, the step succeeds and installs
`commit (cendInitialPERegisters input) cendImmWrites`.  This module chains that
per-PE step over the whole `List.finRange 4096` walk and reads off line 1's step
at the initial state, i.e. the `line1` field of `CendAnswerExecResidual`.

## What is proved

* **The walk invariant** (`CendLine1WalkInvariant`): relative to the list
  `pending` of PEs not yet visited, every pending PE still has the initial
  register file, invalid forwarding and the linear-index context, while every
  PE outside `pending` already has the line-1 committed file
  `cendLine1Files input = commit (cendInitialPERegisters input) cendImmWrites`;
  the mask directive is the initial one throughout.  The invariant starts at
  `pending = List.finRange 4096` on `cendInitialState input`
  (`cendLine1WalkInvariant_initial`) and is preserved by every per-PE step
  (`executeIntegerProducerLineAtPEs_cendLine1_walk`): the only facts needed are
  the frame lemmas of the walk, which say that visiting `pe` leaves every other
  PE's files, forwarding validity and context untouched.
* **The walk succeeds unconditionally** from the initial state
  (`cendLine1_walk`): at the end `pending = []`, so *every* PE holds
  `cendLine1Files input`.
* **Line 1 executes** (`cendLine1_walk_and_execute`, `cendLine1_next`): the line
  step is `executeIntegerProducerInstructionLine` via
  `executeIntegerProducerInstructionLine_pe_lineExec` (all non-integer stages
  are the identity for the `imm` row), and the resulting state is the walk
  result with the clock advanced by the line cost and the L1BM turnaround
  validity cleared.  Explicitly, after line 1:

  - every PE's register file is `commit (cendInitialPERegisters input)
    cendImmWrites` (in particular PE 0's, the file line 2 reads LM0 from);
  - PE 0's LM0 is still `cendInitialPERegisters input.lm0`, so
    `readPair .lm0` returns the input word (`cendLine1_next`, using
    `commitParsedMaskedWrites_lm0_preserves`: line 1 only writes GRF0 and the
    ALU forwarding slots);
  - PE 0's `.alu` forwarding slots are `.known (pack cendImmALUWrite.data)`
    (re-exported from `cendLine1_aluf`);
  - the mask directive and the clock are the initial ones plus one cycle, and
    `l1bmTurnaroundValid = false`.

* **The residual field**: `cendAnswerExecResidual_line1` is exactly the `line1`
  field of `CendAnswerExecResidual`, and `cendAnswerExecResidual_of_tail` turns
  any proof of the `tail` field into the whole residual.

No `sorry`, no `admit`, no `native_decide`, no new axioms.
-/

namespace ProofsLean.MNCore

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

open Issue
open PEMemory

/-! ## 1. The register file line 1 installs at every PE -/

/-- The register file every PE holds after line 1: line 1 commits exactly the
eight prepared writes `cendImmWrites` to its own initial file.  (Every PE starts
from the same input word, so this is the same file at every PE.) -/
def cendLine1Files (input : BitVec 64) : IntegerRegisterFiles :=
  commitParsedMaskedWrites (cendInitialPERegisters input) cendImmWrites

theorem cendLine1Files_def (input : BitVec 64) :
    cendLine1Files input =
      commitParsedMaskedWrites (cendInitialPERegisters input) cendImmWrites := rfl

/-- The cost of line 1's issue line is one cycle. -/
theorem cendLine1_cost :
    InstructionLine.cost (.pe [cendImmExpr.normalize]) = 1 := rfl

/-! ### Line 1's writes never touch LM0

Line 1's eight writes are four GRF0 word writes (`cendImmWrite`) and four
`.alu` forwarding writes with no destination (`immediateALUWrite`).  The commit
fold therefore leaves the whole LM0 bank alone, which is what makes the input
word still readable in line 2. -/

/-- Writing any bank other than LM0 leaves the LM0 file untouched. -/
theorem writeRegisterBankMasked_lm0_of_ne (files : IntegerRegisterFiles)
    (bank : PEMemory.Bank) (width : PEMemory.Width) (address : Fin bank.capacity)
    (data : PEMemory.WordBus) (selection : PEMemory.PEWordSelection) (notLm0 : bank ≠ .lm0) :
    (writeRegisterBankMasked files bank width address data selection).lm0 = files.lm0 := by
  cases bank <;> simp_all [writeRegisterBankMasked]

/-- One commit step leaves LM0 untouched when the write has no mask update and
never targets LM0. -/
theorem welcomeCommitStep_lm0_preserves (files : IntegerRegisterFiles)
    (write : PreparedParsedMaskedWrite)
    (noMask : write.maskUpdate = none)
    (notLm0 : ∀ destination : PEMemory.DirectMemoryAccess,
      write.destination = some destination → destination.bank ≠ .lm0) :
    (welcomeCommitStep files write).lm0 = files.lm0 := by
  unfold welcomeCommitStep
  rw [noMask]
  simp only
  cases hdest : write.destination with
  | none => rfl
  | some destination =>
      simpa only [writeDirectAccessMasked] using
        writeRegisterBankMasked_lm0_of_ne files destination.bank destination.width
          destination.address write.data write.selection (notLm0 destination hdest)

/-- A commit fold whose writes have no mask update and never target LM0 leaves
LM0 untouched. -/
theorem commitParsedMaskedWrites_lm0_preserves (files : IntegerRegisterFiles)
    (writes : List PreparedParsedMaskedWrite)
    (keeps : ∀ write ∈ writes, write.maskUpdate = none ∧
      ∀ destination : PEMemory.DirectMemoryAccess,
        write.destination = some destination → destination.bank ≠ .lm0) :
    (commitParsedMaskedWrites files writes).lm0 = files.lm0 := by
  induction writes generalizing files with
  | nil => rfl
  | cons write rest ih =>
      rw [commitParsedMaskedWrites_cons]
      have hwrite := keeps write (by simp)
      have hrest : ∀ item ∈ rest, item.maskUpdate = none ∧
          ∀ destination : PEMemory.DirectMemoryAccess,
            item.destination = some destination → destination.bank ≠ .lm0 :=
        fun item mem => keeps item (List.mem_cons_of_mem write mem)
      exact (ih (welcomeCommitStep files write) hrest).trans
        (welcomeCommitStep_lm0_preserves files write hwrite.1 hwrite.2)

/-- A `cendImmWrite` targets the GRF0 word `cycle` and has no mask update. -/
theorem cendImmWrite_keeps (cycle : Fin 4) :
    (cendImmWrite cycle).maskUpdate = none ∧
      ∀ destination : PEMemory.DirectMemoryAccess,
        (cendImmWrite cycle).destination = some destination → destination.bank ≠ .lm0 := by
  constructor
  · rfl
  · intro destination hd
    simp only [cendImmWrite] at hd
    cases hd
    show PEMemory.Bank.grf0 ≠ PEMemory.Bank.lm0
    decide

/-- A `cendImmALUWrite` has no destination and no mask update. -/
theorem cendImmALUWrite_keeps :
    cendImmALUWrite.maskUpdate = none ∧
      ∀ destination : PEMemory.DirectMemoryAccess,
        cendImmALUWrite.destination = some destination → destination.bank ≠ .lm0 := by
  constructor
  · rfl
  · intro destination hd
    unfold cendImmALUWrite immediateALUWrite at hd
    cases hd

/-- Every write of `cendImmWrites` keeps LM0. -/
theorem cendImmWrites_keeps (write : PreparedParsedMaskedWrite) (mem : write ∈ cendImmWrites) :
    write.maskUpdate = none ∧
      ∀ destination : PEMemory.DirectMemoryAccess,
        write.destination = some destination → destination.bank ≠ .lm0 := by
  have hmem : write = cendImmWrite 0 ∨ write = cendImmALUWrite ∨
      write = cendImmWrite 1 ∨ write = cendImmALUWrite ∨
      write = cendImmWrite 2 ∨ write = cendImmALUWrite ∨
      write = cendImmWrite 3 ∨ write = cendImmALUWrite := by
    simpa [cendImmWrites, cendImmALUWrite] using mem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [cendImmWrite_keeps 0, cendImmALUWrite_keeps, cendImmWrite_keeps 1,
    cendImmALUWrite_keeps, cendImmWrite_keeps 2, cendImmALUWrite_keeps,
    cendImmWrite_keeps 3, cendImmALUWrite_keeps]

/-- **Line 1 preserves LM0 at every PE.** -/
theorem cendLine1Files_lm0 (input : BitVec 64) :
    (cendLine1Files input).lm0 = (cendInitialPERegisters input).lm0 :=
  commitParsedMaskedWrites_lm0_preserves (cendInitialPERegisters input) cendImmWrites
    cendImmWrites_keeps

/-- **The input word is still LM0 word 0 after line 1** — what line 2's `$m0v`
read consumes. -/
theorem cendLine1Files_lm0_readPair (input : BitVec 64) :
    FloatPEMemory.readPair .lm0 (cendLine1Files input).lm0 ⟨0, by decide⟩ = input := by
  rw [cendLine1Files_lm0]
  exact cendInitialLm0_readPair input

/-! ## 2. The walk invariant over a prefix of `List.finRange 4096` -/

/-- **The 4096-PE walk invariant of line 1, relative to the pending PEs.**

`pending` is the list of PEs the walk has *not* visited yet.  Pending PEs still
carry the initial file, invalid forwarding and the linear-index context (the
three facts `cendImm_pecore` consumes); every PE outside it already carries the
line-1 committed file.  The mask directive is the initial one. -/
structure CendLine1WalkInvariant (input : BitVec 64) (pending : List PEId)
    (state : State) : Prop where
  /-- Every pending PE still has the initial register file. -/
  filesPending : ∀ pe : PEId, pe ∈ pending →
    state.peRegisters pe = cendInitialPERegisters input
  /-- Every already-visited PE has the line-1 committed file. -/
  filesDone : ∀ pe : PEId, pe ∉ pending →
    state.peRegisters pe = cendLine1Files input
  /-- Every pending PE still has invalid forwarding. -/
  validPending : ∀ pe : PEId, pe ∈ pending →
    ∀ (unit : ProofsLean.MNCore.Forwarding.Unit) (cycle : Fin 4),
      state.forwardingValid pe unit cycle = false
  /-- Every pending PE still has the linear-index context. -/
  contextPending : ∀ pe : PEId, pe ∈ pending →
    state.peContext pe = ParsedIntegerContext.ofLinearIndex pe
  /-- The mask directive is the initial one. -/
  directive : state.maskDirective = rustSimulatorInitialState.maskDirective

/-- The invariant holds at the initial state with every PE pending. -/
theorem cendLine1WalkInvariant_initial (input : BitVec 64) :
    CendLine1WalkInvariant input (List.finRange 4096) (cendInitialState input) where
  filesPending := fun pe _ => cendInitialState_peRegisters input pe
  filesDone := fun pe absent => absurd (List.mem_finRange pe) absent
  validPending := fun _ _ _ _ => rfl
  contextPending := fun pe _ => cendInitialState_context input pe
  directive := cendInitialState_maskDirective input

/-! ## 3. One per-PE step of line 1 at a pending PE -/

/-- **Line 1's per-PE step at a pending PE.**  `cendImm_pecore` gives the core
step; the `executeIntegerProducerLineAtPE` wrapper only adds the BAR-writer
guard, which is false for an `.immediate` row (`cendImm` writes no BAR). -/
theorem cendLine1_executeAtPE (input : BitVec 64) (state : State) (pe : PEId)
    (filesEq : state.peRegisters pe = cendInitialPERegisters input)
    (validEq : ∀ (unit : ProofsLean.MNCore.Forwarding.Unit) (cycle : Fin 4),
      state.forwardingValid pe unit cycle = false)
    (contextEq : state.peContext pe = ParsedIntegerContext.ofLinearIndex pe)
    (directiveEq : state.maskDirective = rustSimulatorInitialState.maskDirective) :
    ∃ next : State,
      executeIntegerProducerLineAtPE [cendImmExpr.normalize.toParsed] state pe = .ok next ∧
      next.peRegisters pe = cendLine1Files input := by
  obtain ⟨next, executed, committed⟩ :=
    cendImm_pecore input state pe filesEq validEq contextEq directiveEq
  have notBARWriter : parsedExprIsIntegerBARWriter cendImmExpr.normalize.toParsed = false := by
    rw [cendImmParsed_eq]
    rfl
  refine ⟨next, ?_, committed⟩
  simpa [executeIntegerProducerLineAtPE, notBARWriter] using executed

/-! ## 4. The walk, by induction over the pending list -/

/-- **The walk preserves the invariant and succeeds.**  Starting from any state
satisfying the invariant for `pending`, walking exactly `pending` (which is
duplicate-free) succeeds and leaves every PE with the line-1 committed file
(`pending = []`). -/
theorem executeIntegerProducerLineAtPEs_cendLine1_walk
    (input : BitVec 64) (pending : List PEId) (state : State)
    (nodup : pending.Nodup)
    (inv : CendLine1WalkInvariant input pending state) :
    ∃ next : State,
      executeIntegerProducerLineAtPEs [cendImmExpr.normalize.toParsed] pending state = .ok next ∧
      CendLine1WalkInvariant input [] next := by
  induction pending generalizing state with
  | nil =>
      refine ⟨state, by simp [executeIntegerProducerLineAtPEs], ?_⟩
      exact
        { filesPending := fun pe mem => by simp at mem
          filesDone := fun pe _ => inv.filesDone pe (by simp)
          validPending := fun pe mem => by simp at mem
          contextPending := fun pe mem => by simp at mem
          directive := inv.directive }
  | cons pe rest ih =>
      obtain ⟨peNotRest, restNodup⟩ := List.nodup_cons.mp nodup
      have peMem : pe ∈ pe :: rest := by simp
      obtain ⟨middle, headExecuted, headFiles⟩ :=
        cendLine1_executeAtPE input state pe (inv.filesPending pe peMem)
          (inv.validPending pe peMem) (inv.contextPending pe peMem) inv.directive
      have middleInv : CendLine1WalkInvariant input rest middle := by
        refine
          { filesPending := ?_
            filesDone := ?_
            validPending := ?_
            contextPending := ?_
            directive := ?_ }
        · intro q mem
          have different : q ≠ pe := fun same => peNotRest (same ▸ mem)
          have frame := executeIntegerProducerLineAtPE_peFields_other
            [cendImmExpr.normalize.toParsed] state middle pe q different headExecuted
          rw [frame.1]
          exact inv.filesPending q (List.mem_cons_of_mem pe mem)
        · intro q notMemRest
          by_cases same : q = pe
          · subst same
            exact headFiles
          · have notMemCons : q ∉ pe :: rest := by
              intro member
              rcases List.mem_cons.mp member with head | tail
              · exact same head
              · exact notMemRest tail
            have frame := executeIntegerProducerLineAtPE_peFields_other
              [cendImmExpr.normalize.toParsed] state middle pe q same headExecuted
            rw [frame.1]
            exact inv.filesDone q notMemCons
        · intro q mem unit cycle
          have different : q ≠ pe := fun same => peNotRest (same ▸ mem)
          have frame := executeIntegerProducerLineAtPE_peFields_other
            [cendImmExpr.normalize.toParsed] state middle pe q different headExecuted
          rw [frame.2.2.1]
          exact inv.validPending q (List.mem_cons_of_mem pe mem) unit cycle
        · intro q mem
          have different : q ≠ pe := fun same => peNotRest (same ▸ mem)
          have frame := executeIntegerProducerLineAtPE_peFields_other
            [cendImmExpr.normalize.toParsed] state middle pe q different headExecuted
          rw [frame.2.2.2]
          exact inv.contextPending q (List.mem_cons_of_mem pe mem)
        · exact (executeIntegerProducerLineAtPE_maskDirective_hazardClock
            [cendImmExpr.normalize.toParsed] state middle pe headExecuted).1.trans
            inv.directive
      obtain ⟨next, tailExecuted, tailInv⟩ := ih middle restNodup middleInv
      refine ⟨next, ?_, tailInv⟩
      have unfoldEq : executeIntegerProducerLineAtPEs [cendImmExpr.normalize.toParsed]
          (pe :: rest) state =
          executeIntegerProducerLineAtPEs [cendImmExpr.normalize.toParsed] rest middle := by
        conv_lhs => unfold executeIntegerProducerLineAtPEs
        rw [headExecuted]
      rw [unfoldEq]
      exact tailExecuted

/-- **Line 1's walk succeeds from the initial state, and every PE ends on the
line-1 committed file.** -/
theorem cendLine1_walk (input : BitVec 64) :
    ∃ next : State,
      executeIntegerProducerLineAtPEs [cendImmExpr.normalize.toParsed]
          (List.finRange 4096) (cendInitialState input) = .ok next ∧
      (∀ pe : PEId, next.peRegisters pe = cendLine1Files input) ∧
      next.maskDirective = (cendInitialState input).maskDirective ∧
      next.hazardClock = (cendInitialState input).hazardClock := by
  obtain ⟨next, executed, inv⟩ :=
    executeIntegerProducerLineAtPEs_cendLine1_walk input (List.finRange 4096)
      (cendInitialState input) (List.nodup_finRange 4096)
      (cendLine1WalkInvariant_initial input)
  have frame := executeIntegerProducerLineAtPEs_maskDirective_hazardClock
    [cendImmExpr.normalize.toParsed] (List.finRange 4096) (cendInitialState input) next executed
  exact ⟨next, executed, fun pe => inv.filesDone pe (by simp), frame.1, frame.2⟩

/-! ## 5. The line step -/

/-- The executor's outer stage filter is the identity on line 1's single row. -/
theorem cendImm_lineExecFilter :
    ([cendImmExpr.normalize].map NormalizedExpr.toParsed).filter (fun expression =>
      !parsedExprIsL2BMProducer expression && !parsedExprIsMslMsrProducer expression &&
        !parsedExprIsMatrixMAUProducer expression && !parsedExprIsBlockFloatProducer expression &&
        !parsedExprIsFloatReluProducer expression) = [cendImmExpr.normalize.toParsed] := by
  simp only [List.map_cons, List.map_nil]
  rw [cendImmParsed_eq]
  decide

/-- Line 1's single row is a line-exec row. -/
theorem cendImm_lineExecRows :
    ([cendImmExpr.normalize].map NormalizedExpr.toParsed).all parsedExprIsLineExecRow = true := by
  simpa using cendImm_lineExecRow

/-- **Line 1's walk and line step together, with the walk result explicit.**
The line step's state is the walk's result with the clock advanced by the line
cost and `l1bmTurnaroundValid` cleared. -/
theorem cendLine1_walk_and_execute (input : BitVec 64) :
    ∃ nextPEs : State,
      executeIntegerProducerLineAtPEs [cendImmExpr.normalize.toParsed]
          (List.finRange 4096) (cendInitialState input) = .ok nextPEs ∧
      (∀ pe : PEId, nextPEs.peRegisters pe = cendLine1Files input) ∧
      executeNormalizedLine (.pe [cendImmExpr.normalize]) (cendInitialState input) =
        .ok { nextPEs with
          hazardClock := nextPEs.hazardClock + InstructionLine.cost (.pe [cendImmExpr.normalize])
          l1bmTurnaroundValid := false } := by
  obtain ⟨nextPEs, walkExecuted, filesAll, _, _⟩ := cendLine1_walk input
  have filtered : executeIntegerProducerLineAtPEs
      (([cendImmExpr.normalize].map NormalizedExpr.toParsed).filter (fun expression =>
        !parsedExprIsL2BMProducer expression && !parsedExprIsMslMsrProducer expression &&
          !parsedExprIsMatrixMAUProducer expression && !parsedExprIsBlockFloatProducer expression &&
          !parsedExprIsFloatReluProducer expression))
      (List.finRange 4096) (cendInitialState input) = .ok nextPEs := by
    rw [cendImm_lineExecFilter]
    exact walkExecuted
  have instruction := executeIntegerProducerInstructionLine_pe_lineExec
    [cendImmExpr.normalize] (cendInitialState input) nextPEs cendImmExpr_check
    cendImm_lineExecRows filtered
  have lineExecuted : executeNormalizedLine (.pe [cendImmExpr.normalize])
      (cendInitialState input) =
      .ok { nextPEs with
        hazardClock := nextPEs.hazardClock + 1
        l1bmTurnaroundValid := false } := by
    simpa only [executeNormalizedLine, NormalizedLine.toInstruction?, cendLine1_cost]
      using instruction
  exact ⟨nextPEs, walkExecuted, filesAll, lineExecuted⟩

/-! ## 6. The resulting state, explicitly -/

/-- **Line 1 executes at the initial state, and its result at every PE is
known.**

The state after line 1 is `{ nextPEs with hazardClock := nextPEs.hazardClock + 1,
l1bmTurnaroundValid := false }` for the walk result `nextPEs`, and:

* every PE's register file is `cendLine1Files input` — in particular PE 0's,
  which line 2 reads `$m0v` from;
* PE 0's LM0 is still the initial one, so `readPair .lm0` is the input word;
* PE 0's `.alu` forwarding slots hold the immediate bus
  `⟨0x34F80010 ++ 0x34F80010, 0x34F80010 ++ 0x34F80010⟩`;
* the mask directive is unchanged, the clock advances by one, and the L1BM
  turnaround validity bit is cleared. -/
theorem cendLine1_next (input : BitVec 64) :
    ∃ next : State,
      executeNormalizedLine (.pe [cendImmExpr.normalize]) (cendInitialState input) = .ok next ∧
      (∀ pe : PEId, next.peRegisters pe = cendLine1Files input) ∧
      (next.peRegisters cendPE).lm0 = (cendInitialPERegisters input).lm0 ∧
      FloatPEMemory.readPair .lm0 (next.peRegisters cendPE).lm0 ⟨0, by decide⟩ = input ∧
      (∀ cycle : Fin 4, stateForwardingSlots next cendPE .alu cycle =
        .known (⟨(0x34F80010 : BitVec 32) ++ (0x34F80010 : BitVec 32),
          (0x34F80010 : BitVec 32) ++ (0x34F80010 : BitVec 32)⟩ : IntegerALU.Bus)) ∧
      next.maskDirective = (cendInitialState input).maskDirective ∧
      next.hazardClock = (cendInitialState input).hazardClock + 1 ∧
      next.l1bmTurnaroundValid = false := by
  obtain ⟨nextPEs, walkExecuted, filesAll, lineExecuted⟩ := cendLine1_walk_and_execute input
  have frame := executeIntegerProducerLineAtPEs_maskDirective_hazardClock
    [cendImmExpr.normalize.toParsed] (List.finRange 4096) (cendInitialState input) nextPEs
    walkExecuted
  refine ⟨{ nextPEs with
      hazardClock := nextPEs.hazardClock + 1
      l1bmTurnaroundValid := false }, lineExecuted, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro pe
    exact filesAll pe
  · change (nextPEs.peRegisters cendPE).lm0 = (cendInitialPERegisters input).lm0
    rw [filesAll cendPE, cendLine1Files_lm0]
  · change FloatPEMemory.readPair .lm0 (nextPEs.peRegisters cendPE).lm0 ⟨0, by decide⟩ = input
    rw [filesAll cendPE]
    exact cendLine1Files_lm0_readPair input
  · intro cycle
    exact ((cendLine1_aluf input _ lineExecuted).1 cycle).trans
      (congrArg Forwarding.Value.known cendImmALUWrite_value)
  · exact frame.1
  · rw [frame.2]
  · rfl

/-- **PE 0's `.alu` forwarding is *valid* after line 1.**  This is the
complement of the walk invariant's pending-PE invalidity: visiting a PE turns
its `.alu` (and matrix-read) forwarding validity *on*, so a state-level reader
of `stateForwardingSlots` sees the prepared immediate bus rather than poison.
Only the PEs still pending in `CendLine1WalkInvariant` are guaranteed invalid,
which is exactly the hypothesis `cendImm_pecore` consumes. -/
theorem cendLine1_alu_valid (input : BitVec 64) (next : State)
    (executed : executeNormalizedLine (.pe [cendImmExpr.normalize])
      (cendInitialState input) = .ok next) :
    ∀ cycle : Fin 4, next.forwardingValid cendPE .alu cycle = true := by
  intro cycle
  have slots := (cendLine1_aluf input next executed).1 cycle
  cases h : next.forwardingValid cendPE .alu cycle with
  | false =>
      rw [stateForwardingSlots_invalid_is_poison next cendPE .alu cycle h] at slots
      cases slots
  | true => rfl

/-! ## 7. The residual field -/

/-- **Part (a) of `CendAnswerExecResidual`: line 1 executes at the initial
state**, unconditionally in the input. -/
theorem cendAnswerExecResidual_line1 :
    ∀ input : BitVec 64, ∃ next : State,
      executeNormalizedLine (.pe [cendImmExpr.normalize]) (cendInitialState input) = .ok next := by
  intro input
  exact ⟨_, (cendLine1_next input).choose_spec.1⟩

/-- **The residual from its `tail` field.**  Part (a) is proved here; any proof
of part (b) (lines 2 and 3) completes `CendAnswerExecResidual`. -/
theorem cendAnswerExecResidual_of_tail
    (tail : ∀ (input : BitVec 64) (s1 : State),
      executeNormalizedLine (.pe [cendImmExpr.normalize]) (cendInitialState input) = .ok s1 →
      ∃ result : State,
        ProofsLean.execute cendSealedMachine
          [.pe [cendIbslExpr.normalize, cendFmaExpr.normalize],
           .pe [cendSbslExpr.normalize]] s1 = some result ∧
        cendOutputPair result = byteSwap64 input) :
    CendAnswerExecResidual where
  line1 := cendAnswerExecResidual_line1
  tail := tail

/-! ## Trust report -/

#print axioms cendLine1Files_lm0
#print axioms cendLine1Files_lm0_readPair
#print axioms executeIntegerProducerLineAtPEs_cendLine1_walk
#print axioms cendLine1_walk
#print axioms cendLine1_walk_and_execute
#print axioms cendLine1_next
#print axioms cendLine1_alu_valid
#print axioms cendAnswerExecResidual_line1
#print axioms cendAnswerExecResidual_of_tail

end ProofsLean.MNCore
