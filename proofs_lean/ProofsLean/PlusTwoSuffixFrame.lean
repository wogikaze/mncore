import ProofsLean.ALURequestProvenance
import ProofsLean.PlusTwoSuffix
import ProofsLean.StageCommitWalk
import ProofsLean.WelcomePlainClose

/-! # The corrected `2.plus-two` suffix frame, and the refutation

`ProofsLean/PlusTwoSuffix.lean` reduced the refutation of the recorded
five-line `2.plus-two` answer to `PlusTwoSuffixPreservesWitness`, showed that
the *unconditional* frame is false (the second suffix line writes `LM1` word
`19` at `bar1 = 14`), and left two true obligations:

* `PlusTwoSuffixPreservesWitnessOfBar1Zero` — at states whose observed PE has
  `BAR1 = 0`, the four suffix lines keep `LM1` word `19`; and
* `PlusTwoLine1PreservesBar1Zero` — the first line keeps that `BAR1`.

This module discharges both, using the destination-provenance machinery of
`ProofsLean/ALURequestProvenance.lean`:

1. **The destination list of a successful plain cycle.**
   `plusTwoSuffixDest` is the `(bank, width, word)` triple
   `(.lm1, .word, (bar1 + parsedRegionAddressAt region cycle) % 4096)` of the
   direct `LM1` destination of a suffix line.  `plusTwoIdec_lowered` and
   `plusTwoIxor_lowered` prove, for *every* register file, directive, context
   and `bar1`, that the in-line lowering of the concrete recorded expression
   resolves to accesses with exactly this destination triple.  The proofs go
   through the request lemmas (`.dec`/`.xor` at `.i`), the generic unary/binary
   branch lemmas of `ALURequestProvenance` (the step `rw`/`simp` cannot do while
   the opcode is symbolic), and `directDestination_formula` from
   `PlusTwoSuffix.lean` for the address.
2. **Four-cycle projection.**
   `prepareParsedIntegerALUExprCycles_destination_triples` then pins the
   destination triple list of the four-cycle preparation to
   `[d 0, d 1, d 2, d 3]`, and
   `commitParsedMaskedWrites_lm1_preserves_of_destination_triples` (a wrapper
   around `commitParsedMaskedWrites_lm1_preserves_of_outside`) keeps `LM1`
   word `19` when no triple covers it.  At `bar1 = 0` the four destinations of
   each suffix line are `5,7,29,13` / `31,21,35,17` / `3,1,9,25` /
   `37,23,15,27`, all different from `19`.
3. **The line and walk plumbing.**
   `plusTwoLine_step_context` shows a plain singleton line whose destination
   is not a BAR write keeps the observed PE's context, hence `BAR1 = 0`; this
   needs `executeIntegerProducerLineAtPECore_peContext_eq_of_singleton`,
   the PE-level version and the walk's unvisited-PE frame
   (`executeIntegerProducerLineAtPEs_peContext_of_not_mem`).
   `plusTwoSuffixLine_frame` combines the write-list frame and the context
   frame for one concrete line.
4. **The headline.**
   * `plusTwoSuffix_preserves_witness_of_bar1 : PlusTwoSuffixPreservesWitnessOfBar1Zero`
   * `plusTwoLine1_preserves_bar1 : PlusTwoLine1PreservesBar1Zero`
   * `plusTwoRecorded_not_correct :
       ¬ ProofsLean.Correct plusTwoSealedMachine plusTwoSpec plusTwoRecordedAnswer`

   The last is unconditional: the all-zero input makes the first line write
   `0xFFFFFFFF` into output long 9, the four suffix lines preserve it at
   `BAR1 = 0`, and the specification demands `2`.

No `sorry`, no `admit`, no `native_decide`, no new axioms, no existing module
is edited.
-/

namespace ProofsLean.MNCore

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

open Issue
open PEMemory

/-! ### Commit frame through a destination-triple list -/

theorem commitParsedMaskedWrites_lm1_preserves_of_destination_triples
    (files : IntegerRegisterFiles) (writes : List PreparedParsedMaskedWrite)
    (triples : List (Option (PEMemory.Bank × PEMemory.Width × Nat)))
    (target : Fin Bank.lm1.capacity)
    (mapEq : writes.map (fun w => w.destination.map
      (fun d => (d.bank, d.width, d.address.val))) = triples)
    (outside : ∀ triple ∈ triples, ∀ (width : Width) (address : Nat),
      triple = some (PEMemory.Bank.lm1, width, address) →
        count .lm1 width ≤ (target.val + Bank.lm1.capacity - address) % Bank.lm1.capacity) :
    (commitParsedMaskedWrites files writes).lm1 target = files.lm1 target := by
  apply commitParsedMaskedWrites_lm1_preserves_of_outside
  intro write member width address destination
  have hmem : write.destination.map (fun d => (d.bank, d.width, d.address.val)) ∈ triples := by
    rw [← mapEq]
    exact List.mem_map_of_mem member
  have h := outside _ hmem width address.val (by rw [destination]; rfl)
  simpa [distance] using h

/-! ### Bar updates of the concrete suffix expressions -/

theorem plusTwoIdec_barUpdates (a b c d e f g h : Nat)
    (writes : List PreparedParsedMaskedWrite) :
    parsedIntegerALUBarUpdates (plusTwoIdec a b c d e f g h) writes = [] := by
  simp [parsedIntegerALUBarUpdates, plusTwoIdec, plusTwoMem]

theorem plusTwoIxor_barUpdates (a b c d e f g h i j k l : Nat)
    (writes : List PreparedParsedMaskedWrite) :
    parsedIntegerALUBarUpdates (plusTwoIxor a b c d e f g h i j k l) writes = [] := by
  simp [parsedIntegerALUBarUpdates, plusTwoIxor, plusTwoMem]

/-! ### A plain singleton step preserves the whole PE context -/

theorem executeIntegerProducerLineAtPECore_peContext_eq_of_singleton
    (expression : ParsedExpr) (state next : State)
    (plain : parsedExprIsPlainIntegerALU expression = true)
    (notFloat : parsedExprIsSupportedFloatMAUProducer expression = false)
    (barUpdatesNil : ∀ writes, parsedIntegerALUBarUpdates expression writes = [])
    (executed : executeIntegerProducerLineAtPECore [expression] state plusTwoPE = .ok next) :
    next.peContext = state.peContext := by
  have stageInput : parsedExprIsIntegerMatrixReadStageInput expression = true :=
    plain_stageInput expression plain
  have filterEq : [expression].filter parsedExprIsIntegerMatrixReadStageInput = [expression] := by
    simp [stageInput]
  have floatEmpty : [expression].filter parsedExprIsSupportedFloatMAUProducer = [] := by
    simp [notFloat]
  unfold executeIntegerProducerLineAtPECore parsedIntegerMatrixReadLineFourCycleStep at executed
  dsimp only at executed
  rw [filterEq] at executed
  generalize prepEq : prepareParsedIntegerMatrixReadLineCycles (state.peRegisters plusTwoPE)
    (stateForwardingSlots state plusTwoPE)
    (state.matrixRegisters (ParsedIntegerContext.ofLinearIndex plusTwoPE).group
      (ParsedIntegerContext.ofLinearIndex plusTwoPE).l2b
      (ParsedIntegerContext.ofLinearIndex plusTwoPE).l1b)
    [expression]
    { directive := state.maskDirective
      context := { (ParsedIntegerContext.ofLinearIndex plusTwoPE) with
        bar0 := (state.peContext plusTwoPE).bar0
        bar1 := (state.peContext plusTwoPE).bar1
        tWord := (state.peContext plusTwoPE).tWord }
      elapsedWords := state.hazardClock } false = prepared at executed
  have prepWelcome : welcomeIntegerPrep state plusTwoPE [expression] = prepared := by
    unfold welcomeIntegerPrep
    rw [filterEq]
    exact prepEq
  cases prepared with
  | failure => simp at executed
  | unknown => simp at executed
  | ok result =>
      obtain ⟨writes, slots, bars⟩ := result
      have fourCycle := welcomeIntegerPrep_inv state expression plain writes slots bars prepWelcome
      have hEq := welcomeIntegerPrep_single_plain_eq state expression plain
      rw [prepWelcome] at hEq
      rw [fourCycle] at hEq
      simp only [StepResult.ok.injEq, Prod.mk.injEq] at hEq
      have barsNil : bars = [] := by rw [hEq.2.2, barUpdatesNil]
      rw [barsNil] at executed
      dsimp only at executed
      rw [executeParsedFloatMAUsAtPE_noforward (floatEmpty := floatEmpty)] at executed
      dsimp only at executed
      split at executed
      · simp at executed
      · simp at executed
      · rename_i forwardingState
        simp only [StepResult.ok.injEq] at executed
        subst executed
        funext other
        by_cases same : other = plusTwoPE
        · subst same
          cases hctx : state.peContext plusTwoPE
          simp only [List.foldl_nil, ite_self, if_true]
        · simp [same]



/-! ### Lifting the context frame to one PE line and to the PE walk -/

theorem executeIntegerProducerLineAtPE_peContext_eq_of_singleton
    (expression : ParsedExpr) (state next : State)
    (plain : parsedExprIsPlainIntegerALU expression = true)
    (notFloat : parsedExprIsSupportedFloatMAUProducer expression = false)
    (notBARWriter : parsedExprIsIntegerBARWriter expression = false)
    (barUpdatesNil : ∀ writes, parsedIntegerALUBarUpdates expression writes = [])
    (executed : executeIntegerProducerLineAtPE [expression] state plusTwoPE = .ok next) :
    next.peContext = state.peContext := by
  unfold executeIntegerProducerLineAtPE at executed
  rw [show ([expression].any parsedExprIsIntegerBARWriter &&
      ([expression].length != 1)) = false by simp [notBARWriter]] at executed
  simp only [Bool.false_eq_true, if_false] at executed
  exact executeIntegerProducerLineAtPECore_peContext_eq_of_singleton expression state next
    plain notFloat barUpdatesNil executed

theorem executeIntegerProducerLineAtPEs_peContext_of_not_mem
    (expressions : List ParsedExpr) (pes : List PEId) (state next : State) (pe : PEId)
    (absent : pe ∉ pes)
    (executed : executeIntegerProducerLineAtPEs expressions pes state = .ok next) :
    next.peContext pe = state.peContext pe := by
  induction pes generalizing state next with
  | nil =>
      simp only [executeIntegerProducerLineAtPEs, StepResult.ok.injEq] at executed
      subst executed
      rfl
  | cons head rest ih =>
      simp only [List.mem_cons, not_or] at absent
      obtain ⟨headNe, absent⟩ := absent
      simp only [executeIntegerProducerLineAtPEs] at executed
      split at executed
      · simp at executed
      · simp at executed
      · rename_i middle headExec
        rw [ih middle next absent executed]
        exact (executeIntegerProducerLineAtPE_peFields_other expressions state middle head pe
          headNe headExec).2.2.2

/-! ### The per-line witness frame of one plain singleton suffix line -/

theorem plusTwoSuffixLine_frame
    (nExpr : NormalizedExpr) (expression : ParsedExpr)
    (expressionEq : expression = nExpr.toParsed)
    (name : ParsedAluName) (precision : ParsedPrecision) (unsigned : Bool)
    (arg : Option (Fin 256))
    (opShape : expression.op = .alu name (some precision) unsigned arg)
    (plain : parsedExprIsPlainIntegerALU expression = true)
    (notFloat : parsedExprIsSupportedFloatMAUProducer expression = false)
    (notBARWriter : parsedExprIsIntegerBARWriter expression = false)
    (barUpdatesNil : ∀ writes, parsedIntegerALUBarUpdates expression writes = [])
    (filterEq : ([nExpr].map NormalizedExpr.toParsed).filter (fun expression =>
      !parsedExprIsL2BMProducer expression && !parsedExprIsMslMsrProducer expression &&
        !parsedExprIsMatrixMAUProducer expression && !parsedExprIsBlockFloatProducer expression &&
        !parsedExprIsFloatReluProducer expression) = [expression])
    (dest : BitVec 12 → Fin 4 → PEMemory.Bank × PEMemory.Width × Nat)
    (lowered : ∀ (registers : Masks.RegisterFile) (directive : ParsedMaskDirective)
        (hasSingleLineMask : Bool) (group : Fin 4) (l2b : Fin 2) (l1b : Fin 8)
        (mab : Fin 16) (pe cycle : Fin 4) (bar0 bar1 : BitVec 12) (tWord : BitVec 32),
      ∃ accesses,
        ParsedExpr.toDirectMaskedIntegerAccessesInLine? expression registers directive
          hasSingleLineMask group l2b l1b mab pe cycle bar0 bar1 tWord = some accesses ∧
        (accesses.destination.bank, accesses.destination.width,
          accesses.destination.address.val) = dest bar1 cycle)
    (outside : ∀ (cycle : Fin 4) (width : Width) (address : Nat),
      dest 0 cycle = (PEMemory.Bank.lm1, width, address) →
        count .lm1 width ≤ ((plusTwoLowAddress plusTwoWitnessOutput).val +
          Bank.lm1.capacity - address) % Bank.lm1.capacity)
    (state next : State)
    (bar1Zero : (state.peContext plusTwoPE).bar1 = 0)
    (step : plusTwoSealedMachine.step (InstructionLine.pe [nExpr]) state = some next) :
    (next.peRegisters plusTwoPE).lm1 (plusTwoLowAddress plusTwoWitnessOutput) =
      (state.peRegisters plusTwoPE).lm1 (plusTwoLowAddress plusTwoWitnessOutput) ∧
    (next.peContext plusTwoPE).bar1 = 0 := by
  -- the sealed step is the instruction line step
  have executed : executeNormalizedLine (InstructionLine.pe [nExpr]).toNormalizedLine state
      = .ok next := by
    cases h : executeNormalizedLine (InstructionLine.pe [nExpr]).toNormalizedLine state with
    | ok result => simpa [plusTwoSealedMachine, h] using step
    | failure => simp [plusTwoSealedMachine, h] at step
    | unknown => simp [plusTwoSealedMachine, h] at step
  have lineExecuted : executeIntegerProducerInstructionLine (.pe [nExpr]) state = .ok next := by
    unfold executeNormalizedLine at executed
    simp only [Issue.InstructionLine.toNormalizedLine, NormalizedLine.toInstruction?] at executed
    exact executed
  -- the expression list is plain, so the walk is the integer stage
  have plainList : ([nExpr].map NormalizedExpr.toParsed).all parsedExprIsPlainIntegerALU = true := by
    simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, Bool.and_true]
    rw [show nExpr.toParsed = expression from expressionEq.symm]
    exact plain
  have accepted := executeIntegerProducerInstructionLine_accepted_of_ok (.pe [nExpr]) state next
    lineExecuted
  obtain ⟨nextPEs, walk, nextEq⟩ :=
    executeIntegerProducerInstructionLine_pe_plainIntegerALU_exists [nExpr] state next accepted
      plainList lineExecuted
  -- the stage filter keeps the expression
  have stageFilter : [expression].filter parsedExprIsIntegerMatrixReadStageInput = [expression] := by
    simp [plain_stageInput expression plain]
  have floatEmpty : [expression].filter parsedExprIsSupportedFloatMAUProducer = [] := by
    simp [notFloat]
  obtain ⟨split, absent⟩ := plusTwoFinRange_split
  rw [split, filterEq] at walk
  -- the observed PE's committed write list
  obtain ⟨prepared, prepWelcome, committed⟩ :=
    executeIntegerProducerLineAtPEs_zero_commit_list [expression]
      ((List.finRange 4095).map Fin.succ) state nextPEs absent floatEmpty walk
  obtain ⟨writes, slots, bars⟩ := prepared
  have fourCycle := welcomeIntegerPrep_inv state expression plain writes slots bars prepWelcome
  -- the four destinations, at the observed PE's BAR1 = 0
  let dest0 : Fin 4 → PEMemory.Bank × PEMemory.Width × Nat := dest 0
  have controlBar1 : (parsedPEHazardControl state plusTwoPE).context.bar1 = 0 := bar1Zero
  have lowered0 : ∀ cycle : Fin 4,
      ∃ accesses,
        ParsedExpr.toDirectMaskedIntegerAccessesInLine? expression
          (state.peRegisters plusTwoPE).maskRegisters (parsedPEHazardControl state plusTwoPE).directive
          ([expression].any parsedExprHasSingleLineWriteMask)
          (parsedPEHazardControl state plusTwoPE).context.group
          (parsedPEHazardControl state plusTwoPE).context.l2b
          (parsedPEHazardControl state plusTwoPE).context.l1b
          (parsedPEHazardControl state plusTwoPE).context.mab
          (parsedPEHazardControl state plusTwoPE).context.pe cycle
          (parsedPEHazardControl state plusTwoPE).context.bar0
          (parsedPEHazardControl state plusTwoPE).context.bar1
          (parsedPEHazardControl state plusTwoPE).context.tWord = some accesses ∧
        (accesses.destination.bank, accesses.destination.width,
          accesses.destination.address.val) = dest0 cycle := by
    intro cycle
    obtain ⟨accesses, loweredEq, triple⟩ := lowered
      (state.peRegisters plusTwoPE).maskRegisters
      (parsedPEHazardControl state plusTwoPE).directive
      ([expression].any parsedExprHasSingleLineWriteMask)
      (parsedPEHazardControl state plusTwoPE).context.group
      (parsedPEHazardControl state plusTwoPE).context.l2b
      (parsedPEHazardControl state plusTwoPE).context.l1b
      (parsedPEHazardControl state plusTwoPE).context.mab
      (parsedPEHazardControl state plusTwoPE).context.pe cycle
      (parsedPEHazardControl state plusTwoPE).context.bar0
      (parsedPEHazardControl state plusTwoPE).context.bar1
      (parsedPEHazardControl state plusTwoPE).context.tWord
    refine ⟨accesses, loweredEq, ?_⟩
    rw [triple, controlBar1]
  have destTriples := prepareParsedIntegerALUExprCycles_destination_triples
    (state.peRegisters plusTwoPE) (stateForwardingSlots state plusTwoPE)
    (stateForwardingSlots state plusTwoPE) expression (parsedPEHazardControl state plusTwoPE)
    ([expression].any parsedExprHasSingleLineWriteMask)
    ([expression].any (fun expression =>
      match expression.op with
      | .noforward => true
      | _ => false)) false name precision unsigned arg opShape dest0 lowered0
    writes slots fourCycle
  have destList : writes.map (fun w => w.destination.map
      (fun d => (d.bank, d.width, d.address.val))) =
      [some (dest0 0), some (dest0 1), some (dest0 2), some (dest0 3)] := destTriples
  have outsideList : ∀ triple ∈ [some (dest0 0), some (dest0 1), some (dest0 2),
      some (dest0 3)], ∀ (width : Width) (address : Nat),
      triple = some (PEMemory.Bank.lm1, width, address) →
        count .lm1 width ≤ ((plusTwoLowAddress plusTwoWitnessOutput).val +
          Bank.lm1.capacity - address) % Bank.lm1.capacity := by
    intro triple hmem width address heq
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hmem
    rcases hmem with h0 | h1 | h2 | h3
    · subst h0
      exact outside 0 width address (by simpa [dest0] using heq)
    · subst h1
      exact outside 1 width address (by simpa [dest0] using heq)
    · subst h2
      exact outside 2 width address (by simpa [dest0] using heq)
    · subst h3
      exact outside 3 width address (by simpa [dest0] using heq)
  have preserve := commitParsedMaskedWrites_lm1_preserves_of_destination_triples
    (state.peRegisters plusTwoPE) writes
    [some (dest0 0), some (dest0 1), some (dest0 2), some (dest0 3)]
    (plusTwoLowAddress plusTwoWitnessOutput) destList outsideList
  -- the observed PE's context is only touched by its own (head) step
  obtain ⟨middle, headExec⟩ :=
    executeIntegerProducerLineAtPEs_head_ok [expression] plusTwoPE
      ((List.finRange 4095).map Fin.succ) state nextPEs walk
  have headContext : middle.peContext = state.peContext :=
    executeIntegerProducerLineAtPE_peContext_eq_of_singleton expression state middle plain
      notFloat notBARWriter barUpdatesNil headExec
  have tailWalk : executeIntegerProducerLineAtPEs [expression]
      ((List.finRange 4095).map Fin.succ) middle = .ok nextPEs := by
    simp only [executeIntegerProducerLineAtPEs, headExec] at walk
    exact walk
  have tailContext : nextPEs.peContext plusTwoPE = middle.peContext plusTwoPE :=
    executeIntegerProducerLineAtPEs_peContext_of_not_mem [expression]
      ((List.finRange 4095).map Fin.succ) middle nextPEs plusTwoPE absent tailWalk
  constructor
  · rw [nextEq]
    simp only
    rw [committed, preserve]
  · rw [nextEq]
    simp only
    rw [tailContext, headContext]
    exact bar1Zero



/-! ### Line-level BAR1 frame, independent of the write list -/

theorem plusTwoLine_step_context
    (nExpr : NormalizedExpr) (expression : ParsedExpr)
    (expressionEq : expression = nExpr.toParsed)
    (plain : parsedExprIsPlainIntegerALU expression = true)
    (notFloat : parsedExprIsSupportedFloatMAUProducer expression = false)
    (notBARWriter : parsedExprIsIntegerBARWriter expression = false)
    (barUpdatesNil : ∀ writes, parsedIntegerALUBarUpdates expression writes = [])
    (filterEq : ([nExpr].map NormalizedExpr.toParsed).filter (fun expression =>
      !parsedExprIsL2BMProducer expression && !parsedExprIsMslMsrProducer expression &&
        !parsedExprIsMatrixMAUProducer expression && !parsedExprIsBlockFloatProducer expression &&
        !parsedExprIsFloatReluProducer expression) = [expression])
    (state next : State)
    (step : plusTwoSealedMachine.step (InstructionLine.pe [nExpr]) state = some next) :
    (next.peContext plusTwoPE).bar1 = (state.peContext plusTwoPE).bar1 := by
  have executed : executeNormalizedLine (InstructionLine.pe [nExpr]).toNormalizedLine state
      = .ok next := by
    cases h : executeNormalizedLine (InstructionLine.pe [nExpr]).toNormalizedLine state with
    | ok result => simpa [plusTwoSealedMachine, h] using step
    | failure => simp [plusTwoSealedMachine, h] at step
    | unknown => simp [plusTwoSealedMachine, h] at step
  have lineExecuted : executeIntegerProducerInstructionLine (.pe [nExpr]) state = .ok next := by
    unfold executeNormalizedLine at executed
    simp only [Issue.InstructionLine.toNormalizedLine, NormalizedLine.toInstruction?] at executed
    exact executed
  have plainList : ([nExpr].map NormalizedExpr.toParsed).all parsedExprIsPlainIntegerALU = true := by
    simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, Bool.and_true]
    rw [show nExpr.toParsed = expression from expressionEq.symm]
    exact plain
  have accepted := executeIntegerProducerInstructionLine_accepted_of_ok (.pe [nExpr]) state next
    lineExecuted
  obtain ⟨nextPEs, walk, nextEq⟩ :=
    executeIntegerProducerInstructionLine_pe_plainIntegerALU_exists [nExpr] state next accepted
      plainList lineExecuted
  rw [filterEq] at walk
  obtain ⟨split, absent⟩ := plusTwoFinRange_split
  rw [split] at walk
  obtain ⟨middle, headExec⟩ :=
    executeIntegerProducerLineAtPEs_head_ok [expression] plusTwoPE
      ((List.finRange 4095).map Fin.succ) state nextPEs walk
  have headContext : middle.peContext = state.peContext :=
    executeIntegerProducerLineAtPE_peContext_eq_of_singleton expression state middle plain
      notFloat notBARWriter barUpdatesNil headExec
  have tailWalk : executeIntegerProducerLineAtPEs [expression]
      ((List.finRange 4095).map Fin.succ) middle = .ok nextPEs := by
    simp only [executeIntegerProducerLineAtPEs, headExec] at walk
    exact walk
  have tailContext : nextPEs.peContext plusTwoPE = middle.peContext plusTwoPE :=
    executeIntegerProducerLineAtPEs_peContext_of_not_mem [expression]
      ((List.finRange 4095).map Fin.succ) middle nextPEs plusTwoPE absent tailWalk
  rw [nextEq]
  simp only
  rw [tailContext, headContext]



/-- The destination triple of a one-word `LM1` region at `bar1`. -/
def plusTwoSuffixDest (a b c d : Nat) (bar1 : BitVec 12) (cycle : Fin 4) :
    PEMemory.Bank × PEMemory.Width × Nat :=
  (.lm1, .word, (bar1.toNat + parsedRegionAddressAt ⟨1, a, b, c, d, false, none⟩ cycle) % 4096)

theorem plusTwoIdec_lowered
    (a b c d e f g h : Nat) (registers : Masks.RegisterFile)
    (directive : ParsedMaskDirective) (hasSingleLineMask : Bool) (group : Fin 4)
    (l2b : Fin 2) (l1b : Fin 8) (mab : Fin 16) (pe cycle : Fin 4)
    (bar0 bar1 : BitVec 12) (tWord : BitVec 32) :
    ∃ accesses,
      ParsedExpr.toDirectMaskedIntegerAccessesInLine? (plusTwoIdec a b c d e f g h)
        registers directive hasSingleLineMask group l2b l1b mab pe cycle bar0 bar1 tWord =
        some accesses ∧
      (accesses.destination.bank, accesses.destination.width,
        accesses.destination.address.val) = plusTwoSuffixDest e f g h bar1 cycle := by
  have request : (plusTwoIdec a b c d e f g h).op.executionRequest =
      .ok (.integer .word (.arith .dec false)) := rfl
  obtain ⟨sel, selEq⟩ : ∃ sel, ParsedOperand.resolveMemoryWriteSelection?
      (plusTwoMem .lm1 e f g h) .lm1 registers cycle directive hasSingleLineMask = some sel := by
    cases hasSingleLineMask <;> exact ⟨_, rfl⟩
  have sourceEq : ParsedOperand.toParsedIntegerInput? (plusTwoMem .lm0 a b c d) .word
      group l2b l1b mab pe cycle bar0 bar1 tWord =
      some (.memory ⟨.lm0, .word,
        ⟨(bar0.toNat + parsedRegionAddressAt ⟨1, a, b, c, d, false, none⟩ cycle) % 4096,
          Nat.mod_lt _ (by decide)⟩⟩ false) := by
    simp [plusTwoMem, plusTwoWordRegion, ParsedOperand.toParsedIntegerInput?,
      ParsedOperand.toDirectMemoryAccess?, ParsedOperand.toDirectMemoryAccessMode?,
      issueBankToRegisterBank, parsedWidth?, parsedRegionAddressAt, Width.words, Bank.capacity]
  have destinationEq : (ParsedOperand.toDirectMemoryDestination? (plusTwoMem .lm1 e f g h)
      pe cycle bar0 bar1 tWord).map (fun d => (d.bank, d.width, d.address.val)) =
      some (plusTwoSuffixDest e f g h bar1 cycle) := by
    rw [directDestination_formula]
    rfl
  obtain ⟨accesses, lowered, destination⟩ :=
    toDirectMaskedIntegerAccessesInLine?_alu_unary_triple (plusTwoIdec a b c d e f g h)
      .dec .i false none rfl .word (.arith .dec false) request rfl registers directive
      hasSingleLineMask (plusTwoMem .lm0 a b c d) (plusTwoMem .lm1 e f g h) rfl rfl
      group l2b l1b mab pe cycle bar0 bar1 tWord _ (plusTwoSuffixDest e f g h bar1 cycle)
      sel none sourceEq destinationEq selEq rfl
  exact ⟨accesses, lowered, destination⟩

theorem plusTwoIxor_lowered
    (a b c d e f g h i j k l : Nat) (registers : Masks.RegisterFile)
    (directive : ParsedMaskDirective) (hasSingleLineMask : Bool) (group : Fin 4)
    (l2b : Fin 2) (l1b : Fin 8) (mab : Fin 16) (pe cycle : Fin 4)
    (bar0 bar1 : BitVec 12) (tWord : BitVec 32) :
    ∃ accesses,
      ParsedExpr.toDirectMaskedIntegerAccessesInLine? (plusTwoIxor a b c d e f g h i j k l)
        registers directive hasSingleLineMask group l2b l1b mab pe cycle bar0 bar1 tWord =
        some accesses ∧
      (accesses.destination.bank, accesses.destination.width,
        accesses.destination.address.val) = plusTwoSuffixDest i j k l bar1 cycle := by
  have request : (plusTwoIxor a b c d e f g h i j k l).op.executionRequest =
      .ok (.integer .word .bitXor) := rfl
  obtain ⟨sel, selEq⟩ : ∃ sel, ParsedOperand.resolveMemoryWriteSelection?
      (plusTwoMem .lm1 i j k l) .lm1 registers cycle directive hasSingleLineMask = some sel := by
    cases hasSingleLineMask <;> exact ⟨_, rfl⟩
  have sourceXEq : ParsedOperand.toParsedIntegerInput? (plusTwoMem .lm0 a b c d) .word
      group l2b l1b mab pe cycle bar0 bar1 tWord =
      some (.memory ⟨.lm0, .word,
        ⟨(bar0.toNat + parsedRegionAddressAt ⟨1, a, b, c, d, false, none⟩ cycle) % 4096,
          Nat.mod_lt _ (by decide)⟩⟩ false) := by
    simp [plusTwoMem, plusTwoWordRegion, ParsedOperand.toParsedIntegerInput?,
      ParsedOperand.toDirectMemoryAccess?, ParsedOperand.toDirectMemoryAccessMode?,
      issueBankToRegisterBank, parsedWidth?, parsedRegionAddressAt, Width.words, Bank.capacity]
  have sourceYEq : ParsedOperand.toParsedIntegerInput? (plusTwoMem .grf0 e f g h) .word
      group l2b l1b mab pe cycle bar0 bar1 tWord =
      some (.memory ⟨.grf0, .word,
        ⟨parsedRegionAddressAt ⟨1, e, f, g, h, false, none⟩ cycle % 512,
          Nat.mod_lt _ (by decide)⟩⟩ false) := by
    simp [plusTwoMem, plusTwoWordRegion, ParsedOperand.toParsedIntegerInput?,
      ParsedOperand.toDirectMemoryAccess?, ParsedOperand.toDirectMemoryAccessMode?,
      issueBankToRegisterBank, parsedWidth?, parsedRegionAddressAt, Width.words, Bank.capacity]
  have destinationEq : (ParsedOperand.toDirectMemoryDestination? (plusTwoMem .lm1 i j k l)
      pe cycle bar0 bar1 tWord).map (fun d => (d.bank, d.width, d.address.val)) =
      some (plusTwoSuffixDest i j k l bar1 cycle) := by
    rw [directDestination_formula]
    rfl
  obtain ⟨accesses, lowered, destination⟩ :=
    toDirectMaskedIntegerAccessesInLine?_alu_binary_triple (plusTwoIxor a b c d e f g h i j k l)
      .xor .i false none rfl .word .bitXor request rfl registers directive
      hasSingleLineMask (plusTwoMem .lm0 a b c d) (plusTwoMem .grf0 e f g h)
      (plusTwoMem .lm1 i j k l) rfl rfl group l2b l1b mab pe cycle bar0 bar1 tWord
      _ _ (plusTwoSuffixDest i j k l bar1 cycle) sel none sourceXEq sourceYEq
      destinationEq selEq rfl
  exact ⟨accesses, lowered, destination⟩


/-! ### The four recorded suffix lines -/

def plusTwoSuffixLine2NExpr : NormalizedExpr := (plusTwoIdec 9 29 13 39 5 7 29 13).normalize
def plusTwoSuffixLine2 : InstructionLine := InstructionLine.pe [plusTwoSuffixLine2NExpr]
def plusTwoSuffixLine3NExpr : NormalizedExpr := (plusTwoIdec 21 23 17 15 31 21 35 17).normalize
def plusTwoSuffixLine3 : InstructionLine := InstructionLine.pe [plusTwoSuffixLine3NExpr]
def plusTwoSuffixLine4NExpr : NormalizedExpr :=
  (plusTwoIxor 11 7 39 27 1 1 0 2 3 1 9 25).normalize
def plusTwoSuffixLine4 : InstructionLine := InstructionLine.pe [plusTwoSuffixLine4NExpr]
def plusTwoSuffixLine5NExpr : NormalizedExpr :=
  (plusTwoIxor 27 5 37 19 0 3 0 1 37 23 15 27).normalize
def plusTwoSuffixLine5 : InstructionLine := InstructionLine.pe [plusTwoSuffixLine5NExpr]

theorem plusTwoSuffix_eq :
    plusTwoSuffix = [plusTwoSuffixLine2, plusTwoSuffixLine3, plusTwoSuffixLine4,
      plusTwoSuffixLine5] := rfl

theorem plusTwoSuffixLine2_plain :
    parsedExprIsPlainIntegerALU (plusTwoSuffixLine2NExpr.toParsed) = true := by decide
theorem plusTwoSuffixLine2_notFloat :
    parsedExprIsSupportedFloatMAUProducer (plusTwoSuffixLine2NExpr.toParsed) = false := by decide
theorem plusTwoSuffixLine2_notBAR :
    parsedExprIsIntegerBARWriter (plusTwoSuffixLine2NExpr.toParsed) = false := by decide
theorem plusTwoSuffixLine2_filter :
    ([plusTwoSuffixLine2NExpr].map NormalizedExpr.toParsed).filter (fun expression =>
      !parsedExprIsL2BMProducer expression && !parsedExprIsMslMsrProducer expression &&
        !parsedExprIsMatrixMAUProducer expression && !parsedExprIsBlockFloatProducer expression &&
        !parsedExprIsFloatReluProducer expression) = [plusTwoSuffixLine2NExpr.toParsed] := by
  decide

theorem plusTwoSuffixLine3_plain :
    parsedExprIsPlainIntegerALU (plusTwoSuffixLine3NExpr.toParsed) = true := by decide
theorem plusTwoSuffixLine3_notFloat :
    parsedExprIsSupportedFloatMAUProducer (plusTwoSuffixLine3NExpr.toParsed) = false := by decide
theorem plusTwoSuffixLine3_notBAR :
    parsedExprIsIntegerBARWriter (plusTwoSuffixLine3NExpr.toParsed) = false := by decide
theorem plusTwoSuffixLine3_filter :
    ([plusTwoSuffixLine3NExpr].map NormalizedExpr.toParsed).filter (fun expression =>
      !parsedExprIsL2BMProducer expression && !parsedExprIsMslMsrProducer expression &&
        !parsedExprIsMatrixMAUProducer expression && !parsedExprIsBlockFloatProducer expression &&
        !parsedExprIsFloatReluProducer expression) = [plusTwoSuffixLine3NExpr.toParsed] := by
  decide

theorem plusTwoSuffixLine4_plain :
    parsedExprIsPlainIntegerALU (plusTwoSuffixLine4NExpr.toParsed) = true := by decide
theorem plusTwoSuffixLine4_notFloat :
    parsedExprIsSupportedFloatMAUProducer (plusTwoSuffixLine4NExpr.toParsed) = false := by decide
theorem plusTwoSuffixLine4_notBAR :
    parsedExprIsIntegerBARWriter (plusTwoSuffixLine4NExpr.toParsed) = false := by decide
theorem plusTwoSuffixLine4_filter :
    ([plusTwoSuffixLine4NExpr].map NormalizedExpr.toParsed).filter (fun expression =>
      !parsedExprIsL2BMProducer expression && !parsedExprIsMslMsrProducer expression &&
        !parsedExprIsMatrixMAUProducer expression && !parsedExprIsBlockFloatProducer expression &&
        !parsedExprIsFloatReluProducer expression) = [plusTwoSuffixLine4NExpr.toParsed] := by
  decide

theorem plusTwoSuffixLine5_plain :
    parsedExprIsPlainIntegerALU (plusTwoSuffixLine5NExpr.toParsed) = true := by decide
theorem plusTwoSuffixLine5_notFloat :
    parsedExprIsSupportedFloatMAUProducer (plusTwoSuffixLine5NExpr.toParsed) = false := by decide
theorem plusTwoSuffixLine5_notBAR :
    parsedExprIsIntegerBARWriter (plusTwoSuffixLine5NExpr.toParsed) = false := by decide
theorem plusTwoSuffixLine5_filter :
    ([plusTwoSuffixLine5NExpr].map NormalizedExpr.toParsed).filter (fun expression =>
      !parsedExprIsL2BMProducer expression && !parsedExprIsMslMsrProducer expression &&
        !parsedExprIsMatrixMAUProducer expression && !parsedExprIsBlockFloatProducer expression &&
        !parsedExprIsFloatReluProducer expression) = [plusTwoSuffixLine5NExpr.toParsed] := by
  decide

/-! ### The destination triples avoid word `19` at `BAR1 = 0` -/

theorem plusTwoSuffixDest_outside_5_7_29_13 :
    ∀ (cycle : Fin 4) (width : Width) (address : Nat),
      plusTwoSuffixDest 5 7 29 13 0 cycle = (PEMemory.Bank.lm1, width, address) →
        count .lm1 width ≤ ((plusTwoLowAddress plusTwoWitnessOutput).val +
          Bank.lm1.capacity - address) % Bank.lm1.capacity := by
  intro cycle width address h
  have hcycle : cycle.val = 0 ∨ cycle.val = 1 ∨ cycle.val = 2 ∨ cycle.val = 3 := by
    have := cycle.isLt; omega
  rcases hcycle with h0 | h1 | h2 | h3
  · simp only [plusTwoSuffixDest, parsedRegionAddressAt, h0] at h ⊢
    obtain ⟨rfl, rfl⟩ := h
    decide
  · simp only [plusTwoSuffixDest, parsedRegionAddressAt, h1] at h ⊢
    obtain ⟨rfl, rfl⟩ := h
    decide
  · simp only [plusTwoSuffixDest, parsedRegionAddressAt, h2] at h ⊢
    obtain ⟨rfl, rfl⟩ := h
    decide
  · simp only [plusTwoSuffixDest, parsedRegionAddressAt, h3] at h ⊢
    obtain ⟨rfl, rfl⟩ := h
    decide

theorem plusTwoSuffixDest_outside_31_21_35_17 :
    ∀ (cycle : Fin 4) (width : Width) (address : Nat),
      plusTwoSuffixDest 31 21 35 17 0 cycle = (PEMemory.Bank.lm1, width, address) →
        count .lm1 width ≤ ((plusTwoLowAddress plusTwoWitnessOutput).val +
          Bank.lm1.capacity - address) % Bank.lm1.capacity := by
  intro cycle width address h
  have hcycle : cycle.val = 0 ∨ cycle.val = 1 ∨ cycle.val = 2 ∨ cycle.val = 3 := by
    have := cycle.isLt; omega
  rcases hcycle with h0 | h1 | h2 | h3
  · simp only [plusTwoSuffixDest, parsedRegionAddressAt, h0] at h ⊢
    obtain ⟨rfl, rfl⟩ := h
    decide
  · simp only [plusTwoSuffixDest, parsedRegionAddressAt, h1] at h ⊢
    obtain ⟨rfl, rfl⟩ := h
    decide
  · simp only [plusTwoSuffixDest, parsedRegionAddressAt, h2] at h ⊢
    obtain ⟨rfl, rfl⟩ := h
    decide
  · simp only [plusTwoSuffixDest, parsedRegionAddressAt, h3] at h ⊢
    obtain ⟨rfl, rfl⟩ := h
    decide

theorem plusTwoSuffixDest_outside_3_1_9_25 :
    ∀ (cycle : Fin 4) (width : Width) (address : Nat),
      plusTwoSuffixDest 3 1 9 25 0 cycle = (PEMemory.Bank.lm1, width, address) →
        count .lm1 width ≤ ((plusTwoLowAddress plusTwoWitnessOutput).val +
          Bank.lm1.capacity - address) % Bank.lm1.capacity := by
  intro cycle width address h
  have hcycle : cycle.val = 0 ∨ cycle.val = 1 ∨ cycle.val = 2 ∨ cycle.val = 3 := by
    have := cycle.isLt; omega
  rcases hcycle with h0 | h1 | h2 | h3
  · simp only [plusTwoSuffixDest, parsedRegionAddressAt, h0] at h ⊢
    obtain ⟨rfl, rfl⟩ := h
    decide
  · simp only [plusTwoSuffixDest, parsedRegionAddressAt, h1] at h ⊢
    obtain ⟨rfl, rfl⟩ := h
    decide
  · simp only [plusTwoSuffixDest, parsedRegionAddressAt, h2] at h ⊢
    obtain ⟨rfl, rfl⟩ := h
    decide
  · simp only [plusTwoSuffixDest, parsedRegionAddressAt, h3] at h ⊢
    obtain ⟨rfl, rfl⟩ := h
    decide

theorem plusTwoSuffixDest_outside_37_23_15_27 :
    ∀ (cycle : Fin 4) (width : Width) (address : Nat),
      plusTwoSuffixDest 37 23 15 27 0 cycle = (PEMemory.Bank.lm1, width, address) →
        count .lm1 width ≤ ((plusTwoLowAddress plusTwoWitnessOutput).val +
          Bank.lm1.capacity - address) % Bank.lm1.capacity := by
  intro cycle width address h
  have hcycle : cycle.val = 0 ∨ cycle.val = 1 ∨ cycle.val = 2 ∨ cycle.val = 3 := by
    have := cycle.isLt; omega
  rcases hcycle with h0 | h1 | h2 | h3
  · simp only [plusTwoSuffixDest, parsedRegionAddressAt, h0] at h ⊢
    obtain ⟨rfl, rfl⟩ := h
    decide
  · simp only [plusTwoSuffixDest, parsedRegionAddressAt, h1] at h ⊢
    obtain ⟨rfl, rfl⟩ := h
    decide
  · simp only [plusTwoSuffixDest, parsedRegionAddressAt, h2] at h ⊢
    obtain ⟨rfl, rfl⟩ := h
    decide
  · simp only [plusTwoSuffixDest, parsedRegionAddressAt, h3] at h ⊢
    obtain ⟨rfl, rfl⟩ := h
    decide

/-! ### The per-line frames -/

theorem plusTwoSuffixLine2_frame (state next : State)
    (bar1Zero : (state.peContext plusTwoPE).bar1 = 0)
    (step : plusTwoSealedMachine.step plusTwoSuffixLine2 state = some next) :
    (next.peRegisters plusTwoPE).lm1 (plusTwoLowAddress plusTwoWitnessOutput) =
      (state.peRegisters plusTwoPE).lm1 (plusTwoLowAddress plusTwoWitnessOutput) ∧
    (next.peContext plusTwoPE).bar1 = 0 :=
  plusTwoSuffixLine_frame plusTwoSuffixLine2NExpr (plusTwoIdec 9 29 13 39 5 7 29 13) rfl
    .dec .i false none rfl plusTwoSuffixLine2_plain plusTwoSuffixLine2_notFloat
    plusTwoSuffixLine2_notBAR (plusTwoIdec_barUpdates 9 29 13 39 5 7 29 13)
    plusTwoSuffixLine2_filter (plusTwoSuffixDest 5 7 29 13)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ =>
      plusTwoIdec_lowered 9 29 13 39 5 7 29 13 _ _ _ _ _ _ _ _ _ _ _ _)
    plusTwoSuffixDest_outside_5_7_29_13 state next bar1Zero step

theorem plusTwoSuffixLine3_frame (state next : State)
    (bar1Zero : (state.peContext plusTwoPE).bar1 = 0)
    (step : plusTwoSealedMachine.step plusTwoSuffixLine3 state = some next) :
    (next.peRegisters plusTwoPE).lm1 (plusTwoLowAddress plusTwoWitnessOutput) =
      (state.peRegisters plusTwoPE).lm1 (plusTwoLowAddress plusTwoWitnessOutput) ∧
    (next.peContext plusTwoPE).bar1 = 0 :=
  plusTwoSuffixLine_frame plusTwoSuffixLine3NExpr (plusTwoIdec 21 23 17 15 31 21 35 17) rfl
    .dec .i false none rfl plusTwoSuffixLine3_plain plusTwoSuffixLine3_notFloat
    plusTwoSuffixLine3_notBAR (plusTwoIdec_barUpdates 21 23 17 15 31 21 35 17)
    plusTwoSuffixLine3_filter (plusTwoSuffixDest 31 21 35 17)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ =>
      plusTwoIdec_lowered 21 23 17 15 31 21 35 17 _ _ _ _ _ _ _ _ _ _ _ _)
    plusTwoSuffixDest_outside_31_21_35_17 state next bar1Zero step

theorem plusTwoSuffixLine4_frame (state next : State)
    (bar1Zero : (state.peContext plusTwoPE).bar1 = 0)
    (step : plusTwoSealedMachine.step plusTwoSuffixLine4 state = some next) :
    (next.peRegisters plusTwoPE).lm1 (plusTwoLowAddress plusTwoWitnessOutput) =
      (state.peRegisters plusTwoPE).lm1 (plusTwoLowAddress plusTwoWitnessOutput) ∧
    (next.peContext plusTwoPE).bar1 = 0 :=
  plusTwoSuffixLine_frame plusTwoSuffixLine4NExpr (plusTwoIxor 11 7 39 27 1 1 0 2 3 1 9 25) rfl
    .xor .i false none rfl plusTwoSuffixLine4_plain plusTwoSuffixLine4_notFloat
    plusTwoSuffixLine4_notBAR (plusTwoIxor_barUpdates 11 7 39 27 1 1 0 2 3 1 9 25)
    plusTwoSuffixLine4_filter (plusTwoSuffixDest 3 1 9 25)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ =>
      plusTwoIxor_lowered 11 7 39 27 1 1 0 2 3 1 9 25 _ _ _ _ _ _ _ _ _ _ _ _)
    plusTwoSuffixDest_outside_3_1_9_25 state next bar1Zero step

theorem plusTwoSuffixLine5_frame (state next : State)
    (bar1Zero : (state.peContext plusTwoPE).bar1 = 0)
    (step : plusTwoSealedMachine.step plusTwoSuffixLine5 state = some next) :
    (next.peRegisters plusTwoPE).lm1 (plusTwoLowAddress plusTwoWitnessOutput) =
      (state.peRegisters plusTwoPE).lm1 (plusTwoLowAddress plusTwoWitnessOutput) ∧
    (next.peContext plusTwoPE).bar1 = 0 :=
  plusTwoSuffixLine_frame plusTwoSuffixLine5NExpr (plusTwoIxor 27 5 37 19 0 3 0 1 37 23 15 27) rfl
    .xor .i false none rfl plusTwoSuffixLine5_plain plusTwoSuffixLine5_notFloat
    plusTwoSuffixLine5_notBAR (plusTwoIxor_barUpdates 27 5 37 19 0 3 0 1 37 23 15 27)
    plusTwoSuffixLine5_filter (plusTwoSuffixDest 37 23 15 27)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ =>
      plusTwoIxor_lowered 27 5 37 19 0 3 0 1 37 23 15 27 _ _ _ _ _ _ _ _ _ _ _ _)
    plusTwoSuffixDest_outside_37_23_15_27 state next bar1Zero step


/-! ### The corrected suffix frame -/

theorem plusTwoSuffix_preserves_witness_of_bar1 :
    PlusTwoSuffixPreservesWitnessOfBar1Zero := by
  intro state next bar1Zero executed
  rw [plusTwoSuffix_eq] at executed
  simp only [ProofsLean.execute] at executed
  cases h2 : executeNormalizedLine plusTwoSuffixLine2.toNormalizedLine state with
  | failure => rw [h2] at executed; simp at executed
  | unknown => rw [h2] at executed; simp at executed
  | ok s1 =>
      rw [h2] at executed
      simp only [Option.bind_some] at executed
      cases h3 : executeNormalizedLine plusTwoSuffixLine3.toNormalizedLine s1 with
      | failure => rw [h3] at executed; simp at executed
      | unknown => rw [h3] at executed; simp at executed
      | ok s2 =>
          rw [h3] at executed
          simp only [Option.bind_some] at executed
          cases h4 : executeNormalizedLine plusTwoSuffixLine4.toNormalizedLine s2 with
          | failure => rw [h4] at executed; simp at executed
          | unknown => rw [h4] at executed; simp at executed
          | ok s3 =>
              rw [h4] at executed
              simp only [Option.bind_some] at executed
              cases h5 : executeNormalizedLine plusTwoSuffixLine5.toNormalizedLine s3 with
              | failure => rw [h5] at executed; simp at executed
              | unknown => rw [h5] at executed; simp at executed
              | ok s4 =>
                  rw [h5] at executed
                  simp only [Option.bind_some] at executed
                  simp only [ProofsLean.execute, Option.some.injEq] at executed
                  subst executed
                  have step2 : plusTwoSealedMachine.step plusTwoSuffixLine2 state = some s1 := by
                    simpa [plusTwoSealedMachine, h2]
                  have step3 : plusTwoSealedMachine.step plusTwoSuffixLine3 s1 = some s2 := by
                    simpa [plusTwoSealedMachine, h3]
                  have step4 : plusTwoSealedMachine.step plusTwoSuffixLine4 s2 = some s3 := by
                    simpa [plusTwoSealedMachine, h4]
                  have step5 : plusTwoSealedMachine.step plusTwoSuffixLine5 s3 = some s4 := by
                    simpa [plusTwoSealedMachine, h5]
                  have f2 := plusTwoSuffixLine2_frame state s1 bar1Zero step2
                  have f3 := plusTwoSuffixLine3_frame s1 s2 f2.2 step3
                  have f4 := plusTwoSuffixLine4_frame s2 s3 f3.2 step4
                  have f5 := plusTwoSuffixLine5_frame s3 s4 f4.2 step5
                  rw [f5.1, f4.1, f3.1, f2.1]

/-! ### The first line keeps `BAR1` -/

theorem plusTwoLine1_preserves_bar1 : PlusTwoLine1PreservesBar1Zero := by
  intro state next step
  exact plusTwoLine_step_context plusTwoLine1NExpr plusTwoLine1Expr rfl
    (by decide) (by decide) (by decide)
    (fun writes => by
      simp [parsedIntegerALUBarUpdates, plusTwoLine1Expr, plusTwoIdecWithGrf,
        plusTwoMem]) (by decide) state next step

/-! ### The refutation -/

theorem plusTwoRecorded_not_correct :
    ¬ ProofsLean.Correct plusTwoSealedMachine plusTwoSpec plusTwoRecordedAnswer :=
  plusTwoRecorded_not_correct_of_bar1Frame
    (fun state next bar1Zero executed =>
      plusTwoSuffix_preserves_witness_of_bar1 state next bar1Zero executed)
    plusTwoLine1_preserves_bar1

end ProofsLean.MNCore
