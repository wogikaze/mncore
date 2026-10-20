import ProofsLean.FrameStep

/-! # `.unknown`-freedom for the Welcome line class

The worklist target is the Welcome problem
(`problems/challenge/1.plus-one/answer.vsm`), whose two PE lines are

```text
iinc $lm0v $ln0v
iinc $lm8v $ln8v
```

`ProofsLean.MNCore.wholeMachine.step` is the hazard-aware normalized-line
executor. It may return `.unknown` where value semantics are not connected, so
`seal`/`Complete` cannot be applied to the whole machine until a line class is
proved `.unknown`-free.

This module defines that class *syntactically* on the normalized carrier and
proves, for **every** `HazardAwareState` (no reachability or forwarding
hypothesis), that

* the per-PE walk `executeIntegerProducerLineAtPEs` never returns `.unknown`,
* the line executor `executeIntegerProducerInstructionLine` never returns
  `.unknown`,
* the hazard-aware core and wrapper never return `.unknown`,
* hence `wholeMachine.step` never returns `.unknown` on the class.

The class is exactly the single-expression integer `iinc` PE line with

* opcode shape `.alu .inc (some .i) false none` (the `iinc` opcode),
* `.long` (two-word) memory width,
* one LM0 source and one LM1 destination,
* no operand mask, no flush, no wait tag, no forwarding source.

The Welcome lines are the instances at base `0` and base `8`.

What this module does **not** claim: `.unknown`-freedom for any other line
class (other opcodes, masks, forwarding sources, multiple expressions, MV/nop
lines), agreement with the Rust simulator, or correctness of the computed
values. Only the *epistemic* status of the step is settled here.
-/

namespace ProofsLean.MNCore

open Issue
open PEMemory

/-! ## The syntactic class -/

/-- Canonical normalized form of the Welcome `iinc` expression at word base
`base`: `iinc $lm<base>v $ln<base>v`.

`Issue.plusOneParsedAt` is the existing source-level definition of this line
(`ProofsLean.MNCore.Issue.plusOneParsedAt`, used by `plusOne_issue_legal` and
the `plusOne*_cycle_lowers` family); normalizing only erases the display
string. -/
def welcomeExpr (base : Nat) : NormalizedExpr :=
  (Issue.plusOneParsedAt base).normalize

theorem welcomeExpr_op (base : Nat) :
    (welcomeExpr base).op = .alu .inc (some .i) false none := rfl

theorem welcomeExpr_sources (base : Nat) :
    (welcomeExpr base).sources = [Issue.plusOneReadAt base] := rfl

theorem welcomeExpr_destinations (base : Nat) :
    (welcomeExpr base).destinations = [Issue.plusOneWriteAt base] := rfl

theorem welcomeExpr_flush (base : Nat) : (welcomeExpr base).flush = none := rfl

theorem welcomeExpr_toParsed (base : Nat) :
    (welcomeExpr base).toParsed = { Issue.plusOneParsedAt base with text := "" } := rfl

/-- The LM0 source of a Welcome line: `.long` (two word) direct access, no
mask selector, not negated/extended/rounded, no MADPE index. -/
theorem welcomeExpr_source_shape (base : Nat) :
    (welcomeExpr base).sources =
      [.mem (Issue.plusOneAccess .lm0 base) false false false none] := rfl

/-- The LM1 destination of a Welcome line: same `.long` direct shape. -/
theorem welcomeExpr_destination_shape (base : Nat) :
    (welcomeExpr base).destinations =
      [.mem (Issue.plusOneAccess .lm1 base) false false false none] := rfl

theorem welcomeExpr_source_bank (base : Nat) :
    (Issue.plusOneAccess .lm0 base).bank = .lm0 := rfl

theorem welcomeExpr_destination_bank (base : Nat) :
    (Issue.plusOneAccess .lm1 base).bank = .lm1 := rfl

theorem welcomeExpr_source_width (base : Nat) :
    (Issue.plusOneAccess .lm0 base).region.width = 2 := rfl

theorem welcomeExpr_destination_width (base : Nat) :
    (Issue.plusOneAccess .lm1 base).region.width = 2 := rfl

theorem welcomeExpr_source_not_indirect (base : Nat) :
    (Issue.plusOneAccess .lm0 base).region.tIndirect = false := rfl

theorem welcomeExpr_destination_not_indirect (base : Nat) :
    (Issue.plusOneAccess .lm1 base).region.tIndirect = false := rfl

theorem welcomeExpr_source_no_madpe (base : Nat) :
    (Issue.plusOneAccess .lm0 base).region.madpe = none := rfl

theorem welcomeExpr_destination_no_madpe (base : Nat) :
    (Issue.plusOneAccess .lm1 base).region.madpe = none := rfl

/-- The exact syntactic class of Welcome PE expressions: integer `iinc` with
`.long` width, an LM0 source, an LM1 destination, no mask, no flush. -/
def IsWelcomePEExpr (expression : NormalizedExpr) : Prop :=
  ∃ base : Nat,
    expression = welcomeExpr base ∧
    expression.op = .alu .inc (some .i) false none ∧
    expression.sources =
      [.mem (Issue.plusOneAccess .lm0 base) false false false none] ∧
    expression.destinations =
      [.mem (Issue.plusOneAccess .lm1 base) false false false none] ∧
    expression.flush = none

theorem isWelcomePEExpr_welcomeExpr (base : Nat) :
    IsWelcomePEExpr (welcomeExpr base) :=
  ⟨base, rfl, welcomeExpr_op base, welcomeExpr_source_shape base,
    welcomeExpr_destination_shape base, welcomeExpr_flush base⟩

/-- The Welcome lines themselves: the two `iinc` PE lines of
`problems/challenge/1.plus-one/answer.vsm`. -/
def IsWelcomeLine (line : InstructionLine) : Prop :=
  line = .pe [welcomeExpr 0] ∨ line = .pe [welcomeExpr 8]

theorem isWelcomeLine_pe_zero : IsWelcomeLine (.pe [welcomeExpr 0]) := Or.inl rfl

theorem isWelcomeLine_pe_eight : IsWelcomeLine (.pe [welcomeExpr 8]) := Or.inr rfl

/-- Every line of the class is a single-expression PE line, and its
normalization is the same single-expression PE line. -/
theorem isWelcomeLine_cases (line : InstructionLine) (welcome : IsWelcomeLine line) :
    line.toNormalizedLine = .pe [welcomeExpr 0] ∨
      line.toNormalizedLine = .pe [welcomeExpr 8] := by
  rcases welcome with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem isWelcomeLine_toParsed (line : InstructionLine) (welcome : IsWelcomeLine line) :
    line.toParsed = .pe [(welcomeExpr 0).toParsed] ∨
      line.toParsed = .pe [(welcomeExpr 8).toParsed] := by
  rcases welcome with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

/-! ## Shape facts consumed by the executor -/

theorem welcomeExpr_executionRequest (base : Nat) :
    (welcomeExpr base).op.executionRequest =
      .ok (.integer .word (.arith .inc false)) := by
  rw [welcomeExpr_op]
  exact Issue.integer_request_is_execution_request _ _ _
    (Issue.iinc_integer_request)

theorem welcomeExpr_integerInputCount :
    PEMemory.ParsedAluName.integerInputCount .inc = 1 := rfl

theorem welcomeExpr_plainIntegerALU (base : Nat) :
    parsedExprIsPlainIntegerALU (welcomeExpr base).toParsed = true := rfl

theorem welcomeExpr_supportedPELineProducer (base : Nat) :
    parsedExprIsSupportedPELineProducer (welcomeExpr base).toParsed = true := rfl

theorem welcomeExpr_notUnsupportedRustAlu (base : Nat) :
    parsedExprIsUnsupportedRustAlu (welcomeExpr base).toParsed = false := rfl

theorem welcomeExpr_noWaitTag (base : Nat) :
    parsedExprWaitTag? (welcomeExpr base).toParsed = none := rfl

theorem welcomeExpr_isMatrixReadStageInput (base : Nat) :
    parsedExprIsIntegerMatrixReadStageInput (welcomeExpr base).toParsed = true := rfl

theorem welcomeExpr_integerProducer (base : Nat) :
    parsedExprIsIntegerProducer (welcomeExpr base).toParsed = true := rfl

theorem welcomeExpr_notFloatMAUProducer (base : Nat) :
    parsedExprIsSupportedFloatMAUProducer (welcomeExpr base).toParsed = false := rfl

theorem welcomeExpr_notBARWriter (base : Nat) :
    parsedExprIsIntegerBARWriter (welcomeExpr base).toParsed = false := rfl

theorem welcomeExpr_noForwardProducer (base : Nat) :
    parsedExprIsNoForwardProducer (welcomeExpr base).toParsed = false := rfl

theorem welcomeExpr_noL2BMProducer (base : Nat) :
    parsedExprIsL2BMProducer (welcomeExpr base).toParsed = false := rfl

theorem welcomeExpr_noMslMsrProducer (base : Nat) :
    parsedExprIsMslMsrProducer (welcomeExpr base).toParsed = false := rfl

theorem welcomeExpr_noMatrixMAUProducer (base : Nat) :
    parsedExprIsMatrixMAUProducer (welcomeExpr base).toParsed = false := rfl

theorem welcomeExpr_noBlockFloatProducer (base : Nat) :
    parsedExprIsBlockFloatProducer (welcomeExpr base).toParsed = false := rfl

theorem welcomeExpr_noFloatReluProducer (base : Nat) :
    parsedExprIsFloatReluProducer (welcomeExpr base).toParsed = false := rfl

theorem welcomeExpr_waitPending_false (base : Nat) (state : State) :
    parsedExprWaitPending state (welcomeExpr base).toParsed = false := rfl

theorem welcomeExpr_notNoForward (base : Nat) :
    (match (welcomeExpr base).toParsed.op with | .noforward => true | _ => false) = false := rfl

/-! ## The syntactic class, bundled -/

theorem welcomeExpr_noForwardingSource (base : Nat) :
    (welcomeExpr base).sources.all (fun operand =>
      match operand with | .forward .. => false | _ => true) = true := rfl

theorem welcomeExpr_noSingleLineMask (base : Nat) :
    parsedExprHasSingleLineWriteMask (welcomeExpr base).toParsed = false := rfl

/-- Bundled syntactic characterization: the class is an integer `iinc` at
`.long` width with one LM0 source, one LM1 destination, no mask, no flush, no
wait tag and no forwarding source. -/
theorem welcomeExpr_syntactic_class (base : Nat) :
    (welcomeExpr base).op = .alu .inc (some .i) false none ∧
    (welcomeExpr base).sources =
      [.mem (Issue.plusOneAccess .lm0 base) false false false none] ∧
    (welcomeExpr base).destinations =
      [.mem (Issue.plusOneAccess .lm1 base) false false false none] ∧
    (Issue.plusOneAccess .lm0 base).region.width = 2 ∧
    (Issue.plusOneAccess .lm1 base).region.width = 2 ∧
    (welcomeExpr base).flush = none ∧
    parsedExprWaitTag? (welcomeExpr base).toParsed = none ∧
    (welcomeExpr base).sources.all (fun operand =>
      match operand with | .forward .. => false | _ => true) = true ∧
    parsedExprHasSingleLineWriteMask (welcomeExpr base).toParsed = false :=
  ⟨welcomeExpr_op base, welcomeExpr_source_shape base,
    welcomeExpr_destination_shape base, welcomeExpr_source_width base,
    welcomeExpr_destination_width base, welcomeExpr_flush base,
    welcomeExpr_noWaitTag base, welcomeExpr_noForwardingSource base,
    welcomeExpr_noSingleLineMask base⟩

theorem isWelcomePEExpr_iff (expression : NormalizedExpr) :
    IsWelcomePEExpr expression ↔ ∃ base, expression = welcomeExpr base := by
  constructor
  · rintro ⟨base, rfl, _⟩
    exact ⟨base, rfl⟩
  · rintro ⟨base, rfl⟩
    exact isWelcomePEExpr_welcomeExpr base

/-! ## Direct-memory lowering of the class

The source and the destination both lower to a `some` direct access without any
hypothesis: the bank is `lm0`/`lm1`, the width is the `.long` encoding `2`, the
access is not indirect, and there is no MADPE index. -/

theorem welcome_toDirectMemoryAccess_lm0 (base : Nat) (pe cycle : Fin 4)
    (bar0 bar1 : BitVec 12) (tWord : BitVec 32) :
    ∃ access, ParsedOperand.toDirectMemoryAccess?
        (.mem (Issue.plusOneAccess .lm0 base) false false false none)
        pe cycle bar0 bar1 tWord = some access ∧
      access.bank = .lm0 ∧ access.width = .long := by
  exact ⟨_, rfl, rfl, rfl⟩

theorem welcome_toDirectMemoryAccess_lm1 (base : Nat) (pe cycle : Fin 4)
    (bar0 bar1 : BitVec 12) (tWord : BitVec 32) :
    ∃ access, ParsedOperand.toDirectMemoryDestination?
        (.mem (Issue.plusOneAccess .lm1 base) false false false none)
        pe cycle bar0 bar1 tWord = some access ∧
      access.bank = .lm1 ∧ access.width = .long := by
  exact ⟨_, rfl, rfl, rfl⟩

theorem welcome_toParsedIntegerInput (base : Nat) (precision : IntegerALU.Precision)
    (group : Fin 4) (l2b : Fin 2) (l1b : Fin 8) (mab : Fin 16) (pe cycle : Fin 4)
    (bar0 bar1 : BitVec 12) (tWord : BitVec 32) :
    ∃ access, ParsedOperand.toParsedIntegerInput?
        (.mem (Issue.plusOneAccess .lm0 base) false false false none) precision
        group l2b l1b mab pe cycle bar0 bar1 tWord = some (.memory access false) := by
  obtain ⟨access, lowered, _, _⟩ :=
    welcome_toDirectMemoryAccess_lm0 base pe cycle bar0 bar1 tWord
  exact ⟨access, by simp [ParsedOperand.toParsedIntegerInput?, lowered]⟩

theorem welcome_resolveMemoryWriteSelection (base : Nat) (bank : PEMemory.Bank)
    (registers : Masks.RegisterFile) (cycle : Fin 4) (directive : ParsedMaskDirective)
    (hasSingleLineMask : Bool) :
    ∃ selection, ParsedOperand.resolveMemoryWriteSelection?
        (.mem (Issue.plusOneAccess .lm1 base) false false false none) bank registers
        cycle directive hasSingleLineMask = some selection := by
  unfold ParsedOperand.resolveMemoryWriteSelection?
  cases hasSingleLineMask <;> exact ⟨_, rfl⟩

/-- The Welcome expression lowers for every cycle, PE, BAR/T value and mask
configuration: one `.long` LM0 read feeding one `.long` LM1 write, with no
flush. No hypothesis is needed, because the operand carries no mask selector
and no indirect addressing. -/
theorem welcome_lowers (base : Nat) (registers : Masks.RegisterFile)
    (directive : ParsedMaskDirective) (hasSingleLineMask : Bool)
    (group : Fin 4) (l2b : Fin 2) (l1b : Fin 8) (mab : Fin 16) (pe cycle : Fin 4)
    (bar0 bar1 : BitVec 12) (tWord : BitVec 32) :
    ∃ accesses,
      ParsedExpr.toDirectMaskedIntegerAccessesInLine? (welcomeExpr base).toParsed
        registers directive hasSingleLineMask group l2b l1b mab pe cycle bar0 bar1
        tWord = some accesses ∧
      accesses.op = .alu .inc (some .i) false none ∧
      (∃ source, accesses.sourceX = .memory source false) ∧
      (∃ source, accesses.sourceY = .memory source false) ∧
      accesses.flushSelection = none := by
  simp only [welcomeExpr_toParsed, Issue.plusOneParsedAt,
    ParsedExpr.toDirectMaskedIntegerAccessesInLine?]
  have hreq : (ParsedOp.alu .inc (some .i) false none).executionRequest =
      .ok (.integer .word (.arith .inc false)) :=
    Issue.integer_request_is_execution_request _ _ _ Issue.iinc_integer_request
  split
  · rename_i precision aluOp heq
    rw [hreq] at heq
    cases heq
    cases hasSingleLineMask <;>
      simp (config := { decide := true }) [Issue.plusOneReadAt, Issue.plusOneWriteAt,
        Issue.plusOneAccess,
        ParsedOperand.toParsedIntegerInput?, ParsedOperand.toDirectMemoryAccess?,
        ParsedOperand.toDirectMemoryAccessMode?, ParsedOperand.toDirectMemoryDestination?,
        issueBankToRegisterBank, parsedWidth?, resolveFlushSelection?,
        ParsedOperand.resolveMemoryWriteSelection?]
  · rename_i other
    exfalso
    exact other .word (.arith .inc false) hreq

theorem welcomeExpr_toParsed_op (base : Nat) :
    (welcomeExpr base).toParsed.op = .alu .inc (some .i) false none := rfl

theorem welcomeExpr_toParsed_flush (base : Nat) :
    (welcomeExpr base).toParsed.flush = none := rfl

/-- An integer ALU read from direct PE memory never depends on a forwarding
slot, so it never returns `.unknown`. -/
theorem readWithForwarding_memory_never_unknown
    (files : IntegerRegisterFiles) (slots : Forwarding.Slots) (cycle : Fin 4)
    (access : DirectMemoryAccess) (rounded : Bool) :
    ParsedIntegerInput.readWithForwarding files slots cycle (.memory access rounded) ≠
      .unknown := by
  simp [ParsedIntegerInput.readWithForwarding, ParsedIntegerInput.read]

/-- The float-MAU stage is the identity (hence known) when no expression on the
line is a float MAU producer. -/
theorem executeParsedFloatMAUsAtPE_never_unknown_of_noProducer
    (readState currentFiles : IntegerRegisterFiles) (oldSlots : Forwarding.Slots)
    (context : ParsedIntegerContext) (expressions : List ParsedExpr)
    (directive : ParsedMaskDirective) (hasSingleLineMask : Bool)
    (floatEmpty : expressions.filter parsedExprIsSupportedFloatMAUProducer = []) :
    executeParsedFloatMAUsAtPE readState currentFiles oldSlots context expressions
      directive hasSingleLineMask ≠ .unknown := by
  rw [executeParsedFloatMAUsAtPE_noforward (floatEmpty := floatEmpty)]
  simp

/-! ## The per-cycle integer ALU transition -/

theorem welcome_prepareALUExprCycle_never_unknown (base : Nat)
    (files : IntegerRegisterFiles) (oldSlots nextSlots : Forwarding.Slots)
    (control : ParsedMaskExecutionControl) (hasSingleLineMask noForward reduced : Bool)
    (cycle : Fin 4) :
    prepareParsedIntegerALUExprCycle files oldSlots nextSlots (welcomeExpr base).toParsed
      control hasSingleLineMask noForward reduced cycle ≠ .unknown := by
  obtain ⟨accesses, lowered, -, ⟨source, sourceX⟩, ⟨source', sourceY⟩, -⟩ :=
    welcome_lowers base files.maskRegisters control.directive hasSingleLineMask
      control.context.group control.context.l2b control.context.l1b control.context.mab
      control.context.pe cycle control.context.bar0 control.context.bar1 control.context.tWord
  refine prepareParsedIntegerALUExprCycle_alu_never_unknown_of_resolved files oldSlots
    nextSlots (welcomeExpr base).toParsed control hasSingleLineMask noForward reduced cycle
    ⟨.inc, some .i, false, none, welcomeExpr_toParsed_op base⟩ accesses lowered ?_ ?_
  · rw [sourceX]
    exact readWithForwarding_memory_never_unknown files oldSlots cycle source false
  · rw [sourceY]
    exact readWithForwarding_memory_never_unknown files oldSlots cycle source' false

theorem welcome_prepareALUExprCycles_never_unknown (base : Nat)
    (files : IntegerRegisterFiles) (oldSlots initialOutputSlots : Forwarding.Slots)
    (control : ParsedMaskExecutionControl) (hasSingleLineMask noForward reduced : Bool) :
    prepareParsedIntegerALUExprCycles files oldSlots initialOutputSlots
      (welcomeExpr base).toParsed control hasSingleLineMask noForward reduced ≠ .unknown :=
  prepareParsedIntegerALUExprCycles_never_unknown files oldSlots initialOutputSlots
    (welcomeExpr base).toParsed control hasSingleLineMask noForward reduced
    (fun cycle _ outputSlots =>
      welcome_prepareALUExprCycle_never_unknown base files oldSlots outputSlots control
        hasSingleLineMask noForward reduced cycle)

theorem welcome_prepareMatrixReadLineExpression_never_unknown (base : Nat)
    (files : IntegerRegisterFiles) (oldSlots nextSlots : Forwarding.Slots)
    (store : ParsedMatrixReadStore) (control : ParsedMaskExecutionControl)
    (hasSingleLineMask noForward reduced : Bool) :
    prepareParsedIntegerMatrixReadLineExpression files oldSlots nextSlots store
      (welcomeExpr base).toParsed control hasSingleLineMask noForward reduced ≠ .unknown := by
  have cyclesKnown := welcome_prepareALUExprCycles_never_unknown base files oldSlots
    nextSlots control hasSingleLineMask noForward reduced
  intro h
  simp only [prepareParsedIntegerMatrixReadLineExpression,
    welcomeExpr_toParsed_op base] at h
  cases run : prepareParsedIntegerALUExprCycles files oldSlots nextSlots
      (welcomeExpr base).toParsed control hasSingleLineMask noForward reduced with
  | failure => rw [run] at h; cases h
  | unknown => exact cyclesKnown run
  | ok prepared => rw [run] at h; cases h

theorem welcome_fourCycleStep_never_unknown (base : Nat)
    (files : IntegerRegisterFiles) (slots : Forwarding.Slots)
    (store : ParsedMatrixReadStore) (control : ParsedMaskExecutionControl)
    (reduced : Bool) :
    parsedIntegerMatrixReadLineFourCycleStep files slots store
      [(welcomeExpr base).toParsed] control reduced ≠ .unknown := by
  apply parsedIntegerMatrixReadLineFourCycleStep_never_unknown
  intro expression member outputSlots
  rw [List.mem_singleton] at member
  subst member
  exact welcome_prepareMatrixReadLineExpression_never_unknown base files slots outputSlots
    store control _ _ reduced

/-! ## The per-PE walk -/

theorem welcome_filter_stageInput (base : Nat) :
    [(welcomeExpr base).toParsed].filter parsedExprIsIntegerMatrixReadStageInput =
      [(welcomeExpr base).toParsed] := by
  simp [welcomeExpr_isMatrixReadStageInput base]

theorem welcome_filter_peExpressions (base : Nat) :
    [(welcomeExpr base).toParsed].filter (fun expression =>
      !parsedExprIsL2BMProducer expression && !parsedExprIsMslMsrProducer expression &&
        !parsedExprIsMatrixMAUProducer expression &&
        !parsedExprIsBlockFloatProducer expression &&
        !parsedExprIsFloatReluProducer expression) = [(welcomeExpr base).toParsed] := by
  simp [welcomeExpr_noL2BMProducer base, welcomeExpr_noMslMsrProducer base,
    welcomeExpr_noMatrixMAUProducer base, welcomeExpr_noBlockFloatProducer base,
    welcomeExpr_noFloatReluProducer base]

theorem welcome_executeIntegerProducerLineAtPECore_never_unknown
    (base : Nat) (state : State) (pe : PEId) :
    executeIntegerProducerLineAtPECore [(welcomeExpr base).toParsed] state pe ≠ .unknown := by
  unfold executeIntegerProducerLineAtPECore
  dsimp only
  simp only [welcome_filter_stageInput base]
  split
  · intro h; cases h
  · rename_i matrixUnknown
    intro _
    exact absurd matrixUnknown (welcome_fourCycleStep_never_unknown base _ _ _ _ false)
  · split
    · intro h; cases h
    · rename_i floatUnknown
      intro _
      exact absurd floatUnknown
        (executeParsedFloatMAUsAtPE_never_unknown_of_noProducer _ _ _ _ _ _ _
          (by simp [welcomeExpr_notFloatMAUProducer base]))
    · split
      · intro h; cases h
      · rename_i forwardingUnknown
        intro _
        exact absurd forwardingUnknown
          (updateSupportedPELineForwarding_never_unknown _ _ _ _ _ _)
      · intro h; cases h

theorem welcome_executeIntegerProducerLineAtPE_never_unknown
    (base : Nat) (state : State) (pe : PEId) :
    executeIntegerProducerLineAtPE [(welcomeExpr base).toParsed] state pe ≠ .unknown := by
  simp only [executeIntegerProducerLineAtPE]
  exact welcome_executeIntegerProducerLineAtPECore_never_unknown base state pe

theorem welcome_executeIntegerProducerLineAtPEs_never_unknown
    (base : Nat) (state : State) :
    executeIntegerProducerLineAtPEs [(welcomeExpr base).toParsed] (List.finRange 4096) state ≠
      .unknown :=
  executeIntegerProducerLineAtPEs_never_unknown _ _ state
    (fun pe _ currentState =>
      welcome_executeIntegerProducerLineAtPE_never_unknown base currentState pe)

/-! ## The scored line transition -/

theorem executeNormalizedLine_pe_eq (expressions : List NormalizedExpr) (state : State) :
    executeNormalizedLine (.pe expressions) state =
      executeIntegerProducerInstructionLine (.pe expressions) state := rfl

theorem welcome_executeIntegerProducerInstructionLine_never_unknown
    (base : Nat) (state : State) :
    executeIntegerProducerInstructionLine (.pe [welcomeExpr base]) state ≠ .unknown := by
  have expressions : [(welcomeExpr base).toParsed] =
      ([welcomeExpr base].map NormalizedExpr.toParsed) := rfl
  have waits : ([(welcomeExpr base).toParsed].any (parsedExprWaitPending state)) = false := by
    simp [welcomeExpr_waitPending_false base]
  have supported : ([(welcomeExpr base).toParsed].all
      parsedExprIsSupportedPELineProducer) = true := by
    simp [welcomeExpr_supportedPELineProducer base]
  have noUnsupported : ([(welcomeExpr base).toParsed].any
      parsedExprIsUnsupportedRustAlu) = false := by
    simp [welcomeExpr_notUnsupportedRustAlu base]
  have msl : ∀ (currentState : State) (noForward hasSingleLineMask : Bool),
      executeParsedMslMsrProducers state currentState [(welcomeExpr base).toParsed]
        noForward hasSingleLineMask = .ok currentState :=
    fun currentState noForward hasSingleLineMask =>
      executeParsedMslMsrProducers_nil state currentState _ noForward hasSingleLineMask
        (by simp [welcomeExpr_noMslMsrProducer base])
  have relu : ∀ (currentState : State) (noForward hasSingleLineMask : Bool),
      executeParsedFloatReluProducers state currentState [(welcomeExpr base).toParsed]
        noForward hasSingleLineMask = .ok currentState :=
    fun currentState noForward hasSingleLineMask =>
      executeParsedFloatReluProducers_nil state currentState _ noForward hasSingleLineMask
        (by simp [welcomeExpr_noFloatReluProducer base])
  have block : ∀ (currentState : State) (noForward hasSingleLineMask : Bool),
      executeParsedBlockFloatProducer state currentState [(welcomeExpr base).toParsed]
        noForward hasSingleLineMask = .ok currentState :=
    fun currentState noForward hasSingleLineMask =>
      executeParsedBlockFloatProducer_nil state currentState _ noForward hasSingleLineMask
        (by simp [welcomeExpr_noBlockFloatProducer base])
  have matrix : ∀ (currentState : State) (noForward hasSingleLineMask : Bool),
      executeParsedMatrixMAUAndWrites state currentState [(welcomeExpr base).toParsed]
        noForward hasSingleLineMask = .ok currentState :=
    fun currentState noForward hasSingleLineMask =>
      executeParsedMatrixMAUAndWrites_id state currentState _ noForward hasSingleLineMask
        (by simp [welcomeExpr_noMatrixMAUProducer base])
        (by simp [parsedExprIsMatrixWriteProducer, welcomeExpr_toParsed, Issue.plusOneParsedAt])
  have shared : ∀ (currentState : State) (updateTurnaround : Bool),
      executeParsedSharedBlockProducers state currentState [(welcomeExpr base).toParsed]
        updateTurnaround = .ok currentState :=
    fun currentState updateTurnaround =>
      executeParsedSharedBlockProducers_integer state currentState _ updateTurnaround
        (by simp [welcomeExpr_integerProducer base])
  have l1ToPE : ∀ (currentState : State) (noForward hasSingleLineMask usePreIssueMask : Bool),
      executeParsedL1ToPEProducers state currentState [(welcomeExpr base).toParsed]
        noForward hasSingleLineMask usePreIssueMask = .ok currentState :=
    fun currentState noForward hasSingleLineMask usePreIssueMask =>
      executeParsedL1ToPEProducers_nil state currentState _ noForward hasSingleLineMask
        usePreIssueMask (by simp [parsedExprIsL1ToPEProducer, welcomeExpr_toParsed,
          Issue.plusOneParsedAt])
  have walkKnown := welcome_executeIntegerProducerLineAtPEs_never_unknown base state
  by_cases accepted : checkParsedTopLine (InstructionLine.pe [welcomeExpr base]).toParsed = true
  · simp only [executeIntegerProducerInstructionLine, accepted, Bool.not_true, ite_false,
      List.map_cons, List.map_nil, waits, supported, noUnsupported, Bool.false_eq_true]
    rw [welcome_filter_peExpressions base]
    cases walk : executeIntegerProducerLineAtPEs [(welcomeExpr base).toParsed]
        (List.finRange 4096) state with
    | unknown => exact False.elim (walkKnown walk)
    | failure => simp
    | ok next =>
        simp only [msl, relu, block, matrix, shared, l1ToPE]
        simp
  · have rejected :
        checkParsedTopLine (InstructionLine.pe [welcomeExpr base]).toParsed = false := by
      simpa using accepted
    simp [executeIntegerProducerInstructionLine, rejected]

/-! ## Address-mode validity and hazard events -/

theorem welcome_addressModesValid (base : Nat) :
    parsedNormalizedLinePEAddressModesValid (.pe [welcomeExpr base]) = true := by
  simp (config := { decide := true }) [parsedNormalizedLinePEAddressModesValid,
    NormalizedLine.toInstruction?, welcomeExpr_sources, welcomeExpr_destinations,
    Issue.plusOneReadAt, Issue.plusOneWriteAt, Issue.plusOneAccess,
    ParsedOperand.directMemoryAddressModeValid, issueBankToRegisterBank, parsedWidth?]

theorem welcome_hazardEventsSome (base : Nat) (state : HazardAwareState) :
    (parsedNormalizedLinePEHazardEvents? state.machine (.pe [welcomeExpr base])).isSome =
      true :=
  parsedNormalizedLinePEHazardEvents?_isSome_of_valid state.machine _
    (welcome_addressModesValid base)

/-- Both branches of an `if` on `StepResult` are known, so the `if` is known.
This lets the core's condition chain be discharged without casing its
(noncomputable) hazard predicates. -/
theorem stepResult_ite_ne_unknown {α : Type} {c : Prop} [Decidable c]
    {a b : StepResult α} (ha : a ≠ .unknown) (hb : b ≠ .unknown) :
    (if c then a else b) ≠ .unknown := by
  split
  · exact ha
  · exact hb

/-- A `pe` line whose hazard-event lowering is defined and whose scored
transition is known never returns `.unknown` from the hazard-aware core: the
core's only `.unknown` sites are the event lowering and the scored transition.
All remaining branches of the core are `.failure` or `.ok`. -/
theorem executeHazardAwareNormalizedLineCore_pe_never_unknown
    (expressions : List NormalizedExpr) (state : HazardAwareState)
    (hazardKnown :
      (parsedNormalizedLinePEHazardEvents? state.machine (.pe expressions)).isSome = true)
    (executed : executeNormalizedLine (.pe expressions) state.machine ≠ .unknown) :
    executeHazardAwareNormalizedLineCore (.pe expressions) state ≠ .unknown := by
  obtain ⟨events, eventsEq⟩ : ∃ events,
      parsedNormalizedLinePEHazardEvents? state.machine (.pe expressions) = some events := by
    cases h : parsedNormalizedLinePEHazardEvents? state.machine (.pe expressions) with
    | none => rw [h] at hazardKnown; cases hazardKnown
    | some events => exact ⟨events, rfl⟩
  cases run : executeNormalizedLine (.pe expressions) state.machine with
  | unknown => exact absurd run executed
  | failure =>
      simp only [executeHazardAwareNormalizedLineCore, NormalizedLine.toInstruction?,
        eventsEq, run, Id.run]
      repeat' (first | apply stepResult_ite_ne_unknown | (intro hh; cases hh))
  | ok next =>
      simp only [executeHazardAwareNormalizedLineCore, NormalizedLine.toInstruction?,
        eventsEq, run, Id.run]
      repeat' (first | apply stepResult_ite_ne_unknown | (intro hh; cases hh))

/-! ## Lifting to `wholeMachine.step` -/

theorem welcome_executeNormalizedLine_never_unknown (base : Nat) (state : State) :
    executeNormalizedLine (.pe [welcomeExpr base]) state ≠ .unknown := by
  rw [executeNormalizedLine_pe_eq]
  exact welcome_executeIntegerProducerInstructionLine_never_unknown base state

theorem welcome_noWait (base : Nat) :
    ([welcomeExpr base].findSome? fun expression =>
      parsedExprWaitTag? expression.toParsed) = none := by
  simp [welcomeExpr_noWaitTag base]

theorem welcome_core_never_unknown (base : Nat) (state : HazardAwareState) :
    executeHazardAwareNormalizedLineCore (.pe [welcomeExpr base]) state ≠ .unknown :=
  executeHazardAwareNormalizedLineCore_pe_never_unknown [welcomeExpr base] state
    (welcome_hazardEventsSome base state)
    (welcome_executeNormalizedLine_never_unknown base state.machine)

/-- The hazard-aware wrapper never returns `.unknown` for a Welcome line, for
**every** state: a stalled issue is a known failure and the line has no wait
tag, so the only remaining `.unknown` site is the core. -/
theorem welcome_wrapper_never_unknown (base : Nat) (state : HazardAwareState) :
    executeHazardAwareNormalizedLine (.pe [welcomeExpr base]) state ≠ .unknown := by
  by_cases stalled : state.stalledPEIssue = none
  · rw [executeHazardAwareNormalizedLine_pe_eq_core [welcomeExpr base] state stalled
      (welcome_noWait base)]
    exact welcome_core_never_unknown base state
  · cases h : state.stalledPEIssue with
    | none => exact absurd h stalled
    | some blocked =>
        rw [executeHazardAwareNormalizedLine_rejects_issue_while_stalled _ blocked state h]
        intro hh; cases hh

/-- The whole-machine step never returns `.unknown` on a Welcome expression. -/
theorem wholeMachine_welcome_never_unknown (base : Nat) (state : HazardAwareState) :
    wholeMachine.step (.pe [welcomeExpr base]) state ≠ .unknown := by
  show executeHazardAwareNormalizedLine (NormalizedLine.pe [welcomeExpr base]) state ≠
    .unknown
  exact welcome_wrapper_never_unknown base state

/-- Every `InstructionLine` in the expression class (any base) is `.unknown`-free. -/
theorem wholeMachine_welcomeExprLine_never_unknown (base : Nat) (line : InstructionLine)
    (lineEq : line = .pe [welcomeExpr base]) (state : HazardAwareState) :
    wholeMachine.step line state ≠ .unknown := by
  subst lineEq
  exact wholeMachine_welcome_never_unknown base state

/-- The whole-machine step never returns `.unknown` on either Welcome line. -/
theorem wholeMachine_welcomeLine_never_unknown (line : InstructionLine)
    (welcome : IsWelcomeLine line) (state : HazardAwareState) :
    wholeMachine.step line state ≠ .unknown := by
  rcases welcome with rfl | rfl
  · exact wholeMachine_welcome_never_unknown 0 state
  · exact wholeMachine_welcome_never_unknown 8 state

/-- States reachable from the Rust-simulator initial state by Welcome lines
only. The `.unknown`-freedom theorem below does not need the reachability
invariant, but this is the set named by the Phase 3 statement. -/
inductive WelcomeReachable : HazardAwareState → Prop where
  | initial : WelcomeReachable (HazardAwareState.initial rustSimulatorInitialState)
  | step {line : InstructionLine} {state next : HazardAwareState} :
      IsWelcomeLine line → WelcomeReachable state →
      wholeMachine.step line state = .ok next → WelcomeReachable next

theorem welcomeReachable_initial :
    WelcomeReachable (HazardAwareState.initial rustSimulatorInitialState) :=
  WelcomeReachable.initial

/-- Every step taken from a reachable state on a Welcome line is known: the
reachable set contains no `.unknown` transition. -/
theorem welcomeReachable_step_never_unknown (state : HazardAwareState)
    (_reachable : WelcomeReachable state) (line : InstructionLine)
    (welcome : IsWelcomeLine line) :
    wholeMachine.step line state ≠ .unknown :=
  wholeMachine_welcomeLine_never_unknown line welcome state

/-- The two executed lines of `problems/challenge/1.plus-one/answer.vsm` never
return `.unknown`, from any state. -/
theorem welcomeAnswer_lines_never_unknown (state : HazardAwareState)
    (line : InstructionLine)
    (member : line ∈ [InstructionLine.pe [welcomeExpr 0],
      InstructionLine.pe [welcomeExpr 8]]) :
    wholeMachine.step line state ≠ .unknown := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact wholeMachine_welcome_never_unknown 0 state
  · exact wholeMachine_welcome_never_unknown 8 state

end ProofsLean.MNCore
