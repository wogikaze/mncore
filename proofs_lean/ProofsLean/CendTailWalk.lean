import ProofsLean.CendFinal

/-! # `12.convert-endian` — the 4096-PE walks of the tail lines

`CendTailExec.CendTailForwardResidual` asks for the executor facts of lines 2
and 3.  `ProofsLean/CendFinal.lean` supplies the per-cycle preparation of line
2's `ibsl` row and its `fvfma` stage; this module supplies

* the per-cycle preparation of line 3's `sbsl` row,
* the per-PE core steps of lines 2 and 3,
* the 4096-PE walks, and
* the exact remaining residuals of the assembly (`CendSbslLm1Residual`,
  `CendLine1BarResidual`); `CendLine2SlotsResidual` (A) is proved.  The
  `CendTailComputationForward` construction from the two residuals is the next
  step; it is not part of this module yet.

No `sorry`, no `admit`, no `native_decide`, no new axioms.
-/

namespace ProofsLean.MNCore

open Issue
open PEMemory

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

/-! ## 1. `sbsl`: the operand lowering -/

theorem cendMauf_input (group : Fin 4) (l2b : Fin 2) (l1b : Fin 8) (mab : Fin 16)
    (pe cycle : Fin 4) (bar0 bar1 : BitVec 12) (tWord : BitVec 32) :
    ParsedOperand.toParsedIntegerInput? cendMauf .half group l2b l1b mab pe cycle
      bar0 bar1 tWord = some (.forward .mauf false) := rfl

theorem cendAluf_input_half (group : Fin 4) (l2b : Fin 2) (l1b : Fin 8) (mab : Fin 16)
    (pe cycle : Fin 4) (bar0 bar1 : BitVec 12) (tWord : BitVec 32) :
    ParsedOperand.toParsedIntegerInput? cendAluf .half group l2b l1b mab pe cycle
      bar0 bar1 tWord = some (.forward .aluf false) := rfl

/-- The LM1 destination of `$n[1,0,3,2]` at issue cycle `c`. -/
def cendSbslDestinationAccess (bar1 : BitVec 12) (cycle : Fin 4) : DirectMemoryAccess :=
  ⟨.lm1, .word,
    ⟨(bar1.toNat + (cendSbslDestination cycle).val) % 4096,
      Nat.mod_lt _ (by decide)⟩⟩

theorem cendN2103_destination (pe cycle : Fin 4) (bar0 bar1 : BitVec 12)
    (tWord : BitVec 32) :
    ParsedOperand.toDirectMemoryDestination? cendN2103 pe cycle bar0 bar1 tWord =
      some (cendSbslDestinationAccess bar1 cycle) :=
  cendN2103_access pe cycle bar0 bar1 tWord

/-- **The `sbsl` lowering**, with both sources forwarded and the permuted LM1
destination resolved. -/
theorem cendSbsl_lowered (registers : Masks.RegisterFile) (directive : ParsedMaskDirective)
    (group : Fin 4) (l2b : Fin 2) (l1b : Fin 8) (mab : Fin 16)
    (pe cycle : Fin 4) (bar0 bar1 : BitVec 12) (tWord : BitVec 32)
    (selection : PEWordSelection)
    (hselection : ParsedOperand.resolveMemoryWriteSelection? cendN2103 PEMemory.Bank.lm1
      registers cycle directive false = some selection) :
    ∃ accesses,
      ParsedExpr.toDirectMaskedIntegerAccessesInLine? cendSbslExpr.normalize.toParsed
          registers directive false group l2b l1b mab pe cycle bar0 bar1 tWord = some accesses ∧
      accesses.op = .alu .bsl (some .s) false none ∧
      accesses.sourceX = .forward .aluf false ∧
      accesses.sourceY = .forward .mauf false ∧
      accesses.destination = cendSbslDestinationAccess bar1 cycle ∧
      accesses.writeSelection = selection ∧
      accesses.flushSelection = none := by
  obtain ⟨accesses, hlowered, hx, hy, hdest, hsel, hflush⟩ :=
    toDirectMaskedIntegerAccessesInLine?_alu_binary cendSbslExpr.normalize.toParsed
      .bsl .s false none rfl .half (.shift .rotateLeft) rfl cendSbsl_inputCount
      registers directive false cendAluf cendMauf cendN2103 rfl rfl group l2b l1b mab
      pe cycle bar0 bar1 tWord (.forward .aluf false) (.forward .mauf false)
      (cendSbslDestinationAccess bar1 cycle) selection none
      (cendAluf_input_half group l2b l1b mab pe cycle bar0 bar1 tWord)
      (cendMauf_input group l2b l1b mab pe cycle bar0 bar1 tWord)
      (cendN2103_destination pe cycle bar0 bar1 tWord) hselection rfl
  refine ⟨accesses, hlowered, ?_, hx, hy, hdest, hsel, hflush⟩
  rw [toDirectMaskedIntegerAccessesInLine?_op cendSbslExpr.normalize.toParsed
    registers directive false group l2b l1b mab pe cycle bar0 bar1 tWord accesses hlowered,
    cendSbslOp]

/-! ## 2. `sbsl`: the value of one cycle -/

/-- The result bus of one `sbsl` cycle: half-precision rotate-left of the
forwarded `ibsl` bus by the forwarded MAU count. -/
def cendSbslResultBus (w : BitVec 32) : IntegerALU.Bus :=
  (IntegerALU.evaluateBus .half (.shift .rotateLeft) (cendIbslResultBus w)
    cendMauForwardBus false).value

theorem cendSbsl_readX (files : IntegerRegisterFiles)
    (slots : ProofsLean.MNCore.Forwarding.Slots) (cycle : Fin 4) (w : BitVec 32)
    (slotEq : slots .alu cycle = .known (cendIbslResultBus w)) :
    ParsedIntegerInput.readWithForwarding files slots cycle (.forward .aluf false) =
      .ok (cendIbslResultBus w) :=
  cendTailAlufRead files slots cycle _ slotEq

theorem cendSbsl_readY (files : IntegerRegisterFiles)
    (slots : ProofsLean.MNCore.Forwarding.Slots) (cycle : Fin 4)
    (slotEq : slots .mau cycle = .known cendMauForwardBus) :
    ParsedIntegerInput.readWithForwarding files slots cycle (.forward .mauf false) =
      .ok cendMauForwardBus :=
  cendTailMaufRead files slots cycle _ slotEq

theorem cendSbsl_eval (w : BitVec 32) :
    evaluateParsedIntegerAlu (.alu .bsl (some .s) false none)
      (cendIbslResultBus w) cendMauForwardBus false =
      .ok (IntegerALU.evaluateBus .half (.shift .rotateLeft) (cendIbslResultBus w)
        cendMauForwardBus false) :=
  parsed_integer_evaluation_uses_requested_semantics
    (.alu .bsl (some .s) false none) .half (.shift .rotateLeft) rfl
    (cendIbslResultBus w) cendMauForwardBus false

/-- The selection of `$n` at the initial mask state is fully enabled. -/
theorem cendN2103_selection (registers : Masks.RegisterFile)
    (directive : ParsedMaskDirective) (cycle : Fin 4)
    (directiveEq : directive = rustSimulatorInitialState.maskDirective)
    (registersEq : registers = zeroInitialPERegisterFiles.maskRegisters) :
    ParsedOperand.resolveMemoryWriteSelection? cendN2103 PEMemory.Bank.lm1
      registers cycle directive false = some ⟨BitVec.allOnes 4, true⟩ := by
  subst directiveEq
  subst registersEq
  simp [ParsedOperand.resolveMemoryWriteSelection?, cendN2103,
    resolveMemoryDirectiveSelection?, directiveTargetsBank, rustSimulatorInitialState,
    zeroInitialPERegisterFiles]

def cendSbslSelection (files : IntegerRegisterFiles) (control : ParsedMaskExecutionControl)
    (cycle : Fin 4) : PEWordSelection :=
  (resolveMemoryDirectiveSelection? control.directive PEMemory.Bank.lm1 files.maskRegisters
    cycle).getD ⟨BitVec.allOnes 4, true⟩

def cendSbslWrite (files : IntegerRegisterFiles) (control : ParsedMaskExecutionControl)
    (cycle : Fin 4) : PreparedParsedMaskedWrite :=
  ⟨some (cendSbslDestinationAccess control.context.bar1 cycle), none,
    unpackALUBus (cendSbslResultBus (cendLm0Word files.lm0 control.context.bar0 cycle)),
    cendSbslSelection files control cycle⟩



/-- **One `sbsl` cycle**, with the forwarded `$aluf`/`$mauf` slots resolved. -/
theorem cendSbsl_cycle (files : IntegerRegisterFiles)
    (oldSlots nextSlots : ProofsLean.MNCore.Forwarding.Slots)
    (control : ParsedMaskExecutionControl) (cycle : Fin 4) (w : BitVec 32)
    (aluEq : oldSlots .alu cycle = .known (cendIbslResultBus w))
    (mauEq : oldSlots .mau cycle = .known cendMauForwardBus) :
    ∃ accesses,
      ParsedExpr.toDirectMaskedIntegerAccessesInLine? cendSbslExpr.normalize.toParsed
          files.maskRegisters control.directive false control.context.group control.context.l2b
          control.context.l1b control.context.mab control.context.pe cycle control.context.bar0
          control.context.bar1 control.context.tWord = some accesses ∧
      accesses.op = .alu .bsl (some .s) false none ∧
      accesses.sourceX = .forward .aluf false ∧
      accesses.sourceY = .forward .mauf false ∧
      accesses.destination = cendSbslDestinationAccess control.context.bar1 cycle ∧
      accesses.writeSelection = cendSbslSelection files control cycle ∧
      accesses.flushSelection = none ∧
      prepareParsedIntegerALUExprCycle files oldSlots nextSlots cendSbslExpr.normalize.toParsed
        control false false false cycle =
      .ok ([⟨some (cendSbslDestinationAccess control.context.bar1 cycle), none,
          unpackALUBus (cendSbslResultBus w), cendSbslSelection files control cycle⟩],
        fun unit slotCycle =>
          if unit = .alu ∧ slotCycle = cycle then
            .known (cendSbslResultBus w)
          else nextSlots unit slotCycle) := by
  obtain ⟨accesses, hlowered, hop, hx, hy, hdest, hsel, hflush⟩ :=
    cendSbsl_lowered files.maskRegisters control.directive control.context.group
      control.context.l2b control.context.l1b control.context.mab control.context.pe cycle
      control.context.bar0 control.context.bar1 control.context.tWord
      (cendSbslSelection files control cycle) rfl
  have hwrite : prepareParsedMaskedWriteWithForwarding files oldSlots cycle accesses false =
      .ok ⟨some (cendSbslDestinationAccess control.context.bar1 cycle), none,
        unpackALUBus (cendSbslResultBus w), cendSbslSelection files control cycle⟩ := by
    unfold prepareParsedMaskedWriteWithForwarding
    rw [hx]
    try dsimp only
    rw [show ParsedIntegerInput.readWithForwarding files oldSlots cycle
        (.forward .aluf false) = .ok (cendIbslResultBus w) from
      cendSbsl_readX files oldSlots cycle w aluEq]
    try dsimp only
    rw [hy]
    try dsimp only
    rw [show ParsedIntegerInput.readWithForwarding files oldSlots cycle
        (.forward .mauf false) = .ok cendMauForwardBus from
      cendSbsl_readY files oldSlots cycle mauEq]
    try dsimp only
    rw [hop]
    try dsimp only
    rw [show evaluateParsedIntegerAlu (.alu .bsl (some .s) false none)
        (cendIbslResultBus w) cendMauForwardBus false =
        .ok (IntegerALU.evaluateBus .half (.shift .rotateLeft) (cendIbslResultBus w)
          cendMauForwardBus false) from cendSbsl_eval w]
    try dsimp only
    rw [hflush]
    try dsimp only [parsedOutputAfterFlush]
    rw [hsel, hdest]
    rfl
  have hlowered' : ParsedExpr.toDirectMaskedIntegerAccessesInLine?
      (⟨.alu .bsl (some .s) false none, [cendAluf, cendMauf], [cendN2103], none, ""⟩ : ParsedExpr)
      files.maskRegisters control.directive false control.context.group control.context.l2b
      control.context.l1b control.context.mab control.context.pe cycle control.context.bar0
      control.context.bar1 control.context.tWord = some accesses := by
    rw [← cendSbslOp]
    exact hlowered
  refine ⟨accesses, hlowered, hop, hx, hy, hdest, hsel, hflush, ?_⟩
  rw [cendSbslOp]
  unfold prepareParsedIntegerALUExprCycle
  simp only [hlowered']
  try dsimp only
  rw [hwrite]
  try dsimp only
  rw [updateParsedIntegerALUForwardingCycle_semantics]
  simp only [Bool.false_eq_true, ite_false, StepResult.ok.injEq, Prod.mk.injEq,
    List.cons.injEq, and_true]
  refine ⟨trivial, ?_⟩
  funext unit slotCycle
  by_cases h : unit = .alu ∧ slotCycle = cycle <;> simp [h, pack_unpackALUBus]

/-! ## 3. `sbsl`: four-cycle and line-level preparation -/

def cendSbslSlotAt (old : ProofsLean.MNCore.Forwarding.Slots) (files : IntegerRegisterFiles)
    (bar0 : BitVec 12) (cycle : Fin 4) : ProofsLean.MNCore.Forwarding.Slots :=
  fun unit slotCycle =>
    if unit = .alu ∧ slotCycle = cycle then
      .known (cendSbslResultBus (cendLm0Word files.lm0 bar0 cycle))
    else old unit slotCycle

def cendSbslSlots (old : ProofsLean.MNCore.Forwarding.Slots) (files : IntegerRegisterFiles)
    (bar0 : BitVec 12) : ProofsLean.MNCore.Forwarding.Slots :=
  fun unit cycle =>
    if unit = .alu then
      .known (cendSbslResultBus (cendLm0Word files.lm0 bar0 cycle))
    else old unit cycle

theorem cendSbsl_cycleAt (files : IntegerRegisterFiles)
    (oldSlots nextSlots : ProofsLean.MNCore.Forwarding.Slots)
    (control : ParsedMaskExecutionControl) (cycle : Fin 4)
    (aluEq : oldSlots .alu cycle =
      .known (cendIbslResultBus (cendLm0Word files.lm0 control.context.bar0 cycle)))
    (mauEq : oldSlots .mau cycle = .known cendMauForwardBus) :
    prepareParsedIntegerALUExprCycle files oldSlots nextSlots cendSbslExpr.normalize.toParsed
      control false false false cycle =
    .ok ([cendSbslWrite files control cycle],
      cendSbslSlotAt nextSlots files control.context.bar0 cycle) := by
  obtain ⟨accesses, hlowered, hop, hx, hy, hdest, hsel, hflush, hprep⟩ :=
    cendSbsl_cycle files oldSlots nextSlots control cycle
      (cendLm0Word files.lm0 control.context.bar0 cycle) aluEq mauEq
  rw [hprep]
  rfl

theorem cendSbsl_aluCycles (files : IntegerRegisterFiles)
    (oldSlots : ProofsLean.MNCore.Forwarding.Slots)
    (control : ParsedMaskExecutionControl)
    (aluEq : ∀ cycle : Fin 4, oldSlots .alu cycle =
      .known (cendIbslResultBus (cendLm0Word files.lm0 control.context.bar0 cycle)))
    (mauEq : ∀ cycle : Fin 4, oldSlots .mau cycle = .known cendMauForwardBus) :
    prepareParsedIntegerALUExprCycles files oldSlots oldSlots cendSbslExpr.normalize.toParsed
      control false false false =
    .ok ([cendSbslWrite files control 0, cendSbslWrite files control 1,
        cendSbslWrite files control 2, cendSbslWrite files control 3],
      cendSbslSlots oldSlots files control.context.bar0) := by
  let s1 := cendSbslSlotAt oldSlots files control.context.bar0 0
  let s2 := cendSbslSlotAt s1 files control.context.bar0 1
  let s3 := cendSbslSlotAt s2 files control.context.bar0 2
  let s4 := cendSbslSlotAt s3 files control.context.bar0 3
  have step0 : prepareParsedIntegerALUExprCycle files oldSlots oldSlots
      cendSbslExpr.normalize.toParsed control false false false 0 =
      .ok ([cendSbslWrite files control 0], s1) :=
    cendSbsl_cycleAt files oldSlots oldSlots control 0 (aluEq 0) (mauEq 0)
  have step1 : prepareParsedIntegerALUExprCycle files oldSlots s1
      cendSbslExpr.normalize.toParsed control false false false 1 =
      .ok ([cendSbslWrite files control 1], s2) :=
    cendSbsl_cycleAt files oldSlots s1 control 1 (aluEq 1) (mauEq 1)
  have step2 : prepareParsedIntegerALUExprCycle files oldSlots s2
      cendSbslExpr.normalize.toParsed control false false false 2 =
      .ok ([cendSbslWrite files control 2], s3) :=
    cendSbsl_cycleAt files oldSlots s2 control 2 (aluEq 2) (mauEq 2)
  have step3 : prepareParsedIntegerALUExprCycle files oldSlots s3
      cendSbslExpr.normalize.toParsed control false false false 3 =
      .ok ([cendSbslWrite files control 3], s4) :=
    cendSbsl_cycleAt files oldSlots s3 control 3 (aluEq 3) (mauEq 3)
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
  simp only [StepResult.ok.injEq, Prod.mk.injEq]
  refine ⟨by simp, ?_⟩
  funext unit cycle
  have hc : cycle = 0 ∨ cycle = 1 ∨ cycle = 2 ∨ cycle = 3 := cendCycle_cases cycle
  rcases hc with rfl | rfl | rfl | rfl <;>
    (by_cases hu : unit = .alu <;> simp [s1, s2, s3, s4, cendSbslSlotAt, cendSbslSlots, hu])

theorem cendSbsl_lineCycles (files : IntegerRegisterFiles)
    (oldSlots : ProofsLean.MNCore.Forwarding.Slots) (store : ParsedMatrixReadStore)
    (control : ParsedMaskExecutionControl)
    (aluEq : ∀ cycle : Fin 4, oldSlots .alu cycle =
      .known (cendIbslResultBus (cendLm0Word files.lm0 control.context.bar0 cycle)))
    (mauEq : ∀ cycle : Fin 4, oldSlots .mau cycle = .known cendMauForwardBus) :
    prepareParsedIntegerMatrixReadLineCycles files oldSlots store
        [cendSbslExpr.normalize.toParsed] control false =
      .ok ([cendSbslWrite files control 0, cendSbslWrite files control 1,
        cendSbslWrite files control 2, cendSbslWrite files control 3],
        cendSbslSlots oldSlots files control.context.bar0, []) := by
  have hMask : ([cendSbslExpr.normalize.toParsed].any parsedExprHasSingleLineWriteMask) = false := by
    decide
  have hNoForward : ([cendSbslExpr.normalize.toParsed].any (fun expression =>
      match expression.op with
      | .noforward => true
      | _ => false)) = false := by decide
  unfold prepareParsedIntegerMatrixReadLineCycles
  dsimp only
  simp only [hMask, hNoForward]
  refine prepareParsedIntegerMatrixReadLineExpressions_singleton files oldSlots store
    cendSbslExpr.normalize.toParsed control false false false
    [cendSbslWrite files control 0, cendSbslWrite files control 1,
      cendSbslWrite files control 2, cendSbslWrite files control 3]
    (cendSbslSlots oldSlots files control.context.bar0) [] ?_
  have hcycles : prepareParsedIntegerALUExprCycles files oldSlots oldSlots
      cendSbslExpr.normalize.toParsed control false false false =
      .ok ([cendSbslWrite files control 0, cendSbslWrite files control 1,
        cendSbslWrite files control 2, cendSbslWrite files control 3],
        cendSbslSlots oldSlots files control.context.bar0) :=
    cendSbsl_aluCycles files oldSlots control aluEq mauEq
  have hcycles' : prepareParsedIntegerALUExprCycles files oldSlots oldSlots
      (⟨.alu .bsl (some .s) false none, [cendAluf, cendMauf], [cendN2103], none, ""⟩ : ParsedExpr)
      control false false false =
      .ok ([cendSbslWrite files control 0, cendSbslWrite files control 1,
        cendSbslWrite files control 2, cendSbslWrite files control 3],
        cendSbslSlots oldSlots files control.context.bar0) := by
    rw [← cendSbslOp]
    exact hcycles
  unfold prepareParsedIntegerMatrixReadLineExpression
  rw [cendSbslOp]
  dsimp only
  rw [hcycles']
  dsimp only
  rw [show parsedIntegerALUBarUpdates
      (⟨.alu .bsl (some .s) false none, [cendAluf, cendMauf], [cendN2103], none, ""⟩ : ParsedExpr)
      [cendSbslWrite files control 0, cendSbslWrite files control 1,
        cendSbslWrite files control 2, cendSbslWrite files control 3] = [] from by
    simp [parsedIntegerALUBarUpdates, cendN2103]]

/-! ## 4. Line 2: the per-PE core step -/

/-- The control record `executeIntegerProducerLineAtPECore` builds at `pe`. -/
def cendTailControl (state : State) (pe : PEId) : ParsedMaskExecutionControl :=
  { directive := state.maskDirective,
    context :=
      { (ParsedIntegerContext.ofLinearIndex pe) with
        bar0 := (state.peContext pe).bar0,
        bar1 := (state.peContext pe).bar1,
        tWord := (state.peContext pe).tWord },
    elapsedWords := state.hazardClock }

theorem cendTailControl_eq (state : State) (pe : PEId) :
    cendTailControl state pe =
      { directive := state.maskDirective,
        context :=
          { (ParsedIntegerContext.ofLinearIndex pe) with
            bar0 := (state.peContext pe).bar0,
            bar1 := (state.peContext pe).bar1,
            tWord := (state.peContext pe).tWord },
        elapsedWords := state.hazardClock } := rfl

/-- The four `ibsl` writes of line 2 at a control record. -/
def cendIbslWrites (files : IntegerRegisterFiles) (control : ParsedMaskExecutionControl) :
    List PreparedParsedMaskedWrite :=
  [cendIbslWrite files control 0, cendIbslWrite files control 1,
    cendIbslWrite files control 2, cendIbslWrite files control 3]

theorem cendIbslWrites_eq (files : IntegerRegisterFiles)
    (control : ParsedMaskExecutionControl) :
    cendIbslWrites files control =
      [cendIbslWrite files control 0, cendIbslWrite files control 1,
        cendIbslWrite files control 2, cendIbslWrite files control 3] := rfl

theorem cendIbslWrites_lm0 (files : IntegerRegisterFiles)
    (control : ParsedMaskExecutionControl) :
    (commitParsedMaskedWrites files (cendIbslWrites files control)).lm0 = files.lm0 := by
  refine commitParsedMaskedWrites_lm0_preserves files _ ?_
  intro write mem
  have hmem : write = cendIbslWrite files control 0 ∨ write = cendIbslWrite files control 1 ∨
      write = cendIbslWrite files control 2 ∨ write = cendIbslWrite files control 3 := by
    simpa [cendIbslWrites] using mem
  rcases hmem with rfl | rfl | rfl | rfl
  · refine ⟨rfl, ?_⟩
    intro destination hd
    simp [cendIbslWrite, cendIbslDestination] at hd
    subst hd
    decide
  · refine ⟨rfl, ?_⟩
    intro destination hd
    simp [cendIbslWrite, cendIbslDestination] at hd
    subst hd
    decide
  · refine ⟨rfl, ?_⟩
    intro destination hd
    simp [cendIbslWrite, cendIbslDestination] at hd
    subst hd
    decide
  · refine ⟨rfl, ?_⟩
    intro destination hd
    simp [cendIbslWrite, cendIbslDestination] at hd
    subst hd
    decide

theorem cendIbsl_stageFilter :
    ([cendIbslExpr.normalize.toParsed, cendFmaExpr.normalize.toParsed].filter
      parsedExprIsIntegerMatrixReadStageInput) = [cendIbslExpr.normalize.toParsed] := by
  decide

/-- **Line 2's per-PE core step**, with the post-state's PE-local fields. -/
@[simp] theorem cendIbsl_notNoForward :
    (match cendIbslExpr.normalize.toParsed.op with
      | .noforward => true
      | _ => false) = false := by decide

@[simp] theorem cendFma_notNoForward :
    (match cendFmaExpr.normalize.toParsed.op with
      | .noforward => true
      | _ => false) = false := by decide

@[simp] theorem cendIbsl_isIntegerProducer :
    parsedExprIsIntegerProducer cendIbslExpr.normalize.toParsed = true := by decide

@[simp] theorem cendFma_isIntegerProducer :
    parsedExprIsIntegerProducer cendFmaExpr.normalize.toParsed = false := by decide

@[simp] theorem cendIbsl_notMatrixRead :
    parsedExprIsMatrixReadProducer cendIbslExpr.normalize.toParsed = false := by decide

@[simp] theorem cendFma_notMatrixRead :
    parsedExprIsMatrixReadProducer cendFmaExpr.normalize.toParsed = false := by decide

@[simp] theorem cendIbsl_notBAR0 :
    parsedFloatMAUWritesBAR false cendIbslExpr.normalize.toParsed = false := by decide

@[simp] theorem cendFma_notBAR0 :
    parsedFloatMAUWritesBAR false cendFmaExpr.normalize.toParsed = false := by decide

@[simp] theorem cendIbsl_notBAR1 :
    parsedFloatMAUWritesBAR true cendIbslExpr.normalize.toParsed = false := by decide

@[simp] theorem cendFma_notBAR1 :
    parsedFloatMAUWritesBAR true cendFmaExpr.normalize.toParsed = false := by decide

theorem cendParallel_noForward :
    ([cendIbslExpr.normalize.toParsed, cendFmaExpr.normalize.toParsed].any
      (fun expression =>
        match expression.op with
        | .noforward => true
        | _ => false)) = false := by
  decide

theorem cendParallel_hasALU :
    ([cendIbslExpr.normalize.toParsed, cendFmaExpr.normalize.toParsed].any
      parsedExprIsIntegerProducer) = true := by
  decide

theorem cendParallel_hasMatrixRead :
    ([cendIbslExpr.normalize.toParsed, cendFmaExpr.normalize.toParsed].any
      parsedExprIsMatrixReadProducer) = false := by
  decide

theorem cendParallel_noBAR0 :
    ([cendIbslExpr.normalize.toParsed, cendFmaExpr.normalize.toParsed].any
      (parsedFloatMAUWritesBAR false)) = false := by
  decide

theorem cendParallel_noBAR1 :
    ([cendIbslExpr.normalize.toParsed, cendFmaExpr.normalize.toParsed].any
      (parsedFloatMAUWritesBAR true)) = false := by
  decide

theorem cendLine2_pecore_ok (state : State) (pe : PEId) (files : IntegerRegisterFiles)
    (filesEq : state.peRegisters pe = files)
    (aluEq : ∀ cycle : Fin 4,
      stateForwardingSlots state pe .alu cycle = .known cendImmediateBus) :
    ∃ next : State,
      executeIntegerProducerLineAtPECore
        [cendIbslExpr.normalize.toParsed, cendFmaExpr.normalize.toParsed] state pe = .ok next := by
  unfold executeIntegerProducerLineAtPECore
  dsimp only
  rw [filesEq]
  rw [cendIbsl_stageFilter]
  simp only [← cendTailControl_eq]
  unfold parsedIntegerMatrixReadLineFourCycleStep
  rw [cendIbsl_lineCycles files (stateForwardingSlots state pe)
    (state.matrixRegisters (ParsedIntegerContext.ofLinearIndex pe).group
      (ParsedIntegerContext.ofLinearIndex pe).l2b
      (ParsedIntegerContext.ofLinearIndex pe).l1b)
    (cendTailControl state pe) aluEq]
  dsimp only
  simp only [← cendIbslWrites_eq]
  obtain ⟨nextFiles, hfma, _⟩ :=
    cendFma_stage files
      (commitParsedMaskedWrites files (cendIbslWrites files (cendTailControl state pe)))
      (stateForwardingSlots state pe)
      { (ParsedIntegerContext.ofLinearIndex pe) with
        bar0 := (state.peContext pe).bar0,
        bar1 := (state.peContext pe).bar1,
        tWord := (state.peContext pe).tWord }
      (state.maskDirective) aluEq
  rw [hfma]
  dsimp only
  rw [updateSupportedPELineForwarding_eq]
  exact ⟨_, rfl⟩

/-! ## 14. E1: line 1's BAR context is unchanged -/

theorem cendImm_notBARWriter :
    parsedExprIsIntegerBARWriter cendImmExpr.normalize.toParsed = false := by
  rw [cendImmParsed_eq]
  rfl

theorem cendImm_stageFilter :
    [cendImmExpr.normalize.toParsed].filter parsedExprIsIntegerMatrixReadStageInput =
      [cendImmExpr.normalize.toParsed] := by
  simp [cendImm_stageInput]

theorem cendImm_notFloatMAU :
    [cendImmExpr.normalize.toParsed].filter parsedExprIsSupportedFloatMAUProducer = [] := by
  simp [cendImm_notFloat]

theorem cendImm_noFloatBAR :
    ([cendImmExpr.normalize.toParsed].any (parsedFloatMAUWritesBAR false)) = false ∧
    ([cendImmExpr.normalize.toParsed].any (parsedFloatMAUWritesBAR true)) = false := by
  constructor <;> rw [cendImmParsed_eq] <;> decide

theorem cendImm_pecore_context (input : BitVec 64) (state : State) (pe : PEId)
    (filesEq : state.peRegisters pe = cendInitialPERegisters input)
    (validEq : ∀ (unit : ProofsLean.MNCore.Forwarding.Unit) (cycle : Fin 4),
      state.forwardingValid pe unit cycle = false)
    (contextEq : state.peContext pe = ParsedIntegerContext.ofLinearIndex pe)
    (directiveEq : state.maskDirective = rustSimulatorInitialState.maskDirective) :
    ∃ next : State,
      executeIntegerProducerLineAtPECore [cendImmExpr.normalize.toParsed] state pe = .ok next ∧
      next.peContext pe = state.peContext pe := by
  unfold executeIntegerProducerLineAtPECore
  dsimp only
  rw [filesEq]
  rw [cendImm_stageFilter]
  rw [directiveEq]
  unfold parsedIntegerMatrixReadLineFourCycleStep
  rw [cendImm_lineCycles_any (cendInitialPERegisters input)
    (stateForwardingSlots state pe)
    (state.matrixRegisters (ParsedIntegerContext.ofLinearIndex pe).group
      (ParsedIntegerContext.ofLinearIndex pe).l2b
      (ParsedIntegerContext.ofLinearIndex pe).l1b)
    { directive := rustSimulatorInitialState.maskDirective
      context :=
        { (ParsedIntegerContext.ofLinearIndex pe) with
          bar0 := (state.peContext pe).bar0,
          bar1 := (state.peContext pe).bar1,
          tWord := (state.peContext pe).tWord }
      elapsedWords := state.hazardClock } rfl rfl]
  dsimp only
  rw [executeParsedFloatMAUsAtPE_empty _ _ _ _ _ _ _ cendImm_notFloatMAU]
  dsimp only
  rw [updateSupportedPELineForwarding_eq]
  dsimp only
  refine ⟨_, rfl, ?_⟩
  simp [cendImm_noFloatBAR.1, cendImm_noFloatBAR.2]

theorem cendLine1_executeAtPE_context (input : BitVec 64) (state : State) (pe : PEId)
    (filesEq : state.peRegisters pe = cendInitialPERegisters input)
    (validEq : ∀ (unit : ProofsLean.MNCore.Forwarding.Unit) (cycle : Fin 4),
      state.forwardingValid pe unit cycle = false)
    (contextEq : state.peContext pe = ParsedIntegerContext.ofLinearIndex pe)
    (directiveEq : state.maskDirective = rustSimulatorInitialState.maskDirective) :
    ∃ next : State,
      executeIntegerProducerLineAtPE [cendImmExpr.normalize.toParsed] state pe = .ok next ∧
      next.peContext pe = state.peContext pe := by
  obtain ⟨next, executed, context⟩ :=
    cendImm_pecore_context input state pe filesEq validEq contextEq directiveEq
  obtain ⟨next', executed', _⟩ :=
    cendImm_pecore input state pe filesEq validEq contextEq directiveEq
  rw [executed] at executed'
  have same : next = next' := StepResult.ok.inj executed'
  refine ⟨next, ?_, context⟩
  simpa [executeIntegerProducerLineAtPE, cendImm_notBARWriter] using executed

/-! ## 5. Line 1: every PE's `.alu` slot after the walk -/

/-- Line 1's per-PE step, with the installed `.alu` slots and validity. -/
theorem cendLine1_executeAtPE_slots (input : BitVec 64) (state : State) (pe : PEId)
    (filesEq : state.peRegisters pe = cendInitialPERegisters input)
    (validEq : ∀ (unit : ProofsLean.MNCore.Forwarding.Unit) (cycle : Fin 4),
      state.forwardingValid pe unit cycle = false)
    (contextEq : state.peContext pe = ParsedIntegerContext.ofLinearIndex pe)
    (directiveEq : state.maskDirective = rustSimulatorInitialState.maskDirective) :
    ∃ next : State,
      executeIntegerProducerLineAtPE [cendImmExpr.normalize.toParsed] state pe = .ok next ∧
      next.peRegisters pe = cendLine1Files input ∧
      (∀ cycle : Fin 4,
        stateForwardingSlots next pe .alu cycle = .known cendImmediateBus) ∧
      (∀ cycle : Fin 4, next.forwardingValid pe .alu cycle = true) ∧
      next.peContext pe = state.peContext pe := by
  obtain ⟨next, executed, slots, valid⟩ :=
    cendImm_pecore_slots input state pe filesEq validEq contextEq directiveEq
  obtain ⟨next', executed', committed⟩ :=
    cendImm_pecore input state pe filesEq validEq contextEq directiveEq
  obtain ⟨nextCtx, executedCtx, context⟩ :=
    cendImm_pecore_context input state pe filesEq validEq contextEq directiveEq
  rw [executed] at executed'
  rw [executed] at executedCtx
  have same : next = next' := StepResult.ok.inj executed'
  have sameCtx : nextCtx = next := (StepResult.ok.inj executedCtx).symm
  rw [sameCtx] at context
  refine ⟨next, ?_, ?_, slots, valid, context⟩
  · simpa [executeIntegerProducerLineAtPE, cendImm_notBARWriter] using executed
  · simpa [same, cendLine1Files] using committed

/-- The line-1 walk invariant extended with the `.alu` slots of visited PEs. -/
structure CendLine1SlotsInvariant (input : BitVec 64) (pending : List PEId)
    (state : State) : Prop where
  base : CendLine1WalkInvariant input pending state
  slotsDone : ∀ pe : PEId, pe ∉ pending → ∀ cycle : Fin 4,
    stateForwardingSlots state pe .alu cycle = .known cendImmediateBus
  contextDone : ∀ pe : PEId, pe ∉ pending →
    state.peContext pe = ParsedIntegerContext.ofLinearIndex pe

theorem cendLine1SlotsInvariant_initial (input : BitVec 64) :
    CendLine1SlotsInvariant input (List.finRange 4096) (cendInitialState input) where
  base := cendLine1WalkInvariant_initial input
  slotsDone := fun pe absent => absurd (List.mem_finRange pe) absent
  contextDone := fun pe absent => absurd (List.mem_finRange pe) absent

theorem executeIntegerProducerLineAtPEs_cendLine1_walk_slots
    (input : BitVec 64) (pending : List PEId) (state : State)
    (nodup : pending.Nodup)
    (inv : CendLine1SlotsInvariant input pending state) :
    ∃ next : State,
      executeIntegerProducerLineAtPEs [cendImmExpr.normalize.toParsed] pending state = .ok next ∧
      CendLine1SlotsInvariant input [] next := by
  induction pending generalizing state with
  | nil =>
      refine ⟨state, by simp [executeIntegerProducerLineAtPEs], ?_⟩
      refine ⟨?_, ?_, ?_⟩
      · exact
          { filesPending := fun pe mem => by simp at mem
            filesDone := fun pe _ => inv.base.filesDone pe (by simp)
            validPending := fun pe mem => by simp at mem
            contextPending := fun pe mem => by simp at mem
            directive := inv.base.directive }
      · intro pe _ cycle
        exact inv.slotsDone pe (by simp) cycle
      · intro pe _
        exact inv.contextDone pe (by simp)
  | cons pe rest ih =>
      obtain ⟨peNotRest, restNodup⟩ := List.nodup_cons.mp nodup
      have peMem : pe ∈ pe :: rest := by simp
      obtain ⟨middle, headExecuted, headFiles, headSlots, _headValid, headContext⟩ :=
        cendLine1_executeAtPE_slots input state pe
          (inv.base.filesPending pe peMem) (inv.base.validPending pe peMem)
          (inv.base.contextPending pe peMem) inv.base.directive
      have middleBase : CendLine1WalkInvariant input rest middle := by
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
          exact inv.base.filesPending q (List.mem_cons_of_mem pe mem)
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
            exact inv.base.filesDone q notMemCons
        · intro q mem unit cycle
          have different : q ≠ pe := fun same => peNotRest (same ▸ mem)
          have frame := executeIntegerProducerLineAtPE_peFields_other
            [cendImmExpr.normalize.toParsed] state middle pe q different headExecuted
          rw [frame.2.2.1]
          exact inv.base.validPending q (List.mem_cons_of_mem pe mem) unit cycle
        · intro q mem
          have different : q ≠ pe := fun same => peNotRest (same ▸ mem)
          have frame := executeIntegerProducerLineAtPE_peFields_other
            [cendImmExpr.normalize.toParsed] state middle pe q different headExecuted
          rw [frame.2.2.2]
          exact inv.base.contextPending q (List.mem_cons_of_mem pe mem)
        · exact (executeIntegerProducerLineAtPE_maskDirective_hazardClock
            [cendImmExpr.normalize.toParsed] state middle pe headExecuted).1.trans
            inv.base.directive
      have middleSlots : CendLine1SlotsInvariant input rest middle := by
        refine ⟨middleBase, ?_, ?_⟩
        · intro q notMemRest cycle
          by_cases same : q = pe
          · subst same
            exact headSlots cycle
          · have notMemCons : q ∉ pe :: rest := by
              intro member
              rcases List.mem_cons.mp member with head | tail
              · exact same head
              · exact notMemRest tail
            have frame := executeIntegerProducerLineAtPE_peFields_other
              [cendImmExpr.normalize.toParsed] state middle pe q same headExecuted
            simp only [stateForwardingSlots]
            rw [frame.2.2.1, frame.2.1]
            exact inv.slotsDone q notMemCons cycle
        · intro q notMemRest
          by_cases same : q = pe
          · subst same
            rw [headContext]
            exact inv.base.contextPending q peMem
          · have notMemCons : q ∉ pe :: rest := by
              intro member
              rcases List.mem_cons.mp member with head | tail
              · exact same head
              · exact notMemRest tail
            have frame := executeIntegerProducerLineAtPE_peFields_other
              [cendImmExpr.normalize.toParsed] state middle pe q same headExecuted
            exact (frame.2.2.2).trans (inv.contextDone q notMemCons)
      obtain ⟨next, tailExecuted, tailInv⟩ := ih middle restNodup middleSlots
      refine ⟨next, ?_, tailInv⟩
      have unfoldEq : executeIntegerProducerLineAtPEs [cendImmExpr.normalize.toParsed]
          (pe :: rest) state =
          executeIntegerProducerLineAtPEs [cendImmExpr.normalize.toParsed] rest middle := by
        conv_lhs => unfold executeIntegerProducerLineAtPEs
        rw [headExecuted]
      rw [unfoldEq]
      exact tailExecuted

/-- **After line 1, every PE's `.alu` slot is the immediate bus.** -/
theorem cendLine1_allPE_slots (input : BitVec 64) :
    ∃ next : State,
      executeNormalizedLine (.pe [cendImmExpr.normalize]) (cendInitialState input) = .ok next ∧
      (∀ pe : PEId, ∀ cycle : Fin 4,
        stateForwardingSlots next pe .alu cycle = .known cendImmediateBus) ∧
      (∀ pe : PEId, next.peContext pe = ParsedIntegerContext.ofLinearIndex pe) := by
  obtain ⟨nextPEs, walkExecuted, _, lineExecuted⟩ := cendLine1_walk_and_execute input
  obtain ⟨nextPEs', walkExecuted', slotsInv⟩ :=
    executeIntegerProducerLineAtPEs_cendLine1_walk_slots input (List.finRange 4096)
      (cendInitialState input) (List.nodup_finRange 4096)
      (cendLine1SlotsInvariant_initial input)
  have same : nextPEs = nextPEs' :=
    StepResult.ok.inj (walkExecuted.symm.trans walkExecuted')
  rw [same] at lineExecuted
  let next : State := { nextPEs' with
      hazardClock := nextPEs'.hazardClock + InstructionLine.cost (.pe [cendImmExpr.normalize]),
      l1bmTurnaroundValid := false }
  refine ⟨next, lineExecuted, ?_, ?_⟩
  · intro pe cycle
    exact slotsInv.slotsDone pe (by simp) cycle
  · intro pe
    exact slotsInv.contextDone pe (by simp)

/-! ## 6. A generic walk for a local predicate -/

/-- **A 4096-PE walk succeeds whenever the predicate is local and every PE
satisfying it steps successfully.**  `P` only has to be preserved by a step at
another PE (the frame), exactly what `executeIntegerProducerLineAtPE` provides
for the register-file / forwarding fields. -/
theorem cendWalk_of_local (expressions : List ParsedExpr) (P : State → PEId → Prop)
    (step : ∀ (current : State) (pe : PEId), P current pe →
      ∃ next, executeIntegerProducerLineAtPE expressions current pe = .ok next)
    (frame : ∀ (state middle : State) (pe q : PEId), q ≠ pe →
      executeIntegerProducerLineAtPE expressions state pe = .ok middle →
      P state q → P middle q)
    (pes : List PEId) (nodup : pes.Nodup) (state : State)
    (inv : ∀ pe, pe ∈ pes → P state pe) :
    ∃ next, executeIntegerProducerLineAtPEs expressions pes state = .ok next := by
  induction pes generalizing state with
  | nil => exact ⟨state, by simp [executeIntegerProducerLineAtPEs]⟩
  | cons pe rest ih =>
      obtain ⟨peNotRest, restNodup⟩ := List.nodup_cons.mp nodup
      obtain ⟨middle, headExecuted⟩ := step state pe (inv pe (by simp))
      have restInv : ∀ q, q ∈ rest → P middle q := by
        intro q mem
        exact frame state middle pe q (by
          intro same
          subst same
          exact peNotRest mem) headExecuted (inv q (List.mem_cons_of_mem pe mem))
      obtain ⟨next, tailExecuted⟩ := ih restNodup middle restInv
      refine ⟨next, ?_⟩
      simp only [executeIntegerProducerLineAtPEs]
      rw [headExecuted]
      exact tailExecuted

/-- Line 1's result carries both the committed files and the immediate `.alu`
bus at *every* PE. -/
theorem cendLine1_next_allPE (input : BitVec 64) :
    ∃ next : State,
      executeNormalizedLine (.pe [cendImmExpr.normalize]) (cendInitialState input) = .ok next ∧
      (∀ pe : PEId, next.peRegisters pe = cendLine1Files input) ∧
      (∀ pe : PEId, ∀ cycle : Fin 4,
        stateForwardingSlots next pe .alu cycle = .known cendImmediateBus) := by
  obtain ⟨next, executed, slots, _context⟩ := cendLine1_allPE_slots input
  obtain ⟨next2, executed2, filesAll, _, _, _, _, _, _⟩ := cendLine1_next input
  rw [executed] at executed2
  have same : next = next2 := StepResult.ok.inj executed2
  rw [same] at executed
  refine ⟨next2, executed, filesAll, ?_⟩
  intro pe cycle
  rw [← same]
  exact slots pe cycle

/-! ## 7. Line 2's 4096-PE walk -/

/-- The per-PE precondition of line 2: the line-1 committed file and the
immediate `.alu` bus at every cycle. -/
def CendIbslReady (files : IntegerRegisterFiles) (state : State) (pe : PEId) : Prop :=
  state.peRegisters pe = files ∧
    ∀ cycle : Fin 4, stateForwardingSlots state pe .alu cycle = .known cendImmediateBus

theorem cendLine2_walk (input : BitVec 64) (s1 : State)
    (executed : executeNormalizedLine (.pe [cendImmExpr.normalize])
      (cendInitialState input) = .ok s1) :
    ∃ afterTwo : State,
      executeIntegerProducerLineAtPEs
        [cendIbslExpr.normalize.toParsed, cendFmaExpr.normalize.toParsed]
        (List.finRange 4096) s1 = .ok afterTwo := by
  obtain ⟨next, executedNext, filesAll, slotsAll⟩ := cendLine1_next_allPE input
  rw [executedNext] at executed
  have same : s1 = next := (StepResult.ok.inj executed).symm
  rw [same]
  refine cendWalk_of_local
    [cendIbslExpr.normalize.toParsed, cendFmaExpr.normalize.toParsed]
    (CendIbslReady (cendLine1Files input)) ?_ ?_ (List.finRange 4096)
    (List.nodup_finRange 4096) next ?_
  · intro current pe ready
    exact cendLine2_pecore_ok current pe (cendLine1Files input) ready.1 ready.2
  · intro state middle pe q different head ready
    have frame := executeIntegerProducerLineAtPE_peFields_other
      [cendIbslExpr.normalize.toParsed, cendFmaExpr.normalize.toParsed] state middle pe q
      different head
    refine ⟨?_, ?_⟩
    · rw [frame.1]
      exact ready.1
    · intro cycle
      simp only [stateForwardingSlots]
      rw [frame.2.2.1, frame.2.1]
      exact ready.2 cycle
  · intro pe _
    exact ⟨filesAll pe, slotsAll pe⟩

/-! ## 8. Line 3: the LM1 commit of the four `sbsl` writes -/

theorem cendSbslSelection_full (files : IntegerRegisterFiles)
    (control : ParsedMaskExecutionControl) (cycle : Fin 4)
    (directiveEq : control.directive = rustSimulatorInitialState.maskDirective) :
    cendSbslSelection files control cycle = ⟨BitVec.allOnes 4, true⟩ := by
  simp [cendSbslSelection, directiveEq, resolveMemoryDirectiveSelection?,
    directiveTargetsBank, rustSimulatorInitialState]

theorem cendSbslWrite_maskUpdate (files : IntegerRegisterFiles)
    (control : ParsedMaskExecutionControl) (cycle : Fin 4) :
    (cendSbslWrite files control cycle).maskUpdate = none := rfl

theorem cendSbslWrite_data_zero (files : IntegerRegisterFiles)
    (control : ParsedMaskExecutionControl) (cycle : Fin 4) :
    (cendSbslWrite files control cycle).data 0 =
      byteSwap32 (cendLm0Word files.lm0 control.context.bar0 cycle) :=
  cendSbslData_forward _

def cendSbslMemory (files : IntegerRegisterFiles)
    (control : ParsedMaskExecutionControl) (cycle : Fin 4) : PEMemory.Memory .lm1 :=
  PEMemory.writeWords .lm1 .word files.lm1
    (cendSbslDestinationAccess control.context.bar1 cycle).address
    (cendSbslWrite files control cycle).data

def cendSbslMemoryState (stateFiles files : IntegerRegisterFiles)
    (control : ParsedMaskExecutionControl) (cycle : Fin 4) : PEMemory.Memory .lm1 :=
  PEMemory.writeWords .lm1 .word stateFiles.lm1
    (cendSbslDestinationAccess control.context.bar1 cycle).address
    (cendSbslWrite files control cycle).data

theorem cendSbslCommitStep (stateFiles files : IntegerRegisterFiles)
    (control : ParsedMaskExecutionControl) (cycle : Fin 4)
    (selEq : cendSbslSelection files control cycle = ⟨BitVec.allOnes 4, true⟩) :
    welcomeCommitStep stateFiles (cendSbslWrite files control cycle) =
      { stateFiles with lm1 := cendSbslMemoryState stateFiles files control cycle } := by
  unfold welcomeCommitStep cendSbslMemoryState
  simp only [cendSbslWrite_maskUpdate, cendSbslWrite]
  unfold writeDirectAccessMasked writeRegisterBankMasked
  rw [selEq]
  simp only [writeWordsMasked_allOnes]
  rfl

theorem writeWords_word_congr_zero (memory : PEMemory.Memory .lm1)
    (start : Fin PEMemory.Bank.lm1.capacity) (data1 data2 : PEMemory.WordBus)
    (h : data1 0 = data2 0) :
    PEMemory.writeWords .lm1 .word memory start data1 =
      PEMemory.writeWords .lm1 .word memory start data2 := by
  funext target
  by_cases within : PEMemory.distance .lm1 start target < PEMemory.count .lm1 .word
  · have hcount : PEMemory.count .lm1 .word = 1 := rfl
    have hzero : PEMemory.distance .lm1 start target = 0 := by omega
    have hidx : (⟨PEMemory.distance .lm1 start target,
        Nat.lt_of_lt_of_le within (PEMemory.count_le_four .lm1 .word)⟩ : Fin 4) = 0 :=
      Fin.ext hzero
    simp [PEMemory.writeWords, within, hidx, h]
  · simp [PEMemory.writeWords, within]

/-! ## 9. Line 2: the post-state slots (A) -/

/-- The closed `noForward` condition of line 2, in the exact shape the executor
builds it. -/
theorem cendParallel_noForward_bool :
    ([cendIbslExpr.normalize.toParsed, cendFmaExpr.normalize.toParsed].any
      (fun expression =>
        match expression.op with
        | .noforward => true
        | _ => false)) = false :=
  cendParallel_noForward

/-- **The exact residual A: line 2's post-state slots.**  The proof of the
record-level computation is the only missing piece; everything else about line
2 (`cendLine2_pecore_ok`, the walk `cendLine2_walk`) is proved. -/
def CendLine2SlotsResidual : Prop :=
  ∀ (state : State) (pe : PEId) (files : IntegerRegisterFiles),
    state.peRegisters pe = files →
    (∀ cycle : Fin 4,
      stateForwardingSlots state pe .alu cycle = .known cendImmediateBus) →
    ∃ next : State,
      executeIntegerProducerLineAtPECore
        [cendIbslExpr.normalize.toParsed, cendFmaExpr.normalize.toParsed] state pe = .ok next ∧
      next.peContext pe = state.peContext pe ∧
      (next.peRegisters pe).lm0 = files.lm0 ∧
      (∀ cycle : Fin 4,
        stateForwardingSlots next pe .alu cycle =
          .known (cendIbslResultBus
            (cendLm0Word files.lm0 (state.peContext pe).bar0 cycle))) ∧
      (∀ cycle : Fin 4, stateForwardingSlots next pe .mau cycle = .known cendMauForwardBus)

/-- **The exact residual D: line 3's LM1 commit fold.**  The four `sbsl` writes'
per-step commit is `cendSbslCommitStep`; what is missing is the four-fold
identity with `cendSbslLm1`. -/
def CendSbslWrites (files : IntegerRegisterFiles)
    (control : ParsedMaskExecutionControl) : List PreparedParsedMaskedWrite :=
  [cendSbslWrite files control 0, cendSbslWrite files control 1,
    cendSbslWrite files control 2, cendSbslWrite files control 3]

def CendSbslLm1Residual : Prop :=
  ∀ (files : IntegerRegisterFiles) (control : ParsedMaskExecutionControl),
    control.directive = rustSimulatorInitialState.maskDirective →
    control.context.bar1 = 0 →
    (commitParsedMaskedWrites files (CendSbslWrites files control)).lm1 =
      cendSbslLm1 files.lm1
        (fun cycle => byteSwap32
          (cendLm0Word files.lm0 control.context.bar0 cycle))

/-! ## 10. Line 3: the per-PE core step and the walk -/

theorem cendSbsl_stageFilter :
    [cendSbslExpr.normalize.toParsed].filter parsedExprIsIntegerMatrixReadStageInput =
      [cendSbslExpr.normalize.toParsed] := by
  decide

theorem cendSbsl_floatFilter :
    [cendSbslExpr.normalize.toParsed].filter parsedExprIsSupportedFloatMAUProducer = [] := by
  decide

theorem cendLine3_pecore_ok (state : State) (pe : PEId) (files : IntegerRegisterFiles)
    (filesEq : state.peRegisters pe = files)
    (aluEq : ∀ cycle : Fin 4,
      stateForwardingSlots state pe .alu cycle =
        .known (cendIbslResultBus
          (cendLm0Word files.lm0 (state.peContext pe).bar0 cycle)))
    (mauEq : ∀ cycle : Fin 4, stateForwardingSlots state pe .mau cycle = .known cendMauForwardBus) :
    ∃ next : State,
      executeIntegerProducerLineAtPECore [cendSbslExpr.normalize.toParsed] state pe = .ok next := by
  unfold executeIntegerProducerLineAtPECore
  dsimp only
  rw [filesEq]
  rw [cendSbsl_stageFilter]
  simp only [← cendTailControl_eq]
  unfold parsedIntegerMatrixReadLineFourCycleStep
  rw [cendSbsl_lineCycles files (stateForwardingSlots state pe)
    (state.matrixRegisters (ParsedIntegerContext.ofLinearIndex pe).group
      (ParsedIntegerContext.ofLinearIndex pe).l2b
      (ParsedIntegerContext.ofLinearIndex pe).l1b)
    (cendTailControl state pe) aluEq mauEq]
  dsimp only
  rw [executeParsedFloatMAUsAtPE_empty _ _ _ _ _ _ _ cendSbsl_floatFilter]
  dsimp only
  rw [updateSupportedPELineForwarding_eq]
  exact ⟨_, rfl⟩

/-- The per-PE precondition of line 3: the forwarded `ibsl` and MAU buses. -/
def CendSbslReady (state : State) (pe : PEId) : Prop :=
  (∀ cycle : Fin 4,
    stateForwardingSlots state pe .alu cycle =
      .known (cendIbslResultBus
        (cendLm0Word (state.peRegisters pe).lm0 (state.peContext pe).bar0 cycle))) ∧
  (∀ cycle : Fin 4, stateForwardingSlots state pe .mau cycle = .known cendMauForwardBus)

theorem cendLine3_walk (afterTwo : State)
    (ready : ∀ pe : PEId, CendSbslReady afterTwo pe) :
    ∃ afterThree : State,
      executeIntegerProducerLineAtPEs [cendSbslExpr.normalize.toParsed]
        (List.finRange 4096) afterTwo = .ok afterThree := by
  refine cendWalk_of_local [cendSbslExpr.normalize.toParsed] (CendSbslReady) ?_ ?_
    (List.finRange 4096) (List.nodup_finRange 4096) afterTwo ?_
  · intro current pe hready
    exact cendLine3_pecore_ok current pe (current.peRegisters pe) rfl hready.1 hready.2
  · intro state middle pe q different head hq
    have frame := executeIntegerProducerLineAtPE_peFields_other
      [cendSbslExpr.normalize.toParsed] state middle pe q different head
    refine ⟨?_, ?_⟩
    · intro cycle
      rw [frame.1, frame.2.2.2] at *
      simp only [stateForwardingSlots]
      rw [frame.2.2.1, frame.2.1]
      exact hq.1 cycle
    · intro cycle
      simp only [stateForwardingSlots]
      rw [frame.2.2.1, frame.2.1]
      exact hq.2 cycle
  · intro pe _
    exact ready pe

/-! ## 11. Trust report -/

#print axioms cendSbsl_cycle
#print axioms cendSbsl_lineCycles
#print axioms cendLine1_allPE_slots
#print axioms cendLine2_pecore_ok
#print axioms cendLine2_walk
#print axioms cendLine3_pecore_ok
#print axioms cendLine3_walk
#print axioms cendSbslCommitStep
#print axioms cendWalk_of_local

/-- **The exact residual E1: line 1 does not move PE 0's BAR registers.**
Line 1's `imm` row writes GRF0 only; the walk's context update keeps the old
BARs.  This is the remaining hypothesis of `CendLine1Facts` (the LM0 halves are
already supplied by `cendLine1Files_of_execution`). -/
def CendLine1BarResidual : Prop :=
  ∀ (input : BitVec 64) (s1 : State),
    executeNormalizedLine (.pe [cendImmExpr.normalize]) (cendInitialState input) = .ok s1 →
    (s1.peContext cendPE).bar0 = 0 ∧ (s1.peContext cendPE).bar1 = 0

/-! ## 12. A: closing the line-2 post slots -/

/-- The explicit post-state of line 2 at one PE, with the executor's
`List.any` conditions already reduced to `false`/`true`.  It is definitionally
the record `executeIntegerProducerLineAtPECore` builds, so the step equation is
`rfl`. -/
theorem cendLine2SlotsResidual_proved : CendLine2SlotsResidual := by
  intro state pe files filesEq aluEq
  unfold executeIntegerProducerLineAtPECore
  dsimp only
  rw [filesEq]
  rw [cendIbsl_stageFilter]
  simp only [← cendTailControl_eq]
  unfold parsedIntegerMatrixReadLineFourCycleStep
  rw [cendIbsl_lineCycles files (stateForwardingSlots state pe)
    (state.matrixRegisters (ParsedIntegerContext.ofLinearIndex pe).group
      (ParsedIntegerContext.ofLinearIndex pe).l2b
      (ParsedIntegerContext.ofLinearIndex pe).l1b)
    (cendTailControl state pe) aluEq]
  dsimp only
  simp only [← cendIbslWrites_eq]
  obtain ⟨nextFiles, hfma, hlm0⟩ :=
    cendFma_stage files
      (commitParsedMaskedWrites files (cendIbslWrites files (cendTailControl state pe)))
      (stateForwardingSlots state pe)
      { (ParsedIntegerContext.ofLinearIndex pe) with
        bar0 := (state.peContext pe).bar0,
        bar1 := (state.peContext pe).bar1,
        tWord := (state.peContext pe).tWord }
      (state.maskDirective) aluEq
  rw [hfma]
  dsimp only
  rw [updateSupportedPELineForwarding_eq]
  dsimp only
  let slots := lineIssuedSlots (stateForwardingSlots state pe)
    (linePreparedSlots (cendIbslSlots (stateForwardingSlots state pe) files
      (state.peContext pe).bar0) (fun _ => cendMauForwardBus) true)
    true true false
  let valid := updateIntegerLineForwardingValid (state.forwardingValid pe) slots false
  let next : State :=
    { state with
      peRegisters := fun other => if other = pe then nextFiles else state.peRegisters other,
      forwarding := fun other => if other = pe then slots else state.forwarding other,
      forwardingValid := fun other => if other = pe then valid else state.forwardingValid other,
      peContext := fun other => if other = pe then state.peContext pe else state.peContext other }
  refine ⟨next, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · simp [next]
  · dsimp only [next]
    rw [if_pos rfl, hlm0]
    exact cendIbslWrites_lm0 files (cendTailControl state pe)
  · intro cycle
    dsimp only [next, slots, valid]
    have halu : (lineIssuedSlots (stateForwardingSlots state pe)
        (linePreparedSlots (cendIbslSlots (stateForwardingSlots state pe) files
          (state.peContext pe).bar0) (fun _ => cendMauForwardBus) true)
        true true false) .alu cycle =
        .known (cendIbslResultBus (cendLm0Word files.lm0 (state.peContext pe).bar0 cycle)) := by
      simp [slots, lineIssuedSlots, linePreparedSlots, cendIbslSlots]
    have hvalid : updateIntegerLineForwardingValid (state.forwardingValid pe)
        (lineIssuedSlots (stateForwardingSlots state pe)
          (linePreparedSlots (cendIbslSlots (stateForwardingSlots state pe) files
            (state.peContext pe).bar0) (fun _ => cendMauForwardBus) true)
          true true false) false .alu cycle = true := by
      simp [updateIntegerLineForwardingValid, halu, forwardingValueValid]
    simp only [stateForwardingSlots, if_pos rfl, hvalid, if_true]
    exact halu
  · intro cycle
    dsimp only [next, slots, valid]
    have hmau : (lineIssuedSlots (stateForwardingSlots state pe)
        (linePreparedSlots (cendIbslSlots (stateForwardingSlots state pe) files
          (state.peContext pe).bar0) (fun _ => cendMauForwardBus) true)
        true true false) .mau cycle = .known cendMauForwardBus := by
      simp [lineIssuedSlots, linePreparedSlots]
    have hvalid : updateIntegerLineForwardingValid (state.forwardingValid pe)
        (lineIssuedSlots (stateForwardingSlots state pe)
          (linePreparedSlots (cendIbslSlots (stateForwardingSlots state pe) files
            (state.peContext pe).bar0) (fun _ => cendMauForwardBus) true)
          true true false) false .mau cycle = true := by
      simp [updateIntegerLineForwardingValid, hmau, forwardingValueValid]
    simp only [stateForwardingSlots, if_pos rfl, hvalid, if_true]
    exact hmau

/-! ## 13. D: the four-fold LM1 commit -/

theorem cendSbslWrites_eq (files : IntegerRegisterFiles)
    (control : ParsedMaskExecutionControl) :
    CendSbslWrites files control =
      [cendSbslWrite files control 0, cendSbslWrite files control 1,
        cendSbslWrite files control 2, cendSbslWrite files control 3] := rfl

theorem cendIbsl_notBARWriter :
    parsedExprIsIntegerBARWriter cendIbslExpr.normalize.toParsed = false := by
  decide

theorem cendFma_notBARWriter :
    parsedExprIsIntegerBARWriter cendFmaExpr.normalize.toParsed = false := by
  decide

theorem cendParallel_barWriter :
    ([cendIbslExpr.normalize.toParsed, cendFmaExpr.normalize.toParsed].any
      parsedExprIsIntegerBARWriter) = false := by
  simp [cendIbsl_notBARWriter, cendFma_notBARWriter]

theorem cendParallel_rows :
    ([cendIbslExpr.normalize, cendFmaExpr.normalize].map NormalizedExpr.toParsed).all
      parsedExprIsLineExecRow = true := by
  decide

theorem cendParallel_filter :
    List.filter
      (fun expression =>
        !parsedExprIsL2BMProducer expression && !parsedExprIsMslMsrProducer expression &&
          !parsedExprIsMatrixMAUProducer expression && !parsedExprIsBlockFloatProducer expression &&
          !parsedExprIsFloatReluProducer expression)
      [cendIbslExpr.normalize.toParsed, cendFmaExpr.normalize.toParsed] =
      [cendIbslExpr.normalize.toParsed, cendFmaExpr.normalize.toParsed] := by
  decide

theorem cendParallel_lineStep (s1 nextPEs : State)
    (walk : executeIntegerProducerLineAtPEs
      [cendIbslExpr.normalize.toParsed, cendFmaExpr.normalize.toParsed]
      (List.finRange 4096) s1 = .ok nextPEs) :
    executeNormalizedLine (.pe [cendIbslExpr.normalize, cendFmaExpr.normalize]) s1 =
      .ok { nextPEs with
        hazardClock := nextPEs.hazardClock +
          InstructionLine.cost (.pe [cendIbslExpr.normalize, cendFmaExpr.normalize]),
        l1bmTurnaroundValid := false } := by
  have step := executeIntegerProducerInstructionLine_pe_lineExec
    [cendIbslExpr.normalize, cendFmaExpr.normalize] s1 nextPEs
    cendParallelExpr_check cendParallel_rows
    (by simpa [cendParallel_filter] using walk)
  simpa [executeNormalizedLine, NormalizedLine.toInstruction?] using step

theorem cendSbsl_rows :
    ([cendSbslExpr.normalize].map NormalizedExpr.toParsed).all
      parsedExprIsLineExecRow = true := by
  decide

theorem cendSbsl_filter :
    List.filter
      (fun expression =>
        !parsedExprIsL2BMProducer expression && !parsedExprIsMslMsrProducer expression &&
          !parsedExprIsMatrixMAUProducer expression && !parsedExprIsBlockFloatProducer expression &&
          !parsedExprIsFloatReluProducer expression)
      [cendSbslExpr.normalize.toParsed] =
      [cendSbslExpr.normalize.toParsed] := by
  decide

theorem cendSbsl_lineStep (afterTwo nextPEs : State)
    (walk : executeIntegerProducerLineAtPEs
      [cendSbslExpr.normalize.toParsed] (List.finRange 4096) afterTwo = .ok nextPEs) :
    executeNormalizedLine (.pe [cendSbslExpr.normalize]) afterTwo =
      .ok { nextPEs with
        hazardClock := nextPEs.hazardClock +
          InstructionLine.cost (.pe [cendSbslExpr.normalize]),
        l1bmTurnaroundValid := false } := by
  have step := executeIntegerProducerInstructionLine_pe_lineExec
    [cendSbslExpr.normalize] afterTwo nextPEs
    cendSbslExpr_check cendSbsl_rows
    (by simpa [cendSbsl_filter] using walk)
  simpa [executeNormalizedLine, NormalizedLine.toInstruction?] using step

theorem cendLine2_walk_head (input : BitVec 64) (s1 afterTwoPEs : State)
    (executed : executeNormalizedLine (.pe [cendImmExpr.normalize])
      (cendInitialState input) = .ok s1)
    (walk : executeIntegerProducerLineAtPEs
      [cendIbslExpr.normalize.toParsed, cendFmaExpr.normalize.toParsed]
      (List.finRange 4096) s1 = .ok afterTwoPEs) :
    ∃ headNext : State,
      executeIntegerProducerLineAtPE
        [cendIbslExpr.normalize.toParsed, cendFmaExpr.normalize.toParsed] s1 cendPE =
        .ok headNext ∧
      afterTwoPEs.peRegisters cendPE = headNext.peRegisters cendPE ∧
      afterTwoPEs.peContext cendPE = headNext.peContext cendPE ∧
      stateForwardingSlots afterTwoPEs cendPE = stateForwardingSlots headNext cendPE := by
  obtain ⟨next, executedNext, filesAll, slotsAll⟩ := cendLine1_next_allPE input
  rw [executedNext] at executed
  have same : s1 = next := (StepResult.ok.inj executed).symm
  rw [same] at walk ⊢
  obtain ⟨headNext, headCore, headCtx, headLm0, headAlu, headMau⟩ :=
    cendLine2SlotsResidual_proved next cendPE (cendLine1Files input)
      (filesAll cendPE) (slotsAll cendPE)
  have headPE : executeIntegerProducerLineAtPE
      [cendIbslExpr.normalize.toParsed, cendFmaExpr.normalize.toParsed] next cendPE =
      .ok headNext := by
    simpa [executeIntegerProducerLineAtPE, cendParallel_barWriter,
      cendIbsl_notBARWriter, cendFma_notBARWriter, Bool.false_eq_true, false_or]
      using headCore
  have tailWalk : executeIntegerProducerLineAtPEs
      [cendIbslExpr.normalize.toParsed, cendFmaExpr.normalize.toParsed]
      ((List.finRange 4095).map Fin.succ) headNext = .ok afterTwoPEs := by
    have h := walk
    rw [finRange4096_eq_welcomePE_cons] at h
    change (match executeIntegerProducerLineAtPE
        [cendIbslExpr.normalize.toParsed, cendFmaExpr.normalize.toParsed] next cendPE with
      | StepResult.failure => StepResult.failure
      | StepResult.unknown => StepResult.unknown
      | StepResult.ok next =>
          executeIntegerProducerLineAtPEs
            [cendIbslExpr.normalize.toParsed, cendFmaExpr.normalize.toParsed]
            ((List.finRange 4095).map Fin.succ) next) = .ok afterTwoPEs at h
    rw [headPE] at h
    exact h
  have frame := executeIntegerProducerLineAtPEs_peFields_of_not_mem
    [cendIbslExpr.normalize.toParsed, cendFmaExpr.normalize.toParsed]
    ((List.finRange 4095).map Fin.succ) headNext afterTwoPEs cendPE
    welcomePE_not_mem_finRange4095_map_succ tailWalk
  refine ⟨headNext, headPE, frame.1, frame.2.2.2, ?_⟩
  funext unit cycle
  rw [stateForwardingSlots, stateForwardingSlots, frame.2.2.1, frame.2.1]

theorem commitSbslIndices (files : IntegerRegisterFiles)
    (control : ParsedMaskExecutionControl)
    (sel : ∀ cycle : Fin 4,
      cendSbslSelection files control cycle = ⟨BitVec.allOnes 4, true⟩) :
    ∀ (indices : List (Fin 4)) (stateFiles : IntegerRegisterFiles),
      (commitParsedMaskedWrites stateFiles
        (indices.map (cendSbslWrite files control))).lm1 =
      indices.foldl (fun memory cycle =>
        PEMemory.writeWords .lm1 .word memory
          (cendSbslDestinationAccess control.context.bar1 cycle).address
          (cendSingleWord (byteSwap32
            (cendLm0Word files.lm0 control.context.bar0 cycle)))) stateFiles.lm1 := by
  intro indices
  induction indices with
  | nil => intro stateFiles; rfl
  | cons cycle rest ih =>
      intro stateFiles
      rw [List.map_cons, commitParsedMaskedWrites_cons]
      rw [cendSbslCommitStep stateFiles files control cycle (sel cycle)]
      have hmem : cendSbslMemoryState stateFiles files control cycle =
          PEMemory.writeWords .lm1 .word stateFiles.lm1
            (cendSbslDestinationAccess control.context.bar1 cycle).address
            (cendSingleWord (byteSwap32
              (cendLm0Word files.lm0 control.context.bar0 cycle))) := by
        rw [cendSbslMemoryState]
        exact writeWords_word_congr_zero _ _ _ _ (by
          rw [cendSbslWrite_data_zero]
          rfl)
      rw [hmem]
      rw [List.foldl_cons]
      exact ih _

theorem cendSbslLm1Residual_proved : CendSbslLm1Residual := by
  intro files control hdirective hbar
  have sel : ∀ cycle : Fin 4,
      cendSbslSelection files control cycle = ⟨BitVec.allOnes 4, true⟩ :=
    fun cycle => cendSbslSelection_full files control cycle hdirective
  have h := commitSbslIndices files control sel [0, 1, 2, 3] files
  rw [show CendSbslWrites files control =
    [0, 1, 2, 3].map (cendSbslWrite files control) from rfl]
  rw [h]
  have haddr : ∀ c : Fin 4,
      (cendSbslDestinationAccess (0 : BitVec 12) c).address = cendSbslDestination c := by
    intro c
    apply Fin.ext
    simp [cendSbslDestinationAccess, cendSbslDestination]
  rw [hbar]
  simp only [List.foldl, cendSbslLm1, haddr]

theorem cendLine3_pecore_lm1 (state : State) (pe : PEId) (files : IntegerRegisterFiles)
    (filesEq : state.peRegisters pe = files)
    (directiveEq : state.maskDirective = rustSimulatorInitialState.maskDirective)
    (bar1zero : (state.peContext pe).bar1 = 0)
    (aluEq : ∀ cycle : Fin 4,
      stateForwardingSlots state pe .alu cycle =
        .known (cendIbslResultBus
          (cendLm0Word files.lm0 (state.peContext pe).bar0 cycle)))
    (mauEq : ∀ cycle : Fin 4, stateForwardingSlots state pe .mau cycle = .known cendMauForwardBus) :
    ∃ next : State,
      executeIntegerProducerLineAtPECore [cendSbslExpr.normalize.toParsed] state pe = .ok next ∧
      (next.peRegisters pe).lm1 =
        cendSbslLm1 files.lm1
          (fun cycle => byteSwap32
            (cendLm0Word files.lm0 (state.peContext pe).bar0 cycle)) := by
  unfold executeIntegerProducerLineAtPECore
  dsimp only
  rw [filesEq]
  rw [cendSbsl_stageFilter]
  simp only [← cendTailControl_eq]
  unfold parsedIntegerMatrixReadLineFourCycleStep
  rw [cendSbsl_lineCycles files (stateForwardingSlots state pe)
    (state.matrixRegisters (ParsedIntegerContext.ofLinearIndex pe).group
      (ParsedIntegerContext.ofLinearIndex pe).l2b
      (ParsedIntegerContext.ofLinearIndex pe).l1b)
    (cendTailControl state pe) aluEq mauEq]
  dsimp only
  rw [executeParsedFloatMAUsAtPE_empty _ _ _ _ _ _ _ cendSbsl_floatFilter]
  dsimp only
  rw [updateSupportedPELineForwarding_eq]
  dsimp only
  refine ⟨_, rfl, ?_⟩
  have committed : (commitParsedMaskedWrites files
      (CendSbslWrites files (cendTailControl state pe))).lm1 =
      cendSbslLm1 files.lm1
        (fun cycle => byteSwap32
          (cendLm0Word files.lm0 (cendTailControl state pe).context.bar0 cycle)) :=
    cendSbslLm1Residual_proved files (cendTailControl state pe) directiveEq bar1zero
  simpa [CendSbslWrites, cendTailControl] using committed

theorem cendLine3_walk_head (afterTwo afterThreePEs : State)
    (walk : executeIntegerProducerLineAtPEs
      [cendSbslExpr.normalize.toParsed] (List.finRange 4096) afterTwo = .ok afterThreePEs)
    (directiveEq : afterTwo.maskDirective = rustSimulatorInitialState.maskDirective)
    (bar1zero : (afterTwo.peContext cendPE).bar1 = 0)
    (ready : CendSbslReady afterTwo cendPE) :
    ∃ headNext : State,
      executeIntegerProducerLineAtPE [cendSbslExpr.normalize.toParsed] afterTwo cendPE =
        .ok headNext ∧
      afterThreePEs.peRegisters cendPE = headNext.peRegisters cendPE ∧
      (headNext.peRegisters cendPE).lm1 =
        cendSbslLm1 (afterTwo.peRegisters cendPE).lm1
          (fun cycle => byteSwap32
            (cendLm0Word (afterTwo.peRegisters cendPE).lm0
              (afterTwo.peContext cendPE).bar0 cycle)) := by
  obtain ⟨headNext, headCore, headLm1⟩ :=
    cendLine3_pecore_lm1 afterTwo cendPE (afterTwo.peRegisters cendPE) rfl
      directiveEq bar1zero ready.1 ready.2
  have headPE : executeIntegerProducerLineAtPE [cendSbslExpr.normalize.toParsed]
      afterTwo cendPE = .ok headNext := by
    simpa [executeIntegerProducerLineAtPE] using headCore
  have tailWalk : executeIntegerProducerLineAtPEs [cendSbslExpr.normalize.toParsed]
      ((List.finRange 4095).map Fin.succ) headNext = .ok afterThreePEs := by
    have h := walk
    rw [finRange4096_eq_welcomePE_cons] at h
    change (match executeIntegerProducerLineAtPE [cendSbslExpr.normalize.toParsed]
        afterTwo cendPE with
      | StepResult.failure => StepResult.failure
      | StepResult.unknown => StepResult.unknown
      | StepResult.ok next =>
          executeIntegerProducerLineAtPEs [cendSbslExpr.normalize.toParsed]
            ((List.finRange 4095).map Fin.succ) next) = .ok afterThreePEs at h
    rw [headPE] at h
    exact h
  have frame := executeIntegerProducerLineAtPEs_peFields_of_not_mem
    [cendSbslExpr.normalize.toParsed] ((List.finRange 4095).map Fin.succ) headNext
    afterThreePEs cendPE welcomePE_not_mem_finRange4095_map_succ tailWalk
  exact ⟨headNext, headPE, frame.1, headLm1⟩


theorem cendLine1BarResidual_proved : CendLine1BarResidual := by
  intro input s1 executed
  obtain ⟨next, executedNext, _, contextAll⟩ := cendLine1_allPE_slots input
  rw [executedNext] at executed
  have same : s1 = next := (StepResult.ok.inj executed).symm
  rw [same, contextAll cendPE]
  exact ⟨rfl, rfl⟩

#print axioms cendLine2SlotsResidual_proved
#print axioms cendLine1BarResidual_proved
#print axioms cendSbslLm1Residual_proved
#print axioms cendLine2_walk_head
#print axioms cendLine3_walk_head
#print axioms cendParallel_lineStep
#print axioms cendSbsl_lineStep

