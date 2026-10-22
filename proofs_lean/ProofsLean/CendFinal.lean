import ProofsLean.CendTailExec
import ProofsLean.CendHalfMixLink

/-! # `12.convert-endian`: closing the tail residual

`CendTailExec.CendTailForwardResidual` asks, for every input and every line-1
result, for the executor facts of lines 2 and 3.  This module supplies them:

* the per-cycle preparation of the `ibsl` row (its four LM0 word reads, the
  forwarded `$aluf` operator, the GRF0 destination and the installed `.alu`
  slots), and the four-cycle lift;
* the per-PE core step of line 1 with the installed ALU slots and validity
  (needed to re-run line 2's walk over all 4096 PEs);
* ... (filled in as the proof grows)

No `sorry`, no `admit`, no `native_decide`, no new axioms.
-/

namespace ProofsLean.MNCore

open Issue
open PEMemory

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false


theorem cendIbslOp :
    cendIbslExpr.normalize.toParsed =
      (⟨.alu .bsl (some .i) false none, [cendM0, cendAluf], [cendR8], none, ""⟩ : ParsedExpr) := rfl

theorem cendSbslOp :
    cendSbslExpr.normalize.toParsed =
      (⟨.alu .bsl (some .s) false none, [cendAluf, cendMauf], [cendN2103], none, ""⟩ : ParsedExpr) := rfl

theorem cendIbsl_inputCount : ParsedAluName.integerInputCount .bsl = 2 := by decide

theorem cendSbsl_inputCount : ParsedAluName.integerInputCount .bsl = 2 := by decide

/-! ## `$m0v` / `$r8v` / `$aluf` lowering -/

theorem cendM0_access_dest (pe cycle : Fin 4) (bar0 bar1 : BitVec 12) (tWord : BitVec 32) :
    ∃ access : DirectMemoryAccess,
      ParsedOperand.toDirectMemoryAccess? cendM0 pe cycle bar0 bar1 tWord = some access ∧
      access.bank = .lm0 ∧ access.width = .word ∧
      access.address.val = (bar0.toNat + cycle.val) % 4096 := by
  refine ⟨⟨.lm0, .word,
    ⟨(bar0.toNat + cycle.val) % 4096, Nat.mod_lt _ (by decide)⟩⟩, ?_, rfl, rfl, rfl⟩
  exact cendM0_access pe cycle bar0 bar1 tWord

theorem cendM0_input (group : Fin 4) (l2b : Fin 2) (l1b : Fin 8) (mab : Fin 16)
    (pe cycle : Fin 4) (bar0 bar1 : BitVec 12) (tWord : BitVec 32)
    (access : DirectMemoryAccess)
    (haccess : ParsedOperand.toDirectMemoryAccess? cendM0 pe cycle bar0 bar1 tWord = some access) :
    ParsedOperand.toParsedIntegerInput? cendM0 .word group l2b l1b mab pe cycle bar0 bar1 tWord =
      some (.memory access false) := by
  rw [show ParsedOperand.toParsedIntegerInput? cendM0 .word group l2b l1b mab pe cycle bar0 bar1 tWord
      = (ParsedOperand.toDirectMemoryAccess? cendM0 pe cycle bar0 bar1 tWord).map
          (fun resolved => ParsedIntegerInput.memory resolved false) from rfl]
  rw [haccess]
  rfl

theorem cendAluf_input (group : Fin 4) (l2b : Fin 2) (l1b : Fin 8) (mab : Fin 16)
    (pe cycle : Fin 4) (bar0 bar1 : BitVec 12) (tWord : BitVec 32) :
    ParsedOperand.toParsedIntegerInput? cendAluf .word group l2b l1b mab pe cycle bar0 bar1 tWord =
      some (.forward .aluf false) := rfl

theorem cendR8_destination_triple (pe cycle : Fin 4) (bar0 bar1 : BitVec 12)
    (tWord : BitVec 32) :
    (ParsedOperand.toDirectMemoryDestination? cendR8 pe cycle bar0 bar1 tWord).map
        (fun d => (d.bank, d.width, d.address.val)) =
      some (PEMemory.Bank.grf0, PEMemory.Width.word, (8 + cycle.val) % 512) := by
  rw [show ParsedOperand.toDirectMemoryDestination? cendR8 pe cycle bar0 bar1 tWord =
      some ⟨.grf0, .word, ⟨(8 + cycle.val) % 512, Nat.mod_lt _ (by decide)⟩⟩ from
    cendR8_access pe cycle bar0 bar1 tWord]
  rfl

theorem cendS0_destination_triple (pe cycle : Fin 4) (bar0 bar1 : BitVec 12)
    (tWord : BitVec 32) :
    (ParsedOperand.toDirectMemoryDestination? cendS0 pe cycle bar0 bar1 tWord).map
        (fun d => (d.bank, d.width, d.address.val)) =
      some (PEMemory.Bank.grf1, PEMemory.Width.word, (0 + cycle.val) % 512) := by
  rw [show ParsedOperand.toDirectMemoryDestination? cendS0 pe cycle bar0 bar1 tWord =
      some ⟨.grf1, .word, ⟨(0 + cycle.val) % 512, Nat.mod_lt _ (by decide)⟩⟩ from
    cendS0_access pe cycle bar0 bar1 tWord]
  rfl

theorem cendN2103_destination_triple (pe cycle : Fin 4) (bar0 bar1 : BitVec 12)
    (tWord : BitVec 32) :
    (ParsedOperand.toDirectMemoryDestination? cendN2103 pe cycle bar0 bar1 tWord).map
        (fun d => (d.bank, d.width, d.address.val)) =
      some (PEMemory.Bank.lm1, PEMemory.Width.word,
        (bar1.toNat + (cendSbslDestination cycle).val) % 4096) := by
  rw [show ParsedOperand.toDirectMemoryDestination? cendN2103 pe cycle bar0 bar1 tWord =
      some ⟨.lm1, .word,
        ⟨(bar1.toNat + (cendSbslDestination cycle).val) % 4096, Nat.mod_lt _ (by decide)⟩⟩ from
    cendN2103_access pe cycle bar0 bar1 tWord]
  rfl

/-! ## The ibsl lowering -/

theorem cendIbsl_lowered (registers : Masks.RegisterFile) (directive : ParsedMaskDirective)
    (group : Fin 4) (l2b : Fin 2) (l1b : Fin 8) (mab : Fin 16)
    (pe cycle : Fin 4) (bar0 bar1 : BitVec 12) (tWord : BitVec 32)
    (access : DirectMemoryAccess)
    (haccess : ParsedOperand.toDirectMemoryAccess? cendM0 pe cycle bar0 bar1 tWord = some access)
    (selection : PEWordSelection)
    (hselection : ParsedOperand.resolveMemoryWriteSelection? cendR8 PEMemory.Bank.grf0
      registers cycle directive false = some selection) :
    ∃ accesses,
      ParsedExpr.toDirectMaskedIntegerAccessesInLine? cendIbslExpr.normalize.toParsed registers
        directive false group l2b l1b mab pe cycle bar0 bar1 tWord = some accesses ∧
      accesses.sourceX = .memory access false ∧
      accesses.sourceY = .forward .aluf false ∧
      accesses.destination = ⟨.grf0, .word, ⟨(8 + cycle.val) % 512,
        Nat.mod_lt _ (by decide)⟩⟩ ∧
      accesses.destination.bank = PEMemory.Bank.grf0 ∧
      accesses.destination.width = PEMemory.Width.word ∧
      accesses.destination.address.val = (8 + cycle.val) % 512 ∧
      accesses.writeSelection = selection ∧
      accesses.flushSelection = none := by
  obtain ⟨accesses, hlowered, hx, hy, hdest, hsel, hflush⟩ :=
    toDirectMaskedIntegerAccessesInLine?_alu_binary cendIbslExpr.normalize.toParsed
      .bsl .i false none rfl (.word) (.shift .rotateLeft) rfl cendIbsl_inputCount
      registers directive false cendM0 cendAluf cendR8 rfl rfl group l2b l1b mab pe cycle
      bar0 bar1 tWord (.memory access false) (.forward .aluf false)
      ⟨.grf0, .word, ⟨(8 + cycle.val) % 512, Nat.mod_lt _ (by decide)⟩⟩ selection none
      (cendM0_input group l2b l1b mab pe cycle bar0 bar1 tWord access haccess) rfl
      (by
        rw [show ParsedOperand.toDirectMemoryDestination? cendR8 pe cycle bar0 bar1 tWord =
            some ⟨.grf0, .word, ⟨(8 + cycle.val) % 512, Nat.mod_lt _ (by decide)⟩⟩ from
          cendR8_access pe cycle bar0 bar1 tWord])
      hselection rfl
  refine ⟨accesses, hlowered, hx, hy, hdest, ?_, ?_, ?_, hsel, hflush⟩
  · rw [hdest]
  · rw [hdest]
  · rw [hdest]

end ProofsLean.MNCore

namespace ProofsLean.MNCore
open Issue
open PEMemory

theorem cendLm0_pack_read (files : IntegerRegisterFiles) (address : Fin Bank.lm0.capacity) :
    pack (readDirectAccess files ⟨.lm0, .word, address⟩) =
      (⟨files.lm0 address ++ (0#32), (0#64)⟩ : IntegerALU.Bus) := by
  have hcount : PEMemory.count .lm0 .word = 1 := by decide
  have h0 : PEMemory.advance .lm0 address 0 = address := by
    apply Fin.ext
    simp [PEMemory.advance, Nat.mod_eq_of_lt address.isLt]
  simp only [readDirectAccess, readRegisterBank, PEMemory.readWords, pack, hcount,
    h0, Fin.val_zero, Fin.val_one, Fin.val_two]
  simp

theorem cendIbsl_readX (files : IntegerRegisterFiles)
    (slots : ProofsLean.MNCore.Forwarding.Slots) (cycle : Fin 4)
    (address : Fin Bank.lm0.capacity) :
    ParsedIntegerInput.readWithForwarding files slots cycle (.memory ⟨.lm0, .word, address⟩ false) =
      .ok (⟨files.lm0 address ++ (0#32), (0#64)⟩ : IntegerALU.Bus) := by
  rw [show ParsedIntegerInput.readWithForwarding files slots cycle (.memory ⟨.lm0, .word, address⟩ false)
      = ParsedIntegerInput.read files (.memory ⟨.lm0, .word, address⟩ false) from rfl]
  simp only [ParsedIntegerInput.read, ParsedIntegerInput.applyRounding, Bool.false_eq_true,
    ite_false]
  rw [cendLm0_pack_read]

theorem cendIbsl_readY (files : IntegerRegisterFiles)
    (slots : ProofsLean.MNCore.Forwarding.Slots) (cycle : Fin 4)
    (slotEq : slots .alu cycle = .known cendImmediateBus) :
    ParsedIntegerInput.readWithForwarding files slots cycle (.forward .aluf false) =
      .ok cendImmediateBus := by
  simp [ParsedIntegerInput.readWithForwarding, ParsedIntegerInput.forwardUnit,
    ParsedIntegerInput.applyRounding, slotEq]

theorem cendIbsl_eval (w : BitVec 32) :
    evaluateParsedIntegerAlu (.alu .bsl (some .i) false none)
      (⟨w ++ (0#32), (0#64)⟩ : IntegerALU.Bus) cendImmediateBus false =
      .ok (IntegerALU.evaluateBus .word (.shift .rotateLeft)
        (⟨w ++ (0#32), (0#64)⟩ : IntegerALU.Bus) cendImmediateBus false) := by
  rw [parsed_integer_evaluation_uses_requested_semantics
    (.alu .bsl (some .i) false none) .word (.shift .rotateLeft) rfl]

end ProofsLean.MNCore

namespace ProofsLean.MNCore
open Issue
open PEMemory


theorem cendIbsl_cycle
    (files : IntegerRegisterFiles) (oldSlots nextSlots : ProofsLean.MNCore.Forwarding.Slots)
    (control : ParsedMaskExecutionControl) (cycle : Fin 4)
    (address : Fin Bank.lm0.capacity)
    (destination : DirectMemoryAccess)
    (selection : PEWordSelection)
    (haccess : ParsedOperand.toDirectMemoryAccess? cendM0 control.context.pe cycle
      control.context.bar0 control.context.bar1 control.context.tWord =
        some ⟨.lm0, .word, address⟩)
    (hdestination : ParsedOperand.toDirectMemoryDestination? cendR8 control.context.pe cycle
      control.context.bar0 control.context.bar1 control.context.tWord = some destination)
    (hselection : ParsedOperand.resolveMemoryWriteSelection? cendR8 PEMemory.Bank.grf0
      files.maskRegisters cycle control.directive false = some selection)
    (slotEq : oldSlots .alu cycle = .known cendImmediateBus) :
    ∃ accesses,
      ParsedExpr.toDirectMaskedIntegerAccessesInLine? cendIbslExpr.normalize.toParsed
          files.maskRegisters control.directive false control.context.group control.context.l2b
          control.context.l1b control.context.mab control.context.pe cycle control.context.bar0
          control.context.bar1 control.context.tWord = some accesses ∧
      accesses.op = .alu .bsl (some .i) false none ∧
      accesses.sourceX = .memory ⟨.lm0, .word, address⟩ false ∧
      accesses.sourceY = .forward .aluf false ∧
      accesses.destination = destination ∧
      accesses.writeSelection = selection ∧
      accesses.flushSelection = none ∧
      prepareParsedIntegerALUExprCycle files oldSlots nextSlots cendIbslExpr.normalize.toParsed
        control false false false cycle =
      .ok ([⟨some destination, none,
          unpackALUBus (cendIbslResultBus (files.lm0 address)), selection⟩],
        fun unit slotCycle =>
          if unit = .alu ∧ slotCycle = cycle then
            .known (cendIbslResultBus (files.lm0 address))
          else nextSlots unit slotCycle) := by
  obtain ⟨accesses, hlowered, hx, hy, hdestEq, hbank, hwidth, haddr, hsel, hflush⟩ :=
    cendIbsl_lowered files.maskRegisters control.directive control.context.group
      control.context.l2b control.context.l1b control.context.mab control.context.pe cycle
      control.context.bar0 control.context.bar1 control.context.tWord ⟨.lm0, .word, address⟩
      haccess selection hselection
  have hop : accesses.op = .alu .bsl (some .i) false none := by
    rw [toDirectMaskedIntegerAccessesInLine?_op cendIbslExpr.normalize.toParsed
      files.maskRegisters control.directive false control.context.group control.context.l2b
      control.context.l1b control.context.mab control.context.pe cycle control.context.bar0
      control.context.bar1 control.context.tWord accesses hlowered, cendIbslOp]
  have hdestVal : destination =
      ⟨.grf0, .word, ⟨(8 + cycle.val) % 512, Nat.mod_lt _ (by decide)⟩⟩ := by
    have h : ParsedOperand.toDirectMemoryDestination? cendR8 control.context.pe cycle
        control.context.bar0 control.context.bar1 control.context.tWord =
        some ⟨.grf0, .word, ⟨(8 + cycle.val) % 512, Nat.mod_lt _ (by decide)⟩⟩ :=
      cendR8_access control.context.pe cycle control.context.bar0 control.context.bar1
        control.context.tWord
    rw [h] at hdestination
    exact (Option.some.inj hdestination).symm
  have hdestFull : accesses.destination = destination := by
    rw [hdestEq, hdestVal]
  have hlowered' : ParsedExpr.toDirectMaskedIntegerAccessesInLine?
      (⟨.alu .bsl (some .i) false none, [cendM0, cendAluf], [cendR8], none, ""⟩ : ParsedExpr)
      files.maskRegisters control.directive false control.context.group control.context.l2b
      control.context.l1b control.context.mab control.context.pe cycle control.context.bar0
      control.context.bar1 control.context.tWord = some accesses := by
    rw [← cendIbslOp]
    exact hlowered
  have hwrite : prepareParsedMaskedWriteWithForwarding files oldSlots cycle accesses false =
      .ok ⟨some destination, none,
        unpackALUBus (cendIbslResultBus (files.lm0 address)), selection⟩ := by
    unfold prepareParsedMaskedWriteWithForwarding
    rw [hx]
    rw [show ParsedIntegerInput.readWithForwarding files oldSlots cycle
        (.memory ⟨.lm0, .word, address⟩ false) =
          .ok (⟨files.lm0 address ++ (0#32), (0#64)⟩ : IntegerALU.Bus) from
      cendIbsl_readX files oldSlots cycle address]
    try dsimp only
    rw [hy]
    rw [show ParsedIntegerInput.readWithForwarding files oldSlots cycle (.forward .aluf false) =
        .ok cendImmediateBus from cendIbsl_readY files oldSlots cycle slotEq]
    try dsimp only
    rw [hop]
    rw [show evaluateParsedIntegerAlu (.alu .bsl (some .i) false none)
        (⟨files.lm0 address ++ (0#32), (0#64)⟩ : IntegerALU.Bus) cendImmediateBus false =
          .ok (IntegerALU.evaluateBus .word (.shift .rotateLeft)
            (⟨files.lm0 address ++ (0#32), (0#64)⟩ : IntegerALU.Bus) cendImmediateBus false) from
      cendIbsl_eval (files.lm0 address)]
    try dsimp only
    rw [hflush]
    try dsimp only [parsedOutputAfterFlush]
    rw [show (IntegerALU.evaluateBus .word (.shift .rotateLeft)
        (⟨files.lm0 address ++ (0#32), (0#64)⟩ : IntegerALU.Bus) cendImmediateBus false).value
        = cendIbslResultBus (files.lm0 address) from cendIbslBus (files.lm0 address)]
    rw [hsel, hdestFull]
  refine ⟨accesses, hlowered, hop, hx, hy, hdestFull, hsel, hflush, ?_⟩
  rw [cendIbslOp]
  unfold prepareParsedIntegerALUExprCycle
  simp only [hlowered']
  try dsimp only
  rw [hwrite]
  try dsimp only
  rw [updateParsedIntegerALUForwardingCycle_semantics]
  simp only [Bool.false_eq_true, if_false, StepResult.ok.injEq, Prod.mk.injEq,
    List.cons.injEq, and_true]
  refine ⟨trivial, ?_⟩
  funext unit slotCycle
  by_cases h : unit = .alu ∧ slotCycle = cycle <;> simp [h, pack_unpackALUBus]

def cendIbslDestination (cycle : Fin 4) : DirectMemoryAccess :=
  ⟨.grf0, .word, ⟨(8 + cycle.val) % 512, Nat.mod_lt _ (by decide)⟩⟩

def cendIbslSelection (files : IntegerRegisterFiles) (control : ParsedMaskExecutionControl)
    (cycle : Fin 4) : PEWordSelection :=
  (resolveMemoryDirectiveSelection? control.directive PEMemory.Bank.grf0 files.maskRegisters
    cycle).getD ⟨BitVec.allOnes 4, true⟩

def cendIbslWrite (files : IntegerRegisterFiles) (control : ParsedMaskExecutionControl)
    (cycle : Fin 4) : PreparedParsedMaskedWrite :=
  ⟨some (cendIbslDestination cycle), none,
    unpackALUBus (cendIbslResultBus (cendLm0Word files.lm0 control.context.bar0 cycle)),
    cendIbslSelection files control cycle⟩

def cendIbslSlotAt (old : ProofsLean.MNCore.Forwarding.Slots) (files : IntegerRegisterFiles)
    (bar0 : BitVec 12) (cycle : Fin 4) : ProofsLean.MNCore.Forwarding.Slots :=
  fun unit slotCycle =>
    if unit = .alu ∧ slotCycle = cycle then
      .known (cendIbslResultBus (cendLm0Word files.lm0 bar0 cycle))
    else old unit slotCycle

def cendIbslSlots (old : ProofsLean.MNCore.Forwarding.Slots) (files : IntegerRegisterFiles)
    (bar0 : BitVec 12) : ProofsLean.MNCore.Forwarding.Slots :=
  fun unit cycle =>
    if unit = .alu then
      .known (cendIbslResultBus (cendLm0Word files.lm0 bar0 cycle))
    else old unit cycle

theorem cendIbsl_cycleAt (files : IntegerRegisterFiles)
    (oldSlots nextSlots : ProofsLean.MNCore.Forwarding.Slots)
    (control : ParsedMaskExecutionControl) (cycle : Fin 4)
    (slotEq : oldSlots .alu cycle = .known cendImmediateBus) :
    prepareParsedIntegerALUExprCycle files oldSlots nextSlots cendIbslExpr.normalize.toParsed
      control false false false cycle =
    .ok ([cendIbslWrite files control cycle],
      cendIbslSlotAt nextSlots files control.context.bar0 cycle) := by
  have hdest : ParsedOperand.toDirectMemoryDestination? cendR8 control.context.pe cycle
      control.context.bar0 control.context.bar1 control.context.tWord =
      some (cendIbslDestination cycle) := by
    simp only [cendIbslDestination]
    exact cendR8_access control.context.pe cycle control.context.bar0 control.context.bar1
      control.context.tWord
  have hsel : ParsedOperand.resolveMemoryWriteSelection? cendR8 PEMemory.Bank.grf0
      files.maskRegisters cycle control.directive false = some (cendIbslSelection files control cycle) :=
    rfl
  obtain ⟨accesses, hlowered, hop, hx, hy, hdestEq, hselEq, hflushEq, hprep⟩ :=
    cendIbsl_cycle files oldSlots nextSlots control cycle
      ⟨(control.context.bar0.toNat + cycle.val) % 4096, Nat.mod_lt _ (by decide)⟩
      (cendIbslDestination cycle) (cendIbslSelection files control cycle)
      (cendM0_access control.context.pe cycle control.context.bar0 control.context.bar1
        control.context.tWord)
      hdest hsel slotEq
  rw [hprep]
  rfl

theorem cendIbsl_aluCycles (files : IntegerRegisterFiles)
    (oldSlots : ProofsLean.MNCore.Forwarding.Slots)
    (control : ParsedMaskExecutionControl)
    (slotEq : ∀ cycle : Fin 4, oldSlots .alu cycle = .known cendImmediateBus) :
    prepareParsedIntegerALUExprCycles files oldSlots oldSlots cendIbslExpr.normalize.toParsed
      control false false false =
    .ok ([cendIbslWrite files control 0, cendIbslWrite files control 1,
        cendIbslWrite files control 2, cendIbslWrite files control 3],
      cendIbslSlots oldSlots files control.context.bar0) := by
  let s1 := cendIbslSlotAt oldSlots files control.context.bar0 0
  let s2 := cendIbslSlotAt s1 files control.context.bar0 1
  let s3 := cendIbslSlotAt s2 files control.context.bar0 2
  let s4 := cendIbslSlotAt s3 files control.context.bar0 3
  have step0 : prepareParsedIntegerALUExprCycle files oldSlots oldSlots
      cendIbslExpr.normalize.toParsed control false false false 0 =
      .ok ([cendIbslWrite files control 0], s1) :=
    cendIbsl_cycleAt files oldSlots oldSlots control 0 (slotEq 0)
  have step1 : prepareParsedIntegerALUExprCycle files oldSlots s1
      cendIbslExpr.normalize.toParsed control false false false 1 =
      .ok ([cendIbslWrite files control 1], s2) :=
    cendIbsl_cycleAt files oldSlots s1 control 1 (slotEq 1)
  have step2 : prepareParsedIntegerALUExprCycle files oldSlots s2
      cendIbslExpr.normalize.toParsed control false false false 2 =
      .ok ([cendIbslWrite files control 2], s3) :=
    cendIbsl_cycleAt files oldSlots s2 control 2 (slotEq 2)
  have step3 : prepareParsedIntegerALUExprCycle files oldSlots s3
      cendIbslExpr.normalize.toParsed control false false false 3 =
      .ok ([cendIbslWrite files control 3], s4) :=
    cendIbsl_cycleAt files oldSlots s3 control 3 (slotEq 3)
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
    (by_cases hu : unit = .alu <;> simp [s1, s2, s3, s4, cendIbslSlotAt, cendIbslSlots, hu])

theorem cendIbsl_lineCycles (files : IntegerRegisterFiles)
    (oldSlots : ProofsLean.MNCore.Forwarding.Slots) (store : ParsedMatrixReadStore)
    (control : ParsedMaskExecutionControl)
    (slotEq : ∀ cycle : Fin 4, oldSlots .alu cycle = .known cendImmediateBus) :
    prepareParsedIntegerMatrixReadLineCycles files oldSlots store
        [cendIbslExpr.normalize.toParsed] control false =
      .ok ([cendIbslWrite files control 0, cendIbslWrite files control 1,
        cendIbslWrite files control 2, cendIbslWrite files control 3],
        cendIbslSlots oldSlots files control.context.bar0, []) := by
  have hMask : ([cendIbslExpr.normalize.toParsed].any parsedExprHasSingleLineWriteMask) = false := by
    decide
  have hNoForward : ([cendIbslExpr.normalize.toParsed].any (fun expression =>
      match expression.op with
      | .noforward => true
      | _ => false)) = false := by decide
  unfold prepareParsedIntegerMatrixReadLineCycles
  dsimp only
  simp only [hMask, hNoForward]
  refine prepareParsedIntegerMatrixReadLineExpressions_singleton files oldSlots store
    cendIbslExpr.normalize.toParsed control false false false
    [cendIbslWrite files control 0, cendIbslWrite files control 1,
      cendIbslWrite files control 2, cendIbslWrite files control 3]
    (cendIbslSlots oldSlots files control.context.bar0) [] ?_
  have hcycles : prepareParsedIntegerALUExprCycles files oldSlots oldSlots
      cendIbslExpr.normalize.toParsed control false false false =
      .ok ([cendIbslWrite files control 0, cendIbslWrite files control 1,
        cendIbslWrite files control 2, cendIbslWrite files control 3],
        cendIbslSlots oldSlots files control.context.bar0) :=
    cendIbsl_aluCycles files oldSlots control slotEq
  have hcycles' : prepareParsedIntegerALUExprCycles files oldSlots oldSlots
      (⟨.alu .bsl (some .i) false none, [cendM0, cendAluf], [cendR8], none, ""⟩ : ParsedExpr)
      control false false false =
      .ok ([cendIbslWrite files control 0, cendIbslWrite files control 1,
        cendIbslWrite files control 2, cendIbslWrite files control 3],
        cendIbslSlots oldSlots files control.context.bar0) := by
    rw [← cendIbslOp]
    exact hcycles
  unfold prepareParsedIntegerMatrixReadLineExpression
  rw [cendIbslOp]
  dsimp only
  rw [hcycles']
  dsimp only
  rw [show parsedIntegerALUBarUpdates
      (⟨.alu .bsl (some .i) false none, [cendM0, cendAluf], [cendR8], none, ""⟩ : ParsedExpr)
      [cendIbslWrite files control 0, cendIbslWrite files control 1,
        cendIbslWrite files control 2, cendIbslWrite files control 3] = [] from by
    simp [parsedIntegerALUBarUpdates, cendR8]]

/-! ## The line-1 per-PE core step: installed ALU slots and validity -/

theorem cendImm_pecore_slots (input : BitVec 64) (state : State) (pe : PEId)
    (filesEq : state.peRegisters pe = cendInitialPERegisters input)
    (validEq : ∀ (unit : ProofsLean.MNCore.Forwarding.Unit) (cycle : Fin 4),
      state.forwardingValid pe unit cycle = false)
    (ctxEq : state.peContext pe = ParsedIntegerContext.ofLinearIndex pe)
    (directiveEq : state.maskDirective = rustSimulatorInitialState.maskDirective) :
    ∃ next, executeIntegerProducerLineAtPECore [cendImmExpr.normalize.toParsed] state pe =
        .ok next ∧
      (∀ cycle : Fin 4,
        stateForwardingSlots next pe .alu cycle = .known cendImmediateBus) ∧
      (∀ cycle : Fin 4, next.forwardingValid pe .alu cycle = true) := by
  obtain ⟨next, executed, files⟩ :=
    cendImm_pecore input state pe filesEq validEq ctxEq directiveEq
  have hasALU : ([cendImmExpr.normalize.toParsed].any parsedExprIsIntegerProducer) = true := by
    decide
  have noForward : ([cendImmExpr.normalize.toParsed].any (fun expression =>
      match expression.op with
      | .noforward => true
      | _ => false)) = false := by decide
  obtain ⟨intWrites, intSlots, intBars, preparedEq, slotValues⟩ :=
    executeIntegerProducerLineAtPECore_alu_slot [cendImmExpr.normalize.toParsed] state next pe
      hasALU noForward executed
  have registersEq : (cendInitialPERegisters input).maskRegisters =
      zeroInitialPERegisterFiles.maskRegisters := rfl
  have pinned : prepareParsedIntegerMatrixReadLineCycles (cendInitialPERegisters input)
      (stateForwardingSlots state pe)
      (state.matrixRegisters (ParsedIntegerContext.ofLinearIndex pe).group
        (ParsedIntegerContext.ofLinearIndex pe).l2b
        (ParsedIntegerContext.ofLinearIndex pe).l1b)
      [cendImmExpr.normalize.toParsed]
      { directive := state.maskDirective
        context :=
          { (ParsedIntegerContext.ofLinearIndex pe) with
            bar0 := (state.peContext pe).bar0
            bar1 := (state.peContext pe).bar1
            tWord := (state.peContext pe).tWord }
        elapsedWords := state.hazardClock } false =
      .ok (cendImmWrites,
        immediateALUSlots (stateForwardingSlots state pe) 0x34F80010 false false
          (fun _ => none), []) := by
    rw [directiveEq]
    exact cendImm_lineCycles_any (cendInitialPERegisters input)
      (stateForwardingSlots state pe)
      (state.matrixRegisters (ParsedIntegerContext.ofLinearIndex pe).group
        (ParsedIntegerContext.ofLinearIndex pe).l2b
        (ParsedIntegerContext.ofLinearIndex pe).l1b)
      { directive := rustSimulatorInitialState.maskDirective
        context :=
          { (ParsedIntegerContext.ofLinearIndex pe) with
            bar0 := (state.peContext pe).bar0
            bar1 := (state.peContext pe).bar1
            tWord := (state.peContext pe).tWord }
        elapsedWords := state.hazardClock } rfl registersEq
  have hfilter : List.filter parsedExprIsIntegerMatrixReadStageInput
      [cendImmExpr.normalize.toParsed] = [cendImmExpr.normalize.toParsed] := by
    simp [cendImm_stageInput]
  rw [filesEq] at preparedEq
  rw [hfilter] at preparedEq
  rw [pinned] at preparedEq
  simp only [StepResult.ok.injEq, Prod.mk.injEq] at preparedEq
  obtain ⟨rfl, rfl, -⟩ := preparedEq
  have slotsKnown : ∀ cycle : Fin 4,
      stateForwardingSlots next pe .alu cycle = .known cendImmediateBus := by
    intro cycle
    rw [slotValues cycle]
    simp only [immediateALUSlots, if_true]
    rw [show pack (immediateALUWrite 0x34F80010 false false none).data = cendImmediateBus from
      cendImmALUWrite_value]
  refine ⟨next, executed, slotsKnown, ?_⟩
  intro cycle
  have hknown := slotsKnown cycle
  cases hv : next.forwardingValid pe .alu cycle with
  | false =>
      rw [stateForwardingSlots_invalid_is_poison next pe .alu cycle hv] at hknown
      simp at hknown
  | true => rfl


def cendS0Destination (cycle : Fin 4) : DirectMemoryAccess :=
  ⟨.grf1, .word, ⟨(0 + cycle.val) % 512, Nat.mod_lt _ (by decide)⟩⟩

theorem cendS0_destination (pe cycle : Fin 4) (bar0 bar1 : BitVec 12) (tWord : BitVec 32) :
    ParsedOperand.toDirectMemoryDestination? cendS0 pe cycle bar0 bar1 tWord =
      some (cendS0Destination cycle) := by
  simp only [cendS0Destination]
  exact cendS0_access pe cycle bar0 bar1 tWord

theorem cendS0_destinationBankWidth :
    ParsedOperand.directDestinationBankWidth? cendS0 = some (PEMemory.Bank.grf1, PEMemory.Width.word) := rfl

theorem writeDirectAccessMasked_lm0_of_ne (files : IntegerRegisterFiles)
    (access : DirectMemoryAccess) (data : WordBus) (selection : PEWordSelection)
    (ne : access.bank ≠ PEMemory.Bank.lm0) :
    (writeDirectAccessMasked files access data selection).lm0 = files.lm0 := by
  cases access with
  | mk bank width address =>
      exact writeRegisterBankMasked_lm0_of_ne files bank width address data selection ne

theorem cendS0_msrWrite (files : IntegerRegisterFiles) (context : ParsedIntegerContext)
    (output : IntegerALU.Bus) (flags : BitVec 4) (cycle : Fin 4)
    (directive : ParsedMaskDirective) (hasSingleLineMask : Bool) :
    writeParsedMslMsrDestination? files cendS0 context output flags cycle directive
        hasSingleLineMask =
      some ⟨writeDirectAccessMasked files (cendS0Destination cycle) (unpackALUBus output)
        (if hasSingleLineMask then ⟨BitVec.allOnes 4, true⟩
          else (resolveMemoryDirectiveSelection? directive PEMemory.Bank.grf1
            files.maskRegisters cycle).getD ⟨BitVec.allOnes 4, true⟩), none⟩ := by
  unfold writeParsedMslMsrDestination?
  rw [cendS0_destination]
  simp only [Option.bind_some]
  cases hasSingleLineMask <;> rfl

theorem cendS0_write_exists (files : IntegerRegisterFiles) (context : ParsedIntegerContext)
    (output : IntegerALU.Bus) (flags : BitVec 4) (cycle : Fin 4)
    (directive : ParsedMaskDirective) (hasSingleLineMask : Bool) :
    ∃ writes : ParsedMAUDestinationWrites,
      writeParsedMAUDestinations? files [cendS0] context output flags cycle directive
        hasSingleLineMask = some writes ∧
      writes.bar0 = context.bar0 ∧ writes.bar1 = context.bar1 ∧
      writes.files.lm0 = files.lm0 := by
  refine ⟨⟨writeDirectAccessMasked files (cendS0Destination cycle) (unpackALUBus output)
      (if hasSingleLineMask then ⟨BitVec.allOnes 4, true⟩
        else (resolveMemoryDirectiveSelection? directive PEMemory.Bank.grf1
          files.maskRegisters cycle).getD ⟨BitVec.allOnes 4, true⟩),
    context.bar0, context.bar1⟩, ?_, rfl, rfl, ?_⟩
  · rw [writeParsedMAUDestinations?.eq_1]
    rw [writeParsedMAUDestinations?.writeAll.eq_2]
    rw [cendS0_msrWrite]
    show writeParsedMAUDestinations?.writeAll context output flags cycle directive
        hasSingleLineMask [] (writeDirectAccessMasked files (cendS0Destination cycle)
          (unpackALUBus output) _) context.bar0 context.bar1 =
      some ⟨writeDirectAccessMasked files (cendS0Destination cycle) (unpackALUBus output) _,
        context.bar0, context.bar1⟩
    rw [writeParsedMAUDestinations?.writeAll.eq_1]
  · exact writeDirectAccessMasked_lm0_of_ne files _ _ _ (by simp [cendS0Destination])

theorem cendFma_destinations :
    cendFmaExpr.normalize.toParsed.destinations = [cendS0] := by
  rw [cendFmaExpr_eq]

theorem cendFma_flush (registers : Masks.RegisterFile) (cycle : Fin 4) :
    resolveFlushSelection? cendFmaExpr.normalize.toParsed.flush registers cycle =
      some (none : Option PEWordSelection) := by
  rw [cendFmaExpr_eq]
  rfl

theorem cendFma_cycles_general (readFiles : IntegerRegisterFiles)
    (oldSlots : ProofsLean.MNCore.Forwarding.Slots) (context : ParsedIntegerContext)
    (directive : ParsedMaskDirective) (hasSingleLineMask : Bool)
    (slotEq : ∀ cycle : Fin 4, oldSlots .alu cycle = .known cendImmediateBus) :
    ∀ (cycles : List (Fin 4)) (files : IntegerRegisterFiles) (bar0 bar1 : BitVec 12)
      (outputs : Fin 4 → IntegerALU.Bus),
      ∃ (nextFiles : IntegerRegisterFiles) (out0 out1 : BitVec 12)
        (nextOutputs : Fin 4 → IntegerALU.Bus),
        executeParsedFloatMAUCyclesAtPE readFiles oldSlots cendFmaExpr.normalize.toParsed
          context directive hasSingleLineMask cycles files bar0 bar1 outputs =
          .ok (nextFiles, out0, out1, nextOutputs) ∧
        out0 = bar0 ∧ out1 = bar1 ∧
        (∀ i, nextOutputs i = if i ∈ cycles then cendMauForwardBus else outputs i) ∧
        nextFiles.lm0 = files.lm0 := by
  intro cycles
  induction cycles with
  | nil =>
      intro files bar0 bar1 outputs
      refine ⟨files, bar0, bar1, outputs, by rw [executeParsedFloatMAUCyclesAtPE.eq_1],
        rfl, rfl, ?_, rfl⟩
      intro i
      simp
  | cons cycle rest ih =>
      intro files bar0 bar1 outputs
      rw [executeParsedFloatMAUCyclesAtPE.eq_2]
      dsimp only
      rw [show executeParsedFloatMAUCycleAtPE readFiles files oldSlots
          cendFmaExpr.normalize.toParsed
          { context with cycle := cycle, bar0 := bar0, bar1 := bar1 } cycle =
          .ok (files, cendMauForwardBus,
            parsedVectorMAUFlags .single false cendMauForwardBus) from
        cendFmaCycle readFiles files oldSlots _ cycle (slotEq cycle)]
      dsimp only
      rw [cendFma_flush]
      dsimp only
      rw [cendFma_destinations]
      rw [show parsedOutputAfterFlush (none : Option PEWordSelection) cendMauForwardBus =
        cendMauForwardBus from rfl]
      obtain ⟨write, hwrite, hb0, hb1, hlm0⟩ := cendS0_write_exists files
        { context with cycle := cycle, bar0 := bar0, bar1 := bar1 } cendMauForwardBus
        (parsedVectorMAUFlags .single false cendMauForwardBus) cycle directive hasSingleLineMask
      rw [hwrite]
      dsimp only
      obtain ⟨nextFiles, out0, out1, nextOutputs, hexec, ho0, ho1, houts, hlm⟩ :=
        ih write.files write.bar0 write.bar1
          (fun i => if i = cycle then cendMauForwardBus else outputs i)
      refine ⟨nextFiles, out0, out1, nextOutputs, hexec, ho0.trans hb0, ho1.trans hb1, ?_,
        ?_⟩
      · intro i
        rw [houts i]
        by_cases hi : i ∈ rest
        · rw [if_pos hi]
          simp [List.mem_cons, hi]
        · rw [if_neg hi]
          by_cases hc : i = cycle
          · rw [if_pos hc]
            simp [List.mem_cons, hc]
          · rw [if_neg hc]
            simp [List.mem_cons, hi, hc]
      · rw [hlm, hlm0]

theorem cendFma_cycles (readFiles : IntegerRegisterFiles)
    (oldSlots : ProofsLean.MNCore.Forwarding.Slots) (context : ParsedIntegerContext)
    (directive : ParsedMaskDirective) (hasSingleLineMask : Bool)
    (slotEq : ∀ cycle : Fin 4, oldSlots .alu cycle = .known cendImmediateBus)
    (files : IntegerRegisterFiles) (bar0 bar1 : BitVec 12) (outputs : Fin 4 → IntegerALU.Bus) :
    ∃ (nextFiles : IntegerRegisterFiles) (nextOutputs : Fin 4 → IntegerALU.Bus),
      executeParsedFloatMAUCyclesAtPE readFiles oldSlots cendFmaExpr.normalize.toParsed
        context directive hasSingleLineMask [0, 1, 2, 3] files bar0 bar1 outputs =
        .ok (nextFiles, bar0, bar1, nextOutputs) ∧
      nextOutputs = (fun _ => cendMauForwardBus) ∧
      nextFiles.lm0 = files.lm0 := by
  obtain ⟨nextFiles, out0, out1, nextOutputs, hexec, ho0, ho1, houts, hlm⟩ :=
    cendFma_cycles_general readFiles oldSlots context directive hasSingleLineMask slotEq
      [0, 1, 2, 3] files bar0 bar1 outputs
  refine ⟨nextFiles, nextOutputs, ?_, ?_, hlm⟩
  · rw [hexec, ho0, ho1]
  · funext c
    rw [houts c]
    rw [if_pos (by
      rcases cendCycle_cases c with rfl | rfl | rfl | rfl <;> simp)]

theorem cendFma_filter :
    [cendIbslExpr.normalize.toParsed, cendFmaExpr.normalize.toParsed].filter
      parsedExprIsSupportedFloatMAUProducer = [cendFmaExpr.normalize.toParsed] := by
  decide

theorem cendFma_noMask :
    ([cendIbslExpr.normalize.toParsed, cendFmaExpr.normalize.toParsed].any
      parsedExprHasSingleLineWriteMask) = false := by
  decide

theorem cendFma_stage (readFiles currentFiles : IntegerRegisterFiles)
    (oldSlots : ProofsLean.MNCore.Forwarding.Slots) (context : ParsedIntegerContext)
    (directive : ParsedMaskDirective)
    (slotEq : ∀ cycle : Fin 4, oldSlots .alu cycle = .known cendImmediateBus) :
    ∃ nextFiles : IntegerRegisterFiles,
      executeParsedFloatMAUsAtPE readFiles currentFiles oldSlots context
          [cendIbslExpr.normalize.toParsed, cendFmaExpr.normalize.toParsed] directive
          ([cendIbslExpr.normalize.toParsed, cendFmaExpr.normalize.toParsed].any
            parsedExprHasSingleLineWriteMask) =
        .ok (nextFiles, context.bar0, context.bar1, (fun _ => cendMauForwardBus), true) ∧
      nextFiles.lm0 = currentFiles.lm0 := by
  obtain ⟨middleFiles, middleOutputs, hcycles, houtputs, hlm⟩ :=
    cendFma_cycles readFiles oldSlots context directive false slotEq currentFiles
      context.bar0 context.bar1 (fun _ => ⟨0, 0⟩)
  rw [cendFma_noMask]
  rw [executeParsedFloatMAUsAtPE.eq_1]
  try dsimp only
  rw [cendFma_filter]
  try dsimp only
  rw [executeParsedFloatMAUsAtPE.run.eq_2]
  try dsimp only
  rw [show executeParsedFloatMAUCyclesAtPE readFiles oldSlots cendFmaExpr.normalize.toParsed
      context directive false [0, 1, 2, 3] currentFiles context.bar0 context.bar1
      (fun _ => (⟨0, 0⟩ : IntegerALU.Bus)) =
      .ok (middleFiles, context.bar0, context.bar1, middleOutputs) from hcycles]
  try dsimp only
  rw [executeParsedFloatMAUsAtPE.run.eq_1]
  try dsimp only
  rw [houtputs]
  exact ⟨middleFiles, rfl, hlm⟩

end ProofsLean.MNCore
