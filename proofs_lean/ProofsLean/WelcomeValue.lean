import ProofsLean.WelcomeComplete

/-! # Value semantics of the Welcome `iinc` lines on the whole-machine model -/

namespace ProofsLean.MNCore

open Issue
open PEMemory

/-- The default simulator mask directive (`Machine::new`): no target banks,
entry zero. Both Welcome lines are emitted without a directive, so the
whole-machine state keeps this value. -/
def welcomeMaskDirective : ParsedMaskDirective :=
  { widthWords := 0, targets := {}, entry := ⟨0, by decide⟩ }

theorem welcomeMaskDirective_targets_lm1 :
    directiveTargetsBank welcomeMaskDirective.targets .lm1 = false := rfl

theorem welcomeMaskDirective_targets_lm0 :
    directiveTargetsBank welcomeMaskDirective.targets .lm0 = false := rfl

/-- Raw (pre-`Fin`) address of the long word handled by cycle `cycle` of line
`base`, matching the executor's `(raw / words * words) % capacity` rounding. -/
def welcomeRawAddress (base : Nat) (cycle : Fin 4) : Nat :=
  (base + 2 * cycle.val) / 2 * 2 % 4096

def welcomeSourceAddress (base : Nat) (cycle : Fin 4) : Fin Bank.lm0.capacity :=
  ⟨welcomeRawAddress base cycle, by
    simp [welcomeRawAddress]
    exact Nat.mod_lt _ (by decide)⟩

def welcomeDestinationAddress (base : Nat) (cycle : Fin 4) : Fin Bank.lm1.capacity :=
  ⟨welcomeRawAddress base cycle, by
    simp [welcomeRawAddress]
    exact Nat.mod_lt _ (by decide)⟩

def welcomeSourceAccess (base : Nat) (cycle : Fin 4) : DirectMemoryAccess :=
  ⟨.lm0, .long, welcomeSourceAddress base cycle⟩

def welcomeDestinationAccess (base : Nat) (cycle : Fin 4) : DirectMemoryAccess :=
  ⟨.lm1, .long, welcomeDestinationAddress base cycle⟩

/-- For the two Welcome bases the raw address is the plain word index. -/
theorem welcomeRawAddress_eq (base : Nat) (bounded : base = 0 ∨ base = 8)
    (cycle : Fin 4) :
    welcomeRawAddress base cycle = base + 2 * cycle.val := by
  rcases bounded with rfl | rfl <;>
    simp only [welcomeRawAddress] <;> omega

theorem welcomeSourceAddress_val (base : Nat) (bounded : base = 0 ∨ base = 8)
    (cycle : Fin 4) :
    (welcomeSourceAddress base cycle).val = base + 2 * cycle.val := by
  simp [welcomeSourceAddress, welcomeRawAddress_eq base bounded cycle]

theorem welcomeDestinationAddress_val (base : Nat) (bounded : base = 0 ∨ base = 8)
    (cycle : Fin 4) :
    (welcomeDestinationAddress base cycle).val = base + 2 * cycle.val := by
  simp [welcomeDestinationAddress, welcomeRawAddress_eq base bounded cycle]

/-- Concrete lowering of the Welcome expression at a cycle, for the canonical
mask directive, zero BAR context and empty mask register file. -/
theorem welcome_accesses
    (base : Nat) (registers : Masks.RegisterFile) (group : Fin 4) (l2b : Fin 2)
    (l1b : Fin 8) (mab : Fin 16) (pe cycle : Fin 4) (bar1 : BitVec 12)
    (tWord : BitVec 32) (bar1Zero : bar1 = 0) :
    ∃ accesses,
      ParsedExpr.toDirectMaskedIntegerAccessesInLine? (welcomeExpr base).toParsed
        registers welcomeMaskDirective false group l2b l1b mab pe cycle 0 bar1 tWord =
        some accesses ∧
      accesses.op = .alu .inc (some .i) false none ∧
      accesses.sourceX = .memory (welcomeSourceAccess base cycle) false ∧
      accesses.sourceY = .memory (welcomeSourceAccess base cycle) false ∧
      accesses.destination = welcomeDestinationAccess base cycle ∧
      accesses.writeSelection = ⟨BitVec.allOnes 4, true⟩ ∧
      accesses.flushSelection = none := by
  subst bar1Zero
  have hreq : (ParsedOp.alu .inc (some .i) false none).executionRequest =
      .ok (.integer .word (.arith .inc false)) :=
    Issue.integer_request_is_execution_request _ _ _ Issue.iinc_integer_request
  unfold ParsedExpr.toDirectMaskedIntegerAccessesInLine?
  simp only [welcomeExpr_toParsed, Issue.plusOneParsedAt]
  split
  · rename_i precision aluOp heq
    rw [hreq] at heq
    cases heq
    simp (config := { decide := true }) [Issue.plusOneReadAt, Issue.plusOneWriteAt,
      Issue.plusOneAccess, ParsedOperand.toParsedIntegerInput?,
      ParsedOperand.toDirectMemoryAccess?, ParsedOperand.toDirectMemoryAccessMode?,
      ParsedOperand.toDirectMemoryDestination?,
      ParsedOperand.resolveMemoryWriteSelection?, resolveMemoryDirectiveSelection?,
      directiveTargetsBank, resolveFlushSelection?, welcomeMaskDirective,
      welcomeSourceAccess, welcomeDestinationAccess, welcomeSourceAddress,
      welcomeDestinationAddress, welcomeRawAddress, parsedRegionAddressAt,
      parsedWidth?, issueBankToRegisterBank, Bank.capacity]
    all_goals
      have hcycle : cycle.val = 0 ∨ cycle.val = 1 ∨ cycle.val = 2 ∨ cycle.val = 3 := by
        have := cycle.isLt
        omega
      rcases hcycle with h | h | h | h <;> simp [h, Width.words]
  · rename_i bad
    exact False.elim (bad .word (.arith .inc false) hreq)

/-- The exact prepared write of one Welcome ALU cycle: the `.long` LM1
destination, no mask-register update, the `iinc` bus, and the all-ones
long-word selection. -/
def welcomePreparedWrite (files : IntegerRegisterFiles) (base : Nat)
    (cycle : Fin 4) : PreparedParsedMaskedWrite where
  destination := some (welcomeDestinationAccess base cycle)
  maskUpdate := none
  data := unpackALUBus (parsedIntegerRegisterOutput files
    (welcomeSourceAccess base cycle) (welcomeSourceAccess base cycle)
    .word (.arith .inc false) false).value
  selection := ⟨BitVec.allOnes 4, true⟩

/-- Forwarding slots after committing one Welcome ALU cycle. -/
def welcomePreparedSlots (nextSlots : Forwarding.Slots) (files : IntegerRegisterFiles)
    (base : Nat) (cycle : Fin 4) : Forwarding.Slots :=
  fun unit slotCycle =>
    if unit = .alu ∧ slotCycle = cycle then .known (pack (welcomePreparedWrite files base cycle).data)
    else nextSlots unit slotCycle

/-- A memory-sourced prepared write, with no flush selection, commits exactly
the `evaluateBus` result that `parsedIntegerRegisterOutput` computes. -/
theorem prepareParsedMaskedWriteWithForwarding_memory_eq
    (files : IntegerRegisterFiles) (slots : Forwarding.Slots) (cycle : Fin 4)
    (accesses : ParsedMaskedIntegerAccesses) (reduced : Bool)
    (sourceX : accesses.sourceX = .memory sourceXAccess false)
    (sourceY : accesses.sourceY = .memory sourceYAccess false)
    (flushNone : accesses.flushSelection = none)
    (precision : IntegerALU.Precision) (aluOp : IntegerALU.Op)
    (request : accesses.op.executionRequest = .ok (.integer precision aluOp)) :
    prepareParsedMaskedWriteWithForwarding files slots cycle accesses reduced =
      .ok { destination := some accesses.destination
            maskUpdate := none
            data := unpackALUBus (IntegerALU.evaluateBus precision aluOp
              (pack (readDirectAccess files sourceXAccess))
              (pack (readDirectAccess files sourceYAccess)) reduced).value
            selection := accesses.writeSelection } := by
  unfold prepareParsedMaskedWriteWithForwarding
  rw [sourceX, sourceY, flushNone]
  simp [ParsedIntegerInput.readWithForwarding, ParsedIntegerInput.read,
    ParsedIntegerInput.applyRounding, evaluateParsedIntegerAlu, request,
    evaluateParsedExecutionRequest, parsedOutputAfterFlush]

/-- Per-cycle transition of a Welcome line on the canonical state shape. -/
theorem welcome_prepareParsedIntegerALUExprCycle
    (files : IntegerRegisterFiles) (oldSlots nextSlots : Forwarding.Slots)
    (base : Nat) (control : ParsedMaskExecutionControl) (cycle : Fin 4)
    (directiveEq : control.directive = welcomeMaskDirective)
    (bar0Zero : control.context.bar0 = 0)
    (bar1Zero : control.context.bar1 = 0) :
    prepareParsedIntegerALUExprCycle files oldSlots nextSlots
      (welcomeExpr base).toParsed control false false false cycle =
      .ok ([welcomePreparedWrite files base cycle],
        welcomePreparedSlots nextSlots files base cycle) := by
  obtain ⟨accesses, lowered, op, sourceX, sourceY, destination, selection, flush⟩ :=
    welcome_accesses base files.maskRegisters control.context.group control.context.l2b
      control.context.l1b control.context.mab control.context.pe cycle control.context.bar1
      control.context.tWord bar1Zero
  have request : accesses.op.executionRequest = .ok (.integer .word (.arith .inc false)) := by
    rw [op]
    exact Issue.integer_request_is_execution_request _ _ _ Issue.iinc_integer_request
  unfold prepareParsedIntegerALUExprCycle
  rw [welcomeExpr_toParsed_op]
  have bar0Sub : control.context.bar0 = 0 := bar0Zero
  have directiveSub : control.directive = welcomeMaskDirective := directiveEq
  simp only [bar0Sub, directiveSub, lowered, sourceX, sourceY]
  rw [prepareParsedMaskedWriteWithForwarding_memory_eq files oldSlots cycle accesses false
    sourceX sourceY flush .word (.arith .inc false) request]
  simp [updateParsedIntegerALUForwardingCycle]
  refine ⟨?_, ?_⟩
  · simp [welcomePreparedWrite, destination, selection, parsedIntegerRegisterOutput]
  · funext unit slotCycle
    simp [welcomePreparedWrite, welcomePreparedSlots, parsedIntegerRegisterOutput,
      pack_unpackALUBus]


/-- Four-cycle preparation of one Welcome line: exactly the four per-cycle
writes, in cycle order. -/
theorem welcome_prepareParsedIntegerALUCycles
    (files : IntegerRegisterFiles) (oldSlots initialSlots : Forwarding.Slots) (base : Nat)
    (control : ParsedMaskExecutionControl)
    (directiveEq : control.directive = welcomeMaskDirective)
    (bar0Zero : control.context.bar0 = 0)
    (bar1Zero : control.context.bar1 = 0) :
    ∃ slots,
      prepareParsedIntegerALUExprCycles files oldSlots initialSlots
        (welcomeExpr base).toParsed control false false false =
        .ok ([welcomePreparedWrite files base 0, welcomePreparedWrite files base 1,
          welcomePreparedWrite files base 2, welcomePreparedWrite files base 3], slots) := by
  let s1 := welcomePreparedSlots initialSlots files base 0
  let s2 := welcomePreparedSlots s1 files base 1
  let s3 := welcomePreparedSlots s2 files base 2
  refine ⟨welcomePreparedSlots s3 files base 3, ?_⟩
  unfold prepareParsedIntegerALUExprCycles
  simp only [parsedIntegerALUCycles]
  rw [prepareParsedIntegerALUCycles.eq_2]
  rw [welcome_prepareParsedIntegerALUExprCycle files oldSlots initialSlots base control 0
    directiveEq bar0Zero bar1Zero]
  dsimp only
  simp only [List.nil_append]
  rw [prepareParsedIntegerALUCycles.eq_2]
  rw [welcome_prepareParsedIntegerALUExprCycle files oldSlots s1 base control 1
    directiveEq bar0Zero bar1Zero]
  dsimp only
  rw [prepareParsedIntegerALUCycles.eq_2]
  rw [welcome_prepareParsedIntegerALUExprCycle files oldSlots s2 base control 2
    directiveEq bar0Zero bar1Zero]
  dsimp only
  rw [prepareParsedIntegerALUCycles.eq_2]
  rw [welcome_prepareParsedIntegerALUExprCycle files oldSlots s3 base control 3
    directiveEq bar0Zero bar1Zero]
  dsimp only
  rw [prepareParsedIntegerALUCycles.eq_1]
  simp [s1, s2, s3, List.cons_append, List.nil_append]


/-- The Welcome line has no BAR destination, so the ALU BAR update list is
empty. -/
theorem welcome_toParsed_noSingleLineMask (base : Nat) :
    parsedExprHasSingleLineWriteMask (welcomeExpr base).toParsed = false := by
  simp [parsedExprHasSingleLineWriteMask, parsedOperandHasSingleLineWriteMask,
    welcomeExpr_toParsed, Issue.plusOneParsedAt, Issue.plusOneWriteAt,
    Issue.plusOneAccess]

theorem welcome_toParsed_notNoforward (base : Nat) :
    (match (welcomeExpr base).toParsed.op with
      | .noforward => true
      | _ => false) = false := by
  rw [welcomeExpr_toParsed_op]

theorem welcome_parsedIntegerALUBarUpdates (base : Nat)
    (writes : List PreparedParsedMaskedWrite) :
    parsedIntegerALUBarUpdates (welcomeExpr base).toParsed writes = [] := by
  simp [parsedIntegerALUBarUpdates, welcomeExpr_toParsed, Issue.plusOneParsedAt,
    Issue.plusOneWriteAt, Issue.plusOneAccess]

/-- One Welcome ALU expression over four cycles, as returned by the
matrix-read line expression preparation. -/
theorem welcome_prepareParsedIntegerMatrixReadLineExpression
    (files : IntegerRegisterFiles) (oldSlots nextSlots : Forwarding.Slots)
    (store : ParsedMatrixReadStore) (base : Nat)
    (control : ParsedMaskExecutionControl)
    (directiveEq : control.directive = welcomeMaskDirective)
    (bar0Zero : control.context.bar0 = 0)
    (bar1Zero : control.context.bar1 = 0) :
    ∃ slots,
      prepareParsedIntegerMatrixReadLineExpression files oldSlots nextSlots store
        (welcomeExpr base).toParsed control false false false =
        .ok ([welcomePreparedWrite files base 0, welcomePreparedWrite files base 1,
          welcomePreparedWrite files base 2, welcomePreparedWrite files base 3], slots, []) := by
  obtain ⟨slots, prepared⟩ :=
    welcome_prepareParsedIntegerALUCycles files oldSlots nextSlots base control directiveEq bar0Zero bar1Zero
  refine ⟨slots, ?_⟩
  unfold prepareParsedIntegerMatrixReadLineExpression
  rw [welcomeExpr_toParsed_op]
  dsimp only
  rw [prepared]
  simp [welcome_parsedIntegerALUBarUpdates]

/-- The singleton matrix-read line fold of one Welcome expression. -/
theorem welcome_prepareParsedIntegerMatrixReadLineExpressions
    (files : IntegerRegisterFiles) (oldSlots : Forwarding.Slots)
    (store : ParsedMatrixReadStore) (base : Nat)
    (control : ParsedMaskExecutionControl)
    (directiveEq : control.directive = welcomeMaskDirective)
    (bar0Zero : control.context.bar0 = 0)
    (bar1Zero : control.context.bar1 = 0) :
    ∃ slots,
      prepareParsedIntegerMatrixReadLineExpressions files oldSlots store control
        false false false [(welcomeExpr base).toParsed] [] oldSlots [] =
        .ok ([welcomePreparedWrite files base 0, welcomePreparedWrite files base 1,
          welcomePreparedWrite files base 2, welcomePreparedWrite files base 3], slots, []) := by
  obtain ⟨slots, prepared⟩ :=
    welcome_prepareParsedIntegerMatrixReadLineExpression files oldSlots oldSlots store base
      control directiveEq bar0Zero bar1Zero
  refine ⟨slots, ?_⟩
  simp [prepareParsedIntegerMatrixReadLineExpressions, prepared, List.append_assoc]

/-- Four-cycle execution of one Welcome line expression commits the four
prepared writes and leaves the matrix-read BAR-update list empty. -/
theorem welcome_parsedIntegerMatrixReadLineFourCycleStep
    (files : IntegerRegisterFiles) (slots : Forwarding.Slots)
    (store : ParsedMatrixReadStore) (base : Nat)
    (control : ParsedMaskExecutionControl)
    (directiveEq : control.directive = welcomeMaskDirective)
    (bar0Zero : control.context.bar0 = 0)
    (bar1Zero : control.context.bar1 = 0) :
    ∃ nextSlots,
      parsedIntegerMatrixReadLineFourCycleStep files slots store
        [(welcomeExpr base).toParsed] control false =
        .ok (commitParsedMaskedWrites files
          [welcomePreparedWrite files base 0, welcomePreparedWrite files base 1,
           welcomePreparedWrite files base 2, welcomePreparedWrite files base 3],
          nextSlots, []) := by
  obtain ⟨nextSlots, prepared⟩ :=
    welcome_prepareParsedIntegerMatrixReadLineExpressions files slots store base control
      directiveEq bar0Zero bar1Zero
  refine ⟨nextSlots, ?_⟩
  unfold parsedIntegerMatrixReadLineFourCycleStep
  change (match prepareParsedIntegerMatrixReadLineExpressions files slots store control
      false false false [(welcomeExpr base).toParsed] [] slots [] with
    | StepResult.failure => StepResult.failure
    | StepResult.unknown => StepResult.unknown
    | StepResult.ok (writes, nextSlots, barUpdates) =>
      StepResult.ok (commitParsedMaskedWrites files writes, nextSlots, barUpdates)) =
    StepResult.ok (commitParsedMaskedWrites files
      [welcomePreparedWrite files base 0, welcomePreparedWrite files base 1,
       welcomePreparedWrite files base 2, welcomePreparedWrite files base 3],
      nextSlots, [])
  rw [prepared]


/-- A masked `.long` LM1 write outside the words read back by a `.long` LM1
read preserves that read. -/
theorem readDirectAccess_lm1Long_after_write_outside
    (files : IntegerRegisterFiles) (written read : Fin Bank.lm1.capacity)
    (data : WordBus) (selection : PEWordSelection) (index : Fin 4)
    (outside : count .lm1 .long ≤ distance .lm1 written (advance .lm1 read index.val)) :
    readDirectAccess
      (writeDirectAccessMasked files ⟨.lm1, .long, written⟩ data selection)
      ⟨.lm1, .long, read⟩ index =
      readDirectAccess files ⟨.lm1, .long, read⟩ index := by
  simp only [readDirectAccess, readRegisterBank, writeDirectAccessMasked,
    writeRegisterBankMasked, readWords]
  rw [writeWordsMasked_preserves_outside .lm1 .long files.lm1 written
    (advance .lm1 read index.val) data selection.flags selection.longLong outside]

/-- A single `.long` LM1 write commits to one masked access. -/
theorem commitParsedMaskedWrites_singleton_lm1Long
    (files : IntegerRegisterFiles) (written : Fin Bank.lm1.capacity)
    (data : WordBus) (selection : PEWordSelection) :
    commitParsedMaskedWrites files
      [⟨some ⟨.lm1, .long, written⟩, none, data, selection⟩] =
      writeDirectAccessMasked files ⟨.lm1, .long, written⟩ data selection := by
  simp [commitParsedMaskedWrites]

/-- Folding `.long` LM1 writes that all fall outside a read access preserves
that read. -/
theorem commitParsedMaskedWrites_lm1Long_preserves_read
    (files : IntegerRegisterFiles) (writes : List PreparedParsedMaskedWrite)
    (read : Fin Bank.lm1.capacity) (index : Fin 4)
    (shape : ∀ write ∈ writes, ∃ written data selection,
      write = ⟨some ⟨.lm1, .long, written⟩, none, data, selection⟩)
    (outside : ∀ write ∈ writes, ∀ written data selection,
      write = ⟨some ⟨.lm1, .long, written⟩, none, data, selection⟩ →
        count .lm1 .long ≤ distance .lm1 written (advance .lm1 read index.val)) :
    readDirectAccess (commitParsedMaskedWrites files writes)
      ⟨.lm1, .long, read⟩ index =
      readDirectAccess files ⟨.lm1, .long, read⟩ index := by
  induction writes generalizing files with
  | nil => rfl
  | cons write rest ih =>
      obtain ⟨written, data, selection, writeEq⟩ := shape write (by simp)
      subst writeEq
      rw [show commitParsedMaskedWrites files
          (⟨some ⟨.lm1, .long, written⟩, none, data, selection⟩ :: rest) =
        commitParsedMaskedWrites
          (commitParsedMaskedWrites files
            [⟨some ⟨.lm1, .long, written⟩, none, data, selection⟩]) rest from rfl]
      rw [ih (commitParsedMaskedWrites files
        [⟨some ⟨.lm1, .long, written⟩, none, data, selection⟩])
        (by
          intro item member
          exact shape item (List.mem_cons_of_mem _ member))
        (by
          intro item member written' data' selection' itemEq
          exact outside item (List.mem_cons_of_mem _ member) written' data' selection' itemEq)]
      rw [commitParsedMaskedWrites_singleton_lm1Long]
      exact readDirectAccess_lm1Long_after_write_outside files written read data selection index
        (outside _ (by simp) written data selection rfl)

/-- Each Welcome prepared write has the canonical `.long` LM1 shape. -/
theorem welcomePreparedWrite_shape (files : IntegerRegisterFiles) (base : Nat)
    (cycle : Fin 4) :
    ∃ written data selection,
      welcomePreparedWrite files base cycle =
        ⟨some ⟨.lm1, .long, written⟩, none, data, selection⟩ :=
  ⟨welcomeDestinationAddress base cycle, _, _, rfl⟩


/-- The modular arithmetic behind the Welcome write-window separation. -/
theorem welcomeDistanceArith (read written index : Nat) (hr : read < 4)
    (hw : written < 4) (hi : index < 2) (different : written ≠ read) :
    2 ≤ (2 * read + index + 4096 - 2 * written) % 4096 := by
  by_cases h : written < read
  · have expand : 2 * read + index + 4096 - 2 * written =
        4096 + (2 * (read - written) + index) := by omega
    rw [expand, Nat.add_mod_left]
    rw [Nat.mod_eq_of_lt] <;> omega
  · have reverse : read < written := by omega
    rw [Nat.mod_eq_of_lt] <;> omega

/-- A Welcome write at a different cycle falls outside the `.long` word window
of the read access. -/
theorem welcomeWrite_outside (base : Nat) (bounded : base = 0 ∨ base = 8)
    (read writtenCycle : Fin 4) (index : Fin 4) (indexBound : index.val < 2)
    (different : writtenCycle.val ≠ read.val) :
    count .lm1 .long ≤ distance .lm1 (welcomeDestinationAddress base writtenCycle)
      (advance .lm1 (welcomeDestinationAddress base read) index.val) := by
  have hc := writtenCycle.isLt
  have hr := read.isLt
  have hi := index.isLt
  rcases bounded with rfl | rfl
  · have hrw : (0 + 2 * read.val) / 2 * 2 % 4096 = 2 * read.val := by omega
    have hww : (0 + 2 * writtenCycle.val) / 2 * 2 % 4096 = 2 * writtenCycle.val := by omega
    have hinner : (2 * read.val + index.val) % 4096 = 2 * read.val + index.val := by
      rw [Nat.mod_eq_of_lt] <;> omega
    simp only [count, Width.words, distance, advance, Bank.capacity,
      welcomeDestinationAddress, welcomeRawAddress]
    rw [hrw, hww, hinner]
    exact welcomeDistanceArith read.val writtenCycle.val index.val hr hc indexBound different
  · have hrw : (8 + 2 * read.val) / 2 * 2 % 4096 = 8 + 2 * read.val := by omega
    have hww : (8 + 2 * writtenCycle.val) / 2 * 2 % 4096 = 8 + 2 * writtenCycle.val := by omega
    have hinner : (8 + 2 * read.val + index.val) % 4096 = 8 + 2 * read.val + index.val := by
      rw [Nat.mod_eq_of_lt] <;> omega
    simp only [count, Width.words, distance, advance, Bank.capacity,
      welcomeDestinationAddress, welcomeRawAddress]
    rw [hrw, hww, hinner]
    have expand : 8 + 2 * read.val + index.val + 4096 - (8 + 2 * writtenCycle.val) =
        2 * read.val + index.val + 4096 - 2 * writtenCycle.val := by omega
    rw [expand]
    exact welcomeDistanceArith read.val writtenCycle.val index.val hr hc indexBound different

/-- Committing a list of Welcome writes outside `read` preserves that read. -/
theorem welcomePreparedWrites_preserves_read
    (files writeFiles : IntegerRegisterFiles) (base : Nat) (bounded : base = 0 ∨ base = 8)
    (cycles : List (Fin 4)) (read : Fin 4) (index : Fin 4)
    (indexBound : index.val < 2)
    (allDifferent : ∀ c ∈ cycles, c.val ≠ read.val) :
    readDirectAccess (commitParsedMaskedWrites files
      (cycles.map (welcomePreparedWrite writeFiles base)))
      (welcomeDestinationAccess base read) index =
    readDirectAccess files (welcomeDestinationAccess base read) index := by
  induction cycles generalizing files with
  | nil => rfl
  | cons cycle rest ih =>
      rw [List.map_cons]
      rw [show commitParsedMaskedWrites files
          (welcomePreparedWrite writeFiles base cycle ::
            rest.map (welcomePreparedWrite writeFiles base)) =
        commitParsedMaskedWrites
          (commitParsedMaskedWrites files [welcomePreparedWrite writeFiles base cycle])
          (rest.map (welcomePreparedWrite writeFiles base)) from rfl]
      rw [ih (commitParsedMaskedWrites files [welcomePreparedWrite writeFiles base cycle])
        (by
          intro c member
          exact allDifferent c (List.mem_cons_of_mem _ member))]
      unfold welcomePreparedWrite welcomeDestinationAccess
      rw [commitParsedMaskedWrites_singleton_lm1Long]
      exact readDirectAccess_lm1Long_after_write_outside files
        (welcomeDestinationAddress base cycle) (welcomeDestinationAddress base read)
        (unpackALUBus (parsedIntegerRegisterOutput writeFiles
          (welcomeSourceAccess base cycle) (welcomeSourceAccess base cycle)
          .word (.arith .inc false) false).value)
        ⟨BitVec.allOnes 4, true⟩ index
        (welcomeWrite_outside base bounded read cycle index indexBound
          (allDifferent cycle (by simp)))


/-- A fully enabled masked merge returns the new word. -/
theorem mergeSelectedWord_allOnes (old new : BitVec 32) :
    mergeSelectedWord old new (BitVec.allOnes 32) = new := by
  simp [mergeSelectedWord]
  exact BitVec.and_allOnes

/-- Reading back the last committed Welcome write returns its data. -/
theorem welcomeLastWrite_readback (files writeFiles : IntegerRegisterFiles)
    (base : Nat) (cycle : Fin 4) (index : Fin 4) (indexBound : index.val < 2) :
    readDirectAccess (commitParsedMaskedWrites files
      [welcomePreparedWrite writeFiles base cycle])
      (welcomeDestinationAccess base cycle) index =
    (welcomePreparedWrite writeFiles base cycle).data index := by
  have within : index.val < count .lm1 .long := by
    simp [count, Width.words]
    exact indexBound
  unfold welcomePreparedWrite welcomeDestinationAccess
  rw [commitParsedMaskedWrites_singleton_lm1Long]
  rw [readDirectAccessMasked_after_write files ⟨.lm1, .long, welcomeDestinationAddress base cycle⟩
    _ ⟨BitVec.allOnes 4, true⟩ index within]
  change mergeSelectedWord _ _ (selectedWordMask (BitVec.allOnes 4) true index) = _
  rw [selectedWordMask_allOnes]
  exact mergeSelectedWord_allOnes _ _

/-- The four committed Welcome writes read back as the cycle's own bus word. -/
theorem welcome_commit_readback (files writeFiles : IntegerRegisterFiles)
    (base : Nat) (bounded : base = 0 ∨ base = 8) (cycle : Fin 4)
    (index : Fin 4) (indexBound : index.val < 2) :
    readDirectAccess (commitParsedMaskedWrites files
      [welcomePreparedWrite writeFiles base 0, welcomePreparedWrite writeFiles base 1,
       welcomePreparedWrite writeFiles base 2, welcomePreparedWrite writeFiles base 3])
      (welcomeDestinationAccess base cycle) index =
    (welcomePreparedWrite writeFiles base cycle).data index := by
  have hcycle : cycle.val = 0 ∨ cycle.val = 1 ∨ cycle.val = 2 ∨ cycle.val = 3 := by
    have := cycle.isLt
    omega
  rcases hcycle with h | h | h | h
  · have eq : cycle = 0 := Fin.ext h
    subst eq
    rw [show [welcomePreparedWrite writeFiles base 0, welcomePreparedWrite writeFiles base 1,
        welcomePreparedWrite writeFiles base 2, welcomePreparedWrite writeFiles base 3] =
        [welcomePreparedWrite writeFiles base 0] ++
          List.map (welcomePreparedWrite writeFiles base) [1, 2, 3] from rfl]
    rw [commitParsedMaskedWrites_append]
    rw [welcomePreparedWrites_preserves_read
      (commitParsedMaskedWrites files [welcomePreparedWrite writeFiles base 0])
      writeFiles base bounded [1, 2, 3] 0 index indexBound]
    · exact welcomeLastWrite_readback files writeFiles base 0 index indexBound
    · intro c member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl <;> decide
  · have eq : cycle = 1 := Fin.ext h
    subst eq
    rw [show [welcomePreparedWrite writeFiles base 0, welcomePreparedWrite writeFiles base 1,
        welcomePreparedWrite writeFiles base 2, welcomePreparedWrite writeFiles base 3] =
        [welcomePreparedWrite writeFiles base 0, welcomePreparedWrite writeFiles base 1] ++
          List.map (welcomePreparedWrite writeFiles base) [2, 3] from rfl]
    rw [commitParsedMaskedWrites_append]
    rw [welcomePreparedWrites_preserves_read
      (commitParsedMaskedWrites files
        [welcomePreparedWrite writeFiles base 0, welcomePreparedWrite writeFiles base 1])
      writeFiles base bounded [2, 3] 1 index indexBound]
    · rw [show [welcomePreparedWrite writeFiles base 0, welcomePreparedWrite writeFiles base 1] =
          [welcomePreparedWrite writeFiles base 0] ++ [welcomePreparedWrite writeFiles base 1] from rfl]
      rw [commitParsedMaskedWrites_append]
      exact welcomeLastWrite_readback
        (commitParsedMaskedWrites files [welcomePreparedWrite writeFiles base 0])
        writeFiles base 1 index indexBound
    · intro c member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> decide
  · have eq : cycle = 2 := Fin.ext h
    subst eq
    rw [show [welcomePreparedWrite writeFiles base 0, welcomePreparedWrite writeFiles base 1,
        welcomePreparedWrite writeFiles base 2, welcomePreparedWrite writeFiles base 3] =
        [welcomePreparedWrite writeFiles base 0, welcomePreparedWrite writeFiles base 1,
          welcomePreparedWrite writeFiles base 2] ++
          List.map (welcomePreparedWrite writeFiles base) [3] from rfl]
    rw [commitParsedMaskedWrites_append]
    rw [welcomePreparedWrites_preserves_read
      (commitParsedMaskedWrites files
        [welcomePreparedWrite writeFiles base 0, welcomePreparedWrite writeFiles base 1,
          welcomePreparedWrite writeFiles base 2])
      writeFiles base bounded [3] 2 index indexBound]
    · rw [show [welcomePreparedWrite writeFiles base 0, welcomePreparedWrite writeFiles base 1,
          welcomePreparedWrite writeFiles base 2] =
          [welcomePreparedWrite writeFiles base 0, welcomePreparedWrite writeFiles base 1] ++
            [welcomePreparedWrite writeFiles base 2] from rfl]
      rw [commitParsedMaskedWrites_append]
      exact welcomeLastWrite_readback
        (commitParsedMaskedWrites files
          [welcomePreparedWrite writeFiles base 0, welcomePreparedWrite writeFiles base 1])
        writeFiles base 2 index indexBound
    · intro c member
      simp only [List.mem_singleton] at member
      subst member
      decide
  · have eq : cycle = 3 := Fin.ext h
    subst eq
    rw [show [welcomePreparedWrite writeFiles base 0, welcomePreparedWrite writeFiles base 1,
        welcomePreparedWrite writeFiles base 2, welcomePreparedWrite writeFiles base 3] =
        [welcomePreparedWrite writeFiles base 0, welcomePreparedWrite writeFiles base 1,
          welcomePreparedWrite writeFiles base 2] ++
          [welcomePreparedWrite writeFiles base 3] from rfl]
    rw [commitParsedMaskedWrites_append]
    exact welcomeLastWrite_readback
      (commitParsedMaskedWrites files
        [welcomePreparedWrite writeFiles base 0, welcomePreparedWrite writeFiles base 1,
          welcomePreparedWrite writeFiles base 2])
      writeFiles base 3 index indexBound


/-- The committed Welcome writes preserve LM0. -/
theorem welcomeCommits_lm0_preserved (files writeFiles : IntegerRegisterFiles)
    (base : Nat) :
    (commitParsedMaskedWrites files
      [welcomePreparedWrite writeFiles base 0, welcomePreparedWrite writeFiles base 1,
       welcomePreparedWrite writeFiles base 2, welcomePreparedWrite writeFiles base 3]).lm0 =
      files.lm0 := by
  unfold welcomePreparedWrite welcomeDestinationAccess
  simp [commitParsedMaskedWrites, writeDirectAccessMasked, writeRegisterBankMasked]

/-- `updateSupportedPELineForwarding` never fails: `advanceReference` only
returns `.ok` for an `issue` summary. -/
theorem updateSupportedPELineForwarding_ne_failure (old prepared : Forwarding.Slots)
    (noForward hasALUProducer hasMAUProducer hasMatrixReadProducer : Bool) :
    updateSupportedPELineForwarding old prepared noForward hasALUProducer
      hasMAUProducer hasMatrixReadProducer ≠ .failure := by
  cases noForward <;> cases hasALUProducer <;> cases hasMAUProducer <;>
    cases hasMatrixReadProducer <;>
    simp [updateSupportedPELineForwarding, Forwarding.advanceReference]

/-- Boolean facts about the Welcome expression list used by the line executor. -/
theorem welcome_hasALUProducer (base : Nat) :
    [(welcomeExpr base).toParsed].any parsedExprIsIntegerProducer = true := by
  simp [welcomeExpr_integerProducer]

theorem welcome_hasMAUProducer (base : Nat) :
    [(welcomeExpr base).toParsed].any parsedExprIsSupportedFloatMAUProducer = false := by
  simp [welcomeExpr_notFloatMAUProducer]

theorem welcomeExpr_notMatrixReadProducer (base : Nat) :
    parsedExprIsMatrixReadProducer (welcomeExpr base).toParsed = false := rfl

theorem welcome_hasMatrixReadProducer (base : Nat) :
    [(welcomeExpr base).toParsed].any parsedExprIsMatrixReadProducer = false := by
  simp [welcomeExpr_notMatrixReadProducer]

theorem welcome_lineMaskFalse (base : Nat) :
    [(welcomeExpr base).toParsed].any parsedExprHasSingleLineWriteMask = false := by
  simp [welcome_toParsed_noSingleLineMask]

theorem welcome_lineNoForwardFalse (base : Nat) :
    [(welcomeExpr base).toParsed].any (fun expression =>
      match expression.op with | .noforward => true | _ => false) = false := by
  simp [welcome_toParsed_notNoforward]

/-- The forwarding update of a Welcome line: only the integer ALU slots move. -/
theorem updateSupportedPELineForwarding_welcome_eq (old prepared : Forwarding.Slots) :
    updateSupportedPELineForwarding old prepared false true false false =
      .ok (fun unit cycle =>
        match unit with
        | .alu => prepared .alu cycle
        | .mau => .poison
        | .matrixRead => .known ⟨0, 0⟩
        | .l1ToPE => old unit cycle) := by
  simp [updateSupportedPELineForwarding, Forwarding.advanceReference]
  funext unit cycle
  cases unit <;> rfl

/-- The per-PE core transition of a Welcome line succeeds. -/
theorem welcome_executeIntegerProducerLineAtPECore_success
    (base : Nat) (state : State) (pe : PEId)
    (directiveEq : state.maskDirective = welcomeMaskDirective)
    (bar0Zero : (state.peContext pe).bar0 = 0)
    (bar1Zero : (state.peContext pe).bar1 = 0) :
    ∃ next, executeIntegerProducerLineAtPECore [(welcomeExpr base).toParsed] state pe =
      .ok next := by
  let oldContext := state.peContext pe
  let coordinates := PEMemory.ParsedIntegerContext.ofLinearIndex pe
  let context := { coordinates with
    bar0 := oldContext.bar0
    bar1 := oldContext.bar1
    tWord := oldContext.tWord }
  let control : ParsedMaskExecutionControl :=
    { directive := state.maskDirective
      context := context
      elapsedWords := state.hazardClock }
  have directiveEq' : control.directive = welcomeMaskDirective := by
    simpa [control] using directiveEq
  have bar0Zero' : control.context.bar0 = 0 := by
    simpa [control, context] using bar0Zero
  have bar1Zero' : control.context.bar1 = 0 := by
    simpa [control, context] using bar1Zero
  obtain ⟨nextSlots, fourCycle⟩ :=
    welcome_parsedIntegerMatrixReadLineFourCycleStep (state.peRegisters pe)
      (stateForwardingSlots state pe)
      (state.matrixRegisters context.group context.l2b context.l1b) base control
      directiveEq' bar0Zero' bar1Zero'
  unfold executeIntegerProducerLineAtPECore
  dsimp only
  rw [welcome_filter_stageInput base]
  rw [fourCycle]
  dsimp only
  rw [executeParsedFloatMAUsAtPE_noforward
    (floatEmpty := by simp [welcomeExpr_notFloatMAUProducer])]
  dsimp only
  simp [welcome_lineNoForwardFalse base, welcome_hasALUProducer base,
    welcome_hasMAUProducer base, welcome_hasMatrixReadProducer base,
    updateSupportedPELineForwarding, Forwarding.advanceReference]
  exact ⟨_, rfl⟩

/-- The per-PE core transition of a Welcome line installs the committed
increment writes at `pe` and leaves every other PE untouched. -/
theorem welcome_executeIntegerProducerLineAtPECore_peRegisters
    (base : Nat) (state next : State) (pe : PEId)
    (directiveEq : state.maskDirective = welcomeMaskDirective)
    (bar0Zero : (state.peContext pe).bar0 = 0)
    (bar1Zero : (state.peContext pe).bar1 = 0)
    (executed : executeIntegerProducerLineAtPECore [(welcomeExpr base).toParsed]
      state pe = .ok next) :
    next.peRegisters = fun other =>
      if other = pe then
        commitParsedMaskedWrites (state.peRegisters pe)
          [welcomePreparedWrite (state.peRegisters pe) base 0,
           welcomePreparedWrite (state.peRegisters pe) base 1,
           welcomePreparedWrite (state.peRegisters pe) base 2,
           welcomePreparedWrite (state.peRegisters pe) base 3]
      else state.peRegisters other := by
  let oldContext := state.peContext pe
  let coordinates := PEMemory.ParsedIntegerContext.ofLinearIndex pe
  let context := { coordinates with
    bar0 := oldContext.bar0
    bar1 := oldContext.bar1
    tWord := oldContext.tWord }
  let control : ParsedMaskExecutionControl :=
    { directive := state.maskDirective
      context := context
      elapsedWords := state.hazardClock }
  have directiveEq' : control.directive = welcomeMaskDirective := by
    simpa [control] using directiveEq
  have bar0Zero' : control.context.bar0 = 0 := by
    simpa [control, context] using bar0Zero
  have bar1Zero' : control.context.bar1 = 0 := by
    simpa [control, context] using bar1Zero
  obtain ⟨nextSlots, fourCycle⟩ :=
    welcome_parsedIntegerMatrixReadLineFourCycleStep (state.peRegisters pe)
      (stateForwardingSlots state pe)
      (state.matrixRegisters context.group context.l2b context.l1b) base control
      directiveEq' bar0Zero' bar1Zero'
  unfold executeIntegerProducerLineAtPECore at executed
  dsimp only at executed
  rw [welcome_filter_stageInput base] at executed
  rw [fourCycle] at executed
  dsimp only at executed
  rw [executeParsedFloatMAUsAtPE_noforward
    (floatEmpty := by simp [welcomeExpr_notFloatMAUProducer])] at executed
  dsimp only at executed
  generalize h : updateSupportedPELineForwarding (stateForwardingSlots state pe)
      (fun unit cycle =>
        if (decide (unit = Forwarding.Unit.mau) && false) = true then
          Forwarding.Value.known (⟨0, 0⟩ : IntegerALU.Bus)
        else nextSlots unit cycle)
      ([(welcomeExpr base).toParsed].any (fun expression =>
        match expression.op with
        | .noforward => true
        | _ => false))
      ([(welcomeExpr base).toParsed].any parsedExprIsIntegerProducer)
      false
      ([(welcomeExpr base).toParsed].any parsedExprIsMatrixReadProducer) = result at executed
  cases result with
  | failure =>
      exact absurd h (updateSupportedPELineForwarding_ne_failure _ _ _ _ _ _)
  | unknown =>
      exact absurd h (updateSupportedPELineForwarding_never_unknown _ _ _ _ _ _)
  | ok forwarding =>
      simp only [StepResult.ok.injEq] at executed
      subst executed
      rfl


/-- A Welcome line has no float BAR writer. -/
theorem welcome_floatBAR_false (base : Nat) (lm1 : Bool) :
    [(welcomeExpr base).toParsed].any (parsedFloatMAUWritesBAR lm1) = false := by
  simp [parsedFloatMAUWritesBAR, welcomeExpr_notFloatMAUProducer]

/-- The per-PE core transition of a Welcome line preserves the mask directive
and the zero BAR context. -/
theorem welcome_executeIntegerProducerLineAtPECore_context
    (base : Nat) (state next : State) (pe : PEId)
    (directiveEq : state.maskDirective = welcomeMaskDirective)
    (bar0Zero : (state.peContext pe).bar0 = 0)
    (bar1Zero : (state.peContext pe).bar1 = 0)
    (executed : executeIntegerProducerLineAtPECore [(welcomeExpr base).toParsed]
      state pe = .ok next) :
    next.maskDirective = state.maskDirective ∧
      (∀ other, other ≠ pe → next.peContext other = state.peContext other) ∧
      (next.peContext pe).bar0 = (state.peContext pe).bar0 ∧
      (next.peContext pe).bar1 = (state.peContext pe).bar1 := by
  let oldContext := state.peContext pe
  let coordinates := PEMemory.ParsedIntegerContext.ofLinearIndex pe
  let context := { coordinates with
    bar0 := oldContext.bar0
    bar1 := oldContext.bar1
    tWord := oldContext.tWord }
  let control : ParsedMaskExecutionControl :=
    { directive := state.maskDirective
      context := context
      elapsedWords := state.hazardClock }
  have directiveEq' : control.directive = welcomeMaskDirective := by
    simpa [control] using directiveEq
  have bar0Zero' : control.context.bar0 = 0 := by
    simpa [control, context] using bar0Zero
  have bar1Zero' : control.context.bar1 = 0 := by
    simpa [control, context] using bar1Zero
  obtain ⟨nextSlots, fourCycle⟩ :=
    welcome_parsedIntegerMatrixReadLineFourCycleStep (state.peRegisters pe)
      (stateForwardingSlots state pe)
      (state.matrixRegisters context.group context.l2b context.l1b) base control
      directiveEq' bar0Zero' bar1Zero'
  unfold executeIntegerProducerLineAtPECore at executed
  dsimp only at executed
  rw [welcome_filter_stageInput base] at executed
  rw [fourCycle] at executed
  dsimp only at executed
  rw [executeParsedFloatMAUsAtPE_noforward
    (floatEmpty := by simp [welcomeExpr_notFloatMAUProducer])] at executed
  dsimp only at executed
  generalize h : updateSupportedPELineForwarding (stateForwardingSlots state pe)
      (fun unit cycle =>
        if (decide (unit = Forwarding.Unit.mau) && false) = true then
          Forwarding.Value.known (⟨0, 0⟩ : IntegerALU.Bus)
        else nextSlots unit cycle)
      ([(welcomeExpr base).toParsed].any (fun expression =>
        match expression.op with
        | .noforward => true
        | _ => false))
      ([(welcomeExpr base).toParsed].any parsedExprIsIntegerProducer)
      false
      ([(welcomeExpr base).toParsed].any parsedExprIsMatrixReadProducer) = result at executed
  cases result with
  | failure => exact absurd h (updateSupportedPELineForwarding_ne_failure _ _ _ _ _ _)
  | unknown => exact absurd h (updateSupportedPELineForwarding_never_unknown _ _ _ _ _ _)
  | ok forwarding =>
      simp only [StepResult.ok.injEq] at executed
      subst executed
      refine ⟨rfl, ?_, ?_, ?_⟩
      · intro other different
        simp [different]
      · simp [List.foldl, welcome_floatBAR_false]
      · simp [List.foldl, welcome_floatBAR_false]


/-- The BAR-writer guard of the Welcome line is false. -/
theorem welcome_any_barWriter (base : Nat) :
    [(welcomeExpr base).toParsed].any parsedExprIsIntegerBARWriter = false := by
  simp [welcomeExpr_notBARWriter]

/-- The per-PE step of a Welcome line succeeds. -/
theorem welcome_executeIntegerProducerLineAtPE_success
    (base : Nat) (state : State) (pe : PEId)
    (directiveEq : state.maskDirective = welcomeMaskDirective)
    (bar0Zero : (state.peContext pe).bar0 = 0)
    (bar1Zero : (state.peContext pe).bar1 = 0) :
    ∃ next, executeIntegerProducerLineAtPE [(welcomeExpr base).toParsed] state pe =
      .ok next := by
  obtain ⟨next, executed⟩ :=
    welcome_executeIntegerProducerLineAtPECore_success base state pe
      directiveEq bar0Zero bar1Zero
  refine ⟨next, ?_⟩
  unfold executeIntegerProducerLineAtPE
  rw [welcome_any_barWriter base]
  simp [executed]

/-- The per-PE step of a Welcome line installs the committed writes at `pe`. -/
theorem welcome_executeIntegerProducerLineAtPE_peRegisters
    (base : Nat) (state next : State) (pe : PEId)
    (directiveEq : state.maskDirective = welcomeMaskDirective)
    (bar0Zero : (state.peContext pe).bar0 = 0)
    (bar1Zero : (state.peContext pe).bar1 = 0)
    (executed : executeIntegerProducerLineAtPE [(welcomeExpr base).toParsed]
      state pe = .ok next) :
    next.peRegisters = fun other =>
      if other = pe then
        commitParsedMaskedWrites (state.peRegisters pe)
          [welcomePreparedWrite (state.peRegisters pe) base 0,
           welcomePreparedWrite (state.peRegisters pe) base 1,
           welcomePreparedWrite (state.peRegisters pe) base 2,
           welcomePreparedWrite (state.peRegisters pe) base 3]
      else state.peRegisters other := by
  unfold executeIntegerProducerLineAtPE at executed
  rw [welcome_any_barWriter base] at executed
  simp at executed
  exact welcome_executeIntegerProducerLineAtPECore_peRegisters base state next pe
    directiveEq bar0Zero bar1Zero executed

/-- The per-PE step of a Welcome line preserves the mask directive and the
zero BAR context. -/
theorem welcome_executeIntegerProducerLineAtPE_context
    (base : Nat) (state next : State) (pe : PEId)
    (directiveEq : state.maskDirective = welcomeMaskDirective)
    (bar0Zero : (state.peContext pe).bar0 = 0)
    (bar1Zero : (state.peContext pe).bar1 = 0)
    (executed : executeIntegerProducerLineAtPE [(welcomeExpr base).toParsed]
      state pe = .ok next) :
    next.maskDirective = state.maskDirective ∧
      (∀ other, other ≠ pe → next.peContext other = state.peContext other) ∧
      (next.peContext pe).bar0 = (state.peContext pe).bar0 ∧
      (next.peContext pe).bar1 = (state.peContext pe).bar1 := by
  unfold executeIntegerProducerLineAtPE at executed
  rw [welcome_any_barWriter base] at executed
  simp at executed
  exact welcome_executeIntegerProducerLineAtPECore_context base state next pe
    directiveEq bar0Zero bar1Zero executed

/-- The state invariant of the Welcome run: the simulator mask directive and a
zero BAR context at every PE. -/
def WelcomeStateInvariant (state : State) : Prop :=
  state.maskDirective = welcomeMaskDirective ∧
    ∀ pe, (state.peContext pe).bar0 = 0 ∧ (state.peContext pe).bar1 = 0

/-- One Welcome per-PE step preserves the invariant. -/
theorem welcome_executeIntegerProducerLineAtPE_invariant
    (base : Nat) (state : State) (pe : PEId)
    (invariant : WelcomeStateInvariant state) :
    ∃ next, executeIntegerProducerLineAtPE [(welcomeExpr base).toParsed]
      state pe = .ok next ∧ WelcomeStateInvariant next := by
  obtain ⟨next, executed⟩ :=
    welcome_executeIntegerProducerLineAtPE_success base state pe invariant.1
      (invariant.2 pe).1 (invariant.2 pe).2
  obtain ⟨directive, others, bar0, bar1⟩ :=
    welcome_executeIntegerProducerLineAtPE_context base state next pe invariant.1
      (invariant.2 pe).1 (invariant.2 pe).2 executed
  refine ⟨next, executed, ?_, ?_⟩
  · rw [directive, invariant.1]
  · intro other
    by_cases same : other = pe
    · rw [same]
      exact ⟨bar0.trans (invariant.2 pe).1, bar1.trans (invariant.2 pe).2⟩
    · rw [others other same]
      exact invariant.2 other

/-- The full per-PE walk over a PE list succeeds and preserves the invariant. -/
theorem welcome_executeIntegerProducerLineAtPEs_invariant
    (base : Nat) (pes : List PEId) (state : State)
    (invariant : WelcomeStateInvariant state) :
    ∃ next, executeIntegerProducerLineAtPEs [(welcomeExpr base).toParsed]
      pes state = .ok next ∧ WelcomeStateInvariant next := by
  induction pes generalizing state with
  | nil => exact ⟨state, rfl, invariant⟩
  | cons pe rest ih =>
      obtain ⟨middle, headExecuted, headInvariant⟩ :=
        welcome_executeIntegerProducerLineAtPE_invariant base state pe invariant
      obtain ⟨next, tailExecuted, tailInvariant⟩ := ih middle headInvariant
      refine ⟨next, ?_, tailInvariant⟩
      simp only [executeIntegerProducerLineAtPEs, headExecuted, tailExecuted]

/-- Walking over a PE list that does not contain `p` preserves `p`'s register
file. -/
theorem executeIntegerProducerLineAtPEs_peRegisters_not_mem
    (expressions : List ParsedExpr) (pes : List PEId) (state next : State)
    (executed : executeIntegerProducerLineAtPEs expressions pes state = .ok next)
    (frame : ∀ pe p (s n : State), executeIntegerProducerLineAtPE expressions s pe = .ok n →
      p ≠ pe → n.peRegisters p = s.peRegisters p)
    (p : PEId) (notMem : p ∉ pes) :
    next.peRegisters p = state.peRegisters p := by
  induction pes generalizing state with
  | nil =>
      simp [executeIntegerProducerLineAtPEs] at executed
      subst executed
      rfl
  | cons pe rest ih =>
      simp only [List.mem_cons, not_or] at notMem
      obtain ⟨different, restNotMem⟩ := notMem
      simp only [executeIntegerProducerLineAtPEs] at executed
      split at executed
      · cases executed
      · cases executed
      · rename_i middle headExecuted
        rw [ih middle executed restNotMem, frame pe p state middle headExecuted different]

/-- Walking over a duplicate-free PE list that contains `p` finalizes `p`'s
register file by the per-step commit. -/
theorem executeIntegerProducerLineAtPEs_peRegisters_mem
    (expressions : List ParsedExpr) (pes : List PEId) (state next : State)
    (commit : IntegerRegisterFiles → IntegerRegisterFiles)
    (executed : executeIntegerProducerLineAtPEs expressions pes state = .ok next)
    (nodup : pes.Nodup)
    (frame : ∀ pe p (s n : State), executeIntegerProducerLineAtPE expressions s pe = .ok n →
      p ≠ pe → n.peRegisters p = s.peRegisters p)
    (value : ∀ pe (s n : State), executeIntegerProducerLineAtPE expressions s pe = .ok n →
      n.peRegisters pe = commit (s.peRegisters pe))
    (p : PEId) (mem : p ∈ pes) :
    next.peRegisters p = commit (state.peRegisters p) := by
  induction pes generalizing state with
  | nil => simp at mem
  | cons pe rest ih =>
      obtain ⟨peNotRest, restNodup⟩ := List.nodup_cons.mp nodup
      simp only [executeIntegerProducerLineAtPEs] at executed
      split at executed
      · cases executed
      · cases executed
      · rename_i middle headExecuted
        by_cases same : p = pe
        · rw [same]
          rw [executeIntegerProducerLineAtPEs_peRegisters_not_mem expressions rest middle next
            executed frame pe peNotRest, value pe state middle headExecuted]
        · have pMem : p ∈ rest := by
            rcases List.mem_cons.mp mem with h | h
            · exact False.elim (same h)
            · exact h
          rw [ih middle executed restNodup pMem, frame pe p state middle headExecuted same]


/-- The Welcome line passes the source-level issue checker at both bases. -/
theorem welcome_issueLegal (base : Nat) :
    LegalParsedLine [(welcomeExpr base).toParsed] := by
  unfold LegalParsedLine projectLine projectFrom ParsedExpr.toIssueExpr
    ParsedExpr.issueGroup ParsedExpr.issueMau ParsedOperand.accesses
    ParsedOperand.matrixUseCount ParsedExpr.hasTurnaround
    ParsedExpr.maskApplications ParsedOperand.writeMask?
    ParsedExpr.maskRegisterWrites ParsedOperand.maskRegisterWrite?
    ParsedExpr.barWrites ParsedOperand.barWriteBank?
    ParsedExpr.writesLbf ParsedExpr.nowriteOutputValid
  simp [welcomeExpr_toParsed, Issue.plusOneParsedAt, Issue.plusOneReadAt,
    Issue.plusOneWriteAt, Issue.plusOneAccess,
    Legal, idsUnique, groupsUnique, mauCountBounded, mauExpressions,
    mauPrecisionsAgree, matrixWritePairAgrees, matrixRegistersUnique,
    writesUnique, Expr.writeBanks, barWritesExcludeReads, readsAgree,
    localReadWriteAgree, immediateExcludesLm0,
    zeroFlushUnique, maskWidthsAgree, maskEntriesAgree, nowriteOutputsUnique,
    lbfWritesUnique, maskRegisterWritesUnique,
    projectFrom]

theorem welcome_checkParsedTopLine (base : Nat) :
    checkParsedTopLine (InstructionLine.pe [welcomeExpr base]).toParsed = true :=
  Issue.parsed_topline_check_complete _
    (welcome_issueLegal base)


/-- The full normalized-line transition of one Welcome line succeeds. -/
theorem welcome_executeIntegerProducerInstructionLine_success
    (base : Nat) (state : State) (invariant : WelcomeStateInvariant state) :
    ∃ next,
      executeIntegerProducerInstructionLine (.pe [(welcomeExpr base)]) state = .ok next ∧
      WelcomeStateInvariant next := by
  obtain ⟨nextPEs, walkExecuted, walkInvariant⟩ :=
    welcome_executeIntegerProducerLineAtPEs_invariant base (List.finRange 4096) state invariant
  let expressions := [(welcomeExpr base)].map NormalizedExpr.toParsed
  have filterStage : expressions.filter parsedExprIsIntegerMatrixReadStageInput = expressions :=
    List.filter_eq_self.mpr fun expression member => by
      simp only [expressions, List.mem_map, List.mem_singleton] at member
      obtain ⟨original, rfl, rfl⟩ := member
      exact welcomeExpr_isMatrixReadStageInput base
  have filterPE : expressions.filter (fun expression =>
      !parsedExprIsL2BMProducer expression && !parsedExprIsMslMsrProducer expression &&
        !parsedExprIsMatrixMAUProducer expression &&
        !parsedExprIsBlockFloatProducer expression &&
        !parsedExprIsFloatReluProducer expression) = expressions :=
    List.filter_eq_self.mpr fun expression member => by
      simp only [expressions, List.mem_map, List.mem_singleton] at member
      obtain ⟨original, rfl, rfl⟩ := member
      simp [welcomeExpr_noL2BMProducer, welcomeExpr_noMslMsrProducer,
        welcomeExpr_noMatrixMAUProducer, welcomeExpr_noBlockFloatProducer,
        welcomeExpr_noFloatReluProducer]
  have floatEmpty : expressions.filter parsedExprIsSupportedFloatMAUProducer = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro expression member
    simp only [expressions, List.mem_map, List.mem_singleton] at member
    obtain ⟨original, rfl, rfl⟩ := member
    simp [welcomeExpr_notFloatMAUProducer]
  have msl : ∀ (currentState : State) (noForward hasSingleLineMask : Bool),
      executeParsedMslMsrProducers state currentState
        ([(welcomeExpr base)].map NormalizedExpr.toParsed) noForward
        hasSingleLineMask = .ok currentState :=
    fun currentState noForward hasSingleLineMask =>
      executeParsedMslMsrProducers_nil state currentState expressions noForward
        hasSingleLineMask (by
          apply List.filter_eq_nil_iff.mpr
          intro expression member
          simp only [expressions, List.mem_map, List.mem_singleton] at member
          obtain ⟨original, rfl, rfl⟩ := member
          simp [welcomeExpr_noMslMsrProducer])
  have relu : ∀ (currentState : State) (noForward hasSingleLineMask : Bool),
      executeParsedFloatReluProducers state currentState
        ([(welcomeExpr base)].map NormalizedExpr.toParsed) noForward
        hasSingleLineMask = .ok currentState :=
    fun currentState noForward hasSingleLineMask =>
      executeParsedFloatReluProducers_nil state currentState expressions noForward
        hasSingleLineMask (by
          apply List.filter_eq_nil_iff.mpr
          intro expression member
          simp only [expressions, List.mem_map, List.mem_singleton] at member
          obtain ⟨original, rfl, rfl⟩ := member
          simp [welcomeExpr_noFloatReluProducer])
  have block : ∀ (currentState : State) (noForward hasSingleLineMask : Bool),
      executeParsedBlockFloatProducer state currentState
        ([(welcomeExpr base)].map NormalizedExpr.toParsed) noForward
        hasSingleLineMask = .ok currentState :=
    fun currentState noForward hasSingleLineMask =>
      executeParsedBlockFloatProducer_nil state currentState expressions noForward
        hasSingleLineMask (by
          apply List.filter_eq_nil_iff.mpr
          intro expression member
          simp only [expressions, List.mem_map, List.mem_singleton] at member
          obtain ⟨original, rfl, rfl⟩ := member
          simp [welcomeExpr_noBlockFloatProducer])
  have matrix : ∀ (currentState : State) (noForward hasSingleLineMask : Bool),
      executeParsedMatrixMAUAndWrites state currentState
        ([(welcomeExpr base)].map NormalizedExpr.toParsed) noForward
        hasSingleLineMask = .ok currentState :=
    fun currentState noForward hasSingleLineMask =>
      executeParsedMatrixMAUAndWrites_id state currentState expressions noForward
        hasSingleLineMask
        (by
          apply List.filter_eq_nil_iff.mpr
          intro expression member
          simp only [expressions, List.mem_map, List.mem_singleton] at member
          obtain ⟨original, rfl, rfl⟩ := member
          simp [welcomeExpr_noMatrixMAUProducer])
        (by
          simp [expressions, parsedExprIsMatrixWriteProducer, welcomeExpr_toParsed,
            Issue.plusOneParsedAt])
  have shared : ∀ (currentState : State) (updateTurnaround : Bool),
      executeParsedSharedBlockProducers state currentState
        ([(welcomeExpr base)].map NormalizedExpr.toParsed)
        updateTurnaround = .ok currentState :=
    fun currentState updateTurnaround =>
      executeParsedSharedBlockProducers_integer state currentState expressions
        updateTurnaround (by
          simp [expressions, welcomeExpr_integerProducer])
  have l1ToPE : ∀ (currentState : State) (noForward hasSingleLineMask usePreIssueMask : Bool),
      executeParsedL1ToPEProducers state currentState
        ([(welcomeExpr base)].map NormalizedExpr.toParsed) noForward
        hasSingleLineMask usePreIssueMask = .ok currentState :=
    fun currentState noForward hasSingleLineMask usePreIssueMask =>
      executeParsedL1ToPEProducers_nil state currentState expressions noForward
        hasSingleLineMask usePreIssueMask (by
          apply List.filter_eq_nil_iff.mpr
          intro expression member
          simp only [expressions, List.mem_map, List.mem_singleton] at member
          obtain ⟨original, rfl, rfl⟩ := member
          simp [parsedExprIsL1ToPEProducer, welcomeExpr_toParsed,
            Issue.plusOneParsedAt])
  have waits : ([(welcomeExpr base)].map NormalizedExpr.toParsed).any
      (parsedExprWaitPending state) = false :=
    welcomeExpr_waitPending_false base state
  have unsupported : ([(welcomeExpr base)].map NormalizedExpr.toParsed).any
      parsedExprIsUnsupportedRustAlu = false :=
    welcomeExpr_notUnsupportedRustAlu base
  have supported : ([(welcomeExpr base)].map NormalizedExpr.toParsed).all
      parsedExprIsSupportedPELineProducer = true :=
    welcomeExpr_supportedPELineProducer base
  have filterMap : List.filter (fun expression =>
      !parsedExprIsL2BMProducer expression && !parsedExprIsMslMsrProducer expression &&
        !parsedExprIsMatrixMAUProducer expression &&
        !parsedExprIsBlockFloatProducer expression &&
        !parsedExprIsFloatReluProducer expression)
      ([(welcomeExpr base)].map NormalizedExpr.toParsed) =
      [(welcomeExpr base)].map NormalizedExpr.toParsed := by
    simpa [expressions] using filterPE
  have walk : executeIntegerProducerLineAtPEs
      ([(welcomeExpr base)].map NormalizedExpr.toParsed) (List.finRange 4096) state =
      .ok nextPEs := walkExecuted
  unfold executeIntegerProducerInstructionLine
  rw [welcome_checkParsedTopLine base]
  dsimp only
  simp only [waits, unsupported, supported, Bool.not_true, Bool.not_false,
    Bool.false_eq_true, if_false, if_true]
  rw [filterMap, walk]
  dsimp only
  simp only [msl, relu, block, matrix, shared, l1ToPE]
  refine ⟨_, rfl, ?_⟩
  simpa [WelcomeStateInvariant] using walkInvariant


/-- Walking over a PE list not containing `p` preserves `p`'s register file,
carrying the Welcome invariant. -/
theorem executeIntegerProducerLineAtPEs_peRegisters_not_mem_invariant
    (expressions : List ParsedExpr) (pes : List PEId) (state next : State)
    (invariant : WelcomeStateInvariant state)
    (executed : executeIntegerProducerLineAtPEs expressions pes state = .ok next)
    (preserves : ∀ pe (s n : State), WelcomeStateInvariant s →
      executeIntegerProducerLineAtPE expressions s pe = .ok n → WelcomeStateInvariant n)
    (frame : ∀ pe p (s n : State), WelcomeStateInvariant s →
      executeIntegerProducerLineAtPE expressions s pe = .ok n →
      p ≠ pe → n.peRegisters p = s.peRegisters p)
    (p : PEId) (notMem : p ∉ pes) :
    next.peRegisters p = state.peRegisters p ∧ WelcomeStateInvariant next := by
  induction pes generalizing state with
  | nil =>
      simp [executeIntegerProducerLineAtPEs] at executed
      subst executed
      exact ⟨rfl, invariant⟩
  | cons pe rest ih =>
      simp only [List.mem_cons, not_or] at notMem
      obtain ⟨different, restNotMem⟩ := notMem
      simp only [executeIntegerProducerLineAtPEs] at executed
      split at executed
      · cases executed
      · cases executed
      · rename_i middle headExecuted
        have headInvariant := preserves pe state middle invariant headExecuted
        have headFrame := frame pe p state middle invariant headExecuted different
        obtain ⟨tailFrame, tailInvariant⟩ :=
          ih middle headInvariant executed restNotMem
        exact ⟨tailFrame.trans headFrame, tailInvariant⟩

/-- Walking over a duplicate-free PE list containing `p` finalizes `p`'s
register file by the per-step commit, carrying the Welcome invariant. -/
theorem executeIntegerProducerLineAtPEs_peRegisters_mem_invariant
    (expressions : List ParsedExpr) (pes : List PEId) (state next : State)
    (commit : IntegerRegisterFiles → IntegerRegisterFiles)
    (invariant : WelcomeStateInvariant state)
    (executed : executeIntegerProducerLineAtPEs expressions pes state = .ok next)
    (nodup : pes.Nodup)
    (preserves : ∀ pe (s n : State), WelcomeStateInvariant s →
      executeIntegerProducerLineAtPE expressions s pe = .ok n → WelcomeStateInvariant n)
    (frame : ∀ pe p (s n : State), WelcomeStateInvariant s →
      executeIntegerProducerLineAtPE expressions s pe = .ok n →
      p ≠ pe → n.peRegisters p = s.peRegisters p)
    (value : ∀ pe (s n : State), WelcomeStateInvariant s →
      executeIntegerProducerLineAtPE expressions s pe = .ok n →
      n.peRegisters pe = commit (s.peRegisters pe))
    (p : PEId) (mem : p ∈ pes) :
    next.peRegisters p = commit (state.peRegisters p) := by
  induction pes generalizing state with
  | nil => simp at mem
  | cons pe rest ih =>
      obtain ⟨peNotRest, restNodup⟩ := List.nodup_cons.mp nodup
      simp only [executeIntegerProducerLineAtPEs] at executed
      split at executed
      · cases executed
      · cases executed
      · rename_i middle headExecuted
        have headInvariant := preserves pe state middle invariant headExecuted
        by_cases same : p = pe
        · rw [same]
          have headValue := value pe state middle invariant headExecuted
          obtain ⟨tailFrame, _⟩ :=
            executeIntegerProducerLineAtPEs_peRegisters_not_mem_invariant expressions rest
              middle next headInvariant executed preserves frame pe peNotRest
          rw [tailFrame, headValue]
        · have pMem : p ∈ rest := by
            rcases List.mem_cons.mp mem with h | h
            · exact False.elim (same h)
            · exact h
          have headFrame := frame pe p state middle invariant headExecuted same
          rw [ih middle headInvariant executed restNodup pMem, headFrame]


/-- The full normalized-line transition of one Welcome line installs the
committed increment writes at every PE. -/
theorem welcome_executeIntegerProducerInstructionLine_peRegisters
    (base : Nat) (state next : State) (invariant : WelcomeStateInvariant state)
    (executed : executeIntegerProducerInstructionLine (.pe [(welcomeExpr base)])
      state = .ok next) :
    ∀ p : PEId,
      next.peRegisters p =
        commitParsedMaskedWrites (state.peRegisters p)
          [welcomePreparedWrite (state.peRegisters p) base 0,
           welcomePreparedWrite (state.peRegisters p) base 1,
           welcomePreparedWrite (state.peRegisters p) base 2,
           welcomePreparedWrite (state.peRegisters p) base 3] := by
  obtain ⟨nextPEs, walkExecuted, walkInvariant⟩ :=
    welcome_executeIntegerProducerLineAtPEs_invariant base (List.finRange 4096) state invariant
  let expressions := [(welcomeExpr base)].map NormalizedExpr.toParsed
  have filterPE : expressions.filter (fun expression =>
      !parsedExprIsL2BMProducer expression && !parsedExprIsMslMsrProducer expression &&
        !parsedExprIsMatrixMAUProducer expression &&
        !parsedExprIsBlockFloatProducer expression &&
        !parsedExprIsFloatReluProducer expression) = expressions :=
    List.filter_eq_self.mpr fun expression member => by
      simp only [expressions, List.mem_map, List.mem_singleton] at member
      obtain ⟨original, rfl, rfl⟩ := member
      simp [welcomeExpr_noL2BMProducer, welcomeExpr_noMslMsrProducer,
        welcomeExpr_noMatrixMAUProducer, welcomeExpr_noBlockFloatProducer,
        welcomeExpr_noFloatReluProducer]
  have waits : ([(welcomeExpr base)].map NormalizedExpr.toParsed).any
      (parsedExprWaitPending state) = false :=
    welcomeExpr_waitPending_false base state
  have unsupported : ([(welcomeExpr base)].map NormalizedExpr.toParsed).any
      parsedExprIsUnsupportedRustAlu = false :=
    welcomeExpr_notUnsupportedRustAlu base
  have supported : ([(welcomeExpr base)].map NormalizedExpr.toParsed).all
      parsedExprIsSupportedPELineProducer = true :=
    welcomeExpr_supportedPELineProducer base
  have filterMap : List.filter (fun expression =>
      !parsedExprIsL2BMProducer expression && !parsedExprIsMslMsrProducer expression &&
        !parsedExprIsMatrixMAUProducer expression &&
        !parsedExprIsBlockFloatProducer expression &&
        !parsedExprIsFloatReluProducer expression)
      ([(welcomeExpr base)].map NormalizedExpr.toParsed) =
      [(welcomeExpr base)].map NormalizedExpr.toParsed := by
    simpa [expressions] using filterPE
  have msl : ∀ (currentState : State) (noForward hasSingleLineMask : Bool),
      executeParsedMslMsrProducers state currentState
        ([(welcomeExpr base)].map NormalizedExpr.toParsed) noForward
        hasSingleLineMask = .ok currentState :=
    fun currentState noForward hasSingleLineMask =>
      executeParsedMslMsrProducers_nil state currentState expressions noForward
        hasSingleLineMask (by
          apply List.filter_eq_nil_iff.mpr
          intro expression member
          simp only [expressions, List.mem_map, List.mem_singleton] at member
          obtain ⟨original, rfl, rfl⟩ := member
          simp [welcomeExpr_noMslMsrProducer])
  have relu : ∀ (currentState : State) (noForward hasSingleLineMask : Bool),
      executeParsedFloatReluProducers state currentState
        ([(welcomeExpr base)].map NormalizedExpr.toParsed) noForward
        hasSingleLineMask = .ok currentState :=
    fun currentState noForward hasSingleLineMask =>
      executeParsedFloatReluProducers_nil state currentState expressions noForward
        hasSingleLineMask (by
          apply List.filter_eq_nil_iff.mpr
          intro expression member
          simp only [expressions, List.mem_map, List.mem_singleton] at member
          obtain ⟨original, rfl, rfl⟩ := member
          simp [welcomeExpr_noFloatReluProducer])
  have block : ∀ (currentState : State) (noForward hasSingleLineMask : Bool),
      executeParsedBlockFloatProducer state currentState
        ([(welcomeExpr base)].map NormalizedExpr.toParsed) noForward
        hasSingleLineMask = .ok currentState :=
    fun currentState noForward hasSingleLineMask =>
      executeParsedBlockFloatProducer_nil state currentState expressions noForward
        hasSingleLineMask (by
          apply List.filter_eq_nil_iff.mpr
          intro expression member
          simp only [expressions, List.mem_map, List.mem_singleton] at member
          obtain ⟨original, rfl, rfl⟩ := member
          simp [welcomeExpr_noBlockFloatProducer])
  have matrix : ∀ (currentState : State) (noForward hasSingleLineMask : Bool),
      executeParsedMatrixMAUAndWrites state currentState
        ([(welcomeExpr base)].map NormalizedExpr.toParsed) noForward
        hasSingleLineMask = .ok currentState :=
    fun currentState noForward hasSingleLineMask =>
      executeParsedMatrixMAUAndWrites_id state currentState expressions noForward
        hasSingleLineMask
        (by
          apply List.filter_eq_nil_iff.mpr
          intro expression member
          simp only [expressions, List.mem_map, List.mem_singleton] at member
          obtain ⟨original, rfl, rfl⟩ := member
          simp [welcomeExpr_noMatrixMAUProducer])
        (by
          simp [expressions, parsedExprIsMatrixWriteProducer, welcomeExpr_toParsed,
            Issue.plusOneParsedAt])
  have shared : ∀ (currentState : State) (updateTurnaround : Bool),
      executeParsedSharedBlockProducers state currentState
        ([(welcomeExpr base)].map NormalizedExpr.toParsed)
        updateTurnaround = .ok currentState :=
    fun currentState updateTurnaround =>
      executeParsedSharedBlockProducers_integer state currentState expressions
        updateTurnaround (by
          simp [expressions, welcomeExpr_integerProducer])
  have l1ToPE : ∀ (currentState : State) (noForward hasSingleLineMask usePreIssueMask : Bool),
      executeParsedL1ToPEProducers state currentState
        ([(welcomeExpr base)].map NormalizedExpr.toParsed) noForward
        hasSingleLineMask usePreIssueMask = .ok currentState :=
    fun currentState noForward hasSingleLineMask usePreIssueMask =>
      executeParsedL1ToPEProducers_nil state currentState expressions noForward
        hasSingleLineMask usePreIssueMask (by
          apply List.filter_eq_nil_iff.mpr
          intro expression member
          simp only [expressions, List.mem_map, List.mem_singleton] at member
          obtain ⟨original, rfl, rfl⟩ := member
          simp [parsedExprIsL1ToPEProducer, welcomeExpr_toParsed,
            Issue.plusOneParsedAt])
  have walkMap : executeIntegerProducerLineAtPEs
      ([(welcomeExpr base)].map NormalizedExpr.toParsed) (List.finRange 4096) state =
      .ok nextPEs := walkExecuted
  unfold executeIntegerProducerInstructionLine at executed
  rw [welcome_checkParsedTopLine base] at executed
  dsimp only at executed
  simp only [waits, unsupported, supported, Bool.not_true, Bool.not_false,
    Bool.false_eq_true, ite_false, ite_true] at executed
  rw [filterMap, walkMap] at executed
  dsimp only at executed
  simp only [msl, relu, block, matrix, shared, l1ToPE] at executed
  simp only [StepResult.ok.injEq] at executed
  subst executed
  intro p
  exact executeIntegerProducerLineAtPEs_peRegisters_mem_invariant
    ([(welcomeExpr base)].map NormalizedExpr.toParsed) (List.finRange 4096) state nextPEs
    (fun files => commitParsedMaskedWrites files
      [welcomePreparedWrite files base 0, welcomePreparedWrite files base 1,
       welcomePreparedWrite files base 2, welcomePreparedWrite files base 3])
    invariant walkExecuted (List.nodup_finRange 4096)
    (by
      intro pe s n hs he
      obtain ⟨n', he', hinv⟩ :=
        welcome_executeIntegerProducerLineAtPE_invariant base s pe hs
      have same : n = n' := by
        have h := he.symm.trans he'
        injection h
      subst same
      exact hinv)
    (by
      intro pe other s n hs he different
      have hframe := welcome_executeIntegerProducerLineAtPE_peRegisters base s n pe
        hs.1 (hs.2 pe).1 (hs.2 pe).2 he
      rw [hframe]
      simp [different])
    (by
      intro pe s n hs he
      have hvalue := welcome_executeIntegerProducerLineAtPE_peRegisters base s n pe
        hs.1 (hs.2 pe).1 (hs.2 pe).2 he
      rw [hvalue]
      simp)
    p (List.mem_finRange p)


/-- The LM0 source operand of a Welcome line produces only read events on LM0. -/
theorem welcomeReadEvents (base : Nat) (control : ParsedMaskExecutionControl) :
    ∃ events, ParsedOperand.toTimedPEHazardEvents? (Issue.plusOneReadAt base)
      false control = some events ∧
      ∀ e ∈ events, e.write = false ∧ e.access.bank = .lm0 := by
  unfold ParsedOperand.toTimedPEHazardEvents?
  simp [Issue.plusOneReadAt, Issue.plusOneAccess, issueBankToRegisterBank,
    ParsedOperand.forHazardAddress, parsedHazardCycles,
    ParsedOperand.toDirectMemoryAccessMode?, parsedRegionAddressAt, parsedWidth?,
    TimedPEAccess.ofControl]

/-- The LM1 destination operand of a Welcome line produces only write events
on LM1. -/
theorem welcomeWriteEvents (base : Nat) (control : ParsedMaskExecutionControl) :
    ∃ events, ParsedOperand.toTimedPEHazardEvents? (Issue.plusOneWriteAt base)
      true control = some events ∧
      ∀ e ∈ events, e.write = true ∧ e.access.bank = .lm1 := by
  unfold ParsedOperand.toTimedPEHazardEvents?
  simp [Issue.plusOneWriteAt, Issue.plusOneAccess, issueBankToRegisterBank,
    ParsedOperand.forHazardAddress, parsedHazardCycles,
    ParsedOperand.toDirectMemoryAccessMode?, parsedRegionAddressAt, parsedWidth?,
    TimedPEAccess.ofControl, parsedHazardPatternEnables]

/-- The per-expression hazard events of a Welcome line: writes are LM1, reads
are LM0. -/
theorem welcomeExprEvents (base : Nat) (control : ParsedMaskExecutionControl) :
    ∃ events,
      ParsedExpr.toTimedPEHazardEvents? (welcomeExpr base).toParsed control = some events ∧
      (∀ e ∈ events, e.write = true → e.access.bank = .lm1) ∧
      (∀ e ∈ events, e.write = false → e.access.bank = .lm0) := by
  obtain ⟨reads, hreads, readProp⟩ := welcomeReadEvents base control
  obtain ⟨writes, hwrites, writeProp⟩ := welcomeWriteEvents base control
  refine ⟨reads ++ writes, ?_, ?_, ?_⟩
  · unfold ParsedExpr.toTimedPEHazardEvents?
    rw [welcomeExpr_toParsed]
    simp only [Issue.plusOneParsedAt]
    simp [hreads, hwrites]
  · intro e member writeTrue
    rcases List.mem_append.mp member with h | h
    · rw [(readProp e h).1] at writeTrue
      cases writeTrue
    · exact (writeProp e h).2
  · intro e member writeFalse
    rcases List.mem_append.mp member with h | h
    · exact (readProp e h).2
    · rw [(writeProp e h).1] at writeFalse
      cases writeFalse

/-- No PE hazard constraint exists between two Welcome-line event lists: the
only constrained direction is a write before a read, and Welcome writes LM1
while it reads LM0. -/
theorem welcome_no_peHazard (earlier later : List TimedPEAccess)
    (earlierWrites : ∀ e ∈ earlier, e.write = true → e.access.bank = .lm1)
    (laterReads : ∀ e ∈ later, e.write = false → e.access.bank = .lm0) :
    peHazardConstraintsBetween earlier later = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro constraint member
  rw [pe_hazard_constraints_between_complete] at member
  obtain ⟨write, writeMem, access, accessMem, made⟩ := member
  have noneEq : makePEHazardConstraint? write access = none := by
    by_cases writeTrue : write.write
    · by_cases accessTrue : access.write
      · simp [makePEHazardConstraint?, peHazardRequirement?, writeTrue, accessTrue]
      · have accessFalse : access.write = false := by
          cases h : access.write <;> simp_all
        have writeBank := earlierWrites write writeMem writeTrue
        have accessBank := laterReads access accessMem accessFalse
        simp [makePEHazardConstraint?, peHazardRequirement?, writeTrue, accessFalse,
          writeBank, accessBank]
    · simp [makePEHazardConstraint?, peHazardRequirement?, writeTrue]
  rw [noneEq] at made
  cases made

/-- The block hazard events of a Welcome line are empty: it accesses only PE
LM0/LM1, not L1BM or L2BM. -/
theorem welcome_blockEvents (base : Nat) (startWord : Nat) :
    HazardTrace.parsedLineBlockHazardEvents
      (InstructionLine.pe [welcomeExpr base]).toParsed startWord = [] := by
  simp [HazardTrace.parsedLineBlockHazardEvents, InstructionLine.toParsed,
    welcomeExpr_toParsed, Issue.plusOneParsedAt, HazardTrace.l1ExprHazardEvents]

/-- A read-after-read/write-before-read history with no constrained pairs has
no PE hazard violations. -/
theorem welcome_no_peHazardViolated (history : List TimedPEAccess)
    (later : List TimedPEAccess)
    (earlierWrites : ∀ e ∈ history, e.write = true → e.access.bank = .lm1)
    (laterReads : ∀ e ∈ later, e.write = false → e.access.bank = .lm0) :
    parsedPEHazardViolated history later = false := by
  unfold parsedPEHazardViolated
  rw [welcome_no_peHazard history later earlierWrites laterReads]
  simp



/-- The first bus word of a Welcome write is the increment of the LM0 word at
the long-word start. -/
theorem welcomePreparedWrite_data_zero (files : IntegerRegisterFiles)
    (base : Nat) (cycle : Fin 4) :
    (welcomePreparedWrite files base cycle).data 0 =
      ProofsLean.MNCore.PlusOne.increment
        (files.lm0 (welcomeSourceAddress base cycle)) := by
  unfold welcomePreparedWrite welcomeSourceAccess
  simp only [unpackALUBus, Fin.val_zero, ite_true]
  rw [parsed_iinc_output_eq_incrementPair,
    ProofsLean.MNCore.PlusOne.increment_pair_spec,
    BitVec.extractLsb'_append_eq_left]

/-- The second bus word of a Welcome write is the increment of the next LM0
word. -/
theorem welcomePreparedWrite_data_one (files : IntegerRegisterFiles)
    (base : Nat) (cycle : Fin 4) :
    (welcomePreparedWrite files base cycle).data 1 =
      ProofsLean.MNCore.PlusOne.increment
        (files.lm0 (advance .lm0 (welcomeSourceAddress base cycle) 1)) := by
  unfold welcomePreparedWrite welcomeSourceAccess
  simp (config := { decide := true }) only [unpackALUBus, Fin.val_zero, Fin.val_one,
    ite_true, ite_false, reduceIte]
  rw [parsed_iinc_output_eq_incrementPair,
    ProofsLean.MNCore.PlusOne.increment_pair_spec,
    BitVec.extractLsb'_append_eq_right]

/-- Reading a `.long` LM1 access at a word start returns the word at that
address. -/
theorem readDirectAccess_lm1_long_word (files : IntegerRegisterFiles)
    (start : Fin Bank.lm1.capacity) (index : Fin 4) (indexBound : index.val < 2) :
    readDirectAccess files ⟨.lm1, .long, start⟩ index =
      files.lm1 (advance .lm1 start index.val) := by
  simp [readDirectAccess, readRegisterBank, readWords, count, Width.words, indexBound]

end ProofsLean.MNCore
