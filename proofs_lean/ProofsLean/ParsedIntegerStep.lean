import ProofsLean.BusLayout
import ProofsLean.Issue
import ProofsLean.PlusOne
import ProofsLean.Masks
import ProofsLean.MaskedPEMemory
import ProofsLean.ControlNormalization
import ProofsLean.Forwarding

/-! A deliberately partial instruction fragment: direct PE-memory reads,
the parsed integer ALU request, and masked or unmasked memory writes. This
composes existing datapath pieces without claiming timing, hazards, or
ISA-wide operand legality. -/
namespace ProofsLean.MNCore.PEMemory

open ProofsLean.MNCore.Issue

structure IntegerRegisterFiles where
  lm0 : Memory .lm0
  lm1 : Memory .lm1
  grf0 : Memory .grf0
  grf1 : Memory .grf1
  t : Memory .t
  maskRegisters : ProofsLean.MNCore.Masks.RegisterFile

structure DirectMemoryAccess where
  bank : Bank
  width : Width
  address : Fin bank.capacity
  deriving DecidableEq, Repr

def issueBankToRegisterBank : ProofsLean.MNCore.Issue.Bank → Option Bank
  | .lm0 => some .lm0
  | .lm1 => some .lm1
  | .grf0 => some .grf0
  | .grf1 => some .grf1
  | .t => some .t
  | .l1bm | .l2bm | .pdm | .dram | .omr => none

def parsedRegionAddressAt (region : ProofsLean.MNCore.Issue.Region) (cycle : Fin 4) : Nat :=
  match cycle.val with
  | 0 => region.address0
  | 1 => region.address1
  | 2 => region.address2
  | _ => region.address3

def parsedWidth? (encoded : Nat) : Option Width :=
  match encoded with
  | 1 => some .word
  | 2 => some .long
  | 4 => some .double
  | _ => none

/-- Resolve the memory address fields of a parsed operand for one PE and cycle.
This intentionally rejects rounded inputs and banks outside the PE memories.
The surrounding caller still supplies current BAR and T values. -/
def ParsedOperand.toDirectMemoryAccessMode? (operand : ParsedOperand)
    (allowDestinationMask : Bool)
    (pe cycle : Fin 4) (bar0 bar1 : BitVec 12) (tWord : BitVec 32) :
    Option DirectMemoryAccess :=
  match operand with
  | .mem access negated extended rounded mask =>
      if negated || extended || rounded || (!allowDestinationMask && mask.isSome) then none else
      match issueBankToRegisterBank access.bank, parsedWidth? access.region.width with
      | some bank, some width =>
          if (access.region.tIndirect && bank != .lm0) ||
              (access.region.madpe.isSome && bank != .lm0 && bank != .lm1) then none
          else
            let cycleAddress := parsedRegionAddressAt access.region cycle
            let effective := if bank == .t then cycle.val * 4 else
              let bar := if bank == .lm0 then bar0.toNat
                else if bank == .lm1 then bar1.toNat else 0
              let indirect := if access.region.tIndirect then tWord.toNat else 0
              let madpe := match access.region.madpe with
                | some threshold => if pe.val ≤ threshold then width.words else 0
                | none => 0
              let raw := bar + indirect + cycleAddress + madpe
              (raw / width.words * width.words) % bank.capacity
            some ⟨bank, width, ⟨effective, by
              by_cases isT : bank = .t
              · subst bank
                simp [effective, Bank.capacity]
                have hc := cycle.isLt
                omega
              · simp [effective, isT]
                exact Nat.mod_lt _ (Bank.capacity_positive bank)⟩⟩
      | none, _ | _, none => none
  | _ => none

def ParsedOperand.toDirectMemoryAccess? (operand : ParsedOperand)
    (pe cycle : Fin 4) (bar0 bar1 : BitVec 12) (tWord : BitVec 32) :
    Option DirectMemoryAccess :=
  ParsedOperand.toDirectMemoryAccessMode? operand false pe cycle bar0 bar1 tWord

def ParsedOperand.toDirectMemoryDestination? (operand : ParsedOperand)
    (pe cycle : Fin 4) (bar0 bar1 : BitVec 12) (tWord : BitVec 32) :
    Option DirectMemoryAccess :=
  ParsedOperand.toDirectMemoryAccessMode? operand true pe cycle bar0 bar1 tWord

def ParsedOperand.toUnmaskedDirectDestination? (operand : ParsedOperand)
    (pe cycle : Fin 4) (bar0 bar1 : BitVec 12) (tWord : BitVec 32) :
    Option DirectMemoryAccess :=
  match operand with
  | .mem _ _ _ _ none =>
      ParsedOperand.toDirectMemoryAccess? operand pe cycle bar0 bar1 tWord
  | _ => none

def ParsedOperand.toMaskRegisterEntry? (operand : ParsedOperand) : Option (Fin 15) :=
  match operand with
  | .omr entry _ =>
      if h : 1 ≤ entry ∧ entry < 16 then some ⟨entry - 1, by omega⟩ else none
  | _ => none

def parsedOperandHasSingleLineWriteMask : ParsedOperand → Bool
  | .mem _ _ _ _ mask | .bar _ _ mask | .omr _ mask => mask.isSome
  | _ => false

/-- Resolve the write mask for one PE cycle. Explicit selectors take priority;
the caller supplies an already-resolved multiline directive when no selector
appears on the OMR destination. -/
def resolveParsedMaskFlags? (mask : ParsedMask)
    (registers : ProofsLean.MNCore.Masks.RegisterFile) (cycle : Fin 4) :
    Option (BitVec 4) :=
  match mask with
  | .pattern _ bits =>
      some (if bits.getLsbD (3 - cycle.val) then BitVec.allOnes 4 else 0)
  | .entry _ index =>
      if h : index < 256 then
        some (ProofsLean.MNCore.Masks.readEntry registers
          ⟨index % 32, by omega⟩ cycle)
      else none

structure PEWordSelection where
  flags : BitVec 4
  longLong : Bool
  deriving DecidableEq, Repr

def parsedMaskLongLong : ParsedMask → Bool
  | .pattern ll _ | .entry ll _ => ll

def resolveParsedMaskSelection? (mask : ParsedMask)
    (registers : ProofsLean.MNCore.Masks.RegisterFile) (cycle : Fin 4) :
    Option PEWordSelection :=
  (resolveParsedMaskFlags? mask registers cycle).map fun flags =>
    ⟨flags, parsedMaskLongLong mask⟩

/-- OMR flag selection is independent of the directive's word width. -/
def resolveOmrDirectiveSelection? (directive : ParsedMaskDirective)
    (registers : ProofsLean.MNCore.Masks.RegisterFile) (cycle : Fin 4) :
    Option (BitVec 4) :=
  if directive.targets.maskRegister && directive.entry != 0 then
    resolveParsedMaskFlags? (.entry (directive.widthWords == 4) directive.entry)
      registers cycle
  else none

def directiveTargetsBank (targets : ParsedMaskTargets) : Bank → Bool
  | .lm0 => targets.lm0
  | .lm1 => targets.lm1
  | .grf0 => targets.grf0
  | .grf1 => targets.grf1
  | .t => targets.t

def resolveMemoryDirectiveSelection? (directive : ParsedMaskDirective) (bank : Bank)
    (registers : ProofsLean.MNCore.Masks.RegisterFile) (cycle : Fin 4) :
    Option PEWordSelection :=
  if directiveTargetsBank directive.targets bank && directive.entry != 0 then
    resolveParsedMaskSelection? (.entry (directive.widthWords == 4) directive.entry)
      registers cycle
  else none

example (registers : ProofsLean.MNCore.Masks.RegisterFile) (cycle : Fin 4) :
    resolveOmrDirectiveSelection?
      { targets := { maskRegister := true }, entry := 1 } registers cycle =
      some (registers 0 cycle) := by
  simp [resolveOmrDirectiveSelection?, resolveParsedMaskFlags?,
    ProofsLean.MNCore.Masks.readEntry]

example (registers : ProofsLean.MNCore.Masks.RegisterFile) (cycle : Fin 4) :
    resolveOmrDirectiveSelection? {} registers cycle = none := by
  simp [resolveOmrDirectiveSelection?]

def ParsedOperand.resolveOmrWriteSelection? (operand : ParsedOperand)
    (registers : ProofsLean.MNCore.Masks.RegisterFile) (cycle : Fin 4)
    (directive : ParsedMaskDirective) (hasSingleLineMask : Bool) : Option (BitVec 4) :=
  match operand with
  | .omr _ (some mask) => resolveParsedMaskFlags? mask registers cycle
  | .omr _ none =>
      if hasSingleLineMask then some (BitVec.allOnes 4)
      else some ((resolveOmrDirectiveSelection? directive registers cycle).getD
        (BitVec.allOnes 4))
  | _ => none

def ParsedOperand.resolveMemoryWriteSelection? (operand : ParsedOperand) (bank : Bank)
    (registers : ProofsLean.MNCore.Masks.RegisterFile) (cycle : Fin 4)
    (directive : ParsedMaskDirective) (hasSingleLineMask : Bool) :
    Option PEWordSelection :=
  match operand with
  | .mem _ _ _ _ (some mask) => resolveParsedMaskSelection? mask registers cycle
  | .mem _ _ _ _ none =>
      if hasSingleLineMask then some ⟨BitVec.allOnes 4, true⟩
      else some ((resolveMemoryDirectiveSelection? directive bank registers cycle).getD
        ⟨BitVec.allOnes 4, true⟩)
  | _ => none

def resolveFlushSelection? (flush : Option ParsedMask)
    (registers : ProofsLean.MNCore.Masks.RegisterFile) (cycle : Fin 4) :
    Option (Option PEWordSelection) :=
  match flush with
  | none => some none
  | some mask => (resolveParsedMaskSelection? mask registers cycle).map some

def parsedExprHasSingleLineWriteMask (expression : ParsedExpr) : Bool :=
  expression.destinations.any parsedOperandHasSingleLineWriteMask

theorem single_line_mask_cancels_omr_directive
    (registers : ProofsLean.MNCore.Masks.RegisterFile) (cycle : Fin 4)
    (directive : ParsedMaskDirective) :
    ParsedOperand.resolveOmrWriteSelection? (.omr 1 none) registers cycle directive true =
      some (BitVec.allOnes 4) := by
  simp [ParsedOperand.resolveOmrWriteSelection?]

theorem own_omr_mask_precedes_multiline_directive
    (registers : ProofsLean.MNCore.Masks.RegisterFile) (cycle : Fin 4)
    (directive : ParsedMaskDirective) (mask : ParsedMask) :
    ParsedOperand.resolveOmrWriteSelection? (.omr 1 (some mask)) registers cycle directive true =
      resolveParsedMaskFlags? mask registers cycle := rfl

theorem own_memory_mask_precedes_multiline_directive
    (registers : ProofsLean.MNCore.Masks.RegisterFile) (cycle : Fin 4)
    (directive : ParsedMaskDirective) (bank : Bank) (access : Access)
    (mask : ParsedMask) :
    ParsedOperand.resolveMemoryWriteSelection?
      (.mem access false false false (some mask)) bank registers cycle directive true =
      resolveParsedMaskSelection? mask registers cycle := rfl

theorem single_line_mask_cancels_memory_directive
    (registers : ProofsLean.MNCore.Masks.RegisterFile) (cycle : Fin 4)
    (directive : ParsedMaskDirective) (bank : Bank) (access : Access) :
    ParsedOperand.resolveMemoryWriteSelection?
      (.mem access false false false none) bank registers cycle directive true =
      some ⟨BitVec.allOnes 4, true⟩ := by
  simp [ParsedOperand.resolveMemoryWriteSelection?]

theorem untargeted_memory_uses_unmasked_selection
    (registers : ProofsLean.MNCore.Masks.RegisterFile) (cycle : Fin 4)
    (directive : ParsedMaskDirective) (bank : Bank) (access : Access)
    (notTargeted : directiveTargetsBank directive.targets bank = false) :
    ParsedOperand.resolveMemoryWriteSelection?
      (.mem access false false false none) bank registers cycle directive false =
      some ⟨BitVec.allOnes 4, true⟩ := by
  simp [ParsedOperand.resolveMemoryWriteSelection?, resolveMemoryDirectiveSelection?,
    notTargeted]

example (registers : ProofsLean.MNCore.Masks.RegisterFile) :
    resolveParsedMaskFlags? (.pattern false 8) registers 0 =
      some (BitVec.allOnes 4) := by simp [resolveParsedMaskFlags?]
example (registers : ProofsLean.MNCore.Masks.RegisterFile) :
    resolveParsedMaskFlags? (.pattern false 8) registers 1 = some 0 := by simp [resolveParsedMaskFlags?]

def ParsedAluName.integerInputCount : ParsedAluName → Nat
  | .inc | .dec | .not | .lnot | .passa => 1
  | .and | .or | .xor | .add | .sub | .max | .min | .packbit
  | .lsl | .lsr | .bsl | .bsr => 2
  | _ => 0

structure ParsedIntegerAccesses where
  op : ParsedOp
  sourceX : DirectMemoryAccess
  sourceY : DirectMemoryAccess
  destination : DirectMemoryAccess
  hasIntegerRequest : ∃ precision aluOp,
    op.integerRequest = .ok (.integer precision aluOp)

structure ParsedMaskedIntegerAccesses where
  op : ParsedOp
  sourceX : DirectMemoryAccess
  sourceY : DirectMemoryAccess
  destination : DirectMemoryAccess
  writeSelection : PEWordSelection
  flushSelection : Option PEWordSelection
  hasIntegerRequest : ∃ precision aluOp,
    op.integerRequest = .ok (.integer precision aluOp)

def ParsedIntegerAccesses.locations (accesses : ParsedIntegerAccesses) :=
  (accesses.sourceX, accesses.sourceY, accesses.destination)

structure ParsedIntegerMaskAccesses where
  op : ParsedOp
  sourceX : DirectMemoryAccess
  sourceY : DirectMemoryAccess
  destination : Fin 15
  selection : BitVec 4
  hasIntegerRequest : ∃ precision aluOp,
    op.integerRequest = .ok (.integer precision aluOp)

def ParsedIntegerMaskAccesses.locations (accesses : ParsedIntegerMaskAccesses) :=
  (accesses.sourceX, accesses.sourceY, accesses.destination)

/-- Lower the memory-only ALU expression subset from ParsedExpr to explicit
per-cycle accesses. Inputs with unsupported transformations, non-memory
sources, and instructions whose exact inputs are not represented stay out. -/
def ParsedExpr.toDirectIntegerAccesses? (expression : ParsedExpr)
    (pe cycle : Fin 4) (bar0 bar1 : BitVec 12) (tWord : BitVec 32) :
    Option ParsedIntegerAccesses :=
  match expression.op with
  | .alu name (some _) _ _ =>
      match hRequest : expression.op.integerRequest with
      | .ok (.integer precision aluOp) =>
          if expression.flush.isSome then none else
          match expression.sources, expression.destinations with
          | [source], [destination] =>
              if ParsedAluName.integerInputCount name != 1 then none else
              match ParsedOperand.toDirectMemoryAccess? source pe cycle bar0 bar1 tWord,
                    ParsedOperand.toUnmaskedDirectDestination? destination pe cycle bar0 bar1 tWord with
              | some sourceAccess, some destinationAccess =>
                  some ⟨expression.op, sourceAccess, sourceAccess, destinationAccess,
                    ⟨precision, aluOp, hRequest⟩⟩
              | _, _ => none
          | [sourceX, sourceY], [destination] =>
              if ParsedAluName.integerInputCount name != 2 then none else
              match ParsedOperand.toDirectMemoryAccess? sourceX pe cycle bar0 bar1 tWord,
                    ParsedOperand.toDirectMemoryAccess? sourceY pe cycle bar0 bar1 tWord,
                    ParsedOperand.toUnmaskedDirectDestination? destination pe cycle bar0 bar1 tWord with
              | some xAccess, some yAccess, some destinationAccess =>
                  some ⟨expression.op, xAccess, yAccess, destinationAccess,
                    ⟨precision, aluOp, hRequest⟩⟩
              | _, _, _ => none
          | _, _ => none
      | _ => none
  | _ => none

/-- Lower an integer ALU expression with a direct PE-memory destination,
resolving its explicit or multiline write mask and output flush for this cycle. -/
def ParsedExpr.toDirectMaskedIntegerAccessesInLine? (expression : ParsedExpr)
    (registers : ProofsLean.MNCore.Masks.RegisterFile)
    (directive : ParsedMaskDirective) (hasSingleLineMask : Bool)
    (pe cycle : Fin 4) (bar0 bar1 : BitVec 12) (tWord : BitVec 32) :
    Option ParsedMaskedIntegerAccesses :=
  match expression.op with
  | .alu name (some _) _ _ =>
      match hRequest : expression.op.integerRequest with
      | .ok (.integer precision aluOp) =>
          match expression.sources, expression.destinations with
          | [source], [destination] =>
              if ParsedAluName.integerInputCount name != 1 then none else
              match ParsedOperand.toDirectMemoryAccess? source pe cycle bar0 bar1 tWord with
              | none => none
              | some sourceAccess =>
                  match ParsedOperand.toDirectMemoryDestination? destination pe cycle bar0 bar1 tWord with
                  | none => none
                  | some destinationAccess =>
                      match ParsedOperand.resolveMemoryWriteSelection? destination
                          destinationAccess.bank registers cycle directive
                          hasSingleLineMask,
                          resolveFlushSelection? expression.flush registers cycle with
                      | some writeSelection, some flushSelection =>
                          some ⟨expression.op, sourceAccess, sourceAccess, destinationAccess,
                            writeSelection, flushSelection, ⟨precision, aluOp, hRequest⟩⟩
                      | _, _ => none
          | [sourceX, sourceY], [destination] =>
              if ParsedAluName.integerInputCount name != 2 then none else
              match ParsedOperand.toDirectMemoryAccess? sourceX pe cycle bar0 bar1 tWord,
                    ParsedOperand.toDirectMemoryAccess? sourceY pe cycle bar0 bar1 tWord with
              | some xAccess, some yAccess =>
                  match ParsedOperand.toDirectMemoryDestination? destination pe cycle bar0 bar1 tWord with
                  | none => none
                  | some destinationAccess =>
                      match ParsedOperand.resolveMemoryWriteSelection? destination
                          destinationAccess.bank registers cycle directive
                          hasSingleLineMask,
                          resolveFlushSelection? expression.flush registers cycle with
                      | some writeSelection, some flushSelection =>
                          some ⟨expression.op, xAccess, yAccess, destinationAccess,
                            writeSelection, flushSelection, ⟨precision, aluOp, hRequest⟩⟩
                      | _, _ => none
              | _, _ => none
          | _, _ => none
      | _ => none
  | _ => none

def ParsedExpr.toDirectMaskedIntegerAccesses? (expression : ParsedExpr)
    (registers : ProofsLean.MNCore.Masks.RegisterFile)
    (directive : ParsedMaskDirective)
    (pe cycle : Fin 4) (bar0 bar1 : BitVec 12) (tWord : BitVec 32) :
    Option ParsedMaskedIntegerAccesses :=
  ParsedExpr.toDirectMaskedIntegerAccessesInLine? expression registers directive
    (parsedExprHasSingleLineWriteMask expression) pe cycle bar0 bar1 tWord

example : ParsedOperand.toDirectMemoryAccess?
    (.mem ⟨.grf0, ⟨1, 5, 5, 5, 5, false, none⟩⟩ false false false none)
    0 0 0 0 0 = some ⟨.grf0, .word, ⟨5, by decide⟩⟩ := by decide

example : ParsedOperand.toDirectMemoryAccess?
    (.mem ⟨.lm0, ⟨2, 3, 3, 3, 3, false, some 2⟩⟩ false false false none)
    2 0 3 0 0 = some ⟨.lm0, .long, ⟨8, by decide⟩⟩ := by decide

example : ParsedOperand.toDirectMemoryAccess?
    (.mem ⟨.lm0, ⟨1, 0, 0, 0, 0, false, none⟩⟩ true false false none)
    0 0 0 0 0 = none := by decide

example : ParsedOperand.toDirectMemoryAccess?
    (.mem ⟨.lm0, ⟨1, 0, 0, 0, 0, false, none⟩⟩ false true false none)
    0 0 0 0 0 = none := by decide

example : ParsedOperand.toDirectMemoryAccess?
    (.mem ⟨.lm0, ⟨1, 0, 0, 0, 0, false, none⟩⟩ false false false
      (some (.pattern false 0)))
    0 0 0 0 0 = none := by decide

example : ParsedOperand.toMaskRegisterEntry? (.omr 1 none) = some 0 := by decide
example : ParsedOperand.toMaskRegisterEntry? (.omr 15 none) = some 14 := by decide
example : ParsedOperand.toMaskRegisterEntry? (.omr 0 none) = none := by decide

example : (ParsedExpr.toDirectIntegerAccesses?
    ProofsLean.MNCore.Issue.plusOneParsed 0 0 0 0 0).map
      ParsedIntegerAccesses.locations = some
        (⟨.lm0, .long, ⟨0, by decide⟩⟩,
         ⟨.lm0, .long, ⟨0, by decide⟩⟩,
         ⟨.lm1, .long, ⟨0, by decide⟩⟩) := by decide


def readRegisterBank (files : IntegerRegisterFiles) (bank : Bank) (width : Width)
    (address : Fin bank.capacity) : WordBus :=
  match bank with
  | .lm0 => readWords .lm0 width files.lm0 address
  | .lm1 => readWords .lm1 width files.lm1 address
  | .grf0 => readWords .grf0 width files.grf0 address
  | .grf1 => readWords .grf1 width files.grf1 address
  | .t => readWords .t width files.t address

def writeRegisterBank (files : IntegerRegisterFiles) (bank : Bank) (width : Width)
    (address : Fin bank.capacity) (data : WordBus) : IntegerRegisterFiles :=
  match bank with
  | .lm0 => { files with lm0 := writeWords .lm0 width files.lm0 address data }
  | .lm1 => { files with lm1 := writeWords .lm1 width files.lm1 address data }
  | .grf0 => { files with grf0 := writeWords .grf0 width files.grf0 address data }
  | .grf1 => { files with grf1 := writeWords .grf1 width files.grf1 address data }
  | .t => { files with t := writeWords .t width files.t address data }

def writeRegisterBankMasked (files : IntegerRegisterFiles) (bank : Bank) (width : Width)
    (address : Fin bank.capacity) (data : WordBus) (selection : PEWordSelection) :
    IntegerRegisterFiles :=
  match bank with
  | .lm0 => { files with lm0 :=
      (writeWordsMasked .lm0 width files.lm0 address data selection.flags selection.longLong) }
  | .lm1 => { files with lm1 :=
      (writeWordsMasked .lm1 width files.lm1 address data selection.flags selection.longLong) }
  | .grf0 => { files with grf0 :=
      (writeWordsMasked .grf0 width files.grf0 address data selection.flags selection.longLong) }
  | .grf1 => { files with grf1 :=
      (writeWordsMasked .grf1 width files.grf1 address data selection.flags selection.longLong) }
  | .t => { files with t :=
      (writeWordsMasked .t width files.t address data selection.flags selection.longLong) }

def readDirectAccess (files : IntegerRegisterFiles) (access : DirectMemoryAccess) : WordBus :=
  readRegisterBank files access.bank access.width access.address

def writeDirectAccess (files : IntegerRegisterFiles) (access : DirectMemoryAccess)
    (data : WordBus) : IntegerRegisterFiles :=
  writeRegisterBank files access.bank access.width access.address data

def writeDirectAccessMasked (files : IntegerRegisterFiles) (access : DirectMemoryAccess)
    (data : WordBus) (selection : PEWordSelection) : IntegerRegisterFiles :=
  writeRegisterBankMasked files access.bank access.width access.address data selection

theorem readRegisterBank_after_write (files : IntegerRegisterFiles)
    (bank : Bank) (width : Width) (address : Fin bank.capacity)
    (data : WordBus) (index : Fin 4) (within : index.val < count bank width) :
    readRegisterBank (writeRegisterBank files bank width address data) bank width address index =
      data index := by
  cases bank <;> exact read_after_write _ _ _ _ _ _ within

theorem readDirectAccessMasked_after_write (files : IntegerRegisterFiles)
    (access : DirectMemoryAccess) (data : WordBus) (selection : PEWordSelection)
    (index : Fin 4) (within : index.val < count access.bank access.width) :
    readDirectAccess (writeDirectAccessMasked files access data selection) access index =
      mergeSelectedWord (readDirectAccess files access index) (data index)
        (selectedWordMask selection.flags selection.longLong index) := by
  cases access with
  | mk bank width address =>
    cases bank with
    | lm0 =>
        simp only [readDirectAccess, readRegisterBank, writeDirectAccessMasked,
          writeRegisterBankMasked]
        rw [readWordsMasked_after_mask .lm0 width files.lm0 address data
          selection.flags selection.longLong index within]
        simp [readWords, within]
    | lm1 =>
        simp only [readDirectAccess, readRegisterBank, writeDirectAccessMasked,
          writeRegisterBankMasked]
        rw [readWordsMasked_after_mask .lm1 width files.lm1 address data
          selection.flags selection.longLong index within]
        simp [readWords, within]
    | grf0 =>
        simp only [readDirectAccess, readRegisterBank, writeDirectAccessMasked,
          writeRegisterBankMasked]
        rw [readWordsMasked_after_mask .grf0 width files.grf0 address data
          selection.flags selection.longLong index within]
        simp [readWords, within]
    | grf1 =>
        simp only [readDirectAccess, readRegisterBank, writeDirectAccessMasked,
          writeRegisterBankMasked]
        rw [readWordsMasked_after_mask .grf1 width files.grf1 address data
          selection.flags selection.longLong index within]
        simp [readWords, within]
    | t =>
        simp only [readDirectAccess, readRegisterBank, writeDirectAccessMasked,
          writeRegisterBankMasked]
        rw [readWordsMasked_after_mask .t width files.t address data
          selection.flags selection.longLong index within]
        simp [readWords, within]


def parsedOutputAfterFlush (selection : Option PEWordSelection)
    (output : IntegerALU.Bus) : IntegerALU.Bus :=
  match selection with
  | none => output
  | some selected => ProofsLean.MNCore.Masks.flushBus
      (if selected.longLong then .double else .long) selected.flags output

def parsedIntegerMaskedRegisterStep (files : IntegerRegisterFiles)
    (accesses : ParsedMaskedIntegerAccesses) (reduced : Bool) :
    ProofsLean.StepResult IntegerRegisterFiles :=
  let x := pack (readDirectAccess files accesses.sourceX)
  let y := pack (readDirectAccess files accesses.sourceY)
  match evaluateParsedIntegerAlu accesses.op x y reduced with
  | .ok output =>
      .ok (writeDirectAccessMasked files accesses.destination
        (unpackALUBus (parsedOutputAfterFlush accesses.flushSelection output.value))
        accesses.writeSelection)
  | .failure => .failure
  | .unknown => .unknown

theorem parsedIntegerMaskedRegisterStep_success (files : IntegerRegisterFiles)
    (accesses : ParsedMaskedIntegerAccesses) (reduced : Bool)
    (output : IntegerALU.BusResult)
    (evaluated : evaluateParsedIntegerAlu accesses.op
      (pack (readDirectAccess files accesses.sourceX))
      (pack (readDirectAccess files accesses.sourceY)) reduced = .ok output) :
    parsedIntegerMaskedRegisterStep files accesses reduced =
      .ok (writeDirectAccessMasked files accesses.destination
        (unpackALUBus (parsedOutputAfterFlush accesses.flushSelection output.value))
        accesses.writeSelection) := by
  simp [parsedIntegerMaskedRegisterStep, evaluated]

def executeParsedMaskedIntegerExpr? (files : IntegerRegisterFiles)
    (expression : ParsedExpr) (directive : ParsedMaskDirective)
    (pe cycle : Fin 4) (bar0 bar1 : BitVec 12) (tWord : BitVec 32) :
    Option (ProofsLean.StepResult IntegerRegisterFiles) :=
  match ParsedExpr.toDirectMaskedIntegerAccesses? expression files.maskRegisters
      directive pe cycle bar0 bar1 tWord with
  | some accesses => some (parsedIntegerMaskedRegisterStep files accesses false)
  | none => none

structure ParsedIntegerContext where
  pe : Fin 4
  cycle : Fin 4
  (bar0 bar1 : BitVec 12)
  tWord : BitVec 32
  deriving DecidableEq, Repr

structure ParsedMaskExecutionControl where
  directive : ParsedMaskDirective
  context : ParsedIntegerContext
  elapsedWords : Nat
  deriving DecidableEq, Repr

inductive ParsedMaskedIssueLine where
  | pe (expressions : List ParsedExpr)
  | nop
  deriving DecidableEq, Repr

abbrev ParsedMaskedSourceStatement :=
  ProofsLean.ControlNormalization.Statement ParsedMaskDirective ParsedMaskedIssueLine

def updateParsedMaskDirective (next : ParsedMaskDirective)
    (current : ParsedMaskExecutionControl) : ParsedMaskExecutionControl :=
  { current with directive := next }

def advanceParsedMaskControl (current : ParsedMaskExecutionControl)
    (_line : ParsedMaskedIssueLine) : ParsedMaskExecutionControl :=
  { current with elapsedWords := current.elapsedWords + 1 }

def parsedAccessAbsoluteCycle (control : ParsedMaskExecutionControl)
    (cycle : Fin 4) : Nat := control.elapsedWords * 4 + cycle.val

def advanceParsedControlThroughSource :
    List ParsedMaskedSourceStatement → ParsedMaskExecutionControl →
      ParsedMaskExecutionControl
  | [], control => control
  | .directive directive :: rest, control =>
      advanceParsedControlThroughSource rest (updateParsedMaskDirective directive control)
  | .issue line :: rest, control =>
      advanceParsedControlThroughSource rest (advanceParsedMaskControl control line)

theorem parsed_source_clock_matches_issue_cost
    (source : List ParsedMaskedSourceStatement) (control : ParsedMaskExecutionControl) :
    (advanceParsedControlThroughSource source control).elapsedWords =
      control.elapsedWords + ProofsLean.ControlNormalization.cost source := by
  induction source generalizing control with
  | nil => rfl
  | cons statement rest ih =>
      cases statement with
      | directive directive =>
          simp [advanceParsedControlThroughSource,
            updateParsedMaskDirective, ProofsLean.ControlNormalization.cost, ih]
      | issue line =>
          simp [advanceParsedControlThroughSource, advanceParsedMaskControl,
            ProofsLean.ControlNormalization.cost, ih]
          omega

theorem parsed_source_access_clock_matches_issue_cost
    (source : List ParsedMaskedSourceStatement) (control : ParsedMaskExecutionControl)
    (cycle : Fin 4) :
    parsedAccessAbsoluteCycle (advanceParsedControlThroughSource source control) cycle =
      parsedAccessAbsoluteCycle control cycle +
        4 * ProofsLean.ControlNormalization.cost source := by
  simp [parsedAccessAbsoluteCycle, parsed_source_clock_matches_issue_cost]
  omega

inductive PEHazardDistance where
  | steps (count : Nat)
  | cycles (count : Nat)
  deriving DecidableEq, Repr

structure TimedPEAccess where
  access : DirectMemoryAccess
  write : Bool
  startWord : Nat
  cycle : Fin 4
  deriving DecidableEq, Repr

def TimedPEAccess.absoluteCycle (event : TimedPEAccess) : Nat :=
  event.startWord * 4 + event.cycle.val

def TimedPEAccess.ofControl (control : ParsedMaskExecutionControl)
    (access : DirectMemoryAccess) (write : Bool) (cycle : Fin 4) : TimedPEAccess :=
  ⟨access, write, control.elapsedWords, cycle⟩

def TimedPEAccess.rangeStart (event : TimedPEAccess) : Nat :=
  if event.access.bank = .t then event.cycle.val else event.access.address.val

def TimedPEAccess.rangeLength (event : TimedPEAccess) : Nat :=
  if event.access.bank = .t then 1 else event.access.width.words

def TimedPEAccess.rangesOverlap (left right : TimedPEAccess) : Bool :=
  left.access.bank == right.access.bank &&
    left.rangeStart < right.rangeStart + right.rangeLength &&
    right.rangeStart < left.rangeStart + left.rangeLength

def peHazardRequirement? (earlier later : TimedPEAccess) : Option PEHazardDistance :=
  if !earlier.write || later.write then none
  else match earlier.access.bank, later.access.bank with
    | .lm0, .lm0 | .lm1, .lm1 => some (.steps 3)
    | .grf0, .grf0 | .grf1, .grf1 | .t, .t =>
        if earlier.rangesOverlap later then some (.cycles 7) else none
    | _, _ => none

def peHazardSatisfied (earlier later : TimedPEAccess) : Prop :=
  earlier.startWord < later.startWord ∧
    match peHazardRequirement? earlier later with
    | none => True
    | some (.steps count) =>
        count * 4 ≤ (later.startWord - earlier.startWord) * 4
    | some (.cycles count) =>
        count ≤ later.absoluteCycle - earlier.absoluteCycle

def parsedHazardCycles : List (Fin 4) := [0, 1, 2, 3]

def parsedHazardPatternEnables (mask : Option ParsedMask) (cycle : Fin 4) : Bool :=
  match mask with
  | some (.pattern _ bits) => bits.getLsbD (3 - cycle.val)
  | _ => true

def tIndirectHazardAccess (cycle : Fin 4) : DirectMemoryAccess :=
  ⟨.t, .word, ⟨cycle.val, by have h := cycle.isLt; simp [Bank.capacity]; omega⟩⟩

def ParsedOperand.toTimedPEHazardEvents? (operand : ParsedOperand) (write : Bool)
    (control : ParsedMaskExecutionControl) : Option (List TimedPEAccess) :=
  match operand with
  | .mem access _ _ _ ownMask =>
      match issueBankToRegisterBank access.bank with
      | none => some []
      | some _ => do
          let resolved ← parsedHazardCycles.mapM fun cycle =>
            ParsedOperand.toDirectMemoryAccessMode? operand true
              control.context.pe cycle control.context.bar0 control.context.bar1
              control.context.tWord
          pure <| (parsedHazardCycles.zip resolved).flatMap fun (cycle, direct) =>
            if write && !parsedHazardPatternEnables ownMask cycle then []
            else
              let primary := [TimedPEAccess.ofControl control direct write cycle]
              let indirect := if !write && access.region.tIndirect then
                [TimedPEAccess.ofControl control (tIndirectHazardAccess cycle) false cycle]
                else []
              primary ++ indirect
  | _ => some []

def ParsedExpr.toTimedPEHazardEvents? (expression : ParsedExpr)
    (control : ParsedMaskExecutionControl) : Option (List TimedPEAccess) := do
  let reads ← expression.sources.mapM fun operand =>
    ParsedOperand.toTimedPEHazardEvents? operand false control
  let writes ← expression.destinations.mapM fun operand =>
    ParsedOperand.toTimedPEHazardEvents? operand true control
  pure (reads.flatten ++ writes.flatten)

def ParsedMaskedIssueLine.toTimedPEHazardEvents?
    (line : ParsedMaskedIssueLine) (control : ParsedMaskExecutionControl) :
    Option (List TimedPEAccess) :=
  match line with
  | .nop => some []
  | .pe expressions => do
      let perExpression ← expressions.mapM fun expression =>
        ParsedExpr.toTimedPEHazardEvents? expression control
      pure perExpression.flatten

theorem parsed_mask_pattern_controls_hazard_write_cycle
    (cycle : Fin 4) (bits : BitVec 4) :
    parsedHazardPatternEnables (some (.pattern false bits)) cycle =
      bits.getLsbD (3 - cycle.val) := rfl

theorem parsed_mask_entry_keeps_all_hazard_write_cycles
    (cycle : Fin 4) (longLong : Bool) (entry : Nat) :
    parsedHazardPatternEnables (some (.entry longLong entry)) cycle = true := rfl

theorem t_indirect_hazard_access_uses_cycle_region (cycle : Fin 4) :
    (tIndirectHazardAccess cycle).bank = .t ∧
      TimedPEAccess.rangeStart
        (TimedPEAccess.ofControl
          ⟨{}, ⟨0, cycle, 0, 0, 0⟩, 0⟩
          (tIndirectHazardAccess cycle) false cycle) = cycle.val := by
  constructor
  · rfl
  · simp [TimedPEAccess.rangeStart, TimedPEAccess.ofControl, tIndirectHazardAccess]

structure PEHazardConstraint where
  earlier : TimedPEAccess
  later : TimedPEAccess
  distance : Nat
  required : Nat
  deriving DecidableEq, Repr

def PEHazardConstraint.violated (constraint : PEHazardConstraint) : Bool :=
  constraint.distance < constraint.required

def makePEHazardConstraint? (earlier later : TimedPEAccess) :
    Option PEHazardConstraint :=
  if earlier.startWord < later.startWord then
    match peHazardRequirement? earlier later with
    | none => none
    | some (.steps count) =>
        some ⟨earlier, later, (later.startWord - earlier.startWord) * 4, count * 4⟩
    | some (.cycles count) =>
        some ⟨earlier, later,
          later.absoluteCycle - earlier.absoluteCycle, count⟩
  else none

def peHazardConstraintsBetween (earlier later : List TimedPEAccess) :
    List PEHazardConstraint :=
  earlier.flatMap fun write =>
    later.filterMap fun access =>
      match makePEHazardConstraint? write access with
      | some constraint =>
          if access.startWord - write.startWord ≤ 4 then some constraint else none
      | none => none

def collectPEHazardConstraintsAux (earlier : List TimedPEAccess)
    (remaining : List (List TimedPEAccess)) : List PEHazardConstraint :=
  match remaining with
  | [] => []
  | current :: rest =>
      peHazardConstraintsBetween earlier current ++
        collectPEHazardConstraintsAux (earlier ++ current) rest

def collectPEHazardConstraints (eventsByIssue : List (List TimedPEAccess)) :
    List PEHazardConstraint :=
  collectPEHazardConstraintsAux [] eventsByIssue

def parsedSourcePEHazardEvents? (source : List ParsedMaskedSourceStatement)
    (control : ParsedMaskExecutionControl) : Option (List (List TimedPEAccess)) :=
  let compiled := ProofsLean.ControlNormalization.compileAdvancing
    updateParsedMaskDirective advanceParsedMaskControl source control
  compiled.mapM fun instruction =>
    instruction.2.toTimedPEHazardEvents? instruction.1

def parsedSourcePEHazardConstraints? (source : List ParsedMaskedSourceStatement)
    (control : ParsedMaskExecutionControl) : Option (List PEHazardConstraint) :=
  (parsedSourcePEHazardEvents? source control).map collectPEHazardConstraints

theorem pe_hazard_constraint_uses_rule_distance
    (earlier later : TimedPEAccess) (constraint : PEHazardConstraint)
    (made : makePEHazardConstraint? earlier later = some constraint) :
    ∃ ruleDistance, peHazardRequirement? earlier later = some ruleDistance ∧
      constraint.earlier = earlier ∧ constraint.later = later ∧
      (match ruleDistance with
       | .steps count => constraint.distance =
            (later.startWord - earlier.startWord) * 4 ∧ constraint.required = count * 4
       | .cycles count => constraint.distance =
            later.absoluteCycle - earlier.absoluteCycle ∧ constraint.required = count) := by
  by_cases htime : earlier.startWord < later.startWord
  · cases hreq : peHazardRequirement? earlier later with
    | none => simp [makePEHazardConstraint?, htime, hreq] at made
    | some ruleDistance =>
        cases ruleDistance with
        | steps count =>
            simp [makePEHazardConstraint?, htime, hreq] at made
            cases made
            exact ⟨.steps count, rfl, rfl, rfl, by simp⟩
        | cycles count =>
            simp [makePEHazardConstraint?, htime, hreq] at made
            cases made
            exact ⟨.cycles count, rfl, rfl, rfl, by simp⟩
  · simp [makePEHazardConstraint?, htime] at made

theorem lm_pe_hazard_requires_three_issue_words
    (earlier later : TimedPEAccess)
    (write : earlier.write = true) (read : later.write = false)
    (sameBank : earlier.access.bank = later.access.bank)
    (lm : earlier.access.bank = .lm0 ∨ earlier.access.bank = .lm1) :
    peHazardRequirement? earlier later = some (.steps 3) := by
  cases hEarlier : earlier.access.bank <;>
    cases hLater : later.access.bank <;>
    simp_all [peHazardRequirement?]

theorem grf_t_pe_hazard_requires_seven_cycles
    (earlier later : TimedPEAccess)
    (write : earlier.write = true) (read : later.write = false)
    (sameBank : earlier.access.bank = later.access.bank)
    (grfT : earlier.access.bank = .grf0 ∨ earlier.access.bank = .grf1 ∨
      earlier.access.bank = .t)
    (overlap : earlier.rangesOverlap later = true) :
    peHazardRequirement? earlier later = some (.cycles 7) := by
  cases hEarlier : earlier.access.bank <;>
    cases hLater : later.access.bank <;>
    simp_all [peHazardRequirement?]

theorem lm_pe_hazard_satisfied_after_three_words
    (earlier later : TimedPEAccess)
    (sameBank : earlier.access.bank = later.access.bank)
    (lm : earlier.access.bank = .lm0 ∨ earlier.access.bank = .lm1)
    (accessed : earlier.write = true ∧ later.write = false)
    (distance : earlier.startWord + 3 ≤ later.startWord) :
    peHazardSatisfied earlier later := by
  constructor
  · omega
  rw [lm_pe_hazard_requires_three_issue_words earlier later accessed.1 accessed.2
    sameBank lm]
  omega

theorem grf_t_pe_hazard_satisfied_after_seven_cycles
    (earlier later : TimedPEAccess)
    (sameBank : earlier.access.bank = later.access.bank)
    (grfT : earlier.access.bank = .grf0 ∨ earlier.access.bank = .grf1 ∨
      earlier.access.bank = .t)
    (accessed : earlier.write = true ∧ later.write = false)
    (overlap : earlier.rangesOverlap later = true)
    (distance : earlier.absoluteCycle + 7 ≤ later.absoluteCycle) :
    peHazardSatisfied earlier later := by
  have earlierCycleBound := earlier.cycle.isLt
  have laterCycleBound := later.cycle.isLt
  simp only [peHazardSatisfied]
  unfold TimedPEAccess.absoluteCycle at distance ⊢
  constructor
  · omega
  rw [grf_t_pe_hazard_requires_seven_cycles earlier later accessed.1 accessed.2
    sameBank grfT overlap]
  omega

theorem parsed_issue_advances_elapsed_word
    (control : ParsedMaskExecutionControl) (line : ParsedMaskedIssueLine) :
    (advanceParsedMaskControl control line).elapsedWords = control.elapsedWords + 1 := rfl

theorem parsed_issue_advances_absolute_cycle
    (control : ParsedMaskExecutionControl) (line : ParsedMaskedIssueLine)
    (cycle : Fin 4) :
    parsedAccessAbsoluteCycle (advanceParsedMaskControl control line) cycle =
      parsedAccessAbsoluteCycle control cycle + 4 := by
  simp [advanceParsedMaskControl, parsedAccessAbsoluteCycle]
  omega

theorem mask_directive_replaces_selection_preserves_context
    (next : ParsedMaskDirective) (current : ParsedMaskExecutionControl) :
    (updateParsedMaskDirective next current).directive = next ∧
      (updateParsedMaskDirective next current).context = current.context ∧
      (updateParsedMaskDirective next current).elapsedWords = current.elapsedWords := by
  constructor
  · rfl
  constructor <;> rfl

structure PreparedParsedMaskedWrite where
  destination : DirectMemoryAccess
  data : WordBus
  selection : PEWordSelection

def prepareParsedMaskedWrite (files : IntegerRegisterFiles)
    (accesses : ParsedMaskedIntegerAccesses) (reduced : Bool) :
    ProofsLean.StepResult PreparedParsedMaskedWrite :=
  let x := pack (readDirectAccess files accesses.sourceX)
  let y := pack (readDirectAccess files accesses.sourceY)
  match evaluateParsedIntegerAlu accesses.op x y reduced with
  | .ok output =>
      let bus := parsedOutputAfterFlush accesses.flushSelection output.value
      .ok ⟨accesses.destination, unpackALUBus bus, accesses.writeSelection⟩
  | .failure => .failure
  | .unknown => .unknown

def prepareParsedMaskedLine (files : IntegerRegisterFiles)
    (expressions : List ParsedExpr) (control : ParsedMaskExecutionControl) :
    ProofsLean.StepResult (List PreparedParsedMaskedWrite) :=
  let hasSingleLineMask := expressions.any parsedExprHasSingleLineWriteMask
  let rec prepare : List ParsedExpr → ProofsLean.StepResult (List PreparedParsedMaskedWrite)
    | [] => .ok []
    | expression :: rest =>
        match expression.op with
        | .wait _ | .noforward => prepare rest
        | _ =>
          match ParsedExpr.toDirectMaskedIntegerAccessesInLine? expression files.maskRegisters
              control.directive hasSingleLineMask control.context.pe control.context.cycle
              control.context.bar0 control.context.bar1 control.context.tWord with
          | none => .unknown
          | some accesses =>
              match prepareParsedMaskedWrite files accesses false with
              | .failure => .failure
              | .unknown => .unknown
              | .ok write =>
                  match prepare rest with
                  | .ok writes => .ok (write :: writes)
                  | .failure => .failure
                  | .unknown => .unknown
  prepare expressions

def commitParsedMaskedWrites (files : IntegerRegisterFiles)
    (writes : List PreparedParsedMaskedWrite) : IntegerRegisterFiles :=
  writes.foldl (fun current write =>
    writeDirectAccessMasked current write.destination write.data write.selection) files

def parsedIntegerMaskedLineStep (files : IntegerRegisterFiles)
    (expressions : List ParsedExpr) (control : ParsedMaskExecutionControl) :
    ProofsLean.StepResult IntegerRegisterFiles :=
  match prepareParsedMaskedLine files expressions control with
  | .ok writes => .ok (commitParsedMaskedWrites files writes)
  | .failure => .failure
  | .unknown => .unknown

theorem parsedIntegerMaskedLineStep_prepares_then_commits
    (files : IntegerRegisterFiles) (expressions : List ParsedExpr)
    (control : ParsedMaskExecutionControl) :
    parsedIntegerMaskedLineStep files expressions control =
      match prepareParsedMaskedLine files expressions control with
      | .ok writes => .ok (commitParsedMaskedWrites files writes)
      | .failure => .failure
      | .unknown => .unknown := rfl


def parsedMaskedExpressionStep (control : ParsedMaskExecutionControl)
    (line : ParsedMaskedIssueLine) (files : IntegerRegisterFiles) :
    Option IntegerRegisterFiles :=
  match line with
  | .pe expressions =>
      match parsedIntegerMaskedLineStep files expressions control with
      | .ok next => some next
      | .failure | .unknown => none
  | .nop => some files

def parsedLineHasNoForward (expressions : List ParsedExpr) : Bool :=
  expressions.any fun expression => match expression.op with
    | .noforward => true
    | _ => false

def advanceParsedLineForwarding (old : ProofsLean.MNCore.Forwarding.Slots)
    (expressions : List ParsedExpr)
    (outputs : ProofsLean.MNCore.Forwarding.Unit →
      Option (Fin 4 → ProofsLean.MNCore.Forwarding.Value IntegerALU.Bus)) :
    ProofsLean.StepResult ProofsLean.MNCore.Forwarding.Slots :=
  ProofsLean.MNCore.Forwarding.advance old
    (.issue (parsedLineHasNoForward expressions) outputs)

theorem parsed_noforward_suppresses_forwarding_updates
    (old : ProofsLean.MNCore.Forwarding.Slots) (expressions : List ParsedExpr)
    (outputs : ProofsLean.MNCore.Forwarding.Unit →
      Option (Fin 4 → ProofsLean.MNCore.Forwarding.Value IntegerALU.Bus))
    (hasNoForward : parsedLineHasNoForward expressions = true) :
    advanceParsedLineForwarding old expressions outputs = .ok old := by
  simp [advanceParsedLineForwarding, hasNoForward,
    ProofsLean.MNCore.Forwarding.advance]

def ParsedLine.toParsedMaskedStatements? :
    ParsedLine → Option (List ParsedMaskedSourceStatement)
  | .maskDirective widthWords targets entry =>
      some [.directive ⟨widthWords, targets, entry⟩]
  | .pe expressions => some [.issue (.pe expressions)]
  | .nop count _ => some (List.replicate count (.issue .nop))
  | _ => none

def lowerParsedMaskedSource (lines : List ParsedLine) :
    Option (List ParsedMaskedSourceStatement) := do
  let lowered ← lines.mapM ParsedLine.toParsedMaskedStatements?
  pure lowered.flatten

def ParsedLine.parsedMaskedIssueWords? : ParsedLine → Option Nat
  | .pe _ => some 1
  | .nop count _ => some count
  | .maskDirective _ _ _ => some 0
  | _ => none



def runParsedMaskedSource (source : List ParsedMaskedSourceStatement)
    (control : ParsedMaskExecutionControl) (files : IntegerRegisterFiles) :
    Option IntegerRegisterFiles :=
  ProofsLean.ControlNormalization.runSourceAdvancing updateParsedMaskDirective
    advanceParsedMaskControl parsedMaskedExpressionStep source control files

def parsedMaskedIssueLineLegal : ParsedMaskedIssueLine → Prop
  | .pe expressions => LegalParsedLine expressions
  | .nop => True

def parsedMaskedIssueLegal : List (ParsedMaskExecutionControl × ParsedMaskedIssueLine) → Prop :=
  fun lines => ∀ line ∈ lines, parsedMaskedIssueLineLegal line.2

def parsedMaskedNormalizedMachine : ProofsLean.Machine where
  Line := ParsedMaskExecutionControl × ParsedMaskedIssueLine
  State := IntegerRegisterFiles
  Input := Unit
  step := fun pair files => parsedMaskedExpressionStep pair.1 pair.2 files
  legal := parsedMaskedIssueLegal
  lineCost := fun _ => 1
  positiveCost := fun _ => by decide

def runParsedMaskedCompiled (source : List ParsedMaskedSourceStatement)
    (control : ParsedMaskExecutionControl) (files : IntegerRegisterFiles) :
    Option IntegerRegisterFiles :=
  let compiled := ProofsLean.ControlNormalization.compileAdvancing
    updateParsedMaskDirective advanceParsedMaskControl source control
  ProofsLean.execute parsedMaskedNormalizedMachine compiled files

theorem parsedMaskedSource_execution (source : List ParsedMaskedSourceStatement)
    (control : ParsedMaskExecutionControl) (files : IntegerRegisterFiles) :
    runParsedMaskedSource source control files =
      runParsedMaskedCompiled source control files := by
  exact ProofsLean.ControlNormalization.source_execution_advancing
    updateParsedMaskDirective advanceParsedMaskControl parsedMaskedExpressionStep
    parsedMaskedIssueLegal Unit source control files

theorem mask_directive_has_zero_issue_cost (directive : ParsedMaskDirective) :
    ProofsLean.ControlNormalization.cost
      ([.directive directive] : List ParsedMaskedSourceStatement) = 0 := rfl

theorem parsed_wait_expression_preserves_register_state
    (files : IntegerRegisterFiles) (control : ParsedMaskExecutionControl) (tag : Nat) :
    parsedIntegerMaskedLineStep files
      [{ op := .wait tag, sources := [], destinations := [], flush := none, text := "wait" }]
      control = .ok files := by
  simp [parsedIntegerMaskedLineStep, prepareParsedMaskedLine,
    prepareParsedMaskedLine.prepare,
    commitParsedMaskedWrites]

theorem parsed_nop_preserves_register_state
    (control : ParsedMaskExecutionControl) (files : IntegerRegisterFiles) :
    parsedMaskedExpressionStep control .nop files = some files := rfl

theorem parsed_nop_count_has_matching_issue_cost (count : Nat) :
    ProofsLean.ControlNormalization.cost
      (List.replicate count (.issue ParsedMaskedIssueLine.nop) :
        List ParsedMaskedSourceStatement) = count := by
  induction count with
  | zero => rfl
  | succ count ih => simp [List.replicate_succ, ProofsLean.ControlNormalization.cost, ih]; omega

theorem parsed_line_lowering_preserves_issue_words (line : ParsedLine)
    (statements : List ParsedMaskedSourceStatement)
    (lowered : ParsedLine.toParsedMaskedStatements? line = some statements) :
    ∃ words, ParsedLine.parsedMaskedIssueWords? line = some words ∧
      ProofsLean.ControlNormalization.cost statements = words := by
  cases line with
  | pe expressions =>
      simp [ParsedLine.toParsedMaskedStatements?] at lowered
      subst statements
      exact ⟨1, rfl, rfl⟩
  | nop count wait =>
      simp [ParsedLine.toParsedMaskedStatements?] at lowered
      subst statements
      exact ⟨count, rfl, parsed_nop_count_has_matching_issue_cost count⟩
  | maskDirective width targets entry =>
      simp [ParsedLine.toParsedMaskedStatements?] at lowered
      subst statements
      exact ⟨0, rfl, rfl⟩
  | mv => simp [ParsedLine.toParsedMaskedStatements?] at lowered
  | debugSet => simp [ParsedLine.toParsedMaskedStatements?] at lowered
  | debugGet => simp [ParsedLine.toParsedMaskedStatements?] at lowered
  | dramSet => simp [ParsedLine.toParsedMaskedStatements?] at lowered
theorem parsed_nop_line_lowers_to_count_issue_words (count : Nat) (wait : Option Nat) :
    lowerParsedMaskedSource [.nop count wait] =
      some (List.replicate count (.issue ParsedMaskedIssueLine.nop)) := by
  simp [lowerParsedMaskedSource, ParsedLine.toParsedMaskedStatements?]

theorem parsedMaskedSource_score (source : List ParsedMaskedSourceStatement)
    (control : ParsedMaskExecutionControl) :
    ProofsLean.score parsedMaskedNormalizedMachine
      (ProofsLean.ControlNormalization.compileAdvancing updateParsedMaskDirective
        advanceParsedMaskControl source control) =
      ProofsLean.ControlNormalization.cost source :=
  ProofsLean.ControlNormalization.source_score_advancing updateParsedMaskDirective
    advanceParsedMaskControl parsedMaskedExpressionStep parsedMaskedIssueLegal Unit
    source control

theorem lowered_parsed_masked_source_executes_as_normalized
    (lines : List ParsedLine) (source : List ParsedMaskedSourceStatement)
    (lowered : lowerParsedMaskedSource lines = some source)
    (control : ParsedMaskExecutionControl) (files : IntegerRegisterFiles) :
    (lowerParsedMaskedSource lines).map
      (fun loweredSource => runParsedMaskedSource loweredSource control files) =
      some (ProofsLean.execute parsedMaskedNormalizedMachine
        (ProofsLean.ControlNormalization.compileAdvancing updateParsedMaskDirective
          advanceParsedMaskControl source control)
        files) := by
  rw [lowered]
  simp only [Option.map_some]
  rw [parsedMaskedSource_execution]
  constructor <;> rfl

def parsedIntegerRegisterStep (files : IntegerRegisterFiles)
    (sourceX sourceY destination : DirectMemoryAccess) (op : ParsedOp)
    (reduced : Bool) : ProofsLean.StepResult IntegerRegisterFiles :=
  let x := pack (readDirectAccess files sourceX)
  let y := pack (readDirectAccess files sourceY)
  match evaluateParsedIntegerAlu op x y reduced with
  | .ok output => .ok (writeDirectAccess files destination (unpackALUBus output.value))
  | .failure => .failure
  | .unknown => .unknown

def executeParsedIntegerExpr? (files : IntegerRegisterFiles)
    (expression : ParsedExpr) (pe cycle : Fin 4) (bar0 bar1 : BitVec 12)
    (tWord : BitVec 32) : Option (ProofsLean.StepResult IntegerRegisterFiles) :=
  match ParsedExpr.toDirectIntegerAccesses? expression pe cycle bar0 bar1 tWord with
  | some accesses => some (parsedIntegerRegisterStep files accesses.sourceX
      accesses.sourceY accesses.destination accesses.op false)
  | none => none

def parsedIntegerRegisterOutput (files : IntegerRegisterFiles)
    (sourceX sourceY : DirectMemoryAccess) (precision : IntegerALU.Precision)
    (aluOp : IntegerALU.Op) (reduced : Bool) : IntegerALU.BusResult :=
  IntegerALU.evaluateBus precision aluOp
    (pack (readDirectAccess files sourceX))
    (pack (readDirectAccess files sourceY)) reduced

def integerFlagsVector (output : IntegerALU.BusResult) : BitVec 4 :=
  BitVec.ofBoolListLE [output.flags 0, output.flags 1, output.flags 2, output.flags 3]

theorem integerFlagsVector_bit0 (output : IntegerALU.BusResult) :
    (integerFlagsVector output).getLsbD 0 = output.flags 0 := by
  change (BitVec.ofBoolListLE
    [output.flags 0, output.flags 1, output.flags 2, output.flags 3]).getLsbD 0 = _
  rw [BitVec.getLsbD_ofBoolListLE]
  simp

theorem integerFlagsVector_bit1 (output : IntegerALU.BusResult) :
    (integerFlagsVector output).getLsbD 1 = output.flags 1 := by
  change (BitVec.ofBoolListLE
    [output.flags 0, output.flags 1, output.flags 2, output.flags 3]).getLsbD 1 = _
  rw [BitVec.getLsbD_ofBoolListLE]
  simp

theorem integerFlagsVector_bit2 (output : IntegerALU.BusResult) :
    (integerFlagsVector output).getLsbD 2 = output.flags 2 := by
  change (BitVec.ofBoolListLE
    [output.flags 0, output.flags 1, output.flags 2, output.flags 3]).getLsbD 2 = _
  rw [BitVec.getLsbD_ofBoolListLE]
  simp

theorem integerFlagsVector_bit3 (output : IntegerALU.BusResult) :
    (integerFlagsVector output).getLsbD 3 = output.flags 3 := by
  change (BitVec.ofBoolListLE
    [output.flags 0, output.flags 1, output.flags 2, output.flags 3]).getLsbD 3 = _
  rw [BitVec.getLsbD_ofBoolListLE]
  simp

def parsedIntegerMaskRegisterStep (files : IntegerRegisterFiles)
    (sourceX sourceY : DirectMemoryAccess) (entry : Fin 15) (cycle : Fin 4)
    (selection : BitVec 4) (op : ParsedOp) (reduced : Bool) :
    ProofsLean.StepResult IntegerRegisterFiles :=
  match evaluateParsedIntegerAlu op
      (pack (readDirectAccess files sourceX))
      (pack (readDirectAccess files sourceY)) reduced with
  | .ok output => .ok { files with maskRegisters :=
      (ProofsLean.MNCore.Masks.writeRegister files.maskRegisters entry cycle
        (integerFlagsVector output) selection) }
  | .failure => .failure
  | .unknown => .unknown

def parsedIntegerMaskExprAccesses? (expression : ParsedExpr)
    (registers : ProofsLean.MNCore.Masks.RegisterFile)
    (directive : ParsedMaskDirective)
    (pe cycle : Fin 4) (bar0 bar1 : BitVec 12) (tWord : BitVec 32) :
    Option ParsedIntegerMaskAccesses :=
  match expression.op with
  | .alu name (some _) _ _ =>
      match hRequest : expression.op.integerRequest with
      | .ok (.integer precision aluOp) =>
          match expression.sources, expression.destinations with
          | [source], [destination] =>
              if ParsedAluName.integerInputCount name != 1 then none else
              match ParsedOperand.toDirectMemoryAccess? source pe cycle bar0 bar1 tWord,
                    ParsedOperand.toMaskRegisterEntry? destination,
                    ParsedOperand.resolveOmrWriteSelection? destination registers cycle directive
                      (parsedExprHasSingleLineWriteMask expression) with
              | some sourceAccess, some entry, some selection =>
                  some ⟨expression.op, sourceAccess, sourceAccess, entry,
                    selection, ⟨precision, aluOp, hRequest⟩⟩
              | _, _, _ => none
          | [sourceX, sourceY], [destination] =>
              if ParsedAluName.integerInputCount name != 2 then none else
              match ParsedOperand.toDirectMemoryAccess? sourceX pe cycle bar0 bar1 tWord,
                    ParsedOperand.toDirectMemoryAccess? sourceY pe cycle bar0 bar1 tWord,
                    ParsedOperand.toMaskRegisterEntry? destination,
                    ParsedOperand.resolveOmrWriteSelection? destination registers cycle directive
                      (parsedExprHasSingleLineWriteMask expression) with
              | some xAccess, some yAccess, some entry, some selection =>
                  some ⟨expression.op, xAccess, yAccess, entry,
                    selection, ⟨precision, aluOp, hRequest⟩⟩
              | _, _, _, _ => none
          | _, _ => none
      | _ => none
  | _ => none

example : (parsedIntegerMaskExprAccesses?
    ({ op := .alu .inc (some .i) false none,
       sources := [.mem ⟨.lm0, ⟨2, 0, 0, 0, 0, false, none⟩⟩ false false false none],
       destinations := [.omr 1 none], flush := none, text := "iinc $lm0v $omr1" } : ParsedExpr)
    (fun _ _ => 0) {}
    0 0 0 0 0).map ParsedIntegerMaskAccesses.locations =
      some (⟨.lm0, .long, ⟨0, by decide⟩⟩,
        ⟨.lm0, .long, ⟨0, by decide⟩⟩, 0) := by decide

example : (parsedIntegerMaskExprAccesses?
    ({ op := .alu .inc (some .i) false none,
       sources := [.mem ⟨.lm0, ⟨2, 0, 0, 0, 0, false, none⟩⟩ false false false none],
       destinations := [.omr 1 none], flush := none, text := "iinc $lm0v $omr1" } : ParsedExpr)
    (fun _ _ => 0) {} 0 0 0 0 0).map ParsedIntegerMaskAccesses.selection =
      some (BitVec.allOnes 4) := by decide

def executeParsedIntegerMaskExpr? (files : IntegerRegisterFiles)
    (expression : ParsedExpr) (pe cycle : Fin 4) (bar0 bar1 : BitVec 12)
    (tWord : BitVec 32) (directive : ParsedMaskDirective) :
    Option (ProofsLean.StepResult IntegerRegisterFiles) :=
  match parsedIntegerMaskExprAccesses? expression files.maskRegisters directive
      pe cycle bar0 bar1 tWord with
  | some accesses => some (parsedIntegerMaskRegisterStep files accesses.sourceX
      accesses.sourceY accesses.destination cycle accesses.selection accesses.op false)
  | none => none

theorem mask_read_after_selected_write (registers : ProofsLean.MNCore.Masks.RegisterFile)
    (entry : Fin 15) (cycle : Fin 4) (flags selection : BitVec 4) :
    ProofsLean.MNCore.Masks.readEntry
      (ProofsLean.MNCore.Masks.writeRegister registers entry cycle flags selection)
      ⟨entry.val + 1, by have := entry.isLt; omega⟩ cycle = flags &&& selection := by
  simp [ProofsLean.MNCore.Masks.readEntry, ProofsLean.MNCore.Masks.writeRegister,
    show entry.val + 1 < 16 by have := entry.isLt; omega]

theorem mask_read_after_writeRegister (registers : ProofsLean.MNCore.Masks.RegisterFile)
    (entry : Fin 15) (cycle : Fin 4) (flags : BitVec 4) :
    ProofsLean.MNCore.Masks.readEntry
      (ProofsLean.MNCore.Masks.writeRegister registers entry cycle flags (BitVec.allOnes 4))
      ⟨entry.val + 1, by have := entry.isLt; omega⟩ cycle = flags := by
  simp [ProofsLean.MNCore.Masks.readEntry, ProofsLean.MNCore.Masks.writeRegister,
    show entry.val + 1 < 16 by have := entry.isLt; omega]
  change flags &&& BitVec.allOnes 4 = flags
  exact BitVec.and_allOnes

theorem parsedIntegerMaskStep_readback (files : IntegerRegisterFiles)
    (sourceX sourceY : DirectMemoryAccess) (entry : Fin 15) (cycle : Fin 4)
    (selection : BitVec 4) (op : ParsedOp)
    (precision : IntegerALU.Precision) (aluOp : IntegerALU.Op)
    (selected : op.integerRequest = .ok (.integer precision aluOp))
    (reduced : Bool) :
    ∃ nextFiles,
      parsedIntegerMaskRegisterStep files sourceX sourceY entry cycle selection op reduced =
        .ok nextFiles ∧
      ProofsLean.MNCore.Masks.readEntry nextFiles.maskRegisters
        ⟨entry.val + 1, by have := entry.isLt; omega⟩ cycle =
        integerFlagsVector (parsedIntegerRegisterOutput files sourceX sourceY
          precision aluOp reduced) &&& selection := by
  let output := parsedIntegerRegisterOutput files sourceX sourceY precision aluOp reduced
  refine ⟨{ files with maskRegisters :=
      (ProofsLean.MNCore.Masks.writeRegister files.maskRegisters entry cycle
        (integerFlagsVector output) selection) }, ?_, ?_⟩
  · simp [parsedIntegerMaskRegisterStep, evaluateParsedIntegerAlu, selected,
      output, IntegerALU.partialEvaluate]
    constructor <;> rfl
  · exact mask_read_after_selected_write files.maskRegisters entry cycle
      (integerFlagsVector output) selection

theorem parsed_iinc_output_eq_incrementPair (files : IntegerRegisterFiles)
    (address : Fin Bank.lm0.capacity) :
    (parsedIntegerRegisterOutput files ⟨.lm0, .long, address⟩
      ⟨.lm0, .long, address⟩ .word (.arith .inc false) false).value.high =
      ProofsLean.MNCore.PlusOne.incrementPair
        (files.lm0 address) (files.lm0 (advance .lm0 address 1)) := by
  have hzero : advance .lm0 address 0 = address := by
    apply Fin.ext
    simp [advance, Nat.mod_eq_of_lt address.isLt]
  have hread0 : readWords .lm0 .long files.lm0 address 0 = files.lm0 address := by
    simp [readWords, count, Width.words, advance, Nat.mod_eq_of_lt address.isLt]
  have hread1 : readWords .lm0 .long files.lm0 address 1 =
      files.lm0 (advance .lm0 address 1) := by
    simp [readWords, count, Width.words]
  simp [parsedIntegerRegisterOutput, readDirectAccess, readRegisterBank,
    ProofsLean.MNCore.PlusOne.incrementPair, pack, hread0, hread1,
    IntegerALU.evaluateBus, IntegerALU.lane, IntegerALU.Precision.lanes,
    IntegerALU.Precision.width, IntegerALU.evaluateLane, IntegerALU.arithmetic,
    List.range, List.range.loop]

theorem direct_access_write_readback (files : IntegerRegisterFiles)
    (destination : DirectMemoryAccess) (data : WordBus) (index : Fin 4)
    (within : index.val < count destination.bank destination.width) :
    readDirectAccess (writeDirectAccess files destination data) destination index = data index := by
  cases destination with
  | mk bank width address =>
    exact readRegisterBank_after_write files bank width address data index within


theorem parsedIntegerRegisterStep_succeeds (files : IntegerRegisterFiles)
    (sourceX sourceY destination : DirectMemoryAccess) (op : ParsedOp)
    (reduced : Bool) (precision : IntegerALU.Precision) (aluOp : IntegerALU.Op)
    (selected : op.integerRequest = .ok (.integer precision aluOp)) :
    parsedIntegerRegisterStep files sourceX sourceY destination op reduced =
      .ok (writeDirectAccess files destination
        (unpackALUBus (parsedIntegerRegisterOutput files sourceX sourceY
          precision aluOp reduced).value)) := by
  simp [parsedIntegerRegisterStep, evaluateParsedIntegerAlu, selected,
    parsedIntegerRegisterOutput, IntegerALU.partialEvaluate]

theorem parsedIntegerRegisterStep_readback (files : IntegerRegisterFiles)
    (sourceX sourceY destination : DirectMemoryAccess) (op : ParsedOp)
    (reduced : Bool) (precision : IntegerALU.Precision) (aluOp : IntegerALU.Op)
    (selected : op.integerRequest = .ok (.integer precision aluOp))
    (index : Fin 4) (within : index.val < count destination.bank destination.width) :
    ∃ nextFiles,
      parsedIntegerRegisterStep files sourceX sourceY destination op reduced = .ok nextFiles ∧
      readDirectAccess nextFiles destination index =
        unpackALUBus (parsedIntegerRegisterOutput files sourceX sourceY
          precision aluOp reduced).value index := by
  refine ⟨writeDirectAccess files destination
    (unpackALUBus (parsedIntegerRegisterOutput files sourceX sourceY
      precision aluOp reduced).value),
    parsedIntegerRegisterStep_succeeds files sourceX sourceY destination op reduced
      precision aluOp selected, ?_⟩
  exact direct_access_write_readback files destination
    (unpackALUBus (parsedIntegerRegisterOutput files sourceX sourceY
      precision aluOp reduced).value) index within

theorem executeParsedIntegerExpr_readback (files : IntegerRegisterFiles)
    (expression : ParsedExpr) (pe cycle : Fin 4) (bar0 bar1 : BitVec 12)
    (tWord : BitVec 32) (accesses : ParsedIntegerAccesses)
    (lowered : ParsedExpr.toDirectIntegerAccesses? expression pe cycle bar0 bar1 tWord =
      some accesses)
    (index : Fin 4)
    (within : index.val < count accesses.destination.bank accesses.destination.width) :
    ∃ precision aluOp nextFiles,
      accesses.op.integerRequest = .ok (.integer precision aluOp) ∧
      executeParsedIntegerExpr? files expression pe cycle bar0 bar1 tWord =
        some (.ok nextFiles) ∧
      readDirectAccess nextFiles accesses.destination index =
        unpackALUBus (parsedIntegerRegisterOutput files accesses.sourceX
          accesses.sourceY precision aluOp false).value index := by
  rcases accesses.hasIntegerRequest with ⟨precision, aluOp, selected⟩
  refine ⟨precision, aluOp,
    writeDirectAccess files accesses.destination
      (unpackALUBus (parsedIntegerRegisterOutput files accesses.sourceX
        accesses.sourceY precision aluOp false).value), selected, ?_, ?_⟩
  · simp only [executeParsedIntegerExpr?, lowered, Option.some.injEq]
    exact parsedIntegerRegisterStep_succeeds files accesses.sourceX accesses.sourceY
      accesses.destination accesses.op false precision aluOp selected
  · exact direct_access_write_readback files accesses.destination
      (unpackALUBus (parsedIntegerRegisterOutput files accesses.sourceX
        accesses.sourceY precision aluOp false).value) index within

theorem executeParsedIntegerMaskExpr_readback (files : IntegerRegisterFiles)
    (expression : ParsedExpr) (pe cycle : Fin 4) (bar0 bar1 : BitVec 12)
    (tWord : BitVec 32) (directive : ParsedMaskDirective)
    (accesses : ParsedIntegerMaskAccesses)
    (lowered : parsedIntegerMaskExprAccesses? expression files.maskRegisters directive
      pe cycle bar0 bar1 tWord =
      some accesses) :
    ∃ precision aluOp nextFiles,
      accesses.op.integerRequest = .ok (.integer precision aluOp) ∧
      executeParsedIntegerMaskExpr? files expression pe cycle bar0 bar1 tWord directive =
        some (.ok nextFiles) ∧
      ProofsLean.MNCore.Masks.readEntry nextFiles.maskRegisters
        ⟨accesses.destination.val + 1, by have := accesses.destination.isLt; omega⟩ cycle =
        integerFlagsVector (parsedIntegerRegisterOutput files accesses.sourceX
          accesses.sourceY precision aluOp false) &&& accesses.selection := by
  rcases accesses.hasIntegerRequest with ⟨precision, aluOp, selected⟩
  let output := parsedIntegerRegisterOutput files accesses.sourceX accesses.sourceY
    precision aluOp false
  refine ⟨precision, aluOp,
    { files with maskRegisters :=
      (ProofsLean.MNCore.Masks.writeRegister files.maskRegisters accesses.destination cycle
        (integerFlagsVector output) accesses.selection) }, selected, ?_, ?_⟩
  · simp [executeParsedIntegerMaskExpr?, lowered, parsedIntegerMaskRegisterStep,
      evaluateParsedIntegerAlu, selected, output, IntegerALU.partialEvaluate]
    constructor <;> rfl
  · exact mask_read_after_selected_write files.maskRegisters accesses.destination cycle
      (integerFlagsVector output) accesses.selection


end ProofsLean.MNCore.PEMemory
