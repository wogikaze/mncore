import ProofsLean.BusLayout
import ProofsLean.Issue
import ProofsLean.PlusOne

/-! A deliberately partial instruction fragment: two unmasked memory reads,
the parsed integer ALU request, and one unmasked memory write. This composes
existing datapath pieces without claiming timing, masks, hazards, or ISA-wide
operand legality. -/
namespace ProofsLean.MNCore.PEMemory

open ProofsLean.MNCore.Issue

structure IntegerRegisterFiles where
  lm0 : Memory .lm0
  lm1 : Memory .lm1
  grf0 : Memory .grf0
  grf1 : Memory .grf1
  t : Memory .t

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
def ParsedOperand.toDirectMemoryAccess? (operand : ParsedOperand)
    (pe cycle : Fin 4) (bar0 bar1 : BitVec 12) (tWord : BitVec 32) :
    Option DirectMemoryAccess :=
  match operand with
  | .mem access _ _ rounded _ =>
      if rounded then none else
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

def ParsedOperand.toUnmaskedDirectDestination? (operand : ParsedOperand)
    (pe cycle : Fin 4) (bar0 bar1 : BitVec 12) (tWord : BitVec 32) :
    Option DirectMemoryAccess :=
  match operand with
  | .mem _ _ _ _ none =>
      ParsedOperand.toDirectMemoryAccess? operand pe cycle bar0 bar1 tWord
  | _ => none

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
  deriving DecidableEq, Repr

/-- Lower the memory-only ALU expression subset from ParsedExpr to explicit
per-cycle accesses. Operands with rounding, masked destinations, non-memory
sources, and instructions whose exact inputs are not represented stay out. -/
def ParsedExpr.toDirectIntegerAccesses? (expression : ParsedExpr)
    (pe cycle : Fin 4) (bar0 bar1 : BitVec 12) (tWord : BitVec 32) :
    Option ParsedIntegerAccesses :=
  match expression.op with
  | .alu name (some _) _ _ =>
      match expression.op.integerRequest with
      | .ok (.integer _ _) =>
          if expression.flush.isSome then none else
          match expression.sources, expression.destinations with
          | [source], [destination] =>
              if ParsedAluName.integerInputCount name != 1 then none else
              match ParsedOperand.toDirectMemoryAccess? source pe cycle bar0 bar1 tWord,
                    ParsedOperand.toUnmaskedDirectDestination? destination pe cycle bar0 bar1 tWord with
              | some sourceAccess, some destinationAccess =>
                  some ⟨expression.op, sourceAccess, sourceAccess, destinationAccess⟩
              | _, _ => none
          | [sourceX, sourceY], [destination] =>
              if ParsedAluName.integerInputCount name != 2 then none else
              match ParsedOperand.toDirectMemoryAccess? sourceX pe cycle bar0 bar1 tWord,
                    ParsedOperand.toDirectMemoryAccess? sourceY pe cycle bar0 bar1 tWord,
                    ParsedOperand.toUnmaskedDirectDestination? destination pe cycle bar0 bar1 tWord with
              | some xAccess, some yAccess, some destinationAccess =>
                  some ⟨expression.op, xAccess, yAccess, destinationAccess⟩
              | _, _, _ => none
          | _, _ => none
      | _ => none
  | _ => none

example : ParsedOperand.toDirectMemoryAccess?
    (.mem ⟨.grf0, ⟨1, 5, 5, 5, 5, false, none⟩⟩ false false false none)
    0 0 0 0 0 = some ⟨.grf0, .word, ⟨5, by decide⟩⟩ := by decide

example : ParsedOperand.toDirectMemoryAccess?
    (.mem ⟨.lm0, ⟨2, 3, 3, 3, 3, false, some 2⟩⟩ false false false none)
    2 0 3 0 0 = some ⟨.lm0, .long, ⟨8, by decide⟩⟩ := by decide

example : ParsedExpr.toDirectIntegerAccesses?
    ProofsLean.MNCore.Issue.plusOneParsed 0 0 0 0 0 =
      some ⟨ProofsLean.MNCore.Issue.plusOneParsed.op,
        ⟨.lm0, .long, ⟨0, by decide⟩⟩, ⟨.lm0, .long, ⟨0, by decide⟩⟩,
        ⟨.lm1, .long, ⟨0, by decide⟩⟩⟩ := by decide

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

def readDirectAccess (files : IntegerRegisterFiles) (access : DirectMemoryAccess) : WordBus :=
  readRegisterBank files access.bank access.width access.address

def writeDirectAccess (files : IntegerRegisterFiles) (access : DirectMemoryAccess)
    (data : WordBus) : IntegerRegisterFiles :=
  writeRegisterBank files access.bank access.width access.address data

theorem readRegisterBank_after_write (files : IntegerRegisterFiles)
    (bank : Bank) (width : Width) (address : Fin bank.capacity)
    (data : WordBus) (index : Fin 4) (within : index.val < count bank width) :
    readRegisterBank (writeRegisterBank files bank width address data) bank width address index =
      data index := by
  cases bank <;> exact read_after_write _ _ _ _ _ _ within


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
    (precision : IntegerALU.Precision) (aluOp : IntegerALU.Op)
    (selected : accesses.op.integerRequest = .ok (.integer precision aluOp))
    (index : Fin 4)
    (within : index.val < count accesses.destination.bank accesses.destination.width) :
    ∃ nextFiles,
      executeParsedIntegerExpr? files expression pe cycle bar0 bar1 tWord =
        some (.ok nextFiles) ∧
      readDirectAccess nextFiles accesses.destination index =
        unpackALUBus (parsedIntegerRegisterOutput files accesses.sourceX
          accesses.sourceY precision aluOp false).value index := by
  simp only [executeParsedIntegerExpr?, lowered, Option.some.injEq]
  exact parsedIntegerRegisterStep_readback files accesses.sourceX accesses.sourceY
    accesses.destination accesses.op false precision aluOp selected index within


end ProofsLean.MNCore.PEMemory
