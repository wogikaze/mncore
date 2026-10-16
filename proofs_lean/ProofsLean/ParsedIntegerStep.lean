import ProofsLean.BusLayout
import ProofsLean.Issue

/-! A deliberately partial instruction fragment: two unmasked memory reads,
the parsed integer ALU request, and one unmasked memory write. This composes
existing datapath pieces without claiming timing, masks, hazards, or ISA-wide
operand legality. -/
namespace ProofsLean.MNCore.PEMemory

open ProofsLean.MNCore.Issue

def parsedIntegerWriteStep (bank : Bank) (width : Width)
    (memory : Memory bank) (sourceX sourceY destination : Fin bank.capacity)
    (op : ParsedOp) (reduced : Bool) : ProofsLean.StepResult (Memory bank) :=
  let x := pack (readWords bank width memory sourceX)
  let y := pack (readWords bank width memory sourceY)
  match evaluateParsedIntegerAlu op x y reduced with
  | .ok output => .ok (writeWords bank width memory destination (unpackALUBus output.value))
  | .failure => .failure
  | .unknown => .unknown

def parsedIntegerALUOutput (bank : Bank) (width : Width) (memory : Memory bank)
    (sourceX sourceY : Fin bank.capacity) (precision : IntegerALU.Precision)
    (aluOp : IntegerALU.Op) (reduced : Bool) : IntegerALU.BusResult :=
  IntegerALU.evaluateBus precision aluOp
    (pack (readWords bank width memory sourceX))
    (pack (readWords bank width memory sourceY)) reduced

theorem parsedIntegerWriteStep_readback (bank : Bank) (width : Width)
    (memory : Memory bank) (sourceX sourceY destination : Fin bank.capacity)
    (op : ParsedOp) (reduced : Bool) (precision : IntegerALU.Precision)
    (aluOp : IntegerALU.Op)
    (selected : op.integerRequest = .ok (.integer precision aluOp)) :
    parsedIntegerWriteStep bank width memory sourceX sourceY destination op reduced =
        .ok (writeWords bank width memory destination
          (unpackALUBus (parsedIntegerALUOutput bank width memory sourceX sourceY
            precision aluOp reduced).value)) ∧
      ∀ index, index.val < count bank width →
        readWords bank width
          (writeWords bank width memory destination
            (unpackALUBus (parsedIntegerALUOutput bank width memory sourceX sourceY
              precision aluOp reduced).value))
          destination index = unpackALUBus
            (parsedIntegerALUOutput bank width memory sourceX sourceY
              precision aluOp reduced).value index := by
  constructor
  · simp [parsedIntegerWriteStep, evaluateParsedIntegerAlu, selected,
      parsedIntegerALUOutput, IntegerALU.partialEvaluate]
  · intro index within
    exact read_after_write bank width memory destination
      (unpackALUBus (parsedIntegerALUOutput bank width memory sourceX sourceY
        precision aluOp reduced).value) index within

end ProofsLean.MNCore.PEMemory
