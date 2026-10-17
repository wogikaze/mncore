import ProofsLean.Issue

/-! Unit registration for the structural parsed-op AST. The AST itself stays
independent of execution; this file assigns each producer family to the
corresponding constant/dependency abstraction unit. -/

namespace ProofsLean.MNCore.Issue

/-- Functional producer associated with each parsed PE opcode family. Value
semantics remain separate and may still be unknown for that opcode. -/
def ParsedOp.producerUnit? : ParsedOp → Option UnitKind
  | .alu .. | .immediate .. | .zero => some .integerAlu
  | .mau _ matrix .. => some (if matrix then .matrixUnit else .floatingMau)
  | .matrixWrite .. | .matrixRead .. => some .matrixUnit
  | .l1bm .. => some .l1BlockMemory
  | .l2bm .. => some .l2BlockMemory
  | .wait .. | .noforward => none

theorem ParsedOp.producerUnit?_of_alu (name : ParsedAluName)
    (precision : Option ParsedPrecision) (unsigned : Bool) (arg : Option (Fin 256)) :
    ParsedOp.producerUnit? (ParsedOp.alu name precision unsigned arg) =
      some UnitKind.integerAlu := rfl

theorem ParsedOp.producerUnit?_of_mau (precision : ParsedPrecision)
    (matrix : Bool) (kind : CalcKind) (half : Option Char) (round : Bool) :
    ParsedOp.producerUnit? (ParsedOp.mau precision matrix kind half round) =
      some (if matrix then UnitKind.matrixUnit else UnitKind.floatingMau) := rfl

end ProofsLean.MNCore.Issue
