import ProofsLean.PEMemory

/-! Connects the four MSB-first 32-bit memory words to the ALU's two 64-bit
halves. This is a representation boundary only; it does not model an
instruction's operand reads or write schedule. -/
namespace ProofsLean.MNCore.PEMemory

def unpackALUBus (bus : IntegerALU.Bus) : WordBus := fun index =>
  if index.val = 0 then bus.high.extractLsb' 32 32
  else if index.val = 1 then bus.high.extractLsb' 0 32
  else if index.val = 2 then bus.low.extractLsb' 32 32
  else bus.low.extractLsb' 0 32

theorem bus_ext {left right : IntegerALU.Bus}
    (high : left.high = right.high) (low : left.low = right.low) : left = right := by
  cases left with
  | mk lh ll => cases right with
    | mk rh rl => simp_all

theorem pack_unpackALUBus (bus : IntegerALU.Bus) :
    pack (unpackALUBus bus) = bus := by
  cases bus with
  | mk high low =>
    simp only [pack, unpackALUBus, Fin.val_zero, Fin.val_one]
    apply bus_ext
    · exact BitVec.extractLsb'_append_extractLsb'
    · exact BitVec.extractLsb'_append_extractLsb'

end ProofsLean.MNCore.PEMemory
