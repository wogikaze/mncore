import ProofsLean.PEMemory
import ProofsLean.FloatAdd
import ProofsLean.FloatSubtract
import ProofsLean.FloatMultiply

/-! A one-cycle connection between the float-add datapath and the existing PE
memory primitives. It reads two 64-bit inputs (two f32 lanes each), applies
`fvadd`, and writes the 64-bit result to LM1. This omits masks, hazards,
forwarding and source parsing, which remain obligations for the full machine. -/
namespace ProofsLean.MNCore.FloatPEMemory

open ProofsLean.MNCore

def readPair (bank : PEMemory.Bank) (memory : PEMemory.Memory bank)
    (start : Fin bank.capacity) : BitVec 64 :=
  let words := PEMemory.readWords bank .long memory start
  words 0 ++ words 1

def pairBus (value : BitVec 64) : PEMemory.WordBus := fun index =>
  if index.val = 0 then value.extractLsb' 32 32
  else if index.val = 1 then value.extractLsb' 0 32
  else 0

def writePair (memory : PEMemory.Memory .lm1)
    (start : Fin (PEMemory.Bank.capacity .lm1))
    (value : BitVec 64) : PEMemory.Memory .lm1 :=
  PEMemory.writeWords .lm1 .long memory start (pairBus value)

theorem readPair_after_writePair (memory : PEMemory.Memory .lm1)
    (start : Fin (PEMemory.Bank.capacity .lm1)) (value : BitVec 64) :
    readPair .lm1 (writePair memory start value) start = value := by
  change (PEMemory.readWords .lm1 .long
      (PEMemory.writeWords .lm1 .long memory start (pairBus value)) start) 0 ++
    (PEMemory.readWords .lm1 .long
      (PEMemory.writeWords .lm1 .long memory start (pairBus value)) start) 1 = value
  rw [PEMemory.read_after_write .lm1 .long memory start (pairBus value) 0 (by decide)]
  rw [PEMemory.read_after_write .lm1 .long memory start (pairBus value) 1 (by decide)]
  simp [pairBus]
  bv_decide

theorem writePair_preservesOutside (memory : PEMemory.Memory .lm1)
    (start target : Fin (PEMemory.Bank.capacity .lm1)) (value : BitVec 64)
    (outside : 2 ≤ PEMemory.distance .lm1 start target) :
    writePair memory start value target = memory target := by
  apply PEMemory.write_preserves_outside .lm1 .long memory start target (pairBus value)
  simpa [PEMemory.count, PEMemory.Width.words] using outside

def binaryCycle (operation : BitVec 64 → BitVec 64 → BitVec 64)
    (left : PEMemory.Memory .lm0) (right : PEMemory.Memory .lm0)
    (output : PEMemory.Memory .lm1)
    (leftStart rightStart : Fin (PEMemory.Bank.capacity .lm0))
    (outputStart : Fin (PEMemory.Bank.capacity .lm1)) : PEMemory.Memory .lm1 :=
  writePair output outputStart
    (operation (readPair .lm0 left leftStart) (readPair .lm0 right rightStart))

theorem binaryCycle_readback (operation : BitVec 64 → BitVec 64 → BitVec 64)
    (left : PEMemory.Memory .lm0) (right : PEMemory.Memory .lm0)
    (output : PEMemory.Memory .lm1)
    (leftStart rightStart : Fin (PEMemory.Bank.capacity .lm0))
    (outputStart : Fin (PEMemory.Bank.capacity .lm1)) :
    readPair .lm1 (binaryCycle operation left right output leftStart rightStart outputStart)
      outputStart = operation (readPair .lm0 left leftStart) (readPair .lm0 right rightStart) := by
  exact readPair_after_writePair output outputStart _

theorem binaryCycle_preservesOutside (operation : BitVec 64 → BitVec 64 → BitVec 64)
    (left : PEMemory.Memory .lm0) (right : PEMemory.Memory .lm0)
    (output : PEMemory.Memory .lm1)
    (leftStart rightStart : Fin (PEMemory.Bank.capacity .lm0))
    (outputStart target : Fin (PEMemory.Bank.capacity .lm1))
    (outside : 2 ≤ PEMemory.distance .lm1 outputStart target) :
    binaryCycle operation left right output leftStart rightStart outputStart target =
      output target := by
  exact writePair_preservesOutside output outputStart target _ outside

def addCycle (left : PEMemory.Memory .lm0) (right : PEMemory.Memory .lm0)
    (output : PEMemory.Memory .lm1)
    (leftStart rightStart : Fin (PEMemory.Bank.capacity .lm0))
    (outputStart : Fin (PEMemory.Bank.capacity .lm1)) : PEMemory.Memory .lm1 :=
  binaryCycle FloatAdd.addBus left right output leftStart rightStart outputStart

def subtractCycle (left : PEMemory.Memory .lm0) (right : PEMemory.Memory .lm0)
    (output : PEMemory.Memory .lm1)
    (leftStart rightStart : Fin (PEMemory.Bank.capacity .lm0))
    (outputStart : Fin (PEMemory.Bank.capacity .lm1)) : PEMemory.Memory .lm1 :=
  binaryCycle FloatSubtract.subtractBus left right output leftStart rightStart outputStart

def multiplySevenCycle (input : PEMemory.Memory .lm0)
    (output : PEMemory.Memory .lm1)
    (inputStart : Fin (PEMemory.Bank.capacity .lm0))
    (outputStart : Fin (PEMemory.Bank.capacity .lm1)) : PEMemory.Memory .lm1 :=
  writePair output outputStart (FloatMultiply.multiplySevenBus (readPair .lm0 input inputStart))
theorem addCycle_readback (left : PEMemory.Memory .lm0) (right : PEMemory.Memory .lm0)
    (output : PEMemory.Memory .lm1)
    (leftStart rightStart : Fin (PEMemory.Bank.capacity .lm0))
    (outputStart : Fin (PEMemory.Bank.capacity .lm1)) :
    readPair .lm1 (addCycle left right output leftStart rightStart outputStart) outputStart =
      FloatAdd.addBus (readPair .lm0 left leftStart) (readPair .lm0 right rightStart) := by
  exact binaryCycle_readback FloatAdd.addBus left right output leftStart rightStart outputStart

theorem addCycle_high_lane (left : PEMemory.Memory .lm0) (right : PEMemory.Memory .lm0)
    (output : PEMemory.Memory .lm1)
    (leftStart rightStart : Fin (PEMemory.Bank.capacity .lm0))
    (outputStart : Fin (PEMemory.Bank.capacity .lm1)) :
    ((readPair .lm1 (addCycle left right output leftStart rightStart outputStart)
      outputStart).extractLsb' 32 32) =
        FloatAdd.add (readPair .lm0 left leftStart |>.extractLsb' 32 32)
          (readPair .lm0 right rightStart |>.extractLsb' 32 32) := by
  rw [addCycle_readback, FloatAdd.addBus_high]

theorem addCycle_low_lane (left : PEMemory.Memory .lm0) (right : PEMemory.Memory .lm0)
    (output : PEMemory.Memory .lm1)
    (leftStart rightStart : Fin (PEMemory.Bank.capacity .lm0))
    (outputStart : Fin (PEMemory.Bank.capacity .lm1)) :
    ((readPair .lm1 (addCycle left right output leftStart rightStart outputStart)
      outputStart).extractLsb' 0 32) =
        FloatAdd.add (readPair .lm0 left leftStart |>.extractLsb' 0 32)
          (readPair .lm0 right rightStart |>.extractLsb' 0 32) := by
  rw [addCycle_readback, FloatAdd.addBus_low]

theorem subtractCycle_readback (left : PEMemory.Memory .lm0) (right : PEMemory.Memory .lm0)
    (output : PEMemory.Memory .lm1)
    (leftStart rightStart : Fin (PEMemory.Bank.capacity .lm0))
    (outputStart : Fin (PEMemory.Bank.capacity .lm1)) :
    readPair .lm1 (subtractCycle left right output leftStart rightStart outputStart)
      outputStart =
        FloatSubtract.subtractBus (readPair .lm0 left leftStart)
          (readPair .lm0 right rightStart) := by
  exact binaryCycle_readback FloatSubtract.subtractBus left right output leftStart rightStart
    outputStart

theorem multiplySevenCycle_readback (input : PEMemory.Memory .lm0)
    (output : PEMemory.Memory .lm1)
    (inputStart : Fin (PEMemory.Bank.capacity .lm0))
    (outputStart : Fin (PEMemory.Bank.capacity .lm1)) :
    readPair .lm1 (multiplySevenCycle input output inputStart outputStart) outputStart =
      FloatMultiply.multiplySevenBus (readPair .lm0 input inputStart) := by
  exact readPair_after_writePair output outputStart _

end ProofsLean.MNCore.FloatPEMemory
