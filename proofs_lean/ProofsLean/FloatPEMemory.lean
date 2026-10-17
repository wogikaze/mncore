import ProofsLean.PEMemory
import ProofsLean.FloatAdd
import ProofsLean.FloatSubtract
import ProofsLean.FloatMultiply
import ProofsLean.ParsedIntegerStep

/-! A one-cycle connection between the float-add datapath and the existing PE
memory primitives. It reads two 64-bit inputs (two f32 lanes each), applies
`fvadd`, and writes the 64-bit result to LM1. This omits masks, hazards,
forwarding and source parsing, which remain obligations for the full machine. -/
namespace ProofsLean.MNCore.FloatPEMemory

open ProofsLean.MNCore
open ProofsLean.MNCore.Issue

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


theorem writePair_preservesPairOutside (memory : PEMemory.Memory .lm1)
    (start target : Fin (PEMemory.Bank.capacity .lm1)) (value : BitVec 64)
    (outside : ∀ lane : Fin 2,
      2 ≤ PEMemory.distance .lm1 start (PEMemory.advance .lm1 target lane.val)) :
    readPair .lm1 (writePair memory start value) target = readPair .lm1 memory target := by
  unfold readPair
  change (PEMemory.readWords .lm1 .long (writePair memory start value) target) 0 ++
      (PEMemory.readWords .lm1 .long (writePair memory start value) target) 1 =
    (PEMemory.readWords .lm1 .long memory target) 0 ++
      (PEMemory.readWords .lm1 .long memory target) 1
  rw [PEMemory.readWords, PEMemory.readWords]
  simp only [PEMemory.count, PEMemory.Width.words, ↓reduceIte]
  congr 1
  · exact writePair_preservesOutside memory start (PEMemory.advance .lm1 target 0) value
      (outside ⟨0, by decide⟩)
  · exact writePair_preservesOutside memory start (PEMemory.advance .lm1 target 1) value
      (outside ⟨1, by decide⟩)

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

abbrev BinaryCycleAccesses :=
  List (Fin (PEMemory.Bank.capacity .lm0) ×
    Fin (PEMemory.Bank.capacity .lm0) × Fin (PEMemory.Bank.capacity .lm1))

/-- Execute a sequence of independent binary operations, threading the LM1
memory after every cycle. LM0 remains the read-only input. -/
def executeBinaryPlan (operation : BitVec 64 → BitVec 64 → BitVec 64)
    (left right : PEMemory.Memory .lm0) :
    PEMemory.Memory .lm1 → BinaryCycleAccesses → PEMemory.Memory .lm1
  | output, [] => output
  | output, (access :: rest) =>
      let (leftStart, rightStart, outputStart) := access
      executeBinaryPlan operation left right
        (binaryCycle operation left right output leftStart rightStart outputStart) rest

theorem executeBinaryPlan_preservesPairAt
    (operation : BitVec 64 → BitVec 64 → BitVec 64)
    (left right : PEMemory.Memory .lm0) (output : PEMemory.Memory .lm1)
    (plan : BinaryCycleAccesses) (target : Fin (PEMemory.Bank.capacity .lm1))
    (outside : ∀ access ∈ plan, ∀ lane : Fin 2,
      2 ≤ PEMemory.distance .lm1 access.2.2
        (PEMemory.advance .lm1 target lane.val)) :
    readPair .lm1 (executeBinaryPlan operation left right output plan) target =
      readPair .lm1 output target := by
  induction plan generalizing output with
  | nil => rfl
  | cons access rest ih =>
      obtain ⟨leftStart, rightStart, outputStart⟩ := access
      change readPair .lm1
          (executeBinaryPlan operation left right
            (binaryCycle operation left right output leftStart rightStart outputStart) rest)
          target = _
      rw [ih]
      · exact writePair_preservesPairOutside output outputStart target _ (by
          intro lane
          exact outside (leftStart, rightStart, outputStart) (by simp) lane)
      · intro later member lane
        exact outside later (by simp [member]) lane

theorem executeBinaryPlan_head_readback
    (operation : BitVec 64 → BitVec 64 → BitVec 64)
    (left right : PEMemory.Memory .lm0) (output : PEMemory.Memory .lm1)
    (leftStart rightStart : Fin (PEMemory.Bank.capacity .lm0))
    (outputStart : Fin (PEMemory.Bank.capacity .lm1)) (rest : BinaryCycleAccesses)
    (laterOutside : ∀ access ∈ rest, ∀ lane : Fin 2,
      2 ≤ PEMemory.distance .lm1 access.2.2
        (PEMemory.advance .lm1 outputStart lane.val)) :
    readPair .lm1
      (executeBinaryPlan operation left right output
        ((leftStart, rightStart, outputStart) :: rest)) outputStart =
      operation (readPair .lm0 left leftStart) (readPair .lm0 right rightStart) := by
  change readPair .lm1
      (executeBinaryPlan operation left right
        (binaryCycle operation left right output leftStart rightStart outputStart) rest)
      outputStart = _
  rw [executeBinaryPlan_preservesPairAt operation left right
    (binaryCycle operation left right output leftStart rightStart outputStart)
    rest outputStart laterOutside]
  exact binaryCycle_readback operation left right output leftStart rightStart outputStart

theorem executeBinaryPlan_readback_at
    (operation : BitVec 64 → BitVec 64 → BitVec 64)
    (left right : PEMemory.Memory .lm0) (output : PEMemory.Memory .lm1)
    (before after : BinaryCycleAccesses)
    (leftStart rightStart : Fin (PEMemory.Bank.capacity .lm0))
    (outputStart : Fin (PEMemory.Bank.capacity .lm1))
    (laterOutside : ∀ access ∈ after, ∀ lane : Fin 2,
      2 ≤ PEMemory.distance .lm1 access.2.2
        (PEMemory.advance .lm1 outputStart lane.val)) :
    readPair .lm1
      (executeBinaryPlan operation left right output
        (before ++ (leftStart, rightStart, outputStart) :: after)) outputStart =
      operation (readPair .lm0 left leftStart) (readPair .lm0 right rightStart) := by
  induction before generalizing output with
  | nil =>
      simpa using executeBinaryPlan_head_readback operation left right output
        leftStart rightStart outputStart after laterOutside
  | cons access rest ih =>
      obtain ⟨priorLeft, priorRight, priorOutput⟩ := access
      simpa [executeBinaryPlan] using ih
        (binaryCycle operation left right output priorLeft priorRight priorOutput)

def addressedBinaryCycle (operation : BitVec 64 → BitVec 64 → BitVec 64)
    (left : PEMemory.Memory .lm0) (right : PEMemory.Memory .lm0)
    (output : PEMemory.Memory .lm1)
    (leftSchedule rightSchedule : PEMemory.Schedule)
    (outputSchedule : PEMemory.Schedule) (cycle : Fin 4) : PEMemory.Memory .lm1 :=
  binaryCycle operation left right output
    (PEMemory.address .lm0 .long leftSchedule 0 .direct 0 cycle)
    (PEMemory.address .lm0 .long rightSchedule 0 .direct 0 cycle)
    (PEMemory.address .lm1 .long outputSchedule 0 .direct 0 cycle)

theorem addressedBinaryCycle_readback (operation : BitVec 64 → BitVec 64 → BitVec 64)
    (left : PEMemory.Memory .lm0) (right : PEMemory.Memory .lm0)
    (output : PEMemory.Memory .lm1)
    (leftSchedule rightSchedule : PEMemory.Schedule)
    (outputSchedule : PEMemory.Schedule) (cycle : Fin 4) :
    readPair .lm1
        (addressedBinaryCycle operation left right output leftSchedule rightSchedule
          outputSchedule cycle)
        (PEMemory.address .lm1 .long outputSchedule 0 .direct 0 cycle) =
      operation
        (readPair .lm0 left
          (PEMemory.address .lm0 .long leftSchedule 0 .direct 0 cycle))
        (readPair .lm0 right
          (PEMemory.address .lm0 .long rightSchedule 0 .direct 0 cycle)) := by
  exact binaryCycle_readback operation left right output _ _ _

theorem flatAddress_zero (cycle : Fin 4) :
    (PEMemory.address .lm0 .long (.flat (fun _ => 0)) 0 .direct 0 cycle).val = 0 := by
  simp [PEMemory.address, PEMemory.Schedule.at, PEMemory.baseOffset,
    PEMemory.Adjustment.offset, PEMemory.count]

theorem flatAddress_output_stride (cycle : Fin 4) :
    (PEMemory.address .lm1 .long
      (.flat (fun c => 2 * c.val)) 0 .direct 0 cycle).val = 2 * cycle.val := by
  have hc := cycle.isLt
  simp [PEMemory.address, PEMemory.Schedule.at, PEMemory.baseOffset,
    PEMemory.Adjustment.offset, PEMemory.count, PEMemory.Bank.capacity,
    PEMemory.Width.words]
  omega

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

def lm0LongAddress? (access : PEMemory.DirectMemoryAccess) :
    Option (Fin (PEMemory.Bank.capacity .lm0)) :=
  match access with
  | ⟨.lm0, .long, address⟩ => some address
  | _ => none

def lm1LongAddress? (access : PEMemory.DirectMemoryAccess) :
    Option (Fin (PEMemory.Bank.capacity .lm1)) :=
  match access with
  | ⟨.lm1, .long, address⟩ => some address
  | _ => none

/-- Lower the memory-only parsed `fvadd` subset to explicit LM0/LM1 longword
addresses for one PE cycle. Forwarding, masks, and other banks are left out. -/
def lowerParsedFloatAdd? (expression : ParsedExpr) (pe cycle : Fin 4)
    (bar0 bar1 : BitVec 12) (tWord : BitVec 32) :
    Option (Fin (PEMemory.Bank.capacity .lm0) ×
      Fin (PEMemory.Bank.capacity .lm0) × Fin (PEMemory.Bank.capacity .lm1)) := do
  match expression.op with
  | .mau .f false .add none false => pure ()
  | _ => none
  match expression.sources, expression.destinations with
  | [.mem left false false false none, .mem right false false false none],
      [.mem destination false false false none] =>
      let leftAccess ← PEMemory.ParsedOperand.toDirectMemoryAccess?
        (.mem left false false false none) pe cycle bar0 bar1 tWord
      let rightAccess ← PEMemory.ParsedOperand.toDirectMemoryAccess?
        (.mem right false false false none) pe cycle bar0 bar1 tWord
      let destinationAccess ← PEMemory.ParsedOperand.toDirectMemoryAccess?
        (.mem destination false false false none) pe cycle bar0 bar1 tWord
      let leftAddress ← lm0LongAddress? leftAccess
      let rightAddress ← lm0LongAddress? rightAccess
      let destinationAddress ← lm1LongAddress? destinationAccess
      some (leftAddress, rightAddress, destinationAddress)
  | _, _ => none

def executeParsedFloatAddCycle? (expression : ParsedExpr)
    (files : PEMemory.IntegerRegisterFiles) (pe cycle : Fin 4)
    (bar0 bar1 : BitVec 12) (tWord : BitVec 32) :
    Option PEMemory.IntegerRegisterFiles := do
  let (leftAddress, rightAddress, destinationAddress) ←
    lowerParsedFloatAdd? expression pe cycle bar0 bar1 tWord
  let nextLM1 := addCycle files.lm0 files.lm0 files.lm1
    leftAddress rightAddress destinationAddress
  some { files with lm1 := nextLM1 }

def commitLM1 (files : PEMemory.IntegerRegisterFiles)
    (memory : PEMemory.Memory .lm1) : PEMemory.IntegerRegisterFiles :=
  { files with lm1 := memory }

@[simp] theorem commitLM1_lm0 (files : PEMemory.IntegerRegisterFiles)
    (memory : PEMemory.Memory .lm1) : (commitLM1 files memory).lm0 = files.lm0 := rfl

def executeParsedFloatAddCycles? (expression : ParsedExpr)
    (files : PEMemory.IntegerRegisterFiles) (pe : Fin 4)
    (cycles : List (Fin 4)) (bar0 bar1 : BitVec 12) (tWord : BitVec 32) :
    Option PEMemory.IntegerRegisterFiles :=
  match cycles with
  | [] => some files
  | cycle :: rest => do
      let next ← executeParsedFloatAddCycle? expression files pe cycle bar0 bar1 tWord
      executeParsedFloatAddCycles? expression next pe rest bar0 bar1 tWord

def executeParsedFloatAddLine? (expression : ParsedExpr)
    (files : PEMemory.IntegerRegisterFiles) (pe : Fin 4)
    (bar0 bar1 : BitVec 12) (tWord : BitVec 32) :
    Option PEMemory.IntegerRegisterFiles :=
  executeParsedFloatAddCycles? expression files pe (List.finRange 4) bar0 bar1 tWord

theorem executeParsedFloatAddCycles_success (expression : ParsedExpr)
    (files : PEMemory.IntegerRegisterFiles) (pe : Fin 4)
    (cycles : List (Fin 4)) (bar0 bar1 : BitVec 12) (tWord : BitVec 32)
    (lowered : ∀ cycle ∈ cycles, ∃ leftAddress rightAddress destinationAddress,
      lowerParsedFloatAdd? expression pe cycle bar0 bar1 tWord =
        some (leftAddress, rightAddress, destinationAddress)) :
    ∃ result, executeParsedFloatAddCycles? expression files pe cycles bar0 bar1 tWord =
      some result := by
  induction cycles generalizing files with
  | nil => exact ⟨files, rfl⟩
  | cons cycle rest ih =>
      obtain ⟨leftAddress, rightAddress, destinationAddress, headLowered⟩ :=
        lowered cycle (by simp)
      have tailLowered : ∀ next ∈ rest, ∃ leftAddress rightAddress destinationAddress,
          lowerParsedFloatAdd? expression pe next bar0 bar1 tWord =
            some (leftAddress, rightAddress, destinationAddress) := by
        intro next member
        exact lowered next (by simp [member])
      let middle := commitLM1 files
        (addCycle files.lm0 files.lm0 files.lm1 leftAddress rightAddress destinationAddress)
      have firstStep : executeParsedFloatAddCycle? expression files pe cycle bar0 bar1 tWord =
          some middle := by
        simp [executeParsedFloatAddCycle?, headLowered, middle, commitLM1]
      obtain ⟨result, restSteps⟩ := ih middle tailLowered
      refine ⟨result, ?_⟩
      simp [executeParsedFloatAddCycles?, firstStep, restSteps]

theorem executeParsedFloatAddCycle_success (expression : ParsedExpr)
    (files : PEMemory.IntegerRegisterFiles) (pe cycle : Fin 4)
    (bar0 bar1 : BitVec 12) (tWord : BitVec 32)
    (leftAddress rightAddress : Fin (PEMemory.Bank.capacity .lm0))
    (destinationAddress : Fin (PEMemory.Bank.capacity .lm1))
    (lowered : lowerParsedFloatAdd? expression pe cycle bar0 bar1 tWord =
      some (leftAddress, rightAddress, destinationAddress)) :
    executeParsedFloatAddCycle? expression files pe cycle bar0 bar1 tWord =
      some (commitLM1 files
        (addCycle files.lm0 files.lm0 files.lm1 leftAddress rightAddress destinationAddress)) := by
  simp [executeParsedFloatAddCycle?, lowered, commitLM1]

theorem executeParsedFloatAddCycle_readback (expression : ParsedExpr)
    (files : PEMemory.IntegerRegisterFiles) (pe cycle : Fin 4)
    (bar0 bar1 : BitVec 12) (tWord : BitVec 32)
    (leftAddress rightAddress : Fin (PEMemory.Bank.capacity .lm0))
    (destinationAddress : Fin (PEMemory.Bank.capacity .lm1))
    (lowered : lowerParsedFloatAdd? expression pe cycle bar0 bar1 tWord =
      some (leftAddress, rightAddress, destinationAddress)) :
    (executeParsedFloatAddCycle? expression files pe cycle bar0 bar1 tWord).map
      (fun next => readPair .lm1 next.lm1 destinationAddress) =
      some (FloatAdd.addBus (readPair .lm0 files.lm0 leftAddress)
        (readPair .lm0 files.lm0 rightAddress)) := by
  rw [executeParsedFloatAddCycle_success expression files pe cycle bar0 bar1 tWord
    leftAddress rightAddress destinationAddress lowered]
  simp only [Option.map_some, commitLM1, addCycle]
  exact congrArg some
    (binaryCycle_readback FloatAdd.addBus files.lm0 files.lm0 files.lm1
      leftAddress rightAddress destinationAddress)

/-- Lower the direct-memory `fvadd x -y` form. The sign bit changes the
floating-point operation but does not change the address used to read `y`. -/
def lowerParsedFloatSubtract? (expression : ParsedExpr) (pe cycle : Fin 4)
    (bar0 bar1 : BitVec 12) (tWord : BitVec 32) :
    Option (Fin (PEMemory.Bank.capacity .lm0) ×
      Fin (PEMemory.Bank.capacity .lm0) × Fin (PEMemory.Bank.capacity .lm1)) := do
  match expression.op with
  | .mau .f false .add none false => pure ()
  | _ => none
  match expression.sources, expression.destinations with
  | [.mem left false false false none, .mem right true false false none],
      [.mem destination false false false none] =>
      let leftAccess ← PEMemory.ParsedOperand.toDirectMemoryAccess?
        (.mem left false false false none) pe cycle bar0 bar1 tWord
      let rightAccess ← PEMemory.ParsedOperand.toDirectMemoryAccess?
        (.mem right false false false none) pe cycle bar0 bar1 tWord
      let destinationAccess ← PEMemory.ParsedOperand.toDirectMemoryAccess?
        (.mem destination false false false none) pe cycle bar0 bar1 tWord
      let leftAddress ← lm0LongAddress? leftAccess
      let rightAddress ← lm0LongAddress? rightAccess
      let destinationAddress ← lm1LongAddress? destinationAccess
      some (leftAddress, rightAddress, destinationAddress)
  | _, _ => none

def executeParsedFloatSubtractCycle? (expression : ParsedExpr)
    (files : PEMemory.IntegerRegisterFiles) (pe cycle : Fin 4)
    (bar0 bar1 : BitVec 12) (tWord : BitVec 32) :
    Option PEMemory.IntegerRegisterFiles := do
  let (leftAddress, rightAddress, destinationAddress) ←
    lowerParsedFloatSubtract? expression pe cycle bar0 bar1 tWord
  let nextLM1 := subtractCycle files.lm0 files.lm0 files.lm1
    leftAddress rightAddress destinationAddress
  some { files with lm1 := nextLM1 }

def executeParsedFloatSubtractCycles? (expression : ParsedExpr)
    (files : PEMemory.IntegerRegisterFiles) (pe : Fin 4)
    (cycles : List (Fin 4)) (bar0 bar1 : BitVec 12) (tWord : BitVec 32) :
    Option PEMemory.IntegerRegisterFiles :=
  match cycles with
  | [] => some files
  | cycle :: rest => do
      let next ← executeParsedFloatSubtractCycle? expression files pe cycle bar0 bar1 tWord
      executeParsedFloatSubtractCycles? expression next pe rest bar0 bar1 tWord

def executeParsedFloatSubtractLine? (expression : ParsedExpr)
    (files : PEMemory.IntegerRegisterFiles) (pe : Fin 4)
    (bar0 bar1 : BitVec 12) (tWord : BitVec 32) :
    Option PEMemory.IntegerRegisterFiles :=
  executeParsedFloatSubtractCycles? expression files pe (List.finRange 4) bar0 bar1 tWord

theorem executeParsedFloatSubtractCycles_success (expression : ParsedExpr)
    (files : PEMemory.IntegerRegisterFiles) (pe : Fin 4)
    (cycles : List (Fin 4)) (bar0 bar1 : BitVec 12) (tWord : BitVec 32)
    (lowered : ∀ cycle ∈ cycles, ∃ leftAddress rightAddress destinationAddress,
      lowerParsedFloatSubtract? expression pe cycle bar0 bar1 tWord =
        some (leftAddress, rightAddress, destinationAddress)) :
    ∃ result, executeParsedFloatSubtractCycles? expression files pe cycles
      bar0 bar1 tWord = some result := by
  induction cycles generalizing files with
  | nil => exact ⟨files, rfl⟩
  | cons cycle rest ih =>
      obtain ⟨leftAddress, rightAddress, destinationAddress, headLowered⟩ :=
        lowered cycle (by simp)
      have tailLowered : ∀ next ∈ rest, ∃ leftAddress rightAddress destinationAddress,
          lowerParsedFloatSubtract? expression pe next bar0 bar1 tWord =
            some (leftAddress, rightAddress, destinationAddress) := by
        intro next member
        exact lowered next (by simp [member])
      let middle := commitLM1 files
        (subtractCycle files.lm0 files.lm0 files.lm1
          leftAddress rightAddress destinationAddress)
      have firstStep : executeParsedFloatSubtractCycle? expression files pe cycle
          bar0 bar1 tWord = some middle := by
        simp [executeParsedFloatSubtractCycle?, headLowered, middle, commitLM1]
      obtain ⟨result, restSteps⟩ := ih middle tailLowered
      refine ⟨result, ?_⟩
      simp [executeParsedFloatSubtractCycles?, firstStep, restSteps]

theorem executeParsedFloatSubtractCycle_success (expression : ParsedExpr)
    (files : PEMemory.IntegerRegisterFiles) (pe cycle : Fin 4)
    (bar0 bar1 : BitVec 12) (tWord : BitVec 32)
    (leftAddress rightAddress : Fin (PEMemory.Bank.capacity .lm0))
    (destinationAddress : Fin (PEMemory.Bank.capacity .lm1))
    (lowered : lowerParsedFloatSubtract? expression pe cycle bar0 bar1 tWord =
      some (leftAddress, rightAddress, destinationAddress)) :
    executeParsedFloatSubtractCycle? expression files pe cycle bar0 bar1 tWord =
      some (commitLM1 files
        (subtractCycle files.lm0 files.lm0 files.lm1
          leftAddress rightAddress destinationAddress)) := by
  simp [executeParsedFloatSubtractCycle?, lowered, commitLM1]

theorem executeParsedFloatSubtractCycle_readback (expression : ParsedExpr)
    (files : PEMemory.IntegerRegisterFiles) (pe cycle : Fin 4)
    (bar0 bar1 : BitVec 12) (tWord : BitVec 32)
    (leftAddress rightAddress : Fin (PEMemory.Bank.capacity .lm0))
    (destinationAddress : Fin (PEMemory.Bank.capacity .lm1))
    (lowered : lowerParsedFloatSubtract? expression pe cycle bar0 bar1 tWord =
      some (leftAddress, rightAddress, destinationAddress)) :
    (executeParsedFloatSubtractCycle? expression files pe cycle bar0 bar1 tWord).map
      (fun next => readPair .lm1 next.lm1 destinationAddress) =
      some (FloatSubtract.subtractBus (readPair .lm0 files.lm0 leftAddress)
        (readPair .lm0 files.lm0 rightAddress)) := by
  rw [executeParsedFloatSubtractCycle_success expression files pe cycle bar0 bar1 tWord
    leftAddress rightAddress destinationAddress lowered]
  simp only [Option.map_some, commitLM1, subtractCycle]
  exact congrArg some
    (binaryCycle_readback FloatSubtract.subtractBus files.lm0 files.lm0 files.lm1
      leftAddress rightAddress destinationAddress)

def flatLongAccess (bank : Issue.Bank) (base : Nat) : Issue.Access :=
  ⟨bank, ⟨2, base, base + 2, base + 4, base + 6, false, none⟩⟩

def parsedFloatAddSmoke : ParsedExpr where
  op := .mau .f false .add none false
  sources :=
    [.mem (flatLongAccess .lm0 0) false false false none,
     .mem (flatLongAccess .lm0 8) false false false none]
  destinations := [.mem (flatLongAccess .lm1 16) false false false none]
  flush := none
  text := "fvadd $lm0v $lm8v $ln16v"

theorem parsedFloatAddSmoke_cycle0_lowers :
    lowerParsedFloatAdd? parsedFloatAddSmoke 0 0 0 0 0 =
      some (⟨0, by decide⟩, ⟨8, by decide⟩, ⟨16, by decide⟩) := by decide

theorem parsedFloatAddSmoke_cycle3_lowers :
    lowerParsedFloatAdd? parsedFloatAddSmoke 0 3 0 0 0 =
      some (⟨6, by decide⟩, ⟨14, by decide⟩, ⟨22, by decide⟩) := by decide


theorem parsedFloatAddSmoke_cycle1_lowers :
    lowerParsedFloatAdd? parsedFloatAddSmoke 0 1 0 0 0 =
      some (⟨2, by decide⟩, ⟨10, by decide⟩, ⟨18, by decide⟩) := by decide

theorem parsedFloatAddSmoke_cycle2_lowers :
    lowerParsedFloatAdd? parsedFloatAddSmoke 0 2 0 0 0 =
      some (⟨4, by decide⟩, ⟨12, by decide⟩, ⟨20, by decide⟩) := by decide

def parsedFloatSubtractSmoke : ParsedExpr where
  op := .mau .f false .add none false
  sources :=
    [.mem (flatLongAccess .lm0 0) false false false none,
     .mem (flatLongAccess .lm0 8) true false false none]
  destinations := [.mem (flatLongAccess .lm1 16) false false false none]
  flush := none
  text := "fvadd $lm0v -$lm8v $ln16v"

theorem parsedFloatSubtractSmoke_cycle0_lowers :
    lowerParsedFloatSubtract? parsedFloatSubtractSmoke 0 0 0 0 0 =
      some (⟨0, by decide⟩, ⟨8, by decide⟩, ⟨16, by decide⟩) := by decide

theorem parsedFloatSubtractSmoke_cycle3_lowers :
    lowerParsedFloatSubtract? parsedFloatSubtractSmoke 0 3 0 0 0 =
      some (⟨6, by decide⟩, ⟨14, by decide⟩, ⟨22, by decide⟩) := by decide

theorem executeParsedFloatSubtractLine_succeeds
    (files : PEMemory.IntegerRegisterFiles) :
    ∃ result, executeParsedFloatSubtractLine? parsedFloatSubtractSmoke files
      0 0 0 0 = some result := by
  unfold executeParsedFloatSubtractLine?
  apply executeParsedFloatSubtractCycles_success
  intro cycle member
  have hc := cycle.isLt
  have cases : cycle.val = 0 ∨ cycle.val = 1 ∨ cycle.val = 2 ∨ cycle.val = 3 := by
    simp at member
    omega
  rcases cases with h | h | h | h
  · have same : cycle = ⟨0, by decide⟩ := Fin.ext h
    subst cycle
    exact ⟨⟨0, by decide⟩, ⟨8, by decide⟩, ⟨16, by decide⟩, by decide⟩
  · have same : cycle = ⟨1, by decide⟩ := Fin.ext h
    subst cycle
    exact ⟨⟨2, by decide⟩, ⟨10, by decide⟩, ⟨18, by decide⟩, by decide⟩
  · have same : cycle = ⟨2, by decide⟩ := Fin.ext h
    subst cycle
    exact ⟨⟨4, by decide⟩, ⟨12, by decide⟩, ⟨20, by decide⟩, by decide⟩
  · have same : cycle = ⟨3, by decide⟩ := Fin.ext h
    subst cycle
    exact ⟨⟨6, by decide⟩, ⟨14, by decide⟩, ⟨22, by decide⟩, by decide⟩



def parsedFloatAddSmokeOutputAddress (cycle : Fin 4) :
    Fin (PEMemory.Bank.capacity .lm1) :=
  ⟨16 + 2 * cycle.val, by have hc := cycle.isLt; change 16 + 2 * cycle.val < 4096; omega⟩

theorem parsedFloatAddSmoke_outputAddress_lowers (cycle : Fin 4) :
    (PEMemory.address .lm1 .long
      (.flat (fun c => 16 + 2 * c.val)) 0 .direct 0 cycle) =
      parsedFloatAddSmokeOutputAddress cycle := by
  apply Fin.ext
  simp [PEMemory.address, PEMemory.Schedule.at, PEMemory.baseOffset,
    PEMemory.Adjustment.offset, PEMemory.count, PEMemory.Bank.capacity,
    PEMemory.Width.words, parsedFloatAddSmokeOutputAddress]
  omega

theorem parsedFloatAddSmoke_laterWrite_outsideEarlier
    (later earlier : Fin 4) (ordered : earlier.val < later.val)
    (lane : Fin 2) :
    2 ≤ PEMemory.distance .lm1 (parsedFloatAddSmokeOutputAddress later)
      (PEMemory.advance .lm1 (parsedFloatAddSmokeOutputAddress earlier) lane.val) := by
  have hl := later.isLt
  have he := earlier.isLt
  have hn := lane.isLt
  simp [parsedFloatAddSmokeOutputAddress, PEMemory.distance,
    PEMemory.advance, PEMemory.Bank.capacity]
  omega

theorem parsedFloatAddSmoke_laterWrite_preservesEarlier
    (memory : PEMemory.Memory .lm1) (value : BitVec 64)
    (later earlier : Fin 4) (ordered : earlier.val < later.val)
    (lane : Fin 2) :
    writePair memory (parsedFloatAddSmokeOutputAddress later) value
        (PEMemory.advance .lm1 (parsedFloatAddSmokeOutputAddress earlier) lane.val) =
      memory (PEMemory.advance .lm1 (parsedFloatAddSmokeOutputAddress earlier) lane.val) := by
  apply writePair_preservesOutside
  exact parsedFloatAddSmoke_laterWrite_outsideEarlier later earlier ordered lane

theorem parsedFloatAddSmoke_fourCycles_succeed
    (files : PEMemory.IntegerRegisterFiles) :
    ∃ result, executeParsedFloatAddLine? parsedFloatAddSmoke files 0 0 0 0 =
      some result := by
  unfold executeParsedFloatAddLine?
  apply executeParsedFloatAddCycles_success
  intro cycle member
  have hc := cycle.isLt
  have cases : cycle.val = 0 ∨ cycle.val = 1 ∨ cycle.val = 2 ∨ cycle.val = 3 := by
    simp at member
    omega
  rcases cases with h | h | h | h
  · have same : cycle = ⟨0, by decide⟩ := Fin.ext h
    subst cycle
    exact ⟨⟨0, by decide⟩, ⟨8, by decide⟩, ⟨16, by decide⟩, by decide⟩
  · have same : cycle = ⟨1, by decide⟩ := Fin.ext h
    subst cycle
    exact ⟨⟨2, by decide⟩, ⟨10, by decide⟩, ⟨18, by decide⟩, by decide⟩
  · have same : cycle = ⟨2, by decide⟩ := Fin.ext h
    subst cycle
    exact ⟨⟨4, by decide⟩, ⟨12, by decide⟩, ⟨20, by decide⟩, by decide⟩
  · have same : cycle = ⟨3, by decide⟩ := Fin.ext h
    subst cycle
    exact ⟨⟨6, by decide⟩, ⟨14, by decide⟩, ⟨22, by decide⟩, by decide⟩



set_option maxRecDepth 1024 in
theorem parsedFloatAddSmoke_fourCycles_finalReadback
    (files : PEMemory.IntegerRegisterFiles) :
    ∃ result,
      executeParsedFloatAddLine? parsedFloatAddSmoke files 0 0 0 0 = some result ∧
      readPair .lm1 result.lm1 ⟨22, by decide⟩ =
        FloatAdd.addBus (readPair .lm0 files.lm0 ⟨6, by decide⟩)
          (readPair .lm0 files.lm0 ⟨14, by decide⟩) ∧
      readPair .lm1 result.lm1 ⟨20, by decide⟩ =
        FloatAdd.addBus (readPair .lm0 files.lm0 ⟨4, by decide⟩)
          (readPair .lm0 files.lm0 ⟨12, by decide⟩) ∧
      readPair .lm1 result.lm1 ⟨18, by decide⟩ =
        FloatAdd.addBus (readPair .lm0 files.lm0 ⟨2, by decide⟩)
          (readPair .lm0 files.lm0 ⟨10, by decide⟩) ∧
      readPair .lm1 result.lm1 ⟨16, by decide⟩ =
        FloatAdd.addBus (readPair .lm0 files.lm0 ⟨0, by decide⟩)
          (readPair .lm0 files.lm0 ⟨8, by decide⟩) := by
  let f1 := commitLM1 files (addCycle files.lm0 files.lm0 files.lm1
    ⟨0, by decide⟩ ⟨8, by decide⟩ ⟨16, by decide⟩)
  let f2 := commitLM1 f1 (addCycle f1.lm0 f1.lm0 f1.lm1
    ⟨2, by decide⟩ ⟨10, by decide⟩ ⟨18, by decide⟩)
  let f3 := commitLM1 f2 (addCycle f2.lm0 f2.lm0 f2.lm1
    ⟨4, by decide⟩ ⟨12, by decide⟩ ⟨20, by decide⟩)
  have h0 := executeParsedFloatAddCycle_success parsedFloatAddSmoke files 0 0 0 0 0
    ⟨0, by decide⟩ ⟨8, by decide⟩ ⟨16, by decide⟩ parsedFloatAddSmoke_cycle0_lowers
  have h1 := executeParsedFloatAddCycle_success parsedFloatAddSmoke f1 0 1 0 0 0
    ⟨2, by decide⟩ ⟨10, by decide⟩ ⟨18, by decide⟩ parsedFloatAddSmoke_cycle1_lowers
  have h2 := executeParsedFloatAddCycle_success parsedFloatAddSmoke f2 0 2 0 0 0
    ⟨4, by decide⟩ ⟨12, by decide⟩ ⟨20, by decide⟩ parsedFloatAddSmoke_cycle2_lowers
  have h3 := executeParsedFloatAddCycle_success parsedFloatAddSmoke f3 0 3 0 0 0
    ⟨6, by decide⟩ ⟨14, by decide⟩ ⟨22, by decide⟩ parsedFloatAddSmoke_cycle3_lowers
  refine ⟨commitLM1 f3 (addCycle f3.lm0 f3.lm0 f3.lm1
    ⟨6, by decide⟩ ⟨14, by decide⟩ ⟨22, by decide⟩), ?_, ?_, ?_, ?_, ?_⟩
  · change executeParsedFloatAddCycles? parsedFloatAddSmoke files 0
      (List.finRange 4) 0 0 0 = some (commitLM1 f3 (addCycle f3.lm0 f3.lm0 f3.lm1
        ⟨6, by decide⟩ ⟨14, by decide⟩ ⟨22, by decide⟩))
    have cycles : List.finRange 4 = ([0, 1, 2, 3] : List (Fin 4)) := by decide
    rw [cycles]
    simp only [executeParsedFloatAddCycles?, h0, h1, h2, h3]
    rfl
  · simp only [commitLM1]
    have h3lm : f3.lm0 = files.lm0 := by
      simp only [f3, f2, f1, commitLM1_lm0]
    rw [h3lm]
    exact binaryCycle_readback FloatAdd.addBus files.lm0 files.lm0 f3.lm1
      ⟨6, by decide⟩ ⟨14, by decide⟩ ⟨22, by decide⟩
  · simp only [commitLM1]
    have hpair3 : readPair .lm1
        (addCycle f3.lm0 f3.lm0 f3.lm1 ⟨6, by decide⟩ ⟨14, by decide⟩ ⟨22, by decide⟩)
        ⟨20, by decide⟩ = readPair .lm1 f3.lm1 ⟨20, by decide⟩ := by
      simpa [addCycle, binaryCycle, parsedFloatAddSmokeOutputAddress] using
        (writePair_preservesPairOutside _ (parsedFloatAddSmokeOutputAddress 3)
          (parsedFloatAddSmokeOutputAddress 2)
          (FloatAdd.addBus
            (readPair .lm0 _ ⟨6, by decide⟩)
            (readPair .lm0 _ ⟨14, by decide⟩))
          (by intro lane; exact
            parsedFloatAddSmoke_laterWrite_outsideEarlier 3 2 (by decide) lane))
    rw [hpair3]
    simp only [f3, commitLM1]
    have h2lm : f2.lm0 = files.lm0 := by simp only [f2, f1, commitLM1_lm0]
    rw [h2lm]
    exact binaryCycle_readback FloatAdd.addBus files.lm0 files.lm0 f2.lm1
      ⟨4, by decide⟩ ⟨12, by decide⟩ ⟨20, by decide⟩
  · simp only [commitLM1]
    have hpair3 : readPair .lm1
        (addCycle f3.lm0 f3.lm0 f3.lm1 ⟨6, by decide⟩ ⟨14, by decide⟩ ⟨22, by decide⟩)
        ⟨18, by decide⟩ = readPair .lm1 f3.lm1 ⟨18, by decide⟩ := by
      simpa [addCycle, binaryCycle, parsedFloatAddSmokeOutputAddress] using
        (writePair_preservesPairOutside _ (parsedFloatAddSmokeOutputAddress 3)
          (parsedFloatAddSmokeOutputAddress 1)
          (FloatAdd.addBus
            (readPair .lm0 _ ⟨6, by decide⟩)
            (readPair .lm0 _ ⟨14, by decide⟩))
          (by intro lane; exact
            parsedFloatAddSmoke_laterWrite_outsideEarlier 3 1 (by decide) lane))
    rw [hpair3]
    simp only [f3, commitLM1]
    have hpair2 : readPair .lm1
        (addCycle f2.lm0 f2.lm0 f2.lm1 ⟨4, by decide⟩ ⟨12, by decide⟩ ⟨20, by decide⟩)
        ⟨18, by decide⟩ = readPair .lm1 f2.lm1 ⟨18, by decide⟩ := by
      simpa [addCycle, binaryCycle, parsedFloatAddSmokeOutputAddress] using
        (writePair_preservesPairOutside _ (parsedFloatAddSmokeOutputAddress 2)
          (parsedFloatAddSmokeOutputAddress 1)
          (FloatAdd.addBus
            (readPair .lm0 _ ⟨4, by decide⟩)
            (readPair .lm0 _ ⟨12, by decide⟩))
          (by intro lane; exact
            parsedFloatAddSmoke_laterWrite_outsideEarlier 2 1 (by decide) lane))
    rw [hpair2]
    simp only [f2, commitLM1]
    have h1lm : f1.lm0 = files.lm0 := by simp only [f1, commitLM1_lm0]
    rw [h1lm]
    exact binaryCycle_readback FloatAdd.addBus files.lm0 files.lm0 f1.lm1
      ⟨2, by decide⟩ ⟨10, by decide⟩ ⟨18, by decide⟩
  · simp only [commitLM1]
    have hpair3 : readPair .lm1
        (addCycle f3.lm0 f3.lm0 f3.lm1 ⟨6, by decide⟩ ⟨14, by decide⟩ ⟨22, by decide⟩)
        ⟨16, by decide⟩ = readPair .lm1 f3.lm1 ⟨16, by decide⟩ := by
      simpa [addCycle, binaryCycle, parsedFloatAddSmokeOutputAddress] using
        (writePair_preservesPairOutside _ (parsedFloatAddSmokeOutputAddress 3)
          (parsedFloatAddSmokeOutputAddress 0)
          (FloatAdd.addBus
            (readPair .lm0 _ ⟨6, by decide⟩)
            (readPair .lm0 _ ⟨14, by decide⟩))
          (by intro lane; exact
            parsedFloatAddSmoke_laterWrite_outsideEarlier 3 0 (by decide) lane))
    rw [hpair3]
    simp only [f3, commitLM1]
    have hpair2 : readPair .lm1
        (addCycle f2.lm0 f2.lm0 f2.lm1 ⟨4, by decide⟩ ⟨12, by decide⟩ ⟨20, by decide⟩)
        ⟨16, by decide⟩ = readPair .lm1 f2.lm1 ⟨16, by decide⟩ := by
      simpa [addCycle, binaryCycle, parsedFloatAddSmokeOutputAddress] using
        (writePair_preservesPairOutside _ (parsedFloatAddSmokeOutputAddress 2)
          (parsedFloatAddSmokeOutputAddress 0)
          (FloatAdd.addBus
            (readPair .lm0 _ ⟨4, by decide⟩)
            (readPair .lm0 _ ⟨12, by decide⟩))
          (by intro lane; exact
            parsedFloatAddSmoke_laterWrite_outsideEarlier 2 0 (by decide) lane))
    rw [hpair2]
    simp only [f2, commitLM1]
    have hpair1 : readPair .lm1
        (addCycle f1.lm0 f1.lm0 f1.lm1 ⟨2, by decide⟩ ⟨10, by decide⟩ ⟨18, by decide⟩)
        ⟨16, by decide⟩ = readPair .lm1 f1.lm1 ⟨16, by decide⟩ := by
      simpa [addCycle, binaryCycle, parsedFloatAddSmokeOutputAddress] using
        (writePair_preservesPairOutside _ (parsedFloatAddSmokeOutputAddress 1)
          (parsedFloatAddSmokeOutputAddress 0)
          (FloatAdd.addBus
            (readPair .lm0 _ ⟨2, by decide⟩)
            (readPair .lm0 _ ⟨10, by decide⟩))
          (by intro lane; exact
            parsedFloatAddSmoke_laterWrite_outsideEarlier 1 0 (by decide) lane))
    rw [hpair1]
    simp only [f1, commitLM1]
    exact binaryCycle_readback FloatAdd.addBus files.lm0 files.lm0 files.lm1
      ⟨0, by decide⟩ ⟨8, by decide⟩ ⟨16, by decide⟩

theorem executeParsedFloatAddCycle_preservesLM0 (expression : ParsedExpr)
    (files : PEMemory.IntegerRegisterFiles) (pe cycle : Fin 4)
    (bar0 bar1 : BitVec 12) (tWord : BitVec 32)
    (leftAddress rightAddress : Fin (PEMemory.Bank.capacity .lm0))
    (destinationAddress : Fin (PEMemory.Bank.capacity .lm1))
    (lowered : lowerParsedFloatAdd? expression pe cycle bar0 bar1 tWord =
      some (leftAddress, rightAddress, destinationAddress)) :
    (executeParsedFloatAddCycle? expression files pe cycle bar0 bar1 tWord).map
      (fun next => next.lm0) = some files.lm0 := by
  rw [executeParsedFloatAddCycle_success expression files pe cycle bar0 bar1 tWord
    leftAddress rightAddress destinationAddress lowered]
  rfl

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

theorem subtractCycle_preservesOutside (left : PEMemory.Memory .lm0)
    (right : PEMemory.Memory .lm0) (output : PEMemory.Memory .lm1)
    (leftStart rightStart : Fin (PEMemory.Bank.capacity .lm0))
    (outputStart target : Fin (PEMemory.Bank.capacity .lm1))
    (outside : 2 ≤ PEMemory.distance .lm1 outputStart target) :
    subtractCycle left right output leftStart rightStart outputStart target = output target := by
  exact binaryCycle_preservesOutside FloatSubtract.subtractBus left right output
    leftStart rightStart outputStart target outside

theorem multiplySevenCycle_readback (input : PEMemory.Memory .lm0)
    (output : PEMemory.Memory .lm1)
    (inputStart : Fin (PEMemory.Bank.capacity .lm0))
    (outputStart : Fin (PEMemory.Bank.capacity .lm1)) :
    readPair .lm1 (multiplySevenCycle input output inputStart outputStart) outputStart =
      FloatMultiply.multiplySevenBus (readPair .lm0 input inputStart) := by
  exact readPair_after_writePair output outputStart _

end ProofsLean.MNCore.FloatPEMemory
