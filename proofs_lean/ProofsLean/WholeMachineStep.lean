import ProofsLean.MachineState
import ProofsLean.PEMachine
import ProofsLean.FloatPEMemory

/-! A whole-state transition for the connected PE integer ALU, single-precision
vector `fvadd`/`fvmul`, matrix-read, and raw D/F/G matrix-write fragments. It
runs the same issue-line transaction independently at every physical PE, then
updates ALU/MAU/MREADF/LBF forwarding state. Other producer units remain unresolved. -/
namespace ProofsLean.MNCore

open Issue
open PEMemory

def parsedExprIsIntegerProducer (expression : ParsedExpr) : Bool :=
  match expression.op with
  | .alu .. | .zero | .immediate .. => true
  | _ => false

def parsedExprIsSupportedPELineProducer (expression : ParsedExpr) : Bool :=
  match expression.op with
  | .alu .. | .zero | .immediate .. | .matrixRead .. | .wait .. | .noforward => true
  | .mau .f false .add none false | .mau .f false .mul none false
  | .mau .f false .fma none false => true
  | .matrixWrite .d | .matrixWrite .f | .matrixWrite .g => true
  | _ => false

def parsedExprIsMatrixReadProducer (expression : ParsedExpr) : Bool :=
  match expression.op with
  | .matrixRead .. => true
  | _ => false

def parsedExprIsMatrixWriteProducer (expression : ParsedExpr) : Bool :=
  match expression.op with
  | .matrixWrite .. => true
  | _ => false

def parsedExprIsSupportedFloatMAUProducer (expression : ParsedExpr) : Bool :=
  match expression.op with
  | .mau .f false .add none false | .mau .f false .mul none false
  | .mau .f false .fma none false => true
  | _ => false

def lowerParsedFloatMultiply? (expression : ParsedExpr) (pe cycle : Fin 4)
    (bar0 bar1 : BitVec 12) (tWord : BitVec 32) :
    Option (Fin (Bank.capacity .lm0) × Fin (Bank.capacity .lm0) ×
      Fin (Bank.capacity .lm1)) := do
  match expression.op with
  | .mau .f false .mul none false => pure ()
  | _ => none
  match expression.sources, expression.destinations with
  | [.mem left false false false none, .mem right false false false none],
      [.mem destination false false false none] =>
      let leftAccess ← ParsedOperand.toDirectMemoryAccess?
        (.mem left false false false none) pe cycle bar0 bar1 tWord
      let rightAccess ← ParsedOperand.toDirectMemoryAccess?
        (.mem right false false false none) pe cycle bar0 bar1 tWord
      let destinationAccess ← ParsedOperand.toDirectMemoryAccess?
        (.mem destination false false false none) pe cycle bar0 bar1 tWord
      let leftAddress ← FloatPEMemory.lm0LongAddress? leftAccess
      let rightAddress ← FloatPEMemory.lm0LongAddress? rightAccess
      let destinationAddress ← FloatPEMemory.lm1LongAddress? destinationAccess
      some (leftAddress, rightAddress, destinationAddress)
  | _, _ => none

def lowerParsedFloatFma? (expression : ParsedExpr) (pe cycle : Fin 4)
    (bar0 bar1 : BitVec 12) (tWord : BitVec 32) :
    Option (Fin (Bank.capacity .lm0) × Fin (Bank.capacity .lm0) ×
      Fin (Bank.capacity .lm0) × Fin (Bank.capacity .lm1)) := do
  match expression.op with
  | .mau .f false .fma none false => pure ()
  | _ => none
  match expression.sources, expression.destinations with
  | [.mem left false false false none, .mem right false false false none,
      .mem accumulator false false false none], [.mem destination false false false none] =>
      let leftAccess ← ParsedOperand.toDirectMemoryAccess?
        (.mem left false false false none) pe cycle bar0 bar1 tWord
      let rightAccess ← ParsedOperand.toDirectMemoryAccess?
        (.mem right false false false none) pe cycle bar0 bar1 tWord
      let accumulatorAccess ← ParsedOperand.toDirectMemoryAccess?
        (.mem accumulator false false false none) pe cycle bar0 bar1 tWord
      let destinationAccess ← ParsedOperand.toDirectMemoryAccess?
        (.mem destination false false false none) pe cycle bar0 bar1 tWord
      let leftAddress ← FloatPEMemory.lm0LongAddress? leftAccess
      let rightAddress ← FloatPEMemory.lm0LongAddress? rightAccess
      let accumulatorAddress ← FloatPEMemory.lm0LongAddress? accumulatorAccess
      let destinationAddress ← FloatPEMemory.lm1LongAddress? destinationAccess
      some (leftAddress, rightAddress, accumulatorAddress, destinationAddress)
  | _, _ => none

def singleFmaBus (left right accumulator : BitVec 64) : BitVec 64 :=
  SingleFMA.singleFma (left.extractLsb' 32 32) (right.extractLsb' 32 32)
      (accumulator.extractLsb' 32 32) ++
    SingleFMA.singleFma (left.extractLsb' 0 32) (right.extractLsb' 0 32)
      (accumulator.extractLsb' 0 32)

theorem lowerParsedFloatFma?_direct
    (left right accumulator destination : Access) (pe cycle : Fin 4)
    (bar0 bar1 : BitVec 12) (tWord : BitVec 32)
    (leftAddress rightAddress accumulatorAddress : Fin (Bank.capacity .lm0))
    (destinationAddress : Fin (Bank.capacity .lm1))
    (leftLowered : ParsedOperand.toDirectMemoryAccess?
      (.mem left false false false none) pe cycle bar0 bar1 tWord =
        some ⟨.lm0, .long, leftAddress⟩)
    (rightLowered : ParsedOperand.toDirectMemoryAccess?
      (.mem right false false false none) pe cycle bar0 bar1 tWord =
        some ⟨.lm0, .long, rightAddress⟩)
    (accumulatorLowered : ParsedOperand.toDirectMemoryAccess?
      (.mem accumulator false false false none) pe cycle bar0 bar1 tWord =
        some ⟨.lm0, .long, accumulatorAddress⟩)
    (destinationLowered : ParsedOperand.toDirectMemoryAccess?
      (.mem destination false false false none) pe cycle bar0 bar1 tWord =
        some ⟨.lm1, .long, destinationAddress⟩) :
    lowerParsedFloatFma?
      ⟨.mau .f false .fma none false,
        [.mem left false false false none, .mem right false false false none,
          .mem accumulator false false false none],
        [.mem destination false false false none], none, "fvfma"⟩ pe cycle bar0 bar1 tWord =
      some (leftAddress, rightAddress, accumulatorAddress, destinationAddress) := by
  simp [lowerParsedFloatFma?, leftLowered, rightLowered, accumulatorLowered,
    destinationLowered, FloatPEMemory.lm0LongAddress?, FloatPEMemory.lm1LongAddress?]

theorem lowerParsedFloatMultiply?_fvmul
    (left right destination : Access) (pe cycle : Fin 4)
    (bar0 bar1 : BitVec 12) (tWord : BitVec 32)
    (leftAddress rightAddress : Fin (Bank.capacity .lm0))
    (destinationAddress : Fin (Bank.capacity .lm1))
    (leftLowered : ParsedOperand.toDirectMemoryAccess?
      (.mem left false false false none) pe cycle bar0 bar1 tWord =
        some ⟨.lm0, .long, leftAddress⟩)
    (rightLowered : ParsedOperand.toDirectMemoryAccess?
      (.mem right false false false none) pe cycle bar0 bar1 tWord =
        some ⟨.lm0, .long, rightAddress⟩)
    (destinationLowered : ParsedOperand.toDirectMemoryAccess?
      (.mem destination false false false none) pe cycle bar0 bar1 tWord =
        some ⟨.lm1, .long, destinationAddress⟩) :
    lowerParsedFloatMultiply?
      ⟨.mau .f false .mul none false,
        [.mem left false false false none, .mem right false false false none],
        [.mem destination false false false none], none, "fvmul"⟩ pe cycle bar0 bar1 tWord =
      some (leftAddress, rightAddress, destinationAddress) := by
  simp [lowerParsedFloatMultiply?, leftLowered, rightLowered, destinationLowered,
    FloatPEMemory.lm0LongAddress?, FloatPEMemory.lm1LongAddress?]

def executeParsedFloatMAUCycleAtPE (readFiles currentFiles : IntegerRegisterFiles)
    (expression : ParsedExpr) (pe cycle : Fin 4) (bar0 bar1 : BitVec 12)
    (tWord : BitVec 32) : ProofsLean.StepResult (IntegerRegisterFiles × IntegerALU.Bus) :=
  match expression.op with
  | .mau .f false .fma none false =>
    match lowerParsedFloatFma? expression pe cycle bar0 bar1 tWord with
    | none => .unknown
    | some (leftAddress, rightAddress, accumulatorAddress, destinationAddress) =>
        let left := FloatPEMemory.readPair .lm0 readFiles.lm0 leftAddress
        let right := FloatPEMemory.readPair .lm0 readFiles.lm0 rightAddress
        let accumulator := FloatPEMemory.readPair .lm0 readFiles.lm0 accumulatorAddress
        let output := singleFmaBus left right accumulator
        let nextLM1 := FloatPEMemory.writePair currentFiles.lm1 destinationAddress output
        .ok ({ currentFiles with lm1 := nextLM1 }, ⟨output, 0⟩)
  | .mau .f false .mul none false =>
    match lowerParsedFloatMultiply? expression pe cycle bar0 bar1 tWord with
    | none => .unknown
    | some (leftAddress, rightAddress, destinationAddress) =>
        let left := FloatPEMemory.readPair .lm0 readFiles.lm0 leftAddress
        let right := FloatPEMemory.readPair .lm0 readFiles.lm0 rightAddress
        let output := FloatMultiply.multiplyBus left right
        let nextLM1 := FloatPEMemory.writePair currentFiles.lm1 destinationAddress output
        .ok ({ currentFiles with lm1 := nextLM1 }, ⟨output, 0⟩)
  | _ => match FloatPEMemory.lowerParsedFloatAdd? expression pe cycle bar0 bar1 tWord with
  | none =>
    match FloatPEMemory.lowerParsedFloatSubtract? expression pe cycle bar0 bar1 tWord with
    | none => .unknown
    | some (leftAddress, rightAddress, destinationAddress) =>
        let left := FloatPEMemory.readPair .lm0 readFiles.lm0 leftAddress
        let right := FloatPEMemory.readPair .lm0 readFiles.lm0 rightAddress
        let output := FloatSubtract.subtractBus left right
        let nextLM1 := FloatPEMemory.writePair currentFiles.lm1 destinationAddress output
        .ok ({ currentFiles with lm1 := nextLM1 }, ⟨output, 0⟩)
  | some (leftAddress, rightAddress, destinationAddress) =>
      let left := FloatPEMemory.readPair .lm0 readFiles.lm0 leftAddress
      let right := FloatPEMemory.readPair .lm0 readFiles.lm0 rightAddress
      let output := FloatAdd.addBus left right
      let nextLM1 := FloatPEMemory.writePair currentFiles.lm1 destinationAddress output
      .ok ({ currentFiles with lm1 := nextLM1 }, ⟨output, 0⟩)

theorem executeParsedFloatMAUCycleAtPE_mul_success
    (readFiles currentFiles : IntegerRegisterFiles) (expression : ParsedExpr)
    (pe cycle : Fin 4) (bar0 bar1 : BitVec 12) (tWord : BitVec 32)
    (leftAddress rightAddress : Fin (Bank.capacity .lm0))
    (destinationAddress : Fin (Bank.capacity .lm1))
    (isMul : expression.op = .mau .f false .mul none false)
    (lowered : lowerParsedFloatMultiply? expression pe cycle bar0 bar1 tWord =
      some (leftAddress, rightAddress, destinationAddress)) :
    let output := FloatMultiply.multiplyBus
      (FloatPEMemory.readPair .lm0 readFiles.lm0 leftAddress)
      (FloatPEMemory.readPair .lm0 readFiles.lm0 rightAddress)
    executeParsedFloatMAUCycleAtPE readFiles currentFiles expression pe cycle bar0 bar1 tWord =
      .ok ({ currentFiles with lm1 :=
        (FloatPEMemory.writePair currentFiles.lm1 destinationAddress output) },
        ⟨output, 0⟩) := by
  simp [executeParsedFloatMAUCycleAtPE, isMul, lowered]

theorem executeParsedFloatMAUCycleAtPE_fma_success
    (readFiles currentFiles : IntegerRegisterFiles) (expression : ParsedExpr)
    (pe cycle : Fin 4) (bar0 bar1 : BitVec 12) (tWord : BitVec 32)
    (leftAddress rightAddress accumulatorAddress : Fin (Bank.capacity .lm0))
    (destinationAddress : Fin (Bank.capacity .lm1))
    (isFma : expression.op = .mau .f false .fma none false)
    (lowered : lowerParsedFloatFma? expression pe cycle bar0 bar1 tWord =
      some (leftAddress, rightAddress, accumulatorAddress, destinationAddress)) :
    let output := singleFmaBus
      (FloatPEMemory.readPair .lm0 readFiles.lm0 leftAddress)
      (FloatPEMemory.readPair .lm0 readFiles.lm0 rightAddress)
      (FloatPEMemory.readPair .lm0 readFiles.lm0 accumulatorAddress)
    executeParsedFloatMAUCycleAtPE readFiles currentFiles expression pe cycle bar0 bar1 tWord =
      .ok ({ currentFiles with lm1 :=
        (FloatPEMemory.writePair currentFiles.lm1 destinationAddress output) },
        ⟨output, 0⟩) := by
  simp [executeParsedFloatMAUCycleAtPE, isFma, lowered]

theorem executeParsedFloatMAUCycleAtPE_add_success
    (readFiles currentFiles : IntegerRegisterFiles) (expression : ParsedExpr)
    (pe cycle : Fin 4) (bar0 bar1 : BitVec 12) (tWord : BitVec 32)
    (leftAddress rightAddress : Fin (Bank.capacity .lm0))
    (destinationAddress : Fin (Bank.capacity .lm1))
    (isAdd : expression.op = .mau .f false .add none false)
    (lowered : FloatPEMemory.lowerParsedFloatAdd? expression pe cycle bar0 bar1 tWord =
      some (leftAddress, rightAddress, destinationAddress)) :
    let output := FloatAdd.addBus
      (FloatPEMemory.readPair .lm0 readFiles.lm0 leftAddress)
      (FloatPEMemory.readPair .lm0 readFiles.lm0 rightAddress)
    executeParsedFloatMAUCycleAtPE readFiles currentFiles expression pe cycle bar0 bar1 tWord =
      .ok ({ currentFiles with lm1 :=
        (FloatPEMemory.writePair currentFiles.lm1 destinationAddress output) },
        ⟨output, 0⟩) := by
  simp [executeParsedFloatMAUCycleAtPE, isAdd, lowered]

def executeParsedFloatMAUCyclesAtPE (readFiles : IntegerRegisterFiles)
    (expression : ParsedExpr) (pe : Fin 4) (bar0 bar1 : BitVec 12)
    (tWord : BitVec 32) : List (Fin 4) → IntegerRegisterFiles →
      (Fin 4 → IntegerALU.Bus) → ProofsLean.StepResult
        (IntegerRegisterFiles × (Fin 4 → IntegerALU.Bus))
  | [], files, outputs => .ok (files, outputs)
  | cycle :: rest, files, outputs =>
      match executeParsedFloatMAUCycleAtPE readFiles files expression pe cycle bar0 bar1 tWord with
      | .failure => .failure
      | .unknown => .unknown
      | .ok (nextFiles, output) =>
          executeParsedFloatMAUCyclesAtPE readFiles expression pe bar0 bar1 tWord rest
            nextFiles (fun index => if index = cycle then output else outputs index)

def executeParsedFloatMAUsAtPE (readState currentFiles : IntegerRegisterFiles)
    (pe : Fin 4) (bar0 bar1 : BitVec 12) (tWord : BitVec 32)
    (expressions : List ParsedExpr) : ProofsLean.StepResult
      (IntegerRegisterFiles × (Fin 4 → IntegerALU.Bus) × Bool) :=
  let floatAdds := expressions.filter parsedExprIsSupportedFloatMAUProducer
  let rec run (remaining : List ParsedExpr) (files : IntegerRegisterFiles)
      (outputs : Fin 4 → IntegerALU.Bus) :
      ProofsLean.StepResult (IntegerRegisterFiles × (Fin 4 → IntegerALU.Bus)) :=
    match remaining with
    | [] => .ok (files, outputs)
    | expression :: rest =>
        match executeParsedFloatMAUCyclesAtPE readState expression pe bar0 bar1 tWord
            [0, 1, 2, 3] files (fun _ => ⟨0, 0⟩) with
        | .failure => .failure
        | .unknown => .unknown
        | .ok (nextFiles, nextOutputs) => run rest nextFiles nextOutputs
  match run floatAdds currentFiles (fun _ => ⟨0, 0⟩) with
  | .failure => .failure
  | .unknown => .unknown
  | .ok (files, outputs) => .ok (files, outputs, !floatAdds.isEmpty)

structure MABCoordinate where
  group : Fin 4
  l2b : Fin 2
  l1b : Fin 8
  mab : Fin 16
  deriving DecidableEq, Repr

def allMABCoordinates : List MABCoordinate :=
  (List.finRange 4).flatMap fun group =>
    (List.finRange 2).flatMap fun l2b =>
      (List.finRange 8).flatMap fun l1b =>
        (List.finRange 16).map fun mab => ⟨group, l2b, l1b, mab⟩

def physicalPEId (coordinate : MABCoordinate) (pe : Fin 4) : PEId :=
  ⟨(((coordinate.group.val * 2 + coordinate.l2b.val) * 8 + coordinate.l1b.val) * 16 +
      coordinate.mab.val) * 4 + pe.val, by
    have hg := coordinate.group.isLt
    have h2 := coordinate.l2b.isLt
    have h1 := coordinate.l1b.isLt
    have hm := coordinate.mab.isLt
    have hp := pe.isLt
    omega⟩

def matrixWriteGroupContext (state : State) (coordinate : MABCoordinate) :
    ParsedPEGroupContext :=
  { group := coordinate.group
    l2b := coordinate.l2b
    l1b := coordinate.l1b
    mab := coordinate.mab
    bar0 := fun pe => state.peContext (physicalPEId coordinate pe) |>.bar0
    bar1 := fun pe => state.peContext (physicalPEId coordinate pe) |>.bar1
    tWord := fun pe => state.peContext (physicalPEId coordinate pe) |>.tWord }

def parsedMatrixWriteSource? (expression : ParsedExpr)
    (context : ParsedIntegerContext) : Option ParsedIntegerInput :=
  match expression.op with
  | .matrixWrite .d =>
      (ParsedExpr.toDirectDoubleMatrixWriteAccesses? expression context).map
        ParsedDoubleMatrixWriteAccesses.source
  | .matrixWrite .f | .matrixWrite .g =>
      (ParsedExpr.toDirectSingleMatrixWriteAccesses? expression context).map
        ParsedSingleMatrixWriteAccesses.source
  | _ => none

def readParsedMatrixWriteBuses (state : State) (coordinate : MABCoordinate)
    (expression : ParsedExpr) (cycle : Fin 4) :
    ProofsLean.StepResult (Fin 4 → IntegerALU.Bus) :=
  let groupContext := matrixWriteGroupContext state coordinate
  let rec readPEs (remaining : List (Fin 4)) (buses : Fin 4 → IntegerALU.Bus) :
      ProofsLean.StepResult (Fin 4 → IntegerALU.Bus) :=
    match remaining with
    | [] => .ok buses
    | pe :: rest =>
        let context := groupContext.at pe cycle
        match parsedMatrixWriteSource? expression context with
        | none => .unknown
        | some source =>
            match ParsedIntegerInput.readWithForwarding
                (state.peRegisters (physicalPEId coordinate pe))
                (state.forwarding (physicalPEId coordinate pe)) cycle source with
            | .failure => .failure
            | .unknown => .unknown
            | .ok bus => readPEs rest (fun index => if index = pe then bus else buses index)
  readPEs parsedMatrixWritePEs (fun _ => ⟨0, 0⟩)

def executeParsedMatrixWriteCycle (state : State) (coordinate : MABCoordinate)
    (expression : ParsedExpr) (store : ParsedMatrixReadStore) (cycle : Fin 4) :
    ProofsLean.StepResult ParsedMatrixReadStore :=
  let groupContext := matrixWriteGroupContext state coordinate
  match expression.op with
  | .matrixWrite .d =>
      match ParsedExpr.toDirectDoubleMatrixWriteAccesses? expression
          (groupContext.at 0 cycle) with
      | none => .unknown
      | some accesses =>
          match readParsedMatrixWriteBuses state coordinate expression cycle with
          | .failure => .failure
          | .unknown => .unknown
          | .ok buses =>
              .ok (writeParsedDoubleMatrixStoreRow store coordinate.mab accesses.sideY
                (doubleMatrixWriteRowAt accesses.row cycle) (fun pe => (buses pe).high))
  | .matrixWrite .f | .matrixWrite .g =>
      match ParsedExpr.toDirectSingleMatrixWriteAccesses? expression
          (groupContext.at 0 cycle) with
      | none => .unknown
      | some accesses =>
          match readParsedMatrixWriteBuses state coordinate expression cycle with
          | .failure => .failure
          | .unknown => .unknown
          | .ok buses =>
              .ok (writeParsedSingleMatrixStoreRow store coordinate.mab accesses.sideY
                (singleMatrixWriteRowAt accesses.row cycle) (singleMatrixWriteValues buses))
  | _ => .unknown

def executeParsedMatrixWriteCycles (state : State) (coordinate : MABCoordinate)
    (expression : ParsedExpr) : List (Fin 4) → ParsedMatrixReadStore →
      ProofsLean.StepResult ParsedMatrixReadStore
  | [], store => .ok store
  | cycle :: rest, store =>
      match executeParsedMatrixWriteCycle state coordinate expression store cycle with
      | .failure => .failure
      | .unknown => .unknown
      | .ok nextStore => executeParsedMatrixWriteCycles state coordinate expression rest nextStore

def executeParsedMatrixWriteFourCycle (state : State) (coordinate : MABCoordinate)
    (expression : ParsedExpr) (store : ParsedMatrixReadStore) :
    ProofsLean.StepResult ParsedMatrixReadStore :=
  executeParsedMatrixWriteCycles state coordinate expression [0, 1, 2, 3] store

def executeParsedMatrixWritesAtMAB (readState currentState : State)
    (coordinate : MABCoordinate) (expressions : List ParsedExpr) :
    ProofsLean.StepResult State :=
  let matrixWrites := expressions.filter parsedExprIsMatrixWriteProducer
  let rec applyWrites (remaining : List ParsedExpr) (store : ParsedMatrixReadStore) :
      ProofsLean.StepResult ParsedMatrixReadStore :=
    match remaining with
    | [] => .ok store
    | expression :: rest =>
        match executeParsedMatrixWriteFourCycle readState coordinate expression store with
        | .failure => .failure
        | .unknown => .unknown
        | .ok nextStore => applyWrites rest nextStore
  match applyWrites matrixWrites
      (currentState.matrixRegisters coordinate.group coordinate.l2b coordinate.l1b) with
  | .failure => .failure
  | .unknown => .unknown
  | .ok nextStore =>
      .ok { currentState with matrixRegisters := fun group l2b l1b =>
        if (group, l2b, l1b) = (coordinate.group, coordinate.l2b, coordinate.l1b)
        then nextStore else currentState.matrixRegisters group l2b l1b }

def executeParsedMatrixWritesAtMABs (readState : State) (coordinates : List MABCoordinate)
    (expressions : List ParsedExpr) (currentState : State) :
    ProofsLean.StepResult State :=
  if !(expressions.any parsedExprIsMatrixWriteProducer) then .ok currentState
  else
    match coordinates with
    | [] => .ok currentState
    | coordinate :: rest =>
        match executeParsedMatrixWritesAtMAB readState currentState coordinate expressions with
        | .failure => .failure
        | .unknown => .unknown
        | .ok nextState =>
            executeParsedMatrixWritesAtMABs readState rest expressions nextState

def forwardingValueValid : Forwarding.Value IntegerALU.Bus → Bool
  | .known _ => true
  | .poison | .unknown => false

def updateSupportedPELineForwarding (old prepared : Forwarding.Slots)
    (noForward hasALUProducer hasMAUProducer hasMatrixReadProducer : Bool) :
    ProofsLean.StepResult Forwarding.Slots :=
  match Forwarding.advanceReference old (.issue noForward fun unit =>
      match unit with
      | .alu => if hasALUProducer then some fun cycle => prepared .alu cycle else none
      | .mau => if hasMAUProducer then some fun cycle => prepared .mau cycle else none
      | .matrixRead =>
          if hasMatrixReadProducer then some fun cycle => prepared .matrixRead cycle else none
      | .l1ToPE => none) with
  | .failure => .failure
  | .unknown => .unknown
  | .ok advanced =>
      .ok (fun unit cycle =>
        if unit = .l1ToPE then old unit cycle else advanced unit cycle)

def updateIntegerLineForwardingValid
    (old : Forwarding.Unit → Fin 4 → Bool)
    (slots : Forwarding.Slots) (noForward : Bool) :
    Forwarding.Unit → Fin 4 → Bool :=
  fun unit cycle =>
    if noForward then old unit cycle
    else if unit = .l1ToPE then old unit cycle
    else forwardingValueValid (slots unit cycle)

def executeIntegerProducerLineAtPE (expressions : List ParsedExpr)
    (state : State) (pe : PEId) : ProofsLean.StepResult State :=
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
  let oldSlots := state.forwarding pe
  let matrixStore := state.matrixRegisters context.group context.l2b context.l1b
  let peExpressions := expressions.filter fun expression =>
    !parsedExprIsMatrixWriteProducer expression &&
      !parsedExprIsSupportedFloatMAUProducer expression
  match parsedIntegerMatrixReadLineFourCycleStep (state.peRegisters pe) oldSlots
      matrixStore peExpressions control false with
  | .failure => .failure
  | .unknown => .unknown
  | .ok (registers, integerPreparedSlots) =>
    match executeParsedFloatMAUsAtPE (state.peRegisters pe) registers
        coordinates.pe context.bar0 context.bar1 context.tWord expressions with
    | .failure => .failure
    | .unknown => .unknown
    | .ok (registersWithFloat, floatOutputs, hasMAUProducer) =>
      let preparedSlots := fun unit cycle =>
        if unit = .mau && hasMAUProducer then .known (floatOutputs cycle)
        else integerPreparedSlots unit cycle
      let noForward := expressions.any fun expression =>
        match expression.op with
        | .noforward => true
        | _ => false
      let hasALUProducer := expressions.any parsedExprIsIntegerProducer
      let hasMatrixReadProducer := expressions.any parsedExprIsMatrixReadProducer
      match updateSupportedPELineForwarding oldSlots preparedSlots
          noForward hasALUProducer hasMAUProducer hasMatrixReadProducer with
      | .failure => .failure
      | .unknown => .unknown
      | .ok forwarding =>
          let forwardingValid := updateIntegerLineForwardingValid
            (state.forwardingValid pe) forwarding noForward
          .ok { state with
            peRegisters := fun other =>
              if other = pe then registersWithFloat else state.peRegisters other
            forwarding := fun other =>
              if other = pe then forwarding else state.forwarding other
            forwardingValid := fun other =>
              if other = pe then forwardingValid else state.forwardingValid other }

def executeIntegerProducerLineAtPEs (expressions : List ParsedExpr)
    (pes : List PEId) (state : State) : ProofsLean.StepResult State :=
  match pes with
  | [] => .ok state
  | pe :: rest =>
      match executeIntegerProducerLineAtPE expressions state pe with
      | .failure => .failure
      | .unknown => .unknown
      | .ok next => executeIntegerProducerLineAtPEs expressions rest next

/-- Whole-machine line transition for parsed integer ALU, zero, immediate,
matrix-read, wait, and noforward expressions. Reads and prepared writes use the
existing per-PE transactional semantics; matrix data is read from the PE's
physical group/L2B/L1B MAB bank. The PE traversal is pure, so a failure or
unknown on any PE returns no partially updated state. -/
noncomputable def executeIntegerProducerInstructionLine
    (line : InstructionLine) (state : State) : ProofsLean.StepResult State :=
  if !checkParsedTopLine line.toParsed then .failure
  else
    match line with
    | .pe normalizedExpressions =>
        let expressions := normalizedExpressions.map NormalizedExpr.toParsed
        if expressions.all parsedExprIsSupportedPELineProducer then
          match executeIntegerProducerLineAtPEs expressions (List.finRange 4096) state with
          | .failure => .failure
          | .unknown => .unknown
          | .ok nextPEs =>
              match executeParsedMatrixWritesAtMABs state allMABCoordinates expressions nextPEs with
              | .failure => .failure
              | .unknown => .unknown
              | .ok next =>
                  .ok { next with hazardClock := next.hazardClock + InstructionLine.cost line }
        else .unknown
    | .nop _ _ | .mv _ => .unknown

noncomputable def integerProducerMachine : ProofsLean.PartialMachine where
  Line := InstructionLine
  State := State
  Input := Unit
  step := fun line state => executeIntegerProducerInstructionLine line state
  legal := fun _ => True
  lineCost := InstructionLine.cost
  positiveCost := InstructionLine.cost_positive

theorem integerProducerMachine_issue_failure (line : InstructionLine)
    (state : State) (rejected : checkParsedTopLine line.toParsed = false) :
    integerProducerMachine.step line state = .failure := by
  simp [integerProducerMachine, executeIntegerProducerInstructionLine, rejected]

theorem executeIntegerProducerInstructionLine_pe_success
    (normalizedExpressions : List NormalizedExpr) (state nextPEs next : State)
    (accepted : checkParsedTopLine
      (InstructionLine.pe normalizedExpressions).toParsed = true)
    (supported : (normalizedExpressions.map NormalizedExpr.toParsed).all
      parsedExprIsSupportedPELineProducer = true)
    (executed : executeIntegerProducerLineAtPEs
      (normalizedExpressions.map NormalizedExpr.toParsed) (List.finRange 4096) state =
        .ok nextPEs)
    (matrixWrites : executeParsedMatrixWritesAtMABs state allMABCoordinates
      (normalizedExpressions.map NormalizedExpr.toParsed) nextPEs = .ok next) :
    executeIntegerProducerInstructionLine (.pe normalizedExpressions) state =
      .ok { next with
        hazardClock := next.hazardClock + InstructionLine.cost (.pe normalizedExpressions) } := by
  simp [executeIntegerProducerInstructionLine, accepted, supported, executed, matrixWrites]

end ProofsLean.MNCore
