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

def parsedFloatMAUSource? (operand : ParsedOperand) (context : ParsedIntegerContext) :
    Option ParsedIntegerInput :=
  match operand with
  | .mem _ false false false none | .forward _ false false false =>
      ParsedOperand.toParsedIntegerInput? operand .long context.group context.l2b
        context.l1b context.mab context.pe context.cycle context.bar0 context.bar1 context.tWord
  | _ => none

theorem parsedFloatMAUSource?_memory
    (access : Access) (context : ParsedIntegerContext)
    (resolved : DirectMemoryAccess)
    (lowered : ParsedOperand.toDirectMemoryAccess?
      (.mem access false false false none) context.pe context.cycle
      context.bar0 context.bar1 context.tWord = some resolved) :
    parsedFloatMAUSource? (.mem access false false false none) context =
      some (.memory resolved false) := by
  simp [parsedFloatMAUSource?, ParsedOperand.toParsedIntegerInput?, lowered]

structure ParsedFloatFmaAccesses where
  sourceA : ParsedIntegerInput
  sourceB : ParsedIntegerInput
  sourceC : ParsedIntegerInput
  destination : Fin (Bank.capacity .lm1)

def lowerParsedFloatFma? (expression : ParsedExpr) (context : ParsedIntegerContext) :
    Option ParsedFloatFmaAccesses := do
  match expression.op with
  | .mau .f false .fma none false => pure ()
  | _ => none
  match expression.sources, expression.destinations with
  | [sourceA, sourceB, sourceC], [.mem access false false false none] =>
      let sourceA ← parsedFloatMAUSource? sourceA context
      let sourceB ← parsedFloatMAUSource? sourceB context
      let sourceC ← parsedFloatMAUSource? sourceC context
      let destinationAccess ← ParsedOperand.toDirectMemoryAccess?
        (.mem access false false false none) context.pe context.cycle
        context.bar0 context.bar1 context.tWord
      let destination ← FloatPEMemory.lm1LongAddress? destinationAccess
      some ⟨sourceA, sourceB, sourceC, destination⟩
  | _, _ => none

structure ParsedFloatMultiplyAccesses where
  sourceA : ParsedIntegerInput
  sourceB : ParsedIntegerInput
  destination : Fin (Bank.capacity .lm1)

def lowerParsedFloatMultiply? (expression : ParsedExpr) (context : ParsedIntegerContext) :
    Option ParsedFloatMultiplyAccesses := do
  match expression.op with
  | .mau .f false .mul none false => pure ()
  | _ => none
  match expression.sources, expression.destinations with
  | [sourceA, sourceB], [.mem access false false false none] =>
      let sourceA ← parsedFloatMAUSource? sourceA context
      let sourceB ← parsedFloatMAUSource? sourceB context
      let destinationAccess ← ParsedOperand.toDirectMemoryAccess?
        (.mem access false false false none) context.pe context.cycle
        context.bar0 context.bar1 context.tWord
      let destination ← FloatPEMemory.lm1LongAddress? destinationAccess
      some ⟨sourceA, sourceB, destination⟩
  | _, _ => none

def singleFmaBus (left right accumulator : BitVec 64) : BitVec 64 :=
  SingleFMA.singleFma (left.extractLsb' 32 32) (right.extractLsb' 32 32)
      (accumulator.extractLsb' 32 32) ++
    SingleFMA.singleFma (left.extractLsb' 0 32) (right.extractLsb' 0 32)
      (accumulator.extractLsb' 0 32)

theorem parsedFloatMAUSource?_forward
    (kind : ParsedForward) (context : ParsedIntegerContext) :
    parsedFloatMAUSource? (.forward kind false false false) context =
      some (.forward kind false) := by
  simp [parsedFloatMAUSource?, ParsedOperand.toParsedIntegerInput?]

theorem lowerParsedFloatMultiply?_fvmul
    (sourceA sourceB : ParsedOperand) (destinationAccess : Access)
    (context : ParsedIntegerContext) (inputA inputB : ParsedIntegerInput)
    (destinationAddress : Fin (Bank.capacity .lm1))
    (sourceALowered : parsedFloatMAUSource? sourceA context = some inputA)
    (sourceBLowered : parsedFloatMAUSource? sourceB context = some inputB)
    (destinationLowered : ParsedOperand.toDirectMemoryAccess?
      (.mem destinationAccess false false false none) context.pe context.cycle
      context.bar0 context.bar1 context.tWord =
        some ⟨.lm1, .long, destinationAddress⟩) :
    lowerParsedFloatMultiply?
      ⟨.mau .f false .mul none false,
        [sourceA, sourceB], [.mem destinationAccess false false false none], none, "fvmul"⟩
      context = some ⟨inputA, inputB, destinationAddress⟩ := by
  simp [lowerParsedFloatMultiply?, sourceALowered, sourceBLowered, destinationLowered,
    FloatPEMemory.lm1LongAddress?]

def executeParsedFloatMAUCycleAtPE (readFiles currentFiles : IntegerRegisterFiles)
    (oldSlots : Forwarding.Slots) (expression : ParsedExpr)
    (context : ParsedIntegerContext) (cycle : Fin 4) :
    ProofsLean.StepResult (IntegerRegisterFiles × IntegerALU.Bus) :=
  match expression.op with
  | .mau .f false .fma none false =>
    let cycleContext := { context with cycle := cycle }
    match lowerParsedFloatFma? expression cycleContext with
    | none => .unknown
    | some accesses =>
      match ParsedIntegerInput.readWithForwarding readFiles oldSlots cycle accesses.sourceA with
      | .failure => .failure
      | .unknown => .unknown
      | .ok sourceA =>
        match ParsedIntegerInput.readWithForwarding readFiles oldSlots cycle accesses.sourceB with
        | .failure => .failure
        | .unknown => .unknown
        | .ok sourceB =>
          match ParsedIntegerInput.readWithForwarding readFiles oldSlots cycle accesses.sourceC with
          | .failure => .failure
          | .unknown => .unknown
          | .ok sourceC =>
            let output := singleFmaBus sourceA.high sourceB.high sourceC.high
            let nextLM1 := FloatPEMemory.writePair currentFiles.lm1 accesses.destination output
            .ok ({ currentFiles with lm1 := nextLM1 }, ⟨output, 0⟩)
  | .mau .f false .mul none false =>
    let cycleContext := { context with cycle := cycle }
    match lowerParsedFloatMultiply? expression cycleContext with
    | none => .unknown
    | some accesses =>
      match ParsedIntegerInput.readWithForwarding readFiles oldSlots cycle accesses.sourceA with
      | .failure => .failure
      | .unknown => .unknown
      | .ok sourceA =>
        match ParsedIntegerInput.readWithForwarding readFiles oldSlots cycle accesses.sourceB with
        | .failure => .failure
        | .unknown => .unknown
        | .ok sourceB =>
          let output := FloatMultiply.multiplyBus sourceA.high sourceB.high
          let nextLM1 := FloatPEMemory.writePair currentFiles.lm1 accesses.destination output
          .ok ({ currentFiles with lm1 := nextLM1 }, ⟨output, 0⟩)
  | _ => match FloatPEMemory.lowerParsedFloatAdd? expression context.pe cycle context.bar0
      context.bar1 context.tWord with
  | none =>
    match FloatPEMemory.lowerParsedFloatSubtract? expression context.pe cycle context.bar0
        context.bar1 context.tWord with
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
    (readFiles currentFiles : IntegerRegisterFiles) (oldSlots : Forwarding.Slots)
    (expression : ParsedExpr) (context : ParsedIntegerContext) (cycle : Fin 4)
    (accesses : ParsedFloatMultiplyAccesses) (busA busB : IntegerALU.Bus)
    (isMul : expression.op = .mau .f false .mul none false)
    (lowered : lowerParsedFloatMultiply? expression { context with cycle := cycle } =
      some accesses)
    (readA : ParsedIntegerInput.readWithForwarding readFiles oldSlots cycle accesses.sourceA =
      .ok busA)
    (readB : ParsedIntegerInput.readWithForwarding readFiles oldSlots cycle accesses.sourceB =
      .ok busB) :
    let output := FloatMultiply.multiplyBus busA.high busB.high
    executeParsedFloatMAUCycleAtPE readFiles currentFiles oldSlots expression context cycle =
      .ok ({ currentFiles with lm1 :=
        (FloatPEMemory.writePair currentFiles.lm1 accesses.destination output) },
        ⟨output, 0⟩) := by
  simp [executeParsedFloatMAUCycleAtPE, isMul, lowered, readA, readB]

theorem executeParsedFloatMAUCycleAtPE_fma_success
    (readFiles currentFiles : IntegerRegisterFiles) (oldSlots : Forwarding.Slots)
    (expression : ParsedExpr) (context : ParsedIntegerContext) (cycle : Fin 4)
    (accesses : ParsedFloatFmaAccesses) (busA busB busC : IntegerALU.Bus)
    (isFma : expression.op = .mau .f false .fma none false)
    (lowered : lowerParsedFloatFma? expression { context with cycle := cycle } = some accesses)
    (readA : ParsedIntegerInput.readWithForwarding readFiles oldSlots cycle accesses.sourceA =
      .ok busA)
    (readB : ParsedIntegerInput.readWithForwarding readFiles oldSlots cycle accesses.sourceB =
      .ok busB)
    (readC : ParsedIntegerInput.readWithForwarding readFiles oldSlots cycle accesses.sourceC =
      .ok busC) :
    let output := singleFmaBus busA.high busB.high busC.high
    executeParsedFloatMAUCycleAtPE readFiles currentFiles oldSlots expression context cycle =
      .ok ({ currentFiles with lm1 :=
        (FloatPEMemory.writePair currentFiles.lm1 accesses.destination output) },
        ⟨output, 0⟩) := by
  simp [executeParsedFloatMAUCycleAtPE, isFma, lowered, readA, readB, readC]

theorem executeParsedFloatMAUCycleAtPE_add_success
    (readFiles currentFiles : IntegerRegisterFiles) (oldSlots : Forwarding.Slots)
    (expression : ParsedExpr) (context : ParsedIntegerContext) (cycle : Fin 4)
    (leftAddress rightAddress : Fin (Bank.capacity .lm0))
    (destinationAddress : Fin (Bank.capacity .lm1))
    (isAdd : expression.op = .mau .f false .add none false)
    (lowered : FloatPEMemory.lowerParsedFloatAdd? expression context.pe cycle
      context.bar0 context.bar1 context.tWord =
      some (leftAddress, rightAddress, destinationAddress)) :
    let output := FloatAdd.addBus
      (FloatPEMemory.readPair .lm0 readFiles.lm0 leftAddress)
      (FloatPEMemory.readPair .lm0 readFiles.lm0 rightAddress)
    executeParsedFloatMAUCycleAtPE readFiles currentFiles oldSlots expression context cycle =
      .ok ({ currentFiles with lm1 :=
        (FloatPEMemory.writePair currentFiles.lm1 destinationAddress output) },
        ⟨output, 0⟩) := by
  simp [executeParsedFloatMAUCycleAtPE, isAdd, lowered]

def executeParsedFloatMAUCyclesAtPE (readFiles : IntegerRegisterFiles)
    (oldSlots : Forwarding.Slots) (expression : ParsedExpr)
    (context : ParsedIntegerContext) : List (Fin 4) → IntegerRegisterFiles →
      (Fin 4 → IntegerALU.Bus) → ProofsLean.StepResult
        (IntegerRegisterFiles × (Fin 4 → IntegerALU.Bus))
  | [], files, outputs => .ok (files, outputs)
  | cycle :: rest, files, outputs =>
      match executeParsedFloatMAUCycleAtPE readFiles files oldSlots expression context cycle with
      | .failure => .failure
      | .unknown => .unknown
      | .ok (nextFiles, output) =>
          executeParsedFloatMAUCyclesAtPE readFiles oldSlots expression context rest
            nextFiles (fun index => if index = cycle then output else outputs index)

def executeParsedFloatMAUsAtPE (readState currentFiles : IntegerRegisterFiles)
    (oldSlots : Forwarding.Slots) (context : ParsedIntegerContext)
    (expressions : List ParsedExpr) : ProofsLean.StepResult
      (IntegerRegisterFiles × (Fin 4 → IntegerALU.Bus) × Bool) :=
  let floatAdds := expressions.filter parsedExprIsSupportedFloatMAUProducer
  let rec run (remaining : List ParsedExpr) (files : IntegerRegisterFiles)
      (outputs : Fin 4 → IntegerALU.Bus) :
      ProofsLean.StepResult (IntegerRegisterFiles × (Fin 4 → IntegerALU.Bus)) :=
    match remaining with
    | [] => .ok (files, outputs)
    | expression :: rest =>
        match executeParsedFloatMAUCyclesAtPE readState oldSlots expression context
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
    match executeParsedFloatMAUsAtPE (state.peRegisters pe) registers oldSlots
        context expressions with
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
