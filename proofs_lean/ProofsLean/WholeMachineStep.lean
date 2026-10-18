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
  | .matrixWrite .d | .matrixWrite .f | .matrixWrite .g | .matrixWrite .h => true
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

def parsedFloatMAUSourceAttrs? (operand : ParsedOperand)
    (context : ParsedIntegerContext) : Option (ParsedIntegerInput × Bool × Bool × Bool) :=
  match operand with
  | .mem access neg ext rnd none =>
      let rawOperand := ParsedOperand.mem access neg ext false none
      (ParsedOperand.toParsedIntegerInput? rawOperand .long context.group context.l2b
        context.l1b context.mab context.pe context.cycle context.bar0 context.bar1
        context.tWord).map (fun input => (input, neg, ext, rnd))
  | .forward kind neg ext rnd =>
      let rawOperand := ParsedOperand.forward kind neg ext false
      (ParsedOperand.toParsedIntegerInput? rawOperand .long context.group context.l2b
        context.l1b context.mab context.pe context.cycle context.bar0 context.bar1
        context.tWord).map (fun input => (input, neg, ext, rnd))
  | _ => none

structure ParsedFloatFmaAccesses where
  sourceA : ParsedIntegerInput
  sourceB : ParsedIntegerInput
  sourceC : ParsedIntegerInput
  negateA : Bool
  negateB : Bool
  negateC : Bool
  extendA : Bool
  extendB : Bool
  extendC : Bool
  roundA : Bool
  roundB : Bool
  roundC : Bool
  destination : Fin (Bank.capacity .lm1)

def lowerParsedFloatFma? (expression : ParsedExpr) (context : ParsedIntegerContext) :
    Option ParsedFloatFmaAccesses := do
  match expression.op with
  | .mau .f false .fma none false => pure ()
  | _ => none
  match expression.sources, expression.destinations with
  | [sourceA, sourceB, sourceC], [.mem access false false false none] =>
      let (sourceA, negateA, extendA, roundA) ← parsedFloatMAUSourceAttrs? sourceA context
      let (sourceB, negateB, extendB, roundB) ← parsedFloatMAUSourceAttrs? sourceB context
      let (sourceC, negateC, extendC, roundC) ← parsedFloatMAUSourceAttrs? sourceC context
      let destinationAccess ← ParsedOperand.toDirectMemoryAccess?
        (.mem access false false false none) context.pe context.cycle
        context.bar0 context.bar1 context.tWord
      let destination ← FloatPEMemory.lm1LongAddress? destinationAccess
      some ⟨sourceA, sourceB, sourceC, negateA, negateB, negateC,
        extendA, extendB, extendC, roundA, roundB, roundC, destination⟩
  | _, _ => none

structure ParsedFloatMultiplyAccesses where
  sourceA : ParsedIntegerInput
  sourceB : ParsedIntegerInput
  negateA : Bool
  negateB : Bool
  extendA : Bool
  extendB : Bool
  roundA : Bool
  roundB : Bool
  destination : Fin (Bank.capacity .lm1)

def negateSingleBus (bus : BitVec 64) : BitVec 64 :=
  bus ^^^ (BitVec.ofNat 64 (2 ^ 63 + 2 ^ 31))

def extendHalfPairToSingleBus (bus : BitVec 64) : BitVec 64 :=
  BitVec.ofNat 32 (RRN.extendFloatBits .half .single
    (bus.extractLsb' 48 16).toNat) ++
  BitVec.ofNat 32 (RRN.extendFloatBits .half .single
    (bus.extractLsb' 32 16).toNat)

theorem extendHalfPairToSingleBus_lane_order :
    extendHalfPairToSingleBus
      (BitVec.ofNat 16 0x3e00 ++ BitVec.ofNat 16 0xc000 ++
        BitVec.ofNat 16 0 ++ BitVec.ofNat 16 0) =
      (BitVec.ofNat 32 0x3f800000 ++ BitVec.ofNat 32 0xc0000000) := by
  decide

def roundDoublePairToSingleBus (bus : IntegerALU.Bus) : BitVec 64 :=
  BitVec.ofNat 32 (RRN.extendFloatBits .double .single bus.high.toNat) ++
    BitVec.ofNat 32 (RRN.extendFloatBits .double .single bus.low.toNat)

theorem roundDoublePairToSingleBus_lane_order :
    roundDoublePairToSingleBus
      ⟨0x3ff8000000000000, 0xbff0000000000000⟩ =
      (BitVec.ofNat 32 0x3fc00000 ++ BitVec.ofNat 32 0xbf800000) := by
  decide

def prepareSingleMAUSource (bus : IntegerALU.Bus)
    (negate extend round : Bool) : BitVec 64 :=
  let converted := if extend then extendHalfPairToSingleBus bus.high
    else if round then roundDoublePairToSingleBus bus else bus.high
  if negate then negateSingleBus converted else converted

def lowerParsedFloatMultiply? (expression : ParsedExpr) (context : ParsedIntegerContext) :
    Option ParsedFloatMultiplyAccesses := do
  match expression.op with
  | .mau .f false .mul none false => pure ()
  | _ => none
  match expression.sources, expression.destinations with
  | [sourceA, sourceB], [.mem access false false false none] =>
      let (sourceA, negateA, extendA, roundA) ← parsedFloatMAUSourceAttrs? sourceA context
      let (sourceB, negateB, extendB, roundB) ← parsedFloatMAUSourceAttrs? sourceB context
      let destinationAccess ← ParsedOperand.toDirectMemoryAccess?
        (.mem access false false false none) context.pe context.cycle
        context.bar0 context.bar1 context.tWord
      let destination ← FloatPEMemory.lm1LongAddress? destinationAccess
      some ⟨sourceA, sourceB, negateA, negateB, extendA, extendB, roundA, roundB,
        destination⟩
  | _, _ => none

structure ParsedFloatAddAccesses where
  sourceA : ParsedIntegerInput
  sourceB : ParsedIntegerInput
  negateA : Bool
  negateB : Bool
  extendA : Bool
  extendB : Bool
  roundA : Bool
  roundB : Bool
  destination : Fin (Bank.capacity .lm1)

def lowerParsedFloatAddMachine? (expression : ParsedExpr) (context : ParsedIntegerContext) :
    Option ParsedFloatAddAccesses := do
  match expression.op with
  | .mau .f false .add none false => pure ()
  | _ => none
  match expression.sources, expression.destinations with
  | [sourceA, sourceB], [.mem access false false false none] =>
      let (sourceA, negateA, extendA, roundA) ← parsedFloatMAUSourceAttrs? sourceA context
      let (sourceB, negateB, extendB, roundB) ← parsedFloatMAUSourceAttrs? sourceB context
      let destinationAccess ← ParsedOperand.toDirectMemoryAccess?
        (.mem access false false false none) context.pe context.cycle
        context.bar0 context.bar1 context.tWord
      let destination ← FloatPEMemory.lm1LongAddress? destinationAccess
      some ⟨sourceA, sourceB, negateA, negateB, extendA, extendB, roundA, roundB,
        destination⟩
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
    (negateA negateB extendA extendB roundA roundB : Bool)
    (destinationAddress : Fin (Bank.capacity .lm1))
    (sourceALowered : parsedFloatMAUSourceAttrs? sourceA context =
      some (inputA, negateA, extendA, roundA))
    (sourceBLowered : parsedFloatMAUSourceAttrs? sourceB context =
      some (inputB, negateB, extendB, roundB))
    (destinationLowered : ParsedOperand.toDirectMemoryAccess?
      (.mem destinationAccess false false false none) context.pe context.cycle
      context.bar0 context.bar1 context.tWord =
        some ⟨.lm1, .long, destinationAddress⟩) :
    lowerParsedFloatMultiply?
      ⟨.mau .f false .mul none false,
        [sourceA, sourceB], [.mem destinationAccess false false false none], none, "fvmul"⟩
      context = some ⟨inputA, inputB, negateA, negateB, extendA, extendB, roundA, roundB,
        destinationAddress⟩ := by
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
            let left := prepareSingleMAUSource sourceA accesses.negateA accesses.extendA accesses.roundA
            let right := prepareSingleMAUSource sourceB accesses.negateB accesses.extendB accesses.roundB
            let accumulator := prepareSingleMAUSource sourceC accesses.negateC accesses.extendC accesses.roundC
            let output := singleFmaBus left right accumulator
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
          let left := prepareSingleMAUSource sourceA accesses.negateA accesses.extendA accesses.roundA
          let right := prepareSingleMAUSource sourceB accesses.negateB accesses.extendB accesses.roundB
          let output := FloatMultiply.multiplyBus left right
          let nextLM1 := FloatPEMemory.writePair currentFiles.lm1 accesses.destination output
          .ok ({ currentFiles with lm1 := nextLM1 }, ⟨output, 0⟩)
  | .mau .f false .add none false =>
    let cycleContext := { context with cycle := cycle }
    match lowerParsedFloatAddMachine? expression cycleContext with
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
          let left := prepareSingleMAUSource sourceA accesses.negateA accesses.extendA accesses.roundA
          let right := prepareSingleMAUSource sourceB accesses.negateB accesses.extendB accesses.roundB
          let output := FloatAdd.addBus left right
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
    let output := FloatMultiply.multiplyBus
      (prepareSingleMAUSource busA accesses.negateA accesses.extendA accesses.roundA)
      (prepareSingleMAUSource busB accesses.negateB accesses.extendB accesses.roundB)
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
    let output := singleFmaBus
      (prepareSingleMAUSource busA accesses.negateA accesses.extendA accesses.roundA)
      (prepareSingleMAUSource busB accesses.negateB accesses.extendB accesses.roundB)
      (prepareSingleMAUSource busC accesses.negateC accesses.extendC accesses.roundC)
    executeParsedFloatMAUCycleAtPE readFiles currentFiles oldSlots expression context cycle =
      .ok ({ currentFiles with lm1 :=
        (FloatPEMemory.writePair currentFiles.lm1 accesses.destination output) },
        ⟨output, 0⟩) := by
  simp [executeParsedFloatMAUCycleAtPE, isFma, lowered, readA, readB, readC]

theorem executeParsedFloatMAUCycleAtPE_add_success
    (readFiles currentFiles : IntegerRegisterFiles) (oldSlots : Forwarding.Slots)
    (expression : ParsedExpr) (context : ParsedIntegerContext) (cycle : Fin 4)
    (accesses : ParsedFloatAddAccesses) (busA busB : IntegerALU.Bus)
    (isAdd : expression.op = .mau .f false .add none false)
    (lowered : lowerParsedFloatAddMachine? expression { context with cycle := cycle } =
      some accesses)
    (readA : ParsedIntegerInput.readWithForwarding readFiles oldSlots cycle accesses.sourceA =
      .ok busA)
    (readB : ParsedIntegerInput.readWithForwarding readFiles oldSlots cycle accesses.sourceB =
      .ok busB) :
    let output := FloatAdd.addBus
      (prepareSingleMAUSource busA accesses.negateA accesses.extendA accesses.roundA)
      (prepareSingleMAUSource busB accesses.negateB accesses.extendB accesses.roundB)
    executeParsedFloatMAUCycleAtPE readFiles currentFiles oldSlots expression context cycle =
      .ok ({ currentFiles with lm1 :=
        (FloatPEMemory.writePair currentFiles.lm1 accesses.destination output) },
        ⟨output, 0⟩) := by
  simp [executeParsedFloatMAUCycleAtPE, isAdd, lowered, readA, readB]

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

structure ParsedMatrixWriteAccesses where
  source : ParsedIntegerInput
  sideY : Bool
  row : Nat
  twoRows : Bool
  negate : Bool
  extend : Bool
  round : Bool

def lowerParsedMatrixWrite? (expression : ParsedExpr) (context : ParsedIntegerContext) :
    Option ParsedMatrixWriteAccesses := do
  match expression.op, expression.sources, expression.destinations with
  | .matrixWrite _, [source], [.matrix sideY width (some row)] =>
      let (rawSource, negate, extend, round) ← match source with
        | .mem access negate extend round _ =>
            some (.mem access false false false none, negate, extend, round)
        | .forward kind negate extend round =>
            some (.forward kind false false false, negate, extend, round)
        | _ => none
      let source ← ParsedOperand.toParsedIntegerInput? rawSource .long
        context.group context.l2b context.l1b context.mab context.pe context.cycle
        context.bar0 context.bar1 context.tWord
      some ⟨source, sideY, row.val, width.val == 4, negate, extend, round⟩
  | _, _, _ => none

def prepareMatrixWriteBus (precision : ParsedPrecision) (bus : IntegerALU.Bus)
    (negate extend round twoRows : Bool) : ProofsLean.StepResult IntegerALU.Bus :=
  let converted := match precision with
    | .d =>
        if extend then
          IntegerALU.Bus.mk
            (BitVec.ofNat 64 (RRN.extendFloatBits .single .double
              (bus.high.extractLsb' 32 32).toNat)) 0
        else bus
    | .f | .g =>
        if extend then ⟨extendHalfPairToSingleBus bus.high, 0⟩
        else if round then ⟨roundDoublePairToSingleBus bus, 0⟩
        else bus
    | .h =>
        if round then
          ⟨roundSingleWordToHalf (bus.high.extractLsb' 32 32) ++
            roundSingleWordToHalf (bus.high.extractLsb' 0 32) ++
            roundSingleWordToHalf (bus.low.extractLsb' 32 32) ++
            roundSingleWordToHalf (bus.low.extractLsb' 0 32), 0⟩
        else bus
    | _ => bus
  if precision == .h && extend then .failure
  else if precision == .h && round && twoRows then .failure
  else if precision == .d && round && !extend then .failure
  else if negate then
    match precision with
    | .d => .ok { converted with high := converted.high ^^^ (BitVec.ofNat 64 (2 ^ 63)) }
    | .f | .g => .ok { converted with high := negateSingleBus converted.high }
    | _ => .ok converted
  else .ok converted

def halfMatrixWriteValues (buses : Fin 4 → IntegerALU.Bus) (negate : Bool)
    (laneOffset : Nat) : Fin 16 → BitVec 16 := fun index =>
  let pe : Fin 4 := ⟨index.val / 4, by have h := index.isLt; omega⟩
  let lane := index.val % 4 + laneOffset
  let words := (buses pe).high ++ (buses pe).low
  let value := words.extractLsb' (112 - 16 * lane) 16
  if negate then value ^^^ (BitVec.ofNat 16 0x8000) else value

def writeHalfMatrixPhysicalRow (old : DoubleMatrixPhysicalFace)
    (row : Fin 16) (values : Fin 16 → BitVec 16) : DoubleMatrixPhysicalFace :=
  fun targetRow =>
    if targetRow = row then
      fun word => values ⟨2 * word.val, by have h := word.isLt; omega⟩ ++
        values ⟨2 * word.val + 1, by have h := word.isLt; omega⟩
    else old targetRow

def writeParsedHalfMatrixStoreRow (old : ParsedMatrixReadStore)
    (mab : Fin 16) (sideY : Bool) (row : Fin 16)
    (values : Fin 16 → BitVec 16) : ParsedMatrixReadStore :=
  fun nextMab nextSide =>
    if nextMab = mab ∧ nextSide = sideY then
      writeHalfMatrixPhysicalRow (old nextMab nextSide) row values
    else old nextMab nextSide

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
        match lowerParsedMatrixWrite? expression context with
        | none => .unknown
        | some accesses =>
            match ParsedIntegerInput.readWithForwarding
                (state.peRegisters (physicalPEId coordinate pe))
                (state.forwarding (physicalPEId coordinate pe)) cycle accesses.source with
            | .failure => .failure
            | .unknown => .unknown
            | .ok bus =>
              match prepareMatrixWriteBus
                  (match expression.op with | .matrixWrite precision => precision | _ => .f)
                  bus accesses.negate accesses.extend accesses.round accesses.twoRows with
              | .failure => .failure
              | .unknown => .unknown
              | .ok converted =>
                readPEs rest (fun index => if index = pe then converted else buses index)
  readPEs parsedMatrixWritePEs (fun _ => ⟨0, 0⟩)

def executeParsedMatrixWriteCycle (state : State) (coordinate : MABCoordinate)
    (expression : ParsedExpr) (store : ParsedMatrixReadStore) (cycle : Fin 4) :
    ProofsLean.StepResult ParsedMatrixReadStore :=
  let groupContext := matrixWriteGroupContext state coordinate
  match expression.op with
  | .matrixWrite .d =>
      match lowerParsedMatrixWrite? expression (groupContext.at 0 cycle) with
      | none => .unknown
      | some accesses =>
          match readParsedMatrixWriteBuses state coordinate expression cycle with
          | .failure => .failure
          | .unknown => .unknown
          | .ok buses =>
              .ok (writeParsedDoubleMatrixStoreRow store coordinate.mab accesses.sideY
                (doubleMatrixWriteRowAt accesses.row cycle) (fun pe => (buses pe).high))
  | .matrixWrite .f | .matrixWrite .g =>
      match lowerParsedMatrixWrite? expression (groupContext.at 0 cycle) with
      | none => .unknown
      | some accesses =>
          match readParsedMatrixWriteBuses state coordinate expression cycle with
          | .failure => .failure
          | .unknown => .unknown
          | .ok buses =>
              .ok (writeParsedSingleMatrixStoreRow store coordinate.mab accesses.sideY
                (singleMatrixWriteRowAt accesses.row cycle) (singleMatrixWriteValues buses))
  | .matrixWrite .h =>
      match lowerParsedMatrixWrite? expression (groupContext.at 0 cycle) with
      | none => .unknown
      | some accesses =>
          match readParsedMatrixWriteBuses state coordinate expression cycle with
          | .failure => .failure
          | .unknown => .unknown
          | .ok buses =>
              let rowNat := (accesses.row + (if accesses.twoRows then 2 else 1) * cycle.val) % 16
              let row0 : Fin 16 := ⟨rowNat, Nat.mod_lt _ (by decide)⟩
              let values0 := halfMatrixWriteValues buses accesses.negate 0
              if accesses.twoRows then
                if hlt : rowNat < 15 then
                  let row1 : Fin 16 := ⟨rowNat + 1, by omega⟩
                  let store0 := writeParsedHalfMatrixStoreRow store coordinate.mab
                    accesses.sideY row0 values0
                  let values1 := halfMatrixWriteValues buses accesses.negate 4
                  .ok (writeParsedHalfMatrixStoreRow store0 coordinate.mab
                    accesses.sideY row1 values1)
                else .failure
              else .ok (writeParsedHalfMatrixStoreRow store coordinate.mab
                accesses.sideY row0 values0)
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

def executeParsedMvMemory (state : State) (transfer : ParsedMv) :
    ProofsLean.StepResult State :=
  let nextMemory? := match transfer.kind with
    | .nop => some state.blockMemory
    | .copy => MVSemantics.executeParsedMvPCopy? state.blockMemory transfer
    | .broadcast => MVSemantics.executeParsedMvB? state.blockMemory transfer
    | .broadcast2 => MVSemantics.executeParsedMvB2? state.blockMemory transfer
    | .broadcast4 => MVSemantics.executeParsedMvB4? state.blockMemory transfer
    | .distribute => MVSemantics.executeParsedMvD? state.blockMemory transfer
    | .reduce rrn => MVSemantics.executeParsedMvR? state.blockMemory transfer
    | .reduce2 rrn => MVSemantics.executeParsedMvR2? state.blockMemory transfer
    | .reduce4 rrn => MVSemantics.executeParsedMvR4? state.blockMemory transfer
  match nextMemory? with
  | none => .failure
  | some blockMemory => .ok { state with blockMemory }

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
    | .nop count none =>
        .ok { state with hazardClock := state.hazardClock + count.val }
    | .nop _ (some _) => .unknown
    | .mv transfer =>
        if transfer.kind == .nop then
          .ok { state with hazardClock := state.hazardClock + 1 }
        else
          match executeParsedMvMemory state transfer.toParsed with
          | .failure => .failure
          | .unknown => .unknown
          | .ok next =>
              .ok { next with hazardClock := next.hazardClock + 1 }

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

theorem executeIntegerProducerInstructionLine_nop_without_wait
    (count : {n : Nat // 0 < n}) (state : State)
    (accepted : checkParsedTopLine (.nop count.val none) = true) :
    executeIntegerProducerInstructionLine (.nop count none) state =
      .ok { state with hazardClock := state.hazardClock + count.val } := by
  simp [executeIntegerProducerInstructionLine, InstructionLine.toParsed,
    accepted, InstructionLine.cost]

theorem executeIntegerProducerInstructionLine_mvnop
    (transfer : NormalizedMv) (state : State)
    (isNop : transfer.kind = .nop)
    (accepted : checkParsedTopLine (.mv transfer.toParsed) = true) :
    executeIntegerProducerInstructionLine (.mv transfer) state =
      .ok { state with hazardClock := state.hazardClock + 1 } := by
  simp [executeIntegerProducerInstructionLine, InstructionLine.toParsed,
    InstructionLine.cost, isNop, accepted]

theorem executeIntegerProducerInstructionLine_mv_transfer_success
    (transfer : NormalizedMv) (state next : State)
    (accepted : checkParsedTopLine (.mv transfer.toParsed) = true)
    (notNop : transfer.kind ≠ .nop)
    (executed : executeParsedMvMemory state transfer.toParsed = .ok next) :
    executeIntegerProducerInstructionLine (.mv transfer) state =
      .ok { next with hazardClock := next.hazardClock + 1 } := by
  simp [executeIntegerProducerInstructionLine, InstructionLine.toParsed,
    accepted, notNop, executed]

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
