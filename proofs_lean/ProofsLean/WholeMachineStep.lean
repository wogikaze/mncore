import ProofsLean.MachineState
import ProofsLean.PEMachine
import ProofsLean.FloatPEMemory
import ProofsLean.Footprint
import ProofsLean.HazardTrace

/-! A whole-state transition for connected PE integer ALU, single-precision
vector `fvadd`/`fvmul`/`fvfma`, half-precision `hvadd`/`hvmul`/`hvfma`,
double-precision `dvadd`/`dvmul`/`dvfma`,
floating ALU `relu`/`relu0`/`relu1`/`relu2`/`relu3`,
block-float ALU `bfn`/`bfe`,
matrix-read, D/F/G/H matrix-write, L1BM `mwrite`/`m4write`/`gather`,
and L1BM-to-PE `pbcast`/`mbcast`/`m4bcast`/`distrib` fragments. It runs the
same issue-line transaction independently at every physical PE, then updates
ALU/MAU/MREADF/LBF forwarding state. Other producer units remain unresolved. -/
namespace ProofsLean.MNCore

open Issue
open PEMemory

def parsedExprIsIntegerProducer (expression : ParsedExpr) : Bool :=
  match expression.op with
  | .alu .. | .zero | .immediate .. => true
  | _ => false

/-- Forwarding payloads are meaningful only while their per-unit validity bit
is set. Present invalid slots as poison to every source reader so existing
read semantics consistently turn a disabled forwarding read into failure. -/
def stateForwardingSlots (state : State) (pe : PEId) : Forwarding.Slots :=
  fun unit cycle =>
    if state.forwardingValid pe unit cycle then state.forwarding pe unit cycle
    else .poison

theorem stateForwardingSlots_invalid_is_poison (state : State) (pe : PEId)
    (unit : Forwarding.Unit) (cycle : Fin 4)
    (invalid : state.forwardingValid pe unit cycle = false) :
    stateForwardingSlots state pe unit cycle = .poison := by
  simp [stateForwardingSlots, invalid]

theorem stateForwardingSlots_valid_preserves_payload (state : State) (pe : PEId)
    (unit : Forwarding.Unit) (cycle : Fin 4)
    (valid : state.forwardingValid pe unit cycle = true) :
    stateForwardingSlots state pe unit cycle = state.forwarding pe unit cycle := by
  simp [stateForwardingSlots, valid]

/-- At simulator startup every forwarding read fails exactly as Rust's
uninitialized-register error path: the initial validity bit yields poison,
which the shared parsed-input reader turns into a known execution failure. -/
theorem rustSimulatorInitialState_forwarding_read_fails
    (pe : PEId) (cycle : Fin 4) (kind : ParsedForward) :
    ParsedIntegerInput.readWithForwarding
      (rustSimulatorInitialState.peRegisters pe)
      (stateForwardingSlots rustSimulatorInitialState pe) cycle
      (.forward kind false) = .failure := by
  apply parsedIntegerInput_forward_poison_fails
  exact stateForwardingSlots_invalid_is_poison rustSimulatorInitialState pe
    (ParsedIntegerInput.forwardUnit kind) cycle rfl

/-- These legacy ALU names parse successfully in Rust, but `alu_lanes` has no
implementation for them and returns `ExecError::Unsupported`. -/
def parsedExprIsUnsupportedRustAlu (expression : ParsedExpr) : Bool :=
  match expression.op with
  | .alu .lrelud _ _ _ | .alu .lreluo _ _ _ | .alu .ilrelud _ _ _ => true
  | _ => false

def parsedExprIsSupportedPELineProducer (expression : ParsedExpr) : Bool :=
  match expression.op with
  | .alu .. | .zero | .immediate .. | .matrixRead .. | .wait .. | .noforward => true
  | .mau .f false .add _ false | .mau .f false .mul _ false
  | .mau .f false .fma _ false | .mau .f false .passa _ false => true
  | .mau .f false _ _ true => true
  | .mau .d false .passa _ _ | .mau .h false .passa _ _
  | .mau .h false .mul _ _ | .mau .h false .add _ _
  | .mau .h false .fma _ _ => true
  | .mau .d false .add _ _ | .mau .d false .mul _ _
  | .mau .d false .fma _ _ => true
  | .mau .d true .add _ _ | .mau .d true .mul _ _
  | .mau .d true .fma _ _ | .mau .d true .passa _ _ => true
  | .mau .f true .add _ _ | .mau .f true .mul _ _
  | .mau .f true .fma _ _ | .mau .f true .passa _ _ => true
  | .mau .g true .add _ _ | .mau .g true .mul _ _
  | .mau .g true .fma _ _ | .mau .g true .passa _ _ => true
  | .mau .h true .add _ _ | .mau .h true .mul _ _
  | .mau .h true .fma _ _ | .mau .h true .passa _ _ => true
  | .mau .g false _ _ _ | .mau .l false _ _ _ | .mau .i false _ _ _
  | .mau .s false _ _ _ => true
  | .matrixWrite .d | .matrixWrite .f | .matrixWrite .g | .matrixWrite .h
  | .matrixWrite .l | .matrixWrite .i | .matrixWrite .s => true
  | .l1bm (.mwrite _) | .l1bm (.m4write _) => true
  | .l1bm .pbcast | .l1bm .mbcast | .l1bm .m4bcast | .l1bm (.distrib _) => true
  | .l1bm (.gather _) | .l1bm (.reduce ..) | .l1bm (.reduce4 ..) => true
  | .l2bm _ => true
  | _ => false

def parsedExprIsMatrixReadProducer (expression : ParsedExpr) : Bool :=
  match expression.op with
  | .matrixRead .. => true
  | _ => false

def parsedExprIsMatrixWriteProducer (expression : ParsedExpr) : Bool :=
  match expression.op with
  | .matrixWrite .. => true
  | _ => false

def parsedExprIsMatrixMAUProducer (expression : ParsedExpr) : Bool :=
  match expression.op with
  | .mau .d true .add _ _ | .mau .d true .mul _ _
  | .mau .d true .fma _ _ | .mau .d true .passa _ _
  | .mau .f true .add _ _ | .mau .f true .mul _ _
  | .mau .f true .fma _ _ | .mau .f true .passa _ _
  | .mau .g true .add _ _ | .mau .g true .mul _ _
  | .mau .g true .fma _ _ | .mau .g true .passa _ _
  | .mau .h true .add _ _ | .mau .h true .mul _ _
  | .mau .h true .fma _ _ | .mau .h true .passa _ _ => true
  | _ => false

def parsedExprIsL1MwriteProducer (expression : ParsedExpr) : Bool :=
  match expression.op with
  | .l1bm (.mwrite _) | .l1bm (.m4write _) => true
  | _ => false

def parsedExprIsL1GatherProducer (expression : ParsedExpr) : Bool :=
  match expression.op with
  | .l1bm (.gather _) => true
  | _ => false

def parsedExprIsL1ToPEProducer (expression : ParsedExpr) : Bool :=
  match expression.op with
  | .l1bm .pbcast | .l1bm .mbcast | .l1bm .m4bcast | .l1bm (.distrib _) => true
  | _ => false

def parsedExprIsNoForwardProducer (expression : ParsedExpr) : Bool :=
  match expression.op with
  | .noforward => true
  | _ => false

def parsedExprIsSupportedFloatMAUProducer (expression : ParsedExpr) : Bool :=
  match expression.op with
  | .mau .f false .add _ false | .mau .f false .mul _ false
  | .mau .f false .fma _ false | .mau .f false .passa _ false => true
  | .mau .f false _ _ true => true
  | .mau .d false .passa _ _ | .mau .h false .passa _ _
  | .mau .h false .mul _ _ | .mau .h false .add _ _
  | .mau .h false .fma _ _ => true
  | .mau .d false .add _ _ | .mau .d false .mul _ _
  | .mau .d false .fma _ _ => true
  | .mau .g false _ _ _ | .mau .l false _ _ _ | .mau .i false _ _ _
  | .mau .s false _ _ _ => true
  | _ => false

def parsedFloatMAUWritesBAR (lm1 : Bool) (expression : ParsedExpr) : Bool :=
  parsedExprIsSupportedFloatMAUProducer expression &&
    expression.destinations.any (fun destination =>
      match destination with
      | .bar destinationLM1 .. => destinationLM1 == lm1
      | _ => false)

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

def parsedFloatMAUSourceDefinitelyUnsupported (operand : ParsedOperand) : Bool :=
  match operand with
  | .mem .. | .forward .. => false
  | _ => true

def parsedFloatMAULoweringMiss {α : Type} (expression : ParsedExpr) :
    ProofsLean.StepResult α :=
  if expression.sources.any parsedFloatMAUSourceDefinitelyUnsupported then .failure
  else .unknown

theorem parsedFloatMAU_fixed_source_is_definitely_unsupported (fixed : ParsedFixed) :
    parsedFloatMAUSourceDefinitelyUnsupported (.fixed fixed) = true := by
  rfl

def parsedFloatMAUDestinationRole (destination : ParsedOperand) : Bool :=
  match destination with
  | .mem .. | .omr .. | .bar .. | .nowrite => true
  | _ => false

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
  destinations : List ParsedOperand

def lowerParsedFloatFma? (expression : ParsedExpr) (context : ParsedIntegerContext) :
    Option ParsedFloatFmaAccesses := do
  match expression.op with
  | .mau .f false .fma _ false => pure ()
  | _ => none
  match expression.sources, expression.destinations with
  | [sourceA, sourceB, sourceC], destinations@(_ :: _) => do
      guard (destinations.all parsedFloatMAUDestinationRole)
      let (sourceA, negateA, extendA, roundA) ← parsedFloatMAUSourceAttrs? sourceA context
      let (sourceB, negateB, extendB, roundB) ← parsedFloatMAUSourceAttrs? sourceB context
      let (sourceC, negateC, extendC, roundC) ← parsedFloatMAUSourceAttrs? sourceC context
      some ⟨sourceA, sourceB, sourceC, negateA, negateB, negateC,
        extendA, extendB, extendC, roundA, roundB, roundC, destinations⟩
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
  destinations : List ParsedOperand

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

def prepareDoubleMAUSource (bus : IntegerALU.Bus)
    (negate extend round : Bool) : BitVec 64 :=
  let widened := if extend then
      BitVec.ofNat 64 (RRN.extendFloatBits .single .double
        (bus.high.extractLsb' 32 32).toNat)
    else bus.high
  let signed := if negate then widened ^^^ (BitVec.ofNat 64 (2 ^ 63)) else widened
  if round then
    BitVec.ofNat 32 (RRN.extendFloatBits .double .single signed.toNat) ++
      (BitVec.ofNat 32 0)
  else
    let exponent := signed.toNat / 2 ^ 52 % 2048
    if exponent == 0 then 0
    else if exponent == 2047 then
      BitVec.ofNat 64 ((signed.toNat / 2 ^ 63) * 2 ^ 63 + 2047 * 2 ^ 52)
    else signed

theorem prepareDoubleMAUSource_extend_single_one :
    prepareDoubleMAUSource ⟨0x3f80000000000000, 0⟩ false true false =
      BitVec.ofNat 64 0x3ff0000000000000 := by
  decide

theorem prepareDoubleMAUSource_negativeZero_normalized :
    prepareDoubleMAUSource ⟨0x8000000000000000, 0⟩ false false false = 0 := by
  decide

theorem prepareDoubleMAUSource_round_double_three_halves :
    prepareDoubleMAUSource ⟨0x3ff8000000000000, 0⟩ false false true =
      BitVec.ofNat 32 0x3fc00000 ++ BitVec.ofNat 32 0 := by
  decide

def lowerParsedFloatMultiply? (expression : ParsedExpr) (context : ParsedIntegerContext) :
    Option ParsedFloatMultiplyAccesses := do
  match expression.op with
  | .mau .f false .mul _ false => pure ()
  | _ => none
  match expression.sources, expression.destinations with
  | [sourceA, sourceB], destinations@(_ :: _) => do
      guard (destinations.all parsedFloatMAUDestinationRole)
      let (sourceA, negateA, extendA, roundA) ← parsedFloatMAUSourceAttrs? sourceA context
      let (sourceB, negateB, extendB, roundB) ← parsedFloatMAUSourceAttrs? sourceB context
      some ⟨sourceA, sourceB, negateA, negateB, extendA, extendB, roundA, roundB,
        destinations⟩
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
  destinations : List ParsedOperand

def lowerParsedFloatAddMachine? (expression : ParsedExpr) (context : ParsedIntegerContext) :
    Option ParsedFloatAddAccesses := do
  match expression.op with
  | .mau .f false .add _ false => pure ()
  | _ => none
  match expression.sources, expression.destinations with
  | [sourceA, sourceB], destinations@(_ :: _) => do
      guard (destinations.all parsedFloatMAUDestinationRole)
      let (sourceA, negateA, extendA, roundA) ← parsedFloatMAUSourceAttrs? sourceA context
      let (sourceB, negateB, extendB, roundB) ← parsedFloatMAUSourceAttrs? sourceB context
      some ⟨sourceA, sourceB, negateA, negateB, extendA, extendB, roundA, roundB,
        destinations⟩
  | _, _ => none

def lowerParsedPassa? (precision : ParsedPrecision) (expression : ParsedExpr)
    (context : ParsedIntegerContext) :
    Option (ParsedIntegerInput × Bool × Bool × Bool × List ParsedOperand) := do
  match expression.op with
  | .mau opPrecision false .passa _ _ => guard (opPrecision == precision)
  | _ => none
  match expression.sources, expression.destinations with
  | [source], destinations@(_ :: _) => do
      guard (destinations.all parsedFloatMAUDestinationRole)
      let (source, negate, extend, round) ← parsedFloatMAUSourceAttrs? source context
      some (source, negate, extend, round, destinations)
  | _, _ => none

def lowerParsedHalfPassa? (expression : ParsedExpr) (context : ParsedIntegerContext) :
    Option (ParsedIntegerInput × Bool × Bool × Bool × List ParsedOperand) := do
  match expression.op with
  | .mau .h false .passa _ _ => pure ()
  | _ => none
  match expression.sources, expression.destinations with
  | [source], destinations@(_ :: _) => do
      guard (destinations.all parsedFloatMAUDestinationRole)
      let (source, negate, extend, round) ← parsedFloatMAUSourceAttrs? source context
      some (source, negate, extend, round, destinations)
  | _, _ => none

def lowerParsedHalfMultiply? (expression : ParsedExpr) (context : ParsedIntegerContext) :
    Option (ParsedIntegerInput × Bool × Bool × Bool × ParsedIntegerInput × Bool × Bool × Bool ×
      List ParsedOperand) := do
  match expression.op with
  | .mau .h false .mul _ _ => pure ()
  | _ => none
  match expression.sources, expression.destinations with
  | [sourceA, sourceB], destinations@(_ :: _) => do
      guard (destinations.all parsedFloatMAUDestinationRole)
      let (sourceA, negateA, extendA, roundA) ← parsedFloatMAUSourceAttrs? sourceA context
      let (sourceB, negateB, extendB, roundB) ← parsedFloatMAUSourceAttrs? sourceB context
      some (sourceA, negateA, extendA, roundA, sourceB, negateB, extendB, roundB,
        destinations)
  | _, _ => none

def lowerParsedHalfAdd? (expression : ParsedExpr) (context : ParsedIntegerContext) :
    Option (ParsedIntegerInput × Bool × Bool × Bool × ParsedIntegerInput × Bool × Bool × Bool ×
      List ParsedOperand) := do
  match expression.op with
  | .mau .h false .add _ _ => pure ()
  | _ => none
  match expression.sources, expression.destinations with
  | [sourceA, sourceC], destinations@(_ :: _) => do
      guard (destinations.all parsedFloatMAUDestinationRole)
      let (sourceA, negateA, extendA, roundA) ← parsedFloatMAUSourceAttrs? sourceA context
      let (sourceC, negateC, extendC, roundC) ← parsedFloatMAUSourceAttrs? sourceC context
      some (sourceA, negateA, extendA, roundA, sourceC, negateC, extendC, roundC,
        destinations)
  | _, _ => none

def lowerParsedHalfFma? (expression : ParsedExpr) (context : ParsedIntegerContext) :
    Option (ParsedIntegerInput × Bool × Bool × Bool × ParsedIntegerInput × Bool × Bool × Bool ×
      ParsedIntegerInput × Bool × Bool × Bool × List ParsedOperand) := do
  match expression.op with
  | .mau .h false .fma _ _ => pure ()
  | _ => none
  match expression.sources, expression.destinations with
  | [sourceA, sourceB, sourceC], destinations@(_ :: _) => do
      guard (destinations.all parsedFloatMAUDestinationRole)
      let (sourceA, negateA, extendA, roundA) ← parsedFloatMAUSourceAttrs? sourceA context
      let (sourceB, negateB, extendB, roundB) ← parsedFloatMAUSourceAttrs? sourceB context
      let (sourceC, negateC, extendC, roundC) ← parsedFloatMAUSourceAttrs? sourceC context
      some (sourceA, negateA, extendA, roundA, sourceB, negateB, extendB, roundB,
        sourceC, negateC, extendC, roundC, destinations)
  | _, _ => none

def lowerParsedDoubleArithmetic? (expression : ParsedExpr) (context : ParsedIntegerContext) :
    Option (CalcKind × Bool × List (ParsedIntegerInput × Bool × Bool × Bool) ×
      List ParsedOperand) := do
  let (kind, round) ← match expression.op with
    | .mau .d false kind _ round => do
        guard (kind == .add || kind == .mul || kind == .fma)
        some (kind, round)
    | _ => none
  let expected := match kind with | .fma => 3 | _ => 2
  guard (expression.sources.length == expected)
  let sources ← expression.sources.mapM fun source => parsedFloatMAUSourceAttrs? source context
  match expression.destinations with
  | destinations@(_ :: _) =>
      guard (destinations.all parsedFloatMAUDestinationRole)
      some (kind, round, sources, destinations)
  | _ => none

def normalizeHalfPassaLane (lane : BitVec 16) : BitVec 16 :=
  let exponent := lane.toNat / 2 ^ 9 % 64
  if exponent == 0 then 0
  else if exponent == 63 then
    BitVec.ofNat 16 ((lane.toNat / 2 ^ 15) * 2 ^ 15 + 63 * 2 ^ 9)
  else lane

def roundMAUSingleBusToHalf (bus : IntegerALU.Bus) : BitVec 64 :=
  roundSingleWordToHalf (bus.high.extractLsb' 32 32) ++
    roundSingleWordToHalf (bus.high.extractLsb' 0 32) ++
    roundSingleWordToHalf (bus.low.extractLsb' 32 32) ++
    roundSingleWordToHalf (bus.low.extractLsb' 0 32)

theorem roundMAUSingleBusToHalf_preserves_lane_order :
    roundMAUSingleBusToHalf ⟨0x3f80000040000000, 0x4040000040800000⟩ =
      BitVec.ofNat 16 0x3e00 ++ BitVec.ofNat 16 0x4000 ++
        BitVec.ofNat 16 0x4100 ++ BitVec.ofNat 16 0x4200 := by
  decide

def prepareHalfPassa (bus : IntegerALU.Bus)
    (negate sourceRound outputRound : Bool) : IntegerALU.Bus :=
  let raw := if sourceRound then ⟨roundMAUSingleBusToHalf bus, 0⟩ else bus
  let signMask := BitVec.ofNat 64 (2 ^ 63 + 2 ^ 47 + 2 ^ 31 + 2 ^ 15)
  let signed := if negate then raw.high ^^^ signMask else raw.high
  let lane0 := normalizeHalfPassaLane (signed.extractLsb' 48 16)
  let lane1 := normalizeHalfPassaLane (signed.extractLsb' 32 16)
  let lane2 := normalizeHalfPassaLane (signed.extractLsb' 16 16)
  let lane3 := normalizeHalfPassaLane (signed.extractLsb' 0 16)
  if outputRound then ⟨lane0 ++ lane1 ++ lane2 ++ lane3, 0⟩ else
    ⟨BitVec.ofNat 32 (RRN.extendFloatBits .half .single lane0.toNat) ++
      BitVec.ofNat 32 (RRN.extendFloatBits .half .single lane1.toNat),
     BitVec.ofNat 32 (RRN.extendFloatBits .half .single lane2.toNat) ++
      BitVec.ofNat 32 (RRN.extendFloatBits .half .single lane3.toNat)⟩

def halfMultiplyLane (left right : BitVec 16) : BitVec 16 :=
  let sign := (left.toNat / 2 ^ 15 + right.toNat / 2 ^ 15) % 2
  let leftExponent := left.toNat / 2 ^ 9 % 64
  let rightExponent := right.toNat / 2 ^ 9 % 64
  let exponentMax := 63
  let output := if leftExponent == 0 || rightExponent == 0 then 0
    else if leftExponent == exponentMax || rightExponent == exponentMax then
      sign * 2 ^ 15 + exponentMax * 2 ^ 9
    else
      let leftSignificand := 2 ^ 9 + left.toNat % 2 ^ 9
      let rightSignificand := 2 ^ 9 + right.toNat % 2 ^ 9
      let binaryExponent := Int.ofNat leftExponent + Int.ofNat rightExponent - 2 * 31 - 2 * 9
      RRN.roundPack .half (sign == 1) (leftSignificand * rightSignificand) binaryExponent
  BitVec.ofNat 16 output

def prepareHalfMulInput (bus : IntegerALU.Bus) (negate round : Bool) : BitVec 64 :=
  let raw := if round then roundMAUSingleBusToHalf bus else bus.high
  let signMask := BitVec.ofNat 64 (2 ^ 63 + 2 ^ 47 + 2 ^ 31 + 2 ^ 15)
  let signed := if negate then raw ^^^ signMask else raw
  signed

def prepareHalfMultiplyBus (left right : BitVec 64) (roundOutput : Bool) :
    IntegerALU.Bus :=
  let l0 := left.extractLsb' 48 16
  let l1 := left.extractLsb' 32 16
  let l2 := left.extractLsb' 16 16
  let l3 := left.extractLsb' 0 16
  let r0 := right.extractLsb' 48 16
  let r1 := right.extractLsb' 32 16
  let r2 := right.extractLsb' 16 16
  let r3 := right.extractLsb' 0 16
  let h0 := halfMultiplyLane l0 r0
  let h1 := halfMultiplyLane l1 r1
  let h2 := halfMultiplyLane l2 r2
  let h3 := halfMultiplyLane l3 r3
  if roundOutput then ⟨h0 ++ h1 ++ h2 ++ h3, 0⟩
  else
    ⟨BitVec.ofNat 32 (RRN.extendFloatBits .half .single h0.toNat) ++
        BitVec.ofNat 32 (RRN.extendFloatBits .half .single h1.toNat),
      BitVec.ofNat 32 (RRN.extendFloatBits .half .single h2.toNat) ++
        BitVec.ofNat 32 (RRN.extendFloatBits .half .single h3.toNat)⟩

def prepareHalfAddSource (bus : IntegerALU.Bus) (negate extend round : Bool)
    (asAccumulator : Bool) : List Nat := Id.run do
  let signMask (width : Nat) := 2 ^ (width - 1)
  if asAccumulator then
    let singleValues := if extend then
        (List.range 4).map fun lane =>
          let shift := 48 - lane * 16
          RRN.extendFloatBits .half .single ((bus.high.extractLsb' shift 16).toNat)
      else if round then
        [RRN.extendFloatBits .double .single bus.high.toNat,
          RRN.extendFloatBits .double .single bus.low.toNat, 0, 0]
      else (List.range 4).map fun lane =>
        let bits := if lane < 2 then (bus.high.extractLsb' (32 * (1 - lane)) 32).toNat
          else (bus.low.extractLsb' (32 * (3 - lane)) 32).toNat
        bits
    return singleValues.map fun bits => if negate then bits ^^^ signMask 32 else bits
  else
    let halfValues := if round then
        [roundSingleWordToHalf (bus.high.extractLsb' 32 32),
          roundSingleWordToHalf (bus.high.extractLsb' 0 32),
          roundSingleWordToHalf (bus.low.extractLsb' 32 32),
          roundSingleWordToHalf (bus.low.extractLsb' 0 32)].map BitVec.toNat
      else (List.range 4).map fun lane =>
        let shift := 48 - lane * 16
        (bus.high.extractLsb' shift 16).toNat
    return halfValues.map fun bits => if negate then bits ^^^ signMask 16 else bits

def prepareHalfFmaBus (left right accumulator : List Nat) (roundOutput : Bool) :
    IntegerALU.Bus := Id.run do
  let results := (List.range 4).map fun lane =>
    RRN.vectorMAUFma .half .single (if roundOutput then .half else .single)
      (left[lane]!) (right[lane]!) (accumulator[lane]!)
  if roundOutput then
    return ⟨BitVec.ofNat 64 ((results[0]! * 2 ^ 48) + (results[1]! * 2 ^ 32) +
      (results[2]! * 2 ^ 16) + results[3]!), 0⟩
  else
    return ⟨BitVec.ofNat 32 results[0]! ++ BitVec.ofNat 32 results[1]!,
      BitVec.ofNat 32 results[2]! ++ BitVec.ofNat 32 results[3]!⟩

theorem prepareHalfAddSource_rounds_two_double_accumulator_lanes :
    prepareHalfAddSource ⟨0x3ff0000000000000, 0x4000000000000000⟩
      false false true true = [0x3f800000, 0x40000000, 0, 0] := by
  decide

def readMAUSourceBuses (readFiles : IntegerRegisterFiles) (oldSlots : Forwarding.Slots)
    (cycle : Fin 4) : List ParsedIntegerInput →
      ProofsLean.StepResult (List IntegerALU.Bus)
  | [] => .ok []
  | source :: rest =>
      match ParsedIntegerInput.readWithForwarding readFiles oldSlots cycle source with
      | .failure => .failure
      | .unknown => .unknown
      | .ok bus =>
          match readMAUSourceBuses readFiles oldSlots cycle rest with
          | .failure => .failure
          | .unknown => .unknown
          | .ok buses => .ok (bus :: buses)

def doubleMAUVectorBus (kind : CalcKind) (roundOutput : Bool)
    (values : List (BitVec 64)) : IntegerALU.Bus := Id.run do
  let a := values[0]!.toNat
  let (b, c) := match kind, values with
    | .add, [_, accumulator] => (0x3ff0000000000000, accumulator.toNat)
    | .mul, [_, right] => (right.toNat, 0)
    | .fma, [_, right, accumulator] => (right.toNat, accumulator.toNat)
    | _, _ => (0, 0)
  let outputPrecision := if roundOutput then RRN.FloatPrecision.single
    else RRN.FloatPrecision.double
  let result := RRN.vectorMAUFma .double .double outputPrecision a b c
  if roundOutput then
    return ⟨BitVec.ofNat 32 result ++ BitVec.ofNat 32 0, 0⟩
  else return ⟨BitVec.ofNat 64 result, 0⟩

theorem doubleMAUVectorBus_add_and_fma :
    doubleMAUVectorBus .add false [0x3ff0000000000000, 0x3ff0000000000000] =
      ⟨0x4000000000000000, 0⟩ ∧
    doubleMAUVectorBus .fma true
      [0x3ff0000000000000, 0x4000000000000000, 0x3ff0000000000000] =
      ⟨0x4040000000000000, 0⟩ := by
  decide

theorem halfMultiplyLane_oneAndHalf_times_two :
    halfMultiplyLane 0x3f00 0x4000 = 0x4100 := by
  decide

theorem halfMultiplyLane_zero_times_infinity :
    halfMultiplyLane 0x8000 0x7e00 = 0 := by
  decide

theorem halfMultiplyLane_infinity_sign_and_normalization :
    halfMultiplyLane 0xfc01 0x4000 = 0xfe00 := by
  decide

theorem prepareHalfMultiplyBus_rounds_or_widens_outputs :
    prepareHalfMultiplyBus 0x3f00400000000000 0x40003e0000000000 false =
        ⟨0x4040000040000000, 0⟩ ∧
      prepareHalfMultiplyBus 0x3f00400000000000 0x40003e0000000000 true =
        ⟨0x4100400000000000, 0⟩ := by
  decide

theorem prepareHalfFmaBus_round_modes :
    prepareHalfFmaBus [0x3e00, 0x3e00, 0x3e00, 0x3e00]
      [0x3e00, 0x3e00, 0x3e00, 0x3e00]
      [0x3f800000, 0x3f800000, 0x3f800000, 0x3f800000] false =
        ⟨0x4000000040000000, 0x4000000040000000⟩ ∧
    prepareHalfFmaBus [0x3e00, 0x3e00, 0x3e00, 0x3e00]
      [0x3e00, 0x3e00, 0x3e00, 0x3e00]
      [0x3f800000, 0x3f800000, 0x3f800000, 0x3f800000] true =
        ⟨0x4000400040004000, 0⟩ := by
  decide

theorem prepareHalfPassa_one_widens_to_single :
    prepareHalfPassa ⟨0x3e00000000000000, 0⟩ false false false =
      ⟨0x3f80000000000000, 0⟩ := by
  decide

theorem prepareHalfPassa_single_input_rounding :
    prepareHalfPassa ⟨0x3f80000000000000, 0⟩ false true true =
      ⟨0x3e00000000000000, 0⟩ := by
  decide

theorem prepareHalfPassa_negativeZero_normalized :
    prepareHalfPassa ⟨0x8000000000000000, 0⟩ false false false =
      ⟨0, 0⟩ := by
  decide


def singleFmaBus (left right accumulator : BitVec 64) : BitVec 64 :=
  SingleFMA.singleFma (left.extractLsb' 32 32) (right.extractLsb' 32 32)
      (accumulator.extractLsb' 32 32) ++
    SingleFMA.singleFma (left.extractLsb' 0 32) (right.extractLsb' 0 32)
      (accumulator.extractLsb' 0 32)

def singlePassaBus (source : BitVec 64) : BitVec 64 :=
  singleFmaBus source (BitVec.ofNat 32 0x3f800000 ++ BitVec.ofNat 32 0x3f800000) 0

theorem singlePassaBus_negativeZero_normalized :
    singlePassaBus (BitVec.ofNat 64 0x8000000080000000) = 0 := by
  decide

theorem parsedFloatMAUSource?_forward
    (kind : ParsedForward) (context : ParsedIntegerContext) :
    parsedFloatMAUSource? (.forward kind false false false) context =
      some (.forward kind false) := by
  simp [parsedFloatMAUSource?, ParsedOperand.toParsedIntegerInput?]

theorem lowerParsedFloatMultiply?_fvmul
    (sourceA sourceB : ParsedOperand) (destinationAccess : Access)
    (context : ParsedIntegerContext) (inputA inputB : ParsedIntegerInput)
    (negateA negateB extendA extendB roundA roundB : Bool)
    (sourceALowered : parsedFloatMAUSourceAttrs? sourceA context =
      some (inputA, negateA, extendA, roundA))
    (sourceBLowered : parsedFloatMAUSourceAttrs? sourceB context =
      some (inputB, negateB, extendB, roundB))
    :
    lowerParsedFloatMultiply?
      ⟨.mau .f false .mul none false,
        [sourceA, sourceB], [.mem destinationAccess false false false none], none, "fvmul"⟩
      context = some ⟨inputA, inputB, negateA, negateB, extendA, extendB, roundA, roundB,
        [.mem destinationAccess false false false none]⟩ := by
  simp [lowerParsedFloatMultiply?, sourceALowered, sourceBLowered,
    parsedFloatMAUDestinationRole]

def parsedMauHalfSelectsPE (half : Option Char) (pe : Fin 4) : Bool :=
  match half with
  | none => true
  | some 'u' => pe.val < 2
  | some 'd' => pe.val ≥ 2
  | some _ => false

def parsedVectorMAUFlags (format : RRN.FloatPrecision) (rounded : Bool)
    (output : IntegerALU.Bus) : BitVec 4 := Id.run do
  let lanes : List Nat := match format, rounded with
    | .double, false => [output.high.toNat]
    | .double, true => [(output.high.extractLsb' 32 32).toNat]
    | .single, _ => [
        (output.high.extractLsb' 32 32).toNat,
        (output.high.extractLsb' 0 32).toNat]
    | .half, true => [
        (output.high.extractLsb' 48 16).toNat,
        (output.high.extractLsb' 32 16).toNat,
        (output.high.extractLsb' 16 16).toNat,
        (output.high.extractLsb' 0 16).toNat]
    | .half, false => [
        (output.high.extractLsb' 32 32).toNat,
        (output.high.extractLsb' 0 32).toNat,
        (output.low.extractLsb' 32 32).toNat,
        (output.low.extractLsb' 0 32).toNat]
  let signFormat := match format, rounded with
    | .double, false => .double
    | .double, true => .single
    | .single, _ => .single
    | .half, true => .half
    | .half, false => .single
  let positive (bits : Nat) := !RRN.floatIsNegative signFormat bits
  let flags := match lanes with
    | [value] =>
        let isPositive := positive value
        if signFormat == .double then if isPositive then 0xf else 0
        else if isPositive then 0xc else 0
    | [first, second] =>
        (if positive first then 0xc else 0) + (if positive second then 0x3 else 0)
    | [a, b, c, d] =>
        (if positive a then 8 else 0) + (if positive b then 4 else 0) +
          (if positive c then 2 else 0) + (if positive d then 1 else 0)
    | _ => 0
  return BitVec.ofNat 4 flags

theorem parsedVectorMAUFlags_single_lane_order :
    parsedVectorMAUFlags .single false ⟨0x3f800000bf800000, 0⟩ = 0xc := by
  decide

theorem parsedVectorMAUFlags_double_uses_all_flags_for_positive :
    parsedVectorMAUFlags .double false ⟨0x3ff0000000000000, 0⟩ = 0xf := by
  decide

theorem parsedVectorMAUFlags_half_word_order :
    parsedVectorMAUFlags .half true ⟨0x3c00bc003c00bc00, 0⟩ = 0xa := by
  decide

theorem parsedMauHalfSelectsPE_upper_lanes :
    parsedMauHalfSelectsPE (some 'u') 1 = true ∧
      parsedMauHalfSelectsPE (some 'u') 2 = false := by
  decide

theorem parsedMauHalfSelectsPE_lower_lanes :
    parsedMauHalfSelectsPE (some 'd') 1 = false ∧
      parsedMauHalfSelectsPE (some 'd') 2 = true := by
  decide

structure ParsedMslMsrDestinationWrite where
  files : PEMemory.IntegerRegisterFiles
  barUpdate : Option (Bool × BitVec 12)

def writeParsedMslMsrDestination? (files : PEMemory.IntegerRegisterFiles)
    (destination : ParsedOperand) (context : ParsedIntegerContext)
    (output : IntegerALU.Bus) (flags : BitVec 4) (cycle : Fin 4)
    (directive : ParsedMaskDirective) (hasSingleLineMask : Bool) :
    Option ParsedMslMsrDestinationWrite :=
  match destination with
  | .mem .. => do
      let access ← ParsedOperand.toDirectMemoryDestination? destination context.pe cycle
        context.bar0 context.bar1 context.tWord
      let selection ← ParsedOperand.resolveMemoryWriteSelection? destination access.bank
        files.maskRegisters cycle directive hasSingleLineMask
      some ⟨PEMemory.writeDirectAccessMasked files access
        (PEMemory.unpackALUBus output) selection, none⟩
  | .omr .. => do
      let entry ← ParsedOperand.toMaskRegisterEntry? destination
      let selection ← ParsedOperand.resolveOmrWriteSelection? destination files.maskRegisters
        cycle directive hasSingleLineMask
      let maskRegisters := ProofsLean.MNCore.Masks.writeRegister
        files.maskRegisters entry cycle flags selection
      some ⟨{ files with maskRegisters := maskRegisters }, none⟩
  | .bar lm1 _ _ => do
      let bank := if lm1 then PEMemory.Bank.lm1 else PEMemory.Bank.lm0
      let selection ← ParsedOperand.resolveMemoryWriteSelection? destination bank
        files.maskRegisters cycle directive hasSingleLineMask
      let barValue := BitVec.ofNat 12
        ((output.high.extractLsb' 32 32).toNat % 2 ^ 12)
      let update := if selection.flags == 0 then none else some (lm1, barValue)
      some ⟨files, update⟩
  | .nowrite => some ⟨files, none⟩
  | _ => none

structure ParsedMAUDestinationWrites where
  files : PEMemory.IntegerRegisterFiles
  bar0 : BitVec 12
  bar1 : BitVec 12

def writeParsedMAUDestinations? (files : PEMemory.IntegerRegisterFiles)
    (destinations : List ParsedOperand) (context : ParsedIntegerContext)
    (output : IntegerALU.Bus) (flags : BitVec 4) (cycle : Fin 4)
    (directive : ParsedMaskDirective) (hasSingleLineMask : Bool) :
    Option ParsedMAUDestinationWrites := do
  let rec writeAll : List ParsedOperand → PEMemory.IntegerRegisterFiles →
      BitVec 12 → BitVec 12 → Option ParsedMAUDestinationWrites
    | [], currentFiles, bar0, bar1 => some ⟨currentFiles, bar0, bar1⟩
    | destination :: rest, currentFiles, bar0, bar1 => do
        let currentContext := { context with bar0 := bar0, bar1 := bar1 }
        let write ← writeParsedMslMsrDestination? currentFiles destination currentContext
          output flags cycle directive hasSingleLineMask
        let nextBar0 := match write.barUpdate with
          | some (false, value) => value
          | _ => bar0
        let nextBar1 := match write.barUpdate with
          | some (true, value) => value
          | _ => bar1
        writeAll rest write.files nextBar0 nextBar1
  writeAll destinations files context.bar0 context.bar1

/-- Compute one vector-MAU cycle from the pre-issue operands. Destination
commit is kept in the cycle runner so every encoded output operand receives
the same bus, flags, flush, mask, and sequential BAR behavior. -/
def executeParsedFloatMAUCycleAtPE (readFiles currentFiles : IntegerRegisterFiles)
    (oldSlots : Forwarding.Slots) (expression : ParsedExpr)
    (context : ParsedIntegerContext) (cycle : Fin 4) :
    ProofsLean.StepResult (IntegerRegisterFiles × IntegerALU.Bus × BitVec 4) :=
  match expression.op with
  | .mau .f false .fma half false =>
    let cycleContext := { context with cycle := cycle }
    match lowerParsedFloatFma? expression cycleContext with
    | none => parsedFloatMAULoweringMiss expression
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
            let output := if parsedMauHalfSelectsPE half cycleContext.pe then
              singleFmaBus left right accumulator else singleFmaBus 0 0 accumulator
            .ok (currentFiles, ⟨output, 0⟩,
              parsedVectorMAUFlags .single false ⟨output, 0⟩)
  | .mau .f false .mul half false =>
    let cycleContext := { context with cycle := cycle }
    match lowerParsedFloatMultiply? expression cycleContext with
    | none => parsedFloatMAULoweringMiss expression
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
          let output := if parsedMauHalfSelectsPE half cycleContext.pe then
              FloatMultiply.multiplyBus left right else FloatMultiply.multiplyBus 0 0
          .ok (currentFiles, ⟨output, 0⟩,
            parsedVectorMAUFlags .single false ⟨output, 0⟩)
  | .mau .f false .add half false =>
    let cycleContext := { context with cycle := cycle }
    match lowerParsedFloatAddMachine? expression cycleContext with
    | none => parsedFloatMAULoweringMiss expression
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
          let output := if parsedMauHalfSelectsPE half cycleContext.pe then
              FloatAdd.addBus left right else singleFmaBus 0 0 right
          .ok (currentFiles, ⟨output, 0⟩,
            parsedVectorMAUFlags .single false ⟨output, 0⟩)
  | .mau .f false .passa half false =>
    let cycleContext := { context with cycle := cycle }
    match lowerParsedPassa? .f expression cycleContext with
    | none => parsedFloatMAULoweringMiss expression
    | some (source, negate, extend, round, _destinations) =>
      match ParsedIntegerInput.readWithForwarding readFiles oldSlots cycle source with
      | .failure => .failure
      | .unknown => .unknown
      | .ok sourceBus =>
        let prepared := prepareSingleMAUSource sourceBus negate extend round
        let output := if parsedMauHalfSelectsPE half cycleContext.pe then
            singlePassaBus prepared else singlePassaBus 0
        .ok (currentFiles, ⟨output, 0⟩,
          parsedVectorMAUFlags .single false ⟨output, 0⟩)
  | .mau .d false .passa half round =>
    let cycleContext := { context with cycle := cycle }
    match lowerParsedPassa? .d expression cycleContext with
    | none => parsedFloatMAULoweringMiss expression
    | some (source, negate, extend, sourceRound, _destinations) =>
      if sourceRound && !extend then .failure else
      match ParsedIntegerInput.readWithForwarding readFiles oldSlots cycle source with
      | .failure => .failure
      | .unknown => .unknown
      | .ok sourceBus =>
        let output := if parsedMauHalfSelectsPE half cycleContext.pe then
            prepareDoubleMAUSource sourceBus negate extend round else 0
        .ok (currentFiles, ⟨output, 0⟩,
          parsedVectorMAUFlags .double round ⟨output, 0⟩)
  | .mau .d false kind half roundOutput =>
    let cycleContext := { context with cycle := cycle }
    match lowerParsedDoubleArithmetic? expression cycleContext with
    | none => parsedFloatMAULoweringMiss expression
    | some (kind, roundOutput, sources, _destinations) =>
      if sources.any (fun source => source.2.2.2) then .failure else
      match readMAUSourceBuses readFiles oldSlots cycle (sources.map fun source => source.1) with
      | .failure => .failure
      | .unknown => .unknown
      | .ok sourceBuses =>
        let prepared := (List.zip sources sourceBuses).map fun (source, bus) =>
          prepareDoubleMAUSource bus source.2.1 source.2.2.1 false
        let calculated := doubleMAUVectorBus kind roundOutput prepared
        let inactivePrepared := match kind, prepared with
          | .add, [_, accumulator] => [0, accumulator]
          | .mul, [_, _] => [0, 0]
          | .fma, [_, _, accumulator] => [0, 0, accumulator]
          | _, _ => prepared
        let inactive := doubleMAUVectorBus kind roundOutput inactivePrepared
        let output := if parsedMauHalfSelectsPE half cycleContext.pe then calculated else inactive
        .ok (currentFiles, output, parsedVectorMAUFlags .double roundOutput output)
  | .mau .h false .mul half round =>
    let cycleContext := { context with cycle := cycle }
    match lowerParsedHalfMultiply? expression cycleContext with
    | none => parsedFloatMAULoweringMiss expression
    | some (sourceA, negateA, extendA, roundA, sourceB, negateB, extendB, roundB,
        destinations) =>
      if extendA || extendB then .failure else
      match ParsedIntegerInput.readWithForwarding readFiles oldSlots cycle sourceA with
      | .failure => .failure
      | .unknown => .unknown
      | .ok sourceABus =>
        match ParsedIntegerInput.readWithForwarding readFiles oldSlots cycle sourceB with
        | .failure => .failure
        | .unknown => .unknown
        | .ok sourceBBus =>
          let left := prepareHalfMulInput sourceABus negateA roundA
          let right := prepareHalfMulInput sourceBBus negateB roundB
          let calculated := prepareHalfMultiplyBus left right round
          let output := if parsedMauHalfSelectsPE half cycleContext.pe then calculated
            else (⟨0, 0⟩ : IntegerALU.Bus)
          .ok (currentFiles, output, parsedVectorMAUFlags .half round output)
  | .mau .h false .add half round =>
    let cycleContext := { context with cycle := cycle }
    match lowerParsedHalfAdd? expression cycleContext with
    | none => parsedFloatMAULoweringMiss expression
    | some (sourceA, negateA, extendA, roundA, sourceC, negateC, extendC, roundC,
        destinations) =>
      if extendA then .failure else
      match ParsedIntegerInput.readWithForwarding readFiles oldSlots cycle sourceA with
      | .failure => .failure
      | .unknown => .unknown
      | .ok sourceABus =>
        match ParsedIntegerInput.readWithForwarding readFiles oldSlots cycle sourceC with
        | .failure => .failure
        | .unknown => .unknown
        | .ok sourceCBus =>
          let left := prepareHalfAddSource sourceABus negateA extendA roundA false
          let accumulator := prepareHalfAddSource sourceCBus negateC extendC roundC true
          let ones := [0x3e00, 0x3e00, 0x3e00, 0x3e00]
          let calculated := prepareHalfFmaBus left ones accumulator round
          let zeros := [0, 0, 0, 0]
          let inactive := prepareHalfFmaBus zeros zeros accumulator round
          let output := if parsedMauHalfSelectsPE half cycleContext.pe then calculated else inactive
          .ok (currentFiles, output, parsedVectorMAUFlags .half round output)
  | .mau .h false .fma half round =>
    let cycleContext := { context with cycle := cycle }
    match lowerParsedHalfFma? expression cycleContext with
    | none => parsedFloatMAULoweringMiss expression
    | some (sourceA, negateA, extendA, roundA, sourceB, negateB, extendB, roundB,
        sourceC, negateC, extendC, roundC, destinations) =>
      if extendA || extendB then .failure else
      match ParsedIntegerInput.readWithForwarding readFiles oldSlots cycle sourceA with
      | .failure => .failure
      | .unknown => .unknown
      | .ok sourceABus =>
        match ParsedIntegerInput.readWithForwarding readFiles oldSlots cycle sourceB with
        | .failure => .failure
        | .unknown => .unknown
        | .ok sourceBBus =>
          match ParsedIntegerInput.readWithForwarding readFiles oldSlots cycle sourceC with
          | .failure => .failure
          | .unknown => .unknown
          | .ok sourceCBus =>
            let left := prepareHalfAddSource sourceABus negateA extendA roundA false
            let right := prepareHalfAddSource sourceBBus negateB extendB roundB false
            let accumulator := prepareHalfAddSource sourceCBus negateC extendC roundC true
            let calculated := prepareHalfFmaBus left right accumulator round
            let zeros := [0, 0, 0, 0]
            let inactive := prepareHalfFmaBus zeros zeros accumulator round
            let output := if parsedMauHalfSelectsPE half cycleContext.pe then calculated else inactive
            .ok (currentFiles, output, parsedVectorMAUFlags .half round output)
  | .mau .h false .passa half round =>
    let cycleContext := { context with cycle := cycle }
    match lowerParsedHalfPassa? expression cycleContext with
    | none => parsedFloatMAULoweringMiss expression
    | some (source, negate, extend, sourceRound, _destinations) =>
      if extend then .failure else
      match ParsedIntegerInput.readWithForwarding readFiles oldSlots cycle source with
      | .failure => .failure
      | .unknown => .unknown
      | .ok sourceBus =>
        let output := if parsedMauHalfSelectsPE half cycleContext.pe then
            prepareHalfPassa sourceBus negate sourceRound round else (⟨0, 0⟩ : IntegerALU.Bus)
        .ok (currentFiles, output, parsedVectorMAUFlags .half round output)
  | .mau .f false _ _ true => .failure
  | .mau .g false _ _ _ | .mau .l false _ _ _ | .mau .i false _ _ _
  | .mau .s false _ _ _ => .failure
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
        .ok (currentFiles, ⟨output, 0⟩,
          parsedVectorMAUFlags .single false ⟨output, 0⟩)
  | some (leftAddress, rightAddress, destinationAddress) =>
      let left := FloatPEMemory.readPair .lm0 readFiles.lm0 leftAddress
      let right := FloatPEMemory.readPair .lm0 readFiles.lm0 rightAddress
      let output := FloatAdd.addBus left right
      .ok (currentFiles, ⟨output, 0⟩,
        parsedVectorMAUFlags .single false ⟨output, 0⟩)

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
      .ok (currentFiles, ⟨output, 0⟩, parsedVectorMAUFlags .single false ⟨output, 0⟩) := by
  simp [executeParsedFloatMAUCycleAtPE, parsedMauHalfSelectsPE, isMul, lowered, readA, readB]

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
      .ok (currentFiles, ⟨output, 0⟩, parsedVectorMAUFlags .single false ⟨output, 0⟩) := by
  simp [executeParsedFloatMAUCycleAtPE, parsedMauHalfSelectsPE, isFma, lowered, readA, readB, readC]

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
      .ok (currentFiles, ⟨output, 0⟩, parsedVectorMAUFlags .single false ⟨output, 0⟩) := by
  simp [executeParsedFloatMAUCycleAtPE, parsedMauHalfSelectsPE, isAdd, lowered, readA, readB]

/-- Run vector-MAU cycles and commit the bus to all destinations in source
order, carrying BAR updates into the following cycle. -/
def executeParsedFloatMAUCyclesAtPE (readFiles : IntegerRegisterFiles)
    (oldSlots : Forwarding.Slots) (expression : ParsedExpr)
    (context : ParsedIntegerContext) (directive : ParsedMaskDirective)
    (hasSingleLineMask : Bool) : List (Fin 4) → IntegerRegisterFiles →
      BitVec 12 → BitVec 12 → (Fin 4 → IntegerALU.Bus) → ProofsLean.StepResult
        (IntegerRegisterFiles × BitVec 12 × BitVec 12 × (Fin 4 → IntegerALU.Bus))
  | [], files, bar0, bar1, outputs => .ok (files, bar0, bar1, outputs)
  | cycle :: rest, files, bar0, bar1, outputs =>
      let cycleContext := { context with cycle := cycle, bar0 := bar0, bar1 := bar1 }
      match executeParsedFloatMAUCycleAtPE readFiles files oldSlots expression cycleContext cycle with
      | .failure => .failure
      | .unknown => .unknown
      | .ok (_, output, flags) =>
          match resolveFlushSelection? expression.flush files.maskRegisters cycle with
          | none => .unknown
          | some flushSelection =>
              let writtenOutput := parsedOutputAfterFlush flushSelection output
              match writeParsedMAUDestinations? files expression.destinations cycleContext
                  writtenOutput flags cycle directive hasSingleLineMask with
              | none => .unknown
              | some writes =>
                  executeParsedFloatMAUCyclesAtPE readFiles oldSlots expression context
                    directive hasSingleLineMask rest writes.files writes.bar0 writes.bar1
                    (fun index => if index = cycle then output else outputs index)

def executeParsedFloatMAUsAtPE (readState currentFiles : IntegerRegisterFiles)
    (oldSlots : Forwarding.Slots) (context : ParsedIntegerContext)
    (expressions : List ParsedExpr) (directive : ParsedMaskDirective)
    (hasSingleLineMask : Bool) : ProofsLean.StepResult
      (IntegerRegisterFiles × BitVec 12 × BitVec 12 × (Fin 4 → IntegerALU.Bus) × Bool) :=
  let floatAdds := expressions.filter parsedExprIsSupportedFloatMAUProducer
  let rec run (remaining : List ParsedExpr) (files : IntegerRegisterFiles)
      (bar0 bar1 : BitVec 12) (outputs : Fin 4 → IntegerALU.Bus) :
      ProofsLean.StepResult
        (IntegerRegisterFiles × BitVec 12 × BitVec 12 × (Fin 4 → IntegerALU.Bus)) :=
    match remaining with
    | [] => .ok (files, bar0, bar1, outputs)
    | expression :: rest =>
        match executeParsedFloatMAUCyclesAtPE readState oldSlots expression context
            directive hasSingleLineMask [0, 1, 2, 3] files bar0 bar1 (fun _ => ⟨0, 0⟩) with
        | .failure => .failure
        | .unknown => .unknown
        | .ok (nextFiles, nextBar0, nextBar1, nextOutputs) =>
            run rest nextFiles nextBar0 nextBar1 nextOutputs
  match run floatAdds currentFiles context.bar0 context.bar1 (fun _ => ⟨0, 0⟩) with
  | .failure => .failure
  | .unknown => .unknown
  | .ok (files, bar0, bar1, outputs) =>
      .ok (files, bar0, bar1, outputs, !floatAdds.isEmpty)

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

def lowerParsedMatrixWriteResult (expression : ParsedExpr) (context : ParsedIntegerContext) :
    ProofsLean.StepResult ParsedMatrixWriteAccesses :=
  match lowerParsedMatrixWrite? expression context with
  | some accesses => .ok accesses
  | none => match expression.sources with
      | [.mem ..] | [.forward ..] => .unknown
      | _ => .failure

theorem lowerParsedMatrixWrite_fixed_source_is_failure
    (fixed : ParsedFixed) (context : ParsedIntegerContext) (row : Fin (2 ^ 32)) :
    lowerParsedMatrixWriteResult
      { op := .matrixWrite .d
        sources := [.fixed fixed]
        destinations := [.matrix false ⟨1, by decide⟩ (some row)]
        flush := none
        text := "" } context = .failure := by
  rfl

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
    | .f | .g | .l | .i | .s => .ok { converted with high := negateSingleBus converted.high }
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
        match lowerParsedMatrixWriteResult expression context with
        | .failure => .failure
        | .unknown => .unknown
        | .ok accesses =>
            match ParsedIntegerInput.readWithForwarding
                (state.peRegisters (physicalPEId coordinate pe))
                (stateForwardingSlots state (physicalPEId coordinate pe)) cycle accesses.source with
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
      match lowerParsedMatrixWriteResult expression (groupContext.at 0 cycle) with
      | .failure => .failure
      | .unknown => .unknown
      | .ok accesses =>
          match readParsedMatrixWriteBuses state coordinate expression cycle with
          | .failure => .failure
          | .unknown => .unknown
          | .ok buses =>
              .ok (writeParsedDoubleMatrixStoreRow store coordinate.mab accesses.sideY
                (doubleMatrixWriteRowAt accesses.row cycle) (fun pe => (buses pe).high))
  | .matrixWrite .f | .matrixWrite .g | .matrixWrite .l
  | .matrixWrite .i | .matrixWrite .s =>
      match lowerParsedMatrixWriteResult expression (groupContext.at 0 cycle) with
      | .failure => .failure
      | .unknown => .unknown
      | .ok accesses =>
          match readParsedMatrixWriteBuses state coordinate expression cycle with
          | .failure => .failure
          | .unknown => .unknown
          | .ok buses =>
              .ok (writeParsedSingleMatrixStoreRow store coordinate.mab accesses.sideY
                (singleMatrixWriteRowAt accesses.row cycle) (singleMatrixWriteValues buses))
  | .matrixWrite .h =>
      match lowerParsedMatrixWriteResult expression (groupContext.at 0 cycle) with
      | .failure => .failure
      | .unknown => .unknown
      | .ok accesses =>
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

def parsedMatrixMAUFloatFormat : ParsedPrecision → Option RRN.FloatPrecision
  | .d => some .double
  | .f | .g => some .single
  | .h => some .half
  | .l | .i | .s => none

def parsedMatrixMAUKeptMantissaBits : ParsedPrecision → Nat
  | .d => 52
  | .f => 23
  | .g => 18
  | .h => 9
  | .l | .i | .s => 0

def parsedMatrixMAUOutputFormat (precision : ParsedPrecision) (round : Bool) :
    Option RRN.FloatPrecision := do
  match parsedMatrixMAUFloatFormat precision with
  | none => none
  | some .double => some (if round then .single else .double)
  | some .half => some (if round then .half else .single)
  | some .single => some .single

def parsedMatrixMAULowerFormat : RRN.FloatPrecision → Option RRN.FloatPrecision
  | .double => some .single
  | .single => some .half
  | .half => none

def parsedMatrixMAUHigherFormat : RRN.FloatPrecision → Option RRN.FloatPrecision
  | .half => some .single
  | .single => some .double
  | .double => none

def parsedMatrixMAUVectorLanesPerPE : ParsedPrecision → Nat
  | .d | .f => 1
  | .g => 2
  | .h => 4
  | .l | .i | .s => 0

def parsedMatrixMAUAccumulatorLanesPerPE : ParsedPrecision → Nat
  | .d => 1
  | .f | .g => 2
  | .h => 4
  | .l | .i | .s => 0

def parsedMatrixMAUDecodeLanes? (format : RRN.FloatPrecision) (count : Nat)
    (bus : IntegerALU.Bus) (negate extend round : Bool) : Option (List Nat) := do
  let rawFormat ← if extend then parsedMatrixMAULowerFormat format
    else if round then parsedMatrixMAUHigherFormat format
    else some format
  let rawWidth := rawFormat.width
  let signMask := 2 ^ (format.width - 1)
  let values := (List.range count).map fun index =>
    let shift := 128 - rawWidth * (index + 1)
    let raw := ((bus.high ++ bus.low).extractLsb' shift rawWidth).toNat
    let converted := RRN.encodeMAUValue format (RRN.decodeMAUValue rawFormat raw)
    if negate then
      (BitVec.ofNat format.width converted ^^^ BitVec.ofNat format.width signMask).toNat
    else converted
  some values

theorem parsedMatrixMAUDecodeLanes_half_extend_four :
    parsedMatrixMAUDecodeLanes? .single 4
      ⟨0x3e003c0000000000, 0⟩ false true false =
      some [0x3f800000, 0x3f000000, 0, 0] := by
  decide

def readParsedMatrixMAUSourcePE (state : State) (coordinate : MABCoordinate)
    (operand : ParsedOperand) (precision : RRN.FloatPrecision) (count : Nat)
    (pe cycle : Fin 4) :
    ProofsLean.StepResult (List Nat) := Id.run do
  let physical := physicalPEId coordinate pe
  let oldContext := state.peContext physical
  let context := { ParsedIntegerContext.ofLinearIndex physical with
    cycle := cycle
    bar0 := oldContext.bar0
    bar1 := oldContext.bar1
    tWord := oldContext.tWord }
  let sourceAttrs? := parsedFloatMAUSourceAttrs? operand context
  let some (input, actualNegate, actualExtend, actualRound) := sourceAttrs? |
    match operand with
    | .mem .. | .forward .. => return .unknown
    | _ => return .failure
  if let .forward kind _ := input then
    if !state.forwardingValid physical (ParsedIntegerInput.forwardUnit kind) cycle then
      return .failure
  match ParsedIntegerInput.readWithForwarding (state.peRegisters physical)
      (state.forwarding physical) cycle input with
  | .failure => return .failure
  | .unknown => return .unknown
  | .ok bus =>
    match parsedMatrixMAUDecodeLanes? precision count bus
        actualNegate actualExtend actualRound with
    | none => return .failure
    | some lanes => return .ok lanes

def readParsedMatrixMAUSourceAtMAB (state : State) (coordinate : MABCoordinate)
    (operand : ParsedOperand) (format : RRN.FloatPrecision) (count : Nat)
    (cycle : Fin 4) : ProofsLean.StepResult (List Nat) := Id.run do
  let mut values := []
  for pe in List.finRange 4 do
    match readParsedMatrixMAUSourcePE state coordinate operand format count pe cycle with
    | .failure => return .failure
    | .unknown => return .unknown
    | .ok lanes => values := values ++ lanes
  return .ok values

def parsedMatrixMAURowActive (half : Option Char) (row : Nat) : Bool :=
  match half with
  | some 'u' => row < 2
  | some 'd' => row ≥ 2
  | _ => true

/-- Compute all logical output rows for one MAB and cycle. Vector and
accumulator lists are the concatenated lane values read from its four PEs.
The matrix elements come from the same physical matrix store used by mread. -/
def parsedMatrixMAUCalculateRows? (store : PEMemory.ParsedMatrixReadStore)
    (coordinate : MABCoordinate) (sideY : Bool) (precision : ParsedPrecision) (kind : CalcKind)
    (half : Option Char) (round : Bool) (vector accumulator : List Nat) : Option (List Nat) := do
  let inputFormat ← parsedMatrixMAUFloatFormat precision
  let outputFormat ← parsedMatrixMAUOutputFormat precision round
  let rows := parsedMatrixMAURowCount precision
  let keptBits := parsedMatrixMAUKeptMantissaBits precision
  (List.range rows).mapM fun row => do
    let left ← if parsedMatrixMAURowActive half row then
        PEMemory.parsedMatrixMAUProductRow? store coordinate.mab sideY precision row
      else some []
    let accumulatorBits ← if kind == .fma then accumulator[row]? else some 0
    some (RRN.encodeMAUValue outputFormat
      (let (dot, grid) := RRN.matrixBlockFloatDot inputFormat keptBits left vector
       let c := RRN.decodeMAUValue
         (match precision with | .h => .single | .d => .double | _ => .single)
         accumulatorBits
       let aligned := match grid with
         | some value => RRN.alignMAUAccumulator c value
         | none => c
       RRN.addMAUValues dot aligned))

theorem parsedMatrixMAUCalculateRows_double_zero_store :
    parsedMatrixMAUCalculateRows?
      (fun _ _ _ _ => 0)
      ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩⟩
      false .d .mul none false [0, 0, 0, 0] [] = some [0, 0, 0, 0] := by
  decide

def executeParsedMatrixMAUCalculationAtMAB (state : State) (coordinate : MABCoordinate)
    (expression : ParsedExpr) (cycle : Fin 4) :
    ProofsLean.StepResult (List Nat × Bool × Bool) := Id.run do
  let (.mau precision true kind half round) := expression.op | return .unknown
  let matrixSide ← match expression.sources with
    | .matrix sideY _ none :: _ => pure sideY
    | _ => return .unknown
  let (vector, accumulator) ← match kind, expression.sources with
    | .mul, [.matrix _ _ none, vector] => pure (vector, none)
    | .add, [.matrix _ _ none, vector] => pure (vector, none)
    | .passa, [.matrix _ _ none, vector] => pure (vector, none)
    | .fma, [.matrix _ _ none, vector, acc] => pure (vector, some acc)
    | _, _ => return .unknown
  let some vectorFormat := parsedMatrixMAUFloatFormat precision | return .failure
  let vectorValues ← match readParsedMatrixMAUSourceAtMAB state coordinate vector
      vectorFormat (parsedMatrixMAUVectorLanesPerPE precision) cycle with
    | .failure => return .failure
    | .unknown => return .unknown
    | .ok values => pure values
  let accumulatorValues ← match accumulator with
    | none => pure []
    | some source =>
      let accumulatorFormat := match precision with
        | .d => RRN.FloatPrecision.double
        | _ => RRN.FloatPrecision.single
      match readParsedMatrixMAUSourceAtMAB state coordinate source accumulatorFormat
          (parsedMatrixMAUAccumulatorLanesPerPE precision) cycle with
      | .failure => return .failure
      | .unknown => return .unknown
      | .ok values => pure values
  let store := state.matrixRegisters coordinate.group coordinate.l2b coordinate.l1b
  let vectorInvalid := !RRN.blockFloatExponentValid vectorFormat vectorValues
  let matrixInvalid := (List.range (parsedMatrixMAURowCount precision)).any fun row =>
    if parsedMatrixMAURowActive half row then
      match PEMemory.parsedMatrixMAUProductRow? store coordinate.mab matrixSide precision row with
      | none => true
      | some elements => !RRN.blockFloatExponentValid vectorFormat elements
    else false
  match parsedMatrixMAUCalculateRows? store coordinate matrixSide precision kind half round
      vectorValues accumulatorValues with
  | none => return .failure
  | some rows => return .ok (rows, vectorInvalid || matrixInvalid, false)

def parsedMatrixMAURowsPerPE : ParsedPrecision → Nat
  | .d => 1
  | .f | .g => 2
  | .h => 4
  | .l | .i | .s => 0

def parsedMatrixMAUPackPEBus? (precision : ParsedPrecision) (round : Bool)
    (values : List Nat) : Option IntegerALU.Bus := do
  match precision, round, values with
  | .d, false, [a] => some ⟨BitVec.ofNat 64 a, 0⟩
  | .d, true, [a] => some ⟨BitVec.ofNat 32 a ++ BitVec.ofNat 32 0, 0⟩
  | .f, _, [a, b] | .g, _, [a, b] =>
      some ⟨BitVec.ofNat 32 a ++ BitVec.ofNat 32 b, 0⟩
  | .h, true, [a, b, c, d] =>
      some ⟨BitVec.ofNat 16 a ++ BitVec.ofNat 16 b ++
        BitVec.ofNat 16 c ++ BitVec.ofNat 16 d, 0⟩
  | .h, false, [a, b, c, d] =>
      some ⟨BitVec.ofNat 32 a ++ BitVec.ofNat 32 b,
        BitVec.ofNat 32 c ++ BitVec.ofNat 32 d⟩
  | _, _, _ => none

def parsedMatrixMAUPositive (precision : RRN.FloatPrecision) (bits : Nat) : Bool :=
  !RRN.floatIsNegative precision bits

def parsedMatrixMAUFlags? (precision : ParsedPrecision) (round : Bool)
    (values : List Nat) : Option (BitVec 4) := do
  let outputFormat ← parsedMatrixMAUOutputFormat precision round
  match values with
  | [a] =>
      let positive := parsedMatrixMAUPositive outputFormat a
      some (BitVec.ofNat 4 (if outputFormat == .double then
        if positive then 0xf else 0 else if positive then 0xc else 0))
  | [a, b] =>
      let first := if parsedMatrixMAUPositive outputFormat a then 0xc else 0
      let second := if parsedMatrixMAUPositive outputFormat b then 0x3 else 0
      some (BitVec.ofNat 4 (first + second))
  | [a, b, c, d] =>
      let bits := [a, b, c, d].reverse.zipIdx.foldl (fun flags (value, index) =>
        flags + (if parsedMatrixMAUPositive outputFormat value then 2 ^ index else 0)) 0
      some (BitVec.ofNat 4 bits)
  | _ => none

def parsedMatrixMAUPEOutput? (precision : ParsedPrecision) (round : Bool)
    (values : List Nat) (pe : Fin 4) : Option (IntegerALU.Bus × BitVec 4) := do
  let perPE := parsedMatrixMAURowsPerPE precision
  let rowStart := pe.val * perPE
  let peValues := (values.drop rowStart).take perPE
  let bus ← parsedMatrixMAUPackPEBus? precision round peValues
  let flags ← parsedMatrixMAUFlags? precision round peValues
  some (bus, flags)

def executeParsedMatrixMAUAtMAB (state : State) (coordinate : MABCoordinate)
    (expression : ParsedExpr) (cycle : Fin 4) :
    ProofsLean.StepResult ((Fin 4 → IntegerALU.Bus) × (Fin 4 → BitVec 4) × Bool) := Id.run do
  match executeParsedMatrixMAUCalculationAtMAB state coordinate expression cycle with
  | .failure => return .failure
  | .unknown => return .unknown
  | .ok (rows, poison, flagsUnavailable) =>
    let (.mau precision true _ _ round) := expression.op | return .unknown
    let mut buses : Fin 4 → IntegerALU.Bus := fun _ => ⟨0, 0⟩
    let mut flags : Fin 4 → BitVec 4 := fun _ => 0
    for pe in List.finRange 4 do
      match parsedMatrixMAUPEOutput? precision round rows pe with
      | none => return .failure
      | some (bus, flag) =>
        buses := fun index => if index == pe then bus else buses index
        flags := fun index => if index == pe then
          (if flagsUnavailable then 0 else flag) else flags index
    return .ok (buses, flags, poison)


theorem parsedMatrixMAURowActive_upper_lower_halves :
    parsedMatrixMAURowActive (some 'u') 1 = true ∧
    parsedMatrixMAURowActive (some 'u') 2 = false ∧
    parsedMatrixMAURowActive (some 'd') 1 = false ∧
    parsedMatrixMAURowActive (some 'd') 2 = true := by
  decide

theorem parsedMatrixMAUPEOutput_double_round_layout :
    parsedMatrixMAUPEOutput? .d true [0x3fc00000] 0 =
      some (⟨0x3fc0000000000000, 0⟩, 0xc) := by
  decide

theorem parsedMatrixMAUPEOutput_half_unrounded_layout :
    parsedMatrixMAUPEOutput? .h false
      [0x3f800000, 0xbf800000, 0x40000000, 0x40400000,
        0x40800000, 0x40a00000, 0x40c00000, 0x40e00000,
        0x41000000, 0x41100000, 0x41200000, 0x41300000,
        0x41400000, 0x41500000, 0x41600000, 0x41700000] 0 =
      some (⟨0x3f800000bf800000, 0x4000000040400000⟩, 0xb) := by
  decide

structure ParsedL1MwriteAccess where
  source : ParsedOperand
  selectedMab : Fin 16
  mabGroup : Fin 4
  fourMabs : Bool
  twoLongWords : Bool
  address : Option (Fin L1Transfer.l1bmLongWords)

def lowerParsedL1Mwrite? (expression : ParsedExpr) : Option ParsedL1MwriteAccess := do
  match expression.op, expression.sources, expression.destinations with
  | .l1bm (.mwrite mab), [source], [.l1bm width address] => do
      if hmab : mab.val < 16 then
        let selectedMab : Fin 16 := ⟨mab.val, hmab⟩
        let mabGroup : Fin 4 := ⟨mab.val / 4, by omega⟩
        let address := address.map fun address =>
          ⟨address.val % L1Transfer.l1bmLongWords,
            Nat.mod_lt _ (by decide)⟩
        some ⟨source, selectedMab, mabGroup, false, width.val == 4, address⟩
      else none
  | .l1bm (.m4write mab), [source], [.l1bm width address] => do
      if hmab : mab.val < 4 then
        let selectedMab : Fin 16 := ⟨mab.val, by omega⟩
        let mabGroup : Fin 4 := ⟨mab.val, hmab⟩
        let address := address.map fun address =>
          ⟨address.val % L1Transfer.l1bmLongWords,
            Nat.mod_lt _ (by decide)⟩
        some ⟨source, selectedMab, mabGroup, true, width.val == 4, address⟩
      else none
  | _, _, _ => none

def rawL1MwriteSource? (source : ParsedOperand) (context : ParsedIntegerContext) :
    Option ParsedIntegerInput := do
  let rawSource ← match source with
    | .mem access _ _ _ _ => some (.mem access false false false none)
    | .forward kind _ _ _ => some (.forward kind false false false)
    | _ => none
  ParsedOperand.toParsedIntegerInput? rawSource .long context.group context.l2b
    context.l1b context.mab context.pe context.cycle context.bar0 context.bar1 context.tWord

def rawL1MwriteSourceResult (source : ParsedOperand) (context : ParsedIntegerContext) :
    ProofsLean.StepResult ParsedIntegerInput :=
  match rawL1MwriteSource? source context with
  | some input => .ok input
  | none => match source with
      | .mem .. | .forward .. => .unknown
      | _ => .failure

theorem rawL1Mwrite_fixed_source_is_failure
    (fixed : ParsedFixed) (context : ParsedIntegerContext) :
    rawL1MwriteSourceResult (.fixed fixed) context = .failure := by
  rfl

def readRawL1MwriteBus (state : State) (source : ParsedOperand)
    (pe : PEId) (cycle : Fin 4) : ProofsLean.StepResult IntegerALU.Bus :=
  let oldContext := state.peContext pe
  let coordinates := ParsedIntegerContext.ofLinearIndex pe
  let context := { coordinates with
    cycle := cycle
    bar0 := oldContext.bar0
    bar1 := oldContext.bar1
    tWord := oldContext.tWord }
  match rawL1MwriteSourceResult source context with
  | .failure => .failure
  | .unknown => .unknown
  | .ok input =>
      match input with
      | .forward kind _ =>
          if !state.forwardingValid pe (ParsedIntegerInput.forwardUnit kind) cycle then
            .failure
          else ParsedIntegerInput.readWithForwarding
            (state.peRegisters pe) (stateForwardingSlots state pe) cycle input
      | _ => ParsedIntegerInput.readWithForwarding
          (state.peRegisters pe) (stateForwardingSlots state pe) cycle input

def readL1MwriteBusesAtBank (state : State) (access : ParsedL1MwriteAccess)
    (bank : Fin 64) (mab : Fin 16) (cycle : Fin 4) :
    ProofsLean.StepResult (Fin 4 → IntegerALU.Bus) :=
  let coordinate : MABCoordinate :=
    ⟨⟨bank.val / 16, by have h := bank.isLt; omega⟩,
      ⟨bank.val / 8 % 2, by have h := bank.isLt; omega⟩,
      ⟨bank.val % 8, by have h := bank.isLt; omega⟩, mab⟩
  let rec readPEs : List (Fin 4) → (Fin 4 → IntegerALU.Bus) →
      ProofsLean.StepResult (Fin 4 → IntegerALU.Bus)
    | [], buses => .ok buses
    | pe :: rest, buses =>
        match readRawL1MwriteBus state access.source
            (physicalPEId coordinate pe) cycle with
        | .failure => .failure
        | .unknown => .unknown
        | .ok bus => readPEs rest (fun index => if index = pe then bus else buses index)
  readPEs (List.finRange 4) (fun _ => ⟨0, 0⟩)

def readL1M4writeBusesAtBank (state : State) (access : ParsedL1MwriteAccess)
    (bank : Fin 64) (cycle : Fin 4) :
    ProofsLean.StepResult (Fin 4 → Fin 4 → IntegerALU.Bus) :=
  let rec readGroups : List (Fin 4) → (Fin 4 → Fin 4 → IntegerALU.Bus) →
      ProofsLean.StepResult (Fin 4 → Fin 4 → IntegerALU.Bus)
    | [], buses => .ok buses
    | group :: rest, buses =>
        let mab : Fin 16 := ⟨group.val * 4 + access.mabGroup.val, by
          have hg := group.isLt
          have hm := access.mabGroup.isLt
          omega⟩
        match readL1MwriteBusesAtBank state access bank mab cycle with
        | .failure => .failure
        | .unknown => .unknown
        | .ok groupBuses =>
            readGroups rest (fun nextGroup pe =>
              if nextGroup = group then groupBuses pe else buses nextGroup pe)
  readGroups (List.finRange 4) (fun _ _ => ⟨0, 0⟩)

def l1MwriteTurnaroundWrites (twoLongWords : Bool)
    (buses : Fin 4 → IntegerALU.Bus) : List L1Transfer.L1TurnWrite :=
  (List.finRange 4).flatMap fun pe =>
    [(⟨pe.val, by have h := pe.isLt; omega⟩, (buses pe).high)] ++
      if twoLongWords then
        [(⟨pe.val + 4, by have h := pe.isLt; omega⟩, (buses pe).low)]
      else []

def l1M4writeTurnaroundWrites (twoLongWords : Bool)
    (buses : Fin 4 → Fin 4 → IntegerALU.Bus) : List L1Transfer.L1TurnWrite :=
  (List.finRange 4).flatMap fun group =>
    (List.finRange 4).flatMap fun pe =>
      let offset := group.val * (if twoLongWords then 8 else 4) + pe.val
      [(⟨offset, by
        have hg := group.isLt
        have hp := pe.isLt
        cases twoLongWords <;> simp [offset] <;> omega⟩,
        (buses group pe).high)] ++
        if twoLongWords then
          [(⟨offset + 4, by
            have hg := group.isLt
            have hp := pe.isLt
            cases twoLongWords <;> simp [offset] <;> omega⟩,
            (buses group pe).low)]
        else []

def executeL1MwriteCyclesAtBank (state : State) (access : ParsedL1MwriteAccess)
    (bank : Fin 64) (updateTurnaround : Bool) : ProofsLean.StepResult
      (L1Transfer.L1Bank × L1Transfer.L1Turnaround) :=
  let rec run : List (Fin 4) → L1Transfer.L1Bank → L1Transfer.L1Turnaround →
      ProofsLean.StepResult (L1Transfer.L1Bank × L1Transfer.L1Turnaround)
    | [], memory, turnaround => .ok (memory, turnaround)
    | cycle :: rest, memory, turnaround =>
        let writeCycle (buses : Fin 4 → IntegerALU.Bus) :=
          let writes := match access.address with
            | none => []
            | some base => L1Transfer.mwriteWrites base access.twoLongWords cycle buses
          let turnWrites := if updateTurnaround then
            l1MwriteTurnaroundWrites access.twoLongWords buses else []
          L1Transfer.commitL1Transfer memory turnaround cycle writes turnWrites
        let writeM4Cycle (buses : Fin 4 → Fin 4 → IntegerALU.Bus) :=
          let writes := match access.address with
            | none => []
            | some base => L1Transfer.m4writeWrites base access.twoLongWords
                cycle access.mabGroup (fun group _ pe => buses group pe)
          let turnWrites := if updateTurnaround then
            l1M4writeTurnaroundWrites access.twoLongWords buses else []
          L1Transfer.commitL1Transfer memory turnaround cycle writes turnWrites
        if access.fourMabs then
          match readL1M4writeBusesAtBank state access bank cycle with
          | .failure => .failure
          | .unknown => .unknown
          | .ok buses =>
              let next := writeM4Cycle buses
              run rest next.1 next.2
        else
          match readL1MwriteBusesAtBank state access bank access.selectedMab cycle with
          | .failure => .failure
          | .unknown => .unknown
          | .ok buses =>
              let next := writeCycle buses
              run rest next.1 next.2
  run [0, 1, 2, 3] (state.l1bm bank) (state.l1bmTurnaround bank)

def executeParsedL1MwriteAtAllBanks (readState currentState : State)
    (expression : ParsedExpr) (updateTurnaround : Bool) : ProofsLean.StepResult State :=
  match lowerParsedL1Mwrite? expression with
  | none => .unknown
  | some access =>
      let rec run : List (Fin 64) → State → ProofsLean.StepResult State
        | [], state => .ok state
        | bank :: rest, state =>
            match executeL1MwriteCyclesAtBank readState access bank updateTurnaround with
            | .failure => .failure
            | .unknown => .unknown
            | .ok (memory, turnaround) =>
                let next := { state with
                  l1bm := fun other => if other = bank then memory else state.l1bm other
                  l1bmTurnaround := fun other =>
                    if other = bank then turnaround else state.l1bmTurnaround other }
                run rest next
      run (List.finRange 64) currentState

def executeParsedL1MwriteProducers (readState currentState : State)
    (expressions : List ParsedExpr) (updateTurnaround : Bool) : ProofsLean.StepResult State :=
  match expressions.filter parsedExprIsL1MwriteProducer with
  | [] => .ok currentState
  | [expression] =>
      executeParsedL1MwriteAtAllBanks readState currentState expression updateTurnaround
  | _ => .unknown

structure ParsedL1GatherAccess where
  source : ParsedOperand
  mabDiff : Int
  address : Option (Fin L1Transfer.l1bmLongWords)

def lowerParsedL1Gather? (expression : ParsedExpr) : Option ParsedL1GatherAccess := do
  match expression.op, expression.sources, expression.destinations with
  | .l1bm (.gather mabDiff), [source], [.l1bm _ address] =>
      let address := address.map fun address =>
        ⟨address.val % L1Transfer.l1bmLongWords,
          Nat.mod_lt _ (by decide)⟩
      some ⟨source, mabDiff, address⟩
  | _, _, _ => none

def readL1GatherBusesAtBank (state : State) (access : ParsedL1GatherAccess)
    (bank : Fin 64) (cycle : Fin 4) :
    ProofsLean.StepResult (Fin 16 → Fin 4 → IntegerALU.Bus) :=
  let rec readMABs : List (Fin 16) → (Fin 16 → Fin 4 → IntegerALU.Bus) →
      ProofsLean.StepResult (Fin 16 → Fin 4 → IntegerALU.Bus)
    | [], buses => .ok buses
    | mab :: mabs, buses =>
      let rec readPEs : List (Fin 4) → (Fin 4 → IntegerALU.Bus) →
          ProofsLean.StepResult (Fin 4 → IntegerALU.Bus)
        | [], peBuses => .ok peBuses
        | pe :: pes, peBuses =>
            let linear := bank.val * 64 + mab.val * 4 + pe.val
            let linearPE : PEId := ⟨linear, by
              have hb := bank.isLt
              have hm := mab.isLt
              have hp := pe.isLt
              omega⟩
            match readRawL1MwriteBus state access.source linearPE cycle with
            | .failure => .failure
            | .unknown => .unknown
            | .ok bus => readPEs pes (fun index => if index = pe then bus else peBuses index)
      match readPEs (List.finRange 4) (fun _ => ⟨0, 0⟩) with
      | .failure => .failure
      | .unknown => .unknown
      | .ok peBuses => readMABs mabs
          (fun nextMab pe => if nextMab = mab then peBuses pe else buses nextMab pe)
  readMABs (List.finRange 16) (fun _ _ => ⟨0, 0⟩)

def executeL1GatherCyclesAtBank (state : State) (access : ParsedL1GatherAccess)
    (bank : Fin 64) (updateTurnaround : Bool) :
    ProofsLean.StepResult (L1Transfer.L1Bank × L1Transfer.L1Turnaround) :=
  let rec run : List (Fin 4) → L1Transfer.L1Bank → L1Transfer.L1Turnaround →
      ProofsLean.StepResult (L1Transfer.L1Bank × L1Transfer.L1Turnaround)
    | [], memory, turnaround => .ok (memory, turnaround)
    | cycle :: rest, memory, turnaround =>
        match readL1GatherBusesAtBank state access bank cycle with
        | .failure => .failure
        | .unknown => .unknown
        | .ok buses =>
            let writes := match access.address with
              | none => []
              | some base => L1Transfer.gatherL1Writes base access.mabDiff cycle buses
            let turnWrites := if updateTurnaround then
              L1Transfer.gatherTurnaroundWrites access.mabDiff buses else []
            let next := L1Transfer.commitL1Transfer memory turnaround cycle writes turnWrites
            run rest next.1 next.2
  run [0, 1, 2, 3] (state.l1bm bank) (state.l1bmTurnaround bank)

def executeParsedL1GatherAtAllBanks (readState currentState : State)
    (expression : ParsedExpr) (updateTurnaround : Bool) : ProofsLean.StepResult State :=
  match lowerParsedL1Gather? expression with
  | none => .unknown
  | some access =>
      let rec run : List (Fin 64) → State → ProofsLean.StepResult State
        | [], state => .ok state
        | bank :: rest, state =>
            match executeL1GatherCyclesAtBank readState access bank updateTurnaround with
            | .failure => .failure
            | .unknown => .unknown
            | .ok (memory, turnaround) =>
                let next := { state with
                  l1bm := fun other => if other = bank then memory else state.l1bm other
                  l1bmTurnaround := fun other =>
                    if other = bank then turnaround else state.l1bmTurnaround other }
                run rest next
      run (List.finRange 64) currentState

def executeParsedL1GatherProducers (readState currentState : State)
    (expressions : List ParsedExpr) (updateTurnaround : Bool) : ProofsLean.StepResult State :=
  match expressions.filter parsedExprIsL1GatherProducer with
  | [] => .ok currentState
  | [expression] => executeParsedL1GatherAtAllBanks readState currentState expression updateTurnaround
  | _ => .unknown

structure ParsedL1ReduceAccess where
  source : ParsedOperand
  rrn : ParsedRrn
  round : Bool
  fourGroups : Bool
  twoLongWords : Bool
  extended : Bool
  sourceTwoWords : Bool
  address : Option (Fin L1Transfer.l1bmLongWords)

def parsedL1ReduceSourceAttributes (source : ParsedOperand) : Bool × Bool :=
  match source with
  | .mem access _ extended _ _ =>
      (extended, access.region.width == 4)
  | .forward _ _ extended _ => (extended, true)
  | _ => (false, false)

def lowerParsedL1Reduce? (expression : ParsedExpr) : Option ParsedL1ReduceAccess := do
  match expression.op, expression.sources, expression.destinations with
  | .l1bm (.reduce rrn round), [source], [.l1bm width address] =>
      if width.val != 1 && width.val != 2 && width.val != 4 then none else
      let (extended, sourceTwoWords) := parsedL1ReduceSourceAttributes source
      let address := address.map fun address =>
        ⟨address.val % L1Transfer.l1bmLongWords,
          Nat.mod_lt _ (by decide)⟩
      some ⟨source, rrn, round, false, width.val == 4, extended,
        sourceTwoWords, address⟩
  | .l1bm (.reduce4 rrn round), [source], [.l1bm width address] =>
      if width.val != 1 && width.val != 2 && width.val != 4 then none else
      let (extended, sourceTwoWords) := parsedL1ReduceSourceAttributes source
      let address := address.map fun address =>
        ⟨address.val % L1Transfer.l1bmLongWords,
          Nat.mod_lt _ (by decide)⟩
      some ⟨source, rrn, round, true, width.val == 4, extended,
        sourceTwoWords, address⟩
  | _, _, _ => none

def extendL1ReduceBus (bus : IntegerALU.Bus) : IntegerALU.Bus :=
  let lane (index : Fin 4) := BitVec.ofNat 32 <|
    RRN.extendFloatBits .half .single
      ((bus.high.extractLsb' (48 - index.val * 16) 16).toNat)
  { high := BitVec.ofNat 64 (lane 0).toNat * 2 ^ 32 + (lane 1).toNat
    low := BitVec.ofNat 64 (lane 2).toNat * 2 ^ 32 + (lane 3).toNat }

def parsedL1IntegerRRN? (rrn : ParsedRrn) : Option (RRN.IntegerPrecision × RRN.IntegerOp) := do
  let precision ← match rrn.precision.val with
    | 'd' | 'l' => some .long
    | 'f' | 'i' => some .word
    | 'h' | 's' => some .half
    | _ => none
  let operation ← match rrn.op with
    | .max => some .maximum
    | .min => some .minimum
    | .iadd => some .add
    | .band => some .bitAnd
    | .bor => some .bitOr
    | .and => some .allNonzero
    | .or => some .anyNonzero
    | .fadd => none
  some (precision, operation)

def parsedL1NativeFloatPrecision? (rrn : ParsedRrn) : Option RRN.NativeFloatPrecision :=
  if rrn.op != .fadd then none else
    match rrn.precision.val with
    | 'd' => some .double
    | 'f' => some .single
    | _ => none

def roundedL1IntegerBus (first second : BitVec 64) : BitVec 64 :=
  let halfLane (index : Nat) :=
    let word := if index < 2 then first else second
    let offset := if index % 2 == 0 then 32 else 0
    (word.extractLsb' offset 16).toNat
  BitVec.ofNat 64 ((halfLane 0) * 2 ^ 48 + (halfLane 1) * 2 ^ 32 +
    (halfLane 2) * 2 ^ 16 + halfLane 3)

def parsedL1ReduceWord (fourGroups : Bool) (rrn : ParsedRrn)
    (values : List (BitVec 64)) : Option (BitVec 64) := do
  if rrn.op == .fadd then
    match rrn.precision.val with
    | 'h' => some (RRN.reduceHalfAliasLongWord fourGroups values)
    | 'd' => some (if fourGroups then RRN.reduceLongFloatAdd .double values
        else RRN.reduceLongFloatAdd16 .double values)
    | 'f' => some (if fourGroups then RRN.reduceLongFloatAdd .single values
        else RRN.reduceLongFloatAdd16 .single values)
    | _ => none
  else do
    let (precision, operation) ← parsedL1IntegerRRN? rrn
    some (RRN.reduceLongInteger operation precision values)

def parsedL1ReduceWritesAtCycle (access : ParsedL1ReduceAccess)
    (base : Fin L1Transfer.l1bmLongWords) (cycle : Fin 4)
    (buses : Fin 16 → Fin 4 → IntegerALU.Bus) : Option
      (List L1Transfer.L1Write × List L1Transfer.L1TurnWrite) := do
  let halfAlias := access.rrn.precision.val == 'h' && access.rrn.op == .fadd
  let rounded := access.round || halfAlias
  let inputBus := fun mab pe =>
    let raw := buses mab pe
    if access.extended && !halfAlias then extendL1ReduceBus raw else raw
  let inputs : Fin 4 → Fin 4 → Fin 2 → Fin 16 → BitVec 64 := fun _ pe part mab =>
    let bus := inputBus mab pe
    if part.val == 0 then bus.high else bus.low
  if halfAlias then
    some (L1Transfer.reduceHalfAliasL1Writes base access.fourGroups cycle inputs,
      L1Transfer.reduceHalfAliasTurnaroundWrites access.fourGroups inputs)
  else if let some precision := parsedL1NativeFloatPrecision? access.rrn then
    if access.round then
      let sourceTwo := access.twoLongWords || access.sourceTwoWords || access.extended
      some (L1Transfer.reduceRoundedFloatL1Writes base access.fourGroups
          access.twoLongWords sourceTwo precision cycle inputs,
        L1Transfer.reduceRoundedFloatTurnaroundWrites access.fourGroups
          access.twoLongWords sourceTwo precision inputs)
    else
      let results := fun group pe part =>
        let selected := ((List.finRange 16).filter fun mab =>
          !access.fourGroups || mab.val / 4 == group.val).map fun mab => inputs group pe part mab
        L1Transfer.reduceFloatL1Result access.fourGroups precision selected
      some (L1Transfer.reduceFloatL1Writes base access.fourGroups
          access.twoLongWords precision cycle inputs,
        L1Transfer.reduceL1TurnaroundWrites access.fourGroups false
          access.twoLongWords results)
  else do
    let (precision, operation) ← parsedL1IntegerRRN? access.rrn
    let results := fun group pe part =>
      let selected := ((List.finRange 16).filter fun mab =>
        !access.fourGroups || mab.val / 4 == group.val).map fun mab => inputs group pe part mab
      RRN.reduceLongInteger operation precision selected
    if rounded then
      let roundedResults := fun group pe _part =>
        let second := if access.twoLongWords ||
            (rounded && access.sourceTwoWords) || access.extended then
          results group pe 1 else 0
        roundedL1IntegerBus (results group pe 0) second
      some (L1Transfer.reduceL1Writes base access.fourGroups true
          access.twoLongWords cycle roundedResults,
        L1Transfer.reduceL1TurnaroundWrites access.fourGroups true
          access.twoLongWords roundedResults)
    else
      some (L1Transfer.reduceIntegerL1Writes base access.fourGroups
          access.twoLongWords precision operation cycle inputs,
        L1Transfer.reduceL1TurnaroundWrites access.fourGroups false
          access.twoLongWords results)

def executeL1ReduceCyclesAtBank (state : State) (access : ParsedL1ReduceAccess)
    (bank : Fin 64) (updateTurnaround : Bool) :
    ProofsLean.StepResult (L1Transfer.L1Bank × L1Transfer.L1Turnaround) :=
  let rec run : List (Fin 4) → L1Transfer.L1Bank → L1Transfer.L1Turnaround →
      ProofsLean.StepResult (L1Transfer.L1Bank × L1Transfer.L1Turnaround)
    | [], memory, turnaround => .ok (memory, turnaround)
    | cycle :: rest, memory, turnaround =>
      match readL1GatherBusesAtBank state ⟨access.source, 0, access.address⟩ bank cycle with
      | .failure => .failure
      | .unknown => .unknown
      | .ok buses =>
        match parsedL1ReduceWritesAtCycle access
            (access.address.getD ⟨0, by decide⟩) cycle buses with
        | none => .unknown
        | some (writes, turnWrites) =>
            let writes := match access.address with | none => [] | some _ => writes
            let turnWrites := if updateTurnaround then turnWrites else []
            let next := L1Transfer.commitL1Transfer memory turnaround cycle writes turnWrites
            run rest next.1 next.2
  run [0, 1, 2, 3] (state.l1bm bank) (state.l1bmTurnaround bank)

def executeParsedL1ReduceAtAllBanks (readState currentState : State)
    (expression : ParsedExpr) (updateTurnaround : Bool) : ProofsLean.StepResult State :=
  match lowerParsedL1Reduce? expression with
  | none => .unknown
  | some access =>
      let rec run : List (Fin 64) → State → ProofsLean.StepResult State
        | [], state => .ok state
        | bank :: rest, state =>
            match executeL1ReduceCyclesAtBank readState access bank updateTurnaround with
            | .failure => .failure
            | .unknown => .unknown
            | .ok (memory, turnaround) =>
                let next := { state with
                  l1bm := fun other => if other = bank then memory else state.l1bm other
                  l1bmTurnaround := fun other =>
                    if other = bank then turnaround else state.l1bmTurnaround other }
                run rest next
      run (List.finRange 64) currentState

def parsedExprIsL1ReduceProducer (expression : ParsedExpr) : Bool :=
  match expression.op with
  | .l1bm (.reduce ..) | .l1bm (.reduce4 ..) => true
  | _ => false

def executeParsedL1ReduceProducers (readState currentState : State)
    (expressions : List ParsedExpr) (updateTurnaround : Bool) : ProofsLean.StepResult State :=
  match expressions.filter parsedExprIsL1ReduceProducer with
  | [] => .ok currentState
  | [expression] => executeParsedL1ReduceAtAllBanks readState currentState expression updateTurnaround
  | _ => .unknown

def parsedExprIsL2BMProducer (expression : ParsedExpr) : Bool :=
  match expression.op with
  | .l2bm .. => true
  | _ => false

structure ParsedL2Access where
  op : ParsedL2Op
  sourceAddress : Option Nat
  destinationAddress : Option Nat

def parsedL1BMAddress? : ParsedOperand → Option Nat
  | .l1bm _ (some address) => some address.val
  | _ => none

def parsedL2BMAddress? : ParsedOperand → Option Nat
  | .l2bm address _ => some address.val
  | _ => none

def lowerParsedL2? (expression : ParsedExpr) : Option ParsedL2Access := do
  match expression.op with
  | .l2bm op =>
      match expression.sources, expression.destinations with
      | [source], [destination] =>
          let sourceAddress := match op with
            | .bcast _ | .bcast2 _ | .distrib _ | .dars => parsedL2BMAddress? source
            | .fromL1b _ | .reduce _ _ | .reduce2 _ | .gather | .imcast _ | .darw =>
                parsedL1BMAddress? source
          let destinationAddress := match op with
            | .bcast _ | .bcast2 _ | .distrib _ | .imcast _ => parsedL1BMAddress? destination
            | .fromL1b _ | .reduce _ _ | .reduce2 _ | .gather => parsedL2BMAddress? destination
            | .dars | .darw => none
          some ⟨op, sourceAddress, destinationAddress⟩
      | _, _ => none
  | _ => none

def parsedL2SetContains (set : ParsedL1bSet) (l1b : Fin 8) : Bool :=
  set.mask.val / 2 ^ l1b.val % 2 == 1

def l2PhysicalCell (l2Index : Fin 8) (address : Nat) : MVSemantics.Cell :=
  ⟨.l2bm, ⟨l2Index.val / 2, by omega⟩, ⟨l2Index.val % 2, by omega⟩,
    address % (2 ^ 15)⟩

def l2PhysicalL1Bank (l2Index : Fin 8) (l1b : Fin 8) : Fin 64 :=
  ⟨l2Index.val * 8 + l1b.val, by omega⟩

def parsedL2RRNUnit (rrn : ParsedRrn) : BitVec 64 :=
  let bits := if rrn.precision.val == 'd' || rrn.precision.val == 'l' then 64
    else if rrn.precision.val == 'f' || rrn.precision.val == 'i' then 32 else 16
  let lane := match rrn.op with
    | .fadd | .iadd | .bor | .or => 0
    | .band => 2 ^ bits - 1
    | .and => 1
    | .max => 2 ^ bits - 1
    | .min => 2 ^ (bits - 1) - 1
  BitVec.ofNat 64 ((List.range (64 / bits)).foldl (fun acc index =>
    acc + lane * 2 ^ (64 - bits * (index + 1))) 0)

def parsedL2ReduceWord? (rrn : ParsedRrn) (values : List (BitVec 64)) :
    Option (BitVec 64) := do
  if rrn.op == .fadd then
    match rrn.precision.val with
    | 'd' => some (RRN.reduceLongFloatAddFormat .double values)
    | 'f' => some (RRN.reduceLongFloatAddFormat .single values)
    | 'h' => some (RRN.reduceLongFloatAddFormat .half values)
    | _ => none
  else do
    let (precision, operation) ← parsedL1IntegerRRN? rrn
    some (RRN.reduceLongInteger operation precision values)

def parsedL2Writes? (readState : State) (access : ParsedL2Access) :
    Option (List (Fin 64 × Fin L1Transfer.l1bmLongWords × BitVec 64) ×
      List (MVSemantics.Cell × BitVec 64)) := do
  let sourceAddress ← access.sourceAddress
  let destinationAddress ← access.destinationAddress
  let l1read (l2Index : Fin 8) (l1b : Fin 8) (offset : Nat) : BitVec 64 :=
    readState.l1bm (l2PhysicalL1Bank l2Index l1b)
      ⟨offset % L1Transfer.l1bmLongWords, Nat.mod_lt _ (by decide)⟩
  let l2read (l2Index : Fin 8) (offset : Nat) : BitVec 64 :=
    readState.blockMemory (l2PhysicalCell l2Index offset)
  let l1write (l2Index : Fin 8) (l1b : Fin 8) (offset : Nat) (value : BitVec 64) :=
    (l2PhysicalL1Bank l2Index l1b,
      ⟨offset % L1Transfer.l1bmLongWords, Nat.mod_lt _ (by decide)⟩, value)
  let l2write (l2Index : Fin 8) (offset : Nat) (value : BitVec 64) :=
    (l2PhysicalCell l2Index offset, value)
  let l2Indices := List.finRange 8
  let cycles := List.range 4
  let words16 := List.range 16
  let l1Writes := match access.op with
    | .bcast set => l2Indices.flatMap fun l2Index => cycles.flatMap fun cycle =>
        (List.finRange 8).filter (parsedL2SetContains set) |>.flatMap fun l1b =>
          words16.map fun word => l1write l2Index l1b
            (destinationAddress + cycle * 16 + word)
            (l2read l2Index (sourceAddress + cycle * 16 + word))
    | .bcast2 set => l2Indices.flatMap fun l2Index => cycles.flatMap fun cycle =>
        (List.finRange 8).filter (parsedL2SetContains set) |>.flatMap fun l1b =>
          words16.map fun word => l1write l2Index l1b
            (destinationAddress + cycle * 16 + word)
            (l2read l2Index (sourceAddress + cycle * 64 + 16 * (l1b.val / 2) + word))
    | .distrib set => l2Indices.flatMap fun l2Index => cycles.flatMap fun cycle =>
        (List.finRange 8).filter (parsedL2SetContains set) |>.flatMap fun l1b =>
          (List.range 8).map fun word => l1write l2Index l1b
            (destinationAddress + cycle * 8 + word)
            (l2read l2Index (sourceAddress + cycle * 64 + 8 * l1b.val + word))
    | .imcast set => l2Indices.flatMap fun l2Index => cycles.flatMap fun cycle =>
        (List.finRange 8).filter (parsedL2SetContains set) |>.flatMap fun sourceL1b =>
          (List.finRange 8).filter (fun destinationL1b =>
            destinationL1b != sourceL1b &&
              Nat.land destinationL1b.val set.immode.val ==
                Nat.land sourceL1b.val set.immode.val) |>.flatMap fun destinationL1b =>
            words16.map fun word => l1write l2Index destinationL1b
              (destinationAddress + cycle * 16 + word)
              (l1read l2Index sourceL1b (sourceAddress + cycle * 16 + word))
    | _ => []
  let l2Writes := match access.op with
    | .fromL1b selected => do
        if h : selected.val < 8 then
          let l1b : Fin 8 := ⟨selected.val, h⟩
          l2Indices.flatMap fun l2Index => cycles.flatMap fun cycle =>
            words16.map fun word => l2write l2Index (destinationAddress + cycle * 16 + word)
              (l1read l2Index l1b (sourceAddress + cycle * 16 + word))
        else []
    | .gather => l2Indices.flatMap fun l2Index => cycles.flatMap fun cycle =>
        (List.finRange 8).flatMap fun l1b => (List.range 8).map fun word =>
          l2write l2Index (destinationAddress + cycle * 64 + 8 * l1b.val + word)
            (l1read l2Index l1b (sourceAddress + cycle * 8 + word))
    | .reduce rrn set => l2Indices.flatMap fun l2Index => cycles.flatMap fun cycle =>
        words16.map fun word =>
          let values := (List.finRange 8).map fun l1b =>
            if parsedL2SetContains set l1b then
              l1read l2Index (l1b) (sourceAddress + cycle * 16 + word)
            else parsedL2RRNUnit rrn
          l2write l2Index (destinationAddress + cycle * 16 + word)
            ((parsedL2ReduceWord? rrn values).getD 0)
    | .reduce2 rrn => l2Indices.flatMap fun l2Index => cycles.flatMap fun cycle =>
        (List.finRange 4).flatMap fun group => words16.map fun word =>
          let values := (List.finRange 2).map fun index =>
            let l1b : Fin 8 := ⟨group.val * 2 + index.val, by omega⟩
            l1read l2Index l1b (sourceAddress + cycle * 16 + word)
          l2write l2Index (destinationAddress + cycle * 64 + 16 * group.val + word)
            ((parsedL2ReduceWord? rrn values).getD 0)
    | _ => []
  match access.op with
  | .dars | .darw => none
  | .fromL1b selected => if selected.val < 8 then some (l1Writes, l2Writes) else none
  | .bcast _ | .bcast2 _ | .distrib _ | .imcast _ | .gather | .reduce .. | .reduce2 .. =>
      some (l1Writes, l2Writes)

def executeParsedL2BlockExpression (readState currentState : State)
    (expression : ParsedExpr) : ProofsLean.StepResult State :=
  match expression.op with
  | .l2bm .dars | .l2bm .darw => .failure
  | .l2bm _ =>
      match lowerParsedL2? expression with
      | none => .failure
      | some access =>
          match parsedL2Writes? readState access with
          | none => .failure
          | some (l1Writes, l2Writes) =>
              .ok { currentState with
                l1bm := fun bank =>
                  let writes := l1Writes.filter (fun write => write.1 == bank) |>.map
                    (fun write => (write.2.1, write.2.2))
                  L1Transfer.commitL1Writes (currentState.l1bm bank) writes
                blockMemory := MVSemantics.commitWrites currentState.blockMemory l2Writes }
  | _ => .unknown

def executeParsedL2BlockProducers (readState currentState : State)
    (expressions : List ParsedExpr) : ProofsLean.StepResult State := Id.run do
  let mut state := currentState
  for expression in expressions.filter parsedExprIsL2BMProducer do
    match executeParsedL2BlockExpression readState state expression with
    | .failure => return .failure
    | .unknown => return .unknown
    | .ok next => state := next
  return .ok state

structure ParsedL1ToPEAccess where
  sourceBase : Option (Fin L1Transfer.l1bmLongWords)
  twoLongWords : Bool
  destinations : List ParsedOperand
  deriving Repr

def lowerParsedL1ToPE? (expression : ParsedExpr) : Option ParsedL1ToPEAccess := do
  match expression.op with
  | .l1bm .pbcast | .l1bm .mbcast | .l1bm .m4bcast | .l1bm (.distrib _) => pure ()
  | _ => none
  match expression.sources, expression.destinations with
  | [.l1bm width address], destinations@(_ :: _) =>
      guard (destinations.all fun destination => match destination with
        | .mem .. | .bar .. | .nowrite => true
        | _ => false)
      if width.val != 1 && width.val != 2 && width.val != 4 then none else
      let sourceOperand := ParsedOperand.l1bm width address
      let sourceBase : Option (Fin L1Transfer.l1bmLongWords) :=
        if ParsedOperand.isL1BMTurnaround sourceOperand then none else
        address.map fun address =>
          ⟨address.val % L1Transfer.l1bmLongWords,
            Nat.mod_lt _ (by decide)⟩
      some ⟨sourceBase, width.val == 4, destinations⟩
  | _, _ => none

def writeParsedL1ToPEDestination? (files : PEMemory.IntegerRegisterFiles)
    (destination : ParsedOperand) (context : ParsedIntegerContext)
    (output : IntegerALU.Bus) (cycle : Fin 4) (directive : ParsedMaskDirective)
    (hasSingleLineMask : Bool) :
    Option (PEMemory.IntegerRegisterFiles × Option (Bool × BitVec 12)) :=
  match destination with
  | .mem .. => do
      let access ← ParsedOperand.toDirectMemoryDestination? destination context.pe cycle
        context.bar0 context.bar1 context.tWord
      let selection ← ParsedOperand.resolveMemoryWriteSelection? destination access.bank
        files.maskRegisters cycle directive hasSingleLineMask
      some (PEMemory.writeDirectAccessMasked files access
        (PEMemory.unpackALUBus output) selection, none)
  | .bar lm1 .. => do
      let bank := if lm1 then PEMemory.Bank.lm1 else PEMemory.Bank.lm0
      let selection ← ParsedOperand.resolveMemoryWriteSelection? destination bank
        files.maskRegisters cycle directive hasSingleLineMask
      let barValue := BitVec.ofNat 12
        ((output.high.extractLsb' 32 32).toNat % 2 ^ 12)
      let update := if selection.flags == 0 then none else some (lm1, barValue)
      some (files, update)
  | .nowrite => some (files, none)
  | _ => none

def l1ToPEBusAt (state : State) (expression : ParsedExpr)
    (access : ParsedL1ToPEAccess) (pe : PEId) (cycle : Fin 4) : IntegerALU.Bus := Id.run do
  let context := ParsedIntegerContext.ofLinearIndex pe
  let bank : Fin 64 := ⟨context.group.val * 16 + context.l2b.val * 8 + context.l1b.val,
    by have hg := context.group.isLt; have h2 := context.l2b.isLt
       have h1 := context.l1b.isLt; omega⟩
  let source := match access.sourceBase with
    | some base => L1Transfer.L1ReadSource.addressed base
    | none => L1Transfer.L1ReadSource.turnaround (state.l1bmTurnaround bank)
  let mabGroup : Fin 4 := ⟨context.mab.val / 4, by have hm := context.mab.isLt; omega⟩
  let bus := match expression.op with
    | .l1bm .pbcast => match access.sourceBase with
        | some base => L1Transfer.pbcast (state.l1bm bank) base access.twoLongWords cycle
        | none => L1Transfer.pbcastTurnaround (state.l1bmTurnaround bank)
            access.twoLongWords cycle
    | .l1bm .mbcast => L1Transfer.mbcast (state.l1bm bank) source
        access.twoLongWords context.pe cycle
    | .l1bm .m4bcast => L1Transfer.m4bcast (state.l1bm bank) source
        access.twoLongWords mabGroup context.pe cycle
    | .l1bm (.distrib mabdiff) => L1Transfer.distrib (state.l1bm bank) source
        mabdiff context.mab context.pe cycle
    | _ => ⟨0, 0⟩
  return bus

def executeParsedL1ToPEAtPEs (readState currentState : State)
    (expression : ParsedExpr) (access : ParsedL1ToPEAccess)
    (pes : List PEId) (noForward hasSingleLineMask : Bool) : ProofsLean.StepResult State :=
  match pes with
  | [] => .ok currentState
  | pe :: rest =>
      let coordinates := ParsedIntegerContext.ofLinearIndex pe
      let readContext := readState.peContext pe
      let initialContext := currentState.peContext pe
      let rec writeCycles : List (Fin 4) → PEMemory.IntegerRegisterFiles →
          BitVec 12 → BitVec 12 →
          ProofsLean.StepResult (PEMemory.IntegerRegisterFiles × BitVec 12 × BitVec 12)
        | [], files, bar0, bar1 => .ok (files, bar0, bar1)
        | cycle :: cycles, files, bar0, bar1 =>
            let context := { coordinates with
              cycle := cycle
              bar0 := bar0
              bar1 := bar1
              tWord := readContext.tWord }
            match resolveFlushSelection? expression.flush files.maskRegisters cycle with
            | none => .unknown
            | some flushSelection =>
                let bus := parsedOutputAfterFlush flushSelection
                  (l1ToPEBusAt readState expression access pe cycle)
                let rec writeDestinations : List ParsedOperand →
                    PEMemory.IntegerRegisterFiles → BitVec 12 → BitVec 12 →
                    Option (PEMemory.IntegerRegisterFiles × BitVec 12 × BitVec 12)
                  | [], currentFiles, currentBar0, currentBar1 =>
                      some (currentFiles, currentBar0, currentBar1)
                  | destination :: remaining, currentFiles, currentBar0, currentBar1 => do
                      let destinationContext := { context with
                        bar0 := currentBar0
                        bar1 := currentBar1 }
                      let (nextFiles, barUpdate) ← writeParsedL1ToPEDestination?
                        currentFiles destination destinationContext bus cycle
                        currentState.maskDirective hasSingleLineMask
                      let nextBar0 := match barUpdate with
                        | some (false, value) => value
                        | _ => currentBar0
                      let nextBar1 := match barUpdate with
                        | some (true, value) => value
                        | _ => currentBar1
                      writeDestinations remaining nextFiles nextBar0 nextBar1
                match writeDestinations access.destinations files bar0 bar1 with
                | none => .unknown
                | some (nextFiles, nextBar0, nextBar1) =>
                    writeCycles cycles nextFiles nextBar0 nextBar1
      if access.sourceBase.isNone && !readState.l1bmTurnaroundValid then .failure
      else
        match writeCycles [0, 1, 2, 3] (currentState.peRegisters pe)
            initialContext.bar0 initialContext.bar1 with
        | .failure => .failure
        | .unknown => .unknown
        | .ok (files, bar0, bar1) =>
            let oldSlots := currentState.forwarding pe
            let outputs := fun cycle =>
              let raw := l1ToPEBusAt readState expression access pe cycle
              match resolveFlushSelection? expression.flush files.maskRegisters cycle with
              | some flushSelection => parsedOutputAfterFlush flushSelection raw
              | none => raw
            let forwarding := if noForward then oldSlots else fun unit cycle =>
              if unit = .l1ToPE then .known (outputs cycle) else oldSlots unit cycle
            let valid := if noForward then currentState.forwardingValid pe else
              fun unit cycle => if unit = .l1ToPE then true
                else currentState.forwardingValid pe unit cycle
            let next := { currentState with
              peRegisters := fun other => if other = pe then files else currentState.peRegisters other
              forwarding := fun other => if other = pe then forwarding else currentState.forwarding other
              forwardingValid := fun other => if other = pe then valid else currentState.forwardingValid other
              peContext := fun other => if other = pe then
                { currentState.peContext other with bar0 := bar0, bar1 := bar1 }
                else currentState.peContext other }
            executeParsedL1ToPEAtPEs readState next expression access rest noForward hasSingleLineMask

theorem executeParsedL1ToPEAtPEs_initial_turnaround_failure
    (currentState : State) (expression : ParsedExpr) (access : ParsedL1ToPEAccess)
    (pe : PEId) (rest : List PEId) (noForward hasSingleLineMask : Bool)
    (sourceIsTurnaround : access.sourceBase.isNone = true) :
    executeParsedL1ToPEAtPEs rustSimulatorInitialState currentState expression access (pe :: rest)
      noForward hasSingleLineMask = .failure := by
  simp [executeParsedL1ToPEAtPEs, sourceIsTurnaround, rustSimulatorInitialState]

def executeParsedL1ToPEProducer (readState currentState : State)
    (expression : ParsedExpr) (noForward hasSingleLineMask : Bool) : ProofsLean.StepResult State :=
  match lowerParsedL1ToPE? expression with
  | none => .failure
  | some access => executeParsedL1ToPEAtPEs readState currentState expression access
      (List.finRange 4096) noForward hasSingleLineMask

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

def parsedExprIsMslMsrProducer (expression : ParsedExpr) : Bool :=
  match expression.op with
  | .alu .msl none _ _ | .alu .msr none _ _ => true
  | _ => false

def parsedFloatReluShift (name : ParsedAluName) : Nat :=
  match name with
  | .relu1 => 1
  | .relu2 => 2
  | .relu3 => 3
  | _ => 0

def parsedFloatRsqrtLane (precision : ParsedPrecision) (value : Nat) : Nat := Id.run do
  let (exponentBits, mantissaBits, bias) := match precision with
    | .d => (11, 52, 1023)
    | .f => (8, 23, 127)
    | _ => (5, 10, 15)
  let exponent := value / 2 ^ mantissaBits % 2 ^ exponentBits
  let top4 := value / 2 ^ (mantissaBits - 4) % 16
  let evenMantissas := [13, 11, 10, 9, 8, 7, 6, 5, 4, 4, 3, 2, 2, 1, 1, 0]
  let oddMantissas := [31, 30, 28, 26, 25, 23, 22, 21, 20, 19, 18, 17, 16, 15, 14, 13]
  let mantissa5 := (if exponent % 2 == 0 then evenMantissas else oddMantissas)[top4]!
  let outputExponent := (bias + (bias + 1) / 2 - 1 + 2 ^ exponentBits - (exponent + 1) / 2) %
    2 ^ exponentBits
  return outputExponent * 2 ^ mantissaBits + mantissa5 * 2 ^ (mantissaBits - 5)

def parsedFloatFormat (precision : ParsedPrecision) : RRN.FloatPrecision :=
  match precision with
  | .d => .double
  | .f | .g => .single
  | _ => .half

theorem parsedFloatFormat_g_is_single : parsedFloatFormat .g = .single := by
  rfl

def parsedFloatFloorLane (precision : ParsedPrecision) (value : Nat) : Nat := Id.run do
  let format := parsedFloatFormat precision
  let mantissaBits := format.mantissaBits
  let exponent := value / 2 ^ mantissaBits % 2 ^ format.exponentBits
  let negative := value / 2 ^ (format.width - 1) % 2 == 1
  if exponent == 0 || exponent == format.exponentMax then return value
  let significand := 2 ^ mantissaBits + value % 2 ^ mantissaBits
  let binaryExponent := (exponent : Int) - format.bias - mantissaBits
  if binaryExponent >= 0 then return value
  let shift := (-binaryExponent).toNat
  let integer := if shift >= 128 then 0 else significand / 2 ^ shift
  let fractional := if shift >= 128 then true else significand % 2 ^ shift != 0
  let roundedInteger := integer + if negative && fractional then 1 else 0
  if roundedInteger == 0 then
    return (if negative then 1 else 0) * 2 ^ (format.width - 1)
  return RRN.roundPack format negative roundedInteger 0

def parsedFloatFtoiLane (precision : ParsedPrecision) (unsigned : Bool)
    (value : Nat) : Nat := Id.run do
  let format := parsedFloatFormat precision
  let width := format.width
  let mantissaBits := format.mantissaBits
  let exponent := value / 2 ^ mantissaBits % 2 ^ format.exponentBits
  let negative := value / 2 ^ (width - 1) % 2 == 1
  let magnitude := if exponent == 0 then 0 else if exponent == format.exponentMax then
      2 ^ 127
    else
      let significand := 2 ^ mantissaBits + value % 2 ^ mantissaBits
      let binaryExponent := (exponent : Int) - format.bias - mantissaBits
      if binaryExponent >= 0 then
        if binaryExponent > 70 then 2 ^ 127
        else significand * 2 ^ binaryExponent.toNat
      else if -binaryExponent >= 127 then 0
      else significand / 2 ^ (-binaryExponent).toNat
  let outputWidth := match precision with | .d => 64 | .f => 32 | _ => 16
  if unsigned then return min magnitude (2 ^ outputWidth - 1)
  let limit := if negative then 2 ^ (outputWidth - 1) else 2 ^ (outputWidth - 1) - 1
  let clipped := min magnitude limit
  return if negative then (2 ^ outputWidth - clipped) % 2 ^ outputWidth else clipped

/-- Rust `float::block_float`, used by ALU `bfn` and `bfe`. The caller supplies
one exponent-sharing block and the format's retained mantissa width. -/
def parsedBlockFloat (precision : RRN.FloatPrecision) (values : List Nat)
    (keep : Nat) (extended : Bool) : List Nat :=
  let mantissaBits := precision.mantissaBits
  let exponentMax := precision.exponentMax
  let width := precision.width
  let dropped := mantissaBits - keep
  let exponent (value : Nat) := value / 2 ^ mantissaBits % 2 ^ precision.exponentBits
  let mantissa (value : Nat) := value % 2 ^ mantissaBits
  let sign (value : Nat) := value / 2 ^ (width - 1) % 2 * 2 ^ (width - 1)
  let maxExponent := (values.map exponent).foldl Nat.max 0
  let topOnes (value : Nat) := mantissa value / 2 ^ dropped == 2 ^ keep - 1
  let common0 := maxExponent + if values.any fun value =>
      exponent value == maxExponent && topOnes value then 1 else 0
  let common := common0 + if precision == .half then dropped else 0
  values.map fun value =>
    let inputExponent := exponent value
    if common >= exponentMax then
      sign value + exponentMax * 2 ^ mantissaBits
    else if maxExponent == 0 then sign value
    else if inputExponent == 0 then
      if extended then sign value else sign value + common * 2 ^ mantissaBits
    else
      let distance := common - inputExponent
      let extendedFlag := extended &&
        (distance > 6 + dropped || (distance == 6 + dropped && !topOnes value))
      let shift := (if extendedFlag then distance - 6 else distance) + 1 +
        (if precision == .half then 0 else dropped)
      let rounded := RRN.roundShift (2 ^ mantissaBits + mantissa value) shift
      let resultMantissa := if precision == .half then rounded else rounded * 2 ^ dropped
      if resultMantissa == 0 then
        if extended then sign value else sign value + common * 2 ^ mantissaBits
      else
        sign value + (if extendedFlag then 0 else common) * 2 ^ mantissaBits +
          resultMantissa % 2 ^ mantissaBits

theorem parsedBlockFloat_half_bfn_converts_one :
    parsedBlockFloat .half [0x3e00] 9 false = [0x3f00] := by
  decide

theorem parsedBlockFloat_half_bfe_preserves_negative_zero :
    parsedBlockFloat .half [0x8000] 9 true = [0x8000] := by
  decide

/-- One MAB's four ALU lanes share the exponent blocks used by the Rust executor. -/
def parsedBlockFloatMab (precision : ParsedPrecision) (keep : Nat) (extended : Bool)
    (inputs : Fin 4 → IntegerALU.Bus) : Fin 4 → IntegerALU.Bus := Id.run do
  let laneCount := match precision with | .d => 1 | .f | .g => 2 | _ => 8
  let laneWidth := match precision with | .d => 64 | .f | .g => 32 | _ => 16
  let readLane (pe : Fin 4) (lane : Nat) : Nat :=
    let bus := inputs pe
    match precision with
    | .d => bus.high.toNat
    | .f | .g => bus.high.extractLsb' (32 * (1 - lane)) 32 |>.toNat
    | _ =>
        if lane < 4 then bus.high.extractLsb' (48 - 16 * lane) 16 |>.toNat
        else bus.low.extractLsb' (48 - 16 * (lane - 4)) 16 |>.toNat
  let positionsFor (lane : Nat) : List (Fin 4 × Nat) :=
    match precision with
    | .d => (List.finRange 4).map fun pe => (pe, 0)
    | .f => (List.finRange 4).map fun pe => (pe, lane)
    | .g => (List.finRange 4).flatMap fun pe => [(pe, 0), (pe, 1)]
    | _ => (List.finRange 4).flatMap fun pe =>
        (List.range 4).map fun offset => (pe, (lane / 4) * 4 + offset)
  let convertedLane (pe : Fin 4) (lane : Nat) : Nat := Id.run do
    let positions := positionsFor lane
    let values := positions.map fun (sourcePE, sourceLane) => readLane sourcePE sourceLane
    let converted := parsedBlockFloat (parsedFloatFormat precision) values keep extended
    let targetIndex := positions.idxOf (pe, lane)
    return converted[targetIndex]!
  return fun pe => Id.run do
    let lanes := (List.range laneCount).map (convertedLane pe)
    if laneWidth == 64 then
      return ⟨BitVec.ofNat 64 lanes[0]!, 0⟩
    else if laneWidth == 32 then
      return ⟨BitVec.ofNat 64 (lanes[0]! * 2 ^ 32 + lanes[1]!), 0⟩
    else
      let high := (List.range 4).foldl (fun acc lane =>
        acc + lanes[lane]! * 2 ^ (48 - 16 * lane)) 0
      let low := (List.range 4).foldl (fun acc lane =>
        acc + lanes[lane + 4]! * 2 ^ (48 - 16 * lane)) 0
      return ⟨BitVec.ofNat 64 high, BitVec.ofNat 64 low⟩

theorem parsedBlockFloatMab_double_shares_exponent_across_pes :
    parsedBlockFloatMab .d 52 false
      (fun pe => if pe.val == 0 then ⟨0x3ff0000000000000, 7⟩ else ⟨0, 0⟩) =
      (fun pe => if pe.val == 0 then ⟨0x3ff8000000000000, 0⟩
        else ⟨0x3ff0000000000000, 0⟩) := by
  decide

structure ParsedBlockFloatAccesses where
  precision : ParsedPrecision
  keep : Nat
  extended : Bool
  source : ParsedOperand
  destinations : List ParsedOperand
  deriving DecidableEq, Repr

/-- Syntax lowering for the single-source block-float ALU forms accepted by
the assembler: `bfn` on D/F/G/H and `bfe` on H. -/
def lowerParsedBlockFloat? (expression : ParsedExpr) : Option ParsedBlockFloatAccesses := do
  let (precision, keep, extended) ← match expression.op with
    | .alu .bfn (some precision) _ arg => do
        guard (precision == .d || precision == .f || precision == .g || precision == .h)
        let keep := if precision == .g then 18 else if precision == .h then arg.map Fin.val |>.getD 9
          else (parsedFloatFormat precision).mantissaBits
        some (precision, keep, false)
    | .alu .bfe (some .h) _ arg => some (.h, (arg.map Fin.val).getD 9, true)
    | _ => none
  match expression.sources, expression.destinations with
  | [source], destinations@(_ :: _) => do
      guard (destinations.all fun destination =>
        match destination with
        | .mem .. | .bar .. | .omr .. | .nowrite => true
        | _ => false)
      some ⟨precision, keep, extended, source, destinations⟩
  | _, _ => none

def parsedExprIsBlockFloatProducer (expression : ParsedExpr) : Bool :=
  match expression.op with
  | .alu .bfn (some precision) _ _ =>
      precision == .d || precision == .f || precision == .g || precision == .h
  | .alu .bfe (some .h) _ _ => true
  | _ => false

theorem lowerParsedBlockFloat_bfn_g_uses_pseudo_single_width (source destination : ParsedOperand) :
    lowerParsedBlockFloat?
      { op := .alu .bfn (some .g) false none, sources := [source],
        destinations := [destination], flush := none, text := "gbfn" } =
      (match destination with
      | .mem .. | .bar .. | .omr .. | .nowrite =>
          some ⟨.g, 18, false, source, [destination]⟩
      | _ => none) := by
  cases destination <;> rfl

theorem lowerParsedBlockFloat_bfn_keeps_destination_order :
    lowerParsedBlockFloat?
      { op := .alu .bfn (some .h) false (some 7),
        sources := [.fixed .msb1], destinations := [.omr 2 none, .nowrite],
        flush := none, text := "hbfn" } =
      some ⟨.h, 7, false, .fixed .msb1, [.omr 2 none, .nowrite]⟩ := by
  decide

theorem parsedFloatFloorLane_rounds_negative_fraction_down :
    parsedFloatFloorLane .f 0xbfc00000 = 0xc0000000 := by
  decide

theorem parsedFloatFtoiLane_signed_truncates_fraction :
    parsedFloatFtoiLane .f false 0x3fe00000 = 1 := by
  decide

theorem parsedFloatFtoiLane_unsigned_clamps_infinity :
    parsedFloatFtoiLane .f true 0x7f800000 = 0xffffffff := by
  decide

def parsedFloatMaxPickLeft (precision : ParsedPrecision) (name : ParsedAluName)
    (left right : Nat) : Bool := Id.run do
  let format := parsedFloatFormat precision
  let width := format.width
  let mantissaBits := format.mantissaBits
  let exponentLeft := left / 2 ^ mantissaBits % 2 ^ format.exponentBits
  let exponentRight := right / 2 ^ mantissaBits % 2 ^ format.exponentBits
  if left == right || (exponentLeft == 0 && exponentRight == 0) then return true
  let signLeft := left / 2 ^ (width - 1) % 2 == 1
  let signRight := right / 2 ^ (width - 1) % 2 == 1
  let magnitudeLeft := if exponentLeft == 0 then 0 else left % 2 ^ (width - 1)
  let magnitudeRight := if exponentRight == 0 then 0 else right % 2 ^ (width - 1)
  let keyLeft : Int := if signLeft then -(Int.ofNat magnitudeLeft) else Int.ofNat magnitudeLeft
  let keyRight : Int := if signRight then -(Int.ofNat magnitudeRight) else Int.ofNat magnitudeRight
  return if name == .max then keyLeft >= keyRight else keyLeft <= keyRight

theorem parsedFloatMaxPickLeft_ties_keep_left_zero_sign :
    parsedFloatMaxPickLeft .f .max 0x80000000 0 = true := by
  decide

theorem parsedFloatMaxPickLeft_orders_signed_values :
    parsedFloatMaxPickLeft .f .min 0x3f800000 0xc0000000 = false := by
  decide

theorem parsedFloatRsqrtLane_single_exact_table_entry :
    parsedFloatRsqrtLane .f 0x3f800000 = 0x3f7c0000 := by
  decide

def parsedFloatReluBus (precision : ParsedPrecision) (name : ParsedAluName) (unsigned : Bool)
    (left : IntegerALU.Bus) (right? : Option IntegerALU.Bus) : IntegerALU.Bus × BitVec 4 := Id.run do
  let width := match precision with | .d => 64 | .f => 32 | _ => 16
  let lanes := 64 / width
  let shift := parsedFloatReluShift name
  let inputA := (List.range lanes).map fun lane =>
    (left.high.extractLsb' (64 - width * (lane + 1)) width).toNat
  let inputB := (List.range lanes).map fun lane =>
    ((right?.getD ⟨0, 0⟩).high.extractLsb' (64 - width * (lane + 1)) width).toNat
  let outputs : List (Nat × Bool) := (List.range lanes).map fun lane =>
    let a := inputA[lane]!
    let b := inputB[lane]!
    if name == .passa then (a, a == 0)
    else if name == .rsqrt then (parsedFloatRsqrtLane precision a,
      a / 2 ^ (width - 1) % 2 == 0)
    else if name == .floor then (parsedFloatFloorLane precision a, false)
    else if name == .ftoi then (parsedFloatFtoiLane precision unsigned a, false)
    else if name == .max || name == .min then
      let pickLeft := parsedFloatMaxPickLeft precision name a b
      (if pickLeft then a else b, pickLeft)
    else
      let condition := a / 2 ^ (width - 1 - shift) % 2 == 0
      (if condition then b else 2 ^ (width - 1), condition)
  let packed := (List.range lanes).foldl (fun acc lane =>
    acc + (outputs[lane]!).1 * 2 ^ (64 - width * (lane + 1))) 0
  let conditions : List Bool := outputs.map fun output => output.2
  let flags := match width with
    | 64 => if conditions[0]! then 15 else 0
    | 32 => (if conditions[0]! then 12 else 0) + (if conditions[1]! then 3 else 0)
    | _ => (List.range lanes).foldl (fun acc lane =>
        acc + (if conditions[lane]! then 1 else 0) * 2 ^ (3 - lane)) 0
  let high := if name == .passa then left.high else BitVec.ofNat 64 packed
  return (⟨high, left.low⟩, BitVec.ofNat 4 flags)

theorem parsedFloatMaxBus_selects_each_lane_and_emits_flags :
    parsedFloatReluBus .f .max false
      ⟨0x3f800000c0000000, 0x1122334455667788⟩
      (some ⟨0xc00000003f800000, 0⟩) =
      (⟨0x3f8000003f800000, 0x1122334455667788⟩, 0xc) := by
  decide

theorem parsedFloatReluBus_single_lane_sign_selection :
    parsedFloatReluBus .f .relu false
      ⟨0x3f800000bf800000, 0x1122334455667788⟩
      (some ⟨0x4000000040400000, 0⟩) =
      (⟨0x4000000080000000, 0x1122334455667788⟩, 0xc) := by
  decide

theorem parsedFloatReluBus_float_passa_preserves_bus_and_sets_zero_flags :
    parsedFloatReluBus .f .passa false
      ⟨0x000000003f800000, 0x1122334455667788⟩ none =
      (⟨0x000000003f800000, 0x1122334455667788⟩, 0xc) := by
  decide

def lowerParsedMslMsr? (expression : ParsedExpr) :
    Option (Bool × List ParsedOperand) := do
  let isMsl ← match expression.op with
    | .alu .msl none _ _ => some true
    | .alu .msr none _ _ => some false
    | _ => none
  match expression.sources, expression.destinations with
  | [_], destinations@(_ :: _) =>
      guard (destinations.all fun destination => match destination with
        | .mem .. | .omr .. | .nowrite | .bar .. => true
        | _ => false)
      some (isMsl, destinations)
  | _, _ => none

structure ParsedFloatReluAccesses where
  precision : ParsedPrecision
  name : ParsedAluName
  unsigned : Bool
  sourceA : ParsedIntegerInput
  sourceB : Option ParsedIntegerInput
  destinations : List ParsedOperand

def lowerParsedFloatRelu? (expression : ParsedExpr) (context : ParsedIntegerContext) :
    Option ParsedFloatReluAccesses := do
  let (name, precision, unsigned) ← match expression.op with
    | .alu name (some precision) unsigned _ => do
        guard (name == .passa || name == .rsqrt || name == .floor || name == .ftoi ||
          name == .max || name == .min || name == .relu || name == .relu0 || name == .relu1 ||
          name == .relu2 || name == .relu3)
        guard (precision == .d || precision == .f || precision == .h)
        some (name, precision, unsigned)
    | _ => none
  match expression.sources, expression.destinations with
  | [sourceA], destinations@(_ :: _) => do
      guard (name == .passa || name == .rsqrt || name == .floor || name == .ftoi)
      guard (destinations.all fun destination => match destination with
        | .mem .. | .bar .. | .omr .. | .nowrite => true
        | _ => false)
      let sourceA ← ParsedOperand.toParsedIntegerInput? sourceA precision.laneWidth
        context.group context.l2b context.l1b context.mab context.pe context.cycle
        context.bar0 context.bar1 context.tWord
      some ⟨precision, name, unsigned, sourceA, none, destinations⟩
  | [sourceA, sourceB], destinations@(_ :: _) => do
      guard (name == .max || name == .min || name == .relu || name == .relu0 ||
        name == .relu1 || name == .relu2 || name == .relu3)
      guard (destinations.all fun destination => match destination with
        | .mem .. | .bar .. | .omr .. | .nowrite => true
        | _ => false)
      let sourceA ← ParsedOperand.toParsedIntegerInput? sourceA precision.laneWidth
        context.group context.l2b context.l1b context.mab context.pe context.cycle
        context.bar0 context.bar1 context.tWord
      let sourceB ← ParsedOperand.toParsedIntegerInput? sourceB precision.laneWidth
        context.group context.l2b context.l1b context.mab context.pe context.cycle
        context.bar0 context.bar1 context.tWord
      some ⟨precision, name, unsigned, sourceA, some sourceB, destinations⟩
  | _, _ => none

def parsedMatrixMAUDestinationEnabled? (files : PEMemory.IntegerRegisterFiles)
    (destination : ParsedOperand) (context : ParsedIntegerContext) (cycle : Fin 4)
    (directive : ParsedMaskDirective) (hasSingleLineMask : Bool) : Option Bool := do
  match destination with
  | .mem .. => do
      let access ← ParsedOperand.toDirectMemoryDestination? destination context.pe cycle
        context.bar0 context.bar1 context.tWord
      let selection ← ParsedOperand.resolveMemoryWriteSelection? destination access.bank
        files.maskRegisters cycle directive hasSingleLineMask
      some ((List.finRange 4).any fun word =>
        word.val < access.width.words &&
          PEMemory.selectedWordMask selection.flags selection.longLong word != 0)
  | .bar lm1 .. => do
      let bank := if lm1 then PEMemory.Bank.lm1 else PEMemory.Bank.lm0
      let selection ← ParsedOperand.resolveMemoryWriteSelection? destination bank
        files.maskRegisters cycle directive hasSingleLineMask
      some (selection.flags != 0)
  | .omr .. => some true
  | .nowrite => some false
  | _ => none

def parsedMatrixMAUDestinationDataPoisonApplies
    (poison : Bool) (destination : ParsedOperand) : Bool :=
  match destination with
  | .omr .. => false
  | _ => poison

theorem parsedMatrixMAU_poison_does_not_block_mask_flag_writes
    (poison : Bool) (entry : Fin 256) (mask : Option ParsedMask) :
    parsedMatrixMAUDestinationDataPoisonApplies poison (.omr entry mask) = false := by
  rfl

def executeParsedMatrixMAUTransitionAtMAB (readState currentState : State)
    (expression : ParsedExpr) (coordinate : MABCoordinate)
    (noForward hasSingleLineMask : Bool) : ProofsLean.StepResult State := Id.run do
  let initialFiles := fun pe => currentState.peRegisters (physicalPEId coordinate pe)
  let initialBar0 := fun pe => currentState.peContext (physicalPEId coordinate pe) |>.bar0
  let initialBar1 := fun pe => currentState.peContext (physicalPEId coordinate pe) |>.bar1
  let mut files := initialFiles
  let mut bar0 := initialBar0
  let mut bar1 := initialBar1
  let mut outputs : Fin 4 → Fin 4 → IntegerALU.Bus := fun _ _ => ⟨0, 0⟩
  let mut poisoned : Fin 4 → Bool := fun _ => false
  for cycle in List.finRange 4 do
    match executeParsedMatrixMAUAtMAB readState coordinate expression cycle with
    | .failure => return .failure
    | .unknown => return .unknown
    | .ok (buses, flags, poison) =>
      for pe in List.finRange 4 do
        let peId := physicalPEId coordinate pe
        let oldContext := currentState.peContext peId
        let contextBase := ParsedIntegerContext.ofLinearIndex peId
        match resolveFlushSelection? expression.flush (files pe).maskRegisters cycle with
        | none => return .unknown
        | some flushSelection =>
          let output := parsedOutputAfterFlush flushSelection (buses pe)
          let rec writeDests : List ParsedOperand → PEMemory.IntegerRegisterFiles →
              BitVec 12 → BitVec 12 →
              ProofsLean.StepResult (PEMemory.IntegerRegisterFiles × BitVec 12 × BitVec 12)
            | [], peFiles, peBar0, peBar1 => .ok (peFiles, peBar0, peBar1)
            | destination :: rest, peFiles, peBar0, peBar1 => Id.run do
                let context := { contextBase with
                  cycle := cycle
                  bar0 := peBar0
                  bar1 := peBar1
                  tWord := oldContext.tWord }
                match destination with
                | .omr entry _ =>
                    if entry.val == 0 || entry.val > 15 then return .failure
                | _ => pure ()
                let dataPoisonApplies :=
                  parsedMatrixMAUDestinationDataPoisonApplies poison destination
                if dataPoisonApplies then
                  match parsedMatrixMAUDestinationEnabled? peFiles destination context cycle
                      currentState.maskDirective hasSingleLineMask with
                  | none => return .unknown
                  | some true => return .failure
                  | some false => return writeDests rest peFiles peBar0 peBar1
                match writeParsedMslMsrDestination? peFiles destination context output
                    (flags pe) cycle currentState.maskDirective hasSingleLineMask with
                | none => return .unknown
                | some write =>
                  let nextBar0 := match write.barUpdate with
                    | some (false, value) => value
                    | _ => peBar0
                  let nextBar1 := match write.barUpdate with
                    | some (true, value) => value
                    | _ => peBar1
                  return writeDests rest write.files nextBar0 nextBar1
          match writeDests expression.destinations (files pe) (bar0 pe) (bar1 pe) with
          | .failure => return .failure
          | .unknown => return .unknown
          | .ok (nextFiles, nextBar0, nextBar1) =>
            files := fun index => if index == pe then nextFiles else files index
            bar0 := fun index => if index == pe then nextBar0 else bar0 index
            bar1 := fun index => if index == pe then nextBar1 else bar1 index
            outputs := fun index slot =>
              if index == pe && slot == cycle then output else outputs index slot
            poisoned := fun slot => if slot == cycle then poison else poisoned slot
  let mut nextState := currentState
  for pe in List.finRange 4 do
    let peId := physicalPEId coordinate pe
    let forwarding : Forwarding.Slots := fun unit cycle =>
      if noForward then nextState.forwarding peId unit cycle
      else if unit == .mau then
        if poisoned cycle then .poison else .known (outputs pe cycle)
      else nextState.forwarding peId unit cycle
    let valid : Forwarding.Unit → Fin 4 → Bool := fun unit cycle =>
      if noForward then nextState.forwardingValid peId unit cycle
      else if unit == .mau then true
      else nextState.forwardingValid peId unit cycle
    nextState := { nextState with
      peRegisters := fun other => if other == peId then files pe else nextState.peRegisters other
      forwarding := fun other => if other == peId then forwarding else nextState.forwarding other
      forwardingValid := fun other => if other == peId then valid else nextState.forwardingValid other
      peContext := fun other => if other == peId then
        { nextState.peContext other with bar0 := bar0 pe, bar1 := bar1 pe }
        else nextState.peContext other }
  return .ok nextState

def executeParsedMatrixMAUAtMABs (readState currentState : State)
    (expression : ParsedExpr) (coordinates : List MABCoordinate)
    (noForward hasSingleLineMask : Bool) : ProofsLean.StepResult State :=
  match coordinates with
  | [] => .ok currentState
  | coordinate :: rest =>
      match executeParsedMatrixMAUTransitionAtMAB readState currentState expression
          coordinate noForward hasSingleLineMask with
      | .failure => .failure
      | .unknown => .unknown
      | .ok next => executeParsedMatrixMAUAtMABs readState next expression rest
          noForward hasSingleLineMask

def parsedStateHasMatrixMAUPoison (state : State) : Bool :=
  (List.finRange 4096).any fun pe =>
    (List.finRange 4).any fun cycle =>
      match state.forwarding pe .mau cycle with
      | .poison => true
      | .known _ | .unknown => false

def propagateParsedMatrixMAUPoison (state : State) : State :=
  if parsedStateHasMatrixMAUPoison state then
    { state with forwarding := fun pe unit cycle =>
        if unit == .mau then .poison else state.forwarding pe unit cycle }
  else state

theorem propagateParsedMatrixMAUPoison_is_global
    (state : State) (hasPoison : parsedStateHasMatrixMAUPoison state = true)
    (pe : PEId) (cycle : Fin 4) :
    (propagateParsedMatrixMAUPoison state).forwarding pe .mau cycle = .poison := by
  simp [propagateParsedMatrixMAUPoison, hasPoison]

def executeParsedMatrixMAUProducer (readState currentState : State)
    (expressions : List ParsedExpr) (noForward hasSingleLineMask : Bool) :
    ProofsLean.StepResult State :=
  match expressions.filter parsedExprIsMatrixMAUProducer with
  | [] => .ok currentState
  | [expression] =>
      match executeParsedMatrixMAUAtMABs readState currentState expression
          allMABCoordinates noForward hasSingleLineMask with
      | .failure => .failure
      | .unknown => .unknown
      | .ok next => .ok (propagateParsedMatrixMAUPoison next)
  | _ => .unknown

def executeParsedMatrixMAUAndWrites (readState currentState : State)
    (expressions : List ParsedExpr) (noForward hasSingleLineMask : Bool) :
    ProofsLean.StepResult State := Id.run do
  let afterMAU ← match executeParsedMatrixMAUProducer readState currentState expressions
      noForward hasSingleLineMask with
    | .failure => return .failure
    | .unknown => return .unknown
    | .ok next => pure next
  return executeParsedMatrixWritesAtMABs readState allMABCoordinates expressions afterMAU

def executeParsedBlockFloatAtMAB (readState currentState : State)
    (expression : ParsedExpr) (coordinate : MABCoordinate)
    (noForward hasSingleLineMask : Bool) : ProofsLean.StepResult State := Id.run do
  let some accesses := lowerParsedBlockFloat? expression | return .unknown
  let initialFiles := fun pe => currentState.peRegisters (physicalPEId coordinate pe)
  let initialBar0 := fun pe =>
    currentState.peContext (physicalPEId coordinate pe) |>.bar0
  let initialBar1 := fun pe =>
    currentState.peContext (physicalPEId coordinate pe) |>.bar1
  let initialOutputs := fun _ _ => (⟨0, 0⟩ : IntegerALU.Bus)
  let writeDestinations (pe : Fin 4) (cycle : Fin 4) (output : IntegerALU.Bus)
      (files : PEMemory.IntegerRegisterFiles) (bar0 bar1 : BitVec 12) :
      ProofsLean.StepResult (PEMemory.IntegerRegisterFiles × BitVec 12 × BitVec 12) := Id.run do
    let peId := physicalPEId coordinate pe
    let oldContext := currentState.peContext peId
    let coords := ParsedIntegerContext.ofLinearIndex peId
    let rec apply : List ParsedOperand → PEMemory.IntegerRegisterFiles →
        BitVec 12 → BitVec 12 →
        ProofsLean.StepResult (PEMemory.IntegerRegisterFiles × BitVec 12 × BitVec 12)
      | [], files, bar0, bar1 => .ok (files, bar0, bar1)
      | destination :: rest, files, bar0, bar1 => Id.run do
          let destinationContext := { coords with cycle := cycle, bar0 := bar0, bar1 := bar1, tWord := oldContext.tWord }
          match writeParsedMslMsrDestination? files destination destinationContext output 0 cycle
              currentState.maskDirective hasSingleLineMask with
          | none => return .unknown
          | some write =>
              let nextBar0 := match write.barUpdate with
                | some (false, value) => value
                | _ => bar0
              let nextBar1 := match write.barUpdate with
                | some (true, value) => value
                | _ => bar1
              return apply rest write.files nextBar0 nextBar1
    apply accesses.destinations files bar0 bar1
  let readCycle (cycle : Fin 4) : ProofsLean.StepResult (Fin 4 → IntegerALU.Bus) := Id.run do
    let rec readPEs : List (Fin 4) → (Fin 4 → IntegerALU.Bus) →
        ProofsLean.StepResult (Fin 4 → IntegerALU.Bus)
      | [], buses => .ok buses
      | pe :: rest, buses => Id.run do
          let peId := physicalPEId coordinate pe
          let oldContext := readState.peContext peId
          let coords := ParsedIntegerContext.ofLinearIndex peId
          let context := { coords with cycle := cycle, bar0 := oldContext.bar0, bar1 := oldContext.bar1, tWord := oldContext.tWord }
          let some source := ParsedOperand.toParsedIntegerInput? accesses.source
              accesses.precision.laneWidth context.group context.l2b context.l1b context.mab
              context.pe cycle context.bar0 context.bar1 context.tWord
            | return .unknown
          match ParsedIntegerInput.readWithForwarding (readState.peRegisters peId)
              (stateForwardingSlots readState peId) cycle source with
          | .failure => return .failure
          | .unknown => return .unknown
          | .ok bus => return readPEs rest (fun other => if other == pe then bus else buses other)
    readPEs (List.finRange 4) (fun _ => ⟨0, 0⟩)
  let writeCycle (cycle : Fin 4) (buses : Fin 4 → IntegerALU.Bus)
      (files : Fin 4 → PEMemory.IntegerRegisterFiles)
      (bar0 bar1 : Fin 4 → BitVec 12)
      (outputs : Fin 4 → Fin 4 → IntegerALU.Bus) :
      ProofsLean.StepResult
        (Fin 4 → (PEMemory.IntegerRegisterFiles × BitVec 12 × BitVec 12 ×
          (Fin 4 → IntegerALU.Bus))) := Id.run do
    let rec writePEs : List (Fin 4) → (Fin 4 → PEMemory.IntegerRegisterFiles) →
        (Fin 4 → BitVec 12) → (Fin 4 → BitVec 12) →
        (Fin 4 → Fin 4 → IntegerALU.Bus) →
        ProofsLean.StepResult
          (Fin 4 → (PEMemory.IntegerRegisterFiles × BitVec 12 × BitVec 12 ×
            (Fin 4 → IntegerALU.Bus)))
      | [], files, bar0, bar1, outputs => .ok fun pe =>
          (files pe, bar0 pe, bar1 pe, outputs pe)
      | pe :: rest, files, bar0, bar1, outputs => Id.run do
          match resolveFlushSelection? expression.flush (files pe).maskRegisters cycle with
          | none => return .unknown
          | some flushSelection =>
              let output := parsedOutputAfterFlush flushSelection (buses pe)
              match writeDestinations pe cycle output (files pe) (bar0 pe) (bar1 pe) with
              | .failure => return .failure
              | .unknown => return .unknown
              | .ok (nextPEFiles, nextBar0, nextBar1) =>
                  let nextFiles := fun other => if other == pe then nextPEFiles else files other
                  let nextBar0s := fun other => if other == pe then nextBar0 else bar0 other
                  let nextBar1s := fun other => if other == pe then nextBar1 else bar1 other
                  let nextOutputs := fun other index =>
                    if other == pe && index == cycle then output else outputs other index
                  return writePEs rest nextFiles nextBar0s nextBar1s nextOutputs
    writePEs (List.finRange 4) files bar0 bar1 outputs
  let rec runCycles : List (Fin 4) →
      (Fin 4 → PEMemory.IntegerRegisterFiles) → (Fin 4 → BitVec 12) →
      (Fin 4 → BitVec 12) → (Fin 4 → Fin 4 → IntegerALU.Bus) →
      ProofsLean.StepResult
        (Fin 4 → (PEMemory.IntegerRegisterFiles × BitVec 12 × BitVec 12 ×
          (Fin 4 → IntegerALU.Bus)))
    | [], files, bar0, bar1, outputs => .ok fun pe =>
        (files pe, bar0 pe, bar1 pe, outputs pe)
    | cycle :: rest, files, bar0, bar1, outputs => Id.run do
        match readCycle cycle with
        | .failure => return .failure
        | .unknown => return .unknown
        | .ok inputBuses =>
            let outputBuses := parsedBlockFloatMab accesses.precision accesses.keep
              accesses.extended inputBuses
            match writeCycle cycle outputBuses files bar0 bar1 outputs with
            | .failure => return .failure
            | .unknown => return .unknown
            | .ok results =>
                let nextFiles := fun pe => (results pe).1
                let nextBar0 := fun pe => (results pe).2.1
                let nextBar1 := fun pe => (results pe).2.2.1
                let nextOutputs := fun pe index => (results pe).2.2.2 index
                return runCycles rest nextFiles nextBar0 nextBar1 nextOutputs
  match runCycles [0, 1, 2, 3] initialFiles initialBar0 initialBar1 initialOutputs with
  | .failure => return .failure
  | .unknown => return .unknown
  | .ok results =>
      let nextState := (List.finRange 4).foldl (fun state pe =>
        let peId := physicalPEId coordinate pe
        let (files, bar0, bar1, outputs) := results pe
        let forwarding : Forwarding.Slots := fun unit cycle =>
          if noForward then state.forwarding peId unit cycle
          else if unit == .alu then .known (outputs cycle)
          else state.forwarding peId unit cycle
        let forwardingValid : Forwarding.Unit → Fin 4 → Bool := fun unit cycle =>
          if noForward then state.forwardingValid peId unit cycle
          else if unit == .alu then true
          else state.forwardingValid peId unit cycle
        { state with
          peRegisters := fun other => if other == peId then files else state.peRegisters other
          forwarding := fun other => if other == peId then forwarding else state.forwarding other
          forwardingValid := fun other => if other == peId then forwardingValid else state.forwardingValid other
          peContext := fun other => if other == peId then
            { state.peContext other with bar0 := bar0, bar1 := bar1 }
            else state.peContext other }) currentState
      return .ok nextState

def executeParsedBlockFloatAtMABs (readState currentState : State)
    (expression : ParsedExpr) (coordinates : List MABCoordinate)
    (noForward hasSingleLineMask : Bool) : ProofsLean.StepResult State :=
  match coordinates with
  | [] => .ok currentState
  | coordinate :: rest =>
      match executeParsedBlockFloatAtMAB readState currentState expression coordinate
          noForward hasSingleLineMask with
      | .failure => .failure
      | .unknown => .unknown
      | .ok next => executeParsedBlockFloatAtMABs readState next expression rest
          noForward hasSingleLineMask

def executeParsedBlockFloatProducer (readState currentState : State)
    (expressions : List ParsedExpr) (noForward hasSingleLineMask : Bool) :
    ProofsLean.StepResult State :=
  match expressions.filter parsedExprIsBlockFloatProducer with
  | [] => .ok currentState
  | [expression] => executeParsedBlockFloatAtMABs readState currentState expression
      allMABCoordinates noForward hasSingleLineMask
  | _ => .unknown

def mslMsrSourcePE (pe : PEId) (isMsl : Bool) : PEId :=
  let localPE := pe.val % 4
  let sourcePE := if isMsl then (localPE + 3) % 4 else (localPE + 1) % 4
  have hlocal : localPE < 4 := Nat.mod_lt _ (by decide)
  have hsource : sourcePE < 4 := by
    unfold sourcePE
    split <;> exact Nat.mod_lt _ (by decide : 0 < 4)
  have hgroup : pe.val / 4 < 1024 := by omega
  ⟨pe.val / 4 * 4 + sourcePE, by
    omega⟩

theorem mslMsrSourcePE_stays_in_MAB (pe : PEId) (isMsl : Bool) :
    (mslMsrSourcePE pe isMsl).val / 4 = pe.val / 4 := by
  have hlocal : pe.val % 4 < 4 := Nat.mod_lt _ (by decide)
  have hsource : (if isMsl then (pe.val % 4 + 3) % 4 else
      (pe.val % 4 + 1) % 4) < 4 := by split <;> omega
  simp only [mslMsrSourcePE]
  omega

theorem mslMsrSourcePE_direction_examples :
    mslMsrSourcePE 4 true = 7 ∧ mslMsrSourcePE 4 false = 5 := by
  decide

def mslMsrOutputBus (source : IntegerALU.Bus) : IntegerALU.Bus :=
  ⟨source.high, 0⟩

theorem mslMsrOutputBus_keeps_msb_longword_only (source : IntegerALU.Bus) :
    (mslMsrOutputBus source).high = source.high ∧
      (mslMsrOutputBus source).low = 0 := by
  constructor <;> rfl

def executeParsedMslMsrAtPE (readState currentState : State)
    (expression : ParsedExpr) (pe : PEId) (noForward hasSingleLineMask : Bool) :
    ProofsLean.StepResult State := Id.run do
  let oldContext := readState.peContext pe
  let coordinates := ParsedIntegerContext.ofLinearIndex pe
  let context := { coordinates with
    bar0 := oldContext.bar0
    bar1 := oldContext.bar1
    tWord := oldContext.tWord }
  let some (isMsl, destinations) := lowerParsedMslMsr? expression | return .unknown
  let sourcePE := mslMsrSourcePE pe isMsl
  let sourceOldContext := readState.peContext sourcePE
  let sourceCoordinates := ParsedIntegerContext.ofLinearIndex sourcePE
  let sourceContext := { sourceCoordinates with
    bar0 := sourceOldContext.bar0
    bar1 := sourceOldContext.bar1
    tWord := sourceOldContext.tWord }
  let sourceAt := fun cycle => match expression.sources with
    | [source] => ParsedOperand.toParsedIntegerInput? source .long
        sourceContext.group sourceContext.l2b sourceContext.l1b sourceContext.mab
        sourceContext.pe cycle sourceContext.bar0 sourceContext.bar1 sourceContext.tWord
    | _ => none
  let rec runCycles : List (Fin 4) → PEMemory.IntegerRegisterFiles →
      BitVec 12 → BitVec 12 → (Fin 4 → IntegerALU.Bus) → ProofsLean.StepResult
        (PEMemory.IntegerRegisterFiles × BitVec 12 × BitVec 12 ×
          (Fin 4 → IntegerALU.Bus))
    | [], files, bar0, bar1, outputs => .ok (files, bar0, bar1, outputs)
    | cycle :: rest, files, bar0, bar1, outputs =>
        match sourceAt cycle with
        | none => .unknown
        | some source =>
          match ParsedIntegerInput.readWithForwarding (readState.peRegisters sourcePE)
              (stateForwardingSlots readState sourcePE) cycle source with
          | .failure => .failure
          | .unknown => .unknown
          | .ok sourceBus =>
            let shifted := mslMsrOutputBus sourceBus
            match resolveFlushSelection? expression.flush files.maskRegisters cycle with
            | none => .unknown
            | some flushSelection =>
                let output := parsedOutputAfterFlush flushSelection shifted
                let destinationContext := { context with cycle := cycle, bar0 := bar0, bar1 := bar1 }
                let rec writeDestinations : List ParsedOperand → PEMemory.IntegerRegisterFiles →
                    BitVec 12 → BitVec 12 → Option
                      (PEMemory.IntegerRegisterFiles × BitVec 12 × BitVec 12)
                  | [], currentFiles, currentBar0, currentBar1 =>
                      some (currentFiles, currentBar0, currentBar1)
                  | destination :: remaining, currentFiles, currentBar0, currentBar1 => do
                      let destinationContext := { context with cycle := cycle, bar0 := currentBar0, bar1 := currentBar1 }
                      let write ← writeParsedMslMsrDestination? currentFiles destination
                        destinationContext output 0 cycle currentState.maskDirective
                        hasSingleLineMask
                      let nextBar0 := match write.barUpdate with
                        | some (false, value) => value
                        | _ => currentBar0
                      let nextBar1 := match write.barUpdate with
                        | some (true, value) => value
                        | _ => currentBar1
                      writeDestinations remaining write.files nextBar0 nextBar1
                match writeDestinations destinations files bar0 bar1 with
                | none => .unknown
                | some (nextFiles, nextBar0, nextBar1) =>
                    runCycles rest nextFiles nextBar0 nextBar1
                      (fun index => if index = cycle then output else outputs index)
  match runCycles [0, 1, 2, 3] (currentState.peRegisters pe) context.bar0 context.bar1
      (fun _ => ⟨0, 0⟩) with
  | .failure => return .failure
  | .unknown => return .unknown
  | .ok (registers, bar0, bar1, outputs) =>
      let forwarding : Forwarding.Slots := fun unit cycle =>
        if noForward then currentState.forwarding pe unit cycle
        else if unit == .alu then .known (outputs cycle)
        else currentState.forwarding pe unit cycle
      let valid : Forwarding.Unit → Fin 4 → Bool := fun unit cycle =>
        if noForward then currentState.forwardingValid pe unit cycle
        else if unit == .alu then true
        else currentState.forwardingValid pe unit cycle
      return .ok { currentState with
        peRegisters := fun other => if other = pe then registers else currentState.peRegisters other
        forwarding := fun other => if other = pe then forwarding else currentState.forwarding other
        forwardingValid := fun other => if other = pe then valid else currentState.forwardingValid other
        peContext := fun other => if other = pe then
          { currentState.peContext other with bar0 := bar0, bar1 := bar1 }
          else currentState.peContext other }

def executeParsedMslMsrAtPEs (readState currentState : State)
    (expression : ParsedExpr) (pes : List PEId) (noForward hasSingleLineMask : Bool) :
    ProofsLean.StepResult State :=
  match pes with
  | [] => .ok currentState
  | pe :: rest =>
      match executeParsedMslMsrAtPE readState currentState expression pe
          noForward hasSingleLineMask with
      | .failure => .failure
      | .unknown => .unknown
      | .ok next => executeParsedMslMsrAtPEs readState next expression rest
          noForward hasSingleLineMask

def executeParsedMslMsrProducers (readState currentState : State)
    (expressions : List ParsedExpr) (noForward hasSingleLineMask : Bool) :
    ProofsLean.StepResult State :=
  match expressions.filter parsedExprIsMslMsrProducer with
  | [] => .ok currentState
  | [expression] => executeParsedMslMsrAtPEs readState currentState expression
      (List.finRange 4096) noForward hasSingleLineMask
  | _ => .unknown

def parsedExprIsFloatReluProducer (expression : ParsedExpr) : Bool :=
  match expression.op with
  | .alu name (some precision) _ _ =>
      (name == .passa || name == .rsqrt || name == .floor || name == .ftoi || name == .max ||
        name == .min || name == .relu || name == .relu0 || name == .relu1 || name == .relu2 ||
        name == .relu3) && (precision == .d || precision == .f || precision == .h)
  | _ => false

def executeParsedFloatReluAtPE (readState currentState : State)
    (expression : ParsedExpr) (pe : PEId) (noForward hasSingleLineMask : Bool) :
    ProofsLean.StepResult State := Id.run do
  let oldContext := readState.peContext pe
  let coordinates := ParsedIntegerContext.ofLinearIndex pe
  let sourceContext := { coordinates with
    bar0 := oldContext.bar0
    bar1 := oldContext.bar1
    tWord := oldContext.tWord }
  let rec runCycles : List (Fin 4) → PEMemory.IntegerRegisterFiles →
      BitVec 12 → BitVec 12 → (Fin 4 → IntegerALU.Bus) → ProofsLean.StepResult
        (PEMemory.IntegerRegisterFiles × BitVec 12 × BitVec 12 ×
          (Fin 4 → IntegerALU.Bus))
    | [], files, bar0, bar1, outputs => .ok (files, bar0, bar1, outputs)
    | cycle :: rest, files, bar0, bar1, outputs =>
      match lowerParsedFloatRelu? expression { sourceContext with cycle := cycle } with
      | none => .unknown
      | some accesses =>
        match ParsedIntegerInput.readWithForwarding (readState.peRegisters pe)
            (stateForwardingSlots readState pe) cycle accesses.sourceA with
        | .failure => .failure
        | .unknown => .unknown
        | .ok sourceA =>
          let sourceBResult := match accesses.sourceB with
            | none => ProofsLean.StepResult.ok none
            | some sourceB =>
                match ParsedIntegerInput.readWithForwarding (readState.peRegisters pe)
                    (stateForwardingSlots readState pe) cycle sourceB with
                | .failure => .failure
                | .unknown => .unknown
                | .ok value => .ok (some value)
          match sourceBResult with
          | .failure => .failure
          | .unknown => .unknown
          | .ok sourceB =>
            let (rawOutput, flags) := parsedFloatReluBus accesses.precision accesses.name
              accesses.unsigned
              sourceA sourceB
            match resolveFlushSelection? expression.flush files.maskRegisters cycle with
            | none => .unknown
            | some flushSelection =>
              let output := parsedOutputAfterFlush flushSelection rawOutput
              let rec writeDestinations : List ParsedOperand → PEMemory.IntegerRegisterFiles →
                  BitVec 12 → BitVec 12 → Option
                    (PEMemory.IntegerRegisterFiles × BitVec 12 × BitVec 12)
                | [], currentFiles, currentBar0, currentBar1 =>
                    some (currentFiles, currentBar0, currentBar1)
                | destination :: remaining, currentFiles, currentBar0, currentBar1 => do
                    let destinationContext := { coordinates with cycle := cycle, bar0 := currentBar0, bar1 := currentBar1 }
                    let write ← writeParsedMslMsrDestination? currentFiles destination
                      destinationContext output flags cycle currentState.maskDirective
                      hasSingleLineMask
                    let nextBar0 := match write.barUpdate with
                      | some (false, value) => value
                      | _ => currentBar0
                    let nextBar1 := match write.barUpdate with
                      | some (true, value) => value
                      | _ => currentBar1
                    writeDestinations remaining write.files nextBar0 nextBar1
              match writeDestinations accesses.destinations files bar0 bar1 with
              | none => .unknown
              | some (nextFiles, nextBar0, nextBar1) =>
                  runCycles rest nextFiles nextBar0 nextBar1
                    (fun index => if index = cycle then output else outputs index)
  match runCycles [0, 1, 2, 3] (currentState.peRegisters pe)
      oldContext.bar0 oldContext.bar1 (fun _ => ⟨0, 0⟩) with
  | .failure => return .failure
  | .unknown => return .unknown
  | .ok (registers, bar0, bar1, outputs) =>
      let forwarding : Forwarding.Slots := fun unit cycle =>
        if noForward then currentState.forwarding pe unit cycle
        else if unit == .alu then .known (outputs cycle)
        else currentState.forwarding pe unit cycle
      let valid : Forwarding.Unit → Fin 4 → Bool := fun unit cycle =>
        if noForward then currentState.forwardingValid pe unit cycle
        else if unit == .alu then true
        else currentState.forwardingValid pe unit cycle
      return .ok { currentState with
        peRegisters := fun other => if other = pe then registers else currentState.peRegisters other
        forwarding := fun other => if other = pe then forwarding else currentState.forwarding other
        forwardingValid := fun other => if other = pe then valid else currentState.forwardingValid other
        peContext := fun other => if other = pe then
          { currentState.peContext other with bar0 := bar0, bar1 := bar1 }
          else currentState.peContext other }

def executeParsedFloatReluAtPEs (readState currentState : State)
    (expression : ParsedExpr) (pes : List PEId) (noForward hasSingleLineMask : Bool) :
    ProofsLean.StepResult State :=
  match pes with
  | [] => .ok currentState
  | pe :: rest =>
      match executeParsedFloatReluAtPE readState currentState expression pe
          noForward hasSingleLineMask with
      | .failure => .failure
      | .unknown => .unknown
      | .ok next => executeParsedFloatReluAtPEs readState next expression rest
          noForward hasSingleLineMask

def executeParsedFloatReluProducers (readState currentState : State)
    (expressions : List ParsedExpr) (noForward hasSingleLineMask : Bool) :
    ProofsLean.StepResult State :=
  match expressions.filter parsedExprIsFloatReluProducer with
  | [] => .ok currentState
  | [expression] => executeParsedFloatReluAtPEs readState currentState expression
      (List.finRange 4096) noForward hasSingleLineMask
  | _ => .unknown

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
  let oldSlots := stateForwardingSlots state pe
  let matrixStore := state.matrixRegisters context.group context.l2b context.l1b
  let peExpressions := expressions.filter fun expression =>
    !parsedExprIsMatrixWriteProducer expression &&
      !parsedExprIsL1MwriteProducer expression &&
      !parsedExprIsL1GatherProducer expression &&
      !parsedExprIsL1ReduceProducer expression &&
      !parsedExprIsL1ToPEProducer expression &&
      !parsedExprIsMatrixMAUProducer expression &&
      !parsedExprIsSupportedFloatMAUProducer expression &&
      !parsedExprIsMslMsrProducer expression &&
      !parsedExprIsBlockFloatProducer expression &&
      !parsedExprIsFloatReluProducer expression
  match parsedIntegerMatrixReadLineFourCycleStep (state.peRegisters pe) oldSlots
      matrixStore peExpressions control false with
  | .failure => .failure
  | .unknown => .unknown
  | .ok (registers, integerPreparedSlots, matrixBarUpdates) =>
    match executeParsedFloatMAUsAtPE (state.peRegisters pe) registers oldSlots
        context expressions state.maskDirective
        (expressions.any parsedExprHasSingleLineWriteMask) with
    | .failure => .failure
    | .unknown => .unknown
    | .ok (registersWithFloat, floatBar0, floatBar1, floatOutputs, hasMAUProducer) =>
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
          let (matrixBar0, matrixBar1) := matrixBarUpdates.foldl
            (fun (bar0, bar1) update => match update with
              | (false, value) => (value, bar1)
              | (true, value) => (bar0, value))
            (oldContext.bar0, oldContext.bar1)
          let nextBar0 := if expressions.any (parsedFloatMAUWritesBAR false)
            then floatBar0 else matrixBar0
          let nextBar1 := if expressions.any (parsedFloatMAUWritesBAR true)
            then floatBar1 else matrixBar1
          .ok { state with
            peRegisters := fun other =>
              if other = pe then registersWithFloat else state.peRegisters other
            forwarding := fun other =>
              if other = pe then forwarding else state.forwarding other
            forwardingValid := fun other =>
              if other = pe then forwardingValid else state.forwardingValid other
            peContext := fun other =>
              if other = pe then { oldContext with bar0 := nextBar0, bar1 := nextBar1 }
              else state.peContext other }

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
        if expressions.any parsedExprIsUnsupportedRustAlu then .failure
        else if expressions.all parsedExprIsSupportedPELineProducer then
          let peExpressions := expressions.filter (fun expression =>
            !parsedExprIsL2BMProducer expression && !parsedExprIsMslMsrProducer expression &&
              !parsedExprIsMatrixMAUProducer expression &&
              !parsedExprIsBlockFloatProducer expression &&
              !parsedExprIsFloatReluProducer expression)
          match executeIntegerProducerLineAtPEs peExpressions (List.finRange 4096) state with
          | .failure => .failure
          | .unknown => .unknown
          | .ok nextPEs =>
              let noForward := expressions.any parsedExprIsNoForwardProducer
              let hasSingleLineMask := expressions.any parsedExprHasSingleLineWriteMask
              match executeParsedMslMsrProducers state nextPEs expressions noForward
                  hasSingleLineMask with
              | .failure => .failure
              | .unknown => .unknown
              | .ok nextWithMsl =>
                match executeParsedFloatReluProducers state nextWithMsl expressions noForward
                    hasSingleLineMask with
                | .failure => .failure
                | .unknown => .unknown
                | .ok nextWithRelu =>
                  match executeParsedBlockFloatProducer state nextWithRelu expressions noForward
                      hasSingleLineMask with
                  | .failure => .failure
                  | .unknown => .unknown
                  | .ok nextWithBlockFloat =>
                    match executeParsedMatrixMAUAndWrites state nextWithBlockFloat expressions
                        noForward hasSingleLineMask with
                    | .failure => .failure
                    | .unknown => .unknown
                    | .ok next =>
                        let hasPEToL1Producer :=
                          expressions.any parsedExprMayWriteL1BMTurnaround
                        match executeParsedL1MwriteProducers state next expressions (!noForward) with
                        | .failure => .failure
                        | .unknown => .unknown
                        | .ok nextWithL1 =>
                          match executeParsedL1GatherProducers state nextWithL1 expressions (!noForward) with
                          | .failure => .failure
                          | .unknown => .unknown
                          | .ok nextWithGather =>
                            match executeParsedL1ReduceProducers state nextWithGather expressions (!noForward) with
                            | .failure => .failure
                            | .unknown => .unknown
                            | .ok nextWithReduce =>
                              let l1ToPE := expressions.filter parsedExprIsL1ToPEProducer
                              let afterL1ToPE : ProofsLean.StepResult State := match l1ToPE with
                                | [] => .ok nextWithReduce
                                | [expression] => executeParsedL1ToPEProducer state nextWithReduce
                                    expression noForward
                                    (expressions.any parsedExprHasSingleLineWriteMask)
                                | _ => .unknown
                              match afterL1ToPE with
                              | .failure => .failure
                              | .unknown => .unknown
                              | .ok nextWithBroadcast =>
                                match executeParsedL2BlockProducers state nextWithBroadcast expressions with
                                | .failure => .failure
                                | .unknown => .unknown
                                | .ok nextWithL2 =>
                                  .ok { nextWithL2 with
                                    hazardClock := nextWithL2.hazardClock + InstructionLine.cost line
                                    l1bmTurnaroundValid :=
                                      if noForward then nextWithL2.l1bmTurnaroundValid else hasPEToL1Producer }
        else .unknown
    | .nop count _ =>
        .ok { state with hazardClock := state.hazardClock + count.val }
    | .mv transfer =>
        if transfer.kind == .nop then
          .ok { state with hazardClock := state.hazardClock + 1 }
        else
          match executeParsedMvMemory state transfer.toParsed with
          | .failure => .failure
          | .unknown => .unknown
          | .ok next =>
              .ok { next with hazardClock := next.hazardClock + 1 }

/-- Execute one normalized source line. Zero-cost mask directives update the
control state directly; instruction-bearing lines use the scored line step. -/
noncomputable def executeNormalizedLine (line : NormalizedLine) (state : State) :
    ProofsLean.StepResult State :=
  match line with
  | .maskDirective widthWords targets entry =>
      .ok { state with maskDirective := ⟨widthWords, targets, entry⟩ }
  | _ =>
      match line.toInstruction? with
      | none => .failure
      | some instruction => executeIntegerProducerInstructionLine instruction state

def parsedPEHazardEventsForPE? (state : State) (expressions : List ParsedExpr)
    (pe : PEId) : Option (List PEMemory.TimedPEAccess) := do
  let oldContext := state.peContext pe
  let coordinates := ParsedIntegerContext.ofLinearIndex pe
  let context := { coordinates with
    bar0 := oldContext.bar0
    bar1 := oldContext.bar1
    tWord := oldContext.tWord }
  let control : ParsedMaskExecutionControl :=
    { directive := state.maskDirective
      context := context
      elapsedWords := state.hazardClock }
  let perExpression ← expressions.mapM fun expression =>
    PEMemory.ParsedExpr.toTimedPEHazardEvents? expression control
  some perExpression.flatten

def parsedPEHazardViolated (history current : List PEMemory.TimedPEAccess) : Bool :=
  (PEMemory.peHazardConstraintsBetween history current).any fun constraint =>
    constraint.distance < constraint.required

def parsedNormalizedLinePEHazardEvents?
    (state : State) (line : NormalizedLine) :
    Option (List (List PEMemory.TimedPEAccess)) :=
  match line.toInstruction? with
  | none => some (List.replicate 4096 [])
  | some (.nop _ _) | some (.mv _) => some (List.replicate 4096 [])
  | some (.pe normalizedExpressions) => do
      let expressions := normalizedExpressions.map NormalizedExpr.toParsed
      (List.finRange 4096).mapM fun pe =>
        parsedPEHazardEventsForPE? state expressions pe

def parsedBlockHazardViolated
    (history current : List PEMemory.TimedBlockAccess) : Bool :=
  (HazardTrace.blockHazardConstraintsBetween history current).any fun constraint =>
    constraint.distance < constraint.required

structure HazardAwareState where
  machine : State
  peHistory : PEId → List PEMemory.TimedPEAccess
  blockHistory : List PEMemory.TimedBlockAccess

def HazardAwareState.initial (state : State) : HazardAwareState :=
  ⟨state, fun _ => [], []⟩

noncomputable def executeHazardAwareNormalizedLine (line : NormalizedLine)
    (state : HazardAwareState) : ProofsLean.StepResult HazardAwareState := Id.run do
  match line with
  | .maskDirective .. =>
      match executeNormalizedLine line state.machine with
      | .failure => return .failure
      | .unknown => return .unknown
      | .ok next => return .ok { state with machine := next }
  | _ =>
      let some instruction := line.toInstruction? | return .failure
      if !checkParsedTopLine instruction.toParsed then return .failure
      let some currentPEEvents ← pure
        (parsedNormalizedLinePEHazardEvents? state.machine line) | return .unknown
      let currentBlockEvents := HazardTrace.parsedLineBlockHazardEvents
        line.toParsed state.machine.hazardClock
      if (List.finRange 4096).any fun pe =>
          parsedPEHazardViolated (state.peHistory pe) currentPEEvents[pe.val]! then
        return .failure
      if parsedBlockHazardViolated state.blockHistory currentBlockEvents then
        return .failure
      match executeNormalizedLine line state.machine with
      | .failure => return .failure
      | .unknown => return .unknown
      | .ok next =>
          let nextPEHistory := fun pe =>
            (state.peHistory pe ++ currentPEEvents[pe.val]!).filter fun event =>
              event.startWord + 4 ≥ next.hazardClock
          let nextBlockHistory :=
            (state.blockHistory ++ currentBlockEvents).filter fun event =>
              event.startWord + 4 ≥ next.hazardClock
          return .ok ⟨next, nextPEHistory, nextBlockHistory⟩

/-- Execute a normalized source program in order. The runner carries recent
PE-memory accesses as validation history, rejects PE hazards before applying
the line, and retains the transactional behavior of each datapath step. -/
noncomputable def executeNormalizedProgramAux
    : List NormalizedLine → HazardAwareState →
      ProofsLean.StepResult HazardAwareState
  | [], currentState => .ok currentState
  | line :: rest, currentState =>
      match executeHazardAwareNormalizedLine line currentState with
      | .failure => .failure
      | .unknown => .unknown
      | .ok next => executeNormalizedProgramAux rest next
termination_by remaining _ => remaining.length
decreasing_by simp_wf

noncomputable def executeNormalizedProgram (lines : List NormalizedLine)
    (state : State) : ProofsLean.StepResult State :=
  match executeNormalizedProgramAux lines (HazardAwareState.initial state) with
  | .failure => .failure
  | .unknown => .unknown
  | .ok final => .ok final.machine

/-- Source-level program entry: apply the repository's normalization rules
before executing, so stripped records and mask directives retain their
specified zero-cost behavior. -/
noncomputable def executeParsedProgram (lines : List ParsedLine) (state : State) :
    ProofsLean.StepResult State := Id.run do
  let mut normalized := []
  for line in lines do
    match line.normalizeForSubmission? with
    | none => return .failure
    | some emitted => normalized := normalized ++ emitted
  return executeNormalizedProgram normalized state

theorem executeNormalizedLine_maskDirective_updates_state
    (state : State) (widthWords : Nat) (targets : ParsedMaskTargets)
    (entry : Fin 256) :
    executeNormalizedLine (.maskDirective widthWords targets entry) state =
      .ok { state with maskDirective := ⟨widthWords, targets, entry⟩ } := by
  rfl

/-- The zero-cost directive transition changes exactly the control resource
named by its normalized footprint and leaves the scored hazard clock alone. -/
theorem executeNormalizedLine_maskDirective_matches_footprint
    (state : State) (widthWords : Nat) (targets : ParsedMaskTargets)
    (entry : Fin 256) :
    UnitResource.maskControl ∈
        (normalizedLineFootprint (.maskDirective widthWords targets entry)).unitWrites ∧
      UnitResource.hazardClock ∉
        (normalizedLineFootprint (.maskDirective widthWords targets entry)).unitWrites ∧
      executeNormalizedLine (.maskDirective widthWords targets entry) state =
        .ok { state with maskDirective := ⟨widthWords, targets, entry⟩ } ∧
      ({ state with maskDirective := ⟨widthWords, targets, entry⟩ }).hazardClock =
        state.hazardClock := by
  exact ⟨(NormalizedLine.maskDirective_footprint widthWords targets entry).1,
    (NormalizedLine.maskDirective_footprint widthWords targets entry).2,
    executeNormalizedLine_maskDirective_updates_state state widthWords targets entry,
    rfl⟩

/-- A positive normalized nop advances the clock by exactly its scored cost,
matching its syntactic hazard-clock write footprint. -/
theorem executeNormalizedLine_positive_nop_matches_footprint
    (state : State) (count : Nat) (wait : Option (Fin 256))
    (accepted : checkParsedTopLine (.nop (count + 1) wait) = true) :
    UnitResource.hazardClock ∈
        (normalizedLineFootprint (.nop (count + 1) wait)).unitWrites ∧
      executeNormalizedLine (.nop (count + 1) wait) state =
        .ok { state with hazardClock := state.hazardClock + (count + 1) } := by
  constructor
  · exact NormalizedLine.positive_nop_writes_hazard_clock count wait
  · have acceptedInstruction :
        checkParsedTopLine (InstructionLine.toParsed
          (.nop ⟨count + 1, by omega⟩ wait)) = true := by
      simpa [InstructionLine.toParsed] using accepted
    simp [executeNormalizedLine, NormalizedLine.toInstruction?,
      executeIntegerProducerInstructionLine, acceptedInstruction]

/-- Zero-count nop is erased by normalization. If constructed directly in the
normalized AST, it cannot advance state and its footprint is empty. -/
theorem executeNormalizedLine_zero_nop_matches_footprint
    (state : State) (wait : Option (Fin 256)) :
    normalizedLineFootprint (.nop 0 wait) = emptyFootprint ∧
      executeNormalizedLine (.nop 0 wait) state = .failure := by
  constructor
  · rfl
  · simp [executeNormalizedLine, NormalizedLine.toInstruction?]

/-- The parsed `mvnop` form does not read or write block memory; its sole
state effect is the issue-clock increment represented by the line footprint. -/
theorem executeNormalizedLine_mvnop_matches_footprint
    (state : State) (transfer : NormalizedMv)
    (isNop : transfer.kind = .nop) :
    UnitResource.mv ∉ (normalizedMvFootprint transfer).unitReads ∧
      UnitResource.mv ∉ (normalizedMvFootprint transfer).unitWrites ∧
      UnitResource.hazardClock ∈
        (normalizedLineFootprint (.mv transfer)).unitWrites ∧
      executeNormalizedLine (.mv transfer) state =
        .ok { state with hazardClock := state.hazardClock + 1 } := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [NormalizedMv.nop_has_empty_footprint transfer isNop]
    simp [emptyFootprint]
  · rw [NormalizedMv.nop_has_empty_footprint transfer isNop]
    simp [emptyFootprint]
  · simp [normalizedLineFootprint, normalizedMvFootprint, isNop,
      Footprint.combine]
  · have accepted : checkParsedTopLine (.mv transfer.toParsed) = true := rfl
    simp [executeNormalizedLine, NormalizedLine.toInstruction?,
      executeIntegerProducerInstructionLine, InstructionLine.toParsed,
      accepted, isNop]

theorem executeNormalizedProgram_maskDirective_updates_state
    (state : State) (widthWords : Nat) (targets : ParsedMaskTargets)
    (entry : Fin 256) :
    executeNormalizedProgram [.maskDirective widthWords targets entry] state =
      .ok { state with maskDirective := ⟨widthWords, targets, entry⟩ } := by
  simp [executeNormalizedProgram, executeNormalizedProgramAux,
    executeHazardAwareNormalizedLine, HazardAwareState.initial, executeNormalizedLine]

theorem executeParsedProgram_maskDirective_updates_state
    (state : State) (widthWords : Nat) (targets : ParsedMaskTargets)
    (entry : Fin 256) :
    executeParsedProgram [.maskDirective widthWords targets entry] state =
      .ok { state with maskDirective := ⟨widthWords, targets, entry⟩ } := by
  simp [executeParsedProgram, ParsedLine.normalizeForSubmission?,
    executeNormalizedProgram, executeNormalizedProgramAux,
    executeHazardAwareNormalizedLine, HazardAwareState.initial, executeNormalizedLine]

noncomputable def integerProducerMachine : ProofsLean.PartialMachine where
  Line := InstructionLine
  State := State
  Input := Unit
  step := fun line state => executeIntegerProducerInstructionLine line state
  legal := fun _ => True
  lineCost := InstructionLine.cost
  positiveCost := InstructionLine.cost_positive

def Issue.InstructionLine.toNormalizedLine : Issue.InstructionLine → NormalizedLine
  | .pe expressions => .pe expressions
  | .nop count wait => .nop count.val wait
  | .mv transfer => .mv transfer

@[simp] theorem Issue.InstructionLine.toNormalizedLine_toParsed
    (line : Issue.InstructionLine) :
    line.toNormalizedLine.toParsed = line.toParsed := by
  cases line <;> simp [Issue.InstructionLine.toNormalizedLine,
    Issue.InstructionLine.toParsed, NormalizedLine.toParsed,
    NormalizedMv.toParsed, ParsedMv.normalize]

/-- Stateful instruction machine whose state retains PE and block hazard
history across calls to `step`. Unlike `integerProducerMachine`, its step is
the same hazard-aware transition used by normalized program execution. -/
noncomputable def hazardAwareInstructionMachine : ProofsLean.PartialMachine where
  Line := InstructionLine
  State := HazardAwareState
  Input := Unit
  step := fun line state =>
    executeHazardAwareNormalizedLine line.toNormalizedLine state
  legal := fun lines => ∀ line ∈ lines, checkParsedTopLine line.toParsed = true
  lineCost := InstructionLine.cost
  positiveCost := InstructionLine.cost_positive

theorem integerProducerMachine_issue_failure (line : InstructionLine)
    (state : State) (rejected : checkParsedTopLine line.toParsed = false) :
    integerProducerMachine.step line state = .failure := by
  simp [integerProducerMachine, executeIntegerProducerInstructionLine, rejected]

theorem executeIntegerProducerInstructionLine_unsupported_rust_alu_failure
    (normalizedExpressions : List NormalizedExpr) (state : State)
    (accepted : checkParsedTopLine
      (InstructionLine.pe normalizedExpressions).toParsed = true)
    (unsupported : (normalizedExpressions.map NormalizedExpr.toParsed).any
      parsedExprIsUnsupportedRustAlu = true) :
    executeIntegerProducerInstructionLine (.pe normalizedExpressions) state = .failure := by
  simp [executeIntegerProducerInstructionLine, accepted, unsupported]

theorem executeIntegerProducerInstructionLine_nop
    (count : {n : Nat // 0 < n}) (wait : Option (Fin 256)) (state : State)
    (accepted : checkParsedTopLine (.nop count.val wait) = true) :
    executeIntegerProducerInstructionLine (.nop count wait) state =
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
    (normalizedExpressions : List NormalizedExpr)
    (state nextPEs nextMsl nextRelu nextBlockFloat next nextL1 : State)
    (accepted : checkParsedTopLine
      (InstructionLine.pe normalizedExpressions).toParsed = true)
    (supported : (normalizedExpressions.map NormalizedExpr.toParsed).all
      parsedExprIsSupportedPELineProducer = true)
    (noUnsupportedRustAlu : (normalizedExpressions.map NormalizedExpr.toParsed).any
      parsedExprIsUnsupportedRustAlu = false)
    (executed : executeIntegerProducerLineAtPEs
      ((normalizedExpressions.map NormalizedExpr.toParsed).filter (fun expression =>
        !parsedExprIsL2BMProducer expression && !parsedExprIsMslMsrProducer expression &&
          !parsedExprIsMatrixMAUProducer expression &&
          !parsedExprIsBlockFloatProducer expression &&
          !parsedExprIsFloatReluProducer expression))
      (List.finRange 4096) state =
        .ok nextPEs)
    (mslMsrWrites : executeParsedMslMsrProducers state nextPEs
      (normalizedExpressions.map NormalizedExpr.toParsed)
      (normalizedExpressions.any (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed))
      (normalizedExpressions.any (parsedExprHasSingleLineWriteMask ∘ NormalizedExpr.toParsed)) =
        .ok nextMsl)
    (reluWrites : executeParsedFloatReluProducers state nextMsl
      (normalizedExpressions.map NormalizedExpr.toParsed)
      (normalizedExpressions.any (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed))
      (normalizedExpressions.any (parsedExprHasSingleLineWriteMask ∘ NormalizedExpr.toParsed)) =
        .ok nextRelu)
    (blockFloatWrites : executeParsedBlockFloatProducer state nextRelu
      (normalizedExpressions.map NormalizedExpr.toParsed)
      (normalizedExpressions.any (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed))
      (normalizedExpressions.any (parsedExprHasSingleLineWriteMask ∘ NormalizedExpr.toParsed)) =
        .ok nextBlockFloat)
    (matrixWrites : executeParsedMatrixMAUAndWrites state nextBlockFloat
      (normalizedExpressions.map NormalizedExpr.toParsed)
      (normalizedExpressions.any (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed))
      (normalizedExpressions.any (parsedExprHasSingleLineWriteMask ∘ NormalizedExpr.toParsed)) = .ok next)
    (l1Writes : executeParsedL1MwriteProducers state next
      (normalizedExpressions.map NormalizedExpr.toParsed)
      (!(normalizedExpressions.any
        (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed))) = .ok nextL1)
    (nextGather : State)
    (gatherWrites : executeParsedL1GatherProducers state nextL1
      (normalizedExpressions.map NormalizedExpr.toParsed)
      (!(normalizedExpressions.any
        (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed))) = .ok nextGather)
    (nextReduce : State)
    (reduceWrites : executeParsedL1ReduceProducers state nextGather
      (normalizedExpressions.map NormalizedExpr.toParsed)
      (!(normalizedExpressions.any
        (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed))) = .ok nextReduce)
    (nextBroadcast : State)
    (l1ToPE : (match (normalizedExpressions.map NormalizedExpr.toParsed).filter
        parsedExprIsL1ToPEProducer with
      | [] => (ProofsLean.StepResult.ok nextReduce : ProofsLean.StepResult State)
      | [expression] => executeParsedL1ToPEProducer state nextReduce expression
          (normalizedExpressions.any
            (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed))
          (normalizedExpressions.any
            (parsedExprHasSingleLineWriteMask ∘ NormalizedExpr.toParsed))
      | _ => .unknown) = .ok nextBroadcast)
    (nextL2 : State)
    (l2Writes : executeParsedL2BlockProducers state nextBroadcast
      (normalizedExpressions.map NormalizedExpr.toParsed) = .ok nextL2)
    :
    executeIntegerProducerInstructionLine (.pe normalizedExpressions) state =
      .ok { nextL2 with
        hazardClock := nextL2.hazardClock + InstructionLine.cost (.pe normalizedExpressions)
        l1bmTurnaroundValid :=
          if ∃ expression ∈ normalizedExpressions,
            parsedExprIsNoForwardProducer expression.toParsed = true
          then nextL2.l1bmTurnaroundValid
          else normalizedExpressions.any (fun expression =>
            parsedExprMayWriteL1BMTurnaround expression.toParsed) } := by
  simp [executeIntegerProducerInstructionLine, accepted, supported, noUnsupportedRustAlu,
    executed, mslMsrWrites,
    reluWrites, blockFloatWrites,
    matrixWrites, l1Writes, gatherWrites, reduceWrites, l1ToPE, l2Writes, List.any_map]
  set_option maxRecDepth 8192 in rfl

end ProofsLean.MNCore
