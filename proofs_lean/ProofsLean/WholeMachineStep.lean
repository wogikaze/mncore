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

/-- Any read of a forwarding unit/cycle disabled in the whole-machine state
is a known execution failure, independent of the stale payload stored there. -/
theorem disabledForwardingSlot_read_fails (state : State) (pe : PEId)
    (unit : Forwarding.Unit) (cycle : Fin 4) (kind : ParsedForward)
    (hUnit : ParsedIntegerInput.forwardUnit kind = unit)
    (disabled : state.forwardingValid pe unit cycle = false) :
    ParsedIntegerInput.readWithForwarding
      (state.peRegisters pe) (stateForwardingSlots state pe) cycle
      (.forward kind false) = .failure := by
  apply parsedIntegerInput_forward_poison_fails
  rw [hUnit]
  exact stateForwardingSlots_invalid_is_poison state pe unit cycle disabled

theorem unresolvedForwardingSlot_read_stays_unknown (state : State) (pe : PEId)
    (unit : Forwarding.Unit) (cycle : Fin 4) (kind : ParsedForward)
    (hUnit : ParsedIntegerInput.forwardUnit kind = unit)
    (enabled : state.forwardingValid pe unit cycle = true)
    (unresolved : state.forwarding pe unit cycle = .unknown) :
    ParsedIntegerInput.readWithForwarding
      (state.peRegisters pe) (stateForwardingSlots state pe) cycle
      (.forward kind false) = .unknown := by
  have slot : stateForwardingSlots state pe (ParsedIntegerInput.forwardUnit kind) cycle = .unknown := by
    rw [hUnit]
    rw [stateForwardingSlots_valid_preserves_payload state pe unit cycle enabled]
    exact unresolved
  exact parsedIntegerInput_forward_unknown_stays_unknown
    (state.peRegisters pe) (stateForwardingSlots state pe) cycle kind false slot

/-- At simulator startup every forwarding read fails exactly as Rust's
uninitialized-register error path: the initial validity bit yields poison,
which the shared parsed-input reader turns into a known execution failure. -/
theorem rustSimulatorInitialState_forwarding_read_fails
    (pe : PEId) (cycle : Fin 4) (kind : ParsedForward) :
    ParsedIntegerInput.readWithForwarding
      (rustSimulatorInitialState.peRegisters pe)
      (stateForwardingSlots rustSimulatorInitialState pe) cycle
      (.forward kind false) = .failure := by
  exact disabledForwardingSlot_read_fails rustSimulatorInitialState pe
    (ParsedIntegerInput.forwardUnit kind) cycle kind rfl
    (by rfl)

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

def parsedExprWritesOMR (expression : ParsedExpr) : Bool :=
  expression.destinations.any fun destination =>
    match destination with | .omr .. => true | _ => false

/-- Rust computes every producer first, then commits output destinations in
source order. If the L1-to-PE output precedes the line's OMR writer, its mask
and flush selection therefore read the pre-issue OMR state. -/
def parsedL1ToPEPrecedesOMRWriter : List ParsedExpr → Bool
  | [] => false
  | expression :: rest =>
      if parsedExprIsL1ToPEProducer expression then rest.any parsedExprWritesOMR
      else parsedL1ToPEPrecedesOMRWriter rest

def parsedExprIsNoForwardProducer (expression : ParsedExpr) : Bool :=
  match expression.op with
  | .noforward => true
  | _ => false

def parsedExprWaitTag? (expression : ParsedExpr) : Option (Fin 256) :=
  match expression.op with
  | .wait tag => some tag
  | _ => none

def parsedExprWaitPending (state : State) (expression : ParsedExpr) : Bool :=
  match parsedExprWaitTag? expression with
  | none => false
  | some tag => !state.mvCompletedTags tag

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
  | .mem access neg ext rnd _ =>
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

theorem parsedFloatMAUSourceAttrs?_memory_mask_irrelevant
    (access : Access) (neg ext rnd : Bool) (mask : Option ParsedMask)
    (context : ParsedIntegerContext) :
    parsedFloatMAUSourceAttrs? (.mem access neg ext rnd mask) context =
      parsedFloatMAUSourceAttrs? (.mem access neg ext rnd none) context := by
  rfl

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

theorem executeParsedMatrixWritesAtMAB_preserves_pe_state
    (readState currentState : State) (coordinate : MABCoordinate)
    (expressions : List ParsedExpr) (next : State)
    (executed : executeParsedMatrixWritesAtMAB readState currentState coordinate
      expressions = .ok next) :
    next.peRegisters = currentState.peRegisters ∧
      next.forwarding = currentState.forwarding ∧
      next.forwardingValid = currentState.forwardingValid ∧
      next.peContext = currentState.peContext := by
  simp only [executeParsedMatrixWritesAtMAB] at executed
  cases writeResult : executeParsedMatrixWritesAtMAB.applyWrites readState coordinate
      (expressions.filter parsedExprIsMatrixWriteProducer)
      (currentState.matrixRegisters coordinate.group coordinate.l2b coordinate.l1b) with
  | failure => simp_all [writeResult]
  | unknown => simp_all [writeResult]
  | ok store =>
      simp only [writeResult] at executed
      injection executed with nextEq
      subst next
      simp

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

theorem executeParsedMatrixWritesAtMABs_preserves_pe_state
    (readState currentState next : State) (coordinates : List MABCoordinate)
    (expressions : List ParsedExpr)
    (executed : executeParsedMatrixWritesAtMABs readState coordinates expressions
      currentState = .ok next) :
    next.peRegisters = currentState.peRegisters ∧
      next.forwarding = currentState.forwarding ∧
      next.forwardingValid = currentState.forwardingValid ∧
      next.peContext = currentState.peContext := by
  induction coordinates generalizing currentState with
  | nil =>
      simp [executeParsedMatrixWritesAtMABs] at executed
      cases executed
      exact ⟨rfl, rfl, rfl, rfl⟩
  | cons coordinate rest ih =>
      simp only [executeParsedMatrixWritesAtMABs] at executed
      split at executed
      · cases executed
        exact ⟨rfl, rfl, rfl, rfl⟩
      · cases matrixWrite : executeParsedMatrixWritesAtMAB
            readState currentState coordinate expressions with
        | failure => simp [matrixWrite] at executed
        | unknown => simp [matrixWrite] at executed
        | ok intermediate =>
            have remaining : executeParsedMatrixWritesAtMABs readState rest
                expressions intermediate = .ok next := by
              simpa [matrixWrite] using executed
            rcases ih intermediate remaining with ⟨pe, forwarding, validity, context⟩
            have frame := executeParsedMatrixWritesAtMAB_preserves_pe_state
              readState currentState coordinate expressions intermediate matrixWrite
            exact ⟨pe.trans frame.1, forwarding.trans frame.2.1,
              validity.trans frame.2.2.1, context.trans frame.2.2.2⟩

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
    return .failure
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

def readParsedMatrixMAUSourcePEsAux (state : State) (coordinate : MABCoordinate)
    (operand : ParsedOperand) (format : RRN.FloatPrecision) (count : Nat)
    (cycle : Fin 4) : List (Fin 4) → List Nat → ProofsLean.StepResult (List Nat)
  | [], values => .ok values
  | pe :: rest, values =>
      match readParsedMatrixMAUSourcePE state coordinate operand format count pe cycle with
      | .failure => .failure
      | .unknown => .unknown
      | .ok lanes =>
          readParsedMatrixMAUSourcePEsAux state coordinate operand format count cycle
            rest (values ++ lanes)

def readParsedMatrixMAUSourcePEs (state : State) (coordinate : MABCoordinate)
    (operand : ParsedOperand) (format : RRN.FloatPrecision) (count : Nat)
    (cycle : Fin 4) (pes : List (Fin 4)) : ProofsLean.StepResult (List Nat) :=
  readParsedMatrixMAUSourcePEsAux state coordinate operand format count cycle pes []

def readParsedMatrixMAUSourcePEsLoopAux (state : State) (coordinate : MABCoordinate)
    (operand : ParsedOperand) (format : RRN.FloatPrecision) (count : Nat)
    (cycle : Fin 4) (pes : List (Fin 4)) (initial : List Nat) :
    ProofsLean.StepResult (List Nat) := Id.run do
  let mut values := initial
  for pe in pes do
    match readParsedMatrixMAUSourcePE state coordinate operand format count pe cycle with
    | .failure => return .failure
    | .unknown => return .unknown
    | .ok lanes => values := values ++ lanes
  return .ok values

def readParsedMatrixMAUSourcePEsLoop (state : State) (coordinate : MABCoordinate)
    (operand : ParsedOperand) (format : RRN.FloatPrecision) (count : Nat)
    (cycle : Fin 4) (pes : List (Fin 4)) : ProofsLean.StepResult (List Nat) :=
  readParsedMatrixMAUSourcePEsLoopAux state coordinate operand format count cycle pes []

theorem readParsedMatrixMAUSourcePEsAux_eq_loopAux
    (state : State) (coordinate : MABCoordinate) (operand : ParsedOperand)
    (format : RRN.FloatPrecision) (count : Nat) (cycle : Fin 4)
    (pes : List (Fin 4)) (initial : List Nat) :
    readParsedMatrixMAUSourcePEsAux state coordinate operand format count cycle pes initial =
      readParsedMatrixMAUSourcePEsLoopAux state coordinate operand format count cycle pes
        initial := by
  induction pes generalizing initial with
  | nil => simp [readParsedMatrixMAUSourcePEsAux, readParsedMatrixMAUSourcePEsLoopAux]
  | cons pe rest ih =>
      cases h : readParsedMatrixMAUSourcePE state coordinate operand format count pe cycle <;>
        simp [readParsedMatrixMAUSourcePEsAux, readParsedMatrixMAUSourcePEsLoopAux,
          h, ih]

theorem readParsedMatrixMAUSourcePEs_eq_loop
    (state : State) (coordinate : MABCoordinate) (operand : ParsedOperand)
    (format : RRN.FloatPrecision) (count : Nat) (cycle : Fin 4)
    (pes : List (Fin 4)) :
    readParsedMatrixMAUSourcePEs state coordinate operand format count cycle pes =
      readParsedMatrixMAUSourcePEsLoop state coordinate operand format count cycle pes := by
  exact readParsedMatrixMAUSourcePEsAux_eq_loopAux state coordinate operand format count
    cycle pes []

def readParsedMatrixMAUSourceAtMAB (state : State) (coordinate : MABCoordinate)
    (operand : ParsedOperand) (format : RRN.FloatPrecision) (count : Nat)
    (cycle : Fin 4) : ProofsLean.StepResult (List Nat) :=
  readParsedMatrixMAUSourcePEs state coordinate operand format count cycle
    (List.finRange 4)

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

def parsedMatrixMAUAccumulatorFormat (precision : ParsedPrecision) : RRN.FloatPrecision :=
  match precision with
  | .d => RRN.FloatPrecision.double
  | _ => RRN.FloatPrecision.single

def executeParsedMatrixMAUCalculationAtMAB (state : State) (coordinate : MABCoordinate)
    (expression : ParsedExpr) (cycle : Fin 4) :
    ProofsLean.StepResult (List Nat × Bool × Bool) := Id.run do
  let (.mau precision true kind half round) := expression.op | return .unknown
  -- Once this matrix-MAU executor is selected, malformed required sources
  -- follow Rust's known operand-error path rather than an epistemic gap.
  let matrixSide ← match expression.sources with
    | .matrix sideY _ none :: _ => pure sideY
    | _ => return .failure
  let (vector, accumulator) ← match kind, expression.sources with
    | .mul, [.matrix _ _ none, vector] => pure (vector, none)
    | .add, [.matrix _ _ none, vector] => pure (vector, none)
    | .passa, [.matrix _ _ none, vector] => pure (vector, none)
    | .fma, [.matrix _ _ none, vector, acc] => pure (vector, some acc)
    | _, _ => return .failure
  let some vectorFormat := parsedMatrixMAUFloatFormat precision | return .failure
  let vectorValues ← match readParsedMatrixMAUSourceAtMAB state coordinate vector
      vectorFormat (parsedMatrixMAUVectorLanesPerPE precision) cycle with
    | .failure => return .failure
    | .unknown => return .unknown
    | .ok values => pure values
  let accumulatorValues ← match accumulator with
    | none => pure []
    | some source =>
      let accumulatorFormat := parsedMatrixMAUAccumulatorFormat precision
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

theorem executeParsedMatrixMAUCalculationAtMAB_mul_read_known_never_unknown
    (state : State) (coordinate : MABCoordinate) (precision : ParsedPrecision)
    (half : Option Char) (round : Bool) (sideY : Bool) (width : Fin 5)
    (vectorSource : ParsedOperand) (cycle : Fin 4)
    (format : RRN.FloatPrecision)
    (formatLowered : parsedMatrixMAUFloatFormat precision = some format)
    (vectorReadKnown : readParsedMatrixMAUSourceAtMAB state coordinate vectorSource
      format (parsedMatrixMAUVectorLanesPerPE precision) cycle ≠ .unknown) :
    executeParsedMatrixMAUCalculationAtMAB state coordinate
      { op := .mau precision true .mul half round
        sources := [.matrix sideY width none, vectorSource]
        destinations := []
        flush := none
        text := "" } cycle ≠ .unknown := by
  cases vectorRead : readParsedMatrixMAUSourceAtMAB state coordinate vectorSource
      format (parsedMatrixMAUVectorLanesPerPE precision) cycle with
  | failure => simp [executeParsedMatrixMAUCalculationAtMAB, formatLowered, vectorRead]
  | unknown => exact (vectorReadKnown vectorRead).elim
  | ok vectorValues =>
      cases calculation : parsedMatrixMAUCalculateRows?
          (state.matrixRegisters coordinate.group coordinate.l2b coordinate.l1b)
          coordinate sideY precision .mul half round vectorValues [] with
      | none => simp [executeParsedMatrixMAUCalculationAtMAB, formatLowered,
          vectorRead, calculation]
      | some rows => simp [executeParsedMatrixMAUCalculationAtMAB, formatLowered,
          vectorRead, calculation]

theorem executeParsedMatrixMAUCalculationAtMAB_add_read_known_never_unknown
    (state : State) (coordinate : MABCoordinate) (precision : ParsedPrecision)
    (half : Option Char) (round : Bool) (sideY : Bool) (width : Fin 5)
    (vectorSource : ParsedOperand) (cycle : Fin 4)
    (format : RRN.FloatPrecision)
    (formatLowered : parsedMatrixMAUFloatFormat precision = some format)
    (vectorReadKnown : readParsedMatrixMAUSourceAtMAB state coordinate vectorSource
      format (parsedMatrixMAUVectorLanesPerPE precision) cycle ≠ .unknown) :
    executeParsedMatrixMAUCalculationAtMAB state coordinate
      { op := .mau precision true .add half round
        sources := [.matrix sideY width none, vectorSource]
        destinations := []
        flush := none
        text := "" } cycle ≠ .unknown := by
  cases vectorRead : readParsedMatrixMAUSourceAtMAB state coordinate vectorSource
      format (parsedMatrixMAUVectorLanesPerPE precision) cycle with
  | failure => simp [executeParsedMatrixMAUCalculationAtMAB, formatLowered, vectorRead]
  | unknown => exact (vectorReadKnown vectorRead).elim
  | ok vectorValues =>
      cases calculation : parsedMatrixMAUCalculateRows?
          (state.matrixRegisters coordinate.group coordinate.l2b coordinate.l1b)
          coordinate sideY precision .add half round vectorValues [] with
      | none => simp [executeParsedMatrixMAUCalculationAtMAB, formatLowered,
          vectorRead, calculation]
      | some rows => simp [executeParsedMatrixMAUCalculationAtMAB, formatLowered,
          vectorRead, calculation]

theorem executeParsedMatrixMAUCalculationAtMAB_passa_read_known_never_unknown
    (state : State) (coordinate : MABCoordinate) (precision : ParsedPrecision)
    (half : Option Char) (round : Bool) (sideY : Bool) (width : Fin 5)
    (vectorSource : ParsedOperand) (cycle : Fin 4)
    (format : RRN.FloatPrecision)
    (formatLowered : parsedMatrixMAUFloatFormat precision = some format)
    (vectorReadKnown : readParsedMatrixMAUSourceAtMAB state coordinate vectorSource
      format (parsedMatrixMAUVectorLanesPerPE precision) cycle ≠ .unknown) :
    executeParsedMatrixMAUCalculationAtMAB state coordinate
      { op := .mau precision true .passa half round
        sources := [.matrix sideY width none, vectorSource]
        destinations := []
        flush := none
        text := "" } cycle ≠ .unknown := by
  cases vectorRead : readParsedMatrixMAUSourceAtMAB state coordinate vectorSource
      format (parsedMatrixMAUVectorLanesPerPE precision) cycle with
  | failure => simp [executeParsedMatrixMAUCalculationAtMAB, formatLowered, vectorRead]
  | unknown => exact (vectorReadKnown vectorRead).elim
  | ok vectorValues =>
      cases calculation : parsedMatrixMAUCalculateRows?
          (state.matrixRegisters coordinate.group coordinate.l2b coordinate.l1b)
          coordinate sideY precision .passa half round vectorValues [] with
      | none => simp [executeParsedMatrixMAUCalculationAtMAB, formatLowered,
          vectorRead, calculation]
      | some rows => simp [executeParsedMatrixMAUCalculationAtMAB, formatLowered,
          vectorRead, calculation]

theorem executeParsedMatrixMAUCalculationAtMAB_fma_reads_known_never_unknown
    (state : State) (coordinate : MABCoordinate) (precision : ParsedPrecision)
    (half : Option Char) (round : Bool) (sideY : Bool) (width : Fin 5)
    (vectorSource accumulatorSource : ParsedOperand) (cycle : Fin 4)
    (format : RRN.FloatPrecision)
    (formatLowered : parsedMatrixMAUFloatFormat precision = some format)
    (vectorReadKnown : readParsedMatrixMAUSourceAtMAB state coordinate vectorSource
      format (parsedMatrixMAUVectorLanesPerPE precision) cycle ≠ .unknown)
    (accumulatorReadKnown : readParsedMatrixMAUSourceAtMAB state coordinate
      accumulatorSource (parsedMatrixMAUAccumulatorFormat precision)
      (parsedMatrixMAUAccumulatorLanesPerPE precision) cycle ≠ .unknown) :
    executeParsedMatrixMAUCalculationAtMAB state coordinate
      { op := .mau precision true .fma half round
        sources := [.matrix sideY width none, vectorSource, accumulatorSource]
        destinations := []
        flush := none
        text := "" } cycle ≠ .unknown := by
  cases vectorRead : readParsedMatrixMAUSourceAtMAB state coordinate vectorSource
      format (parsedMatrixMAUVectorLanesPerPE precision) cycle with
  | failure => simp [executeParsedMatrixMAUCalculationAtMAB, formatLowered, vectorRead]
  | unknown => exact (vectorReadKnown vectorRead).elim
  | ok vectorValues =>
      cases accumulatorRead : readParsedMatrixMAUSourceAtMAB state coordinate
          accumulatorSource (parsedMatrixMAUAccumulatorFormat precision)
          (parsedMatrixMAUAccumulatorLanesPerPE precision) cycle with
      | failure => simp [executeParsedMatrixMAUCalculationAtMAB, formatLowered,
          vectorRead, accumulatorRead]
      | unknown => exact (accumulatorReadKnown accumulatorRead).elim
      | ok accumulatorValues =>
          cases calculation : parsedMatrixMAUCalculateRows?
              (state.matrixRegisters coordinate.group coordinate.l2b coordinate.l1b)
              coordinate sideY precision .fma half round vectorValues accumulatorValues with
          | none => simp [executeParsedMatrixMAUCalculationAtMAB, formatLowered,
              vectorRead, accumulatorRead, calculation]
          | some rows => simp [executeParsedMatrixMAUCalculationAtMAB, formatLowered,
              vectorRead, accumulatorRead, calculation]

theorem executeParsedMatrixMAUCalculationAtMAB_missing_matrix_operand_fails
    (state : State) (coordinate : MABCoordinate) (cycle : Fin 4)
    (precision : ParsedPrecision) (kind : CalcKind) (half : Option Char)
    (round : Bool) :
    executeParsedMatrixMAUCalculationAtMAB state coordinate
      { op := .mau precision true kind half round
        sources := []
        destinations := []
        flush := none
        text := "" } cycle = .failure := by
  simp [executeParsedMatrixMAUCalculationAtMAB]

theorem executeParsedMatrixMAUCalculationAtMAB_wrong_matrix_operand_fails
    (state : State) (coordinate : MABCoordinate) (cycle : Fin 4)
    (precision : ParsedPrecision) (kind : CalcKind) (half : Option Char)
    (round : Bool) :
    executeParsedMatrixMAUCalculationAtMAB state coordinate
      { op := .mau precision true kind half round
        sources := [.fixed .peid]
        destinations := []
        flush := none
        text := "" } cycle = .failure := by
  simp [executeParsedMatrixMAUCalculationAtMAB]

theorem executeParsedMatrixMAUCalculationAtMAB_row_selected_matrix_operand_fails
    (state : State) (coordinate : MABCoordinate) (cycle : Fin 4)
    (precision : ParsedPrecision) (kind : CalcKind) (half : Option Char)
    (round : Bool) (row : Fin (2 ^ 32)) :
    executeParsedMatrixMAUCalculationAtMAB state coordinate
      { op := .mau precision true kind half round
        sources := [.matrix false ⟨2, by decide⟩ (some row)]
        destinations := []
        flush := none
        text := "" } cycle = .failure := by
  simp [executeParsedMatrixMAUCalculationAtMAB]

theorem executeParsedMatrixMAUCalculationAtMAB_missing_vector_operand_fails
    (state : State) (coordinate : MABCoordinate) (cycle : Fin 4)
    (precision : ParsedPrecision) (kind : CalcKind) (half : Option Char)
    (round : Bool) :
    executeParsedMatrixMAUCalculationAtMAB state coordinate
      { op := .mau precision true kind half round
        sources := [.matrix false ⟨2, by decide⟩ none]
        destinations := []
        flush := none
        text := "" } cycle = .failure := by
  cases kind <;> simp [executeParsedMatrixMAUCalculationAtMAB]

theorem executeParsedMatrixMAUCalculationAtMAB_missing_accumulator_operand_fails
    (state : State) (coordinate : MABCoordinate) (cycle : Fin 4)
    (precision : ParsedPrecision) (half : Option Char) (round : Bool) :
    executeParsedMatrixMAUCalculationAtMAB state coordinate
      { op := .mau precision true .fma half round
        sources := [.matrix false ⟨2, by decide⟩ none, .fixed .peid]
        destinations := []
        flush := none
        text := "" } cycle = .failure := by
  simp [executeParsedMatrixMAUCalculationAtMAB]

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

def parsedMatrixMAUPackOutputs (precision : ParsedPrecision) (round flagsUnavailable : Bool)
    (rows : List Nat) (poison : Bool) :
    List (Fin 4) → (Fin 4 → IntegerALU.Bus) → (Fin 4 → BitVec 4) →
      ProofsLean.StepResult ((Fin 4 → IntegerALU.Bus) × (Fin 4 → BitVec 4) × Bool)
  | [], buses, flags => .ok (buses, flags, poison)
  | pe :: rest, buses, flags =>
      match parsedMatrixMAUPEOutput? precision round rows pe with
      | none => .failure
      | some (bus, flag) =>
          parsedMatrixMAUPackOutputs precision round flagsUnavailable rows poison rest
            (fun index => if index == pe then bus else buses index)
            (fun index => if index == pe then
              (if flagsUnavailable then 0 else flag) else flags index)

theorem parsedMatrixMAUPackOutputs_never_unknown
    (precision : ParsedPrecision) (round flagsUnavailable : Bool) (rows : List Nat)
    (poison : Bool) (pes : List (Fin 4)) (buses : Fin 4 → IntegerALU.Bus)
    (flags : Fin 4 → BitVec 4) :
    parsedMatrixMAUPackOutputs precision round flagsUnavailable rows poison pes buses flags ≠
      .unknown := by
  induction pes generalizing buses flags with
  | nil => simp [parsedMatrixMAUPackOutputs]
  | cons pe rest ih =>
      cases packed : parsedMatrixMAUPEOutput? precision round rows pe with
      | none => simp [parsedMatrixMAUPackOutputs, packed]
      | some output =>
          cases output with
          | mk bus flag =>
              simp only [parsedMatrixMAUPackOutputs, packed]
              exact ih
                (fun index => if index == pe then bus else buses index)
                (fun index => if index == pe then
                  (if flagsUnavailable then 0 else flag) else flags index)

def executeParsedMatrixMAUAtMAB (state : State) (coordinate : MABCoordinate)
    (expression : ParsedExpr) (cycle : Fin 4) :
    ProofsLean.StepResult ((Fin 4 → IntegerALU.Bus) × (Fin 4 → BitVec 4) × Bool) :=
  match executeParsedMatrixMAUCalculationAtMAB state coordinate expression cycle with
  | .failure => .failure
  | .unknown => .unknown
  | .ok (rows, poison, flagsUnavailable) =>
      match expression.op with
      | .mau precision true _ _ round =>
          parsedMatrixMAUPackOutputs precision round flagsUnavailable rows poison
            (List.finRange 4) (fun _ => ⟨0, 0⟩) (fun _ => 0)
      | _ => .unknown

theorem executeParsedMatrixMAUAtMAB_calculation_known_never_unknown
    (state : State) (coordinate : MABCoordinate) (expression : ParsedExpr) (cycle : Fin 4)
    (calculationKnown : executeParsedMatrixMAUCalculationAtMAB state coordinate
      expression cycle ≠ .unknown)
    (matrixMAUOp : ∃ precision kind half round,
      expression.op = .mau precision true kind half round) :
    executeParsedMatrixMAUAtMAB state coordinate expression cycle ≠ .unknown := by
  cases expression with
  | mk op sources destinations flush text =>
      cases calculated : executeParsedMatrixMAUCalculationAtMAB state coordinate
          { op := op, sources := sources, destinations := destinations,
            flush := flush, text := text } cycle with
      | failure => simp [executeParsedMatrixMAUAtMAB, calculated]
      | unknown => exact (calculationKnown calculated).elim
      | ok result =>
          rcases matrixMAUOp with ⟨precision, kind, half, round, opEq⟩
          change op = .mau precision true kind half round at opEq
          subst op
          rcases result with ⟨rows, poison, flagsUnavailable⟩
          simpa [executeParsedMatrixMAUAtMAB, calculated] using
            parsedMatrixMAUPackOutputs_never_unknown precision round flagsUnavailable
              rows poison (List.finRange 4) (fun _ => ⟨0, 0⟩) (fun _ => 0)


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
  | none => .failure

theorem rawL1Mwrite_fixed_source_is_failure
    (fixed : ParsedFixed) (context : ParsedIntegerContext) :
    rawL1MwriteSourceResult (.fixed fixed) context = .failure := by
  rfl

theorem rawL1Mwrite_invalid_memory_source_is_failure
    (access : Access) (context : ParsedIntegerContext)
    (loweringFails : ParsedOperand.toParsedIntegerInput?
      (.mem access false false false none) .long context.group context.l2b
      context.l1b context.mab context.pe context.cycle context.bar0 context.bar1
      context.tWord = none) :
    rawL1MwriteSourceResult (.mem access false false false none) context = .failure := by
  simp [rawL1MwriteSourceResult, rawL1MwriteSource?, loweringFails]

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

theorem readRawL1MwriteBus_memory_never_unknown
    (state : State) (access : Access) (negated extended rounded : Bool)
    (mask : Option ParsedMask) (pe : PEId) (cycle : Fin 4) :
    readRawL1MwriteBus state (.mem access negated extended rounded mask) pe cycle ≠
      .unknown := by
  cases h : ParsedOperand.toDirectMemoryAccess?
      (.mem access false false false none) (ParsedIntegerContext.ofLinearIndex pe).pe cycle
      (state.peContext pe).bar0 (state.peContext pe).bar1
      (state.peContext pe).tWord with
  | none =>
      simp [readRawL1MwriteBus, rawL1MwriteSourceResult, rawL1MwriteSource?,
        ParsedOperand.toParsedIntegerInput?, h]
  | some resolved =>
      simp [readRawL1MwriteBus, rawL1MwriteSourceResult, rawL1MwriteSource?,
        ParsedOperand.toParsedIntegerInput?, h, ParsedIntegerInput.readWithForwarding,
        ParsedIntegerInput.read]

theorem readRawL1MwriteBus_forward_never_unknown
    (state : State) (kind : ParsedForward) (negated extended rounded : Bool)
    (pe : PEId) (cycle : Fin 4)
    (resolved : state.forwardingValid pe (ParsedIntegerInput.forwardUnit kind) cycle = false ∨
      stateForwardingSlots state pe (ParsedIntegerInput.forwardUnit kind) cycle ≠ .unknown) :
    readRawL1MwriteBus state (.forward kind negated extended rounded) pe cycle ≠
      .unknown := by
  cases valid : state.forwardingValid pe (ParsedIntegerInput.forwardUnit kind) cycle with
  | false =>
      simp [readRawL1MwriteBus, rawL1MwriteSourceResult, rawL1MwriteSource?,
        ParsedOperand.toParsedIntegerInput?, valid]
  | true =>
      have slotResolved :
          stateForwardingSlots state pe (ParsedIntegerInput.forwardUnit kind) cycle ≠
            .unknown := by
        rcases resolved with invalid | slotResolved
        · simp [valid] at invalid
        · exact slotResolved
      cases slot : stateForwardingSlots state pe
          (ParsedIntegerInput.forwardUnit kind) cycle with
      | known bus =>
          simp [readRawL1MwriteBus, rawL1MwriteSourceResult, rawL1MwriteSource?,
            ParsedOperand.toParsedIntegerInput?, ParsedIntegerInput.readWithForwarding,
            valid, slot]
      | poison =>
          simp [readRawL1MwriteBus, rawL1MwriteSourceResult, rawL1MwriteSource?,
            ParsedOperand.toParsedIntegerInput?, ParsedIntegerInput.readWithForwarding,
            valid, slot]
      | unknown => exact (slotResolved slot).elim

def forwardingSourceResolved (state : State) : Prop :=
  ∀ pe unit cycle,
    state.forwardingValid pe unit cycle = false ∨
      stateForwardingSlots state pe unit cycle ≠ .unknown

theorem readParsedMatrixMAUSourcePE_lowering_miss_fails
    (state : State) (coordinate : MABCoordinate) (operand : ParsedOperand)
    (precision : RRN.FloatPrecision) (count : Nat) (pe cycle : Fin 4)
    (lowered : parsedFloatMAUSourceAttrs? operand
      ({ ParsedIntegerContext.ofLinearIndex (physicalPEId coordinate pe) with
        cycle := cycle
        bar0 := (state.peContext (physicalPEId coordinate pe)).bar0
        bar1 := (state.peContext (physicalPEId coordinate pe)).bar1
        tWord := (state.peContext (physicalPEId coordinate pe)).tWord }) = none) :
    readParsedMatrixMAUSourcePE state coordinate operand precision count pe cycle =
      .failure := by
  simp [readParsedMatrixMAUSourcePE, lowered]

theorem readParsedMatrixMAUSourcePE_resolved_never_unknown
    (state : State) (coordinate : MABCoordinate) (operand : ParsedOperand)
    (precision : RRN.FloatPrecision) (count : Nat) (pe cycle : Fin 4)
    (attrs : (∃ access rounded negate extend round,
      parsedFloatMAUSourceAttrs? operand
        ({ ParsedIntegerContext.ofLinearIndex (physicalPEId coordinate pe) with
          cycle := cycle
          bar0 := (state.peContext (physicalPEId coordinate pe)).bar0
          bar1 := (state.peContext (physicalPEId coordinate pe)).bar1
          tWord := (state.peContext (physicalPEId coordinate pe)).tWord }) =
        some (.memory access rounded, negate, extend, round)) ∨
      (∃ kind rounded negate extend round,
        parsedFloatMAUSourceAttrs? operand
          ({ ParsedIntegerContext.ofLinearIndex (physicalPEId coordinate pe) with
            cycle := cycle
            bar0 := (state.peContext (physicalPEId coordinate pe)).bar0
            bar1 := (state.peContext (physicalPEId coordinate pe)).bar1
            tWord := (state.peContext (physicalPEId coordinate pe)).tWord }) =
          some (.forward kind rounded, negate, extend, round)))
    (resolved : forwardingSourceResolved state) :
    readParsedMatrixMAUSourcePE state coordinate operand precision count pe cycle ≠
      .unknown := by
  rcases attrs with
    ⟨access, rounded, negate, extend, round, lowered⟩ |
    ⟨kind, rounded, negate, extend, round, lowered⟩
  · simp only [readParsedMatrixMAUSourcePE, lowered,
      ParsedIntegerInput.readWithForwarding, ParsedIntegerInput.read]
    cases decode : parsedMatrixMAUDecodeLanes? precision count
        (ParsedIntegerInput.applyRounding rounded
          (pack (readDirectAccess (state.peRegisters (physicalPEId coordinate pe)) access)))
        negate extend round <;> simp [decode]
  · by_cases valid : state.forwardingValid (physicalPEId coordinate pe)
        (ParsedIntegerInput.forwardUnit kind) cycle
    · cases slot : state.forwarding (physicalPEId coordinate pe)
          (ParsedIntegerInput.forwardUnit kind) cycle with
      | known bus =>
          simp only [readParsedMatrixMAUSourcePE, lowered, valid, slot,
            ParsedIntegerInput.readWithForwarding]
          cases decode : parsedMatrixMAUDecodeLanes? precision count
              (ParsedIntegerInput.applyRounding rounded bus) negate extend round <;>
            simp [decode]
      | poison =>
          simp [readParsedMatrixMAUSourcePE, lowered, valid, slot,
            ParsedIntegerInput.readWithForwarding]
      | unknown =>
          have slotResolved := resolved (physicalPEId coordinate pe)
            (ParsedIntegerInput.forwardUnit kind) cycle
          rw [stateForwardingSlots_valid_preserves_payload state
            (physicalPEId coordinate pe) (ParsedIntegerInput.forwardUnit kind)
            cycle valid] at slotResolved
          rcases slotResolved with invalid | notUnknown
          · simp [valid] at invalid
          · exact (notUnknown slot).elim
    · simp [readParsedMatrixMAUSourcePE, lowered, valid,
        ParsedIntegerInput.readWithForwarding]

theorem readParsedMatrixMAUSourcePEsAux_resolved_never_unknown
    (state : State) (coordinate : MABCoordinate) (operand : ParsedOperand)
    (precision : RRN.FloatPrecision) (count : Nat) (cycle : Fin 4)
    (pes : List (Fin 4)) (initial : List Nat)
    (attrs : ∀ pe ∈ pes,
      (∃ access rounded negate extend round,
        parsedFloatMAUSourceAttrs? operand
          ({ ParsedIntegerContext.ofLinearIndex (physicalPEId coordinate pe) with
            cycle := cycle
            bar0 := (state.peContext (physicalPEId coordinate pe)).bar0
            bar1 := (state.peContext (physicalPEId coordinate pe)).bar1
            tWord := (state.peContext (physicalPEId coordinate pe)).tWord }) =
          some (.memory access rounded, negate, extend, round)) ∨
      (∃ kind rounded negate extend round,
        parsedFloatMAUSourceAttrs? operand
          ({ ParsedIntegerContext.ofLinearIndex (physicalPEId coordinate pe) with
            cycle := cycle
            bar0 := (state.peContext (physicalPEId coordinate pe)).bar0
            bar1 := (state.peContext (physicalPEId coordinate pe)).bar1
            tWord := (state.peContext (physicalPEId coordinate pe)).tWord }) =
          some (.forward kind rounded, negate, extend, round)))
    (resolved : forwardingSourceResolved state) :
    readParsedMatrixMAUSourcePEsAux state coordinate operand precision count cycle pes initial ≠
      .unknown := by
  induction pes generalizing initial with
  | nil => simp [readParsedMatrixMAUSourcePEsAux]
  | cons pe rest ih =>
      have headKnown := readParsedMatrixMAUSourcePE_resolved_never_unknown
        state coordinate operand precision count pe cycle (attrs pe (by simp)) resolved
      have tailAttrs : ∀ item ∈ rest,
          (∃ access rounded negate extend round,
            parsedFloatMAUSourceAttrs? operand
              ({ ParsedIntegerContext.ofLinearIndex (physicalPEId coordinate item) with
                cycle := cycle
                bar0 := (state.peContext (physicalPEId coordinate item)).bar0
                bar1 := (state.peContext (physicalPEId coordinate item)).bar1
                tWord := (state.peContext (physicalPEId coordinate item)).tWord }) =
              some (.memory access rounded, negate, extend, round)) ∨
          (∃ kind rounded negate extend round,
            parsedFloatMAUSourceAttrs? operand
              ({ ParsedIntegerContext.ofLinearIndex (physicalPEId coordinate item) with
                cycle := cycle
                bar0 := (state.peContext (physicalPEId coordinate item)).bar0
                bar1 := (state.peContext (physicalPEId coordinate item)).bar1
                tWord := (state.peContext (physicalPEId coordinate item)).tWord }) =
              some (.forward kind rounded, negate, extend, round)) := by
        intro item member
        exact attrs item (List.mem_cons_of_mem _ member)
      cases head : readParsedMatrixMAUSourcePE state coordinate operand precision count pe cycle with
      | failure => simp [readParsedMatrixMAUSourcePEsAux, head]
      | unknown =>
          simp only [readParsedMatrixMAUSourcePEsAux, head]
          exact False.elim (headKnown head)
      | ok lanes =>
          cases tail : readParsedMatrixMAUSourcePEsAux state coordinate operand
              precision count cycle rest (initial ++ lanes) with
          | failure =>
              simp [readParsedMatrixMAUSourcePEsAux, head, tail]
          | unknown =>
              simp only [readParsedMatrixMAUSourcePEsAux, head, tail]
              exact False.elim ((ih (initial ++ lanes) tailAttrs) tail)
          | ok values =>
              simp [readParsedMatrixMAUSourcePEsAux, head, tail]

theorem readParsedMatrixMAUSourcePEs_resolved_never_unknown
    (state : State) (coordinate : MABCoordinate) (operand : ParsedOperand)
    (precision : RRN.FloatPrecision) (count : Nat) (cycle : Fin 4)
    (pes : List (Fin 4))
    (attrs : ∀ pe ∈ pes,
      (∃ access rounded negate extend round,
        parsedFloatMAUSourceAttrs? operand
          ({ ParsedIntegerContext.ofLinearIndex (physicalPEId coordinate pe) with
            cycle := cycle
            bar0 := (state.peContext (physicalPEId coordinate pe)).bar0
            bar1 := (state.peContext (physicalPEId coordinate pe)).bar1
            tWord := (state.peContext (physicalPEId coordinate pe)).tWord }) =
          some (.memory access rounded, negate, extend, round)) ∨
      (∃ kind rounded negate extend round,
        parsedFloatMAUSourceAttrs? operand
          ({ ParsedIntegerContext.ofLinearIndex (physicalPEId coordinate pe) with
            cycle := cycle
            bar0 := (state.peContext (physicalPEId coordinate pe)).bar0
            bar1 := (state.peContext (physicalPEId coordinate pe)).bar1
            tWord := (state.peContext (physicalPEId coordinate pe)).tWord }) =
          some (.forward kind rounded, negate, extend, round)))
    (resolved : forwardingSourceResolved state) :
    readParsedMatrixMAUSourcePEs state coordinate operand precision count cycle pes ≠
      .unknown := by
  simpa [readParsedMatrixMAUSourcePEs] using
    readParsedMatrixMAUSourcePEsAux_resolved_never_unknown state coordinate operand
      precision count cycle pes [] attrs resolved

theorem readParsedMatrixMAUSourceAtMAB_resolved_never_unknown
    (state : State) (coordinate : MABCoordinate) (operand : ParsedOperand)
    (precision : RRN.FloatPrecision) (count : Nat) (cycle : Fin 4)
    (attrs : ∀ pe : Fin 4,
      (∃ access rounded negate extend round,
        parsedFloatMAUSourceAttrs? operand
          ({ ParsedIntegerContext.ofLinearIndex (physicalPEId coordinate pe) with
            cycle := cycle
            bar0 := (state.peContext (physicalPEId coordinate pe)).bar0
            bar1 := (state.peContext (physicalPEId coordinate pe)).bar1
            tWord := (state.peContext (physicalPEId coordinate pe)).tWord }) =
          some (.memory access rounded, negate, extend, round)) ∨
      (∃ kind rounded negate extend round,
        parsedFloatMAUSourceAttrs? operand
          ({ ParsedIntegerContext.ofLinearIndex (physicalPEId coordinate pe) with
            cycle := cycle
            bar0 := (state.peContext (physicalPEId coordinate pe)).bar0
            bar1 := (state.peContext (physicalPEId coordinate pe)).bar1
            tWord := (state.peContext (physicalPEId coordinate pe)).tWord }) =
          some (.forward kind rounded, negate, extend, round)))
    (resolved : forwardingSourceResolved state) :
    readParsedMatrixMAUSourceAtMAB state coordinate operand precision count cycle ≠
      .unknown := by
  simpa [readParsedMatrixMAUSourceAtMAB] using
    readParsedMatrixMAUSourcePEs_resolved_never_unknown state coordinate operand
      precision count cycle (List.finRange 4) (by
        intro pe _
        exact attrs pe) resolved

def parsedFloatMAUSourceLoweredAtMAB (state : State) (coordinate : MABCoordinate)
    (operand : ParsedOperand) (cycle : Fin 4) : Prop :=
  ∀ pe : Fin 4,
    (∃ access rounded negate extend round,
      parsedFloatMAUSourceAttrs? operand
        ({ ParsedIntegerContext.ofLinearIndex (physicalPEId coordinate pe) with
          cycle := cycle
          bar0 := (state.peContext (physicalPEId coordinate pe)).bar0
          bar1 := (state.peContext (physicalPEId coordinate pe)).bar1
          tWord := (state.peContext (physicalPEId coordinate pe)).tWord }) =
        some (.memory access rounded, negate, extend, round)) ∨
    (∃ kind rounded negate extend round,
      parsedFloatMAUSourceAttrs? operand
        ({ ParsedIntegerContext.ofLinearIndex (physicalPEId coordinate pe) with
          cycle := cycle
          bar0 := (state.peContext (physicalPEId coordinate pe)).bar0
          bar1 := (state.peContext (physicalPEId coordinate pe)).bar1
          tWord := (state.peContext (physicalPEId coordinate pe)).tWord }) =
        some (.forward kind rounded, negate, extend, round))

theorem executeParsedMatrixMAUCalculationAtMAB_mul_lowered_reads_never_unknown
    (state : State) (coordinate : MABCoordinate) (precision : ParsedPrecision)
    (half : Option Char) (round : Bool) (sideY : Bool) (width : Fin 5)
    (source : ParsedOperand) (cycle : Fin 4) (format : RRN.FloatPrecision)
    (formatLowered : parsedMatrixMAUFloatFormat precision = some format)
    (lowered : parsedFloatMAUSourceLoweredAtMAB state coordinate source cycle)
    (resolved : forwardingSourceResolved state) :
    executeParsedMatrixMAUCalculationAtMAB state coordinate
      { op := .mau precision true .mul half round
        sources := [.matrix sideY width none, source]
        destinations := []
        flush := none
        text := "" } cycle ≠ .unknown := by
  apply executeParsedMatrixMAUCalculationAtMAB_mul_read_known_never_unknown
    state coordinate precision half round sideY width source cycle format formatLowered
  exact readParsedMatrixMAUSourceAtMAB_resolved_never_unknown
    state coordinate source format (parsedMatrixMAUVectorLanesPerPE precision) cycle
    lowered resolved

theorem executeParsedMatrixMAUCalculationAtMAB_add_lowered_reads_never_unknown
    (state : State) (coordinate : MABCoordinate) (precision : ParsedPrecision)
    (half : Option Char) (round : Bool) (sideY : Bool) (width : Fin 5)
    (source : ParsedOperand) (cycle : Fin 4) (format : RRN.FloatPrecision)
    (formatLowered : parsedMatrixMAUFloatFormat precision = some format)
    (lowered : parsedFloatMAUSourceLoweredAtMAB state coordinate source cycle)
    (resolved : forwardingSourceResolved state) :
    executeParsedMatrixMAUCalculationAtMAB state coordinate
      { op := .mau precision true .add half round
        sources := [.matrix sideY width none, source]
        destinations := []
        flush := none
        text := "" } cycle ≠ .unknown := by
  apply executeParsedMatrixMAUCalculationAtMAB_add_read_known_never_unknown
    state coordinate precision half round sideY width source cycle format formatLowered
  exact readParsedMatrixMAUSourceAtMAB_resolved_never_unknown
    state coordinate source format (parsedMatrixMAUVectorLanesPerPE precision) cycle
    lowered resolved

theorem executeParsedMatrixMAUCalculationAtMAB_passa_lowered_reads_never_unknown
    (state : State) (coordinate : MABCoordinate) (precision : ParsedPrecision)
    (half : Option Char) (round : Bool) (sideY : Bool) (width : Fin 5)
    (source : ParsedOperand) (cycle : Fin 4) (format : RRN.FloatPrecision)
    (formatLowered : parsedMatrixMAUFloatFormat precision = some format)
    (lowered : parsedFloatMAUSourceLoweredAtMAB state coordinate source cycle)
    (resolved : forwardingSourceResolved state) :
    executeParsedMatrixMAUCalculationAtMAB state coordinate
      { op := .mau precision true .passa half round
        sources := [.matrix sideY width none, source]
        destinations := []
        flush := none
        text := "" } cycle ≠ .unknown := by
  apply executeParsedMatrixMAUCalculationAtMAB_passa_read_known_never_unknown
    state coordinate precision half round sideY width source cycle format formatLowered
  exact readParsedMatrixMAUSourceAtMAB_resolved_never_unknown
    state coordinate source format (parsedMatrixMAUVectorLanesPerPE precision) cycle
    lowered resolved

theorem executeParsedMatrixMAUCalculationAtMAB_fma_lowered_reads_never_unknown
    (state : State) (coordinate : MABCoordinate) (precision : ParsedPrecision)
    (half : Option Char) (round : Bool) (sideY : Bool) (width : Fin 5)
    (vectorSource accumulatorSource : ParsedOperand) (cycle : Fin 4)
    (format : RRN.FloatPrecision)
    (formatLowered : parsedMatrixMAUFloatFormat precision = some format)
    (vectorLowered : parsedFloatMAUSourceLoweredAtMAB state coordinate vectorSource cycle)
    (accumulatorLowered : parsedFloatMAUSourceLoweredAtMAB state coordinate accumulatorSource cycle)
    (resolved : forwardingSourceResolved state) :
    executeParsedMatrixMAUCalculationAtMAB state coordinate
      { op := .mau precision true .fma half round
        sources := [.matrix sideY width none, vectorSource, accumulatorSource]
        destinations := []
        flush := none
        text := "" } cycle ≠ .unknown := by
  apply executeParsedMatrixMAUCalculationAtMAB_fma_reads_known_never_unknown
    state coordinate precision half round sideY width vectorSource accumulatorSource cycle
    format formatLowered
  · exact readParsedMatrixMAUSourceAtMAB_resolved_never_unknown
      state coordinate vectorSource format (parsedMatrixMAUVectorLanesPerPE precision)
      cycle vectorLowered resolved
  · exact readParsedMatrixMAUSourceAtMAB_resolved_never_unknown
      state coordinate accumulatorSource (parsedMatrixMAUAccumulatorFormat precision)
      (parsedMatrixMAUAccumulatorLanesPerPE precision) cycle accumulatorLowered resolved

theorem readRawL1MwriteBus_resolved_never_unknown
    (state : State) (source : ParsedOperand) (pe : PEId) (cycle : Fin 4)
    (resolved : forwardingSourceResolved state) :
    readRawL1MwriteBus state source pe cycle ≠ .unknown := by
  cases source with
  | mem access negated extended rounded mask =>
      exact readRawL1MwriteBus_memory_never_unknown state access negated extended
        rounded mask pe cycle
  | forward kind negated extended rounded =>
      exact readRawL1MwriteBus_forward_never_unknown state kind negated extended
        rounded pe cycle (resolved pe (ParsedIntegerInput.forwardUnit kind) cycle)
  | bar lm1 width mask =>
      simp [readRawL1MwriteBus, rawL1MwriteSourceResult, rawL1MwriteSource?]
  | fixed kind =>
      simp [readRawL1MwriteBus, rawL1MwriteSourceResult, rawL1MwriteSource?]
  | omr entry mask =>
      simp [readRawL1MwriteBus, rawL1MwriteSourceResult, rawL1MwriteSource?]
  | matrix y width row =>
      simp [readRawL1MwriteBus, rawL1MwriteSourceResult, rawL1MwriteSource?]
  | nowrite =>
      simp [readRawL1MwriteBus, rawL1MwriteSourceResult, rawL1MwriteSource?]
  | l1bm width address =>
      simp [readRawL1MwriteBus, rawL1MwriteSourceResult, rawL1MwriteSource?]
  | l2bm address l2b =>
      simp [readRawL1MwriteBus, rawL1MwriteSourceResult, rawL1MwriteSource?]
  | dar address =>
      simp [readRawL1MwriteBus, rawL1MwriteSourceResult, rawL1MwriteSource?]

def readL1MwritePEList (state : State) (source : ParsedOperand)
    (coordinate : MABCoordinate) (cycle : Fin 4) :
    List (Fin 4) → (Fin 4 → IntegerALU.Bus) →
      ProofsLean.StepResult (Fin 4 → IntegerALU.Bus)
    | [], buses => .ok buses
    | pe :: rest, buses =>
        match readRawL1MwriteBus state source
            (physicalPEId coordinate pe) cycle with
        | .failure => .failure
        | .unknown => .unknown
        | .ok bus => readL1MwritePEList state source coordinate cycle rest
            (fun index => if index = pe then bus else buses index)

theorem readL1MwritePEList_direct_memory_never_unknown
    (state : State) (access : Access) (negated extended rounded : Bool)
    (mask : Option ParsedMask) (coordinate : MABCoordinate) (cycle : Fin 4)
    (pes : List (Fin 4)) (buses : Fin 4 → IntegerALU.Bus) :
    readL1MwritePEList state (.mem access negated extended rounded mask)
      coordinate cycle pes buses ≠ .unknown := by
  induction pes generalizing buses with
  | nil => simp [readL1MwritePEList]
  | cons pe rest ih =>
      simp only [readL1MwritePEList]
      cases result : readRawL1MwriteBus state
          (.mem access negated extended rounded mask)
          (physicalPEId coordinate pe) cycle with
      | failure => simp [result]
      | unknown =>
          exact (readRawL1MwriteBus_memory_never_unknown state access negated
            extended rounded mask (physicalPEId coordinate pe) cycle result).elim
      | ok bus =>
          simp only [result]
          exact ih (fun index => if index = pe then bus else buses index)

theorem readL1MwritePEList_resolved_forward_never_unknown
    (state : State) (kind : ParsedForward) (negated extended rounded : Bool)
    (coordinate : MABCoordinate) (cycle : Fin 4) (pes : List (Fin 4))
    (buses : Fin 4 → IntegerALU.Bus)
    (resolved : ∀ pe ∈ pes,
      state.forwardingValid (physicalPEId coordinate pe)
        (ParsedIntegerInput.forwardUnit kind) cycle = false ∨
      stateForwardingSlots state (physicalPEId coordinate pe)
        (ParsedIntegerInput.forwardUnit kind) cycle ≠ .unknown) :
    readL1MwritePEList state (.forward kind negated extended rounded)
      coordinate cycle pes buses ≠ .unknown := by
  induction pes generalizing buses with
  | nil => simp [readL1MwritePEList]
  | cons pe rest ih =>
      simp only [readL1MwritePEList]
      cases result : readRawL1MwriteBus state
          (.forward kind negated extended rounded)
          (physicalPEId coordinate pe) cycle with
      | failure => simp [result]
      | unknown =>
          have headResolved := resolved pe (by simp)
          exact (readRawL1MwriteBus_forward_never_unknown state kind negated extended
            rounded (physicalPEId coordinate pe) cycle headResolved result).elim
      | ok bus =>
          simp only [result]
          apply ih
          intro next member
          exact resolved next (by simp [member])

theorem readL1MwritePEList_resolved_source_never_unknown
    (state : State) (source : ParsedOperand) (coordinate : MABCoordinate)
    (cycle : Fin 4) (pes : List (Fin 4)) (buses : Fin 4 → IntegerALU.Bus)
    (resolved : forwardingSourceResolved state) :
    readL1MwritePEList state source coordinate cycle pes buses ≠ .unknown := by
  induction pes generalizing buses with
  | nil => simp [readL1MwritePEList]
  | cons pe rest ih =>
      simp only [readL1MwritePEList]
      cases result : readRawL1MwriteBus state source
          (physicalPEId coordinate pe) cycle with
      | failure => simp [result]
      | unknown =>
          exact (readRawL1MwriteBus_resolved_never_unknown state source
            (physicalPEId coordinate pe) cycle resolved result).elim
      | ok bus =>
          simp only [result]
          exact ih (fun index => if index = pe then bus else buses index)

def readL1MwriteBusesAtBank (state : State) (access : ParsedL1MwriteAccess)
    (bank : Fin 64) (mab : Fin 16) (cycle : Fin 4) :
    ProofsLean.StepResult (Fin 4 → IntegerALU.Bus) :=
  let coordinate : MABCoordinate :=
    ⟨⟨bank.val / 16, by have h := bank.isLt; omega⟩,
      ⟨bank.val / 8 % 2, by have h := bank.isLt; omega⟩,
      ⟨bank.val % 8, by have h := bank.isLt; omega⟩, mab⟩
  readL1MwritePEList state access.source coordinate cycle
    (List.finRange 4) (fun _ => ⟨0, 0⟩)

theorem readL1MwriteBusesAtBank_direct_memory_never_unknown
    (state : State) (access : ParsedL1MwriteAccess)
    (operandAccess : Access) (negated extended rounded : Bool)
    (mask : Option ParsedMask) (bank : Fin 64) (mab : Fin 16) (cycle : Fin 4)
    (source : access.source = .mem operandAccess negated extended rounded mask) :
    readL1MwriteBusesAtBank state access bank mab cycle ≠ .unknown := by
  simp only [readL1MwriteBusesAtBank, source]
  exact readL1MwritePEList_direct_memory_never_unknown state operandAccess
    negated extended rounded mask
    ⟨⟨bank.val / 16, by have h := bank.isLt; omega⟩,
      ⟨bank.val / 8 % 2, by have h := bank.isLt; omega⟩,
      ⟨bank.val % 8, by have h := bank.isLt; omega⟩, mab⟩
    cycle (List.finRange 4) (fun _ => ⟨0, 0⟩)

theorem readL1MwriteBusesAtBank_resolved_forward_never_unknown
    (state : State) (access : ParsedL1MwriteAccess) (kind : ParsedForward)
    (negated extended rounded : Bool) (bank : Fin 64) (mab : Fin 16)
    (cycle : Fin 4)
    (resolved : ∀ pe : PEId,
      state.forwardingValid pe (ParsedIntegerInput.forwardUnit kind) cycle = false ∨
      stateForwardingSlots state pe (ParsedIntegerInput.forwardUnit kind) cycle ≠ .unknown)
    (source : access.source = .forward kind negated extended rounded) :
    readL1MwriteBusesAtBank state access bank mab cycle ≠ .unknown := by
  simp only [readL1MwriteBusesAtBank, source]
  apply readL1MwritePEList_resolved_forward_never_unknown
  intro pe member
  exact resolved (physicalPEId
    ⟨⟨bank.val / 16, by have h := bank.isLt; omega⟩,
      ⟨bank.val / 8 % 2, by have h := bank.isLt; omega⟩,
      ⟨bank.val % 8, by have h := bank.isLt; omega⟩, mab⟩ pe)

theorem readL1MwriteBusesAtBank_resolved_source_never_unknown
    (state : State) (access : ParsedL1MwriteAccess) (bank : Fin 64)
    (mab : Fin 16) (cycle : Fin 4)
    (resolved : forwardingSourceResolved state) :
    readL1MwriteBusesAtBank state access bank mab cycle ≠ .unknown := by
  simp only [readL1MwriteBusesAtBank]
  exact readL1MwritePEList_resolved_source_never_unknown state access.source
    ⟨⟨bank.val / 16, by have h := bank.isLt; omega⟩,
      ⟨bank.val / 8 % 2, by have h := bank.isLt; omega⟩,
      ⟨bank.val % 8, by have h := bank.isLt; omega⟩, mab⟩
    cycle (List.finRange 4) (fun _ => ⟨0, 0⟩) resolved

def readL1M4writeGroupList (state : State) (access : ParsedL1MwriteAccess)
    (bank : Fin 64) (cycle : Fin 4) :
    List (Fin 4) → (Fin 4 → Fin 4 → IntegerALU.Bus) →
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
            readL1M4writeGroupList state access bank cycle rest (fun nextGroup pe =>
              if nextGroup = group then groupBuses pe else buses nextGroup pe)

theorem readL1M4writeGroupList_direct_memory_never_unknown
    (state : State) (access : ParsedL1MwriteAccess)
    (operandAccess : Access) (negated extended rounded : Bool)
    (mask : Option ParsedMask) (bank : Fin 64) (cycle : Fin 4)
    (groups : List (Fin 4)) (buses : Fin 4 → Fin 4 → IntegerALU.Bus)
    (source : access.source = .mem operandAccess negated extended rounded mask) :
    readL1M4writeGroupList state access bank cycle groups buses ≠ .unknown := by
  induction groups generalizing buses with
  | nil => simp [readL1M4writeGroupList]
  | cons group rest ih =>
      simp only [readL1M4writeGroupList]
      cases result : readL1MwriteBusesAtBank state access bank
          ⟨group.val * 4 + access.mabGroup.val, by
            have hg := group.isLt
            have hm := access.mabGroup.isLt
            omega⟩ cycle with
      | failure => simp [result]
      | unknown =>
          exact (readL1MwriteBusesAtBank_direct_memory_never_unknown state access
            operandAccess negated extended rounded mask bank
            ⟨group.val * 4 + access.mabGroup.val, by
              have hg := group.isLt
              have hm := access.mabGroup.isLt
              omega⟩ cycle source result).elim
      | ok groupBuses =>
          simp only [result]
          exact ih (fun nextGroup pe =>
            if nextGroup = group then groupBuses pe else buses nextGroup pe)

def readL1M4writeBusesAtBank (state : State) (access : ParsedL1MwriteAccess)
    (bank : Fin 64) (cycle : Fin 4) :
    ProofsLean.StepResult (Fin 4 → Fin 4 → IntegerALU.Bus) :=
  readL1M4writeGroupList state access bank cycle (List.finRange 4)
    (fun _ _ => ⟨0, 0⟩)

theorem readL1M4writeBusesAtBank_direct_memory_never_unknown
    (state : State) (access : ParsedL1MwriteAccess)
    (operandAccess : Access) (negated extended rounded : Bool)
    (mask : Option ParsedMask) (bank : Fin 64) (cycle : Fin 4)
    (source : access.source = .mem operandAccess negated extended rounded mask) :
    readL1M4writeBusesAtBank state access bank cycle ≠ .unknown := by
  simpa [readL1M4writeBusesAtBank] using
    readL1M4writeGroupList_direct_memory_never_unknown state access operandAccess
      negated extended rounded mask bank cycle (List.finRange 4)
      (fun _ _ => ⟨0, 0⟩) source

theorem readL1M4writeGroupList_resolved_forward_never_unknown
    (state : State) (access : ParsedL1MwriteAccess) (kind : ParsedForward)
    (negated extended rounded : Bool) (bank : Fin 64) (cycle : Fin 4)
    (groups : List (Fin 4)) (buses : Fin 4 → Fin 4 → IntegerALU.Bus)
    (resolved : forwardingSourceResolved state)
    (source : access.source = .forward kind negated extended rounded) :
    readL1M4writeGroupList state access bank cycle groups buses ≠ .unknown := by
  induction groups generalizing buses with
  | nil => simp [readL1M4writeGroupList]
  | cons group rest ih =>
      simp only [readL1M4writeGroupList]
      let mab : Fin 16 := ⟨group.val * 4 + access.mabGroup.val, by
        have hg := group.isLt
        have hm := access.mabGroup.isLt
        omega⟩
      cases result : readL1MwriteBusesAtBank state access bank mab cycle with
      | failure => simp [result]
      | unknown =>
          exact (readL1MwriteBusesAtBank_resolved_forward_never_unknown state access
            kind negated extended rounded bank mab cycle
            (by
              intro pe
              exact resolved pe (ParsedIntegerInput.forwardUnit kind) cycle)
            source result).elim
      | ok groupBuses =>
          simp only [result]
          exact ih (fun nextGroup pe =>
            if nextGroup = group then groupBuses pe else buses nextGroup pe)

theorem readL1M4writeBusesAtBank_resolved_forward_never_unknown
    (state : State) (access : ParsedL1MwriteAccess) (kind : ParsedForward)
    (negated extended rounded : Bool) (bank : Fin 64) (cycle : Fin 4)
    (resolved : forwardingSourceResolved state)
    (source : access.source = .forward kind negated extended rounded) :
    readL1M4writeBusesAtBank state access bank cycle ≠ .unknown := by
  simpa [readL1M4writeBusesAtBank] using
    readL1M4writeGroupList_resolved_forward_never_unknown state access kind
      negated extended rounded bank cycle (List.finRange 4)
      (fun _ _ => ⟨0, 0⟩) resolved source

theorem readL1M4writeGroupList_resolved_source_never_unknown
    (state : State) (access : ParsedL1MwriteAccess) (bank : Fin 64)
    (cycle : Fin 4) (groups : List (Fin 4))
    (buses : Fin 4 → Fin 4 → IntegerALU.Bus)
    (resolved : forwardingSourceResolved state) :
    readL1M4writeGroupList state access bank cycle groups buses ≠ .unknown := by
  induction groups generalizing buses with
  | nil => simp [readL1M4writeGroupList]
  | cons group rest ih =>
      simp only [readL1M4writeGroupList]
      let mab : Fin 16 := ⟨group.val * 4 + access.mabGroup.val, by
        have hg := group.isLt
        have hm := access.mabGroup.isLt
        omega⟩
      cases result : readL1MwriteBusesAtBank state access bank mab cycle with
      | failure => simp [result]
      | unknown =>
          exact (readL1MwriteBusesAtBank_resolved_source_never_unknown state access
            bank mab cycle resolved result).elim
      | ok groupBuses =>
          simp only [result]
          exact ih (fun nextGroup pe =>
            if nextGroup = group then groupBuses pe else buses nextGroup pe)

theorem readL1M4writeBusesAtBank_resolved_source_never_unknown
    (state : State) (access : ParsedL1MwriteAccess) (bank : Fin 64)
    (cycle : Fin 4) (resolved : forwardingSourceResolved state) :
    readL1M4writeBusesAtBank state access bank cycle ≠ .unknown := by
  simpa [readL1M4writeBusesAtBank] using
    readL1M4writeGroupList_resolved_source_never_unknown state access bank cycle
      (List.finRange 4) (fun _ _ => ⟨0, 0⟩) resolved

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

def executeL1MwriteCycleList (readState : State) (access : ParsedL1MwriteAccess)
    (bank : Fin 64) (updateTurnaround : Bool) : List (Fin 4) →
      L1Transfer.L1Bank → L1Transfer.L1Turnaround → ProofsLean.StepResult
        (L1Transfer.L1Bank × L1Transfer.L1Turnaround)
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
          match readL1M4writeBusesAtBank readState access bank cycle with
          | .failure => .failure
          | .unknown => .unknown
          | .ok buses =>
              let next := writeM4Cycle buses
              executeL1MwriteCycleList readState access bank updateTurnaround rest
                next.1 next.2
        else
          match readL1MwriteBusesAtBank readState access bank access.selectedMab cycle with
          | .failure => .failure
          | .unknown => .unknown
          | .ok buses =>
              let next := writeCycle buses
              executeL1MwriteCycleList readState access bank updateTurnaround rest
                next.1 next.2

theorem executeL1MwriteCycleList_direct_memory_never_unknown
    (readState : State) (access : ParsedL1MwriteAccess) (bank : Fin 64)
    (updateTurnaround : Bool) (cycles : List (Fin 4))
    (memory : L1Transfer.L1Bank) (turnaround : L1Transfer.L1Turnaround)
    (operandAccess : Access) (negated extended rounded : Bool)
    (mask : Option ParsedMask)
    (source : access.source = .mem operandAccess negated extended rounded mask) :
    executeL1MwriteCycleList readState access bank updateTurnaround cycles memory
      turnaround ≠ .unknown := by
  induction cycles generalizing memory turnaround with
  | nil => simp [executeL1MwriteCycleList]
  | cons cycle rest ih =>
      simp only [executeL1MwriteCycleList]
      cases hFour : access.fourMabs with
      | true =>
          cases read : readL1M4writeBusesAtBank readState access bank cycle with
          | failure => simp [hFour, read]
          | unknown =>
              exact (readL1M4writeBusesAtBank_direct_memory_never_unknown
                readState access operandAccess negated extended rounded mask bank
                cycle source read).elim
          | ok buses =>
              simp only [hFour, read]
              exact ih _ _
      | false =>
          cases read : readL1MwriteBusesAtBank readState access bank
              access.selectedMab cycle with
          | failure => simp [hFour, read]
          | unknown =>
              exact (readL1MwriteBusesAtBank_direct_memory_never_unknown
                readState access operandAccess negated extended rounded mask bank
                access.selectedMab cycle source read).elim
          | ok buses =>
              simp only [hFour, read]
              exact ih _ _

theorem executeL1MwriteCycleList_resolved_forward_never_unknown
    (readState : State) (access : ParsedL1MwriteAccess) (bank : Fin 64)
    (updateTurnaround : Bool) (cycles : List (Fin 4))
    (memory : L1Transfer.L1Bank) (turnaround : L1Transfer.L1Turnaround)
    (kind : ParsedForward) (negated extended rounded : Bool)
    (resolved : forwardingSourceResolved readState)
    (source : access.source = .forward kind negated extended rounded) :
    executeL1MwriteCycleList readState access bank updateTurnaround cycles memory
      turnaround ≠ .unknown := by
  induction cycles generalizing memory turnaround with
  | nil => simp [executeL1MwriteCycleList]
  | cons cycle rest ih =>
      simp only [executeL1MwriteCycleList]
      cases hFour : access.fourMabs with
      | true =>
          cases read : readL1M4writeBusesAtBank readState access bank cycle with
          | failure => simp [hFour, read]
          | unknown =>
              exact (readL1M4writeBusesAtBank_resolved_forward_never_unknown
                readState access kind negated extended rounded bank cycle resolved
                source read).elim
          | ok buses =>
              simp only [hFour, read]
              exact ih _ _
      | false =>
          cases read : readL1MwriteBusesAtBank readState access bank
              access.selectedMab cycle with
          | failure => simp [hFour, read]
          | unknown =>
              exact (readL1MwriteBusesAtBank_resolved_forward_never_unknown
                readState access kind negated extended rounded bank
                access.selectedMab cycle
                (by
                  intro pe
                  exact resolved pe (ParsedIntegerInput.forwardUnit kind) cycle)
                source read).elim
          | ok buses =>
              simp only [hFour, read]
              exact ih _ _

theorem executeL1MwriteCycleList_resolved_source_never_unknown
    (readState : State) (access : ParsedL1MwriteAccess) (bank : Fin 64)
    (updateTurnaround : Bool) (cycles : List (Fin 4))
    (memory : L1Transfer.L1Bank) (turnaround : L1Transfer.L1Turnaround)
    (resolved : forwardingSourceResolved readState) :
    executeL1MwriteCycleList readState access bank updateTurnaround cycles memory
      turnaround ≠ .unknown := by
  induction cycles generalizing memory turnaround with
  | nil => simp [executeL1MwriteCycleList]
  | cons cycle rest ih =>
      simp only [executeL1MwriteCycleList]
      cases hFour : access.fourMabs with
      | true =>
          cases read : readL1M4writeBusesAtBank readState access bank cycle with
          | failure => simp [hFour, read]
          | unknown =>
              exact (readL1M4writeBusesAtBank_resolved_source_never_unknown
                readState access bank cycle resolved read).elim
          | ok buses =>
              simp only [hFour, read]
              exact ih _ _
      | false =>
          cases read : readL1MwriteBusesAtBank readState access bank
              access.selectedMab cycle with
          | failure => simp [hFour, read]
          | unknown =>
              exact (readL1MwriteBusesAtBank_resolved_source_never_unknown
                readState access bank access.selectedMab cycle resolved read).elim
          | ok buses =>
              simp only [hFour, read]
              exact ih _ _

def executeL1MwriteCyclesAtBank (readState currentState : State)
    (access : ParsedL1MwriteAccess)
    (bank : Fin 64) (updateTurnaround : Bool) : ProofsLean.StepResult
      (L1Transfer.L1Bank × L1Transfer.L1Turnaround) :=
  executeL1MwriteCycleList readState access bank updateTurnaround [0, 1, 2, 3]
    (currentState.l1bm bank) (readState.l1bmTurnaround bank)

theorem executeL1MwriteCyclesAtBank_direct_memory_never_unknown
    (readState currentState : State) (access : ParsedL1MwriteAccess)
    (bank : Fin 64) (updateTurnaround : Bool)
    (operandAccess : Access) (negated extended rounded : Bool)
    (mask : Option ParsedMask)
    (source : access.source = .mem operandAccess negated extended rounded mask) :
    executeL1MwriteCyclesAtBank readState currentState access bank updateTurnaround ≠
      .unknown := by
  exact executeL1MwriteCycleList_direct_memory_never_unknown readState access bank
    updateTurnaround [0, 1, 2, 3] (currentState.l1bm bank)
    (readState.l1bmTurnaround bank) operandAccess negated extended rounded mask source

theorem executeL1MwriteCyclesAtBank_resolved_forward_never_unknown
    (readState currentState : State) (access : ParsedL1MwriteAccess)
    (bank : Fin 64) (updateTurnaround : Bool) (kind : ParsedForward)
    (negated extended rounded : Bool) (resolved : forwardingSourceResolved readState)
    (source : access.source = .forward kind negated extended rounded) :
    executeL1MwriteCyclesAtBank readState currentState access bank updateTurnaround ≠
      .unknown := by
  exact executeL1MwriteCycleList_resolved_forward_never_unknown readState access bank
    updateTurnaround [0, 1, 2, 3] (currentState.l1bm bank)
    (readState.l1bmTurnaround bank) kind negated extended rounded resolved source

theorem executeL1MwriteCyclesAtBank_resolved_source_never_unknown
    (readState currentState : State) (access : ParsedL1MwriteAccess)
    (bank : Fin 64) (updateTurnaround : Bool)
    (resolved : forwardingSourceResolved readState) :
    executeL1MwriteCyclesAtBank readState currentState access bank updateTurnaround ≠
      .unknown := by
  exact executeL1MwriteCycleList_resolved_source_never_unknown readState access bank
    updateTurnaround [0, 1, 2, 3] (currentState.l1bm bank)
    (readState.l1bmTurnaround bank) resolved

def executeL1MwriteBankList (readState : State) (access : ParsedL1MwriteAccess)
    (updateTurnaround : Bool) : List (Fin 64) → State → ProofsLean.StepResult State
  | [], state => .ok state
  | bank :: rest, state =>
      match executeL1MwriteCyclesAtBank readState state access bank updateTurnaround with
      | .failure => .failure
      | .unknown => .unknown
      | .ok (memory, turnaround) =>
          let next := { state with
            l1bm := fun other => if other = bank then memory else state.l1bm other
            l1bmTurnaround := fun other =>
              if other = bank then turnaround else state.l1bmTurnaround other }
          executeL1MwriteBankList readState access updateTurnaround rest next

theorem executeL1MwriteBankList_direct_memory_never_unknown
    (readState : State) (access : ParsedL1MwriteAccess) (updateTurnaround : Bool)
    (banks : List (Fin 64)) (state : State)
    (operandAccess : Access) (negated extended rounded : Bool)
    (mask : Option ParsedMask)
    (source : access.source = .mem operandAccess negated extended rounded mask) :
    executeL1MwriteBankList readState access updateTurnaround banks state ≠ .unknown := by
  induction banks generalizing state with
  | nil => simp [executeL1MwriteBankList]
  | cons bank rest ih =>
      simp only [executeL1MwriteBankList]
      cases result : executeL1MwriteCyclesAtBank readState state access bank
          updateTurnaround with
      | failure => simp [result]
      | unknown =>
          exact (executeL1MwriteCyclesAtBank_direct_memory_never_unknown
            readState state access bank updateTurnaround operandAccess negated extended
            rounded mask source result).elim
      | ok completion =>
          rcases completion with ⟨memory, turnaround⟩
          simp only [result]
          exact ih _

theorem executeL1MwriteBankList_resolved_forward_never_unknown
    (readState : State) (access : ParsedL1MwriteAccess) (updateTurnaround : Bool)
    (banks : List (Fin 64)) (state : State) (kind : ParsedForward)
    (negated extended rounded : Bool)
    (resolved : forwardingSourceResolved readState)
    (source : access.source = .forward kind negated extended rounded) :
    executeL1MwriteBankList readState access updateTurnaround banks state ≠ .unknown := by
  induction banks generalizing state with
  | nil => simp [executeL1MwriteBankList]
  | cons bank rest ih =>
      simp only [executeL1MwriteBankList]
      cases result : executeL1MwriteCyclesAtBank readState state access bank
          updateTurnaround with
      | failure => simp [result]
      | unknown =>
          exact (executeL1MwriteCyclesAtBank_resolved_forward_never_unknown
            readState state access bank updateTurnaround kind negated extended rounded
            resolved source result).elim
      | ok completion =>
          rcases completion with ⟨memory, turnaround⟩
          simp only [result]
          exact ih _

theorem executeL1MwriteBankList_resolved_source_never_unknown
    (readState : State) (access : ParsedL1MwriteAccess) (updateTurnaround : Bool)
    (banks : List (Fin 64)) (state : State)
    (resolved : forwardingSourceResolved readState) :
    executeL1MwriteBankList readState access updateTurnaround banks state ≠ .unknown := by
  induction banks generalizing state with
  | nil => simp [executeL1MwriteBankList]
  | cons bank rest ih =>
      simp only [executeL1MwriteBankList]
      cases result : executeL1MwriteCyclesAtBank readState state access bank
          updateTurnaround with
      | failure => simp [result]
      | unknown =>
          exact (executeL1MwriteCyclesAtBank_resolved_source_never_unknown readState
            state access bank updateTurnaround resolved result).elim
      | ok completion =>
          rcases completion with ⟨memory, turnaround⟩
          simp only [result]
          exact ih _

def executeParsedL1MwriteAtAllBanks (readState currentState : State)
    (expression : ParsedExpr) (updateTurnaround : Bool) : ProofsLean.StepResult State :=
  match lowerParsedL1Mwrite? expression with
  | none => .failure
  | some access => executeL1MwriteBankList readState access updateTurnaround
      (List.finRange 64) currentState

theorem executeParsedL1MwriteAtAllBanks_direct_memory_never_unknown
    (readState currentState : State) (expression : ParsedExpr)
    (updateTurnaround : Bool) (access : ParsedL1MwriteAccess)
    (operandAccess : Access) (negated extended rounded : Bool)
    (mask : Option ParsedMask)
    (lowered : lowerParsedL1Mwrite? expression = some access)
    (source : access.source = .mem operandAccess negated extended rounded mask) :
    executeParsedL1MwriteAtAllBanks readState currentState expression updateTurnaround ≠
      .unknown := by
  simp only [executeParsedL1MwriteAtAllBanks, lowered]
  exact executeL1MwriteBankList_direct_memory_never_unknown readState access
    updateTurnaround (List.finRange 64) currentState operandAccess negated extended
    rounded mask source

theorem executeParsedL1MwriteAtAllBanks_resolved_forward_never_unknown
    (readState currentState : State) (expression : ParsedExpr)
    (updateTurnaround : Bool) (access : ParsedL1MwriteAccess)
    (kind : ParsedForward) (negated extended rounded : Bool)
    (lowered : lowerParsedL1Mwrite? expression = some access)
    (resolved : forwardingSourceResolved readState)
    (source : access.source = .forward kind negated extended rounded) :
    executeParsedL1MwriteAtAllBanks readState currentState expression updateTurnaround ≠
      .unknown := by
  simp only [executeParsedL1MwriteAtAllBanks, lowered]
  exact executeL1MwriteBankList_resolved_forward_never_unknown readState access
    updateTurnaround (List.finRange 64) currentState kind negated extended rounded
    resolved source

theorem executeParsedL1MwriteAtAllBanks_resolved_source_never_unknown
    (readState currentState : State) (expression : ParsedExpr)
    (updateTurnaround : Bool) (access : ParsedL1MwriteAccess)
    (lowered : lowerParsedL1Mwrite? expression = some access)
    (resolved : forwardingSourceResolved readState) :
    executeParsedL1MwriteAtAllBanks readState currentState expression updateTurnaround ≠
      .unknown := by
  simp only [executeParsedL1MwriteAtAllBanks, lowered]
  exact executeL1MwriteBankList_resolved_source_never_unknown readState access
    updateTurnaround (List.finRange 64) currentState resolved

theorem executeParsedL1MwriteAtAllBanks_lowering_failure
    (readState currentState : State) (expression : ParsedExpr) (updateTurnaround : Bool)
    (notLowered : lowerParsedL1Mwrite? expression = none) :
    executeParsedL1MwriteAtAllBanks readState currentState expression updateTurnaround =
      .failure := by
  simp [executeParsedL1MwriteAtAllBanks, notLowered]

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

def readL1GatherPEList (state : State) (source : ParsedOperand)
    (bank : Fin 64) (mab : Fin 16) (cycle : Fin 4) :
    List (Fin 4) → (Fin 4 → IntegerALU.Bus) →
      ProofsLean.StepResult (Fin 4 → IntegerALU.Bus)
  | [], buses => .ok buses
  | pe :: pes, buses =>
      let linear := bank.val * 64 + mab.val * 4 + pe.val
      let linearPE : PEId := ⟨linear, by
        have hb := bank.isLt
        have hm := mab.isLt
        have hp := pe.isLt
        omega⟩
      match readRawL1MwriteBus state source linearPE cycle with
      | .failure => .failure
      | .unknown => .unknown
      | .ok bus => readL1GatherPEList state source bank mab cycle pes
          (fun index => if index = pe then bus else buses index)

theorem readL1GatherPEList_direct_memory_never_unknown
    (state : State) (sourceAccess : Access) (negated extended rounded : Bool)
    (mask : Option ParsedMask) (bank : Fin 64) (mab : Fin 16) (cycle : Fin 4)
    (pes : List (Fin 4)) (buses : Fin 4 → IntegerALU.Bus) :
    readL1GatherPEList state (.mem sourceAccess negated extended rounded mask)
      bank mab cycle pes buses ≠ .unknown := by
  induction pes generalizing buses with
  | nil => simp [readL1GatherPEList]
  | cons pe rest ih =>
      simp only [readL1GatherPEList]
      let linear := bank.val * 64 + mab.val * 4 + pe.val
      let linearPE : PEId := ⟨linear, by
        have hb := bank.isLt
        have hm := mab.isLt
        have hp := pe.isLt
        omega⟩
      cases result : readRawL1MwriteBus state
          (.mem sourceAccess negated extended rounded mask) linearPE cycle with
      | failure => simp [result]
      | unknown =>
          exact (readRawL1MwriteBus_memory_never_unknown state sourceAccess negated
            extended rounded mask linearPE cycle result).elim
      | ok bus =>
          simp only [result]
          exact ih (fun index => if index = pe then bus else buses index)

theorem readL1GatherPEList_resolved_forward_never_unknown
    (state : State) (kind : ParsedForward) (negated extended rounded : Bool)
    (bank : Fin 64) (mab : Fin 16) (cycle : Fin 4) (pes : List (Fin 4))
    (buses : Fin 4 → IntegerALU.Bus) (resolved : forwardingSourceResolved state) :
    readL1GatherPEList state (.forward kind negated extended rounded)
      bank mab cycle pes buses ≠ .unknown := by
  induction pes generalizing buses with
  | nil => simp [readL1GatherPEList]
  | cons pe rest ih =>
      simp only [readL1GatherPEList]
      let linear := bank.val * 64 + mab.val * 4 + pe.val
      let linearPE : PEId := ⟨linear, by
        have hb := bank.isLt
        have hm := mab.isLt
        have hp := pe.isLt
        omega⟩
      cases result : readRawL1MwriteBus state
          (.forward kind negated extended rounded) linearPE cycle with
      | failure => simp [result]
      | unknown =>
          have known := resolved linearPE (ParsedIntegerInput.forwardUnit kind) cycle
          exact (readRawL1MwriteBus_forward_never_unknown state kind negated extended
            rounded linearPE cycle known result).elim
      | ok bus =>
          simp only [result]
          exact ih (fun index => if index = pe then bus else buses index)

theorem readL1GatherPEList_resolved_source_never_unknown
    (state : State) (source : ParsedOperand) (bank : Fin 64) (mab : Fin 16)
    (cycle : Fin 4) (pes : List (Fin 4)) (buses : Fin 4 → IntegerALU.Bus)
    (resolved : forwardingSourceResolved state) :
    readL1GatherPEList state source bank mab cycle pes buses ≠ .unknown := by
  induction pes generalizing buses with
  | nil => simp [readL1GatherPEList]
  | cons pe rest ih =>
      simp only [readL1GatherPEList]
      let linear := bank.val * 64 + mab.val * 4 + pe.val
      let linearPE : PEId := ⟨linear, by
        have hb := bank.isLt
        have hm := mab.isLt
        have hp := pe.isLt
        omega⟩
      cases result : readRawL1MwriteBus state source linearPE cycle with
      | failure => simp [result]
      | unknown =>
          exact (readRawL1MwriteBus_resolved_never_unknown state source linearPE cycle
            resolved result).elim
      | ok bus =>
          simp only [result]
          exact ih (fun index => if index = pe then bus else buses index)

def readL1GatherMabList (state : State) (source : ParsedOperand)
    (bank : Fin 64) (cycle : Fin 4) :
    List (Fin 16) → (Fin 16 → Fin 4 → IntegerALU.Bus) →
      ProofsLean.StepResult (Fin 16 → Fin 4 → IntegerALU.Bus)
  | [], buses => .ok buses
  | mab :: mabs, buses =>
      match readL1GatherPEList state source bank mab cycle
          (List.finRange 4) (fun _ => ⟨0, 0⟩) with
      | .failure => .failure
      | .unknown => .unknown
      | .ok peBuses => readL1GatherMabList state source bank cycle mabs
          (fun nextMab pe => if nextMab = mab then peBuses pe else buses nextMab pe)

theorem readL1GatherMabList_direct_memory_never_unknown
    (state : State) (sourceAccess : Access) (negated extended rounded : Bool)
    (mask : Option ParsedMask) (bank : Fin 64) (cycle : Fin 4)
    (mabs : List (Fin 16)) (buses : Fin 16 → Fin 4 → IntegerALU.Bus) :
    readL1GatherMabList state (.mem sourceAccess negated extended rounded mask)
      bank cycle mabs buses ≠ .unknown := by
  induction mabs generalizing buses with
  | nil => simp [readL1GatherMabList]
  | cons mab rest ih =>
      simp only [readL1GatherMabList]
      cases result : readL1GatherPEList state
          (.mem sourceAccess negated extended rounded mask) bank mab cycle
          (List.finRange 4) (fun _ => ⟨0, 0⟩) with
      | failure => simp [result]
      | unknown =>
          exact (readL1GatherPEList_direct_memory_never_unknown state sourceAccess
            negated extended rounded mask bank mab cycle (List.finRange 4)
            (fun _ => ⟨0, 0⟩) result).elim
      | ok peBuses =>
          simp only [result]
          exact ih (fun nextMab pe =>
            if nextMab = mab then peBuses pe else buses nextMab pe)

theorem readL1GatherMabList_resolved_forward_never_unknown
    (state : State) (kind : ParsedForward) (negated extended rounded : Bool)
    (bank : Fin 64) (cycle : Fin 4) (mabs : List (Fin 16))
    (buses : Fin 16 → Fin 4 → IntegerALU.Bus)
    (resolved : forwardingSourceResolved state) :
    readL1GatherMabList state (.forward kind negated extended rounded)
      bank cycle mabs buses ≠ .unknown := by
  induction mabs generalizing buses with
  | nil => simp [readL1GatherMabList]
  | cons mab rest ih =>
      simp only [readL1GatherMabList]
      cases result : readL1GatherPEList state
          (.forward kind negated extended rounded) bank mab cycle
          (List.finRange 4) (fun _ => ⟨0, 0⟩) with
      | failure => simp [result]
      | unknown =>
          exact (readL1GatherPEList_resolved_forward_never_unknown state kind negated
            extended rounded bank mab cycle (List.finRange 4) (fun _ => ⟨0, 0⟩)
            resolved result).elim
      | ok peBuses =>
          simp only [result]
          exact ih (fun nextMab pe =>
            if nextMab = mab then peBuses pe else buses nextMab pe)

theorem readL1GatherMabList_resolved_source_never_unknown
    (state : State) (source : ParsedOperand) (bank : Fin 64) (cycle : Fin 4)
    (mabs : List (Fin 16)) (buses : Fin 16 → Fin 4 → IntegerALU.Bus)
    (resolved : forwardingSourceResolved state) :
    readL1GatherMabList state source bank cycle mabs buses ≠ .unknown := by
  induction mabs generalizing buses with
  | nil => simp [readL1GatherMabList]
  | cons mab rest ih =>
      simp only [readL1GatherMabList]
      cases result : readL1GatherPEList state source bank mab cycle
          (List.finRange 4) (fun _ => ⟨0, 0⟩) with
      | failure => simp [result]
      | unknown =>
          exact (readL1GatherPEList_resolved_source_never_unknown state source bank mab
            cycle (List.finRange 4) (fun _ => ⟨0, 0⟩) resolved result).elim
      | ok peBuses =>
          simp only [result]
          exact ih (fun nextMab pe =>
            if nextMab = mab then peBuses pe else buses nextMab pe)

def readL1GatherBusesAtBank (state : State) (access : ParsedL1GatherAccess)
    (bank : Fin 64) (cycle : Fin 4) :
    ProofsLean.StepResult (Fin 16 → Fin 4 → IntegerALU.Bus) :=
  readL1GatherMabList state access.source bank cycle (List.finRange 16)
    (fun _ _ => ⟨0, 0⟩)

theorem readL1GatherBusesAtBank_direct_memory_never_unknown
    (state : State) (access : ParsedL1GatherAccess)
    (sourceAccess : Access) (negated extended rounded : Bool)
    (mask : Option ParsedMask) (bank : Fin 64) (cycle : Fin 4)
    (source : access.source = .mem sourceAccess negated extended rounded mask) :
    readL1GatherBusesAtBank state access bank cycle ≠ .unknown := by
  simpa [readL1GatherBusesAtBank, source] using
    readL1GatherMabList_direct_memory_never_unknown state sourceAccess negated
      extended rounded mask bank cycle (List.finRange 16)
      (fun _ _ => ⟨0, 0⟩)

theorem readL1GatherBusesAtBank_resolved_forward_never_unknown
    (state : State) (access : ParsedL1GatherAccess) (kind : ParsedForward)
    (negated extended rounded : Bool) (bank : Fin 64) (cycle : Fin 4)
    (resolved : forwardingSourceResolved state)
    (source : access.source = .forward kind negated extended rounded) :
    readL1GatherBusesAtBank state access bank cycle ≠ .unknown := by
  simpa [readL1GatherBusesAtBank, source] using
    readL1GatherMabList_resolved_forward_never_unknown state kind negated extended
      rounded bank cycle (List.finRange 16) (fun _ _ => ⟨0, 0⟩) resolved

theorem readL1GatherBusesAtBank_resolved_source_never_unknown
    (state : State) (access : ParsedL1GatherAccess) (bank : Fin 64) (cycle : Fin 4)
    (resolved : forwardingSourceResolved state) :
    readL1GatherBusesAtBank state access bank cycle ≠ .unknown := by
  simpa [readL1GatherBusesAtBank] using
    readL1GatherMabList_resolved_source_never_unknown state access.source bank cycle
      (List.finRange 16) (fun _ _ => ⟨0, 0⟩) resolved

def executeL1GatherCycleList (readState : State) (access : ParsedL1GatherAccess)
    (bank : Fin 64) (updateTurnaround : Bool) : List (Fin 4) →
      L1Transfer.L1Bank → L1Transfer.L1Turnaround →
      ProofsLean.StepResult (L1Transfer.L1Bank × L1Transfer.L1Turnaround)
    | [], memory, turnaround => .ok (memory, turnaround)
    | cycle :: rest, memory, turnaround =>
        match readL1GatherBusesAtBank readState access bank cycle with
        | .failure => .failure
        | .unknown => .unknown
        | .ok buses =>
            let writes := match access.address with
              | none => []
              | some base => L1Transfer.gatherL1Writes base access.mabDiff cycle buses
            let turnWrites := if updateTurnaround then
              L1Transfer.gatherTurnaroundWrites access.mabDiff buses else []
            let next := L1Transfer.commitL1Transfer memory turnaround cycle writes turnWrites
            executeL1GatherCycleList readState access bank updateTurnaround rest
              next.1 next.2

theorem executeL1GatherCycleList_direct_memory_never_unknown
    (readState : State) (access : ParsedL1GatherAccess) (bank : Fin 64)
    (updateTurnaround : Bool) (cycles : List (Fin 4))
    (memory : L1Transfer.L1Bank) (turnaround : L1Transfer.L1Turnaround)
    (sourceAccess : Access) (negated extended rounded : Bool)
    (mask : Option ParsedMask)
    (source : access.source = .mem sourceAccess negated extended rounded mask) :
    executeL1GatherCycleList readState access bank updateTurnaround cycles memory
      turnaround ≠ .unknown := by
  induction cycles generalizing memory turnaround with
  | nil => simp [executeL1GatherCycleList]
  | cons cycle rest ih =>
      simp only [executeL1GatherCycleList]
      cases result : readL1GatherBusesAtBank readState access bank cycle with
      | failure => simp [result]
      | unknown =>
          exact (readL1GatherBusesAtBank_direct_memory_never_unknown readState access
            sourceAccess negated extended rounded mask bank cycle source result).elim
      | ok buses =>
          simp only [result]
          exact ih _ _

theorem executeL1GatherCycleList_resolved_forward_never_unknown
    (readState : State) (access : ParsedL1GatherAccess) (bank : Fin 64)
    (updateTurnaround : Bool) (cycles : List (Fin 4))
    (memory : L1Transfer.L1Bank) (turnaround : L1Transfer.L1Turnaround)
    (kind : ParsedForward) (negated extended rounded : Bool)
    (resolved : forwardingSourceResolved readState)
    (source : access.source = .forward kind negated extended rounded) :
    executeL1GatherCycleList readState access bank updateTurnaround cycles memory
      turnaround ≠ .unknown := by
  induction cycles generalizing memory turnaround with
  | nil => simp [executeL1GatherCycleList]
  | cons cycle rest ih =>
      simp only [executeL1GatherCycleList]
      cases result : readL1GatherBusesAtBank readState access bank cycle with
      | failure => simp [result]
      | unknown =>
          exact (readL1GatherBusesAtBank_resolved_forward_never_unknown readState access
            kind negated extended rounded bank cycle resolved source result).elim
      | ok buses =>
          simp only [result]
          exact ih _ _

theorem executeL1GatherCycleList_resolved_source_never_unknown
    (readState : State) (access : ParsedL1GatherAccess) (bank : Fin 64)
    (updateTurnaround : Bool) (cycles : List (Fin 4))
    (memory : L1Transfer.L1Bank) (turnaround : L1Transfer.L1Turnaround)
    (resolved : forwardingSourceResolved readState) :
    executeL1GatherCycleList readState access bank updateTurnaround cycles memory
      turnaround ≠ .unknown := by
  induction cycles generalizing memory turnaround with
  | nil => simp [executeL1GatherCycleList]
  | cons cycle rest ih =>
      simp only [executeL1GatherCycleList]
      cases result : readL1GatherBusesAtBank readState access bank cycle with
      | failure => simp [result]
      | unknown =>
          exact (readL1GatherBusesAtBank_resolved_source_never_unknown readState
            access bank cycle resolved result).elim
      | ok buses =>
          simp only [result]
          exact ih _ _

def executeL1GatherCyclesAtBank (readState currentState : State)
    (access : ParsedL1GatherAccess)
    (bank : Fin 64) (updateTurnaround : Bool) :
    ProofsLean.StepResult (L1Transfer.L1Bank × L1Transfer.L1Turnaround) :=
  executeL1GatherCycleList readState access bank updateTurnaround [0, 1, 2, 3]
    (currentState.l1bm bank) (readState.l1bmTurnaround bank)

theorem executeL1GatherCyclesAtBank_direct_memory_never_unknown
    (readState currentState : State) (access : ParsedL1GatherAccess)
    (bank : Fin 64) (updateTurnaround : Bool)
    (sourceAccess : Access) (negated extended rounded : Bool)
    (mask : Option ParsedMask)
    (source : access.source = .mem sourceAccess negated extended rounded mask) :
    executeL1GatherCyclesAtBank readState currentState access bank updateTurnaround ≠
      .unknown := by
  exact executeL1GatherCycleList_direct_memory_never_unknown readState access bank
    updateTurnaround [0, 1, 2, 3] (currentState.l1bm bank)
    (readState.l1bmTurnaround bank) sourceAccess negated extended rounded mask source

theorem executeL1GatherCyclesAtBank_resolved_forward_never_unknown
    (readState currentState : State) (access : ParsedL1GatherAccess)
    (bank : Fin 64) (updateTurnaround : Bool) (kind : ParsedForward)
    (negated extended rounded : Bool) (resolved : forwardingSourceResolved readState)
    (source : access.source = .forward kind negated extended rounded) :
    executeL1GatherCyclesAtBank readState currentState access bank updateTurnaround ≠
      .unknown := by
  exact executeL1GatherCycleList_resolved_forward_never_unknown readState access bank
    updateTurnaround [0, 1, 2, 3] (currentState.l1bm bank)
    (readState.l1bmTurnaround bank) kind negated extended rounded resolved source

theorem executeL1GatherCyclesAtBank_resolved_source_never_unknown
    (readState currentState : State) (access : ParsedL1GatherAccess)
    (bank : Fin 64) (updateTurnaround : Bool)
    (resolved : forwardingSourceResolved readState) :
    executeL1GatherCyclesAtBank readState currentState access bank updateTurnaround ≠
      .unknown := by
  exact executeL1GatherCycleList_resolved_source_never_unknown readState access bank
    updateTurnaround [0, 1, 2, 3] (currentState.l1bm bank)
    (readState.l1bmTurnaround bank) resolved

def executeL1GatherBankList (readState : State) (access : ParsedL1GatherAccess)
    (updateTurnaround : Bool) : List (Fin 64) → State → ProofsLean.StepResult State
  | [], state => .ok state
  | bank :: rest, state =>
      match executeL1GatherCyclesAtBank readState state access bank updateTurnaround with
      | .failure => .failure
      | .unknown => .unknown
      | .ok (memory, turnaround) =>
          let next := { state with
            l1bm := fun other => if other = bank then memory else state.l1bm other
            l1bmTurnaround := fun other =>
              if other = bank then turnaround else state.l1bmTurnaround other }
          executeL1GatherBankList readState access updateTurnaround rest next

theorem executeL1GatherBankList_direct_memory_never_unknown
    (readState : State) (access : ParsedL1GatherAccess) (updateTurnaround : Bool)
    (banks : List (Fin 64)) (state : State)
    (sourceAccess : Access) (negated extended rounded : Bool)
    (mask : Option ParsedMask)
    (source : access.source = .mem sourceAccess negated extended rounded mask) :
    executeL1GatherBankList readState access updateTurnaround banks state ≠ .unknown := by
  induction banks generalizing state with
  | nil => simp [executeL1GatherBankList]
  | cons bank rest ih =>
      simp only [executeL1GatherBankList]
      cases result : executeL1GatherCyclesAtBank readState state access bank
          updateTurnaround with
      | failure => simp [result]
      | unknown =>
          exact (executeL1GatherCyclesAtBank_direct_memory_never_unknown readState
            state access bank updateTurnaround sourceAccess negated extended rounded
            mask source result).elim
      | ok completion =>
          rcases completion with ⟨memory, turnaround⟩
          simp only [result]
          exact ih _

theorem executeL1GatherBankList_resolved_forward_never_unknown
    (readState : State) (access : ParsedL1GatherAccess) (updateTurnaround : Bool)
    (banks : List (Fin 64)) (state : State) (kind : ParsedForward)
    (negated extended rounded : Bool) (resolved : forwardingSourceResolved readState)
    (source : access.source = .forward kind negated extended rounded) :
    executeL1GatherBankList readState access updateTurnaround banks state ≠ .unknown := by
  induction banks generalizing state with
  | nil => simp [executeL1GatherBankList]
  | cons bank rest ih =>
      simp only [executeL1GatherBankList]
      cases result : executeL1GatherCyclesAtBank readState state access bank
          updateTurnaround with
      | failure => simp [result]
      | unknown =>
          exact (executeL1GatherCyclesAtBank_resolved_forward_never_unknown readState
            state access bank updateTurnaround kind negated extended rounded resolved
            source result).elim
      | ok completion =>
          rcases completion with ⟨memory, turnaround⟩
          simp only [result]
          exact ih _

theorem executeL1GatherBankList_resolved_source_never_unknown
    (readState : State) (access : ParsedL1GatherAccess) (updateTurnaround : Bool)
    (banks : List (Fin 64)) (state : State)
    (resolved : forwardingSourceResolved readState) :
    executeL1GatherBankList readState access updateTurnaround banks state ≠ .unknown := by
  induction banks generalizing state with
  | nil => simp [executeL1GatherBankList]
  | cons bank rest ih =>
      simp only [executeL1GatherBankList]
      cases result : executeL1GatherCyclesAtBank readState state access bank
          updateTurnaround with
      | failure => simp [result]
      | unknown =>
          exact (executeL1GatherCyclesAtBank_resolved_source_never_unknown readState
            state access bank updateTurnaround resolved result).elim
      | ok completion =>
          rcases completion with ⟨memory, turnaround⟩
          simp only [result]
          exact ih _

def executeParsedL1GatherAtAllBanks (readState currentState : State)
    (expression : ParsedExpr) (updateTurnaround : Bool) : ProofsLean.StepResult State :=
  match lowerParsedL1Gather? expression with
  | none => .failure
  | some access => executeL1GatherBankList readState access updateTurnaround
      (List.finRange 64) currentState

theorem executeParsedL1GatherAtAllBanks_direct_memory_never_unknown
    (readState currentState : State) (expression : ParsedExpr)
    (updateTurnaround : Bool) (access : ParsedL1GatherAccess)
    (sourceAccess : Access) (negated extended rounded : Bool)
    (mask : Option ParsedMask)
    (lowered : lowerParsedL1Gather? expression = some access)
    (source : access.source = .mem sourceAccess negated extended rounded mask) :
    executeParsedL1GatherAtAllBanks readState currentState expression updateTurnaround ≠
      .unknown := by
  simp only [executeParsedL1GatherAtAllBanks, lowered]
  exact executeL1GatherBankList_direct_memory_never_unknown readState access
    updateTurnaround (List.finRange 64) currentState sourceAccess negated extended
    rounded mask source

theorem executeParsedL1GatherAtAllBanks_resolved_forward_never_unknown
    (readState currentState : State) (expression : ParsedExpr)
    (updateTurnaround : Bool) (access : ParsedL1GatherAccess)
    (kind : ParsedForward) (negated extended rounded : Bool)
    (lowered : lowerParsedL1Gather? expression = some access)
    (resolved : forwardingSourceResolved readState)
    (source : access.source = .forward kind negated extended rounded) :
    executeParsedL1GatherAtAllBanks readState currentState expression updateTurnaround ≠
      .unknown := by
  simp only [executeParsedL1GatherAtAllBanks, lowered]
  exact executeL1GatherBankList_resolved_forward_never_unknown readState access
    updateTurnaround (List.finRange 64) currentState kind negated extended rounded
    resolved source

theorem executeParsedL1GatherAtAllBanks_resolved_source_never_unknown
    (readState currentState : State) (expression : ParsedExpr)
    (updateTurnaround : Bool) (access : ParsedL1GatherAccess)
    (lowered : lowerParsedL1Gather? expression = some access)
    (resolved : forwardingSourceResolved readState) :
    executeParsedL1GatherAtAllBanks readState currentState expression updateTurnaround ≠
      .unknown := by
  simp only [executeParsedL1GatherAtAllBanks, lowered]
  exact executeL1GatherBankList_resolved_source_never_unknown readState access
    updateTurnaround (List.finRange 64) currentState resolved

theorem executeParsedL1GatherAtAllBanks_lowering_failure
    (readState currentState : State) (expression : ParsedExpr) (updateTurnaround : Bool)
    (notLowered : lowerParsedL1Gather? expression = none) :
    executeParsedL1GatherAtAllBanks readState currentState expression updateTurnaround =
      .failure := by
  simp [executeParsedL1GatherAtAllBanks, notLowered]

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

def executeL1ReduceCycleList (readState : State) (access : ParsedL1ReduceAccess)
    (bank : Fin 64) (updateTurnaround : Bool) : List (Fin 4) →
      L1Transfer.L1Bank → L1Transfer.L1Turnaround →
      ProofsLean.StepResult (L1Transfer.L1Bank × L1Transfer.L1Turnaround)
    | [], memory, turnaround => .ok (memory, turnaround)
    | cycle :: rest, memory, turnaround =>
      match readL1GatherBusesAtBank readState ⟨access.source, 0, access.address⟩ bank cycle with
      | .failure => .failure
      | .unknown => .unknown
      | .ok buses =>
        match parsedL1ReduceWritesAtCycle access
            (access.address.getD ⟨0, by decide⟩) cycle buses with
        | none => .failure
        | some (writes, turnWrites) =>
            let writes := match access.address with | none => [] | some _ => writes
            let turnWrites := if updateTurnaround then turnWrites else []
            let next := L1Transfer.commitL1Transfer memory turnaround cycle writes turnWrites
            executeL1ReduceCycleList readState access bank updateTurnaround rest
              next.1 next.2

theorem executeL1ReduceCycleList_direct_memory_never_unknown
    (readState : State) (access : ParsedL1ReduceAccess) (bank : Fin 64)
    (updateTurnaround : Bool) (cycles : List (Fin 4))
    (memory : L1Transfer.L1Bank) (turnaround : L1Transfer.L1Turnaround)
    (sourceAccess : Access) (negated extended rounded : Bool)
    (mask : Option ParsedMask)
    (source : access.source = .mem sourceAccess negated extended rounded mask) :
    executeL1ReduceCycleList readState access bank updateTurnaround cycles memory
      turnaround ≠ .unknown := by
  induction cycles generalizing memory turnaround with
  | nil => simp [executeL1ReduceCycleList]
  | cons cycle rest ih =>
      simp only [executeL1ReduceCycleList]
      let gatherAccess : ParsedL1GatherAccess := ⟨access.source, 0, access.address⟩
      cases result : readL1GatherBusesAtBank readState gatherAccess bank cycle with
      | failure => simp [result]
      | unknown =>
          exact (readL1GatherBusesAtBank_direct_memory_never_unknown readState
            gatherAccess sourceAccess negated extended rounded mask bank cycle source
            result).elim
      | ok buses =>
          cases writes : parsedL1ReduceWritesAtCycle access
              (access.address.getD ⟨0, by decide⟩) cycle buses with
          | none => simp [result, writes]
          | some writePair =>
              simp only [result, writes]
              rcases writePair with ⟨l1Writes, turnWrites⟩
              exact ih _ _

theorem executeL1ReduceCycleList_resolved_forward_never_unknown
    (readState : State) (access : ParsedL1ReduceAccess) (bank : Fin 64)
    (updateTurnaround : Bool) (cycles : List (Fin 4))
    (memory : L1Transfer.L1Bank) (turnaround : L1Transfer.L1Turnaround)
    (kind : ParsedForward) (negated extended rounded : Bool)
    (resolved : forwardingSourceResolved readState)
    (source : access.source = .forward kind negated extended rounded) :
    executeL1ReduceCycleList readState access bank updateTurnaround cycles memory
      turnaround ≠ .unknown := by
  induction cycles generalizing memory turnaround with
  | nil => simp [executeL1ReduceCycleList]
  | cons cycle rest ih =>
      simp only [executeL1ReduceCycleList]
      let gatherAccess : ParsedL1GatherAccess := ⟨access.source, 0, access.address⟩
      cases result : readL1GatherBusesAtBank readState gatherAccess bank cycle with
      | failure => simp [result]
      | unknown =>
          exact (readL1GatherBusesAtBank_resolved_forward_never_unknown readState
            gatherAccess kind negated extended rounded bank cycle resolved source
            result).elim
      | ok buses =>
          cases writes : parsedL1ReduceWritesAtCycle access
              (access.address.getD ⟨0, by decide⟩) cycle buses with
          | none => simp [result, writes]
          | some writePair =>
              simp only [result, writes]
              rcases writePair with ⟨l1Writes, turnWrites⟩
              exact ih _ _

theorem executeL1ReduceCycleList_resolved_source_never_unknown
    (readState : State) (access : ParsedL1ReduceAccess) (bank : Fin 64)
    (updateTurnaround : Bool) (cycles : List (Fin 4))
    (memory : L1Transfer.L1Bank) (turnaround : L1Transfer.L1Turnaround)
    (resolved : forwardingSourceResolved readState) :
    executeL1ReduceCycleList readState access bank updateTurnaround cycles memory
      turnaround ≠ .unknown := by
  induction cycles generalizing memory turnaround with
  | nil => simp [executeL1ReduceCycleList]
  | cons cycle rest ih =>
      simp only [executeL1ReduceCycleList]
      let gatherAccess : ParsedL1GatherAccess := ⟨access.source, 0, access.address⟩
      cases result : readL1GatherBusesAtBank readState gatherAccess bank cycle with
      | failure => simp [result]
      | unknown =>
          exact (readL1GatherBusesAtBank_resolved_source_never_unknown readState
            gatherAccess bank cycle resolved result).elim
      | ok buses =>
          cases writes : parsedL1ReduceWritesAtCycle access
              (access.address.getD ⟨0, by decide⟩) cycle buses with
          | none => simp [result, writes]
          | some writePair =>
              simp only [result, writes]
              rcases writePair with ⟨l1Writes, turnWrites⟩
              exact ih _ _

def executeL1ReduceCyclesAtBank (readState currentState : State)
    (access : ParsedL1ReduceAccess)
    (bank : Fin 64) (updateTurnaround : Bool) :
    ProofsLean.StepResult (L1Transfer.L1Bank × L1Transfer.L1Turnaround) :=
  executeL1ReduceCycleList readState access bank updateTurnaround [0, 1, 2, 3]
    (currentState.l1bm bank) (readState.l1bmTurnaround bank)

theorem executeL1ReduceCyclesAtBank_direct_memory_never_unknown
    (readState currentState : State) (access : ParsedL1ReduceAccess)
    (bank : Fin 64) (updateTurnaround : Bool)
    (sourceAccess : Access) (negated extended rounded : Bool)
    (mask : Option ParsedMask)
    (source : access.source = .mem sourceAccess negated extended rounded mask) :
    executeL1ReduceCyclesAtBank readState currentState access bank updateTurnaround ≠
      .unknown := by
  exact executeL1ReduceCycleList_direct_memory_never_unknown readState access bank
    updateTurnaround [0, 1, 2, 3] (currentState.l1bm bank)
    (readState.l1bmTurnaround bank) sourceAccess negated extended rounded mask source

theorem executeL1ReduceCyclesAtBank_resolved_forward_never_unknown
    (readState currentState : State) (access : ParsedL1ReduceAccess)
    (bank : Fin 64) (updateTurnaround : Bool) (kind : ParsedForward)
    (negated extended rounded : Bool) (resolved : forwardingSourceResolved readState)
    (source : access.source = .forward kind negated extended rounded) :
    executeL1ReduceCyclesAtBank readState currentState access bank updateTurnaround ≠
      .unknown := by
  exact executeL1ReduceCycleList_resolved_forward_never_unknown readState access bank
    updateTurnaround [0, 1, 2, 3] (currentState.l1bm bank)
    (readState.l1bmTurnaround bank) kind negated extended rounded resolved source

theorem executeL1ReduceCyclesAtBank_resolved_source_never_unknown
    (readState currentState : State) (access : ParsedL1ReduceAccess)
    (bank : Fin 64) (updateTurnaround : Bool)
    (resolved : forwardingSourceResolved readState) :
    executeL1ReduceCyclesAtBank readState currentState access bank updateTurnaround ≠
      .unknown := by
  exact executeL1ReduceCycleList_resolved_source_never_unknown readState access bank
    updateTurnaround [0, 1, 2, 3] (currentState.l1bm bank)
    (readState.l1bmTurnaround bank) resolved

def executeL1ReduceBankList (readState : State) (access : ParsedL1ReduceAccess)
    (updateTurnaround : Bool) : List (Fin 64) → State → ProofsLean.StepResult State
  | [], state => .ok state
  | bank :: rest, state =>
      match executeL1ReduceCyclesAtBank readState state access bank updateTurnaround with
      | .failure => .failure
      | .unknown => .unknown
      | .ok (memory, turnaround) =>
          let next := { state with
            l1bm := fun other => if other = bank then memory else state.l1bm other
            l1bmTurnaround := fun other =>
              if other = bank then turnaround else state.l1bmTurnaround other }
          executeL1ReduceBankList readState access updateTurnaround rest next

theorem executeL1ReduceBankList_direct_memory_never_unknown
    (readState : State) (access : ParsedL1ReduceAccess) (updateTurnaround : Bool)
    (banks : List (Fin 64)) (state : State)
    (sourceAccess : Access) (negated extended rounded : Bool)
    (mask : Option ParsedMask)
    (source : access.source = .mem sourceAccess negated extended rounded mask) :
    executeL1ReduceBankList readState access updateTurnaround banks state ≠ .unknown := by
  induction banks generalizing state with
  | nil => simp [executeL1ReduceBankList]
  | cons bank rest ih =>
      simp only [executeL1ReduceBankList]
      cases result : executeL1ReduceCyclesAtBank readState state access bank
          updateTurnaround with
      | failure => simp [result]
      | unknown =>
          exact (executeL1ReduceCyclesAtBank_direct_memory_never_unknown readState
            state access bank updateTurnaround sourceAccess negated extended rounded
            mask source result).elim
      | ok completion =>
          rcases completion with ⟨memory, turnaround⟩
          simp only [result]
          exact ih _

theorem executeL1ReduceBankList_resolved_forward_never_unknown
    (readState : State) (access : ParsedL1ReduceAccess) (updateTurnaround : Bool)
    (banks : List (Fin 64)) (state : State) (kind : ParsedForward)
    (negated extended rounded : Bool) (resolved : forwardingSourceResolved readState)
    (source : access.source = .forward kind negated extended rounded) :
    executeL1ReduceBankList readState access updateTurnaround banks state ≠ .unknown := by
  induction banks generalizing state with
  | nil => simp [executeL1ReduceBankList]
  | cons bank rest ih =>
      simp only [executeL1ReduceBankList]
      cases result : executeL1ReduceCyclesAtBank readState state access bank
          updateTurnaround with
      | failure => simp [result]
      | unknown =>
          exact (executeL1ReduceCyclesAtBank_resolved_forward_never_unknown readState
            state access bank updateTurnaround kind negated extended rounded resolved
            source result).elim
      | ok completion =>
          rcases completion with ⟨memory, turnaround⟩
          simp only [result]
          exact ih _

theorem executeL1ReduceBankList_resolved_source_never_unknown
    (readState : State) (access : ParsedL1ReduceAccess) (updateTurnaround : Bool)
    (banks : List (Fin 64)) (state : State)
    (resolved : forwardingSourceResolved readState) :
    executeL1ReduceBankList readState access updateTurnaround banks state ≠ .unknown := by
  induction banks generalizing state with
  | nil => simp [executeL1ReduceBankList]
  | cons bank rest ih =>
      simp only [executeL1ReduceBankList]
      cases result : executeL1ReduceCyclesAtBank readState state access bank
          updateTurnaround with
      | failure => simp [result]
      | unknown =>
          exact (executeL1ReduceCyclesAtBank_resolved_source_never_unknown readState
            state access bank updateTurnaround resolved result).elim
      | ok completion =>
          rcases completion with ⟨memory, turnaround⟩
          simp only [result]
          exact ih _

def executeParsedL1ReduceAtAllBanks (readState currentState : State)
    (expression : ParsedExpr) (updateTurnaround : Bool) : ProofsLean.StepResult State :=
  match lowerParsedL1Reduce? expression with
  | none => .failure
  | some access => executeL1ReduceBankList readState access updateTurnaround
      (List.finRange 64) currentState

theorem executeParsedL1ReduceAtAllBanks_direct_memory_never_unknown
    (readState currentState : State) (expression : ParsedExpr)
    (updateTurnaround : Bool) (access : ParsedL1ReduceAccess)
    (sourceAccess : Access) (negated extended rounded : Bool)
    (mask : Option ParsedMask)
    (lowered : lowerParsedL1Reduce? expression = some access)
    (source : access.source = .mem sourceAccess negated extended rounded mask) :
    executeParsedL1ReduceAtAllBanks readState currentState expression updateTurnaround ≠
      .unknown := by
  simp only [executeParsedL1ReduceAtAllBanks, lowered]
  exact executeL1ReduceBankList_direct_memory_never_unknown readState access
    updateTurnaround (List.finRange 64) currentState sourceAccess negated extended
    rounded mask source

theorem executeParsedL1ReduceAtAllBanks_resolved_forward_never_unknown
    (readState currentState : State) (expression : ParsedExpr)
    (updateTurnaround : Bool) (access : ParsedL1ReduceAccess)
    (kind : ParsedForward) (negated extended rounded : Bool)
    (lowered : lowerParsedL1Reduce? expression = some access)
    (resolved : forwardingSourceResolved readState)
    (source : access.source = .forward kind negated extended rounded) :
    executeParsedL1ReduceAtAllBanks readState currentState expression updateTurnaround ≠
      .unknown := by
  simp only [executeParsedL1ReduceAtAllBanks, lowered]
  exact executeL1ReduceBankList_resolved_forward_never_unknown readState access
    updateTurnaround (List.finRange 64) currentState kind negated extended rounded
    resolved source

theorem executeParsedL1ReduceAtAllBanks_resolved_source_never_unknown
    (readState currentState : State) (expression : ParsedExpr)
    (updateTurnaround : Bool) (access : ParsedL1ReduceAccess)
    (lowered : lowerParsedL1Reduce? expression = some access)
    (resolved : forwardingSourceResolved readState) :
    executeParsedL1ReduceAtAllBanks readState currentState expression updateTurnaround ≠
      .unknown := by
  simp only [executeParsedL1ReduceAtAllBanks, lowered]
  exact executeL1ReduceBankList_resolved_source_never_unknown readState access
    updateTurnaround (List.finRange 64) currentState resolved

theorem executeParsedL1ReduceAtAllBanks_lowering_failure
    (readState currentState : State) (expression : ParsedExpr) (updateTurnaround : Bool)
    (notLowered : lowerParsedL1Reduce? expression = none) :
    executeParsedL1ReduceAtAllBanks readState currentState expression updateTurnaround =
      .failure := by
  simp [executeParsedL1ReduceAtAllBanks, notLowered]

def parsedExprIsL1ReduceProducer (expression : ParsedExpr) : Bool :=
  match expression.op with
  | .l1bm (.reduce ..) | .l1bm (.reduce4 ..) => true
  | _ => false

def executeParsedL1PEToL1Expression (readState currentState : State)
    (expression : ParsedExpr) (updateTurnaround : Bool) : ProofsLean.StepResult State :=
  match expression.op with
  | .l1bm (.mwrite _) | .l1bm (.m4write _) =>
      executeParsedL1MwriteAtAllBanks readState currentState expression updateTurnaround
  | .l1bm (.gather _) =>
      executeParsedL1GatherAtAllBanks readState currentState expression updateTurnaround
  | .l1bm (.reduce ..) | .l1bm (.reduce4 ..) =>
      executeParsedL1ReduceAtAllBanks readState currentState expression updateTurnaround
  | _ => .ok currentState

theorem executeParsedL1PEToL1Expression_resolved_never_unknown
    (readState currentState : State) (expression : ParsedExpr)
    (updateTurnaround : Bool) (resolved : forwardingSourceResolved readState) :
    executeParsedL1PEToL1Expression readState currentState expression updateTurnaround ≠
      .unknown := by
  cases hOp : expression.op with
  | l1bm operation =>
      cases operation with
      | mwrite mab =>
          cases lowered : lowerParsedL1Mwrite? expression with
          | none => simp [executeParsedL1PEToL1Expression, hOp,
              executeParsedL1MwriteAtAllBanks, lowered]
          | some access =>
              simp only [executeParsedL1PEToL1Expression, hOp]
              simpa only [executeParsedL1MwriteAtAllBanks] using
                executeParsedL1MwriteAtAllBanks_resolved_source_never_unknown
                  readState currentState expression updateTurnaround access lowered resolved
      | m4write mab =>
          cases lowered : lowerParsedL1Mwrite? expression with
          | none => simp [executeParsedL1PEToL1Expression, hOp,
              executeParsedL1MwriteAtAllBanks, lowered]
          | some access =>
              simp only [executeParsedL1PEToL1Expression, hOp]
              simpa only [executeParsedL1MwriteAtAllBanks] using
                executeParsedL1MwriteAtAllBanks_resolved_source_never_unknown
                  readState currentState expression updateTurnaround access lowered resolved
      | gather mabDiff =>
          cases lowered : lowerParsedL1Gather? expression with
          | none => simp [executeParsedL1PEToL1Expression, hOp,
              executeParsedL1GatherAtAllBanks, lowered]
          | some access =>
              simp only [executeParsedL1PEToL1Expression, hOp]
              simpa only [executeParsedL1GatherAtAllBanks] using
                executeParsedL1GatherAtAllBanks_resolved_source_never_unknown
                  readState currentState expression updateTurnaround access lowered resolved
      | reduce rrn round | reduce4 rrn round =>
          cases lowered : lowerParsedL1Reduce? expression with
          | none => simp [executeParsedL1PEToL1Expression, hOp,
              executeParsedL1ReduceAtAllBanks, lowered]
          | some access =>
              simp only [executeParsedL1PEToL1Expression, hOp]
              simpa only [executeParsedL1ReduceAtAllBanks] using
                executeParsedL1ReduceAtAllBanks_resolved_source_never_unknown
                  readState currentState expression updateTurnaround access lowered resolved
      | pbcast | mbcast | m4bcast | distrib _ =>
          simp [executeParsedL1PEToL1Expression, hOp]
  | _ => simp [executeParsedL1PEToL1Expression, hOp]

def executeParsedL1PEToL1ProducerList (readState : State) (updateTurnaround : Bool)
    : List ParsedExpr → State → ProofsLean.StepResult State
  | [], state => .ok state
  | expression :: rest, state =>
      match executeParsedL1PEToL1Expression readState state expression updateTurnaround with
      | .failure => .failure
      | .unknown => .unknown
      | .ok next => executeParsedL1PEToL1ProducerList readState updateTurnaround rest next

def executeParsedL1PEToL1Producers (readState currentState : State)
    (expressions : List ParsedExpr) (updateTurnaround : Bool) : ProofsLean.StepResult State :=
  executeParsedL1PEToL1ProducerList readState updateTurnaround expressions currentState

theorem executeParsedL1PEToL1ProducerList_two_success
    (readState state : State) (first second : ParsedExpr) (updateTurnaround : Bool)
    (firstResult : executeParsedL1PEToL1Expression readState state first
      updateTurnaround = .ok stateAfterFirst)
    (secondResult : executeParsedL1PEToL1Expression readState stateAfterFirst second
      updateTurnaround = .ok stateAfterSecond) :
    executeParsedL1PEToL1ProducerList readState updateTurnaround [first, second] state =
      .ok stateAfterSecond := by
  simp [executeParsedL1PEToL1ProducerList, firstResult, secondResult]

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

/-- The block reduction executor must never turn an unsupported RRN spelling
into a successful zero write. `parsedL2Writes?` uses this predicate to guard
the total list construction below. -/
def parsedL2ReductionSupported (op : ParsedL2Op) : Bool :=
  match op with
  | .reduce rrn _ | .reduce2 rrn =>
      (parsedL2ReduceWord? rrn [0]).isSome
  | _ => true

theorem parsedL2ReductionSupported_rejects_integer_float_add (set : ParsedL1bSet) :
    parsedL2ReductionSupported
      (.reduce ⟨⟨'i', by decide⟩, .fadd⟩ set) = false := by
  simp [parsedL2ReductionSupported, parsedL2ReduceWord?, parsedL1IntegerRRN?]

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
  if !parsedL2ReductionSupported access.op then none else
    match access.op with
    | .dars | .darw => none
    | .fromL1b selected => if selected.val < 8 then some (l1Writes, l2Writes) else none
    | .bcast _ | .bcast2 _ | .distrib _ | .imcast _ | .gather | .reduce .. | .reduce2 .. =>
        some (l1Writes, l2Writes)

theorem parsedL2Writes_rejects_integer_float_add
    (state : State) (set : ParsedL1bSet) :
    parsedL2Writes? state ⟨.reduce ⟨⟨'i', by decide⟩, .fadd⟩ set, some 0, some 0⟩ = none := by
  simp [parsedL2Writes?, parsedL2ReductionSupported_rejects_integer_float_add]

def parsedDarsSource? (expression : ParsedExpr) : Option (Nat × Fin 2 × Fin 1024) := do
  let (.l2bm .dars) := expression.op | none
  let [.l2bm address (some l2b)] := expression.sources | none
  let [.dar darAddress] := expression.destinations | none
  if h : l2b.val < 2 then
    if ha : address.val < 2 ^ 15 then
      if hd : darAddress.val < 1024 then
        some (address.val, ⟨l2b.val, h⟩, ⟨darAddress.val, hd⟩)
      else none
    else none
  else none

def executeParsedDars (state : State) (expression : ParsedExpr) :
    ProofsLean.StepResult State := Id.run do
  let some (sourceAddress, selectedL2b, darStart) := parsedDarsSource? expression
    | return .failure
  let mut buffer := state.darBuffer
  for group in List.finRange 4 do
    let l2Index : Fin 8 :=
      ⟨group.val * 2 + selectedL2b.val, by omega⟩
    for cycle in List.range 4 do
      for word in List.range 64 do
        let longWord := state.blockMemory
          (l2PhysicalCell l2Index (sourceAddress + cycle * 64 + word))
        let evenAddress : Fin 512 :=
          ⟨(cycle * 128 + word * 2) % 512, Nat.mod_lt _ (by omega)⟩
        let oddAddress : Fin 512 :=
          ⟨(cycle * 128 + word * 2 + 1) % 512, Nat.mod_lt _ (by omega)⟩
        let high := longWord.extractLsb' 32 32
        let low := longWord.extractLsb' 0 32
        buffer := fun other address =>
          if other == group && address == evenAddress then high
          else if other == group && address == oddAddress then low
          else buffer other address
  return .ok { state with
    darBuffer := buffer
    darBufferReadAddress := ⟨0, by decide⟩
    darWriteAddress := darStart }

theorem executeParsedDars_never_unknown (state : State) (expression : ParsedExpr) :
    executeParsedDars state expression ≠ .unknown := by
  unfold executeParsedDars
  split <;> simp_all [Id.run]

def executeParsedDarw (state : State) : State := Id.run do
  let mut dar := state.dar
  let mut readAddress := state.darBufferReadAddress
  let mut writeAddress := state.darWriteAddress
  for _cycle in List.range 4 do
    for group in List.finRange 4 do
      let value := state.darBuffer group readAddress
      dar := fun other address =>
        if other == group && address == writeAddress then value else dar other address
    readAddress := ⟨(readAddress.val + 1) % 512, Nat.mod_lt _ (by decide)⟩
    writeAddress := ⟨(writeAddress.val + 1) % 1024, Nat.mod_lt _ (by decide)⟩
  return { state with
    dar := dar
    darBufferReadAddress := readAddress
    darWriteAddress := writeAddress }

def executeParsedL2BlockExpression (readState currentState : State)
    (expression : ParsedExpr) : ProofsLean.StepResult State :=
  match expression.op with
  | .l2bm .dars => executeParsedDars currentState expression
  | .l2bm .darw =>
      if expression.sources.isEmpty && expression.destinations.isEmpty then
        .ok (executeParsedDarw currentState)
      else .failure
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

theorem executeParsedL2BlockExpression_l2bm_never_unknown
    (readState currentState : State) (expression : ParsedExpr) (operation : ParsedL2Op)
    (isL2 : expression.op = .l2bm operation) :
    executeParsedL2BlockExpression readState currentState expression ≠ .unknown := by
  cases operation <;> simp only [executeParsedL2BlockExpression, isL2]
  all_goals
    first
    | exact executeParsedDars_never_unknown currentState expression
    | (split <;> simp_all <;> split <;> simp_all)

def executeParsedL2BlockProducers (readState currentState : State)
    (expressions : List ParsedExpr) : ProofsLean.StepResult State := Id.run do
  let mut state := currentState
  for expression in expressions.filter parsedExprIsL2BMProducer do
    match executeParsedL2BlockExpression readState state expression with
    | .failure => return .failure
    | .unknown => return .unknown
    | .ok next => state := next
  return .ok state

def executeParsedSharedBlockExpression (readState currentState : State)
    (expression : ParsedExpr) (updateTurnaround : Bool) : ProofsLean.StepResult State :=
  match expression.op with
  | .l1bm (.mwrite _) | .l1bm (.m4write _) | .l1bm (.gather _) |
      .l1bm (.reduce ..) | .l1bm (.reduce4 ..) =>
      executeParsedL1PEToL1Expression readState currentState expression updateTurnaround
  | .l2bm _ => executeParsedL2BlockExpression readState currentState expression
  | _ => .ok currentState

theorem executeParsedSharedBlockExpression_l2bm_never_unknown
    (readState currentState : State) (expression : ParsedExpr)
    (operation : ParsedL2Op) (updateTurnaround : Bool)
    (isL2 : expression.op = .l2bm operation) :
    executeParsedSharedBlockExpression readState currentState expression
      updateTurnaround ≠ .unknown := by
  simp only [executeParsedSharedBlockExpression, isL2]
  exact executeParsedL2BlockExpression_l2bm_never_unknown
    readState currentState expression operation isL2

theorem executeParsedSharedBlockExpression_resolved_never_unknown
    (readState currentState : State) (expression : ParsedExpr)
    (updateTurnaround : Bool) (resolved : forwardingSourceResolved readState) :
    executeParsedSharedBlockExpression readState currentState expression
      updateTurnaround ≠ .unknown := by
  cases hOp : expression.op with
  | l1bm operation =>
      cases operation with
      | mwrite _ | m4write _ | gather _ | reduce _ _ | reduce4 _ _ =>
          simp only [executeParsedSharedBlockExpression, hOp]
          exact executeParsedL1PEToL1Expression_resolved_never_unknown
            readState currentState expression updateTurnaround resolved
      | pbcast | mbcast | m4bcast | distrib _ =>
          simp [executeParsedSharedBlockExpression, hOp]
  | l2bm operation =>
      exact executeParsedSharedBlockExpression_l2bm_never_unknown
        readState currentState expression operation updateTurnaround hOp
  | alu _ _ _ _ => simp [executeParsedSharedBlockExpression, hOp]
  | immediate _ _ => simp [executeParsedSharedBlockExpression, hOp]
  | zero => simp [executeParsedSharedBlockExpression, hOp]
  | mau _ _ _ _ _ => simp [executeParsedSharedBlockExpression, hOp]
  | matrixWrite _ => simp [executeParsedSharedBlockExpression, hOp]
  | matrixRead _ => simp [executeParsedSharedBlockExpression, hOp]
  | «wait» _ => simp [executeParsedSharedBlockExpression, hOp]
  | noforward => simp [executeParsedSharedBlockExpression, hOp]

def executeParsedSharedBlockProducerList (readState : State) (updateTurnaround : Bool)
    : List ParsedExpr → State → ProofsLean.StepResult State
  | [], state => .ok state
  | expression :: rest, state =>
      match executeParsedSharedBlockExpression readState state expression updateTurnaround with
      | .failure => .failure
      | .unknown => .unknown
      | .ok next => executeParsedSharedBlockProducerList readState updateTurnaround rest next

def executeParsedSharedBlockProducers (readState currentState : State)
    (expressions : List ParsedExpr) (updateTurnaround : Bool) : ProofsLean.StepResult State :=
  executeParsedSharedBlockProducerList readState updateTurnaround expressions currentState

/-- A source-ordered block-producer list cannot introduce epistemic
`.unknown` when every selected expression is unknown-free at every
intermediate state. This composes per-expression semantic guarantees without
assuming that each expression succeeds: ordinary execution failures remain
observable as failures. -/
theorem executeParsedSharedBlockProducerList_never_unknown
    (readState : State) (updateTurnaround : Bool)
    (expressions : List ParsedExpr) (currentState : State)
    (known : ∀ expression ∈ expressions, ∀ state,
      executeParsedSharedBlockExpression readState state expression
        updateTurnaround ≠ .unknown) :
    executeParsedSharedBlockProducerList readState updateTurnaround
      expressions currentState ≠ .unknown := by
  induction expressions generalizing currentState with
  | nil => simp [executeParsedSharedBlockProducerList]
  | cons expression rest ih =>
      have headKnown := known expression (by simp) currentState
      have tailKnown : ∀ item ∈ rest, ∀ state,
          executeParsedSharedBlockExpression readState state item
            updateTurnaround ≠ .unknown := by
        intro item member state
        exact known item (List.mem_cons_of_mem _ member) state
      cases h : executeParsedSharedBlockExpression readState currentState
          expression updateTurnaround with
      | failure => simp [executeParsedSharedBlockProducerList, h]
      | unknown => exact (headKnown h).elim
      | ok next =>
          simp only [executeParsedSharedBlockProducerList, h]
          exact ih next tailKnown

/-- The public shared-block producer runner preserves the list-level
unknown-free guarantee used by the whole PE issue transition. -/
theorem executeParsedSharedBlockProducers_never_unknown
    (readState currentState : State) (expressions : List ParsedExpr)
    (updateTurnaround : Bool)
    (known : ∀ expression ∈ expressions, ∀ state,
      executeParsedSharedBlockExpression readState state expression
        updateTurnaround ≠ .unknown) :
    executeParsedSharedBlockProducers readState currentState expressions
      updateTurnaround ≠ .unknown := by
  exact executeParsedSharedBlockProducerList_never_unknown readState
    updateTurnaround expressions currentState known

theorem executeParsedSharedBlockProducers_resolved_never_unknown
    (readState currentState : State) (expressions : List ParsedExpr)
    (updateTurnaround : Bool) (resolved : forwardingSourceResolved readState) :
    executeParsedSharedBlockProducers readState currentState expressions
      updateTurnaround ≠ .unknown := by
  apply executeParsedSharedBlockProducers_never_unknown
  intro expression _ state
  exact executeParsedSharedBlockExpression_resolved_never_unknown
    readState state expression updateTurnaround resolved

/-- Any list consisting solely of L2BM expressions is unknown-free under the
shared source-order runner, regardless of intermediate memory contents. -/
theorem executeParsedSharedBlockProducerList_l2bm_never_unknown
    (readState : State) (updateTurnaround : Bool)
    (expressions : List ParsedExpr) (currentState : State)
    (allL2 : ∀ expression ∈ expressions,
      ∃ operation, expression.op = .l2bm operation) :
    executeParsedSharedBlockProducerList readState updateTurnaround
      expressions currentState ≠ .unknown := by
  apply executeParsedSharedBlockProducerList_never_unknown
  intro expression member state
  obtain ⟨operation, isL2⟩ := allL2 expression member
  exact executeParsedSharedBlockExpression_l2bm_never_unknown
    readState state expression operation updateTurnaround isL2

theorem executeParsedSharedBlockProducerList_two_success
    (readState state : State) (first second : ParsedExpr) (updateTurnaround : Bool)
    (firstResult : executeParsedSharedBlockExpression readState state first
      updateTurnaround = .ok stateAfterFirst)
    (secondResult : executeParsedSharedBlockExpression readState stateAfterFirst second
      updateTurnaround = .ok stateAfterSecond) :
    executeParsedSharedBlockProducerList readState updateTurnaround [first, second] state =
      .ok stateAfterSecond := by
  simp [executeParsedSharedBlockProducerList, firstResult, secondResult]

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
    (maskRegisters : ProofsLean.MNCore.Masks.RegisterFile)
    (destination : ParsedOperand) (context : ParsedIntegerContext)
    (output : IntegerALU.Bus) (cycle : Fin 4) (directive : ParsedMaskDirective)
    (hasSingleLineMask : Bool) :
    Option (PEMemory.IntegerRegisterFiles × Option (Bool × BitVec 12)) :=
  match destination with
  | .mem .. => do
      let access ← ParsedOperand.toDirectMemoryDestination? destination context.pe cycle
        context.bar0 context.bar1 context.tWord
      let selection ← ParsedOperand.resolveMemoryWriteSelection? destination access.bank
        maskRegisters cycle directive hasSingleLineMask
      some (PEMemory.writeDirectAccessMasked files access
        (PEMemory.unpackALUBus output) selection, none)
  | .bar lm1 .. => do
      let bank := if lm1 then PEMemory.Bank.lm1 else PEMemory.Bank.lm0
      let selection ← ParsedOperand.resolveMemoryWriteSelection? destination bank
        maskRegisters cycle directive hasSingleLineMask
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
    (pes : List PEId) (noForward hasSingleLineMask usePreIssueMask : Bool) :
    ProofsLean.StepResult State :=
  match pes with
  | [] => .ok currentState
  | pe :: rest =>
      let coordinates := ParsedIntegerContext.ofLinearIndex pe
      let readContext := readState.peContext pe
      let initialContext := currentState.peContext pe
      let maskRegisters := if usePreIssueMask then
        (readState.peRegisters pe).maskRegisters
        else (currentState.peRegisters pe).maskRegisters
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
            match resolveFlushSelection? expression.flush maskRegisters cycle with
            | none => .failure
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
                        currentFiles maskRegisters destination destinationContext bus cycle
                        currentState.maskDirective hasSingleLineMask
                      let nextBar0 := match barUpdate with
                        | some (false, value) => value
                        | _ => currentBar0
                      let nextBar1 := match barUpdate with
                        | some (true, value) => value
                        | _ => currentBar1
                      writeDestinations remaining nextFiles nextBar0 nextBar1
                match writeDestinations access.destinations files bar0 bar1 with
                | none => .failure
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
              match resolveFlushSelection? expression.flush maskRegisters cycle with
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
            executeParsedL1ToPEAtPEs readState next expression access rest noForward
              hasSingleLineMask usePreIssueMask

theorem executeParsedL1ToPEAtPEs_initial_turnaround_failure
    (currentState : State) (expression : ParsedExpr) (access : ParsedL1ToPEAccess)
    (pe : PEId) (rest : List PEId) (noForward hasSingleLineMask usePreIssueMask : Bool)
    (sourceIsTurnaround : access.sourceBase.isNone = true) :
    executeParsedL1ToPEAtPEs rustSimulatorInitialState currentState expression access (pe :: rest)
      noForward hasSingleLineMask usePreIssueMask = .failure := by
  simp [executeParsedL1ToPEAtPEs, sourceIsTurnaround, rustSimulatorInitialState]

def executeParsedL1ToPEProducer (readState currentState : State)
    (expression : ParsedExpr) (noForward hasSingleLineMask usePreIssueMask : Bool) :
    ProofsLean.StepResult State :=
  match lowerParsedL1ToPE? expression with
  | none => .failure
  | some access => executeParsedL1ToPEAtPEs readState currentState expression access
      (List.finRange 4096) noForward hasSingleLineMask usePreIssueMask

def forwardingValueValid : Forwarding.Value IntegerALU.Bus → Bool
  | .known _ => true
  | .poison => false
  | .unknown => true

theorem unknown_forwarding_value_keeps_slot_enabled :
    forwardingValueValid (.unknown : Forwarding.Value IntegerALU.Bus) = true := rfl

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
  | .ok advanced => .ok advanced

theorem updateSupportedPELineForwarding_absent_l1ToPE_preserves
    (old prepared : Forwarding.Slots) :
    updateSupportedPELineForwarding old prepared false false false false =
      .ok (fun unit cycle => match unit with
        | .alu | .mau => .poison
        | .matrixRead => .known ⟨0, 0⟩
        | .l1ToPE => old unit cycle) := by
  unfold updateSupportedPELineForwarding
  simp only [Forwarding.advanceReference]
  congr 1
  funext unit cycle
  cases unit <;> rfl

def updateIntegerLineForwardingValid
    (old : Forwarding.Unit → Fin 4 → Bool)
    (slots : Forwarding.Slots) (noForward : Bool) :
    Forwarding.Unit → Fin 4 → Bool :=
  fun unit cycle =>
    if noForward then old unit cycle
    else if unit = .l1ToPE then old unit cycle
    else forwardingValueValid (slots unit cycle)

theorem noforward_preserves_forwarding_validity
    (old : Forwarding.Unit → Fin 4 → Bool)
    (slots : Forwarding.Slots) :
    updateIntegerLineForwardingValid old slots true = old := by
  funext unit cycle
  simp [updateIntegerLineForwardingValid]

theorem unresolved_forwarding_output_sets_enabled_validity
    (oldValid : Forwarding.Unit → Fin 4 → Bool)
    (slots : Forwarding.Slots) (unit : Forwarding.Unit) (cycle : Fin 4)
    (notL1ToPE : unit ≠ .l1ToPE)
    (unresolved : slots unit cycle = .unknown) :
    updateIntegerLineForwardingValid oldValid slots false unit cycle = true := by
  simp [updateIntegerLineForwardingValid, unresolved, forwardingValueValid, notL1ToPE]

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

def commitParsedMatrixMAUPEState (coordinates : List (Fin 4)) (currentState : State)
    (coordinate : MABCoordinate)
    (noForward : Bool) (files : Fin 4 → PEMemory.IntegerRegisterFiles)
    (bar0 bar1 : Fin 4 → BitVec 12)
    (outputs : Fin 4 → Fin 4 → IntegerALU.Bus) (poisoned : Fin 4 → Bool) : State :=
  List.foldl (fun nextState pe =>
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
    { nextState with
      peRegisters := fun other => if other == peId then files pe else nextState.peRegisters other
      forwarding := fun other => if other == peId then forwarding else nextState.forwarding other
      forwardingValid := fun other => if other == peId then valid else nextState.forwardingValid other
      peContext := fun other => if other == peId then
        { nextState.peContext other with bar0 := bar0 pe, bar1 := bar1 pe }
        else nextState.peContext other }) currentState coordinates

theorem commitParsedMatrixMAUPEState_preserves_non_pe_state
    (coordinates : List (Fin 4)) (currentState : State)
    (coordinate : MABCoordinate) (noForward : Bool)
    (files : Fin 4 → PEMemory.IntegerRegisterFiles) (bar0 bar1 : Fin 4 → BitVec 12)
    (outputs : Fin 4 → Fin 4 → IntegerALU.Bus) (poisoned : Fin 4 → Bool) :
    let next := commitParsedMatrixMAUPEState coordinates currentState coordinate noForward
      files bar0 bar1 outputs poisoned
    (next.l1bm, next.l1bmTurnaround, next.l1bmTurnaroundValid, next.blockMemory,
      next.dar, next.darBuffer, next.darBufferReadAddress, next.darWriteAddress,
      next.mvCompletedTags, next.pendingMv, next.matrixRegisters, next.maskDirective,
      next.hazardClock) =
    (currentState.l1bm, currentState.l1bmTurnaround, currentState.l1bmTurnaroundValid,
      currentState.blockMemory, currentState.dar, currentState.darBuffer,
      currentState.darBufferReadAddress, currentState.darWriteAddress,
      currentState.mvCompletedTags, currentState.pendingMv, currentState.matrixRegisters,
      currentState.maskDirective, currentState.hazardClock) := by
  simp only [commitParsedMatrixMAUPEState]
  induction coordinates generalizing currentState with
  | nil => rfl
  | cons pe rest ih =>
      simp only [List.foldl_cons]
      rw [ih]

def writeParsedMatrixMAUDestinationsAtPE (currentState : State)
    (expression : ParsedExpr) (coordinate : MABCoordinate) (pe cycle : Fin 4)
    (poison hasSingleLineMask : Bool) (output : IntegerALU.Bus) (flags : BitVec 4) :
    List ParsedOperand → PEMemory.IntegerRegisterFiles → BitVec 12 → BitVec 12 →
      ProofsLean.StepResult (PEMemory.IntegerRegisterFiles × BitVec 12 × BitVec 12)
  | [], peFiles, peBar0, peBar1 => .ok (peFiles, peBar0, peBar1)
  | destination :: rest, peFiles, peBar0, peBar1 => Id.run do
      let peId := physicalPEId coordinate pe
      let oldContext := currentState.peContext peId
      let contextBase := ParsedIntegerContext.ofLinearIndex peId
      let context := { contextBase with
        cycle := cycle
        bar0 := peBar0
        bar1 := peBar1
        tWord := oldContext.tWord }
      match destination with
      | .omr entry _ =>
          if entry.val == 0 || entry.val > 15 then return .failure
      | _ => pure ()
      let dataPoisonApplies := parsedMatrixMAUDestinationDataPoisonApplies poison destination
      if dataPoisonApplies then
        match parsedMatrixMAUDestinationEnabled? peFiles destination context cycle
            currentState.maskDirective hasSingleLineMask with
        | none => return .failure
        | some true => return .failure
        | some false =>
            return writeParsedMatrixMAUDestinationsAtPE currentState expression coordinate pe
              cycle poison hasSingleLineMask output flags rest peFiles peBar0 peBar1
      match writeParsedMslMsrDestination? peFiles destination context output flags cycle
          currentState.maskDirective hasSingleLineMask with
      | none => return .failure
      | some write =>
          let nextBar0 := match write.barUpdate with
            | some (false, value) => value
            | _ => peBar0
          let nextBar1 := match write.barUpdate with
            | some (true, value) => value
            | _ => peBar1
          return writeParsedMatrixMAUDestinationsAtPE currentState expression coordinate pe
            cycle poison hasSingleLineMask output flags rest write.files nextBar0 nextBar1

theorem writeParsedMatrixMAUDestinationsAtPE_never_unknown
    (currentState : State) (expression : ParsedExpr) (coordinate : MABCoordinate)
    (pe cycle : Fin 4) (poison hasSingleLineMask : Bool)
    (output : IntegerALU.Bus) (flags : BitVec 4) (destinations : List ParsedOperand)
    (files : PEMemory.IntegerRegisterFiles) (bar0 bar1 : BitVec 12) :
    writeParsedMatrixMAUDestinationsAtPE currentState expression coordinate pe cycle poison
      hasSingleLineMask output flags destinations files bar0 bar1 ≠ .unknown := by
  induction destinations generalizing files bar0 bar1 with
  | nil => simp [writeParsedMatrixMAUDestinationsAtPE]
  | cons destination rest ih =>
      simp only [writeParsedMatrixMAUDestinationsAtPE]
      split <;> simp_all [parsedMatrixMAUDestinationDataPoisonApplies]
      all_goals split <;> simp_all
      all_goals split <;> simp_all
      all_goals first | exact ih _ _ _ | simp_all

structure ParsedMatrixMAUWriteAccum where
  files : Fin 4 → PEMemory.IntegerRegisterFiles
  bar0 : Fin 4 → BitVec 12
  bar1 : Fin 4 → BitVec 12
  outputs : Fin 4 → Fin 4 → IntegerALU.Bus
  poisoned : Fin 4 → Bool


def executeParsedMatrixMAUPEWritesAtCycle (currentState : State)
    (expression : ParsedExpr) (coordinate : MABCoordinate) (hasSingleLineMask : Bool)
    (cycle : Fin 4) (buses : Fin 4 → IntegerALU.Bus)
    (flags : Fin 4 → BitVec 4) (poison : Bool) :
    List (Fin 4) → ParsedMatrixMAUWriteAccum →
      ProofsLean.StepResult ParsedMatrixMAUWriteAccum
  | [], accum => .ok accum
  | pe :: rest, accum =>
      match resolveFlushSelection? expression.flush (accum.files pe).maskRegisters cycle with
      | none => .failure
      | some flushSelection =>
          let output := parsedOutputAfterFlush flushSelection (buses pe)
          match writeParsedMatrixMAUDestinationsAtPE currentState expression coordinate pe cycle
              poison hasSingleLineMask output (flags pe) expression.destinations
              (accum.files pe) (accum.bar0 pe) (accum.bar1 pe) with
          | .failure => .failure
          | .unknown => .unknown
          | .ok (nextFiles, nextBar0, nextBar1) =>
              executeParsedMatrixMAUPEWritesAtCycle currentState expression coordinate
                hasSingleLineMask cycle buses flags poison rest
                { files := fun index => if index == pe then nextFiles else accum.files index
                  bar0 := fun index => if index == pe then nextBar0 else accum.bar0 index
                  bar1 := fun index => if index == pe then nextBar1 else accum.bar1 index
                  outputs := fun index slot =>
                    if index == pe && slot == cycle then output else accum.outputs index slot
                  poisoned := fun slot => if slot == cycle then poison else accum.poisoned slot }

theorem executeParsedMatrixMAUPEWritesAtCycle_never_unknown
    (currentState : State) (expression : ParsedExpr) (coordinate : MABCoordinate)
    (hasSingleLineMask : Bool) (cycle : Fin 4) (buses : Fin 4 → IntegerALU.Bus)
    (flags : Fin 4 → BitVec 4) (poison : Bool) (pes : List (Fin 4))
    (accum : ParsedMatrixMAUWriteAccum) :
    executeParsedMatrixMAUPEWritesAtCycle currentState expression coordinate
      hasSingleLineMask cycle buses flags poison pes accum ≠ .unknown := by
  induction pes generalizing accum with
  | nil => simp [executeParsedMatrixMAUPEWritesAtCycle]
  | cons pe rest ih =>
      cases flush : resolveFlushSelection? expression.flush
          (accum.files pe).maskRegisters cycle with
      | none => simp [executeParsedMatrixMAUPEWritesAtCycle, flush]
      | some selection =>
          have writeKnown := writeParsedMatrixMAUDestinationsAtPE_never_unknown
            currentState expression coordinate pe cycle poison hasSingleLineMask
            (parsedOutputAfterFlush selection (buses pe)) (flags pe)
            expression.destinations (accum.files pe) (accum.bar0 pe) (accum.bar1 pe)
          cases write : writeParsedMatrixMAUDestinationsAtPE currentState expression
              coordinate pe cycle poison hasSingleLineMask
              (parsedOutputAfterFlush selection (buses pe)) (flags pe)
              expression.destinations (accum.files pe) (accum.bar0 pe) (accum.bar1 pe) with
          | failure => simp [executeParsedMatrixMAUPEWritesAtCycle, flush, write]
          | unknown => exact (writeKnown write).elim
          | ok next =>
              simpa [executeParsedMatrixMAUPEWritesAtCycle, flush, write] using
                ih ({ files := fun index => if index == pe then next.1 else accum.files index
                      bar0 := fun index => if index == pe then next.2.1 else accum.bar0 index
                      bar1 := fun index => if index == pe then next.2.2 else accum.bar1 index
                      outputs := fun index slot => if index == pe && slot == cycle then
                        parsedOutputAfterFlush selection (buses pe) else accum.outputs index slot
                      poisoned := fun slot => if slot == cycle then poison else accum.poisoned slot })

def executeParsedMatrixMAUWriteCycles (readState currentState : State)
    (expression : ParsedExpr) (coordinate : MABCoordinate) (hasSingleLineMask : Bool) :
    List (Fin 4) → ParsedMatrixMAUWriteAccum →
      ProofsLean.StepResult ParsedMatrixMAUWriteAccum
  | [], accum => .ok accum
  | cycle :: rest, accum =>
      match executeParsedMatrixMAUAtMAB readState coordinate expression cycle with
      | .failure => .failure
      | .unknown => .unknown
      | .ok (buses, flags, poison) =>
          match executeParsedMatrixMAUPEWritesAtCycle currentState expression coordinate
              hasSingleLineMask cycle buses flags poison (List.finRange 4) accum with
          | .failure => .failure
          | .unknown => .unknown
          | .ok next =>
              executeParsedMatrixMAUWriteCycles readState currentState expression coordinate
                hasSingleLineMask rest next

theorem executeParsedMatrixMAUWriteCycles_never_unknown
    (readState currentState : State) (expression : ParsedExpr) (coordinate : MABCoordinate)
    (hasSingleLineMask : Bool) (cycles : List (Fin 4)) (accum : ParsedMatrixMAUWriteAccum)
    (known : ∀ cycle ∈ cycles,
      executeParsedMatrixMAUAtMAB readState coordinate expression cycle ≠ .unknown) :
    executeParsedMatrixMAUWriteCycles readState currentState expression coordinate
      hasSingleLineMask cycles accum ≠ .unknown := by
  induction cycles generalizing accum with
  | nil => simp [executeParsedMatrixMAUWriteCycles]
  | cons cycle rest ih =>
      have headKnown := known cycle (by simp)
      have tailKnown : ∀ item ∈ rest,
          executeParsedMatrixMAUAtMAB readState coordinate expression item ≠ .unknown := by
        intro item member
        exact known item (List.mem_cons_of_mem _ member)
      cases output : executeParsedMatrixMAUAtMAB readState coordinate expression cycle with
      | failure => simp [executeParsedMatrixMAUWriteCycles, output]
      | unknown => exact (headKnown output).elim
      | ok result =>
          have peWritesKnown := executeParsedMatrixMAUPEWritesAtCycle_never_unknown
            currentState expression coordinate hasSingleLineMask cycle result.1 result.2.1
            result.2.2 (List.finRange 4) accum
          cases writes : executeParsedMatrixMAUPEWritesAtCycle currentState expression
              coordinate hasSingleLineMask cycle result.1 result.2.1 result.2.2
              (List.finRange 4) accum with
          | failure => simp [executeParsedMatrixMAUWriteCycles, output, writes]
          | unknown => exact (peWritesKnown writes).elim
          | ok next =>
              simpa [executeParsedMatrixMAUWriteCycles, output, writes] using
                ih next tailKnown


def executeParsedMatrixMAUPEWritesAtMAB (readState currentState : State)
    (expression : ParsedExpr) (coordinate : MABCoordinate)
    (hasSingleLineMask : Bool) : ProofsLean.StepResult
      ((Fin 4 → PEMemory.IntegerRegisterFiles) × (Fin 4 → BitVec 12) ×
        (Fin 4 → BitVec 12) × (Fin 4 → Fin 4 → IntegerALU.Bus) × (Fin 4 → Bool)) :=
  match executeParsedMatrixMAUWriteCycles readState currentState expression coordinate
      hasSingleLineMask (List.finRange 4)
      { files := fun pe => currentState.peRegisters (physicalPEId coordinate pe)
        bar0 := fun pe => currentState.peContext (physicalPEId coordinate pe) |>.bar0
        bar1 := fun pe => currentState.peContext (physicalPEId coordinate pe) |>.bar1
        outputs := fun _ _ => ⟨0, 0⟩
        poisoned := fun _ => false } with
  | .failure => .failure
  | .unknown => .unknown
  | .ok accum => .ok (accum.files, accum.bar0, accum.bar1, accum.outputs, accum.poisoned)

theorem executeParsedMatrixMAUPEWritesAtMAB_known_never_unknown
    (readState currentState : State) (expression : ParsedExpr) (coordinate : MABCoordinate)
    (hasSingleLineMask : Bool)
    (known : ∀ cycle : Fin 4,
      executeParsedMatrixMAUAtMAB readState coordinate expression cycle ≠ .unknown) :
    executeParsedMatrixMAUPEWritesAtMAB readState currentState expression coordinate
      hasSingleLineMask ≠ .unknown := by
  simp only [executeParsedMatrixMAUPEWritesAtMAB]
  cases result : executeParsedMatrixMAUWriteCycles readState currentState expression
      coordinate hasSingleLineMask (List.finRange 4)
      { files := fun pe => currentState.peRegisters (physicalPEId coordinate pe)
        bar0 := fun pe => currentState.peContext (physicalPEId coordinate pe) |>.bar0
        bar1 := fun pe => currentState.peContext (physicalPEId coordinate pe) |>.bar1
        outputs := fun _ _ => ⟨0, 0⟩
        poisoned := fun _ => false } with
  | failure => simp
  | unknown =>
      have resultKnown := executeParsedMatrixMAUWriteCycles_never_unknown
        readState currentState expression coordinate hasSingleLineMask (List.finRange 4)
        { files := fun pe => currentState.peRegisters (physicalPEId coordinate pe)
          bar0 := fun pe => currentState.peContext (physicalPEId coordinate pe) |>.bar0
          bar1 := fun pe => currentState.peContext (physicalPEId coordinate pe) |>.bar1
          outputs := fun _ _ => ⟨0, 0⟩
          poisoned := fun _ => false }
        (by intro cycle _; exact known cycle)
      exact (resultKnown result).elim
  | ok accum => simp

theorem executeParsedMatrixMAUPEWritesAtMAB_mul_lowered_never_unknown
    (readState currentState : State) (coordinate : MABCoordinate)
    (precision : ParsedPrecision) (half : Option Char) (round : Bool)
    (sideY : Bool) (width : Fin 5) (source : ParsedOperand)
    (hasSingleLineMask : Bool) (format : RRN.FloatPrecision)
    (formatLowered : parsedMatrixMAUFloatFormat precision = some format)
    (lowered : ∀ cycle : Fin 4,
      parsedFloatMAUSourceLoweredAtMAB readState coordinate source cycle)
    (resolved : forwardingSourceResolved readState) :
    executeParsedMatrixMAUPEWritesAtMAB readState currentState
      { op := .mau precision true .mul half round
        sources := [.matrix sideY width none, source]
        destinations := []
        flush := none
        text := "" } coordinate hasSingleLineMask ≠ .unknown := by
  apply executeParsedMatrixMAUPEWritesAtMAB_known_never_unknown
  intro cycle
  have calculationKnown := executeParsedMatrixMAUCalculationAtMAB_mul_lowered_reads_never_unknown
    readState coordinate precision half round sideY width source cycle format formatLowered
    (lowered cycle) resolved
  exact executeParsedMatrixMAUAtMAB_calculation_known_never_unknown
    readState coordinate _ cycle calculationKnown ⟨precision, .mul, half, round, rfl⟩

theorem executeParsedMatrixMAUPEWritesAtMAB_add_lowered_never_unknown
    (readState currentState : State) (coordinate : MABCoordinate)
    (precision : ParsedPrecision) (half : Option Char) (round : Bool)
    (sideY : Bool) (width : Fin 5) (source : ParsedOperand)
    (hasSingleLineMask : Bool) (format : RRN.FloatPrecision)
    (formatLowered : parsedMatrixMAUFloatFormat precision = some format)
    (lowered : ∀ cycle : Fin 4,
      parsedFloatMAUSourceLoweredAtMAB readState coordinate source cycle)
    (resolved : forwardingSourceResolved readState) :
    executeParsedMatrixMAUPEWritesAtMAB readState currentState
      { op := .mau precision true .add half round
        sources := [.matrix sideY width none, source]
        destinations := []
        flush := none
        text := "" } coordinate hasSingleLineMask ≠ .unknown := by
  apply executeParsedMatrixMAUPEWritesAtMAB_known_never_unknown
  intro cycle
  have calculationKnown := executeParsedMatrixMAUCalculationAtMAB_add_lowered_reads_never_unknown
    readState coordinate precision half round sideY width source cycle format formatLowered
    (lowered cycle) resolved
  exact executeParsedMatrixMAUAtMAB_calculation_known_never_unknown
    readState coordinate _ cycle calculationKnown ⟨precision, .add, half, round, rfl⟩

theorem executeParsedMatrixMAUPEWritesAtMAB_passa_lowered_never_unknown
    (readState currentState : State) (coordinate : MABCoordinate)
    (precision : ParsedPrecision) (half : Option Char) (round : Bool)
    (sideY : Bool) (width : Fin 5) (source : ParsedOperand)
    (hasSingleLineMask : Bool) (format : RRN.FloatPrecision)
    (formatLowered : parsedMatrixMAUFloatFormat precision = some format)
    (lowered : ∀ cycle : Fin 4,
      parsedFloatMAUSourceLoweredAtMAB readState coordinate source cycle)
    (resolved : forwardingSourceResolved readState) :
    executeParsedMatrixMAUPEWritesAtMAB readState currentState
      { op := .mau precision true .passa half round
        sources := [.matrix sideY width none, source]
        destinations := []
        flush := none
        text := "" } coordinate hasSingleLineMask ≠ .unknown := by
  apply executeParsedMatrixMAUPEWritesAtMAB_known_never_unknown
  intro cycle
  have calculationKnown := executeParsedMatrixMAUCalculationAtMAB_passa_lowered_reads_never_unknown
    readState coordinate precision half round sideY width source cycle format formatLowered
    (lowered cycle) resolved
  exact executeParsedMatrixMAUAtMAB_calculation_known_never_unknown
    readState coordinate _ cycle calculationKnown ⟨precision, .passa, half, round, rfl⟩

theorem executeParsedMatrixMAUPEWritesAtMAB_fma_lowered_never_unknown
    (readState currentState : State) (coordinate : MABCoordinate)
    (precision : ParsedPrecision) (half : Option Char) (round : Bool)
    (sideY : Bool) (width : Fin 5) (vectorSource accumulatorSource : ParsedOperand)
    (hasSingleLineMask : Bool) (format : RRN.FloatPrecision)
    (formatLowered : parsedMatrixMAUFloatFormat precision = some format)
    (vectorLowered : ∀ cycle : Fin 4,
      parsedFloatMAUSourceLoweredAtMAB readState coordinate vectorSource cycle)
    (accumulatorLowered : ∀ cycle : Fin 4,
      parsedFloatMAUSourceLoweredAtMAB readState coordinate accumulatorSource cycle)
    (resolved : forwardingSourceResolved readState) :
    executeParsedMatrixMAUPEWritesAtMAB readState currentState
      { op := .mau precision true .fma half round
        sources := [.matrix sideY width none, vectorSource, accumulatorSource]
        destinations := []
        flush := none
        text := "" } coordinate hasSingleLineMask ≠ .unknown := by
  apply executeParsedMatrixMAUPEWritesAtMAB_known_never_unknown
  intro cycle
  have calculationKnown := executeParsedMatrixMAUCalculationAtMAB_fma_lowered_reads_never_unknown
    readState coordinate precision half round sideY width vectorSource accumulatorSource cycle
    format formatLowered (vectorLowered cycle) (accumulatorLowered cycle) resolved
  exact executeParsedMatrixMAUAtMAB_calculation_known_never_unknown
    readState coordinate _ cycle calculationKnown ⟨precision, .fma, half, round, rfl⟩

def executeParsedMatrixMAUTransitionAtMAB (readState currentState : State)
    (expression : ParsedExpr) (coordinate : MABCoordinate)
    (noForward hasSingleLineMask : Bool) : ProofsLean.StepResult State :=
  match executeParsedMatrixMAUPEWritesAtMAB readState currentState expression coordinate
      hasSingleLineMask with
  | .failure => .failure
  | .unknown => .unknown
  | .ok (files, bar0, bar1, outputs, poisoned) =>
      .ok (commitParsedMatrixMAUPEState (List.finRange 4) currentState coordinate noForward
        files bar0 bar1 outputs poisoned)

theorem executeParsedMatrixMAUTransitionAtMAB_known_never_unknown
    (readState currentState : State) (expression : ParsedExpr)
    (coordinate : MABCoordinate) (noForward hasSingleLineMask : Bool)
    (writesKnown : executeParsedMatrixMAUPEWritesAtMAB readState currentState
      expression coordinate hasSingleLineMask ≠ .unknown) :
    executeParsedMatrixMAUTransitionAtMAB readState currentState expression coordinate
      noForward hasSingleLineMask ≠ .unknown := by
  cases writes : executeParsedMatrixMAUPEWritesAtMAB readState currentState expression
      coordinate hasSingleLineMask with
  | failure => simp [executeParsedMatrixMAUTransitionAtMAB, writes]
  | unknown => exact (writesKnown writes).elim
  | ok result => simp [executeParsedMatrixMAUTransitionAtMAB, writes]

theorem commitParsedMatrixMAUPEState_preserves_matrix_registers
    (coordinates : List (Fin 4)) (currentState : State)
    (coordinate : MABCoordinate) (noForward : Bool)
    (files : Fin 4 → PEMemory.IntegerRegisterFiles) (bar0 bar1 : Fin 4 → BitVec 12)
    (outputs : Fin 4 → Fin 4 → IntegerALU.Bus) (poisoned : Fin 4 → Bool) :
    (commitParsedMatrixMAUPEState coordinates currentState coordinate noForward files bar0 bar1
      outputs poisoned).matrixRegisters = currentState.matrixRegisters := by
  simp only [commitParsedMatrixMAUPEState]
  induction coordinates generalizing currentState with
  | nil => rfl
  | cons pe rest ih =>
      simp only [List.foldl_cons]
      rw [ih]

theorem executeParsedMatrixMAUTransitionAtMAB_preserves_matrix_registers
    (readState currentState : State) (expression : ParsedExpr)
    (coordinate : MABCoordinate) (noForward hasSingleLineMask : Bool)
    (next : State)
    (executed : executeParsedMatrixMAUTransitionAtMAB readState currentState
      expression coordinate noForward hasSingleLineMask = .ok next) :
    next.matrixRegisters = currentState.matrixRegisters := by
  simp only [executeParsedMatrixMAUTransitionAtMAB] at executed
  cases writes : executeParsedMatrixMAUPEWritesAtMAB readState currentState expression
      coordinate hasSingleLineMask with
  | failure => simp [writes] at executed
  | unknown => simp [writes] at executed
  | ok result =>
      simp only [writes] at executed
      injection executed with nextEq
      subst next
      exact commitParsedMatrixMAUPEState_preserves_matrix_registers
        (List.finRange 4) currentState coordinate noForward
        result.1 result.2.1 result.2.2.1 result.2.2.2.1 result.2.2.2.2

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

theorem executeParsedMatrixMAUAtMABs_known_never_unknown
    (readState currentState : State) (expression : ParsedExpr)
    (coordinates : List MABCoordinate) (noForward hasSingleLineMask : Bool)
    (known : ∀ (state : State) coordinate, coordinate ∈ coordinates →
      executeParsedMatrixMAUTransitionAtMAB readState state expression coordinate
        noForward hasSingleLineMask ≠ .unknown) :
    executeParsedMatrixMAUAtMABs readState currentState expression coordinates
      noForward hasSingleLineMask ≠ .unknown := by
  induction coordinates generalizing currentState with
  | nil => simp [executeParsedMatrixMAUAtMABs]
  | cons coordinate rest ih =>
      have headKnown := known currentState coordinate (by simp)
      have tailKnown : ∀ (state : State) item, item ∈ rest →
          executeParsedMatrixMAUTransitionAtMAB readState state expression item
            noForward hasSingleLineMask ≠ .unknown := by
        intro state item member
        exact known state item (List.mem_cons_of_mem _ member)
      cases transition : executeParsedMatrixMAUTransitionAtMAB readState currentState
          expression coordinate noForward hasSingleLineMask with
      | failure => simp [executeParsedMatrixMAUAtMABs, transition]
      | unknown => exact (headKnown transition).elim
      | ok next =>
          simpa [executeParsedMatrixMAUAtMABs, transition] using
            ih next (fun state item member => tailKnown state item member)

theorem executeParsedMatrixMAUAtMABs_mul_lowered_never_unknown
    (readState currentState : State) (coordinates : List MABCoordinate)
    (precision : ParsedPrecision) (half : Option Char) (round : Bool)
    (sideY : Bool) (width : Fin 5) (source : ParsedOperand)
    (noForward hasSingleLineMask : Bool) (format : RRN.FloatPrecision)
    (formatLowered : parsedMatrixMAUFloatFormat precision = some format)
    (lowered : ∀ coordinate, coordinate ∈ coordinates → ∀ cycle : Fin 4,
      parsedFloatMAUSourceLoweredAtMAB readState coordinate source cycle)
    (resolved : forwardingSourceResolved readState) :
    executeParsedMatrixMAUAtMABs readState currentState
      { op := .mau precision true .mul half round
        sources := [.matrix sideY width none, source]
        destinations := []
        flush := none
        text := "" }
      coordinates noForward hasSingleLineMask ≠ .unknown := by
  apply executeParsedMatrixMAUAtMABs_known_never_unknown
  intro intermediate coordinate member
  apply executeParsedMatrixMAUTransitionAtMAB_known_never_unknown
  exact executeParsedMatrixMAUPEWritesAtMAB_mul_lowered_never_unknown
    readState intermediate coordinate precision half round sideY width source
    hasSingleLineMask format formatLowered (lowered coordinate member) resolved

theorem executeParsedMatrixMAUAtMABs_add_lowered_never_unknown
    (readState currentState : State) (coordinates : List MABCoordinate)
    (precision : ParsedPrecision) (half : Option Char) (round : Bool)
    (sideY : Bool) (width : Fin 5) (source : ParsedOperand)
    (noForward hasSingleLineMask : Bool) (format : RRN.FloatPrecision)
    (formatLowered : parsedMatrixMAUFloatFormat precision = some format)
    (lowered : ∀ coordinate, coordinate ∈ coordinates → ∀ cycle : Fin 4,
      parsedFloatMAUSourceLoweredAtMAB readState coordinate source cycle)
    (resolved : forwardingSourceResolved readState) :
    executeParsedMatrixMAUAtMABs readState currentState
      { op := .mau precision true .add half round
        sources := [.matrix sideY width none, source]
        destinations := []
        flush := none
        text := "" }
      coordinates noForward hasSingleLineMask ≠ .unknown := by
  apply executeParsedMatrixMAUAtMABs_known_never_unknown
  intro intermediate coordinate member
  apply executeParsedMatrixMAUTransitionAtMAB_known_never_unknown
  exact executeParsedMatrixMAUPEWritesAtMAB_add_lowered_never_unknown
    readState intermediate coordinate precision half round sideY width source
    hasSingleLineMask format formatLowered (lowered coordinate member) resolved

theorem executeParsedMatrixMAUAtMABs_passa_lowered_never_unknown
    (readState currentState : State) (coordinates : List MABCoordinate)
    (precision : ParsedPrecision) (half : Option Char) (round : Bool)
    (sideY : Bool) (width : Fin 5) (source : ParsedOperand)
    (noForward hasSingleLineMask : Bool) (format : RRN.FloatPrecision)
    (formatLowered : parsedMatrixMAUFloatFormat precision = some format)
    (lowered : ∀ coordinate, coordinate ∈ coordinates → ∀ cycle : Fin 4,
      parsedFloatMAUSourceLoweredAtMAB readState coordinate source cycle)
    (resolved : forwardingSourceResolved readState) :
    executeParsedMatrixMAUAtMABs readState currentState
      { op := .mau precision true .passa half round
        sources := [.matrix sideY width none, source]
        destinations := []
        flush := none
        text := "" }
      coordinates noForward hasSingleLineMask ≠ .unknown := by
  apply executeParsedMatrixMAUAtMABs_known_never_unknown
  intro intermediate coordinate member
  apply executeParsedMatrixMAUTransitionAtMAB_known_never_unknown
  exact executeParsedMatrixMAUPEWritesAtMAB_passa_lowered_never_unknown
    readState intermediate coordinate precision half round sideY width source
    hasSingleLineMask format formatLowered (lowered coordinate member) resolved

theorem executeParsedMatrixMAUAtMABs_fma_lowered_never_unknown
    (readState currentState : State) (coordinates : List MABCoordinate)
    (precision : ParsedPrecision) (half : Option Char) (round : Bool)
    (sideY : Bool) (width : Fin 5) (vectorSource accumulatorSource : ParsedOperand)
    (noForward hasSingleLineMask : Bool) (format : RRN.FloatPrecision)
    (formatLowered : parsedMatrixMAUFloatFormat precision = some format)
    (vectorLowered : ∀ coordinate, coordinate ∈ coordinates → ∀ cycle : Fin 4,
      parsedFloatMAUSourceLoweredAtMAB readState coordinate vectorSource cycle)
    (accumulatorLowered : ∀ coordinate, coordinate ∈ coordinates → ∀ cycle : Fin 4,
      parsedFloatMAUSourceLoweredAtMAB readState coordinate accumulatorSource cycle)
    (resolved : forwardingSourceResolved readState) :
    executeParsedMatrixMAUAtMABs readState currentState
      { op := .mau precision true .fma half round
        sources := [.matrix sideY width none, vectorSource, accumulatorSource]
        destinations := []
        flush := none
        text := "" }
      coordinates noForward hasSingleLineMask ≠ .unknown := by
  apply executeParsedMatrixMAUAtMABs_known_never_unknown
  intro intermediate coordinate member
  apply executeParsedMatrixMAUTransitionAtMAB_known_never_unknown
  exact executeParsedMatrixMAUPEWritesAtMAB_fma_lowered_never_unknown
    readState intermediate coordinate precision half round sideY width vectorSource
    accumulatorSource hasSingleLineMask format formatLowered
    (vectorLowered coordinate member) (accumulatorLowered coordinate member) resolved

theorem executeParsedMatrixMAUAtMABs_preserves_matrix_registers
    (readState currentState next : State) (expression : ParsedExpr)
    (coordinates : List MABCoordinate) (noForward hasSingleLineMask : Bool)
    (executed : executeParsedMatrixMAUAtMABs readState currentState expression
      coordinates noForward hasSingleLineMask = .ok next) :
    next.matrixRegisters = currentState.matrixRegisters := by
  induction coordinates generalizing currentState with
  | nil =>
      simp [executeParsedMatrixMAUAtMABs] at executed
      cases executed
      rfl
  | cons coordinate rest ih =>
      simp only [executeParsedMatrixMAUAtMABs] at executed
      cases transition : executeParsedMatrixMAUTransitionAtMAB readState currentState
          expression coordinate noForward hasSingleLineMask with
      | failure => simp [transition] at executed
      | unknown => simp [transition] at executed
      | ok intermediate =>
          have remaining : executeParsedMatrixMAUAtMABs readState intermediate
              expression rest noForward hasSingleLineMask = .ok next := by
            simpa [transition] using executed
          have restFrame := ih intermediate remaining
          have transitionFrame :=
            executeParsedMatrixMAUTransitionAtMAB_preserves_matrix_registers
              readState currentState expression coordinate noForward hasSingleLineMask
              intermediate transition
          exact restFrame.trans transitionFrame

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

theorem propagateParsedMatrixMAUPoison_preserves_matrix_registers (state : State) :
    (propagateParsedMatrixMAUPoison state).matrixRegisters = state.matrixRegisters := by
  by_cases hasPoison : parsedStateHasMatrixMAUPoison state = true <;>
    simp [propagateParsedMatrixMAUPoison, hasPoison]

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

theorem executeParsedMatrixMAUProducer_preserves_matrix_registers
    (readState currentState next : State) (expressions : List ParsedExpr)
    (noForward hasSingleLineMask : Bool)
    (executed : executeParsedMatrixMAUProducer readState currentState expressions
      noForward hasSingleLineMask = .ok next) :
    next.matrixRegisters = currentState.matrixRegisters := by
  cases filtered : expressions.filter parsedExprIsMatrixMAUProducer with
  | nil =>
      simp [executeParsedMatrixMAUProducer, filtered] at executed
      cases executed
      rfl
  | cons expression rest =>
      cases rest with
      | nil =>
          simp only [executeParsedMatrixMAUProducer, filtered] at executed
          cases execution : executeParsedMatrixMAUAtMABs readState currentState expression
              allMABCoordinates noForward hasSingleLineMask with
          | failure => simp [execution] at executed
          | unknown => simp [execution] at executed
          | ok intermediate =>
              simp only [execution] at executed
              have outputFrame := congrArg (fun result : ProofsLean.StepResult State =>
                match result with
                | .ok value => value.matrixRegisters
                | .failure | .unknown => currentState.matrixRegisters) executed
              simp only at outputFrame
              have mauFrame := executeParsedMatrixMAUAtMABs_preserves_matrix_registers
                readState currentState intermediate expression allMABCoordinates
                noForward hasSingleLineMask execution
              have poisonFrame := propagateParsedMatrixMAUPoison_preserves_matrix_registers
                intermediate
              exact outputFrame.symm.trans (poisonFrame.trans mauFrame)
      | cons second remaining =>
          simp [executeParsedMatrixMAUProducer, filtered] at executed

def executeParsedMatrixMAUAndWrites (readState currentState : State)
    (expressions : List ParsedExpr) (noForward hasSingleLineMask : Bool) :
    ProofsLean.StepResult State :=
  match executeParsedMatrixMAUProducer readState currentState expressions
      noForward hasSingleLineMask with
  | .failure => .failure
  | .unknown => .unknown
  | .ok afterMAU =>
      executeParsedMatrixWritesAtMABs readState allMABCoordinates expressions afterMAU

theorem executeParsedMatrixMAUAndWrites_preserves_post_mau_pe_state
    (readState currentState afterMAU next : State) (expressions : List ParsedExpr)
    (noForward hasSingleLineMask : Bool)
    (mauExecuted : executeParsedMatrixMAUProducer readState currentState expressions
      noForward hasSingleLineMask = .ok afterMAU)
    (executed : executeParsedMatrixMAUAndWrites readState currentState expressions
      noForward hasSingleLineMask = .ok next) :
    next.peRegisters = afterMAU.peRegisters ∧
      next.forwarding = afterMAU.forwarding ∧
      next.forwardingValid = afterMAU.forwardingValid ∧
      next.peContext = afterMAU.peContext := by
  simp only [executeParsedMatrixMAUAndWrites, mauExecuted] at executed
  exact executeParsedMatrixWritesAtMABs_preserves_pe_state readState afterMAU next
    allMABCoordinates expressions executed

def executeParsedBlockFloatAtMAB (readState currentState : State)
    (expression : ParsedExpr) (coordinate : MABCoordinate)
    (noForward hasSingleLineMask : Bool) : ProofsLean.StepResult State := Id.run do
  let some accesses := lowerParsedBlockFloat? expression | return .failure
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

/-- A block-float producer that cannot be lowered to its supported source and
destination shape is a known execution failure, not an unresolved value. -/
theorem executeParsedBlockFloatAtMAB_lowering_failure
    (readState currentState : State) (expression : ParsedExpr)
    (coordinate : MABCoordinate) (noForward hasSingleLineMask : Bool)
    (notLowered : lowerParsedBlockFloat? expression = none) :
    executeParsedBlockFloatAtMAB readState currentState expression coordinate
      noForward hasSingleLineMask = .failure := by
  simp [executeParsedBlockFloatAtMAB, notLowered]

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
  | _ => .failure

theorem executeParsedBlockFloatProducer_multiple_fail
    (readState currentState : State) (first second : ParsedExpr) (rest : List ParsedExpr)
    (noForward hasSingleLineMask : Bool)
    (multiple : List.filter parsedExprIsBlockFloatProducer (first :: second :: rest) =
      first :: second :: rest) :
    executeParsedBlockFloatProducer readState currentState (first :: second :: rest)
      noForward hasSingleLineMask = .failure := by
  simp [executeParsedBlockFloatProducer, multiple]

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
  let some (isMsl, destinations) := lowerParsedMslMsr? expression | return .failure
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

/-- An MSL/MSR expression with an unsupported source or destination shape is a
known execution failure; unresolved values read from forwarding remain unknown. -/
theorem executeParsedMslMsrAtPE_lowering_failure
    (readState currentState : State) (expression : ParsedExpr) (pe : PEId)
    (noForward hasSingleLineMask : Bool)
    (notLowered : lowerParsedMslMsr? expression = none) :
    executeParsedMslMsrAtPE readState currentState expression pe noForward
      hasSingleLineMask = .failure := by
  simp [executeParsedMslMsrAtPE, notLowered]

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
  | _ => .failure

theorem executeParsedMslMsrProducers_multiple_fail
    (readState currentState : State) (first second : ParsedExpr) (rest : List ParsedExpr)
    (noForward hasSingleLineMask : Bool)
    (multiple : List.filter parsedExprIsMslMsrProducer (first :: second :: rest) =
      first :: second :: rest) :
    executeParsedMslMsrProducers readState currentState (first :: second :: rest)
      noForward hasSingleLineMask = .failure := by
  simp [executeParsedMslMsrProducers, multiple]

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
  | _ => .failure

theorem executeParsedFloatReluProducers_multiple_fail
    (readState currentState : State) (first second : ParsedExpr) (rest : List ParsedExpr)
    (noForward hasSingleLineMask : Bool)
    (multiple : List.filter parsedExprIsFloatReluProducer (first :: second :: rest) =
      first :: second :: rest) :
    executeParsedFloatReluProducers readState currentState (first :: second :: rest)
      noForward hasSingleLineMask = .failure := by
  simp [executeParsedFloatReluProducers, multiple]

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
    parsedExprWaitTag? expression == none &&
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
  match MVSemantics.parsedMvPendingWritesWithDAR? state.blockMemory state.dar transfer with
  | none => .failure
  | some writes =>
      if transfer.kind == .nop then .ok state
      else
        .ok { state with
          pendingMv := state.pendingMv ++ [{ tag := transfer.tag, writes := writes }]
          mvCompletedTags := fun tag =>
            if transfer.tag == some tag then false else state.mvCompletedTags tag }

/-- Remove one pending operation carrying `tag` without completing unrelated
operations. MV priority and resource contention can change completion order. -/
def removePendingMvTag : Fin 256 → List PendingMv → Option (PendingMv × List PendingMv)
  | _, [] => none
  | tag, pending :: rest =>
      if pending.tag == some tag then some (pending, rest)
      else do
        let (target, remaining) ← removePendingMvTag tag rest
        some (target, pending :: remaining)

theorem removePendingMvTag_preserves_other_operations
    (tag : Fin 256) (pending : List PendingMv) (target : PendingMv)
    (remaining : List PendingMv)
    (removed : removePendingMvTag tag pending = some (target, remaining)) :
    remaining.filter (fun operation => operation.tag != some tag) =
      pending.filter (fun operation => operation.tag != some tag) := by
  induction pending generalizing target remaining with
  | nil => simp [removePendingMvTag] at removed
  | cons head rest ih =>
      cases hmatch : head.tag == some tag with
      | true =>
          simp [removePendingMvTag, hmatch] at removed
          cases removed
          subst target
          subst remaining
          simp_all [List.filter_cons]
      | false =>
          have headDiffers : head.tag ≠ some tag := by simpa using hmatch
          cases tail : removePendingMvTag tag rest with
          | none => simp [removePendingMvTag, hmatch, tail] at removed
          | some pair =>
              rcases pair with ⟨removedHead, removedRest⟩
              simp [removePendingMvTag, hmatch, tail] at removed
              cases removed
              subst target
              subst remaining
              have preservedTail := ih removedHead removedRest tail
              have hother : (head.tag != some tag) = true := by simp [headDiffers]
              simp only [List.filter_cons, hother, ite_true, preservedTail]

def pendingMvContainsTag (tag : Fin 256) (pending : List PendingMv) : Bool :=
  pending.any fun operation => operation.tag == some tag

/-- Complete the tagged MV operation while preserving every other pending
operation and applying writes over the current memory. -/
def completePendingMvTag (state : State) (tag : Fin 256) : Option State := do
  if state.mvCompletedTags tag then return state
  let (pending, remaining) ← removePendingMvTag tag state.pendingMv
  some { state with
    blockMemory := MVSemantics.commitWrites state.blockMemory pending.writes
    pendingMv := remaining
    mvCompletedTags := fun other =>
      if other == tag then !pendingMvContainsTag tag remaining
      else state.mvCompletedTags other }

def completePendingMvTagFuel : Nat → State → Fin 256 → Option State
  | 0, state, tag => if state.mvCompletedTags tag then some state else none
  | fuel + 1, state, tag =>
      if state.mvCompletedTags tag then some state else
        match completePendingMvTag state tag with
        | none => none
        | some next => completePendingMvTagFuel fuel next tag

/-- Deterministic runner profile: complete all currently pending transfers
with this tag, preserving unrelated pending transfers. -/
def completePendingMvTagAll (state : State) (tag : Fin 256) : Option State :=
  completePendingMvTagFuel (state.pendingMv.length + 1) state tag

theorem completePendingMvTagFuel_success_completes_tag
    (fuel : Nat) (state next : State) (tag : Fin 256)
    (completed : completePendingMvTagFuel fuel state tag = some next) :
    next.mvCompletedTags tag = true := by
  induction fuel generalizing state next with
  | zero =>
      by_cases already : state.mvCompletedTags tag
      · simp [completePendingMvTagFuel, already] at completed
        cases completed
        exact already
      · simp [completePendingMvTagFuel, already] at completed
  | succ fuel ih =>
      by_cases already : state.mvCompletedTags tag
      · simp [completePendingMvTagFuel, already] at completed
        cases completed
        exact already
      · cases step : completePendingMvTag state tag with
        | none => simp [completePendingMvTagFuel, already, step] at completed
        | some intermediate =>
            simp [completePendingMvTagFuel, already, step] at completed
            exact ih intermediate next completed

theorem completePendingMvTagAll_success_completes_tag
    (state next : State) (tag : Fin 256)
    (completed : completePendingMvTagAll state tag = some next) :
    next.mvCompletedTags tag = true := by
  exact completePendingMvTagFuel_success_completes_tag
    (state.pendingMv.length + 1) state next tag completed

theorem completePendingMvTag_success_matches_pending_queue
    (state next : State) (tag : Fin 256)
    (initiallyIncomplete : state.mvCompletedTags tag = false)
    (completed : completePendingMvTag state tag = some next) :
    next.mvCompletedTags tag = !pendingMvContainsTag tag next.pendingMv := by
  cases removed : removePendingMvTag tag state.pendingMv with
  | none => simp [completePendingMvTag, initiallyIncomplete, removed] at completed
  | some result =>
      rcases result with ⟨pending, remaining⟩
      simp [completePendingMvTag, initiallyIncomplete, removed] at completed
      cases completed
      simp [pendingMvContainsTag]

theorem completePendingMvTagFuel_of_tag_completed
    (fuel : Nat) (state : State) (tag : Fin 256)
    (completed : state.mvCompletedTags tag = true) :
    completePendingMvTagFuel fuel state tag = some state := by
  induction fuel with
  | zero => simp [completePendingMvTagFuel, completed]
  | succ fuel ih => simp [completePendingMvTagFuel, completed]

theorem completePendingMvTagFuel_success_clears_tag_queue
    (fuel : Nat) (state next : State) (tag : Fin 256)
    (initiallyIncomplete : state.mvCompletedTags tag = false)
    (completed : completePendingMvTagFuel fuel state tag = some next) :
    pendingMvContainsTag tag next.pendingMv = false := by
  induction fuel generalizing state next with
  | zero => simp [completePendingMvTagFuel, initiallyIncomplete] at completed
  | succ fuel ih =>
      cases step : completePendingMvTag state tag with
      | none => simp [completePendingMvTagFuel, initiallyIncomplete, step] at completed
      | some intermediate =>
          have queueFlag := completePendingMvTag_success_matches_pending_queue
            state intermediate tag initiallyIncomplete step
          simp [completePendingMvTagFuel, initiallyIncomplete, step] at completed
          by_cases finished : intermediate.mvCompletedTags tag = true
          · have sameIntermediate : completePendingMvTagFuel fuel intermediate tag =
                some intermediate :=
              completePendingMvTagFuel_of_tag_completed fuel intermediate tag finished
            rw [sameIntermediate] at completed
            injection completed with equal
            subst next
            have noTag : pendingMvContainsTag tag intermediate.pendingMv = false := by
              rw [finished] at queueFlag
              simpa using queueFlag
            exact noTag
          · have unfinished : intermediate.mvCompletedTags tag = false := by
              cases h : intermediate.mvCompletedTags tag <;> simp_all
            exact ih intermediate next unfinished completed

theorem completePendingMvTagAll_success_clears_tag_queue
    (state next : State) (tag : Fin 256)
    (initiallyIncomplete : state.mvCompletedTags tag = false)
    (completed : completePendingMvTagAll state tag = some next) :
    pendingMvContainsTag tag next.pendingMv = false := by
  exact completePendingMvTagFuel_success_clears_tag_queue
    (state.pendingMv.length + 1) state next tag initiallyIncomplete completed

theorem completePendingMvTag_success_preserves_other_pending
    (state next : State) (tag : Fin 256)
    (initiallyIncomplete : state.mvCompletedTags tag = false)
    (completed : completePendingMvTag state tag = some next) :
    next.pendingMv.filter (fun operation => operation.tag != some tag) =
      state.pendingMv.filter (fun operation => operation.tag != some tag) := by
  cases removed : removePendingMvTag tag state.pendingMv with
  | none => simp [completePendingMvTag, initiallyIncomplete, removed] at completed
  | some result =>
      rcases result with ⟨pending, remaining⟩
      simp [completePendingMvTag, initiallyIncomplete, removed] at completed
      cases completed
      exact removePendingMvTag_preserves_other_operations tag state.pendingMv
        pending remaining removed

theorem completePendingMvTagFuel_success_preserves_other_pending
    (fuel : Nat) (state next : State) (tag : Fin 256)
    (initiallyIncomplete : state.mvCompletedTags tag = false)
    (completed : completePendingMvTagFuel fuel state tag = some next) :
    next.pendingMv.filter (fun operation => operation.tag != some tag) =
      state.pendingMv.filter (fun operation => operation.tag != some tag) := by
  induction fuel generalizing state next with
  | zero => simp [completePendingMvTagFuel, initiallyIncomplete] at completed
  | succ fuel ih =>
      cases step : completePendingMvTag state tag with
      | none => simp [completePendingMvTagFuel, initiallyIncomplete, step] at completed
      | some intermediate =>
          have oneStep := completePendingMvTag_success_preserves_other_pending
            state intermediate tag initiallyIncomplete step
          simp [completePendingMvTagFuel, initiallyIncomplete, step] at completed
          by_cases finished : intermediate.mvCompletedTags tag = true
          · have stop := completePendingMvTagFuel_of_tag_completed fuel
              intermediate tag finished
            rw [stop] at completed
            injection completed with same
            subst next
            exact oneStep
          · have stillIncomplete : intermediate.mvCompletedTags tag = false := by
              cases h : intermediate.mvCompletedTags tag <;> simp_all
            calc
              next.pendingMv.filter (fun operation => operation.tag != some tag) =
                  intermediate.pendingMv.filter (fun operation => operation.tag != some tag) :=
                    ih intermediate next stillIncomplete completed
              _ = state.pendingMv.filter (fun operation => operation.tag != some tag) := oneStep

theorem completePendingMvTagAll_success_preserves_other_pending
    (state next : State) (tag : Fin 256)
    (initiallyIncomplete : state.mvCompletedTags tag = false)
    (completed : completePendingMvTagAll state tag = some next) :
    next.pendingMv.filter (fun operation => operation.tag != some tag) =
      state.pendingMv.filter (fun operation => operation.tag != some tag) := by
  exact completePendingMvTagFuel_success_preserves_other_pending
    (state.pendingMv.length + 1) state next tag initiallyIncomplete completed

theorem completePendingMvTagAll_completes_two_same_tag
    (state : State) (tag : Fin 256)
    (firstWrites secondWrites : List (MVSemantics.Cell × BitVec 64)) :
    (completePendingMvTagAll
      { state with
        mvCompletedTags := fun other => other != tag
        pendingMv := [⟨some tag, firstWrites⟩, ⟨some tag, secondWrites⟩] } tag).map
      (fun completed => (completed.pendingMv.length, completed.mvCompletedTags tag)) =
        some (0, true) := by
  simp [completePendingMvTagAll, completePendingMvTagFuel,
    completePendingMvTag, removePendingMvTag, pendingMvContainsTag]

theorem completePendingMvTagAll_preserves_untagged_issue_between_matches
    (state : State) (tag : Fin 256)
    (firstWrites middleWrites lastWrites : List (MVSemantics.Cell × BitVec 64)) :
    (completePendingMvTagAll
      { state with
        mvCompletedTags := fun other => other != tag
        pendingMv := [⟨some tag, firstWrites⟩, ⟨none, middleWrites⟩,
          ⟨some tag, lastWrites⟩] } tag).map
      (fun completed =>
        (completed.pendingMv.map PendingMv.tag, completed.mvCompletedTags tag)) =
      some ([none], true) := by
  simp [completePendingMvTagAll, completePendingMvTagFuel,
    completePendingMvTag, removePendingMvTag, pendingMvContainsTag]

/-- Remove a pending MV by its current queue position. This also completes
untagged transfers, which cannot be named by a wait tag but still progress
asynchronously before program termination. -/
def removePendingMvAtIndex : Nat → List PendingMv → Option (PendingMv × List PendingMv)
  | _, [] => none
  | 0, pending :: rest => some (pending, rest)
  | index + 1, pending :: rest => do
      let (target, remaining) ← removePendingMvAtIndex index rest
      some (target, pending :: remaining)

def completePendingMvAtIndex (state : State) (index : Nat) :
    Option (PendingMv × State) := do
  let (pending, remaining) ← removePendingMvAtIndex index state.pendingMv
  let completedTags := match pending.tag with
    | none => state.mvCompletedTags
    | some tag => fun other =>
        if other == tag then !pendingMvContainsTag tag remaining
        else state.mvCompletedTags other
  some (pending, { state with
    blockMemory := MVSemantics.commitWrites state.blockMemory pending.writes
    pendingMv := remaining
    mvCompletedTags := completedTags })

theorem completePendingMvAtIndex_untagged_head (state : State)
    (writes : List (MVSemantics.Cell × BitVec 64)) (rest : List PendingMv) :
    completePendingMvAtIndex
      { state with pendingMv := ⟨none, writes⟩ :: rest } 0 =
        some (⟨none, writes⟩, { state with
          blockMemory := MVSemantics.commitWrites state.blockMemory writes
          pendingMv := rest }) := by
  simp [completePendingMvAtIndex, removePendingMvAtIndex]

theorem completePendingMvAtIndex_preserves_incomplete_duplicate_tag
    (state : State) (tag : Fin 256)
    (writes : List (MVSemantics.Cell × BitVec 64)) (rest : List PendingMv)
    (duplicateRemains : pendingMvContainsTag tag rest = true) :
    completePendingMvAtIndex
      { state with pendingMv := ⟨some tag, writes⟩ :: rest } 0 =
        some (⟨some tag, writes⟩, { state with
          blockMemory := MVSemantics.commitWrites state.blockMemory writes
          pendingMv := rest
          mvCompletedTags := fun other =>
            if other == tag then false else state.mvCompletedTags other }) := by
  simp [completePendingMvAtIndex, removePendingMvAtIndex, pendingMvContainsTag]
  funext other
  by_cases h : other = tag
  · subst other
    have hdup : rest.any (fun operation => operation.tag == some tag) = true := by
      simpa [pendingMvContainsTag] using duplicateRemains
    simp [hdup]
  · simp [h]

/-- Drain all remaining MV operations at program termination. -/
def completeAllPendingMvs (state : State) : State := Id.run do
  let mut memory := state.blockMemory
  let mut completed := state.mvCompletedTags
  for pending in state.pendingMv do
    memory := MVSemantics.commitWrites memory pending.writes
    match pending.tag with
    | none => pure ()
    | some tag => completed := fun other => other == tag || completed other
  return { state with blockMemory := memory, pendingMv := [], mvCompletedTags := completed }

/-- Dispatch the L1BM-to-PE producers present on a PE issue line. The issue
checker rejects multiple such producers because they conflict on L1BM emission
or turnaround state. -/
def executeParsedL1ToPEProducers (readState currentState : State)
    (expressions : List ParsedExpr) (noForward hasSingleLineMask usePreIssueMask : Bool) :
    ProofsLean.StepResult State :=
  match expressions.filter parsedExprIsL1ToPEProducer with
  | [] => .ok currentState
  | [expression] => executeParsedL1ToPEProducer readState currentState expression noForward
      hasSingleLineMask usePreIssueMask
  | _ => .failure

theorem executeParsedL1ToPEProducers_multiple_fail
    (readState currentState : State) (first second : ParsedExpr) (rest : List ParsedExpr)
    (noForward hasSingleLineMask usePreIssueMask : Bool)
    (multiple : List.filter parsedExprIsL1ToPEProducer (first :: second :: rest) =
      first :: second :: rest) :
    executeParsedL1ToPEProducers readState currentState (first :: second :: rest)
      noForward hasSingleLineMask usePreIssueMask = .failure := by
  simp [executeParsedL1ToPEProducers, multiple]

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
        if expressions.any (parsedExprWaitPending state) then .unknown
        else if expressions.any parsedExprIsUnsupportedRustAlu then .failure
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
                        match executeParsedSharedBlockProducers state next expressions (!noForward) with
                        | .failure => .failure
                        | .unknown => .unknown
                        | .ok nextWithBlocks =>
                            let l1ToPEUsesPreIssueMask :=
                              parsedL1ToPEPrecedesOMRWriter expressions
                            let afterL1ToPE := executeParsedL1ToPEProducers state nextWithBlocks
                              expressions noForward
                              (expressions.any parsedExprHasSingleLineWriteMask)
                              l1ToPEUsesPreIssueMask
                            match afterL1ToPE with
                            | .failure => .failure
                            | .unknown => .unknown
                            | .ok nextWithBroadcast =>
                              .ok { nextWithBroadcast with
                                hazardClock := nextWithBroadcast.hazardClock + InstructionLine.cost line
                                l1bmTurnaroundValid :=
                                  if noForward then nextWithBroadcast.l1bmTurnaroundValid else hasPEToL1Producer }
        else .unknown
    | .nop count wait =>
        match wait with
        | none => .ok { state with hazardClock := state.hazardClock + count.val }
        | some tag =>
            if state.mvCompletedTags tag then
              .ok { state with hazardClock := state.hazardClock + count.val }
            else .unknown
    | .mv transfer =>
        if transfer.kind == .nop then
          .ok { state with hazardClock := state.hazardClock + 1 }
        else
          match executeParsedMvMemory state transfer.toParsed with
          | .failure => .failure
          | .unknown => .unknown
          | .ok next =>
              .ok { next with
                hazardClock := next.hazardClock + 1 }

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

def parsedPEHazardControl (state : State) (pe : PEId) : ParsedMaskExecutionControl :=
  let oldContext := state.peContext pe
  let coordinates := ParsedIntegerContext.ofLinearIndex pe
  let context := { coordinates with
    bar0 := oldContext.bar0
    bar1 := oldContext.bar1
    tWord := oldContext.tWord }
  { directive := state.maskDirective
    context := context
    elapsedWords := state.hazardClock }

def parsedPEHazardEventsForPE? (state : State) (expressions : List ParsedExpr)
    (pe : PEId) : Option (List PEMemory.TimedPEAccess) := do
  let control := parsedPEHazardControl state pe
  let perExpression ← expressions.mapM fun expression =>
    PEMemory.ParsedExpr.toTimedPEHazardEvents? expression control
  some perExpression.flatten

theorem parsedPEHazardEventsForPE?_isSome_of_valid
    (state : State) (expressions : List ParsedExpr) (pe : PEId)
    (valid : expressions.all fun expression =>
      (expression.sources ++ expression.destinations).all
        PEMemory.ParsedOperand.directMemoryAddressModeValid = true) :
    (parsedPEHazardEventsForPE? state expressions pe).isSome = true := by
  let control := parsedPEHazardControl state pe
  have eventsSome := PEMemory.list_mapM_isSome_of_forall expressions
    (fun expression => PEMemory.ParsedExpr.toTimedPEHazardEvents? expression control)
    (fun expression member => PEMemory.ParsedExpr.toTimedPEHazardEvents?_isSome_of_valid
      expression control ((List.all_eq_true.mp valid) expression member))
  unfold parsedPEHazardEventsForPE?
  change (do
    let perExpression ← expressions.mapM fun expression =>
      PEMemory.ParsedExpr.toTimedPEHazardEvents? expression control
    pure perExpression.flatten).isSome = true
  cases mapped : expressions.mapM
      (fun expression => PEMemory.ParsedExpr.toTimedPEHazardEvents? expression control) with
  | none => simp [mapped] at eventsSome
  | some perExpression => simp [mapped]

theorem parsedPEHazardEventsForAllPEs_isSome_of_valid
    (state : State) (expressions : List ParsedExpr)
    (valid : expressions.all fun expression =>
      (expression.sources ++ expression.destinations).all
        PEMemory.ParsedOperand.directMemoryAddressModeValid = true) :
    ((List.finRange 4096).mapM fun pe =>
      parsedPEHazardEventsForPE? state expressions pe).isSome = true := by
  apply PEMemory.list_mapM_isSome_of_forall
  intro pe member
  exact parsedPEHazardEventsForPE?_isSome_of_valid state expressions pe valid

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

/-- Reject malformed direct PE-memory address modes as instruction failures
before hazard lowering can turn their unsupported width/bank combination into
an epistemic `.unknown`. Value-semantic gaps remain `.unknown` downstream. -/
def parsedNormalizedLinePEAddressModesValid (line : NormalizedLine) : Bool :=
  match line.toInstruction? with
  | some (.pe expressions) =>
      expressions.all fun expression =>
        (expression.sources ++ expression.destinations).all
          PEMemory.ParsedOperand.directMemoryAddressModeValid
  | _ => true

theorem parsedNormalizedLinePEHazardEvents?_isSome_of_valid
    (state : State) (line : NormalizedLine)
    (valid : parsedNormalizedLinePEAddressModesValid line = true) :
    (parsedNormalizedLinePEHazardEvents? state line).isSome = true := by
  cases line with
  | pe normalizedExpressions =>
      have parsedExpressionsValid :
          ∀ expression ∈ normalizedExpressions.map NormalizedExpr.toParsed,
            (∀ operand ∈ expression.sources,
              PEMemory.ParsedOperand.directMemoryAddressModeValid operand = true) ∧
            (∀ operand ∈ expression.destinations,
              PEMemory.ParsedOperand.directMemoryAddressModeValid operand = true) := by
        simpa [parsedNormalizedLinePEAddressModesValid, NormalizedLine.toInstruction?,
          NormalizedExpr.toParsed, List.all_eq_true] using valid
      have expressionsValid :
          (normalizedExpressions.map NormalizedExpr.toParsed).all fun expression =>
            (expression.sources ++ expression.destinations).all
              PEMemory.ParsedOperand.directMemoryAddressModeValid = true := by
        apply List.all_eq_true.mpr
        intro expression member
        apply List.all_eq_true.mpr
        intro operand operandMember
        rcases List.mem_append.mp operandMember with sourceMember | destinationMember
        · exact (parsedExpressionsValid expression member).1 operand sourceMember
        · exact (parsedExpressionsValid expression member).2 operand destinationMember
      have allPEs := parsedPEHazardEventsForAllPEs_isSome_of_valid state
        (normalizedExpressions.map NormalizedExpr.toParsed) expressionsValid
      unfold parsedNormalizedLinePEHazardEvents?
      simp only [NormalizedLine.toInstruction?]
      change ((List.finRange 4096).mapM fun pe =>
        parsedPEHazardEventsForPE? state (normalizedExpressions.map NormalizedExpr.toParsed) pe).isSome = true
      exact allPEs
  | nop count wait =>
      cases count <;> rfl
  | mv transfer => rfl
  | maskDirective width targets entry => rfl

def parsedBlockHazardViolated
    (history current : List PEMemory.TimedBlockAccess) : Bool :=
  (HazardTrace.blockHazardConstraintsBetween history current).any fun constraint =>
    constraint.distance < constraint.required

structure HazardAwareState where
  machine : State
  peHistory : PEId → List PEMemory.TimedPEAccess
  blockHistory : List PEMemory.TimedBlockAccess
  /-- PE line held at its issue boundary while its MV wait tag is incomplete. -/
  stalledPEIssue : Option NormalizedLine

def HazardAwareState.initial (state : State) : HazardAwareState :=
  ⟨state, fun _ => [], [], none⟩

def normalizedLineWaitTag? : NormalizedLine → Option (Fin 256)
  | .nop _ wait => wait
  | .pe expressions =>
      expressions.findSome? fun expression => parsedExprWaitTag? expression.toParsed
  | .mv _ | .maskDirective .. => none

noncomputable def executeHazardAwareNormalizedLineCore (line : NormalizedLine)
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
      if !parsedNormalizedLinePEAddressModesValid line then return .failure
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
          return .ok ⟨next, nextPEHistory, nextBlockHistory, state.stalledPEIssue⟩

/-- Deterministic program-runner profile: when a PE line waits, schedule the
tagged completion immediately if its MV has already been issued. -/
noncomputable def executeHazardAwareNormalizedLine (line : NormalizedLine)
    (state : HazardAwareState) : ProofsLean.StepResult HazardAwareState := Id.run do
  if state.stalledPEIssue.isSome then return .failure
  let state ← match normalizedLineWaitTag? line with
    | none => pure state
    | some tag =>
        match completePendingMvTagAll state.machine tag with
        | none => return .unknown
        | some machine => pure { state with machine }
  return executeHazardAwareNormalizedLineCore line state

theorem executeHazardAwareNormalizedLine_rejects_issue_while_stalled
    (line blocked : NormalizedLine) (state : HazardAwareState)
    (stalled : state.stalledPEIssue = some blocked) :
    executeHazardAwareNormalizedLine line state = .failure := by
  simp [executeHazardAwareNormalizedLine, stalled]

/-- A mask directive updates only the machine mask-control field in the
hazard-aware state; PE/block histories and the stalled-issue marker are
preserved, and the underlying instruction clock is unchanged. -/
theorem executeHazardAwareNormalizedLineCore_maskDirective
    (state : HazardAwareState) (widthWords : Nat)
    (targets : ParsedMaskTargets) (entry : Fin 256) :
    executeHazardAwareNormalizedLineCore
      (.maskDirective widthWords targets entry) state =
      .ok { state with machine :=
        { state.machine with maskDirective := ⟨widthWords, targets, entry⟩ } } := by
  simp [executeHazardAwareNormalizedLineCore, executeNormalizedLine]

theorem executeHazardAwareNormalizedLine_maskDirective
    (state : HazardAwareState) (widthWords : Nat)
    (targets : ParsedMaskTargets) (entry : Fin 256)
    (notStalled : state.stalledPEIssue = none) :
    executeHazardAwareNormalizedLine
      (.maskDirective widthWords targets entry) state =
      .ok { state with machine :=
        { state.machine with maskDirective := ⟨widthWords, targets, entry⟩ } } := by
  simp [executeHazardAwareNormalizedLine, normalizedLineWaitTag?, notStalled,
    executeHazardAwareNormalizedLineCore_maskDirective]

inductive ScheduledEvent where
  | issue (line : NormalizedLine)
  | completeMv (tag : Fin 256)
  | completeMvIssue (pendingIndex : Nat)

/-- One explicitly scheduled transition. `completeMv` events may complete any
issued tag independently, so traces can represent out-of-order MV completion. -/
noncomputable def executeScheduledEvent (event : ScheduledEvent)
    (state : HazardAwareState) : ProofsLean.StepResult HazardAwareState :=
  match event with
  | .issue line => if state.stalledPEIssue.isSome then .failure else
      match line.toInstruction? with
      | none => executeHazardAwareNormalizedLineCore line state
      | some instruction =>
          if !checkParsedTopLine instruction.toParsed then
            .failure
          else
            match normalizedLineWaitTag? line with
            | some tag =>
                if state.machine.mvCompletedTags tag then
                  executeHazardAwareNormalizedLineCore line state
                else .ok { state with stalledPEIssue := some line }
            | none => executeHazardAwareNormalizedLineCore line state
  | .completeMv tag =>
      match completePendingMvTag state.machine tag with
      | none => .unknown
      | some machine =>
          let withCompletion := { state with machine }
          match state.stalledPEIssue with
          | none => .ok withCompletion
          | some line =>
              if normalizedLineWaitTag? line == some tag && machine.mvCompletedTags tag then
                match executeHazardAwareNormalizedLineCore line withCompletion with
                | .failure => .failure
                | .unknown => .unknown
                | .ok next => .ok { next with stalledPEIssue := none }
              else .ok withCompletion
  | .completeMvIssue pendingIndex =>
      match completePendingMvAtIndex state.machine pendingIndex with
      | none => .unknown
      | some (completed, machine) =>
          let withCompletion := { state with machine }
          match state.stalledPEIssue with
          | none => .ok withCompletion
          | some line =>
              if normalizedLineWaitTag? line == completed.tag &&
                  (match completed.tag with
                  | none => false
                  | some tag => machine.mvCompletedTags tag) then
                match executeHazardAwareNormalizedLineCore line withCompletion with
                | .failure => .failure
                | .unknown => .unknown
                | .ok next => .ok { next with stalledPEIssue := none }
              else .ok withCompletion

theorem executeScheduledEvent_wait_enters_stall
    (state : HazardAwareState) (line : NormalizedLine) (instruction : InstructionLine)
    (tag : Fin 256)
    (notAlreadyStalled : state.stalledPEIssue = none)
    (instructionLine : line.toInstruction? = some instruction)
    (legal : checkParsedTopLine instruction.toParsed = true)
    (waitTag : normalizedLineWaitTag? line = some tag)
    (incomplete : state.machine.mvCompletedTags tag = false) :
    executeScheduledEvent (.issue line) state =
      .ok { state with stalledPEIssue := some line } := by
  simp [executeScheduledEvent, notAlreadyStalled, instructionLine, legal,
    waitTag, incomplete]

theorem executeScheduledEvent_rejects_issue_while_pe_waits
    (state : HazardAwareState) (blocked line : NormalizedLine)
    (stalled : state.stalledPEIssue = some blocked) :
    executeScheduledEvent (.issue line) state = .failure := by
  simp [executeScheduledEvent, stalled]

theorem executeScheduledEvent_unrelated_completion_preserves_stalled_pe_line
    (state : HazardAwareState) (line : NormalizedLine) (tag : Fin 256) (next : State)
    (stalled : state.stalledPEIssue = some line)
    (unrelated : (normalizedLineWaitTag? line == some tag) = false)
    (completed : completePendingMvTag state.machine tag = some next) :
    executeScheduledEvent (.completeMv tag) state =
      .ok { state with machine := next } := by
  simp [executeScheduledEvent, completed, stalled, unrelated]

theorem executeScheduledEvent_incomplete_tag_completion_preserves_stall
    (state : HazardAwareState) (line : NormalizedLine) (tag : Fin 256)
    (next : State) (stalled : state.stalledPEIssue = some line)
    (waitTag : normalizedLineWaitTag? line = some tag)
    (completed : completePendingMvTag state.machine tag = some next)
    (stillIncomplete : next.mvCompletedTags tag = false) :
    executeScheduledEvent (.completeMv tag) state =
      .ok { state with machine := next } := by
  simp [executeScheduledEvent, completed, stalled, waitTag, stillIncomplete]

theorem executeScheduledEvent_completion_releases_stalled_pe_line
    (state : HazardAwareState) (line : NormalizedLine) (tag : Fin 256)
    (next : State) (resumedState : HazardAwareState)
    (stalled : state.stalledPEIssue = some line)
    (waitTag : normalizedLineWaitTag? line = some tag)
    (completed : completePendingMvTag state.machine tag = some next)
    (tagFinished : next.mvCompletedTags tag = true)
    (resumed : executeHazardAwareNormalizedLineCore line
      { state with machine := next, stalledPEIssue := some line } =
      .ok resumedState) :
    executeScheduledEvent (.completeMv tag) state =
      .ok { resumedState with stalledPEIssue := none } := by
  have tagEq : (normalizedLineWaitTag? line == some tag) = true := by
    simp [waitTag]
  have stateStall : state.stalledPEIssue = some line := stalled
  rw [executeScheduledEvent, completed, stateStall]
  simp only [tagEq, tagFinished, Bool.and_true, ↓reduceIte]
  rw [resumed]

noncomputable def executeScheduledEvents
    : List ScheduledEvent → HazardAwareState → ProofsLean.StepResult HazardAwareState
  | [], state => .ok state
  | event :: rest, state =>
      match executeScheduledEvent event state with
      | .failure => .failure
      | .unknown => .unknown
      | .ok next => executeScheduledEvents rest next

/-- Execute a chosen PE/MV issue and completion schedule without draining
remaining MV work at the end. The returned hazard-aware state retains pending
operations, allowing the caller to extend the trace. -/
noncomputable def executeScheduledProgram (events : List ScheduledEvent)
    (state : State) : ProofsLean.StepResult HazardAwareState :=
  executeScheduledEvents events (HazardAwareState.initial state)

theorem executeScheduledProgram_wait_enters_stall
    (machine : State) (line : NormalizedLine) (instruction : InstructionLine)
    (tag : Fin 256)
    (instructionLine : line.toInstruction? = some instruction)
    (legal : checkParsedTopLine instruction.toParsed = true)
    (waitTag : normalizedLineWaitTag? line = some tag)
    (incomplete : machine.mvCompletedTags tag = false) :
    executeScheduledProgram [.issue line] machine =
      .ok { HazardAwareState.initial machine with stalledPEIssue := some line } := by
  unfold executeScheduledProgram
  simp only [executeScheduledEvents]
  rw [executeScheduledEvent_wait_enters_stall
    (HazardAwareState.initial machine) line instruction tag rfl
    instructionLine legal waitTag incomplete]

theorem executeScheduledProgram_wait_releases_on_completion
    (machine next : State) (line : NormalizedLine) (instruction : InstructionLine)
    (tag : Fin 256) (resumedState : HazardAwareState)
    (instructionLine : line.toInstruction? = some instruction)
    (legal : checkParsedTopLine instruction.toParsed = true)
    (waitTag : normalizedLineWaitTag? line = some tag)
    (incomplete : machine.mvCompletedTags tag = false)
    (completed : completePendingMvTag machine tag = some next)
    (tagFinished : next.mvCompletedTags tag = true)
    (resumed : executeHazardAwareNormalizedLineCore line
      { (HazardAwareState.initial machine) with
        machine := next, stalledPEIssue := some line } = .ok resumedState) :
    executeScheduledProgram [.issue line, .completeMv tag] machine =
      .ok { resumedState with stalledPEIssue := none } := by
  unfold executeScheduledProgram
  simp only [executeScheduledEvents]
  rw [executeScheduledEvent_wait_enters_stall
    (HazardAwareState.initial machine) line instruction tag rfl
    instructionLine legal waitTag incomplete]
  dsimp only
  rw [executeScheduledEvent_completion_releases_stalled_pe_line
    { (HazardAwareState.initial machine) with stalledPEIssue := some line }
    line tag next resumedState rfl waitTag completed tagFinished resumed]

def scheduledIssueLines : List ScheduledEvent → List NormalizedLine
  | [] => []
  | .issue line :: rest => line :: scheduledIssueLines rest
  | .completeMv _ :: rest | .completeMvIssue _ :: rest => scheduledIssueLines rest

/-- Run a completion schedule only when its issue events exactly preserve the
source program's instruction order. Completion events may be interleaved. -/
noncomputable def executeScheduledProgramForLines (lines : List NormalizedLine)
    (events : List ScheduledEvent) (state : State) :
    ProofsLean.StepResult HazardAwareState :=
  if scheduledIssueLines events == lines then executeScheduledProgram events state
  else .failure

/-- Execute a normalized source program in order. The runner carries recent
PE-memory accesses as validation history, rejects PE hazards before applying
the line, and retains the transactional behavior of each datapath step. -/
noncomputable def executeNormalizedProgramAuxFuel
    : Nat → List NormalizedLine → HazardAwareState →
      ProofsLean.StepResult HazardAwareState
  | 0, [], currentState => .ok currentState
  | 0, _ :: _, _ => .unknown
  | _ + 1, [], currentState => .ok currentState
  | fuel + 1, line :: rest, currentState =>
      match executeHazardAwareNormalizedLine line currentState with
      | .failure => .failure
      | .unknown => .unknown
      | .ok next => executeNormalizedProgramAuxFuel fuel rest next

noncomputable def executeNormalizedProgramAux
    (remaining : List NormalizedLine) (currentState : HazardAwareState) :
    ProofsLean.StepResult HazardAwareState :=
  executeNormalizedProgramAuxFuel remaining.length remaining currentState

noncomputable def executeNormalizedProgram (lines : List NormalizedLine)
    (state : State) : ProofsLean.StepResult State :=
  match executeNormalizedProgramAux lines (HazardAwareState.initial state) with
  | .failure => .failure
  | .unknown => .unknown
  | .ok final => .ok (completeAllPendingMvs final.machine)

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
    (accepted : checkParsedTopLine (.nop (count + 1) wait) = true)
    (waitNone : wait = none) :
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
    rw [waitNone] at acceptedInstruction
    simp [executeNormalizedLine, NormalizedLine.toInstruction?,
      executeIntegerProducerInstructionLine, acceptedInstruction, waitNone]

/-- A positive no-wait nop advances the machine clock by its issue cost,
emits no PE or block hazard events, and ages existing histories against the
new clock. The stalled marker is preserved. -/
theorem executeHazardAwareNormalizedLineCore_positive_nop
    (state : HazardAwareState) (count : Nat) :
    executeHazardAwareNormalizedLineCore (.nop (count + 1) none) state =
      .ok { state with
        machine := { state.machine with
          hazardClock := state.machine.hazardClock + (count + 1) }
        peHistory := fun pe => (state.peHistory pe).filter fun event =>
          event.startWord + 4 ≥ state.machine.hazardClock + (count + 1)
        blockHistory := state.blockHistory.filter fun event =>
          event.startWord + 4 ≥ state.machine.hazardClock + (count + 1) } := by
  have accepted : checkParsedTopLine (.nop (count + 1) none) = true := by
    simp [checkParsedTopLine, ParsedLine.nopIssueLegalB]
  have acceptedInstruction : checkParsedTopLine (InstructionLine.toParsed
      (.nop ⟨count + 1, by omega⟩ none)) = true := by
    simpa [InstructionLine.toParsed] using accepted
  have executed :=
    (executeNormalizedLine_positive_nop_matches_footprint state.machine count none
      accepted rfl).2
  have peEvents : parsedNormalizedLinePEHazardEvents? state.machine
      (.nop (count + 1) none) = some (List.replicate 4096 []) := rfl
  have blockEvents : HazardTrace.parsedLineBlockHazardEvents
      (NormalizedLine.toParsed (.nop (count + 1) none))
        state.machine.hazardClock = [] := rfl
  have noPEHazard : ∀ pe, parsedPEHazardViolated
      (state.peHistory pe) ([] : List PEMemory.TimedPEAccess) = false := by
    intro pe
    simp [parsedPEHazardViolated, PEMemory.peHazardConstraintsBetween]
  have noBlockHazard : parsedBlockHazardViolated state.blockHistory [] = false := by
    simp [parsedBlockHazardViolated, HazardTrace.blockHazardConstraintsBetween]
  simp [-List.reduceReplicate, executeHazardAwareNormalizedLineCore,
    NormalizedLine.toInstruction?,
    parsedNormalizedLinePEAddressModesValid, peEvents, blockEvents,
    noPEHazard, noBlockHazard, executed, acceptedInstruction]

theorem executeHazardAwareNormalizedLine_positive_nop
    (state : HazardAwareState) (count : Nat)
    (notStalled : state.stalledPEIssue = none) :
    executeHazardAwareNormalizedLine (.nop (count + 1) none) state =
      .ok { state with
        machine := { state.machine with
          hazardClock := state.machine.hazardClock + (count + 1) }
        peHistory := fun pe => (state.peHistory pe).filter fun event =>
          event.startWord + 4 ≥ state.machine.hazardClock + (count + 1)
        blockHistory := state.blockHistory.filter fun event =>
          event.startWord + 4 ≥ state.machine.hazardClock + (count + 1) } := by
  simp [executeHazardAwareNormalizedLine, normalizedLineWaitTag?, notStalled,
    executeHazardAwareNormalizedLineCore_positive_nop]

theorem executeHazardAwareNormalizedLineCore_completed_wait_nop
    (state : HazardAwareState) (count : Nat) (tag : Fin 256)
    (accepted : checkParsedTopLine (.nop (count + 1) (some tag)) = true)
    (completed : state.machine.mvCompletedTags tag = true) :
    executeHazardAwareNormalizedLineCore (.nop (count + 1) (some tag)) state =
      .ok { state with
        machine := { state.machine with
          hazardClock := state.machine.hazardClock + (count + 1) }
        peHistory := fun pe => (state.peHistory pe).filter fun event =>
          event.startWord + 4 ≥ state.machine.hazardClock + (count + 1)
        blockHistory := state.blockHistory.filter fun event =>
          event.startWord + 4 ≥ state.machine.hazardClock + (count + 1) } := by
  have acceptedInstruction : checkParsedTopLine (InstructionLine.toParsed
      (.nop ⟨count + 1, by omega⟩ (some tag))) = true := by
    simpa [InstructionLine.toParsed] using accepted
  have executed : executeNormalizedLine (.nop (count + 1) (some tag)) state.machine =
      .ok { state.machine with
        hazardClock := state.machine.hazardClock + (count + 1) } := by
    have executedInstruction : executeIntegerProducerInstructionLine
        (.nop ⟨count + 1, by omega⟩ (some tag)) state.machine =
          .ok { state.machine with
            hazardClock := state.machine.hazardClock + (count + 1) } := by
      simp [executeIntegerProducerInstructionLine, InstructionLine.toParsed,
        accepted, completed]
    simpa [executeNormalizedLine, NormalizedLine.toInstruction?]
      using executedInstruction
  have peEvents : parsedNormalizedLinePEHazardEvents? state.machine
      (.nop (count + 1) (some tag)) = some (List.replicate 4096 []) := rfl
  have blockEvents : HazardTrace.parsedLineBlockHazardEvents
      (NormalizedLine.toParsed (.nop (count + 1) (some tag)))
        state.machine.hazardClock = [] := rfl
  have noPEHazard : ∀ pe, parsedPEHazardViolated
      (state.peHistory pe) ([] : List PEMemory.TimedPEAccess) = false := by
    intro pe
    simp [parsedPEHazardViolated, PEMemory.peHazardConstraintsBetween]
  have noBlockHazard : parsedBlockHazardViolated state.blockHistory [] = false := by
    simp [parsedBlockHazardViolated, HazardTrace.blockHazardConstraintsBetween]
  simp [-List.reduceReplicate, executeHazardAwareNormalizedLineCore,
    NormalizedLine.toInstruction?, parsedNormalizedLinePEAddressModesValid,
    peEvents, blockEvents, noPEHazard, noBlockHazard, executed,
    acceptedInstruction]

theorem executeHazardAwareNormalizedLine_completed_wait_nop
    (state : HazardAwareState) (count : Nat) (tag : Fin 256)
    (notStalled : state.stalledPEIssue = none)
    (accepted : checkParsedTopLine (.nop (count + 1) (some tag)) = true)
    (completed : state.machine.mvCompletedTags tag = true) :
    executeHazardAwareNormalizedLine (.nop (count + 1) (some tag)) state =
      .ok { state with
        machine := { state.machine with
          hazardClock := state.machine.hazardClock + (count + 1) }
        peHistory := fun pe => (state.peHistory pe).filter fun event =>
          event.startWord + 4 ≥ state.machine.hazardClock + (count + 1)
        blockHistory := state.blockHistory.filter fun event =>
          event.startWord + 4 ≥ state.machine.hazardClock + (count + 1) } := by
  have completedAll : completePendingMvTagAll state.machine tag =
      some state.machine := by
    simp [completePendingMvTagAll, completePendingMvTagFuel, completed]
  simp [executeHazardAwareNormalizedLine, normalizedLineWaitTag?, notStalled,
    completedAll]
  have sameState : { state with machine := state.machine, stalledPEIssue := none } = state := by
    cases state with
    | mk machine peHistory blockHistory stalled => simp_all
  rw [sameState]
  rw [executeHazardAwareNormalizedLineCore_completed_wait_nop
    state count tag accepted completed]
  simp
  exact notStalled

theorem executeHazardAwareNormalizedLine_drains_tag_then_wait_nop
    (state : HazardAwareState) (next : State) (count : Nat) (tag : Fin 256)
    (notStalled : state.stalledPEIssue = none)
    (accepted : checkParsedTopLine (.nop (count + 1) (some tag)) = true)
    (initiallyIncomplete : state.machine.mvCompletedTags tag = false)
    (drained : completePendingMvTagAll state.machine tag = some next) :
    (executeHazardAwareNormalizedLine (.nop (count + 1) (some tag)) state =
      .ok { state with
        machine := { next with hazardClock := next.hazardClock + (count + 1) }
        peHistory := fun pe => (state.peHistory pe).filter fun event =>
          event.startWord + 4 ≥ next.hazardClock + (count + 1)
        blockHistory := state.blockHistory.filter fun event =>
          event.startWord + 4 ≥ next.hazardClock + (count + 1) }) ∧
      pendingMvContainsTag tag next.pendingMv = false ∧
      next.pendingMv.filter (fun operation => operation.tag != some tag) =
        state.machine.pendingMv.filter (fun operation => operation.tag != some tag) := by
  constructor
  ·
      have tagCompleted := completePendingMvTagAll_success_completes_tag
        state.machine next tag drained
      have core := executeHazardAwareNormalizedLineCore_completed_wait_nop
        { state with machine := next } count tag accepted tagCompleted
      simp [executeHazardAwareNormalizedLine, normalizedLineWaitTag?, notStalled,
        drained]
      have sameDrained : { state with machine := next, stalledPEIssue := none } =
          { state with machine := next } := by
        cases state with
        | mk machine peHistory blockHistory stalled => simp_all
      rw [sameDrained, core]
      simp
      exact notStalled
  · constructor
    · exact completePendingMvTagAll_success_clears_tag_queue
        state.machine next tag initiallyIncomplete drained
    · exact completePendingMvTagAll_success_preserves_other_pending
        state.machine next tag initiallyIncomplete drained

theorem executeScheduledProgram_wait_nop_releases_after_completion
    (machine next : State) (count : Nat) (tag : Fin 256)
    (accepted : checkParsedTopLine (.nop (count + 1) (some tag)) = true)
    (incomplete : machine.mvCompletedTags tag = false)
    (completed : completePendingMvTag machine tag = some next)
    (tagFinished : next.mvCompletedTags tag = true) :
    executeScheduledProgram
      [.issue (.nop (count + 1) (some tag)), .completeMv tag] machine =
      .ok { (HazardAwareState.initial next) with machine :=
        { next with hazardClock := next.hazardClock + (count + 1) } } := by
  let line : NormalizedLine := .nop (count + 1) (some tag)
  let instruction : InstructionLine := .nop ⟨count + 1, by omega⟩ (some tag)
  let stalledState : HazardAwareState := { (HazardAwareState.initial machine) with
    machine := next, stalledPEIssue := some line }
  have instructionLine : line.toInstruction? = some instruction := rfl
  have legal : checkParsedTopLine instruction.toParsed = true := by
    simpa [instruction, InstructionLine.toParsed] using accepted
  have waitTag : normalizedLineWaitTag? line = some tag := rfl
  have resumed : executeHazardAwareNormalizedLineCore line stalledState =
      .ok { stalledState with machine :=
        { next with hazardClock := next.hazardClock + (count + 1) } } := by
    have core := executeHazardAwareNormalizedLineCore_completed_wait_nop
      stalledState count tag accepted tagFinished
    simpa [line, stalledState, HazardAwareState.initial] using core
  have schedule := executeScheduledProgram_wait_releases_on_completion
    machine next line instruction tag
    { stalledState with machine :=
        { next with hazardClock := next.hazardClock + (count + 1) } }
    instructionLine legal waitTag incomplete completed tagFinished resumed
  simpa [line, stalledState, HazardAwareState.initial] using schedule

theorem executeScheduledProgram_wait_nop_releases_after_two_completions
    (machine first next : State) (count : Nat) (tag : Fin 256)
    (accepted : checkParsedTopLine (.nop (count + 1) (some tag)) = true)
    (initiallyIncomplete : machine.mvCompletedTags tag = false)
    (firstCompletion : completePendingMvTag machine tag = some first)
    (stillIncomplete : first.mvCompletedTags tag = false)
    (finalCompletion : completePendingMvTag first tag = some next)
    (tagFinished : next.mvCompletedTags tag = true) :
    executeScheduledProgram
      [.issue (.nop (count + 1) (some tag)), .completeMv tag, .completeMv tag]
      machine =
      .ok { (HazardAwareState.initial next) with machine :=
        { next with hazardClock := next.hazardClock + (count + 1) } } := by
  let line : NormalizedLine := .nop (count + 1) (some tag)
  let instruction : InstructionLine := .nop ⟨count + 1, by omega⟩ (some tag)
  let stalledState := { (HazardAwareState.initial machine) with
    stalledPEIssue := some line }
  let intermediate := { stalledState with machine := first }
  let resumedBase := { intermediate with machine := next }
  let resumedState := { resumedBase with
    machine := { next with hazardClock := next.hazardClock + (count + 1) } }
  have instructionLine : line.toInstruction? = some instruction := rfl
  have legal : checkParsedTopLine instruction.toParsed = true := by
    simpa [instruction, InstructionLine.toParsed] using accepted
  have waitTag : normalizedLineWaitTag? line = some tag := rfl
  have resumed : executeHazardAwareNormalizedLineCore line resumedBase =
      .ok resumedState := by
    have core := executeHazardAwareNormalizedLineCore_completed_wait_nop
      resumedBase count tag accepted tagFinished
    simpa [line, resumedState, resumedBase, intermediate, stalledState,
      HazardAwareState.initial] using core
  have issue := executeScheduledEvent_wait_enters_stall
    (HazardAwareState.initial machine) line instruction tag rfl
    instructionLine legal waitTag initiallyIncomplete
  have firstStep := executeScheduledEvent_incomplete_tag_completion_preserves_stall
    stalledState line tag first rfl waitTag firstCompletion stillIncomplete
  have finalStep := executeScheduledEvent_completion_releases_stalled_pe_line
    intermediate line tag next resumedState rfl waitTag finalCompletion
    tagFinished resumed
  unfold executeScheduledProgram
  simp only [executeScheduledEvents]
  rw [issue]
  simp only [executeScheduledEvents]
  rw [firstStep]
  simp only [executeScheduledEvents]
  rw [finalStep]
  simpa [resumedState, resumedBase, intermediate, stalledState,
    HazardAwareState.initial, line]

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
    (entry : Fin 256) (noPendingMv : state.pendingMv = []) :
    executeNormalizedProgram [.maskDirective widthWords targets entry] state =
      .ok { state with maskDirective := ⟨widthWords, targets, entry⟩ } := by
  have hstep : executeHazardAwareNormalizedLine
      (.maskDirective widthWords targets entry) (HazardAwareState.initial state) =
      .ok { (HazardAwareState.initial state) with
        machine := { state with maskDirective := ⟨widthWords, targets, entry⟩ } } := by
    simp [executeHazardAwareNormalizedLine, executeHazardAwareNormalizedLineCore,
      HazardAwareState.initial, executeNormalizedLine, normalizedLineWaitTag?]
  simp only [executeNormalizedProgram, executeNormalizedProgramAux,
    List.length_cons, List.length_nil, executeNormalizedProgramAuxFuel]
  rw [hstep]
  simp [completeAllPendingMvs, noPendingMv]

theorem executeParsedProgram_maskDirective_updates_state
    (state : State) (widthWords : Nat) (targets : ParsedMaskTargets)
    (entry : Fin 256) (noPendingMv : state.pendingMv = []) :
    executeParsedProgram [.maskDirective widthWords targets entry] state =
      .ok { state with maskDirective := ⟨widthWords, targets, entry⟩ } := by
  simp [executeParsedProgram, ParsedLine.normalizeForSubmission?,
    executeNormalizedProgram_maskDirective_updates_state, noPendingMv]

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
    (waitsComplete : (normalizedExpressions.map NormalizedExpr.toParsed).any
      (parsedExprWaitPending state) = false)
    (unsupported : (normalizedExpressions.map NormalizedExpr.toParsed).any
      parsedExprIsUnsupportedRustAlu = true) :
    executeIntegerProducerInstructionLine (.pe normalizedExpressions) state = .failure := by
  simp [executeIntegerProducerInstructionLine, accepted, waitsComplete, unsupported]

theorem executeIntegerProducerInstructionLine_pe_wait_pending
    (normalizedExpressions : List NormalizedExpr) (state : State)
    (accepted : checkParsedTopLine
      (InstructionLine.pe normalizedExpressions).toParsed = true)
    (pending : (normalizedExpressions.map NormalizedExpr.toParsed).any
      (parsedExprWaitPending state) = true) :
    executeIntegerProducerInstructionLine (.pe normalizedExpressions) state = .unknown := by
  simp [executeIntegerProducerInstructionLine, accepted, pending]

theorem executeIntegerProducerInstructionLine_nop
    (count : {n : Nat // 0 < n}) (wait : Option (Fin 256)) (state : State)
    (accepted : checkParsedTopLine (.nop count.val wait) = true)
    (waitNone : wait = none) :
    executeIntegerProducerInstructionLine (.nop count wait) state =
      .ok { state with hazardClock := state.hazardClock + count.val } := by
  rw [waitNone] at accepted
  simp [executeIntegerProducerInstructionLine, InstructionLine.toParsed,
    accepted, InstructionLine.cost, waitNone]

theorem executeIntegerProducerInstructionLine_wait_completed
    (count : {n : Nat // 0 < n}) (tag : Fin 256) (state : State)
    (accepted : checkParsedTopLine (.nop count.val (some tag)) = true)
    (completed : state.mvCompletedTags tag = true) :
    executeIntegerProducerInstructionLine (.nop count (some tag)) state =
      .ok { state with hazardClock := state.hazardClock + count.val } := by
  simp [executeIntegerProducerInstructionLine, InstructionLine.toParsed,
    accepted, completed]

theorem executeIntegerProducerInstructionLine_wait_pending_unknown
    (count : {n : Nat // 0 < n}) (tag : Fin 256) (state : State)
    (accepted : checkParsedTopLine (.nop count.val (some tag)) = true)
    (pending : state.mvCompletedTags tag = false) :
    executeIntegerProducerInstructionLine (.nop count (some tag)) state = .unknown := by
  simp [executeIntegerProducerInstructionLine, InstructionLine.toParsed,
    accepted, pending]

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
      .ok { next with
        hazardClock := next.hazardClock + 1 } := by
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
    (nextSharedBlocks : State)
    (sharedBlockWrites : executeParsedSharedBlockProducers state next
      (normalizedExpressions.map NormalizedExpr.toParsed)
      (!(normalizedExpressions.any
        (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed))) = .ok nextSharedBlocks)
    (nextBroadcast : State)
    (l1ToPE : executeParsedL1ToPEProducers state nextSharedBlocks
      (normalizedExpressions.map NormalizedExpr.toParsed)
      (normalizedExpressions.any (parsedExprIsNoForwardProducer ∘ NormalizedExpr.toParsed))
      (normalizedExpressions.any (parsedExprHasSingleLineWriteMask ∘ NormalizedExpr.toParsed))
      (parsedL1ToPEPrecedesOMRWriter (normalizedExpressions.map NormalizedExpr.toParsed)) =
        .ok nextBroadcast)
    (waitsComplete : (normalizedExpressions.map NormalizedExpr.toParsed).any
      (parsedExprWaitPending state) = false)
    :
    executeIntegerProducerInstructionLine (.pe normalizedExpressions) state =
      .ok { nextBroadcast with
        hazardClock := nextBroadcast.hazardClock + InstructionLine.cost (.pe normalizedExpressions)
        l1bmTurnaroundValid :=
          if ∃ expression ∈ normalizedExpressions,
            parsedExprIsNoForwardProducer expression.toParsed = true
          then nextBroadcast.l1bmTurnaroundValid
          else normalizedExpressions.any (fun expression =>
            parsedExprMayWriteL1BMTurnaround expression.toParsed) } := by
  simp [executeIntegerProducerInstructionLine, accepted, waitsComplete, supported, noUnsupportedRustAlu,
    executed, mslMsrWrites,
    reluWrites, blockFloatWrites,
    matrixWrites, sharedBlockWrites, l1ToPE, List.any_map]
  set_option maxRecDepth 8192 in rfl

end ProofsLean.MNCore
