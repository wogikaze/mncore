import ProofsLean.MachineState
import ProofsLean.PEMachine
import ProofsLean.FloatPEMemory

/-! A whole-state transition for connected PE integer ALU, single-precision
vector `fvadd`/`fvmul`/`fvfma`, half-precision `hvadd`/`hvmul`/`hvfma`,
double-precision `dvadd`/`dvmul`/`dvfma`,
floating ALU `relu`/`relu0`/`relu1`/`relu2`/`relu3`,
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

def parsedExprIsSupportedPELineProducer (expression : ParsedExpr) : Bool :=
  match expression.op with
  | .alu .. | .zero | .immediate .. | .matrixRead .. | .wait .. | .noforward => true
  | .mau .f false .add none false | .mau .f false .mul none false
  | .mau .f false .fma none false | .mau .f false .passa _ false => true
  | .mau .f false _ _ true => true
  | .mau .d false .passa _ _ | .mau .h false .passa _ _
  | .mau .h false .mul _ _ | .mau .h false .add _ _
  | .mau .h false .fma _ _ => true
  | .mau .d false .add _ _ | .mau .d false .mul _ _
  | .mau .d false .fma _ _ => true
  | .mau .g false _ _ _ | .mau .l false _ _ _ | .mau .i false _ _ _
  | .mau .s false _ _ _ => true
  | .matrixWrite .d | .matrixWrite .f | .matrixWrite .g | .matrixWrite .h => true
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
  | .mau .f false .add none false | .mau .f false .mul none false
  | .mau .f false .fma none false | .mau .f false .passa _ false => true
  | .mau .f false _ _ true => true
  | .mau .d false .passa _ _ | .mau .h false .passa _ _
  | .mau .h false .mul _ _ | .mau .h false .add _ _
  | .mau .h false .fma _ _ => true
  | .mau .d false .add _ _ | .mau .d false .mul _ _
  | .mau .d false .fma _ _ => true
  | .mau .g false _ _ _ | .mau .l false _ _ _ | .mau .i false _ _ _
  | .mau .s false _ _ _ => true
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

def lowerParsedPassa? (precision : ParsedPrecision) (expression : ParsedExpr)
    (context : ParsedIntegerContext) :
    Option (ParsedIntegerInput × Bool × Bool × Bool × Fin (Bank.capacity .lm1)) := do
  match expression.op with
  | .mau opPrecision false .passa _ _ => guard (opPrecision == precision)
  | _ => none
  match expression.sources, expression.destinations with
  | [source], [.mem access false false false none] =>
      let (source, negate, extend, round) ← parsedFloatMAUSourceAttrs? source context
      let destinationAccess ← ParsedOperand.toDirectMemoryAccess?
        (.mem access false false false none) context.pe context.cycle
        context.bar0 context.bar1 context.tWord
      let destination ← FloatPEMemory.lm1LongAddress? destinationAccess
      some (source, negate, extend, round, destination)
  | _, _ => none

def lowerParsedHalfPassa? (expression : ParsedExpr) (context : ParsedIntegerContext) :
    Option (ParsedIntegerInput × Bool × Bool × Bool × PEMemory.Width ×
      Fin (Bank.capacity .lm1)) := do
  match expression.op with
  | .mau .h false .passa _ _ => pure ()
  | _ => none
  match expression.sources, expression.destinations with
  | [source], [.mem access false false false none] =>
      let (source, negate, extend, round) ← parsedFloatMAUSourceAttrs? source context
      let destination ← ParsedOperand.toDirectMemoryAccess?
        (.mem access false false false none) context.pe context.cycle
        context.bar0 context.bar1 context.tWord
      match destination with
      | ⟨.lm1, .long, address⟩ => some (source, negate, extend, round, .long, address)
      | ⟨.lm1, .double, address⟩ => some (source, negate, extend, round, .double, address)
      | _ => none
  | _, _ => none

def lowerParsedHalfMultiply? (expression : ParsedExpr) (context : ParsedIntegerContext) :
    Option (ParsedIntegerInput × Bool × Bool × Bool × ParsedIntegerInput × Bool × Bool × Bool ×
      PEMemory.Width × Fin (Bank.capacity .lm1)) := do
  match expression.op with
  | .mau .h false .mul _ _ => pure ()
  | _ => none
  match expression.sources, expression.destinations with
  | [sourceA, sourceB], [.mem access false false false none] =>
      let (sourceA, negateA, extendA, roundA) ← parsedFloatMAUSourceAttrs? sourceA context
      let (sourceB, negateB, extendB, roundB) ← parsedFloatMAUSourceAttrs? sourceB context
      let destination ← ParsedOperand.toDirectMemoryAccess?
        (.mem access false false false none) context.pe context.cycle
        context.bar0 context.bar1 context.tWord
      match destination with
      | ⟨.lm1, .long, address⟩ =>
          some (sourceA, negateA, extendA, roundA, sourceB, negateB, extendB, roundB,
            .long, address)
      | ⟨.lm1, .double, address⟩ =>
          some (sourceA, negateA, extendA, roundA, sourceB, negateB, extendB, roundB,
            .double, address)
      | _ => none
  | _, _ => none

def lowerParsedHalfAdd? (expression : ParsedExpr) (context : ParsedIntegerContext) :
    Option (ParsedIntegerInput × Bool × Bool × Bool × ParsedIntegerInput × Bool × Bool × Bool ×
      PEMemory.Width × Fin (Bank.capacity .lm1)) := do
  match expression.op with
  | .mau .h false .add _ _ => pure ()
  | _ => none
  match expression.sources, expression.destinations with
  | [sourceA, sourceC], [.mem access false false false none] =>
      let (sourceA, negateA, extendA, roundA) ← parsedFloatMAUSourceAttrs? sourceA context
      let (sourceC, negateC, extendC, roundC) ← parsedFloatMAUSourceAttrs? sourceC context
      let destination ← ParsedOperand.toDirectMemoryAccess?
        (.mem access false false false none) context.pe context.cycle
        context.bar0 context.bar1 context.tWord
      match destination with
      | ⟨.lm1, .long, address⟩ =>
          some (sourceA, negateA, extendA, roundA, sourceC, negateC, extendC, roundC,
            .long, address)
      | ⟨.lm1, .double, address⟩ =>
          some (sourceA, negateA, extendA, roundA, sourceC, negateC, extendC, roundC,
            .double, address)
      | _ => none
  | _, _ => none

def lowerParsedHalfFma? (expression : ParsedExpr) (context : ParsedIntegerContext) :
    Option (ParsedIntegerInput × Bool × Bool × Bool × ParsedIntegerInput × Bool × Bool × Bool ×
      ParsedIntegerInput × Bool × Bool × Bool × PEMemory.Width × Fin (Bank.capacity .lm1)) := do
  match expression.op with
  | .mau .h false .fma _ _ => pure ()
  | _ => none
  match expression.sources, expression.destinations with
  | [sourceA, sourceB, sourceC], [.mem access false false false none] =>
      let (sourceA, negateA, extendA, roundA) ← parsedFloatMAUSourceAttrs? sourceA context
      let (sourceB, negateB, extendB, roundB) ← parsedFloatMAUSourceAttrs? sourceB context
      let (sourceC, negateC, extendC, roundC) ← parsedFloatMAUSourceAttrs? sourceC context
      let destination ← ParsedOperand.toDirectMemoryAccess?
        (.mem access false false false none) context.pe context.cycle
        context.bar0 context.bar1 context.tWord
      match destination with
      | ⟨.lm1, .long, address⟩ =>
          some (sourceA, negateA, extendA, roundA, sourceB, negateB, extendB, roundB,
            sourceC, negateC, extendC, roundC, .long, address)
      | ⟨.lm1, .double, address⟩ =>
          some (sourceA, negateA, extendA, roundA, sourceB, negateB, extendB, roundB,
            sourceC, negateC, extendC, roundC, .double, address)
      | _ => none
  | _, _ => none

def lowerParsedDoubleArithmetic? (expression : ParsedExpr) (context : ParsedIntegerContext) :
    Option (CalcKind × Bool × List (ParsedIntegerInput × Bool × Bool × Bool) ×
      PEMemory.Width × Fin (Bank.capacity .lm1)) := do
  let (kind, round) ← match expression.op with
    | .mau .d false kind _ round => do
        guard (kind == .add || kind == .mul || kind == .fma)
        some (kind, round)
    | _ => none
  let expected := match kind with | .fma => 3 | _ => 2
  guard (expression.sources.length == expected)
  let sources ← expression.sources.mapM fun source => parsedFloatMAUSourceAttrs? source context
  match expression.destinations with
  | [.mem access false false false none] =>
      let destination ← ParsedOperand.toDirectMemoryAccess?
        (.mem access false false false none) context.pe context.cycle
        context.bar0 context.bar1 context.tWord
      match destination with
      | ⟨.lm1, .long, address⟩ => some (kind, round, sources, .long, address)
      | ⟨.lm1, .double, address⟩ => some (kind, round, sources, .double, address)
      | _ => none
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
        [0, 1].flatMap fun word =>
          let bits := if word == 0 then (bus.high.extractLsb' 32 32).toNat
            else (bus.high.extractLsb' 0 32).toNat
          [RRN.extendFloatBits .double .single bits] ++ (if word == 1 then [0, 0] else [])
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

def parsedMauHalfSelectsPE (half : Option Char) (pe : Fin 4) : Bool :=
  match half with
  | none => true
  | some 'u' => pe.val < 2
  | some 'd' => pe.val ≥ 2
  | some _ => false

theorem parsedMauHalfSelectsPE_upper_lanes :
    parsedMauHalfSelectsPE (some 'u') 1 = true ∧
      parsedMauHalfSelectsPE (some 'u') 2 = false := by
  decide

theorem parsedMauHalfSelectsPE_lower_lanes :
    parsedMauHalfSelectsPE (some 'd') 1 = false ∧
      parsedMauHalfSelectsPE (some 'd') 2 = true := by
  decide

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
  | .mau .f false .passa half false =>
    let cycleContext := { context with cycle := cycle }
    match lowerParsedPassa? .f expression cycleContext with
    | none => .unknown
    | some (source, negate, extend, round, destination) =>
      match ParsedIntegerInput.readWithForwarding readFiles oldSlots cycle source with
      | .failure => .failure
      | .unknown => .unknown
      | .ok sourceBus =>
        let prepared := prepareSingleMAUSource sourceBus negate extend round
        let output := if parsedMauHalfSelectsPE half cycleContext.pe then
            singlePassaBus prepared else singlePassaBus 0
        let nextLM1 := FloatPEMemory.writePair currentFiles.lm1 destination output
        .ok ({ currentFiles with lm1 := nextLM1 }, ⟨output, 0⟩)
  | .mau .d false .passa half round =>
    let cycleContext := { context with cycle := cycle }
    match lowerParsedPassa? .d expression cycleContext with
    | none => .unknown
    | some (source, negate, extend, sourceRound, destination) =>
      if sourceRound && !extend then .failure else
      match ParsedIntegerInput.readWithForwarding readFiles oldSlots cycle source with
      | .failure => .failure
      | .unknown => .unknown
      | .ok sourceBus =>
        let output := if parsedMauHalfSelectsPE half cycleContext.pe then
            prepareDoubleMAUSource sourceBus negate extend round else 0
        let nextLM1 := FloatPEMemory.writePair currentFiles.lm1 destination output
        .ok ({ currentFiles with lm1 := nextLM1 }, ⟨output, 0⟩)
  | .mau .d false kind half roundOutput =>
    let cycleContext := { context with cycle := cycle }
    match lowerParsedDoubleArithmetic? expression cycleContext with
    | none => .unknown
    | some (kind, roundOutput, sources, destinationWidth, destinationAddress) =>
      if sources.any (fun source => source.2.2.2) then .failure else
      match readMAUSourceBuses readFiles oldSlots cycle (sources.map fun source => source.1) with
      | .failure => .failure
      | .unknown => .unknown
      | .ok sourceBuses =>
        let prepared := (List.zip sources sourceBuses).map fun (source, bus) =>
          prepareDoubleMAUSource bus source.2.1 source.2.2.1 false
        let calculated := doubleMAUVectorBus kind roundOutput prepared
        let output := if parsedMauHalfSelectsPE half cycleContext.pe then calculated
          else (⟨0, 0⟩ : IntegerALU.Bus)
        let nextLM1 := PEMemory.writeWords .lm1 destinationWidth currentFiles.lm1
          destinationAddress (unpackALUBus output)
        .ok ({ currentFiles with lm1 := nextLM1 }, output)
  | .mau .h false .mul half round =>
    let cycleContext := { context with cycle := cycle }
    match lowerParsedHalfMultiply? expression cycleContext with
    | none => .unknown
    | some (sourceA, negateA, extendA, roundA, sourceB, negateB, extendB, roundB,
        destinationWidth, destinationAddress) =>
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
          let nextLM1 := PEMemory.writeWords .lm1 destinationWidth currentFiles.lm1
            destinationAddress (unpackALUBus output)
          .ok ({ currentFiles with lm1 := nextLM1 }, output)
  | .mau .h false .add half round =>
    let cycleContext := { context with cycle := cycle }
    match lowerParsedHalfAdd? expression cycleContext with
    | none => .unknown
    | some (sourceA, negateA, extendA, roundA, sourceC, negateC, extendC, roundC,
        destinationWidth, destinationAddress) =>
      if extendA then .failure else if roundC then .unknown else
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
          let output := if parsedMauHalfSelectsPE half cycleContext.pe then calculated
            else (⟨0, 0⟩ : IntegerALU.Bus)
          let nextLM1 := PEMemory.writeWords .lm1 destinationWidth currentFiles.lm1
            destinationAddress (unpackALUBus output)
          .ok ({ currentFiles with lm1 := nextLM1 }, output)
  | .mau .h false .fma half round =>
    let cycleContext := { context with cycle := cycle }
    match lowerParsedHalfFma? expression cycleContext with
    | none => .unknown
    | some (sourceA, negateA, extendA, roundA, sourceB, negateB, extendB, roundB,
        sourceC, negateC, extendC, roundC, destinationWidth, destinationAddress) =>
      if extendA || extendB then .failure else if roundC then .unknown else
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
            let output := if parsedMauHalfSelectsPE half cycleContext.pe then calculated
              else (⟨0, 0⟩ : IntegerALU.Bus)
            let nextLM1 := PEMemory.writeWords .lm1 destinationWidth currentFiles.lm1
              destinationAddress (unpackALUBus output)
            .ok ({ currentFiles with lm1 := nextLM1 }, output)
  | .mau .h false .passa half round =>
    let cycleContext := { context with cycle := cycle }
    match lowerParsedHalfPassa? expression cycleContext with
    | none => .unknown
    | some (source, negate, extend, sourceRound, destinationWidth, destinationAddress) =>
      if extend then .failure else
      match ParsedIntegerInput.readWithForwarding readFiles oldSlots cycle source with
      | .failure => .failure
      | .unknown => .unknown
      | .ok sourceBus =>
        let output := if parsedMauHalfSelectsPE half cycleContext.pe then
            prepareHalfPassa sourceBus negate sourceRound round else (⟨0, 0⟩ : IntegerALU.Bus)
        let nextLM1 := PEMemory.writeWords .lm1 destinationWidth currentFiles.lm1
          destinationAddress (unpackALUBus output)
        .ok ({ currentFiles with lm1 := nextLM1 }, output)
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

def readRawL1MwriteBus (state : State) (source : ParsedOperand)
    (pe : PEId) (cycle : Fin 4) : ProofsLean.StepResult IntegerALU.Bus :=
  let oldContext := state.peContext pe
  let coordinates := ParsedIntegerContext.ofLinearIndex pe
  let context := { coordinates with
    cycle := cycle
    bar0 := oldContext.bar0
    bar1 := oldContext.bar1
    tWord := oldContext.tWord }
  match rawL1MwriteSource? source context with
  | none => .failure
  | some input =>
      match input with
      | .forward kind _ =>
          if !state.forwardingValid pe (ParsedIntegerInput.forwardUnit kind) cycle then
            .failure
          else ParsedIntegerInput.readWithForwarding
            (state.peRegisters pe) (state.forwarding pe) cycle input
      | _ => ParsedIntegerInput.readWithForwarding
          (state.peRegisters pe) (state.forwarding pe) cycle input

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
  destination : ParsedOperand
  deriving Repr

def lowerParsedL1ToPE? (expression : ParsedExpr) : Option ParsedL1ToPEAccess := do
  match expression.op with
  | .l1bm .pbcast | .l1bm .mbcast | .l1bm .m4bcast | .l1bm (.distrib _) => pure ()
  | _ => none
  match expression.sources, expression.destinations with
  | [.l1bm width address], [destination@(.mem _ false false false _)] =>
      if width.val != 1 && width.val != 2 && width.val != 4 then none else
      let sourceBase := address.map fun address =>
        ⟨address.val % L1Transfer.l1bmLongWords,
          Nat.mod_lt _ (by decide)⟩
      some ⟨sourceBase, width.val == 4, destination⟩
  | _, _ => none

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
      let oldContext := readState.peContext pe
      let rec writeCycles : List (Fin 4) → PEMemory.IntegerRegisterFiles →
          ProofsLean.StepResult PEMemory.IntegerRegisterFiles
        | [], files => .ok files
        | cycle :: cycles, files =>
            match ParsedOperand.toDirectMemoryAccess? access.destination
                coordinates.pe cycle oldContext.bar0 oldContext.bar1 oldContext.tWord with
            | none => .unknown
            | some destination =>
              match ParsedOperand.resolveMemoryWriteSelection? access.destination
                  destination.bank files.maskRegisters cycle currentState.maskDirective
                  hasSingleLineMask with
              | none => .unknown
              | some writeSelection =>
                match resolveFlushSelection? expression.flush files.maskRegisters cycle with
                | none => .unknown
                | some flushSelection =>
                    let bus := parsedOutputAfterFlush flushSelection
                      (l1ToPEBusAt readState expression access pe cycle)
                    let next := PEMemory.writeDirectAccessMasked files destination
                      (PEMemory.unpackALUBus bus) writeSelection
                    writeCycles cycles next
      if access.sourceBase.isNone && !readState.l1bmTurnaroundValid then .failure
      else
        match writeCycles [0, 1, 2, 3] (currentState.peRegisters pe) with
        | .failure => .failure
        | .unknown => .unknown
        | .ok files =>
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
              forwardingValid := fun other => if other = pe then valid else currentState.forwardingValid other }
            executeParsedL1ToPEAtPEs readState next expression access rest noForward hasSingleLineMask

def executeParsedL1ToPEProducer (readState currentState : State)
    (expression : ParsedExpr) (noForward hasSingleLineMask : Bool) : ProofsLean.StepResult State :=
  match lowerParsedL1ToPE? expression with
  | none => .unknown
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

def parsedFloatReluBus (precision : ParsedPrecision) (name : ParsedAluName)
    (left right : IntegerALU.Bus) : IntegerALU.Bus × BitVec 4 := Id.run do
  let width := match precision with | .d => 64 | .f => 32 | _ => 16
  let lanes := 64 / width
  let shift := parsedFloatReluShift name
  let inputA := (List.range lanes).map fun lane =>
    (left.high.extractLsb' (64 - width * (lane + 1)) width).toNat
  let inputB := (List.range lanes).map fun lane =>
    (right.high.extractLsb' (64 - width * (lane + 1)) width).toNat
  let outputs : List (Nat × Bool) := (List.range lanes).map fun lane =>
    let a := inputA[lane]!
    let b := inputB[lane]!
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
  return (⟨BitVec.ofNat 64 packed, left.low⟩, BitVec.ofNat 4 flags)

theorem parsedFloatReluBus_single_lane_sign_selection :
    parsedFloatReluBus .f .relu
      ⟨0x3f800000bf800000, 0x1122334455667788⟩
      ⟨0x4000000040400000, 0⟩ =
      (⟨0x4000000080000000, 0x1122334455667788⟩, 0xc) := by
  decide

def lowerParsedMslMsr? (expression : ParsedExpr) :
    Option (Bool × ParsedOperand) := do
  let isMsl ← match expression.op with
    | .alu .msl none _ _ => some true
    | .alu .msr none _ _ => some false
    | _ => none
  match expression.sources, expression.destinations with
  | [_], [destination@(.mem ..)] =>
      some (isMsl, destination)
  | [_], [destination@(.omr ..)] =>
      some (isMsl, destination)
  | [_], [.nowrite] =>
      some (isMsl, .nowrite)
  | [_], [destination@(.bar ..)] =>
      some (isMsl, destination)
  | _, _ => none

structure ParsedFloatReluAccesses where
  precision : ParsedPrecision
  name : ParsedAluName
  sourceA : ParsedIntegerInput
  sourceB : ParsedIntegerInput
  destination : ParsedOperand

def lowerParsedFloatRelu? (expression : ParsedExpr) (context : ParsedIntegerContext) :
    Option ParsedFloatReluAccesses := do
  let (name, precision) ← match expression.op with
    | .alu name (some precision) _ _ => do
        guard (name == .relu || name == .relu0 || name == .relu1 || name == .relu2 ||
          name == .relu3)
        guard (precision == .d || precision == .f || precision == .h)
        some (name, precision)
    | _ => none
  match expression.sources, expression.destinations with
  | [sourceA, sourceB], [destination] => do
      let sourceA ← ParsedOperand.toParsedIntegerInput? sourceA precision.laneWidth
        context.group context.l2b context.l1b context.mab context.pe context.cycle
        context.bar0 context.bar1 context.tWord
      let sourceB ← ParsedOperand.toParsedIntegerInput? sourceB precision.laneWidth
        context.group context.l2b context.l1b context.mab context.pe context.cycle
        context.bar0 context.bar1 context.tWord
      match destination with
      | .mem .. | .bar .. | .omr .. | .nowrite => some ⟨precision, name, sourceA, sourceB,
          destination⟩
      | _ => none
  | _, _ => none

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
  let some (isMsl, destination) := lowerParsedMslMsr? expression | return .unknown
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
              (readState.forwarding sourcePE) cycle source with
          | .failure => .failure
          | .unknown => .unknown
          | .ok sourceBus =>
            let shifted := mslMsrOutputBus sourceBus
            match resolveFlushSelection? expression.flush files.maskRegisters cycle with
            | none => .unknown
            | some flushSelection =>
                let output := parsedOutputAfterFlush flushSelection shifted
                let destinationContext := { context with cycle := cycle, bar0 := bar0, bar1 := bar1 }
                match writeParsedMslMsrDestination? files destination destinationContext output 0 cycle
                    currentState.maskDirective hasSingleLineMask with
                | none => .unknown
                | some write =>
                    let nextBar0 := match write.barUpdate with
                      | some (false, value) => value
                      | _ => bar0
                    let nextBar1 := match write.barUpdate with
                      | some (true, value) => value
                      | _ => bar1
                    runCycles rest write.files nextBar0 nextBar1
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
      (name == .relu || name == .relu0 || name == .relu1 || name == .relu2 ||
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
            (readState.forwarding pe) cycle accesses.sourceA with
        | .failure => .failure
        | .unknown => .unknown
        | .ok sourceA =>
          match ParsedIntegerInput.readWithForwarding (readState.peRegisters pe)
              (readState.forwarding pe) cycle accesses.sourceB with
          | .failure => .failure
          | .unknown => .unknown
          | .ok sourceB =>
            let (rawOutput, flags) := parsedFloatReluBus accesses.precision accesses.name
              sourceA sourceB
            match resolveFlushSelection? expression.flush files.maskRegisters cycle with
            | none => .unknown
            | some flushSelection =>
              let output := parsedOutputAfterFlush flushSelection rawOutput
              let destinationContext := { coordinates with cycle := cycle, bar0 := bar0, bar1 := bar1 }
              match writeParsedMslMsrDestination? files accesses.destination destinationContext
                  output flags cycle currentState.maskDirective hasSingleLineMask with
              | none => .unknown
              | some write =>
                let nextBar0 := match write.barUpdate with
                  | some (false, value) => value
                  | _ => bar0
                let nextBar1 := match write.barUpdate with
                  | some (true, value) => value
                  | _ => bar1
                runCycles rest write.files nextBar0 nextBar1
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
  let oldSlots := state.forwarding pe
  let matrixStore := state.matrixRegisters context.group context.l2b context.l1b
  let peExpressions := expressions.filter fun expression =>
    !parsedExprIsMatrixWriteProducer expression &&
      !parsedExprIsL1MwriteProducer expression &&
      !parsedExprIsL1GatherProducer expression &&
      !parsedExprIsL1ReduceProducer expression &&
      !parsedExprIsL1ToPEProducer expression &&
      !parsedExprIsSupportedFloatMAUProducer expression &&
      !parsedExprIsMslMsrProducer expression &&
      !parsedExprIsFloatReluProducer expression
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
          let peExpressions := expressions.filter (fun expression =>
            !parsedExprIsL2BMProducer expression && !parsedExprIsMslMsrProducer expression &&
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
                  match executeParsedMatrixWritesAtMABs state allMABCoordinates expressions
                    nextWithRelu with
                  | .failure => .failure
                  | .unknown => .unknown
                  | .ok next =>
                  let noForward := expressions.any parsedExprIsNoForwardProducer
                  let hasPEToL1Producer := expressions.any fun expression =>
                    parsedExprIsL1MwriteProducer expression ||
                      parsedExprIsL1GatherProducer expression || parsedExprIsL1ReduceProducer expression
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
    (state nextPEs nextMsl nextRelu next nextL1 : State)
    (accepted : checkParsedTopLine
      (InstructionLine.pe normalizedExpressions).toParsed = true)
    (supported : (normalizedExpressions.map NormalizedExpr.toParsed).all
      parsedExprIsSupportedPELineProducer = true)
    (executed : executeIntegerProducerLineAtPEs
      ((normalizedExpressions.map NormalizedExpr.toParsed).filter (fun expression =>
        !parsedExprIsL2BMProducer expression && !parsedExprIsMslMsrProducer expression &&
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
    (matrixWrites : executeParsedMatrixWritesAtMABs state allMABCoordinates
      (normalizedExpressions.map NormalizedExpr.toParsed) nextRelu = .ok next)
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
            parsedExprIsL1MwriteProducer expression.toParsed ||
              parsedExprIsL1GatherProducer expression.toParsed ||
              parsedExprIsL1ReduceProducer expression.toParsed) } := by
  simp [executeIntegerProducerInstructionLine, accepted, supported, executed, mslMsrWrites,
    reluWrites,
    matrixWrites, l1Writes, gatherWrites, reduceWrites, l1ToPE, l2Writes, List.any_map]
  rfl

end ProofsLean.MNCore
