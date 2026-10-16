import ProofsLean.BusLayout
import ProofsLean.Issue
import ProofsLean.PlusOne
import ProofsLean.Masks
import ProofsLean.MaskedPEMemory
import ProofsLean.ControlNormalization
import ProofsLean.Forwarding

/-! A deliberately partial instruction fragment: direct PE-memory reads,
the parsed integer ALU request, and masked or unmasked memory writes. This
composes existing datapath pieces without claiming timing, hazards, or
ISA-wide operand legality. -/
namespace ProofsLean.MNCore.PEMemory

open ProofsLean.MNCore.Issue

structure IntegerRegisterFiles where
  lm0 : Memory .lm0
  lm1 : Memory .lm1
  grf0 : Memory .grf0
  grf1 : Memory .grf1
  t : Memory .t
  maskRegisters : ProofsLean.MNCore.Masks.RegisterFile

structure DirectMemoryAccess where
  bank : Bank
  width : Width
  address : Fin bank.capacity
  deriving DecidableEq, Repr

structure ParsedIntegerContext where
  pe : Fin 4
  cycle : Fin 4
  bar0 : BitVec 12
  bar1 : BitVec 12
  tWord : BitVec 32
  group : Fin 2
  l2b : Fin 2
  l1b : Fin 8
  mab : Fin 16
  deriving DecidableEq, Repr

def ParsedIntegerContext.linearIndex (context : ParsedIntegerContext) : Nat :=
  (((context.group.val * 2 + context.l2b.val) * 8 + context.l1b.val) * 16 +
    context.mab.val) * 4 + context.pe.val

def ParsedIntegerContext.ofLinearIndex (index : Fin 2048) : ParsedIntegerContext where
  pe := ⟨index.val % 4, by have h := index.isLt; omega⟩
  cycle := 0
  bar0 := 0
  bar1 := 0
  tWord := 0
  group := ⟨index.val / 1024, by have h := index.isLt; omega⟩
  l2b := ⟨index.val / 512 % 2, by have h := index.isLt; omega⟩
  l1b := ⟨index.val / 64 % 8, by have h := index.isLt; omega⟩
  mab := ⟨index.val / 4 % 16, by have h := index.isLt; omega⟩

theorem ParsedIntegerContext.linearIndex_ofLinearIndex (index : Fin 2048) :
    (ParsedIntegerContext.ofLinearIndex index).linearIndex = index.val := by
  simp [ParsedIntegerContext.linearIndex, ParsedIntegerContext.ofLinearIndex]
  have h := index.isLt
  omega

theorem ParsedIntegerContext.linearIndex_lt (context : ParsedIntegerContext) :
    context.linearIndex < 2048 := by
  simp [ParsedIntegerContext.linearIndex]
  have hg := context.group.isLt
  have hl2 := context.l2b.isLt
  have hl1 := context.l1b.isLt
  have hm := context.mab.isLt
  have hp := context.pe.isLt
  omega

inductive ParsedIntegerInput where
  | memory (access : DirectMemoryAccess) (rounded : Bool)
  | fixed (value : IntegerALU.Bus)
  | forward (kind : ParsedForward) (rounded : Bool)
  deriving DecidableEq, Repr

def replicateIntegerLane : (precision : IntegerALU.Precision) → Nat → IntegerALU.Bus
  | .long, value =>
      let lane := BitVec.ofNat 64 value
      ⟨lane, lane⟩
  | .word, value =>
      let lane := BitVec.ofNat 32 value
      let longword := lane ++ lane
      ⟨longword, longword⟩
  | .half, value =>
      let lane := BitVec.ofNat 16 value
      let longword := lane ++ lane ++ lane ++ lane
      ⟨longword, longword⟩


def issueBankToRegisterBank : ProofsLean.MNCore.Issue.Bank → Option Bank
  | .lm0 => some .lm0
  | .lm1 => some .lm1
  | .grf0 => some .grf0
  | .grf1 => some .grf1
  | .t => some .t
  | .l1bm | .l2bm | .pdm | .dram | .omr => none

def parsedRegionAddressAt (region : ProofsLean.MNCore.Issue.Region) (cycle : Fin 4) : Nat :=
  match cycle.val with
  | 0 => region.address0
  | 1 => region.address1
  | 2 => region.address2
  | _ => region.address3

def parsedWidth? (encoded : Nat) : Option Width :=
  match encoded with
  | 1 => some .word
  | 2 => some .long
  | 4 => some .double
  | _ => none

/-- Resolve the memory address fields of a parsed operand for one PE and cycle.
This intentionally rejects rounded inputs and banks outside the PE memories.
The surrounding caller still supplies current BAR and T values. -/
def ParsedOperand.toDirectMemoryAccessMode? (operand : ParsedOperand)
    (allowDestinationMask : Bool)
    (pe cycle : Fin 4) (bar0 bar1 : BitVec 12) (tWord : BitVec 32) :
    Option DirectMemoryAccess :=
  match operand with
  | .mem access negated extended rounded mask =>
      if negated || extended || rounded || (!allowDestinationMask && mask.isSome) then none else
      match issueBankToRegisterBank access.bank, parsedWidth? access.region.width with
      | some bank, some width =>
          if (access.region.tIndirect && bank != .lm0) ||
              (access.region.madpe.isSome && bank != .lm0 && bank != .lm1) then none
          else
            let cycleAddress := parsedRegionAddressAt access.region cycle
            let effective := if bank == .t then cycle.val * 4 else
              let bar := if bank == .lm0 then bar0.toNat
                else if bank == .lm1 then bar1.toNat else 0
              let indirect := if access.region.tIndirect then tWord.toNat else 0
              let madpe := match access.region.madpe with
                | some threshold => if pe.val ≤ threshold then width.words else 0
                | none => 0
              let raw := bar + indirect + cycleAddress + madpe
              (raw / width.words * width.words) % bank.capacity
            some ⟨bank, width, ⟨effective, by
              by_cases isT : bank = .t
              · subst bank
                simp [effective, Bank.capacity]
                have hc := cycle.isLt
                omega
              · simp [effective, isT]
                exact Nat.mod_lt _ (Bank.capacity_positive bank)⟩⟩
      | none, _ | _, none => none
  | _ => none


def ParsedOperand.toDirectMemoryAccess? (operand : ParsedOperand)
    (pe cycle : Fin 4) (bar0 bar1 : BitVec 12) (tWord : BitVec 32) :
    Option DirectMemoryAccess :=
  ParsedOperand.toDirectMemoryAccessMode? operand false pe cycle bar0 bar1 tWord

def ParsedFixed.integerValue (fixed : ParsedFixed) (precision : IntegerALU.Precision)
    (group : Fin 2) (l2b : Fin 2) (l1b : Fin 8) (mab : Fin 16) (pe : Fin 4) : Nat :=
  match fixed with
  | .l2bid => group.val * 2 + l2b.val
  | .l1bid => l1b.val
  | .mabid => mab.val
  | .peid => mab.val * 4 + pe.val
  | .subpeid => pe.val
  | .msb1 => 2 ^ (precision.width - 1)

theorem parsed_fixed_integerValue_ofLinearIndex (fixed : ParsedFixed)
    (precision : IntegerALU.Precision) (index : Fin 2048) :
    ParsedFixed.integerValue fixed precision
      (ParsedIntegerContext.ofLinearIndex index).group
      (ParsedIntegerContext.ofLinearIndex index).l2b
      (ParsedIntegerContext.ofLinearIndex index).l1b
      (ParsedIntegerContext.ofLinearIndex index).mab
      (ParsedIntegerContext.ofLinearIndex index).pe =
    match fixed with
    | .l2bid => index.val / 512
    | .l1bid => index.val / 64 % 8
    | .mabid => index.val / 4 % 16
    | .peid => index.val % 64
    | .subpeid => index.val % 4
    | .msb1 => 2 ^ (precision.width - 1) := by
  cases fixed <;> simp [ParsedFixed.integerValue, ParsedIntegerContext.ofLinearIndex] <;> omega

example : ParsedFixed.integerValue .l2bid .long 1 1 0 0 0 = 3 := by decide
example : ParsedFixed.integerValue .l1bid .long 0 0 7 0 0 = 7 := by decide
example : ParsedFixed.integerValue .mabid .long 0 0 0 15 0 = 15 := by decide
example : ParsedFixed.integerValue .peid .long 0 0 0 15 3 = 63 := by decide

def roundNearestEven (kept remainder midpoint : Nat) : Nat :=
  kept + if midpoint < remainder || (remainder == midpoint && kept % 2 == 1)
    then 1 else 0

theorem roundNearestEven_tie_even (kept midpoint : Nat)
    (even : kept % 2 = 0) :
    roundNearestEven kept midpoint midpoint = kept := by
  simp [roundNearestEven, even]

theorem roundNearestEven_tie_odd (kept midpoint : Nat)
    (odd : kept % 2 = 1) :
    roundNearestEven kept midpoint midpoint = kept + 1 := by
  simp [roundNearestEven, odd]

/-- Rust `read_alu_input` converts each rounded single word through the MN-Core
half format: 1/6/9 sign/exponent/mantissa bits, round-to-nearest-even, no subnormals. -/
def roundSingleWordToHalf (word : BitVec 32) : BitVec 16 :=
  let raw := word.toNat
  let sign := raw / 2 ^ 31
  let exponent := raw / 2 ^ 23 % 256
  let mantissa := raw % 2 ^ 23
  let signBit := sign * 2 ^ 15
  if exponent == 0 then 0
  else if exponent == 255 then BitVec.ofNat 16 (signBit + 63 * 2 ^ 9)
  else
    let significand := 2 ^ 23 + mantissa
    let kept := significand / 2 ^ 14
    let remainder := significand % 2 ^ 14
    let rounded := roundNearestEven kept remainder (2 ^ 13)
    let carried := rounded == 2 ^ 10
    let halfExponent : Int := Int.ofNat exponent - 96 + if carried then 1 else 0
    if halfExponent >= 63 then BitVec.ofNat 16 (signBit + 63 * 2 ^ 9)
    else if halfExponent <= 0 then 0
    else BitVec.ofNat 16 (signBit + halfExponent.toNat * 2 ^ 9 +
      if carried then 0 else rounded % 2 ^ 9)

def roundSingleWordBusToHalf (words : WordBus) : WordBus := fun index =>
  match index.val with
  | 0 => roundSingleWordToHalf (words 0) ++ roundSingleWordToHalf (words 1)
  | 1 => roundSingleWordToHalf (words 2) ++ roundSingleWordToHalf (words 3)
  | _ => 0

def roundSingleInputBusToHalf (bus : IntegerALU.Bus) : IntegerALU.Bus :=
  pack (roundSingleWordBusToHalf (unpackALUBus bus))

theorem roundSingleWordBusToHalf_lane0 (words : WordBus) :
    IntegerALU.lane .half (pack (roundSingleWordBusToHalf words)) 0 =
      roundSingleWordToHalf (words 3) := by
  simp only [IntegerALU.lane, IntegerALU.Precision.width,
    roundSingleWordBusToHalf, pack, Fin.val_zero, Fin.val_one]
  simp only [Nat.reduceMul]
  rw [BitVec.extractLsb'_append_eq_of_add_le (by decide)]
  exact BitVec.extractLsb'_append_eq_right

theorem roundSingleWordBusToHalf_lane1 (words : WordBus) :
    IntegerALU.lane .half (pack (roundSingleWordBusToHalf words)) 1 =
      roundSingleWordToHalf (words 2) := by
  simp only [IntegerALU.lane, IntegerALU.Precision.width,
    roundSingleWordBusToHalf, pack, Fin.val_zero, Fin.val_one]
  simp only [Nat.reduceMul]
  rw [BitVec.extractLsb'_append_eq_of_add_le (by decide)]
  rw [BitVec.extractLsb'_append_eq_of_le (by decide)]
  simp

theorem roundSingleWordBusToHalf_lane2 (words : WordBus) :
    IntegerALU.lane .half (pack (roundSingleWordBusToHalf words)) 2 =
      roundSingleWordToHalf (words 1) := by
  simp only [IntegerALU.lane, IntegerALU.Precision.width,
    roundSingleWordBusToHalf, pack, Fin.val_zero, Fin.val_one]
  simp only [Nat.reduceMul]
  rw [BitVec.extractLsb'_append_eq_of_le (by decide)]
  exact BitVec.extractLsb'_append_eq_right

theorem roundSingleWordBusToHalf_lane3 (words : WordBus) :
    IntegerALU.lane .half (pack (roundSingleWordBusToHalf words)) 3 =
      roundSingleWordToHalf (words 0) := by
  simp only [IntegerALU.lane, IntegerALU.Precision.width,
    roundSingleWordBusToHalf, pack, Fin.val_zero, Fin.val_one]
  simp only [Nat.reduceMul]
  rw [BitVec.extractLsb'_append_eq_of_le (by decide)]
  rw [BitVec.extractLsb'_append_eq_of_le (by decide)]
  simp

theorem roundSingleInputBusToHalf_lane0 (bus : IntegerALU.Bus) :
    IntegerALU.lane .half (roundSingleInputBusToHalf bus) 0 =
      roundSingleWordToHalf (unpackALUBus bus 3) := by
  simpa [roundSingleInputBusToHalf] using
    roundSingleWordBusToHalf_lane0 (unpackALUBus bus)

theorem roundSingleInputBusToHalf_lane1 (bus : IntegerALU.Bus) :
    IntegerALU.lane .half (roundSingleInputBusToHalf bus) 1 =
      roundSingleWordToHalf (unpackALUBus bus 2) := by
  simpa [roundSingleInputBusToHalf] using
    roundSingleWordBusToHalf_lane1 (unpackALUBus bus)

theorem roundSingleInputBusToHalf_lane2 (bus : IntegerALU.Bus) :
    IntegerALU.lane .half (roundSingleInputBusToHalf bus) 2 =
      roundSingleWordToHalf (unpackALUBus bus 1) := by
  simpa [roundSingleInputBusToHalf] using
    roundSingleWordBusToHalf_lane2 (unpackALUBus bus)

theorem roundSingleInputBusToHalf_lane3 (bus : IntegerALU.Bus) :
    IntegerALU.lane .half (roundSingleInputBusToHalf bus) 3 =
      roundSingleWordToHalf (unpackALUBus bus 0) := by
  simpa [roundSingleInputBusToHalf] using
    roundSingleWordBusToHalf_lane3 (unpackALUBus bus)

example : roundSingleWordToHalf 0x3f800000 = 0x3e00 := by decide
example : roundSingleWordToHalf 0x3f802000 = 0x3e00 := by decide
example : roundSingleWordToHalf 0x3f806000 = 0x3e02 := by decide
example : roundSingleWordToHalf 0x3f807fff = 0x3e02 := by decide
example : roundSingleWordToHalf 0x3f804000 = 0x3e01 := by decide
example : roundSingleWordToHalf 0x00000001 = 0 := by decide
example : roundSingleWordToHalf 0x30000000 = 0 := by decide
example : roundSingleWordToHalf 0x30800000 = 0x0200 := by decide
example : roundSingleWordToHalf 0x4f7fffff = 0x7e00 := by decide
example : roundSingleWordToHalf 0x7f800000 = 0x7e00 := by decide
example : roundSingleWordToHalf 0xff800000 = 0xfe00 := by decide

def ParsedOperand.toParsedIntegerInput? (operand : ParsedOperand)
    (precision : IntegerALU.Precision)
    (group : Fin 2) (l2b : Fin 2) (l1b : Fin 8) (mab : Fin 16) (pe cycle : Fin 4)
    (bar0 bar1 : BitVec 12) (tWord : BitVec 32) : Option ParsedIntegerInput :=
  match operand with
  | .fixed fixed =>
      some (.fixed (replicateIntegerLane precision
        (ParsedFixed.integerValue fixed precision group l2b l1b mab pe)))
  | .forward kind _ _ rounded => some (.forward kind rounded)
  | .mem access _ _ rounded none =>
      (ParsedOperand.toDirectMemoryAccess? (.mem access false false false none)
        pe cycle bar0 bar1 tWord).map (fun resolved => .memory resolved rounded)
  | _ =>
      (ParsedOperand.toDirectMemoryAccess? operand pe cycle bar0 bar1 tWord).map
        (fun resolved => .memory resolved false)

theorem parsed_fixed_integer_input
    (fixed : ParsedFixed) (precision : IntegerALU.Precision)
    (group : Fin 2) (l2b : Fin 2) (l1b : Fin 8) (mab : Fin 16) (pe cycle : Fin 4)
    (bar0 bar1 : BitVec 12) (tWord : BitVec 32) :
    ParsedOperand.toParsedIntegerInput? (.fixed fixed) precision
      group l2b l1b mab pe cycle bar0 bar1 tWord =
        some (.fixed (replicateIntegerLane precision
          (ParsedFixed.integerValue fixed precision group l2b l1b mab pe))) := rfl

theorem parsed_integer_memory_input_ignores_negation_extension
    (access : Access) (negated extended : Bool) (precision : IntegerALU.Precision)
    (group : Fin 2) (l2b : Fin 2) (l1b : Fin 8) (mab : Fin 16)
    (pe cycle : Fin 4) (bar0 bar1 : BitVec 12) (tWord : BitVec 32) :
    ParsedOperand.toParsedIntegerInput?
      (.mem access negated extended false none) precision group l2b l1b mab pe cycle
      bar0 bar1 tWord =
    (ParsedOperand.toDirectMemoryAccess? (.mem access false false false none)
      pe cycle bar0 bar1 tWord).map (fun resolved => .memory resolved false) := rfl

theorem parsed_forward_integer_input (kind : ParsedForward) (negated extended rounded : Bool)
    (precision : IntegerALU.Precision)
    (group : Fin 2) (l2b : Fin 2) (l1b : Fin 8) (mab : Fin 16)
    (pe cycle : Fin 4) (bar0 bar1 : BitVec 12) (tWord : BitVec 32) :
    ParsedOperand.toParsedIntegerInput?
      (.forward kind negated extended rounded) precision group l2b l1b mab pe cycle
      bar0 bar1 tWord = some (.forward kind rounded) := rfl

theorem parsed_integer_memory_input_preserves_rounding
    (access : Access) (precision : IntegerALU.Precision)
    (group : Fin 2) (l2b : Fin 2) (l1b : Fin 8) (mab : Fin 16)
    (pe cycle : Fin 4) (bar0 bar1 : BitVec 12) (tWord : BitVec 32)
    (rounded : Bool) :
    ParsedOperand.toParsedIntegerInput?
      (.mem access false false rounded none) precision group l2b l1b mab pe cycle
      bar0 bar1 tWord =
    (ParsedOperand.toDirectMemoryAccess? (.mem access false false false none)
      pe cycle bar0 bar1 tWord).map (fun resolved => .memory resolved rounded) := rfl

def ParsedOperand.toDirectMemoryDestination? (operand : ParsedOperand)
    (pe cycle : Fin 4) (bar0 bar1 : BitVec 12) (tWord : BitVec 32) :
    Option DirectMemoryAccess :=
  ParsedOperand.toDirectMemoryAccessMode? operand true pe cycle bar0 bar1 tWord

def ParsedOperand.toUnmaskedDirectDestination? (operand : ParsedOperand)
    (pe cycle : Fin 4) (bar0 bar1 : BitVec 12) (tWord : BitVec 32) :
    Option DirectMemoryAccess :=
  match operand with
  | .mem _ _ _ _ none =>
      ParsedOperand.toDirectMemoryAccess? operand pe cycle bar0 bar1 tWord
  | _ => none

def ParsedOperand.toMaskRegisterEntry? (operand : ParsedOperand) : Option (Fin 15) :=
  match operand with
  | .omr entry _ =>
      if h : 1 ≤ entry ∧ entry < 16 then some ⟨entry - 1, by omega⟩ else none
  | _ => none

def parsedOperandHasSingleLineWriteMask : ParsedOperand → Bool
  | .mem _ _ _ _ mask | .bar _ _ mask | .omr _ mask => mask.isSome
  | _ => false

/-- Resolve the write mask for one PE cycle. Explicit selectors take priority;
the caller supplies an already-resolved multiline directive when no selector
appears on the OMR destination. -/
def resolveParsedMaskFlags? (mask : ParsedMask)
    (registers : ProofsLean.MNCore.Masks.RegisterFile) (cycle : Fin 4) :
    Option (BitVec 4) :=
  match mask with
  | .pattern _ bits =>
      some (if bits.getLsbD (3 - cycle.val) then BitVec.allOnes 4 else 0)
  | .entry _ index =>
      if h : index < 256 then
        some (ProofsLean.MNCore.Masks.readEntry registers
          ⟨index % 32, by omega⟩ cycle)
      else none

structure PEWordSelection where
  flags : BitVec 4
  longLong : Bool
  deriving DecidableEq, Repr

def parsedMaskLongLong : ParsedMask → Bool
  | .pattern ll _ | .entry ll _ => ll

def resolveParsedMaskSelection? (mask : ParsedMask)
    (registers : ProofsLean.MNCore.Masks.RegisterFile) (cycle : Fin 4) :
    Option PEWordSelection :=
  (resolveParsedMaskFlags? mask registers cycle).map fun flags =>
    ⟨flags, parsedMaskLongLong mask⟩

/-- OMR flag selection is independent of the directive's word width. -/
def resolveOmrDirectiveSelection? (directive : ParsedMaskDirective)
    (registers : ProofsLean.MNCore.Masks.RegisterFile) (cycle : Fin 4) :
    Option (BitVec 4) :=
  if directive.targets.maskRegister && directive.entry != 0 then
    resolveParsedMaskFlags? (.entry (directive.widthWords == 4) directive.entry)
      registers cycle
  else none

def directiveTargetsBank (targets : ParsedMaskTargets) : Bank → Bool
  | .lm0 => targets.lm0
  | .lm1 => targets.lm1
  | .grf0 => targets.grf0
  | .grf1 => targets.grf1
  | .t => targets.t

def resolveMemoryDirectiveSelection? (directive : ParsedMaskDirective) (bank : Bank)
    (registers : ProofsLean.MNCore.Masks.RegisterFile) (cycle : Fin 4) :
    Option PEWordSelection :=
  if directiveTargetsBank directive.targets bank && directive.entry != 0 then
    resolveParsedMaskSelection? (.entry (directive.widthWords == 4) directive.entry)
      registers cycle
  else none

example (registers : ProofsLean.MNCore.Masks.RegisterFile) (cycle : Fin 4) :
    resolveOmrDirectiveSelection?
      { targets := { maskRegister := true }, entry := 1 } registers cycle =
      some (registers 0 cycle) := by
  simp [resolveOmrDirectiveSelection?, resolveParsedMaskFlags?,
    ProofsLean.MNCore.Masks.readEntry]

example (registers : ProofsLean.MNCore.Masks.RegisterFile) (cycle : Fin 4) :
    resolveOmrDirectiveSelection? {} registers cycle = none := by
  simp [resolveOmrDirectiveSelection?]

def ParsedOperand.resolveOmrWriteSelection? (operand : ParsedOperand)
    (registers : ProofsLean.MNCore.Masks.RegisterFile) (cycle : Fin 4)
    (directive : ParsedMaskDirective) (hasSingleLineMask : Bool) : Option (BitVec 4) :=
  match operand with
  | .omr _ (some mask) => resolveParsedMaskFlags? mask registers cycle
  | .omr _ none =>
      if hasSingleLineMask then some (BitVec.allOnes 4)
      else some ((resolveOmrDirectiveSelection? directive registers cycle).getD
        (BitVec.allOnes 4))
  | _ => none

def ParsedOperand.resolveMemoryWriteSelection? (operand : ParsedOperand) (bank : Bank)
    (registers : ProofsLean.MNCore.Masks.RegisterFile) (cycle : Fin 4)
    (directive : ParsedMaskDirective) (hasSingleLineMask : Bool) :
    Option PEWordSelection :=
  match operand with
  | .mem _ _ _ _ (some mask) => resolveParsedMaskSelection? mask registers cycle
  | .mem _ _ _ _ none =>
      if hasSingleLineMask then some ⟨BitVec.allOnes 4, true⟩
      else some ((resolveMemoryDirectiveSelection? directive bank registers cycle).getD
        ⟨BitVec.allOnes 4, true⟩)
  | _ => none

def resolveFlushSelection? (flush : Option ParsedMask)
    (registers : ProofsLean.MNCore.Masks.RegisterFile) (cycle : Fin 4) :
    Option (Option PEWordSelection) :=
  match flush with
  | none => some none
  | some mask => (resolveParsedMaskSelection? mask registers cycle).map some

def parsedExprHasSingleLineWriteMask (expression : ParsedExpr) : Bool :=
  expression.destinations.any parsedOperandHasSingleLineWriteMask

theorem parsed_issue_line_mask_flag_iff
    (expressions : List ParsedExpr) :
    expressions.any parsedExprHasSingleLineWriteMask = true ↔
      ∃ expression, expression ∈ expressions ∧
        parsedExprHasSingleLineWriteMask expression = true := by
  simp [List.any_eq_true]

theorem parsed_issue_line_mask_cancels_unmasked_memory_target
    (expressions : List ParsedExpr)
    (registers : ProofsLean.MNCore.Masks.RegisterFile) (cycle : Fin 4)
    (directive : ParsedMaskDirective) (bank : Bank) (access : Access)
    (lineHasMask : expressions.any parsedExprHasSingleLineWriteMask = true) :
    ParsedOperand.resolveMemoryWriteSelection?
      (.mem access false false false none) bank registers cycle directive
      (expressions.any parsedExprHasSingleLineWriteMask) =
      some ⟨BitVec.allOnes 4, true⟩ := by
  simp [lineHasMask, ParsedOperand.resolveMemoryWriteSelection?]

theorem single_line_mask_cancels_omr_directive
    (registers : ProofsLean.MNCore.Masks.RegisterFile) (cycle : Fin 4)
    (directive : ParsedMaskDirective) :
    ParsedOperand.resolveOmrWriteSelection? (.omr 1 none) registers cycle directive true =
      some (BitVec.allOnes 4) := by
  simp [ParsedOperand.resolveOmrWriteSelection?]

theorem own_omr_mask_precedes_multiline_directive
    (registers : ProofsLean.MNCore.Masks.RegisterFile) (cycle : Fin 4)
    (directive : ParsedMaskDirective) (mask : ParsedMask) :
    ParsedOperand.resolveOmrWriteSelection? (.omr 1 (some mask)) registers cycle directive true =
      resolveParsedMaskFlags? mask registers cycle := rfl

theorem own_memory_mask_precedes_multiline_directive
    (registers : ProofsLean.MNCore.Masks.RegisterFile) (cycle : Fin 4)
    (directive : ParsedMaskDirective) (bank : Bank) (access : Access)
    (mask : ParsedMask) :
    ParsedOperand.resolveMemoryWriteSelection?
      (.mem access false false false (some mask)) bank registers cycle directive true =
      resolveParsedMaskSelection? mask registers cycle := rfl

theorem single_line_mask_cancels_memory_directive
    (registers : ProofsLean.MNCore.Masks.RegisterFile) (cycle : Fin 4)
    (directive : ParsedMaskDirective) (bank : Bank) (access : Access) :
    ParsedOperand.resolveMemoryWriteSelection?
      (.mem access false false false none) bank registers cycle directive true =
      some ⟨BitVec.allOnes 4, true⟩ := by
  simp [ParsedOperand.resolveMemoryWriteSelection?]

theorem untargeted_memory_uses_unmasked_selection
    (registers : ProofsLean.MNCore.Masks.RegisterFile) (cycle : Fin 4)
    (directive : ParsedMaskDirective) (bank : Bank) (access : Access)
    (notTargeted : directiveTargetsBank directive.targets bank = false) :
    ParsedOperand.resolveMemoryWriteSelection?
      (.mem access false false false none) bank registers cycle directive false =
      some ⟨BitVec.allOnes 4, true⟩ := by
  simp [ParsedOperand.resolveMemoryWriteSelection?, resolveMemoryDirectiveSelection?,
    notTargeted]

example (registers : ProofsLean.MNCore.Masks.RegisterFile) :
    resolveParsedMaskFlags? (.pattern false 8) registers 0 =
      some (BitVec.allOnes 4) := by simp [resolveParsedMaskFlags?]
example (registers : ProofsLean.MNCore.Masks.RegisterFile) :
    resolveParsedMaskFlags? (.pattern false 8) registers 1 = some 0 := by simp [resolveParsedMaskFlags?]

def ParsedAluName.integerInputCount (name : ParsedAluName) : Nat :=
  name.inputCount

structure ParsedIntegerAccesses where
  op : ParsedOp
  sourceX : DirectMemoryAccess
  sourceY : DirectMemoryAccess
  destination : DirectMemoryAccess
  hasIntegerRequest : ∃ precision aluOp,
    op.integerRequest = .ok (.integer precision aluOp)

structure ParsedMaskedIntegerAccesses where
  op : ParsedOp
  sourceX : ParsedIntegerInput
  sourceY : ParsedIntegerInput
  destination : DirectMemoryAccess
  writeSelection : PEWordSelection
  flushSelection : Option PEWordSelection
  hasRequest : ∃ request, op.executionRequest = .ok request

def ParsedIntegerAccesses.locations (accesses : ParsedIntegerAccesses) :=
  (accesses.sourceX, accesses.sourceY, accesses.destination)

structure ParsedIntegerMaskAccesses where
  op : ParsedOp
  sourceX : DirectMemoryAccess
  sourceY : DirectMemoryAccess
  destination : Fin 15
  selection : BitVec 4
  hasIntegerRequest : ∃ precision aluOp,
    op.integerRequest = .ok (.integer precision aluOp)

def ParsedIntegerMaskAccesses.locations (accesses : ParsedIntegerMaskAccesses) :=
  (accesses.sourceX, accesses.sourceY, accesses.destination)

/-- Lower the memory-only ALU expression subset from ParsedExpr to explicit
per-cycle accesses. Inputs with unsupported transformations, non-memory
sources, and instructions whose exact inputs are not represented stay out. -/
def ParsedExpr.toDirectIntegerAccesses? (expression : ParsedExpr)
    (pe cycle : Fin 4) (bar0 bar1 : BitVec 12) (tWord : BitVec 32) :
    Option ParsedIntegerAccesses :=
  match expression.op with
  | .alu name (some _) _ _ =>
      match hRequest : expression.op.integerRequest with
      | .ok (.integer precision aluOp) =>
          if expression.flush.isSome then none else
          match expression.sources, expression.destinations with
          | [source], [destination] =>
              if ParsedAluName.integerInputCount name != 1 then none else
              match ParsedOperand.toDirectMemoryAccess? source pe cycle bar0 bar1 tWord,
                    ParsedOperand.toUnmaskedDirectDestination? destination pe cycle bar0 bar1 tWord with
              | some sourceAccess, some destinationAccess =>
                  some ⟨expression.op, sourceAccess, sourceAccess, destinationAccess,
                    ⟨precision, aluOp, hRequest⟩⟩
              | _, _ => none
          | [sourceX, sourceY], [destination] =>
              if ParsedAluName.integerInputCount name != 2 then none else
              match ParsedOperand.toDirectMemoryAccess? sourceX pe cycle bar0 bar1 tWord,
                    ParsedOperand.toDirectMemoryAccess? sourceY pe cycle bar0 bar1 tWord,
                    ParsedOperand.toUnmaskedDirectDestination? destination pe cycle bar0 bar1 tWord with
              | some xAccess, some yAccess, some destinationAccess =>
                  some ⟨expression.op, xAccess, yAccess, destinationAccess,
                    ⟨precision, aluOp, hRequest⟩⟩
              | _, _, _ => none
          | _, _ => none
      | _ => none
  | _ => none

/-- Lower an integer ALU expression with a direct PE-memory destination,
resolving its explicit or multiline write mask and output flush for this cycle. -/
def ParsedExpr.toDirectMaskedIntegerAccessesInLine? (expression : ParsedExpr)
    (registers : ProofsLean.MNCore.Masks.RegisterFile)
    (directive : ParsedMaskDirective) (hasSingleLineMask : Bool)
    (group : Fin 2) (l2b : Fin 2) (l1b : Fin 8) (mab : Fin 16)
    (pe cycle : Fin 4) (bar0 bar1 : BitVec 12) (tWord : BitVec 32) :
    Option ParsedMaskedIntegerAccesses :=
  match expression.op with
  | .alu name (some parsedPrecision) _ _ =>
      match hRequest : expression.op.executionRequest with
      | .ok (.integer precision aluOp) =>
          match expression.sources, expression.destinations with
          | [source], [destination] =>
              if ParsedAluName.integerInputCount name != 1 then none else
              match ParsedOperand.toParsedIntegerInput? source parsedPrecision.laneWidth
                  group l2b l1b mab pe cycle bar0 bar1 tWord with
              | none => none
              | some sourceAccess =>
                  match ParsedOperand.toDirectMemoryDestination? destination pe cycle bar0 bar1 tWord with
                  | none => none
                  | some destinationAccess =>
                      match ParsedOperand.resolveMemoryWriteSelection? destination
                          destinationAccess.bank registers cycle directive
                          hasSingleLineMask,
                          resolveFlushSelection? expression.flush registers cycle with
                      | some writeSelection, some flushSelection =>
                          some ⟨expression.op, sourceAccess, sourceAccess, destinationAccess,
                            writeSelection, flushSelection, ⟨.integer precision aluOp, hRequest⟩⟩
                      | _, _ => none
          | [sourceX, sourceY], [destination] =>
              if ParsedAluName.integerInputCount name != 2 then none else
              match ParsedOperand.toParsedIntegerInput? sourceX parsedPrecision.laneWidth
                    group l2b l1b mab pe cycle bar0 bar1 tWord,
                    ParsedOperand.toParsedIntegerInput? sourceY parsedPrecision.laneWidth
                    group l2b l1b mab pe cycle bar0 bar1 tWord with
              | some xAccess, some yAccess =>
                  match ParsedOperand.toDirectMemoryDestination? destination pe cycle bar0 bar1 tWord with
                  | none => none
                  | some destinationAccess =>
                      match ParsedOperand.resolveMemoryWriteSelection? destination
                          destinationAccess.bank registers cycle directive
                          hasSingleLineMask,
                          resolveFlushSelection? expression.flush registers cycle with
                      | some writeSelection, some flushSelection =>
                          some ⟨expression.op, xAccess, yAccess, destinationAccess,
                            writeSelection, flushSelection, ⟨.integer precision aluOp, hRequest⟩⟩
                      | _, _ => none
              | _, _ => none
          | _, _ => none
      | _ => none
  | .zero | .immediate .. =>
      match hRequest : expression.op.executionRequest with
      | .ok request =>
          match expression.sources, expression.destinations with
          | [], [destination] =>
              match ParsedOperand.toDirectMemoryDestination? destination pe cycle bar0 bar1 tWord with
              | none => none
              | some destinationAccess =>
                  match ParsedOperand.resolveMemoryWriteSelection? destination
                      destinationAccess.bank registers cycle directive hasSingleLineMask,
                      resolveFlushSelection? expression.flush registers cycle with
                  | some writeSelection, some flushSelection =>
                      some ⟨expression.op, .memory destinationAccess false, .memory destinationAccess false,
                        destinationAccess, writeSelection, flushSelection, ⟨request, hRequest⟩⟩
                  | _, _ => none
          | _, _ => none
      | _ => none
  | _ => none

def ParsedExpr.toDirectMaskedIntegerAccesses? (expression : ParsedExpr)
    (registers : ProofsLean.MNCore.Masks.RegisterFile)
    (directive : ParsedMaskDirective)
    (group : Fin 2) (l2b : Fin 2) (l1b : Fin 8) (mab : Fin 16)
    (pe cycle : Fin 4) (bar0 bar1 : BitVec 12) (tWord : BitVec 32) :
    Option ParsedMaskedIntegerAccesses :=
  ParsedExpr.toDirectMaskedIntegerAccessesInLine? expression registers directive
    (parsedExprHasSingleLineWriteMask expression) group l2b l1b mab pe cycle bar0 bar1 tWord

inductive ParsedConstantDestination where
  | memory (accesses : ParsedMaskedIntegerAccesses)
  | maskRegister (entry : Fin 15)
  | noWrite

/-- Lower each destination of zero/imm/immu independently, as the Rust executor
writes the same computed bus to every destination in source order. -/
def ParsedExpr.toDirectMaskedConstantWrites? (expression : ParsedExpr)
    (registers : ProofsLean.MNCore.Masks.RegisterFile)
    (directive : ParsedMaskDirective) (hasSingleLineMask : Bool)
    (group : Fin 2) (l2b : Fin 2) (l1b : Fin 8) (mab : Fin 16)
    (pe cycle : Fin 4) (bar0 bar1 : BitVec 12) (tWord : BitVec 32) :
    Option (List ParsedConstantDestination) :=
  match expression.op with
  | .zero | .immediate .. => do
      expression.destinations.mapM fun destination =>
        match destination with
        | .nowrite => some .noWrite
        | .omr _ _ => do
            let entry ← ParsedOperand.toMaskRegisterEntry? destination
            let _ ← ParsedOperand.resolveOmrWriteSelection? destination registers cycle
              directive hasSingleLineMask
            some (.maskRegister entry)
        | _ => do
            let oneDestination := { expression with destinations := [destination] }
            let lowered ← ParsedExpr.toDirectMaskedIntegerAccessesInLine? oneDestination
              registers directive hasSingleLineMask group l2b l1b mab pe cycle bar0 bar1 tWord
            some (.memory lowered)
  | _ => none


def parsedZeroMaskedExpr : ParsedExpr where
  op := .zero
  sources := []
  destinations := [plusOneWrite]
  flush := none
  text := "zero $ln0v"

def parsedImmediateMaskedExpr (value : BitVec 32) (unsigned : Bool) : ParsedExpr where
  op := .immediate value unsigned
  sources := []
  destinations := [plusOneWrite]
  flush := none
  text := "imm $ln0v"

def parsedSubpeidMaskedExpr : ParsedExpr where
  op := .alu .inc (some .i) false none
  sources := [.fixed .subpeid]
  destinations := [plusOneWrite]
  flush := none
  text := "iinc $subpeid $ln0v"

def parsedMsb1MaskedExpr : ParsedExpr where
  op := .alu .inc (some .i) false none
  sources := [.fixed .msb1]
  destinations := [plusOneWrite]
  flush := none
  text := "iinc $msb1 $ln0v"

example : (ParsedExpr.toDirectMaskedIntegerAccesses? parsedSubpeidMaskedExpr
    (fun _ _ => 0) {} 0 0 0 0 0 2 0 0 0).isSome = true := by decide

example : (ParsedExpr.toDirectMaskedIntegerAccesses? parsedMsb1MaskedExpr
    (fun _ _ => 0) {} 0 0 0 0 0 2 0 0 0).isSome = true := by decide

def parsedImmediateMultiDestinationExpr : ParsedExpr where
  op := .immediate 0x12345678 false
  sources := []
  destinations := [plusOneWrite,
    .mem ⟨.grf0, ⟨1, 1, 1, 1, 1, false, none⟩⟩ false false false none,
    .nowrite]
  flush := none
  text := "imm f\"1.0\" $ln0v $lr1v"

example :
    (ParsedExpr.toDirectMaskedConstantWrites? parsedImmediateMultiDestinationExpr
      (fun _ _ => 0) {} false 0 0 0 0 0 0 0 0 0).isSome = true := by decide

def parsedZeroOmrExpr : ParsedExpr where
  op := .zero
  sources := []
  destinations := [.omr 1 none]
  flush := none
  text := "zero $omr1"

def parsedZeroNowriteExpr : ParsedExpr where
  op := .zero
  sources := []
  destinations := [.nowrite]
  flush := none
  text := "zero $nowrite"

example :
    (ParsedExpr.toDirectMaskedConstantWrites? parsedZeroOmrExpr
      (fun _ _ => 0) {} false 0 0 0 0 0 0 0 0 0).isSome = true := by decide

example :
    (ParsedExpr.toDirectMaskedConstantWrites? parsedZeroNowriteExpr
      (fun _ _ => 0) {} false 0 0 0 0 0 0 0 0 0).isSome = true := by decide

example :
    (ParsedExpr.toDirectMaskedIntegerAccesses? parsedZeroMaskedExpr (fun _ _ => 0) {}
      0 0 0 0 0 0 0 0 0).isSome = true := by decide

example :
    (ParsedExpr.toDirectMaskedIntegerAccesses?
      (parsedImmediateMaskedExpr 0x12345678 false) (fun _ _ => 0) {} 0 0 0 0 0 0 0 0 0).isSome =
      true := by decide

example : ParsedOperand.toDirectMemoryAccess?
    (.mem ⟨.grf0, ⟨1, 5, 5, 5, 5, false, none⟩⟩ false false false none)
    0 0 0 0 0 = some ⟨.grf0, .word, ⟨5, by decide⟩⟩ := by decide

example : ParsedOperand.toDirectMemoryAccess?
    (.mem ⟨.lm0, ⟨2, 3, 3, 3, 3, false, some 2⟩⟩ false false false none)
    2 0 3 0 0 = some ⟨.lm0, .long, ⟨8, by decide⟩⟩ := by decide

example : ParsedOperand.toDirectMemoryAccess?
    (.mem ⟨.lm0, ⟨1, 0, 0, 0, 0, false, none⟩⟩ true false false none)
    0 0 0 0 0 = none := by decide

example : ParsedOperand.toDirectMemoryAccess?
    (.mem ⟨.lm0, ⟨1, 0, 0, 0, 0, false, none⟩⟩ false true false none)
    0 0 0 0 0 = none := by decide

example : ParsedOperand.toDirectMemoryAccess?
    (.mem ⟨.lm0, ⟨1, 0, 0, 0, 0, false, none⟩⟩ false false false
      (some (.pattern false 0)))
    0 0 0 0 0 = none := by decide

example : ParsedOperand.toMaskRegisterEntry? (.omr 1 none) = some 0 := by decide
example : ParsedOperand.toMaskRegisterEntry? (.omr 15 none) = some 14 := by decide
example : ParsedOperand.toMaskRegisterEntry? (.omr 0 none) = none := by decide

example : (ParsedExpr.toDirectIntegerAccesses?
    ProofsLean.MNCore.Issue.plusOneParsed 0 0 0 0 0).map
      ParsedIntegerAccesses.locations = some
        (⟨.lm0, .long, ⟨0, by decide⟩⟩,
         ⟨.lm0, .long, ⟨0, by decide⟩⟩,
         ⟨.lm1, .long, ⟨0, by decide⟩⟩) := by decide


def readRegisterBank (files : IntegerRegisterFiles) (bank : Bank) (width : Width)
    (address : Fin bank.capacity) : WordBus :=
  match bank with
  | .lm0 => readWords .lm0 width files.lm0 address
  | .lm1 => readWords .lm1 width files.lm1 address
  | .grf0 => readWords .grf0 width files.grf0 address
  | .grf1 => readWords .grf1 width files.grf1 address
  | .t => readWords .t width files.t address

theorem readRegisterBank_t_reads_all_four_words (files : IntegerRegisterFiles)
    (width : Width) (address : Fin Bank.t.capacity) (index : Fin 4) :
    readRegisterBank files .t width address index =
      files.t (advance .t address index.val) := by
  simp [readRegisterBank, readWords, count, Bank.capacity, advance]

theorem readRegisterBank_t_independent_of_width (files : IntegerRegisterFiles)
    (width : Width) (address : Fin Bank.t.capacity) :
    readRegisterBank files .t width address =
      readRegisterBank files .t .word address := by
  funext index
  have hindex : index.val < 4 := by have h := index.isLt; exact h
  simp [readRegisterBank, readWords, count, Bank.capacity, advance, hindex]

def writeRegisterBank (files : IntegerRegisterFiles) (bank : Bank) (width : Width)
    (address : Fin bank.capacity) (data : WordBus) : IntegerRegisterFiles :=
  match bank with
  | .lm0 => { files with lm0 := writeWords .lm0 width files.lm0 address data }
  | .lm1 => { files with lm1 := writeWords .lm1 width files.lm1 address data }
  | .grf0 => { files with grf0 := writeWords .grf0 width files.grf0 address data }
  | .grf1 => { files with grf1 := writeWords .grf1 width files.grf1 address data }
  | .t => { files with t := writeWords .t width files.t address data }

def writeRegisterBankMasked (files : IntegerRegisterFiles) (bank : Bank) (width : Width)
    (address : Fin bank.capacity) (data : WordBus) (selection : PEWordSelection) :
    IntegerRegisterFiles :=
  match bank with
  | .lm0 => { files with lm0 :=
      (writeWordsMasked .lm0 width files.lm0 address data selection.flags selection.longLong) }
  | .lm1 => { files with lm1 :=
      (writeWordsMasked .lm1 width files.lm1 address data selection.flags selection.longLong) }
  | .grf0 => { files with grf0 :=
      (writeWordsMasked .grf0 width files.grf0 address data selection.flags selection.longLong) }
  | .grf1 => { files with grf1 :=
      (writeWordsMasked .grf1 width files.grf1 address data selection.flags selection.longLong) }
  | .t => { files with t :=
      (writeWordsMasked .t width files.t address data selection.flags selection.longLong) }

def readDirectAccess (files : IntegerRegisterFiles) (access : DirectMemoryAccess) : WordBus :=
  readRegisterBank files access.bank access.width access.address

def ParsedIntegerInput.applyRounding (rounded : Bool) (bus : IntegerALU.Bus) :
    IntegerALU.Bus := if rounded then roundSingleInputBusToHalf bus else bus

def ParsedIntegerInput.forwardUnit : ParsedForward → ProofsLean.MNCore.Forwarding.Unit
  | .aluf => .alu
  | .mauf => .mau
  | .lbf => .l1ToPE
  | .mreadf => .matrixRead

def ParsedIntegerInput.read (files : IntegerRegisterFiles) (input : ParsedIntegerInput) :
    ProofsLean.StepResult IntegerALU.Bus :=
  match input with
  | .memory access rounded =>
      .ok (applyRounding rounded (pack (readDirectAccess files access)))
  | .fixed value => .ok value
  | .forward _ _ => .unknown

def ParsedIntegerInput.readWithForwarding (files : IntegerRegisterFiles)
    (slots : ProofsLean.MNCore.Forwarding.Slots) (cycle : Fin 4)
    (input : ParsedIntegerInput) : ProofsLean.StepResult IntegerALU.Bus :=
  match input with
  | .forward kind rounded =>
      match slots (ParsedIntegerInput.forwardUnit kind) cycle with
      | .known bus => .ok (applyRounding rounded bus)
      | .poison => .failure
      | .unknown => .unknown
  | _ => read files input

def ParsedIntegerInput.resolveForwarding? (slots : ProofsLean.MNCore.Forwarding.Slots)
    (cycle : Fin 4) (input : ParsedIntegerInput) : Option ParsedIntegerInput :=
  match input with
  | .forward kind rounded =>
      match slots (forwardUnit kind) cycle with
      | .known bus => some (.fixed (applyRounding rounded bus))
      | .poison | .unknown => none
  | _ => some input

theorem ParsedIntegerInput.readWithForwarding_resolved
    (files : IntegerRegisterFiles) (slots : ProofsLean.MNCore.Forwarding.Slots)
    (cycle : Fin 4) (input resolved : ParsedIntegerInput)
    (hResolved : resolveForwarding? slots cycle input = some resolved) :
    readWithForwarding files slots cycle input = read files resolved := by
  cases input with
  | memory access rounded =>
      simp [resolveForwarding?] at hResolved
      cases hResolved
      rfl
  | fixed value =>
      simp [resolveForwarding?] at hResolved
      cases hResolved
      rfl
  | forward kind rounded =>
      cases hSlot : slots (forwardUnit kind) cycle with
      | known bus =>
          simp [resolveForwarding?, hSlot] at hResolved
          cases hResolved
          simp [readWithForwarding, hSlot, read]
      | poison => simp [resolveForwarding?, hSlot] at hResolved
      | unknown => simp [resolveForwarding?, hSlot] at hResolved

theorem parsedIntegerInput_read_rounded (files : IntegerRegisterFiles)
    (access : DirectMemoryAccess) :
    ParsedIntegerInput.read files (.memory access true) =
      .ok (roundSingleInputBusToHalf (pack (readDirectAccess files access))) := rfl

theorem parsedIntegerInput_read_unrounded (files : IntegerRegisterFiles)
    (access : DirectMemoryAccess) :
    ParsedIntegerInput.read files (.memory access false) =
      .ok (pack (readDirectAccess files access)) := rfl

theorem parsedIntegerInput_forward_known (files : IntegerRegisterFiles)
    (slots : ProofsLean.MNCore.Forwarding.Slots) (cycle : Fin 4)
    (kind : ParsedForward) (rounded : Bool) (bus : IntegerALU.Bus)
    (known : slots (ParsedIntegerInput.forwardUnit kind) cycle = .known bus) :
    ParsedIntegerInput.readWithForwarding files slots cycle (.forward kind rounded) =
      .ok (ParsedIntegerInput.applyRounding rounded bus) := by
  simp [ParsedIntegerInput.readWithForwarding, known]

theorem parsedIntegerInput_forward_poison_fails (files : IntegerRegisterFiles)
    (slots : ProofsLean.MNCore.Forwarding.Slots) (cycle : Fin 4)
    (kind : ParsedForward) (rounded : Bool)
    (poisoned : slots (ParsedIntegerInput.forwardUnit kind) cycle = .poison) :
    ParsedIntegerInput.readWithForwarding files slots cycle (.forward kind rounded) =
      .failure := by simp [ParsedIntegerInput.readWithForwarding, poisoned]

theorem parsedIntegerInput_forward_unknown_stays_unknown (files : IntegerRegisterFiles)
    (slots : ProofsLean.MNCore.Forwarding.Slots) (cycle : Fin 4)
    (kind : ParsedForward) (rounded : Bool)
    (unresolved : slots (ParsedIntegerInput.forwardUnit kind) cycle = .unknown) :
    ParsedIntegerInput.readWithForwarding files slots cycle (.forward kind rounded) =
      .unknown := by simp [ParsedIntegerInput.readWithForwarding, unresolved]

def writeDirectAccess (files : IntegerRegisterFiles) (access : DirectMemoryAccess)
    (data : WordBus) : IntegerRegisterFiles :=
  writeRegisterBank files access.bank access.width access.address data

def writeDirectAccessMasked (files : IntegerRegisterFiles) (access : DirectMemoryAccess)
    (data : WordBus) (selection : PEWordSelection) : IntegerRegisterFiles :=
  writeRegisterBankMasked files access.bank access.width access.address data selection

theorem readRegisterBank_after_write (files : IntegerRegisterFiles)
    (bank : Bank) (width : Width) (address : Fin bank.capacity)
    (data : WordBus) (index : Fin 4) (within : index.val < count bank width) :
    readRegisterBank (writeRegisterBank files bank width address data) bank width address index =
      data index := by
  cases bank <;> exact read_after_write _ _ _ _ _ _ within

theorem readDirectAccessMasked_after_write (files : IntegerRegisterFiles)
    (access : DirectMemoryAccess) (data : WordBus) (selection : PEWordSelection)
    (index : Fin 4) (within : index.val < count access.bank access.width) :
    readDirectAccess (writeDirectAccessMasked files access data selection) access index =
      mergeSelectedWord (readDirectAccess files access index) (data index)
        (selectedWordMask selection.flags selection.longLong index) := by
  cases access with
  | mk bank width address =>
    cases bank with
    | lm0 =>
        simp only [readDirectAccess, readRegisterBank, writeDirectAccessMasked,
          writeRegisterBankMasked]
        rw [readWordsMasked_after_mask .lm0 width files.lm0 address data
          selection.flags selection.longLong index within]
        simp [readWords, within]
    | lm1 =>
        simp only [readDirectAccess, readRegisterBank, writeDirectAccessMasked,
          writeRegisterBankMasked]
        rw [readWordsMasked_after_mask .lm1 width files.lm1 address data
          selection.flags selection.longLong index within]
        simp [readWords, within]
    | grf0 =>
        simp only [readDirectAccess, readRegisterBank, writeDirectAccessMasked,
          writeRegisterBankMasked]
        rw [readWordsMasked_after_mask .grf0 width files.grf0 address data
          selection.flags selection.longLong index within]
        simp [readWords, within]
    | grf1 =>
        simp only [readDirectAccess, readRegisterBank, writeDirectAccessMasked,
          writeRegisterBankMasked]
        rw [readWordsMasked_after_mask .grf1 width files.grf1 address data
          selection.flags selection.longLong index within]
        simp [readWords, within]
    | t =>
        simp only [readDirectAccess, readRegisterBank, writeDirectAccessMasked,
          writeRegisterBankMasked]
        rw [readWordsMasked_after_mask .t width files.t address data
          selection.flags selection.longLong index within]
        simp [readWords, within]


def parsedOutputAfterFlush (selection : Option PEWordSelection)
    (output : IntegerALU.Bus) : IntegerALU.Bus :=
  match selection with
  | none => output
  | some selected => ProofsLean.MNCore.Masks.flushBus
      (if selected.longLong then .double else .long) selected.flags output

def parsedIntegerMaskedRegisterStep (files : IntegerRegisterFiles)
    (accesses : ParsedMaskedIntegerAccesses) (reduced : Bool) :
    ProofsLean.StepResult IntegerRegisterFiles :=
  match ParsedIntegerInput.read files accesses.sourceX with
  | .failure => .failure
  | .unknown => .unknown
  | .ok x =>
    match ParsedIntegerInput.read files accesses.sourceY with
    | .failure => .failure
    | .unknown => .unknown
    | .ok y =>
      match evaluateParsedIntegerAlu accesses.op x y reduced with
      | .ok output =>
          .ok (writeDirectAccessMasked files accesses.destination
            (unpackALUBus (parsedOutputAfterFlush accesses.flushSelection output.value))
            accesses.writeSelection)
      | .failure => .failure
      | .unknown => .unknown

theorem parsedIntegerMaskedRegisterStep_success (files : IntegerRegisterFiles)
    (accesses : ParsedMaskedIntegerAccesses) (reduced : Bool)
    (x y : IntegerALU.Bus) (output : IntegerALU.BusResult)
    (sourceX : ParsedIntegerInput.read files accesses.sourceX = .ok x)
    (sourceY : ParsedIntegerInput.read files accesses.sourceY = .ok y)
    (evaluated : evaluateParsedIntegerAlu accesses.op x y reduced = .ok output) :
    parsedIntegerMaskedRegisterStep files accesses reduced =
      .ok (writeDirectAccessMasked files accesses.destination
        (unpackALUBus (parsedOutputAfterFlush accesses.flushSelection output.value))
        accesses.writeSelection) := by
  simp [parsedIntegerMaskedRegisterStep, sourceX, sourceY, evaluated]

def executeParsedMaskedIntegerExpr? (files : IntegerRegisterFiles)
    (expression : ParsedExpr) (directive : ParsedMaskDirective)
    (group : Fin 2) (l2b : Fin 2) (l1b : Fin 8) (mab : Fin 16)
    (pe cycle : Fin 4) (bar0 bar1 : BitVec 12) (tWord : BitVec 32) :
    Option (ProofsLean.StepResult IntegerRegisterFiles) :=
  match ParsedExpr.toDirectMaskedIntegerAccesses? expression files.maskRegisters
      directive group l2b l1b mab pe cycle bar0 bar1 tWord with
  | some accesses => some (parsedIntegerMaskedRegisterStep files accesses false)
  | none => none

structure ParsedMaskExecutionControl where
  directive : ParsedMaskDirective
  context : ParsedIntegerContext
  elapsedWords : Nat
  deriving DecidableEq, Repr

inductive ParsedMaskedIssueLine where
  | pe (expressions : List ParsedExpr)
  | nop
  deriving DecidableEq, Repr

abbrev ParsedMaskedSourceStatement :=
  ProofsLean.ControlNormalization.Statement ParsedMaskDirective ParsedMaskedIssueLine

def updateParsedMaskDirective (next : ParsedMaskDirective)
    (current : ParsedMaskExecutionControl) : ParsedMaskExecutionControl :=
  { current with directive := next }

def advanceParsedMaskControl (current : ParsedMaskExecutionControl)
    (_line : ParsedMaskedIssueLine) : ParsedMaskExecutionControl :=
  { current with elapsedWords := current.elapsedWords + 1 }

def parsedAccessAbsoluteCycle (control : ParsedMaskExecutionControl)
    (cycle : Fin 4) : Nat := control.elapsedWords * 4 + cycle.val

def advanceParsedControlThroughSource :
    List ParsedMaskedSourceStatement → ParsedMaskExecutionControl →
      ParsedMaskExecutionControl
  | [], control => control
  | .directive directive :: rest, control =>
      advanceParsedControlThroughSource rest (updateParsedMaskDirective directive control)
  | .issue line :: rest, control =>
      advanceParsedControlThroughSource rest (advanceParsedMaskControl control line)

theorem parsed_source_clock_matches_issue_cost
    (source : List ParsedMaskedSourceStatement) (control : ParsedMaskExecutionControl) :
    (advanceParsedControlThroughSource source control).elapsedWords =
      control.elapsedWords + ProofsLean.ControlNormalization.cost source := by
  induction source generalizing control with
  | nil => rfl
  | cons statement rest ih =>
      cases statement with
      | directive directive =>
          simp [advanceParsedControlThroughSource,
            updateParsedMaskDirective, ProofsLean.ControlNormalization.cost, ih]
      | issue line =>
          simp [advanceParsedControlThroughSource, advanceParsedMaskControl,
            ProofsLean.ControlNormalization.cost, ih]
          omega

theorem parsed_source_access_clock_matches_issue_cost
    (source : List ParsedMaskedSourceStatement) (control : ParsedMaskExecutionControl)
    (cycle : Fin 4) :
    parsedAccessAbsoluteCycle (advanceParsedControlThroughSource source control) cycle =
      parsedAccessAbsoluteCycle control cycle +
        4 * ProofsLean.ControlNormalization.cost source := by
  simp [parsedAccessAbsoluteCycle, parsed_source_clock_matches_issue_cost]
  omega

inductive PEHazardDistance where
  | steps (count : Nat)
  | cycles (count : Nat)
  deriving DecidableEq, Repr

structure TimedPEAccess where
  access : DirectMemoryAccess
  write : Bool
  startWord : Nat
  cycle : Fin 4
  deriving DecidableEq, Repr

def TimedPEAccess.absoluteCycle (event : TimedPEAccess) : Nat :=
  event.startWord * 4 + event.cycle.val

def TimedPEAccess.ofControl (control : ParsedMaskExecutionControl)
    (access : DirectMemoryAccess) (write : Bool) (cycle : Fin 4) : TimedPEAccess :=
  ⟨access, write, control.elapsedWords, cycle⟩

def TimedPEAccess.rangeStart (event : TimedPEAccess) : Nat :=
  if event.access.bank = .t then event.cycle.val else event.access.address.val

def TimedPEAccess.rangeLength (event : TimedPEAccess) : Nat :=
  if event.access.bank = .t then 1 else event.access.width.words

def TimedPEAccess.rangesOverlap (left right : TimedPEAccess) : Bool :=
  left.access.bank == right.access.bank &&
    left.rangeStart < right.rangeStart + right.rangeLength &&
    right.rangeStart < left.rangeStart + left.rangeLength

def peHazardRequirement? (earlier later : TimedPEAccess) : Option PEHazardDistance :=
  if !earlier.write || later.write then none
  else match earlier.access.bank, later.access.bank with
    | .lm0, .lm0 | .lm1, .lm1 => some (.steps 3)
    | .grf0, .grf0 | .grf1, .grf1 | .t, .t =>
        if earlier.rangesOverlap later then some (.cycles 7) else none
    | _, _ => none

def peHazardSatisfied (earlier later : TimedPEAccess) : Prop :=
  earlier.startWord < later.startWord ∧
    match peHazardRequirement? earlier later with
    | none => True
    | some (.steps count) =>
        count * 4 ≤ (later.startWord - earlier.startWord) * 4
    | some (.cycles count) =>
        count ≤ later.absoluteCycle - earlier.absoluteCycle

def parsedHazardCycles : List (Fin 4) := [0, 1, 2, 3]

def parsedHazardPatternEnables (mask : Option ParsedMask) (cycle : Fin 4) : Bool :=
  match mask with
  | some (.pattern _ bits) => bits.getLsbD (3 - cycle.val)
  | _ => true

def tIndirectHazardAccess (cycle : Fin 4) : DirectMemoryAccess :=
  ⟨.t, .word, ⟨cycle.val, by have h := cycle.isLt; simp [Bank.capacity]; omega⟩⟩

def ParsedOperand.toTimedPEHazardEvents? (operand : ParsedOperand) (write : Bool)
    (control : ParsedMaskExecutionControl) : Option (List TimedPEAccess) :=
  match operand with
  | .mem access _ _ _ ownMask =>
      match issueBankToRegisterBank access.bank with
      | none => some []
      | some _ => do
          let resolved ← parsedHazardCycles.mapM fun cycle =>
            ParsedOperand.toDirectMemoryAccessMode? operand true
              control.context.pe cycle control.context.bar0 control.context.bar1
              control.context.tWord
          pure <| (parsedHazardCycles.zip resolved).flatMap fun (cycle, direct) =>
            if write && !parsedHazardPatternEnables ownMask cycle then []
            else
              let primary := [TimedPEAccess.ofControl control direct write cycle]
              let indirect := if !write && access.region.tIndirect then
                [TimedPEAccess.ofControl control (tIndirectHazardAccess cycle) false cycle]
                else []
              primary ++ indirect
  | _ => some []

def ParsedExpr.toTimedPEHazardEvents? (expression : ParsedExpr)
    (control : ParsedMaskExecutionControl) : Option (List TimedPEAccess) := do
  let reads ← expression.sources.mapM fun operand =>
    ParsedOperand.toTimedPEHazardEvents? operand false control
  let writes ← expression.destinations.mapM fun operand =>
    ParsedOperand.toTimedPEHazardEvents? operand true control
  pure (reads.flatten ++ writes.flatten)

def ParsedMaskedIssueLine.toTimedPEHazardEvents?
    (line : ParsedMaskedIssueLine) (control : ParsedMaskExecutionControl) :
    Option (List TimedPEAccess) :=
  match line with
  | .nop => some []
  | .pe expressions => do
      let perExpression ← expressions.mapM fun expression =>
        ParsedExpr.toTimedPEHazardEvents? expression control
      pure perExpression.flatten

theorem parsed_mask_pattern_controls_hazard_write_cycle
    (cycle : Fin 4) (bits : BitVec 4) :
    parsedHazardPatternEnables (some (.pattern false bits)) cycle =
      bits.getLsbD (3 - cycle.val) := rfl

theorem parsed_mask_entry_keeps_all_hazard_write_cycles
    (cycle : Fin 4) (longLong : Bool) (entry : Nat) :
    parsedHazardPatternEnables (some (.entry longLong entry)) cycle = true := rfl

theorem t_indirect_hazard_access_uses_cycle_region (cycle : Fin 4) :
    (tIndirectHazardAccess cycle).bank = .t ∧
      TimedPEAccess.rangeStart
        (TimedPEAccess.ofControl
          ⟨{}, ⟨0, cycle, 0, 0, 0, 0, 0, 0, 0⟩, 0⟩
          (tIndirectHazardAccess cycle) false cycle) = cycle.val := by
  constructor
  · rfl
  · simp [TimedPEAccess.rangeStart, TimedPEAccess.ofControl, tIndirectHazardAccess]

structure PEHazardConstraint where
  earlier : TimedPEAccess
  later : TimedPEAccess
  distance : Nat
  required : Nat
  deriving DecidableEq, Repr

def PEHazardConstraint.violated (constraint : PEHazardConstraint) : Bool :=
  constraint.distance < constraint.required

def violatingPEHazardConstraints (constraints : List PEHazardConstraint) :
    List PEHazardConstraint :=
  constraints.filter PEHazardConstraint.violated

theorem pe_hazard_violation_filter_exact
    (constraints : List PEHazardConstraint) (constraint : PEHazardConstraint) :
    constraint ∈ violatingPEHazardConstraints constraints ↔
      constraint ∈ constraints ∧ constraint.distance < constraint.required := by
  simp [violatingPEHazardConstraints, PEHazardConstraint.violated]

def makePEHazardConstraint? (earlier later : TimedPEAccess) :
    Option PEHazardConstraint :=
  if earlier.startWord < later.startWord then
    match peHazardRequirement? earlier later with
    | none => none
    | some (.steps count) =>
        some ⟨earlier, later, (later.startWord - earlier.startWord) * 4, count * 4⟩
    | some (.cycles count) =>
        some ⟨earlier, later,
          later.absoluteCycle - earlier.absoluteCycle, count⟩
  else none

def peHazardConstraintsBetween (earlier later : List TimedPEAccess) :
    List PEHazardConstraint :=
  earlier.flatMap fun write =>
    later.filterMap fun access =>
      match makePEHazardConstraint? write access with
      | some constraint =>
          if access.startWord - write.startWord ≤ 4 then some constraint else none
      | none => none

theorem pe_hazard_constraints_between_complete
    (earlier later : List TimedPEAccess) (constraint : PEHazardConstraint) :
    constraint ∈ peHazardConstraintsBetween earlier later ↔
      ∃ write, write ∈ earlier ∧ ∃ access, access ∈ later ∧
        (match makePEHazardConstraint? write access with
         | some candidate =>
             if access.startWord - write.startWord ≤ 4 then some candidate else none
         | none => none) = some constraint := by
  simp [peHazardConstraintsBetween, List.mem_flatMap, List.mem_filterMap]

def collectPEHazardConstraintsAux (earlier : List TimedPEAccess)
    (remaining : List (List TimedPEAccess)) : List PEHazardConstraint :=
  match remaining with
  | [] => []
  | current :: rest =>
      peHazardConstraintsBetween earlier current ++
        collectPEHazardConstraintsAux (earlier ++ current) rest

def collectPEHazardConstraints (eventsByIssue : List (List TimedPEAccess)) :
    List PEHazardConstraint :=
  collectPEHazardConstraintsAux [] eventsByIssue

def parsedSourcePEHazardEvents? (source : List ParsedMaskedSourceStatement)
    (control : ParsedMaskExecutionControl) : Option (List (List TimedPEAccess)) :=
  let compiled := ProofsLean.ControlNormalization.compileAdvancing
    updateParsedMaskDirective advanceParsedMaskControl source control
  compiled.mapM fun instruction =>
    instruction.2.toTimedPEHazardEvents? instruction.1

def parsedSourcePEHazardConstraints? (source : List ParsedMaskedSourceStatement)
    (control : ParsedMaskExecutionControl) : Option (List PEHazardConstraint) :=
  (parsedSourcePEHazardEvents? source control).map collectPEHazardConstraints

def parsedSourcePEHazardViolations? (source : List ParsedMaskedSourceStatement)
    (control : ParsedMaskExecutionControl) : Option (List PEHazardConstraint) :=
  (parsedSourcePEHazardConstraints? source control).map violatingPEHazardConstraints

theorem pe_hazard_constraint_uses_rule_distance
    (earlier later : TimedPEAccess) (constraint : PEHazardConstraint)
    (made : makePEHazardConstraint? earlier later = some constraint) :
    earlier.startWord < later.startWord ∧
      ∃ ruleDistance, peHazardRequirement? earlier later = some ruleDistance ∧
        constraint.earlier = earlier ∧ constraint.later = later ∧
      (match ruleDistance with
       | .steps count => constraint.distance =
            (later.startWord - earlier.startWord) * 4 ∧ constraint.required = count * 4
       | .cycles count => constraint.distance =
            later.absoluteCycle - earlier.absoluteCycle ∧ constraint.required = count) := by
  by_cases htime : earlier.startWord < later.startWord
  · cases hreq : peHazardRequirement? earlier later with
    | none => simp [makePEHazardConstraint?, htime, hreq] at made
    | some ruleDistance =>
        cases ruleDistance with
        | steps count =>
            simp [makePEHazardConstraint?, htime, hreq] at made
            cases made
            exact ⟨htime, .steps count, rfl, rfl, rfl, by simp⟩
        | cycles count =>
            simp [makePEHazardConstraint?, htime, hreq] at made
            cases made
            exact ⟨htime, .cycles count, rfl, rfl, rfl, by simp⟩
  · simp [makePEHazardConstraint?, htime] at made

theorem pe_hazard_constraint_violation_matches_pair_safety
    (earlier later : TimedPEAccess) (constraint : PEHazardConstraint)
    (made : makePEHazardConstraint? earlier later = some constraint) :
    constraint.violated = true ↔ ¬ peHazardSatisfied earlier later := by
  have info := pe_hazard_constraint_uses_rule_distance earlier later constraint made
  rcases info with ⟨timeOrder, ruleDistance, requirement, sourceEq, targetEq, distanceFields⟩
  cases ruleDistance with
  | steps count =>
      rcases distanceFields with ⟨hdistance, hrequired⟩
      simp [PEHazardConstraint.violated, peHazardSatisfied, requirement,
        hdistance, hrequired, timeOrder]
  | cycles count =>
      rcases distanceFields with ⟨hdistance, hrequired⟩
      simp [PEHazardConstraint.violated, peHazardSatisfied, requirement,
        hdistance, hrequired, timeOrder]

theorem lm_pe_hazard_requires_three_issue_words
    (earlier later : TimedPEAccess)
    (write : earlier.write = true) (read : later.write = false)
    (sameBank : earlier.access.bank = later.access.bank)
    (lm : earlier.access.bank = .lm0 ∨ earlier.access.bank = .lm1) :
    peHazardRequirement? earlier later = some (.steps 3) := by
  cases hEarlier : earlier.access.bank <;>
    cases hLater : later.access.bank <;>
    simp_all [peHazardRequirement?]

theorem grf_t_pe_hazard_requires_seven_cycles
    (earlier later : TimedPEAccess)
    (write : earlier.write = true) (read : later.write = false)
    (sameBank : earlier.access.bank = later.access.bank)
    (grfT : earlier.access.bank = .grf0 ∨ earlier.access.bank = .grf1 ∨
      earlier.access.bank = .t)
    (overlap : earlier.rangesOverlap later = true) :
    peHazardRequirement? earlier later = some (.cycles 7) := by
  cases hEarlier : earlier.access.bank <;>
    cases hLater : later.access.bank <;>
    simp_all [peHazardRequirement?]

theorem lm_pe_hazard_satisfied_after_three_words
    (earlier later : TimedPEAccess)
    (sameBank : earlier.access.bank = later.access.bank)
    (lm : earlier.access.bank = .lm0 ∨ earlier.access.bank = .lm1)
    (accessed : earlier.write = true ∧ later.write = false)
    (distance : earlier.startWord + 3 ≤ later.startWord) :
    peHazardSatisfied earlier later := by
  constructor
  · omega
  rw [lm_pe_hazard_requires_three_issue_words earlier later accessed.1 accessed.2
    sameBank lm]
  omega

theorem grf_t_pe_hazard_satisfied_after_seven_cycles
    (earlier later : TimedPEAccess)
    (sameBank : earlier.access.bank = later.access.bank)
    (grfT : earlier.access.bank = .grf0 ∨ earlier.access.bank = .grf1 ∨
      earlier.access.bank = .t)
    (accessed : earlier.write = true ∧ later.write = false)
    (overlap : earlier.rangesOverlap later = true)
    (distance : earlier.absoluteCycle + 7 ≤ later.absoluteCycle) :
    peHazardSatisfied earlier later := by
  have earlierCycleBound := earlier.cycle.isLt
  have laterCycleBound := later.cycle.isLt
  simp only [peHazardSatisfied]
  unfold TimedPEAccess.absoluteCycle at distance ⊢
  constructor
  · omega
  rw [grf_t_pe_hazard_requires_seven_cycles earlier later accessed.1 accessed.2
    sameBank grfT overlap]
  omega

theorem parsed_issue_advances_elapsed_word
    (control : ParsedMaskExecutionControl) (line : ParsedMaskedIssueLine) :
    (advanceParsedMaskControl control line).elapsedWords = control.elapsedWords + 1 := rfl

theorem parsed_issue_advances_absolute_cycle
    (control : ParsedMaskExecutionControl) (line : ParsedMaskedIssueLine)
    (cycle : Fin 4) :
    parsedAccessAbsoluteCycle (advanceParsedMaskControl control line) cycle =
      parsedAccessAbsoluteCycle control cycle + 4 := by
  simp [advanceParsedMaskControl, parsedAccessAbsoluteCycle]
  omega

theorem mask_directive_replaces_selection_preserves_context
    (next : ParsedMaskDirective) (current : ParsedMaskExecutionControl) :
    (updateParsedMaskDirective next current).directive = next ∧
      (updateParsedMaskDirective next current).context = current.context ∧
      (updateParsedMaskDirective next current).elapsedWords = current.elapsedWords := by
  constructor
  · rfl
  constructor <;> rfl

structure PreparedParsedMaskedWrite where
  destination : Option DirectMemoryAccess
  maskUpdate : Option (Fin 15 × Fin 4)
  data : WordBus
  selection : PEWordSelection

def prepareParsedMaskedWrite (files : IntegerRegisterFiles)
    (accesses : ParsedMaskedIntegerAccesses) (reduced : Bool) :
    ProofsLean.StepResult PreparedParsedMaskedWrite :=
  match ParsedIntegerInput.read files accesses.sourceX with
  | .failure => .failure
  | .unknown => .unknown
  | .ok x =>
    match ParsedIntegerInput.read files accesses.sourceY with
    | .failure => .failure
    | .unknown => .unknown
    | .ok y =>
      match evaluateParsedIntegerAlu accesses.op x y reduced with
      | .ok output =>
          let bus := parsedOutputAfterFlush accesses.flushSelection output.value
          .ok ⟨some accesses.destination, none, unpackALUBus bus, accesses.writeSelection⟩
      | .failure => .failure
      | .unknown => .unknown


def prepareParsedMaskedWriteWithForwarding (files : IntegerRegisterFiles)
    (slots : ProofsLean.MNCore.Forwarding.Slots) (cycle : Fin 4)
    (accesses : ParsedMaskedIntegerAccesses) (reduced : Bool) :
    ProofsLean.StepResult PreparedParsedMaskedWrite :=
  match ParsedIntegerInput.readWithForwarding files slots cycle accesses.sourceX with
  | .failure => .failure
  | .unknown => .unknown
  | .ok x =>
    match ParsedIntegerInput.readWithForwarding files slots cycle accesses.sourceY with
    | .failure => .failure
    | .unknown => .unknown
    | .ok y =>
      match evaluateParsedIntegerAlu accesses.op x y reduced with
      | .ok output =>
          let bus := parsedOutputAfterFlush accesses.flushSelection output.value
          .ok ⟨some accesses.destination, none, unpackALUBus bus, accesses.writeSelection⟩
      | .failure => .failure
      | .unknown => .unknown

def prepareParsedConstantTarget (files : IntegerRegisterFiles) (cycle : Fin 4)
    (target : ParsedConstantDestination) : ProofsLean.StepResult PreparedParsedMaskedWrite :=
  match target with
  | .memory accesses => prepareParsedMaskedWrite files accesses false
  | .maskRegister entry =>
      .ok ⟨none, some (entry, cycle), (fun _ => 0), ⟨BitVec.allOnes 4, true⟩⟩
  | .noWrite => .ok ⟨none, none, (fun _ => 0), ⟨BitVec.allOnes 4, true⟩⟩

def prepareParsedMaskedConstantWrites (files : IntegerRegisterFiles) (cycle : Fin 4)
    (targets : List ParsedConstantDestination) :
    ProofsLean.StepResult (List PreparedParsedMaskedWrite) :=
  match targets with
  | [] => .ok []
  | target :: rest =>
      match prepareParsedConstantTarget files cycle target with
      | .failure => .failure
      | .unknown => .unknown
      | .ok write =>
          match prepareParsedMaskedConstantWrites files cycle rest with
          | .ok writes => .ok (write :: writes)
          | .failure => .failure
          | .unknown => .unknown

theorem prepareParsedMaskedConstantWrites_preserves_order
    (files : IntegerRegisterFiles) (cycle : Fin 4)
    (target : ParsedConstantDestination) (rest : List ParsedConstantDestination)
    (write : PreparedParsedMaskedWrite) (writes : List PreparedParsedMaskedWrite)
    (headReady : prepareParsedConstantTarget files cycle target = .ok write)
    (tailReady : prepareParsedMaskedConstantWrites files cycle rest = .ok writes) :
    prepareParsedMaskedConstantWrites files cycle (target :: rest) = .ok (write :: writes) := by
  simp [prepareParsedMaskedConstantWrites, headReady, tailReady]

def prepareParsedMaskedLine (files : IntegerRegisterFiles)
    (expressions : List ParsedExpr) (control : ParsedMaskExecutionControl) :
    ProofsLean.StepResult (List PreparedParsedMaskedWrite) :=
  let hasSingleLineMask := expressions.any parsedExprHasSingleLineWriteMask
  let rec prepare : List ParsedExpr → ProofsLean.StepResult (List PreparedParsedMaskedWrite)
    | [] => .ok []
    | expression :: rest =>
        match expression.op with
        | .wait _ | .noforward => prepare rest
        | .zero | .immediate .. =>
          match ParsedExpr.toDirectMaskedConstantWrites? expression files.maskRegisters
              control.directive hasSingleLineMask control.context.group control.context.l2b
              control.context.l1b control.context.mab control.context.pe control.context.cycle
              control.context.bar0 control.context.bar1 control.context.tWord with
          | none => .unknown
          | some accesses =>
              match prepareParsedMaskedConstantWrites files control.context.cycle accesses with
              | .failure => .failure
              | .unknown => .unknown
              | .ok lineWrites =>
                  match prepare rest with
                  | .ok writes => .ok (lineWrites ++ writes)
                  | .failure => .failure
                  | .unknown => .unknown
        | _ =>
          match ParsedExpr.toDirectMaskedIntegerAccessesInLine? expression files.maskRegisters
              control.directive hasSingleLineMask control.context.group control.context.l2b
              control.context.l1b control.context.mab control.context.pe control.context.cycle
              control.context.bar0 control.context.bar1 control.context.tWord with
          | none => .unknown
          | some accesses =>
              match prepareParsedMaskedWrite files accesses false with
              | .failure => .failure
              | .unknown => .unknown
              | .ok write =>
                  match prepare rest with
                  | .ok writes => .ok (write :: writes)
                  | .failure => .failure
                  | .unknown => .unknown
  prepare expressions

def commitParsedMaskedWrites (files : IntegerRegisterFiles)
    (writes : List PreparedParsedMaskedWrite) : IntegerRegisterFiles :=
  writes.foldl (fun current write =>
    match write.maskUpdate with
    | some (entry, cycle) =>
        { current with maskRegisters :=
            (ProofsLean.MNCore.Masks.writeRegister current.maskRegisters entry cycle
              (0 : BitVec 4) (BitVec.allOnes 4)) }
    | none =>
        match write.destination with
        | some destination =>
            writeDirectAccessMasked current destination write.data write.selection
        | none => current) files

def parsedIntegerMaskedRegisterStepWithForwarding (files : IntegerRegisterFiles)
    (slots : ProofsLean.MNCore.Forwarding.Slots) (cycle : Fin 4)
    (accesses : ParsedMaskedIntegerAccesses) (reduced : Bool) :
    ProofsLean.StepResult IntegerRegisterFiles :=
  match prepareParsedMaskedWriteWithForwarding files slots cycle accesses reduced with
  | .ok write => .ok (commitParsedMaskedWrites files [write])
  | .failure => .failure
  | .unknown => .unknown

theorem parsedIntegerMaskedRegisterStepWithForwarding_success
    (files : IntegerRegisterFiles) (slots : ProofsLean.MNCore.Forwarding.Slots)
    (cycle : Fin 4) (accesses : ParsedMaskedIntegerAccesses) (reduced : Bool)
    (write : PreparedParsedMaskedWrite)
    (prepared : prepareParsedMaskedWriteWithForwarding files slots cycle accesses reduced = .ok write) :
    parsedIntegerMaskedRegisterStepWithForwarding files slots cycle accesses reduced =
      .ok (commitParsedMaskedWrites files [write]) := by
  simp [parsedIntegerMaskedRegisterStepWithForwarding, prepared]


theorem commitParsedMaskedWrites_single_memory (files : IntegerRegisterFiles)
    (destination : DirectMemoryAccess) (data : WordBus) (selection : PEWordSelection) :
    commitParsedMaskedWrites files
      [⟨some destination, none, data, selection⟩] =
    writeDirectAccessMasked files destination data selection := by
  cases destination with
  | mk bank width address =>
      cases bank <;>
        simp [commitParsedMaskedWrites, writeDirectAccessMasked,
          writeRegisterBankMasked]

theorem parsedIntegerMaskedRegisterStepWithForwarding_resolves_to_fixed
    (files : IntegerRegisterFiles) (slots : ProofsLean.MNCore.Forwarding.Slots)
    (cycle : Fin 4) (accesses : ParsedMaskedIntegerAccesses) (reduced : Bool)
    (sourceX sourceY : ParsedIntegerInput)
    (resolvedX : ParsedIntegerInput.resolveForwarding? slots cycle accesses.sourceX = some sourceX)
    (resolvedY : ParsedIntegerInput.resolveForwarding? slots cycle accesses.sourceY = some sourceY) :
    parsedIntegerMaskedRegisterStepWithForwarding files slots cycle accesses reduced =
      parsedIntegerMaskedRegisterStep files
        { accesses with sourceX := sourceX, sourceY := sourceY } reduced := by
  unfold parsedIntegerMaskedRegisterStepWithForwarding
  simp only [prepareParsedMaskedWriteWithForwarding,
    ParsedIntegerInput.readWithForwarding_resolved files slots cycle accesses.sourceX sourceX resolvedX,
    ParsedIntegerInput.readWithForwarding_resolved files slots cycle accesses.sourceY sourceY resolvedY]
  cases hx : ParsedIntegerInput.read files sourceX with
  | failure => simp [parsedIntegerMaskedRegisterStep, hx]
  | unknown => simp [parsedIntegerMaskedRegisterStep, hx]
  | ok x =>
    cases hy : ParsedIntegerInput.read files sourceY with
    | failure => simp [parsedIntegerMaskedRegisterStep, hx, hy]
    | unknown => simp [parsedIntegerMaskedRegisterStep, hx, hy]
    | ok y =>
      cases hv : evaluateParsedIntegerAlu accesses.op x y reduced <;>
        simp [parsedIntegerMaskedRegisterStep, hx, hy, hv,
          commitParsedMaskedWrites_single_memory]

theorem commit_constant_omr_destination_writes_zero
    (files : IntegerRegisterFiles) (entry : Fin 15) (cycle : Fin 4) :
    (commitParsedMaskedWrites files
      [⟨none, some (entry, cycle), (fun _ => 0), ⟨BitVec.allOnes 4, true⟩⟩]).maskRegisters
      entry cycle = 0 := by
  simp [commitParsedMaskedWrites, ProofsLean.MNCore.Masks.writeRegister]

def parsedIntegerMaskedLineStep (files : IntegerRegisterFiles)
    (expressions : List ParsedExpr) (control : ParsedMaskExecutionControl) :
    ProofsLean.StepResult IntegerRegisterFiles :=
  match prepareParsedMaskedLine files expressions control with
  | .ok writes => .ok (commitParsedMaskedWrites files writes)
  | .failure => .failure
  | .unknown => .unknown

theorem parsedIntegerMaskedLineStep_prepares_then_commits
    (files : IntegerRegisterFiles) (expressions : List ParsedExpr)
    (control : ParsedMaskExecutionControl) :
    parsedIntegerMaskedLineStep files expressions control =
      match prepareParsedMaskedLine files expressions control with
      | .ok writes => .ok (commitParsedMaskedWrites files writes)
      | .failure => .failure
      | .unknown => .unknown := rfl


def parsedMaskedExpressionStep (control : ParsedMaskExecutionControl)
    (line : ParsedMaskedIssueLine) (files : IntegerRegisterFiles) :
    Option IntegerRegisterFiles :=
  match line with
  | .pe expressions =>
      match parsedIntegerMaskedLineStep files expressions control with
      | .ok next => some next
      | .failure | .unknown => none
  | .nop => some files

def parsedLineHasNoForward (expressions : List ParsedExpr) : Bool :=
  expressions.any fun expression => match expression.op with
    | .noforward => true
    | _ => false

def advanceParsedLineForwarding (old : ProofsLean.MNCore.Forwarding.Slots)
    (expressions : List ParsedExpr)
    (outputs : ProofsLean.MNCore.Forwarding.Unit →
      Option (Fin 4 → ProofsLean.MNCore.Forwarding.Value IntegerALU.Bus)) :
    ProofsLean.StepResult ProofsLean.MNCore.Forwarding.Slots :=
  ProofsLean.MNCore.Forwarding.advance old
    (.issue (parsedLineHasNoForward expressions) outputs)

theorem parsed_noforward_suppresses_forwarding_updates
    (old : ProofsLean.MNCore.Forwarding.Slots) (expressions : List ParsedExpr)
    (outputs : ProofsLean.MNCore.Forwarding.Unit →
      Option (Fin 4 → ProofsLean.MNCore.Forwarding.Value IntegerALU.Bus))
    (hasNoForward : parsedLineHasNoForward expressions = true) :
    advanceParsedLineForwarding old expressions outputs = .ok old := by
  simp [advanceParsedLineForwarding, hasNoForward,
    ProofsLean.MNCore.Forwarding.advance]

def ParsedLine.toParsedMaskedStatements? :
    ParsedLine → Option (List ParsedMaskedSourceStatement)
  | .maskDirective widthWords targets entry =>
      some [.directive ⟨widthWords, targets, entry⟩]
  | .pe expressions => some [.issue (.pe expressions)]
  | .nop count _ => some (List.replicate count (.issue .nop))
  | _ => none

def lowerParsedMaskedSource (lines : List ParsedLine) :
    Option (List ParsedMaskedSourceStatement) := do
  let lowered ← lines.mapM ParsedLine.toParsedMaskedStatements?
  pure lowered.flatten

def ParsedLine.parsedMaskedIssueWords? : ParsedLine → Option Nat
  | .pe _ => some 1
  | .nop count _ => some count
  | .maskDirective _ _ _ => some 0
  | _ => none



def runParsedMaskedSource (source : List ParsedMaskedSourceStatement)
    (control : ParsedMaskExecutionControl) (files : IntegerRegisterFiles) :
    Option IntegerRegisterFiles :=
  ProofsLean.ControlNormalization.runSourceAdvancing updateParsedMaskDirective
    advanceParsedMaskControl parsedMaskedExpressionStep source control files

def parsedMaskedIssueLineLegal : ParsedMaskedIssueLine → Prop
  | .pe expressions => LegalParsedLine expressions
  | .nop => True

def parsedMaskedIssueLegal : List (ParsedMaskExecutionControl × ParsedMaskedIssueLine) → Prop :=
  fun lines => ∀ line ∈ lines, parsedMaskedIssueLineLegal line.2

def parsedMaskedNormalizedMachine : ProofsLean.Machine where
  Line := ParsedMaskExecutionControl × ParsedMaskedIssueLine
  State := IntegerRegisterFiles
  Input := Unit
  step := fun pair files => parsedMaskedExpressionStep pair.1 pair.2 files
  legal := parsedMaskedIssueLegal
  lineCost := fun _ => 1
  positiveCost := fun _ => by decide

def runParsedMaskedCompiled (source : List ParsedMaskedSourceStatement)
    (control : ParsedMaskExecutionControl) (files : IntegerRegisterFiles) :
    Option IntegerRegisterFiles :=
  let compiled := ProofsLean.ControlNormalization.compileAdvancing
    updateParsedMaskDirective advanceParsedMaskControl source control
  ProofsLean.execute parsedMaskedNormalizedMachine compiled files

theorem parsedMaskedSource_execution (source : List ParsedMaskedSourceStatement)
    (control : ParsedMaskExecutionControl) (files : IntegerRegisterFiles) :
    runParsedMaskedSource source control files =
      runParsedMaskedCompiled source control files := by
  exact ProofsLean.ControlNormalization.source_execution_advancing
    updateParsedMaskDirective advanceParsedMaskControl parsedMaskedExpressionStep
    parsedMaskedIssueLegal Unit source control files

theorem mask_directive_has_zero_issue_cost (directive : ParsedMaskDirective) :
    ProofsLean.ControlNormalization.cost
      ([.directive directive] : List ParsedMaskedSourceStatement) = 0 := rfl

theorem parsed_wait_expression_preserves_register_state
    (files : IntegerRegisterFiles) (control : ParsedMaskExecutionControl) (tag : Nat) :
    parsedIntegerMaskedLineStep files
      [{ op := .wait tag, sources := [], destinations := [], flush := none, text := "wait" }]
      control = .ok files := by
  simp [parsedIntegerMaskedLineStep, prepareParsedMaskedLine,
    prepareParsedMaskedLine.prepare,
    commitParsedMaskedWrites]

theorem parsed_nop_preserves_register_state
    (control : ParsedMaskExecutionControl) (files : IntegerRegisterFiles) :
    parsedMaskedExpressionStep control .nop files = some files := rfl

theorem parsed_nop_count_has_matching_issue_cost (count : Nat) :
    ProofsLean.ControlNormalization.cost
      (List.replicate count (.issue ParsedMaskedIssueLine.nop) :
        List ParsedMaskedSourceStatement) = count := by
  induction count with
  | zero => rfl
  | succ count ih => simp [List.replicate_succ, ProofsLean.ControlNormalization.cost, ih]; omega

theorem parsed_line_lowering_preserves_issue_words (line : ParsedLine)
    (statements : List ParsedMaskedSourceStatement)
    (lowered : ParsedLine.toParsedMaskedStatements? line = some statements) :
    ∃ words, ParsedLine.parsedMaskedIssueWords? line = some words ∧
      ProofsLean.ControlNormalization.cost statements = words := by
  cases line with
  | pe expressions =>
      simp [ParsedLine.toParsedMaskedStatements?] at lowered
      subst statements
      exact ⟨1, rfl, rfl⟩
  | nop count wait =>
      simp [ParsedLine.toParsedMaskedStatements?] at lowered
      subst statements
      exact ⟨count, rfl, parsed_nop_count_has_matching_issue_cost count⟩
  | maskDirective width targets entry =>
      simp [ParsedLine.toParsedMaskedStatements?] at lowered
      subst statements
      exact ⟨0, rfl, rfl⟩
  | mv => simp [ParsedLine.toParsedMaskedStatements?] at lowered
  | debugSet => simp [ParsedLine.toParsedMaskedStatements?] at lowered
  | debugGet => simp [ParsedLine.toParsedMaskedStatements?] at lowered
  | dramSet => simp [ParsedLine.toParsedMaskedStatements?] at lowered
theorem parsed_nop_line_lowers_to_count_issue_words (count : Nat) (wait : Option Nat) :
    lowerParsedMaskedSource [.nop count wait] =
      some (List.replicate count (.issue ParsedMaskedIssueLine.nop)) := by
  simp [lowerParsedMaskedSource, ParsedLine.toParsedMaskedStatements?]

theorem parsedMaskedSource_score (source : List ParsedMaskedSourceStatement)
    (control : ParsedMaskExecutionControl) :
    ProofsLean.score parsedMaskedNormalizedMachine
      (ProofsLean.ControlNormalization.compileAdvancing updateParsedMaskDirective
        advanceParsedMaskControl source control) =
      ProofsLean.ControlNormalization.cost source :=
  ProofsLean.ControlNormalization.source_score_advancing updateParsedMaskDirective
    advanceParsedMaskControl parsedMaskedExpressionStep parsedMaskedIssueLegal Unit
    source control

theorem lowered_parsed_masked_source_executes_as_normalized
    (lines : List ParsedLine) (source : List ParsedMaskedSourceStatement)
    (lowered : lowerParsedMaskedSource lines = some source)
    (control : ParsedMaskExecutionControl) (files : IntegerRegisterFiles) :
    (lowerParsedMaskedSource lines).map
      (fun loweredSource => runParsedMaskedSource loweredSource control files) =
      some (ProofsLean.execute parsedMaskedNormalizedMachine
        (ProofsLean.ControlNormalization.compileAdvancing updateParsedMaskDirective
          advanceParsedMaskControl source control)
        files) := by
  rw [lowered]
  simp only [Option.map_some]
  rw [parsedMaskedSource_execution]
  constructor <;> rfl

def parsedIntegerRegisterStep (files : IntegerRegisterFiles)
    (sourceX sourceY destination : DirectMemoryAccess) (op : ParsedOp)
    (reduced : Bool) : ProofsLean.StepResult IntegerRegisterFiles :=
  let x := pack (readDirectAccess files sourceX)
  let y := pack (readDirectAccess files sourceY)
  match evaluateParsedIntegerAlu op x y reduced with
  | .ok output => .ok (writeDirectAccess files destination (unpackALUBus output.value))
  | .failure => .failure
  | .unknown => .unknown

def executeParsedIntegerExpr? (files : IntegerRegisterFiles)
    (expression : ParsedExpr) (pe cycle : Fin 4) (bar0 bar1 : BitVec 12)
    (tWord : BitVec 32) : Option (ProofsLean.StepResult IntegerRegisterFiles) :=
  match ParsedExpr.toDirectIntegerAccesses? expression pe cycle bar0 bar1 tWord with
  | some accesses => some (parsedIntegerRegisterStep files accesses.sourceX
      accesses.sourceY accesses.destination accesses.op false)
  | none => none

def parsedIntegerRegisterOutput (files : IntegerRegisterFiles)
    (sourceX sourceY : DirectMemoryAccess) (precision : IntegerALU.Precision)
    (aluOp : IntegerALU.Op) (reduced : Bool) : IntegerALU.BusResult :=
  IntegerALU.evaluateBus precision aluOp
    (pack (readDirectAccess files sourceX))
    (pack (readDirectAccess files sourceY)) reduced

def integerFlagsVector (output : IntegerALU.BusResult) : BitVec 4 :=
  BitVec.ofBoolListLE [output.flags 0, output.flags 1, output.flags 2, output.flags 3]

theorem integerFlagsVector_bit0 (output : IntegerALU.BusResult) :
    (integerFlagsVector output).getLsbD 0 = output.flags 0 := by
  change (BitVec.ofBoolListLE
    [output.flags 0, output.flags 1, output.flags 2, output.flags 3]).getLsbD 0 = _
  rw [BitVec.getLsbD_ofBoolListLE]
  simp

theorem integerFlagsVector_bit1 (output : IntegerALU.BusResult) :
    (integerFlagsVector output).getLsbD 1 = output.flags 1 := by
  change (BitVec.ofBoolListLE
    [output.flags 0, output.flags 1, output.flags 2, output.flags 3]).getLsbD 1 = _
  rw [BitVec.getLsbD_ofBoolListLE]
  simp

theorem integerFlagsVector_bit2 (output : IntegerALU.BusResult) :
    (integerFlagsVector output).getLsbD 2 = output.flags 2 := by
  change (BitVec.ofBoolListLE
    [output.flags 0, output.flags 1, output.flags 2, output.flags 3]).getLsbD 2 = _
  rw [BitVec.getLsbD_ofBoolListLE]
  simp

theorem integerFlagsVector_bit3 (output : IntegerALU.BusResult) :
    (integerFlagsVector output).getLsbD 3 = output.flags 3 := by
  change (BitVec.ofBoolListLE
    [output.flags 0, output.flags 1, output.flags 2, output.flags 3]).getLsbD 3 = _
  rw [BitVec.getLsbD_ofBoolListLE]
  simp

def parsedIntegerMaskRegisterStep (files : IntegerRegisterFiles)
    (sourceX sourceY : DirectMemoryAccess) (entry : Fin 15) (cycle : Fin 4)
    (selection : BitVec 4) (op : ParsedOp) (reduced : Bool) :
    ProofsLean.StepResult IntegerRegisterFiles :=
  match evaluateParsedIntegerAlu op
      (pack (readDirectAccess files sourceX))
      (pack (readDirectAccess files sourceY)) reduced with
  | .ok output => .ok { files with maskRegisters :=
      (ProofsLean.MNCore.Masks.writeRegister files.maskRegisters entry cycle
        (integerFlagsVector output) selection) }
  | .failure => .failure
  | .unknown => .unknown

def parsedIntegerMaskExprAccesses? (expression : ParsedExpr)
    (registers : ProofsLean.MNCore.Masks.RegisterFile)
    (directive : ParsedMaskDirective)
    (pe cycle : Fin 4) (bar0 bar1 : BitVec 12) (tWord : BitVec 32) :
    Option ParsedIntegerMaskAccesses :=
  match expression.op with
  | .alu name (some _) _ _ =>
      match hRequest : expression.op.integerRequest with
      | .ok (.integer precision aluOp) =>
          match expression.sources, expression.destinations with
          | [source], [destination] =>
              if ParsedAluName.integerInputCount name != 1 then none else
              match ParsedOperand.toDirectMemoryAccess? source pe cycle bar0 bar1 tWord,
                    ParsedOperand.toMaskRegisterEntry? destination,
                    ParsedOperand.resolveOmrWriteSelection? destination registers cycle directive
                      (parsedExprHasSingleLineWriteMask expression) with
              | some sourceAccess, some entry, some selection =>
                  some ⟨expression.op, sourceAccess, sourceAccess, entry,
                    selection, ⟨precision, aluOp, hRequest⟩⟩
              | _, _, _ => none
          | [sourceX, sourceY], [destination] =>
              if ParsedAluName.integerInputCount name != 2 then none else
              match ParsedOperand.toDirectMemoryAccess? sourceX pe cycle bar0 bar1 tWord,
                    ParsedOperand.toDirectMemoryAccess? sourceY pe cycle bar0 bar1 tWord,
                    ParsedOperand.toMaskRegisterEntry? destination,
                    ParsedOperand.resolveOmrWriteSelection? destination registers cycle directive
                      (parsedExprHasSingleLineWriteMask expression) with
              | some xAccess, some yAccess, some entry, some selection =>
                  some ⟨expression.op, xAccess, yAccess, entry,
                    selection, ⟨precision, aluOp, hRequest⟩⟩
              | _, _, _, _ => none
          | _, _ => none
      | _ => none
  | _ => none

example : (parsedIntegerMaskExprAccesses?
    ({ op := .alu .inc (some .i) false none,
       sources := [.mem ⟨.lm0, ⟨2, 0, 0, 0, 0, false, none⟩⟩ false false false none],
       destinations := [.omr 1 none], flush := none, text := "iinc $lm0v $omr1" } : ParsedExpr)
    (fun _ _ => 0) {}
    0 0 0 0 0).map ParsedIntegerMaskAccesses.locations =
      some (⟨.lm0, .long, ⟨0, by decide⟩⟩,
        ⟨.lm0, .long, ⟨0, by decide⟩⟩, 0) := by decide

example : (parsedIntegerMaskExprAccesses?
    ({ op := .alu .inc (some .i) false none,
       sources := [.mem ⟨.lm0, ⟨2, 0, 0, 0, 0, false, none⟩⟩ false false false none],
       destinations := [.omr 1 none], flush := none, text := "iinc $lm0v $omr1" } : ParsedExpr)
    (fun _ _ => 0) {} 0 0 0 0 0).map ParsedIntegerMaskAccesses.selection =
      some (BitVec.allOnes 4) := by decide

def executeParsedIntegerMaskExpr? (files : IntegerRegisterFiles)
    (expression : ParsedExpr) (pe cycle : Fin 4) (bar0 bar1 : BitVec 12)
    (tWord : BitVec 32) (directive : ParsedMaskDirective) :
    Option (ProofsLean.StepResult IntegerRegisterFiles) :=
  match parsedIntegerMaskExprAccesses? expression files.maskRegisters directive
      pe cycle bar0 bar1 tWord with
  | some accesses => some (parsedIntegerMaskRegisterStep files accesses.sourceX
      accesses.sourceY accesses.destination cycle accesses.selection accesses.op false)
  | none => none

theorem mask_read_after_selected_write (registers : ProofsLean.MNCore.Masks.RegisterFile)
    (entry : Fin 15) (cycle : Fin 4) (flags selection : BitVec 4) :
    ProofsLean.MNCore.Masks.readEntry
      (ProofsLean.MNCore.Masks.writeRegister registers entry cycle flags selection)
      ⟨entry.val + 1, by have := entry.isLt; omega⟩ cycle = flags &&& selection := by
  simp [ProofsLean.MNCore.Masks.readEntry, ProofsLean.MNCore.Masks.writeRegister,
    show entry.val + 1 < 16 by have := entry.isLt; omega]

theorem mask_read_after_writeRegister (registers : ProofsLean.MNCore.Masks.RegisterFile)
    (entry : Fin 15) (cycle : Fin 4) (flags : BitVec 4) :
    ProofsLean.MNCore.Masks.readEntry
      (ProofsLean.MNCore.Masks.writeRegister registers entry cycle flags (BitVec.allOnes 4))
      ⟨entry.val + 1, by have := entry.isLt; omega⟩ cycle = flags := by
  simp [ProofsLean.MNCore.Masks.readEntry, ProofsLean.MNCore.Masks.writeRegister,
    show entry.val + 1 < 16 by have := entry.isLt; omega]
  change flags &&& BitVec.allOnes 4 = flags
  exact BitVec.and_allOnes

theorem parsedIntegerMaskStep_readback (files : IntegerRegisterFiles)
    (sourceX sourceY : DirectMemoryAccess) (entry : Fin 15) (cycle : Fin 4)
    (selection : BitVec 4) (op : ParsedOp)
    (precision : IntegerALU.Precision) (aluOp : IntegerALU.Op)
    (selected : op.integerRequest = .ok (.integer precision aluOp))
    (reduced : Bool) :
    ∃ nextFiles,
      parsedIntegerMaskRegisterStep files sourceX sourceY entry cycle selection op reduced =
        .ok nextFiles ∧
      ProofsLean.MNCore.Masks.readEntry nextFiles.maskRegisters
        ⟨entry.val + 1, by have := entry.isLt; omega⟩ cycle =
        integerFlagsVector (parsedIntegerRegisterOutput files sourceX sourceY
          precision aluOp reduced) &&& selection := by
  let output := parsedIntegerRegisterOutput files sourceX sourceY precision aluOp reduced
  refine ⟨{ files with maskRegisters :=
      (ProofsLean.MNCore.Masks.writeRegister files.maskRegisters entry cycle
        (integerFlagsVector output) selection) }, ?_, ?_⟩
  · have selectedExec := integer_request_is_execution_request op precision aluOp selected
    simp [parsedIntegerMaskRegisterStep, evaluateParsedIntegerAlu, selectedExec,
      output, evaluateParsedExecutionRequest, parsedIntegerRegisterOutput]
  · exact mask_read_after_selected_write files.maskRegisters entry cycle
      (integerFlagsVector output) selection

theorem parsed_iinc_output_eq_incrementPair (files : IntegerRegisterFiles)
    (address : Fin Bank.lm0.capacity) :
    (parsedIntegerRegisterOutput files ⟨.lm0, .long, address⟩
      ⟨.lm0, .long, address⟩ .word (.arith .inc false) false).value.high =
      ProofsLean.MNCore.PlusOne.incrementPair
        (files.lm0 address) (files.lm0 (advance .lm0 address 1)) := by
  have hzero : advance .lm0 address 0 = address := by
    apply Fin.ext
    simp [advance, Nat.mod_eq_of_lt address.isLt]
  have hread0 : readWords .lm0 .long files.lm0 address 0 = files.lm0 address := by
    simp [readWords, count, Width.words, advance, Nat.mod_eq_of_lt address.isLt]
  have hread1 : readWords .lm0 .long files.lm0 address 1 =
      files.lm0 (advance .lm0 address 1) := by
    simp [readWords, count, Width.words]
  simp [parsedIntegerRegisterOutput, readDirectAccess, readRegisterBank,
    ProofsLean.MNCore.PlusOne.incrementPair, pack, hread0, hread1,
    IntegerALU.evaluateBus, IntegerALU.lane, IntegerALU.Precision.lanes,
    IntegerALU.Precision.width, IntegerALU.evaluateLane, IntegerALU.arithmetic,
    List.range, List.range.loop]

theorem direct_access_write_readback (files : IntegerRegisterFiles)
    (destination : DirectMemoryAccess) (data : WordBus) (index : Fin 4)
    (within : index.val < count destination.bank destination.width) :
    readDirectAccess (writeDirectAccess files destination data) destination index = data index := by
  cases destination with
  | mk bank width address =>
    exact readRegisterBank_after_write files bank width address data index within


theorem parsedIntegerRegisterStep_succeeds (files : IntegerRegisterFiles)
    (sourceX sourceY destination : DirectMemoryAccess) (op : ParsedOp)
    (reduced : Bool) (precision : IntegerALU.Precision) (aluOp : IntegerALU.Op)
    (selected : op.integerRequest = .ok (.integer precision aluOp)) :
    parsedIntegerRegisterStep files sourceX sourceY destination op reduced =
      .ok (writeDirectAccess files destination
        (unpackALUBus (parsedIntegerRegisterOutput files sourceX sourceY
          precision aluOp reduced).value)) := by
  have selectedExec : op.executionRequest = .ok (.integer precision aluOp) := by
    exact integer_request_is_execution_request op precision aluOp selected
  simp [parsedIntegerRegisterStep, evaluateParsedIntegerAlu, selectedExec,
    parsedIntegerRegisterOutput, evaluateParsedExecutionRequest]

theorem parsedIntegerRegisterStep_readback (files : IntegerRegisterFiles)
    (sourceX sourceY destination : DirectMemoryAccess) (op : ParsedOp)
    (reduced : Bool) (precision : IntegerALU.Precision) (aluOp : IntegerALU.Op)
    (selected : op.integerRequest = .ok (.integer precision aluOp))
    (index : Fin 4) (within : index.val < count destination.bank destination.width) :
    ∃ nextFiles,
      parsedIntegerRegisterStep files sourceX sourceY destination op reduced = .ok nextFiles ∧
      readDirectAccess nextFiles destination index =
        unpackALUBus (parsedIntegerRegisterOutput files sourceX sourceY
          precision aluOp reduced).value index := by
  refine ⟨writeDirectAccess files destination
    (unpackALUBus (parsedIntegerRegisterOutput files sourceX sourceY
      precision aluOp reduced).value),
    parsedIntegerRegisterStep_succeeds files sourceX sourceY destination op reduced
      precision aluOp selected, ?_⟩
  exact direct_access_write_readback files destination
    (unpackALUBus (parsedIntegerRegisterOutput files sourceX sourceY
      precision aluOp reduced).value) index within

theorem executeParsedIntegerExpr_readback (files : IntegerRegisterFiles)
    (expression : ParsedExpr) (pe cycle : Fin 4) (bar0 bar1 : BitVec 12)
    (tWord : BitVec 32) (accesses : ParsedIntegerAccesses)
    (lowered : ParsedExpr.toDirectIntegerAccesses? expression pe cycle bar0 bar1 tWord =
      some accesses)
    (index : Fin 4)
    (within : index.val < count accesses.destination.bank accesses.destination.width) :
    ∃ precision aluOp nextFiles,
      accesses.op.integerRequest = .ok (.integer precision aluOp) ∧
      executeParsedIntegerExpr? files expression pe cycle bar0 bar1 tWord =
        some (.ok nextFiles) ∧
      readDirectAccess nextFiles accesses.destination index =
        unpackALUBus (parsedIntegerRegisterOutput files accesses.sourceX
          accesses.sourceY precision aluOp false).value index := by
  rcases accesses.hasIntegerRequest with ⟨precision, aluOp, selected⟩
  refine ⟨precision, aluOp,
    writeDirectAccess files accesses.destination
      (unpackALUBus (parsedIntegerRegisterOutput files accesses.sourceX
        accesses.sourceY precision aluOp false).value), selected, ?_, ?_⟩
  · simp only [executeParsedIntegerExpr?, lowered, Option.some.injEq]
    exact parsedIntegerRegisterStep_succeeds files accesses.sourceX accesses.sourceY
      accesses.destination accesses.op false precision aluOp selected
  · exact direct_access_write_readback files accesses.destination
      (unpackALUBus (parsedIntegerRegisterOutput files accesses.sourceX
        accesses.sourceY precision aluOp false).value) index within

theorem executeParsedIntegerMaskExpr_readback (files : IntegerRegisterFiles)
    (expression : ParsedExpr) (pe cycle : Fin 4) (bar0 bar1 : BitVec 12)
    (tWord : BitVec 32) (directive : ParsedMaskDirective)
    (accesses : ParsedIntegerMaskAccesses)
    (lowered : parsedIntegerMaskExprAccesses? expression files.maskRegisters directive
      pe cycle bar0 bar1 tWord =
      some accesses) :
    ∃ precision aluOp nextFiles,
      accesses.op.integerRequest = .ok (.integer precision aluOp) ∧
      executeParsedIntegerMaskExpr? files expression pe cycle bar0 bar1 tWord directive =
        some (.ok nextFiles) ∧
      ProofsLean.MNCore.Masks.readEntry nextFiles.maskRegisters
        ⟨accesses.destination.val + 1, by have := accesses.destination.isLt; omega⟩ cycle =
        integerFlagsVector (parsedIntegerRegisterOutput files accesses.sourceX
          accesses.sourceY precision aluOp false) &&& accesses.selection := by
  rcases accesses.hasIntegerRequest with ⟨precision, aluOp, selected⟩
  let output := parsedIntegerRegisterOutput files accesses.sourceX accesses.sourceY
    precision aluOp false
  refine ⟨precision, aluOp,
    { files with maskRegisters :=
      (ProofsLean.MNCore.Masks.writeRegister files.maskRegisters accesses.destination cycle
        (integerFlagsVector output) accesses.selection) }, selected, ?_, ?_⟩
  · have selectedExec : accesses.op.executionRequest = .ok (.integer precision aluOp) := by
      exact integer_request_is_execution_request accesses.op precision aluOp selected
    simp [executeParsedIntegerMaskExpr?, lowered, parsedIntegerMaskRegisterStep,
      evaluateParsedIntegerAlu, selectedExec, output, evaluateParsedExecutionRequest]
    constructor <;> rfl
  · exact mask_read_after_selected_write files.maskRegisters accesses.destination cycle
      (integerFlagsVector output) accesses.selection


end ProofsLean.MNCore.PEMemory
