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

/-- Coordinates shared by the four PEs in one MAB, with per-PE BAR/T state. -/
structure ParsedPEGroupContext where
  group : Fin 2
  l2b : Fin 2
  l1b : Fin 8
  mab : Fin 16
  bar0 : Fin 4 → BitVec 12
  bar1 : Fin 4 → BitVec 12
  tWord : Fin 4 → BitVec 32

def ParsedPEGroupContext.at (groupContext : ParsedPEGroupContext)
    (pe cycle : Fin 4) : ParsedIntegerContext where
  pe := pe
  cycle := cycle
  bar0 := groupContext.bar0 pe
  bar1 := groupContext.bar1 pe
  tWord := groupContext.tWord pe
  group := groupContext.group
  l2b := groupContext.l2b
  l1b := groupContext.l1b
  mab := groupContext.mab

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

def trimMaskSelectorModifiers (text : String) : List Char :=
  (text.toList.reverse.dropWhile fun c => c == 't' || c == 'p').reverse

def parseMaskSelectorDigits : List Char → Nat → Option Nat
  | [], value => some value
  | digit :: rest, value =>
      if 48 ≤ digit.toNat && digit.toNat ≤ 57 then
        parseMaskSelectorDigits rest (value * 10 + digit.toNat - 48)
      else none

def parseMaskSelector? (text : String) : Option ParsedMask := do
  let chars := trimMaskSelectorModifiers text
  let (longLong, body) :=
    if chars.take 6 == "$llimr".toList then (true, "$imr".toList ++ chars.drop 6)
    else if chars.take 2 == "ll".toList then (true, chars.drop 2)
    else (false, chars)
  if body.take 4 == "$imr".toList then
    let rawDigits := body.drop 4
    let digits := if rawDigits.head? == some '+' then rawDigits.drop 1 else rawDigits
    if digits.isEmpty then none else
    let index ← parseMaskSelectorDigits digits 0
    if index < 256 then some (.entry longLong index) else none
  else
    match body with
    | [b3, b2, b1, b0] =>
        if [b3, b2, b1, b0].all (fun bit => bit == '0' || bit == '1') then
          let value := (if b3 == '1' then 8 else 0) +
            (if b2 == '1' then 4 else 0) +
            (if b1 == '1' then 2 else 0) + (if b0 == '1' then 1 else 0)
          some (.pattern longLong (BitVec.ofNat 4 value))
        else none
    | _ => none

theorem parseMaskSelector_pattern :
    parseMaskSelector? "1010" = some (.pattern false 10) := by
  rfl

theorem parseMaskSelector_ll_imr :
    parseMaskSelector? "ll$imr7tp" = some (.entry true 7) := by
  rfl

theorem parseMaskSelector_positive_imr :
    parseMaskSelector? "$imr+7" = some (.entry false 7) := by
  rfl

theorem parseMaskSelector_llimr :
    parseMaskSelector? "$llimr15p" = some (.entry true 15) := by
  rfl

theorem parseMaskSelector_rejects_u8_overflow :
    parseMaskSelector? "$imr256" = none := by
  rfl

theorem parseMaskSelector_rejects_bad_pattern :
    parseMaskSelector? "10x0" = none := by
  rfl

def maskDirectiveDigit? (base : Nat) (digit : Char) : Option Nat :=
  let code := digit.toNat
  if 48 ≤ code && code ≤ 57 then
    let value := code - 48
    if value < base then some value else none
  else if base == 16 && 65 ≤ code && code ≤ 70 then some (code - 55)
  else if base == 16 && 97 ≤ code && code ≤ 102 then some (code - 87)
  else none

def parseMaskDirectiveDigits (base : Nat) : List Char → Nat → Option Nat
  | [], value => some value
  | digit :: rest, value => do
      let digitValue ← maskDirectiveDigit? base digit
      parseMaskDirectiveDigits base rest (value * base + digitValue)

def parseMaskDirectiveNumber? (text : String) : Option Nat := do
  let chars := text.toList
  let (base, rawDigits) :=
    if chars.take 2 == "0x".toList then (16, chars.drop 2)
    else if chars.take 2 == "0b".toList then (2, chars.drop 2)
    else (10, chars)
  let digits := if rawDigits.head? == some '+' then rawDigits.drop 1 else rawDigits
  if digits.isEmpty then none else
  let value ← parseMaskDirectiveDigits base digits 0
  if value < 2 ^ 64 then some value else none

def parseMaskDirectiveTargets : List Char → ParsedMaskTargets → Option ParsedMaskTargets
  | [], targets => some targets
  | target :: rest, targets =>
      match target with
      | 'r' => parseMaskDirectiveTargets rest { targets with grf0 := true }
      | 's' => parseMaskDirectiveTargets rest { targets with grf1 := true }
      | 't' => parseMaskDirectiveTargets rest { targets with t := true }
      | 'm' => parseMaskDirectiveTargets rest { targets with lm0 := true }
      | 'n' => parseMaskDirectiveTargets rest { targets with lm1 := true }
      | 'k' => parseMaskDirectiveTargets rest { targets with maskRegister := true }
      | _ => none

def parseMaskDirectiveOperator? (operator : String) :
    Option (Nat × ParsedMaskTargets) := do
  let chars := operator.toList
  if chars.take 4 != "mask".toList then none else
  let suffix := chars.drop 4
  let (widthWords, targets) :=
    if suffix.take 2 == "ll".toList then (4, suffix.drop 2)
    else if suffix.head? == some 'l' then (2, suffix.drop 1)
    else (2, suffix)
  let targets ← parseMaskDirectiveTargets targets {}
  some (widthWords, targets)

def splitMaskDirectiveWhitespace : List Char → List Char → List String → List String
  | [], current, tokens =>
      if current.isEmpty then tokens.reverse
      else (String.ofList current.reverse :: tokens).reverse
  | char :: rest, current, tokens =>
      if char.isWhitespace then
        if current.isEmpty then splitMaskDirectiveWhitespace rest [] tokens
        else splitMaskDirectiveWhitespace rest [] (String.ofList current.reverse :: tokens)
      else splitMaskDirectiveWhitespace rest (char :: current) tokens

def parseMaskDirective? (text : String) : Option ParsedLine := do
  let tokens := splitMaskDirectiveWhitespace text.toList [] []
  let [operator, address] := tokens | none
  let (widthWords, targets) ← parseMaskDirectiveOperator? operator
  let entry ← parseMaskDirectiveNumber? address
  some (.maskDirective widthWords targets (entry % 256))

theorem parseMaskDirective_targets_and_u8_cast :
    parseMaskDirective? "maskllrstmnk 0x123" = some
      (.maskDirective 4 (⟨true, true, true, true, true, true⟩ : ParsedMaskTargets) 35) := by
  rfl

theorem parseMaskDirective_binary_entry_cast :
    parseMaskDirective? "maskl 0b111111111" =
      some (.maskDirective 2 {} 255) := by
  rfl

theorem parseMaskDirective_decimal_plus :
    parseMaskDirective? "maskk +257" =
      some (.maskDirective 2 { maskRegister := true } 1) := by
  rfl

theorem parseMaskDirective_u64_max_casts_to_u8 :
    parseMaskDirective? "mask 18446744073709551615" =
      some (.maskDirective 2 {} 255) := by
  rfl

theorem parseMaskDirective_rejects_u64_overflow :
    parseMaskDirective? "mask 18446744073709551616" = none := by
  rfl

theorem parseMaskDirective_rejects_bad_target :
    parseMaskDirective? "maskx 1" = none := by
  rfl

theorem parseMaskDirective_rejects_extra_token :
    parseMaskDirective? "mask 1 trailing" = none := by
  rfl

theorem parsed_mask_directive_updates_runtime_state (state : ParsedMaskDirective) :
    (parseMaskDirective? "maskllm 258").map
      (fun line => ParsedLine.updateMaskState line state) =
        some ⟨4, ⟨false, false, false, true, false, false⟩, 2⟩ := by
  rfl

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
      if index == 0 then some (BitVec.allOnes 4)
      else if h : index < 16 then
        some (registers ⟨index - 1, by omega⟩ cycle)
      else if h : index < 256 then
        some (if (index / 2 ^ (3 - cycle.val)) % 2 == 1
          then BitVec.allOnes 4 else 0)
      else none

theorem mask_entry_zero_selects_all_cycles
    (registers : ProofsLean.MNCore.Masks.RegisterFile) (cycle : Fin 4) :
    resolveParsedMaskFlags? (.entry false 0) registers cycle =
      some (BitVec.allOnes 4) := by
  simp [resolveParsedMaskFlags?]

theorem mask_entry_32_is_pattern_not_entry_zero
    (registers : ProofsLean.MNCore.Masks.RegisterFile) (cycle : Fin 4) :
    resolveParsedMaskFlags? (.entry false 32) registers cycle = some 0 := by
  have hs : 3 - cycle.val = 0 ∨ 3 - cycle.val = 1 ∨
      3 - cycle.val = 2 ∨ 3 - cycle.val = 3 := by omega
  rcases hs with h | h | h | h <;> simp [resolveParsedMaskFlags?, h]

theorem mask_entry_255_selects_all_cycles
    (registers : ProofsLean.MNCore.Masks.RegisterFile) (cycle : Fin 4) :
    resolveParsedMaskFlags? (.entry false 255) registers cycle =
      some (BitVec.allOnes 4) := by
  have hs : 3 - cycle.val = 0 ∨ 3 - cycle.val = 1 ∨
      3 - cycle.val = 2 ∨ 3 - cycle.val = 3 := by omega
  rcases hs with h | h | h | h <;> simp [resolveParsedMaskFlags?, h]

theorem parsed_mask_selector_32_resolves_as_cycle_pattern
    (registers : ProofsLean.MNCore.Masks.RegisterFile) (cycle : Fin 4) :
    (parseMaskSelector? "$imr32").bind
      (fun mask => resolveParsedMaskFlags? mask registers cycle) = some 0 := by
  have hp : parseMaskSelector? "$imr32" = some (.entry false 32) := rfl
  rw [hp]
  exact mask_entry_32_is_pattern_not_entry_zero registers cycle

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

/-- Lower every direct PE-memory destination of one integer ALU expression.
Each destination receives the same prepared ALU result, in source order. -/
def ParsedExpr.toDirectMaskedIntegerWritesInLine? (expression : ParsedExpr)
    (registers : ProofsLean.MNCore.Masks.RegisterFile)
    (directive : ParsedMaskDirective) (hasSingleLineMask : Bool)
    (group : Fin 2) (l2b : Fin 2) (l1b : Fin 8) (mab : Fin 16)
    (pe cycle : Fin 4) (bar0 bar1 : BitVec 12) (tWord : BitVec 32) :
    Option (List ParsedMaskedIntegerAccesses) :=
  match expression.op, expression.destinations with
  | .alu .., _ :: _ =>
      expression.destinations.mapM fun destination =>
        ParsedExpr.toDirectMaskedIntegerAccessesInLine?
          { expression with destinations := [destination] }
          registers directive hasSingleLineMask group l2b l1b mab pe cycle
          bar0 bar1 tWord
  | _, _ => none

def parsedTwoDestinationInteger : ParsedExpr where
  op := .alu .inc (some .i) false none
  sources := [.mem ⟨.lm0, ⟨2, 0, 0, 0, 0, false, none⟩⟩ false false false none]
  destinations := [
    .mem ⟨.lm1, ⟨2, 0, 0, 0, 0, false, none⟩⟩ false false false none,
    .mem ⟨.grf0, ⟨2, 0, 0, 0, 0, false, none⟩⟩ false false false none]
  flush := none
  text := "iinc $lm0v $lr0v $ls0v"

theorem parsed_integer_multiple_destinations_lower_in_order :
    (ParsedExpr.toDirectMaskedIntegerWritesInLine? parsedTwoDestinationInteger
      (fun _ _ => 0) {} false 0 0 0 0 0 0 0 0 0).map
      (List.map fun accesses => accesses.destination) =
        some [⟨.lm1, .long, ⟨0, by decide⟩⟩,
          ⟨.grf0, .long, ⟨0, by decide⟩⟩] := by
  decide

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

def parsedAlufForwardMaskedExpr : ParsedExpr where
  op := .alu .inc (some .i) false none
  sources := [.forward .aluf false false false]
  destinations := [plusOneWrite]
  flush := none
  text := "iinc $aluf $ln0v"

theorem parsed_forward_expr_lowering :
    (ParsedExpr.toDirectMaskedIntegerAccesses? parsedAlufForwardMaskedExpr (fun _ _ => 0) {}
      0 0 0 0 0 0 0 0 0).map (fun accesses => accesses.sourceX) =
        some (.forward .aluf false) := by decide

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

/-- One selected MN-Core matrix face at double precision. Rows and columns
are logical 64-bit elements; the executor stores each element as two adjacent
32-bit words in a physical row. -/
abbrev DoubleMatrixFace := Fin 4 → Fin 4 → BitVec 64

abbrev DoubleMatrixPhysicalFace := Fin 16 → Fin 8 → BitVec 32
abbrev ParsedMatrixReadStore := Fin 16 → Bool → DoubleMatrixPhysicalFace

inductive ParsedMatrixReadTarget where
  | memory (access : DirectMemoryAccess) (selection : PEWordSelection)
  | noWrite

structure ParsedMatrixReadAccesses where
  precision : ProofsLean.MNCore.Issue.ParsedPrecision
  sideY : Bool
  row : Nat
  targets : List ParsedMatrixReadTarget

def ParsedExpr.toDirectMatrixReadAccesses?
    (expression : ParsedExpr) (registers : ProofsLean.MNCore.Masks.RegisterFile)
    (directive : ParsedMaskDirective) (hasSingleLineMask : Bool)
    (context : ParsedIntegerContext) : Option ParsedMatrixReadAccesses := do
  match expression.op, expression.sources with
  | .matrixRead precision, [.matrix sideY _ (some row)] =>
      let targets ← expression.destinations.mapM fun target =>
        match target with
        | .nowrite => some .noWrite
        | .mem .. => do
            let access ← ParsedOperand.toDirectMemoryDestination? target context.pe
              context.cycle context.bar0 context.bar1 context.tWord
            let selection ← ParsedOperand.resolveMemoryWriteSelection? target access.bank
              registers context.cycle directive hasSingleLineMask
            some (.memory access selection)
        | _ => none
      some ⟨precision, sideY, row, targets⟩
  | _, _ => none

structure ParsedDoubleMatrixWriteAccesses where
  source : ParsedIntegerInput
  sideY : Bool
  row : Nat

structure ParsedDoubleMatrixWriteShape where
  source : ParsedOperand
  sideY : Bool
  row : Nat

def ParsedExpr.toDirectDoubleMatrixWriteShape?
    (expression : ParsedExpr) : Option ParsedDoubleMatrixWriteShape :=
  match expression.op, expression.sources, expression.destinations with
  | .matrixWrite .d, [source], [.matrix sideY _ (some row)] =>
      match source with
      | .mem _ false false false _ | .forward _ false false false =>
          some ⟨source, sideY, row⟩
      | _ => none
  | _, _, _ => none

/-- Lower the raw-bit D-precision matrix-write subset. Matrix-write operands
with numerical conversion flags and fixed sources remain unresolved. -/
def ParsedExpr.toDirectDoubleMatrixWriteAccesses?
    (expression : ParsedExpr) (context : ParsedIntegerContext) :
    Option ParsedDoubleMatrixWriteAccesses := do
  let shape ← ParsedExpr.toDirectDoubleMatrixWriteShape? expression
  let source ← ParsedOperand.toParsedIntegerInput? shape.source .long
    context.group context.l2b context.l1b context.mab context.pe context.cycle
    context.bar0 context.bar1 context.tWord
  some ⟨source, shape.sideY, shape.row⟩

theorem ParsedExpr.toDirectDoubleMatrixWriteAccesses_destination_invariant
    (expression : ParsedExpr) (contextA contextB : ParsedIntegerContext)
    (accessesA accessesB : ParsedDoubleMatrixWriteAccesses)
    (loweredA : ParsedExpr.toDirectDoubleMatrixWriteAccesses? expression contextA = some accessesA)
    (loweredB : ParsedExpr.toDirectDoubleMatrixWriteAccesses? expression contextB = some accessesB) :
    accessesA.sideY = accessesB.sideY ∧ accessesA.row = accessesB.row := by
  cases hShape : ParsedExpr.toDirectDoubleMatrixWriteShape? expression with
  | none => simp [ParsedExpr.toDirectDoubleMatrixWriteAccesses?, hShape] at loweredA
  | some shape =>
      simp only [ParsedExpr.toDirectDoubleMatrixWriteAccesses?, hShape] at loweredA loweredB
      cases hSourceA : ParsedOperand.toParsedIntegerInput? shape.source .long
        contextA.group contextA.l2b contextA.l1b contextA.mab contextA.pe contextA.cycle
        contextA.bar0 contextA.bar1 contextA.tWord <;>
        simp [hSourceA] at loweredA
      cases hSourceB : ParsedOperand.toParsedIntegerInput? shape.source .long
        contextB.group contextB.l2b contextB.l1b contextB.mab contextB.pe contextB.cycle
        contextB.bar0 contextB.bar1 contextB.tWord <;>
        simp [hSourceB] at loweredB
      cases loweredA
      cases loweredB
      exact ⟨rfl, rfl⟩

structure ParsedSingleMatrixWriteAccesses where
  source : ParsedIntegerInput
  sideY : Bool
  row : Nat

structure ParsedSingleMatrixWriteShape where
  source : ParsedOperand
  sideY : Bool
  row : Nat

def ParsedExpr.toDirectSingleMatrixWriteShape?
    (expression : ParsedExpr) : Option ParsedSingleMatrixWriteShape :=
  match expression.op, expression.sources, expression.destinations with
  -- F and G share the 32-bit physical row layout.  Keep G values raw: in
  -- particular, block-float encodings must not be normalized here.
  | .matrixWrite .f, [source], [.matrix sideY _ (some row)] =>
      match source with
      | .mem _ false false false _ | .forward _ false false false =>
          some ⟨source, sideY, row⟩
      | _ => none
  | .matrixWrite .g, [source], [.matrix sideY _ (some row)] =>
      match source with
      | .mem _ false false false _ | .forward _ false false false =>
          some ⟨source, sideY, row⟩
      | _ => none
  | _, _, _ => none

theorem ParsedExpr.toDirectSingleMatrixWriteShape?_g
    (access : Access) (sideY : Bool) (row : Nat) (mask : Option ParsedMask) :
    ParsedExpr.toDirectSingleMatrixWriteShape?
      ⟨.matrixWrite .g, [.mem access false false false mask],
        [.matrix sideY 0 (some row)], none, "g-mwrite"⟩ =
      some ⟨.mem access false false false mask, sideY, row⟩ := by
  simp [ParsedExpr.toDirectSingleMatrixWriteShape?]

def ParsedExpr.toDirectSingleMatrixWriteAccesses?
    (expression : ParsedExpr) (context : ParsedIntegerContext) :
    Option ParsedSingleMatrixWriteAccesses := do
  let shape ← ParsedExpr.toDirectSingleMatrixWriteShape? expression
  let source ← ParsedOperand.toParsedIntegerInput? shape.source .long
    context.group context.l2b context.l1b context.mab context.pe context.cycle
    context.bar0 context.bar1 context.tWord
  some ⟨source, shape.sideY, shape.row⟩

theorem ParsedExpr.toDirectSingleMatrixWriteAccesses_destination_invariant
    (expression : ParsedExpr) (contextA contextB : ParsedIntegerContext)
    (accessesA accessesB : ParsedSingleMatrixWriteAccesses)
    (loweredA : ParsedExpr.toDirectSingleMatrixWriteAccesses? expression contextA = some accessesA)
    (loweredB : ParsedExpr.toDirectSingleMatrixWriteAccesses? expression contextB = some accessesB) :
    accessesA.sideY = accessesB.sideY ∧ accessesA.row = accessesB.row := by
  cases hShape : ParsedExpr.toDirectSingleMatrixWriteShape? expression with
  | none => simp [ParsedExpr.toDirectSingleMatrixWriteAccesses?, hShape] at loweredA
  | some shape =>
      simp only [ParsedExpr.toDirectSingleMatrixWriteAccesses?, hShape] at loweredA loweredB
      cases hSourceA : ParsedOperand.toParsedIntegerInput? shape.source .long
        contextA.group contextA.l2b contextA.l1b contextA.mab contextA.pe contextA.cycle
        contextA.bar0 contextA.bar1 contextA.tWord <;>
        simp [hSourceA] at loweredA
      cases hSourceB : ParsedOperand.toParsedIntegerInput? shape.source .long
        contextB.group contextB.l2b contextB.l1b contextB.mab contextB.pe contextB.cycle
        contextB.bar0 contextB.bar1 contextB.tWord <;>
        simp [hSourceB] at loweredB
      cases loweredA
      cases loweredB
      exact ⟨rfl, rfl⟩

def parsedMatrixReadBaseD (row : Nat) : Fin 4 :=
  ⟨row % 4, Nat.mod_lt _ (by decide)⟩

def parsedMatrixReadBaseS (row : Nat) : Fin 8 :=
  ⟨row % 8, Nat.mod_lt _ (by decide)⟩

def parsedMatrixReadBaseH (row : Nat) : Fin 16 :=
  ⟨row % 16, Nat.mod_lt _ (by decide)⟩

def doubleMatrixPhysicalRow (row : Fin 4) : Fin 16 :=
  ⟨row.val * 4, by have h := row.isLt; omega⟩

def doubleMatrixPhysicalColumnHigh (column : Fin 4) : Fin 8 :=
  ⟨column.val * 2, by have h := column.isLt; omega⟩

def doubleMatrixPhysicalColumnLow (column : Fin 4) : Fin 8 :=
  ⟨column.val * 2 + 1, by have h := column.isLt; omega⟩

def doubleMatrixFaceFromPhysicalWords (words : DoubleMatrixPhysicalFace) :
    DoubleMatrixFace := fun row column =>
  words (doubleMatrixPhysicalRow row) (doubleMatrixPhysicalColumnHigh column) ++
    words (doubleMatrixPhysicalRow row) (doubleMatrixPhysicalColumnLow column)

def doubleMatrixWriteRowWords (values : Fin 4 → BitVec 64) :
    Fin 8 → BitVec 32 := fun word =>
  let value := values ⟨word.val / 2, by have h := word.isLt; omega⟩
  if word.val % 2 = 0 then value.extractLsb' 32 32 else value.extractLsb' 0 32

def writeDoubleMatrixPhysicalRow (old : DoubleMatrixPhysicalFace)
    (row : Fin 4) (values : Fin 4 → BitVec 64) : DoubleMatrixPhysicalFace :=
  let physicalRow := doubleMatrixPhysicalRow row
  fun targetRow => if targetRow = physicalRow then doubleMatrixWriteRowWords values
    else old targetRow

def doubleMatrixWriteRowAt (base : Nat) (cycle : Fin 4) : Fin 4 :=
  ⟨(base + cycle.val) % 4, Nat.mod_lt _ (by decide)⟩

theorem doubleMatrixWriteRowAt_injective (base : Nat) :
    Function.Injective (doubleMatrixWriteRowAt base) := by
  intro left right equal
  apply Fin.ext
  have values := congrArg Fin.val equal
  simp [doubleMatrixWriteRowAt] at values
  have leftLt := left.isLt
  have rightLt := right.isLt
  omega

def writeParsedDoubleMatrixStoreRow (old : ParsedMatrixReadStore)
    (mab : Fin 16) (sideY : Bool) (row : Fin 4)
    (values : Fin 4 → BitVec 64) : ParsedMatrixReadStore :=
  fun nextMab nextSide =>
    if nextMab = mab ∧ nextSide = sideY then
      writeDoubleMatrixPhysicalRow (old nextMab nextSide) row values
    else old nextMab nextSide

def parsedMatrixWritePEs : List (Fin 4) := [0, 1, 2, 3]

def prepareParsedSingleMatrixWritePEs (files : IntegerRegisterFiles)
    (slots : ProofsLean.MNCore.Forwarding.Slots) (expression : ParsedExpr)
    (groupContext : ParsedPEGroupContext) (cycle : Fin 4)
    (pes : List (Fin 4)) (buses : Fin 4 → IntegerALU.Bus) :
    ProofsLean.StepResult (Fin 4 → IntegerALU.Bus) :=
  match pes with
  | [] => .ok buses
  | pe :: rest =>
      let context := groupContext.at pe cycle
      match ParsedExpr.toDirectSingleMatrixWriteAccesses? expression context with
      | none => .unknown
      | some accesses =>
          match ParsedIntegerInput.readWithForwarding files slots cycle accesses.source with
          | .failure => .failure
          | .unknown => .unknown
          | .ok bus =>
              prepareParsedSingleMatrixWritePEs files slots expression groupContext cycle rest
                (fun index => if index = pe then bus else buses index)

theorem prepareParsedSingleMatrixWritePEs_all
    (files : IntegerRegisterFiles) (slots : ProofsLean.MNCore.Forwarding.Slots)
    (expression : ParsedExpr) (groupContext : ParsedPEGroupContext) (cycle : Fin 4)
    (accesses : Fin 4 → ParsedSingleMatrixWriteAccesses)
    (buses : Fin 4 → IntegerALU.Bus)
    (lowered : ∀ pe, ParsedExpr.toDirectSingleMatrixWriteAccesses? expression
      (groupContext.at pe cycle) = some (accesses pe))
    (read : ∀ pe, ParsedIntegerInput.readWithForwarding files slots cycle
      (accesses pe).source = .ok (buses pe)) :
    prepareParsedSingleMatrixWritePEs files slots expression groupContext cycle
      parsedMatrixWritePEs (fun _ => ⟨0, 0⟩) = .ok buses := by
  simp [prepareParsedSingleMatrixWritePEs, parsedMatrixWritePEs, lowered, read]
  funext pe
  have peCases : pe = 0 ∨ pe = 1 ∨ pe = 2 ∨ pe = 3 := by
    have h := pe.isLt
    omega
  rcases peCases with h | h | h | h <;> simp [h]

def prepareParsedDoubleMatrixWritePEs (files : IntegerRegisterFiles)
    (slots : ProofsLean.MNCore.Forwarding.Slots) (expression : ParsedExpr)
    (groupContext : ParsedPEGroupContext) (cycle : Fin 4)
    (pes : List (Fin 4)) (values : Fin 4 → BitVec 64) :
    ProofsLean.StepResult (Fin 4 → BitVec 64) :=
  match pes with
  | [] => .ok values
  | pe :: rest =>
      let context := groupContext.at pe cycle
      match ParsedExpr.toDirectDoubleMatrixWriteAccesses? expression context with
      | none => .unknown
      | some accesses =>
          match ParsedIntegerInput.readWithForwarding files slots cycle accesses.source with
          | .failure => .failure
          | .unknown => .unknown
          | .ok bus =>
              prepareParsedDoubleMatrixWritePEs files slots expression groupContext cycle rest
                (fun index => if index = pe then bus.high else values index)

theorem prepareParsedDoubleMatrixWritePEs_all
    (files : IntegerRegisterFiles) (slots : ProofsLean.MNCore.Forwarding.Slots)
    (expression : ParsedExpr) (groupContext : ParsedPEGroupContext) (cycle : Fin 4)
    (accesses : Fin 4 → ParsedDoubleMatrixWriteAccesses)
    (buses : Fin 4 → IntegerALU.Bus)
    (lowered : ∀ pe, ParsedExpr.toDirectDoubleMatrixWriteAccesses? expression
      (groupContext.at pe cycle) = some (accesses pe))
    (read : ∀ pe, ParsedIntegerInput.readWithForwarding files slots cycle
      (accesses pe).source = .ok (buses pe)) :
    prepareParsedDoubleMatrixWritePEs files slots expression groupContext cycle
      parsedMatrixWritePEs (fun _ => 0) = .ok (fun pe => (buses pe).high) := by
  simp [prepareParsedDoubleMatrixWritePEs, parsedMatrixWritePEs, lowered, read]
  funext pe
  have peCases : pe = 0 ∨ pe = 1 ∨ pe = 2 ∨ pe = 3 := by
    have h := pe.isLt
    omega
  rcases peCases with h | h | h | h <;> simp [h]

def parsedDoubleMatrixWriteCycle (files : IntegerRegisterFiles)
    (slots : ProofsLean.MNCore.Forwarding.Slots)
    (groupContext : ParsedPEGroupContext) (expression : ParsedExpr)
    (oldStore : ParsedMatrixReadStore) (cycle : Fin 4) :
    ProofsLean.StepResult ParsedMatrixReadStore :=
  let context := groupContext.at 0 cycle
  match ParsedExpr.toDirectDoubleMatrixWriteAccesses? expression context with
  | none => .unknown
  | some accesses =>
      match prepareParsedDoubleMatrixWritePEs files slots expression groupContext cycle
          parsedMatrixWritePEs (fun _ => 0) with
      | .failure => .failure
      | .unknown => .unknown
      | .ok values =>
          .ok (writeParsedDoubleMatrixStoreRow oldStore groupContext.mab accesses.sideY
            (doubleMatrixWriteRowAt accesses.row cycle) values)

/-- D-precision matrix write over one four-PE MAB. All source reads use the
old PE files and forwarding slots; each cycle writes row `(addr + cycle) % 4`
to the selected matrix side. Only raw, unconverted memory/forward sources are
currently lowered, matching `read_raw_elems` when its format is already D. -/
def parsedDoubleMatrixWriteCycles (files : IntegerRegisterFiles)
    (slots : ProofsLean.MNCore.Forwarding.Slots)
    (groupContext : ParsedPEGroupContext) (expression : ParsedExpr) :
    List (Fin 4) → ParsedMatrixReadStore → ProofsLean.StepResult ParsedMatrixReadStore
  | [], store => .ok store
  | cycle :: rest, store =>
      match parsedDoubleMatrixWriteCycle files slots groupContext expression store cycle with
      | .failure => .failure
      | .unknown => .unknown
      | .ok nextStore => parsedDoubleMatrixWriteCycles files slots groupContext expression rest nextStore

def parsedDoubleMatrixWriteFourCycle (files : IntegerRegisterFiles)
    (slots : ProofsLean.MNCore.Forwarding.Slots)
    (groupContext : ParsedPEGroupContext) (expression : ParsedExpr)
    (oldStore : ParsedMatrixReadStore) :
    ProofsLean.StepResult ParsedMatrixReadStore :=
  parsedDoubleMatrixWriteCycles files slots groupContext expression [0, 1, 2, 3] oldStore

theorem doubleMatrixWriteRowWords_high_word (values : Fin 4 → BitVec 64)
    (column : Fin 4) :
    doubleMatrixWriteRowWords values (doubleMatrixPhysicalColumnHigh column) =
      (values column).extractLsb' 32 32 := by
  simp [doubleMatrixWriteRowWords, doubleMatrixPhysicalColumnHigh]

theorem doubleMatrixWriteRowWords_low_word (values : Fin 4 → BitVec 64)
    (column : Fin 4) :
    doubleMatrixWriteRowWords values (doubleMatrixPhysicalColumnLow column) =
      (values column).extractLsb' 0 32 := by
  have division : (column.val * 2 + 1) / 2 = column.val := by omega
  simp [doubleMatrixWriteRowWords, doubleMatrixPhysicalColumnLow, division]

theorem doubleMatrixPhysicalRow_injective :
    Function.Injective doubleMatrixPhysicalRow := by
  intro left right equal
  apply Fin.ext
  have values := congrArg Fin.val equal
  simp [doubleMatrixPhysicalRow] at values
  omega

theorem doubleMatrixFaceFromPhysicalWords_after_write
    (old : DoubleMatrixPhysicalFace) (writeRow logicalRow column : Fin 4)
    (values : Fin 4 → BitVec 64) :
    doubleMatrixFaceFromPhysicalWords
      (writeDoubleMatrixPhysicalRow old writeRow values) logicalRow column =
        if logicalRow = writeRow then values column
        else doubleMatrixFaceFromPhysicalWords old logicalRow column := by
  by_cases same : logicalRow = writeRow
  · subst logicalRow
    simp [doubleMatrixFaceFromPhysicalWords, writeDoubleMatrixPhysicalRow,
      doubleMatrixWriteRowWords_high_word, doubleMatrixWriteRowWords_low_word]
    exact BitVec.extractLsb'_append_extractLsb'
  · have physicalDifferent : doubleMatrixPhysicalRow logicalRow ≠
        doubleMatrixPhysicalRow writeRow := by
      intro equal
      exact same (doubleMatrixPhysicalRow_injective equal)
    simp [doubleMatrixFaceFromPhysicalWords, writeDoubleMatrixPhysicalRow, physicalDifferent,
      same]

def doubleMatrixReadRow (base cycle : Fin 4) : Fin 4 :=
  ⟨(base.val + cycle.val) % 4, Nat.mod_lt _ (by decide)⟩

/-- Rust `compute_mread` at D precision selects the PE as matrix row and the
operand row plus cycle as matrix column, then packs that 64-bit element in
the most-significant long word and zero-fills the rest of the bus. -/
def doubleMatrixReadBus (face : DoubleMatrixFace) (base pe cycle : Fin 4) :
    IntegerALU.Bus :=
  ⟨face pe (doubleMatrixReadRow base cycle), 0⟩

theorem doubleMatrixRead_after_transposed_write
    (old : DoubleMatrixPhysicalFace) (writeRow sourcePE : Fin 4)
    (values : Fin 4 → BitVec 64) :
    doubleMatrixReadBus
      (doubleMatrixFaceFromPhysicalWords (writeDoubleMatrixPhysicalRow old writeRow values))
      sourcePE writeRow 0 = ⟨values sourcePE, 0⟩ := by
  simp [doubleMatrixReadBus, doubleMatrixReadRow,
    Nat.mod_eq_of_lt sourcePE.isLt,
    doubleMatrixFaceFromPhysicalWords_after_write]

theorem parsedDoubleMatrixStore_write_readback
    (old : ParsedMatrixReadStore) (mab : Fin 16) (sideY : Bool)
    (row sourcePE : Fin 4) (values : Fin 4 → BitVec 64) :
    doubleMatrixReadBus
      (doubleMatrixFaceFromPhysicalWords
        ((writeParsedDoubleMatrixStoreRow old mab sideY row values) mab sideY))
      sourcePE row 0 = ⟨values sourcePE, 0⟩ := by
  simp [writeParsedDoubleMatrixStoreRow, doubleMatrixRead_after_transposed_write]

theorem parsedDoubleMatrixStore_other_write_preserves_readback
    (old : ParsedMatrixReadStore) (mab : Fin 16) (sideY : Bool)
    (writeRow readRow sourcePE : Fin 4) (values : Fin 4 → BitVec 64)
    (different : readRow ≠ writeRow) :
    doubleMatrixReadBus
      (doubleMatrixFaceFromPhysicalWords
        ((writeParsedDoubleMatrixStoreRow old mab sideY writeRow values) mab sideY))
      sourcePE readRow 0 =
    doubleMatrixReadBus (doubleMatrixFaceFromPhysicalWords (old mab sideY))
      sourcePE readRow 0 := by
  simp [writeParsedDoubleMatrixStoreRow, doubleMatrixReadBus, doubleMatrixReadRow,
    Nat.mod_eq_of_lt sourcePE.isLt,
    doubleMatrixFaceFromPhysicalWords_after_write, different]

def writeParsedDoubleMatrixStoreFourRows (old : ParsedMatrixReadStore)
    (mab : Fin 16) (sideY : Bool) (base : Nat)
    (values : Fin 4 → Fin 4 → BitVec 64) : ParsedMatrixReadStore :=
  writeParsedDoubleMatrixStoreRow
    (writeParsedDoubleMatrixStoreRow
      (writeParsedDoubleMatrixStoreRow
        (writeParsedDoubleMatrixStoreRow old mab sideY (doubleMatrixWriteRowAt base 0)
          (values 0))
        mab sideY (doubleMatrixWriteRowAt base 1) (values 1))
      mab sideY (doubleMatrixWriteRowAt base 2) (values 2))
    mab sideY (doubleMatrixWriteRowAt base 3) (values 3)

theorem parsedDoubleMatrixWriteFourCycle_store
    (files : IntegerRegisterFiles) (slots : ProofsLean.MNCore.Forwarding.Slots)
    (groupContext : ParsedPEGroupContext) (expression : ParsedExpr)
    (oldStore : ParsedMatrixReadStore)
    (accesses : Fin 4 → Fin 4 → ParsedDoubleMatrixWriteAccesses)
    (buses : Fin 4 → Fin 4 → IntegerALU.Bus)
    (lowered : ∀ cycle pe, ParsedExpr.toDirectDoubleMatrixWriteAccesses? expression
      (groupContext.at pe cycle) = some (accesses cycle pe))
    (read : ∀ cycle pe, ParsedIntegerInput.readWithForwarding files slots cycle
      (accesses cycle pe).source = .ok (buses cycle pe)) :
    parsedDoubleMatrixWriteFourCycle files slots groupContext expression oldStore =
      .ok (writeParsedDoubleMatrixStoreFourRows oldStore groupContext.mab
        (accesses 0 0).sideY (accesses 0 0).row
        (fun cycle pe => (buses cycle pe).high)) := by
  have sameDestination (cycle pe : Fin 4) :=
    ParsedExpr.toDirectDoubleMatrixWriteAccesses_destination_invariant expression
      (groupContext.at pe cycle) (groupContext.at 0 0) (accesses cycle pe) (accesses 0 0)
      (lowered cycle pe) (lowered 0 0)
  have cycleStep (cycle : Fin 4) (store : ParsedMatrixReadStore) :
      parsedDoubleMatrixWriteCycle files slots groupContext expression store cycle =
        .ok (writeParsedDoubleMatrixStoreRow store groupContext.mab (accesses 0 0).sideY
          (doubleMatrixWriteRowAt (accesses 0 0).row cycle)
          (fun pe => (buses cycle pe).high)) := by
    have prepared := prepareParsedDoubleMatrixWritePEs_all files slots expression
      groupContext cycle (accesses cycle) (buses cycle) (lowered cycle) (read cycle)
    have hLower := lowered cycle 0
    have hDestination := sameDestination cycle 0
    simp only [parsedDoubleMatrixWriteCycle, hLower, prepared, hDestination.1, hDestination.2]
  simp [parsedDoubleMatrixWriteFourCycle, parsedDoubleMatrixWriteCycles, cycleStep,
    writeParsedDoubleMatrixStoreFourRows]

theorem parsedDoubleMatrixStore_four_rows_readback
    (old : ParsedMatrixReadStore) (mab : Fin 16) (sideY : Bool) (base : Nat)
    (values : Fin 4 → Fin 4 → BitVec 64) (cycle sourcePE : Fin 4) :
    doubleMatrixReadBus
      (doubleMatrixFaceFromPhysicalWords
        ((writeParsedDoubleMatrixStoreFourRows old mab sideY base values) mab sideY))
      sourcePE (doubleMatrixWriteRowAt base cycle) 0 = ⟨values cycle sourcePE, 0⟩ := by
  have rowDifferent (left right : Fin 4) (different : left ≠ right) :
      doubleMatrixWriteRowAt base left ≠ doubleMatrixWriteRowAt base right := by
    intro equal
    exact different (doubleMatrixWriteRowAt_injective base equal)
  have cycleCases : cycle = 0 ∨ cycle = 1 ∨ cycle = 2 ∨ cycle = 3 := by
    have h := cycle.isLt
    omega
  rcases cycleCases with cycleEq | cycleEq | cycleEq | cycleEq
  · subst cycle
    simp only [writeParsedDoubleMatrixStoreFourRows]
    rw [parsedDoubleMatrixStore_other_write_preserves_readback _ _ _
      (doubleMatrixWriteRowAt base 3) (doubleMatrixWriteRowAt base 0) sourcePE (values 3)
      (rowDifferent 0 3 (by decide))]
    rw [parsedDoubleMatrixStore_other_write_preserves_readback _ _ _
      (doubleMatrixWriteRowAt base 2) (doubleMatrixWriteRowAt base 0) sourcePE (values 2)
      (rowDifferent 0 2 (by decide))]
    rw [parsedDoubleMatrixStore_other_write_preserves_readback _ _ _
      (doubleMatrixWriteRowAt base 1) (doubleMatrixWriteRowAt base 0) sourcePE (values 1)
      (rowDifferent 0 1 (by decide))]
    exact parsedDoubleMatrixStore_write_readback old mab sideY
      (doubleMatrixWriteRowAt base 0) sourcePE (values 0)
  · subst cycle
    simp only [writeParsedDoubleMatrixStoreFourRows]
    rw [parsedDoubleMatrixStore_other_write_preserves_readback _ _ _
      (doubleMatrixWriteRowAt base 3) (doubleMatrixWriteRowAt base 1) sourcePE (values 3)
      (rowDifferent 1 3 (by decide))]
    rw [parsedDoubleMatrixStore_other_write_preserves_readback _ _ _
      (doubleMatrixWriteRowAt base 2) (doubleMatrixWriteRowAt base 1) sourcePE (values 2)
      (rowDifferent 1 2 (by decide))]
    exact parsedDoubleMatrixStore_write_readback
      (writeParsedDoubleMatrixStoreRow old mab sideY (doubleMatrixWriteRowAt base 0)
        (values 0)) mab sideY (doubleMatrixWriteRowAt base 1) sourcePE (values 1)
  · subst cycle
    simp only [writeParsedDoubleMatrixStoreFourRows]
    rw [parsedDoubleMatrixStore_other_write_preserves_readback _ _ _
      (doubleMatrixWriteRowAt base 3) (doubleMatrixWriteRowAt base 2) sourcePE (values 3)
      (rowDifferent 2 3 (by decide))]
    exact parsedDoubleMatrixStore_write_readback
      (writeParsedDoubleMatrixStoreRow
        (writeParsedDoubleMatrixStoreRow old mab sideY (doubleMatrixWriteRowAt base 0)
          (values 0)) mab sideY (doubleMatrixWriteRowAt base 1) (values 1))
      mab sideY (doubleMatrixWriteRowAt base 2) sourcePE (values 2)
  · subst cycle
    simp only [writeParsedDoubleMatrixStoreFourRows]
    exact parsedDoubleMatrixStore_write_readback
      (writeParsedDoubleMatrixStoreRow
        (writeParsedDoubleMatrixStoreRow
          (writeParsedDoubleMatrixStoreRow old mab sideY (doubleMatrixWriteRowAt base 0)
            (values 0)) mab sideY (doubleMatrixWriteRowAt base 1) (values 1))
        mab sideY (doubleMatrixWriteRowAt base 2) (values 2))
      mab sideY (doubleMatrixWriteRowAt base 3) sourcePE (values 3)

theorem parsedDoubleMatrixWriteFourCycle_readback
    (files : IntegerRegisterFiles) (slots : ProofsLean.MNCore.Forwarding.Slots)
    (groupContext : ParsedPEGroupContext) (expression : ParsedExpr)
    (oldStore : ParsedMatrixReadStore)
    (accesses : Fin 4 → Fin 4 → ParsedDoubleMatrixWriteAccesses)
    (buses : Fin 4 → Fin 4 → IntegerALU.Bus)
    (lowered : ∀ cycle pe, ParsedExpr.toDirectDoubleMatrixWriteAccesses? expression
      (groupContext.at pe cycle) = some (accesses cycle pe))
    (read : ∀ cycle pe, ParsedIntegerInput.readWithForwarding files slots cycle
      (accesses cycle pe).source = .ok (buses cycle pe))
    (cycle sourcePE : Fin 4) :
    ∃ newStore, parsedDoubleMatrixWriteFourCycle files slots groupContext expression oldStore =
        .ok newStore ∧
      doubleMatrixReadBus
        (doubleMatrixFaceFromPhysicalWords
          (newStore groupContext.mab (accesses 0 0).sideY))
        sourcePE (doubleMatrixWriteRowAt (accesses 0 0).row cycle) 0 =
          ⟨(buses cycle sourcePE).high, 0⟩ := by
  refine ⟨writeParsedDoubleMatrixStoreFourRows oldStore groupContext.mab
    (accesses 0 0).sideY (accesses 0 0).row
    (fun writtenCycle pe => (buses writtenCycle pe).high), ?_, ?_⟩
  · exact parsedDoubleMatrixWriteFourCycle_store files slots groupContext expression oldStore
      accesses buses lowered read
  · exact parsedDoubleMatrixStore_four_rows_readback oldStore groupContext.mab
      (accesses 0 0).sideY (accesses 0 0).row
      (fun writtenCycle pe => (buses writtenCycle pe).high) cycle sourcePE


theorem parsedDoubleMatrixWriteCycle_readback
    (files : IntegerRegisterFiles) (slots : ProofsLean.MNCore.Forwarding.Slots)
    (groupContext : ParsedPEGroupContext) (expression : ParsedExpr)
    (oldStore : ParsedMatrixReadStore) (cycle sourcePE : Fin 4)
    (accesses : ParsedDoubleMatrixWriteAccesses) (values : Fin 4 → BitVec 64)
    (lowered : ParsedExpr.toDirectDoubleMatrixWriteAccesses? expression
      (groupContext.at 0 cycle) = some accesses)
    (prepared : prepareParsedDoubleMatrixWritePEs files slots expression groupContext cycle
      parsedMatrixWritePEs (fun _ => 0) = .ok values) :
    ∃ newStore, parsedDoubleMatrixWriteCycle files slots groupContext expression oldStore cycle =
        .ok newStore ∧
      doubleMatrixReadBus
        (doubleMatrixFaceFromPhysicalWords (newStore groupContext.mab accesses.sideY))
        sourcePE (doubleMatrixWriteRowAt accesses.row cycle) 0 = ⟨values sourcePE, 0⟩ := by
  refine ⟨writeParsedDoubleMatrixStoreRow oldStore groupContext.mab accesses.sideY
    (doubleMatrixWriteRowAt accesses.row cycle) values, ?_, ?_⟩
  · simp only [parsedDoubleMatrixWriteCycle, lowered, prepared]
  · exact parsedDoubleMatrixStore_write_readback oldStore groupContext.mab accesses.sideY
      (doubleMatrixWriteRowAt accesses.row cycle) sourcePE values

theorem parsedDoubleMatrixWriteCycle_readback_of_pe_reads
    (files : IntegerRegisterFiles) (slots : ProofsLean.MNCore.Forwarding.Slots)
    (groupContext : ParsedPEGroupContext) (expression : ParsedExpr)
    (oldStore : ParsedMatrixReadStore) (cycle sourcePE : Fin 4)
    (accesses : Fin 4 → ParsedDoubleMatrixWriteAccesses)
    (buses : Fin 4 → IntegerALU.Bus)
    (lowered : ∀ pe, ParsedExpr.toDirectDoubleMatrixWriteAccesses? expression
      (groupContext.at pe cycle) = some (accesses pe))
    (read : ∀ pe, ParsedIntegerInput.readWithForwarding files slots cycle
      (accesses pe).source = .ok (buses pe)) :
    ∃ newStore, parsedDoubleMatrixWriteCycle files slots groupContext expression oldStore cycle =
        .ok newStore ∧
      doubleMatrixReadBus
        (doubleMatrixFaceFromPhysicalWords (newStore groupContext.mab (accesses 0).sideY))
        sourcePE (doubleMatrixWriteRowAt (accesses 0).row cycle) 0 =
          ⟨(buses sourcePE).high, 0⟩ := by
  have prepared := prepareParsedDoubleMatrixWritePEs_all files slots expression groupContext
    cycle accesses buses lowered read
  refine ⟨writeParsedDoubleMatrixStoreRow oldStore groupContext.mab (accesses 0).sideY
    (doubleMatrixWriteRowAt (accesses 0).row cycle) (fun pe => (buses pe).high), ?_, ?_⟩
  · simp only [parsedDoubleMatrixWriteCycle, lowered, prepared]
  · exact parsedDoubleMatrixStore_write_readback oldStore groupContext.mab (accesses 0).sideY
      (doubleMatrixWriteRowAt (accesses 0).row cycle) sourcePE (fun pe => (buses pe).high)

def writeDoubleMatrixReadSlots (old : ProofsLean.MNCore.Forwarding.Slots)
    (face : DoubleMatrixFace) (base pe : Fin 4) (noForward : Bool) :
    ProofsLean.StepResult ProofsLean.MNCore.Forwarding.Slots :=
  if noForward then .ok old else .ok (fun unit cycle =>
    if unit = .matrixRead then
      .known (doubleMatrixReadBus face base pe cycle)
    else old unit cycle)

theorem doubleMatrixRead_mreadf_readback
    (files : IntegerRegisterFiles) (old : ProofsLean.MNCore.Forwarding.Slots)
    (words : DoubleMatrixPhysicalFace) (base pe cycle : Fin 4) :
    ParsedIntegerInput.readWithForwarding files
      (fun unit slotCycle =>
        if unit = .matrixRead then
          .known (doubleMatrixReadBus (doubleMatrixFaceFromPhysicalWords words)
            base pe slotCycle)
        else old unit slotCycle)
      cycle (.forward .mreadf false) =
        .ok (doubleMatrixReadBus (doubleMatrixFaceFromPhysicalWords words)
          base pe cycle) := by
  simp [ParsedIntegerInput.readWithForwarding, ParsedIntegerInput.forwardUnit,
    ParsedIntegerInput.applyRounding]

theorem doubleMatrixReadBus_physical_layout
    (words : DoubleMatrixPhysicalFace) (base pe cycle : Fin 4) :
    doubleMatrixReadBus (doubleMatrixFaceFromPhysicalWords words) base pe cycle =
      ⟨words (doubleMatrixPhysicalRow pe)
          (doubleMatrixPhysicalColumnHigh (doubleMatrixReadRow base cycle)) ++
        words (doubleMatrixPhysicalRow pe)
          (doubleMatrixPhysicalColumnLow (doubleMatrixReadRow base cycle)), 0⟩ := rfl

def singleMatrixPhysicalRow (row : Fin 8) : Fin 16 :=
  ⟨row.val * 2, by have h := row.isLt; omega⟩

theorem singleMatrixPhysicalRow_injective : Function.Injective singleMatrixPhysicalRow := by
  intro left right equal
  apply Fin.ext
  have values := congrArg Fin.val equal
  simp [singleMatrixPhysicalRow] at values
  omega

def singleMatrixReadColumn (base : Fin 8) (cycle : Fin 4) : Fin 8 :=
  ⟨(base.val + cycle.val) % 8, Nat.mod_lt _ (by decide)⟩

def singleMatrixReadBus (words : DoubleMatrixPhysicalFace)
    (base : Fin 8) (pe cycle : Fin 4) : IntegerALU.Bus :=
  let column := singleMatrixReadColumn base cycle
  let row0 : Fin 8 := ⟨2 * pe.val, by have h := pe.isLt; omega⟩
  let row1 : Fin 8 := ⟨2 * pe.val + 1, by have h := pe.isLt; omega⟩
  ⟨words (singleMatrixPhysicalRow row0) column ++
    words (singleMatrixPhysicalRow row1) column, 0⟩

def singleMatrixWriteRowAt (base : Nat) (cycle : Fin 4) : Fin 8 :=
  ⟨(base + cycle.val) % 8, Nat.mod_lt _ (by decide)⟩

theorem singleMatrixWriteRowAt_injective (base : Nat) :
    Function.Injective (singleMatrixWriteRowAt base) := by
  intro left right equal
  apply Fin.ext
  have values := congrArg Fin.val equal
  simp [singleMatrixWriteRowAt] at values
  have leftLt := left.isLt
  have rightLt := right.isLt
  omega

/-- Rust `unpack(..., 32, 2)` for one PE reads the two high 32-bit words. -/
def singleMatrixWriteValues (buses : Fin 4 → IntegerALU.Bus) : Fin 8 → BitVec 32 :=
  fun index =>
    let pe : Fin 4 := ⟨index.val / 2, by have h := index.isLt; omega⟩
    if index.val % 2 = 0 then (buses pe).high.extractLsb' 32 32
    else (buses pe).high.extractLsb' 0 32

def writeSingleMatrixPhysicalRow (old : DoubleMatrixPhysicalFace)
    (row : Fin 8) (values : Fin 8 → BitVec 32) : DoubleMatrixPhysicalFace :=
  let physicalRow := singleMatrixPhysicalRow row
  fun targetRow => if targetRow = physicalRow then values else old targetRow

def writeParsedSingleMatrixStoreRow (old : ParsedMatrixReadStore)
    (mab : Fin 16) (sideY : Bool) (row : Fin 8)
    (values : Fin 8 → BitVec 32) : ParsedMatrixReadStore :=
  fun nextMab nextSide =>
    if nextMab = mab ∧ nextSide = sideY then
      writeSingleMatrixPhysicalRow (old nextMab nextSide) row values
    else old nextMab nextSide

def writeParsedSingleMatrixStoreFourRows (old : ParsedMatrixReadStore)
    (mab : Fin 16) (sideY : Bool) (base : Nat)
    (values : Fin 4 → Fin 8 → BitVec 32) : ParsedMatrixReadStore :=
  writeParsedSingleMatrixStoreRow
    (writeParsedSingleMatrixStoreRow
      (writeParsedSingleMatrixStoreRow
        (writeParsedSingleMatrixStoreRow old mab sideY (singleMatrixWriteRowAt base 0)
          (values 0))
        mab sideY (singleMatrixWriteRowAt base 1) (values 1))
      mab sideY (singleMatrixWriteRowAt base 2) (values 2))
    mab sideY (singleMatrixWriteRowAt base 3) (values 3)

theorem singleMatrixWriteValues_high_word
    (buses : Fin 4 → IntegerALU.Bus) (pe : Fin 4) :
    singleMatrixWriteValues buses ⟨2 * pe.val, by have h := pe.isLt; omega⟩ =
      (buses pe).high.extractLsb' 32 32 := by
  simp [singleMatrixWriteValues]

theorem singleMatrixWriteValues_low_word
    (buses : Fin 4 → IntegerALU.Bus) (pe : Fin 4) :
    singleMatrixWriteValues buses ⟨2 * pe.val + 1, by have h := pe.isLt; omega⟩ =
      (buses pe).high.extractLsb' 0 32 := by
  have division : (2 * pe.val + 1) / 2 = pe.val := by omega
  simp [singleMatrixWriteValues, division]

theorem singleMatrixReadBus_after_write_high_cell
    (old : DoubleMatrixPhysicalFace) (row column : Fin 8)
    (values : Fin 8 → BitVec 32)
    (even : row.val % 2 = 0) :
    (singleMatrixReadBus (writeSingleMatrixPhysicalRow old row values) column
      ⟨row.val / 2, by have _h := row.isLt; omega⟩ 0).high.extractLsb' 32 32 =
        values column := by
  let row0 : Fin 8 := ⟨2 * (row.val / 2), by have h := row.isLt; omega⟩
  let row1 : Fin 8 := ⟨2 * (row.val / 2) + 1, by have h := row.isLt; omega⟩
  have row0Eq : row0 = row := by
    apply Fin.ext
    simp [row0]
    omega
  have row1Ne : row1 ≠ row := by
    intro equal
    have values := congrArg Fin.val equal
    simp [row1] at values
    omega
  have row0PhysicalEq : singleMatrixPhysicalRow row0 = singleMatrixPhysicalRow row :=
    congrArg singleMatrixPhysicalRow row0Eq
  have row1PhysicalNe : singleMatrixPhysicalRow row1 ≠ singleMatrixPhysicalRow row := by
    intro equal
    exact row1Ne (singleMatrixPhysicalRow_injective equal)
  simp [singleMatrixReadBus, singleMatrixReadColumn, writeSingleMatrixPhysicalRow,
    row0, row1, row0PhysicalEq, row1PhysicalNe,
    Nat.mod_eq_of_lt column.isLt]
  exact BitVec.extractLsb'_append_eq_left

theorem singleMatrixReadBus_after_write_low_cell
    (old : DoubleMatrixPhysicalFace) (row column : Fin 8)
    (values : Fin 8 → BitVec 32)
    (odd : row.val % 2 = 1) :
    (singleMatrixReadBus (writeSingleMatrixPhysicalRow old row values) column
      ⟨row.val / 2, by have _h := row.isLt; omega⟩ 0).high.extractLsb' 0 32 =
        values column := by
  let row0 : Fin 8 := ⟨2 * (row.val / 2), by have h := row.isLt; omega⟩
  let row1 : Fin 8 := ⟨2 * (row.val / 2) + 1, by have h := row.isLt; omega⟩
  have row1Eq : row1 = row := by
    apply Fin.ext
    simp [row1]
    omega
  have row0Ne : row0 ≠ row := by
    intro equal
    have values := congrArg Fin.val equal
    simp [row0] at values
    omega
  have row1PhysicalEq : singleMatrixPhysicalRow row1 = singleMatrixPhysicalRow row :=
    congrArg singleMatrixPhysicalRow row1Eq
  have row0PhysicalNe : singleMatrixPhysicalRow row0 ≠ singleMatrixPhysicalRow row := by
    intro equal
    exact row0Ne (singleMatrixPhysicalRow_injective equal)
  simp [singleMatrixReadBus, singleMatrixReadColumn, writeSingleMatrixPhysicalRow,
    row0, row1, row1PhysicalEq, row0PhysicalNe,
    Nat.mod_eq_of_lt column.isLt]
  exact BitVec.extractLsb'_append_eq_right

theorem parsedSingleMatrixStore_readback_cell
    (old : ParsedMatrixReadStore) (mab : Fin 16) (sideY : Bool)
    (row column : Fin 8) (values : Fin 8 → BitVec 32) :
    let readPE : Fin 4 := ⟨row.val / 2, by have h := row.isLt; omega⟩
    if row.val % 2 = 0 then
      (singleMatrixReadBus
        (writeParsedSingleMatrixStoreRow old mab sideY row values mab sideY)
        column readPE 0).high.extractLsb' 32 32 = values column
    else
      (singleMatrixReadBus
        (writeParsedSingleMatrixStoreRow old mab sideY row values mab sideY)
        column readPE 0).high.extractLsb' 0 32 = values column := by
  dsimp
  by_cases even : row.val % 2 = 0
  · simp [even, writeParsedSingleMatrixStoreRow]
    exact singleMatrixReadBus_after_write_high_cell (old mab sideY) row column values even
  · have odd : row.val % 2 = 1 := by
      have h : row.val % 2 < 2 := Nat.mod_lt _ (by decide)
      omega
    simp [writeParsedSingleMatrixStoreRow, odd]
    exact singleMatrixReadBus_after_write_low_cell (old mab sideY) row column values odd

theorem singleMatrixReadBus_other_write_preserves_high_cell
    (old : DoubleMatrixPhysicalFace) (writeRow readRow column : Fin 8)
    (values : Fin 8 → BitVec 32) (even : readRow.val % 2 = 0)
    (different : readRow ≠ writeRow) :
    (singleMatrixReadBus (writeSingleMatrixPhysicalRow old writeRow values) column
      ⟨readRow.val / 2, by have h := readRow.isLt; omega⟩ 0).high.extractLsb' 32 32 =
    (singleMatrixReadBus old column
      ⟨readRow.val / 2, by have h := readRow.isLt; omega⟩ 0).high.extractLsb' 32 32 := by
  let row0 : Fin 8 := ⟨2 * (readRow.val / 2), by have h := readRow.isLt; omega⟩
  let row1 : Fin 8 := ⟨2 * (readRow.val / 2) + 1, by have h := readRow.isLt; omega⟩
  have row0Eq : row0 = readRow := by
    apply Fin.ext
    simp [row0]
    omega
  have row0NeWrite : row0 ≠ writeRow := by
    intro h
    exact different (row0Eq.symm.trans h)
  have row0PhysicalNe : singleMatrixPhysicalRow row0 ≠ singleMatrixPhysicalRow writeRow := by
    intro h
    exact row0NeWrite (singleMatrixPhysicalRow_injective h)
  simp [singleMatrixReadBus, singleMatrixReadColumn, writeSingleMatrixPhysicalRow,
    row0, row1, row0PhysicalNe, Nat.mod_eq_of_lt column.isLt]
  rw [BitVec.extractLsb'_append_eq_left, BitVec.extractLsb'_append_eq_left]

theorem singleMatrixReadBus_other_write_preserves_low_cell
    (old : DoubleMatrixPhysicalFace) (writeRow readRow column : Fin 8)
    (values : Fin 8 → BitVec 32) (odd : readRow.val % 2 = 1)
    (different : readRow ≠ writeRow) :
    (singleMatrixReadBus (writeSingleMatrixPhysicalRow old writeRow values) column
      ⟨readRow.val / 2, by have h := readRow.isLt; omega⟩ 0).high.extractLsb' 0 32 =
    (singleMatrixReadBus old column
      ⟨readRow.val / 2, by have h := readRow.isLt; omega⟩ 0).high.extractLsb' 0 32 := by
  let row0 : Fin 8 := ⟨2 * (readRow.val / 2), by have h := readRow.isLt; omega⟩
  let row1 : Fin 8 := ⟨2 * (readRow.val / 2) + 1, by have h := readRow.isLt; omega⟩
  have row1Eq : row1 = readRow := by
    apply Fin.ext
    simp [row1]
    omega
  have row1NeWrite : row1 ≠ writeRow := by
    intro h
    exact different (row1Eq.symm.trans h)
  have row1PhysicalNe : singleMatrixPhysicalRow row1 ≠ singleMatrixPhysicalRow writeRow := by
    intro h
    exact row1NeWrite (singleMatrixPhysicalRow_injective h)
  simp [singleMatrixReadBus, singleMatrixReadColumn, writeSingleMatrixPhysicalRow,
    row0, row1, row1PhysicalNe, Nat.mod_eq_of_lt column.isLt]
  rw [BitVec.extractLsb'_append_eq_right, BitVec.extractLsb'_append_eq_right]

def singleMatrixReadSelectedWord (words : DoubleMatrixPhysicalFace)
    (row column : Fin 8) : BitVec 32 :=
  let pe : Fin 4 := ⟨row.val / 2, by have h := row.isLt; omega⟩
  if row.val % 2 = 0 then
    (singleMatrixReadBus words column pe 0).high.extractLsb' 32 32
  else
    (singleMatrixReadBus words column pe 0).high.extractLsb' 0 32

theorem singleMatrixReadSelectedWord_after_write
    (old : DoubleMatrixPhysicalFace) (row column : Fin 8)
    (values : Fin 8 → BitVec 32) :
    singleMatrixReadSelectedWord (writeSingleMatrixPhysicalRow old row values) row column =
      values column := by
  unfold singleMatrixReadSelectedWord
  by_cases even : row.val % 2 = 0
  · simp [even]
    exact singleMatrixReadBus_after_write_high_cell old row column values even
  · have odd : row.val % 2 = 1 := by
      have h : row.val % 2 < 2 := Nat.mod_lt _ (by decide)
      omega
    simp [even, odd]
    exact singleMatrixReadBus_after_write_low_cell old row column values odd

theorem singleMatrixReadSelectedWord_other_write
    (old : DoubleMatrixPhysicalFace) (writeRow readRow column : Fin 8)
    (values : Fin 8 → BitVec 32) (different : readRow ≠ writeRow) :
    singleMatrixReadSelectedWord (writeSingleMatrixPhysicalRow old writeRow values)
      readRow column = singleMatrixReadSelectedWord old readRow column := by
  unfold singleMatrixReadSelectedWord
  by_cases even : readRow.val % 2 = 0
  · simp [even]
    exact singleMatrixReadBus_other_write_preserves_high_cell
      old writeRow readRow column values even different
  · have odd : readRow.val % 2 = 1 := by
      have h : readRow.val % 2 < 2 := Nat.mod_lt _ (by decide)
      omega
    simp [even, odd]
    exact singleMatrixReadBus_other_write_preserves_low_cell
      old writeRow readRow column values odd different

theorem parsedSingleMatrixStore_readback_selected_word
    (old : ParsedMatrixReadStore) (mab : Fin 16) (sideY : Bool)
    (row column : Fin 8) (values : Fin 8 → BitVec 32) :
    singleMatrixReadSelectedWord
      ((writeParsedSingleMatrixStoreRow old mab sideY row values) mab sideY) row column =
        values column := by
  simpa [writeParsedSingleMatrixStoreRow] using
    singleMatrixReadSelectedWord_after_write (old mab sideY) row column values

theorem parsedSingleMatrixStore_other_write_preserves_selected_word
    (old : ParsedMatrixReadStore) (mab : Fin 16) (sideY : Bool)
    (writeRow readRow column : Fin 8) (values : Fin 8 → BitVec 32)
    (different : readRow ≠ writeRow) :
    singleMatrixReadSelectedWord
      ((writeParsedSingleMatrixStoreRow old mab sideY writeRow values) mab sideY)
      readRow column = singleMatrixReadSelectedWord (old mab sideY) readRow column := by
  simpa [writeParsedSingleMatrixStoreRow] using
    singleMatrixReadSelectedWord_other_write (old mab sideY) writeRow readRow column
      values different

theorem parsedSingleMatrixStore_four_rows_readback
    (old : ParsedMatrixReadStore) (mab : Fin 16) (sideY : Bool) (base : Nat)
    (values : Fin 4 → Fin 8 → BitVec 32) (cycle : Fin 4) (column : Fin 8) :
    singleMatrixReadSelectedWord
      ((writeParsedSingleMatrixStoreFourRows old mab sideY base values) mab sideY)
      (singleMatrixWriteRowAt base cycle) column = values cycle column := by
  have rowDifferent (left right : Fin 4) (different : left ≠ right) :
      singleMatrixWriteRowAt base left ≠ singleMatrixWriteRowAt base right := by
    intro equal
    exact different (singleMatrixWriteRowAt_injective base equal)
  have cycleCases : cycle = 0 ∨ cycle = 1 ∨ cycle = 2 ∨ cycle = 3 := by
    have h := cycle.isLt
    omega
  rcases cycleCases with cycleEq | cycleEq | cycleEq | cycleEq
  · subst cycle
    simp only [writeParsedSingleMatrixStoreFourRows]
    rw [parsedSingleMatrixStore_other_write_preserves_selected_word _ _ _
      (singleMatrixWriteRowAt base 3) (singleMatrixWriteRowAt base 0) column (values 3)
      (rowDifferent 0 3 (by decide))]
    rw [parsedSingleMatrixStore_other_write_preserves_selected_word _ _ _
      (singleMatrixWriteRowAt base 2) (singleMatrixWriteRowAt base 0) column (values 2)
      (rowDifferent 0 2 (by decide))]
    rw [parsedSingleMatrixStore_other_write_preserves_selected_word _ _ _
      (singleMatrixWriteRowAt base 1) (singleMatrixWriteRowAt base 0) column (values 1)
      (rowDifferent 0 1 (by decide))]
    exact parsedSingleMatrixStore_readback_selected_word old mab sideY
      (singleMatrixWriteRowAt base 0) column (values 0)
  · subst cycle
    simp only [writeParsedSingleMatrixStoreFourRows]
    rw [parsedSingleMatrixStore_other_write_preserves_selected_word _ _ _
      (singleMatrixWriteRowAt base 3) (singleMatrixWriteRowAt base 1) column (values 3)
      (rowDifferent 1 3 (by decide))]
    rw [parsedSingleMatrixStore_other_write_preserves_selected_word _ _ _
      (singleMatrixWriteRowAt base 2) (singleMatrixWriteRowAt base 1) column (values 2)
      (rowDifferent 1 2 (by decide))]
    exact parsedSingleMatrixStore_readback_selected_word
      (writeParsedSingleMatrixStoreRow old mab sideY (singleMatrixWriteRowAt base 0)
        (values 0)) mab sideY (singleMatrixWriteRowAt base 1) column (values 1)
  · subst cycle
    simp only [writeParsedSingleMatrixStoreFourRows]
    rw [parsedSingleMatrixStore_other_write_preserves_selected_word _ _ _
      (singleMatrixWriteRowAt base 3) (singleMatrixWriteRowAt base 2) column (values 3)
      (rowDifferent 2 3 (by decide))]
    exact parsedSingleMatrixStore_readback_selected_word
      (writeParsedSingleMatrixStoreRow
        (writeParsedSingleMatrixStoreRow old mab sideY (singleMatrixWriteRowAt base 0)
          (values 0)) mab sideY (singleMatrixWriteRowAt base 1) (values 1))
      mab sideY (singleMatrixWriteRowAt base 2) column (values 2)
  · subst cycle
    simp only [writeParsedSingleMatrixStoreFourRows]
    exact parsedSingleMatrixStore_readback_selected_word
      (writeParsedSingleMatrixStoreRow
        (writeParsedSingleMatrixStoreRow
          (writeParsedSingleMatrixStoreRow old mab sideY (singleMatrixWriteRowAt base 0)
            (values 0)) mab sideY (singleMatrixWriteRowAt base 1) (values 1))
        mab sideY (singleMatrixWriteRowAt base 2) (values 2))
      mab sideY (singleMatrixWriteRowAt base 3) column (values 3)

def parsedSingleMatrixWriteCycle (files : IntegerRegisterFiles)
    (slots : ProofsLean.MNCore.Forwarding.Slots)
    (groupContext : ParsedPEGroupContext) (expression : ParsedExpr)
    (oldStore : ParsedMatrixReadStore) (cycle : Fin 4) :
    ProofsLean.StepResult ParsedMatrixReadStore :=
  let context := groupContext.at 0 cycle
  match ParsedExpr.toDirectSingleMatrixWriteAccesses? expression context with
  | none => .unknown
  | some accesses =>
      match prepareParsedSingleMatrixWritePEs files slots expression groupContext cycle
          parsedMatrixWritePEs (fun _ => ⟨0, 0⟩) with
      | .failure => .failure
      | .unknown => .unknown
      | .ok buses =>
          .ok (writeParsedSingleMatrixStoreRow oldStore groupContext.mab accesses.sideY
            (singleMatrixWriteRowAt accesses.row cycle) (singleMatrixWriteValues buses))

def parsedSingleMatrixWriteCycles (files : IntegerRegisterFiles)
    (slots : ProofsLean.MNCore.Forwarding.Slots)
    (groupContext : ParsedPEGroupContext) (expression : ParsedExpr) :
    List (Fin 4) → ParsedMatrixReadStore → ProofsLean.StepResult ParsedMatrixReadStore
  | [], store => .ok store
  | cycle :: rest, store =>
      match parsedSingleMatrixWriteCycle files slots groupContext expression store cycle with
      | .failure => .failure
      | .unknown => .unknown
      | .ok nextStore => parsedSingleMatrixWriteCycles files slots groupContext expression rest nextStore

def parsedSingleMatrixWriteFourCycle (files : IntegerRegisterFiles)
    (slots : ProofsLean.MNCore.Forwarding.Slots)
    (groupContext : ParsedPEGroupContext) (expression : ParsedExpr)
    (oldStore : ParsedMatrixReadStore) :
    ProofsLean.StepResult ParsedMatrixReadStore :=
  parsedSingleMatrixWriteCycles files slots groupContext expression [0, 1, 2, 3] oldStore

theorem parsedSingleMatrixWriteCycle_readback_cell
    (files : IntegerRegisterFiles) (slots : ProofsLean.MNCore.Forwarding.Slots)
    (groupContext : ParsedPEGroupContext) (expression : ParsedExpr)
    (oldStore : ParsedMatrixReadStore) (cycle column : Fin 4)
    (accesses : Fin 4 → ParsedSingleMatrixWriteAccesses)
    (buses : Fin 4 → IntegerALU.Bus)
    (lowered : ∀ pe, ParsedExpr.toDirectSingleMatrixWriteAccesses? expression
      (groupContext.at pe cycle) = some (accesses pe))
    (read : ∀ pe, ParsedIntegerInput.readWithForwarding files slots cycle
      (accesses pe).source = .ok (buses pe)) :
    ∃ newStore, parsedSingleMatrixWriteCycle files slots groupContext expression oldStore cycle =
      .ok newStore ∧
      (let writeRow := singleMatrixWriteRowAt (accesses 0).row cycle
       let readPE : Fin 4 := ⟨writeRow.val / 2, by have h := writeRow.isLt; omega⟩
       if writeRow.val % 2 = 0 then
         (singleMatrixReadBus
           (newStore groupContext.mab (accesses 0).sideY)
           ⟨2 * column.val, by have h := column.isLt; omega⟩ readPE 0).high.extractLsb' 32 32 =
             singleMatrixWriteValues buses ⟨2 * column.val, by have h := column.isLt; omega⟩
       else
         (singleMatrixReadBus
           (newStore groupContext.mab (accesses 0).sideY)
           ⟨2 * column.val + 1, by have h := column.isLt; omega⟩ readPE 0).high.extractLsb' 0 32 =
             singleMatrixWriteValues buses ⟨2 * column.val + 1, by have h := column.isLt; omega⟩) := by
  have prepared := prepareParsedSingleMatrixWritePEs_all files slots expression groupContext
    cycle accesses buses lowered read
  refine ⟨writeParsedSingleMatrixStoreRow oldStore groupContext.mab (accesses 0).sideY
    (singleMatrixWriteRowAt (accesses 0).row cycle) (singleMatrixWriteValues buses), ?_, ?_⟩
  · simp only [parsedSingleMatrixWriteCycle, lowered, prepared]
  · let writeRow := singleMatrixWriteRowAt (accesses 0).row cycle
    dsimp
    by_cases even : writeRow.val % 2 = 0
    · simpa [even, writeRow] using parsedSingleMatrixStore_readback_cell oldStore
        groupContext.mab (accesses 0).sideY writeRow
        ⟨2 * column.val, by have h := column.isLt; omega⟩
        (singleMatrixWriteValues buses)
    · have odd : writeRow.val % 2 = 1 := by
        have h : writeRow.val % 2 < 2 := Nat.mod_lt _ (by decide)
        omega
      simpa [even, odd, writeRow] using parsedSingleMatrixStore_readback_cell oldStore
        groupContext.mab (accesses 0).sideY writeRow
        ⟨2 * column.val + 1, by have h := column.isLt; omega⟩
        (singleMatrixWriteValues buses)

theorem parsedSingleMatrixWriteFourCycle_store
    (files : IntegerRegisterFiles) (slots : ProofsLean.MNCore.Forwarding.Slots)
    (groupContext : ParsedPEGroupContext) (expression : ParsedExpr)
    (oldStore : ParsedMatrixReadStore)
    (accesses : Fin 4 → Fin 4 → ParsedSingleMatrixWriteAccesses)
    (buses : Fin 4 → Fin 4 → IntegerALU.Bus)
    (lowered : ∀ cycle pe, ParsedExpr.toDirectSingleMatrixWriteAccesses? expression
      (groupContext.at pe cycle) = some (accesses cycle pe))
    (read : ∀ cycle pe, ParsedIntegerInput.readWithForwarding files slots cycle
      (accesses cycle pe).source = .ok (buses cycle pe)) :
    parsedSingleMatrixWriteFourCycle files slots groupContext expression oldStore =
      .ok (writeParsedSingleMatrixStoreFourRows oldStore groupContext.mab
        (accesses 0 0).sideY (accesses 0 0).row
        (fun cycle => singleMatrixWriteValues (buses cycle))) := by
  have sameDestination (cycle pe : Fin 4) :=
    ParsedExpr.toDirectSingleMatrixWriteAccesses_destination_invariant expression
      (groupContext.at pe cycle) (groupContext.at 0 0) (accesses cycle pe) (accesses 0 0)
      (lowered cycle pe) (lowered 0 0)
  have cycleStep (cycle : Fin 4) (store : ParsedMatrixReadStore) :
      parsedSingleMatrixWriteCycle files slots groupContext expression store cycle =
        .ok (writeParsedSingleMatrixStoreRow store groupContext.mab (accesses 0 0).sideY
          (singleMatrixWriteRowAt (accesses 0 0).row cycle)
          (singleMatrixWriteValues (buses cycle))) := by
    have prepared := prepareParsedSingleMatrixWritePEs_all files slots expression
      groupContext cycle (accesses cycle) (buses cycle) (lowered cycle) (read cycle)
    have hLower := lowered cycle 0
    have hDestination := sameDestination cycle 0
    simp only [parsedSingleMatrixWriteCycle, hLower, prepared,
      hDestination.1, hDestination.2]
  simp [parsedSingleMatrixWriteFourCycle, parsedSingleMatrixWriteCycles, cycleStep,
    writeParsedSingleMatrixStoreFourRows]

theorem parsedSingleMatrixWriteFourCycle_readback_selected_word
    (files : IntegerRegisterFiles) (slots : ProofsLean.MNCore.Forwarding.Slots)
    (groupContext : ParsedPEGroupContext) (expression : ParsedExpr)
    (oldStore : ParsedMatrixReadStore)
    (accesses : Fin 4 → Fin 4 → ParsedSingleMatrixWriteAccesses)
    (buses : Fin 4 → Fin 4 → IntegerALU.Bus)
    (lowered : ∀ cycle pe, ParsedExpr.toDirectSingleMatrixWriteAccesses? expression
      (groupContext.at pe cycle) = some (accesses cycle pe))
    (read : ∀ cycle pe, ParsedIntegerInput.readWithForwarding files slots cycle
      (accesses cycle pe).source = .ok (buses cycle pe))
    (cycle : Fin 4) (column : Fin 8) :
    ∃ newStore, parsedSingleMatrixWriteFourCycle files slots groupContext expression oldStore =
        .ok newStore ∧
      singleMatrixReadSelectedWord
        (newStore groupContext.mab (accesses 0 0).sideY)
        (singleMatrixWriteRowAt (accesses 0 0).row cycle) column =
          singleMatrixWriteValues (buses cycle) column := by
  refine ⟨writeParsedSingleMatrixStoreFourRows oldStore groupContext.mab
    (accesses 0 0).sideY (accesses 0 0).row
    (fun writtenCycle => singleMatrixWriteValues (buses writtenCycle)), ?_, ?_⟩
  · exact parsedSingleMatrixWriteFourCycle_store files slots groupContext expression oldStore
      accesses buses lowered read
  · exact parsedSingleMatrixStore_four_rows_readback oldStore groupContext.mab
      (accesses 0 0).sideY (accesses 0 0).row
      (fun writtenCycle => singleMatrixWriteValues (buses writtenCycle)) cycle column

/-- G precision has the same raw 32-bit physical write and selected-word
readback semantics as F, provided each PE's direct source lowering and read
succeed. The opcode premise pins this result to the block-float ISA operation. -/
theorem parsedGMatrixWriteFourCycle_readback_selected_word
    (files : IntegerRegisterFiles) (slots : ProofsLean.MNCore.Forwarding.Slots)
    (groupContext : ParsedPEGroupContext) (expression : ParsedExpr)
    (isGWrite : expression.op = .matrixWrite .g)
    (oldStore : ParsedMatrixReadStore)
    (accesses : Fin 4 → Fin 4 → ParsedSingleMatrixWriteAccesses)
    (buses : Fin 4 → Fin 4 → IntegerALU.Bus)
    (lowered : ∀ cycle pe, ParsedExpr.toDirectSingleMatrixWriteAccesses? expression
      (groupContext.at pe cycle) = some (accesses cycle pe))
    (read : ∀ cycle pe, ParsedIntegerInput.readWithForwarding files slots cycle
      (accesses cycle pe).source = .ok (buses cycle pe))
    (cycle : Fin 4) (column : Fin 8) :
    ∃ newStore, parsedSingleMatrixWriteFourCycle files slots groupContext expression oldStore =
        .ok newStore ∧
      singleMatrixReadSelectedWord
        (newStore groupContext.mab (accesses 0 0).sideY)
        (singleMatrixWriteRowAt (accesses 0 0).row cycle) column =
          singleMatrixWriteValues (buses cycle) column := by
  cases expression with
  | mk op sources destinations flush text =>
    cases isGWrite
    exact parsedSingleMatrixWriteFourCycle_readback_selected_word files slots groupContext
      { op := .matrixWrite .g, sources := sources, destinations := destinations,
        flush := flush, text := text } oldStore accesses buses lowered read cycle column

def halfMatrixReadColumn (base : Fin 16) (cycle : Fin 4) : Fin 16 :=
  ⟨(base.val + 2 * cycle.val) % 16, Nat.mod_lt _ (by decide)⟩

def halfMatrixReadNextColumn (column : Fin 16) : Fin 16 :=
  ⟨(column.val + 1) % 16, Nat.mod_lt _ (by decide)⟩

def halfMatrixPhysicalElement (words : DoubleMatrixPhysicalFace)
    (row column : Fin 16) : BitVec 16 :=
  let word := words row ⟨column.val / 2, by have h := column.isLt; omega⟩
  if column.val % 2 = 0 then word.extractLsb' 16 16 else word.extractLsb' 0 16

def halfMatrixReadBus (words : DoubleMatrixPhysicalFace)
    (base : Fin 16) (pe cycle : Fin 4) : IntegerALU.Bus :=
  let column0 := halfMatrixReadColumn base cycle
  let column1 := halfMatrixReadNextColumn column0
  let row0 : Fin 16 := ⟨4 * pe.val, by have h := pe.isLt; omega⟩
  let row1 : Fin 16 := ⟨4 * pe.val + 1, by have h := pe.isLt; omega⟩
  let row2 : Fin 16 := ⟨4 * pe.val + 2, by have h := pe.isLt; omega⟩
  let row3 : Fin 16 := ⟨4 * pe.val + 3, by have h := pe.isLt; omega⟩
  let h0 := halfMatrixPhysicalElement words row0 column0
  let h1 := halfMatrixPhysicalElement words row1 column0
  let h2 := halfMatrixPhysicalElement words row2 column0
  let h3 := halfMatrixPhysicalElement words row3 column0
  let h4 := halfMatrixPhysicalElement words row0 column1
  let h5 := halfMatrixPhysicalElement words row1 column1
  let h6 := halfMatrixPhysicalElement words row2 column1
  let h7 := halfMatrixPhysicalElement words row3 column1
  ⟨h0 ++ h1 ++ h2 ++ h3, h4 ++ h5 ++ h6 ++ h7⟩

def parsedMatrixReadBus (store : ParsedMatrixReadStore)
    (accesses : ParsedMatrixReadAccesses) (context : ParsedIntegerContext) :
    IntegerALU.Bus :=
  let face := store context.mab accesses.sideY
  match accesses.precision with
  | .d => doubleMatrixReadBus (doubleMatrixFaceFromPhysicalWords face)
      (parsedMatrixReadBaseD accesses.row) context.pe context.cycle
  | .h => halfMatrixReadBus face (parsedMatrixReadBaseH accesses.row)
      context.pe context.cycle
  | _ => singleMatrixReadBus face (parsedMatrixReadBaseS accesses.row)
      context.pe context.cycle

def writeMatrixReadOutputs (old : ProofsLean.MNCore.Forwarding.Slots)
    (outputs : Fin 4 → IntegerALU.Bus) (noForward : Bool) :
    ProofsLean.StepResult ProofsLean.MNCore.Forwarding.Slots :=
  if noForward then .ok old else .ok (fun unit cycle =>
    if unit = .matrixRead then .known (outputs cycle) else old unit cycle)

theorem writeMatrixReadOutputs_semantics
    (old : ProofsLean.MNCore.Forwarding.Slots)
    (outputs : Fin 4 → IntegerALU.Bus) (noForward : Bool) :
    writeMatrixReadOutputs old outputs noForward =
      if noForward then .ok old else .ok (fun unit cycle =>
        if unit = .matrixRead then .known (outputs cycle) else old unit cycle) := by
  cases noForward <;> rfl

theorem singleMatrixReadBus_physical_layout
    (words : DoubleMatrixPhysicalFace) (base : Fin 8) (pe cycle : Fin 4) :
    (singleMatrixReadBus words base pe cycle).high =
        words (singleMatrixPhysicalRow ⟨2 * pe.val, by have h := pe.isLt; omega⟩)
          (singleMatrixReadColumn base cycle) ++
        words (singleMatrixPhysicalRow ⟨2 * pe.val + 1, by have h := pe.isLt; omega⟩)
          (singleMatrixReadColumn base cycle) ∧
      (singleMatrixReadBus words base pe cycle).low = 0 := by
  simp [singleMatrixReadBus]

theorem halfMatrixReadBus_physical_layout
    (words : DoubleMatrixPhysicalFace) (base : Fin 16) (pe cycle : Fin 4) :
    halfMatrixReadBus words base pe cycle =
      ⟨(halfMatrixPhysicalElement words ⟨4 * pe.val, by have h := pe.isLt; omega⟩
          (halfMatrixReadColumn base cycle) ++
        halfMatrixPhysicalElement words ⟨4 * pe.val + 1, by have h := pe.isLt; omega⟩
          (halfMatrixReadColumn base cycle) ++
        halfMatrixPhysicalElement words ⟨4 * pe.val + 2, by have h := pe.isLt; omega⟩
          (halfMatrixReadColumn base cycle) ++
        halfMatrixPhysicalElement words ⟨4 * pe.val + 3, by have h := pe.isLt; omega⟩
          (halfMatrixReadColumn base cycle)),
       (halfMatrixPhysicalElement words ⟨4 * pe.val, by have h := pe.isLt; omega⟩
          (halfMatrixReadNextColumn (halfMatrixReadColumn base cycle)) ++
        halfMatrixPhysicalElement words ⟨4 * pe.val + 1, by have h := pe.isLt; omega⟩
          (halfMatrixReadNextColumn (halfMatrixReadColumn base cycle)) ++
        halfMatrixPhysicalElement words ⟨4 * pe.val + 2, by have h := pe.isLt; omega⟩
          (halfMatrixReadNextColumn (halfMatrixReadColumn base cycle)) ++
        halfMatrixPhysicalElement words ⟨4 * pe.val + 3, by have h := pe.isLt; omega⟩
          (halfMatrixReadNextColumn (halfMatrixReadColumn base cycle)))⟩ := by
  simp [halfMatrixReadBus]

theorem matrixReadOutputs_mreadf_readback
    (files : IntegerRegisterFiles) (old : ProofsLean.MNCore.Forwarding.Slots)
    (outputs : Fin 4 → IntegerALU.Bus) (cycle : Fin 4) :
    ParsedIntegerInput.readWithForwarding files
      (fun unit slotCycle =>
        if unit = .matrixRead then .known (outputs slotCycle) else old unit slotCycle)
      cycle (.forward .mreadf false) = .ok (outputs cycle) := by
  simp [ParsedIntegerInput.readWithForwarding, ParsedIntegerInput.forwardUnit,
    ParsedIntegerInput.applyRounding]

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

theorem parsedIntegerMaskedRegisterStep_masked_readback
    (files : IntegerRegisterFiles) (accesses : ParsedMaskedIntegerAccesses)
    (reduced : Bool) (x y : IntegerALU.Bus) (output : IntegerALU.BusResult)
    (sourceX : ParsedIntegerInput.read files accesses.sourceX = .ok x)
    (sourceY : ParsedIntegerInput.read files accesses.sourceY = .ok y)
    (evaluated : evaluateParsedIntegerAlu accesses.op x y reduced = .ok output)
    (index : Fin 4) (within : index.val < count accesses.destination.bank
      accesses.destination.width) :
    ∃ nextFiles, parsedIntegerMaskedRegisterStep files accesses reduced = .ok nextFiles ∧
      readDirectAccess nextFiles accesses.destination index =
        mergeSelectedWord (readDirectAccess files accesses.destination index)
          (unpackALUBus
            (parsedOutputAfterFlush accesses.flushSelection output.value) index)
          (selectedWordMask accesses.writeSelection.flags
            accesses.writeSelection.longLong index) := by
  refine ⟨writeDirectAccessMasked files accesses.destination
      (unpackALUBus (parsedOutputAfterFlush accesses.flushSelection output.value))
      accesses.writeSelection, ?_, ?_⟩
  · exact parsedIntegerMaskedRegisterStep_success files accesses reduced x y output
      sourceX sourceY evaluated
  · exact readDirectAccessMasked_after_write files accesses.destination
      (unpackALUBus (parsedOutputAfterFlush accesses.flushSelection output.value))
      accesses.writeSelection index within

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

inductive BlockHazardResource where
  | l1bm (index : Fin 8)
  | l2bm (index : Fin 2)
  deriving DecidableEq, Repr

inductive BlockHazardPath where
  | l1ToPe
  | peToL1
  | l2ToL1
  | l1ToL2
  | multicast
  | mv
  deriving DecidableEq, Repr

inductive BlockHazardKind where
  | dataRace
  | portConflict
  deriving DecidableEq, Repr

structure TimedBlockAccess where
  resource : BlockHazardResource
  path : BlockHazardPath
  write : Bool
  address : Option Nat
  length : Nat
  startWord : Nat
  cycle : Fin 4
  deriving DecidableEq, Repr

structure BlockHazardRule where
  kind : BlockHazardKind
  distance : PEHazardDistance
  deriving DecidableEq, Repr

def timedBlockAccessesOverlap (left right : TimedBlockAccess) : Bool :=
  match left.address, right.address with
  | some leftAddress, some rightAddress =>
      leftAddress < rightAddress + right.length &&
        rightAddress < leftAddress + left.length
  | _, _ => true

/-- SDM 3.6.3.1–3.6.3.8 block-memory rules transcribed from
`viz/core/src/hazard.rs`; same-resource filtering is part of this relation. -/
def blockHazardRule? (earlier later : TimedBlockAccess) : Option BlockHazardRule :=
  if earlier.resource != later.resource || !earlier.write || later.write then none
  else match earlier.path, later.path, earlier.resource with
  | .l1ToL2, .mv, .l2bm _ => some ⟨.dataRace, .steps 2⟩
  | .l1ToL2, .l2ToL1, .l2bm _ => some ⟨.portConflict, .steps 4⟩
  | .l2ToL1, .l1ToL2, .l1bm _ => some ⟨.portConflict, .steps 3⟩
  | .l2ToL1, .multicast, .l1bm _ => some ⟨.portConflict, .steps 3⟩
  | .multicast, .l1ToL2, .l1bm _ => some ⟨.portConflict, .steps 4⟩
  | .multicast, .multicast, .l1bm _ => some ⟨.portConflict, .steps 4⟩
  | .multicast, .l1ToPe, .l1bm _ => some ⟨.dataRace, .cycles 11⟩
  | .l2ToL1, .l1ToPe, .l1bm _ => some ⟨.dataRace, .cycles 7⟩
  | .peToL1, .l1ToL2, .l1bm _ => some ⟨.dataRace, .cycles 11⟩
  | .peToL1, .multicast, .l1bm _ => some ⟨.dataRace, .cycles 11⟩
  | .peToL1, .l1ToPe, .l1bm _ => some ⟨.portConflict, .steps 3⟩
  | _, _, _ => none

/-- Data-race rules require overlapping regions; port conflicts cover the whole
resource regardless of address. -/
def applicableBlockHazardRule? (earlier later : TimedBlockAccess) :
    Option BlockHazardRule := do
  let rule ← blockHazardRule? earlier later
  if rule.kind == .dataRace && !timedBlockAccessesOverlap earlier later then none
  else some rule

def TimedBlockAccess.absoluteCycle (access : TimedBlockAccess) : Nat :=
  access.startWord * 4 + access.cycle.val

structure TimedBlockHazardConstraint where
  earlier : TimedBlockAccess
  later : TimedBlockAccess
  kind : BlockHazardKind
  distance : Nat
  required : Nat
  deriving DecidableEq, Repr

/-- Construct an in-window constraint with the step/cycle units used by the
Rust analyzer. -/
def makeTimedBlockHazardConstraint? (earlier later : TimedBlockAccess) :
    Option TimedBlockHazardConstraint := do
  if !(earlier.startWord < later.startWord) ||
      later.startWord - earlier.startWord > 4 then none else
    let rule ← applicableBlockHazardRule? earlier later
    match rule.distance with
    | .steps count =>
        some ⟨earlier, later, rule.kind,
          (later.startWord - earlier.startWord) * 4, count * 4⟩
    | .cycles count =>
        some ⟨earlier, later, rule.kind,
          later.absoluteCycle - earlier.absoluteCycle, count⟩

/-- A data-race constraint is emitted only for overlapping locations. -/
theorem applicableBlockHazardRule_dataRace_overlaps
    (earlier later : TimedBlockAccess) (rule : BlockHazardRule)
    (applicable : applicableBlockHazardRule? earlier later = some rule)
    (dataRace : rule.kind = .dataRace) :
    timedBlockAccessesOverlap earlier later = true := by
  cases hRule : blockHazardRule? earlier later with
  | none => simp [applicableBlockHazardRule?, hRule] at applicable
  | some found =>
      cases hKind : found.kind with
      | dataRace =>
          cases hOverlap : timedBlockAccessesOverlap earlier later with
          | false => simp [applicableBlockHazardRule?, hRule, hKind, hOverlap] at applicable
          | true =>
              have same : found = rule := by
                simpa [applicableBlockHazardRule?, hRule, hKind, hOverlap] using applicable
              simpa [same] using hOverlap
      | portConflict =>
          simp [applicableBlockHazardRule?, hRule, hKind] at applicable
          have same : found = rule := applicable
          subst rule
          simp [hKind] at dataRace

/-- Port conflicts do not depend on address overlap. -/
theorem applicableBlockHazardRule_portConflict_keeps_disjoint
    (earlier later : TimedBlockAccess) (rule : BlockHazardRule)
    (generated : blockHazardRule? earlier later = some rule)
    (portConflict : rule.kind = .portConflict)
    (disjoint : timedBlockAccessesOverlap earlier later = false) :
    applicableBlockHazardRule? earlier later = some rule := by
  simp [applicableBlockHazardRule?, generated, portConflict, disjoint]

theorem l1ToL2_mv_l2bm_hazard_rule (index : Fin 2) :
    blockHazardRule?
      ⟨.l2bm index, .l1ToL2, true, some 0, 1, 0, 0⟩
      ⟨.l2bm index, .mv, false, some 8, 1, 2, 0⟩ =
      some ⟨.dataRace, .steps 2⟩ := by simp [blockHazardRule?]

theorem l1ToL2_l2ToL1_l2bm_hazard_rule (index : Fin 2) :
    blockHazardRule?
      ⟨.l2bm index, .l1ToL2, true, some 0, 1, 0, 0⟩
      ⟨.l2bm index, .l2ToL1, false, some 8, 1, 4, 0⟩ =
      some ⟨.portConflict, .steps 4⟩ := by simp [blockHazardRule?]

theorem l2ToL1_l1ToL2_l1bm_hazard_rule (index : Fin 8) :
    blockHazardRule?
      ⟨.l1bm index, .l2ToL1, true, some 0, 1, 0, 0⟩
      ⟨.l1bm index, .l1ToL2, false, some 8, 1, 3, 0⟩ =
      some ⟨.portConflict, .steps 3⟩ := by simp [blockHazardRule?]

theorem l2ToL1_multicast_l1bm_hazard_rule (index : Fin 8) :
    blockHazardRule?
      ⟨.l1bm index, .l2ToL1, true, some 0, 1, 0, 0⟩
      ⟨.l1bm index, .multicast, false, some 8, 1, 3, 0⟩ =
      some ⟨.portConflict, .steps 3⟩ := by simp [blockHazardRule?]

theorem multicast_l1ToL2_l1bm_hazard_rule (index : Fin 8) :
    blockHazardRule?
      ⟨.l1bm index, .multicast, true, some 0, 1, 0, 0⟩
      ⟨.l1bm index, .l1ToL2, false, some 8, 1, 4, 0⟩ =
      some ⟨.portConflict, .steps 4⟩ := by simp [blockHazardRule?]

theorem multicast_multicast_l1bm_hazard_rule (index : Fin 8) :
    blockHazardRule?
      ⟨.l1bm index, .multicast, true, some 0, 1, 0, 0⟩
      ⟨.l1bm index, .multicast, false, some 8, 1, 4, 0⟩ =
      some ⟨.portConflict, .steps 4⟩ := by simp [blockHazardRule?]

theorem multicast_l1ToPe_l1bm_hazard_rule (index : Fin 8) :
    blockHazardRule?
      ⟨.l1bm index, .multicast, true, some 0, 1, 0, 0⟩
      ⟨.l1bm index, .l1ToPe, false, some 8, 1, 11, 0⟩ =
      some ⟨.dataRace, .cycles 11⟩ := by simp [blockHazardRule?]

theorem l2ToL1_l1ToPe_l1bm_hazard_rule (index : Fin 8) :
    blockHazardRule?
      ⟨.l1bm index, .l2ToL1, true, some 0, 1, 0, 0⟩
      ⟨.l1bm index, .l1ToPe, false, some 8, 1, 7, 0⟩ =
      some ⟨.dataRace, .cycles 7⟩ := by simp [blockHazardRule?]

theorem peToL1_l1ToL2_l1bm_hazard_rule (index : Fin 8) :
    blockHazardRule?
      ⟨.l1bm index, .peToL1, true, some 0, 1, 0, 0⟩
      ⟨.l1bm index, .l1ToL2, false, some 8, 1, 11, 0⟩ =
      some ⟨.dataRace, .cycles 11⟩ := by simp [blockHazardRule?]

theorem peToL1_multicast_l1bm_hazard_rule (index : Fin 8) :
    blockHazardRule?
      ⟨.l1bm index, .peToL1, true, some 0, 1, 0, 0⟩
      ⟨.l1bm index, .multicast, false, some 8, 1, 11, 0⟩ =
      some ⟨.dataRace, .cycles 11⟩ := by simp [blockHazardRule?]

theorem peToL1_l1ToPe_l1bm_hazard_rule (index : Fin 8) :
    blockHazardRule?
      ⟨.l1bm index, .peToL1, true, some 0, 1, 0, 0⟩
      ⟨.l1bm index, .l1ToPe, false, some 8, 1, 3, 0⟩ =
      some ⟨.portConflict, .steps 3⟩ := by simp [blockHazardRule?]

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

/-- The static PE hazard analyzer ignores the multiline mask directive; only a
single-line mask attached to the memory operand affects written cycles. -/
theorem ParsedOperand.toTimedPEHazardEvents?_directive_irrelevant
    (operand : ParsedOperand) (write : Bool) (control : ParsedMaskExecutionControl)
    (directive : ParsedMaskDirective) :
    ParsedOperand.toTimedPEHazardEvents? operand write
        { control with directive := directive } =
      ParsedOperand.toTimedPEHazardEvents? operand write control := by
  cases operand <;> rfl

def ParsedExpr.toTimedPEHazardEvents? (expression : ParsedExpr)
    (control : ParsedMaskExecutionControl) : Option (List TimedPEAccess) := do
  let reads ← expression.sources.mapM fun operand =>
    ParsedOperand.toTimedPEHazardEvents? operand false control
  let writes ← expression.destinations.mapM fun operand =>
    ParsedOperand.toTimedPEHazardEvents? operand true control
  pure (reads.flatten ++ writes.flatten)

theorem ParsedExpr.toTimedPEHazardEvents?_directive_irrelevant
    (expression : ParsedExpr) (control : ParsedMaskExecutionControl)
    (directive : ParsedMaskDirective) :
    ParsedExpr.toTimedPEHazardEvents? expression
        { control with directive := directive } =
      ParsedExpr.toTimedPEHazardEvents? expression control := by
  simp [ParsedExpr.toTimedPEHazardEvents?,
    ParsedOperand.toTimedPEHazardEvents?_directive_irrelevant]

def ParsedMaskedIssueLine.toTimedPEHazardEvents?
    (line : ParsedMaskedIssueLine) (control : ParsedMaskExecutionControl) :
    Option (List TimedPEAccess) :=
  match line with
  | .nop => some []
  | .pe expressions => do
      let perExpression ← expressions.mapM fun expression =>
        ParsedExpr.toTimedPEHazardEvents? expression control
      pure perExpression.flatten

theorem ParsedMaskedIssueLine.toTimedPEHazardEvents?_directive_irrelevant
    (line : ParsedMaskedIssueLine) (control : ParsedMaskExecutionControl)
    (directive : ParsedMaskDirective) :
    ParsedMaskedIssueLine.toTimedPEHazardEvents? line
        { control with directive := directive } =
      ParsedMaskedIssueLine.toTimedPEHazardEvents? line control := by
  cases line with
  | nop => rfl
  | pe expressions =>
      simp [ParsedMaskedIssueLine.toTimedPEHazardEvents?,
        ParsedExpr.toTimedPEHazardEvents?_directive_irrelevant]

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

/-- An empty violation report certifies every emitted distance constraint. -/
theorem pe_hazard_no_violations_satisfies_constraints
    (constraints : List PEHazardConstraint)
    (noViolations : violatingPEHazardConstraints constraints = []) :
    ∀ constraint ∈ constraints, constraint.required ≤ constraint.distance := by
  intro constraint member
  have notViolated : constraint.violated = false := by
    cases value : constraint.violated with
    | false => rfl
    | true =>
        have present : constraint ∈ violatingPEHazardConstraints constraints := by
          simp [violatingPEHazardConstraints, member, value]
        rw [noViolations] at present
        simp at present
  simp [PEHazardConstraint.violated] at notViolated
  omega

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

/-- Provenance that a constraint was emitted while comparing a prior issue
window with a later issue's events. -/
inductive PEHazardConstraintEmitted : List TimedPEAccess →
    List (List TimedPEAccess) → PEHazardConstraint → Prop where
  | current {earlier current rest constraint} :
      constraint ∈ peHazardConstraintsBetween earlier current →
      PEHazardConstraintEmitted earlier (current :: rest) constraint
  | later {earlier current rest constraint} :
      PEHazardConstraintEmitted (earlier ++ current) rest constraint →
      PEHazardConstraintEmitted earlier (current :: rest) constraint

theorem collectPEHazardConstraintsAux_mem_iff_emitted
    (earlier : List TimedPEAccess) (remaining : List (List TimedPEAccess))
    (constraint : PEHazardConstraint) :
    constraint ∈ collectPEHazardConstraintsAux earlier remaining ↔
      PEHazardConstraintEmitted earlier remaining constraint := by
  induction remaining generalizing earlier with
  | nil =>
      constructor
      · simp [collectPEHazardConstraintsAux]
      · intro emitted
        cases emitted
  | cons current rest ih =>
      simp only [collectPEHazardConstraintsAux, List.mem_append]
      constructor
      · intro member
        rcases member with currentMember | laterMember
        · exact .current currentMember
        · exact .later ((ih (earlier ++ current)).mp laterMember)
      · intro emitted
        cases emitted with
        | current currentMember => exact Or.inl currentMember
        | later laterEmitted => exact Or.inr ((ih (earlier ++ current)).mpr laterEmitted)

/-- Every collected constraint has an issue-group pair that emitted it. -/
theorem collectPEHazardConstraintsAux_mem_has_emitting_groups
    (earlier : List TimedPEAccess) (remaining : List (List TimedPEAccess))
    (constraint : PEHazardConstraint)
    (member : constraint ∈ collectPEHazardConstraintsAux earlier remaining) :
    ∃ prior current, constraint ∈ peHazardConstraintsBetween prior current := by
  induction remaining generalizing earlier with
  | nil => simp [collectPEHazardConstraintsAux] at member
  | cons current rest ih =>
      simp only [collectPEHazardConstraintsAux, List.mem_append] at member
      rcases member with currentMember | laterMember
      · exact ⟨earlier, current, currentMember⟩
      · exact ih (earlier ++ current) laterMember

/-- A collected constraint records concrete write and read events from the
issue groups compared by the hazard collector. -/
theorem collectPEHazardConstraintsAux_mem_has_event_pair
    (earlier : List TimedPEAccess) (remaining : List (List TimedPEAccess))
    (constraint : PEHazardConstraint)
    (member : constraint ∈ collectPEHazardConstraintsAux earlier remaining) :
    ∃ (prior current : List TimedPEAccess) (write access : TimedPEAccess),
      write ∈ prior ∧ access ∈ current ∧
      makePEHazardConstraint? write access = some constraint ∧
      access.startWord - write.startWord ≤ 4 := by
  obtain ⟨prior, current, betweenMember⟩ :=
    collectPEHazardConstraintsAux_mem_has_emitting_groups
      earlier remaining constraint member
  obtain ⟨write, writeMember, access, accessMember, generated⟩ :=
    (pe_hazard_constraints_between_complete prior current constraint).mp betweenMember
  cases made : makePEHazardConstraint? write access with
  | none => simp [made] at generated
  | some candidate =>
      simp only [made] at generated
      split at generated
      · rename_i withinWindow
        cases generated
        exact ⟨prior, current, write, access, writeMember, accessMember,
          made, withinWindow⟩
      · simp at generated

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

/-- Passing the list-level check implies each modeled write/read pair meets its
rule-specific distance whenever that pair emitted a constraint. -/
theorem pe_hazard_checked_constraint_matches_pair_safety
    (constraints : List PEHazardConstraint) (earlier later : TimedPEAccess)
    (constraint : PEHazardConstraint)
    (member : constraint ∈ constraints)
    (made : makePEHazardConstraint? earlier later = some constraint)
    (noViolations : violatingPEHazardConstraints constraints = []) :
    peHazardSatisfied earlier later := by
  have safeDistance := pe_hazard_no_violations_satisfies_constraints
    constraints noViolations constraint member
  have pairRelation := pe_hazard_constraint_violation_matches_pair_safety
    earlier later constraint made
  by_cases safe : peHazardSatisfied earlier later
  · exact safe
  · have violated := pairRelation.mpr safe
    simp [PEHazardConstraint.violated] at safeDistance violated
    omega

/-- A source-level empty hazard report certifies that each reported constraint
comes from concrete events in two issue groups and that the corresponding
write/read pair satisfies the modeled distance rule. -/
theorem parsedSourcePEHazardViolations_empty_certifies_pairs
    (source : List ParsedMaskedSourceStatement) (control : ParsedMaskExecutionControl)
    (events : List (List TimedPEAccess))
    (eventsGenerated : parsedSourcePEHazardEvents? source control = some events)
    (noViolations : parsedSourcePEHazardViolations? source control = some [])
    (constraint : PEHazardConstraint)
    (member : constraint ∈ collectPEHazardConstraints events) :
    ∃ (prior current : List TimedPEAccess) (write access : TimedPEAccess),
      write ∈ prior ∧ access ∈ current ∧
      makePEHazardConstraint? write access = some constraint ∧
      access.startWord - write.startWord ≤ 4 ∧
      peHazardSatisfied write access := by
  have noGeneratedViolations :
      violatingPEHazardConstraints (collectPEHazardConstraints events) = [] := by
    simpa [parsedSourcePEHazardViolations?, parsedSourcePEHazardConstraints?,
      eventsGenerated] using noViolations
  obtain ⟨prior, current, write, access, writeMember, accessMember, made, withinWindow⟩ :=
    collectPEHazardConstraintsAux_mem_has_event_pair [] events constraint member
  exact ⟨prior, current, write, access, writeMember, accessMember, made, withinWindow,
    pe_hazard_checked_constraint_matches_pair_safety
      (collectPEHazardConstraints events) write access constraint member made
      noGeneratedViolations⟩

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

def prepareParsedMaskedIntegerWrites (files : IntegerRegisterFiles)
    (accesses : List ParsedMaskedIntegerAccesses) (reduced : Bool) :
    ProofsLean.StepResult (List PreparedParsedMaskedWrite) :=
  match accesses with
  | [] => .ok []
  | access :: rest =>
      match prepareParsedMaskedWrite files access reduced with
      | .failure => .failure
      | .unknown => .unknown
      | .ok write =>
          match prepareParsedMaskedIntegerWrites files rest reduced with
          | .failure => .failure
          | .unknown => .unknown
          | .ok writes => .ok (write :: writes)

def traverseStepResult {α β : Type} (f : α → ProofsLean.StepResult β) :
    List α → ProofsLean.StepResult (List β)
  | [] => .ok []
  | value :: rest =>
      match f value with
      | .failure => .failure
      | .unknown => .unknown
      | .ok head =>
          match traverseStepResult f rest with
          | .failure => .failure
          | .unknown => .unknown
          | .ok tail => .ok (head :: tail)

theorem prepareParsedMaskedIntegerWrites_preserves_order
    (files : IntegerRegisterFiles) (access : ParsedMaskedIntegerAccesses)
    (rest : List ParsedMaskedIntegerAccesses) (reduced : Bool)
    (write : PreparedParsedMaskedWrite) (writes : List PreparedParsedMaskedWrite)
    (headReady : prepareParsedMaskedWrite files access reduced = .ok write)
    (tailReady : prepareParsedMaskedIntegerWrites files rest reduced = .ok writes) :
    prepareParsedMaskedIntegerWrites files (access :: rest) reduced = .ok (write :: writes) := by
  simp [prepareParsedMaskedIntegerWrites, headReady, tailReady]

theorem prepareParsedMaskedIntegerWrites_is_traverse (files : IntegerRegisterFiles)
    (accesses : List ParsedMaskedIntegerAccesses) (reduced : Bool) :
    prepareParsedMaskedIntegerWrites files accesses reduced =
      traverseStepResult
        (fun access => prepareParsedMaskedWrite files access reduced) accesses := by
  induction accesses with
  | nil => rfl
  | cons access rest ih =>
      cases h : prepareParsedMaskedWrite files access reduced with
      | failure => simp [prepareParsedMaskedIntegerWrites, traverseStepResult, h]
      | unknown => simp [prepareParsedMaskedIntegerWrites, traverseStepResult, h]
      | ok write =>
          cases htail : traverseStepResult
              (fun access => prepareParsedMaskedWrite files access reduced) rest with
          | failure =>
              simp [prepareParsedMaskedIntegerWrites, traverseStepResult, h, htail, ih]
          | unknown =>
              simp [prepareParsedMaskedIntegerWrites, traverseStepResult, h, htail, ih]
          | ok writes =>
              simp [prepareParsedMaskedIntegerWrites, traverseStepResult, h, htail, ih]

def prepareParsedMaskedIntegerWritesWithForwarding (files : IntegerRegisterFiles)
    (slots : ProofsLean.MNCore.Forwarding.Slots) (cycle : Fin 4)
    (accesses : List ParsedMaskedIntegerAccesses) (reduced : Bool) :
    ProofsLean.StepResult (List PreparedParsedMaskedWrite) :=
  match accesses with
  | [] => .ok []
  | access :: rest =>
      match prepareParsedMaskedWriteWithForwarding files slots cycle access reduced with
      | .failure => .failure
      | .unknown => .unknown
      | .ok write =>
          match prepareParsedMaskedIntegerWritesWithForwarding
              files slots cycle rest reduced with
          | .failure => .failure
          | .unknown => .unknown
          | .ok writes => .ok (write :: writes)

theorem prepareParsedMaskedIntegerWritesWithForwarding_preserves_order
    (files : IntegerRegisterFiles) (slots : ProofsLean.MNCore.Forwarding.Slots)
    (cycle : Fin 4) (access : ParsedMaskedIntegerAccesses)
    (rest : List ParsedMaskedIntegerAccesses) (reduced : Bool)
    (write : PreparedParsedMaskedWrite) (writes : List PreparedParsedMaskedWrite)
    (headReady : prepareParsedMaskedWriteWithForwarding files slots cycle access reduced =
      .ok write)
    (tailReady : prepareParsedMaskedIntegerWritesWithForwarding
      files slots cycle rest reduced = .ok writes) :
    prepareParsedMaskedIntegerWritesWithForwarding files slots cycle
      (access :: rest) reduced = .ok (write :: writes) := by
  simp [prepareParsedMaskedIntegerWritesWithForwarding, headReady, tailReady]

theorem prepareParsedMaskedIntegerWritesWithForwarding_is_traverse
    (files : IntegerRegisterFiles) (slots : ProofsLean.MNCore.Forwarding.Slots)
    (cycle : Fin 4) (accesses : List ParsedMaskedIntegerAccesses) (reduced : Bool) :
    prepareParsedMaskedIntegerWritesWithForwarding files slots cycle accesses reduced =
      traverseStepResult (fun access =>
        prepareParsedMaskedWriteWithForwarding files slots cycle access reduced) accesses := by
  induction accesses with
  | nil => rfl
  | cons access rest ih =>
      cases h : prepareParsedMaskedWriteWithForwarding files slots cycle access reduced with
      | failure =>
          simp [prepareParsedMaskedIntegerWritesWithForwarding, traverseStepResult, h]
      | unknown =>
          simp [prepareParsedMaskedIntegerWritesWithForwarding, traverseStepResult, h]
      | ok write =>
          cases htail : traverseStepResult
              (fun access => prepareParsedMaskedWriteWithForwarding files slots cycle access reduced)
              rest with
          | failure =>
              simp [prepareParsedMaskedIntegerWritesWithForwarding,
                traverseStepResult, h, htail, ih]
          | unknown =>
              simp [prepareParsedMaskedIntegerWritesWithForwarding,
                traverseStepResult, h, htail, ih]
          | ok writes =>
              simp [prepareParsedMaskedIntegerWritesWithForwarding,
                traverseStepResult, h, htail, ih]

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
          match ParsedExpr.toDirectMaskedIntegerWritesInLine? expression files.maskRegisters
              control.directive hasSingleLineMask control.context.group control.context.l2b
              control.context.l1b control.context.mab control.context.pe control.context.cycle
              control.context.bar0 control.context.bar1 control.context.tWord with
          | none => .unknown
          | some accesses =>
              match prepareParsedMaskedIntegerWrites files accesses false with
              | .failure => .failure
              | .unknown => .unknown
              | .ok lineWrites =>
                  match prepare rest with
                  | .ok writes => .ok (lineWrites ++ writes)
                  | .failure => .failure
                  | .unknown => .unknown
  prepare expressions

def prepareParsedMaskedLineWithForwarding (files : IntegerRegisterFiles)
    (slots : ProofsLean.MNCore.Forwarding.Slots)
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
          | some targets =>
              match prepareParsedMaskedConstantWrites files control.context.cycle targets with
              | .failure => .failure
              | .unknown => .unknown
              | .ok writes =>
                  match prepare rest with
                  | .ok tail => .ok (writes ++ tail)
                  | .failure => .failure
                  | .unknown => .unknown
        | _ =>
          match ParsedExpr.toDirectMaskedIntegerWritesInLine? expression
              files.maskRegisters control.directive hasSingleLineMask
              control.context.group control.context.l2b control.context.l1b control.context.mab
              control.context.pe control.context.cycle control.context.bar0 control.context.bar1
              control.context.tWord with
          | none => .unknown
          | some accesses =>
              match prepareParsedMaskedIntegerWritesWithForwarding files slots
                  control.context.cycle accesses false with
              | .failure => .failure
              | .unknown => .unknown
              | .ok lineWrites =>
                  match prepare rest with
                  | .ok tail => .ok (lineWrites ++ tail)
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

theorem commitParsedMaskedWrites_append (files : IntegerRegisterFiles)
    (first second : List PreparedParsedMaskedWrite) :
    commitParsedMaskedWrites files (first ++ second) =
      commitParsedMaskedWrites (commitParsedMaskedWrites files first) second := by
  simp [commitParsedMaskedWrites, List.foldl_append]

def updateParsedMatrixReadForwardingCycle
    (old : ProofsLean.MNCore.Forwarding.Slots) (cycle : Fin 4)
    (output : IntegerALU.Bus) (noForward : Bool) :
    ProofsLean.MNCore.Forwarding.Slots :=
  if noForward then old else fun unit slotCycle =>
    if unit = .matrixRead ∧ slotCycle = cycle then .known output else old unit slotCycle

theorem updateParsedMatrixReadForwardingCycle_semantics
    (old : ProofsLean.MNCore.Forwarding.Slots) (cycle : Fin 4)
    (output : IntegerALU.Bus) (noForward : Bool) :
    updateParsedMatrixReadForwardingCycle old cycle output noForward =
      if noForward then old else fun unit slotCycle =>
        if unit = .matrixRead ∧ slotCycle = cycle then .known output else old unit slotCycle := by
  cases noForward <;> rfl

theorem updateParsedMatrixReadForwardingCycle_reads_back
    (files : IntegerRegisterFiles) (old : ProofsLean.MNCore.Forwarding.Slots)
    (cycle : Fin 4) (output : IntegerALU.Bus) :
    ParsedIntegerInput.readWithForwarding files
      (updateParsedMatrixReadForwardingCycle old cycle output false)
      cycle (.forward .mreadf false) = .ok output := by
  simp [updateParsedMatrixReadForwardingCycle, ParsedIntegerInput.readWithForwarding,
    ParsedIntegerInput.forwardUnit, ParsedIntegerInput.applyRounding]

def prepareParsedMatrixReadTargets (targets : List ParsedMatrixReadTarget)
    (output : IntegerALU.Bus) : ProofsLean.StepResult (List PreparedParsedMaskedWrite) :=
  match targets with
  | [] => .ok []
  | .noWrite :: rest =>
      match prepareParsedMatrixReadTargets rest output with
      | .failure => .failure
      | .unknown => .unknown
      | .ok writes =>
          .ok (⟨none, none, unpackALUBus output, ⟨BitVec.allOnes 4, true⟩⟩ :: writes)
  | .memory access selection :: rest =>
      match prepareParsedMatrixReadTargets rest output with
      | .failure => .failure
      | .unknown => .unknown
      | .ok writes =>
          .ok (⟨some access, none, unpackALUBus output, selection⟩ :: writes)

/-- Prepare one cycle of a parsed matrix-read expression. -/
def prepareParsedMatrixReadCycle (files : IntegerRegisterFiles)
    (slots : ProofsLean.MNCore.Forwarding.Slots) (store : ParsedMatrixReadStore)
    (expression : ParsedExpr) (directive : ParsedMaskDirective)
    (hasSingleLineMask noForward : Bool) (context : ParsedIntegerContext) :
    ProofsLean.StepResult (List PreparedParsedMaskedWrite ×
      ProofsLean.MNCore.Forwarding.Slots) :=
  match ParsedExpr.toDirectMatrixReadAccesses? expression files.maskRegisters
      directive hasSingleLineMask context with
  | none => .unknown
  | some accesses =>
      match resolveFlushSelection? expression.flush files.maskRegisters context.cycle with
      | none => .unknown
      | some flushSelection =>
          let output := parsedOutputAfterFlush flushSelection
            (parsedMatrixReadBus store accesses context)
          match prepareParsedMatrixReadTargets accesses.targets output with
          | .failure => .failure
          | .unknown => .unknown
          | .ok writes =>
              .ok (writes, updateParsedMatrixReadForwardingCycle
                slots context.cycle output noForward)

def parsedMatrixReadCycleStep (files : IntegerRegisterFiles)
    (slots : ProofsLean.MNCore.Forwarding.Slots) (store : ParsedMatrixReadStore)
    (expression : ParsedExpr) (directive : ParsedMaskDirective)
    (hasSingleLineMask noForward : Bool) (context : ParsedIntegerContext) :
    ProofsLean.StepResult (IntegerRegisterFiles × ProofsLean.MNCore.Forwarding.Slots) :=
  match prepareParsedMatrixReadCycle files slots store expression directive
      hasSingleLineMask noForward context with
  | .failure => .failure
  | .unknown => .unknown
  | .ok (writes, nextSlots) =>
      .ok (commitParsedMaskedWrites files writes, nextSlots)

theorem parsedMatrixReadCycleStep_output_forwardable
    (files : IntegerRegisterFiles) (slots : ProofsLean.MNCore.Forwarding.Slots)
    (store : ParsedMatrixReadStore) (expression : ParsedExpr)
    (directive : ParsedMaskDirective) (hasSingleLineMask : Bool)
    (context : ParsedIntegerContext) (accesses : ParsedMatrixReadAccesses)
    (flushSelection : Option PEWordSelection) (writes : List PreparedParsedMaskedWrite)
    (lowered : ParsedExpr.toDirectMatrixReadAccesses? expression files.maskRegisters
      directive hasSingleLineMask context = some accesses)
    (flushResolved : resolveFlushSelection? expression.flush files.maskRegisters context.cycle =
      some flushSelection)
    (writesReady : prepareParsedMatrixReadTargets accesses.targets
      (parsedOutputAfterFlush flushSelection (parsedMatrixReadBus store accesses context)) =
        .ok writes) :
    ∃ nextFiles nextSlots,
      parsedMatrixReadCycleStep files slots store expression directive hasSingleLineMask false
        context = .ok (nextFiles, nextSlots) ∧
      ParsedIntegerInput.readWithForwarding files nextSlots context.cycle
        (.forward .mreadf false) =
          .ok (parsedOutputAfterFlush flushSelection (parsedMatrixReadBus store accesses context)) := by
  refine ⟨commitParsedMaskedWrites files writes,
    updateParsedMatrixReadForwardingCycle slots context.cycle
      (parsedOutputAfterFlush flushSelection (parsedMatrixReadBus store accesses context)) false,
    ?_, ?_⟩
  · simp [parsedMatrixReadCycleStep, prepareParsedMatrixReadCycle,
      lowered, flushResolved, writesReady]
  · exact updateParsedMatrixReadForwardingCycle_reads_back files slots context.cycle _

def parsedMatrixReadCycles : List (Fin 4) := [0, 1, 2, 3]

/-- Prepare one matrix-read expression across all four cycles using the old
PE-memory and matrix state, then commit the cycle-ordered destination writes. -/
def prepareParsedMatrixReadExprCycles (files : IntegerRegisterFiles)
    (initialSlots : ProofsLean.MNCore.Forwarding.Slots) (store : ParsedMatrixReadStore)
    (expression : ParsedExpr) (directive : ParsedMaskDirective)
    (hasSingleLineMask noForward : Bool) (context : ParsedIntegerContext) :
    ProofsLean.StepResult (List PreparedParsedMaskedWrite ×
      ProofsLean.MNCore.Forwarding.Slots) :=
  let rec prepare (cycles : List (Fin 4))
      (writes : List PreparedParsedMaskedWrite)
      (nextSlots : ProofsLean.MNCore.Forwarding.Slots) :=
    match cycles with
    | [] => .ok (writes, nextSlots)
    | cycle :: rest =>
        let cycleContext := { context with cycle := cycle }
        match prepareParsedMatrixReadCycle files nextSlots store expression directive
            hasSingleLineMask noForward cycleContext with
        | .failure => .failure
        | .unknown => .unknown
        | .ok (cycleWrites, cycleSlots) =>
            prepare rest (writes ++ cycleWrites) cycleSlots
  prepare parsedMatrixReadCycles [] initialSlots

def parsedMatrixReadExprFourCycleStep (files : IntegerRegisterFiles)
    (slots : ProofsLean.MNCore.Forwarding.Slots) (store : ParsedMatrixReadStore)
    (expression : ParsedExpr) (directive : ParsedMaskDirective)
    (hasSingleLineMask noForward : Bool) (context : ParsedIntegerContext) :
    ProofsLean.StepResult (IntegerRegisterFiles × ProofsLean.MNCore.Forwarding.Slots) :=
  match prepareParsedMatrixReadExprCycles files slots store expression directive
      hasSingleLineMask noForward context with
  | .failure => .failure
  | .unknown => .unknown
  | .ok (writes, nextSlots) =>
      .ok (commitParsedMaskedWrites files writes, nextSlots)

/-- Update the ALU forwarding value for one cycle from an already prepared
integer ALU result. `data` is the post-flush four-word bus; the flag controls
the architectural noforward behavior for this producer. This primitive does
not summarize other producers or execute the other three cycles. -/
def updateParsedIntegerALUForwardingCycle
    (old : ProofsLean.MNCore.Forwarding.Slots) (cycle : Fin 4)
    (prepared : ProofsLean.StepResult PreparedParsedMaskedWrite) (noForward : Bool) :
    ProofsLean.StepResult ProofsLean.MNCore.Forwarding.Slots :=
  match prepared with
  | .failure => .failure
  | .unknown => .unknown
  | .ok write =>
      if noForward then .ok old
      else .ok (fun unit slotCycle =>
        if unit = .alu ∧ slotCycle = cycle then
          .known (pack write.data)
        else old unit slotCycle)

theorem updateParsedIntegerALUForwardingCycle_semantics
    (old : ProofsLean.MNCore.Forwarding.Slots) (cycle : Fin 4)
    (write : PreparedParsedMaskedWrite) (noForward : Bool) :
    updateParsedIntegerALUForwardingCycle old cycle (.ok write) noForward =
      if noForward then .ok old else .ok (fun unit slotCycle =>
        if unit = .alu ∧ slotCycle = cycle then
          .known (pack write.data)
        else old unit slotCycle) := by
  cases noForward <;> rfl

theorem updateParsedIntegerALUForwardingCycle_reads_back
    (files : IntegerRegisterFiles) (old : ProofsLean.MNCore.Forwarding.Slots)
    (cycle : Fin 4) (write : PreparedParsedMaskedWrite) :
    ParsedIntegerInput.readWithForwarding files
      (fun unit slotCycle =>
        if unit = .alu ∧ slotCycle = cycle then
          .known (pack write.data)
        else old unit slotCycle)
      cycle (.forward .aluf false) = .ok (pack write.data) := by
  simp [ParsedIntegerInput.readWithForwarding, ParsedIntegerInput.forwardUnit,
    ParsedIntegerInput.applyRounding]

/-- Single-expression, single-cycle integer ALU transition. The register write
and ALU forwarding update consume the same prepared, post-flush result. -/
def parsedIntegerMaskedALUAndForwardingCycleStep
    (files : IntegerRegisterFiles) (slots : ProofsLean.MNCore.Forwarding.Slots)
    (cycle : Fin 4) (accesses : ParsedMaskedIntegerAccesses) (reduced noForward : Bool) :
    ProofsLean.StepResult (IntegerRegisterFiles × ProofsLean.MNCore.Forwarding.Slots) :=
  match prepareParsedMaskedWriteWithForwarding files slots cycle accesses reduced with
  | .failure => .failure
  | .unknown => .unknown
  | .ok write =>
      match updateParsedIntegerALUForwardingCycle slots cycle (.ok write) noForward with
      | .failure => .failure
      | .unknown => .unknown
      | .ok nextSlots =>
          .ok (commitParsedMaskedWrites files [write], nextSlots)

theorem parsedIntegerMaskedALUAndForwardingCycleStep_prepares_once
    (files : IntegerRegisterFiles) (slots : ProofsLean.MNCore.Forwarding.Slots)
    (cycle : Fin 4) (accesses : ParsedMaskedIntegerAccesses) (reduced noForward : Bool) :
    parsedIntegerMaskedALUAndForwardingCycleStep files slots cycle accesses reduced noForward =
      match prepareParsedMaskedWriteWithForwarding files slots cycle accesses reduced with
      | .failure => .failure
      | .unknown => .unknown
      | .ok write =>
          match updateParsedIntegerALUForwardingCycle slots cycle (.ok write) noForward with
          | .failure => .failure
          | .unknown => .unknown
          | .ok nextSlots =>
              .ok (commitParsedMaskedWrites files [write], nextSlots) := rfl

def parsedIntegerALUCycles : List (Fin 4) := [0, 1, 2, 3]

/-- Prepare one parsed integer ALU expression for all four PE cycles. Each
cycle reads the same pre-issue register files and forwarding slots; only the
accumulated output slots change. This preserves issue-line read-before-write. -/
def prepareParsedIntegerALUExprCycles (files : IntegerRegisterFiles)
    (oldSlots : ProofsLean.MNCore.Forwarding.Slots)
    (initialOutputSlots : ProofsLean.MNCore.Forwarding.Slots)
    (expression : ParsedExpr) (control : ParsedMaskExecutionControl)
    (hasSingleLineMask noForward reduced : Bool) :
    ProofsLean.StepResult
      (List PreparedParsedMaskedWrite × ProofsLean.MNCore.Forwarding.Slots) :=
  let rec prepare (cycles : List (Fin 4))
      (writes : List PreparedParsedMaskedWrite)
      (nextSlots : ProofsLean.MNCore.Forwarding.Slots) :=
    match cycles with
    | [] => ProofsLean.StepResult.ok (writes, nextSlots)
    | cycle :: rest =>
        let cycleControl := { control with context := { control.context with cycle := cycle } }
        match expression.op with
        | .alu .. =>
            match ParsedExpr.toDirectMaskedIntegerAccessesInLine? expression
                files.maskRegisters cycleControl.directive hasSingleLineMask
                cycleControl.context.group cycleControl.context.l2b cycleControl.context.l1b
                cycleControl.context.mab cycleControl.context.pe cycle
                cycleControl.context.bar0 cycleControl.context.bar1 cycleControl.context.tWord with
            | none => ProofsLean.StepResult.unknown
            | some accesses =>
                match prepareParsedMaskedWriteWithForwarding files oldSlots cycle accesses reduced with
                | .failure => ProofsLean.StepResult.failure
                | .unknown => ProofsLean.StepResult.unknown
                | .ok write =>
                    match updateParsedIntegerALUForwardingCycle nextSlots cycle
                        (.ok write) noForward with
                    | .failure => ProofsLean.StepResult.failure
                    | .unknown => ProofsLean.StepResult.unknown
                    | .ok updatedSlots => prepare rest (writes ++ [write]) updatedSlots
        | .zero | .immediate .. =>
            match ParsedExpr.toDirectMaskedConstantWrites? expression files.maskRegisters
                cycleControl.directive hasSingleLineMask cycleControl.context.group
                cycleControl.context.l2b cycleControl.context.l1b cycleControl.context.mab
                cycleControl.context.pe cycle cycleControl.context.bar0 cycleControl.context.bar1
                cycleControl.context.tWord with
            | none => ProofsLean.StepResult.unknown
            | some targets =>
                match prepareParsedMaskedConstantWrites files cycle targets with
                | .failure => ProofsLean.StepResult.failure
                | .unknown => ProofsLean.StepResult.unknown
                | .ok destinationWrites =>
                    match expression.op.executionRequest with
                    | .ok request =>
                        match resolveFlushSelection? expression.flush files.maskRegisters cycle with
                        | none => ProofsLean.StepResult.unknown
                        | some flushSelection =>
                            let output := evaluateParsedExecutionRequest request
                              ⟨0, 0⟩ ⟨0, 0⟩ reduced
                            let outputBus := parsedOutputAfterFlush flushSelection output.value
                            let producerWrite : PreparedParsedMaskedWrite :=
                              ⟨none, none, unpackALUBus outputBus,
                                ⟨BitVec.allOnes 4, true⟩⟩
                            match updateParsedIntegerALUForwardingCycle nextSlots cycle
                                (.ok producerWrite) noForward with
                            | .failure => ProofsLean.StepResult.failure
                            | .unknown => ProofsLean.StepResult.unknown
                            | .ok updatedSlots =>
                                prepare rest
                                  (writes ++ destinationWrites ++ [producerWrite]) updatedSlots
                    | .failure => ProofsLean.StepResult.failure
                    | .unknown => ProofsLean.StepResult.unknown
        | _ => ProofsLean.StepResult.unknown
  prepare parsedIntegerALUCycles [] initialOutputSlots

/-- Four-cycle execution of one integer ALU expression, including its
cycle-indexed `aluf` outputs. Other expressions and producer units remain
outside this transition. -/
def parsedIntegerALUExprFourCycleStep (files : IntegerRegisterFiles)
    (slots : ProofsLean.MNCore.Forwarding.Slots)
    (expression : ParsedExpr) (control : ParsedMaskExecutionControl)
    (hasSingleLineMask noForward reduced : Bool) :
    ProofsLean.StepResult (IntegerRegisterFiles × ProofsLean.MNCore.Forwarding.Slots) :=
  match prepareParsedIntegerALUExprCycles files slots slots expression control
      hasSingleLineMask noForward reduced with
  | .failure => .failure
  | .unknown => .unknown
  | .ok (writes, nextSlots) =>
      .ok (commitParsedMaskedWrites files writes, nextSlots)

/-- Four-cycle issue-line transition for integer ALU, zero, and immediate
producers. All
expressions read the same old files and slots. Writes are accumulated in
expression-major, then cycle-major order, matching the executor's per-output
write loop. Repeated ALU producers overwrite the same cycle slot in source
order, so the last producer wins. -/
def prepareParsedALUProducerLineCycles (files : IntegerRegisterFiles)
    (oldSlots : ProofsLean.MNCore.Forwarding.Slots)
    (expressions : List ParsedExpr) (control : ParsedMaskExecutionControl)
    (hasSingleLineMask noForward reduced : Bool) :
    ProofsLean.StepResult
      (List PreparedParsedMaskedWrite × ProofsLean.MNCore.Forwarding.Slots) :=
  let rec prepare (remaining : List ParsedExpr)
      (writes : List PreparedParsedMaskedWrite)
      (nextSlots : ProofsLean.MNCore.Forwarding.Slots) :=
    match remaining with
    | [] => ProofsLean.StepResult.ok (writes, nextSlots)
    | expression :: rest =>
        match expression.op with
        | .wait _ | .noforward => prepare rest writes nextSlots
        | .alu .. | .zero | .immediate .. =>
            match prepareParsedIntegerALUExprCycles files oldSlots nextSlots expression
                control hasSingleLineMask noForward reduced with
            | .failure => ProofsLean.StepResult.failure
            | .unknown => ProofsLean.StepResult.unknown
            | .ok (expressionWrites, expressionSlots) =>
                prepare rest (writes ++ expressionWrites) expressionSlots
        | _ => ProofsLean.StepResult.unknown
  prepare expressions [] oldSlots

def parsedALUProducerLineFourCycleStep (files : IntegerRegisterFiles)
    (slots : ProofsLean.MNCore.Forwarding.Slots)
    (expressions : List ParsedExpr) (control : ParsedMaskExecutionControl)
    (reduced : Bool) :
    ProofsLean.StepResult (IntegerRegisterFiles × ProofsLean.MNCore.Forwarding.Slots) :=
  let hasSingleLineMask := expressions.any parsedExprHasSingleLineWriteMask
  let noForward := expressions.any fun expression =>
    match expression.op with
    | .noforward => true
    | _ => false
  match prepareParsedALUProducerLineCycles files slots expressions control
      hasSingleLineMask noForward reduced with
  | .failure => .failure
  | .unknown => .unknown
  | .ok (writes, nextSlots) =>
      .ok (commitParsedMaskedWrites files writes, nextSlots)

/-- Issue-checked entrypoint for the currently modeled ALU/constant line
subset. A line rejected by the local PE issue checker is kept unresolved;
the checker is not claimed to cover parser or assembler legality. -/
noncomputable def parsedIssueCheckedALUProducerLineFourCycleStep (files : IntegerRegisterFiles)
    (slots : ProofsLean.MNCore.Forwarding.Slots)
    (expressions : List ParsedExpr) (control : ParsedMaskExecutionControl)
    (reduced : Bool) :
    ProofsLean.StepResult (IntegerRegisterFiles × ProofsLean.MNCore.Forwarding.Slots) :=
  if checkParsedLine expressions then
    parsedALUProducerLineFourCycleStep files slots expressions control reduced
  else .unknown

theorem parsedIssueCheckedALUProducerLineFourCycleStep_accepted
    (files : IntegerRegisterFiles) (slots : ProofsLean.MNCore.Forwarding.Slots)
    (expressions : List ParsedExpr) (control : ParsedMaskExecutionControl)
    (reduced : Bool)
    (accepted : checkParsedLine expressions = true) :
    parsedIssueCheckedALUProducerLineFourCycleStep files slots expressions control reduced =
      parsedALUProducerLineFourCycleStep files slots expressions control reduced ∧
        LegalParsedLine expressions := by
  constructor
  · simp [parsedIssueCheckedALUProducerLineFourCycleStep, accepted]
  · exact parsed_check_sound expressions accepted

theorem parsedIssueCheckedALUProducerLineFourCycleStep_rejects
    (files : IntegerRegisterFiles) (slots : ProofsLean.MNCore.Forwarding.Slots)
    (expressions : List ParsedExpr) (control : ParsedMaskExecutionControl)
    (reduced : Bool)
    (rejected : checkParsedLine expressions = false) :
    parsedIssueCheckedALUProducerLineFourCycleStep files slots expressions control reduced =
      .unknown := by
  simp [parsedIssueCheckedALUProducerLineFourCycleStep, rejected]

/-- Four-cycle line execution for the parsed integer ALU/constant and matrix
read producers. Every expression reads pre-issue PE memory and matrix words;
forwarding outputs accumulate by expression order, and writes commit at end. -/
def prepareParsedIntegerMatrixReadLineCycles (files : IntegerRegisterFiles)
    (oldSlots : ProofsLean.MNCore.Forwarding.Slots) (store : ParsedMatrixReadStore)
    (expressions : List ParsedExpr) (control : ParsedMaskExecutionControl)
    (reduced : Bool) :
    ProofsLean.StepResult (List PreparedParsedMaskedWrite ×
      ProofsLean.MNCore.Forwarding.Slots) :=
  let hasSingleLineMask := expressions.any parsedExprHasSingleLineWriteMask
  let noForward := expressions.any fun expression =>
    match expression.op with
    | .noforward => true
    | _ => false
  let rec prepare (remaining : List ParsedExpr)
      (writes : List PreparedParsedMaskedWrite)
      (nextSlots : ProofsLean.MNCore.Forwarding.Slots) :=
    match remaining with
    | [] => .ok (writes, nextSlots)
    | expression :: rest =>
        match expression.op with
        | .wait _ | .noforward => prepare rest writes nextSlots
        | .alu .. | .zero | .immediate .. =>
            match prepareParsedIntegerALUExprCycles files oldSlots nextSlots expression
                control hasSingleLineMask noForward reduced with
            | .failure => .failure
            | .unknown => .unknown
            | .ok (expressionWrites, expressionSlots) =>
                prepare rest (writes ++ expressionWrites) expressionSlots
        | .matrixRead .. =>
            match prepareParsedMatrixReadExprCycles files nextSlots store expression
                control.directive hasSingleLineMask noForward control.context with
            | .failure => .failure
            | .unknown => .unknown
            | .ok (expressionWrites, expressionSlots) =>
                prepare rest (writes ++ expressionWrites) expressionSlots
        | _ => .unknown
  prepare expressions [] oldSlots

def parsedIntegerMatrixReadLineFourCycleStep (files : IntegerRegisterFiles)
    (slots : ProofsLean.MNCore.Forwarding.Slots) (store : ParsedMatrixReadStore)
    (expressions : List ParsedExpr) (control : ParsedMaskExecutionControl)
    (reduced : Bool) :
    ProofsLean.StepResult (IntegerRegisterFiles × ProofsLean.MNCore.Forwarding.Slots) :=
  match prepareParsedIntegerMatrixReadLineCycles files slots store expressions control reduced with
  | .failure => .failure
  | .unknown => .unknown
  | .ok (writes, nextSlots) =>
      .ok (commitParsedMaskedWrites files writes, nextSlots)

theorem parsedIntegerALUCycles_complete :
    parsedIntegerALUCycles = [0, 1, 2, 3] := rfl

def parsedIntegerMaskedLineStepWithForwarding (files : IntegerRegisterFiles)
    (slots : ProofsLean.MNCore.Forwarding.Slots)
    (expressions : List ParsedExpr) (control : ParsedMaskExecutionControl) :
    ProofsLean.StepResult IntegerRegisterFiles :=
  match prepareParsedMaskedLineWithForwarding files slots expressions control with
  | .ok writes => .ok (commitParsedMaskedWrites files writes)
  | .failure => .failure
  | .unknown => .unknown

theorem parsedIntegerMaskedLineStepWithForwarding_prepares_then_commits
    (files : IntegerRegisterFiles) (slots : ProofsLean.MNCore.Forwarding.Slots)
    (expressions : List ParsedExpr) (control : ParsedMaskExecutionControl) :
    parsedIntegerMaskedLineStepWithForwarding files slots expressions control =
      match prepareParsedMaskedLineWithForwarding files slots expressions control with
      | .ok writes => .ok (commitParsedMaskedWrites files writes)
      | .failure => .failure
      | .unknown => .unknown := rfl

def parsedIntegerMaskedRegisterStepWithForwarding (files : IntegerRegisterFiles)
    (slots : ProofsLean.MNCore.Forwarding.Slots) (cycle : Fin 4)
    (accesses : ParsedMaskedIntegerAccesses) (reduced : Bool) :
    ProofsLean.StepResult IntegerRegisterFiles :=
  match prepareParsedMaskedWriteWithForwarding files slots cycle accesses reduced with
  | .ok write => .ok (commitParsedMaskedWrites files [write])
  | .failure => .failure
  | .unknown => .unknown

def executeParsedMaskedIntegerExprWithForwarding? (files : IntegerRegisterFiles)
    (slots : ProofsLean.MNCore.Forwarding.Slots) (expression : ParsedExpr)
    (directive : ParsedMaskDirective)
    (group : Fin 2) (l2b : Fin 2) (l1b : Fin 8) (mab : Fin 16)
    (pe cycle : Fin 4) (bar0 bar1 : BitVec 12) (tWord : BitVec 32) :
    Option (ProofsLean.StepResult IntegerRegisterFiles) :=
  match ParsedExpr.toDirectMaskedIntegerAccesses? expression files.maskRegisters
      directive group l2b l1b mab pe cycle bar0 bar1 tWord with
  | some accesses =>
      some (parsedIntegerMaskedRegisterStepWithForwarding files slots cycle accesses false)
  | none => none

theorem executeParsedMaskedIntegerExprWithForwarding?_uses_lowering
    (files : IntegerRegisterFiles) (slots : ProofsLean.MNCore.Forwarding.Slots)
    (expression : ParsedExpr) (directive : ParsedMaskDirective)
    (group : Fin 2) (l2b : Fin 2) (l1b : Fin 8) (mab : Fin 16)
    (pe cycle : Fin 4) (bar0 bar1 : BitVec 12) (tWord : BitVec 32)
    (accesses : ParsedMaskedIntegerAccesses)
    (lowered : ParsedExpr.toDirectMaskedIntegerAccesses? expression files.maskRegisters
      directive group l2b l1b mab pe cycle bar0 bar1 tWord = some accesses) :
    executeParsedMaskedIntegerExprWithForwarding? files slots expression directive
      group l2b l1b mab pe cycle bar0 bar1 tWord =
        some (parsedIntegerMaskedRegisterStepWithForwarding files slots cycle accesses false) := by
  simp [executeParsedMaskedIntegerExprWithForwarding?, lowered]

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

def lowerParsedMaskedSource : List ParsedLine →
    Option (List ParsedMaskedSourceStatement)
  | [] => some []
  | line :: rest => do
      let head ← ParsedLine.toParsedMaskedStatements? line
      let tail ← lowerParsedMaskedSource rest
      pure (head ++ tail)

def ParsedLine.parsedMaskedIssueWords? : ParsedLine → Option Nat
  | .pe _ => some 1
  | .mv _ => some 1
  | .nop count _ => some count
  | .maskDirective _ _ _ => some 0
  | _ => none

def parsedMaskedIssueWordTotal? : List ParsedLine → Option Nat
  | [] => some 0
  | line :: rest => do
      let lineWords ← ParsedLine.parsedMaskedIssueWords? line
      let restWords ← parsedMaskedIssueWordTotal? rest
      pure (lineWords + restWords)



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
  | mv _ => simp [ParsedLine.toParsedMaskedStatements?] at lowered
  | debugSet => simp [ParsedLine.toParsedMaskedStatements?] at lowered
  | debugGet => simp [ParsedLine.toParsedMaskedStatements?] at lowered
  | dramSet => simp [ParsedLine.toParsedMaskedStatements?] at lowered

theorem parsedMaskedSourceCost_append (left right : List ParsedMaskedSourceStatement) :
    ProofsLean.ControlNormalization.cost (left ++ right) =
      ProofsLean.ControlNormalization.cost left +
        ProofsLean.ControlNormalization.cost right := by
  induction left with
  | nil => simp [ProofsLean.ControlNormalization.cost]
  | cons statement rest ih =>
      cases statement <;>
        simp [ProofsLean.ControlNormalization.cost, ih, Nat.add_assoc]

theorem parsed_source_lowering_preserves_total_issue_words
    (lines : List ParsedLine) (source : List ParsedMaskedSourceStatement)
    (lowered : lowerParsedMaskedSource lines = some source) :
    parsedMaskedIssueWordTotal? lines =
      some (ProofsLean.ControlNormalization.cost source) := by
  induction lines generalizing source with
  | nil =>
      simp [lowerParsedMaskedSource] at lowered
      subst source
      rfl
  | cons line rest ih =>
      cases hline : ParsedLine.toParsedMaskedStatements? line with
      | none =>
          simp [lowerParsedMaskedSource, hline] at lowered
      | some lineSource =>
          have hlineCost := parsed_line_lowering_preserves_issue_words line lineSource hline
          rcases hlineCost with ⟨lineWords, hscore, hcost⟩
          cases hrest : lowerParsedMaskedSource rest with
          | none => simp [lowerParsedMaskedSource, hline, hrest] at lowered
          | some restSource =>
              simp [lowerParsedMaskedSource, hline, hrest] at lowered
              subst source
              have hrestCost := ih restSource hrest
              rw [parsedMaskedSourceCost_append, hcost]
              simp [parsedMaskedIssueWordTotal?, hscore, hrestCost]
theorem parsed_nop_line_lowers_to_count_issue_words (count : Nat) (wait : Option Nat) :
    lowerParsedMaskedSource [.nop count wait] =
      some (List.replicate count (.issue ParsedMaskedIssueLine.nop)) := by
  simp [lowerParsedMaskedSource, ParsedLine.toParsedMaskedStatements?]

theorem parsed_mask_directive_text_lowers_to_zero_cost :
    (parseMaskDirective? "maskllm 258").bind (fun line =>
      (lowerParsedMaskedSource [line]).map ProofsLean.ControlNormalization.cost) =
        some 0 := by
  rfl

theorem parsed_mask_directive_text_controls_following_issue
    (control : ParsedMaskExecutionControl) :
    (parseMaskDirective? "maskllm 258").bind (fun line =>
      (lowerParsedMaskedSource [line, .pe []]).map (fun source =>
        advanceParsedControlThroughSource source control =
          { control with
            directive := ⟨4, ⟨false, false, false, true, false, false⟩, 2⟩,
            elapsedWords := control.elapsedWords + 1 })) = some true := by
  rw [show parseMaskDirective? "maskllm 258" =
    some (.maskDirective 4 ⟨false, false, false, true, false, false⟩ 2) by rfl]
  simp [lowerParsedMaskedSource, ParsedLine.toParsedMaskedStatements?,
    advanceParsedControlThroughSource, updateParsedMaskDirective,
    advanceParsedMaskControl]

theorem parsedMaskedSource_score (source : List ParsedMaskedSourceStatement)
    (control : ParsedMaskExecutionControl) :
    ProofsLean.score parsedMaskedNormalizedMachine
      (ProofsLean.ControlNormalization.compileAdvancing updateParsedMaskDirective
        advanceParsedMaskControl source control) =
      ProofsLean.ControlNormalization.cost source :=
  ProofsLean.ControlNormalization.source_score_advancing updateParsedMaskDirective
    advanceParsedMaskControl parsedMaskedExpressionStep parsedMaskedIssueLegal Unit
    source control

theorem parsed_source_issue_words_equal_compiled_score
    (lines : List ParsedLine) (source : List ParsedMaskedSourceStatement)
    (lowered : lowerParsedMaskedSource lines = some source)
    (control : ParsedMaskExecutionControl) :
    parsedMaskedIssueWordTotal? lines = some
      (ProofsLean.score parsedMaskedNormalizedMachine
        (ProofsLean.ControlNormalization.compileAdvancing updateParsedMaskDirective
          advanceParsedMaskControl source control)) := by
  rw [parsedMaskedSource_score]
  exact parsed_source_lowering_preserves_total_issue_words lines source lowered

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
