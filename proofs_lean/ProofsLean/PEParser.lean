import ProofsLean.Issue

/-! A structured subset of Rust `vsm.rs::parse_operand`. This parser covers
forwarding/fixed operands, OMR, BAR, matrix, L1BM, L2BM, DAR, `$nowrite`, and
ordinary PE-memory operands. This module does not claim complete PE expression
parsing (for example, it does not parse complete lines or opcodes). -/

namespace ProofsLean.MNCore.Issue

def parsedPETrimMaskSuffix (chars : List Char) : List Char :=
  (chars.reverse.dropWhile fun c => c == 't' || c == 'p').reverse

def parseParsedPEMask? (text : String) : Option ParsedMask := do
  let trimmed := parsedPETrimMaskSuffix text.toList
  let (longLong, body) ←
    if (parsedStripChars? ['$','l','l','i','m','r'] trimmed).isSome then
      let suffix := (parsedStripChars? ['$','l','l','i','m','r'] trimmed).getD []
      some (true, ['$','i','m','r'] ++ suffix)
    else if (parsedStripChars? ['l','l'] trimmed).isSome then
      some (true, (parsedStripChars? ['l','l'] trimmed).getD [])
    else some (false, trimmed)
  if let some entryChars := parsedStripChars? ['$','i','m','r'] body then
    let entry ← parsedMvDecimal? entryChars
    if h : entry < 256 then some (.entry longLong ⟨entry, h⟩) else none
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

def parsedPEAccessLength : List Char → Nat × List Char
  | 'l' :: 'l' :: rest => (4, rest)
  | 'l' :: rest => (2, rest)
  | chars => (1, chars)

def parsedPEU32? (chars : List Char) : Option Nat := do
  let value ← parsedMvDecimal? chars
  if value < 2 ^ 32 then some value else none

def parsedPEU8? (chars : List Char) : Option Nat := do
  let value ← parsedMvDecimal? chars
  if value < 256 then some value else none

def parsedPEMatrixRow? (chars : List Char) : Option (Option Nat) := do
  match chars with
  | [] => some none
  | first :: _ =>
      if (parsedMvDigit? 10 first).isNone then none else do
        let (value, rest) ← parsedMvDigitsPrefix 10 chars 0
        if rest.isEmpty then
          if value < 2 ^ 64 then some (some (value % (2 ^ 32))) else some none
        else none

def parseParsedPEForward? (token : List Char) (neg : Bool) : Option ParsedOperand :=
  match token with
  | ['a','l','u','f'] => some (.forward .aluf neg false false)
  | ['a','l','u','f','e'] => some (.forward .aluf neg true false)
  | ['a','l','u','f','r'] => some (.forward .aluf neg false true)
  | ['m','a','u','f'] => some (.forward .mauf neg false false)
  | ['m','a','u','f','e'] => some (.forward .mauf neg true false)
  | ['m','a','u','f','r'] => some (.forward .mauf neg false true)
  | ['l','b','f'] => some (.forward .lbf neg false false)
  | ['l','b','f','e'] => some (.forward .lbf neg true false)
  | ['l','b','f','r'] => some (.forward .lbf neg false true)
  | ['m','r','e','a','d','f'] => some (.forward .mreadf neg false false)
  | ['m','r','e','a','d','f','e'] => some (.forward .mreadf neg true false)
  | ['m','r','e','a','d','f','r'] => some (.forward .mreadf neg false true)
  | _ => none

def parseParsedPEFixed? : List Char → Option ParsedOperand
  | ['l','2','b','i','d'] => some (.fixed .l2bid)
  | ['l','1','b','i','d'] => some (.fixed .l1bid)
  | ['m','a','b','i','d'] => some (.fixed .mabid)
  | ['p','e','i','d'] => some (.fixed .peid)
  | ['s','u','b','p','e','i','d'] => some (.fixed .subpeid)
  | ['m','s','b','1'] => some (.fixed .msb1)
  | _ => none

def parsedPETakeDigitsAux : List Char → Nat → Nat × List Char
  | char :: rest, value =>
      if (parsedMvDigit? 10 char).isSome then
        parsedPETakeDigitsAux rest (value * 10 + (parsedMvDigit? 10 char).getD 0)
      else (value, char :: rest)
  | [], value => (value, [])

/-- Rust `take_num`: consume the complete initial decimal run, but represent a
u64 overflow as `none` while still returning the unconsumed suffix. -/
def parsedPETakeNum (chars : List Char) : Option Nat × List Char :=
  let (value, rest) := parsedPETakeDigitsAux chars 0
  if rest == chars then (none, chars)
  else (if value < 2 ^ 64 then some value else none, rest)

def parsedPESplitCommaAux : List Char → List Char → List (List Char) → List (List Char)
  | [], current, reversedEntries => (current.reverse :: reversedEntries).reverse
  | ',' :: rest, current, reversedEntries =>
      parsedPESplitCommaAux rest [] (current.reverse :: reversedEntries)
  | char :: rest, current, reversedEntries =>
      parsedPESplitCommaAux rest (char :: current) reversedEntries

def parsedPEFlatAddresses? (chars : List Char) : Option (Nat × Nat × Nat × Nat) := do
  let values := parsedPESplitCommaAux chars [] []
  match values with
  | [a, b, c, d] => do
      let a ← parsedPEU32? (parsedL1bTrim a)
      let b ← parsedPEU32? (parsedL1bTrim b)
      let c ← parsedPEU32? (parsedL1bTrim c)
      let d ← parsedPEU32? (parsedL1bTrim d)
      some (a, b, c, d)
  | _ => none

def parsedPENatToU32 (value : Nat) : Nat := value % (2 ^ 32)

def parsedPEAddressRegion? (width : Nat) (tIndirect : Bool) (chars : List Char) :
    Option (Region × List Char) := do
  let (a0, a1, a2, a3, rest) ← match chars with
    | '[' :: afterOpen => do
        let (inside, suffix) ← parsedSplitAt? afterOpen ']'
        let (first, second, third, fourth) ← parsedPEFlatAddresses? inside
        some (first, second, third, fourth, suffix)
    | _ =>
        let (base?, afterBase) := parsedPETakeNum chars
        let base := parsedPENatToU32 (base?.getD 0)
        let (increment, suffix) := match afterBase with
          | 'v' :: afterV =>
              let (increment?, tail) := parsedPETakeNum afterV
              (parsedPENatToU32 (increment?.getD width), tail)
          | _ => (0, afterBase)
        some (base, parsedPENatToU32 (base + increment),
          parsedPENatToU32 (base + 2 * increment),
          parsedPENatToU32 (base + 3 * increment), suffix)
  some (⟨width, a0, a1, a2, a3, tIndirect, none⟩, rest)

def parsedPEFinishMemory? (bank : Bank) (width : Nat) (neg ext rnd : Bool)
    (mask : Option ParsedMask) (chars : List Char) : Option ParsedOperand := do
  let (tIndirect, addressChars) :=
    if bank == .lm0 then
      match chars with
      | 't' :: rest => (true, rest)
      | _ => (false, chars)
    else (false, chars)
  let (region, suffix0) ← parsedPEAddressRegion? width tIndirect addressChars
  let (region, suffix) ← match suffix0 with
    | 'j' :: afterJ => do
        let (index?, tail) := parsedPETakeNum afterJ
        let index ← index?
        some ({ region with madpe := some (index % 256) }, tail)
    | _ => some (region, suffix0)
  let (extended, rounded) ← match suffix with
    | [] => some (ext, rnd)
    | ['e'] => some (true, false)
    | ['r'] => some (false, true)
    | _ => none
  some (.mem ⟨bank, region⟩ neg extended rounded mask)

def parseParsedPEMemory? (bank : Bank) (width : Nat) (neg ext rnd : Bool)
    (mask : Option ParsedMask) (chars : List Char) : Option ParsedOperand :=
  if bank == .t then
    match chars with
    | [] => some (.mem ⟨.t, ⟨4, 0, 0, 0, 0, false, none⟩⟩ neg ext rnd mask)
    | ['e'] => some (.mem ⟨.t, ⟨4, 0, 0, 0, 0, false, none⟩⟩ neg true false mask)
    | ['r'] => some (.mem ⟨.t, ⟨4, 0, 0, 0, 0, false, none⟩⟩ neg false true mask)
    | _ => none
  else parsedPEFinishMemory? bank width neg ext rnd mask chars

def parseParsedPEOperandBody? (body : List Char) (neg : Bool)
    (mask : Option ParsedMask) : Option ParsedOperand := do
  if body == ['n','o','w','r','i','t','e'] then some .nowrite
  else if let some forward := parseParsedPEForward? body neg then some forward
  else if let some fixed := parseParsedPEFixed? body then some fixed
  else if let some entryChars := parsedStripChars? ['o','m','r'] body then do
    let entry ← parsedPEU8? entryChars
    if h : entry < 256 then some (.omr ⟨entry, h⟩ mask) else none
  else if let some addressChars := parsedStripChars? ['d','a','r'] body then do
    let address ← parsedPEU32? addressChars
    some (.dar address)
  else do
    let (width, rest) := parsedPEAccessLength body
    if rest == ['m','b'] then some (.bar false width mask)
    else if rest == ['n','b'] then some (.bar true width mask)
    else match rest with
      | 'b' :: addressChars =>
          if addressChars == ['i'] then some (.l1bm width none)
          else do
            let address ← parsedPEU32? addressChars
            some (.l1bm width (some address))
      | 'c' :: addressAndSelector => do
          let (addressChars, l2b) ← match parsedSplitAt? addressAndSelector '@' with
            | none => some (addressAndSelector, none)
            | some (address, '.' :: indexChars) => some (address, some indexChars)
            | _ => none
          let address ← parsedPEU32? addressChars
          let l2b ← match l2b with
            | none => some none
            | some chars => some (some (← parsedPEU8? chars))
          some (.l2bm address l2b)
      | 'x' :: rowChars => do
          let row ← parsedPEMatrixRow? rowChars
          some (.matrix false width row)
      | 'y' :: rowChars => do
          let row ← parsedPEMatrixRow? rowChars
          some (.matrix true width row)
      | 'm' :: addressChars => parsedPEFinishMemory? .lm0 width neg false false mask addressChars
      | 'n' :: addressChars => parsedPEFinishMemory? .lm1 width neg false false mask addressChars
      | 'r' :: addressChars => parsedPEFinishMemory? .grf0 width neg false false mask addressChars
      | 's' :: addressChars => parsedPEFinishMemory? .grf1 width neg false false mask addressChars
      | 't' :: suffix => parseParsedPEMemory? .t width neg false false mask suffix
      | _ => none

/-- Parse the structured PE operand productions from Rust
`parse_operand`. Unknown memory banks still return `none`, matching the
distinction between structured candidates and Rust's diagnostic `Raw` fallback. -/
def parseParsedPEOperand? (text : String) : Option ParsedOperand := do
  let (rawBody, mask) ← match parsedSplitAt? text.toList '/' with
    | none => some (text.toList, none)
    | some (body, maskChars) => do
        let mask ← parseParsedPEMask? (String.ofList maskChars)
        some (body, some mask)
  let (neg, body) := match rawBody with
    | '-' :: rest => (true, rest)
    | _ => (false, rawBody)
  let body ← parsedStripChars? ['$'] body
  parseParsedPEOperandBody? body neg mask

theorem parseParsedPEOperand_forward_masked_memory_register :
    parseParsedPEOperand? "-$alufe/$imr7" =
      some (.forward .aluf true true false) := by decide

theorem parseParsedPEOperand_fixed_and_nowrite :
    parseParsedPEOperand? "$subpeid" = some (.fixed .subpeid) ∧
      parseParsedPEOperand? "$nowrite" = some .nowrite := by decide

theorem parseParsedPEOperand_omr_mask :
    parseParsedPEOperand? "$omr15/ll1000tp" =
      some (.omr 15 (some (.pattern true 8))) := by decide

theorem parseParsedPEOperand_omr_preserves_u8_boundary :
    parseParsedPEOperand? "$omr255" = some (.omr ⟨255, by decide⟩ none) ∧
      parseParsedPEOperand? "$omr256" = none := by decide

theorem parseParsedPEMask_preserves_u8_selector_boundary :
    parseParsedPEMask? "$imr255" = some (.entry false ⟨255, by decide⟩) ∧
      parseParsedPEMask? "$imr256" = none := by decide

theorem parseParsedPEOperand_base_address_registers :
    parseParsedPEOperand? "$mb" = some (.bar false 1 none) ∧
      parseParsedPEOperand? "$lnb" = some (.bar true 2 none) := by decide

theorem parseParsedPEOperand_matrix_row :
    parseParsedPEOperand? "$llx4294967297" = some (.matrix false 4 (some 1)) := by decide

theorem parseParsedPEOperand_block_memory :
    parseParsedPEOperand? "$lb8191" = some (.l1bm 2 (some 8191)) ∧
      parseParsedPEOperand? "$lbi" = some (.l1bm 2 none) ∧
      parseParsedPEOperand? "$lc4294967295@.255" =
        some (.l2bm 4294967295 (some 255)) := by decide

theorem parseParsedPEOperand_dar_u32_boundary :
    parseParsedPEOperand? "$dar4294967295" = some (.dar 4294967295) ∧
      parseParsedPEOperand? "$dar4294967296" = none := by decide

theorem parseParsedPEOperand_memory_forms :
    parseParsedPEOperand? "$r0" =
      some (.mem ⟨.grf0, ⟨1, 0, 0, 0, 0, false, none⟩⟩ false false false none) ∧
      parseParsedPEOperand? "$lm0v4" =
      some (.mem ⟨.lm0, ⟨2, 0, 4, 8, 12, false, none⟩⟩ false false false none) ∧
      parseParsedPEOperand? "$mt0v" =
      some (.mem ⟨.lm0, ⟨1, 0, 1, 2, 3, true, none⟩⟩ false false false none) ∧
      parseParsedPEOperand? "$llm[1, 2, 3, 4]j5e" =
      some (.mem ⟨.lm0, ⟨4, 1, 2, 3, 4, false, some 5⟩⟩ false true false none) ∧
      parseParsedPEOperand? "$te" =
      some (.mem ⟨.t, ⟨4, 0, 0, 0, 0, false, none⟩⟩ false true false none) := by decide

theorem parseParsedPEOperand_memory_rejects_malformed_forms :
    parseParsedPEOperand? "$r0junk" = none ∧
      parseParsedPEOperand? "$m[1,2,3]" = none ∧
      parseParsedPEOperand? "$tx" = none := by decide

end ProofsLean.MNCore.Issue
