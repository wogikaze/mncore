import ProofsLean.Issue

/-! A structured subset of Rust `vsm.rs::parse_operand`. This parser covers
forwarding/fixed operands, OMR, BAR, matrix, L1BM, L2BM, DAR, and `$nowrite`.
Ordinary PE-memory address operands are intentionally left to a later parser
fragment; this module does not claim complete PE expression parsing. -/

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
    if entry < 256 then some (.entry longLong entry) else none
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
        if rest.isEmpty && value < 2 ^ 64 then some (some (value % (2 ^ 32)))
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

def parseParsedPEOperandBody? (body : List Char) (neg : Bool)
    (mask : Option ParsedMask) : Option ParsedOperand := do
  if body == ['n','o','w','r','i','t','e'] then some .nowrite
  else if let some forward := parseParsedPEForward? body neg then some forward
  else if let some fixed := parseParsedPEFixed? body then some fixed
  else if let some entryChars := parsedStripChars? ['o','m','r'] body then do
    let entry ← parsedPEU8? entryChars
    some (.omr entry mask)
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
      | _ => none

/-- Parse the structured non-memory PE operand productions from Rust
`parse_operand`. Unknown memory banks and ordinary `$m/$n/$r/$s` addressed
memory forms remain unsupported by this fragment. -/
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

end ProofsLean.MNCore.Issue
