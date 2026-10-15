import ProofsLean.PEMemory

/- Finite experiments for dynamic address arithmetic, not a full ISA theorem. -/
open ProofsLean.MNCore.PEMemory

inductive Mode where
  | direct | indirect (large : Bool) | madpe (threshold : Fin 4)

structure Case where
  bank : Bank
  width : Width
  bar : Nat
  mode : Mode
  flat : Bool := false

def testCases : List Case := [Bank.lm0, Bank.lm1].flatMap fun bank =>
  [Width.word, Width.long, Width.double].flatMap fun width =>
    ([0, 1, 2, 3, 4093, 4095].map fun bar => ⟨bank, width, bar, .direct, false⟩) ++
    (if bank = .lm0 then [0, 1, 4095].flatMap (fun bar =>
      [false, true].flatMap fun large => [false, true].map fun flat =>
        ⟨bank, width, bar, .indirect large, flat⟩) else []) ++
    ([0, 4095].flatMap fun bar => (List.finRange 4).map fun threshold =>
      ⟨bank, width, bar, .madpe threshold, false⟩)

def tValue (mode : Mode) (pe cycle : Fin 4) : BitVec 64 :=
  let small := match cycle.val with
    | 0 => 0 | 1 => 1 | 2 => 4095 | _ => 4096
  let large := match cycle.val with
    | 0 => 0x100000001 | 1 => 0xffffffffffffffff
    | 2 => 0x8000000000000003 | _ => 0xffffffff00000ffd
  BitVec.ofNat 64 ((match mode with | .indirect true => large | _ => small) + pe.val)

def main : IO Unit := do
  for (entry, caseId) in testCases.zipIdx do
    let letter := if entry.bank = .lm0 then "m" else "n"
    let access := match entry.width with | .word => "" | .long => "l" | .double => "ll"
    let flat := fun cycle : Fin 4 => match cycle.val with
      | 0 => 0 | 1 => 4096 - entry.width.words | 2 => 2 * entry.width.words | _ => 5 * entry.width.words
    let schedule := if entry.flat then Schedule.flat flat else
      Schedule.auto (4096 - entry.width.words) entry.width.words
    let spelling := if entry.flat then s!"[0,{4096-entry.width.words},{2*entry.width.words},{5*entry.width.words}]"
      else s!"{4096-entry.width.words}v"
    let modifier := match entry.mode with | .indirect _ => "t" | _ => ""
    let suffix := match entry.mode with | .madpe threshold => s!"j{threshold.val}" | _ => ""
    let operand := "$" ++ access ++ letter ++ modifier ++ spelling ++ suffix
    for pe in List.finRange 4 do
      for cycle in List.finRange 4 do
        let t := tValue entry.mode pe cycle
        let adjustment := match entry.mode with
          | .direct => Adjustment.direct
          | .indirect _ => .tIndirect t
          | .madpe threshold => .madpe threshold
        let bar := BitVec.ofNat 12 entry.bar
        let start := address entry.bank entry.width schedule bar adjustment pe cycle
        let memory : Memory entry.bank := fun index => BitVec.ofNat 32 (0x12345678 + 1664525 * index.val)
        let result := pack (readWords entry.bank entry.width memory start)
        IO.println s!"{caseId}\t{letter}\t{operand}\t{bar.toNat}\t{t.toNat}\t{pe.val}\t{cycle.val}\t{start.val}\t{result.high.toNat}\t{result.low.toNat}"
