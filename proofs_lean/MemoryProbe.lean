import ProofsLean.PEMemory

/- Experimental read vectors: no claim of full instruction/legality coverage. -/
open ProofsLean.MNCore.PEMemory

def pattern (index : Nat) : BitVec 32 := BitVec.ofNat 32 (0x12345678 + 1664525 * index)

def main : IO Unit := do
  let mut caseId := 0
  for (letter, bank) in [("m", Bank.lm0), ("n", Bank.lm1), ("r", Bank.grf0),
                         ("s", Bank.grf1), ("t", Bank.t)] do
    for (access, width) in [("", Width.word), ("l", Width.long), ("ll", Width.double)] do
      let flat := fun cycle : Fin 4 =>
        match cycle.val with
        | 0 => 0
        | 1 => bank.capacity - width.words
        | 2 => 2 * width.words
        | _ => 5 * width.words
      let schedules := [(.auto 0 0, "0"), (.auto 0 width.words, "0v"),
                         (.auto (bank.capacity - width.words) width.words, s!"{bank.capacity - width.words}v"),
                         (.flat flat, s!"[0,{bank.capacity - width.words},{2 * width.words},{5 * width.words}]")]
      let selected := if bank = .t then schedules.take 1 else schedules
      for (schedule, spelling) in selected do
        let operand := if bank = .t then "$" ++ access ++ "t" else "$" ++ access ++ letter ++ spelling
        for cycle in List.finRange 4 do
          let start := address bank width schedule 0 .direct 0 cycle
          let memory : Memory bank := fun index => pattern index.val
          let result := pack (readWords bank width memory start)
          IO.println s!"{caseId}\t{letter}\t{operand}\t{cycle.val}\t{start.val}\t{result.high.toNat}\t{result.low.toNat}"
        caseId := caseId + 1
