import ProofsLean.Masks

/- Explicit referenceBinary mask profile. Finite experiments, not ISA proof. -/
open ProofsLean.MNCore

def dataBus (cycle : Fin 4) : IntegerALU.Bus :=
  let high := match cycle.val with
    | 0 => 0x0000ffff7fff0000 | 1 => 0xabcd000000001234
    | 2 => 0 | _ => 0x80007fff0000ffff
  ⟨BitVec.ofNat 64 high, BitVec.ofNat 64 (0xfedcba9876543210 + cycle.val)⟩

def oldBus (cycle : Fin 4) : IntegerALU.Bus :=
  ⟨BitVec.ofNat 64 (0x1122334455667788 + cycle.val),
   BitVec.ofNat 64 (0x99aabbccddeeff00 + cycle.val)⟩

def selection (seed : Nat) (cycle : Fin 4) : BitVec 4 :=
  BitVec.ofNat 4 (seed + 5 * cycle.val)

def flagsBits (result : IntegerALU.BusResult) : BitVec 4 :=
  BitVec.ofNat 4 ((List.finRange 4).foldl (fun acc bit =>
    acc + if result.flags bit then 2^bit.val else 0) 0)

def selectedValue (policy : Masks.LongWritePolicy) (width : Masks.Width)
    (mode : String) (mask : BitVec 4) (old : IntegerALU.Bus) (raw : IntegerALU.BusResult) : IntegerALU.Bus :=
  let data := if mode = "flush" ∨ mode = "both" then Masks.flushBus width mask raw.value else raw.value
  if mode = "write" ∨ mode = "both" ∨ mode = "directive" then Masks.writeBus policy width mask old data else data

def main : IO Unit := do
  let mut caseId := 0
  for (spelling, width) in [("l", Masks.Width.long), ("ll", Masks.Width.double)] do
    for mode in ["write", "flush", "both", "register", "directive", "override"] do
      for seed in List.range 16 do
        for cycle in List.finRange 4 do
          let mask := selection seed cycle
          let data := dataBus cycle
          let old := oldBus cycle
          let raw := IntegerALU.evaluateBus .half .passa data ⟨0, 0⟩ false
          let result := selectedValue .referenceBinary width mode mask old raw
          let manual := selectedValue .manualReading width mode mask old raw
          let flags := if mode = "register" ∨ mode = "override" then flagsBits raw &&& mask else flagsBits raw
          IO.println s!"{caseId}\t{spelling}\t{mode}\t{seed}\t{cycle.val}\t{mask.toNat}\t{data.high.toNat}\t{data.low.toNat}\t{old.high.toNat}\t{old.low.toNat}\t{result.high.toNat}\t{result.low.toNat}\t{flags.toNat}\t{manual.high.toNat}\t{manual.low.toNat}"
        caseId := caseId + 1
