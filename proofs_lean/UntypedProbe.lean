import ProofsLean.UntypedALU

/- Finite experimental vectors, not a universal binary-conformance theorem. -/
open ProofsLean.MNCore.UntypedALU

def payloads : List Nat := [0, 1, 0xffff, 0x10000, 0x7fffffff, 0x80000000,
  0xffffffff, 0x12345678] ++
  (List.range 16).map (fun seed => (seed * 1664525 + 1013904223) % 2^32)

def inputs (seed : Nat) : MABInput := fun pe =>
  ⟨BitVec.ofNat 64 ((seed + 1) * 6364136223846793005 + pe.val * 1442695040888963407),
   BitVec.ofNat 64 ((pe.val + 1) * 0x0123456789abcdef + seed)⟩

def cases : List (String × Nat × Op × Nat) :=
  (List.range 16).map (fun seed => ("zero", 0, .zero, seed)) ++
  payloads.flatMap (fun payload =>
    [("imm", payload, .imm (BitVec.ofNat 32 payload) false, payload),
     ("immu", payload, .imm (BitVec.ofNat 32 payload) true, payload)]) ++
  (List.range 16).flatMap (fun seed => [("msl", 0, .msl, seed), ("msr", 0, .msr, seed)])

def main : IO Unit := do
  for (index, (name, payload, op, seed)) in cases.zipIdx |>.map (fun (row, i) => (i, row)) do
    let input := inputs seed
    for pe in List.finRange 4 do
      let result := evaluateWithPolicy .referenceBinary op input pe
      let mask := (List.finRange 4).foldl (fun acc bit =>
        acc + if result.flags bit then 2^bit.val else 0) 0
      IO.println s!"{index}\t{name}\t{payload}\t{pe.val}\t{(input pe).high.toNat}\t{(input pe).low.toNat}\t{result.value.high.toNat}\t{result.value.low.toNat}\t{mask}"
