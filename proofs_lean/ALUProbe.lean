import ProofsLean.IntegerALU

/- Experimental oracle export. Running compiled Lean is not a kernel proof of
reference-binary conformance. The Python runner compares these datapath values
with the official tools and records the exact scope and source hashes. -/
open ProofsLean.MNCore.IntegerALU

def operations : List (String × Op × Bool) := [
  ("inc", .arith .inc false, false), ("uinc", .arith .inc true, false),
  ("dec", .arith .dec false, false), ("udec", .arith .dec true, false),
  ("add", .arith .add false, true), ("uadd", .arith .add true, true),
  ("sub", .arith .sub false, true), ("usub", .arith .sub true, true),
  ("not", .bitNot, false), ("lnot", .logicalNot, false),
  ("and", .bitAnd, true), ("or", .bitOr, true), ("xor", .bitXor, true),
  ("max", .maximum false, true), ("umax", .maximum true, true),
  ("min", .minimum false, true), ("umin", .minimum true, true),
  ("passa", .passa, false)]

def pairs : List (Nat × Nat) := [
  (0, 0), (0, 1), (1, 0), (1, 1),
  (0xffffffffffffffff, 1), (0xffffffffffffffff, 0xffffffffffffffff),
  (0x7fffffffffffffff, 1), (0x8000000000000000, 1),
  (0x7fffffff7fffffff, 0x0000000100000001),
  (0x8000000080000000, 0xffffffff00000001),
  (0x0000ffff7fff8000, 0x0001000100010001),
  (0xffff000080007fff, 0x00010000ffff8000),
  (0x0123456789abcdef, 0xfedcba9876543210),
  (0xaaaaaaaa55555555, 0x55555555aaaaaaaa)] ++
  (List.range 16).map (fun seed =>
    ((seed * 6364136223846793005 + 1442695040888963407) % 2^64,
     (seed * 2862933555777941757 + 3037000493) % 2^64))

def main : IO Unit := do
  for (letter, precision) in [("l", Precision.long), ("i", Precision.word), ("s", Precision.half)] do
    for (name, op, binary) in operations do
      let spelling := if name.startsWith "u" then "u" ++ letter ++ (name.drop 1).toString
                      else letter ++ name
      for (a, b) in pairs do
        let x : Bus := ⟨BitVec.ofNat 64 a, 0x0123456789abcdef⟩
        let y : Bus := ⟨BitVec.ofNat 64 b, 0xfedcba9876543210⟩
        let result := evaluateBus precision op x y false
        let mask := (List.finRange 4).foldl (fun acc bit =>
          acc + if result.flags bit then 2 ^ bit.val else 0) 0
        IO.println s!"{spelling}\t{binary}\t{a}\t{b}\t{result.value.high.toNat}\t{result.value.low.toNat}\t{mask}"
