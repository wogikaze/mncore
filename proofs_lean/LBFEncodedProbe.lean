import ProofsLean.EncodedForwarding

open ProofsLean.MNCore.Forwarding

def main : IO _root_.Unit := do
  let old : Slots := fun unit _ => if unit = .l1ToPE then .known ⟨0x3ff0000000000000, 0⟩ else .poison
  for scenario in ["disabled-write", "disabled-discard", "disabled-mask-off", "disabled-narrow-off",
                   "disabled-chain", "after-alu-imm", "after-mau", "after-two-ordinary",
                   "producer-new", "noforward-producer-new", "nop"] do
    let fresh : ProofsLean.MNCore.Forwarding.Unit → Option (Fin 4 → Value ProofsLean.MNCore.IntegerALU.Bus) := fun unit =>
      if unit = .l1ToPE then some (fun _ => Value.known ⟨0x4000000000000000, 0⟩) else none
    let summary := if scenario = "producer-new" then StepSummary.issue false fresh
      else if scenario = "noforward-producer-new" then .issue true fresh
      else if scenario = "nop" then .nop else .issue false (fun _ => none)
    let value := match advanceEncodedReference old summary with
      | .ok slots => slots .l1ToPE 0
      | .failure | .unknown => .unknown
    let expected := if scenario = "disabled-mask-off" ∨ scenario = "disabled-narrow-off" then
      (⟨0x1122334455667788, 0x99aabbccddeeff00⟩ : ProofsLean.MNCore.IntegerALU.Bus)
      else match value with | .known bus => bus | _ => ⟨0, 0⟩
    let status := match consume .discard value with
      | .ok _ => "ok" | .failure => "failure" | .unknown => "unknown"
    IO.println s!"lbf\t{scenario}\t{status}\t{expected.high.toNat}\t{expected.low.toNat}"
