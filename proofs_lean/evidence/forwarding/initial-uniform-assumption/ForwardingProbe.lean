import ProofsLean.Forwarding

/- Expected values/errors from the partial forwarding abstraction. The runner
separately checks assembler acceptance and recognizes forwarding runtime errors. -/
open ProofsLean.MNCore.Forwarding
abbrev FwdUnit := ProofsLean.MNCore.Forwarding.Unit

def initial : Slots := fun _ _ => .poison

def base (unit : FwdUnit) : ProofsLean.MNCore.IntegerALU.Bus :=
  ⟨0x3ff0000000000000, if unit = .alu then 0x3ff0000000000000 else 0⟩

def old : ProofsLean.MNCore.IntegerALU.Bus := ⟨0x1122334455667788, 0x99aabbccddeeff00⟩

def unwrap (state : ProofsLean.StepResult Slots) : Slots :=
  match state with
  | .ok slots => slots
  | .failure | .unknown => fun _ _ => .unknown

def main : IO _root_.Unit := do
  let units : List (String × FwdUnit) := [("alu", .alu), ("mau", .mau), ("mread", .matrixRead), ("lbf", .l1ToPE)]
  for (name, unit) in units do
    let producer := StepSummary.issue false (fun candidate =>
      if candidate = unit then some (fun _ => .known (base unit)) else none)
    let afterProducer := unwrap (advance initial producer)
    let scenarios := ["valid", "nop", "noforward", "noforward-alu", "disabled-write",
                      "disabled-discard", "disabled-mask-off", "disabled-narrow-off", "disabled-chain"] ++
      (if unit = .alu then ["disabled-long-off", "disabled-flush-off", "disabled-register-off"] else [])
    for scenario in scenarios do
      let state := if scenario = "nop" then unwrap (advance afterProducer .nop)
        else if scenario = "noforward" ∨ scenario = "noforward-alu" then
          unwrap (advance afterProducer (.issue true (fun _ => none)))
        else if scenario.startsWith "disabled" then
          unwrap (advance afterProducer (.issue false (fun _ => none))) else afterProducer
      let value := state unit 0
      let sink := if scenario = "disabled-discard" then Sink.discard
        else if scenario = "disabled-mask-off" ∨ scenario = "disabled-narrow-off" then .memory false
        else if scenario = "disabled-register-off" then .maskRegister else .memory true
      let result := consume sink value
      let status := match result with | .ok _ => "ok" | .failure => "failure" | .unknown => "unknown"
      let expected := match value with
        | .known value => value
        | _ => old
      IO.println s!"{name}\t{scenario}\t{status}\t{expected.high.toNat}\t{expected.low.toNat}"
