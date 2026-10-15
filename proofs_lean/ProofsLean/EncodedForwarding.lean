import ProofsLean.Forwarding

namespace ProofsLean.MNCore.Forwarding

/- Profile for explicitly encoded PE word streams. Fragment-based experiments
observe LBF retention across ordinary steps. This is not a decoder, a proof
that a rejected VSM source is legal, or a promotion of the VSM unknown cases. -/
def encodedReferenceSlot (old : Slots)
    (outputs : Unit → Option (Fin 4 → Value IntegerALU.Bus)) (unit : Unit) (cycle : Fin 4) :
    Value IntegerALU.Bus :=
  match outputs unit with
  | some values => values cycle
  | none => match unit with
      | .alu | .mau => .poison
      | .matrixRead => .known ⟨0, 0⟩
      | .l1ToPE => old unit cycle

def advanceEncodedReference (old : Slots) : StepSummary → StepResult Slots
  | .nop | .issue true _ => .ok old
  | .issue false outputs => .ok (encodedReferenceSlot old outputs)
  | .unsupported => .unknown

theorem encoded_lbf_absent_retains (old : Slots)
    (outputs : Unit → Option (Fin 4 → Value IntegerALU.Bus)) (cycle : Fin 4)
    (absent : outputs .l1ToPE = none) :
    encodedReferenceSlot old outputs .l1ToPE cycle = old .l1ToPE cycle := by
  simp [encodedReferenceSlot, absent]

theorem encoded_producer_overrides (old : Slots)
    (outputs : Unit → Option (Fin 4 → Value IntegerALU.Bus)) (unit : Unit) (cycle : Fin 4)
    (values : Fin 4 → Value IntegerALU.Bus) (produced : outputs unit = some values) :
    encodedReferenceSlot old outputs unit cycle = values cycle := by
  simp [encodedReferenceSlot, produced]

theorem encoded_noforward_preserves (old : Slots)
    (outputs : Unit → Option (Fin 4 → Value IntegerALU.Bus)) :
    advanceEncodedReference old (.issue true outputs) = .ok old := rfl

theorem encoded_unsupported_remains_unknown (old : Slots) :
    advanceEncodedReference old .unsupported = .unknown := rfl

end ProofsLean.MNCore.Forwarding
