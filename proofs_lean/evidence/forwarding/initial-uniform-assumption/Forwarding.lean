import ProofsLean.Masks

/- MN-Core 2 manual (2026-06-02), §3.6.1.15–19 and §3.6.6.
Pure forwarding lifecycle primitives, not decoded VSM execution or hazard checks.
Poison is a KNOWN invalid value; missing semantics must remain unknown. -/
namespace ProofsLean.MNCore.Forwarding

inductive Value (α : Type) where
  | known (value : α)
  | poison
  | unknown
  deriving DecidableEq, Repr

def Value.map (f : α → β) : Value α → Value β
  | .known value => .known (f value)
  | .poison => .poison
  | .unknown => .unknown

inductive Unit where
  | alu | mau | matrixRead | l1ToPE
  deriving DecidableEq, Repr

abbrev Slots := Unit → Fin 4 → Value IntegerALU.Bus

/-- A summary requires known unit usage and outputs for the whole step.
An unimplemented instruction cannot be summarized as an absent producer. -/
inductive StepSummary where
  | nop
  | issue (noForward : Bool) (outputs : Unit → Option (Fin 4 → Value IntegerALU.Bus))
  | unsupported

def advance (old : Slots) : StepSummary → StepResult Slots
  | .nop => .ok old
  | .issue true _ => .ok old
  | .issue false outputs => .ok (fun unit cycle => match outputs unit with
      | some values => values cycle
      | none => .poison)
  | .unsupported => .unknown

inductive Sink where
  | discard
  | memory (anyPartWritten : Bool)
  | maskRegister

/-- Known poison is tolerated only when no write is performed. A zero-flush
operation is NOT a write mask: it cannot by itself suppress a write/error.
This whole-value abstraction does not resolve per-lane numerical poison. -/
def consume (sink : Sink) : Value α → StepResult PUnit
  | .unknown => .unknown
  | .known _ => .ok ⟨⟩
  | .poison => match sink with
      | .discard | .memory false => .ok ⟨⟩
      | .memory true | .maskRegister => .failure

theorem nop_preserves (old : Slots) : advance old .nop = .ok old := rfl

theorem noforward_preserves (old : Slots) (outputs : Unit → Option (Fin 4 → Value IntegerALU.Bus)) :
    advance old (.issue true outputs) = .ok old := rfl

theorem unsupported_is_not_disabled (old : Slots) : advance old .unsupported = .unknown := rfl

theorem disabled_producer_is_poison (old : Slots) :
    advance old (.issue false (fun _ => none)) = .ok (fun _ _ => .poison) := rfl

theorem unknown_not_discardable : consume .discard (Value.unknown : Value α) = .unknown := rfl

theorem poison_discard_does_not_fail : consume .discard (Value.poison : Value α) = .ok ⟨⟩ := rfl

theorem poison_masked_write_does_not_fail :
    consume (.memory false) (Value.poison : Value α) = .ok ⟨⟩ := rfl

theorem poison_live_write_fails : consume (.memory true) (Value.poison : Value α) = .failure := rfl

theorem poison_mask_register_write_fails : consume .maskRegister (Value.poison : Value α) = .failure := rfl

end ProofsLean.MNCore.Forwarding
