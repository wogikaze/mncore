import ProofsLean.IntegerALU

/- MN-Core 2 manual (2026-06-02), §3.6.12.2–4, tables 3.9 and 3.11.
Input buses have already been read. This does not implement memory access,
parallel-issue legality (including imm/LM0 conflict), masks or forwarding. -/
namespace ProofsLean.MNCore.UntypedALU

open IntegerALU (Bus BusResult)

abbrev MABInput := Fin 4 → Bus

def previous (pe : Fin 4) : Fin 4 := ⟨(pe.val + 3) % 4, Nat.mod_lt _ (by decide)⟩
def next (pe : Fin 4) : Fin 4 := ⟨(pe.val + 1) % 4, Nat.mod_lt _ (by decide)⟩

theorem previous_next (pe : Fin 4) : previous (next pe) = pe := by
  apply Fin.ext
  simp only [previous, next]
  omega

theorem next_previous (pe : Fin 4) : next (previous pe) = pe := by
  apply Fin.ext
  simp only [previous, next]
  omega

/-- Permutation under the manual's general LSB-passthrough reading.
This is NOT the observed msl semantics: the reference binary zeros the LSB.
Keep the discrepancy explicit instead of asserting physical conformance. -/
def rotateLeft (input : MABInput) (pe : Fin 4) : Bus :=
  ⟨(input (previous pe)).high, (input pe).low⟩

def rotateRight (input : MABInput) (pe : Fin 4) : Bus :=
  ⟨(input (next pe)).high, (input pe).low⟩

theorem manual_reading_rotations_cancel (input : MABInput) (pe : Fin 4) :
    rotateRight (rotateLeft input) pe = input pe := by
  simp [rotateRight, rotateLeft, previous_next]

theorem manual_reading_reverse_rotations_cancel (input : MABInput) (pe : Fin 4) :
    rotateLeft (rotateRight input) pe = input pe := by
  simp [rotateRight, rotateLeft, next_previous]

def immediate (payload : BitVec 32) (sparse : Bool) : Bus :=
  let longWord := payload ++ (if sparse then (0 : BitVec 32) else payload)
  ⟨longWord, longWord⟩

inductive Op where
  | zero
  | imm (payload : BitVec 32) (sparse : Bool)
  | msl | msr
  deriving DecidableEq, Repr

inductive RotationPolicy where
  | manualReading | referenceBinary
  deriving DecidableEq, Repr

/-- Explicit target profiles. Agreement on finite tests with referenceBinary
does not resolve the manual/implementation discrepancy. -/
def evaluateWithPolicy (policy : RotationPolicy) (op : Op) (input : MABInput) (pe : Fin 4) : BusResult :=
  let value := match op with
    | .zero => ⟨0, 0⟩
    | .imm payload sparse => immediate payload sparse
    | .msl => let rotated := rotateLeft input pe
              match policy with
              | .manualReading => rotated
              | .referenceBinary => ⟨rotated.high, 0⟩
    | .msr => let rotated := rotateRight input pe
              match policy with
              | .manualReading => rotated
              | .referenceBinary => ⟨rotated.high, 0⟩
  ⟨value, fun _ => false⟩

/-- The unqualified model cannot silently choose between conflicting targets. -/
def partialEvaluate (op : Op) (input : MABInput) (pe : Fin 4) : StepResult BusResult :=
  match op with
  | .zero | .imm _ _ => .ok (evaluateWithPolicy .referenceBinary op input pe)
  | .msl | .msr => .unknown

theorem unresolved_rotation_is_unknown (input : MABInput) (pe : Fin 4) :
    partialEvaluate .msl input pe = .unknown ∧
      partialEvaluate .msr input pe = .unknown := ⟨rfl, rfl⟩

theorem reference_msl_lsb_zero (input : MABInput) (pe : Fin 4) :
    (evaluateWithPolicy .referenceBinary .msl input pe).value.low = 0 := rfl

theorem reference_msr_lsb_zero (input : MABInput) (pe : Fin 4) :
    (evaluateWithPolicy .referenceBinary .msr input pe).value.low = 0 := rfl

theorem reference_differs_from_manual_when_lsb_nonzero (input : MABInput) (pe : Fin 4)
    (nonzero : (input pe).low ≠ 0) :
    (evaluateWithPolicy .referenceBinary .msl input pe).value ≠
      (evaluateWithPolicy .manualReading .msl input pe).value := by
  intro same
  apply nonzero
  have low := congrArg Bus.low same
  simpa [evaluateWithPolicy, rotateLeft] using low.symm

theorem flags_always_zero (policy : RotationPolicy) (op : Op) (input : MABInput) (pe : Fin 4) (bit : Fin 4) :
    (evaluateWithPolicy policy op input pe).flags bit = false := rfl

theorem zero_ignores_inputs (policy : RotationPolicy) (input other : MABInput) (pe q : Fin 4) :
    (evaluateWithPolicy policy .zero input pe).value = (evaluateWithPolicy policy .zero other q).value := rfl

theorem immediate_ignores_inputs (policy : RotationPolicy) (payload : BitVec 32) (sparse : Bool)
    (input other : MABInput) (pe q : Fin 4) :
    (evaluateWithPolicy policy (.imm payload sparse) input pe).value =
      (evaluateWithPolicy policy (.imm payload sparse) other q).value := rfl

theorem immediate_longwords_equal (payload : BitVec 32) (sparse : Bool) :
    (immediate payload sparse).high = (immediate payload sparse).low := rfl

example : immediate 0x12345678 false = ⟨0x1234567812345678, 0x1234567812345678⟩ := by decide
example : immediate 0x12345678 true = ⟨0x1234567800000000, 0x1234567800000000⟩ := by decide

end ProofsLean.MNCore.UntypedALU
