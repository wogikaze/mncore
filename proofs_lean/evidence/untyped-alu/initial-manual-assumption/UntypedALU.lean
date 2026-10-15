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

/-- msl transfers high long-words PE0→1→2→3→0. The low long-word
bypasses from the local first input, as for other one-long-word ALU ops. -/
def rotateLeft (input : MABInput) (pe : Fin 4) : Bus :=
  ⟨(input (previous pe)).high, (input pe).low⟩

def rotateRight (input : MABInput) (pe : Fin 4) : Bus :=
  ⟨(input (next pe)).high, (input pe).low⟩

theorem rotations_cancel (input : MABInput) (pe : Fin 4) :
    rotateRight (rotateLeft input) pe = input pe := by
  simp [rotateRight, rotateLeft, previous_next]

theorem reverse_rotations_cancel (input : MABInput) (pe : Fin 4) :
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

def evaluate (op : Op) (input : MABInput) (pe : Fin 4) : BusResult :=
  let value := match op with
    | .zero => ⟨0, 0⟩
    | .imm payload sparse => immediate payload sparse
    | .msl => rotateLeft input pe
    | .msr => rotateRight input pe
  ⟨value, fun _ => false⟩

theorem flags_always_zero (op : Op) (input : MABInput) (pe : Fin 4) (bit : Fin 4) :
    (evaluate op input pe).flags bit = false := rfl

theorem zero_ignores_inputs (input other : MABInput) (pe q : Fin 4) :
    (evaluate .zero input pe).value = (evaluate .zero other q).value := rfl

theorem immediate_ignores_inputs (payload : BitVec 32) (sparse : Bool)
    (input other : MABInput) (pe q : Fin 4) :
    (evaluate (.imm payload sparse) input pe).value =
      (evaluate (.imm payload sparse) other q).value := rfl

theorem immediate_longwords_equal (payload : BitVec 32) (sparse : Bool) :
    (immediate payload sparse).high = (immediate payload sparse).low := rfl

example : immediate 0x12345678 false = ⟨0x1234567812345678, 0x1234567812345678⟩ := by decide
example : immediate 0x12345678 true = ⟨0x1234567800000000, 0x1234567800000000⟩ := by decide

end ProofsLean.MNCore.UntypedALU
