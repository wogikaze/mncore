import ProofsLean.IntegerALU
import ProofsLean.ParsedIntegerStep

/- Raw L1BM-to-PE broadcast transfer, mirroring `Blocks::l1_to_pe`
(`viz/core/src/blocks.rs`). This models one L1B bank; PE destination writes,
other transfer opcodes, turnaround updates, masks, and issue timing remain
separate obligations. -/
namespace ProofsLean.MNCore.L1Transfer

open ProofsLean.MNCore.IntegerALU

def l1bmLongWords : Nat := 8192

abbrev L1Bank := Fin l1bmLongWords → BitVec 64
abbrev L1Turnaround := Fin 4 → Fin 64 → BitVec 64

def addressAt (base : Fin l1bmLongWords) (offset : Nat) : Fin l1bmLongWords :=
  ⟨(base.val + offset) % l1bmLongWords, Nat.mod_lt _ (by decide)⟩

/-- `pbcast` reads one long word per cycle, and a second word four positions
later only for a two-long-word (`wl == 4`) source. -/
def pbcast (memory : L1Bank) (base : Fin l1bmLongWords)
    (twoLongWords : Bool) (cycle : Fin 4) : Bus :=
  { high := memory (addressAt base cycle.val)
    low := if twoLongWords then memory (addressAt base (cycle.val + 4)) else 0 }

/-- A turnaround-register `pbcast` reads fixed offsets in the current cycle's
64-word L1B block; unlike an addressed source, its offset does not advance. -/
def pbcastTurnaround (turnaround : L1Turnaround)
    (twoLongWords : Bool) (cycle : Fin 4) : Bus :=
  { high := turnaround cycle 0
    low := if twoLongWords then turnaround cycle 4 else 0 }

theorem pbcast_high (memory : L1Bank) (base : Fin l1bmLongWords)
    (twoLongWords : Bool) (cycle : Fin 4) :
    (pbcast memory base twoLongWords cycle).high = memory (addressAt base cycle.val) := rfl

theorem pbcast_low (memory : L1Bank) (base : Fin l1bmLongWords)
    (twoLongWords : Bool) (cycle : Fin 4) :
    (pbcast memory base twoLongWords cycle).low =
      if twoLongWords then memory (addressAt base (cycle.val + 4)) else 0 := rfl

theorem pbcastTurnaround_high (turnaround : L1Turnaround)
    (twoLongWords : Bool) (cycle : Fin 4) :
    (pbcastTurnaround turnaround twoLongWords cycle).high = turnaround cycle 0 := rfl

theorem pbcastTurnaround_low (turnaround : L1Turnaround)
    (twoLongWords : Bool) (cycle : Fin 4) :
    (pbcastTurnaround turnaround twoLongWords cycle).low =
      if twoLongWords then turnaround cycle 4 else 0 := rfl

theorem addressAt_wraps (base : Fin l1bmLongWords) (offset : Nat) :
    (addressAt base offset).val = (base.val + offset) % l1bmLongWords := rfl

def updateBroadcastForwarding (old : ProofsLean.MNCore.Forwarding.Slots)
    (outputs : Fin 4 → Bus) (noForward : Bool) :
    ProofsLean.MNCore.Forwarding.Slots :=
  if noForward then old else fun unit cycle =>
    if unit = .l1ToPE then .known (outputs cycle) else old unit cycle

theorem pbcast_forwarding_readback
    (files : ProofsLean.MNCore.PEMemory.IntegerRegisterFiles)
    (old : ProofsLean.MNCore.Forwarding.Slots)
    (memory : L1Bank) (base : Fin l1bmLongWords)
    (twoLongWords : Bool) (cycle : Fin 4) :
    ProofsLean.MNCore.PEMemory.ParsedIntegerInput.readWithForwarding files
      (updateBroadcastForwarding old (fun c => pbcast memory base twoLongWords c) false)
      cycle (.forward .lbf false) = .ok (pbcast memory base twoLongWords cycle) := by
  simp [ProofsLean.MNCore.PEMemory.ParsedIntegerInput.readWithForwarding,
    ProofsLean.MNCore.PEMemory.ParsedIntegerInput.forwardUnit,
    ProofsLean.MNCore.PEMemory.ParsedIntegerInput.applyRounding,
    updateBroadcastForwarding]

end ProofsLean.MNCore.L1Transfer
