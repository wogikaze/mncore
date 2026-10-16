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

inductive L1ReadSource where
  | addressed (base : Fin l1bmLongWords)
  | turnaround (values : L1Turnaround)

def addressAt (base : Fin l1bmLongWords) (offset : Nat) : Fin l1bmLongWords :=
  ⟨(base.val + offset) % l1bmLongWords, Nat.mod_lt _ (by decide)⟩

def readL1Long (memory : L1Bank) (source : L1ReadSource)
    (cycle : Fin 4) (offset : Nat) : BitVec 64 :=
  match source with
  | .addressed base => memory (addressAt base offset)
  | .turnaround values => values cycle ⟨offset % 64, Nat.mod_lt _ (by decide)⟩

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

/-- `mbcast` distributes one long word per PE from its MAB block. Addressed
sources advance by eight words per cycle; turnaround reads use PE-relative
offsets, and retain the paired long word even for a one-word destination. -/
def mbcast (memory : L1Bank) (source : L1ReadSource)
    (twoLongWords : Bool) (pe cycle : Fin 4) : Bus :=
  match source with
  | .addressed _ =>
      let offset := (if twoLongWords then cycle.val * 8 else cycle.val * 4) + pe.val
      { high := readL1Long memory source cycle offset
        low := if twoLongWords then readL1Long memory source cycle (offset + 4) else 0 }
  | .turnaround _ =>
      { high := readL1Long memory source cycle pe.val
        low := readL1Long memory source cycle (4 + pe.val) }

/-- `m4bcast` reads the four-MAB block selected by the high two MAB bits.
Each cycle advances by 16 or 32 long words according to source width. -/
def m4bcast (memory : L1Bank) (source : L1ReadSource)
    (twoLongWords : Bool) (mabGroup pe cycle : Fin 4) : Bus :=
  let groupIndex := mabGroup.val
  let base := match source with
    | .addressed _ => cycle.val * 32
    | .turnaround _ => 0
  let offset := match twoLongWords, source with
    | true, _ => base + groupIndex * 8 + pe.val
    | false, .addressed _ => cycle.val * 16 + groupIndex * 4 + pe.val
    | false, .turnaround _ => groupIndex * 4 + pe.val
  { high := readL1Long memory source cycle offset
    low := if twoLongWords then readL1Long memory source cycle (offset + 4) else 0 }

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

theorem mbcast_addressed_words (memory : L1Bank) (base : Fin l1bmLongWords)
    (twoLongWords : Bool) (pe cycle : Fin 4) :
    (mbcast memory (.addressed base) twoLongWords pe cycle).high =
        memory (addressAt base
          ((if twoLongWords then cycle.val * 8 else cycle.val * 4) + pe.val)) ∧
      (mbcast memory (.addressed base) twoLongWords pe cycle).low =
        if twoLongWords then memory (addressAt base (cycle.val * 8 + pe.val + 4)) else 0 := by
  cases twoLongWords <;> simp [mbcast, readL1Long]

theorem mbcast_turnaround_words (memory : L1Bank) (values : L1Turnaround)
    (twoLongWords : Bool) (pe cycle : Fin 4) :
    (mbcast memory (.turnaround values) twoLongWords pe cycle).high =
        values cycle ⟨pe.val, by have h := pe.isLt; omega⟩ ∧
      (mbcast memory (.turnaround values) twoLongWords pe cycle).low =
        values cycle ⟨(4 + pe.val) % 64, Nat.mod_lt _ (by decide)⟩ := by
  have hpe : pe.val < 64 := by have h := pe.isLt; omega
  simp [mbcast, readL1Long, Nat.mod_eq_of_lt hpe]

def m4bcastGroup (mab : Fin 16) : Fin 4 :=
  ⟨mab.val / 4, by have h := mab.isLt; omega⟩

theorem m4bcastGroup_matches_rust_index (mab : Fin 16) :
    (m4bcastGroup mab).val = mab.val / 4 := rfl

theorem m4bcast_addressed_words (memory : L1Bank) (base : Fin l1bmLongWords)
    (twoLongWords : Bool) (mabGroup pe cycle : Fin 4) :
    (m4bcast memory (.addressed base) twoLongWords mabGroup pe cycle).high =
        memory (addressAt base
          (if twoLongWords then cycle.val * 32 + mabGroup.val * 8 + pe.val
           else cycle.val * 16 + mabGroup.val * 4 + pe.val)) ∧
      (m4bcast memory (.addressed base) twoLongWords mabGroup pe cycle).low =
        if twoLongWords then memory (addressAt base
          (cycle.val * 32 + mabGroup.val * 8 + pe.val + 4)) else 0 := by
  cases twoLongWords <;> simp [m4bcast, readL1Long, addressAt]

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
