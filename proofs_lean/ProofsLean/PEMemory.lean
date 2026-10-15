import ProofsLean.IntegerALU

/- MN-Core 2 manual (2026-06-02), §3.6.1.6–12.
Combinational address/read/write primitives, not an instruction-step model.
No mask, hazard, parallel-port legality, or precision conversion is implemented. -/
namespace ProofsLean.MNCore.PEMemory

inductive Bank where
  | lm0 | lm1 | grf0 | grf1 | t
  deriving DecidableEq, Repr

def Bank.capacity : Bank → Nat
  | .lm0 | .lm1 => 4096
  | .grf0 | .grf1 => 512
  | .t => 16

theorem Bank.capacity_positive (bank : Bank) : 0 < bank.capacity := by cases bank <;> decide

inductive Width where
  | word | long | double
  deriving DecidableEq, Repr

def Width.words : Width → Nat
  | .word => 1
  | .long => 2
  | .double => 4

/-- T always reads/writes four words, irrespective of the written width prefix. -/
def count (bank : Bank) (width : Width) : Nat :=
  if bank = .t then 4 else width.words

theorem count_le_four (bank : Bank) (width : Width) : count bank width ≤ 4 := by
  cases bank <;> cases width <;> decide

inductive Schedule where
  /-- Stride is measured in 32-bit words, not accesses. -/
  | auto (base strideWords : Nat)
  | flat (addresses : Fin 4 → Nat)

def Schedule.at (schedule : Schedule) (cycle : Fin 4) : Nat :=
  match schedule with
  | .auto base stride => base + stride * cycle.val
  | .flat addresses => addresses cycle

/-- Syntax must establish these checks before executing a descriptor. This
predicate alone is not the full VSM legality rule. -/
def Schedule.WellFormed (schedule : Schedule) (bank : Bank) (width : Width) : Prop :=
  match schedule with
  | .auto base stride => base < bank.capacity ∧ base % width.words = 0 ∧ stride % width.words = 0
  | .flat addresses => ∀ cycle, addresses cycle < bank.capacity ∧ addresses cycle % width.words = 0

inductive Adjustment where
  | direct
  | tIndirect (value : BitVec 64)
  | madpe (threshold : Fin 4)

def Adjustment.offset (adjustment : Adjustment) (width : Width) (pe : Fin 4) : Nat :=
  match adjustment with
  | .direct => 0
  | .tIndirect value => value.toNat
  | .madpe threshold => if pe.val ≤ threshold.val then width.words else 0

def Adjustment.Allowed (adjustment : Adjustment) (bank : Bank) : Prop :=
  match adjustment with
  | .direct => True
  | .tIndirect _ => bank = .lm0
  | .madpe _ => bank = .lm0 ∨ bank = .lm1

def baseOffset (bank : Bank) (bar : BitVec 12) : Nat :=
  match bank with
  | .lm0 | .lm1 => bar.toNat
  | _ => 0

/-- Dynamic BAR/T offsets may be unaligned: round down after adding them.
The final memory address wraps. T uses a dedicated four-word cycle region. -/
def address (bank : Bank) (width : Width) (schedule : Schedule) (bar : BitVec 12)
    (adjustment : Adjustment) (pe cycle : Fin 4) : Fin bank.capacity :=
  let raw := if bank = .t then 4 * cycle.val else
    baseOffset bank bar + schedule.at cycle + adjustment.offset width pe
  let aligned := raw / count bank width * count bank width
  ⟨aligned % bank.capacity, Nat.mod_lt _ bank.capacity_positive⟩

theorem address_aligned (bank : Bank) (width : Width) (schedule : Schedule) (bar : BitVec 12)
    (adjustment : Adjustment) (pe cycle : Fin 4) :
    (address bank width schedule bar adjustment pe cycle).val % count bank width = 0 := by
  have divides : count bank width ∣ bank.capacity := by cases bank <;> cases width <;> decide
  dsimp [address]
  rw [Nat.mod_mod_of_dvd _ divides]
  exact Nat.mul_mod_left _ _

abbrev Memory (bank : Bank) := Fin bank.capacity → BitVec 32
abbrev WordBus := Fin 4 → BitVec 32

def advance (bank : Bank) (start : Fin bank.capacity) (offset : Nat) : Fin bank.capacity :=
  ⟨(start.val + offset) % bank.capacity, Nat.mod_lt _ bank.capacity_positive⟩

def distance (bank : Bank) (start target : Fin bank.capacity) : Nat :=
  (target.val + bank.capacity - start.val) % bank.capacity

theorem distance_advance (bank : Bank) (start : Fin bank.capacity) (index : Fin 4) :
    distance bank start (advance bank start index.val) = index.val := by
  have bounded := start.isLt
  have indexBound := index.isLt
  cases bank <;> simp only [distance, advance, Bank.capacity] at * <;> omega

/-- Narrow reads place words at the MSB side of the four-word bus and zero
the unused words; no replication or sign extension occurs here. -/
def readWords (bank : Bank) (width : Width) (memory : Memory bank)
    (start : Fin bank.capacity) : WordBus := fun index =>
  if index.val < count bank width then memory (advance bank start index.val) else 0

/-- Unmasked instantaneous writes. The instruction model must separately
schedule writes after all reads and check hazards and parallel ports. -/
def writeWords (bank : Bank) (width : Width) (memory : Memory bank)
    (start : Fin bank.capacity) (data : WordBus) : Memory bank := fun target =>
  if within : distance bank start target < count bank width then
    data ⟨distance bank start target, Nat.lt_of_lt_of_le within (count_le_four bank width)⟩
  else memory target

theorem write_preserves_outside (bank : Bank) (width : Width) (memory : Memory bank)
    (start target : Fin bank.capacity) (data : WordBus)
    (outside : count bank width ≤ distance bank start target) :
    writeWords bank width memory start data target = memory target := by
  simp [writeWords, Nat.not_lt.mpr outside]

theorem read_after_write (bank : Bank) (width : Width) (memory : Memory bank)
    (start : Fin bank.capacity) (data : WordBus) (index : Fin 4)
    (within : index.val < count bank width) :
    readWords bank width (writeWords bank width memory start data) start index = data index := by
  simp [readWords, within, writeWords, distance_advance]

def pack (data : WordBus) : IntegerALU.Bus :=
  ⟨data 0 ++ data 1, data 2 ++ data 3⟩

theorem t_ignores_width (width : Width) (schedule : Schedule) (bar : BitVec 12)
    (adjustment : Adjustment) (pe cycle : Fin 4) :
    address .t width schedule bar adjustment pe cycle =
      address .t .double (.auto 0 0) 0 .direct 0 cycle := by
  simp [address, count]

example : (address .lm0 .double (.auto 4092 4) 7 .direct 0 1).val = 4 := by decide
example : (address .lm0 .long (.auto 0 0) 0 (.tIndirect 4095) 0 0).val = 4094 := by decide
example : (address .lm0 .double (.auto 0 0) 0 (.madpe 2) 2 0).val = 4 := by decide
example : (address .lm0 .double (.auto 0 0) 0 (.madpe 2) 3 0).val = 0 := by decide

end ProofsLean.MNCore.PEMemory
