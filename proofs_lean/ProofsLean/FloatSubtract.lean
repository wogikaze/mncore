import ProofsLean.SingleFMA

/-! A bit-level model of the `fvadd x -y out` datapath used by problem 1.a-b.
The instruction is a fused multiply-add with a unit multiplier and a
sign-flipped second addend. This file proves the constant/dependency tracking
for that cross-unit operation; full address and issue semantics remain separate
obligations. -/
namespace ProofsLean.MNCore.FloatSubtract

def negateBits (value : BitVec 32) : BitVec 32 := value ^^^ 0x80000000

def subtract (left right : BitVec 32) : BitVec 32 :=
  SingleFMA.singleFma left 0x3F800000 (negateBits right)

/-- Apply `fvadd x -y` independently to both float lanes of one PE bus. -/
def subtractBus (left right : BitVec 64) : BitVec 64 :=
  subtract (left.extractLsb' 32 32) (right.extractLsb' 32 32) ++
    subtract (left.extractLsb' 0 32) (right.extractLsb' 0 32)

theorem subtractBus_high (left right : BitVec 64) :
    (subtractBus left right).extractLsb' 32 32 =
      subtract (left.extractLsb' 32 32) (right.extractLsb' 32 32) := by
  simp only [subtractBus]
  rw [BitVec.extractLsb'_append_eq_left]

theorem subtractBus_low (left right : BitVec 64) :
    (subtractBus left right).extractLsb' 0 32 =
      subtract (left.extractLsb' 0 32) (right.extractLsb' 0 32) := by
  simp only [subtractBus]
  rw [BitVec.extractLsb'_append_eq_right]

def abstractSubtractBus {Atom : Type}
    (left right : AbstractValue Atom (BitVec 64)) :
    AbstractValue Atom (BitVec 64) :=
  AbstractValue.binary .floatingMau subtractBus left right

abbrev Words := Fin 16 → BitVec 32

/-- The public Mat Sub answer writes eight float words in each MAU line. -/
def chunkIndex (line : Fin 2) (lane : Fin 8) : Fin 16 :=
  ⟨8 * line.val + lane.val, by
    have hl := line.isLt
    have hw := lane.isLt
    omega⟩

def vectorAnswer (left right : Words) : Words := fun index =>
  subtract (left index) (right index)

def writeChunk (left right output : Words) (line : Fin 2) : Words := fun index =>
  if index.val / 8 = line.val then vectorAnswer left right index else output index

def twoLineResult (left right initialOutput : Words) : Words :=
  writeChunk left right (writeChunk left right initialOutput ⟨0, by decide⟩)
    ⟨1, by decide⟩

theorem chunkIndex_injective (line₁ line₂ : Fin 2) (lane₁ lane₂ : Fin 8)
    (equal : chunkIndex line₁ lane₁ = chunkIndex line₂ lane₂) :
    line₁ = line₂ ∧ lane₁ = lane₂ := by
  have values := congrArg Fin.val equal
  simp only [chunkIndex, Fin.val_mk] at values
  have lineEqual : line₁.val = line₂.val := by omega
  have laneEqual : lane₁.val = lane₂.val := by omega
  exact ⟨Fin.ext lineEqual, Fin.ext laneEqual⟩

theorem chunkIndex_covers_all_words (index : Fin 16) :
    ∃ line : Fin 2, ∃ lane : Fin 8, chunkIndex line lane = index := by
  let line : Fin 2 := ⟨index.val / 8, by have hi := index.isLt; omega⟩
  let lane : Fin 8 := ⟨index.val % 8, Nat.mod_lt _ (by decide)⟩
  refine ⟨line, lane, ?_⟩
  apply Fin.ext
  simp [chunkIndex, line, lane]
  omega

theorem twoLineResult_correct (left right initialOutput : Words) (index : Fin 16) :
    twoLineResult left right initialOutput index = vectorAnswer left right index := by
  simp only [twoLineResult, writeChunk, vectorAnswer]
  repeat (first | rfl | split)
  have hi := index.isLt
  omega

theorem abstractSubtractBus_evaluation {Atom : Type}
    (left right : AbstractValue Atom (BitVec 64))
    (environment : Atom → BitVec 64) :
    (abstractSubtractBus left right).evaluate environment =
      subtractBus (left.evaluate environment) (right.evaluate environment) := by
  exact AbstractValue.binary_evaluation .floatingMau subtractBus left right environment

theorem abstractSubtractBus_dependencies_are_sound {Atom : Type}
    (left right : AbstractValue Atom (BitVec 64))
    (leftEnv rightEnv : Atom → BitVec 64)
    (agree : ∀ atom, atom ∈ (abstractSubtractBus left right).dependencies →
      leftEnv atom = rightEnv atom) :
    (abstractSubtractBus left right).evaluate leftEnv =
      (abstractSubtractBus left right).evaluate rightEnv :=
  AbstractValue.depends_only_on_inputs _ leftEnv rightEnv agree

def abstractSubtract {Atom : Type}
    (left right : AbstractValue Atom (BitVec 32)) :
    AbstractValue Atom (BitVec 32) :=
  AbstractValue.ternary .floatingMau (fun a _ c => subtract a c) left
    (AbstractValue.constant .floatingMau 0x3F800000) right

theorem abstractSubtract_evaluation {Atom : Type}
    (left right : AbstractValue Atom (BitVec 32))
    (environment : Atom → BitVec 32) :
    (abstractSubtract left right).evaluate environment =
      subtract (left.evaluate environment) (right.evaluate environment) := by
  exact AbstractValue.ternary_evaluation .floatingMau (fun a _ c => subtract a c) left
    (AbstractValue.constant .floatingMau 0x3F800000) right environment

theorem subtract_one_zero : subtract 0x3F800000 0x3F800000 = 0 := by decide

theorem subtract_positive : subtract 0x41200000 0x40000000 = 0x41000000 := by decide

theorem subtract_negative : subtract 0x40000000 0x41200000 = 0xC1000000 := by decide

theorem subtract_preserves_dependencies {Atom : Type}
    (left right : AbstractValue Atom (BitVec 32))
    (leftEnv rightEnv : Atom → BitVec 32)
    (agree : ∀ atom, atom ∈ (abstractSubtract left right).dependencies →
      leftEnv atom = rightEnv atom) :
    (abstractSubtract left right).evaluate leftEnv =
      (abstractSubtract left right).evaluate rightEnv :=
  AbstractValue.depends_only_on_inputs _ leftEnv rightEnv agree

end ProofsLean.MNCore.FloatSubtract
