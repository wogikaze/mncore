import ProofsLean.SingleFMA

/-! Value-level model for the `fvmul` stage of problem 2 (multiply by 7).
As in the MAU datapath, multiplication is the FMA product with a zero
accumulator. The file covers one lane; the 4-line memory schedule is tracked
separately and is not yet connected to `PEMachine`. -/
namespace ProofsLean.MNCore.FloatMultiply

def multiply (left right : BitVec 32) : BitVec 32 :=
  SingleFMA.singleFma left right 0

def abstractMultiply {Atom : Type}
    (left right : AbstractValue Atom (BitVec 32)) :
    AbstractValue Atom (BitVec 32) :=
  AbstractValue.ternary .floatingMau (fun a b _ => multiply a b) left right
    (AbstractValue.constant .floatingMau 0)

theorem abstractMultiply_evaluation {Atom : Type}
    (left right : AbstractValue Atom (BitVec 32))
    (environment : Atom → BitVec 32) :
    (abstractMultiply left right).evaluate environment =
      multiply (left.evaluate environment) (right.evaluate environment) := by
  exact AbstractValue.ternary_evaluation .floatingMau
    (fun a b _ => multiply a b) left right
    (AbstractValue.constant .floatingMau 0) environment

def seven : BitVec 32 := 0x40E00000

/-- Apply `fvmul` independently to the two single-precision lanes in a PE bus. -/
def multiplyBus (left right : BitVec 64) : BitVec 64 :=
  multiply (left.extractLsb' 32 32) (right.extractLsb' 32 32) ++
    multiply (left.extractLsb' 0 32) (right.extractLsb' 0 32)

def sevenBus : BitVec 64 := seven ++ seven

def multiplySevenBus (input : BitVec 64) : BitVec 64 :=
  multiplyBus input sevenBus

theorem multiplySevenBus_high (input : BitVec 64) :
    (multiplySevenBus input).extractLsb' 32 32 =
      multiply (input.extractLsb' 32 32) seven := by
  simp only [multiplySevenBus, multiplyBus, sevenBus]
  rw [BitVec.extractLsb'_append_eq_left, BitVec.extractLsb'_append_eq_left]

theorem multiplySevenBus_low (input : BitVec 64) :
    (multiplySevenBus input).extractLsb' 0 32 =
      multiply (input.extractLsb' 0 32) seven := by
  simp only [multiplySevenBus, multiplyBus, sevenBus]
  rw [BitVec.extractLsb'_append_eq_right, BitVec.extractLsb'_append_eq_right]

def abstractMultiplySevenBus {Atom : Type}
    (input : AbstractValue Atom (BitVec 64)) :
    AbstractValue Atom (BitVec 64) :=
  AbstractValue.unary .floatingMau multiplySevenBus input

abbrev Words := Fin 32 → BitVec 32

/-- The four public `fvmul` lines each cover eight consecutive float words. -/
def chunkIndex (line : Fin 4) (lane : Fin 8) : Fin 32 :=
  ⟨8 * line.val + lane.val, by
    have hl := line.isLt
    have hw := lane.isLt
    omega⟩

theorem chunkIndex_injective (line₁ line₂ : Fin 4) (lane₁ lane₂ : Fin 8)
    (equal : chunkIndex line₁ lane₁ = chunkIndex line₂ lane₂) :
    line₁ = line₂ ∧ lane₁ = lane₂ := by
  have values := congrArg Fin.val equal
  simp only [chunkIndex, Fin.val_mk] at values
  have lineEqual : line₁.val = line₂.val := by omega
  have laneEqual : lane₁.val = lane₂.val := by omega
  exact ⟨Fin.ext lineEqual, Fin.ext laneEqual⟩

def vectorAnswer (input : Words) : Words := fun index =>
  multiply (input index) seven

def scheduledLane (input : Words) (line : Fin 4) (lane : Fin 8) : BitVec 32 :=
  multiply (input (chunkIndex line lane)) seven

def writeChunk (input output : Words) (line : Fin 4) : Words := fun index =>
  if index.val / 8 = line.val then vectorAnswer input index else output index

def fourLineResult (input initialOutput : Words) : Words :=
  writeChunk input
    (writeChunk input
      (writeChunk input
        (writeChunk input initialOutput ⟨0, by decide⟩)
        ⟨1, by decide⟩)
      ⟨2, by decide⟩)
    ⟨3, by decide⟩

theorem fourLineResult_correct (input initialOutput : Words) (index : Fin 32) :
    fourLineResult input initialOutput index = vectorAnswer input index := by
  simp only [fourLineResult, writeChunk, vectorAnswer]
  repeat (first | rfl | split)
  have hi := index.isLt
  omega

theorem scheduledLane_correct (input : Words) (line : Fin 4) (lane : Fin 8) :
    scheduledLane input line lane = vectorAnswer input (chunkIndex line lane) := rfl

theorem chunkIndex_covers_all_words (index : Fin 32) :
    ∃ line : Fin 4, ∃ lane : Fin 8, chunkIndex line lane = index := by
  let line : Fin 4 := ⟨index.val / 8, by have hi := index.isLt; omega⟩
  let lane : Fin 8 := ⟨index.val % 8, Nat.mod_lt _ (by decide)⟩
  refine ⟨line, lane, ?_⟩
  apply Fin.ext
  simp [chunkIndex, line, lane]
  omega

theorem every_word_has_scheduled_answer (input : Words) (index : Fin 32) :
    ∃ line : Fin 4, ∃ lane : Fin 8,
      scheduledLane input line lane = vectorAnswer input index := by
  obtain ⟨line, lane, covers⟩ := chunkIndex_covers_all_words index
  exact ⟨line, lane, by rw [scheduledLane_correct, covers]⟩

theorem abstractMultiplySevenBus_evaluation {Atom : Type}
    (input : AbstractValue Atom (BitVec 64))
    (environment : Atom → BitVec 64) :
    (abstractMultiplySevenBus input).evaluate environment =
      multiplySevenBus (input.evaluate environment) := by
  exact AbstractValue.unary_evaluation .floatingMau multiplySevenBus input environment

theorem abstractMultiplySevenBus_dependencies_are_sound {Atom : Type}
    (input : AbstractValue Atom (BitVec 64))
    (leftEnv rightEnv : Atom → BitVec 64)
    (agree : ∀ atom, atom ∈ (abstractMultiplySevenBus input).dependencies →
      leftEnv atom = rightEnv atom) :
    (abstractMultiplySevenBus input).evaluate leftEnv =
      (abstractMultiplySevenBus input).evaluate rightEnv :=
  AbstractValue.depends_only_on_inputs _ leftEnv rightEnv agree

theorem seven_times_one : multiply 0x3F800000 seven = seven := by decide

theorem seven_times_zero : multiply 0 seven = 0 := by decide

theorem seven_times_two : multiply 0x40000000 seven = 0x41600000 := by decide

theorem abstractMultiply_preserves_dependencies {Atom : Type}
    (left right : AbstractValue Atom (BitVec 32))
    (leftEnv rightEnv : Atom → BitVec 32)
    (agree : ∀ atom, atom ∈ (abstractMultiply left right).dependencies →
      leftEnv atom = rightEnv atom) :
    (abstractMultiply left right).evaluate leftEnv =
      (abstractMultiply left right).evaluate rightEnv :=
  AbstractValue.depends_only_on_inputs _ leftEnv rightEnv agree

end ProofsLean.MNCore.FloatMultiply
