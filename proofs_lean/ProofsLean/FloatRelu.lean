import ProofsLean.OperatorAbstraction

/-! Value abstraction for the single-precision `frelu` used by problem 3.
The challenge input domain contains finite values only. IEEE negative zero
compares equal to zero, so both signed zeros select the second operand. -/
namespace ProofsLean.MNCore.FloatRelu

def isZero (value : BitVec 32) : Bool :=
  value.extractLsb' 0 31 == 0

def isNonnegative (value : BitVec 32) : Bool :=
  !value.msb || isZero value

def negativeZero : BitVec 32 := 0x80000000

def relu (condition value : BitVec 32) : BitVec 32 :=
  if isNonnegative condition then value else negativeZero

def abstractRelu {Atom : Type}
    (condition value : AbstractValue Atom (BitVec 32)) :
    AbstractValue Atom (BitVec 32) :=
  AbstractValue.binary .floatingMau relu condition value

theorem abstractRelu_evaluation {Atom : Type}
    (condition value : AbstractValue Atom (BitVec 32))
    (environment : Atom → BitVec 32) :
    (abstractRelu condition value).evaluate environment =
      relu (condition.evaluate environment) (value.evaluate environment) := by
  exact AbstractValue.binary_evaluation .floatingMau relu condition value environment

theorem relu_positive (value : BitVec 32) : relu 0x3F800000 value = value := by
  have h : isNonnegative (0x3F800000 : BitVec 32) = true := by decide
  change (if isNonnegative (0x3F800000 : BitVec 32) then value else negativeZero) = value
  rw [h]
  rfl

theorem relu_negative (value : BitVec 32) : relu 0xBF800000 value = negativeZero := by
  have h : isNonnegative (0xBF800000 : BitVec 32) = false := by decide
  change (if isNonnegative (0xBF800000 : BitVec 32) then value else negativeZero) = negativeZero
  rw [h]
  rfl

theorem relu_positive_zero (value : BitVec 32) : relu 0 value = value := by
  have h : isNonnegative (0 : BitVec 32) = true := by decide
  change (if isNonnegative (0 : BitVec 32) then value else negativeZero) = value
  rw [h]
  rfl

theorem relu_negative_zero (value : BitVec 32) : relu 0x80000000 value = value := by
  have h : isNonnegative (0x80000000 : BitVec 32) = true := by decide
  change (if isNonnegative (0x80000000 : BitVec 32) then value else negativeZero) = value
  rw [h]
  rfl

theorem abstractRelu_dependencies_are_sound {Atom : Type}
    (condition value : AbstractValue Atom (BitVec 32))
    (leftEnv rightEnv : Atom → BitVec 32)
    (agree : ∀ atom, atom ∈ (abstractRelu condition value).dependencies →
      leftEnv atom = rightEnv atom) :
    (abstractRelu condition value).evaluate leftEnv =
      (abstractRelu condition value).evaluate rightEnv :=
  AbstractValue.depends_only_on_inputs _ leftEnv rightEnv agree

abbrev Words := Fin 16 → BitVec 32

def chunkIndex (line : Fin 2) (lane : Fin 8) : Fin 16 :=
  ⟨8 * line.val + lane.val, by
    have hl := line.isLt
    have hw := lane.isLt
    omega⟩

def vectorAnswer (input : Words) : Words := fun index =>
  relu (input index) (input index)

def writeChunk (input output : Words) (line : Fin 2) : Words := fun index =>
  if index.val / 8 = line.val then vectorAnswer input index else output index

def twoLineResult (input initialOutput : Words) : Words :=
  writeChunk input (writeChunk input initialOutput ⟨0, by decide⟩)
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

theorem twoLineResult_correct (input initialOutput : Words) (index : Fin 16) :
    twoLineResult input initialOutput index = vectorAnswer input index := by
  simp only [twoLineResult, writeChunk, vectorAnswer]
  repeat (first | rfl | split)
  have hi := index.isLt
  omega

end ProofsLean.MNCore.FloatRelu
