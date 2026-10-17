import ProofsLean.SingleFMA

/-! Single-precision addition and the value layout for problem 5 (AddCol vec).
The addition is the MAU's exact `a * 1 + b` datapath. The vector theorem
captures the per-PE 4x4 layout and the two eight-element output chunks; actual
forwarding/T-register transitions and physical memory addressing remain
separate proof obligations. -/
namespace ProofsLean.MNCore.FloatAdd

def add (left right : BitVec 32) : BitVec 32 :=
  SingleFMA.singleFma left 0x3F800000 right

def abstractAdd {Atom : Type}
    (left right : AbstractValue Atom (BitVec 32)) :
    AbstractValue Atom (BitVec 32) :=
  AbstractValue.ternary .floatingMau (fun a _ c => add a c) left
    (AbstractValue.constant .floatingMau 0x3F800000) right

theorem abstractAdd_evaluation {Atom : Type}
    (left right : AbstractValue Atom (BitVec 32))
    (environment : Atom → BitVec 32) :
    (abstractAdd left right).evaluate environment =
      add (left.evaluate environment) (right.evaluate environment) := by
  exact AbstractValue.ternary_evaluation .floatingMau (fun a _ c => add a c) left
    (AbstractValue.constant .floatingMau 0x3F800000) right environment

theorem add_zero_to_one : add 0x3F800000 0x00000000 = 0x3F800000 := by decide

theorem add_one_and_two : add 0x3F800000 0x40000000 = 0x40400000 := by decide

def addBus (left right : BitVec 64) : BitVec 64 :=
  add (left.extractLsb' 32 32) (right.extractLsb' 32 32) ++
    add (left.extractLsb' 0 32) (right.extractLsb' 0 32)

theorem addBus_high (left right : BitVec 64) :
    (addBus left right).extractLsb' 32 32 =
      add (left.extractLsb' 32 32) (right.extractLsb' 32 32) := by
  simp only [addBus]
  rw [BitVec.extractLsb'_append_eq_left]

theorem addBus_low (left right : BitVec 64) :
    (addBus left right).extractLsb' 0 32 =
      add (left.extractLsb' 0 32) (right.extractLsb' 0 32) := by
  simp only [addBus]
  rw [BitVec.extractLsb'_append_eq_right]

theorem abstractAdd_dependencies_are_sound {Atom : Type}
    (left right : AbstractValue Atom (BitVec 32))
    (leftEnv rightEnv : Atom → BitVec 32)
    (agree : ∀ atom, atom ∈ (abstractAdd left right).dependencies →
      leftEnv atom = rightEnv atom) :
    (abstractAdd left right).evaluate leftEnv =
      (abstractAdd left right).evaluate rightEnv :=
  AbstractValue.depends_only_on_inputs _ leftEnv rightEnv agree

abbrev MatrixWords := Fin 16 → BitVec 32
abbrev VectorWords := Fin 4 → BitVec 32

def vectorColumn (index : Fin 16) : Fin 4 :=
  ⟨index.val % 4, Nat.mod_lt _ (by decide)⟩

def matrixAnswer (matrix : MatrixWords) (vector : VectorWords) : MatrixWords :=
  fun index => add (matrix index) (vector (vectorColumn index))

def chunkIndex (line : Fin 2) (lane : Fin 8) : Fin 16 :=
  ⟨8 * line.val + lane.val, by
    have hl := line.isLt
    have hw := lane.isLt
    omega⟩

def writeChunk (matrix : MatrixWords) (vector : VectorWords)
    (output : MatrixWords) (line : Fin 2) : MatrixWords := fun index =>
  if index.val / 8 = line.val then matrixAnswer matrix vector index else output index

def twoLineResult (matrix : MatrixWords) (vector : VectorWords)
    (initialOutput : MatrixWords) : MatrixWords :=
  writeChunk matrix vector
    (writeChunk matrix vector initialOutput ⟨0, by decide⟩) ⟨1, by decide⟩

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

theorem twoLineResult_correct (matrix : MatrixWords) (vector : VectorWords)
    (initialOutput : MatrixWords) (index : Fin 16) :
    twoLineResult matrix vector initialOutput index = matrixAnswer matrix vector index := by
  simp only [twoLineResult, writeChunk, matrixAnswer]
  repeat (first | rfl | split)
  have hi := index.isLt
  omega

end ProofsLean.MNCore.FloatAdd
