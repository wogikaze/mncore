import ProofsLean.PEMemory

/- SDM §3.6.2 PE-memory destination mask application. This is a combinational
store primitive; instruction timing, target selection, hazards, and port
legality are modeled elsewhere or remain open. -/
namespace ProofsLean.MNCore.PEMemory

/-- Per-word write bits for masked PE-memory stores. With `ll` masks each
selected flag enables one full word. Otherwise the first long word is selected
by its four half-word flags and the second long word is always written. -/
def selectedWordMask (flags : BitVec 4) (longLong : Bool) (index : Fin 4) :
    BitVec 32 :=
  if longLong then
    if flags.getLsbD (3 - index.val) then BitVec.allOnes 32 else 0
  else if index.val < 2 then
    let high := flags.getLsbD (3 - 2 * index.val)
    let low := flags.getLsbD (2 - 2 * index.val)
    (if high then (0xffff : BitVec 32) <<< 16 else 0) |||
      (if low then (0xffff : BitVec 32) else 0)
  else BitVec.allOnes 32

def mergeSelectedWord (old new enable : BitVec 32) : BitVec 32 :=
  (old &&& ~~~enable) ||| (new &&& enable)

/-- Apply one ALU cycle's mask to a scheduled PE-memory access. -/
def writeWordsMasked (bank : Bank) (width : Width) (memory : Memory bank)
    (start : Fin bank.capacity) (data : WordBus) (flags : BitVec 4)
    (longLong : Bool) : Memory bank := fun target =>
  if within : distance bank start target < count bank width then
    let index : Fin 4 := ⟨distance bank start target,
      Nat.lt_of_lt_of_le within (count_le_four bank width)⟩
    mergeSelectedWord (memory target) (data index)
      (selectedWordMask flags longLong index)
  else memory target

theorem writeWordsMasked_at (bank : Bank) (width : Width)
    (memory : Memory bank) (start target : Fin bank.capacity) (data : WordBus)
    (flags : BitVec 4) (longLong : Bool)
    (within : distance bank start target < count bank width) :
    writeWordsMasked bank width memory start data flags longLong target =
      mergeSelectedWord (memory target)
        (data ⟨distance bank start target,
          Nat.lt_of_lt_of_le within (count_le_four bank width)⟩)
        (selectedWordMask flags longLong
          ⟨distance bank start target,
            Nat.lt_of_lt_of_le within (count_le_four bank width)⟩) := by
  simp [writeWordsMasked, within]

theorem writeWordsMasked_preserves_outside (bank : Bank) (width : Width)
    (memory : Memory bank) (start target : Fin bank.capacity) (data : WordBus)
    (flags : BitVec 4) (longLong : Bool)
    (outside : count bank width ≤ distance bank start target) :
    writeWordsMasked bank width memory start data flags longLong target = memory target := by
  simp [writeWordsMasked, Nat.not_lt.mpr outside]

theorem selectedWordMask_allOnes (longLong : Bool) (index : Fin 4) :
    selectedWordMask (BitVec.allOnes 4) longLong index = BitVec.allOnes 32 := by
  cases longLong
  · by_cases h : index.val < 2
    · have h0 : index.val = 0 ∨ index.val = 1 := by omega
      rcases h0 with h0 | h1
      · simp [selectedWordMask, h0]
      · simp [selectedWordMask, h1]
    · simp [selectedWordMask, h]
  · simp only [selectedWordMask, BitVec.getLsbD_allOnes]
    have hi : 3 - index.val < 4 := by have := index.isLt; omega
    simp [hi]

theorem writeWordsMasked_allOnes (bank : Bank) (width : Width)
    (memory : Memory bank) (start : Fin bank.capacity) (data : WordBus)
    (longLong : Bool) :
    writeWordsMasked bank width memory start data (BitVec.allOnes 4) longLong =
      writeWords bank width memory start data := by
  funext target
  by_cases within : distance bank start target < count bank width
  · simp only [writeWordsMasked, writeWords, dite_eq_left within]
    let index : Fin 4 := ⟨distance bank start target,
      Nat.lt_of_lt_of_le within (count_le_four bank width)⟩
    change mergeSelectedWord (memory target) (data index)
      (selectedWordMask (BitVec.allOnes 4) longLong index) = data index
    rw [selectedWordMask_allOnes]
    simp [mergeSelectedWord]
    exact BitVec.and_allOnes
  · simp [writeWordsMasked, writeWords, within]

theorem readWordsMasked_after_allOnes (bank : Bank) (width : Width)
    (memory : Memory bank) (start : Fin bank.capacity) (data : WordBus)
    (index : Fin 4) (within : index.val < count bank width)
    (longLong : Bool) :
    readWords bank width
      (writeWordsMasked bank width memory start data (BitVec.allOnes 4) longLong)
      start index = data index := by
  rw [writeWordsMasked_allOnes]
  exact read_after_write bank width memory start data index within

theorem zeroLongMask_on_double_access (bank : Bank) (memory : Memory bank)
    (start : Fin bank.capacity) (data : WordBus) (index : Fin 4) :
    writeWordsMasked bank .double memory start data 0 false
      (advance bank start index.val) =
      if index.val < 2 then memory (advance bank start index.val) else data index := by
  have hdistance : distance bank start (advance bank start index.val) = index.val := by
    simpa using distance_advance bank start index
  have hwithin : distance bank start (advance bank start index.val) < count bank .double := by
    rw [hdistance]
    simp [count, Width.words]
  rw [writeWordsMasked_at bank .double memory start
    (advance bank start index.val) data 0 false hwithin]
  have hindex : (⟨distance bank start (advance bank start index.val),
      Nat.lt_of_lt_of_le hwithin (count_le_four bank .double)⟩ : Fin 4) = index :=
    Fin.ext hdistance
  rw [hindex]
  by_cases high : index.val < 2
  · simp [selectedWordMask, high, mergeSelectedWord]
    exact BitVec.and_allOnes
  · simp [selectedWordMask, high, mergeSelectedWord]
    exact BitVec.and_allOnes

theorem selectedWordMask_zero_high : selectedWordMask 0 false 0 = 0 := by decide
theorem selectedWordMask_zero_lowLong :
    selectedWordMask 0 false 2 = BitVec.allOnes 32 := by decide

example : selectedWordMask 0 false 1 = 0 := by decide
example : selectedWordMask 0 false 3 = BitVec.allOnes 32 := by decide
example : selectedWordMask 0 true 2 = 0 := by decide

end ProofsLean.MNCore.PEMemory
