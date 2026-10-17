import ProofsLean.ByteSwap
import ProofsLean.SingleFMA

/-! Bit-level datapath reconstruction of the public Convert Endian answer.

The integer barrel shift first exchanges the two 16-bit halves within each
32-bit lane. The single
precision MAU FMA transforms the immediate bit pattern into the halfword shift
count used by the next issue word. That barrel shift rotates each 16-bit lane
by one byte, and the destination selector exchanges the 32-bit lanes again. -/
namespace ProofsLean.MNCore.ConvertEndian

def swap32 (word : BitVec 64) : BitVec 64 :=
  (word.extractLsb' 0 32) ++ (word.extractLsb' 32 32)

def swapHalfwordsWithin32 (word : BitVec 64) : BitVec 64 :=
  (word.extractLsb' 32 16) ++ (word.extractLsb' 48 16) ++
    (word.extractLsb' 0 16) ++ (word.extractLsb' 16 16)

def ibsl (word : BitVec 64) : BitVec 64 :=
  (word.extractLsb' 32 32).rotateLeft 16 ++
    (word.extractLsb' 0 32).rotateLeft 16

def sbsl (word : BitVec 64) : BitVec 64 :=
  (word.extractLsb' 48 16).rotateLeft 8 ++
    (word.extractLsb' 32 16).rotateLeft 8 ++
    (word.extractLsb' 16 16).rotateLeft 8 ++
    (word.extractLsb' 0 16).rotateLeft 8

/-- The FMA is issued with three copies of the same immediate lane. -/
def immediateWord : BitVec 32 := 0x34F80010
def mauShiftWord : BitVec 32 := 0x34F80018

theorem immediate_fma_generates_shift_word :
    SingleFMA.singleFma immediateWord immediateWord immediateWord = mauShiftWord := by
  decide

theorem ibsl_is_32bit_lane_rotate (word : BitVec 64) :
    ibsl word = swapHalfwordsWithin32 word := by
  unfold ibsl swapHalfwordsWithin32
  bv_decide

/-- The `[1,0,3,2]` destination selector exchanges the two 32-bit groups. -/
def selector2103 (word : BitVec 64) : BitVec 64 := swap32 word

def answerDatapath (input : BitVec 64) : BitVec 64 :=
  selector2103 (sbsl (ibsl input))

theorem answerDatapath_is_byteSwap (input : BitVec 64) :
    answerDatapath input = byteSwap64 input := by
  unfold answerDatapath selector2103 sbsl ibsl swap32 byteSwap64
  bv_decide

theorem answerDatapath_involutive (input : BitVec 64) :
    answerDatapath (answerDatapath input) = input := by
  rw [answerDatapath_is_byteSwap, answerDatapath_is_byteSwap]
  exact byteSwap64_involutive input

def packedSingleFma (a b c : BitVec 64) : BitVec 64 :=
  (SingleFMA.singleFma (a.extractLsb' 32 32) (b.extractLsb' 32 32)
    (c.extractLsb' 32 32)) ++
  (SingleFMA.singleFma (a.extractLsb' 0 32) (b.extractLsb' 0 32)
    (c.extractLsb' 0 32))

def mauShiftBus : BitVec 64 := mauShiftWord ++ mauShiftWord
def immediateBus : BitVec 64 := immediateWord ++ immediateWord

def shiftHalfword (value count : BitVec 16) : BitVec 16 :=
  let raw := count.toNat % 32
  let amount := if raw >= 16 then raw - 16 else raw
  value.rotateLeft amount

def sbslWithShift (word shifts : BitVec 64) : BitVec 64 :=
  shiftHalfword (word.extractLsb' 48 16) (shifts.extractLsb' 48 16) ++
    shiftHalfword (word.extractLsb' 32 16) (shifts.extractLsb' 32 16) ++
    shiftHalfword (word.extractLsb' 16 16) (shifts.extractLsb' 16 16) ++
    shiftHalfword (word.extractLsb' 0 16) (shifts.extractLsb' 0 16)

theorem packed_fma_produces_shift_bus :
    packedSingleFma immediateBus immediateBus immediateBus = mauShiftBus := by
  unfold packedSingleFma immediateBus mauShiftBus
  rw [BitVec.extractLsb'_append_eq_left, BitVec.extractLsb'_append_eq_right]
  rfl

theorem mauf_count_selects_byte_rotation (word : BitVec 64) :
    sbslWithShift word mauShiftBus = sbsl word := by
  unfold sbslWithShift sbsl shiftHalfword mauShiftBus mauShiftWord
  bv_decide

def abstractMauShift {Atom : Type} : AbstractValue Atom (BitVec 64) :=
  let immediate := AbstractValue.constant UnitKind.integerAlu immediateBus
  AbstractValue.ternary UnitKind.floatingMau packedSingleFma
    immediate immediate immediate

theorem abstractMauShift_evaluation {Atom : Type}
    (environment : Atom → BitVec 64) :
    abstractMauShift.evaluate environment = mauShiftBus := by
  calc
    abstractMauShift.evaluate environment =
        packedSingleFma immediateBus immediateBus immediateBus := by
      exact AbstractValue.ternary_evaluation UnitKind.floatingMau packedSingleFma
        (AbstractValue.constant UnitKind.integerAlu immediateBus)
        (AbstractValue.constant UnitKind.integerAlu immediateBus)
        (AbstractValue.constant UnitKind.integerAlu immediateBus) environment
    _ = mauShiftBus := packed_fma_produces_shift_bus

def abstractConvertEndian {Atom : Type}
    (input : AbstractValue Atom (BitVec 64)) : AbstractValue Atom (BitVec 64) :=
  let afterIbs := AbstractValue.unary UnitKind.integerAlu ibsl input
  let afterSbs := AbstractValue.binary UnitKind.integerAlu sbslWithShift
    afterIbs abstractMauShift
  AbstractValue.unary UnitKind.peTransfer selector2103 afterSbs

theorem abstractConvertEndian_evaluation {Atom : Type}
    (input : AbstractValue Atom (BitVec 64)) (environment : Atom → BitVec 64) :
    (abstractConvertEndian input).evaluate environment =
      answerDatapath (input.evaluate environment) := by
  unfold abstractConvertEndian
  rw [AbstractValue.unary_evaluation, AbstractValue.binary_evaluation,
    AbstractValue.unary_evaluation]
  rw [abstractMauShift_evaluation, mauf_count_selects_byte_rotation]
  rfl

theorem abstractConvertEndian_is_byteSwap {Atom : Type}
    (input : AbstractValue Atom (BitVec 64)) (environment : Atom → BitVec 64) :
    (abstractConvertEndian input).evaluate environment =
      byteSwap64 (input.evaluate environment) := by
  rw [abstractConvertEndian_evaluation, answerDatapath_is_byteSwap]

theorem abstractConvertEndian_dependencies_are_sound {Atom : Type}
    (input : AbstractValue Atom (BitVec 64))
    (leftEnvironment rightEnvironment : Atom → BitVec 64)
    (agree : ∀ atom, atom ∈ (abstractConvertEndian input).dependencies →
      leftEnvironment atom = rightEnvironment atom) :
    (abstractConvertEndian input).evaluate leftEnvironment =
      (abstractConvertEndian input).evaluate rightEnvironment :=
  AbstractValue.depends_only_on_inputs _ leftEnvironment rightEnvironment agree

end ProofsLean.MNCore.ConvertEndian
