import ProofsLean.CendAnswerExec
import ProofsLean.ByteSwapKernel

/-! # `12.convert-endian` — the value chain of lines 2 and 3

This module proves the **value chain** of the answer's tail

```
ibsl $m0v $aluf $r8v; fvfma $aluf $aluf $aluf $s0v
sbsl $aluf $mauf $n[1,0,3,2]
```

from line 1's result, and reduces the remaining executor work to an explicit,
per-line computation hypothesis (`CendTailComputation`).  It is the tail
counterpart of `ProofsLean/CendAnswerExec.lean`'s `CendAnswerExecResidual`.

## The datapath, proved here

* `byteSwap32`/`byteSwap16` and the structural identity
  `byteSwap64 x = byteSwap32 (x.extractLsb' 0 32) ++ byteSwap32 (x.extractLsb' 32 32)`
  (`byteSwap64_eq_byteSwap32_halves`), proved from the axiom-free
  `ByteSwapKernel` byte lemma.  No `bv_decide`, no `answerDatapath_is_byteSwap`.
* `rotateLeft16_low/high`: a 32-bit word rotated left by 16 has its 16-bit
  halves exchanged; `rotateLeft24_eq_byteSwap16`: a 16-bit halfword rotated
  left by 24 (equivalently, right by 8) is byte-swapped.
* `cendIbslBus`: the `ibsl` row's ALU result on the word read from LM0 is
  `⟨(w.rotateLeft 16) ++ 0, 0⟩`; its written word (`unpackALUBus … 0`) is the
  halfword swap `w.rotateLeft 16`.  The forwarded ALU slot read by line 3
  carries the same bus.
* `cendSbslData`: the `sbsl` row's ALU result on that forwarded bus, with the
  MAU bus `0x34F80018 ++ 0x34F80018` as the shift source (every halfword lane
  count is `24`, i.e. a rotate-left-by-8 inside each halfword), writes
  `byteSwap32 w`.  This is the row the task calls out: halfword rotate-left-8
  of the forwarded bus.
* `cendSbslLm1_readPair`: committing the four word writes at the `[1,0,3,2]`
  destinations and reading LM1 words `0/1` gives `data 1 ++ data 0`; with
  `data c = byteSwap32 (LM0 word c)` this is `byteSwap64 input`.

## The remaining executor computation

`CendTailComputation input s1` is the exact residual: line 1's value facts
(`CendLine1Facts`: LM0 word 0/1 are the input halves, BAR0/BAR1 are zero), the
two line steps `executeNormalizedLine` of lines 2 and 3, the forwarding slots
they install, and the committed LM1 file of line 3.  Those are precisely the
facts that require the 4096-PE walk and the per-cycle preparation of
`ProofsLean/WholeMachineStep.lean`; everything that consumes them is proved
here.  `cendAnswerExecResidual_of_line1_and_tail` assembles
`CendAnswerExecResidual`, and `cendAnswerCorrect_of_tail` concludes
`Correct cendSealedMachine cendSpec cendAnswer`.

No `sorry`, no `admit`, no `native_decide`, no `bv_decide`, no new axioms.
-/

namespace ProofsLean.MNCore

open Issue
open PEMemory

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false

/-! ## 1. Byte-swap algebra -/

/-- Extracting from an extracted block adds the inner offset. -/
theorem extractLsb'_extractLsb'_shift {w : Nat} (x : BitVec w) (off inner start len : Nat)
    (h : start + len ≤ inner) :
    (x.extractLsb' off inner).extractLsb' start len = x.extractLsb' (off + start) len := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hinner : i < inner := by omega
  have hstart : start + i < inner := by omega
  simp only [BitVec.getLsbD_extractLsb', hi, hstart, decide_true, Bool.true_and]
  congr 1
  omega

theorem extractLsb'_extractLsb'_zero {w : Nat} (x : BitVec w) (inner start len : Nat)
    (h : start + len ≤ inner) :
    (x.extractLsb' 0 inner).extractLsb' start len = x.extractLsb' start len := by
  rw [extractLsb'_extractLsb'_shift x 0 inner start len h]
  simp

/-- Byte reversal of a 16-bit halfword. -/
def byteSwap16 (x : BitVec 16) : BitVec 16 :=
  x.extractLsb' 0 8 ++ x.extractLsb' 8 8

/-- Byte reversal of a 32-bit word: byte `p` of the result is byte `3 - p`. -/
def byteSwap32 (x : BitVec 32) : BitVec 32 :=
  byteSwap16 (x.extractLsb' 0 16) ++ byteSwap16 (x.extractLsb' 16 16)

/-- Rotating a 32-bit word left by 16 exchanges its two 16-bit halves. -/
theorem rotateLeft16_low (x : BitVec 32) :
    (x.rotateLeft 16).extractLsb' 0 16 = x.extractLsb' 16 16 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hi32 : i < 32 := by omega
  simp only [BitVec.getLsbD_extractLsb', Nat.zero_add, hi, hi32, decide_true, Bool.true_and]
  rw [BitVec.getLsbD_rotateLeft]
  have hmod : 16 % 32 = 16 := by decide
  rw [hmod, if_pos (by omega : i < 16)]

theorem rotateLeft16_high (x : BitVec 32) :
    (x.rotateLeft 16).extractLsb' 16 16 = x.extractLsb' 0 16 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hi32 : 16 + i < 32 := by omega
  simp only [BitVec.getLsbD_extractLsb', Nat.zero_add, hi, hi32, decide_true, Bool.true_and]
  rw [BitVec.getLsbD_rotateLeft]
  have hmod : 16 % 32 = 16 := by decide
  rw [hmod, if_neg (by omega : ¬ 16 + i < 16)]
  have h32 : 16 + i < 32 := by omega
  simp only [h32, decide_true, Bool.true_and]
  congr 1
  omega

/-- Rotating a 16-bit halfword left by 24 (right by 8) byteswaps it. -/
theorem rotateLeft24_eq_byteSwap16 (x : BitVec 16) : x.rotateLeft 24 = byteSwap16 x := by
  unfold byteSwap16
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hi16 : i < 16 := by omega
  rw [BitVec.getLsbD_rotateLeft]
  have hmod : 24 % 16 = 8 := by decide
  rw [hmod]
  by_cases h : i < 8
  · rw [if_pos h, BitVec.getLsbD_append, if_pos h]
    simp only [BitVec.getLsbD_extractLsb', h, decide_true, Bool.true_and]
  · rw [if_neg h, BitVec.getLsbD_append, if_neg h]
    simp only [hi16, decide_true, Bool.true_and]
    simp only [BitVec.getLsbD_extractLsb', h, decide_false, Bool.false_and]
    have h8 : i - 8 < 8 := by omega
    simp only [h8, decide_true, Bool.true_and, Nat.zero_add]

/-- The byte-swap of a 32-bit word, byte by byte. -/
theorem byteSwap32_byte (x : BitVec 32) (p : Nat) (hp : p < 4) :
    (byteSwap32 x).extractLsb' (8 * p) 8 = x.extractLsb' (8 * (3 - p)) 8 := by
  unfold byteSwap32 byteSwap16
  have hp_cases : p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 3 := by omega
  rcases hp_cases with rfl | rfl | rfl | rfl
  · rw [show (8 * 0 : Nat) = 0 from by decide,
      show (3 - 0 : Nat) = 3 from by decide]
    simp only [Nat.reduceMul]
    rw [BitVec.extractLsb'_append_eq_of_add_le (by decide),
      BitVec.extractLsb'_append_eq_of_add_le (by decide),
      extractLsb'_extractLsb'_shift x 16 16 8 8 (by decide)]
    simp
  · rw [show (8 * 1 : Nat) = 8 from by decide,
      show (3 - 1 : Nat) = 2 from by decide]
    simp only [Nat.reduceMul]
    rw [BitVec.extractLsb'_append_eq_of_add_le (by decide),
      BitVec.extractLsb'_append_eq_of_le (by decide)]
    simp only [Nat.sub_self]
    rw [extractLsb'_extractLsb'_shift (x.extractLsb' 16 16) 0 8 0 8 (by decide),
      extractLsb'_extractLsb'_shift x 16 16 0 8 (by decide)]
  · rw [show (8 * 2 : Nat) = 16 from by decide,
      show (3 - 2 : Nat) = 1 from by decide]
    simp only [Nat.reduceMul]
    rw [BitVec.extractLsb'_append_eq_of_le (by decide),
      BitVec.extractLsb'_append_eq_of_add_le (by decide),
      extractLsb'_extractLsb'_shift x 0 16 8 8 (by decide)]
    simp
  · rw [show (8 * 3 : Nat) = 24 from by decide,
      show (3 - 3 : Nat) = 0 from by decide]
    simp only [Nat.reduceMul]
    rw [BitVec.extractLsb'_append_eq_of_le (by decide),
      BitVec.extractLsb'_append_eq_of_le (by decide)]
    simp only [Nat.sub_self]
    rw [extractLsb'_extractLsb'_shift (x.extractLsb' 0 16) 0 8 0 8 (by decide),
      extractLsb'_extractLsb'_shift x 0 16 0 8 (by decide)]

/-- **`byteSwap64` splits into the byte swaps of its two 32-bit halves.**  The
proof is byte-exact and uses only the axiom-free structural kernel
`ByteSwapKernel.byteSwap64Kernel`, never `answerDatapath_is_byteSwap`. -/
theorem byteSwap64_eq_byteSwap32_halves (x : BitVec 64) :
    byteSwap64 x = byteSwap32 (x.extractLsb' 0 32) ++ byteSwap32 (x.extractLsb' 32 32) := by
  rw [byteSwap64_eq_kernel]
  apply eq_of_byte_extractLsb
  intro p hp
  rw [byteSwap64Kernel_extractLsb x p hp]
  have hp8 : p < 8 := by omega
  by_cases hlow : p < 4
  · rw [BitVec.extractLsb'_append_eq_of_add_le (by omega)]
    rw [byteSwap32_byte (x.extractLsb' 32 32) p hlow]
    rw [extractLsb'_extractLsb'_shift x 32 32 (8 * (3 - p)) 8 (by omega)]
    congr 1
    omega
  · have hq : p - 4 < 4 := by omega
    rw [show 8 * p = 32 + 8 * (p - 4) from by omega,
      BitVec.extractLsb'_append_eq_of_le (by omega)]
    rw [show 32 + 8 * (p - 4) - 32 = 8 * (p - 4) from by omega]
    rw [byteSwap32_byte (x.extractLsb' 0 32) (p - 4) hq]
    rw [extractLsb'_extractLsb'_zero x 32 (8 * (3 - (p - 4))) 8 (by omega)]
    congr 1
    omega

/-! ## 2. The two answer buses and the two rows' datapath -/

/-- The ALU forwarding bus installed by line 1: four copies of the immediate
word `0x34F80010`. -/
def cendImmediateBus : IntegerALU.Bus :=
  ⟨(0x34F80010 : BitVec 32) ++ (0x34F80010 : BitVec 32),
   (0x34F80010 : BitVec 32) ++ (0x34F80010 : BitVec 32)⟩

/-- The MAU forwarding bus installed by line 2's `fvfma`: four copies of
`0x34F80018` (the single-precision FMA of `0x34F80010` with itself). -/
def cendMauShiftBus : IntegerALU.Bus :=
  ⟨(0x34F80018 : BitVec 32) ++ (0x34F80018 : BitVec 32),
   (0x34F80018 : BitVec 32) ++ (0x34F80018 : BitVec 32)⟩

theorem lane_zero_immediate : IntegerALU.lane .word cendImmediateBus 0 = 0x34F80010 := rfl
theorem lane_one_immediate : IntegerALU.lane .word cendImmediateBus 1 = 0x34F80010 := rfl
theorem lane_zero_mau : IntegerALU.lane .half cendMauShiftBus 0 = 0x0018 := rfl
theorem lane_one_mau : IntegerALU.lane .half cendMauShiftBus 1 = 0x34F8 := rfl
theorem lane_two_mau : IntegerALU.lane .half cendMauShiftBus 2 = 0x0018 := rfl
theorem lane_three_mau : IntegerALU.lane .half cendMauShiftBus 3 = 0x34F8 := rfl

/-- A 32-bit value placed in the high half of a 64-bit bus. -/
theorem setWidth_shiftLeft_32 (w : BitVec 32) :
    (w.setWidth 64 <<< 32) = (w ++ 0#32) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_append, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_zero]
  by_cases h : i < 32
  · simp [h]
  · have h1 : i - 32 < 64 := by omega
    simp [h, hi, h1]

/-- **The `fvfma` value, recorded exactly.**  The single-precision FMA of three
copies of the immediate word `0x34F80010` is `0x34F80018`; the MAU forwarding
bus line 2 installs is therefore four copies of `0x34F80018`
(`cendMauShiftBus`). -/
theorem cendMauShiftWord :
    SingleFMA.singleFma 0x34F80010 0x34F80010 0x34F80010 = 0x34F80018 := by
  decide

/-- The MAU bus, written as the two lanes of the FMA datapath. -/
theorem cendMauShiftBus_eq :
    cendMauShiftBus =
      (⟨SingleFMA.singleFma 0x34F80010 0x34F80010 0x34F80010 ++
          SingleFMA.singleFma 0x34F80010 0x34F80010 0x34F80010,
        SingleFMA.singleFma 0x34F80010 0x34F80010 0x34F80010 ++
          SingleFMA.singleFma 0x34F80010 0x34F80010 0x34F80010⟩ : IntegerALU.Bus) := by
  rw [cendMauShiftWord]
  rfl

/-- The bus a `.word`-precision rotate-left writes to the forwarding slot and
to GRF0: the word read from LM0, halfword-swapped, placed in the high half. -/
def cendIbslResultBus (w : BitVec 32) : IntegerALU.Bus :=
  ⟨(w.rotateLeft 16) ++ 0#32, 0#64⟩

/-- **Line 2, first row: the `ibsl` datapath.**  The word read from LM0 is
rotated left by the forwarded immediate (count `0x34F80010 % 64 = 16`), which
exchanges its 16-bit halves.  The ALU result bus is
`⟨(w.rotateLeft 16) ++ 0, 0⟩`. -/
theorem cendIbslBus (w : BitVec 32) :
    (IntegerALU.evaluateBus .word (.shift .rotateLeft)
      (⟨w ++ 0#32, 0#64⟩ : IntegerALU.Bus) cendImmediateBus false).value =
      cendIbslResultBus w := by
  simp [IntegerALU.evaluateBus, IntegerALU.lane, IntegerALU.Precision.lanes,
    IntegerALU.Precision.width, IntegerALU.evaluateLane, IntegerALU.shift,
    cendImmediateBus, cendIbslResultBus, List.range, List.range.loop]
  have h0 : BitVec.extractLsb' 0 32 (w ++ 0#32) = 0#32 := by
    rw [BitVec.extractLsb'_append_eq_of_add_le (by decide)]
    rfl
  have h1 : BitVec.extractLsb' 32 32 (w ++ 0#32) = w := by
    rw [BitVec.extractLsb'_append_eq_left]
  rw [h0, h1]
  have hz : (0#32).rotateLeft 16 = 0#32 := by decide
  rw [hz]
  have hw : BitVec.setWidth 64 (0#32) = 0#64 := by decide
  rw [hw]
  calc (0#64 ||| BitVec.setWidth 64 (w.rotateLeft 16) <<< 32)
      = BitVec.setWidth 64 (w.rotateLeft 16) <<< 32 := BitVec.zero_or
    _ = w.rotateLeft 16 ++ 0#32 := setWidth_shiftLeft_32 _

theorem extractLsb'_or_shift16 (a b : BitVec 16) :
    ((a.setWidth 64 <<< 32) ||| (b.setWidth 64 <<< 48)).extractLsb' 32 32 = b ++ a := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hi32 : i < 32 := by omega
  rw [BitVec.getLsbD_extractLsb']
  simp only [hi, hi32, decide_true, Bool.true_and]
  rw [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_setWidth, BitVec.getLsbD_append]
  have h64 : 32 + i < 64 := by omega
  have hn32 : ¬ 32 + i < 32 := by omega
  have hsub64 : 32 + i - 32 < 64 := by omega
  by_cases h : i < 16
  · rw [if_pos h]
    have h48 : 32 + i < 48 := by omega
    have hi64 : i < 64 := by omega
    rw [show 32 + i - 32 = i from by omega]
    simp only [h64, hn32, h48, hi64, decide_true, decide_false, Bool.not_true,
      Bool.not_false, Bool.true_and, Bool.false_and, Bool.false_or, Bool.or_false]
  · rw [if_neg h]
    have hn48 : ¬ 32 + i < 48 := by omega
    have h48sub : 32 + i - 48 < 64 := by omega
    have hi64 : i < 64 := by omega
    have hsub64' : i - 16 < 64 := by omega
    have ha : a.getLsbD i = false := BitVec.getLsbD_of_ge a i (by omega)
    rw [show 32 + i - 32 = i from by omega, show 32 + i - 48 = i - 16 from by omega, ha]
    simp only [h64, hn32, hn48, h48sub, hi64, hsub64', decide_true, decide_false,
      Bool.not_true, Bool.not_false, Bool.true_and, Bool.false_and, Bool.false_or,
      Bool.or_false]

theorem extractLsb'_or_shift16_zero (a b : BitVec 16) :
    ((((0#64 : BitVec 64) ||| (0#64 : BitVec 64)) ||| a.setWidth 64 <<< 32) |||
      b.setWidth 64 <<< 48).extractLsb' 32 32 = b ++ a := by
  rw [show ((0#64 : BitVec 64) ||| (0#64 : BitVec 64)) = 0#64 from by decide]
  rw [show ((0#64 : BitVec 64) ||| a.setWidth 64 <<< 32) = a.setWidth 64 <<< 32 from
      BitVec.zero_or]
  exact extractLsb'_or_shift16 a b

/-- **Line 2's written word.**  The word that `unpackALUBus … 0` stores to GRF0
word `8+c` at cycle `c` is the halfword swap of the LM0 word. -/
theorem cendIbslWrittenWord (w : BitVec 32) :
    (PEMemory.unpackALUBus (cendIbslResultBus w)) 0 = w.rotateLeft 16 := by
  simp only [cendIbslResultBus, PEMemory.unpackALUBus, Fin.val_zero, if_true]
  exact BitVec.extractLsb'_append_eq_left

/-- The four 16-bit halfword lanes of the `ibsl` result bus' high word: two
zero lanes and the two (exchanged) halves of the word. -/
theorem cendIbslBus_lane_zero (w : BitVec 32) :
    (cendIbslResultBus w).high.extractLsb' 0 16 = 0#16 := by
  show (w.rotateLeft 16 ++ 0#32).extractLsb' 0 16 = 0#16
  rw [BitVec.extractLsb'_append_eq_of_add_le (by decide)]
  rfl

theorem cendIbslBus_lane_one (w : BitVec 32) :
    (cendIbslResultBus w).high.extractLsb' 16 16 = 0#16 := by
  show (w.rotateLeft 16 ++ 0#32).extractLsb' 16 16 = 0#16
  rw [BitVec.extractLsb'_append_eq_of_add_le (by decide)]
  rfl

theorem cendIbslBus_lane_two (w : BitVec 32) :
    (cendIbslResultBus w).high.extractLsb' 32 16 = w.extractLsb' 16 16 := by
  show (w.rotateLeft 16 ++ 0#32).extractLsb' 32 16 = w.extractLsb' 16 16
  rw [BitVec.extractLsb'_append_eq_of_le (by decide)]
  simp only [Nat.sub_self]
  exact rotateLeft16_low w

theorem cendIbslBus_lane_three (w : BitVec 32) :
    (cendIbslResultBus w).high.extractLsb' 48 16 = w.extractLsb' 0 16 := by
  show (w.rotateLeft 16 ++ 0#32).extractLsb' 48 16 = w.extractLsb' 0 16
  rw [BitVec.extractLsb'_append_eq_of_le (by decide)]
  simp only [show (48 - 32 : Nat) = 16 from by decide]
  exact rotateLeft16_high w

/-- **Line 3's written word: the `sbsl` datapath.**  With the forwarded ALU bus
(the halfword-swapped word, `0x34F80010`'s rotate count `16` having been applied
by line 2) as data and the MAU bus `0x34F80018 ++ 0x34F80018` as the shift
source (every halfword count is `24`, a rotate-left-8 inside each halfword),
the word stored to LM1 is `byteSwap32 w`. -/
theorem cendSbslData (w : BitVec 32) :
    (PEMemory.unpackALUBus
      (IntegerALU.evaluateBus .half (.shift .rotateLeft) (cendIbslResultBus w)
        cendMauShiftBus false).value) 0 = byteSwap32 w := by
  simp [IntegerALU.evaluateBus, IntegerALU.lane, IntegerALU.Precision.lanes,
    IntegerALU.Precision.width, IntegerALU.evaluateLane, IntegerALU.shift,
    PEMemory.unpackALUBus, cendMauShiftBus, List.range, List.range.loop]
  rw [cendIbslBus_lane_zero w, cendIbslBus_lane_one w, cendIbslBus_lane_two w,
    cendIbslBus_lane_three w]
  rw [show (0#16).rotateLeft 24 = 0#16 from by decide,
    rotateLeft24_eq_byteSwap16 (w.extractLsb' 16 16),
    rotateLeft24_eq_byteSwap16 (w.extractLsb' 0 16)]
  have h1 : BitVec.setWidth 64 (0#16) <<< 16 = 0#64 := by decide
  have h0 : BitVec.setWidth 64 (0#16) = 0#64 := by decide
  rw [h1, h0]
  exact extractLsb'_or_shift16_zero (byteSwap16 (w.extractLsb' 16 16))
    (byteSwap16 (w.extractLsb' 0 16))

/-! ## 3. The LM1 destination selector and the readback -/

/-- The LM1 word line 3's `[1,0,3,2]` destination selector writes at issue cycle
`c` (with BAR1 = 0). -/
def cendSbslDestination (c : Fin 4) : Fin 4096 :=
  if c.val = 0 then 1 else if c.val = 1 then 0 else if c.val = 2 then 3 else 2

theorem cendSbslDestination_zero : cendSbslDestination 0 = 1 := by decide
theorem cendSbslDestination_one : cendSbslDestination 1 = 0 := by decide
theorem cendSbslDestination_two : cendSbslDestination 2 = 3 := by decide
theorem cendSbslDestination_three : cendSbslDestination 3 = 2 := by decide

/-- The single enabled word of a one-word ALU store. -/
def cendSingleWord (x : BitVec 32) : PEMemory.WordBus := fun index =>
  if index.val = 0 then x else 0

/-- The LM1 memory after line 3's four word writes: cycle `c` stores
`data c` at LM1 word `[1,0,3,2][c]`. -/
def cendSbslLm1 (memory : PEMemory.Memory .lm1) (data : Fin 4 → BitVec 32) :
    PEMemory.Memory .lm1 :=
  PEMemory.writeWords .lm1 .word
    (PEMemory.writeWords .lm1 .word
      (PEMemory.writeWords .lm1 .word
        (PEMemory.writeWords .lm1 .word memory (cendSbslDestination 0)
          (cendSingleWord (data 0))) (cendSbslDestination 1) (cendSingleWord (data 1)))
      (cendSbslDestination 2) (cendSingleWord (data 2)))
    (cendSbslDestination 3) (cendSingleWord (data 3))

/-- The `$aluf` read of a slot function whose `.alu` slot at the cycle is
`known bus` returns that bus (the read line 3 performs). -/
theorem cendTailAlufRead (files : IntegerRegisterFiles)
    (slots : ProofsLean.MNCore.Forwarding.Slots) (cycle : Fin 4) (bus : IntegerALU.Bus)
    (known : slots .alu cycle = .known bus) :
    ParsedIntegerInput.readWithForwarding files slots cycle (.forward .aluf false) =
      .ok bus :=
  readWithForwarding_aluf_known files slots cycle bus known

/-- The `$mauf` read of a slot function whose `.mau` slot at the cycle is
`known bus` returns that bus (the shift source of line 3's `sbsl`). -/
theorem cendTailMaufRead (files : IntegerRegisterFiles)
    (slots : ProofsLean.MNCore.Forwarding.Slots) (cycle : Fin 4) (bus : IntegerALU.Bus)
    (known : slots .mau cycle = .known bus) :
    ParsedIntegerInput.readWithForwarding files slots cycle (.forward .mauf false) =
      .ok bus :=
  parsedIntegerInput_forward_known files slots cycle .mauf false bus known

/-- **The LM1 readback.**  Reading LM1 words `0/1` after the `[1,0,3,2]` stores
returns the words of cycles `1` and `0`, in that order. -/
theorem cendSbslLm1_readPair (memory : PEMemory.Memory .lm1)
    (data : Fin 4 → BitVec 32) :
    FloatPEMemory.readPair .lm1 (cendSbslLm1 memory data) ⟨0, by decide⟩ =
      data 1 ++ data 0 := by
  unfold cendSbslLm1 cendSbslDestination cendSingleWord FloatPEMemory.readPair
  simp [PEMemory.readWords, PEMemory.writeWords, PEMemory.advance, PEMemory.distance,
    PEMemory.count, PEMemory.Width.words, PEMemory.Bank.capacity,
    show (0 : Fin 4).val = 0 from rfl]

/-! ## 4. Line 1's value facts and the exact per-line residual -/

/-- The `c`-th LM0 word read by a `word` access with BAR0: the address is
`(BAR0 + c) mod 4096`. -/
def cendLm0Word (memory : PEMemory.Memory .lm0) (bar : BitVec 12) (c : Fin 4) :
    BitVec 32 :=
  memory ⟨(bar.toNat + c.val) % 4096, Nat.mod_lt _ (by decide)⟩

/-- **Line 1's value facts.**  They are what line 1's executor computation must
deliver to the tail: the input word's two halves in LM0 words `0/1`, and the
initial BAR registers (line 1's `imm` row writes neither BAR). -/
structure CendLine1Facts (input : BitVec 64) (s1 : State) : Prop where
  lm0_zero : cendLm0Word (s1.peRegisters cendPE).lm0 (s1.peContext cendPE).bar0 0 =
    input.extractLsb' 32 32
  lm0_one : cendLm0Word (s1.peRegisters cendPE).lm0 (s1.peContext cendPE).bar0 1 =
    input.extractLsb' 0 32
  bar0 : (s1.peContext cendPE).bar0 = 0
  bar1 : (s1.peContext cendPE).bar1 = 0

/-- **Part (a)'s explicit commit implies the line-1 value facts.**  Once the
line-1 executor computation pins PE 0's register file to the explicit
`cendImmWrites` commit (the statement `cendImm_pecore` and the 4096-PE walk
deliver) and line 1 writes no BAR, the value facts the tail consumes follow.
This is the interface between `CendAnswerExec.cendLine1_aluf`'s line and the
value chain below. -/
theorem cendLine1Facts_of_commit (input : BitVec 64) (s1 : State)
    (files : s1.peRegisters cendPE =
      commitParsedMaskedWrites (cendInitialPERegisters input) cendImmWrites)
    (bar0 : (s1.peContext cendPE).bar0 = 0)
    (bar1 : (s1.peContext cendPE).bar1 = 0) : CendLine1Facts input s1 := by
  have lm0 : (s1.peRegisters cendPE).lm0 = (cendInitialPERegisters input).lm0 := by
    rw [files]
    simp [commitParsedMaskedWrites, cendImmWrites, cendImmWrite, immediateALUWrite,
      writeDirectAccessMasked, writeRegisterBankMasked, cendInitialPERegisters]
  refine ⟨?_, ?_, bar0, bar1⟩
  · rw [cendLm0Word, lm0, bar0]
    simp [cendInitialPERegisters]
  · rw [cendLm0Word, lm0, bar0]
    simp [cendInitialPERegisters]

/-- **The exact residual executor computation of lines 2 and 3.**

* `line2` / `line3`: the two `executeNormalizedLine` steps succeed.
* `aluSlots` / `mauSlots`: the forwarding slots the steps install — the
  `ibsl` result bus (the halfword swap of each LM0 word, `cendIbslResultBus`)
  and the `fvfma` MAU bus `0x34F80018 ++ 0x34F80018` (`cendMauShiftBus`).
* `afterTwoBar0`/`afterTwoBar1`/`afterTwoLm0`: line 2 does not touch the BAR
  registers or LM0 (it writes GRF0/GRF1 and the forwarding slots only).
* `afterThreeLm1`: line 3 commits the four `[1,0,3,2]` word stores whose data are
  `byteSwap32` of the LM0 words read at the same cycles.

Everything below consumes these facts; proving them is the 4096-PE walk and the
per-cycle preparation of `WholeMachineStep`. -/
structure CendTailComputation (input : BitVec 64) (s1 : State) where
  line1 : CendLine1Facts input s1
  afterTwo : State
  line2 : executeNormalizedLine (.pe [cendIbslExpr.normalize, cendFmaExpr.normalize]) s1 =
    .ok afterTwo
  aluSlots : ∀ c : Fin 4,
    stateForwardingSlots afterTwo cendPE .alu c =
      .known (cendIbslResultBus
        (cendLm0Word (s1.peRegisters cendPE).lm0 (s1.peContext cendPE).bar0 c))
  mauSlots : ∀ c : Fin 4,
    stateForwardingSlots afterTwo cendPE .mau c = .known cendMauShiftBus
  afterTwoBar0 : (afterTwo.peContext cendPE).bar0 = (s1.peContext cendPE).bar0
  afterTwoBar1 : (afterTwo.peContext cendPE).bar1 = (s1.peContext cendPE).bar1
  afterTwoLm0 : (afterTwo.peRegisters cendPE).lm0 = (s1.peRegisters cendPE).lm0
  afterThree : State
  line3 : executeNormalizedLine (.pe [cendSbslExpr.normalize]) afterTwo = .ok afterThree
  afterThreeLm1 : (afterThree.peRegisters cendPE).lm1 =
    cendSbslLm1 (afterTwo.peRegisters cendPE).lm1
      (fun c => byteSwap32
        (cendLm0Word (afterTwo.peRegisters cendPE).lm0 (afterTwo.peContext cendPE).bar0 c))

/-- **The value chain closes the tail from the per-line computation.** -/
theorem cendTail_of_computation
    (computation : ∀ (input : BitVec 64) (s1 : State),
      executeNormalizedLine (.pe [cendImmExpr.normalize]) (cendInitialState input) = .ok s1 →
      CendTailComputation input s1) :
    ∀ (input : BitVec 64) (s1 : State),
      executeNormalizedLine (.pe [cendImmExpr.normalize]) (cendInitialState input) = .ok s1 →
      ∃ result : State,
        ProofsLean.execute cendSealedMachine
            [.pe [cendIbslExpr.normalize, cendFmaExpr.normalize],
             .pe [cendSbslExpr.normalize]] s1 = some result ∧
        cendOutputPair result = byteSwap64 input := by
  intro input s1 line1
  obtain ⟨facts, afterTwo, line2, aluSlots, mauSlots, afterTwoBar0, afterTwoBar1,
    afterTwoLm0, afterThree, line3, afterThreeLm1⟩ := computation input s1 line1
  refine ⟨afterThree, ?_, ?_⟩
  · have stepTwo : cendSealedMachine.step
        (.pe [cendIbslExpr.normalize, cendFmaExpr.normalize]) s1 = some afterTwo := by
      simp only [cendSealedMachine, InstructionLine.toNormalizedLine, line2]
    have stepThree : cendSealedMachine.step (.pe [cendSbslExpr.normalize]) afterTwo =
        some afterThree := by
      simp only [cendSealedMachine, InstructionLine.toNormalizedLine, line3]
    show (cendSealedMachine.step
        (.pe [cendIbslExpr.normalize, cendFmaExpr.normalize]) s1).bind
      (fun next => ProofsLean.execute cendSealedMachine
        [.pe [cendSbslExpr.normalize]] next) = some afterThree
    rw [stepTwo]
    show (cendSealedMachine.step (.pe [cendSbslExpr.normalize]) afterTwo).bind
      (fun next => some next) = some afterThree
    rw [stepThree]
    rfl
  · unfold cendOutputPair
    rw [afterThreeLm1, cendSbslLm1_readPair]
    have hlm0 : cendLm0Word (afterTwo.peRegisters cendPE).lm0
        (afterTwo.peContext cendPE).bar0 0 = input.extractLsb' 32 32 := by
      rw [afterTwoLm0, afterTwoBar0]
      exact facts.lm0_zero
    have hlm1 : cendLm0Word (afterTwo.peRegisters cendPE).lm0
        (afterTwo.peContext cendPE).bar0 1 = input.extractLsb' 0 32 := by
      rw [afterTwoLm0, afterTwoBar0]
      exact facts.lm0_one
    rw [hlm1, hlm0]
    exact (byteSwap64_eq_byteSwap32_halves input).symm

/-- **The residual in `Prop` form.**  Line 1's success implies the existence of
the per-line computation data; this is the shape to assume if a `Prop`-valued
residual is preferred to the data-carrying `CendTailComputation`. -/
theorem cendTail_of_residual
    (residual : ∀ (input : BitVec 64) (s1 : State),
      executeNormalizedLine (.pe [cendImmExpr.normalize]) (cendInitialState input) = .ok s1 →
      Nonempty (CendTailComputation input s1)) :
    ∀ (input : BitVec 64) (s1 : State),
      executeNormalizedLine (.pe [cendImmExpr.normalize]) (cendInitialState input) = .ok s1 →
      ∃ result : State,
        ProofsLean.execute cendSealedMachine
            [.pe [cendIbslExpr.normalize, cendFmaExpr.normalize],
             .pe [cendSbslExpr.normalize]] s1 = some result ∧
        cendOutputPair result = byteSwap64 input :=
  cendTail_of_computation fun input s1 line1 => (residual input s1 line1).some

/-- **`CendAnswerExecResidual` from part (a) and the tail computation.** -/
theorem cendAnswerExecResidual_of_line1_and_tail
    (line1 : ∀ input : BitVec 64, ∃ next : State,
      executeNormalizedLine (.pe [cendImmExpr.normalize]) (cendInitialState input) = .ok next)
    (tail : ∀ (input : BitVec 64) (s1 : State),
      executeNormalizedLine (.pe [cendImmExpr.normalize]) (cendInitialState input) = .ok s1 →
      ∃ result : State,
        ProofsLean.execute cendSealedMachine
            [.pe [cendIbslExpr.normalize, cendFmaExpr.normalize],
             .pe [cendSbslExpr.normalize]] s1 = some result ∧
        cendOutputPair result = byteSwap64 input) :
    CendAnswerExecResidual where
  line1 := line1
  tail := tail

/-- **`Correct` from part (a) and the per-line computation residual.** -/
theorem cendAnswerCorrect_of_tail
    (line1 : ∀ input : BitVec 64, ∃ next : State,
      executeNormalizedLine (.pe [cendImmExpr.normalize]) (cendInitialState input) = .ok next)
    (computation : ∀ (input : BitVec 64) (s1 : State),
      executeNormalizedLine (.pe [cendImmExpr.normalize]) (cendInitialState input) = .ok s1 →
      CendTailComputation input s1) :
    ProofsLean.Correct cendSealedMachine cendSpec cendAnswer :=
  cendAnswerCorrect_of_residual
    (cendAnswerExecResidual_of_line1_and_tail line1 (cendTail_of_computation computation))

/-! ## 5. Trust report -/

#print axioms byteSwap64_eq_byteSwap32_halves
#print axioms cendIbslBus
#print axioms cendMauShiftWord
#print axioms cendIbslWrittenWord
#print axioms cendSbslData
#print axioms cendTailAlufRead
#print axioms cendTailMaufRead
#print axioms cendSbslLm1_readPair
#print axioms cendLine1Facts_of_commit
#print axioms cendTail_of_residual
#print axioms cendTail_of_computation
#print axioms cendAnswerCorrect_of_tail

end ProofsLean.MNCore
