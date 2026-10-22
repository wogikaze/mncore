import ProofsLean.ByteSwap

/-!
# A structural, axiom-free kernel for `byteSwap64`

`ProofsLean/ByteSwap.lean` defines `byteSwap64` as an OR of eight masked shifts and
proves involutivity with `bv_decide`.  For a 64-bit goal that tactic falls back to
native evaluation and leaves the axiom
`ByteSwap.byteSwap64_involutive._native.bv_decide.ax_1_5` in the trust closure of
everything that uses the theorem.

This file rebuilds the same fact with no bit blasting, no unfinished proof, and no
new axiom.  The work is split into three parts.

* `byteSwap64Kernel` is the byte permutation written out structurally: extract the
  eight bytes of `x` and reassemble them in reverse order with `++`.
* `byteSwap64_getLsbD` reads bit `8*p + j` of the *existing* `byteSwap64` (the
  definition in `ByteSwap.lean`) and shows it is bit `8*(7-p) + j` of the input.
  The eight masks are evaluated by `Nat.testBit_mul_two_pow` and
  `Nat.testBit_two_pow_sub_one`; no bit blasting is involved.
* `eq_of_byte_extractLsb` observes that the eight byte blocks determine a 64-bit
  vector, so checking the eight blocks proves both that the two definitions agree
  and that byte reversal is an involution.

The public results are `byteSwap64_eq_kernel`, `byteSwap64Kernel_involutive`,
`byteSwap64Kernel_injective`, `byteSwap64Kernel_bijective`,
`byteSwap64_involutive_kernel`, `byteSwap64_injective_kernel`, and
`byteSwap64_bijective_kernel`.  The last three are drop-in replacements for the
facts about the definition in `ByteSwap.lean`.

Routing notes:

* `ProgramWitness.byteSwap64_injective` becomes native-axiom-free when its body is
  replaced by `byteSwap64_injective_kernel`; consequently
  `cendPE_not_correct_of_candidatePair` becomes native-axiom-free as well.
* `ConvertEndian.answerDatapath_involutive` can replace its final
  `byteSwap64_involutive` call by `byteSwap64_involutive_kernel`, but it still
  uses `ConvertEndian.answerDatapath_is_byteSwap`, which has its own native
  `bv_decide` axiom.  Fully clearing that theorem needs a separate structural
  proof of `answerDatapath_is_byteSwap`.
-/

namespace ProofsLean.MNCore

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false

/-! ## Byte masks as bit selectors

The masks in `byteSwap64` are `0xFF` shifted by a multiple of eight.  The next
lemma evaluates the `i`-th bit of such a mask. -/

theorem byteSwap64_mask_getLsbD (p i : Nat) :
    (BitVec.ofNat 64 (255 * 2 ^ (8 * p))).getLsbD i =
      (decide (i < 64) && decide (8 * p ≤ i) && decide (i < 8 * p + 8)) := by
  rw [BitVec.getLsbD_ofNat]
  by_cases hi : i < 64
  · simp only [hi, decide_true, Bool.true_and]
    rw [Nat.testBit_mul_two_pow]
    rw [show (255 : Nat) = 2 ^ 8 - 1 by decide, Nat.testBit_two_pow_sub_one]
    by_cases hp : 8 * p ≤ i
    · simp only [hp, decide_true, Bool.true_and]
      rw [decide_eq_decide]
      omega
    · simp only [hp, decide_false, Bool.false_and]
  · simp only [hi, decide_false, Bool.false_and]

@[simp] theorem byteSwap64_mask0_getLsbD (i : Nat) :
    (0xFF#64).getLsbD i = (decide (i < 64) && decide (i < 8)) := by
  simpa using byteSwap64_mask_getLsbD 0 i

@[simp] theorem byteSwap64_mask1_getLsbD (i : Nat) :
    (0xFF00#64).getLsbD i = (decide (i < 64) && decide (8 ≤ i) && decide (i < 16)) := by
  simpa using byteSwap64_mask_getLsbD 1 i

@[simp] theorem byteSwap64_mask2_getLsbD (i : Nat) :
    (0xFF0000#64).getLsbD i = (decide (i < 64) && decide (16 ≤ i) && decide (i < 24)) := by
  simpa using byteSwap64_mask_getLsbD 2 i

@[simp] theorem byteSwap64_mask3_getLsbD (i : Nat) :
    (0xFF000000#64).getLsbD i = (decide (i < 64) && decide (24 ≤ i) && decide (i < 32)) := by
  simpa using byteSwap64_mask_getLsbD 3 i

@[simp] theorem byteSwap64_mask4_getLsbD (i : Nat) :
    (0xFF00000000#64).getLsbD i = (decide (i < 64) && decide (32 ≤ i) && decide (i < 40)) := by
  simpa using byteSwap64_mask_getLsbD 4 i

@[simp] theorem byteSwap64_mask5_getLsbD (i : Nat) :
    (0xFF0000000000#64).getLsbD i = (decide (i < 64) && decide (40 ≤ i) && decide (i < 48)) := by
  simpa using byteSwap64_mask_getLsbD 5 i

@[simp] theorem byteSwap64_mask6_getLsbD (i : Nat) :
    (0xFF000000000000#64).getLsbD i = (decide (i < 64) && decide (48 ≤ i) && decide (i < 56)) := by
  simpa using byteSwap64_mask_getLsbD 6 i

@[simp] theorem byteSwap64_mask7_getLsbD (i : Nat) :
    (0xFF00000000000000#64).getLsbD i = (decide (i < 64) && decide (56 ≤ i) && decide (i < 64)) := by
  simpa using byteSwap64_mask_getLsbD 7 i

@[simp] theorem byteSwap64_mask0_getElem (i : Nat) (h : i < 64) :
    (0xFF#64)[i] = decide (i < 8) := by
  rw [← BitVec.getLsbD_eq_getElem h, byteSwap64_mask0_getLsbD]
  simp [h]

@[simp] theorem byteSwap64_mask1_getElem (i : Nat) (h : i < 64) :
    (0xFF00#64)[i] = (decide (i < 64) && decide (8 ≤ i) && decide (i < 16)) := by
  rw [← BitVec.getLsbD_eq_getElem h, byteSwap64_mask1_getLsbD]

@[simp] theorem byteSwap64_mask2_getElem (i : Nat) (h : i < 64) :
    (0xFF0000#64)[i] = (decide (i < 64) && decide (16 ≤ i) && decide (i < 24)) := by
  rw [← BitVec.getLsbD_eq_getElem h, byteSwap64_mask2_getLsbD]

@[simp] theorem byteSwap64_mask3_getElem (i : Nat) (h : i < 64) :
    (0xFF000000#64)[i] = (decide (i < 64) && decide (24 ≤ i) && decide (i < 32)) := by
  rw [← BitVec.getLsbD_eq_getElem h, byteSwap64_mask3_getLsbD]

@[simp] theorem byteSwap64_mask4_getElem (i : Nat) (h : i < 64) :
    (0xFF00000000#64)[i] = (decide (i < 64) && decide (32 ≤ i) && decide (i < 40)) := by
  rw [← BitVec.getLsbD_eq_getElem h, byteSwap64_mask4_getLsbD]

@[simp] theorem byteSwap64_mask5_getElem (i : Nat) (h : i < 64) :
    (0xFF0000000000#64)[i] = (decide (i < 64) && decide (40 ≤ i) && decide (i < 48)) := by
  rw [← BitVec.getLsbD_eq_getElem h, byteSwap64_mask5_getLsbD]

@[simp] theorem byteSwap64_mask6_getElem (i : Nat) (h : i < 64) :
    (0xFF000000000000#64)[i] = (decide (i < 64) && decide (48 ≤ i) && decide (i < 56)) := by
  rw [← BitVec.getLsbD_eq_getElem h, byteSwap64_mask6_getLsbD]

@[simp] theorem byteSwap64_mask7_getElem (i : Nat) (h : i < 64) :
    (0xFF00000000000000#64)[i] = (decide (i < 64) && decide (56 ≤ i) && decide (i < 64)) := by
  rw [← BitVec.getLsbD_eq_getElem h, byteSwap64_mask7_getLsbD]

/-! ## Reading a bit of `byteSwap64`

For an output byte `p` and a bit `j` inside that byte, exactly one of the eight
masked shifts of `byteSwap64` is active, and it reads bit `8*(7-p)+j` of the
input.  The lemmas below record this for each of the eight bytes.  Their proofs
only evaluate the masks and use linear arithmetic on byte indices. -/

theorem byteSwap64_getLsbD_0 (x : BitVec 64) (j : Nat) (hj : j < 8) :
    (byteSwap64 x).getLsbD (8 * 0 + j) = x.getLsbD (8 * (7 - 0) + j) := by
  simp only [byteSwap64, BitVec.getLsbD_or, BitVec.getLsbD_and,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft,
    byteSwap64_mask0_getLsbD, byteSwap64_mask1_getLsbD, byteSwap64_mask2_getLsbD,
    byteSwap64_mask3_getLsbD, byteSwap64_mask4_getLsbD, byteSwap64_mask5_getLsbD,
    byteSwap64_mask6_getLsbD, byteSwap64_mask7_getLsbD]
  have h64 : 8 * 0 + j < 64 := by omega
  have hj64 : j < 64 := by omega
  have hle0 : 8 * 0 ≤ j := by omega
  have hlt0 : j < 8 * 0 + 8 := by omega
  have hnle1 : ¬ (8 * 1 ≤ j) := by omega
  have hnle2 : ¬ (8 * 2 ≤ j) := by omega
  have hnle3 : ¬ (8 * 3 ≤ j) := by omega
  have hnle4 : ¬ (8 * 4 ≤ j) := by omega
  have hnle5 : ¬ (8 * 5 ≤ j) := by omega
  have hnle6 : ¬ (8 * 6 ≤ j) := by omega
  have hnle7 : ¬ (8 * 7 ≤ j) := by omega
  have hbit : 8 * (7 - 2 * 0) + (j) = 8 * (7 - 0) + j := by omega
  simp [hj, h64, hj64, hle0, hlt0, hnle1, hnle2, hnle3, hnle4, hnle5, hnle6, hnle7, hbit]

theorem byteSwap64_getLsbD_1 (x : BitVec 64) (j : Nat) (hj : j < 8) :
    (byteSwap64 x).getLsbD (8 * 1 + j) = x.getLsbD (8 * (7 - 1) + j) := by
  simp only [byteSwap64, BitVec.getLsbD_or, BitVec.getLsbD_and,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft,
    byteSwap64_mask0_getLsbD, byteSwap64_mask1_getLsbD, byteSwap64_mask2_getLsbD,
    byteSwap64_mask3_getLsbD, byteSwap64_mask4_getLsbD, byteSwap64_mask5_getLsbD,
    byteSwap64_mask6_getLsbD, byteSwap64_mask7_getLsbD]
  have h64 : 8 * 1 + j < 64 := by omega
  have hj64 : j < 64 := by omega
  have hle0 : 8 * 0 ≤ 8 * 1 + j := by omega
  have hnlt0 : ¬ (8 * 1 + j < 8 * 0 + 8) := by omega
  have hle1 : 8 * 1 ≤ 8 * 1 + j := by omega
  have hlt1 : 8 * 1 + j < 8 * 1 + 8 := by omega
  have hnle2 : ¬ (8 * 2 ≤ 8 * 1 + j) := by omega
  have hnle3 : ¬ (8 * 3 ≤ 8 * 1 + j) := by omega
  have hnle4 : ¬ (8 * 4 ≤ 8 * 1 + j) := by omega
  have hnle5 : ¬ (8 * 5 ≤ 8 * 1 + j) := by omega
  have hnle6 : ¬ (8 * 6 ≤ 8 * 1 + j) := by omega
  have hnle7 : ¬ (8 * 7 ≤ 8 * 1 + j) := by omega
  have hbit : 8 * (7 - 2 * 1) + (8 * 1 + j) = 8 * (7 - 1) + j := by omega
  simp [hj, h64, hj64, hle0, hnlt0, hle1, hlt1, hnle2, hnle3, hnle4, hnle5, hnle6, hnle7, hbit]

theorem byteSwap64_getLsbD_2 (x : BitVec 64) (j : Nat) (hj : j < 8) :
    (byteSwap64 x).getLsbD (8 * 2 + j) = x.getLsbD (8 * (7 - 2) + j) := by
  simp only [byteSwap64, BitVec.getLsbD_or, BitVec.getLsbD_and,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft,
    byteSwap64_mask0_getLsbD, byteSwap64_mask1_getLsbD, byteSwap64_mask2_getLsbD,
    byteSwap64_mask3_getLsbD, byteSwap64_mask4_getLsbD, byteSwap64_mask5_getLsbD,
    byteSwap64_mask6_getLsbD, byteSwap64_mask7_getLsbD]
  have h64 : 8 * 2 + j < 64 := by omega
  have hj64 : j < 64 := by omega
  have hle0 : 8 * 0 ≤ 8 * 2 + j := by omega
  have hnlt0 : ¬ (8 * 2 + j < 8 * 0 + 8) := by omega
  have hle1 : 8 * 1 ≤ 8 * 2 + j := by omega
  have hnlt1 : ¬ (8 * 2 + j < 8 * 1 + 8) := by omega
  have hle2 : 8 * 2 ≤ 8 * 2 + j := by omega
  have hlt2 : 8 * 2 + j < 8 * 2 + 8 := by omega
  have hnle3 : ¬ (8 * 3 ≤ 8 * 2 + j) := by omega
  have hnle4 : ¬ (8 * 4 ≤ 8 * 2 + j) := by omega
  have hnle5 : ¬ (8 * 5 ≤ 8 * 2 + j) := by omega
  have hnle6 : ¬ (8 * 6 ≤ 8 * 2 + j) := by omega
  have hnle7 : ¬ (8 * 7 ≤ 8 * 2 + j) := by omega
  have hbit : 8 * (7 - 2 * 2) + (8 * 2 + j) = 8 * (7 - 2) + j := by omega
  simp [hj, h64, hj64, hle0, hnlt0, hle1, hnlt1, hle2, hlt2, hnle3, hnle4, hnle5, hnle6, hnle7, hbit]

theorem byteSwap64_getLsbD_3 (x : BitVec 64) (j : Nat) (hj : j < 8) :
    (byteSwap64 x).getLsbD (8 * 3 + j) = x.getLsbD (8 * (7 - 3) + j) := by
  simp only [byteSwap64, BitVec.getLsbD_or, BitVec.getLsbD_and,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft,
    byteSwap64_mask0_getLsbD, byteSwap64_mask1_getLsbD, byteSwap64_mask2_getLsbD,
    byteSwap64_mask3_getLsbD, byteSwap64_mask4_getLsbD, byteSwap64_mask5_getLsbD,
    byteSwap64_mask6_getLsbD, byteSwap64_mask7_getLsbD]
  have h64 : 8 * 3 + j < 64 := by omega
  have hj64 : j < 64 := by omega
  have hle0 : 8 * 0 ≤ 8 * 3 + j := by omega
  have hnlt0 : ¬ (8 * 3 + j < 8 * 0 + 8) := by omega
  have hle1 : 8 * 1 ≤ 8 * 3 + j := by omega
  have hnlt1 : ¬ (8 * 3 + j < 8 * 1 + 8) := by omega
  have hle2 : 8 * 2 ≤ 8 * 3 + j := by omega
  have hnlt2 : ¬ (8 * 3 + j < 8 * 2 + 8) := by omega
  have hle3 : 8 * 3 ≤ 8 * 3 + j := by omega
  have hlt3 : 8 * 3 + j < 8 * 3 + 8 := by omega
  have hnle4 : ¬ (8 * 4 ≤ 8 * 3 + j) := by omega
  have hnle5 : ¬ (8 * 5 ≤ 8 * 3 + j) := by omega
  have hnle6 : ¬ (8 * 6 ≤ 8 * 3 + j) := by omega
  have hnle7 : ¬ (8 * 7 ≤ 8 * 3 + j) := by omega
  have hbit : 8 * (7 - 2 * 3) + (8 * 3 + j) = 8 * (7 - 3) + j := by omega
  simp [hj, h64, hj64, hle0, hnlt0, hle1, hnlt1, hle2, hnlt2, hle3, hlt3, hnle4, hnle5, hnle6, hnle7, hbit]

theorem byteSwap64_getLsbD_4 (x : BitVec 64) (j : Nat) (hj : j < 8) :
    (byteSwap64 x).getLsbD (8 * 4 + j) = x.getLsbD (8 * (7 - 4) + j) := by
  simp only [byteSwap64, BitVec.getLsbD_or, BitVec.getLsbD_and,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft,
    byteSwap64_mask0_getLsbD, byteSwap64_mask1_getLsbD, byteSwap64_mask2_getLsbD,
    byteSwap64_mask3_getLsbD, byteSwap64_mask4_getLsbD, byteSwap64_mask5_getLsbD,
    byteSwap64_mask6_getLsbD, byteSwap64_mask7_getLsbD]
  have h64 : 8 * 4 + j < 64 := by omega
  have hj64 : j < 64 := by omega
  have hle0 : 8 * 0 ≤ 8 * 4 + j := by omega
  have hnlt0 : ¬ (8 * 4 + j < 8 * 0 + 8) := by omega
  have hle1 : 8 * 1 ≤ 8 * 4 + j := by omega
  have hnlt1 : ¬ (8 * 4 + j < 8 * 1 + 8) := by omega
  have hle2 : 8 * 2 ≤ 8 * 4 + j := by omega
  have hnlt2 : ¬ (8 * 4 + j < 8 * 2 + 8) := by omega
  have hle3 : 8 * 3 ≤ 8 * 4 + j := by omega
  have hnlt3 : ¬ (8 * 4 + j < 8 * 3 + 8) := by omega
  have hle4 : 8 * 4 ≤ 8 * 4 + j := by omega
  have hlt4 : 8 * 4 + j < 8 * 4 + 8 := by omega
  have hnle5 : ¬ (8 * 5 ≤ 8 * 4 + j) := by omega
  have hnle6 : ¬ (8 * 6 ≤ 8 * 4 + j) := by omega
  have hnle7 : ¬ (8 * 7 ≤ 8 * 4 + j) := by omega
  have hguard : ¬ (8 * 4 + j < 8 * (2 * 4 - 7)) := by omega
  have hbit : 8 * 4 + j - 8 * (2 * 4 - 7) = 8 * (7 - 4) + j := by omega
  simp [hj, h64, hj64, hle0, hnlt0, hle1, hnlt1, hle2, hnlt2, hle3, hnlt3, hle4, hlt4, hnle5, hnle6, hnle7, hguard, hbit]

theorem byteSwap64_getLsbD_5 (x : BitVec 64) (j : Nat) (hj : j < 8) :
    (byteSwap64 x).getLsbD (8 * 5 + j) = x.getLsbD (8 * (7 - 5) + j) := by
  simp only [byteSwap64, BitVec.getLsbD_or, BitVec.getLsbD_and,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft,
    byteSwap64_mask0_getLsbD, byteSwap64_mask1_getLsbD, byteSwap64_mask2_getLsbD,
    byteSwap64_mask3_getLsbD, byteSwap64_mask4_getLsbD, byteSwap64_mask5_getLsbD,
    byteSwap64_mask6_getLsbD, byteSwap64_mask7_getLsbD]
  have h64 : 8 * 5 + j < 64 := by omega
  have hj64 : j < 64 := by omega
  have hle0 : 8 * 0 ≤ 8 * 5 + j := by omega
  have hnlt0 : ¬ (8 * 5 + j < 8 * 0 + 8) := by omega
  have hle1 : 8 * 1 ≤ 8 * 5 + j := by omega
  have hnlt1 : ¬ (8 * 5 + j < 8 * 1 + 8) := by omega
  have hle2 : 8 * 2 ≤ 8 * 5 + j := by omega
  have hnlt2 : ¬ (8 * 5 + j < 8 * 2 + 8) := by omega
  have hle3 : 8 * 3 ≤ 8 * 5 + j := by omega
  have hnlt3 : ¬ (8 * 5 + j < 8 * 3 + 8) := by omega
  have hle4 : 8 * 4 ≤ 8 * 5 + j := by omega
  have hnlt4 : ¬ (8 * 5 + j < 8 * 4 + 8) := by omega
  have hle5 : 8 * 5 ≤ 8 * 5 + j := by omega
  have hlt5 : 8 * 5 + j < 8 * 5 + 8 := by omega
  have hnle6 : ¬ (8 * 6 ≤ 8 * 5 + j) := by omega
  have hnle7 : ¬ (8 * 7 ≤ 8 * 5 + j) := by omega
  have hguard : ¬ (8 * 5 + j < 8 * (2 * 5 - 7)) := by omega
  have hbit : 8 * 5 + j - 8 * (2 * 5 - 7) = 8 * (7 - 5) + j := by omega
  simp [hj, h64, hj64, hle0, hnlt0, hle1, hnlt1, hle2, hnlt2, hle3, hnlt3, hle4, hnlt4, hle5, hlt5, hnle6, hnle7, hguard, hbit]

theorem byteSwap64_getLsbD_6 (x : BitVec 64) (j : Nat) (hj : j < 8) :
    (byteSwap64 x).getLsbD (8 * 6 + j) = x.getLsbD (8 * (7 - 6) + j) := by
  simp only [byteSwap64, BitVec.getLsbD_or, BitVec.getLsbD_and,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft,
    byteSwap64_mask0_getLsbD, byteSwap64_mask1_getLsbD, byteSwap64_mask2_getLsbD,
    byteSwap64_mask3_getLsbD, byteSwap64_mask4_getLsbD, byteSwap64_mask5_getLsbD,
    byteSwap64_mask6_getLsbD, byteSwap64_mask7_getLsbD]
  have h64 : 8 * 6 + j < 64 := by omega
  have hj64 : j < 64 := by omega
  have hle0 : 8 * 0 ≤ 8 * 6 + j := by omega
  have hnlt0 : ¬ (8 * 6 + j < 8 * 0 + 8) := by omega
  have hle1 : 8 * 1 ≤ 8 * 6 + j := by omega
  have hnlt1 : ¬ (8 * 6 + j < 8 * 1 + 8) := by omega
  have hle2 : 8 * 2 ≤ 8 * 6 + j := by omega
  have hnlt2 : ¬ (8 * 6 + j < 8 * 2 + 8) := by omega
  have hle3 : 8 * 3 ≤ 8 * 6 + j := by omega
  have hnlt3 : ¬ (8 * 6 + j < 8 * 3 + 8) := by omega
  have hle4 : 8 * 4 ≤ 8 * 6 + j := by omega
  have hnlt4 : ¬ (8 * 6 + j < 8 * 4 + 8) := by omega
  have hle5 : 8 * 5 ≤ 8 * 6 + j := by omega
  have hnlt5 : ¬ (8 * 6 + j < 8 * 5 + 8) := by omega
  have hle6 : 8 * 6 ≤ 8 * 6 + j := by omega
  have hlt6 : 8 * 6 + j < 8 * 6 + 8 := by omega
  have hnle7 : ¬ (8 * 7 ≤ 8 * 6 + j) := by omega
  have hguard : ¬ (8 * 6 + j < 8 * (2 * 6 - 7)) := by omega
  have hbit : 8 * 6 + j - 8 * (2 * 6 - 7) = 8 * (7 - 6) + j := by omega
  simp [hj, h64, hj64, hle0, hnlt0, hle1, hnlt1, hle2, hnlt2, hle3, hnlt3, hle4, hnlt4, hle5, hnlt5, hle6, hlt6, hnle7, hguard, hbit]

theorem byteSwap64_getLsbD_7 (x : BitVec 64) (j : Nat) (hj : j < 8) :
    (byteSwap64 x).getLsbD (8 * 7 + j) = x.getLsbD (8 * (7 - 7) + j) := by
  simp only [byteSwap64, BitVec.getLsbD_or, BitVec.getLsbD_and,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft,
    byteSwap64_mask0_getLsbD, byteSwap64_mask1_getLsbD, byteSwap64_mask2_getLsbD,
    byteSwap64_mask3_getLsbD, byteSwap64_mask4_getLsbD, byteSwap64_mask5_getLsbD,
    byteSwap64_mask6_getLsbD, byteSwap64_mask7_getLsbD]
  have h64 : 8 * 7 + j < 64 := by omega
  have hj64 : j < 64 := by omega
  have hle0 : 8 * 0 ≤ 8 * 7 + j := by omega
  have hnlt0 : ¬ (8 * 7 + j < 8 * 0 + 8) := by omega
  have hle1 : 8 * 1 ≤ 8 * 7 + j := by omega
  have hnlt1 : ¬ (8 * 7 + j < 8 * 1 + 8) := by omega
  have hle2 : 8 * 2 ≤ 8 * 7 + j := by omega
  have hnlt2 : ¬ (8 * 7 + j < 8 * 2 + 8) := by omega
  have hle3 : 8 * 3 ≤ 8 * 7 + j := by omega
  have hnlt3 : ¬ (8 * 7 + j < 8 * 3 + 8) := by omega
  have hle4 : 8 * 4 ≤ 8 * 7 + j := by omega
  have hnlt4 : ¬ (8 * 7 + j < 8 * 4 + 8) := by omega
  have hle5 : 8 * 5 ≤ 8 * 7 + j := by omega
  have hnlt5 : ¬ (8 * 7 + j < 8 * 5 + 8) := by omega
  have hle6 : 8 * 6 ≤ 8 * 7 + j := by omega
  have hnlt6 : ¬ (8 * 7 + j < 8 * 6 + 8) := by omega
  have hle7 : 8 * 7 ≤ 8 * 7 + j := by omega
  have hlt7 : 8 * 7 + j < 8 * 7 + 8 := by omega
  have hguard : ¬ (8 * 7 + j < 8 * (2 * 7 - 7)) := by omega
  have hbit : 8 * 7 + j - 8 * (2 * 7 - 7) = 8 * (7 - 7) + j := by omega
  simp [hj, h64, hj64, hle0, hnlt0, hle1, hnlt1, hle2, hnlt2, hle3, hnlt3, hle4, hnlt4, hle5, hnlt5, hle6, hnlt6, hle7, hlt7, hguard, hbit]

theorem byteSwap64_getLsbD (x : BitVec 64) (p j : Nat) (hp : p < 8) (hj : j < 8) :
    (byteSwap64 x).getLsbD (8 * p + j) = x.getLsbD (8 * (7 - p) + j) := by
  have hp_cases : p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 3 ∨ p = 4 ∨ p = 5 ∨ p = 6 ∨ p = 7 := by
    omega
  rcases hp_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa using byteSwap64_getLsbD_0 x j hj
  · simpa using byteSwap64_getLsbD_1 x j hj
  · simpa using byteSwap64_getLsbD_2 x j hj
  · simpa using byteSwap64_getLsbD_3 x j hj
  · simpa using byteSwap64_getLsbD_4 x j hj
  · simpa using byteSwap64_getLsbD_5 x j hj
  · simpa using byteSwap64_getLsbD_6 x j hj
  · simpa using byteSwap64_getLsbD_7 x j hj

/-- The `p`-th byte of `byteSwap64 x` is the `(7-p)`-th byte of `x`. -/
theorem byteSwap64_extractLsb (x : BitVec 64) (p : Nat) (hp : p < 8) :
    (byteSwap64 x).extractLsb' (8 * p) 8 = x.extractLsb' (8 * (7 - p)) 8 := by
  ext j hj
  simpa only [BitVec.getElem_extractLsb'] using byteSwap64_getLsbD x p j hp hj

/-! ## A 64-bit word is determined by its eight bytes -/

theorem eq_of_byte_extractLsb {x y : BitVec 64}
    (h : ∀ p : Nat, p < 8 → x.extractLsb' (8 * p) 8 = y.extractLsb' (8 * p) 8) :
    x = y := by
  ext i hi
  rw [← BitVec.getLsbD_eq_getElem hi, ← BitVec.getLsbD_eq_getElem hi]
  have hp : i / 8 < 8 := by omega
  have hmod : i % 8 < 8 := Nat.mod_lt _ (by decide)
  have hdiv : 8 * (i / 8) + i % 8 = i := by omega
  have hb := congrArg (fun z => z.getLsbD (i % 8)) (h (i / 8) hp)
  simpa [BitVec.getLsbD_extractLsb', hmod, hdiv] using hb

/-! ## The structural byte-reversal kernel

`byteSwap64Kernel x` extracts the eight bytes of `x` and concatenates them in
reverse order: the high byte of the result is the low byte of `x`, and so on.
Each `++` is eight bits wide, so the definition is manifestly a permutation of
the eight byte blocks. -/

def byteSwap64Kernel (x : BitVec 64) : BitVec 64 :=
  x.extractLsb' 0 8 ++
    (x.extractLsb' 8 8 ++
      (x.extractLsb' 16 8 ++
        (x.extractLsb' 24 8 ++
          (x.extractLsb' 32 8 ++
            (x.extractLsb' 40 8 ++
              (x.extractLsb' 48 8 ++
                x.extractLsb' 56 8))))))

/-- Peel the high byte off the kernel until the requested byte is reached. -/
macro "byteSwap64_kernel_byte" : tactic => `(tactic|
  (unfold byteSwap64Kernel
   repeat rw [BitVec.extractLsb'_append_eq_of_add_le (by decide)]
   first
    | rw [BitVec.extractLsb'_append_eq_left]
    | rw [BitVec.extractLsb'_append_eq_right]
    | rw [BitVec.extractLsb'_eq_self]))

theorem byteSwap64Kernel_extractLsb_0 (x : BitVec 64) :
    (byteSwap64Kernel x).extractLsb' 0 8 = x.extractLsb' 56 8 := by
  byteSwap64_kernel_byte

theorem byteSwap64Kernel_extractLsb_1 (x : BitVec 64) :
    (byteSwap64Kernel x).extractLsb' 8 8 = x.extractLsb' 48 8 := by
  byteSwap64_kernel_byte

theorem byteSwap64Kernel_extractLsb_2 (x : BitVec 64) :
    (byteSwap64Kernel x).extractLsb' 16 8 = x.extractLsb' 40 8 := by
  byteSwap64_kernel_byte

theorem byteSwap64Kernel_extractLsb_3 (x : BitVec 64) :
    (byteSwap64Kernel x).extractLsb' 24 8 = x.extractLsb' 32 8 := by
  byteSwap64_kernel_byte

theorem byteSwap64Kernel_extractLsb_4 (x : BitVec 64) :
    (byteSwap64Kernel x).extractLsb' 32 8 = x.extractLsb' 24 8 := by
  byteSwap64_kernel_byte

theorem byteSwap64Kernel_extractLsb_5 (x : BitVec 64) :
    (byteSwap64Kernel x).extractLsb' 40 8 = x.extractLsb' 16 8 := by
  byteSwap64_kernel_byte

theorem byteSwap64Kernel_extractLsb_6 (x : BitVec 64) :
    (byteSwap64Kernel x).extractLsb' 48 8 = x.extractLsb' 8 8 := by
  byteSwap64_kernel_byte

theorem byteSwap64Kernel_extractLsb_7 (x : BitVec 64) :
    (byteSwap64Kernel x).extractLsb' 56 8 = x.extractLsb' 0 8 := by
  byteSwap64_kernel_byte

/-- The `p`-th byte of the structural kernel is the `(7-p)`-th byte of `x`. -/
theorem byteSwap64Kernel_extractLsb (x : BitVec 64) (p : Nat) (hp : p < 8) :
    (byteSwap64Kernel x).extractLsb' (8 * p) 8 = x.extractLsb' (8 * (7 - p)) 8 := by
  have hp_cases : p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 3 ∨ p = 4 ∨ p = 5 ∨ p = 6 ∨ p = 7 := by
    omega
  rcases hp_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa using byteSwap64Kernel_extractLsb_0 x
  · simpa using byteSwap64Kernel_extractLsb_1 x
  · simpa using byteSwap64Kernel_extractLsb_2 x
  · simpa using byteSwap64Kernel_extractLsb_3 x
  · simpa using byteSwap64Kernel_extractLsb_4 x
  · simpa using byteSwap64Kernel_extractLsb_5 x
  · simpa using byteSwap64Kernel_extractLsb_6 x
  · simpa using byteSwap64Kernel_extractLsb_7 x

/-! ## Agreement with `ByteSwap.lean`, and the permutation laws -/

/-- The definition in `ProofsLean/ByteSwap.lean` agrees with the structural
byte-reversal kernel on every input. -/
theorem byteSwap64_eq_kernel (x : BitVec 64) :
    byteSwap64 x = byteSwap64Kernel x := by
  apply eq_of_byte_extractLsb
  intro p hp
  rw [byteSwap64_extractLsb x p hp, byteSwap64Kernel_extractLsb x p hp]

/-- Byte reversal is an involution. -/
theorem byteSwap64Kernel_involutive (x : BitVec 64) :
    byteSwap64Kernel (byteSwap64Kernel x) = x := by
  apply eq_of_byte_extractLsb
  intro p hp
  have hp7 : 7 - p < 8 := by omega
  rw [byteSwap64Kernel_extractLsb (byteSwap64Kernel x) p hp,
    byteSwap64Kernel_extractLsb x (7 - p) hp7]
  have h : 7 - (7 - p) = p := by omega
  rw [h]

/-- Byte reversal is injective. -/
theorem byteSwap64Kernel_injective : Function.Injective byteSwap64Kernel := by
  intro x y hxy
  apply eq_of_byte_extractLsb
  intro p hp
  have hp7 : 7 - p < 8 := by omega
  have hb := congrArg (fun z => z.extractLsb' (8 * (7 - p)) 8) hxy
  rw [byteSwap64Kernel_extractLsb x (7 - p) hp7,
    byteSwap64Kernel_extractLsb y (7 - p) hp7] at hb
  have h : 7 - (7 - p) = p := by omega
  rw [h] at hb
  exact hb

/-- Drop-in replacement for `ByteSwap.byteSwap64_involutive`, with no native
`bv_decide` axiom in its trust closure. -/
theorem byteSwap64_involutive_kernel (x : BitVec 64) :
    byteSwap64 (byteSwap64 x) = x := by
  rw [byteSwap64_eq_kernel (byteSwap64 x), byteSwap64_eq_kernel x]
  exact byteSwap64Kernel_involutive x

/-- Drop-in replacement for `ProgramWitness.byteSwap64_injective`, with no native
`bv_decide` axiom in its trust closure. -/
theorem byteSwap64_injective_kernel : Function.Injective byteSwap64 := by
  intro x y hxy
  apply byteSwap64Kernel_injective
  simpa [byteSwap64_eq_kernel] using hxy

/-- The structural kernel is equal to the definition in `ByteSwap.lean`. -/
theorem byteSwap64Kernel_eq (x : BitVec 64) :
    byteSwap64Kernel x = byteSwap64 x :=
  (byteSwap64_eq_kernel x).symm

/-- The structural kernel is surjective (indeed an involution). -/
theorem byteSwap64Kernel_surjective : Function.Surjective byteSwap64Kernel := by
  intro y
  exact ⟨byteSwap64Kernel y, byteSwap64Kernel_involutive y⟩

/-- The structural kernel is injective and surjective, hence a bijection. -/
theorem byteSwap64Kernel_bijective :
    Function.Injective byteSwap64Kernel ∧ Function.Surjective byteSwap64Kernel :=
  ⟨byteSwap64Kernel_injective, byteSwap64Kernel_surjective⟩

/-- The `ByteSwap.lean` function is surjective (indeed an involution). -/
theorem byteSwap64_surjective_kernel : Function.Surjective byteSwap64 := by
  intro y
  exact ⟨byteSwap64 y, byteSwap64_involutive_kernel y⟩

/-- The `ByteSwap.lean` function is injective and surjective, hence a bijection. -/
theorem byteSwap64_bijective_kernel :
    Function.Injective byteSwap64 ∧ Function.Surjective byteSwap64 :=
  ⟨byteSwap64_injective_kernel, byteSwap64_surjective_kernel⟩

/-! ## Trust report -/

#print axioms byteSwap64_mask_getLsbD
#print axioms byteSwap64_mask0_getLsbD
#print axioms byteSwap64_mask1_getLsbD
#print axioms byteSwap64_mask2_getLsbD
#print axioms byteSwap64_mask3_getLsbD
#print axioms byteSwap64_mask4_getLsbD
#print axioms byteSwap64_mask5_getLsbD
#print axioms byteSwap64_mask6_getLsbD
#print axioms byteSwap64_mask7_getLsbD
#print axioms byteSwap64_mask0_getElem
#print axioms byteSwap64_mask1_getElem
#print axioms byteSwap64_mask2_getElem
#print axioms byteSwap64_mask3_getElem
#print axioms byteSwap64_mask4_getElem
#print axioms byteSwap64_mask5_getElem
#print axioms byteSwap64_mask6_getElem
#print axioms byteSwap64_mask7_getElem
#print axioms byteSwap64_getLsbD
#print axioms byteSwap64_extractLsb
#print axioms eq_of_byte_extractLsb
#print axioms byteSwap64Kernel_extractLsb
#print axioms byteSwap64_eq_kernel
#print axioms byteSwap64Kernel_involutive
#print axioms byteSwap64Kernel_injective
#print axioms byteSwap64_involutive_kernel
#print axioms byteSwap64_injective_kernel
#print axioms byteSwap64Kernel_eq
#print axioms byteSwap64Kernel_surjective
#print axioms byteSwap64Kernel_bijective
#print axioms byteSwap64_surjective_kernel
#print axioms byteSwap64_bijective_kernel

end ProofsLean.MNCore
