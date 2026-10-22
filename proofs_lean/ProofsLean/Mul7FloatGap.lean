import ProofsLean.Mul7Spec

/-! # Problem `4.mul7` — why the float datapath of this repository cannot carry the answer

`4.mul7` multiplies **integers** `X[i] <= 1000` held as `ULong`. The public
accepted answer (`problems/challenge/4.mul7/answer.vsm`, six lines) reaches that
through the single-precision MAU, and the emulator accepts it. This module
records, in Lean, why the repository's bit-level float model cannot reproduce
that value: `ProofsLean.MNCore.SingleFMA.decode` flushes every exponent-zero
pattern to `.zero`, i.e. it models flush-to-zero and no subnormals
(`viz/core/src/float.rs` says the same: "no subnormals and no NaN"), while every
admissible input word of `4.mul7` **is** an exponent-zero (subnormal) pattern.

Consequently, in this model, a float multiply of an admissible input word by
`7.0f` yields `0`, never `7 * X`. That is a genuine instrument gap: it means
the correctness of the published answer cannot be *stated* against
`SingleFMA.singleFma`, no matter how the executor is inverted, and it is the
reason stage 2 of the `4.mul7` optimality track is open.

## Results

* `mul7_input_is_subnormal` — every admissible input word decodes to zero.
* `mul7_float_multiply_is_zero` — `singleFma X 7.0f 0 = 0` for `X <= 1000`, so
  the modelled MAU cannot produce the required `7 * X != 0`.
* `mul7_required_is_not_zero` — the required value for `X = 5` is `35 != 0`.

No `sorry`, no `admit`, no `native_decide`, no new axioms, no edited module.
-/

namespace ProofsLean.MNCore.Mul7Float

open ProofsLean.MNCore

/-- `7.0f`, the multiplier the published answer materialises with
`imm i"1088421888" $ls64v` (`1088421888 = 0x40E00000`). -/
def seven : BitVec 32 := 0x40E00000

theorem seven_bits : seven = BitVec.ofNat 32 1088421888 := by decide

/-- **Every admissible `4.mul7` input word is a subnormal (`f32`) pattern**, and
the repository's float model decodes exponent-zero patterns as `.zero`. -/
theorem mul7_input_is_subnormal (m : Nat) (bounded : m < 2 ^ 23) :
    ProofsLean.MNCore.SingleFMA.decode (BitVec.ofNat 32 m) =
      ProofsLean.MNCore.SingleFMA.Value.zero false := by
  have rawLt : (BitVec.ofNat 32 m).toNat = m := by
    rw [BitVec.toNat_ofNat]
    omega
  have exponentZero : m / 2 ^ 23 % 256 = 0 := by
    rw [show m / 2 ^ 23 = 0 from Nat.div_eq_of_lt bounded, Nat.zero_mod]
  have signZero : m / 2 ^ 31 % 2 = 0 := by
    rw [show m / 2 ^ 31 = 0 from Nat.div_eq_of_lt (by omega), Nat.zero_mod]
  simp only [ProofsLean.MNCore.SingleFMA.decode, rawLt, exponentZero, signZero]
  rfl

/-- **The modelled float MAU maps every admissible input to zero.**  A float
multiply of an exponent-zero pattern by `7.0f` with a zero accumulator is `0` in
`SingleFMA`, so it can never produce the required `7 * X`. -/
theorem mul7_float_multiply_is_zero (m : Nat) (bounded : m < 2 ^ 23) :
    ProofsLean.MNCore.SingleFMA.singleFma (BitVec.ofNat 32 m) seven 0 = 0 := by
  have decoded := mul7_input_is_subnormal m bounded
  have decodedZero : ProofsLean.MNCore.SingleFMA.decode (0 : BitVec 32) =
      ProofsLean.MNCore.SingleFMA.Value.zero false := by decide
  unfold ProofsLean.MNCore.SingleFMA.singleFma
  simp only [decoded, decodedZero]
  cases hb : ProofsLean.MNCore.SingleFMA.decode seven with
  | zero negative =>
      simp [ProofsLean.MNCore.SingleFMA.multiply, ProofsLean.MNCore.SingleFMA.add,
        ProofsLean.MNCore.SingleFMA.encode]
  | infinity negative =>
      simp [ProofsLean.MNCore.SingleFMA.multiply, ProofsLean.MNCore.SingleFMA.add,
        ProofsLean.MNCore.SingleFMA.encode]
  | finite negative significand exponent =>
      simp [ProofsLean.MNCore.SingleFMA.multiply, ProofsLean.MNCore.SingleFMA.add,
        ProofsLean.MNCore.SingleFMA.encode]

/-- The required value for the input word `5` is `35`, which is not `0`. -/
theorem mul7_required_is_not_zero :
    ((7 : BitVec 32) * 5 = 35) ∧ ((35 : BitVec 32) ≠ 0) := by decide

/-- The specification's own value for the all-`5` input is `35`, while the
modelled float datapath of that word is `0`: the gap is value-level, not
executor-level. -/
theorem mul7_model_gap :
    ProofsLean.MNCore.SingleFMA.singleFma (BitVec.ofNat 32 5) seven 0 = 0 ∧
      (7 : BitVec 32) * 5 = 35 := by
  refine ⟨mul7_float_multiply_is_zero 5 (by decide), ?_⟩
  decide

end ProofsLean.MNCore.Mul7Float

-- End of module: no sorry, no admit, no native_decide, no new axioms.
