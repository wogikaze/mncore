import ProofsLean.PEMemory

namespace ProofsLean.MNCore.PEMemory

/-- For LM0 the address depends only on T modulo the memory capacity,
including when dynamic offsets are rounded down to the access alignment. -/
theorem indirect_high_bits_irrelevant (width : Width) (schedule : Schedule)
    (bar : BitVec 12) (x y : BitVec 64) (pe cycle : Fin 4)
    (sameLowBits : x.toNat % 4096 = y.toNat % 4096) :
    address .lm0 width schedule bar (.tIndirect x) pe cycle =
      address .lm0 width schedule bar (.tIndirect y) pe cycle := by
  apply Fin.ext
  cases width <;> simp [address, count, baseOffset, Adjustment.offset, Width.words, Bank.capacity] <;> omega

/-- MADPE changes only PEs at or below its threshold. This lemma is about
the address primitive; Adjustment.Allowed separately limits its legal banks. -/
theorem madpe_above_threshold_unchanged (bank : Bank) (width : Width)
    (schedule : Schedule) (bar : BitVec 12) (threshold pe cycle : Fin 4)
    (above : threshold.val < pe.val) :
    address bank width schedule bar (.madpe threshold) pe cycle =
      address bank width schedule bar .direct pe cycle := by
  simp [address, Adjustment.offset, Nat.not_le.mpr above]

end ProofsLean.MNCore.PEMemory
