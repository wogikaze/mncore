import Std.Tactic.BVDecide

namespace ProofsLean.MNCore

/-- Byte reversal of a 64-bit word, following the Convert Endian specification:
output byte i takes input byte 7-i. -/
def byteSwap64 (x : BitVec 64) : BitVec 64 :=
  ((x >>> 56) &&& 0xFF)
    ||| ((x >>> 40) &&& 0xFF00)
    ||| ((x >>> 24) &&& 0xFF0000)
    ||| ((x >>> 8) &&& 0xFF000000)
    ||| ((x <<< 8) &&& 0xFF00000000)
    ||| ((x <<< 24) &&& 0xFF0000000000)
    ||| ((x <<< 40) &&& 0xFF000000000000)
    ||| ((x <<< 56) &&& 0xFF00000000000000)

theorem byteSwap64_involutive (x : BitVec 64) : byteSwap64 (byteSwap64 x) = x := by
  unfold byteSwap64
  bv_decide

end ProofsLean.MNCore
