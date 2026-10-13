//! MN-Core 2 floating-point arithmetic.
//!
//! The formats and rounding follow the SDM (judge/sdm/sdm.txt), chapter 1.3 and chapter 4:
//! - half is sign 1 / exponent 6 / mantissa 9 (not IEEE fp16)
//! - no subnormals and no NaN; exponent field 0 is zero, all ones is infinity
//! - results are rounded once, to nearest even, then "normalized" (SDM 4.1):
//!   zero and infinity get an all-zero mantissa, and zero always gets a positive sign

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Fmt {
    pub exp_bits: u32,
    pub man_bits: u32,
    /// Number of high mantissa bits that take part in every partial product of a multiplication.
    /// Products of two mantissa bits that are both below this position are dropped and replaced
    /// by a correction term (SDM 4.3, equations 4.6 to 4.9). `None` means the product is exact.
    pub mul_full_bits: Option<u32>,
}

pub const HALF: Fmt = Fmt { exp_bits: 6, man_bits: 9, mul_full_bits: None };
pub const SINGLE: Fmt = Fmt { exp_bits: 8, man_bits: 23, mul_full_bits: Some(18) };
pub const DOUBLE: Fmt = Fmt { exp_bits: 11, man_bits: 52, mul_full_bits: Some(36) };

impl Fmt {
    pub const fn bias(self) -> i32 {
        (1 << (self.exp_bits - 1)) - 1
    }
    pub const fn exp_max(self) -> u64 {
        (1 << self.exp_bits) - 1
    }
    pub const fn width(self) -> u32 {
        1 + self.exp_bits + self.man_bits
    }
    const fn man_mask(self) -> u64 {
        (1 << self.man_bits) - 1
    }
    pub fn inf(self, neg: bool) -> u64 {
        ((neg as u64) << (self.width() - 1)) | (self.exp_max() << self.man_bits)
    }
}

/// A decoded floating-point value.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Val {
    Zero { neg: bool },
    Inf { neg: bool },
    /// `sig * 2^exp`, where `sig` includes the hidden bit.
    Fin { neg: bool, sig: u128, exp: i32 },
}

impl Val {
    fn neg(self) -> bool {
        match self {
            Val::Zero { neg } | Val::Inf { neg } | Val::Fin { neg, .. } => neg,
        }
    }
    pub fn negate(self) -> Val {
        match self {
            Val::Zero { neg } => Val::Zero { neg: !neg },
            Val::Inf { neg } => Val::Inf { neg: !neg },
            Val::Fin { neg, sig, exp } => Val::Fin { neg: !neg, sig, exp },
        }
    }
}

pub fn decode(fmt: Fmt, bits: u64) -> Val {
    let neg = (bits >> (fmt.width() - 1)) & 1 == 1;
    let e = (bits >> fmt.man_bits) & fmt.exp_max();
    let m = bits & fmt.man_mask();
    if e == 0 {
        Val::Zero { neg }
    } else if e == fmt.exp_max() {
        Val::Inf { neg }
    } else {
        let sig = (1u128 << fmt.man_bits) | m as u128;
        Val::Fin { neg, sig, exp: e as i32 - fmt.bias() - fmt.man_bits as i32 }
    }
}

/// Rounds `sig * 2^exp` to `fmt` with round-to-nearest-even, then normalizes (SDM 4.1, 4.3).
pub fn round_pack(fmt: Fmt, neg: bool, sig: u128, exp: i32) -> u64 {
    if sig == 0 {
        return 0;
    }
    let m = fmt.man_bits as i32;
    let mut p = 127 - sig.leading_zeros() as i32;
    let mut keep: u128 = if p > m {
        let shift = (p - m) as u32;
        let k = sig >> shift;
        let rem = sig & ((1u128 << shift) - 1);
        let half = 1u128 << (shift - 1);
        let up = rem > half || (rem == half && k & 1 == 1);
        k + up as u128
    } else {
        sig << (m - p) as u32
    };
    if keep >> (m + 1) != 0 {
        keep >>= 1;
        p += 1;
    }
    let biased = exp + p + fmt.bias();
    if biased >= fmt.exp_max() as i32 {
        return fmt.inf(neg);
    }
    if biased <= 0 {
        return 0;
    }
    ((neg as u64) << (fmt.width() - 1))
        | ((biased as u64) << fmt.man_bits)
        | (keep as u64 & fmt.man_mask())
}

pub fn encode(fmt: Fmt, v: Val) -> u64 {
    match v {
        Val::Zero { .. } => 0,
        Val::Inf { neg } => fmt.inf(neg),
        Val::Fin { neg, sig, exp } => round_pack(fmt, neg, sig, exp),
    }
}

/// Exact product of two values of `fmt`, including the dropped partial products of SDM 4.3.
fn mul_exact(fmt: Fmt, a: Val, b: Val) -> Val {
    let neg = a.neg() ^ b.neg();
    match (a, b) {
        // Not in the SDM. The emulator gives zero for inf * 0 (difftest_mau).
        (Val::Zero { .. }, _) | (_, Val::Zero { .. }) => Val::Zero { neg },
        (Val::Inf { .. }, _) | (_, Val::Inf { .. }) => Val::Inf { neg },
        (Val::Fin { sig: sa, exp: ea, .. }, Val::Fin { sig: sb, exp: eb, .. }) => {
            let mut prod = sa * sb;
            if let Some(full) = fmt.mul_full_bits {
                let low_bits = fmt.man_bits - full;
                let low_mask = (1u128 << low_bits) - 1;
                let dropped = (sa & low_mask) * (sb & low_mask);
                if dropped != 0 {
                    // r = 2^-(2*full+2) in units of 2^-(2*man_bits)
                    prod = prod - dropped + (1u128 << (2 * low_bits - 2));
                }
            }
            Val::Fin { neg, sig: prod, exp: ea + eb }
        }
    }
}

/// Exact sum of two values, kept to 128 bits with a sticky bit.
///
/// The result is only used for a single rounding to at most 53 bits, so collapsing the bits
/// shifted out of the smaller operand into a sticky bit does not change the rounded result.
fn add_exact(a: Val, b: Val) -> Val {
    match (a, b) {
        // Not in the SDM. The emulator gives +inf for inf + -inf (difftest_mau).
        (Val::Inf { neg: na }, Val::Inf { neg: nb }) => Val::Inf { neg: na && nb },
        (Val::Inf { neg }, _) | (_, Val::Inf { neg }) => Val::Inf { neg },
        (Val::Zero { neg: na }, Val::Zero { neg: nb }) => Val::Zero { neg: na && nb },
        (Val::Zero { .. }, x) | (x, Val::Zero { .. }) => x,
        (Val::Fin { neg: na, sig: sa, exp: ea }, Val::Fin { neg: nb, sig: sb, exp: eb }) => {
            const TOP: i32 = 125;
            let norm = |sig: u128, exp: i32| {
                let p = 127 - sig.leading_zeros() as i32;
                (sig << (TOP - p) as u32, exp - (TOP - p))
            };
            let (sa, ea) = norm(sa, ea);
            let (sb, eb) = norm(sb, eb);
            let ((nh, sh, eh), (nl, sl, el)) =
                if ea >= eb { ((na, sa, ea), (nb, sb, eb)) } else { ((nb, sb, eb), (na, sa, ea)) };
            let d = (eh - el) as u32;
            let sl = if d == 0 {
                sl
            } else if d >= 127 {
                (sl != 0) as u128
            } else {
                (sl >> d) | ((sl & ((1u128 << d) - 1)) != 0) as u128
            };
            if nh == nl {
                Val::Fin { neg: nh, sig: sh + sl, exp: eh }
            } else if sh > sl {
                Val::Fin { neg: nh, sig: sh - sl, exp: eh }
            } else if sl > sh {
                Val::Fin { neg: nl, sig: sl - sh, exp: eh }
            } else {
                Val::Zero { neg: false }
            }
        }
    }
}

/// Vector fused multiply-add `a * b + c` of MAU (SDM 4.3).
///
/// `in_fmt` is the format of a, b and c after any precision extension, and `out_fmt` is the
/// format the result is rounded to (which may be lower when output rounding is requested).
pub fn vfma(in_fmt: Fmt, out_fmt: Fmt, a: Val, b: Val, c: Val) -> u64 {
    let mut c = c;
    // Not in the SDM. The emulator ignores c entirely when its exponent is too far below the
    // product's: 43 for single and 90 for double, which is full + man_bits + 2 (difftest_mau).
    if let (Val::Fin { exp: ea, .. }, Val::Fin { exp: eb, .. }, Val::Fin { exp: ec, .. }) = (a, b, c) {
        let full = in_fmt.mul_full_bits.unwrap_or(in_fmt.man_bits) as i32;
        let m = in_fmt.man_bits as i32;
        let (ea, eb, ec) = (ea + m, eb + m, ec + m);
        if (ea + eb) - ec >= full + m + 2 {
            c = Val::Zero { neg: false };
        }
    }
    encode(out_fmt, add_exact(mul_exact(in_fmt, a, b), c))
}

/// Converts a value to a higher-precision format. The conversion is exact.
pub fn widen(to: Fmt, v: Val) -> u64 {
    encode(to, v)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn f(bits: u32) -> Val {
        decode(SINGLE, bits as u64)
    }
    fn fma32(a: u32, b: u32, c: u32) -> u32 {
        vfma(SINGLE, SINGLE, f(a), f(b), f(c)) as u32
    }

    #[test]
    fn sdm_example_dropped_partial_products() {
        // SDM 4.3: (2^20 + 1)^2 - 2^40 prints 0x4a000010, not the exact 0x4a000004.
        let a = (1048577.0f32).to_bits();
        let c = (-1099511627776.0f32).to_bits();
        assert_eq!(fma32(a, a, c), 0x4a000010);
    }

    #[test]
    fn round_to_nearest_even() {
        let one = 0x3f80_0000;
        assert_eq!(fma32(one, one, 0x3380_0000), 0x3f80_0000); // 1 + 2^-24 ties to even
        assert_eq!(fma32(one, one, 0x33c0_0000), 0x3f80_0001); // 1 + 1.5 * 2^-24 rounds up
        assert_eq!(fma32(0xbf80_0000, one, one), 0); // -1 + 1 is +0
    }

    #[test]
    fn overflow_and_underflow() {
        let two = 0x4000_0000;
        assert_eq!(fma32(0x7f7f_ffff, two, 0), 0x7f80_0000);
        assert_eq!(fma32(0xff7f_ffff, two, 0), 0xff80_0000);
        assert_eq!(fma32(0x0080_0000, 0x3f00_0000, 0), 0); // min normal / 2 flushes to +0
    }

    #[test]
    fn half_one_is_3e00() {
        let one = decode(HALF, 0x3e00);
        assert_eq!(vfma(HALF, HALF, one, one, Val::Zero { neg: false }), 0x3e00);
    }
}
