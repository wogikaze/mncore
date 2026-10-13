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

/// Block-float conversion (SDM 4.4) of one block of raw values of `fmt`.
///
/// `keep` is the number of mantissa bits kept: `man_bits` for double and single, 18 for
/// pseudo-single, and 6 to 9 for half (`hbfn/<n>`). `extended` selects the half-precision
/// extended representation (`hbfe`).
pub fn block_float(fmt: Fmt, block: &[u64], keep: u32, extended: bool) -> Vec<u64> {
    let m = fmt.man_bits;
    let emax = fmt.exp_max();
    let sign_bit = 1u64 << (fmt.width() - 1);
    let exp = |v: u64| (v >> m) & emax;
    let man = |v: u64| v & ((1 << m) - 1);
    // Half drops b = 9 - n low bits; pseudo-single keeps the top 18 of 23 bits.
    let dropped = m - keep;
    let max_e = block.iter().map(|&v| exp(v)).max().unwrap_or(0);
    let mut common = max_e;
    let top_ones = |v: u64| (man(v) >> dropped) == (1 << keep) - 1;
    if block.iter().any(|&v| exp(v) == max_e && top_ones(v)) {
        common += 1;
    }
    if fmt == HALF {
        common += dropped as u64;
    }
    block
        .iter()
        .map(|&v| {
            let s = v & sign_bit;
            if common >= emax {
                return s | (emax << m);
            }
            if max_e == 0 {
                return s;
            }
            if exp(v) == 0 {
                return s | (common << m);
            }
            let d = (common - exp(v)) as u32;
            let sig = (1u128 << m) | man(v) as u128;
            let flag = extended && (d > 6 + dropped || (d == 6 + dropped && !top_ones(v)));
            // M = sig * 2^(e - common - 1): the hidden bit lands on the field MSB when d == 0.
            // Pseudo-single rounds to its top 18 bits, so it shifts `dropped` more and back.
            let shift = if flag { d - 6 } else { d } + 1 + if fmt == HALF { 0 } else { dropped };
            let r = round_shift(sig, shift);
            let r = if fmt == HALF { r } else { r << dropped };
            if r == 0 {
                if flag {
                    return s;
                }
                return s | (common << m);
            }
            let e = if flag { 0 } else { common };
            s | (e << m) | (r as u64 & ((1 << m) - 1))
        })
        .collect()
}

fn round_shift(v: u128, shift: u32) -> u128 {
    if shift == 0 {
        return v;
    }
    if shift >= 128 {
        return 0;
    }
    let k = v >> shift;
    let rem = v & ((1u128 << shift) - 1);
    let half = 1u128 << (shift - 1);
    k + (rem > half || (rem == half && k & 1 == 1)) as u128
}

/// Format of block-float values for the matrix product: mantissa bits used and dropped
/// partial products, per SDM 4.5.
#[derive(Clone, Copy, Debug)]
pub struct BfFmt {
    pub fmt: Fmt,
    /// Mantissa field bits that take part (18 for pseudo-single).
    pub m: u32,
}

pub const BF_DOUBLE: BfFmt = BfFmt { fmt: DOUBLE, m: 52 };
pub const BF_SINGLE: BfFmt = BfFmt { fmt: SINGLE, m: 23 };
pub const BF_PSEUDO: BfFmt = BfFmt { fmt: SINGLE, m: 18 };
pub const BF_HALF: BfFmt = BfFmt { fmt: HALF, m: 9 };

/// Exact dot product of block-float vectors (SDM 4.5), as a value to be added to c and rounded.
pub fn bf_dot(bf: BfFmt, a: &[u64], b: &[u64]) -> Val {
    let f = bf.fmt;
    let emax = f.exp_max();
    let decode = |v: u64| {
        let neg = (v >> (f.width() - 1)) & 1 == 1;
        let e = (v >> f.man_bits) & emax;
        let mant = (v & ((1 << f.man_bits) - 1)) >> (f.man_bits - bf.m);
        (neg, e, mant as u128)
    };
    // The half extended representation stores exponent 0 for "common exponent - 6".
    let common = |xs: &[u64]| xs.iter().map(|&v| (v >> f.man_bits) & emax).max().unwrap_or(0);
    let (ca, cb) = (common(a), common(b));
    let mut terms: Vec<(bool, u128, i32)> = Vec::new();
    let mut inf: Option<bool> = None;
    for (&x, &y) in a.iter().zip(b) {
        let (na, mut ea, ma) = decode(x);
        let (nb, mut eb, mb) = decode(y);
        let neg = na ^ nb;
        if ma == 0 || mb == 0 {
            continue;
        }
        if ea == emax || eb == emax {
            inf = Some(neg);
            continue;
        }
        if ea == 0 {
            ea = ca.saturating_sub(6);
        }
        if eb == 0 {
            eb = cb.saturating_sub(6);
        }
        let mut p = ma * mb;
        if let Some(full) = f.mul_full_bits {
            if bf.m == f.man_bits {
                let low = f.man_bits - full;
                let lm = (1u128 << low) - 1;
                let dropped = (ma & lm) * (mb & lm);
                if dropped != 0 {
                    p = p - dropped + (1u128 << (2 * low - 2));
                }
            }
        }
        // value = Ma * Mb * 2^(ea + eb - 2 bias - 2 (m - 1))
        let e = ea as i32 + eb as i32 - 2 * f.bias() - 2 * (bf.m as i32 - 1);
        terms.push((neg, p, e));
    }
    if let Some(neg) = inf {
        return Val::Inf { neg };
    }
    let Some(min_e) = terms.iter().map(|t| t.2).min() else {
        return Val::Zero { neg: false };
    };
    let mut acc: Val = Val::Zero { neg: false };
    let mut int: i128 = 0;
    let mut exact = true;
    for &(neg, p, e) in &terms {
        let sh = (e - min_e) as u32;
        if sh > 16 || p.leading_zeros() < sh + 4 {
            exact = false;
            break;
        }
        let v = (p << sh) as i128;
        int += if neg { -v } else { v };
    }
    if exact {
        if int == 0 {
            return Val::Zero { neg: false };
        }
        return Val::Fin { neg: int < 0, sig: int.unsigned_abs(), exp: min_e };
    }
    // Invalid block-float input (exponents differ widely): undefined in the SDM.
    for &(neg, p, e) in &terms {
        acc = add_exact(acc, Val::Fin { neg, sig: p, exp: e });
    }
    acc
}

/// Matrix FMA: rounds `dot + c` once to `out` (SDM 4.5, then the same steps as 4.3).
pub fn mat_fma(out: Fmt, dot: Val, c: Val) -> u64 {
    encode(out, add_exact(dot, c))
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
