//! Reductions of the result reduction network (RRN), used by L1BM, L2BM and MV reductions
//! (SDM 3.5.5 and 4.2).

use crate::blockop::{Rrn, RrnOp};
use crate::float::{self, Fmt, DOUBLE, HALF, SINGLE};

pub fn fmt_of(prec: char) -> Fmt {
    match prec {
        'd' => DOUBLE,
        'f' => SINGLE,
        _ => HALF,
    }
}

fn mask(bits: u32) -> u64 {
    if bits == 64 {
        u64::MAX
    } else {
        (1u64 << bits) - 1
    }
}

/// The identity element sent by L1Bs outside the selected set.
pub fn unit_value(rrn: Rrn) -> u64 {
    let bits = rrn.bits();
    match rrn.op {
        RrnOp::Fadd | RrnOp::Iadd | RrnOp::Bor | RrnOp::Or => 0,
        RrnOp::Band => mask(bits),
        RrnOp::And => 1,
        // Max/min compare sign-magnitude integers: the smallest is all ones (negative, largest
        // magnitude), the largest is all ones without the sign bit.
        RrnOp::Max => mask(bits),
        RrnOp::Min => mask(bits) >> 1,
    }
}

/// One reduction stage over `vals` (raw elements of the RRN precision). For float addition the
/// result is rounded to `out` (SDM 4.2.1); other operations ignore `out`.
pub fn reduce(rrn: Rrn, vals: &[u64], out: Fmt) -> u64 {
    let bits = rrn.bits();
    let m = mask(bits);
    match rrn.op {
        RrnOp::Fadd => fadd(fmt_of(rrn.prec), vals, out),
        RrnOp::Max | RrnOp::Min => {
            // Sign-magnitude integer comparison; +0 is larger than -0 (SDM 4.2.2).
            let key = |v: u64| -> i128 {
                let neg = (v >> (bits - 1)) & 1 == 1;
                let mag = (v & (m >> 1)) as i128;
                if neg {
                    -mag - 1
                } else {
                    mag
                }
            };
            let pick = if rrn.op == RrnOp::Max { vals.iter().max_by_key(|&&v| key(v)) } else { vals.iter().min_by_key(|&&v| key(v)) };
            *pick.unwrap()
        }
        RrnOp::Iadd => vals.iter().fold(0u64, |a, &v| a.wrapping_add(v)) & m,
        RrnOp::Band => vals.iter().fold(m, |a, &v| a & v),
        RrnOp::Bor => vals.iter().fold(0, |a, &v| a | v),
        RrnOp::And => vals.iter().all(|&v| v != 0) as u64,
        RrnOp::Or => vals.iter().any(|&v| v != 0) as u64,
    }
}

/// Floating-point addition of the RRN (SDM 4.2.1): each mantissa gets its hidden bit and three
/// zero guard bits, is shifted to the largest exponent with round-to-nearest-even, the
/// mantissas are added exactly, and the sum is rounded once to `out` and normalized.
pub fn fadd(f: Fmt, vals: &[u64], out: Fmt) -> u64 {
    let mbits = f.man_bits;
    let emask = f.exp_max();
    let exp = |v: u64| (v >> mbits) & emask;
    let max_e = vals.iter().map(|&v| exp(v)).max().unwrap_or(0);
    if max_e == 0 {
        return 0;
    }
    if max_e == emask {
        // TODO(difftest): infinities in RRN addition are not defined in the SDM.
        let negs: Vec<bool> = vals.iter().filter(|&&v| exp(v) == emask).map(|&v| (v >> (f.width() - 1)) & 1 == 1).collect();
        let neg = negs.iter().all(|&n| n);
        return out.inf(neg);
    }
    let mut sum: i128 = 0;
    for &v in vals {
        let e = exp(v);
        if e == 0 {
            continue;
        }
        let sig = (((1u128 << mbits) | (v & ((1 << mbits) - 1)) as u128) << 3) as u128;
        let d = (max_e - e) as u32;
        let aligned = round_shift(sig, d) as i128;
        let neg = (v >> (f.width() - 1)) & 1 == 1;
        sum += if neg { -aligned } else { aligned };
    }
    if sum == 0 {
        return 0;
    }
    // value = sum * 2^(max_e - bias - mbits - 3)
    let e = max_e as i32 - f.bias() - mbits as i32 - 3;
    float::round_pack(out, sum < 0, sum.unsigned_abs(), e)
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

/// A 16-element reduction of L1BM done as two stages of 4 (SDM 4.2.1). `mid` is the precision
/// of the first stage's result, `out` that of the second.
pub fn reduce16(rrn: Rrn, vals: &[u64; 16], mid: Fmt, out: Fmt) -> u64 {
    let stage: Vec<u64> = (0..4).map(|g| reduce(rrn, &vals[g * 4..g * 4 + 4], mid)).collect();
    if rrn.op == RrnOp::Fadd && mid != fmt_of(rrn.prec) {
        // The second stage reads the first stage's results in the intermediate precision.
        let r2 = Rrn { prec: if mid == SINGLE { 'f' } else { 'd' }, ..rrn };
        return reduce(r2, &stage, out);
    }
    reduce(rrn, &stage, out)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fadd_basic() {
        let f = |x: f32| x.to_bits() as u64;
        let r = Rrn { prec: 'f', op: RrnOp::Fadd };
        assert_eq!(reduce(r, &[f(1.0), f(2.0), f(3.0), f(4.0)], SINGLE), f(10.0));
        assert_eq!(reduce(r, &[f(1.0), f(-1.0), 0, 0], SINGLE), 0);
    }

    #[test]
    fn max_min_sign_magnitude() {
        let r = Rrn { prec: 'f', op: RrnOp::Max };
        assert_eq!(reduce(r, &[0x8000_0000, 0, 0xbf80_0000, 0xbf00_0000], SINGLE), 0);
        let r = Rrn { prec: 'f', op: RrnOp::Min };
        assert_eq!(reduce(r, &[0x8000_0000, 0, 0x3f80_0000, 0x3f00_0000], SINGLE), 0x8000_0000);
    }
}
