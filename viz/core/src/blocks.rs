//! L1BM and L2BM state and instruction semantics (SDM 3.6.7, 3.6.8).
//!
//! Layouts follow the pseudo code of the SDM. Addresses are in long words.

use crate::blockop::{L1Op, L2Op, Rrn, RrnOp};
use crate::float::{self, HALF, SINGLE};
use crate::machine::{Bus, ExecError, PES};
use crate::rrn;
use crate::vsm::{Expr, Operand};

pub const L1BS: usize = PES / 64;
pub const L2BS: usize = L1BS / 8;
pub const L1BM_LONGS: usize = 8 * 1024;
pub const L2BM_LONGS: usize = 32 * 1024;

/// Memories of the L2B/L1B levels.
pub struct Blocks {
    pub l1bm: Vec<Vec<u64>>,
    pub l2bm: Vec<Vec<u64>>,
    /// L1BM turnaround register ($lbi) of each L1B: up to 64 long words per cycle.
    pub lbi: Vec<[[u64; 64]; 4]>,
    /// Why $lbi cannot be read, if it cannot (written by a step without PE-to-L1BM transfer).
    pub lbi_error: Option<String>,
}

impl Default for Blocks {
    fn default() -> Self {
        Blocks {
            l1bm: vec![vec![0; L1BM_LONGS]; L1BS],
            l2bm: vec![vec![0; L2BM_LONGS]; L2BS],
            lbi: vec![[[0; 64]; 4]; L1BS],
            lbi_error: Some("the L1BM turnaround register has not been written".into()),
        }
    }
}

/// Pending writes of a step to L1BM, L2BM and the turnaround register.
#[derive(Default)]
pub struct BlockWrites {
    /// (L1B, long word address, value, cycle, expression index).
    pub l1bm: Vec<(usize, usize, u64, u8, u16)>,
    /// Expression index for the next L1BM writes.
    pub expr: u16,
    pub l2bm: Vec<(usize, usize, u64)>,
    /// New turnaround contents per L1B, when a PE-to-L1BM transfer happened.
    pub lbi: Option<Vec<[[u64; 64]; 4]>>,
}

/// The L1BM operand of an L1BM expression: access length (2 or 4 words) and address (None
/// for the turnaround register).
pub fn l1_operand(op: &Operand) -> Option<(u8, Option<u32>)> {
    match op {
        Operand::L1bm { wl, addr } => Some((*wl, *addr)),
        _ => None,
    }
}

fn hi_lo(v: u64) -> [u32; 2] {
    [(v >> 32) as u32, v as u32]
}

fn bus_of(msb: u64, lsb: u64) -> Bus {
    let a = hi_lo(msb);
    let b = hi_lo(lsb);
    [a[0], a[1], b[0], b[1]]
}

fn long(bus: &Bus, k: usize) -> u64 {
    ((bus[2 * k] as u64) << 32) | bus[2 * k + 1] as u64
}

impl Blocks {
    /// Reads L1BM long word `addr` of an L1B, or position `addr` of the turnaround register.
    fn l1_read(&self, l1b: usize, addr: Option<u32>, offset: usize, cycle: usize) -> Result<u64, ExecError> {
        match addr {
            Some(a) => Ok(self.l1bm[l1b][(a as usize + offset) % L1BM_LONGS]),
            None => {
                if let Some(e) = &self.lbi_error {
                    return Err(ExecError::Runtime(format!("reading $lbi failed: {e}")));
                }
                Ok(self.lbi[l1b][cycle][offset % 64])
            }
        }
    }

    /// Values an L1BM-to-PE transfer delivers to every PE in every cycle.
    pub fn l1_to_pe(&self, op: L1Op, src: &Operand) -> Result<Vec<[Bus; 4]>, ExecError> {
        let (wl, addr) = l1_operand(src).ok_or_else(|| ExecError::Unsupported(format!("L1BM source {src:?}")))?;
        let two = wl == 4;
        let mut out = vec![[[0u32; 4]; 4]; PES];
        for l1b in 0..L1BS {
            for c in 0..4 {
                // For the turnaround register the address is relative to this cycle's block.
                let base = |step: usize| if addr.is_some() { c * step } else { 0 };
                for mab in 0..16 {
                    for pe in 0..4 {
                        let (m, l) = match op {
                            L1Op::Pbcast => {
                                let o = if addr.is_some() { c } else { 0 };
                                (self.l1_read(l1b, addr, o, c)?, if two { self.l1_read(l1b, addr, o + 4, c)? } else { 0 })
                            }
                            L1Op::Mbcast => {
                                if two {
                                    (self.l1_read(l1b, addr, base(8) + pe, c)?, self.l1_read(l1b, addr, base(8) + 4 + pe, c)?)
                                } else if addr.is_none() {
                                    // From the turnaround register, the LSB long word carries what
                                    // a two long word transfer would (visible when writing T).
                                    (self.l1_read(l1b, addr, pe, c)?, self.l1_read(l1b, addr, 4 + pe, c)?)
                                } else {
                                    (self.l1_read(l1b, addr, base(4) + pe, c)?, 0)
                                }
                            }
                            L1Op::M4bcast => {
                                let i = mab >> 2;
                                if two {
                                    (self.l1_read(l1b, addr, base(32) + i * 8 + pe, c)?, self.l1_read(l1b, addr, base(32) + i * 8 + 4 + pe, c)?)
                                } else {
                                    (self.l1_read(l1b, addr, base(16) + i * 4 + pe, c)?, 0)
                                }
                            }
                            L1Op::Distrib { mabdiff } => {
                                // PE (mab, pe) receives what MAB (mab - mabdiff) would have.
                                let src_mab = (mab as i32 - mabdiff as i32).rem_euclid(16) as usize;
                                (self.l1_read(l1b, addr, base(64) + src_mab * 4 + pe, c)?, 0)
                            }
                            other => return Err(ExecError::Unsupported(format!("{other:?} is not an L1BM-to-PE transfer"))),
                        };
                        out[l1b * 64 + mab * 4 + pe][c] = bus_of(m, l);
                    }
                }
            }
        }
        Ok(out)
    }

    /// Computes a PE-to-L1BM transfer from the PE values `src[pe][cycle]`.
    /// `src_two` tells whether the PE operand is two long words, which decides the width of
    /// reductions whose result is rounded to half precision.
    pub fn pe_to_l1(&self, op: L1Op, dst: &Operand, src: &[[Bus; 4]], ext: bool, src_two: bool, w: &mut BlockWrites) -> Result<(), ExecError> {
        let (wl, addr) = l1_operand(dst).ok_or_else(|| ExecError::Unsupported(format!("L1BM destination {dst:?}")))?;
        let two = wl == 4;
        // Positions not written keep their old values (measured with the emulator).
        let mut lbi = self.lbi.clone();
        for l1b in 0..L1BS {
            let pe_of = |mab: usize, pe: usize| l1b * 64 + mab * 4 + pe;
            for c in 0..4 {
                // (offset within this cycle's block, value); also the turnaround layout.
                let mut items: Vec<(usize, u64)> = Vec::new();
                let mut turn: Vec<(usize, u64)> = Vec::new();
                match op {
                    L1Op::Mwrite { mab } => {
                        for pe in 0..4 {
                            let b = &src[pe_of(mab as usize, pe)][c];
                            items.push((pe, long(b, 0)));
                            if two {
                                items.push((4 + pe, long(b, 1)));
                            }
                        }
                    }
                    L1Op::M4write { mab } => {
                        for mo in 0..4 {
                            for pe in 0..4 {
                                let b = &src[pe_of(mo * 4 + mab as usize, pe)][c];
                                if two {
                                    items.push((mo * 8 + pe, long(b, 0)));
                                    items.push((mo * 8 + 4 + pe, long(b, 1)));
                                } else {
                                    items.push((mo * 4 + pe, long(b, 0)));
                                }
                            }
                        }
                    }
                    L1Op::Gather { mabdiff } => {
                        for mab in 0..16 {
                            for pe in 0..4 {
                                let v = long(&src[pe_of(mab, pe)][c], 0);
                                let dst_mab = (mab as i32 + mabdiff as i32).rem_euclid(16) as usize;
                                items.push((dst_mab * 4 + pe, v));
                                turn.push((mab * 4 + pe, v));
                            }
                        }
                    }
                    L1Op::Reduce { rrn, round } | L1Op::Reduce4 { rrn, round }
                        if round || ext || rrn.prec == 'h' && rrn.op == RrnOp::Fadd =>
                    {
                        // Reductions with precision extension and/or output rounding (including
                        // the half-precision float reductions, which are implemented that way).
                        let four = matches!(op, L1Op::Reduce4 { .. });
                        let rounded = round || (rrn.prec == 'h' && rrn.op == RrnOp::Fadd);
                        for group in 0..(if four { 4 } else { 1 }) {
                            let mabs: Vec<usize> = if four { (group * 4..group * 4 + 4).collect() } else { (0..16).collect() };
                            let mut res: Vec<Bus> = Vec::new();
                            for pe in 0..4 {
                                let vals: Vec<Bus> = mabs.iter().map(|&m| src[pe_of(m, pe)][c]).collect();
                                res.push(reduce_buses(rrn, round, ext, two || (rounded && src_two), &vals, !four)?);
                            }
                            for pe in 0..4 {
                                if rounded {
                                    // PE p's 4 halves stay together in one long word (measured with
                                    // the emulator); the orders in SDM 3.6.8.4 and 3.6.8.5 describe
                                    // the reduction circuit and cancel out.
                                    let v = (0..4).fold(0u64, |acc, j| {
                                        let l = long(&res[pe], j / 2);
                                        (acc << 16) | ((l >> (32 - 32 * (j % 2) as u32)) & 0xffff)
                                    });
                                    items.push((group * 4 + pe, v));
                                } else if four {
                                    items.push((group * 8 + pe, long(&res[pe], 0)));
                                    items.push((group * 8 + 4 + pe, long(&res[pe], 1)));
                                } else {
                                    items.push((pe, long(&res[pe], 0)));
                                    items.push((4 + pe, long(&res[pe], 1)));
                                }
                            }
                        }
                    }
                    L1Op::Reduce { rrn, round } | L1Op::Reduce4 { rrn, round } => {
                        let four = matches!(op, L1Op::Reduce4 { .. });
                        for group in 0..(if four { 4 } else { 1 }) {
                            for pe in 0..4 {
                                let mabs: Vec<usize> = if four { (group * 4..group * 4 + 4).collect() } else { (0..16).collect() };
                                let vals: Vec<Bus> = mabs.iter().map(|&m| src[pe_of(m, pe)][c]).collect();
                                let red = reduce_buses(rrn, round, ext, two, &vals, !four)?;
                                if two {
                                    let (o0, o1) = if four { (group * 8 + pe, group * 8 + 4 + pe) } else { (pe, 4 + pe) };
                                    items.push((o0, long(&red, 0)));
                                    items.push((o1, long(&red, 1)));
                                } else {
                                    let o = if four { group * 4 + pe } else { pe };
                                    items.push((o, long(&red, 0)));
                                }
                            }
                        }
                    }
                    other => return Err(ExecError::Unsupported(format!("{other:?} is not a PE-to-L1BM transfer"))),
                }
                if turn.is_empty() {
                    turn = items.clone();
                }
                for &(o, v) in &turn {
                    lbi[l1b][c][o % 64] = v;
                }
                if let Some(a) = addr {
                    let step = match op {
                        L1Op::Gather { .. } => 64,
                        L1Op::Reduce { rrn, round } if round || rrn.prec == 'h' && rrn.op == RrnOp::Fadd => 4,
                        L1Op::Reduce4 { rrn, round } if round || rrn.prec == 'h' && rrn.op == RrnOp::Fadd => 16,
                        L1Op::Reduce { .. } if ext => 8,
                        L1Op::Reduce4 { .. } if ext => 32,
                        L1Op::M4write { .. } | L1Op::Reduce4 { .. } => if two { 32 } else { 16 },
                        _ => if two { 8 } else { 4 },
                    };
                    for (o, v) in items {
                        w.l1bm.push((l1b, (a as usize + c * step + o) % L1BM_LONGS, v, c as u8, w.expr));
                    }
                }
            }
        }
        w.lbi = Some(lbi);
        Ok(())
    }

    /// Computes an L2BM expression.
    pub fn l2(&self, e: &Expr, op: L2Op, w: &mut BlockWrites) -> Result<(), ExecError> {
        let addr = |o: &Operand| -> Result<usize, ExecError> {
            match o {
                Operand::L1bm { addr: Some(a), .. } => Ok(*a as usize),
                Operand::L2bm { addr, .. } => Ok(*addr as usize),
                other => Err(ExecError::Unsupported(format!("L2BM operand {other:?}"))),
            }
        };
        if matches!(op, L2Op::Dars | L2Op::Darw) {
            return Err(ExecError::Unsupported("l2bmdars / l2bmdarw (DAR)".into()));
        }
        let a0 = addr(e.srcs.first().ok_or_else(|| ExecError::Unsupported("missing operand".into()))?)?;
        let a1 = addr(e.dsts.first().ok_or_else(|| ExecError::Unsupported("missing operand".into()))?)?;
        for l2 in 0..L2BS {
            let l1 = |b: usize| l2 * 8 + b;
            for c in 0..4 {
                match op {
                    L2Op::Bcast { set } => {
                        for b in (0..8).filter(|&b| set.contains(b)) {
                            for k in 0..16 {
                                w.l1bm.push((l1(b), (a1 + c * 16 + k) % L1BM_LONGS, self.l2bm[l2][(a0 + c * 16 + k) % L2BM_LONGS], c as u8, w.expr));
                            }
                        }
                    }
                    L2Op::Bcast2 { set } => {
                        for b in (0..8).filter(|&b| set.contains(b)) {
                            for k in 0..16 {
                                let v = self.l2bm[l2][(a0 + c * 64 + 16 * (b / 2) + k) % L2BM_LONGS];
                                w.l1bm.push((l1(b), (a1 + c * 16 + k) % L1BM_LONGS, v, c as u8, w.expr));
                            }
                        }
                    }
                    L2Op::Distrib { set } => {
                        for b in (0..8).filter(|&b| set.contains(b)) {
                            for k in 0..8 {
                                let v = self.l2bm[l2][(a0 + c * 64 + 8 * b + k) % L2BM_LONGS];
                                w.l1bm.push((l1(b), (a1 + c * 8 + k) % L1BM_LONGS, v, c as u8, w.expr));
                            }
                        }
                    }
                    L2Op::FromL1b { l1b } => {
                        for k in 0..16 {
                            let v = self.l1bm[l1(l1b as usize)][(a0 + c * 16 + k) % L1BM_LONGS];
                            w.l2bm.push((l2, (a1 + c * 16 + k) % L2BM_LONGS, v));
                        }
                    }
                    L2Op::Gather => {
                        for b in 0..8 {
                            for k in 0..8 {
                                let v = self.l1bm[l1(b)][(a0 + c * 8 + k) % L1BM_LONGS];
                                w.l2bm.push((l2, (a1 + c * 64 + 8 * b + k) % L2BM_LONGS, v));
                            }
                        }
                    }
                    L2Op::Reduce { rrn, set } => {
                        for k in 0..16 {
                            let vals: Vec<u64> = (0..8)
                                .map(|b| if set.contains(b) { self.l1bm[l1(b)][(a0 + c * 16 + k) % L1BM_LONGS] } else { unit_long(rrn) })
                                .collect();
                            w.l2bm.push((l2, (a1 + c * 16 + k) % L2BM_LONGS, reduce_longs(rrn, &vals)));
                        }
                    }
                    L2Op::Reduce2 { rrn } => {
                        for g in 0..4 {
                            for k in 0..16 {
                                let vals: Vec<u64> = (0..2).map(|j| self.l1bm[l1(2 * g + j)][(a0 + c * 16 + k) % L1BM_LONGS]).collect();
                                w.l2bm.push((l2, (a1 + c * 64 + 16 * g + k) % L2BM_LONGS, reduce_longs(rrn, &vals)));
                            }
                        }
                    }
                    L2Op::Imcast { set } => {
                        for s in (0..8).filter(|&b| set.contains(b)) {
                            for d in (0..8).filter(|&d| d != s && d as u8 & set.immode == s as u8 & set.immode) {
                                for k in 0..16 {
                                    let v = self.l1bm[l1(s)][(a0 + c * 16 + k) % L1BM_LONGS];
                                    w.l1bm.push((l1(d), (a1 + c * 16 + k) % L1BM_LONGS, v, c as u8, w.expr));
                                }
                            }
                        }
                    }
                    L2Op::Dars | L2Op::Darw => unreachable!(),
                }
            }
        }
        Ok(())
    }

    pub fn apply(&mut self, w: BlockWrites) {
        for (b, a, v, _, _) in w.l1bm {
            self.l1bm[b][a] = v;
        }
        for (b, a, v) in w.l2bm {
            self.l2bm[b][a] = v;
        }
    }
}

/// The identity element replicated over a long word.
fn unit_long(rrn: Rrn) -> u64 {
    let bits = rrn.bits();
    let u = rrn::unit_value(rrn);
    (0..64 / bits).fold(0u64, |acc, i| acc | (u << (i * bits)))
}

/// Reduces long words lane by lane in one stage (L2BM reductions).
fn reduce_longs(rrn: Rrn, vals: &[u64]) -> u64 {
    let bits = rrn.bits();
    let m = if bits == 64 { u64::MAX } else { (1u64 << bits) - 1 };
    let out_fmt = rrn::fmt_of(rrn.prec);
    let mut out = 0u64;
    for lane in 0..64 / bits {
        let sh = 64 - bits * (lane + 1);
        let lanes: Vec<u64> = vals.iter().map(|v| (v >> sh) & m).collect();
        out |= (rrn::reduce(rrn, &lanes, out_fmt) & m) << sh;
    }
    out
}

/// Reduces the PE buses of one L1BM reduction lane over MABs (16x1: two stages of four).
///
/// Half-precision float reductions are single-precision reductions with input extension and
/// output rounding (SDM 3.6.8.5: `l1bmrhfadd` is an alias of `l1bmrffaddr` with `e` inputs).
/// With extension, the 4 halves of each PE's MSB long word become 4 singles (two long words).
/// Returns the reduced two long words; with rounding, each single lane holds a half.
fn reduce_buses(rrn: Rrn, round: bool, ext: bool, two: bool, vals: &[Bus], sixteen: bool) -> Result<Bus, ExecError> {
    let half_alias = rrn.prec == 'h' && rrn.op == RrnOp::Fadd;
    let ext = ext || half_alias;
    let round = round || half_alias;
    let rrn = if half_alias { Rrn { prec: 'f', ..rrn } } else { rrn };
    let vals: Vec<Bus> = if ext { vals.iter().map(extend_halves).collect() } else { vals.to_vec() };
    let two = two || ext;
    let bits = rrn.bits();
    let m = if bits == 64 { u64::MAX } else { (1u64 << bits) - 1 };
    let longs = if two { 2 } else { 1 };
    let in_fmt = rrn::fmt_of(rrn.prec);
    let out_fmt = if round { HALF } else { in_fmt };
    let mut out = [0u32; 4];
    for k in 0..longs {
        let mut res = 0u64;
        for lane in 0..64 / bits {
            let sh = 64 - bits * (lane + 1);
            let lanes: Vec<u64> = vals.iter().map(|b| (long(b, k) >> sh) & m).collect();
            let r = if sixteen {
                let arr: [u64; 16] = lanes.try_into().unwrap();
                // The first stage rounds to single precision even when the output is half.
                rrn::reduce16(rrn, &arr, in_fmt, out_fmt)
            } else {
                rrn::reduce(rrn, &lanes, out_fmt)
            };
            // Rounded results are halves; keep them in the lane's low bits for round_layout.
            res |= (r & m) << sh;
        }
        let hl = hi_lo(res);
        out[2 * k] = hl[0];
        out[2 * k + 1] = hl[1];
    }
    Ok(out)
}

/// Precision extension of an L1BM reduction input: the 4 halves of the MSB long word become
/// 4 singles in two long words, in the same order.
fn extend_halves(b: &Bus) -> Bus {
    let msb = long(b, 0);
    let s: Vec<u64> = (0..4)
        .map(|j| float::encode(SINGLE, float::decode(HALF, (msb >> (48 - 16 * j)) & 0xffff)))
        .collect();
    bus_of((s[0] << 32) | s[1], (s[2] << 32) | s[3])
}
