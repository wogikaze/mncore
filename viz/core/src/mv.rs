//! MV instructions: transfers among PDM, DRAM and L2BM (SDM 3.5).
//!
//! The emulator completes an MV instruction as soon as it is issued, and so does this
//! simulator. How long a transfer takes is not static (SDM 3.6.13); the visualization estimates
//! it from the throughputs in SDM 3.5.8.

use std::collections::HashMap;

use crate::blockop::Rrn;
use crate::blocks::{Blocks, L2BM_LONGS};
use crate::machine::ExecError;
use crate::rrn;

pub const GROUPS: usize = 4;
pub const PDM_LONGS: u64 = 512 * 1024;
pub const DRAM_LONGS: u64 = 512 * 1024 * 1024;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MvKind {
    /// `mvp`: individual transfer (single or parallel).
    P,
    /// `mvb`: broadcast between groups.
    B,
    /// `mvb2`: broadcast within a group.
    B2,
    /// `mvb4`: distribution-broadcast between groups.
    B4,
    /// `mvd`: distribution or gathering.
    D,
    /// `mvr<op>`: reduction between groups.
    R(Rrn),
    /// `mvr2<op>`: reduction within a group.
    R2(Rrn),
    /// `mvr4<op>`: gathering reduction between groups.
    R4(Rrn),
    Nop,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MvOperand {
    Pdm { addr: u64, group: Option<u8> },
    Dram { addr: u64, group: Option<u8>, indirect: bool },
    L2bm { addr: u64, group: Option<u8>, l2b: Option<u8> },
}

#[derive(Clone, Debug, PartialEq)]
pub struct Mv {
    pub kind: MvKind,
    /// Number of long words (counted on the L2BM side, or the PDM side for PDM-DRAM).
    pub size: u64,
    pub tag: Option<u8>,
    /// DAR entry reuse count of DRAM indirect access (`nd<N>`).
    pub nd: Option<u32>,
    pub priority: u8,
    pub src: Option<MvOperand>,
    pub dst: Option<MvOperand>,
    pub text: String,
}

fn parse_num(s: &str) -> Option<u64> {
    if let Some(h) = s.strip_prefix("0x") {
        u64::from_str_radix(h, 16).ok()
    } else {
        s.parse().ok()
    }
}

fn take_num(s: &str) -> Option<(u64, &str)> {
    let end = if s.starts_with("0x") {
        2 + s[2..].find(|c: char| !c.is_ascii_hexdigit()).unwrap_or(s.len() - 2)
    } else {
        s.find(|c: char| !c.is_ascii_digit()).unwrap_or(s.len())
    };
    if end == 0 {
        return None;
    }
    Some((parse_num(&s[..end])?, &s[end..]))
}

pub fn parse(text: &str) -> Result<Mv, String> {
    let mut it = text.split_whitespace();
    let opcode = it.next().ok_or("empty MV statement")?;
    let ops: Vec<&str> = it.collect();
    let bad = || format!("bad MV statement `{text}`");
    if opcode == "mvnop" {
        return Ok(Mv { kind: MvKind::Nop, size: 0, tag: None, nd: None, priority: 0, src: None, dst: None, text: text.into() });
    }
    let (mode, params) = opcode.split_once('/').ok_or_else(bad)?;
    let mode = mode.strip_prefix("mv").ok_or_else(bad)?;
    let kind = match mode {
        "p" => MvKind::P,
        "b" => MvKind::B,
        "b2" => MvKind::B2,
        "b4" => MvKind::B4,
        "d" => MvKind::D,
        _ => {
            let (r, rest) = if let Some(r) = mode.strip_prefix("r2") {
                (r, 2)
            } else if let Some(r) = mode.strip_prefix("r4") {
                (r, 4)
            } else if let Some(r) = mode.strip_prefix('r') {
                (r, 1)
            } else {
                return Err(bad());
            };
            let (rrn, tail) = Rrn::parse_prefix(r).ok_or_else(bad)?;
            if !tail.is_empty() {
                return Err(bad());
            }
            match rest {
                2 => MvKind::R2(rrn),
                4 => MvKind::R4(rrn),
                _ => MvKind::R(rrn),
            }
        }
    };
    let (mut size, mut tag, mut nd, mut priority) = (None, None, None, 0);
    let mut p = params;
    while !p.is_empty() {
        if let Some(r) = p.strip_prefix("nd") {
            let (n, r) = take_num(r).ok_or_else(bad)?;
            nd = Some(n as u32);
            p = r;
        } else if let Some(r) = p.strip_prefix('n') {
            let (n, r) = take_num(r).ok_or_else(bad)?;
            size = Some(n);
            p = r;
        } else if let Some(r) = p.strip_prefix('i') {
            if r.len() < 2 {
                return Err(bad());
            }
            tag = Some(u8::from_str_radix(&r[..2], 16).map_err(|_| bad())?);
            p = &r[2..];
        } else if let Some(r) = p.strip_prefix('p') {
            let (n, r) = take_num(r).ok_or_else(bad)?;
            priority = n as u8;
            p = r;
        } else {
            return Err(bad());
        }
    }
    let size = size.ok_or_else(|| format!("MV statement without size `{text}`"))?;
    if ops.len() != 2 {
        return Err(bad());
    }
    let src = parse_operand(ops[0]).ok_or_else(bad)?;
    let dst = parse_operand(ops[1]).ok_or_else(bad)?;
    Ok(Mv { kind, size, tag, nd, priority, src: Some(src), dst: Some(dst), text: text.into() })
}

fn parse_operand(s: &str) -> Option<MvOperand> {
    let s = s.strip_prefix('$')?;
    if let Some(r) = s.strip_prefix("lc") {
        let (addr, r) = take_num(r)?;
        let (group, l2b) = match r.strip_prefix('@') {
            None if r.is_empty() => (None, None),
            None => return None,
            Some(g) => {
                let (g, l) = g.split_once('.').unwrap_or((g, ""));
                let group = if g.is_empty() { None } else { Some(g.parse().ok()?) };
                let l2b = if l.is_empty() { None } else { Some(l.parse().ok()?) };
                (group, l2b)
            }
        };
        return Some(MvOperand::L2bm { addr, group, l2b });
    }
    let (kind, r) = if let Some(r) = s.strip_prefix("di") {
        ('i', r)
    } else if let Some(r) = s.strip_prefix('d') {
        ('d', r)
    } else if let Some(r) = s.strip_prefix('p') {
        ('p', r)
    } else {
        return None;
    };
    let (addr, r) = take_num(r)?;
    let group = match r.strip_prefix('@') {
        Some(g) => Some(g.parse().ok()?),
        None if r.is_empty() => None,
        None => return None,
    };
    Some(match kind {
        'p' => MvOperand::Pdm { addr, group },
        _ => MvOperand::Dram { addr, group, indirect: kind == 'i' },
    })
}

/// Paged sparse memory of long words; unwritten memory reads as zero (the judge runs the
/// emulator with `--offchip-memory-init zero`).
#[derive(Default)]
pub struct Sparse {
    pages: HashMap<u64, Box<[u64; 4096]>>,
}

impl Sparse {
    pub fn get(&self, a: u64) -> u64 {
        self.pages.get(&(a >> 12)).map(|p| p[(a & 4095) as usize]).unwrap_or(0)
    }
    pub fn set(&mut self, a: u64, v: u64) {
        self.pages.entry(a >> 12).or_insert_with(|| Box::new([0; 4096]))[(a & 4095) as usize] = v;
    }
}

/// PDM and DRAM of the four groups.
#[derive(Default)]
pub struct OffChip {
    pub pdm: [Sparse; GROUPS],
    pub dram: [Sparse; GROUPS],
}

/// A location of one long word at the top level.
#[derive(Clone, Copy, Debug)]
enum Loc {
    Pdm(usize, u64),
    Dram(usize, u64),
    L2bm(usize, usize, u64),
}

impl OffChip {
    fn read(&self, b: &Blocks, l: Loc) -> u64 {
        match l {
            Loc::Pdm(g, a) => self.pdm[g].get(a % PDM_LONGS),
            Loc::Dram(g, a) => self.dram[g].get(a % DRAM_LONGS),
            Loc::L2bm(g, c, a) => b.l2bm[g * 2 + c][(a % L2BM_LONGS as u64) as usize],
        }
    }

    /// Executes an MV instruction.
    pub fn exec(&mut self, b: &mut Blocks, mv: &Mv) -> Result<(), ExecError> {
        let (Some(src), Some(dst)) = (mv.src, mv.dst) else { return Ok(()) };
        let unsupported = || ExecError::Unsupported(format!("MV instruction `{}`", mv.text));
        if matches!(src, MvOperand::Dram { indirect: true, .. }) || matches!(dst, MvOperand::Dram { indirect: true, .. }) {
            return Err(ExecError::Unsupported(format!("DRAM indirect access in `{}`", mv.text)));
        }
        // Reads are done before writes, so overlapping source and destination behave like a copy.
        let mut writes: Vec<(Loc, u64)> = Vec::new();
        let n = mv.size / 64;
        let groups = |o: MvOperand| -> Vec<usize> {
            let g = match o {
                MvOperand::Pdm { group, .. } | MvOperand::Dram { group, .. } | MvOperand::L2bm { group, .. } => group,
            };
            match g {
                Some(g) => vec![g as usize],
                None => (0..GROUPS).collect(),
            }
        };
        let at = |o: MvOperand, g: usize, c: usize, off: u64| -> Loc {
            match o {
                MvOperand::Pdm { addr, .. } => Loc::Pdm(g, addr + off),
                MvOperand::Dram { addr, .. } => Loc::Dram(g, addr + off),
                MvOperand::L2bm { addr, .. } => Loc::L2bm(g, c, addr + off),
            }
        };
        let l2b_of = |o: MvOperand| match o {
            MvOperand::L2bm { l2b, .. } => l2b,
            _ => None,
        };
        use MvOperand::*;
        match mv.kind {
            MvKind::Nop => {}
            MvKind::P => {
                // Single transfers name both groups; parallel ones name none and run per group.
                let pairs: Vec<(usize, usize)> = match (groups(src).len(), groups(dst).len()) {
                    (1, 1) => vec![(groups(src)[0], groups(dst)[0])],
                    (4, 4) => (0..GROUPS).map(|g| (g, g)).collect(),
                    _ => return Err(unsupported()),
                };
                let (cs, cd) = (l2b_of(src).unwrap_or(0) as usize, l2b_of(dst).unwrap_or(0) as usize);
                for (gs, gd) in pairs {
                    for k in 0..n * 64 {
                        writes.push((at(dst, gd, cd, k), self.read(b, at(src, gs, cs, k))));
                    }
                }
            }
            MvKind::B2 => {
                // DRAM -> both L2BMs of every group.
                for g in 0..GROUPS {
                    for k in 0..n * 64 {
                        let v = self.read(b, at(src, g, 0, k));
                        for c in 0..2 {
                            writes.push((at(dst, g, c, k), v));
                        }
                    }
                }
            }
            MvKind::B => match src {
                Pdm { .. } => {
                    let gs = groups(src)[0];
                    for k in 0..n * 64 {
                        let v = self.read(b, at(src, gs, 0, k));
                        for g in 0..GROUPS {
                            for c in 0..2 {
                                writes.push((at(dst, g, c, k), v));
                            }
                        }
                    }
                }
                Dram { addr, .. } => {
                    for i in 0..n {
                        for gd in 0..GROUPS {
                            for k in 0..16 {
                                let v = self.read(b, Loc::Dram(gd, addr + 16 * i + k));
                                for g in 0..GROUPS {
                                    for c in 0..2 {
                                        writes.push((at(dst, g, c, 64 * i + gd as u64 * 16 + k), v));
                                    }
                                }
                            }
                        }
                    }
                }
                _ => return Err(unsupported()),
            },
            MvKind::B4 => {
                let Dram { addr, .. } = src else { return Err(unsupported()) };
                for i in 0..n {
                    for c in 0..2 {
                        for gs in 0..GROUPS {
                            for k in 0..16 {
                                let v = self.read(b, Loc::Dram(gs, addr + 32 * i + c as u64 * 16 + k));
                                for g in 0..GROUPS {
                                    writes.push((at(dst, g, c, 64 * i + gs as u64 * 16 + k), v));
                                }
                            }
                        }
                    }
                }
            }
            MvKind::D => match (src, dst) {
                (Pdm { addr, .. }, L2bm { .. }) => {
                    let gp = groups(src)[0];
                    for i in 0..n {
                        for j in 0..4 {
                            for g in 0..GROUPS {
                                for c in 0..2 {
                                    let buf = (j * 8 + g as u64 * 2 + c as u64) * 16;
                                    for k in 0..16 {
                                        let v = self.read(b, Loc::Pdm(gp, addr + 512 * i + buf + k));
                                        writes.push((at(dst, g, c, 64 * i + j * 16 + k), v));
                                    }
                                }
                            }
                        }
                    }
                }
                (L2bm { addr, .. }, Pdm { .. }) => {
                    let gp = groups(dst)[0];
                    for i in 0..n {
                        for j in 0..4 {
                            for g in 0..GROUPS {
                                for c in 0..2 {
                                    let buf = (j * 8 + g as u64 * 2 + c as u64) * 16;
                                    for k in 0..16 {
                                        let v = self.read(b, Loc::L2bm(g, c, addr + 64 * i + j * 16 + k));
                                        writes.push((at(dst, gp, 0, 512 * i + buf + k), v));
                                    }
                                }
                            }
                        }
                    }
                }
                (Pdm { addr, .. }, Dram { .. }) => {
                    let gp = groups(src)[0];
                    for i in 0..n {
                        for g in 0..GROUPS {
                            for k in 0..16 {
                                let v = self.read(b, Loc::Pdm(gp, addr + 64 * i + g as u64 * 16 + k));
                                writes.push((at(dst, g, 0, 16 * i + k), v));
                            }
                        }
                    }
                }
                (Dram { addr, .. }, Pdm { .. }) => {
                    let gp = groups(dst)[0];
                    for i in 0..n {
                        for g in 0..GROUPS {
                            for k in 0..16 {
                                let v = self.read(b, Loc::Dram(g, addr + 16 * i + k));
                                writes.push((at(dst, gp, 0, 64 * i + g as u64 * 16 + k), v));
                            }
                        }
                    }
                }
                _ => return Err(unsupported()),
            },
            MvKind::R2(op) => {
                // Both L2BMs of a group, reduced (2-element RRN), to the same group's DRAM/PDM.
                for g in groups(dst) {
                    for k in 0..n * 64 {
                        let vals = [self.read(b, at(src, g, 0, k)), self.read(b, at(src, g, 1, k))];
                        writes.push((at(dst, g, 0, k), reduce_long(op, &vals)));
                    }
                }
            }
            MvKind::R(op) => {
                // All 8 L2BMs: 2-element reduction within each group, then 4 across groups.
                let reduced = |off: u64| -> u64 {
                    let per_group: Vec<u64> = (0..GROUPS)
                        .map(|g| reduce_long(op, &[self.read(b, at(src, g, 0, off)), self.read(b, at(src, g, 1, off))]))
                        .collect();
                    reduce_long(op, &per_group)
                };
                match dst {
                    Pdm { .. } => {
                        let gp = groups(dst)[0];
                        for k in 0..n * 64 {
                            writes.push((at(dst, gp, 0, k), reduced(k)));
                        }
                    }
                    Dram { .. } => {
                        for i in 0..n {
                            for g in 0..GROUPS {
                                for k in 0..16 {
                                    writes.push((at(dst, g, 0, 16 * i + k), reduced(64 * i + g as u64 * 16 + k)));
                                }
                            }
                        }
                    }
                    _ => return Err(unsupported()),
                }
            }
            MvKind::R4(op) => {
                // For each L2B number, reduce across groups (4-element), then gather to DRAMs.
                for i in 0..n {
                    for c in 0..2 {
                        for g in 0..GROUPS {
                            for k in 0..16 {
                                let off = 64 * i + g as u64 * 16 + k;
                                let vals: Vec<u64> = (0..GROUPS).map(|gs| self.read(b, at(src, gs, c, off))).collect();
                                writes.push((at(dst, g, 0, 32 * i + c as u64 * 16 + k), reduce_long(op, &vals)));
                            }
                        }
                    }
                }
            }
        }
        for (l, v) in writes {
            match l {
                Loc::Pdm(g, a) => self.pdm[g].set(a % PDM_LONGS, v),
                Loc::Dram(g, a) => self.dram[g].set(a % DRAM_LONGS, v),
                Loc::L2bm(g, c, a) => b.l2bm[g * 2 + c][(a % L2BM_LONGS as u64) as usize] = v,
            }
        }
        Ok(())
    }
}

/// Reduces long words lane by lane in one RRN stage.
fn reduce_long(op: Rrn, vals: &[u64]) -> u64 {
    let bits = op.bits();
    let m = if bits == 64 { u64::MAX } else { (1u64 << bits) - 1 };
    let out_fmt = rrn::fmt_of(op.prec);
    let mut out = 0u64;
    for lane in 0..64 / bits {
        let sh = 64 - bits * (lane + 1);
        let lanes: Vec<u64> = vals.iter().map(|v| (v >> sh) & m).collect();
        out |= (rrn::reduce(op, &lanes, out_fmt) & m) << sh;
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_mv() {
        let m = parse("mvp/n64i01 $p0@0 $lc0@2.1").unwrap();
        assert_eq!(m.kind, MvKind::P);
        assert_eq!(m.size, 64);
        assert_eq!(m.tag, Some(1));
        assert_eq!(m.dst, Some(MvOperand::L2bm { addr: 0, group: Some(2), l2b: Some(1) }));
        let m = parse("mvp/n256nd4 $p1600@1 $di512@2").unwrap();
        assert_eq!(m.nd, Some(4));
        assert_eq!(m.dst, Some(MvOperand::Dram { addr: 512, group: Some(2), indirect: true }));
        let m = parse("mvrffadd/n8192 $lc0 $p0@0").unwrap();
        assert!(matches!(m.kind, MvKind::R(_)));
        let m = parse("mvp/n0x80 $p0x40@1 $d0x20@2").unwrap();
        assert_eq!(m.size, 128);
        assert_eq!(m.src, Some(MvOperand::Pdm { addr: 64, group: Some(1) }));
        assert_eq!(parse("mvp/n64 $lc0@.1 $d0").unwrap().src, Some(MvOperand::L2bm { addr: 0, group: None, l2b: Some(1) }));
    }
}
