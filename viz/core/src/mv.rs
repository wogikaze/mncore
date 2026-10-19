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
    ///
    /// DRAM indirect mode (SDM 3.5.6) walks the transfer in 16-long-word chunks,
    /// independently of the basic mode. Chunk `i` uses DAR entry
    /// `(M + i / N) % 1024` and the long-word address `16 * (DAR[entry] + i % N)`;
    /// without `nd` (`N` infinite) it uses `DAR[(M + i) % 1024]` and offset 0.
    /// With no `nd` the address word is selected by `M + i` exactly as in SDM
    /// 3.5.6. The measured official emulator uses 16 long words per address word
    /// (the SDM text's "6 long words" is inconsistent with its own example and
    /// with the emulator).
    pub fn exec(&mut self, b: &mut Blocks, mv: &Mv) -> Result<(), ExecError> {
        let (Some(src), Some(dst)) = (mv.src, mv.dst) else { return Ok(()) };
        let unsupported = || ExecError::Unsupported(format!("MV instruction `{}`", mv.text));
        if mv.nd == Some(0) {
            return Err(ExecError::Unsupported(format!("nd0 in `{}`", mv.text)));
        }
        // Reads are done before writes, so overlapping source and destination behave like a copy.
        let mut writes: Vec<(Loc, u64)> = Vec::new();
        let n = mv.size / 64;
        let nd = mv.nd.map(|n| n as u64);
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
        // One 16-long-word DRAM chunk in the order the transfer walks the DRAM side.
        let dram = |o: MvOperand, g: usize, chunk: u64, k: u64| -> Loc {
            let MvOperand::Dram { addr, indirect, .. } = o else {
                unreachable!("dram() called for a non-DRAM operand")
            };
            if !indirect {
                return Loc::Dram(g, addr + 16 * chunk + k);
            }
            let (entry, off) = match nd {
                Some(n) => ((addr + chunk / n) % crate::blocks::DAR_ENTRIES as u64, chunk % n),
                None => ((addr + chunk) % crate::blocks::DAR_ENTRIES as u64, 0),
            };
            let word = (b.dar[g][entry as usize] as u64 + off) & 0xffff_ffff;
            Loc::Dram(g, (word.wrapping_mul(16) + k) % DRAM_LONGS)
        };
        let is_dram = |o: MvOperand| matches!(o, MvOperand::Dram { .. });
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
                        let (chunk, kk) = (k / 16, k % 16);
                        let value = if is_dram(src) {
                            self.read(b, dram(src, gs, chunk, kk))
                        } else {
                            self.read(b, at(src, gs, cs, k))
                        };
                        let loc = if is_dram(dst) {
                            dram(dst, gd, chunk, kk)
                        } else {
                            at(dst, gd, cd, k)
                        };
                        writes.push((loc, value));
                    }
                }
            }
            MvKind::B2 => {
                // DRAM -> both L2BMs of every group.
                for g in 0..GROUPS {
                    for k in 0..n * 64 {
                        let value = self.read(b, dram(src, g, k / 16, k % 16));
                        for c in 0..2 {
                            writes.push((at(dst, g, c, k), value));
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
                Dram { .. } => {
                    for i in 0..n {
                        for gd in 0..GROUPS {
                            for k in 0..16 {
                                let v = self.read(b, dram(src, gd, 4 * i + gd as u64, k));
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
                let Dram { .. } = src else { return Err(unsupported()) };
                for i in 0..n {
                    for c in 0..2 {
                        for gs in 0..GROUPS {
                            for k in 0..16 {
                                let v = self.read(b, dram(src, gs, 2 * i + c as u64, k));
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
                                writes.push((dram(dst, g, 4 * i + g as u64, k), v));
                            }
                        }
                    }
                }
                (Dram { .. }, Pdm { .. }) => {
                    let gp = groups(dst)[0];
                    for i in 0..n {
                        for g in 0..GROUPS {
                            for k in 0..16 {
                                let v = self.read(b, dram(src, g, 4 * i + g as u64, k));
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
                        let loc = if is_dram(dst) {
                            dram(dst, g, k / 16, k % 16)
                        } else {
                            at(dst, g, 0, k)
                        };
                        writes.push((loc, reduce_long(op, &vals)));
                    }
                }
            }
            MvKind::R(op) => {
                // All 8 L2BMs: 2-element reduction within each group, then 4 across groups.
                let reduced = |b: &Blocks, off: u64| -> u64 {
                    let per_group: Vec<u64> = (0..GROUPS)
                        .map(|g| reduce_long(op, &[self.read(b, at(src, g, 0, off)), self.read(b, at(src, g, 1, off))]))
                        .collect();
                    reduce_long(op, &per_group)
                };
                match dst {
                    Pdm { .. } => {
                        let gp = groups(dst)[0];
                        for k in 0..n * 64 {
                            writes.push((at(dst, gp, 0, k), reduced(b, k)));
                        }
                    }
                    Dram { .. } => {
                        for i in 0..n {
                            for g in 0..GROUPS {
                                for k in 0..16 {
                                    writes.push((
                                        dram(dst, g, 4 * i + g as u64, k),
                                        reduced(b, 64 * i + g as u64 * 16 + k),
                                    ));
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
                                writes.push((dram(dst, g, 2 * i + c as u64, k), reduce_long(op, &vals)));
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
    fn dram_indirect_chunks() {
        let mut b = Blocks::default();
        let mut off = OffChip::default();
        b.dar[0][0] = 100;
        b.dar[0][1] = 1;
        b.dar[0][2] = 200;
        b.dar[0][3] = 2;
        for i in 0..128 {
            off.pdm[0].set(i, 0x1000 + i);
        }
        // nd4: chunks 0..3 use DAR[0] + i, so addresses 1600, 1616, 1632, 1648.
        let mv = parse("mvp/n128nd4 $p0@0 $di0@0").unwrap();
        off.exec(&mut b, &mv).unwrap();
        for chunk in 0..8u64 {
            let entry = (chunk / 4) as usize;
            let off_in_entry = chunk % 4;
            let addr = 16 * (b.dar[0][entry] as u64 + off_in_entry);
            for k in 0..16 {
                assert_eq!(
                    off.dram[0].get(addr + k),
                    0x1000 + chunk * 16 + k,
                    "chunk {chunk} at {addr} + {k}"
                );
            }
        }
        // Without nd each chunk uses the next DAR entry.
        let mut b = Blocks::default();
        let mut off = OffChip::default();
        b.dar[1][5] = 7;
        b.dar[1][6] = 9;
        for i in 0..128 {
            off.pdm[1].set(i, 0x2000 + i);
        }
        let mv = parse("mvp/n128 $p0@1 $di5@1").unwrap();
        off.exec(&mut b, &mv).unwrap();
        assert_eq!(off.dram[1].get(16 * 7), 0x2000);
        assert_eq!(off.dram[1].get(16 * 9), 0x2010);
    }

    #[test]
    fn l2_dar() {
        let mut sim = crate::run::Sim::new();
        sim.m.blocks.l2bm[0][0] = 0x1234_5678_9abc_def0;
        sim.m.blocks.l2bm[2][0] = 0x1111_2222_3333_4444;
        let lines = crate::vsm::parse("l2bmdars $lc0@.0 $dar2;l2bmdarw").unwrap();
        sim.run(&lines).unwrap();
        assert_eq!(sim.m.blocks.dar[0][2], 0x1234_5678);
        assert_eq!(sim.m.blocks.dar[0][3], 0x9abc_def0);
        assert_eq!(sim.m.blocks.dar[1][2], 0x1111_2222);
        assert_eq!(sim.m.blocks.dar[1][3], 0x3333_4444);
        assert_eq!(sim.m.blocks.darw_addr, 6);
        assert_eq!(sim.m.blocks.darbuf_read_addr, 4);
    }

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
