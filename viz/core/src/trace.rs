//! Records what the visualization shows: per-step reads, results and writes of a few focus PEs,
//! and chip-level transfer volumes of every line.

use serde::Serialize;

use crate::blockop::{L1Op, L2Op};
use crate::mv::{MvKind, MvOperand};
use crate::vsm::{Line, Op, Operand};

/// One memory access or result of a focus PE (or a focus L1B for `l1bm`).
#[derive(Clone, Debug, Serialize)]
pub struct Access {
    /// Index of the expression within its line.
    pub expr: u16,
    /// Global PE index, or L1B index for `l1bm`, or MAB index for the matrix register.
    pub unit: u32,
    pub cycle: u8,
    /// What is accessed: lm0, lm1, grf0, grf1, t, aluf, mauf, mreadf, lbf, omr, bar0, bar1,
    /// matx, maty, l1bm, out (the result of the expression before masking).
    pub loc: &'static str,
    pub write: bool,
    /// Word address (PE memories), long word address (L1BM), physical row (matrix register),
    /// or mask register entry.
    pub addr: Option<u32>,
    /// The words read or written, MSB first.
    pub words: Vec<u32>,
    /// Which operand of the expression: the index among its sources (reads) or destinations
    /// (writes).
    pub slot: Option<u8>,
}

/// Collects accesses of focus units during a step.
#[derive(Default)]
pub struct Tracer {
    pub focus_pe: Vec<bool>,
    pub focus_l1b: Vec<bool>,
    pub expr: u16,
    /// Addresses of the current expression's source operands, to find the slot of a read.
    pub srcs: Vec<usize>,
    /// Destination slot of the write being recorded.
    pub wslot: Option<u8>,
    pub accesses: Vec<Access>,
}

impl Tracer {
    pub fn new(focus: &[usize], pes: usize) -> Tracer {
        let mut focus_pe = vec![false; pes];
        let mut focus_l1b = vec![false; pes / 64];
        for &p in focus {
            focus_pe[p] = true;
            focus_l1b[p / 64] = true;
        }
        Tracer { focus_pe, focus_l1b, expr: 0, srcs: Vec::new(), wslot: None, accesses: Vec::new() }
    }

    pub fn pe(&mut self, pe: usize, cycle: usize, loc: &'static str, write: bool, addr: Option<u32>, words: &[u32]) {
        let slot = if write { self.wslot } else { None };
        self.pe_slot(pe, cycle, loc, write, addr, words, slot);
    }

    /// Records a read of a source operand (identified by its address in memory).
    pub fn pe_read(&mut self, pe: usize, cycle: usize, loc: &'static str, op: usize, addr: Option<u32>, words: &[u32]) {
        let slot = self.srcs.iter().position(|&p| p == op).map(|i| i as u8);
        self.pe_slot(pe, cycle, loc, false, addr, words, slot);
    }

    #[allow(clippy::too_many_arguments)]
    fn pe_slot(&mut self, pe: usize, cycle: usize, loc: &'static str, write: bool, addr: Option<u32>, words: &[u32], slot: Option<u8>) {
        if self.focus_pe[pe] {
            self.accesses.push(Access { expr: self.expr, unit: pe as u32, cycle: cycle as u8, loc, write, addr, words: words.to_vec(), slot });
        }
    }

    pub fn l1bm(&mut self, l1b: usize, cycle: usize, write: bool, addr: u32, v: u64) {
        if self.focus_l1b[l1b] {
            let words = vec![(v >> 32) as u32, v as u32];
            self.accesses.push(Access { expr: self.expr, unit: l1b as u32, cycle: cycle as u8, loc: "l1bm", write, addr: Some(addr), words, slot: None });
        }
    }

    pub fn mat(&mut self, mab: usize, cycle: usize, side: usize, row: usize, words: &[u32]) {
        if self.focus_pe[mab * 4] {
            let loc = if side == 0 { "matx" } else { "maty" };
            self.accesses.push(Access { expr: self.expr, unit: mab as u32, cycle: cycle as u8, loc, write: true, addr: Some(row as u32), words: words.to_vec(), slot: Some(0) });
        }
    }

    pub fn take(&mut self) -> Vec<Access> {
        std::mem::take(&mut self.accesses)
    }
}

/// A region of one kind of memory in a set of units.
#[derive(Clone, Debug, Serialize)]
pub struct Region {
    /// dram, pdm, l2bm, l1bm
    pub mem: &'static str,
    /// Global unit indices: groups for dram/pdm, L2B (group * 2 + l2b) for l2bm, L1B for l1bm.
    pub units: Vec<u32>,
    /// First long word address and number of long words in each unit.
    pub addr: u64,
    pub len: u64,
}

/// Chip-level volume of one transfer or computation of a line.
#[derive(Clone, Debug, Serialize)]
pub struct Flow {
    /// From and to, as level names: dram, pdm, l2bm, l1bm, pe; or "alu", "mau", "matrix" for
    /// computations inside PEs.
    pub from: &'static str,
    pub to: &'static str,
    /// Long words moved (or produced) over the whole chip.
    pub longs: u64,
    /// The kind of transfer: copy, broadcast, distribute, gather, reduce, multicast, compute.
    pub kind: &'static str,
    /// Regions read and written (for transfers that involve L1BM, L2BM, PDM or DRAM).
    pub src: Option<Region>,
    pub dst: Option<Region>,
}

fn region(mem: &'static str, units: Vec<u32>, addr: u64, len: u64) -> Option<Region> {
    Some(Region { mem, units, addr, len })
}

/// Global L1B indices of an L1B set in every L2B.
fn l1b_units(mask: u8) -> Vec<u32> {
    (0..L1BS as u32).filter(|i| (mask >> (i % 8)) & 1 == 1).collect()
}

fn all(n: u64) -> Vec<u32> {
    (0..n as u32).collect()
}

const PES: u64 = 4096;
const L1BS: u64 = 64;
const L2BS: u64 = 8;

/// Chip-level flows of a line, from the instruction alone.
pub fn flows(line: &Line) -> Vec<Flow> {
    let mut out = Vec::new();
    match line {
        Line::Pe(exprs) => {
            for e in exprs {
                match &e.op {
                    Op::Alu { .. } | Op::Imm { .. } | Op::Zero => out.push(Flow { from: "pe", to: "alu", longs: PES * 4 * 2, kind: "compute", src: None, dst: None }),
                    Op::Mau { matrix, .. } => {
                        let kind = if *matrix { "matrix" } else { "mau" };
                        out.push(Flow { from: "pe", to: kind, longs: PES * 4 * 2, kind: "compute", src: None, dst: None })
                    }
                    Op::MatWrite { .. } => out.push(Flow { from: "pe", to: "matrix", longs: PES * 4, kind: "copy", src: None, dst: None }),
                    Op::MatRead { .. } => out.push(Flow { from: "matrix", to: "pe", longs: PES * 4, kind: "copy", src: None, dst: None }),
                    Op::L1(op) => {
                        let two = e.srcs.iter().chain(&e.dsts).any(|o| matches!(o, Operand::L1bm { wl: 4, .. }));
                        let per_pe = if two { 2 } else { 1 } * 4;
                        let (from, to, kind, longs) = match op {
                            L1Op::Pbcast => ("l1bm", "pe", "broadcast", PES * per_pe),
                            L1Op::Mbcast | L1Op::M4bcast => ("l1bm", "pe", "broadcast", PES * per_pe),
                            L1Op::Distrib { .. } => ("l1bm", "pe", "distribute", PES * 4),
                            L1Op::Mwrite { .. } => ("pe", "l1bm", "copy", L1BS * 4 * per_pe),
                            L1Op::M4write { .. } => ("pe", "l1bm", "copy", L1BS * 16 * per_pe),
                            L1Op::Reduce { .. } | L1Op::Reduce4 { .. } => ("pe", "l1bm", "reduce", PES * per_pe),
                            L1Op::Gather { .. } => ("pe", "l1bm", "gather", PES * 4),
                        };
                        // The L1BM region: per-cycle span from the hazard analysis, over 4 cycles.
                        let block = e.srcs.iter().chain(&e.dsts).find_map(|o| match o {
                            Operand::L1bm { addr: Some(a), wl } => Some((*a as u64, *wl)),
                            _ => None,
                        });
                        let r = block.map(|(a, _)| {
                            let span = match op {
                                L1Op::Pbcast => if two { 8 } else { 4 },
                                L1Op::Mbcast | L1Op::Mwrite { .. } | L1Op::Reduce { .. } => 4 * per_pe,
                                L1Op::M4bcast | L1Op::M4write { .. } | L1Op::Reduce4 { .. } => 16 * per_pe,
                                L1Op::Distrib { .. } | L1Op::Gather { .. } => 256,
                            };
                            Region { mem: "l1bm", units: all(L1BS), addr: a, len: span }
                        });
                        let (src, dst) = if from == "l1bm" { (r, None) } else { (None, r) };
                        out.push(Flow { from, to, longs, kind, src, dst });
                    }
                    Op::L2(op) => {
                        let set = |s: crate::blockop::L1bSet| s.mask.count_ones() as u64;
                        let addr = |o: Option<&Operand>| match o {
                            Some(Operand::L1bm { addr: Some(a), .. }) => *a as u64,
                            Some(Operand::L2bm { addr, .. }) => *addr as u64,
                            _ => 0,
                        };
                        let (a0, a1) = (addr(e.srcs.first()), addr(e.dsts.first()));
                        let l2 = |a: u64, len: u64| region("l2bm", all(L2BS), a, len);
                        let l1 = |mask: u8, a: u64, len: u64| region("l1bm", l1b_units(mask), a, len);
                        let (from, to, kind, longs, src, dst) = match op {
                            L2Op::Bcast { set: s } => ("l2bm", "l1bm", "broadcast", L2BS * set(*s) * 64, l2(a0, 64), l1(s.mask, a1, 64)),
                            L2Op::Bcast2 { set: s } => ("l2bm", "l1bm", "broadcast", L2BS * set(*s) * 64, l2(a0, 256), l1(s.mask, a1, 64)),
                            L2Op::Distrib { set: s } => ("l2bm", "l1bm", "distribute", L2BS * set(*s) * 32, l2(a0, 256), l1(s.mask, a1, 32)),
                            L2Op::FromL1b { l1b } => ("l1bm", "l2bm", "copy", L2BS * 64, l1(1 << l1b, a0, 64), l2(a1, 64)),
                            L2Op::Reduce { set: s, .. } => ("l1bm", "l2bm", "reduce", L2BS * set(*s) * 64, l1(s.mask, a0, 64), l2(a1, 64)),
                            L2Op::Reduce2 { .. } => ("l1bm", "l2bm", "reduce", L2BS * 8 * 64, l1(0xff, a0, 64), l2(a1, 256)),
                            L2Op::Gather => ("l1bm", "l2bm", "gather", L2BS * 8 * 32, l1(0xff, a0, 32), l2(a1, 256)),
                            L2Op::Imcast { set: s } => ("l1bm", "l1bm", "multicast", L2BS * set(*s) * 64, l1(s.mask, a0, 64), l1(!s.mask, a1, 64)),
                            L2Op::Dars | L2Op::Darw => continue,
                        };
                        out.push(Flow { from, to, longs, kind, src, dst });
                    }
                    _ => {}
                }
            }
        }
        Line::Mv(mv) => {
            let level = |o: Option<MvOperand>| match o {
                Some(MvOperand::Pdm { .. }) => "pdm",
                Some(MvOperand::Dram { .. }) => "dram",
                Some(MvOperand::L2bm { .. }) => "l2bm",
                None => "",
            };
            let groups = |o: Option<MvOperand>| match o {
                Some(MvOperand::Pdm { group, .. }) | Some(MvOperand::Dram { group, .. }) | Some(MvOperand::L2bm { group, .. }) => {
                    if group.is_some() {
                        1
                    } else {
                        4
                    }
                }
                None => 0,
            };
            let kind = match mv.kind {
                MvKind::P => "copy",
                MvKind::B | MvKind::B2 | MvKind::B4 => "broadcast",
                MvKind::D => "distribute",
                MvKind::R(_) | MvKind::R2(_) | MvKind::R4(_) => "reduce",
                MvKind::Nop => return out,
            };
            let longs = mv.size * groups(mv.src).max(groups(mv.dst)) as u64;
            // Long words each unit reads or writes, per the layouts of SDM 3.5.8.
            let per_unit = |o: MvOperand| -> u64 {
                let lvl = level(Some(o));
                match (mv.kind, lvl) {
                    (MvKind::B, "dram") | (MvKind::R(_), "dram") => mv.size / 4,
                    (MvKind::B4, "dram") | (MvKind::R4(_), "dram") => mv.size / 2,
                    (MvKind::D, "pdm") if level(mv.src) == "l2bm" || level(mv.dst) == "l2bm" => mv.size * 8,
                    (MvKind::D, "dram") => mv.size / 4,
                    _ => mv.size,
                }
            };
            let reg = |o: Option<MvOperand>| -> Option<Region> {
                let o = o?;
                match o {
                    MvOperand::Pdm { addr, group } => region("pdm", group.map(|g| vec![g as u32]).unwrap_or_else(|| all(4)), addr, per_unit(o)),
                    MvOperand::Dram { addr, group, .. } => region("dram", group.map(|g| vec![g as u32]).unwrap_or_else(|| all(4)), addr, per_unit(o)),
                    MvOperand::L2bm { addr, group, l2b } => {
                        let units = (0..8u32).filter(|u| group.is_none_or(|g| g as u32 == u / 2) && l2b.is_none_or(|c| c as u32 == u % 2)).collect();
                        region("l2bm", units, addr, per_unit(o))
                    }
                }
            };
            out.push(Flow { from: level(mv.src), to: level(mv.dst), longs, kind, src: reg(mv.src), dst: reg(mv.dst) });
        }
        _ => {}
    }
    out
}
