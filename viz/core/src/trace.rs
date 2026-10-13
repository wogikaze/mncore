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
}

/// Collects accesses of focus units during a step.
#[derive(Default)]
pub struct Tracer {
    pub focus_pe: Vec<bool>,
    pub focus_l1b: Vec<bool>,
    pub expr: u16,
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
        Tracer { focus_pe, focus_l1b, expr: 0, accesses: Vec::new() }
    }

    #[allow(clippy::too_many_arguments)]
    pub fn pe(&mut self, pe: usize, cycle: usize, loc: &'static str, write: bool, addr: Option<u32>, words: &[u32]) {
        if self.focus_pe[pe] {
            self.accesses.push(Access { expr: self.expr, unit: pe as u32, cycle: cycle as u8, loc, write, addr, words: words.to_vec() });
        }
    }

    pub fn l1bm(&mut self, l1b: usize, cycle: usize, write: bool, addr: u32, v: u64) {
        if self.focus_l1b[l1b] {
            let words = vec![(v >> 32) as u32, v as u32];
            self.accesses.push(Access { expr: self.expr, unit: l1b as u32, cycle: cycle as u8, loc: "l1bm", write, addr: Some(addr), words });
        }
    }

    pub fn mat(&mut self, mab: usize, cycle: usize, side: usize, row: usize, words: &[u32]) {
        if self.focus_pe[mab * 4] {
            let loc = if side == 0 { "matx" } else { "maty" };
            self.accesses.push(Access { expr: self.expr, unit: mab as u32, cycle: cycle as u8, loc, write: true, addr: Some(row as u32), words: words.to_vec() });
        }
    }

    pub fn take(&mut self) -> Vec<Access> {
        std::mem::take(&mut self.accesses)
    }
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
                    Op::Alu { .. } | Op::Imm { .. } | Op::Zero => out.push(Flow { from: "pe", to: "alu", longs: PES * 4 * 2, kind: "compute" }),
                    Op::Mau { matrix, .. } => {
                        let kind = if *matrix { "matrix" } else { "mau" };
                        out.push(Flow { from: "pe", to: kind, longs: PES * 4 * 2, kind: "compute" })
                    }
                    Op::MatWrite { .. } => out.push(Flow { from: "pe", to: "matrix", longs: PES * 4, kind: "copy" }),
                    Op::MatRead { .. } => out.push(Flow { from: "matrix", to: "pe", longs: PES * 4, kind: "copy" }),
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
                        out.push(Flow { from, to, longs, kind });
                    }
                    Op::L2(op) => {
                        let set = |s: crate::blockop::L1bSet| s.mask.count_ones() as u64;
                        let (from, to, kind, longs) = match op {
                            L2Op::Bcast { set: s } => ("l2bm", "l1bm", "broadcast", L2BS * set(*s) * 64),
                            L2Op::Bcast2 { set: s } => ("l2bm", "l1bm", "broadcast", L2BS * set(*s) * 64),
                            L2Op::Distrib { set: s } => ("l2bm", "l1bm", "distribute", L2BS * set(*s) * 32),
                            L2Op::FromL1b { .. } => ("l1bm", "l2bm", "copy", L2BS * 64),
                            L2Op::Reduce { set: s, .. } => ("l1bm", "l2bm", "reduce", L2BS * set(*s) * 64),
                            L2Op::Reduce2 { .. } => ("l1bm", "l2bm", "reduce", L2BS * 8 * 64),
                            L2Op::Gather => ("l1bm", "l2bm", "gather", L2BS * 8 * 32),
                            L2Op::Imcast { set: s } => ("l1bm", "l1bm", "multicast", L2BS * set(*s) * 64),
                            L2Op::Dars | L2Op::Darw => continue,
                        };
                        out.push(Flow { from, to, longs, kind });
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
            out.push(Flow { from: level(mv.src), to: level(mv.dst), longs, kind });
        }
        _ => {}
    }
    out
}
