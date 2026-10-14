//! Static hazard analysis (SDM 3.6.3).
//!
//! Every statement occupies one step of 4 cycles (`nop/<n>` occupies n). For each step this
//! module lists which memory locations are read and written in which cycle, and checks the
//! hazard rules between steps. It explains why a nop is needed (which write and which read it
//! separates, and whether the reason is a data race or a port conflict), and finds nops that
//! no rule needs.

use crate::blockop::{L1Op, L2Op};
use crate::blocks::l1_operand;
use crate::mv::{MvKind, MvOperand};
use crate::vsm::{Expr, Line, MaskSource, MemKind, Op, Operand};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Res {
    Grf0,
    Grf1,
    T,
    Lm0,
    Lm1,
    /// L1BM of the L1B with this number in each L2B.
    L1bm(u8),
    /// L2BM of the L2B with this number in each group.
    L2bm(u8),
}

/// How an L1BM or L2BM access is made, which decides the hazard rules that apply.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Path {
    /// PE instruction reading or writing PE memory.
    Pe,
    /// L1BM instruction: L1BM to PE.
    L1ToPe,
    /// L1BM instruction: PE to L1BM.
    PeToL1,
    /// L2BM instruction: L2BM to L1BM.
    L2ToL1,
    /// L2BM instruction: L1BM to L2BM.
    L1ToL2,
    /// L2BM instruction: L1BM internal multicast.
    Multicast,
    /// MV instruction.
    Mv,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Access {
    pub write: bool,
    pub res: Res,
    pub path: Path,
    /// Word address for PE memories, long word address for L1BM/L2BM. `None` when unknown
    /// statically (T indirect) or when the whole memory is meant.
    pub addr: Option<u32>,
    /// Number of consecutive addresses.
    pub len: u32,
    /// Cycle within the step (0 to 3).
    pub cycle: u8,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Kind {
    /// The read must not see the location before the write completes (same address only).
    DataRace,
    /// The memory port is busy (any address).
    PortConflict,
}

/// A rule of SDM 3.6.3 that applies between a write and a later access.
#[derive(Clone, Debug, PartialEq)]
pub struct Constraint {
    /// Section of the SDM, such as "3.6.3.9".
    pub rule: &'static str,
    pub kind: Kind,
    pub res: Res,
    pub addr: Option<u32>,
    /// Index of the writing and of the reading line.
    pub from_line: usize,
    pub to_line: usize,
    /// Cycles from the write to the read (absolute cycle of the read minus that of the write).
    pub distance: u32,
    /// Smallest allowed distance.
    pub required: u32,
}

impl Constraint {
    pub fn violated(&self) -> bool {
        self.distance < self.required
    }
    /// How many cycles could be removed before the rule is violated.
    pub fn slack(&self) -> i64 {
        self.distance as i64 - self.required as i64
    }
}

fn pe_res(m: MemKind) -> Option<Res> {
    Some(match m {
        MemKind::Grf0 => Res::Grf0,
        MemKind::Grf1 => Res::Grf1,
        MemKind::T => Res::T,
        MemKind::Lm0 => Res::Lm0,
        MemKind::Lm1 => Res::Lm1,
        _ => return None,
    })
}

/// Cycles in which a destination is written, from a fixed single-line mask pattern.
fn written_cycles(op: &Operand) -> [bool; 4] {
    match op {
        Operand::Mem { mask: Some(sel), .. } => match sel.source {
            MaskSource::Pattern(p) => p,
            MaskSource::Entry(_) => [true; 4],
        },
        _ => [true; 4],
    }
}

fn pe_operand_accesses(op: &Operand, write: bool, out: &mut Vec<Access>) {
    let Operand::Mem { mem, wl, addr, .. } = op else { return };
    let Some(res) = pe_res(*mem) else { return };
    let cycles = if write { written_cycles(op) } else { [true; 4] };
    for c in 0..4 {
        if !cycles[c] {
            continue;
        }
        let (a, len) = if *mem == MemKind::T {
            // T has a region per cycle: use the cycle as the address.
            (Some(c as u32), 1)
        } else if addr.t_indirect {
            (None, *wl as u32)
        } else {
            (Some(addr.cycles[c]), *wl as u32)
        };
        out.push(Access { write, res, path: Path::Pe, addr: a, len, cycle: c as u8 });
        // T indirect addressing reads the T register's entry for the cycle (SDM 3.6.1.6).
        if addr.t_indirect && !write {
            out.push(Access { write: false, res: Res::T, path: Path::Pe, addr: Some(c as u32), len: 1, cycle: c as u8 });
        }
    }
}

/// L1BM long words accessed in each cycle by an L1BM expression: (offset, length) relative to
/// the operand address. Mirrors the layouts in `blocks.rs`.
fn l1_cycle_span(op: L1Op, two: bool, rounded: bool, ext: bool) -> (u32, u32) {
    match op {
        L1Op::Pbcast => (1, if two { 5 } else { 1 }),
        L1Op::Mbcast | L1Op::Mwrite { .. } => if two { (8, 8) } else { (4, 4) },
        L1Op::Reduce { .. } if rounded => (4, 4),
        L1Op::Reduce4 { .. } if rounded => (16, 16),
        L1Op::Reduce { .. } if ext => (8, 8),
        L1Op::Reduce4 { .. } if ext => (32, 32),
        L1Op::Reduce { .. } => if two { (8, 8) } else { (4, 4) },
        L1Op::M4bcast | L1Op::M4write { .. } | L1Op::Reduce4 { .. } => if two { (32, 32) } else { (16, 16) },
        L1Op::Distrib { .. } | L1Op::Gather { .. } => (64, 64),
    }
}

/// Lists the accesses of one line.
pub fn accesses(line: &Line) -> Vec<Access> {
    let mut out = Vec::new();
    match line {
        Line::Pe(exprs) => {
            for e in exprs {
                expr_accesses(e, &mut out);
            }
        }
        Line::Mv(mv) => {
            // The assembler treats an MV instruction as accessing its whole L2BM region in the
            // cycle it is issued (SDM 3.6.3.1).
            for (op, write) in [(mv.src, false), (mv.dst, true)] {
                if let Some(MvOperand::L2bm { addr, l2b, .. }) = op {
                    let len = match mv.kind {
                        MvKind::Nop => 0,
                        _ => mv.size as u32,
                    };
                    for c in 0..2u8 {
                        if l2b.is_none_or(|x| x == c) {
                            out.push(Access { write, res: Res::L2bm(c), path: Path::Mv, addr: Some(addr as u32), len, cycle: 0 });
                        }
                    }
                }
            }
        }
        _ => {}
    }
    out
}

fn expr_accesses(e: &Expr, out: &mut Vec<Access>) {
    match &e.op {
        Op::L1(op) => {
            let to_pe = matches!(e.srcs.first(), Some(Operand::L1bm { .. }));
            let (block_op, pe_ops, write_block) = if to_pe { (&e.srcs[0], &e.dsts[..], false) } else { (&e.dsts[0], &e.srcs[..], true) };
            for p in pe_ops {
                pe_operand_accesses(p, !write_block, out);
            }
            let Some((wl, Some(addr))) = l1_operand(block_op) else { return };
            let ext = matches!(e.srcs.first(), Some(Operand::Mem { ext: true, .. }));
            let rounded = matches!(op, L1Op::Reduce { round: true, .. } | L1Op::Reduce4 { round: true, .. })
                || matches!(op, L1Op::Reduce { rrn, .. } | L1Op::Reduce4 { rrn, .. } if rrn.prec == 'h' && rrn.op == crate::blockop::RrnOp::Fadd);
            let (step, len) = l1_cycle_span(*op, wl == 4, rounded, ext);
            let path = if write_block { Path::PeToL1 } else { Path::L1ToPe };
            for b in 0..8 {
                for c in 0..4u32 {
                    out.push(Access { write: write_block, res: Res::L1bm(b), path, addr: Some((addr + c * step) % 8192), len, cycle: c as u8 });
                }
            }
        }
        Op::L2(op) => {
            let addr = |o: Option<&Operand>| match o {
                Some(Operand::L1bm { addr: Some(a), .. }) => *a,
                Some(Operand::L2bm { addr, .. }) => *addr,
                _ => 0,
            };
            let (a0, a1) = (addr(e.srcs.first()), addr(e.dsts.first()));
            let mut l1 = |write: bool, set: u8, base: u32, step: u32, len: u32, path: Path| {
                for b in (0..8u8).filter(|b| (set >> b) & 1 == 1) {
                    for c in 0..4u32 {
                        out.push(Access { write, res: Res::L1bm(b), path, addr: Some((base + c * step) % 8192), len, cycle: c as u8 });
                    }
                }
            };
            let mut l2: Vec<Access> = Vec::new();
            let mut l2acc = |write: bool, base: u32, step: u32, path: Path| {
                for c in 0..2u8 {
                    for cy in 0..4u32 {
                        l2.push(Access { write, res: Res::L2bm(c), path, addr: Some((base + cy * step) % 32768), len: step, cycle: cy as u8 });
                    }
                }
            };
            match op {
                L2Op::Bcast { set } => {
                    l1(true, set.mask, a1, 16, 16, Path::L2ToL1);
                    l2acc(false, a0, 16, Path::L2ToL1);
                }
                L2Op::Bcast2 { set } => {
                    l1(true, set.mask, a1, 16, 16, Path::L2ToL1);
                    l2acc(false, a0, 64, Path::L2ToL1);
                }
                L2Op::Distrib { set } => {
                    l1(true, set.mask, a1, 8, 8, Path::L2ToL1);
                    l2acc(false, a0, 64, Path::L2ToL1);
                }
                L2Op::FromL1b { l1b } => {
                    l1(false, 1 << l1b, a0, 16, 16, Path::L1ToL2);
                    l2acc(true, a1, 16, Path::L1ToL2);
                }
                L2Op::Reduce { set, .. } => {
                    l1(false, set.mask, a0, 16, 16, Path::L1ToL2);
                    l2acc(true, a1, 16, Path::L1ToL2);
                }
                L2Op::Reduce2 { .. } => {
                    l1(false, 0xff, a0, 16, 16, Path::L1ToL2);
                    l2acc(true, a1, 64, Path::L1ToL2);
                }
                L2Op::Gather => {
                    l1(false, 0xff, a0, 8, 8, Path::L1ToL2);
                    l2acc(true, a1, 64, Path::L1ToL2);
                }
                L2Op::Imcast { set } => {
                    l1(false, set.mask, a0, 16, 16, Path::Multicast);
                    // Written: every L1B that shares the immode bits with a source, except it.
                    let mut wmask = 0u8;
                    for s in (0..8u8).filter(|b| (set.mask >> b) & 1 == 1) {
                        for d in (0..8u8).filter(|&d| d != s && d & set.immode == s & set.immode) {
                            wmask |= 1 << d;
                        }
                    }
                    l1(true, wmask, a1, 16, 16, Path::Multicast);
                }
                L2Op::Dars | L2Op::Darw => {}
            }
            out.extend(l2);
        }
        _ => {
            for s in &e.srcs {
                pe_operand_accesses(s, false, out);
            }
            for d in &e.dsts {
                pe_operand_accesses(d, true, out);
            }
        }
    }
}

fn overlaps(a: &Access, b: &Access) -> bool {
    match (a.addr, b.addr) {
        (Some(x), Some(y)) => x < y + b.len && y < x + a.len,
        _ => true,
    }
}

/// The rule between an earlier write `w` and a later access `r`, if any:
/// (section, kind, required distance in cycles from the write's cycle to the read's cycle).
fn rule(w: &Access, r: &Access) -> Option<(&'static str, Kind, RuleDist)> {
    use Path::*;
    match (w.path, r.path, w.res, r.write) {
        // 3.6.3.9: PE memories.
        (_, _, Res::Lm0 | Res::Lm1, false) if pe_side(w) && pe_side(r) => Some(("3.6.3.9", Kind::PortConflict, RuleDist::Steps(3))),
        (_, _, Res::Grf0 | Res::Grf1 | Res::T, false) if pe_side(w) && pe_side(r) => Some(("3.6.3.9", Kind::DataRace, RuleDist::Cycles(7))),
        (L1ToL2, Mv, Res::L2bm(_), false) => Some(("3.6.3.1", Kind::DataRace, RuleDist::Steps(2))),
        (L1ToL2, L2ToL1, Res::L2bm(_), false) => Some(("3.6.3.2", Kind::PortConflict, RuleDist::Steps(4))),
        (L2ToL1, L1ToL2 | Multicast, Res::L1bm(_), false) => Some(("3.6.3.3", Kind::PortConflict, RuleDist::Steps(3))),
        (Multicast, L1ToL2 | Multicast, Res::L1bm(_), false) => Some(("3.6.3.4", Kind::PortConflict, RuleDist::Steps(4))),
        (Multicast, L1ToPe, Res::L1bm(_), false) => Some(("3.6.3.5", Kind::DataRace, RuleDist::Cycles(11))),
        (L2ToL1, L1ToPe, Res::L1bm(_), false) => Some(("3.6.3.6", Kind::DataRace, RuleDist::Cycles(7))),
        (PeToL1, L1ToL2 | Multicast, Res::L1bm(_), false) => Some(("3.6.3.7", Kind::DataRace, RuleDist::Cycles(11))),
        (PeToL1, L1ToPe, Res::L1bm(_), false) => Some(("3.6.3.8", Kind::PortConflict, RuleDist::Steps(3))),
        _ => None,
    }
}

fn pe_side(a: &Access) -> bool {
    matches!(a.res, Res::Grf0 | Res::Grf1 | Res::T | Res::Lm0 | Res::Lm1)
}

#[derive(Clone, Copy, Debug)]
enum RuleDist {
    /// The later access must start this many steps after the write's step (a gap of n-1 steps).
    Steps(u32),
    /// The access cycle must be at least this many cycles after the write cycle.
    Cycles(u32),
}

/// Checks all hazard rules of a program. Returns the constraints between writes and later
/// accesses that are within the look-back window (all rules span at most 4 steps).
pub fn analyze(lines: &[(usize, Line)]) -> Vec<Constraint> {
    // Step index of each line.
    let mut steps = Vec::with_capacity(lines.len());
    let mut s = 0u32;
    for (_, l) in lines {
        steps.push(s);
        s += l.words();
    }
    let acc: Vec<Vec<Access>> = lines.iter().map(|(_, l)| accesses(l)).collect();
    let mut out = Vec::new();
    for j in 0..lines.len() {
        if acc[j].is_empty() {
            continue;
        }
        // Look back over earlier lines within 4 steps.
        let mut i = j;
        while i > 0 {
            i -= 1;
            if steps[j] - steps[i] > 4 {
                break;
            }
            for w in acc[i].iter().filter(|a| a.write) {
                for r in &acc[j] {
                    if r.res != w.res {
                        continue;
                    }
                    let Some((sec, kind, dist)) = rule(w, r) else { continue };
                    if kind == Kind::DataRace && !overlaps(w, r) {
                        continue;
                    }
                    let (distance, required) = match dist {
                        RuleDist::Steps(n) => ((steps[j] - steps[i]) * 4, n * 4),
                        RuleDist::Cycles(n) => ((steps[j] * 4 + r.cycle as u32) - (steps[i] * 4 + w.cycle as u32), n),
                    };
                    out.push(Constraint {
                        rule: sec,
                        kind,
                        res: r.res,
                        addr: r.addr,
                        from_line: i,
                        to_line: j,
                        distance,
                        required,
                    });
                }
            }
        }
    }
    // Keep the tightest constraint per (rule, lines, resource).
    out.sort_by_key(|c| (c.from_line, c.to_line, c.rule, c.slack()));
    out.dedup_by(|b, a| a.from_line == b.from_line && a.to_line == b.to_line && a.rule == b.rule && a.res == b.res);
    out
}

/// Why a nop step is needed: the constraints that would be violated if one step of the nop
/// line were removed. An empty list means the step can be removed.
pub fn nop_reasons(lines: &[(usize, Line)], constraints: &[Constraint]) -> Vec<(usize, Vec<Constraint>)> {
    let mut out = Vec::new();
    for (k, (_, l)) in lines.iter().enumerate() {
        if !matches!(l, Line::Nop { .. }) {
            continue;
        }
        let binding: Vec<Constraint> = constraints
            .iter()
            .filter(|c| c.from_line < k && k < c.to_line && c.slack() < 4)
            .cloned()
            .collect();
        out.push((k, binding));
    }
    out
}
