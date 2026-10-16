//! Conditions for issuing several PE expressions in one step (SDM 3.6.4).
//!
//! The assembler rejects a line that breaks any of these, so a program that breaks them never
//! runs on the emulator. The machine model itself would execute such a line without trouble,
//! which is why they are checked separately here.

use crate::blockop::L2Op;
use crate::vsm::{Addr, Expr, MaskSource, MemKind, Op, Operand, Prec};

/// Issue group of an expression (table 3.6), or `None` for expressions not simulated.
pub fn group(e: &Expr) -> Option<&'static str> {
    let turnaround = e.srcs.iter().chain(&e.dsts).any(|o| matches!(o, Operand::L1bm { addr: None, .. }));
    Some(match &e.op {
        Op::Alu { .. } | Op::Imm { .. } | Op::Zero => "alu",
        Op::Mau { .. } => "mau-calc",
        Op::MatWrite { .. } => "mau-mwrite",
        Op::MatRead { .. } => "mau-mread",
        Op::L1(_) if turnaround => "l1bm-turnaround",
        Op::L1(_) => "l1bm",
        Op::L2(L2Op::Darw) => "l2bmdarw",
        Op::L2(_) => "l2bm",
        Op::Wait(_) => "wait",
        Op::Noforward => "noforward",
        Op::Other(_) => return None,
    })
}

fn mem_name(m: MemKind) -> &'static str {
    match m {
        MemKind::Grf0 => "GRF0",
        MemKind::Grf1 => "GRF1",
        MemKind::Lm0 => "LM0",
        MemKind::Lm1 => "LM1",
        MemKind::T => "the T register",
        _ => "a PE memory",
    }
}

/// Region of a PE memory read or written by an operand, compared for equality.
#[derive(Clone, Copy, PartialEq, Eq)]
struct Region {
    wl: u8,
    addr: Addr,
}

fn prec_of(e: &Expr) -> Option<Prec> {
    match e.op {
        Op::Mau { prec, .. } | Op::MatWrite { prec } | Op::MatRead { prec } => Some(prec),
        _ => None,
    }
}

fn mask_applications_agree(exprs: &[Expr]) -> bool {
    // Mask selectors read the mask-register file. Keep those reads on one
    // width and, for variable selectors, one OMR entry across the issue line.
    let mut width = None;
    let mut entry = None;
    for expression in exprs {
        for mask in expression.flush.into_iter().chain(
            expression.srcs.iter().chain(&expression.dsts).filter_map(|operand| match operand {
                Operand::Mem { mask, .. } | Operand::Bar { mask, .. } |
                Operand::Omr { mask, .. } => *mask,
                _ => None,
            }),
        ) {
            if let Some(previous) = width {
                if previous != mask.ll {
                    return false;
                }
            } else {
                width = Some(mask.ll);
            }
            if let MaskSource::Entry(current) = mask.source {
                if let Some(previous) = entry {
                    if previous != current {
                        return false;
                    }
                } else {
                    entry = Some(current);
                }
            }
        }
    }
    true
}

/// Checks a line of PE expressions against SDM 3.6.4. Returns the first violation found.
pub fn check(exprs: &[Expr]) -> Result<(), String> {
    // One expression per group.
    let mut seen: Vec<(&str, &Expr)> = Vec::new();
    for e in exprs {
        let Some(g) = group(e) else { continue };
        if let Some((_, first)) = seen.iter().find(|(s, _)| *s == g) {
            return Err(format!("`{}` and `{}` are both in the {g} group", first.text, e.text));
        }
        seen.push((g, e));
    }

    // At most two of the three MAU groups, with the same precision.
    let mau: Vec<&Expr> = exprs.iter().filter(|e| matches!(e.op, Op::Mau { .. } | Op::MatWrite { .. } | Op::MatRead { .. })).collect();
    if mau.len() > 2 {
        return Err("mau-calc, mau-mwrite and mau-mread are all issued in one step (at most two)".into());
    }
    if let [a, b] = mau[..] {
        if prec_of(a) != prec_of(b) {
            return Err(format!("`{}` and `{}` have different precisions", a.text, b.text));
        }
        // vfma/vmul with mwrite: the second input of the former is the input of the latter.
        let (v, w) = if matches!(a.op, Op::MatWrite { .. }) { (b, a) } else { (a, b) };
        if matches!(v.op, Op::Mau { matrix: false, kind: crate::vsm::MauKind::Fma | crate::vsm::MauKind::Mul, .. })
            && matches!(w.op, Op::MatWrite { .. })
            && v.srcs.get(1) != w.srcs.first()
        {
            return Err(format!("`{}` must read its second input from the same operand as `{}`", v.text, w.text));
        }
    }

    // Each matrix register side appears at most once.
    for y in [false, true] {
        let n = exprs.iter().flat_map(|e| e.srcs.iter().chain(&e.dsts)).filter(|o| matches!(o, Operand::Mat { y: s, .. } if *s == y)).count();
        if n > 1 {
            return Err(format!("the matrix register ${} appears {n} times (at most once per step)", if y { "y" } else { "x" }));
        }
    }

    // PE memories: one writer per memory, one read region per memory, and for LM0/LM1 a read
    // and a write in the same step must access the same region.
    let mut writes: Vec<(MemKind, Region, &Expr)> = Vec::new();
    let mut reads: Vec<(MemKind, Region, &Expr)> = Vec::new();
    for e in exprs {
        for (ops, list) in [(&e.srcs, &mut reads), (&e.dsts, &mut writes)] {
            for o in ops {
                if let Operand::Mem { mem, wl, addr, .. } = o {
                    list.push((*mem, Region { wl: *wl, addr: *addr }, e));
                }
            }
        }
    }
    for e in exprs {
        if e.dsts.iter().any(|operand| matches!(operand, Operand::Nowrite)) && e.dsts.len() != 1 {
            return Err(format!("`{}` uses $nowrite with another destination", e.text));
        }
    }
    for (i, (m, _, e)) in writes.iter().enumerate() {
        if let Some((_, _, f)) = writes[..i].iter().find(|(n, _, _)| n == m) {
            return Err(format!("`{}` and `{}` both write {}", f.text, e.text, mem_name(*m)));
        }
    }
    // The mask register file exposes one write port per issue step. This
    // includes writes made by otherwise distinct issue groups.
    let mask_writes = exprs.iter().flat_map(|e| e.dsts.iter())
        .filter(|operand| matches!(operand, Operand::Omr { .. }))
        .count();
    if mask_writes > 1 {
        return Err("multiple expressions write mask registers in one step".into());
    }
    // Every L1BM-to-PE expression updates the shared $lbf forwarding operand.
    // The normal and turnaround L1BM groups are distinct, so group uniqueness
    // alone does not prevent two such writes.
    let lbf_writes = exprs.iter().filter(|e| {
        matches!(e.op, Op::L1(_))
            && e.srcs.iter().any(|operand| matches!(operand, Operand::L1bm { .. }))
    }).count();
    if lbf_writes > 1 {
        return Err("multiple expressions write the L1BM forwarding register in one step".into());
    }
    for (i, (m, r, e)) in reads.iter().enumerate() {
        if let Some((_, _, f)) = reads[..i].iter().find(|(n, s, _)| n == m && s != r) {
            return Err(format!("{} is read at two different addresses (`{}` and `{}`)", mem_name(*m), f.text, e.text));
        }
    }
    for (m, r, e) in &reads {
        if !matches!(m, MemKind::Lm0 | MemKind::Lm1) {
            continue;
        }
        if let Some((_, _, f)) = writes.iter().find(|(n, s, _)| n == m && s != r) {
            return Err(format!("{} is read and written at different addresses in one step (`{}` and `{}`)", mem_name(*m), e.text, f.text));
        }
    }

    // imm does not go with an access to LM0.
    if let Some(imm) = exprs.iter().find(|e| matches!(e.op, Op::Imm { .. })) {
        if reads.iter().chain(&writes).any(|(m, _, _)| *m == MemKind::Lm0) {
            return Err(format!("LM0 is accessed in the same step as `{}`", imm.text));
        }
    }

    // At most one zero-flush mask.
    if exprs.iter().filter(|e| e.flush.is_some()).count() > 1 {
        return Err("zero-flush masks are applied more than once in one step".into());
    }
    // Single-row mask applications in one step must use one width and, when
    // multiple variable entries are read, one entry. This also covers a
    // zero-flush mask combined with a write mask.
    if !mask_applications_agree(exprs) {
        return Err("mask applications use conflicting widths or entries".into());
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::check;
    use crate::vsm::{parse, Line};

    fn issue(src: &str) -> Result<(), String> {
        let lines = parse(src).unwrap();
        let Line::Pe(exprs) = &lines[0].1 else { panic!("not a PE line") };
        check(exprs)
    }

    // Each case was checked against assemble3 --instruction-mode flat.
    #[test]
    fn matches_the_assembler() {
        for ok in [
            "gmwrite $lr0v $lx0;gmfma $ly $ls0v $lr0v $ln0v",
            "gmfma $ly $ls0v $lr0v $lr8v",
            "gmwrite $ln0v $lx0;gmfma $ly $ls0v $lr0v $lm8v",
            "gmfma $ly $ls[0,2,4,6] $lr[8,10,12,14] $lr[16,18,20,22]",
            "gbfn $ls0v $lr0v;gmwrite $lr8v $lx0",
            "gmwrite $aluf $ly0;gmread $lx4 $nowrite",
            "lpassa $lm0v $lr0v/$imr1; l1bmm $lb0 $ls0v/$imr1",
            "gmfma $ly $ls0v $lr0v $ln0v $omr1",
            "lpassa $lt $omr1",
            "zero $nowrite",
            "lpassa $lm0v $lr0v/$imr1; gmfma $ly $ls0v $lr0v $ln0v $omr1",
            "lpassa $lm0v $lr0v/$imr1; gmfma $ly $ls0v $lr0v $ln0v $omr2",
            "l1bmm $lb0 $lr0v",
        ] {
            assert_eq!(issue(ok), Ok(()), "{ok}");
        }
        for bad in [
            "gmfma $ly $ls0v $ls8v $ls16v",
            "gmwrite $lr0v $lx0;gmfma $ly $ls0v $lr8v $ln0v",
            "gmfma $ly $ls0v $ln0v $ln8v",
            "gmread $lx0 $lr0v;gmwrite $lr8v $lx4",
            "gbfn $ls0v $lr0v;gmmul $ly $ls0v $lr8v",
            "lpassa $lm0v $lr0v/$imr1; l1bmm $lb0 $ls0v/$llimr1",
            "lpassa $lm0v $lr0v/$imr1; l1bmm $lb0 $ls0v/$imr2",
            "lpassa/$imr1 $lm0v $lr0v/$imr2",
            "gmfma $ly $ls0v $lr0v $ln0v $omr1; lpassa $lt $omr1",
            "gmfma $ly $ls0v $lr0v $ln0v $omr1; lpassa $lt $omr2",
            "l1bmm $lb0 $lr8v; l1bmm $lbi $lm0v",
            "zero $lm0 $lm2",
            "zero $nowrite $omr1",
            "zero $nowrite $nowrite",
        ] {
            assert!(issue(bad).is_err(), "{bad}");
        }
    }
}
