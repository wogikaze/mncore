//! Counts how much of a VSM program the current GPU MAU path can execute.
//!
//! Usage: gpu_coverage [program.vsm]

use mncore_sim::gpu::{
    alu_line_from_expr, bfn_line_from_expr, l1_read_line_from_expr, l1_write_line_from_expr,
    l2_line_from_expr, l2_reduce_line_from_expr, mau_line_from_expr,
};
use mncore_sim::machine::MaskState;
use mncore_sim::vsm::{self, Line, Op};

fn main() {
    let path = std::env::args()
        .nth(1)
        .unwrap_or_else(|| "benchmarks/mnist_train_step.vsm".to_string());
    let source = std::fs::read_to_string(&path).expect("read program");
    let program = vsm::parse(&source).expect("parse");
    let mut lines = 0usize;
    let mut pe_lines = 0usize;
    let mut mau_exprs = 0usize;
    let mut mau_supported = 0usize;
    let mut alu_exprs = 0usize;
    let mut alu_supported = 0usize;
    let mut l1_exprs = 0usize;
    let mut l1_supported = 0usize;
    let mut l2_exprs = 0usize;
    let mut l2_supported = 0usize;
    let mut l2_red_exprs = 0usize;
    let mut l2_red_supported = 0usize;
    let mut single_mau_supported = 0usize;
    let mut supported_lines = 0usize;
    let mut t_indirect = 0usize;
    let mut madpe = 0usize;
    let mut neg = 0usize;
    let mut ext = 0usize;
    let mut rnd = 0usize;
    let mut masked = 0usize;
    let mut wl4 = 0usize;
    let mut other_forward = 0usize;
    let mut mask_state = MaskState::default();
    for (_, line) in &program {
        lines += 1;
        if let Line::MaskDirective { wl, targets, entry } = line {
            mask_state = MaskState {
                wl: *wl,
                targets: *targets,
                entry: *entry,
            };
            continue;
        }
        let Line::Pe(exprs) = line else {
            continue;
        };
        pe_lines += 1;
        let mut all_mau = true;
        let mut all_supported = true;
        for expr in exprs {
            if let Op::L2(op) = &expr.op {
                l2_exprs += 1;
                let transfer = l2_line_from_expr(expr).is_some();
                let reduction = l2_reduce_line_from_expr(expr).is_some();
                if transfer || reduction {
                    l2_supported += 1;
                } else {
                    all_supported = false;
                }
                if matches!(
                    op,
                    mncore_sim::blockop::L2Op::Reduce { .. }
                        | mncore_sim::blockop::L2Op::Reduce2 { .. }
                        | mncore_sim::blockop::L2Op::Imcast { .. }
                ) {
                    l2_red_exprs += 1;
                    if reduction {
                        l2_red_supported += 1;
                    }
                }
            } else if let Op::L1(_) = expr.op {
                l1_exprs += 1;
                if l1_read_line_from_expr(expr).is_some() || l1_write_line_from_expr(expr).is_some() {
                    l1_supported += 1;
                } else {
                    all_supported = false;
                }
            } else if matches!(expr.op, Op::Alu { .. } | Op::Zero | Op::Imm { .. }) {
                alu_exprs += 1;
                if alu_line_from_expr(expr).is_some() || bfn_line_from_expr(expr).is_some() {
                    alu_supported += 1;
                } else {
                    all_supported = false;
                }
            } else {
                all_supported = false;
            }
            if matches!(expr.op, Op::Mau { .. }) {
                mau_exprs += 1;
                for op in expr.srcs.iter().chain(expr.dsts.iter()) {
                    match op {
                        mncore_sim::vsm::Operand::Mem {
                            wl,
                            addr,
                            neg: n,
                            ext: e,
                            rnd: r,
                            mask,
                            ..
                        } => {
                            if addr.t_indirect {
                                t_indirect += 1;
                            }
                            if addr.madpe.is_some() {
                                madpe += 1;
                            }
                            if *n {
                                neg += 1;
                            }
                            if *e {
                                ext += 1;
                            }
                            if *r {
                                rnd += 1;
                            }
                            if mask.is_some() {
                                masked += 1;
                            }
                            if *wl == 4 {
                                wl4 += 1;
                            }
                        }
                        mncore_sim::vsm::Operand::Forward { kind, .. } => {
                            if *kind != mncore_sim::vsm::FwdKind::Mauf {
                                other_forward += 1;
                            }
                        }
                        _ => {}
                    }
                }
                if mau_line_from_expr(expr, mask_state).is_some() {
                    mau_supported += 1;
                } else {
                    all_mau = false;
                }
            } else {
                all_mau = false;
            }
        }
        if all_mau && !exprs.is_empty() {
            single_mau_supported += 1;
        }
        if all_supported && !exprs.is_empty() {
            supported_lines += 1;
        }
    }
    println!("program: {path}");
    println!("lines: {lines}, PE lines: {pe_lines}");
    println!("MAU expressions: {mau_exprs}, supported: {mau_supported}");
    println!("ALU expressions: {alu_exprs}, supported (Passa/Xor/Max/Rsqrt/Bfn): {alu_supported}");
    println!("L1 expressions: {l1_exprs}, supported reads/writes: {l1_supported}");
    println!("L2 expressions: {l2_exprs}, supported transfers/reductions/multicast: {l2_supported}");
    println!("L2 reductions/multicast: {l2_red_exprs}, supported: {l2_red_supported}");
    println!("lines with every expression supported: {supported_lines}");
    println!("lines consisting only of supported MAU expressions: {single_mau_supported}");
    println!(
        "features: t={t_indirect} madpe={madpe} neg={neg} ext={ext} rnd={rnd} mask={masked} wl4={wl4} other_forward={other_forward}"
    );
}
