//! Prints PE expressions the current GPU descriptors reject, grouped by opcode.

use std::collections::BTreeMap;

use mncore_sim::gpu::{
    alu_line_from_expr, bfn_line_from_expr, l1_read_line_from_expr, l1_write_line_from_expr,
    l2_line_from_expr, l2_reduce_line_from_expr, mat_mau_line_from_expr, mat_read_line_from_expr,
    mat_write_line_from_expr, mau_line_from_expr,
};
use mncore_sim::machine::MaskState;
use mncore_sim::vsm::{self, Line, Op};

fn main() {
    let path = std::env::args()
        .nth(1)
        .unwrap_or_else(|| "benchmarks/mnist_train_step.vsm".to_string());
    let source = std::fs::read_to_string(&path).expect("read");
    let program = vsm::parse(&source).expect("parse");
    let mut mask = MaskState::default();
    let mut by_op: BTreeMap<String, (usize, Vec<String>)> = BTreeMap::new();
    let mut pe_lines = 0usize;
    let mut unsupported_lines = 0usize;
    let mut empty_lines = 0usize;
    for (_, line) in &program {
        let mut any_bad = false;
        match line {
            Line::MaskDirective { wl, targets, entry } => {
                mask = MaskState { wl: *wl, targets: *targets, entry: *entry };
            }
            Line::Pe(exprs) => {
                pe_lines += 1;
                if exprs.is_empty() {
                    empty_lines += 1;
                }
                for expr in exprs {
                    let ok = alu_line_from_expr(expr).is_some()
                        || bfn_line_from_expr(expr).is_some()
                        || l1_read_line_from_expr(expr).is_some()
                        || l1_write_line_from_expr(expr).is_some()
                        || l2_line_from_expr(expr).is_some()
                        || l2_reduce_line_from_expr(expr).is_some()
                        || mat_mau_line_from_expr(expr, mask).is_some()
                        || mat_read_line_from_expr(expr, mask).is_some()
                        || mat_write_line_from_expr(expr).is_some()
                        || mau_line_from_expr(expr, mask).is_some();
                    if !ok {
                        any_bad = true;
                        let opcode = expr.text.split_whitespace().next().unwrap_or("?").to_string();
                        let entry = by_op.entry(opcode).or_default();
                        entry.0 += 1;
                        if entry.1.len() < 3 {
                            entry.1.push(expr.text.clone());
                        }
                    }
                }
            }
            _ => {}
        }
        if any_bad {
            unsupported_lines += 1;
        }
    }
    println!("PE lines: {pe_lines}, unsupported lines: {unsupported_lines}, empty: {empty_lines}");
    for (op, (count, samples)) in by_op {
        println!("{op}: {count}");
        for sample in samples {
            println!("  {sample}");
        }
    }
}
