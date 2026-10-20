//! Runs the fx_export MNIST train step repeatedly on the GPU.
//!
//! The VSM updates the four parameter tensors in place at their input DRAM
//! addresses, so a captured CUDA graph can run many SGD steps as long as each
//! step's input and target are copied into DRAM first.
//!
//! Usage: gpu_train [data-dir] [--epochs N] [--steps N]

use std::fs;

use mncore_sim::blocks::{L1BM_LONGS, L1BS, L2BM_LONGS, L2BS};
use mncore_sim::gpu::{
    alu_line_from_expr, bfn_line_from_expr_state, l1_read_line_from_expr, l1_write_line_from_expr,
    l2_line_from_expr, l2_reduce_line_from_expr, mat_mau_line_from_expr,
    mat_read_line_from_expr, mat_write_line_from_expr, mau_line_from_expr, mv_line_from_mv, Gpu,
    MAT_WORDS,
};
use mncore_sim::machine::{MaskState, GRF_WORDS, LM_WORDS, PES};
use mncore_sim::vsm::{self, Line, Op};

const DRAM_LONGS: u64 = 264064;
const GROUPS: usize = 4;
const INPUT_LONGS: usize = 32768; // 256 x 1024 floats, two per long word
const TARGET_LONGS: usize = 32; // 256 floats
const INPUT_ADDR: u64 = 0;
const TARGET_ADDR: u64 = 40000;

fn reads_fwd(e: &mncore_sim::vsm::Expr, kind: mncore_sim::vsm::FwdKind) -> bool {
    e.srcs
        .iter()
        .any(|o| matches!(o, mncore_sim::vsm::Operand::Forward { kind: k, .. } if *k == kind))
}

fn is_lbi_write(e: &mncore_sim::vsm::Expr) -> bool {
    matches!(e.op, Op::L1(_))
        && e.dsts
            .iter()
            .any(|d| matches!(d, mncore_sim::vsm::Operand::L1bm { addr: None, .. }))
}

fn is_lbi_read(e: &mncore_sim::vsm::Expr) -> bool {
    matches!(e.op, Op::L1(_))
        && e.srcs
            .iter()
            .any(|d| matches!(d, mncore_sim::vsm::Operand::L1bm { addr: None, .. }))
}

fn same_fwd(a: Option<usize>, b: Option<usize>) -> bool {
    a.is_some() && a == b
}

fn order_step<'a>(exprs: &'a [mncore_sim::vsm::Expr]) -> Vec<&'a mncore_sim::vsm::Expr> {
    let n = exprs.len();
    let mut edge = vec![vec![false; n]; n];
    let writes: Vec<Option<usize>> = exprs.iter().map(fwd_written_by).collect();
    for i in 0..n {
        for k in [
            mncore_sim::vsm::FwdKind::Mauf,
            mncore_sim::vsm::FwdKind::Aluf,
            mncore_sim::vsm::FwdKind::Mreadf,
            mncore_sim::vsm::FwdKind::Lbf,
        ] {
            if reads_fwd(&exprs[i], k) {
                for j in 0..n {
                    if i != j && same_fwd(writes[j], fwd_written_by_kind(k)) {
                        edge[i][j] = true;
                    }
                }
            }
        }
        if is_lbi_read(&exprs[i]) {
            for j in 0..n {
                if i != j && is_lbi_write(&exprs[j]) {
                    edge[i][j] = true;
                }
            }
        }
    }
    let mut used = vec![false; n];
    let mut out = Vec::with_capacity(n);
    for _ in 0..n {
        let pick = (0..n).find(|&i| !used[i] && (0..n).all(|j| j == i || used[j] || !edge[j][i]));
        let pick = match pick {
            Some(p) => p,
            None => break,
        };
        used[pick] = true;
        out.push(&exprs[pick]);
    }
    for (i, e) in exprs.iter().enumerate() {
        if !used[i] {
            out.push(e);
        }
    }
    out
}

fn fwd_written_by_kind(kind: mncore_sim::vsm::FwdKind) -> Option<usize> {
    Some(match kind {
        mncore_sim::vsm::FwdKind::Mauf => 0,
        mncore_sim::vsm::FwdKind::Aluf => 1,
        mncore_sim::vsm::FwdKind::Mreadf => 2,
        mncore_sim::vsm::FwdKind::Lbf => 3,
    })
}

fn fwd_written_by(expr: &mncore_sim::vsm::Expr) -> Option<usize> {
    match &expr.op {
        Op::Mau { .. } => Some(0),
        Op::Alu { .. } | Op::Imm { .. } | Op::Zero => Some(1),
        Op::MatRead { .. } => Some(2),
        Op::L1(_) if matches!(expr.srcs.first(), Some(mncore_sim::vsm::Operand::L1bm { .. })) => {
            Some(3)
        }
        _ => None,
    }
}

fn run_program(gpu: &Gpu, state: &mncore_sim::gpu::GpuState, program: &[(usize, Line)]) {
    let mut mask = MaskState::default();
    let mut fwd_enabled = [false; 4];
    for (lineno, line) in program {
        match line {
            Line::Nop { .. } => {}
            Line::MaskDirective { wl, targets, entry } => {
                mask = MaskState {
                    wl: *wl,
                    targets: *targets,
                    entry: *entry,
                };
            }
            Line::Mv(mv) => {
                let desc = mv_line_from_mv(mv).expect("MV descriptor");
                gpu.run_mv_line(state, &desc).expect("mv");
            }
            Line::Pe(exprs) => {
                if let Err(error) = mncore_sim::issue::check(exprs) {
                    panic!("line {lineno}: {error}");
                }
                let wait = exprs.iter().any(|e| matches!(e.op, Op::Wait(_)));
                if wait && exprs.len() < 2 {
                    panic!("line {lineno}: wait without another PE expression");
                }
                if exprs.iter().any(|e| matches!(e.op, Op::Wait(0))) {
                    panic!("line {lineno}: wait tag 0 is invalid");
                }
                let update_forward = !exprs.iter().any(|e| matches!(e.op, Op::Noforward));
                let has_mread = exprs.iter().any(|e| matches!(e.op, Op::MatRead { .. }));
                for expr in exprs {
                    for src in &expr.srcs {
                        if let mncore_sim::vsm::Operand::Forward { kind, .. } = src {
                            let index = match kind {
                                mncore_sim::vsm::FwdKind::Mauf => 0,
                                mncore_sim::vsm::FwdKind::Aluf => 1,
                                mncore_sim::vsm::FwdKind::Mreadf => 2,
                                mncore_sim::vsm::FwdKind::Lbf => 3,
                            };
                            if !fwd_enabled[index] {
                                panic!("line {lineno}: forwarding register {kind:?} is not enabled");
                            }
                        }
                    }
                }
                let mut fwd_written = [false; 4];
                let ordered = order_step(exprs);
                for expr in ordered {
                    if matches!(expr.op, Op::Noforward | Op::Wait(_)) {
                        continue;
                    }
                    if update_forward {
                        if let Some(index) = fwd_written_by(expr) {
                            fwd_written[index] = true;
                        }
                    }
                    if let Some(line) = alu_line_from_expr(expr, mask) {
                        gpu.run_alu_line_with(state, &line, update_forward)
                            .expect("alu");
                    } else if let Some(line) = bfn_line_from_expr_state(expr, mask) {
                        gpu.run_bfn_line_with(state, &line, update_forward)
                            .expect("bfn");
                    } else if let Some(line) = l1_read_line_from_expr(expr, mask) {
                        gpu.run_l1_read_line(state, &line).expect("l1 read");
                    } else if let Some(line) = l1_write_line_from_expr(expr) {
                        gpu.run_l1_write_line_with(state, &line, update_forward)
                            .expect("l1 write");
                    } else if let Some(line) = l2_line_from_expr(expr) {
                        gpu.run_l2_line(state, &line).expect("l2");
                    } else if let Some(line) = l2_reduce_line_from_expr(expr) {
                        gpu.run_l2_reduce_line(state, &line).expect("l2 red");
                    } else if let Some(line) = mat_write_line_from_expr(expr) {
                        gpu.run_mat_write_line(state, &line).expect("mat write");
                    } else if let Some(line) = mat_read_line_from_expr(expr, mask) {
                        gpu.run_mat_read_line_with(state, &line, update_forward)
                            .expect("mat read");
                    } else if let Some(line) = mat_mau_line_from_expr(expr, mask) {
                        gpu.run_mat_mau_line_with(state, &line, update_forward)
                            .expect("mat mau");
                    } else if let Some(line) = mau_line_from_expr(expr, mask) {
                        gpu.run_mau_line_with(state, &line, update_forward)
                            .expect("mau");
                    } else {
                        panic!("line {lineno}: no GPU descriptor for {:?}", expr.text);
                    }
                }
                fwd_enabled = if update_forward { fwd_written } else { [false; 4] };
                if update_forward && !has_mread {
                    gpu.clear_mreadf(state).expect("clear mreadf");
                }
            }
            other => panic!("line {lineno}: unsupported line {other:?}"),
        }
    }
}

fn read_u64(path: &str) -> Vec<u64> {
    let bytes = fs::read(path).unwrap_or_else(|e| panic!("read {path}: {e}"));
    bytes
        .chunks_exact(8)
        .map(|c| u64::from_le_bytes(c.try_into().unwrap()))
        .collect()
}

fn main() {
    let mut args = std::env::args().skip(1);
    let dir = args
        .next()
        .unwrap_or_else(|| "research/experiments/mnist-gpu".to_string());
    let mut epochs = 100usize;
    let mut steps_limit: Option<usize> = None;
    let mut once = false;
    let mut reset_mats = true;
    let mut program_path = "viz/core/benchmarks/mnist_train_step.vsm".to_string();
    let mut init_path = format!("{dir}/init_dram.bin");
    let mut out_path = format!("{dir}/final_dram.bin");
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--epochs" => epochs = args.next().unwrap().parse().unwrap(),
            "--steps" => steps_limit = Some(args.next().unwrap().parse().unwrap()),
            "--once" => once = true,
            "--no-reset-mats" => reset_mats = false,
            "--program" => program_path = args.next().unwrap(),
            "--init" => init_path = args.next().unwrap(),
            "--out" => out_path = args.next().unwrap(),
            _ => panic!("unknown argument {arg}"),
        }
    }

    let source = fs::read_to_string(&program_path).expect("vsm");
    let program = vsm::parse(&source).expect("parse");

    let init = read_u64(&init_path);
    let train_inputs = if once { Vec::new() } else { read_u64(&format!("{dir}/train_inputs.bin")) };
    let train_targets = if once { Vec::new() } else { read_u64(&format!("{dir}/train_targets.bin")) };
    let train_batches = train_inputs.len() / (GROUPS * INPUT_LONGS);
    let orders = {
        if once { Vec::new() } else {
        let bytes = fs::read(format!("{dir}/epoch_orders.bin")).unwrap();
        bytes
            .chunks_exact(4)
            .map(|c| i32::from_le_bytes(c.try_into().unwrap()) as usize)
            .collect::<Vec<_>>()
        }
    };
    assert_eq!(train_targets.len(), train_batches * GROUPS * TARGET_LONGS);
    eprintln!(
        "{} batches, {} epochs, {} steps max",
        train_batches,
        epochs,
        steps_limit.unwrap_or(usize::MAX)
    );

    let gpu = Gpu::new().expect("gpu");
    let state = gpu
        .allocate_state_with_mv(DRAM_LONGS, 1)
        .expect("allocate");
    gpu.upload_state(
        &state,
        &vec![0u32; PES * LM_WORDS],
        &vec![0u32; PES * LM_WORDS],
        &vec![0u32; PES * GRF_WORDS],
        &vec![0u32; PES * GRF_WORDS],
    )
    .expect("state");
    gpu.upload_mats(&state, &vec![0u32; MAT_WORDS]).expect("mats");
    gpu.upload_l1bm(&state, &vec![0u64; L1BS * L1BM_LONGS]).expect("l1");
    gpu.upload_l2bm(&state, &vec![0u64; L2BS * L2BM_LONGS]).expect("l2");
    let pdm = vec![0u64; (mncore_sim::mv::GROUPS as u64 * mncore_sim::mv::PDM_LONGS) as usize];
    gpu.upload_pdm(&state, &pdm).expect("pdm");
    assert_eq!(init.len(), GROUPS * DRAM_LONGS as usize);
    gpu.upload_dram(&state, &init).expect("dram");

    if once {
        gpu.sync().expect("sync");
        run_program(&gpu, &state, &program);
        gpu.sync().expect("sync");
        let final_dram = gpu.download_dram(&state).expect("download dram");
        let bytes: Vec<u8> = final_dram.iter().flat_map(|w| w.to_le_bytes()).collect();
        fs::write(&out_path, bytes).expect("write dram");
        return;
    }

    gpu.sync().expect("sync before capture");
    gpu.begin_capture().expect("begin capture");
    run_program(&gpu, &state, &program);
    let graph = gpu.end_capture().expect("end capture");
    let exec = gpu.instantiate_graph(graph).expect("instantiate");

    let upload = |gpu: &Gpu, state: &mncore_sim::gpu::GpuState, group: usize, addr: u64, words: &[u64]| {
        gpu.upload_dram_at(state, group, addr, words).expect("upload");
    };

    let zero_mats = vec![0u32; MAT_WORDS];
    let mut step = 0usize;
    let start = std::time::Instant::now();
    'outer: for epoch in 0..epochs {
        let epoch_start = std::time::Instant::now();
        for i in 0..train_batches {
            let b = if epoch == 0 {
                i
            } else {
                orders[epoch * train_batches + i]
            };
            for g in 0..GROUPS {
                let base = (b * GROUPS + g) * INPUT_LONGS;
                upload(&gpu, &state, g, INPUT_ADDR, &train_inputs[base..base + INPUT_LONGS]);
                let tbase = (b * GROUPS + g) * TARGET_LONGS;
                upload(&gpu, &state, g, TARGET_ADDR, &train_targets[tbase..tbase + TARGET_LONGS]);
            }
            if reset_mats {
                gpu.upload_mats(&state, &zero_mats).expect("reset mats");
            }
            gpu.launch_graph(exec).expect("launch");
            gpu.sync().expect("sync");
            step += 1;
            if let Some(limit) = steps_limit {
                if step >= limit {
                    break 'outer;
                }
            }
        }
        eprintln!(
            "epoch {:3}: {:?} ({} steps total)",
            epoch + 1,
            epoch_start.elapsed(),
            step
        );
    }
    eprintln!(
        "{} steps in {:?} ({:?} per step)",
        step,
        start.elapsed(),
        start.elapsed() / step.max(1) as u32
    );

    let final_dram = gpu.download_dram(&state).expect("download dram");
    let bytes: Vec<u8> = final_dram.iter().flat_map(|w| w.to_le_bytes()).collect();
    fs::write(&out_path, bytes).expect("write final dram");
    gpu.destroy_graph(exec, graph);
}
