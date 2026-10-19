//! Runs a whole VSM program on the GPU and compares the final state with Sim.
//!
//! Usage: gpu_run_program [program.vsm]

use mncore_sim::blocks::{L1BM_LONGS, L1BS, L2BM_LONGS, L2BS};
use mncore_sim::gpu::{
    alu_line_from_expr, bfn_line_from_expr_state, l1_read_line_from_expr, l1_write_line_from_expr,
    l2_line_from_expr, l2_reduce_line_from_expr, mat_mau_line_from_expr,
    mat_read_line_from_expr, mat_write_line_from_expr, mau_line_from_expr, mv_line_from_mv, Gpu,
    MAT_WORDS,
};
use mncore_sim::machine::{MaskState, GRF_WORDS, LM_WORDS, PES};
use mncore_sim::run::Sim;
use mncore_sim::vsm::{self, Line, Op};

fn main() {
    let path = std::env::args()
        .nth(1)
        .unwrap_or_else(|| "benchmarks/mnist_train_step.vsm".to_string());
    let source = std::fs::read_to_string(&path).expect("read");
    let program = vsm::parse(&source).expect("parse");

    let mut mask = MaskState::default();
    let mut dram_longs = 0u64;
    let mut scratch_longs = 1u64;
    let mut indirect = false;
    for (_, line) in &program {
        if let Line::Mv(mv) = line {
            if let Some(desc) = mv_line_from_mv(mv) {
                dram_longs = dram_longs.max(desc.dram_longs_needed());
                scratch_longs = scratch_longs.max(desc.scratch_longs_needed());
                indirect |= desc.uses_indirect();
            }
        }
    }
    if indirect {
        // A DAR entry decides the address at run time, so the device DRAM size
        // cannot be derived from the statement. One million long words per group
        // (8 MiB) is enough for the checked-in programs; the kernel counts every
        // out-of-range indirect access, and the run fails if the count is nonzero.
        dram_longs = dram_longs.max(1 << 20);
    }
    eprintln!("mv capacity: dram_longs={dram_longs}, scratch={scratch_longs}, indirect={indirect}");

    let gpu = match Gpu::new() {
        Ok(gpu) => gpu,
        Err(error) => {
            eprintln!("gpu unavailable: {error}");
            std::process::exit(2);
        }
    };
    let state = gpu
        .allocate_state_with_mv(dram_longs, scratch_longs)
        .expect("allocate");
    let lm = vec![0u32; PES * LM_WORDS];
    let grf = vec![0u32; PES * GRF_WORDS];
    gpu.upload_state(&state, &lm, &lm, &grf, &grf).expect("state");
    gpu.upload_mats(&state, &vec![0u32; MAT_WORDS]).expect("mats");
    gpu.upload_l1bm(&state, &vec![0u64; L1BS * L1BM_LONGS]).expect("l1");
    gpu.upload_l2bm(&state, &vec![0u64; L2BS * L2BM_LONGS]).expect("l2");
    if dram_longs > 0 {
        let pdm = vec![0u64; (mncore_sim::mv::GROUPS as u64 * mncore_sim::mv::PDM_LONGS) as usize];
        gpu.upload_pdm(&state, &pdm).expect("pdm");
        let dram = vec![0u64; (mncore_sim::mv::GROUPS as u64 * dram_longs) as usize];
        gpu.upload_dram(&state, &dram).expect("dram");
    }

    let start = std::time::Instant::now();
    let mut pe_lines = 0usize;
    for (lineno, line) in &program {
        match line {
            Line::Nop { .. } => {}
            Line::MaskDirective { wl, targets, entry } => {
                mask = MaskState { wl: *wl, targets: *targets, entry: *entry };
            }
            Line::Mv(mv) => {
                let desc = mv_line_from_mv(mv).expect("MV descriptor");
                gpu.run_mv_line(&state, &desc).expect("mv");
            }
            Line::Pe(exprs) => {
                pe_lines += 1;
                if let Err(error) = mncore_sim::issue::check(exprs) {
                    eprintln!("line {lineno}: {error}");
                    std::process::exit(3);
                }
                // SDM 3.6.4/3.6.13: a wait must accompany another PE expression and
                // its tag must be nonzero. The backend runs every MV to completion
                // in stream order, so an issued wait is already satisfied.
                let wait = exprs.iter().any(|e| matches!(e.op, Op::Wait(_)));
                if wait {
                    if exprs.len() < 2 {
                        eprintln!("line {lineno}: wait without another PE expression");
                        std::process::exit(3);
                    }
                    if exprs
                        .iter()
                        .any(|e| matches!(e.op, Op::Wait(0)))
                    {
                        eprintln!("line {lineno}: wait tag 0 is invalid");
                        std::process::exit(3);
                    }
                }
                let update_forward = !exprs.iter().any(|e| matches!(e.op, Op::Noforward));
                let has_mread = exprs.iter().any(|e| matches!(e.op, Op::MatRead { .. }));
                for expr in exprs {
                    if matches!(expr.op, Op::Noforward | Op::Wait(_)) {
                        continue;
                    }
                    if let Some(line) = alu_line_from_expr(expr, mask) {
                        gpu.run_alu_line_with(&state, &line, update_forward)
                            .expect("alu");
                    } else if let Some(line) = bfn_line_from_expr_state(expr, mask) {
                        gpu.run_bfn_line_with(&state, &line, update_forward)
                            .expect("bfn");
                    } else if let Some(line) = l1_read_line_from_expr(expr, mask) {
                        gpu.run_l1_read_line(&state, &line).expect("l1 read");
                    } else if let Some(line) = l1_write_line_from_expr(expr) {
                        gpu.run_l1_write_line_with(&state, &line, update_forward)
                            .expect("l1 write");
                    } else if let Some(line) = l2_line_from_expr(expr) {
                        gpu.run_l2_line(&state, &line).expect("l2");
                    } else if let Some(line) = l2_reduce_line_from_expr(expr) {
                        gpu.run_l2_reduce_line(&state, &line).expect("l2 red");
                    } else if let Some(line) = mat_write_line_from_expr(expr) {
                        gpu.run_mat_write_line(&state, &line).expect("mat write");
                    } else if let Some(line) = mat_read_line_from_expr(expr, mask) {
                        gpu.run_mat_read_line_with(&state, &line, update_forward)
                            .expect("mat read");
                    } else if let Some(line) = mat_mau_line_from_expr(expr, mask) {
                        gpu.run_mat_mau_line_with(&state, &line, update_forward)
                            .expect("mat mau");
                    } else if let Some(line) = mau_line_from_expr(expr, mask) {
                        gpu.run_mau_line_with(&state, &line, update_forward)
                            .expect("mau");
                    } else {
                        eprintln!("line {lineno}: no GPU descriptor for {:?}", expr.text);
                        std::process::exit(3);
                    }
                }
                // CPU steps without a matrix read expose zero on mreadf.
                if update_forward && !has_mread {
                    gpu.clear_mreadf(&state).expect("clear mreadf");
                }
            }
            other => {
                eprintln!("line {lineno}: unsupported line {other:?}");
                std::process::exit(3);
            }
        }
    }
    gpu.sync().expect("sync");
    let gpu_elapsed = start.elapsed();
    let mv_errors = gpu.download_mv_errors(&state).expect("mv errors");
    if mv_errors != 0 {
        println!("{mv_errors} indirect MV accesses fell outside the device DRAM");
    }

    let cpu_start = std::time::Instant::now();
    let mut sim = Sim::new();
    sim.run(&program).expect("cpu run");
    let cpu_elapsed = cpu_start.elapsed();

    let mut out = (
        vec![0u32; PES * LM_WORDS],
        vec![0u32; PES * LM_WORDS],
        vec![0u32; PES * GRF_WORDS],
        vec![0u32; PES * GRF_WORDS],
    );
    gpu.download_state(&state, &mut out.0, &mut out.1, &mut out.2, &mut out.3)
        .expect("download");
    let mut bad = 0usize;
    for (name, cpu, gpu, width) in [
        ("lm0", sim.m.mem.lm0.as_slice(), out.0.as_slice(), LM_WORDS),
        ("lm1", sim.m.mem.lm1.as_slice(), out.1.as_slice(), LM_WORDS),
        ("grf0", sim.m.mem.grf0.as_slice(), out.2.as_slice(), GRF_WORDS),
        ("grf1", sim.m.mem.grf1.as_slice(), out.3.as_slice(), GRF_WORDS),
    ] {
        if let Some(index) = cpu.iter().zip(gpu).position(|(a, b)| a != b) {
            println!(
                "{name}: first mismatch at pe {} addr {}: cpu {:08x} gpu {:08x}",
                index / width,
                index % width,
                cpu[index],
                gpu[index]
            );
            bad += cpu.iter().zip(gpu).filter(|(a, b)| a != b).count();
        }
    }
    let mats = gpu.download_mats(&state).expect("mats");
    for mab in 0..PES / 4 {
        for face in 0..2 {
            for row in 0..16 {
                for w in 0..8 {
                    let idx = ((mab * 2 + face) * 16 + row) * 8 + w;
                    if sim.m.mats[mab][face][row][w] != mats[idx] {
                        println!("mats first mismatch mab {mab} face {face} row {row} word {w}");
                        bad += 1;
                    }
                }
            }
        }
    }
    let mask_out = gpu.download_mask(&state).expect("mask");
    for pe in 0..PES {
        for entry in 0..16 {
            if sim.m.pes[pe].mask[entry] as u32 != mask_out[pe * 16 + entry] {
                println!("mask first mismatch pe {pe} entry {entry}");
                bad += 1;
            }
        }
    }
    let l1 = gpu.download_l1bm(&state).expect("l1");
    for l1b in 0..L1BS {
        for addr in 0..L1BM_LONGS {
            if sim.m.blocks.l1bm[l1b][addr] != l1[l1b * L1BM_LONGS + addr] {
                println!("l1bm first mismatch l1b {l1b} addr {addr}");
                bad += 1;
            }
        }
    }
    let l2 = gpu.download_l2bm(&state).expect("l2");
    for l2b in 0..L2BS {
        for addr in 0..L2BM_LONGS {
            if sim.m.blocks.l2bm[l2b][addr] != l2[l2b * L2BM_LONGS + addr] {
                println!("l2bm first mismatch l2b {l2b} addr {addr}");
                bad += 1;
            }
        }
    }
    let (bar0, bar1) = gpu.download_bar(&state).expect("bar");
    for pe in 0..PES {
        if sim.m.pes[pe].bar0 != bar0[pe] {
            println!("bar0 first mismatch pe {pe}");
            bad += 1;
        }
        if sim.m.pes[pe].bar1 != bar1[pe] {
            println!("bar1 first mismatch pe {pe}");
            bad += 1;
        }
    }
    let lbi = gpu.download_l1bi(&state).expect("lbi");
    for l1b in 0..L1BS {
        for c in 0..4 {
            for o in 0..64 {
                if sim.m.blocks.lbi[l1b][c][o] != lbi[(l1b * 4 + c) * 64 + o] {
                    println!("lbi first mismatch l1b {l1b} cycle {c} offset {o}");
                    bad += 1;
                    break;
                }
            }
        }
    }
    let dar = gpu.download_dar(&state).expect("dar");
    for g in 0..mncore_sim::mv::GROUPS {
        for e in 0..mncore_sim::blocks::DAR_ENTRIES {
            if sim.m.blocks.dar[g][e] != dar[g * mncore_sim::blocks::DAR_ENTRIES + e] {
                println!("dar first mismatch group {g} entry {e}");
                bad += 1;
                break;
            }
        }
    }
    let darbuf = gpu.download_darbuf(&state).expect("darbuf");
    for g in 0..mncore_sim::mv::GROUPS {
        for e in 0..mncore_sim::blocks::DARBUF_ENTRIES {
            if sim.m.blocks.darbuf[g][e] != darbuf[g * mncore_sim::blocks::DARBUF_ENTRIES + e] {
                println!("darbuf first mismatch group {g} entry {e}");
                bad += 1;
                break;
            }
        }
    }
    let dar_addr = gpu.download_dar_addr(&state).expect("dar addr");
    if [sim.m.blocks.darw_addr as u32, sim.m.blocks.darbuf_read_addr as u32] != dar_addr {
        println!("dar address mismatch");
        bad += 1;
    }
    let aluf = gpu.download_aluf(&state).expect("aluf");
    let mauf = gpu.download_mauf(&state).expect("mauf");
    let mreadf = gpu.download_mreadf(&state).expect("mreadf");
    let lbf = gpu.download_lbf(&state).expect("lbf");
    for pe in 0..PES {
        for c in 0..4 {
            for w in 0..4 {
                let i = pe * 16 + c * 4 + w;
                if sim.m.pes[pe].aluf[c][w] != aluf[i] {
                    println!("aluf first mismatch pe {pe} cycle {c} word {w}");
                    bad += 1;
                    break;
                }
                if sim.m.pes[pe].mauf[c][w] != mauf[i] {
                    println!("mauf first mismatch pe {pe} cycle {c} word {w}");
                    bad += 1;
                    break;
                }
                if sim.m.pes[pe].mreadf[c][w] != mreadf[i] {
                    println!("mreadf first mismatch pe {pe} cycle {c} word {w}");
                    bad += 1;
                    break;
                }
                if sim.m.pes[pe].lbf[c][w] != lbf[i] {
                    println!("lbf first mismatch pe {pe} cycle {c} word {w}");
                    bad += 1;
                    break;
                }
            }
        }
    }
    if dram_longs > 0 {
        let pdm = gpu.download_pdm(&state).expect("pdm");
        for g in 0..mncore_sim::mv::GROUPS {
            for a in 0..mncore_sim::mv::PDM_LONGS {
                if sim.off.pdm[g].get(a) != pdm[(g as u64 * mncore_sim::mv::PDM_LONGS + a) as usize] {
                    println!("pdm first mismatch group {g} addr {a}");
                    bad += 1;
                    break;
                }
            }
        }
        let dram = gpu.download_dram(&state).expect("dram");
        for g in 0..mncore_sim::mv::GROUPS {
            for a in 0..dram_longs as usize {
                if sim.off.dram[g].get(a as u64) != dram[(g as u64 * dram_longs + a as u64) as usize] {
                    println!("dram first mismatch group {g} addr {a}");
                    bad += 1;
                    break;
                }
            }
        }
    }
    println!(
        "{} PE lines, {} mismatches, cpu {:?}, gpu {:?}",
        pe_lines, bad, cpu_elapsed, gpu_elapsed
    );
    if bad != 0 || mv_errors != 0 {
        std::process::exit(1);
    }
}
