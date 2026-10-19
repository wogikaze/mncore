//! Runs OMR-masked MAU lines on the CPU simulator and the GPU.
//!
//! Usage: gpu_vsm_mask [rounds]

use mncore_sim::gpu::{alu_line_from_expr, mau_line_from_expr, Gpu};
use mncore_sim::machine::{MaskState, GRF_WORDS, LM_WORDS, PES};
use mncore_sim::run::Sim;
use mncore_sim::vsm::{self, Line};

enum Action {
    Alu(mncore_sim::gpu::AluLine),
    Mau(mncore_sim::gpu::MauLine),
}

fn main() {
    let rounds: usize = std::env::args()
        .nth(1)
        .and_then(|s| s.parse().ok())
        .unwrap_or(100);
    let mut text = String::new();
    for i in 0..rounds {
        let offset = (i % 8) * 8;
        text.push_str(&format!("ixor $m{} $r{} $omr1\n", offset, offset));
        text.push_str("maskn 1\n");
        text.push_str(&format!("fvadd $r{} $s{} $n{}\n", offset, offset + 4, offset));
        text.push_str("mask 0\n");
        text.push_str(&format!("fvadd $r{} $s{} $n{}\n", offset, offset + 4, offset + 4));
    }
    let program = vsm::parse(&text).expect("parse");
    let mut state = MaskState::default();
    let mut actions = Vec::new();
    for (_, line) in &program {
        match line {
            Line::MaskDirective {
                wl,
                targets,
                entry,
            } => {
                state = MaskState {
                    wl: *wl,
                    targets: *targets,
                    entry: *entry,
                };
            }
            Line::Pe(exprs) => {
                let expr = &exprs[0];
                if let Some(line) = alu_line_from_expr(expr) {
                    actions.push(Action::Alu(line));
                } else if let Some(line) = mau_line_from_expr(expr, state) {
                    actions.push(Action::Mau(line));
                } else {
                    eprintln!("unsupported: {expr:?}");
                    std::process::exit(1);
                }
            }
            other => {
                eprintln!("unsupported line: {other:?}");
                std::process::exit(1);
            }
        }
    }

    let mut seed = 0xfeed_face_dead_beefu64;
    let mut next = || {
        seed ^= seed << 13;
        seed ^= seed >> 7;
        seed ^= seed << 17;
        seed
    };
    let lm_len = PES * LM_WORDS;
    let grf_len = PES * GRF_WORDS;
    let lm0: Vec<u32> = (0..lm_len).map(|_| next() as u32).collect();
    let lm1: Vec<u32> = (0..lm_len).map(|_| next() as u32).collect();
    let grf0: Vec<u32> = (0..grf_len).map(|_| next() as u32).collect();
    let grf1: Vec<u32> = (0..grf_len).map(|_| next() as u32).collect();

    let mut sim = Sim::new();
    sim.m.mem.lm0.copy_from_slice(&lm0);
    sim.m.mem.lm1.copy_from_slice(&lm1);
    sim.m.mem.grf0.copy_from_slice(&grf0);
    sim.m.mem.grf1.copy_from_slice(&grf1);
    let cpu_start = std::time::Instant::now();
    sim.run(&program).expect("cpu run");
    let cpu_elapsed = cpu_start.elapsed();

    let gpu = match Gpu::new() {
        Ok(gpu) => gpu,
        Err(error) => {
            eprintln!("gpu unavailable: {error}");
            std::process::exit(2);
        }
    };
    let gpu_state = gpu.allocate_state().expect("allocate");
    gpu.upload_state(&gpu_state, &lm0, &lm1, &grf0, &grf1)
        .expect("upload");
    let gpu_start = std::time::Instant::now();
    for action in &actions {
        match action {
            Action::Alu(line) => gpu.run_alu_line(&gpu_state, line).expect("alu"),
            Action::Mau(line) => gpu.run_mau_line(&gpu_state, line).expect("mau"),
        }
    }
    gpu.sync().expect("sync");
    let gpu_elapsed = gpu_start.elapsed();
    let mut out = (
        vec![0u32; lm_len],
        vec![0u32; lm_len],
        vec![0u32; grf_len],
        vec![0u32; grf_len],
    );
    gpu.download_state(
        &gpu_state,
        &mut out.0,
        &mut out.1,
        &mut out.2,
        &mut out.3,
    )
    .expect("download");
    let gpu_mask = gpu.download_mask(&gpu_state).expect("mask");
    let mut mismatches = 0usize;
    for pe in 0..PES {
        for entry in 0..16 {
            if sim.m.pes[pe].mask[entry] as u32 != gpu_mask[pe * 16 + entry] {
                mismatches += 1;
            }
        }
    }
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
            mismatches += cpu.iter().zip(gpu).filter(|(a, b)| a != b).count();
        }
    }
    println!(
        "{} rounds, {} mismatches, cpu {:?}, gpu {:?}",
        rounds, mismatches, cpu_elapsed, gpu_elapsed
    );
    if mismatches != 0 {
        std::process::exit(1);
    }
}
