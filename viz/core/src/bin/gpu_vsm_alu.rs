//! Runs f32 ALU Passa and MAU-aluf lines on the CPU simulator and the GPU.
//!
//! Usage: gpu_vsm_alu [lines]

use mncore_sim::gpu::{
    alu_line_from_expr, bfn_line_from_expr, mau_line_from_expr, AluLine, BfnLine, Gpu, MauLine,
};
use mncore_sim::machine::{GRF_WORDS, LM_WORDS, PES};
use mncore_sim::run::Sim;
use mncore_sim::vsm::{self, Line};

enum Action {
    Alu(AluLine),
    Bfn(BfnLine),
    Mau(MauLine),
}

fn main() {
    let lines: usize = std::env::args()
        .nth(1)
        .and_then(|s| s.parse().ok())
        .unwrap_or(1000);
    let forms = [
        "fpassa $r{} $n{}",
        "fvadd $r{} $aluf $n{}",
        "fpassa $r{} $n{}",
        "fvmul $r{} $aluf $n{}",
        "ixor $m{} $r{} $omr1",
        "fmax $m{}v $aluf $nowrite",
        "fmax $m{}v $aluf $r{}v",
        "frsqrt $m{}v $nowrite",
        "frsqrt $m{}v $r{}v",
        "gbfn $lm{}v $nowrite",
        "fvadd $r{} $aluf $n{}",
        "msr $s{}v $s{}v",
        "msr $aluf $s{}v",
        "zero $ln{}v",
        "imm f\"0.5\" $r{}v",
        "imm i\"1\" $s{}v",
    ];
    let mut text = String::new();
    for i in 0..lines {
        let offset = (i % 8) * 4;
        text.push_str(&forms[i % forms.len()].replace("{}", &offset.to_string()));
        text.push('\n');
    }
    let program = vsm::parse(&text).expect("parse");
    let mut actions = Vec::new();
    for (_, line) in &program {
        let Line::Pe(exprs) = line else {
            panic!("expected PE line");
        };
        let expr = &exprs[0];
        if let Some(line) = alu_line_from_expr(expr) {
            actions.push(Action::Alu(line));
        } else if let Some(line) = bfn_line_from_expr(expr) {
            actions.push(Action::Bfn(line));
        } else if let Some(line) = mau_line_from_expr(expr, Default::default()) {
            actions.push(Action::Mau(line));
        } else {
            eprintln!("unsupported: {:?}", expr);
            std::process::exit(1);
        }
    }

    let mut seed = 0x1234_5678_9abc_def0u64;
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
    let state = gpu.allocate_state().expect("allocate");
    gpu.upload_state(&state, &lm0, &lm1, &grf0, &grf1)
        .expect("upload");
    let gpu_start = std::time::Instant::now();
    for action in &actions {
        match action {
            Action::Alu(line) => gpu.run_alu_line(&state, line).expect("alu"),
            Action::Bfn(line) => gpu.run_bfn_line(&state, line).expect("bfn"),
            Action::Mau(line) => gpu.run_mau_line(&state, line).expect("mau"),
        }
    }
    gpu.sync().expect("sync");
    let gpu_elapsed = gpu_start.elapsed();
    let gpu_mask = gpu.download_mask(&state).expect("download mask");
    let mut out = (
        vec![0u32; lm_len],
        vec![0u32; lm_len],
        vec![0u32; grf_len],
        vec![0u32; grf_len],
    );
    gpu.download_state(&state, &mut out.0, &mut out.1, &mut out.2, &mut out.3)
        .expect("download");
    let mut mismatches = 0usize;
    for pe in 0..PES {
        for entry in 0..16 {
            let cpu = sim.m.pes[pe].mask[entry] as u32;
            let gpu = gpu_mask[pe * 16 + entry];
            if cpu != gpu {
                if mismatches == 0 {
                    println!("omr first mismatch at pe {pe} entry {entry}: cpu {cpu:x} gpu {gpu:x}");
                }
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
        "{} lines, {} mismatches, cpu {:?}, gpu {:?}",
        lines, mismatches, cpu_elapsed, gpu_elapsed
    );
    if mismatches != 0 {
        std::process::exit(1);
    }
}
