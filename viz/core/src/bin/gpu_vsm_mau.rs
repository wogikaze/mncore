//! Runs a VSM program made of simple f32 MAU lines on the CPU simulator and
//! on the GPU, then compares the four PE memories.
//!
//! Usage: gpu_vsm_mau [lines]

use mncore_sim::gpu::{mau_line_from_expr, Gpu};
use mncore_sim::machine::{GRF_WORDS, LM_WORDS, PES};
use mncore_sim::run::Sim;
use mncore_sim::vsm::{self, Line};


fn main() {
    let lines: usize = std::env::args()
        .nth(1)
        .and_then(|s| s.parse().ok())
        .unwrap_or(100);
    let forms = [
        "fvpassa $m{}v $r{}v",
        "fvadd $m{}v $r{}v $n{}v",
        "fvmul $m{}v $r{}v $n{}v",
        "fvfma $m{}v $r{}v $n{}v $r{}v",
        "fvadd $r{}v $mauf $n{}v",
        "fvpassa $llm{}v $llr{}v",
        "fvadd $m{}v -$r{}v $n{}v",
    ];
    let mut text = String::new();
    for i in 0..lines {
        let offset = (i % 8) * 8;
        text.push_str(&forms[i % forms.len()].replace("{}", &offset.to_string()));
        text.push('\n');
    }
    let program = vsm::parse(&text).expect("parse");
    let mut descriptors = Vec::with_capacity(program.len());
    for (_, line) in &program {
        let Line::Pe(exprs) = line else {
            panic!("expected a PE line");
        };
        if exprs.len() != 1 {
            panic!("expected one expression per line");
        }
        match mau_line_from_expr(&exprs[0]) {
            Some(line) => descriptors.push(line),
            None => {
                eprintln!("unsupported: {:?} {:?}", exprs[0].op, exprs[0]);
                std::process::exit(1);
            }
        }
    }

    let mut seed = 0xdead_beef_1234_5678u64;
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
    let state = gpu.allocate_state().expect("allocate state");
    gpu.upload_state(&state, &lm0, &lm1, &grf0, &grf1)
        .expect("upload");
    let gpu_start = std::time::Instant::now();
    for line in &descriptors {
        gpu.run_mau_line(&state, line).expect("run mau line");
    }
    gpu.sync().expect("sync");
    let gpu_elapsed = gpu_start.elapsed();
    let mut out_lm0 = vec![0u32; lm_len];
    let mut out_lm1 = vec![0u32; lm_len];
    let mut out_grf0 = vec![0u32; grf_len];
    let mut out_grf1 = vec![0u32; grf_len];
    gpu.download_state(&state, &mut out_lm0, &mut out_lm1, &mut out_grf0, &mut out_grf1)
        .expect("download");

    let mut mismatches = 0usize;
    for (name, cpu, gpu, width) in [
        ("lm0", sim.m.mem.lm0.as_slice(), out_lm0.as_slice(), LM_WORDS),
        ("lm1", sim.m.mem.lm1.as_slice(), out_lm1.as_slice(), LM_WORDS),
        ("grf0", sim.m.mem.grf0.as_slice(), out_grf0.as_slice(), GRF_WORDS),
        ("grf1", sim.m.mem.grf1.as_slice(), out_grf1.as_slice(), GRF_WORDS),
    ] {
        let first = cpu.iter().zip(gpu).position(|(a, b)| a != b);
        if let Some(index) = first {
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
        "{} MAU lines, {} mismatches, cpu {:?}, gpu {:?}",
        lines, mismatches, cpu_elapsed, gpu_elapsed
    );
    if mismatches != 0 {
        std::process::exit(1);
    }
}
