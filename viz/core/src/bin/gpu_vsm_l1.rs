//! Runs L1BM-to-PE reads (l1bmd/l1bmm) on the CPU and the GPU.
//!
//! Usage: gpu_vsm_l1 [lines]

use mncore_sim::blocks::{L1BM_LONGS, L1BS};
use mncore_sim::gpu::{l1_read_line_from_expr, Gpu, L1ReadLine};
use mncore_sim::machine::{GRF_WORDS, LM_WORDS, PES};
use mncore_sim::run::Sim;
use mncore_sim::vsm::{self, Line};

fn main() {
    let lines: usize = std::env::args()
        .nth(1)
        .and_then(|s| s.parse().ok())
        .unwrap_or(100);
    let mut text = String::new();
    for i in 0..lines {
        let offset = (i % 16) * 4;
        if i % 2 == 0 {
            text.push_str(&format!("l1bmd $lb{} $lm{}v\n", offset, offset));
        } else {
            text.push_str(&format!("l1bmm $llb{} $llm{}v\n", offset, offset));
        }
    }
    let program = vsm::parse(&text).expect("parse");
    let mut descriptors: Vec<L1ReadLine> = Vec::new();
    for (_, line) in &program {
        let Line::Pe(exprs) = line else {
            panic!("expected PE line");
        };
        descriptors.push(l1_read_line_from_expr(&exprs[0]).expect("L1 read"));
    }

    let mut seed = 0x5eed_1234_5678_9abcu64;
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
    let l1bm: Vec<u64> = (0..L1BS * L1BM_LONGS).map(|_| next()).collect();

    let mut sim = Sim::new();
    sim.m.mem.lm0.copy_from_slice(&lm0);
    sim.m.mem.lm1.copy_from_slice(&lm1);
    sim.m.mem.grf0.copy_from_slice(&grf0);
    sim.m.mem.grf1.copy_from_slice(&grf1);
    for (l1b, words) in sim.m.blocks.l1bm.iter_mut().enumerate() {
        for (addr, value) in words.iter_mut().enumerate() {
            *value = l1bm[l1b * L1BM_LONGS + addr];
        }
    }
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
    gpu.upload_l1bm(&state, &l1bm).expect("upload l1bm");
    let gpu_start = std::time::Instant::now();
    for line in &descriptors {
        gpu.run_l1_read_line(&state, line).expect("l1");
    }
    gpu.sync().expect("sync");
    let gpu_elapsed = gpu_start.elapsed();
    let mut out = (
        vec![0u32; lm_len],
        vec![0u32; lm_len],
        vec![0u32; grf_len],
        vec![0u32; grf_len],
    );
    gpu.download_state(&state, &mut out.0, &mut out.1, &mut out.2, &mut out.3)
        .expect("download");
    let mut mismatches = 0usize;
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
        "{} L1 reads, {} mismatches, cpu {:?}, gpu {:?}",
        lines, mismatches, cpu_elapsed, gpu_elapsed
    );
    if mismatches != 0 {
        std::process::exit(1);
    }
}
