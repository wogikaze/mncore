//! Runs L1BM-to-PE reads (l1bmd/l1bmm) on the CPU and the GPU.
//!
//! Usage: gpu_vsm_l1 [lines]

use mncore_sim::blocks::{L1BM_LONGS, L1BS};
use mncore_sim::gpu::{
    l1_read_line_from_expr, l1_reduce_line_from_expr, l1_write_line_from_expr, Gpu, L1ReadLine,
    L1ReduceLine, L1WriteLine,
};
use mncore_sim::machine::{GRF_WORDS, LM_WORDS, PES};
use mncore_sim::run::Sim;
use mncore_sim::vsm::{self, Line};

fn main() {
    let lines: usize = std::env::args()
        .nth(1)
        .and_then(|s| s.parse().ok())
        .unwrap_or(100);
    enum Action {
        Read(L1ReadLine),
        Write(L1WriteLine),
        Reduce(L1ReduceLine),
    }
    let mut text = String::new();
    for i in 0..lines {
        let offset = (i % 16) * 4;
        match i % 6 {
            0 => text.push_str(&format!(
                "l1bmm@{} $lln{}v $llb{}\n",
                i % 16,
                offset,
                offset
            )),
            1 => text.push_str(&format!("l1bmm $llb{} $llm{}v\n", offset, offset)),
            2 => text.push_str(&format!("l1bmd $lb{} $lm{}v\n", offset, offset)),
            3 => text.push_str(&format!("l1bmp $lb{} $lm{}v\n", offset, offset)),
            4 => text.push_str(&format!("l1bmrffadd $ln{}v $lb{}\n", offset, offset)),
            _ => text.push_str(&format!("l1bmd $ln{}v $lb{}\n", offset, offset)),
        }
    }
    let program = vsm::parse(&text).expect("parse");
    let mut actions = Vec::new();
    for (_, line) in &program {
        let Line::Pe(exprs) = line else {
            panic!("expected PE line");
        };
        let expr = &exprs[0];
        if let Some(line) = l1_read_line_from_expr(expr) {
            actions.push(Action::Read(line));
        } else if let Some(line) = l1_write_line_from_expr(expr) {
            actions.push(Action::Write(line));
        } else if let Some(line) = l1_reduce_line_from_expr(expr) {
            actions.push(Action::Reduce(line));
        } else {
            eprintln!("unsupported: {expr:?}");
            std::process::exit(1);
        }
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
    for action in &actions {
        match action {
            Action::Read(line) => gpu.run_l1_read_line(&state, line).expect("l1 read"),
            Action::Write(line) => gpu.run_l1_write_line(&state, line).expect("l1 write"),
            Action::Reduce(line) => gpu.run_l1_reduce_line(&state, line).expect("l1 reduce"),
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
    gpu.download_state(&state, &mut out.0, &mut out.1, &mut out.2, &mut out.3)
        .expect("download");
    let gpu_l1bm = gpu.download_l1bm(&state).expect("download l1bm");
    let mut mismatches = 0usize;
    for l1b in 0..L1BS {
        for addr in 0..L1BM_LONGS {
            let cpu = sim.m.blocks.l1bm[l1b][addr];
            let gpu = gpu_l1bm[l1b * L1BM_LONGS + addr];
            if cpu != gpu {
                if mismatches == 0 {
                    println!("l1bm first mismatch at l1b {l1b} addr {addr}: cpu {cpu:016x} gpu {gpu:016x}");
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
        "{} L1 reads, {} mismatches, cpu {:?}, gpu {:?}",
        lines, mismatches, cpu_elapsed, gpu_elapsed
    );
    if mismatches != 0 {
        std::process::exit(1);
    }
}
