//! Runs L2BM transfers on the CPU simulator and the GPU.
//!
//! Usage: gpu_vsm_l2 [lines]

use mncore_sim::blocks::{L1BM_LONGS, L1BS, L2BM_LONGS, L2BS};
use mncore_sim::gpu::{l2_line_from_expr, Gpu, L2Line};
use mncore_sim::run::Sim;
use mncore_sim::vsm::{self, Line};

fn main() {
    let lines: usize = std::env::args()
        .nth(1)
        .and_then(|s| s.parse().ok())
        .unwrap_or(100);
    let mut text = String::new();
    for i in 0..lines {
        let offset = (i % 32) * 8;
        match i % 5 {
            0 => text.push_str(&format!("l2bmd $lc{} $lb{}\n", offset, offset)),
            1 => text.push_str(&format!("l2bmb $lc{} $lb{}\n", offset, offset)),
            2 => text.push_str(&format!("l2bm@0 $lb{} $lc{}\n", offset, offset)),
            3 => text.push_str(&format!("l2bmb2 $lc{} $lb{}\n", offset, offset)),
            _ => text.push_str(&format!("l2bmd@[0,4] $lc{} $lb{}\n", offset, offset)),
        }
    }
    let program = vsm::parse(&text).expect("parse");
    let mut descriptors: Vec<L2Line> = Vec::new();
    for (_, line) in &program {
        let Line::Pe(exprs) = line else {
            panic!("expected PE line");
        };
        descriptors.push(l2_line_from_expr(&exprs[0]).expect("L2 line"));
    }

    let mut seed = 0x1a2b_3c4d_5e6f_7788u64;
    let mut next = || {
        seed ^= seed << 13;
        seed ^= seed >> 7;
        seed ^= seed << 17;
        seed
    };
    let l1bm: Vec<u64> = (0..L1BS * L1BM_LONGS).map(|_| next()).collect();
    let l2bm: Vec<u64> = (0..L2BS * L2BM_LONGS).map(|_| next()).collect();
    let mut sim = Sim::new();
    for (l1b, words) in sim.m.blocks.l1bm.iter_mut().enumerate() {
        for (addr, value) in words.iter_mut().enumerate() {
            *value = l1bm[l1b * L1BM_LONGS + addr];
        }
    }
    for (l2, words) in sim.m.blocks.l2bm.iter_mut().enumerate() {
        for (addr, value) in words.iter_mut().enumerate() {
            *value = l2bm[l2 * L2BM_LONGS + addr];
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
    gpu.upload_l1bm(&state, &l1bm).expect("upload l1bm");
    gpu.upload_l2bm(&state, &l2bm).expect("upload l2bm");
    let gpu_start = std::time::Instant::now();
    for line in &descriptors {
        gpu.run_l2_line(&state, line).expect("l2");
    }
    gpu.sync().expect("sync");
    let gpu_elapsed = gpu_start.elapsed();
    let out_l1 = gpu.download_l1bm(&state).expect("download l1bm");
    let out_l2 = gpu.download_l2bm(&state).expect("download l2bm");
    let mut mismatches = 0usize;
    for l1b in 0..L1BS {
        for addr in 0..L1BM_LONGS {
            let cpu = sim.m.blocks.l1bm[l1b][addr];
            let gpu = out_l1[l1b * L1BM_LONGS + addr];
            if cpu != gpu {
                if mismatches == 0 {
                    println!("l1bm first mismatch at l1b {l1b} addr {addr}");
                }
                mismatches += 1;
            }
        }
    }
    for l2 in 0..L2BS {
        for addr in 0..L2BM_LONGS {
            let cpu = sim.m.blocks.l2bm[l2][addr];
            let gpu = out_l2[l2 * L2BM_LONGS + addr];
            if cpu != gpu {
                if mismatches == 0 {
                    println!("l2bm first mismatch at l2 {l2} addr {addr}");
                }
                mismatches += 1;
            }
        }
    }
    println!(
        "{} L2 lines, {} mismatches, cpu {:?}, gpu {:?}",
        lines, mismatches, cpu_elapsed, gpu_elapsed
    );
    if mismatches != 0 {
        std::process::exit(1);
    }
}
