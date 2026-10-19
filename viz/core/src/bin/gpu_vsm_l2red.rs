//! Runs L2BM reductions and internal multicast on the CPU simulator and the GPU.
//!
//! The generated program mixes the `l2bmrffadd` form used by
//! `benchmarks/mnist_train_step.vsm` with L1B subsets, `l2bmr2` and `l2bmi`,
//! and exercises every supported RRN opcode.
//!
//! Usage: gpu_vsm_l2red [lines]

use std::collections::BTreeSet;

use mncore_sim::blocks::{L1BM_LONGS, L1BS, L2BM_LONGS, L2BS};
use mncore_sim::gpu::{l2_reduce_line_from_expr, Gpu, L2RedLine};
use mncore_sim::run::Sim;
use mncore_sim::vsm::{self, Line};

/// RRN opcodes exercised beyond `ffadd`, which is the one the benchmark uses.
const RRNS: [&str; 24] = [
    "dfadd", "ffadd", "hfadd", "dmax", "fmax", "hmax", "dmin", "fmin", "hmin", "liadd", "iiadd",
    "siadd", "lband", "iband", "sband", "land", "iand", "sand", "lbor", "ibor", "sbor", "lor",
    "ior", "sor",
];

fn main() {
    let lines: usize = std::env::args()
        .nth(1)
        .and_then(|s| s.parse().ok())
        .unwrap_or(512);
    let mut text = String::new();
    let mut reduce_rrn = 0usize;
    let mut reduce2_rrn = 0usize;
    let (mut n_reduce, mut n_reduce2, mut n_imcast) = (0usize, 0usize, 0usize);
    let mut used_reduce = BTreeSet::new();
    let mut used_reduce2 = BTreeSet::new();
    for i in 0..lines {
        let a0 = (i * 16) % L1BM_LONGS;
        let a1_l2 = (i * 48) % L2BM_LONGS;
        let a1_l1 = (i * 32) % L1BM_LONGS;
        let line = match i % 20 {
            // The benchmark form: full L1B set, `ffadd`.
            0..=5 => {
                n_reduce += 1;
                format!("l2bmrffadd $lb{a0} $lc{a1_l2}\n")
            }
            6 => {
                n_reduce += 1;
                format!("l2bmrffadd@[0,4] $lb{a0} $lc{a1_l2}\n")
            }
            7 => {
                n_reduce += 1;
                format!("l2bmrffadd@1/6 $lb{a0} $lc{a1_l2}\n")
            }
            8 => {
                n_reduce2 += 1;
                format!("l2bmr2ffadd $lb{a0} $lc{a1_l2}\n")
            }
            9 => {
                n_imcast += 1;
                format!("l2bmi@0/0 $lb{a0} $lb{a1_l1}\n")
            }
            10 => {
                n_imcast += 1;
                format!("l2bmi@0/4 $lb{a0} $lb{a1_l1}\n")
            }
            11 => {
                n_imcast += 1;
                format!("l2bmi@[0,2,4,6] $lb{a0} $lb{a1_l1}\n")
            }
            12 => {
                n_imcast += 1;
                format!("l2bmi@1/1 $lb{a0} $lb{a1_l1}\n")
            }
            // Every RRN once with the full set and once with a subset.
            13 | 14 => {
                let rrn = RRNS[reduce_rrn % RRNS.len()];
                used_reduce.insert(rrn);
                reduce_rrn += 1;
                n_reduce += 1;
                if reduce_rrn > RRNS.len() {
                    format!("l2bmr{rrn}@[0,2,4,6] $lb{a0} $lc{a1_l2}\n")
                } else {
                    format!("l2bmr{rrn} $lb{a0} $lc{a1_l2}\n")
                }
            }
            15 | 16 => {
                let rrn = RRNS[reduce2_rrn % RRNS.len()];
                used_reduce2.insert(rrn);
                reduce2_rrn += 1;
                n_reduce2 += 1;
                format!("l2bmr2{rrn} $lb{a0} $lc{a1_l2}\n")
            }
            17 => {
                n_imcast += 1;
                format!("l2bmi@7 $lb{a0} $lb{a1_l1}\n")
            }
            18 => {
                n_imcast += 1;
                format!("l2bmi@[1,3,5,7] $lb{a0} $lb{a1_l1}\n")
            }
            _ => {
                n_imcast += 1;
                format!("l2bmi@2/2 $lb{a0} $lb{a1_l1}\n")
            }
        };
        text.push_str(&line);
    }
    let program = vsm::parse(&text).expect("parse");
    let mut descriptors: Vec<L2RedLine> = Vec::new();
    for (_, line) in &program {
        let Line::Pe(exprs) = line else {
            panic!("expected PE line");
        };
        assert_eq!(exprs.len(), 1, "one expression per line");
        descriptors.push(l2_reduce_line_from_expr(&exprs[0]).expect("L2 reduction line"));
    }

    let mut seed = 0x2c1b_3e4d_5f60_7182u64;
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
        gpu.run_l2_reduce_line(&state, line).expect("l2 reduce");
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
                    println!(
                        "l1bm first mismatch at l1b {l1b} addr {addr}: cpu {cpu:016x} gpu {gpu:016x}"
                    );
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
                    println!(
                        "l2bm first mismatch at l2 {l2} addr {addr}: cpu {cpu:016x} gpu {gpu:016x}"
                    );
                }
                mismatches += 1;
            }
        }
    }
    println!(
        "l2bmr {n_reduce} lines, l2bmr2 {n_reduce2} lines, l2bmi {n_imcast} lines (RRNs: l2bmr {}/{}, l2bmr2 {}/{})",
        used_reduce.len(),
        RRNS.len(),
        used_reduce2.len(),
        RRNS.len()
    );
    println!(
        "{lines} lines, {mismatches} mismatches, cpu {cpu_elapsed:?}, gpu {gpu_elapsed:?}"
    );
    if mismatches != 0 {
        std::process::exit(1);
    }
}
