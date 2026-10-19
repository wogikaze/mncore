//! Runs MV statements on the CPU simulator and the GPU and compares the
//! off-chip memories (PDM, truncated DRAM) and the L1BM/L2BM blocks.
//!
//! Usage:
//!   gpu_vsm_mv [lines]                   synthetic MV statements (default 200)
//!   gpu_vsm_mv --program FILE [lines]    MV statements extracted from a VSM program
//!
//! Exit codes: 0 all compared lines match, 1 mismatch, 2 setup/GPU error,
//! 3 at least one MV statement is not supported by the GPU kernel.

use std::time::Instant;

use mncore_sim::blocks::{L1BM_LONGS, L1BS, L2BM_LONGS, L2BS};
use mncore_sim::gpu::{mv_line_from_mv, Gpu, MvLine};
use mncore_sim::mv::{GROUPS, PDM_LONGS};
use mncore_sim::run::Sim;
use mncore_sim::vsm::{self, Line};

const SEED: u64 = 0x6d76_5f67_7075_0001;

struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    fn below(&mut self, n: u64) -> u64 {
        self.next() % n.max(1)
    }
}

struct Gen {
    rng: Rng,
    dram_cap: u64,
}

impl Gen {
    fn size(&mut self) -> u64 {
        64 * (1 + self.rng.below(16))
    }
    fn pdm(&mut self, size: u64) -> u64 {
        self.rng.below(PDM_LONGS - size)
    }
    fn l2(&mut self, size: u64) -> u64 {
        self.rng.below(L2BM_LONGS as u64 - size)
    }
    fn dram(&mut self, size: u64) -> u64 {
        self.rng.below(self.dram_cap - 2 * size)
    }
    fn group(&mut self) -> u8 {
        self.rng.below(4) as u8
    }
    fn l2b(&mut self) -> u8 {
        self.rng.below(2) as u8
    }
}

fn synthetic(seed: u64, count: usize) -> String {
    let dram_cap = 1 << 19;
    let mut g = Gen {
        rng: Rng(seed),
        dram_cap,
    };
    let mut text = String::new();
    let mut push = |s: String| {
        text.push_str(&s);
        text.push('\n');
    };
    for i in 0..count {
        let size = g.size();
        // Every eleventh line starts near the end of PDM/L2BM so that the
        // transfer wraps; the CPU and the kernel both use the same modulo.
        let wrap = i % 11 == 0;
        let pdm = |g: &mut Gen| {
            if wrap {
                PDM_LONGS - size / 2
            } else {
                g.pdm(size)
            }
        };
        let l2 = |g: &mut Gen| {
            if wrap {
                L2BM_LONGS as u64 - size / 2
            } else {
                g.l2(size)
            }
        };
        match i % 21 {
            0 => {
                let (pa, gs) = (pdm(&mut g), g.group());
                let (da, gd) = (g.dram(size), g.group());
                push(format!("mvp/n{size}i9f $p{pa}@{gs} $d{da}@{gd}"));
            }
            1 => {
                let (da, gs) = (g.dram(size), g.group());
                let (pa, gd) = (pdm(&mut g), g.group());
                push(format!("mvp/n{size}i9f $d{da}@{gs} $p{pa}@{gd}"));
            }
            2 => {
                let (da, c) = (g.dram(size), g.l2b());
                push(format!("mvp/n{size}i9f $d{da} $lc0@.{c}"));
            }
            3 => {
                let (la, c) = (l2(&mut g), g.l2b());
                let da = g.dram(size);
                push(format!("mvp/n{size}i9f $lc{la}@.{c} $d{da}"));
            }
            4 => {
                let (pa, gs) = (pdm(&mut g), g.group());
                let (la, gd, c) = (l2(&mut g), g.group(), g.l2b());
                push(format!("mvp/n{size}i9f $p{pa}@{gs} $lc{la}@{gd}.{c}"));
            }
            5 => {
                let (la, gs, c) = (l2(&mut g), g.group(), g.l2b());
                let (pa, gd) = (pdm(&mut g), g.group());
                push(format!("mvp/n{size}i9f $lc{la}@{gs}.{c} $p{pa}@{gd}"));
            }
            6 => {
                // Same-level, overlapping copy: exercises the two-pass snapshot.
                let delta = g.rng.below(size);
                match i % 3 {
                    0 => {
                        let pa = g.rng.below(PDM_LONGS - size - delta);
                        push(format!("mvp/n{size}i9f $p{pa}@0 $p{}@0", pa + delta));
                    }
                    1 => {
                        let la = g.rng.below(L2BM_LONGS as u64 - size - delta);
                        push(format!("mvp/n{size}i9f $lc{la}@0.0 $lc{}@0.0", la + delta));
                    }
                    _ => {
                        let da = g.rng.below(dram_cap - size - delta);
                        push(format!("mvp/n{size}i9f $d{da}@0 $d{}@0", da + delta));
                    }
                }
            }
            7 => {
                let delta = g.rng.below(size);
                let la = g.rng.below(L2BM_LONGS as u64 - size - delta);
                let c = g.l2b();
                push(format!("mvp/n{size}i9f $lc{la}@{c}.0 $lc{}@{c}.0", la + delta));
            }
            8 => {
                let (pa, gs) = (g.pdm(size), g.group());
                push(format!("mvb/n{size}i9f $p{pa}@{gs} $lc0"));
            }
            9 => {
                let da = g.dram(size);
                push(format!("mvb/n{size}i9f $d{da} $lc0"));
            }
            10 => {
                let da = g.dram(size);
                push(format!("mvb2/n{size}i9f $d{da} $lc0"));
            }
            11 => {
                let (pa, gs) = (g.pdm(size), g.group());
                push(format!("mvd/n{size}i9f $p{pa}@{gs} $lc0"));
            }
            12 => {
                let (la, gd, pa) = (g.l2(size), g.group(), g.pdm(size));
                push(format!("mvd/n{size}i9f $lc{la} $p{pa}@{gd}"));
            }
            13 => {
                let (pa, gs) = (g.pdm(size), g.group());
                push(format!("mvd/n{size}i9f $p{pa}@{gs} $d{}", g.dram(size)));
            }
            14 => {
                let (da, gd) = (g.dram(size), g.group());
                push(format!("mvd/n{size}i9f $d{da} $p{}@{gd}", g.pdm(size)));
            }
            15 => {
                let da = g.dram(size);
                push(format!("mvb4/n{size}i9f $d{da} $lc0"));
            }
            16 => {
                let (la, gd) = (g.l2(size), g.group());
                push(format!("mvrffadd/n{size}i9f $lc{la} $p{}@{gd}", g.pdm(size)));
            }
            17 => {
                let (la, da) = (g.l2(size), g.dram(size));
                push(format!("mvrffadd/n{size}i9f $lc{la} $d{da}"));
            }
            18 => {
                let (la, gd) = (g.l2(size), g.group());
                match i % 3 {
                    0 => push(format!("mvr2ffadd/n{size}i9f $lc{la} $p{}@{gd}", g.pdm(size))),
                    1 => push(format!("mvr2ffadd/n{size}i9f $lc{la} $p{}", g.pdm(size))),
                    _ => push(format!("mvr2ffadd/n{size}i9f $lc{la} $d{}", g.dram(size))),
                }
            }
            19 => {
                let (la, da) = (g.l2(size), g.dram(size));
                push(format!("mvr4ffadd/n{size}i9f $lc{la} $d{da}"));
            }
            _ => {
                // Other RRN operations and precisions, plus mvnop.
                let (la, gd) = (g.l2(size), g.group());
                let pdm = g.pdm(size);
                let ops = [
                    "mvr2iiadd", "mvr2iband", "mvr2iand", "mvr2ibor", "mvr2ior",
                    "mvr2hfadd", "mvrdfadd", "mvr2liadd", "mvr2lband", "mvr2land",
                    "mvr2lbor", "mvr2lor", "mvr2fmax", "mvr2fmin",
                ];
                let op = ops[(i / 21) % ops.len()];
                push(format!("{op}/n{size}i9f $lc{la} $p{pdm}@{gd}"));
                if i % 4 == 0 {
                    push("mvnop".to_string());
                }
            }
        }
    }
    text
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let mut count = 200usize;
    let mut program: Option<String> = None;
    let mut seed = SEED;
    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "--program" => {
                i += 1;
                program = Some(args.get(i).cloned().unwrap_or_else(|| {
                    eprintln!("--program needs a path");
                    std::process::exit(2);
                }));
            }
            "--seed" => {
                i += 1;
                seed = args
                    .get(i)
                    .and_then(|s| s.parse().ok())
                    .unwrap_or_else(|| {
                        eprintln!("--seed needs a number");
                        std::process::exit(2);
                    });
            }
            "-h" | "--help" => {
                println!(
                    "usage: gpu_vsm_mv [--seed N] [lines]\n       gpu_vsm_mv --program FILE [--seed N] [lines]"
                );
                return;
            }
            other => match other.parse() {
                Ok(n) => count = n,
                Err(_) => {
                    eprintln!("bad argument `{other}`");
                    std::process::exit(2);
                }
            },
        }
        i += 1;
    }

    let (label, text) = match &program {
        Some(path) => (
            format!("program {path}"),
            std::fs::read_to_string(path).unwrap_or_else(|e| {
                eprintln!("read {path}: {e}");
                std::process::exit(2);
            }),
        ),
        None => (format!("synthetic {count} seed {seed:#x}"), synthetic(seed, count)),
    };
    let parsed = vsm::parse(&text).unwrap_or_else(|e| {
        eprintln!("parse {}:{}: {}", label, e.line, e.msg);
        std::process::exit(2);
    });

    let mut cpu_lines: Vec<(usize, Line)> = Vec::new();
    let mut gpu_lines: Vec<MvLine> = Vec::new();
    let mut texts: Vec<String> = Vec::new();
    let mut skipped = 0usize;
    for (lineno, line) in &parsed {
        let Line::Mv(mv) = line else { continue };
        if cpu_lines.len() >= count && program.is_some() {
            break;
        }
        match mv_line_from_mv(mv) {
            Some(descriptor) => {
                cpu_lines.push((*lineno, line.clone()));
                gpu_lines.push(descriptor);
                texts.push(mv.text.clone());
            }
            None => {
                skipped += 1;
                if skipped <= 10 {
                    eprintln!("unsupported MV line {lineno}: {}", mv.text);
                }
            }
        }
    }
    if gpu_lines.is_empty() {
        eprintln!("{label}: no MV statements to run");
        std::process::exit(2);
    }

    let dram_longs = gpu_lines
        .iter()
        .map(|line| line.dram_longs_needed())
        .max()
        .unwrap_or(1)
        .max(1);
    let scratch_longs = gpu_lines
        .iter()
        .map(|line| line.scratch_longs_needed())
        .max()
        .unwrap_or(1)
        .max(1);

    // Random initial state, shared byte-for-byte by the CPU and the GPU.
    let mut rng = Rng(seed ^ 0x9e37_79b9_7f4a_7c15);
    let pdm_len = GROUPS * PDM_LONGS as usize;
    let dram_len = GROUPS * dram_longs as usize;
    let l1_len = L1BS * L1BM_LONGS;
    let l2_len = L2BS * L2BM_LONGS;
    let pdm_host: Vec<u64> = (0..pdm_len).map(|_| rng.next()).collect();
    let dram_host: Vec<u64> = (0..dram_len).map(|_| rng.next()).collect();
    let l1_host: Vec<u64> = (0..l1_len).map(|_| rng.next()).collect();
    let l2_host: Vec<u64> = (0..l2_len).map(|_| rng.next()).collect();

    let mut sim = Sim::new();
    for g in 0..GROUPS {
        for a in 0..PDM_LONGS as usize {
            sim.off.pdm[g].set(a as u64, pdm_host[g * PDM_LONGS as usize + a]);
        }
        for a in 0..dram_longs as usize {
            sim.off.dram[g].set(a as u64, dram_host[g * dram_longs as usize + a]);
        }
    }
    for (b, words) in sim.m.blocks.l1bm.iter_mut().enumerate() {
        words.copy_from_slice(&l1_host[b * L1BM_LONGS..(b + 1) * L1BM_LONGS]);
    }
    for (b, words) in sim.m.blocks.l2bm.iter_mut().enumerate() {
        words.copy_from_slice(&l2_host[b * L2BM_LONGS..(b + 1) * L2BM_LONGS]);
    }

    let cpu_start = Instant::now();
    sim.run(&cpu_lines).unwrap_or_else(|e| {
        eprintln!("CPU run failed at line {}: {}", e.line, e.msg);
        std::process::exit(2);
    });
    let cpu_elapsed = cpu_start.elapsed();

    let gpu = match Gpu::new() {
        Ok(gpu) => gpu,
        Err(error) => {
            eprintln!("gpu unavailable: {error}");
            std::process::exit(2);
        }
    };
    let state = gpu
        .allocate_state_with_mv(dram_longs, scratch_longs)
        .unwrap_or_else(|e| {
            eprintln!("allocate state: {e}");
            std::process::exit(2);
        });
    for (what, result) in [
        ("pdm", gpu.upload_pdm(&state, &pdm_host)),
        ("dram", gpu.upload_dram(&state, &dram_host)),
        ("l1bm", gpu.upload_l1bm(&state, &l1_host)),
        ("l2bm", gpu.upload_l2bm(&state, &l2_host)),
    ] {
        if let Err(error) = result {
            eprintln!("upload {what}: {error}");
            std::process::exit(2);
        }
    }
    let gpu_start = Instant::now();
    for (i, line) in gpu_lines.iter().enumerate() {
        if let Err(error) = gpu.run_mv_line(&state, line) {
            eprintln!("GPU MV line {} (`{}`): {error}", i + 1, texts[i]);
            std::process::exit(2);
        }
    }
    if let Err(error) = gpu.sync() {
        eprintln!("gpu sync: {error}");
        std::process::exit(2);
    }
    let gpu_elapsed = gpu_start.elapsed();

    let out_pdm = gpu.download_pdm(&state).expect("download pdm");
    let out_dram = gpu.download_dram(&state).expect("download dram");
    let out_l1 = gpu.download_l1bm(&state).expect("download l1bm");
    let out_l2 = gpu.download_l2bm(&state).expect("download l2bm");

    let mut pdm_mismatches = 0usize;
    for g in 0..GROUPS {
        for a in 0..PDM_LONGS as usize {
            let cpu = sim.off.pdm[g].get(a as u64);
            let gpu = out_pdm[g * PDM_LONGS as usize + a];
            if cpu != gpu {
                if pdm_mismatches == 0 {
                    println!(
                        "pdm first mismatch at group {g} addr {a}: cpu {cpu:016x} gpu {gpu:016x}"
                    );
                }
                pdm_mismatches += 1;
            }
        }
    }
    let mut dram_mismatches = 0usize;
    for g in 0..GROUPS {
        for a in 0..dram_longs as usize {
            let cpu = sim.off.dram[g].get(a as u64);
            let gpu = out_dram[g * dram_longs as usize + a];
            if cpu != gpu {
                if dram_mismatches == 0 {
                    println!(
                        "dram first mismatch at group {g} addr {a}: cpu {cpu:016x} gpu {gpu:016x}"
                    );
                }
                dram_mismatches += 1;
            }
        }
    }
    let mut l1_mismatches = 0usize;
    for b in 0..L1BS {
        for a in 0..L1BM_LONGS {
            let cpu = sim.m.blocks.l1bm[b][a];
            let gpu = out_l1[b * L1BM_LONGS + a];
            if cpu != gpu {
                if l1_mismatches == 0 {
                    println!(
                        "l1bm first mismatch at l1b {b} addr {a}: cpu {cpu:016x} gpu {gpu:016x}"
                    );
                }
                l1_mismatches += 1;
            }
        }
    }
    let mut l2_mismatches = 0usize;
    for b in 0..L2BS {
        for a in 0..L2BM_LONGS {
            let cpu = sim.m.blocks.l2bm[b][a];
            let gpu = out_l2[b * L2BM_LONGS + a];
            if cpu != gpu {
                if l2_mismatches == 0 {
                    println!(
                        "l2bm first mismatch at l2 {b} addr {a}: cpu {cpu:016x} gpu {gpu:016x}"
                    );
                }
                l2_mismatches += 1;
            }
        }
    }
    let mismatches = pdm_mismatches + dram_mismatches + l1_mismatches + l2_mismatches;

    println!("mode: {label}");
    println!(
        "MV lines: {} compared, {skipped} unsupported",
        gpu_lines.len()
    );
    println!(
        "device state: DRAM {dram_longs} long words/group, PDM {PDM_LONGS}, scratch {scratch_longs}"
    );
    println!("cpu: {cpu_elapsed:?}, gpu: {gpu_elapsed:?}");
    println!(
        "mismatches: pdm {pdm_mismatches}, dram {dram_mismatches}, l1bm {l1_mismatches}, l2bm {l2_mismatches}"
    );
    if mismatches != 0 {
        std::process::exit(1);
    }
    if skipped != 0 {
        std::process::exit(3);
    }
}
