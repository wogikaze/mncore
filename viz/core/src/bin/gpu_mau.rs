//! Runs f32 MAU lines on the CPU and the GPU and compares the whole PE memory.
//!
//! Usage: gpu_mau [lines]

use mncore_sim::float::{self, SINGLE};
use mncore_sim::gpu::{AluDstDesc, AluSrc, Gpu, MauLine};
use mncore_sim::machine::{GRF_WORDS, LM_WORDS, PES};

fn mem_len(mem: u8) -> usize {
    if mem < 2 {
        LM_WORDS
    } else {
        GRF_WORDS
    }
}

fn get(mem: u8, pe: usize, addr: usize, lm0: &[u32], lm1: &[u32], grf0: &[u32], grf1: &[u32]) -> u32 {
    match mem {
        0 => lm0[pe * LM_WORDS + addr],
        1 => lm1[pe * LM_WORDS + addr],
        2 => grf0[pe * GRF_WORDS + addr],
        _ => grf1[pe * GRF_WORDS + addr],
    }
}

fn set(
    mem: u8,
    pe: usize,
    addr: usize,
    value: u32,
    lm0: &mut [u32],
    lm1: &mut [u32],
    grf0: &mut [u32],
    grf1: &mut [u32],
) {
    match mem {
        0 => lm0[pe * LM_WORDS + addr] = value,
        1 => lm1[pe * LM_WORDS + addr] = value,
        2 => grf0[pe * GRF_WORDS + addr] = value,
        _ => grf1[pe * GRF_WORDS + addr] = value,
    }
}

fn cpu_line(
    line: &MauLine,
    lm0: &mut [u32],
    lm1: &mut [u32],
    grf0: &mut [u32],
    grf1: &mut [u32],
) {
    let zero = float::Val::Zero { neg: false };
    let one = (SINGLE.bias() as u32) << SINGLE.man_bits;
    let mut values = [[0u32; 4]; 2];
    for pe in 0..PES {
        for c in 0..4 {
            for l in 0..2 {
                let a = get(
                    line.a.mem as u8,
                    pe,
                    line.a.base[c] as usize + l,
                    lm0,
                    lm1,
                    grf0,
                    grf1,
                );
                let (b, cc) = match line.kind {
                    0 => (
                        get(line.b.mem as u8, pe, line.b.base[c] as usize + l, lm0, lm1, grf0, grf1),
                        get(line.c.mem as u8, pe, line.c.base[c] as usize + l, lm0, lm1, grf0, grf1),
                    ),
                    1 => (
                        get(line.b.mem as u8, pe, line.b.base[c] as usize + l, lm0, lm1, grf0, grf1),
                        0,
                    ),
                    2 => (
                        one,
                        get(line.c.mem as u8, pe, line.c.base[c] as usize + l, lm0, lm1, grf0, grf1),
                    ),
                    _ => (one, 0),
                };
                let va = float::decode(SINGLE, a as u64);
                let vb = if b == 0 { zero } else { float::decode(SINGLE, b as u64) };
                let vc = if cc == 0 { zero } else { float::decode(SINGLE, cc as u64) };
                values[l][c] = float::vfma(SINGLE, SINGLE, va, vb, vc) as u32;
            }
        }
        for c in 0..4 {
            for l in 0..2 {
                set(
                    line.dst[0].mem as u8,
                    pe,
                    line.dst[0].base[c] as usize + l,
                    values[l][c],
                    lm0,
                    lm1,
                    grf0,
                    grf1,
                );
            }
        }
    }
}

fn make_src(next: &mut impl FnMut() -> u64, mem: u8) -> AluSrc {
    let len = mem_len(mem);
    let max = (len - 8) / 2;
    let base = ((next() as usize) % (max + 1)) * 2;
    AluSrc {
        mem: mem as u32,
        wl: 2,
        base: [base as u32, (base + 2) as u32, (base + 4) as u32, (base + 6) as u32],
        ..AluSrc::default()
    }
}

fn main() {
    let lines: usize = std::env::args()
        .nth(1)
        .and_then(|s| s.parse().ok())
        .unwrap_or(200);
    let mut state = 0x9e37_79b9_7f4a_7c15u64;
    let mut next = || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state
    };
    let lm_len = PES * LM_WORDS;
    let grf_len = PES * GRF_WORDS;
    let mut lm0: Vec<u32> = (0..lm_len).map(|_| next() as u32).collect();
    let mut lm1: Vec<u32> = (0..lm_len).map(|_| next() as u32).collect();
    let mut grf0: Vec<u32> = (0..grf_len).map(|_| next() as u32).collect();
    let mut grf1: Vec<u32> = (0..grf_len).map(|_| next() as u32).collect();
    let gpu_lm0 = lm0.clone();
    let gpu_lm1 = lm1.clone();
    let gpu_grf0 = grf0.clone();
    let gpu_grf1 = grf1.clone();

    let mut program = Vec::with_capacity(lines);
    for _ in 0..lines {
        let am = (next() % 4) as u8;
        let a = make_src(&mut next, am);
        let bm = (next() % 4) as u8;
        let b = make_src(&mut next, bm);
        let cm = (next() % 4) as u8;
        let c = make_src(&mut next, cm);
        let dm = (next() % 4) as u8;
        let dst = make_src(&mut next, dm);
        let mut line = MauLine {
            prec: 1,
            kind: (next() % 4) as u32,
            half: 0,
            round: 0,
            a,
            b,
            c,
            ndst: 1,
            dst: [AluDstDesc::default(); 16],
            flush_kind: 0,
            flush_entry: 0,
            flush_pattern: 0,
            flush_ll: 0,
        };
        line.dst[0] = AluDstDesc {
            kind: 0,
            mem: dst.mem,
            wl: dst.wl,
            base: dst.base,
            ..AluDstDesc::default()
        };
        program.push(line);
    }

    let cpu_start = std::time::Instant::now();
    for line in &program {
        cpu_line(line, &mut lm0, &mut lm1, &mut grf0, &mut grf1);
    }
    let cpu_elapsed = cpu_start.elapsed();

    let gpu = match Gpu::new() {
        Ok(gpu) => gpu,
        Err(error) => {
            eprintln!("gpu unavailable: {error}");
            std::process::exit(2);
        }
    };
    let state = gpu.allocate_state().expect("allocate state");
    gpu.upload_state(&state, &gpu_lm0, &gpu_lm1, &gpu_grf0, &gpu_grf1)
        .expect("upload");
    let gpu_start = std::time::Instant::now();
    for line in &program {
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
    for (name, cpu, gpu) in [
        ("lm0", &lm0, &out_lm0),
        ("lm1", &lm1, &out_lm1),
        ("grf0", &grf0, &out_grf0),
        ("grf1", &grf1, &out_grf1),
    ] {
        let first = cpu.iter().zip(gpu).position(|(a, b)| a != b);
        if let Some(index) = first {
            let pe = index / if name.starts_with("grf") { GRF_WORDS } else { LM_WORDS };
            let addr = index % if name.starts_with("grf") { GRF_WORDS } else { LM_WORDS };
            println!(
                "{name}: first mismatch at pe {pe} addr {addr}: cpu {:08x} gpu {:08x}",
                cpu[index], gpu[index]
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
