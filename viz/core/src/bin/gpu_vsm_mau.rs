//! Runs a VSM program made of simple f32 MAU lines on the CPU simulator and
//! on the GPU, then compares the four PE memories.
//!
//! Usage: gpu_vsm_mau [lines]

use mncore_sim::gpu::{Gpu, MauLine, MauSrc};
use mncore_sim::machine::{GRF_WORDS, LM_WORDS, PES};
use mncore_sim::run::Sim;
use mncore_sim::vsm::{self, Expr, Line, MauKind, MemKind, Op, Operand, Prec};

fn mem_source(op: &Operand, wl: u8) -> Option<MauSrc> {
    let Operand::Mem {
        mem,
        wl: op_wl,
        addr,
        neg,
        ext,
        rnd,
        mask,
    } = op
    else {
        return None;
    };
    if *op_wl != wl || *neg || *ext || *rnd || mask.is_some() {
        return None;
    }
    if addr.t_indirect || addr.madpe.is_some() {
        return None;
    }
    let mem = match mem {
        MemKind::Lm0 => 0,
        MemKind::Lm1 => 1,
        MemKind::Grf0 => 2,
        MemKind::Grf1 => 3,
        _ => return None,
    };
    Some(MauSrc {
        mem,
        base: addr.cycles.map(|c| c & !(wl as u32 - 1)),
    })
}

fn source(op: &Operand, wl: u8) -> Option<MauSrc> {
    if let Operand::Forward {
        kind: mncore_sim::vsm::FwdKind::Mauf,
        neg: false,
        ext: false,
        rnd: false,
    } = op
    {
        return Some(MauSrc {
            mem: 4,
            base: [0; 4],
        });
    }
    mem_source(op, wl)
}

fn descriptor(expr: &Expr) -> Option<MauLine> {
    let Op::Mau {
        prec: Prec::F,
        matrix: false,
        kind,
        half: None,
        round: false,
    } = &expr.op
    else {
        return None;
    };
    if expr.flush.is_some() || expr.dsts.len() != 1 {
        return None;
    }
    let Operand::Mem { wl, .. } = &expr.dsts[0] else {
        return None;
    };
    if *wl != 1 && *wl != 2 {
        return None;
    }
    let wl = *wl;
    let zero = MauSrc {
        mem: 0,
        base: [0; 4],
    };
    let kind = match kind {
        MauKind::Fma => 0,
        MauKind::Mul => 1,
        MauKind::Add => 2,
        MauKind::Passa => 3,
    };
    let a = source(expr.srcs.first()?, wl)?;
    let (b, c) = match kind {
        0 => (source(expr.srcs.get(1)?, wl)?, source(expr.srcs.get(2)?, wl)?),
        1 => (source(expr.srcs.get(1)?, wl)?, zero),
        2 => (zero, source(expr.srcs.get(1)?, wl)?),
        _ => (zero, zero),
    };
    let dst = mem_source(&expr.dsts[0], wl)?;
    Some(MauLine {
        kind,
        wl,
        a,
        b,
        c,
        dst,
    })
}

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
        match descriptor(&exprs[0]) {
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
