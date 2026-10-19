//! Runs gmread followed by gbfn $mreadf and compares PE memory.

use mncore_sim::gpu::{
    bfn_line_from_expr, mat_read_line_from_expr, BfnLine, Gpu, MatReadLine, MAT_WORDS,
};
use mncore_sim::machine::{GRF_WORDS, LM_WORDS, MaskState, PES};
use mncore_sim::run::Sim;
use mncore_sim::vsm::{self, Line};

enum Action {
    MatRead(MatReadLine),
    Bfn(BfnLine),
}

fn main() {
    let lines: usize = std::env::args()
        .nth(1)
        .and_then(|s| s.parse().ok())
        .unwrap_or(100);
    let mut text = String::new();
    for i in 0..lines {
        let off = (i % 8) * 4;
        text.push_str(&format!("gmread $lx{} $lr{}v\n", off, off));
        text.push_str("gbfn $mreadf $nowrite\n");
    }
    let program = vsm::parse(&text).expect("parse");
    let mut actions = Vec::new();
    for (_, line) in &program {
        let Line::Pe(exprs) = line else {
            panic!("expected PE line");
        };
        let expr = &exprs[0];
        if let Some(line) = mat_read_line_from_expr(expr, MaskState::default()) {
            actions.push(Action::MatRead(line));
        } else if let Some(line) = bfn_line_from_expr(expr) {
            actions.push(Action::Bfn(line));
        } else {
            eprintln!("unsupported: {expr:?}");
            std::process::exit(1);
        }
    }

    let mut seed = 0x1357_9bdf_2468_ace0u64;
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
    let mats: Vec<u32> = (0..MAT_WORDS).map(|_| next() as u32).collect();

    let mut sim = Sim::new();
    sim.m.mem.lm0.copy_from_slice(&lm0);
    sim.m.mem.lm1.copy_from_slice(&lm1);
    sim.m.mem.grf0.copy_from_slice(&grf0);
    sim.m.mem.grf1.copy_from_slice(&grf1);
    for (mab, faces) in sim.m.mats.iter_mut().enumerate() {
        for (face, rows) in faces.iter_mut().enumerate() {
            for (row, words) in rows.iter_mut().enumerate() {
                for (w, value) in words.iter_mut().enumerate() {
                    let index = ((mab * 2 + face) * 16 + row) * 8 + w;
                    *value = mats[index];
                }
            }
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
    gpu.upload_mats(&state, &mats).expect("upload mats");
    let gpu_start = std::time::Instant::now();
    for action in &actions {
        match action {
            Action::MatRead(line) => gpu.run_mat_read_line(&state, line).expect("read"),
            Action::Bfn(line) => gpu.run_bfn_line(&state, line).expect("bfn"),
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
        "{} pairs, {} mismatches, cpu {:?}, gpu {:?}",
        lines, mismatches, cpu_elapsed, gpu_elapsed
    );
    if mismatches != 0 {
        std::process::exit(1);
    }
}
