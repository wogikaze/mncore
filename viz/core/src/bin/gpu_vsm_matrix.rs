//! Runs VSM matrix-register lines (gmwrite/gmread/gmmul) on the CPU
//! simulator and the GPU, then compares the matrix registers and the four PE
//! memories.
//!
//! Usage: gpu_vsm_matrix [rounds]

use mncore_sim::gpu::{
    alu_line_from_expr, mat_mau_line_from_expr, mat_read_line_from_expr,
    mat_write_line_from_expr, AluLine, Gpu, MatMauLine, MatReadLine, MatWriteLine, MAT_WORDS,
};
use mncore_sim::machine::{MaskState, GRF_WORDS, LM_WORDS, PES};
use mncore_sim::run::Sim;
use mncore_sim::vsm::{self, Line};

enum Action {
    Alu(AluLine),
    Write(MatWriteLine),
    Read(MatReadLine),
    Mau(MatMauLine),
}

fn flat_mats(mats: &[[[[u32; 8]; 16]; 2]]) -> Vec<u32> {
    mats.iter()
        .flat_map(|faces| faces.iter())
        .flat_map(|face| face.iter())
        .flat_map(|row| row.iter().copied())
        .collect()
}

fn main() {
    let rounds: usize = std::env::args()
        .nth(1)
        .and_then(|s| s.parse().ok())
        .unwrap_or(100);
    // One round exercises both faces, both precisions, memory and forwarding
    // sources, negation, and the three matrix operations.
    let mut text = String::new();
    for i in 0..rounds {
        let off = (i % 8) * 8;
        let off2 = off + 8;
        let dst = 256 + (i % 16) * 8;
        let row = i % 8;
        let next = (row + 1) % 8;
        text.push_str(&format!("fpassa $lr{off}v $lm{dst}v\n"));
        text.push_str(&format!("gmwrite $aluf $ly{row}\n"));
        text.push_str(&format!("fpassa $lr{off2}v $lm{dst}v\n"));
        text.push_str(&format!("gmmul $ly $aluf $ln{}v4\n", dst + 8));
        text.push_str(&format!(
            "gmfma $ly $lr{off}v $ls{off2}v $ln{}v4\n",
            dst + 16
        ));
        text.push_str(&format!("fpassa $lr{off}v $lm{dst}v\n"));
        text.push_str(&format!("fmmul $lx $aluf $lm{}v4\n", dst + 24));
        text.push_str(&format!("gmwrite $llr{off}v $ly{next}\n"));
        text.push_str(&format!("gmread $ly{row} $ln{dst}v4\n"));
        text.push_str(&format!("gmread $ly{row} $nowrite\n"));
        text.push_str(&format!("fmwrite -$lr{off}v $lx{row}\n"));
        text.push_str(&format!("fmread $lx{row} $r{dst}v4\n"));
        text.push_str(&format!(
            "fmfma $lx $lr{off}v $ls{off2}v $ln{}v4\n",
            dst + 32
        ));
    }
    let program = vsm::parse(&text).expect("parse");
    let mut actions = Vec::new();
    for (_, line) in &program {
        let Line::Pe(exprs) = line else {
            panic!("expected a PE line");
        };
        if exprs.len() != 1 {
            panic!("expected one expression per line");
        }
        let expr = &exprs[0];
        if let Some(line) = alu_line_from_expr(expr) {
            actions.push(Action::Alu(line));
        } else if let Some(line) = mat_write_line_from_expr(expr) {
            actions.push(Action::Write(line));
        } else if let Some(line) = mat_read_line_from_expr(expr, MaskState::default()) {
            actions.push(Action::Read(line));
        } else if let Some(line) = mat_mau_line_from_expr(expr, MaskState::default()) {
            actions.push(Action::Mau(line));
        } else {
            eprintln!("unsupported: {:?} {:?}", expr.op, expr);
            std::process::exit(1);
        }
    }

    let mut seed = 0x6d61_7472_6978_0001u64;
    let mut next = || {
        seed ^= seed << 13;
        seed ^= seed >> 7;
        seed ^= seed << 17;
        seed
    };
    // Values used by the matrix unit must share one block-float exponent within
    // each block. Keep every 8-word block on one exponent and vary the exponent
    // between blocks so the matrix adder sees different grids, zero blocks and
    // infinity blocks.
    let block_exponent = |block: usize| -> u32 {
        match block % 6 {
            0 => 0,
            1 => 255,
            2 => 126,
            3 => 127,
            4 => 128,
            _ => 125,
        }
    };
    let matrix_value = |next: &mut dyn FnMut() -> u64, exponent: u32| {
        (next() as u32 & 0x807f_ffff) | (exponent << 23)
    };
    let lm_len = PES * LM_WORDS;
    let grf_len = PES * GRF_WORDS;
    let lm0: Vec<u32> = (0..lm_len).map(|_| next() as u32).collect();
    let lm1: Vec<u32> = (0..lm_len).map(|_| next() as u32).collect();
    let grf0: Vec<u32> = (0..grf_len)
        .map(|i| matrix_value(&mut next, block_exponent((i % GRF_WORDS) / 8)))
        .collect();
    let grf1: Vec<u32> = (0..grf_len)
        .map(|i| matrix_value(&mut next, block_exponent((i % GRF_WORDS) / 8)))
        .collect();
    let mut mats = vec![0u32; MAT_WORDS];
    for (i, value) in mats.iter_mut().enumerate() {
        // The exponent of one physical row is what the matrix unit pairs.
        *value = matrix_value(&mut next, block_exponent((i / 8) % 16));
    }

    let mut sim = Sim::new();
    sim.m.mem.lm0.copy_from_slice(&lm0);
    sim.m.mem.lm1.copy_from_slice(&lm1);
    sim.m.mem.grf0.copy_from_slice(&grf0);
    sim.m.mem.grf1.copy_from_slice(&grf1);
    for mab in 0..PES / 4 {
        for side in 0..2 {
            for row in 0..16 {
                for word in 0..8 {
                    let index = ((mab * 2 + side) * 16 + row) * 8 + word;
                    sim.m.mats[mab][side][row][word] = mats[index];
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
    let state = gpu.allocate_state().expect("allocate state");
    gpu.upload_state(&state, &lm0, &lm1, &grf0, &grf1)
        .expect("upload state");
    gpu.upload_mats(&state, &mats).expect("upload mats");
    let gpu_start = std::time::Instant::now();
    for action in &actions {
        match action {
            Action::Alu(line) => gpu.run_alu_line(&state, line).expect("alu"),
            Action::Write(line) => gpu.run_mat_write_line(&state, line).expect("mat write"),
            Action::Read(line) => gpu.run_mat_read_line(&state, line).expect("mat read"),
            Action::Mau(line) => gpu.run_mat_mau_line(&state, line).expect("mat mau"),
        }
    }
    gpu.sync().expect("sync");
    let gpu_elapsed = gpu_start.elapsed();

    let cpu_mats = flat_mats(&sim.m.mats);
    let gpu_mats = gpu.download_mats(&state).expect("download mats");
    let mut out_lm0 = vec![0u32; lm_len];
    let mut out_lm1 = vec![0u32; lm_len];
    let mut out_grf0 = vec![0u32; grf_len];
    let mut out_grf1 = vec![0u32; grf_len];
    gpu.download_state(&state, &mut out_lm0, &mut out_lm1, &mut out_grf0, &mut out_grf1)
        .expect("download state");

    let mut mismatches = 0usize;
    if let Some(index) = cpu_mats.iter().zip(&gpu_mats).position(|(a, b)| a != b) {
        let mab = index / (2 * 16 * 8);
        let rest = index % (2 * 16 * 8);
        let side = rest / (16 * 8);
        let row = (rest % (16 * 8)) / 8;
        let word = rest % 8;
        println!(
            "mats first mismatch at mab {mab} face {} row {row} word {word}: cpu {:08x} gpu {:08x}",
            if side == 0 { 'x' } else { 'y' },
            cpu_mats[index],
            gpu_mats[index]
        );
        mismatches += cpu_mats
            .iter()
            .zip(&gpu_mats)
            .filter(|(a, b)| a != b)
            .count();
    }
    for (name, cpu, gpu, width) in [
        ("lm0", sim.m.mem.lm0.as_slice(), out_lm0.as_slice(), LM_WORDS),
        ("lm1", sim.m.mem.lm1.as_slice(), out_lm1.as_slice(), LM_WORDS),
        ("grf0", sim.m.mem.grf0.as_slice(), out_grf0.as_slice(), GRF_WORDS),
        ("grf1", sim.m.mem.grf1.as_slice(), out_grf1.as_slice(), GRF_WORDS),
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
        program.len(),
        mismatches,
        cpu_elapsed,
        gpu_elapsed
    );
    if mismatches != 0 {
        std::process::exit(1);
    }
}
