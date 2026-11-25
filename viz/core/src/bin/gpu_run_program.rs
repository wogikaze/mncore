//! Runs a whole VSM program on the GPU and compares the final state with Sim.
//!
//! Usage: gpu_run_program [program.vsm] [--engine jit|program|lines] [--replay N]
//!
//! `program` (default) runs the whole program as one interpreter launch;
//! `lines` launches one kernel per operation (`GPU_PROFILE=1` times them).

use mncore_sim::blocks::{L1BM_LONGS, L1BS, L2BM_LONGS, L2BS};
use mncore_sim::gpu::{
    lower_program, Gpu, GpuOp, MAT_WORDS, PROGRAM_FLAG_BARRIER, PROGRAM_KIND_NAMES,
};
use mncore_sim::machine::{GRF_WORDS, LM_WORDS, PES};
use mncore_sim::run::Sim;
use mncore_sim::vsm;

fn path_display(p: &str) -> String {
    p.to_string()
}

fn op_name(op: &GpuOp) -> &'static str {
    match op {
        GpuOp::Alu(..) => "alu_line",
        GpuOp::Bfn(..) => "bfn_line",
        GpuOp::Mau(..) => "mau_line",
        GpuOp::L1Read(..) => "l1_read_line",
        GpuOp::L1Write(..) => "l1_write_line",
        GpuOp::L2(..) => "l2_line",
        GpuOp::L2Red(..) => "l2_reduce_line",
        GpuOp::MatWrite(..) => "mat_write_line",
        GpuOp::MatRead(..) => "mat_read_line",
        GpuOp::MatMau(..) => "mat_mau_line",
        GpuOp::Mv(..) => "mv",
        GpuOp::ClearMreadf => "clear_mreadf",
    }
}

fn main() {
    let mut cli = std::env::args().skip(1);
    let mut path = "benchmarks/mnist_train_step.vsm".to_string();
    let mut replay: Option<u32> = None;
    let mut engine = "program".to_string();
    while let Some(arg) = cli.next() {
        match arg.as_str() {
            "--replay" => replay = Some(cli.next().and_then(|n| n.parse().ok()).unwrap_or(1)),
            "--engine" => engine = cli.next().expect("--engine jit|program|lines"),
            other => path = other.to_string(),
        }
    }
    let source = std::fs::read_to_string(&path).expect("read");
    let path_of_program = path.clone();
    let program = vsm::parse(&source).expect("parse");
    let lowered = match lower_program(&program) {
        Ok(l) => l,
        Err(error) => {
            eprintln!("{error}");
            std::process::exit(3);
        }
    };
    let (dram_longs, scratch_longs) = (lowered.dram_longs, lowered.scratch_longs);
    eprintln!(
        "mv capacity: dram_longs={dram_longs}, scratch={scratch_longs}, indirect={}",
        lowered.indirect
    );

    let gpu = match Gpu::new() {
        Ok(gpu) => gpu,
        Err(error) => {
            eprintln!("gpu unavailable: {error}");
            std::process::exit(2);
        }
    };
    let state = gpu
        .allocate_state_with_mv(dram_longs, scratch_longs)
        .expect("allocate");
    let lm = vec![0u32; PES * LM_WORDS];
    let grf = vec![0u32; PES * GRF_WORDS];
    gpu.upload_state(&state, &lm, &lm, &grf, &grf).expect("state");
    gpu.upload_mats(&state, &vec![0u32; MAT_WORDS]).expect("mats");
    gpu.upload_l1bm(&state, &vec![0u64; L1BS * L1BM_LONGS]).expect("l1");
    gpu.upload_l2bm(&state, &vec![0u64; L2BS * L2BM_LONGS]).expect("l2");
    if dram_longs > 0 {
        let pdm = vec![0u64; (mncore_sim::mv::GROUPS as u64 * mncore_sim::mv::PDM_LONGS) as usize];
        gpu.upload_pdm(&state, &pdm).expect("pdm");
        let dram = vec![0u64; (mncore_sim::mv::GROUPS as u64 * dram_longs) as usize];
        gpu.upload_dram(&state, &dram).expect("dram");
        for (group, addr, payload) in &lowered.dram_init {
            gpu.upload_dram_at(&state, *group, *addr, payload).expect("dram records");
        }
    }
    let pe_lines = lowered.pe_lines;
    let words = lowered.words;

    let mut graph = None;
    let mut loaded = None;
    let start = std::time::Instant::now();
    let mut jit = None;
    if engine == "jit" {
        let prog = gpu.compile_program(&state, &lowered.ops, words).expect("compile program");
        let (regs, local) = gpu.jit_resources(&prog);
        eprintln!(
            "jit: {} words, {} ops ({} direct, {} shapes), {} grid barriers, nvrtc {:.1} s, {regs} registers, {local} local bytes",
            words, prog.ops, prog.direct, prog.shapes, prog.barriers, prog.compile_seconds
        );
        gpu.launch_jit(&state, &prog).expect("launch jit");
        gpu.sync().expect("sync");
        if let Ok(path) = std::env::var("GPU_TIMELINE") {
            // Warm the GPU clocks up first, as a replay would.
            for _ in 0..300 {
                gpu.launch_jit(&state, &prog).expect("warm-up");
            }
            gpu.sync().expect("sync warm-up");
            let tl = gpu.timeline_jit(&state, &prog, 8).expect("timeline");
            let lines: Vec<&str> = source.lines().collect();
            let esc = |t: &str| t.replace('\\', "\\\\").replace('"', "\\\"");
            let mut out = String::new();
            out.push_str(&format!(
                "{{\"program\":\"{}\",\"words\":{},\"block\":{},\"ghz\":{:.4},\"ops\":[\n",
                esc(&path_display(&path_of_program)),
                words,
                tl.block,
                tl.ghz
            ));
            for (i, op) in tl.ops.iter().enumerate() {
                let line = lowered.op_lines.get(op.src_op).copied().unwrap_or(0);
                let text = if line > 0 { lines.get(line - 1).copied().unwrap_or("").trim() } else { "(final mreadf clear)" };
                let us = |c: u64| c as f64 / tl.ghz / 1000.0;
                out.push_str(&format!(
                    "{}{{\"i\":{i},\"kind\":\"{}\",\"direct\":{},\"barrier\":{},\"line\":{line},\"text\":\"{}\",\"start\":{:.4},\"ready\":{:.4},\"end\":{:.4}}}\n",
                    if i == 0 { "" } else { "," },
                    PROGRAM_KIND_NAMES[op.kind as usize],
                    op.direct,
                    op.barrier,
                    esc(text),
                    us(op.start),
                    us(op.ready),
                    us(op.end)
                ));
            }
            out.push_str("]}\n");
            std::fs::write(&path, out).expect("write timeline");
            eprintln!("timeline of block {} ({:.3} GHz) written to {path}", tl.block, tl.ghz);
        }
        if std::env::var("GPU_PROFILE").is_ok() {
            let rows = gpu.profile_jit(&state, &prog).expect("profile");
            if let Some(top) = std::env::var("GPU_PROFILE_TOP").ok().and_then(|v| v.parse::<usize>().ok()) {
                let mut idx: Vec<usize> = (0..rows.len()).collect();
                idx.sort_by_key(|&i| std::cmp::Reverse(rows[i].3));
                for &i in idx.iter().take(top) {
                    let (kind, flags, direct, cyc) = rows[i];
                    eprintln!(
                        "op {i:5}: {:>12}{}{} {:8.2} us",
                        PROGRAM_KIND_NAMES[kind as usize],
                        if direct { "/direct" } else { "" },
                        if flags & PROGRAM_FLAG_BARRIER != 0 { "+bar" } else { "" },
                        cyc as f64 / 1.9e3
                    );
                }
            }
            let mut totals: std::collections::BTreeMap<String, (usize, u64)> = Default::default();
            for (kind, flags, direct, cyc) in rows {
                let mut name = PROGRAM_KIND_NAMES[kind as usize].to_string();
                if direct {
                    name.push_str("/direct");
                }
                if flags & PROGRAM_FLAG_BARRIER != 0 {
                    name.push_str("+bar");
                }
                let e = totals.entry(name).or_default();
                e.0 += 1;
                e.1 += cyc;
            }
            let sum: u64 = totals.values().map(|v| v.1).sum();
            for (name, (count, cyc)) in &totals {
                eprintln!(
                    "{name:>18}: {count:5} ops, {:8.3} ms, {:8.2} us/op, {:5.1}% (1.9 GHz)",
                    *cyc as f64 / 1.9e6,
                    *cyc as f64 / 1.9e3 / *count as f64,
                    *cyc as f64 / sum as f64 * 100.0
                );
            }
            eprintln!("{:>18}: {:.3} ms", "total", sum as f64 / 1.9e6);
        }
        jit = Some(prog);
    } else if engine == "program" {
        let prog = gpu.load_program(&state, &lowered.ops, words).expect("load program");
        eprintln!(
            "program: {} words, {} ops, {} grid barriers",
            words, prog.ops, prog.barriers
        );
        let (regs, local, shared) = gpu.program_kernel_resources();
        eprintln!("run_program: {regs} registers, {local} local bytes, {shared} shared bytes per block");
        gpu.launch_program(&state, &prog).expect("launch program");
        gpu.sync().expect("sync");
        if std::env::var("GPU_PROFILE").is_ok() {
            // Profile a later run of the same program (the state keeps evolving,
            // which only affects data, not the instruction mix).
            let rows = gpu.profile_program(&state, &prog).expect("profile");
            let mut totals: std::collections::BTreeMap<String, (usize, u64)> = Default::default();
            for (kind, flags, ns) in rows {
                let mut name = PROGRAM_KIND_NAMES[kind as usize].to_string();
                if flags & PROGRAM_FLAG_BARRIER != 0 {
                    name.push_str("+bar");
                }
                let e = totals.entry(name).or_default();
                e.0 += 1;
                e.1 += ns;
            }
            let sum: u64 = totals.values().map(|v| v.1).sum();
            for (name, (count, ns)) in &totals {
                eprintln!(
                    "{name:>16}: {count:5} ins, {:9.3} ms, {:8.2} us/ins, {:5.1}% (1.9 GHz)",
                    *ns as f64 / 1.9e6,
                    *ns as f64 / 1.9e3 / *count as f64,
                    *ns as f64 / sum as f64 * 100.0
                );
            }
            eprintln!("{:>16}: {:.3} ms (sum of per-instruction worst blocks)", "total", sum as f64 / 1.9e6);
        }
        loaded = Some(prog);
    } else {
        let profile = std::env::var("GPU_PROFILE").is_ok();
        let mut marks: Vec<(&'static str, *mut std::ffi::c_void)> = Vec::new();
        if replay.is_some() {
            gpu.sync().expect("sync before capture");
            gpu.begin_capture().expect("begin capture");
        }
        for op in &lowered.ops {
            if profile {
                let event = gpu.event_create().expect("event");
                gpu.event_record(event).expect("record");
                marks.push((op_name(op), event));
            }
            gpu.run_op(&state, op).expect("run op");
        }
        if profile {
            let event = gpu.event_create().expect("event");
            gpu.event_record(event).expect("record");
            marks.push(("end", event));
        }
        if replay.is_some() {
            let g = gpu.end_capture().expect("end capture");
            let exec = gpu.instantiate_graph(g).expect("instantiate graph");
            gpu.launch_graph(exec).expect("graph launch");
            graph = Some((g, exec));
        }
        gpu.sync().expect("sync");
        if profile {
            let mut totals: std::collections::BTreeMap<&str, (usize, f64)> = Default::default();
            for pair in marks.windows(2) {
                let ms = gpu.event_elapsed_ms(pair[0].1, pair[1].1).expect("elapsed") as f64;
                let entry = totals.entry(pair[0].0).or_default();
                entry.0 += 1;
                entry.1 += ms;
            }
            let sum: f64 = totals.values().map(|v| v.1).sum();
            for (label, (count, ms)) in &totals {
                eprintln!(
                    "{label:>14}: {count:5} launches, {ms:9.3} ms, {:7.2} us/launch, {:5.1}%",
                    ms * 1000.0 / *count as f64,
                    ms / sum * 100.0
                );
            }
            eprintln!("{:>14}: {sum:.3} ms", "total");
        }
    }
    let gpu_elapsed = start.elapsed();
    let mv_errors = gpu.download_mv_errors(&state).expect("mv errors");
    if mv_errors != 0 {
        println!("{mv_errors} indirect MV accesses fell outside the device DRAM");
    }

    let cpu_start = std::time::Instant::now();
    let mut sim = Sim::new();
    sim.run(&program).expect("cpu run");
    let cpu_elapsed = cpu_start.elapsed();

    if let Ok(pv) = std::env::var("DUMP_PE") {
        if let Ok(pe) = pv.parse::<usize>() {
            eprintln!("cpu grf0 pe{pe}: {:08x?}", &sim.m.mem.grf0[pe * GRF_WORDS..pe * GRF_WORDS + 16]);
            eprintln!("cpu grf1 pe{pe}: {:08x?}", &sim.m.mem.grf1[pe * GRF_WORDS..pe * GRF_WORDS + 16]);
            eprintln!("cpu mauf pe{pe}: {:08x?}", &sim.m.pes[pe].mauf);
        }
    }
    let mut out = (
        vec![0u32; PES * LM_WORDS],
        vec![0u32; PES * LM_WORDS],
        vec![0u32; PES * GRF_WORDS],
        vec![0u32; PES * GRF_WORDS],
    );
    gpu.download_state(&state, &mut out.0, &mut out.1, &mut out.2, &mut out.3)
        .expect("download");
    let mut bad = 0usize;
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
            bad += cpu.iter().zip(gpu).filter(|(a, b)| a != b).count();
        }
    }
    let mats = gpu.download_mats(&state).expect("mats");
    for mab in 0..PES / 4 {
        for face in 0..2 {
            for row in 0..16 {
                for w in 0..8 {
                    let idx = ((mab * 2 + face) * 16 + row) * 8 + w;
                    if sim.m.mats[mab][face][row][w] != mats[idx] {
                        println!("mats first mismatch mab {mab} face {face} row {row} word {w}");
                        bad += 1;
                    }
                }
            }
        }
    }
    let mask_out = gpu.download_mask(&state).expect("mask");
    for pe in 0..PES {
        for entry in 0..16 {
            if sim.m.pes[pe].mask[entry] as u32 != mask_out[pe * 16 + entry] {
                println!("mask first mismatch pe {pe} entry {entry}");
                bad += 1;
            }
        }
    }
    let l1 = gpu.download_l1bm(&state).expect("l1");
    for l1b in 0..L1BS {
        for addr in 0..L1BM_LONGS {
            if sim.m.blocks.l1bm[l1b][addr] != l1[l1b * L1BM_LONGS + addr] {
                println!("l1bm first mismatch l1b {l1b} addr {addr}");
                bad += 1;
            }
        }
    }
    let l2 = gpu.download_l2bm(&state).expect("l2");
    for l2b in 0..L2BS {
        for addr in 0..L2BM_LONGS {
            if sim.m.blocks.l2bm[l2b][addr] != l2[l2b * L2BM_LONGS + addr] {
                println!("l2bm first mismatch l2b {l2b} addr {addr}");
                bad += 1;
            }
        }
    }
    let (bar0, bar1) = gpu.download_bar(&state).expect("bar");
    for pe in 0..PES {
        if sim.m.pes[pe].bar0 != bar0[pe] {
            println!("bar0 first mismatch pe {pe}");
            bad += 1;
        }
        if sim.m.pes[pe].bar1 != bar1[pe] {
            println!("bar1 first mismatch pe {pe}");
            bad += 1;
        }
    }
    let lbi = gpu.download_l1bi(&state).expect("lbi");
    for l1b in 0..L1BS {
        for c in 0..4 {
            for o in 0..128 {
                if sim.m.blocks.lbi[l1b][c][o] != lbi[(l1b * 4 + c) * 128 + o] {
                    println!("lbi first mismatch l1b {l1b} cycle {c} offset {o}: cpu {:016x} gpu {:016x}", sim.m.blocks.lbi[l1b][c][o], lbi[(l1b * 4 + c) * 128 + o]);
                    bad += 1;
                    break;
                }
            }
        }
    }
    let dar = gpu.download_dar(&state).expect("dar");
    for g in 0..mncore_sim::mv::GROUPS {
        for e in 0..mncore_sim::blocks::DAR_ENTRIES {
            if sim.m.blocks.dar[g][e] != dar[g * mncore_sim::blocks::DAR_ENTRIES + e] {
                println!("dar first mismatch group {g} entry {e}");
                bad += 1;
                break;
            }
        }
    }
    let darbuf = gpu.download_darbuf(&state).expect("darbuf");
    for g in 0..mncore_sim::mv::GROUPS {
        for e in 0..mncore_sim::blocks::DARBUF_ENTRIES {
            if sim.m.blocks.darbuf[g][e] != darbuf[g * mncore_sim::blocks::DARBUF_ENTRIES + e] {
                println!("darbuf first mismatch group {g} entry {e}");
                bad += 1;
                break;
            }
        }
    }
    let dar_addr = gpu.download_dar_addr(&state).expect("dar addr");
    if [sim.m.blocks.darw_addr as u32, sim.m.blocks.darbuf_read_addr as u32] != dar_addr {
        println!("dar address mismatch");
        bad += 1;
    }
    let aluf = gpu.download_aluf(&state).expect("aluf");
    let mauf = gpu.download_mauf(&state).expect("mauf");
    let mreadf = gpu.download_mreadf(&state).expect("mreadf");
    let lbf = gpu.download_lbf(&state).expect("lbf");
    for pe in 0..PES {
        for c in 0..4 {
            for w in 0..4 {
                let i = pe * 16 + c * 4 + w;
                if sim.m.pes[pe].aluf[c][w] != aluf[i] {
                    println!("aluf first mismatch pe {pe} cycle {c} word {w}");
                    bad += 1;
                    break;
                }
                if sim.m.pes[pe].mauf[c][w] != mauf[i] {
                    println!("mauf first mismatch pe {pe} cycle {c} word {w}: cpu {:08x} gpu {:08x}", sim.m.pes[pe].mauf[c][w], mauf[i]);
                    bad += 1;
                    break;
                }
                if sim.m.pes[pe].mreadf[c][w] != mreadf[i] {
                    println!("mreadf first mismatch pe {pe} cycle {c} word {w}");
                    bad += 1;
                    break;
                }
                if sim.m.pes[pe].lbf[c][w] != lbf[i] {
                    println!("lbf first mismatch pe {pe} cycle {c} word {w}");
                    bad += 1;
                    break;
                }
            }
        }
    }
    if dram_longs > 0 {
        let pdm = gpu.download_pdm(&state).expect("pdm");
        for g in 0..mncore_sim::mv::GROUPS {
            for a in 0..mncore_sim::mv::PDM_LONGS {
                if sim.off.pdm[g].get(a) != pdm[(g as u64 * mncore_sim::mv::PDM_LONGS + a) as usize] {
                    println!("pdm first mismatch group {g} addr {a}");
                    bad += 1;
                    break;
                }
            }
        }
        let dram = gpu.download_dram(&state).expect("dram");
        for g in 0..mncore_sim::mv::GROUPS {
            for a in 0..dram_longs as usize {
                if sim.off.dram[g].get(a as u64) != dram[(g as u64 * dram_longs + a as u64) as usize] {
                    println!("dram first mismatch group {g} addr {a}");
                    bad += 1;
                    break;
                }
            }
        }
    }
    println!(
        "{} PE lines, {} mismatches, cpu {:?}, gpu {:?}",
        pe_lines, bad, cpu_elapsed, gpu_elapsed
    );
    if let Some(n) = replay {
        let replay_start = std::time::Instant::now();
        for _ in 0..n {
            if let Some(prog) = &jit {
                gpu.launch_jit(&state, prog).expect("jit replay");
            } else if let Some(prog) = &loaded {
                gpu.launch_program(&state, prog).expect("program replay");
            } else if let Some((_, exec)) = graph {
                gpu.launch_graph(exec).expect("graph replay");
            }
        }
        gpu.sync().expect("sync replay");
        let elapsed = replay_start.elapsed();
        let per_run = elapsed.as_secs_f64() / n as f64;
        println!(
            "{engine} replay: {} runs, {:?} total, {:.3} ms per run, {:.3} M words/s",
            n,
            elapsed,
            per_run * 1e3,
            words as f64 / per_run / 1e6
        );
        if let Some((g, exec)) = graph {
            gpu.destroy_graph(exec, g);
        }
    }
    if bad != 0 || mv_errors != 0 {
        std::process::exit(1);
    }
}
