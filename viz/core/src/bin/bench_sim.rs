//! Measures simulator throughput on one VSM program.
//!
//! Usage: bench_sim <program.vsm> [iterations] [--official]
//!
//! With `--official`, the same program is assembled once and then run on the official
//! emulator (`judge/`, fetched by `setup_judge.sh`). Pin the process and limit OpenMP outside
//! when comparing one core against one core:
//!
//! ```sh
//! OMP_THREAD_LIMIT=1 taskset -c 2 cargo run --release --bin bench_sim -- \
//!     benchmarks/mnist_train_step.vsm 3 --official
//! ```

use std::time::{Duration, Instant};

use mncore_sim::{emu, run::Sim, vsm};

/// Physical PEs in one group (the simulator models one group).
const PES: u64 = 4096;
/// Each instruction word occupies four PE cycles.
const CYCLES_PER_WORD: u64 = 4;

fn main() {
    let mut args = std::env::args().skip(1);
    let path = args.next().unwrap_or_else(|| usage());
    let mut iterations = 3usize;
    let mut official = false;
    for arg in args {
        match arg.as_str() {
            "--official" => official = true,
            n => iterations = n.parse().unwrap_or_else(|_| usage()),
        }
    }
    let iterations = iterations.max(1);

    let text = std::fs::read_to_string(&path).unwrap_or_else(|e| fail(&format!("{path}: {e}")));
    let lines = vsm::parse(&text).unwrap_or_else(|e| fail(&format!("{path}: {e}")));
    let words: u64 = lines.iter().map(|(_, line)| u64::from(line.words())).sum();

    println!("workload: {path}");
    println!("program: {} lines, {words} words", lines.len());

    // Warm up the allocator and page cache before timing.
    run_native(&lines).unwrap_or_else(|e| fail(&e));
    let native = time(iterations, || run_native(&lines)).unwrap_or_else(|e| fail(&e));
    print_stats("native", &native, words);

    if official {
        if !emu::available() {
            eprintln!("official emulator not found; run setup_judge.sh first");
            std::process::exit(1);
        }
        let start = Instant::now();
        let asm = emu::assemble(&text).unwrap_or_else(|e| fail(&e));
        let assemble = start.elapsed();
        let body: String = asm
            .lines()
            .filter(|line| line.starts_with("j ") || line.starts_with("m "))
            .map(|line| format!("{line}\n"))
            .collect();
        println!("assemble: {:.3} s", assemble.as_secs_f64());
        let official =
            time(iterations, || emu::run_asm(&body).map(|_| ())).unwrap_or_else(|e| fail(&e));
        print_stats("official", &official, words);
        let speedup = median(&official).as_secs_f64() / median(&native).as_secs_f64();
        println!("speedup: {speedup:.2}x");
    }
}

fn usage() -> ! {
    eprintln!("usage: bench_sim <program.vsm> [iterations] [--official]");
    std::process::exit(2);
}

fn fail(message: &str) -> ! {
    eprintln!("bench_sim: {message}");
    std::process::exit(1);
}

fn run_native(lines: &[(usize, vsm::Line)]) -> Result<(), String> {
    let mut sim = Sim::new();
    sim.run(lines)
        .map_err(|e| format!("line {}: {}", e.line, e.msg))
}

fn time(
    iterations: usize,
    mut run: impl FnMut() -> Result<(), String>,
) -> Result<Vec<Duration>, String> {
    let mut times = Vec::with_capacity(iterations);
    for _ in 0..iterations {
        let start = Instant::now();
        run()?;
        times.push(start.elapsed());
    }
    Ok(times)
}

fn median(times: &[Duration]) -> Duration {
    let mut sorted = times.to_vec();
    sorted.sort();
    sorted[sorted.len() / 2]
}

fn print_stats(label: &str, times: &[Duration], words: u64) {
    let median = median(times).as_secs_f64();
    let min = times.iter().min().map_or(0.0, |t| t.as_secs_f64());
    let pe_cycles = words * PES * CYCLES_PER_WORD;
    println!(
        "{label:8} median {median:7.3} s (min {min:7.3} s)  {:6.0} words/s  {:5.1} M PE-cycles/s",
        words as f64 / median,
        pe_cycles as f64 / median / 1e6
    );
}
