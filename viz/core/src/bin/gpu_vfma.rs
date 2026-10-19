//! Verifies and benchmarks the CUDA f32 vfma kernel through the Rust wrapper.
//!
//! Usage: gpu_vfma [count]

use mncore_sim::float::{self, SINGLE};
use mncore_sim::gpu::Gpu;

fn main() {
    let count: usize = std::env::args()
        .nth(1)
        .and_then(|s| s.parse().ok())
        .unwrap_or(1_000_000);
    let mut state = 0x1234_5678_9abc_def0u64;
    let mut next = || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state
    };
    let mut a = Vec::with_capacity(count);
    let mut b = Vec::with_capacity(count);
    let mut c = Vec::with_capacity(count);
    let mut expected = Vec::with_capacity(count);
    let cpu_start = std::time::Instant::now();
    for _ in 0..count {
        let (x, y, z) = (next() as u32, next() as u32, next() as u32);
        a.push(x);
        b.push(y);
        c.push(z);
        expected.push(
            float::vfma(
                SINGLE,
                SINGLE,
                float::decode(SINGLE, x as u64),
                float::decode(SINGLE, y as u64),
                float::decode(SINGLE, z as u64),
            ) as u32,
        );
    }
    let cpu_elapsed = cpu_start.elapsed();
    let gpu = match Gpu::new() {
        Ok(gpu) => gpu,
        Err(error) => {
            eprintln!("gpu unavailable: {error}");
            std::process::exit(2);
        }
    };
    let gpu_start = std::time::Instant::now();
    let out = gpu.vfma_f32(&a, &b, &c).expect("vfma");
    let gpu_elapsed = gpu_start.elapsed();
    let mismatches = out
        .iter()
        .zip(&expected)
        .filter(|(lhs, rhs)| lhs != rhs)
        .count();
    println!(
        "{} vectors, {} mismatches, cpu {:?} ({:.1} Mvfma/s), gpu {:?} ({:.1} Mvfma/s)",
        count,
        mismatches,
        cpu_elapsed,
        count as f64 / cpu_elapsed.as_secs_f64() / 1e6,
        gpu_elapsed,
        count as f64 / gpu_elapsed.as_secs_f64() / 1e6,
    );
    if mismatches != 0 {
        std::process::exit(1);
    }
}
