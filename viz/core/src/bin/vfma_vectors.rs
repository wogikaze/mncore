//! Emits f32 vfma test vectors for the GPU backend checks.
//!
//! Usage: vfma_vectors [count] [output]
//!
//! The binary layout is four little-endian u32 per vector: a, b, c, expected.

use std::io::{BufWriter, Write};

use mncore_sim::float::{self, SINGLE};

fn main() {
    let mut args = std::env::args().skip(1);
    let count: usize = args
        .next()
        .and_then(|s| s.parse().ok())
        .unwrap_or(1_000_000);
    let path = args
        .next()
        .unwrap_or_else(|| "target/vfma_vectors.bin".to_string());
    let mut state = 0x1234_5678_9abc_def0u64;
    let mut next = || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state
    };
    let file = std::fs::File::create(&path).expect("create output");
    let mut out = BufWriter::new(file);
    let start = std::time::Instant::now();
    for _ in 0..count {
        let a = next() as u32;
        let b = next() as u32;
        let c = next() as u32;
        let result = float::vfma(
            SINGLE,
            SINGLE,
            float::decode(SINGLE, a as u64),
            float::decode(SINGLE, b as u64),
            float::decode(SINGLE, c as u64),
        ) as u32;
        out.write_all(&a.to_le_bytes()).unwrap();
        out.write_all(&b.to_le_bytes()).unwrap();
        out.write_all(&c.to_le_bytes()).unwrap();
        out.write_all(&result.to_le_bytes()).unwrap();
    }
    out.flush().unwrap();
    let elapsed = start.elapsed();
    println!(
        "{} vectors, {} bytes, {:?} ({:.1} Mvfma/s)",
        count,
        count * 16,
        elapsed,
        count as f64 / elapsed.as_secs_f64() / 1e6
    );
}
