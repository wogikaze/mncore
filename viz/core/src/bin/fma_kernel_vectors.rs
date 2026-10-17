//! Emit deterministic single-precision FMA vectors from the Rust model.
//!
//! The Lean proof gate consumes these expected outputs and kernel-reduces its
//! bit-level FMA implementation against them.

use mncore_sim::float::{self, SINGLE, Val};

struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }

    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
}

fn value(rng: &mut Rng) -> u32 {
    let sign = (rng.below(2) as u32) << 31;
    let mantissa = rng.next() as u32 & 0x7f_ffff;
    let exponent = match rng.below(12) {
        0 => 0,
        1 => 255,
        2 => 1,
        3 => 2,
        4 => 253,
        5 => 254,
        _ => rng.below(255) as u32,
    };
    sign | (exponent << 23) | mantissa
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let count = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(256usize);
    let seed = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(1u64);
    let operation = args.get(3).map(String::as_str).unwrap_or("fvfma");
    let mut rng = Rng(seed.wrapping_mul(0x9e37_79b9_7f4a_7c15) | 1);
    for index in 0..count {
        let a = value(&mut rng);
        let b = value(&mut rng);
        let mut c = value(&mut rng);
        if operation == "fvmul" {
            c = 0;
        } else if operation == "fvsub" {
            c = 0;
        } else if operation == "fvfma" && index % 3 == 0 {
            let product = float::vfma(
                SINGLE,
                SINGLE,
                float::decode(SINGLE, a as u64),
                float::decode(SINGLE, b as u64),
                Val::Zero { neg: false },
            ) as u32;
            c = (product ^ 0x8000_0000).wrapping_add(rng.below(5) as u32);
        }
        let expected = match operation {
            "fvfma" => float::vfma(
                SINGLE, SINGLE, float::decode(SINGLE, a as u64),
                float::decode(SINGLE, b as u64), float::decode(SINGLE, c as u64),
            ) as u32,
            "fvmul" => float::vfma(
                SINGLE, SINGLE, float::decode(SINGLE, a as u64),
                float::decode(SINGLE, b as u64), Val::Zero { neg: false },
            ) as u32,
            "fvadd" => float::vfma(
                SINGLE, SINGLE, float::decode(SINGLE, a as u64),
                float::decode(SINGLE, 0x3f80_0000), float::decode(SINGLE, c as u64),
            ) as u32,
            "fvsub" => float::vfma(
                SINGLE, SINGLE, float::decode(SINGLE, a as u64),
                float::decode(SINGLE, 0x3f80_0000), float::decode(SINGLE, b as u64).negate(),
            ) as u32,
            "frelu" => {
                if a & 0x7fff_ffff == 0 || a & 0x8000_0000 == 0 { c } else { 0x8000_0000 }
            }
            _ => panic!("unknown operation {operation}"),
        };
        println!("{a:08x} {b:08x} {c:08x} {expected:08x}");
    }
}
