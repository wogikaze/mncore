//! Differential test of MAU vector instructions against the official emulator.
//!
//! Usage: difftest_mau <op> [runs] [seed]
//!   op: fvfma | fvmul | fvadd | fvsub | frelu | fvpassa | dvfmau | dvmulu | dvadd | dvpassa
//!
//! Each run fills LM0 / LM1 / GRF0 of 64 PEs with random operands, executes 32 steps of the
//! instruction into GRF1, and compares every result bit for bit with `float::vfma`.

use mncore_sim::emu;
use mncore_sim::float::{self, Fmt, Val, DOUBLE, SINGLE};

const PES: usize = 64;
const STEPS: usize = 32;
const LONGS: usize = STEPS * 4; // long words per PE per operand

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

/// Random raw bits of `fmt`, biased toward the cases where rounding rules matter.
fn gen_value(rng: &mut Rng, fmt: Fmt) -> u64 {
    let sign = rng.below(2) << (fmt.width() - 1);
    let man = rng.next() & ((1 << fmt.man_bits) - 1);
    let emax = fmt.exp_max();
    let bias = fmt.bias() as u64;
    let exp = match rng.below(20) {
        0 => 0,                        // zero, possibly with a nonzero mantissa
        1 => emax,                     // infinity, possibly with a nonzero mantissa
        2 => 1 + rng.below(4),         // near underflow
        3 => emax - 1 - rng.below(4),  // near overflow
        4 => return rng.next() & ((1u64 << fmt.width()) - 1).max(u64::MAX >> (64 - fmt.width())),
        _ => bias - 8 + rng.below(16), // ordinary magnitudes
    };
    let man = match rng.below(6) {
        0 => (1 << fmt.man_bits) - 1,                       // all ones
        1 => man & !((1 << (fmt.man_bits - 6)) - 1),         // short mantissa
        2 => man | 1,                                        // low bit set
        _ => man,
    };
    sign | (exp << fmt.man_bits) | man
}

#[derive(Clone, Copy)]
enum Kind {
    Fma,
    Mul,
    Add,
    Sub,
    Relu,
    Pass,
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let op = args.get(1).map(String::as_str).unwrap_or("fvfma");
    let runs: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(1);
    let seed: u64 = args.get(3).and_then(|s| s.parse().ok()).unwrap_or(1);
    let (fmt, kind, mul_pes): (Fmt, Kind, [bool; 4]) = match op {
        "fvfma" => (SINGLE, Kind::Fma, [true; 4]),
        "fvmul" => (SINGLE, Kind::Mul, [true; 4]),
        "fvadd" => (SINGLE, Kind::Add, [true; 4]),
        "fvsub" => (SINGLE, Kind::Sub, [true; 4]),
        "frelu" => (SINGLE, Kind::Relu, [true; 4]),
        "fvpassa" => (SINGLE, Kind::Pass, [true; 4]),
        "dvfmau" => (DOUBLE, Kind::Fma, [true, true, false, false]),
        "dvmulu" => (DOUBLE, Kind::Mul, [true, true, false, false]),
        "dvadd" => (DOUBLE, Kind::Add, [true; 4]),
        "dvpassa" => (DOUBLE, Kind::Pass, [true; 4]),
        _ => panic!("unknown op {op}"),
    };
    let lanes = 64 / fmt.width() as usize;
    let mut rng = Rng(seed.wrapping_mul(0x9e37_79b9_7f4a_7c15) | 1);
    let mut total = 0usize;
    let mut bad = 0usize;

    for run in 0..runs {
        let pe_name = |i: usize| format!("n0c0b0m{}p{}", i / 4, i % 4);
        let mut a = vec![[0u64; LONGS]; PES];
        let mut b = vec![[0u64; LONGS]; PES];
        let mut c = vec![[0u64; LONGS]; PES];
        let mut vsm = String::new();
        for pe in 0..PES {
            for i in 0..LONGS {
                let mut la = 0;
                let mut lb = 0;
                let mut lc = 0;
                for lane in 0..lanes {
                    let sh = (lanes - 1 - lane) * fmt.width() as usize;
                    let x = if matches!(kind, Kind::Relu) {
                        let sign = (rng.below(2) as u32) << 31;
                        let exponent = rng.below(137) as u32;
                        let mantissa = rng.next() as u32 & 0x7f_ffff;
                        (sign | (exponent << 23) | mantissa) as u64
                    } else {
                        gen_value(&mut rng, fmt)
                    };
                    let y = gen_value(&mut rng, fmt);
                    let mut z = gen_value(&mut rng, fmt);
                    if rng.below(3) == 0 {
                        // Make c cancel most of a * b.
                        let p = float::vfma(fmt, fmt, float::decode(fmt, x), float::decode(fmt, y), Val::Zero { neg: false });
                        let ulps = rng.below(5);
                        z = (p ^ (1 << (fmt.width() - 1))).wrapping_add(ulps) & (u64::MAX >> (64 - fmt.width()));
                    }
                    la |= x << sh;
                    lb |= y << sh;
                    lc |= z << sh;
                }
                a[pe][i] = la;
                b[pe][i] = lb;
                c[pe][i] = lc;
            }
            for (mem, data) in [("lm0", &a[pe]), ("ln0", &b[pe]), ("lr0", &c[pe])] {
                vsm += &format!("d set ${mem}{} {LONGS} ", pe_name(pe));
                for v in data.iter() {
                    vsm += &format!("{v:016X}");
                }
                vsm += "\n";
            }
        }
        for s in 0..STEPS {
            let w = s * 8; // word address of this step's 4 long words
            vsm += &match kind {
                Kind::Fma => format!("{op} $lm{w}v $ln{w}v $lr{w}v $ls{w}v\n"),
                Kind::Mul => format!("{op} $lm{w}v $ln{w}v $ls{w}v\n"),
                Kind::Add => format!("{op} $lm{w}v $lr{w}v $ls{w}v\n"),
                Kind::Sub => format!("fvadd $lm{w}v -$lr{w}v $ls{w}v\n"),
                Kind::Relu => format!("frelu $lm{w}v $lr{w}v $ls{w}v\n"),
                Kind::Pass => format!("{op} $lm{w}v $ls{w}v\n"),
            };
        }
        vsm += "nop\n";
        for pe in 0..PES {
            vsm += &format!("d get $ls0{} {LONGS}\n", pe_name(pe));
        }

        let dump = match emu::run(&vsm) {
            Ok(d) => d,
            Err(e) => {
                eprintln!("{e}");
                std::process::exit(2);
            }
        };
        let got = emu::parse_dump(&dump);

        for pe in 0..PES {
            for i in 0..LONGS {
                let actual = *got
                    .get(&("GREG1".to_string(), pe_name(pe), (i * 2) as u32))
                    .unwrap_or_else(|| panic!("missing dump for pe {pe} long {i}"));
                for lane in 0..lanes {
                    let sh = (lanes - 1 - lane) * fmt.width() as usize;
                    let mask = u64::MAX >> (64 - fmt.width());
                    let x = (a[pe][i] >> sh) & mask;
                    let y = (b[pe][i] >> sh) & mask;
                    let z = (c[pe][i] >> sh) & mask;
                    let one = float::decode(fmt, (fmt.bias() as u64) << fmt.man_bits);
                    let zero = Val::Zero { neg: false };
                    let (va, vb, vc) = match kind {
                        Kind::Fma => (float::decode(fmt, x), float::decode(fmt, y), float::decode(fmt, z)),
                        Kind::Mul => (float::decode(fmt, x), float::decode(fmt, y), zero),
                        Kind::Add => (float::decode(fmt, x), one, float::decode(fmt, z)),
                        Kind::Sub => (float::decode(fmt, x), one, float::decode(fmt, z).negate()),
                        Kind::Relu => (zero, zero, zero),
                        Kind::Pass => (float::decode(fmt, x), one, zero),
                    };
                    let relu_expect = (x as u32 & 0x7fff_ffff == 0 || x as u32 & 0x8000_0000 == 0)
                        .then_some(z as u32 as u64)
                        .unwrap_or(0x8000_0000);
                    let expect = if matches!(kind, Kind::Relu) {
                        relu_expect
                    } else if mul_pes[pe % 4] {
                        float::vfma(fmt, fmt, va, vb, vc)
                    } else {
                        float::vfma(fmt, fmt, zero, zero, vc)
                    };
                    let actual = (actual >> sh) & mask;
                    total += 1;
                    if actual != expect {
                        bad += 1;
                        if bad <= 20 {
                            println!(
                                "MISMATCH run {run} pe {pe} long {i} lane {lane}: a={x:0w$x} b={y:0w$x} c={z:0w$x} emu={actual:0w$x} sim={expect:0w$x}",
                                w = fmt.width() as usize / 4
                            );
                        }
                    }
                }
            }
        }
    }
    println!("{op}: {total} values, {bad} mismatches");
    if bad > 0 {
        std::process::exit(1);
    }
}
