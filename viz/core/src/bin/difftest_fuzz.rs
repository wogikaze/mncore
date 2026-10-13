//! Random PE programs compared against the official emulator.
//!
//! Usage: difftest_fuzz [runs] [seed] [statements]
//!
//! Each run fills the PE memories of two MABs with random values, executes random PE
//! statements (each followed by `nop/3` so that no hazard rule applies), and compares LM0, LM1,
//! GRF0, GRF1, T and the mask register entries of those PEs. Statements that the official
//! assembler rejects are dropped and the program is reassembled.

use mncore_sim::{emu, run::Sim, vsm};

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
    fn pick<'a, T>(&mut self, xs: &'a [T]) -> &'a T {
        &xs[self.below(xs.len() as u64) as usize]
    }
    fn chance(&mut self, p: u64) -> bool {
        self.below(100) < p
    }
}

/// PEs whose memories are initialized and compared: all MABs of two L1Bs, so that L1BM
/// reductions over MABs see real data.
const L1BS: [&str; 2] = ["n0c0b0", "n2c1b3"];
/// L2Bs whose L2BM is initialized and compared.
const L2BS: [&str; 2] = ["n0c0", "n2c1"];
/// L1BM / L2BM long words initialized and compared.
const L1_LONGS: usize = 512;
const L2_LONGS: usize = 1024;
/// DRAM long words per group initialized and compared (PDM is only reached through MV).
const DRAM_LONGS: usize = 1024;
const LONGS: usize = 64; // long words of LM/GRF filled and compared

/// A random long word: floats of each precision, integers, and special patterns.
fn value(r: &mut Rng) -> u64 {
    if std::env::var_os("FUZZ_FINITE").is_some() {
        return finite_value(r);
    }
    let f32b = |r: &mut Rng| -> u64 {
        let e = match r.below(10) {
            0 => 0,
            1 => 255,
            2 => 1 + r.below(3),
            _ => 120 + r.below(16),
        };
        (r.below(2) << 31) | (e << 23) | (r.next() & 0x7f_ffff)
    };
    let f16b = |r: &mut Rng| -> u64 {
        let e = match r.below(10) {
            0 => 0,
            1 => 63,
            _ => 25 + r.below(12),
        };
        (r.below(2) << 15) | (e << 9) | (r.next() & 0x1ff)
    };
    match r.below(7) {
        0 | 1 => (f32b(r) << 32) | f32b(r),
        2 => {
            let e = match r.below(10) {
                0 => 0,
                1 => 2047,
                _ => 1015 + r.below(16),
            };
            (r.below(2) << 63) | (e << 52) | (r.next() & ((1 << 52) - 1))
        }
        3 => (f16b(r) << 48) | (f16b(r) << 32) | (f16b(r) << 16) | f16b(r),
        4 => r.below(64) | (r.below(64) << 32),
        5 => 0,
        _ => r.next(),
    }
}

/// Like `value`, but only finite nonzero floats of ordinary magnitude.
fn finite_value(r: &mut Rng) -> u64 {
    match r.below(3) {
        0 => {
            let f = |r: &mut Rng| (r.below(2) << 31) | ((120 + r.below(16)) << 23) | (r.next() & 0x7f_ffff);
            (f(r) << 32) | f(r)
        }
        1 => (r.below(2) << 63) | ((1015 + r.below(16)) << 52) | (r.next() & ((1 << 52) - 1)),
        _ => {
            let f = |r: &mut Rng| (r.below(2) << 15) | ((25 + r.below(12)) << 9) | (r.next() & 0x1ff);
            (f(r) << 48) | (f(r) << 32) | (f(r) << 16) | f(r)
        }
    }
}

fn mem_operand(r: &mut Rng, read: bool) -> String {
    let neg = if read && r.chance(8) { "-" } else { "" };
    if read && r.chance(15) {
        return format!("{neg}{}", r.pick(&["$aluf", "$mauf"]));
    }
    let kind = *r.pick(&["m", "n", "r", "s", "m", "n", "r", "s", "t"]);
    if kind == "t" {
        return format!("{neg}$lt");
    }
    if read && kind == "m" && r.chance(10) {
        // T register indirect: the address comes from T (wraps at the LM0 size).
        return format!("{neg}$lmt{}v", r.below(8) * 2);
    }
    let (len, wl) = *r.pick(&[("l", 2u64), ("l", 2), ("l", 2), ("", 1), ("ll", 4)]);
    let addr = r.below(LONGS as u64 * 2 / wl / 2) * wl;
    if r.chance(10) {
        let a: Vec<String> = (0..4).map(|_| (r.below(LONGS as u64 * 2 / wl / 2) * wl).to_string()).collect();
        return format!("{neg}${len}{kind}[{}]", a.join(","));
    }
    format!("{neg}${len}{kind}{addr}v")
}

fn dst_operand(r: &mut Rng) -> String {
    let mut d = mem_operand(r, false);
    if r.chance(10) {
        d += &format!("/{}", r.pick(&["1010", "0110", "1000", "$imr1", "$imr2", "$imr3"]));
    }
    d
}

fn statement(r: &mut Rng) -> String {
    let src = |r: &mut Rng| mem_operand(r, true);
    let mut dsts = vec![dst_operand(r)];
    if r.chance(15) {
        dsts.push(format!("$omr{}", 1 + r.below(3)));
    }
    if r.chance(10) {
        dsts = vec!["$nowrite".into()];
    }
    let dst = dsts.join(" ");
    match r.below(12) {
        0 | 1 | 2 => {
            let (name, n, precs): (&str, usize, &[&str]) = *r.pick(&[
                ("passa", 1, &["d", "f", "h", "l", "i", "s"][..]),
                ("inc", 1, &["l", "i", "s"]),
                ("dec", 1, &["l", "i", "s"]),
                ("not", 1, &["l", "i", "s"]),
                ("lnot", 1, &["l", "i", "s"]),
                ("floor", 1, &["d", "f", "h"]),
                ("ftoi", 1, &["d", "f", "h"]),
                ("max", 2, &["d", "f", "h", "l", "i", "s"]),
                ("min", 2, &["d", "f", "h", "l", "i", "s"]),
                ("packbit", 2, &["d", "f", "h", "l", "i", "s"]),
                ("and", 2, &["l", "i", "s"]),
                ("or", 2, &["l", "i", "s"]),
                ("xor", 2, &["l", "i", "s"]),
                ("add", 2, &["l", "i", "s"]),
                ("sub", 2, &["l", "i", "s"]),
                ("lsl", 2, &["l", "i", "s"]),
                ("lsr", 2, &["l", "i", "s"]),
                ("bsl", 2, &["l", "i", "s"]),
                ("bsr", 2, &["l", "i", "s"]),
                ("relu", 2, &["d", "f", "h"]),
                ("relu1", 2, &["d", "f", "h"]),
                ("relu3", 2, &["d", "f", "h"]),
                ("rsqrt", 1, &["d", "f", "h"]),
            ]);
            let p = r.pick(precs);
            let u = if ["inc", "dec", "add", "sub", "lsr", "ftoi"].contains(&name) && r.chance(30) { "u" } else { "" };
            let u = if ["max", "min"].contains(&name) && ["l", "i", "s"].contains(p) && r.chance(30) { "u" } else { u };
            let srcs: Vec<String> = (0..n).map(|_| src(r).trim_start_matches('-').to_string()).collect();
            format!("{u}{p}{name} {} {dst}", srcs.join(" "))
        }
        3 => format!("{} {dst}", r.pick(&["msl", "msr"])).replacen(' ', &format!(" {} ", src(r).trim_start_matches('-')), 1),
        4 => {
            let lit = match r.below(4) {
                0 => format!("f\"{}\"", (r.below(2000) as f32 - 1000.0) / 8.0),
                1 => format!("i\"{}\"", r.below(200) as i64 - 100),
                2 => format!("h\"{}\"", (r.below(200) as f32 - 100.0) / 4.0),
                _ => format!("us\"{}\"", r.below(65536)),
            };
            format!("{} {lit} {dst}", r.pick(&["imm", "immu"]))
        }
        5 => format!("zero {dst}"),
        6 | 7 => {
            let (op, n) = *r.pick(&[("fvfma", 3), ("fvmul", 2), ("fvadd", 2), ("fvpassa", 1), ("dvfmau", 3), ("dvfmad", 3), ("dvmulu", 2), ("dvadd", 2), ("dvpassa", 1)]);
            let srcs: Vec<String> = (0..n).map(|_| src(r)).collect();
            format!("{op} {} {dst}", srcs.join(" "))
        }
        8 => {
            let p = *r.pick(&["d", "f", "g", "h"]);
            let op = if p == "h" { format!("h{}/{}", r.pick(&["bfn", "bfe"]), 6 + r.below(4)) } else { format!("{p}bfn") };
            format!("{op} {} {dst}", src(r).trim_start_matches('-'))
        }
        9 => {
            let p = *r.pick(&["d", "f", "g", "h"]);
            let side = r.pick(&["x", "y"]);
            let row = r.below(if p == "d" { 4 } else { 8 });
            format!("{p}mwrite {} $l{side}{row}", src(r))
        }
        10 => {
            let p = *r.pick(&["d", "f", "g"]);
            let side = r.pick(&["x", "y"]);
            format!("{p}mread $l{side}{} {dst}", r.below(4))
        }
        _ => {
            let (op, n) = *r.pick(&[("dmfmau", 2), ("dmfmad", 2), ("dmmulu", 1), ("fmfma", 2), ("fmmul", 1), ("gmfma", 2), ("gmmul", 1)]);
            let side = r.pick(&["x", "y"]);
            let srcs: Vec<String> = (0..n).map(|_| src(r)).collect();
            format!("{op} $l{side} {} {dst}", srcs.join(" "))
        }
    }
}

/// A group of statements issued in consecutive steps. Matrix products need block-float
/// inputs, so they come with the bfn and mwrite statements that prepare them.
fn group(r: &mut Rng) -> Vec<String> {
    if r.chance(15) {
        return mv_group(r);
    }
    if r.chance(30) {
        return block_group(r);
    }
    if !r.chance(25) {
        return vec![statement(r)];
    }
    let src = |r: &mut Rng| mem_operand(r, false);
    let side = *r.pick(&["x", "y"]);
    let (p, rows_per_write, writes) = *r.pick(&[("d", 4, 1), ("f", 4, 2), ("g", 4, 2)]);
    let mut g = Vec::new();
    for w in 0..writes {
        g.push(format!("{p}bfn {} $nowrite", src(r)));
        g.push(format!("{p}mwrite $aluf $l{side}{}", w * rows_per_write));
    }
    g.push(format!("{p}bfn {} $nowrite", src(r)));
    let dst = dst_operand(r);
    let op = match p {
        "d" => format!("{} $l{side} $aluf", r.pick(&["dmmulu", "dmmuld"])),
        "f" => format!("fmmul $l{side} $aluf"),
        _ => format!("gmmul $l{side} $aluf"),
    };
    if r.chance(50) {
        let fma = op.replacen("mul", "fma", 1);
        g.push(format!("{fma} {} {dst}", mem_operand(r, true)));
    } else {
        g.push(format!("{op} {dst}"));
    }
    if r.chance(30) {
        g.push(format!("{p}mread $l{side}{} {}", r.below(4), dst_operand(r)));
    }
    g
}

fn rrn(r: &mut Rng, two: bool) -> String {
    if two {
        // Two long word reductions only allow single-precision floats or bor.
        return r.pick(&["ffadd", "fmax", "fmin", "lbor", "ibor", "sbor"]).to_string();
    }
    r.pick(&["dfadd", "ffadd", "hfadd", "dmax", "fmin", "hmax", "liadd", "iiadd", "siadd", "lband", "iand", "sbor", "lor"]).to_string()
}

fn set(r: &mut Rng) -> String {
    match r.below(3) {
        0 => String::new(),
        1 => format!("@{}", r.below(8)),
        _ => format!("@{}/{}", r.below(8), r.below(7)),
    }
}

/// L1BM and L2BM transfers (addresses stay within the compared region).
fn block_group(r: &mut Rng) -> Vec<String> {
    let pe_src = |r: &mut Rng, two: bool| if two { format!("$llr{}v", r.below(16) * 4) } else { mem_operand(r, true) };
    let pe_dst = |r: &mut Rng, two: bool| if two { format!("$llm{}v", r.below(16) * 4) } else { dst_operand(r) };
    let two = r.chance(30);
    let (b, w) = if two { ("$llb", 2) } else { ("$lb", 1) };
    let lb = |r: &mut Rng, align: u64| r.below(L1_LONGS as u64 / align / 4) * align;
    let lc = |r: &mut Rng, align: u64| r.below(L2_LONGS as u64 / align / 4) * align;
    match r.below(12) {
        0 => vec![format!("l1bmp {b}{} {}", lb(r, 1) & !if two { 7 } else { 0 }, pe_dst(r, two))],
        1 => vec![format!("l1bmm {b}{} {}", lb(r, 4 * w), pe_dst(r, two))],
        2 => vec![format!("l1bmm@{} {} {b}{}", r.below(16), pe_src(r, two), lb(r, 4 * w))],
        3 => vec![format!("l1bmm4 {b}{} {}", lb(r, 16 * w), pe_dst(r, two))],
        4 => vec![format!("l1bmm4@{} {} {b}{}", r.below(4), pe_src(r, two), lb(r, 16 * w))],
        5 => match r.below(4) {
            // Explicit output rounding (single to half) and input extension (half to single).
            0 => vec![format!("l1bmrffaddr {} $lb{}", pe_src(r, true), lb(r, 4))],
            1 => vec![format!("l1bmrffadd $lr{}ve $llb{}", r.below(16) * 2, lb(r, 8))],
            _ => vec![format!("l1bmr{} {} {b}{}", rrn(r, two), pe_src(r, two), lb(r, 4 * w))],
        },
        6 => vec![format!("l1bmr4{} {} {b}{}", rrn(r, two), pe_src(r, two), lb(r, 16 * w))],
        7 => {
            let d = if r.chance(50) { format!("{}{}", r.pick(&["+", "-"]), r.below(16)) } else { String::new() };
            if r.chance(50) {
                vec![format!("l1bmd{d} $lb{} {}", lb(r, 64), dst_operand(r))]
            } else {
                vec![format!("l1bmd{d} {} $lb{}", mem_operand(r, true), lb(r, 64))]
            }
        }
        8 => {
            // Turnaround: write, then read the turnaround register in the next step.
            let m = r.below(16);
            vec![format!("l1bmm@{m} {} {b}{}", pe_src(r, two), lb(r, 4 * w)), format!("l1bmm {b}i {}", pe_dst(r, two))]
        }
        9 => {
            let op = *r.pick(&["l2bmb", "l2bmb2", "l2bmd"]);
            let (ca, ba) = match op {
                "l2bmb" => (lc(r, 16), lb(r, 16)),
                "l2bmb2" => (lc(r, 64), lb(r, 16)),
                _ => (lc(r, 64), lb(r, 8)),
            };
            vec![format!("{op}{} $lc{ca} $lb{ba}", set(r))]
        }
        10 => match r.below(4) {
            0 => vec![format!("l2bm@{} $lb{} $lc{}", r.below(8), lb(r, 16), lc(r, 16))],
            1 => vec![format!("l2bmr{}{} $lb{} $lc{}", rrn(r, false), set(r), lb(r, 16), lc(r, 16))],
            2 => vec![format!("l2bmr2{} $lb{} $lc{}", rrn(r, false), lb(r, 16), lc(r, 64))],
            _ => vec![format!("l2bmd $lb{} $lc{}", lb(r, 8), lc(r, 64))],
        },
        _ => vec![format!("l2bmi@{}/{} $lb{} $lb{}", r.below(8), r.below(7), lb(r, 16), lb(r, 16))],
    }
}

/// MV transfers among DRAM, PDM and L2BM (sizes and addresses within the compared region).
fn mv_group(r: &mut Rng) -> Vec<String> {
    let n = *r.pick(&[64u64, 128]);
    let a = |r: &mut Rng, lim: u64, align: u64| r.below(lim / align) * align;
    let g = |r: &mut Rng| r.below(4);
    let op = |r: &mut Rng| r.pick(&["dfadd", "ffadd", "hfadd", "dmax", "fmin", "liadd", "iband", "sbor"]).to_string();
    let d = |r: &mut Rng| a(r, DRAM_LONGS as u64 / 2, 64);
    let c = |r: &mut Rng| a(r, L2_LONGS as u64 / 2, 64);
    let p = |r: &mut Rng| a(r, 4096, 64);
    let mv = match r.below(14) {
        0 => format!("mvp/n{n} $d{}@{} $lc{}@{}.{}", d(r), g(r), c(r), g(r), r.below(2)),
        1 => format!("mvp/n{n} $lc{}@{}.{} $d{}@{}", c(r), g(r), r.below(2), d(r), g(r)),
        2 => format!("mvp/n{n} $d{} $lc{}@.{}", d(r), c(r), r.below(2)),
        3 => format!("mvp/n{n} $lc{}@.{} $d{}", c(r), r.below(2), d(r)),
        4 => format!("mvp/n{n} $lc{}@{}.{} $p{}@{}", c(r), g(r), r.below(2), p(r), g(r)),
        5 => format!("mvp/n{n} $p{}@{} $d{}@{}", p(r), g(r), d(r), g(r)),
        6 => format!("mvb2/n{n} $d{} $lc{}", d(r), c(r)),
        7 => format!("mvb4/n{n} $d{} $lc{}", d(r), c(r)),
        8 => format!("mvb/n{n} $d{} $lc{}", d(r), c(r)),
        9 => format!("mvr{}/n{n} $lc{} $d{}", op(r), c(r), d(r)),
        10 => format!("mvr2{}/n{n} $lc{} $d{}", op(r), c(r), d(r)),
        11 => format!("mvr4{}/n{n} $lc{} $d{}", op(r), c(r), d(r)),
        12 => format!("mvd/n{n} $lc{} $p{}@{}", c(r), p(r) * 8, g(r)),
        _ => format!("mvd/n{n} $p{}@{} $d{}", p(r), g(r), d(r)),
    };
    vec![mv]
}

fn body(groups: &[Vec<String>]) -> (String, Vec<usize>, Vec<usize>) {
    // Returns the VSM text, the group of each VSM line, and the group of each asm j-line.
    let mut text = String::new();
    let mut vsm_group = Vec::new();
    let mut asm_group = Vec::new();
    for (gi, g) in groups.iter().enumerate() {
        for st in g {
            text += st;
            text += "\n";
            vsm_group.push(gi);
            asm_group.push(gi);
        }
        text += "nop/3\n";
        vsm_group.push(gi);
        asm_group.extend([gi; 3]);
    }
    (text, vsm_group, asm_group)
}

fn assembled(text: &str) -> Result<String, String> {
    emu::assemble(text).map(|a| a.lines().filter(|l| l.starts_with('j') || l.starts_with('m')).map(|l| format!("{l}\n")).collect())
}

fn error_line(e: &str) -> Option<usize> {
    e.lines()
        .find_map(|l| l.strip_prefix("Line ").and_then(|n| n.trim().parse::<usize>().ok()))
        .or_else(|| e.lines().find_map(|l| l.trim().strip_prefix("line no :").and_then(|n| n.trim().parse().ok())))
        .or_else(|| e.split("at line ").nth(1).and_then(|t| t.split(|c: char| !c.is_ascii_digit()).next()?.parse().ok()))
        .or_else(|| e.split("line ").nth(1).and_then(|t| t.split(|c: char| !c.is_ascii_digit()).next()?.parse().ok()))
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let runs: usize = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(1);
    let seed: u64 = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(1);
    let n_stmt: usize = args.get(3).and_then(|s| s.parse().ok()).unwrap_or(40);
    let mut r = Rng(seed.wrapping_mul(0x9e37_79b9_7f4a_7c15) | 1);
    let mut total_bad = 0;
    let mut runtime_agree = 0;
    let mut runtime_disagree = 0;

    for run in 0..runs {
        let mut init = String::new();
        let mut probe = String::new();
        for l1 in L1BS {
            let vals: String = (0..L1_LONGS).map(|_| format!("{:016X}", value(&mut r))).collect();
            init += &format!("d set $lb0{l1} {L1_LONGS} {vals}\n");
            probe += &format!("d get $lb0{l1} {L1_LONGS}\n");
        }
        for l2 in ["n0c0", "n0c1", "n1c0", "n1c1", "n2c0", "n2c1", "n3c0", "n3c1"] {
            let vals: String = (0..L2_LONGS).map(|_| format!("{:016X}", value(&mut r))).collect();
            init += &format!("d set $lc0{l2} {L2_LONGS} {vals}\n");
            if L2BS.contains(&l2) || l2.ends_with("c1") {
                probe += &format!("d get $lc0{l2} {L2_LONGS}\n");
            }
        }
        for g in 0..4 {
            for chunk in 0..DRAM_LONGS / 64 {
                let vals: String = (0..64).map(|_| format!("{:016X}", value(&mut r))).collect();
                init += &format!("r {g} {:09X} 040 {vals}\n", chunk * 64);
            }
            probe += &format!("d get $d0n{g} {DRAM_LONGS}\n");
        }
        for (l1, m) in L1BS.iter().flat_map(|l| (0..16).map(move |m| (l, m))) {
            for p in 0..4 {
                let pe = format!("{l1}m{m}p{p}");
                for mem in ["lm0", "ln0", "lr0", "ls0"] {
                    let vals: String = (0..LONGS).map(|_| format!("{:016X}", value(&mut r))).collect();
                    init += &format!("d set ${mem}{pe} {LONGS} {vals}\n");
                    probe += &format!("d get ${mem}{pe} {LONGS}\n");
                }
                let vals: String = (0..8).map(|_| format!("{:016X}", value(&mut r))).collect();
                init += &format!("d set $llt{pe} 4 {vals}\n");
                probe += &format!("d get $llt{pe} 4\n");
                for k in 1..=3 {
                    probe += &format!("d get $omr{k}{pe} 1\n");
                }
            }
        }
        let init_lines = init.lines().count();
        let mut groups: Vec<Vec<String>> = (0..n_stmt).map(|_| group(&mut r)).collect();
        // Drop groups that the assembler rejects or that make the emulator stop.
        let (text, dump) = loop {
            let (text, vsm_group, asm_group) = body(&groups);
            let asm = match assembled(&text) {
                Ok(a) => a,
                Err(e) => {
                    match error_line(&e).filter(|&l| l >= 1 && l <= vsm_group.len()) {
                        Some(l) => {
                            groups.remove(vsm_group[l - 1]);
                        }
                        None => {
                            // The assembler crashed without a line number: find the first group
                            // whose prefix fails to assemble.
                            let (mut lo, mut hi) = (0, groups.len());
                            while hi - lo > 1 {
                                let mid = (lo + hi) / 2;
                                if assembled(&body(&groups[..mid]).0).is_err() {
                                    hi = mid;
                                } else {
                                    lo = mid;
                                }
                            }
                            groups.remove(hi - 1);
                        }
                    }
                    continue;
                }
            };
            match emu::run_asm(&format!("{init}{asm}{probe}")) {
                Ok(d) => break (text, d),
                Err(e) => {
                    let Some(l) = error_line(&e).filter(|&l| l > init_lines && l - init_lines <= asm_group.len()) else {
                        panic!("cannot locate emulator error:\n{e}")
                    };
                    let gi = asm_group[l - init_lines - 1];
                    // The simulator should stop with a runtime error in the same group.
                    let (prefix_text, _, _) = body(&groups[..=gi]);
                    let mut sim = Sim::new();
                    match sim.run(&vsm::parse(&format!("{init}{prefix_text}")).unwrap()) {
                        Err(err) if err.msg.starts_with("runtime error") => runtime_agree += 1,
                        other => {
                            runtime_disagree += 1;
                            let first = e.lines().find(|l| l.contains("exception")).unwrap_or("");
                            println!("run {run}: emulator error not detected by the simulator ({:?}): {first}\n    group: {:?}", other.err().map(|e| e.msg), groups[gi]);
                        }
                    }
                    groups.remove(gi);
                }
            }
        };
        let expect = emu::parse_dump(&dump);

        let src = format!("{init}{text}{probe}");
        let lines = vsm::parse(&src).unwrap_or_else(|e| panic!("parse: {e}\n{}", src.lines().nth(e.line - 1).unwrap_or("")));
        let mut sim = Sim::new();
        if let Err(e) = sim.run(&lines) {
            println!("run {run}: {} : {}", e.msg, src.lines().nth(e.line - 1).unwrap_or(""));
            let path = format!("/tmp/fuzz_simerr_s{seed}_r{run}.vsm");
            std::fs::write(&path, &src).unwrap();
            println!("      saved to {path} (line {})", e.line);
            total_bad += 1;
            continue;
        }
        let mut bad = 0;
        let mut keys: Vec<_> = expect.keys().collect();
        keys.sort();
        for k in keys {
            let e = expect[k];
            if sim.dump.get(k) != Some(&e) {
                bad += 1;
                if bad <= 8 {
                    println!(
                        "run {run} MISMATCH {} {} {}: emu={e:016x} sim={}",
                        k.0,
                        k.1,
                        k.2,
                        sim.dump.get(k).map(|v| format!("{v:016x}")).unwrap_or("missing".into())
                    );
                }
            }
        }
        if bad > 0 {
            // Bisect to the first group that makes the final state differ.
            let mut lo = 0;
            let mut hi = groups.len();
            while hi - lo > 1 {
                let mid = (lo + hi) / 2;
                if differs(&init, &groups[..mid], &probe) {
                    hi = mid;
                } else {
                    lo = mid;
                }
            }
            println!("run {run}: {bad} mismatches; first differing group #{}: {:?}", hi - 1, groups[hi - 1]);
            show_diff(&init, &groups[..hi], &probe);
            let (t, _, _) = body(&groups[..hi]);
            let path = format!("/tmp/fuzz_fail_s{seed}_r{run}.vsm");
            std::fs::write(&path, format!("{init}{t}{probe}")).unwrap();
            println!("      saved to {path}");
            total_bad += 1;
        } else {
            let n: usize = groups.iter().map(|g| g.len()).sum();
            println!("run {run}: {n} statements, {} values, ok", expect.len());
        }
    }
    println!("emulator runtime errors: {runtime_agree} also detected by the simulator, {runtime_disagree} not");
    if total_bad > 0 || runtime_disagree > 0 {
        std::process::exit(1);
    }
}

fn differs(init: &str, groups: &[Vec<String>], probe: &str) -> bool {
    let (text, _, _) = body(groups);
    let asm = assembled(&text).unwrap();
    let expect = emu::parse_dump(&emu::run_asm(&format!("{init}{asm}{probe}")).unwrap());
    let mut sim = Sim::new();
    if sim.run(&vsm::parse(&format!("{init}{text}{probe}")).unwrap()).is_err() {
        return true;
    }
    expect.iter().any(|(k, v)| sim.dump.get(k) != Some(v))
}

fn show_diff(init: &str, groups: &[Vec<String>], probe: &str) {
    let (text, _, _) = body(groups);
    let asm = assembled(&text).unwrap();
    let expect = emu::parse_dump(&emu::run_asm(&format!("{init}{asm}{probe}")).unwrap());
    let mut sim = Sim::new();
    let _ = sim.run(&vsm::parse(&format!("{init}{text}{probe}")).unwrap());
    let mut keys: Vec<_> = expect.keys().filter(|k| sim.dump.get(*k) != Some(&expect[*k])).collect();
    keys.sort();
    for k in keys.iter().take(6) {
        println!("      {} {} {}: emu={:016x} sim={}", k.0, k.1, k.2, expect[*k], sim.dump.get(*k).map(|v| format!("{v:016x}")).unwrap_or("missing".into()));
    }
}
