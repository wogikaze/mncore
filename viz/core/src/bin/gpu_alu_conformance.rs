//! Conformance test for the GPU ALU backend: one or more VSM lines for every ALU opcode,
//! precision, unsigned variant, input option, zero-flush mask and multi-destination form.
//!
//! The CPU `Sim` executes the generated program line by line; after every PE line the GPU's
//! `aluf`, OMR and T state must match, and at the end all four PE memories are compared too.
//!
//! Usage: gpu_alu_conformance [--list]
//! Exit status: 0 all compared state matches, 1 mismatch or unsupported expression, 2 no GPU.

use std::collections::BTreeSet;

use mncore_sim::gpu::{
    alu_line_from_expr, bfn_line_from_expr_state, AluLine, BfnLine, Gpu,
};
use mncore_sim::machine::{MaskState, GRF_WORDS, LM_WORDS, PES};
use mncore_sim::run::Sim;
use mncore_sim::vsm::{self, Line, Prec};

const LM_LIMIT: u32 = 3584;
const GRF_LIMIT: u32 = 384;
const LM_SRC: u32 = 3900;

enum Action {
    Alu(AluLine),
    Bfn(BfnLine),
}

#[derive(Default)]
struct Builder {
    text: String,
    labels: Vec<String>,
    configs: BTreeSet<String>,
    ops: BTreeSet<String>,
    alloc: [u32; 4],
    config_seq: usize,
    lines: usize,
    rnd_lines: usize,
    ext_lines: usize,
    flush_lines: usize,
    multi_lines: usize,
}

fn mem_char(mem: usize) -> char {
    ['m', 'n', 'r', 's'][mem]
}

impl Builder {
    fn alloc(&mut self, mem: usize, words: u32) -> u32 {
        let limit = if mem < 2 { LM_LIMIT } else { GRF_LIMIT };
        let at = self.alloc[mem];
        assert!(
            at + words <= limit,
            "conformance destination allocation exhausted memory {mem}: {} + {words} > {limit}",
            at
        );
        self.alloc[mem] += words;
        at
    }

    fn line(&mut self, label: &str, text: String) {
        self.labels.push(label.to_string());
        self.text.push_str(&text);
        self.text.push('\n');
        self.lines += 1;
    }

    fn directive(&mut self, text: &str) {
        self.labels.push(String::new());
        self.text.push_str(text);
        self.text.push('\n');
    }
}

fn pchar(prec: Option<Prec>) -> char {
    match prec {
        Some(Prec::D) => 'd',
        Some(Prec::F) => 'f',
        Some(Prec::G) => 'g',
        Some(Prec::H) => 'h',
        Some(Prec::L) => 'l',
        Some(Prec::I) => 'i',
        Some(Prec::S) => 's',
        None => '-',
    }
}

fn src_off(prec: Option<Prec>, second: bool) -> u32 {
    let base = match prec {
        Some(Prec::D) => 384,
        Some(Prec::F | Prec::G) => 400,
        Some(Prec::H) => 416,
        Some(Prec::L | Prec::I | Prec::S) => 432,
        None => 448,
    };
    base + if second { 8 } else { 0 }
}

fn opcode_for(prec: Option<Prec>, name: &str, unsigned: bool) -> String {
    let p = match prec {
        Some(p) => pchar(Some(p)),
        None => '-',
    };
    if prec.is_none() {
        name.to_string()
    } else {
        format!("{}{}{}", if unsigned { "u" } else { "" }, p, name)
    }
}

fn emit_alu(b: &mut Builder, prec: Option<Prec>, name: &str, unsigned: bool, two: bool) {
    let opcode = opcode_for(prec, name, unsigned);
    let label = format!("{opcode}/{}", if unsigned { "unsigned" } else { "signed" });
    b.configs.insert(label.clone());
    b.ops.insert(name.to_string());
    let idx = b.config_seq;
    b.config_seq += 1;

    let off = src_off(prec, false);
    let off2 = src_off(prec, true);
    let a = format!("$llr{off}v");
    let c = format!("$lls{off2}v");
    let (main, other) = if idx % 2 == 0 { (0usize, 1usize) } else { (1usize, 0usize) };

    // Main line: both inputs, four-word destination so the untouched LSB long word is compared.
    let slot = b.alloc(main, 16);
    let dst = format!("$ll{}{}v", mem_char(main), slot);
    let text = if two {
        format!("{opcode} {a} {c} {dst}")
    } else {
        format!("{opcode} {a} {dst}")
    };
    b.line(&label, text);

    // Input options and multiple destinations (memory + T/GRF + OMR).
    let slot2 = b.alloc(other, 4);
    let dst2 = format!("$l{}{}v", mem_char(other), slot2);
    let extra = if idx % 8 == 0 {
        let s = b.alloc(2, 16);
        format!("$llr{}v", s)
    } else {
        "$llt".to_string()
    };
    let omr = format!("$omr{}", 1 + idx % 3);
    let ar = format!("$llr{off}vr");
    let ce = format!("$lls{off2}ve");
    let text2 = if two {
        format!("{opcode} {ar} {ce} {dst2} {extra} {omr}")
    } else {
        format!("{opcode} {ar} {dst2} {extra} {omr}")
    };
    b.line(&label, text2);
    b.rnd_lines += 1;
    if two {
        b.ext_lines += 1;
    }
    b.multi_lines += 1;

    // Zero-flush mask, swapped memories to catch operand-order bugs.
    let slot3 = b.alloc(other, 16);
    let dst3 = format!("$ll{}{}v", mem_char(other), slot3);
    let flush = match idx % 3 {
        0 => "0110",
        1 => "1001",
        _ => "ll1010",
    };
    let a3 = format!("$lls{off}v");
    let c3 = format!("$llr{off2}v");
    let text3 = if two {
        format!("{opcode}/{flush} {a3} {c3} {dst3}")
    } else {
        // Single-input configurations exercise the `e` option here.
        format!("{opcode}/{flush} $lls{off}ve {dst3}")
    };
    b.line(&label, text3);
    b.flush_lines += 1;
    if !two {
        b.ext_lines += 1;
    }

    // An OMR-entry zero flush for a subset.
    if idx % 4 == 0 {
        let slot4 = b.alloc(main, 16);
        let dst4 = format!("$ll{}{}v", mem_char(main), slot4);
        let entry = 1 + idx % 3;
        let text4 = if two {
            format!("{opcode}/$imr{entry} {a} {c} {dst4}")
        } else {
            format!("{opcode}/$imr{entry} {a} {dst4}")
        };
        b.line(&label, text4);
        b.flush_lines += 1;
    }
}

fn emit_bfn(b: &mut Builder, prec: Prec, opcode: &str, arg: Option<u8>) {
    let label = format!("{opcode}/{}", pchar(Some(prec)));
    b.configs.insert(label.clone());
    b.ops.insert(if opcode.starts_with("hbfe") { "bfe" } else { "bfn" }.to_string());
    let idx = b.config_seq;
    b.config_seq += 1;
    let off = src_off(Some(prec), false);
    let a = format!("$llr{off}v");
    let mut op = opcode.to_string();
    if let Some(n) = arg {
        op = format!("{opcode}/{n}");
    }
    let (main, other) = if idx % 2 == 0 { (0usize, 1usize) } else { (1usize, 0usize) };
    let slot = b.alloc(main, 16);
    let dst = format!("$ll{}{}v", mem_char(main), slot);
    b.line(&label, format!("{op} {a} {dst}"));

    let slot2 = b.alloc(other, 4);
    let dst2 = format!("$l{}{}v", mem_char(other), slot2);
    let extra = if idx % 4 == 0 {
        let s = b.alloc(2, 16);
        format!("$llr{}v", s)
    } else {
        "$llt".to_string()
    };
    let omr = format!("$omr{}", 1 + idx % 3);
    let ar = format!("$llr{off}vr");
    b.line(&label, format!("{op} {ar} {dst2} {extra} {omr}"));
    b.rnd_lines += 1;
    b.multi_lines += 1;

    let slot3 = b.alloc(other, 16);
    let dst3 = format!("$ll{}{}v", mem_char(other), slot3);
    let flush = match idx % 3 {
        0 => "0101",
        1 => "ll0011",
        _ => "1010",
    };
    // `hbfn/<n>` already uses the slash for the mantissa length, so always spell the
    // default 9 out when a zero-flush mask is appended.
    let flush_op = if (opcode == "hbfn" || opcode == "hbfe") && arg.is_none() {
        format!("{opcode}/9/{flush}")
    } else {
        format!("{op}/{flush}")
    };
    b.line(&label, format!("{flush_op} {a} {dst3}"));
    b.flush_lines += 1;
}

const FLOAT: &[Option<Prec>] = &[Some(Prec::D), Some(Prec::F), Some(Prec::H)];
const INT: &[Option<Prec>] = &[Some(Prec::L), Some(Prec::I), Some(Prec::S)];
const BOTH: &[Option<Prec>] = &[
    Some(Prec::D),
    Some(Prec::F),
    Some(Prec::H),
    Some(Prec::L),
    Some(Prec::I),
    Some(Prec::S),
];

struct Spec {
    name: &'static str,
    precs: &'static [Option<Prec>],
    inputs: usize,
    unsigned: bool,
}

const SPECS: &[Spec] = &[
    Spec { name: "msl", precs: &[None], inputs: 1, unsigned: false },
    Spec { name: "msr", precs: &[None], inputs: 1, unsigned: false },
    Spec { name: "passa", precs: BOTH, inputs: 1, unsigned: false },
    Spec { name: "inc", precs: INT, inputs: 1, unsigned: true },
    Spec { name: "dec", precs: INT, inputs: 1, unsigned: true },
    Spec { name: "not", precs: INT, inputs: 1, unsigned: false },
    Spec { name: "lnot", precs: INT, inputs: 1, unsigned: false },
    Spec { name: "rsqrt", precs: FLOAT, inputs: 1, unsigned: false },
    Spec { name: "floor", precs: FLOAT, inputs: 1, unsigned: false },
    Spec { name: "ftoi", precs: FLOAT, inputs: 1, unsigned: true },
    Spec { name: "max", precs: BOTH, inputs: 2, unsigned: true },
    Spec { name: "min", precs: BOTH, inputs: 2, unsigned: true },
    Spec { name: "packbit", precs: BOTH, inputs: 2, unsigned: false },
    Spec { name: "and", precs: INT, inputs: 2, unsigned: false },
    Spec { name: "or", precs: INT, inputs: 2, unsigned: false },
    Spec { name: "xor", precs: INT, inputs: 2, unsigned: false },
    Spec { name: "add", precs: INT, inputs: 2, unsigned: true },
    Spec { name: "sub", precs: INT, inputs: 2, unsigned: true },
    Spec { name: "lsl", precs: INT, inputs: 2, unsigned: false },
    Spec { name: "lsr", precs: INT, inputs: 2, unsigned: true },
    Spec { name: "bsl", precs: INT, inputs: 2, unsigned: false },
    Spec { name: "bsr", precs: INT, inputs: 2, unsigned: false },
    Spec { name: "relu", precs: FLOAT, inputs: 2, unsigned: false },
    Spec { name: "relu0", precs: FLOAT, inputs: 2, unsigned: false },
    Spec { name: "relu1", precs: FLOAT, inputs: 2, unsigned: false },
    Spec { name: "relu2", precs: FLOAT, inputs: 2, unsigned: false },
    Spec { name: "relu3", precs: FLOAT, inputs: 2, unsigned: false },
    Spec { name: "lrelud", precs: FLOAT, inputs: 2, unsigned: false },
    Spec { name: "lreluo", precs: FLOAT, inputs: 2, unsigned: false },
    Spec { name: "ilrelud", precs: FLOAT, inputs: 2, unsigned: false },
];

fn build(b: &mut Builder) {
    for spec in SPECS {
        for &prec in spec.precs {
            emit_alu(b, prec, spec.name, false, spec.inputs == 2);
            if spec.unsigned {
                emit_alu(b, prec, spec.name, true, spec.inputs == 2);
            }
        }
    }

    for (prec, op, arg) in [
        (Prec::D, "dbfn", None),
        (Prec::F, "fbfn", None),
        (Prec::G, "gbfn", None),
        (Prec::H, "hbfn", None),
        (Prec::H, "hbfn", Some(6)),
        (Prec::H, "hbfn", Some(7)),
        (Prec::H, "hbfn", Some(8)),
        (Prec::H, "hbfn", Some(9)),
        (Prec::H, "hbfe", None),
        (Prec::H, "hbfe", Some(6)),
        (Prec::H, "hbfe", Some(7)),
        (Prec::H, "hbfe", Some(8)),
        (Prec::H, "hbfe", Some(9)),
    ] {
        emit_bfn(b, prec, op, arg);
    }

    // zero, imm and immu forms with several destinations.
    let z0 = b.alloc(0, 16);
    let z1 = b.alloc(2, 16);
    let z2 = b.alloc(1, 4);
    b.configs.insert("zero".into());
    b.ops.insert("zero".into());
    b.line("zero", format!("zero $llm{z0}v $llt $omr1"));
    b.multi_lines += 1;
    b.line("zero", format!("zero $llr{z1}v"));
    b.line("zero", format!("zero $ln{z2}v"));
    b.configs.insert("imm".into());
    b.configs.insert("immu".into());
    b.ops.insert("imm".into());
    let i0 = b.alloc(1, 16);
    let i1 = b.alloc(2, 4);
    let i2 = b.alloc(1, 4);
    b.line("imm", format!("imm f\"0.5\" $lln{i0}v $llt $omr2"));
    b.multi_lines += 1;
    b.line("immu", format!("immu i\"1\" $llr{i1}v"));
    b.line("imm", format!("imm s\"1\" $ln{i2}v"));

    // A T source needs a value: copy one source bank long word into T first.
    b.line("t-setup", format!("ipassa $llr432v $llt"));
    b.ops.insert("passa".into());

    // Input operand forms: T, fixed table 3.5, LM source, and aluf forwarding.
    let (s0, s1) = (b.alloc(1, 16), b.alloc(2, 16));
    b.configs.insert("operand/t+f".into());
    b.line("operand/t+f", format!("hpassa $llt $lln{s0}v"));
    b.line("operand/t+f", format!("ipassa $msb1 $llr{s1}v"));
    b.line("operand/t+f", format!("spassa $peid $lln{s0}v"));
    b.line("operand/t+f", format!("dpassa $l2bid $lln{s0}v"));
    let lm0_src = b.alloc(0, 16);
    b.line("operand/lm", format!("fpassa $llm{LM_SRC}v $llr{lm0_src}v"));
    b.line("operand/lm", format!("hrelu $llm{LM_SRC}v $lls416v $lln{s0}v"));
    b.line("operand/ext+rnd-on-t", format!("fpassa $lltr $lln{s0}v"));
    // aluf forwarding: the immediately preceding line produced aluf.
    b.line("operand/aluf", format!("iadd $aluf $lls432v $lln{s0}v"));
    b.line("operand/aluf", format!("frelu $aluf $llr400v $lln{s1}v"));
    b.multi_lines += 1;

    // Fixed-value inputs (table 3.5) at every ALU precision, plus T sources and both inputs
    // rounded independently.
    const FIXED: [&str; 6] = ["$l2bid", "$l1bid", "$mabid", "$peid", "$subpeid", "$msb1"];
    for &prec in &[
        Prec::D,
        Prec::F,
        Prec::H,
        Prec::L,
        Prec::I,
        Prec::S,
    ] {
        let op = format!("{}passa", pchar(Some(prec)));
        for (i, fixed) in FIXED.iter().enumerate() {
            let mem = i % 2;
            let slot = b.alloc(mem, 4);
            b.line(
                "operand/fixed",
                format!("{op} {fixed} $l{}{}v", mem_char(mem), slot),
            );
        }
        let mem = if prec as u8 % 2 == 0 { 0 } else { 1 };
        let slot = b.alloc(mem, 4);
        b.line(
            "operand/t",
            format!("{op} $llt $l{}{}v", mem_char(mem), slot),
        );
    }
    b.configs.insert("operand/fixed".into());
    b.configs.insert("operand/t".into());
    let r0 = b.alloc(0, 16);
    let r1 = b.alloc(1, 16);
    let r2 = b.alloc(0, 16);
    b.configs.insert("operand/rnd-both".into());
    b.line(
        "operand/rnd-both",
        format!("fmax $llr400vr $lls408vr $llm{r0}v"),
    );
    b.line(
        "operand/rnd-both",
        format!("dmax $llr384vr $lls392vr $lln{r1}v"),
    );
    b.line(
        "operand/rnd-both",
        format!("imax $llr432vr $lls440vr $llm{r2}v"),
    );
    b.rnd_lines += 3;

    // Explicit single-line destination masks (with and without `ll`) and `$nowrite`.
    let e0 = b.alloc(0, 16);
    let e1 = b.alloc(1, 4);
    b.configs.insert("mask/explicit".into());
    b.line(
        "mask/explicit",
        format!("iadd $llr432v $lls440v $llm{e0}v/0110 $ln{e1}v"),
    );
    let e2 = b.alloc(1, 16);
    b.line(
        "mask/explicit",
        format!("fpassa $llr400v $lln{e2}v/ll1010 $omr5"),
    );
    b.multi_lines += 1;
    b.line("mask/explicit", "zero $nowrite".to_string());
    let e3 = b.alloc(1, 16);
    b.line(
        "mask/explicit",
        format!("fpassa $llr400v $omr6/1010 $lln{e3}v"),
    );
    b.line("mask/explicit", "hpassa $llr416v $llt/0110".to_string());

    // Multi-line write mask on LM0/LM1 destinations.
    b.line("omr-setup", "ilnot $subpeid $omr4".to_string());
    b.directive("maskmn 1");
    let m0 = b.alloc(0, 4);
    let m1 = b.alloc(1, 4);
    b.configs.insert("mask/directive".into());
    b.line("mask/directive", format!("iadd $llr432v $lls440v $lm{m0}v $ln{m1}v"));
    b.directive("maskllmn 1");
    let m2 = b.alloc(0, 16);
    b.line("mask/directive", format!("ixor $llr432v $lls440v $llm{m2}v"));
    b.directive("mask 0");
}

fn cpu_aluf(sim: &Sim) -> Vec<u32> {
    sim.m
        .pes
        .iter()
        .flat_map(|p| p.aluf.iter().flat_map(|bus| bus.iter().copied()))
        .collect()
}

fn cpu_mask(sim: &Sim) -> Vec<u32> {
    sim.m
        .pes
        .iter()
        .flat_map(|p| p.mask.iter().map(|&e| e as u32))
        .collect()
}

fn cpu_t(sim: &Sim) -> Vec<u32> {
    sim.m.pes.iter().flat_map(|p| p.t.iter().copied()).collect()
}

fn first_mismatch(cpu: &[u32], gpu: &[u32], name: &str, label: &str, text: &str) -> bool {
    if cpu == gpu {
        return false;
    }
    let n = cpu.len().min(gpu.len());
    let mut index = n;
    for i in 0..n {
        if cpu[i] != gpu[i] {
            index = i;
            break;
        }
    }
    println!("mismatch in {name} at [{index}] for `{text}` ({label})");
    if index < n {
        println!(
            "  pe {} word {}: cpu {:08x} gpu {:08x}",
            index / 16,
            index % 16,
            cpu[index],
            gpu[index]
        );
    }
    true
}

fn main() {
    let list = std::env::args().any(|a| a == "--list");
    let mut b = Builder::default();
    build(&mut b);

    let program = match vsm::parse(&b.text) {
        Ok(p) => p,
        Err(e) => {
            eprintln!("generated program does not parse: {e}");
            std::process::exit(1);
        }
    };
    assert_eq!(program.len(), b.labels.len(), "label/program line mismatch");

    let lm_len = PES * LM_WORDS;
    let grf_len = PES * GRF_WORDS;
    let mut state = 0x0bad_c0de_1234_5678u64;
    let mut next = || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state
    };
    let mut lm0: Vec<u32> = (0..lm_len).map(|_| next() as u32).collect();
    let mut lm1: Vec<u32> = (0..lm_len).map(|_| next() as u32).collect();
    let mut grf0: Vec<u32> = (0..grf_len).map(|_| next() as u32).collect();
    let mut grf1: Vec<u32> = (0..grf_len).map(|_| next() as u32).collect();

    // Overlay the source banks with interesting values so every precision sees zeros,
    // infinities, extrema and random patterns rather than only random words.
    let f32_values: [u32; 16] = [
        0, 0x8000_0000, 0x3f80_0000, 0xbf80_0000, 0x3f00_0000, 0xbf00_0000,
        0x7f7f_ffff, 0xff7f_ffff, 0x7f80_0000, 0xff80_0000, 0x0080_0000,
        0x0000_0001, 0x8000_0001, 0x4b00_0000, 0xcb00_0000, 0x3f7f_ffff,
    ];
    let half_values: [u16; 16] = [
        0x0000, 0x8000, 0x3e00, 0xbe00, 0x3c00, 0xbc00, 0x7bff, 0xfbff,
        0x7c00, 0xfc00, 0x0400, 0x8400, 0x0001, 0x8001, 0x3d00, 0xbd00,
    ];
    let f64_values: [(u32, u32); 16] = [
        (0, 0),
        (0x8000_0000, 0),
        (0x3ff0_0000, 0),
        (0xbff0_0000, 0),
        (0x3fe0_0000, 0),
        (0xbfe0_0000, 0),
        (0x7fef_ffff, 0xffff_ffff),
        (0xffef_ffff, 0xffff_ffff),
        (0x7ff0_0000, 0),
        (0xfff0_0000, 0),
        (0x0010_0000, 0),
        (0x0000_0000, 1),
        (0x8000_0000, 1),
        (0x4340_0000, 0),
        (0xc340_0000, 0),
        (0x3fef_ffff, 0xffff_ffff),
    ];
    for pe in 0..PES {
        let base = pe * GRF_WORDS;
        for i in 0..16 {
            // f32 bank: 400..415
            grf0[base + 400 + i] = f32_values[i];
            grf1[base + 400 + i] = f32_values[(i * 5 + 3) % 16];
            // half bank: 416..431, two halves per word
            let h0 = half_values[i % 16];
            let h1 = half_values[(i * 7 + 5) % 16];
            grf0[base + 416 + i] = ((h0 as u32) << 16) | h1 as u32;
            grf1[base + 416 + i] = ((h1 as u32) << 16) | h0 as u32;
            // double bank: 384..415, two words per value
            let d0 = f64_values[i % 16];
            let d1 = f64_values[(i * 3 + 7) % 16];
            grf0[base + 384 + 2 * i] = d0.0;
            grf0[base + 384 + 2 * i + 1] = d0.1;
            grf1[base + 384 + 2 * i] = d1.0;
            grf1[base + 384 + 2 * i + 1] = d1.1;
        }
        // Integer source bank 432..447 keeps the random words but makes a few of them special.
        grf0[base + 432] = 0;
        grf0[base + 433] = u32::MAX;
        grf0[base + 434] = 0x8000_0000;
        grf1[base + 432] = 0x5555_5555;
        grf1[base + 433] = 0xaaaa_aaaa;
        // LM source bank.
        let lm_base = pe * LM_WORDS;
        for i in 0..16 {
            lm0[lm_base + (LM_SRC as usize + i) % LM_WORDS] = f32_values[i];
            lm1[lm_base + (LM_SRC as usize + i) % LM_WORDS] = f32_values[(i * 11 + 1) % 16];
        }
    }

    let mut sim = Sim::new();
    sim.m.mem.lm0.copy_from_slice(&lm0);
    sim.m.mem.lm1.copy_from_slice(&lm1);
    sim.m.mem.grf0.copy_from_slice(&grf0);
    sim.m.mem.grf1.copy_from_slice(&grf1);

    let gpu = match Gpu::new() {
        Ok(gpu) => gpu,
        Err(error) => {
            eprintln!("gpu unavailable: {error}");
            std::process::exit(2);
        }
    };
    let gpu_state = gpu.allocate_state().expect("allocate state");
    gpu.upload_state(&gpu_state, &lm0, &lm1, &grf0, &grf1)
        .expect("upload state");

    let mut mask_state = MaskState::default();
    let mut checked = 0usize;
    let mut failures = 0usize;
    let mut unsupported = 0usize;

    for (((_, line), label), _) in program.iter().zip(b.labels.iter()).zip(0..) {
        match line {
            Line::MaskDirective {
                wl,
                targets,
                entry,
            } => {
                sim.exec(line).expect("cpu mask directive");
                mask_state = MaskState {
                    wl: *wl,
                    targets: *targets,
                    entry: *entry,
                };
            }
            Line::Pe(exprs) => {
                sim.exec(line).unwrap_or_else(|e| {
                    panic!("cpu line `{}` ({label}): {e:?}", exprs.first().map(|e| &e.text).unwrap_or(&String::new()))
                });
                let mut actions = Vec::new();
                for expr in exprs {
                    if let Some(alu) = alu_line_from_expr(expr, mask_state) {
                        actions.push(Action::Alu(alu));
                    } else if let Some(bfn) = bfn_line_from_expr_state(expr, mask_state) {
                        actions.push(Action::Bfn(bfn));
                    } else {
                        eprintln!("unsupported ALU expression for GPU: {}", expr.text);
                        unsupported += 1;
                        continue;
                    }
                }
                for action in &actions {
                    match action {
                        Action::Alu(line) => gpu.run_alu_line(&gpu_state, line).expect("alu line"),
                        Action::Bfn(line) => gpu.run_bfn_line(&gpu_state, line).expect("bfn line"),
                    }
                }
                gpu.sync().expect("sync");
                let gpu_aluf = gpu.download_aluf(&gpu_state).expect("download aluf");
                let gpu_mask = gpu.download_mask(&gpu_state).expect("download mask");
                let gpu_t = gpu.download_t(&gpu_state).expect("download t");
                let text = exprs.first().map(|e| e.text.as_str()).unwrap_or("");
                let ca = cpu_aluf(&sim);
                let cm = cpu_mask(&sim);
                let ct = cpu_t(&sim);
                if first_mismatch(&ca, &gpu_aluf, "aluf", label, text) {
                    failures += 1;
                }
                if first_mismatch(&cm, &gpu_mask, "omr", label, text) {
                    failures += 1;
                }
                if first_mismatch(&ct, &gpu_t, "t", label, text) {
                    failures += 1;
                }
                checked += actions.len();
            }
            other => panic!("unexpected generated line: {other:?}"),
        }
    }

    // Final state: all four memories plus the forwarding/mask/T arrays.
    let mut out = (
        vec![0u32; lm_len],
        vec![0u32; lm_len],
        vec![0u32; grf_len],
        vec![0u32; grf_len],
    );
    gpu.download_state(&gpu_state, &mut out.0, &mut out.1, &mut out.2, &mut out.3)
        .expect("download state");
    let gpu_aluf = gpu.download_aluf(&gpu_state).expect("download aluf");
    let gpu_mask = gpu.download_mask(&gpu_state).expect("download mask");
    let gpu_t = gpu.download_t(&gpu_state).expect("download t");
    for (name, cpu, gpu_mem) in [
        ("lm0", sim.m.mem.lm0.as_slice(), out.0.as_slice()),
        ("lm1", sim.m.mem.lm1.as_slice(), out.1.as_slice()),
        ("grf0", sim.m.mem.grf0.as_slice(), out.2.as_slice()),
        ("grf1", sim.m.mem.grf1.as_slice(), out.3.as_slice()),
    ] {
        if cpu != gpu_mem {
            let mut count = 0usize;
            let mut first = None;
            for (i, (a, b)) in cpu.iter().zip(gpu_mem).enumerate() {
                if a != b {
                    if first.is_none() {
                        first = Some(i);
                    }
                    count += 1;
                }
            }
            let width = if name.starts_with("lm") { LM_WORDS } else { GRF_WORDS };
            if let Some(i) = first {
                println!(
                    "final {name} mismatch at pe {} addr {}: cpu {:08x} gpu {:08x}",
                    i / width,
                    i % width,
                    cpu[i],
                    gpu_mem[i]
                );
            }
            println!("final {name}: {count} mismatched words");
            failures += 1;
        }
    }
    let ca = cpu_aluf(&sim);
    let cm = cpu_mask(&sim);
    let ct = cpu_t(&sim);
    if first_mismatch(&ca, &gpu_aluf, "aluf", "final", "") {
        failures += 1;
    }
    if first_mismatch(&cm, &gpu_mask, "omr", "final", "") {
        failures += 1;
    }
    if first_mismatch(&ct, &gpu_t, "t", "final", "") {
        failures += 1;
    }

    let ops: Vec<&str> = b.ops.iter().map(|s| s.as_str()).collect();
    println!("opcodes: {}", ops.join(" "));
    println!(
        "{} configs, {} opcodes, {} PE lines, {} GPU actions, {} rnd lines, {} ext lines, {} flush lines, {} multi-dst lines",
        b.configs.len(),
        b.ops.len(),
        b.lines,
        checked,
        b.rnd_lines,
        b.ext_lines,
        b.flush_lines,
        b.multi_lines
    );
    if list {
        for c in &b.configs {
            println!("config {c}");
        }
    }
    if unsupported != 0 {
        println!("FAIL: {unsupported} unsupported expressions");
        std::process::exit(1);
    }
    if failures != 0 {
        println!("FAIL: {failures} mismatching state groups");
        std::process::exit(1);
    }
    println!("PASS: aluf, OMR, T and all four memories match");
    if checked == 0 {
        println!("FAIL: no GPU actions were checked");
        std::process::exit(1);
    }
}
