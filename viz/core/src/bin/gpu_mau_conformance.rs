//! Conformance test for the GPU MAU and matrix-register backend.
//!
//! The generator below emits one expression per PE line and covers:
//!
//! * vector MAU `d/f/g/h` `vfma/vmul/vadd/vpassa`, `(u|d)` half selection,
//!   output rounding, word/long/long-long sources and destinations, sign
//!   inversion, precision extension and reduction, T and every forwarding
//!   register, write masks, zero-flush masks, OMR/T destinations and multiple
//!   destinations;
//! * matrix MAU `dmfma/dmmul/fmfma/fmmul/gmfma/gmmul/hmfma/hmmul`, both faces,
//!   `(u|d)`, output rounding, list/T/forwarding x and y sources, masks,
//!   flush, T/OMR destinations and multiple destinations;
//! * matrix writes `dmwrite/fmwrite/gmwrite/hmwrite` with every access length,
//!   both faces, row wrap, neg/e/r and forwarding/list sources;
//! * matrix reads `dmread/fmread/gmread/hmread` with both faces, row wrap,
//!   `$nowrite`, masks, flush, T/OMR destinations and multiple destinations.
//!
//! The CPU `Sim` executes the same program text. After every line the state the
//! line can change (mauf/aluf/mreadf, the matrix registers, OMR or T) is
//! compared; at the end all four PE memories and every remaining state are
//! compared. Exit status: 0 match, 1 mismatch or unsupported form, 2 no GPU.
//!
//! Usage: gpu_mau_conformance [--list]

use std::collections::{BTreeMap, BTreeSet};

use mncore_sim::gpu::{
    alu_line_from_expr, mat_mau_line_from_expr, mat_read_line_from_expr,
    mat_write_line_from_expr, mau_line_from_expr, AluDstDesc, AluLine, Gpu, MatMauLine,
    MatReadLine, MatWriteLine, MauLine, MAT_WORDS,
};
use mncore_sim::machine::{MaskState, GRF_WORDS, LM_WORDS, PES};
use mncore_sim::run::Sim;
use mncore_sim::vsm::{self, Line};

#[derive(Clone, Copy)]
enum Action {
    Alu(AluLine),
    Mau(MauLine),
    MatWrite(MatWriteLine),
    MatRead(MatReadLine),
    MatMau(MatMauLine),
}

struct Entry {
    label: String,
    text: String,
    line: Line,
    action: Option<Action>,
}

struct Builder {
    entries: Vec<Entry>,
    configs: BTreeSet<String>,
    ops: BTreeSet<String>,
    counts: BTreeMap<String, usize>,
    mask: MaskState,
    lines: usize,
}

impl Builder {
    fn new() -> Builder {
        Builder {
            entries: Vec::new(),
            configs: BTreeSet::new(),
            ops: BTreeSet::new(),
            counts: BTreeMap::new(),
            mask: MaskState::default(),
            lines: 0,
        }
    }

    fn bump(&mut self, key: &str) {
        *self.counts.entry(key.to_string()).or_default() += 1;
    }

    /// Parses exactly one generated line, records the matching GPU descriptor,
    /// and advances the multi-line mask directive state.
    fn emit(&mut self, label: &str, text: &str) {
        let parsed = vsm::parse(text).unwrap_or_else(|e| panic!("generated line `{text}`: {e}"));
        assert_eq!(parsed.len(), 1, "one line expected for `{text}`");
        let line = parsed[0].1.clone();
        let action = match &line {
            Line::MaskDirective {
                wl,
                targets,
                entry,
            } => {
                self.mask = MaskState {
                    wl: *wl,
                    targets: *targets,
                    entry: *entry,
                };
                None
            }
            Line::Pe(exprs) => {
                assert_eq!(exprs.len(), 1, "one expression expected in `{text}`");
                let expr = &exprs[0];
                let action = if let Some(line) = alu_line_from_expr(expr, self.mask) {
                    Action::Alu(line)
                } else if let Some(line) = mau_line_from_expr(expr, self.mask) {
                    self.ops.insert("vector-mau".into());
                    Action::Mau(line)
                } else if let Some(line) = mat_write_line_from_expr(expr) {
                    self.ops.insert("mat-write".into());
                    Action::MatWrite(line)
                } else if let Some(line) = mat_read_line_from_expr(expr, self.mask) {
                    self.ops.insert("mat-read".into());
                    Action::MatRead(line)
                } else if let Some(line) = mat_mau_line_from_expr(expr, self.mask) {
                    self.ops.insert("mat-mau".into());
                    Action::MatMau(line)
                } else {
                    panic!("no GPU descriptor for generated line `{text}` ({:?})", expr.op);
                };
                Some(action)
            }
            other => panic!("generated line `{text}` parsed as {other:?}"),
        };
        self.entries.push(Entry {
            label: label.to_string(),
            text: text.to_string(),
            line,
            action,
        });
        self.lines += 1;
    }

    fn directive(&mut self, label: &str, text: &str) {
        self.emit(label, text);
    }
}

// ---------------------------------------------------------------------------
// Text helpers
// ---------------------------------------------------------------------------

fn mchar(mem: usize) -> char {
    ['m', 'n', 'r', 's'][mem]
}

fn pchar(prec: &str) -> char {
    match prec {
        "d" => 'd',
        "f" => 'f',
        "g" => 'g',
        "h" => 'h',
        _ => unreachable!(),
    }
}

fn mem_tok(mem: usize, wl: usize, addr: u32) -> String {
    let prefix = match wl {
        1 => "",
        2 => "l",
        4 => "ll",
        _ => unreachable!(),
    };
    format!("${prefix}{}{}v", mchar(mem), addr)
}

fn opts(tok: &str, neg: bool, ext: bool, rnd: bool) -> String {
    format!(
        "{}{}{}{}",
        if neg { "-" } else { "" },
        tok,
        if ext { "e" } else { "" },
        if rnd { "r" } else { "" }
    )
}

fn kind_name(kind: usize) -> &'static str {
    ["fma", "mul", "add", "passa"][kind]
}

fn vec_opcode(prec: &str, kind: usize, half: usize, round: bool) -> String {
    let h = match half {
        0 => "",
        1 => "u",
        2 => "d",
        _ => unreachable!(),
    };
    format!(
        "{}v{}{}{}",
        pchar(prec),
        kind_name(kind),
        h,
        if round { "r" } else { "" }
    )
}

fn mat_opcode(prec: &str, kind: usize, half: usize, round: bool) -> String {
    let h = match half {
        0 => "",
        1 => "u",
        2 => "d",
        _ => unreachable!(),
    };
    format!(
        "{}m{}{}{}",
        pchar(prec),
        kind_name(kind),
        h,
        if round { "r" } else { "" }
    )
}

fn src_addr(mem: usize, slot: usize) -> u32 {
    if mem < 2 {
        3072 + (slot % 32) as u32 * 8
    } else {
        256 + (slot % 32) as u32 * 8
    }
}

fn dst_addr(mem: usize, slot: usize) -> u32 {
    if mem < 2 {
        16 + (slot % 64) as u32 * 8
    } else {
        8 + (slot % 8) as u32 * 8
    }
}

fn pick_mem(used: &[usize], slot: usize) -> usize {
    (0..4)
        .find(|m| !used.contains(m))
        .unwrap_or((slot + used.len()) % 4)
}

// ---------------------------------------------------------------------------
// Generator
// ---------------------------------------------------------------------------

fn emit_vector(b: &mut Builder) {
    for prec in ["d", "f", "g", "h"] {
        for kind in 0..4 {
            // (u|d) is documented for double; the CPU and GPU accept it for
            // every vector precision, so cover all of them.
            let halves: &[usize] = &[0, 1, 2];
            for &half in halves {
                let rounds: &[bool] = if matches!(prec, "d" | "h") {
                    &[false, true]
                } else {
                    &[false]
                };
                for &round in rounds {
                    let opcode = vec_opcode(prec, kind, half, round);
                    b.configs.insert(opcode.clone());
                    let mut slot = b.lines;
                    let n_src = match kind {
                        0 => 3,
                        1 | 2 => 2,
                        _ => 1,
                    };
                    let src_mems: Vec<usize> = match n_src {
                        3 => vec![0, 2, 1],
                        2 => vec![0, 2],
                        _ => vec![0],
                    };
                    // An alternate bank set writes LM0/GRF0 destinations too.
                    let alt_mems: Vec<usize> = match n_src {
                        3 => vec![1, 3, 2],
                        2 => vec![1, 3],
                        _ => vec![1],
                    };
                    let dst_mem = pick_mem(&src_mems, slot);
                    let dst = dst_addr(dst_mem, slot);
                    let sources_in = |mems: &[usize],
                                      slot: usize,
                                      wl: usize,
                                      neg: bool,
                                      ext: bool,
                                      rnd: bool|
                     -> Vec<String> {
                        (0..n_src)
                            .map(|i| {
                                let mem = mems[i];
                                let addr = src_addr(mem, slot + i);
                                let tok = mem_tok(mem, wl, addr);
                                let (e, r) = if i + 1 == n_src {
                                    // The last source of add/fma uses the c format.
                                    if prec == "h" && kind != 0 && kind != 2 {
                                        (false, false)
                                    } else {
                                        (ext, rnd)
                                    }
                                } else {
                                    (ext, rnd)
                                };
                                opts(&tok, neg && i == 0, e, r)
                            })
                            .collect()
                    };
                    let sources = |slot: usize, wl: usize, neg: bool, ext: bool, rnd: bool| {
                        sources_in(&src_mems, slot, wl, neg, ext, rnd)
                    };
                    let line = |srcs: Vec<String>, dst_text: &str| {
                        format!("{opcode} {} {dst_text}", srcs.join(" "))
                    };

                    // Word, long and long-long accesses.
                    for (wl, tag) in [(2usize, "wl2"), (4, "wl4"), (1, "wl1")] {
                        let srcs = sources(slot, wl, false, false, false);
                        let d = mem_tok(dst_mem, if wl == 1 { 2 } else { wl }, dst);
                        let text = line(srcs, &d);
                        b.emit(&format!("{opcode}/{tag}"), &text);
                        b.bump(tag);
                        slot += 1;
                    }

                    // Alternate source banks and destination banks, covering
                    // writes to LM0/GRF0.
                    let alt_dst_mem = pick_mem(&alt_mems, slot);
                    let alt_dst = dst_addr(alt_dst_mem, slot);
                    let srcs = sources_in(&alt_mems, slot, 2, false, false, false);
                    let d = mem_tok(alt_dst_mem, 2, alt_dst);
                    b.emit(&format!("{opcode}/alt"), &line(srcs, &d));
                    b.bump("alt");

                    // A word-length destination and $nowrite.
                    let srcs = sources(slot, 2, false, false, false);
                    let d = mem_tok(dst_mem, 1, dst);
                    b.emit(&format!("{opcode}/wl1-dst"), &line(srcs, &d));
                    b.bump("wl1-dst");

                    let srcs = sources(slot, 2, false, false, false);
                    b.emit(&format!("{opcode}/nowrite"), &line(srcs, "$nowrite"));
                    b.bump("nowrite");

                    // An explicit OMR-entry write mask.
                    let srcs = sources(slot, 2, false, false, false);
                    let d = format!("{}/$imr1", mem_tok(dst_mem, 2, dst_addr(dst_mem, slot)));
                    b.emit(&format!("{opcode}/imr-mask"), &line(srcs, &d));
                    b.bump("imr-mask");
                    slot += 1;

                    // Sign inversion on the first input.
                    let srcs = sources(slot, 2, true, false, false);
                    let d = mem_tok(dst_mem, 2, dst_addr(dst_mem, slot));
                    b.emit(
                        &format!("{opcode}/neg"),
                        &line(srcs, &d),
                    );
                    b.bump("neg");

                    // Precision extension and reduction where the SDM allows them.
                    let ext_ok = prec != "h" || matches!(kind, 0 | 2);
                    if ext_ok {
                        let srcs: Vec<String> = (0..n_src)
                            .map(|i| {
                                let mem = src_mems[i];
                                let addr = src_addr(mem, slot + i);
                                let tok = mem_tok(mem, 2, addr);
                                let is_c = i + 1 == n_src && matches!(kind, 0 | 2);
                                let e = if prec == "h" {
                                    is_c
                                } else {
                                    !(prec == "h")
                                };
                                opts(&tok, false, e, false)
                            })
                            .collect();
                        let d = mem_tok(dst_mem, 2, dst_addr(dst_mem, slot));
                        b.emit(&format!("{opcode}/ext"), &line(srcs, &d));
                        b.bump("ext");
                        slot += 1;
                    }
                    if prec != "d" {
                        let srcs: Vec<String> = (0..n_src)
                            .map(|i| {
                                let mem = src_mems[i];
                                let addr = src_addr(mem, slot + i);
                                // `r` reads wider elements; use the long-long
                                // operand so all lanes have real values.
                                let tok = mem_tok(mem, 4, addr);
                                let is_c = i + 1 == n_src && matches!(kind, 0 | 2);
                                let r = !(prec == "h" && is_c);
                                opts(&tok, false, false, r)
                            })
                            .collect();
                        let d = mem_tok(dst_mem, 2, dst_addr(dst_mem, slot));
                        b.emit(&format!("{opcode}/rnd"), &line(srcs, &d));
                        b.bump("rnd");
                        slot += 1;
                    }

                    // Zero-flush mask and multiple destinations (PE memory, T, OMR).
                    let srcs = sources(slot, 2, false, false, false);
                    let d = mem_tok(dst_mem, 2, dst_addr(dst_mem, slot));
                    let text = format!(
                        "{opcode}/0110 {} {d} $t $omr{}",
                        srcs.join(" "),
                        1 + slot % 3
                    );
                    b.emit(&format!("{opcode}/flush"), &text);
                    b.bump("flush");
                    slot += 1;

                    // Explicit masks on the T and OMR destinations.
                    let srcs = sources(slot, 2, false, false, false);
                    let text = format!(
                        "{opcode} {} {}/1010 $t/0110 $omr1/1001",
                        srcs.join(" "),
                        mem_tok(dst_mem, 2, dst_addr(dst_mem, slot))
                    );
                    b.emit(&format!("{opcode}/dst-masks"), &text);
                    b.bump("dst-masks");
                    slot += 1;

                    // An explicit per-destination mask, then a long-word mask.
                    let srcs = sources(slot, 2, false, false, false);
                    let d = format!(
                        "{}/1010",
                        mem_tok(dst_mem, 2, dst_addr(dst_mem, slot))
                    );
                    b.emit(&format!("{opcode}/mask"), &line(srcs, &d));
                    b.bump("mask");
                    slot += 1;

                    let srcs = sources(slot, 2, false, false, false);
                    let d = format!(
                        "{}/ll0110",
                        mem_tok(dst_mem, 4, dst_addr(dst_mem, slot) & !3)
                    );
                    b.emit(&format!("{opcode}/llmask"), &line(srcs, &d));
                    b.bump("llmask");
                    slot += 1;

                    // Multi-line mask directive.
                    let target = mchar(dst_mem).to_string();
                    b.directive(
                        &format!("{opcode}/directive"),
                        &format!("mask{target} 1"),
                    );
                    let srcs = sources(slot, 2, false, false, false);
                    let d = mem_tok(dst_mem, 2, dst_addr(dst_mem, slot));
                    b.emit(&format!("{opcode}/directive-line"), &line(srcs, &d));
                    b.directive(&format!("{opcode}/directive-off"), "mask 0");
                    b.bump("directive");
                    slot += 1;

                    // Forwarding and T sources. Each consumer immediately follows
                    // its producer, because a step without the producer disables
                    // the forwarding register in the CPU model.
                    let consumer = |src_tok: String, slot: usize| -> String {
                        let mut srcs: Vec<String> = vec![src_tok];
                        for i in 1..n_src {
                            let mem = src_mems[i];
                            let tok = mem_tok(mem, 2, src_addr(mem, slot + i));
                            srcs.push(tok);
                        }
                        line(srcs, &mem_tok(dst_mem, 2, dst_addr(dst_mem, slot)))
                    };

                    // Input options on a forwarding or T source. Each is a
                    // separate operand suffix (`e` and `r` can not be combined).
                    let fa_opts: &[char] = match prec {
                        "d" => &['e'],
                        "h" => &['r'],
                        _ => &['e', 'r'],
                    };

                    // aluf: an ALU pass-through writes it.
                    let alu_dst = mem_tok(pick_mem(&[0], slot), 2, dst_addr(pick_mem(&[0], slot), slot));
                    let alu_src = mem_tok(0, 4, src_addr(0, slot));
                    let alu_text = format!(
                        "{}passa {alu_src} {alu_dst}",
                        if prec == "g" { 'f' } else { pchar(prec) }
                    );
                    b.emit(&format!("{opcode}/aluf-producer"), &alu_text);
                    b.emit(
                        &format!("{opcode}/aluf"),
                        &consumer("$aluf".into(), slot),
                    );
                    for opt in fa_opts {
                        b.emit(&format!("{opcode}/aluf-producer2"), &alu_text);
                        b.emit(
                            &format!("{opcode}/aluf-{opt}"),
                            &consumer(
                                opts(
                                    "$aluf",
                                    false,
                                    *opt == 'e',
                                    *opt == 'r',
                                ),
                                slot,
                            ),
                        );
                    }
                    b.bump("forward-aluf");
                    slot += 1;

                    // mauf: a vector MAU pass-through writes it.
                    let mau_src = mem_tok(0, 4, src_addr(0, slot));
                    let mau_text = format!(
                        "{} {mau_src} $nowrite",
                        if prec == "h" { "hvpassar" } else { &format!("{}vpassa", pchar(prec)) }
                    );
                    b.emit(&format!("{opcode}/mauf-producer"), &mau_text);
                    b.emit(
                        &format!("{opcode}/mauf"),
                        &consumer("$mauf".into(), slot),
                    );
                    for opt in fa_opts {
                        b.emit(&format!("{opcode}/mauf-producer2"), &mau_text);
                        b.emit(
                            &format!("{opcode}/mauf-{opt}"),
                            &consumer(
                                opts(
                                    "$mauf",
                                    false,
                                    *opt == 'e',
                                    *opt == 'r',
                                ),
                                slot,
                            ),
                        );
                    }
                    b.bump("forward-mauf");
                    slot += 1;

                    // T: a vector MAU pass-through writes it.
                    let t_src = mem_tok(0, 4, src_addr(0, slot));
                    let t_text = format!(
                        "{} {t_src} $t",
                        if prec == "h" { "hvpassar" } else { &format!("{}vpassa", pchar(prec)) }
                    );
                    b.emit(&format!("{opcode}/t-producer"), &t_text);
                    b.emit(&format!("{opcode}/t"), &consumer("$t".into(), slot));
                    for opt in fa_opts {
                        b.emit(&format!("{opcode}/t-producer2"), &t_text);
                        b.emit(
                            &format!("{opcode}/t-{opt}"),
                            &consumer(
                                opts("$t", false, *opt == 'e', *opt == 'r'),
                                slot,
                            ),
                        );
                    }
                    b.bump("forward-t");
                    slot += 1;

                    // mreadf: a matrix read writes it.
                    let rm = format!("{}mread", pchar(prec));
                    let mat_side = if prec == "h" { "$lly0" } else { "$ly0" };
                    let rm_text = format!("{rm} {mat_side} $nowrite");
                    b.emit(&format!("{opcode}/mreadf-producer"), &rm_text);
                    b.emit(
                        &format!("{opcode}/mreadf"),
                        &consumer("$mreadf".into(), slot),
                    );
                    for opt in fa_opts {
                        b.emit(&format!("{opcode}/mreadf-producer2"), &rm_text);
                        b.emit(
                            &format!("{opcode}/mreadf-{opt}"),
                            &consumer(
                                opts(
                                    "$mreadf",
                                    false,
                                    *opt == 'e',
                                    *opt == 'r',
                                ),
                                slot,
                            ),
                        );
                    }
                    b.bump("forward-mreadf");
                }
            }
        }
    }
}

/// Which input option can be applied to a matrix x (or y) operand: `e`, `r`,
/// both (`er`) or none, following the CPU's format rules and bus width.
fn forward_options(prec: &str, x: bool) -> &'static [char] {
    match (prec, x) {
        ("d", _) => &['e'],
        // A half matrix x operand reads half words, but `r` would read f32
        // words from the forwarding register; those are not block-float valid,
        // so only list sources exercise it.
        ("h", true) => &[],
        ("h", false) => &['e'],
        ("f" | "g", _) => &['e', 'r'],
        _ => &[],
    }
}

fn emit_matrix_mau(b: &mut Builder) {
    for prec in ["d", "f", "g", "h"] {
        for kind in 0..2 {
            // (u|d) is documented for double; the CPU and GPU accept it for
            // every matrix precision, so cover all of them.
            let halves: &[usize] = &[0, 1, 2];
            for &half in halves {
                let rounds: &[bool] = if matches!(prec, "d" | "h") {
                    &[false, true]
                } else {
                    &[false, true] // f/g accept the option (single output)
                };
                for &round in rounds {
                    let opcode = mat_opcode(prec, kind, half, round);
                    b.configs.insert(opcode.clone());
                    for side in ["x", "y"] {
                        let slot = b.lines;
                        let xm = 0usize;
                        let ym = 2usize;
                        let dm = 1usize;
                        let xaddr = src_addr(xm, slot);
                        let yaddr = src_addr(ym, slot);
                        let daddr = dst_addr(dm, slot);
                        let x = mem_tok(xm, 2, xaddr);
                        let y = mem_tok(ym, 2, yaddr);
                        let d = mem_tok(dm, 2, daddr);
                        let sources = if kind == 0 {
                            format!("{x} {y}")
                        } else {
                            x.clone()
                        };
                        b.emit(
                            &format!("{opcode}/${side}/basic"),
                            &format!("{opcode} $l{side} {sources} {d}"),
                        );
                        b.bump("basic");

                        // Sign inversion of the x and y inputs (SDM 3.6.9.22).
                        b.emit(
                            &format!("{opcode}/${side}/x-neg"),
                            &format!(
                                "{opcode} $l{side} -{x} {} {d}",
                                if kind == 0 { y.clone() } else { String::new() }
                            ),
                        );
                        b.bump("x-neg");
                        if kind == 0 {
                            b.emit(
                                &format!("{opcode}/${side}/y-neg"),
                                &format!("{opcode} $l{side} {x} -{y} {d}"),
                            );
                            b.bump("y-neg");
                        }

                        // Half extended block-float representation in x.
                        if prec == "h" && side == "x" {
                            let sources = if kind == 0 {
                                format!("$lm4000v {}", mem_tok(ym, 2, yaddr))
                            } else {
                                "$lm4000v".to_string()
                            };
                            b.emit(
                                &format!("{opcode}/${side}/extended-bf"),
                                &format!("{opcode} $l{side} {sources} {d}"),
                            );
                            b.bump("extended-bf");
                        }

                        // Alternate banks write LM0 and read LM1/GRF1.
                        let (axm, aym, adm) = (1usize, 3usize, 0usize);
                        let axaddr = src_addr(axm, slot);
                        let ayaddr = src_addr(aym, slot);
                        let adaddr = dst_addr(adm, slot);
                        let ax = mem_tok(axm, 2, axaddr);
                        let ay = mem_tok(aym, 2, ayaddr);
                        let ad = mem_tok(adm, 2, adaddr);
                        let alt_sources = if kind == 0 {
                            format!("{ax} {ay}")
                        } else {
                            ax.clone()
                        };
                        b.emit(
                            &format!("{opcode}/${side}/alt"),
                            &format!("{opcode} $l{side} {alt_sources} {ad}"),
                        );
                        b.bump("alt");

                        // y from LM0 (x from GRF0).
                        if kind == 0 {
                            b.emit(
                                &format!("{opcode}/${side}/y-lm"),
                                &format!(
                                    "{opcode} $l{side} {} {} {}",
                                    mem_tok(2, 2, src_addr(2, slot)),
                                    mem_tok(0, 2, src_addr(0, slot)),
                                    mem_tok(1, 2, dst_addr(1, slot))
                                ),
                            );
                            b.bump("y-lm");
                        }

                        // Word-length list sources (double and single fit one
                        // word; wider block-float operands would read zero).
                        if matches!(prec, "d" | "f") {
                            let sources = if kind == 0 {
                                format!(
                                    "{} {}",
                                    mem_tok(xm, 1, xaddr),
                                    mem_tok(ym, 1, yaddr)
                                )
                            } else {
                                mem_tok(xm, 1, xaddr)
                            };
                            b.emit(
                                &format!("{opcode}/${side}/wl1"),
                                &format!("{opcode} $l{side} {sources} {}", mem_tok(dm, 2, daddr)),
                            );
                            b.bump("wl1");
                        }

                        // No memory destination; mauf is still updated.
                        let sources = if kind == 0 {
                            format!("{x} {y}")
                        } else {
                            x.clone()
                        };
                        b.emit(
                            &format!("{opcode}/${side}/nowrite"),
                            &format!("{opcode} $l{side} {sources} $nowrite"),
                        );
                        b.bump("nowrite");

                        // Long-word list sources.
                        let x4 = mem_tok(xm, 4, xaddr);
                        let y4 = mem_tok(ym, 4, yaddr);
                        let sources4 = if kind == 0 {
                            format!("{x4} {y4}")
                        } else {
                            x4.clone()
                        };
                        b.emit(
                            &format!("{opcode}/${side}/wl4"),
                            &format!("{opcode} $ll{side} {sources4} {}", mem_tok(dm, 4, daddr & !3)),
                        );
                        b.bump("wl4");

                        // Input options.
                        if kind == 0 {
                            // `e`/`r` change the element width, so use the
                            // long-long operands to supply every element.
                            let xe = opts(&x4, false, true, false);
                            let ye = opts(&y4, false, true, false);
                            if let Some(text) = option_line(
                                &opcode, side, &xe, Some(&ye), &d, prec, "ext",
                            ) {
                                b.emit(&format!("{opcode}/${side}/ext"), &text);
                                b.bump("ext");
                            }
                            let xr = opts(&x4, false, false, true);
                            let yr = opts(&y4, false, false, true);
                            if let Some(text) = option_line(
                                &opcode, side, &xr, Some(&yr), &d, prec, "rnd",
                            ) {
                                b.emit(&format!("{opcode}/${side}/rnd"), &text);
                                b.bump("rnd");
                            }
                        } else {
                            let xe = opts(&x4, false, true, false);
                            if let Some(text) = option_line(
                                &opcode, side, &xe, None, &d, prec, "ext",
                            ) {
                                b.emit(&format!("{opcode}/${side}/ext"), &text);
                                b.bump("ext");
                            }
                            let xr = opts(&x4, false, false, true);
                            if let Some(text) = option_line(
                                &opcode, side, &xr, None, &d, prec, "rnd",
                            ) {
                                b.emit(&format!("{opcode}/${side}/rnd"), &text);
                                b.bump("rnd");
                            }
                        }

                        // Zero-flush and multiple destinations.
                        let sources = if kind == 0 {
                            format!("{x} {y}")
                        } else {
                            x.clone()
                        };
                        b.emit(
                            &format!("{opcode}/${side}/flush"),
                            &format!(
                                "{opcode}/0110 $l{side} {sources} {d} $t $omr{}",
                                1 + slot % 3
                            ),
                        );
                        b.bump("flush");
                        b.emit(
                            &format!("{opcode}/${side}/dst-masks"),
                            &format!(
                                "{opcode} $l{side} {sources} {}/1010 $t/0110 $omr1/1001",
                                mem_tok(dm, 2, dst_addr(dm, slot))
                            ),
                        );
                        b.bump("dst-masks");

                        // Explicit and directive masks.
                        b.emit(
                            &format!("{opcode}/${side}/mask"),
                            &format!(
                                "{opcode} $l{side} {sources} {}/1010",
                                mem_tok(dm, 2, dst_addr(dm, slot))
                            ),
                        );
                        b.bump("mask");
                        b.emit(
                            &format!("{opcode}/${side}/imr-mask"),
                            &format!(
                                "{opcode} $l{side} {sources} {}/$imr1",
                                mem_tok(dm, 2, dst_addr(dm, slot))
                            ),
                        );
                        b.bump("imr-mask");
                        b.emit(
                            &format!("{opcode}/${side}/imr-flush"),
                            &format!(
                                "{opcode}/$imr1 $l{side} {sources} {}",
                                mem_tok(dm, 2, dst_addr(dm, slot))
                            ),
                        );
                        b.bump("imr-flush");
                        let target = mchar(dm).to_string();
                        b.directive(
                            &format!("{opcode}/${side}/directive"),
                            &format!("mask{target} 1"),
                        );
                        b.emit(
                            &format!("{opcode}/${side}/directive-line"),
                            &format!(
                                "{opcode} $l{side} {sources} {}",
                                mem_tok(dm, 2, dst_addr(dm, slot))
                            ),
                        );
                        b.directive(&format!("{opcode}/${side}/directive-off"), "mask 0");
                        b.bump("directive");

                        // Forwarding sources in x (must stay block-float valid;
                        // every producer below copies a valid list block).
                        for (name, producer, token) in forward_producers(prec, slot) {
                            b.emit(
                                &format!("{opcode}/${side}/x-{name}-producer"),
                                &producer,
                            );
                            let sources = if kind == 0 {
                                format!("{token} {y}")
                            } else {
                                token.clone()
                            };
                            b.emit(
                                &format!("{opcode}/${side}/x-{name}"),
                                &format!("{opcode} $l{side} {sources} {d}"),
                            );
                            b.bump(&format!("x-{name}"));
                            for opt in forward_options(prec, true) {
                                // A G round reads two doubles (four words).
                                // mauf/T/mreadf only carry two valid words for
                                // a G producer, so the second double would be
                                // zero and fail the block-float check.
                                if prec == "g" && name != "aluf" && *opt == 'r' {
                                    continue;
                                }
                                b.emit(
                                    &format!("{opcode}/${side}/x-{name}-producer2"),
                                    &producer,
                                );
                                let token = opts(
                                    &token,
                                    false,
                                    *opt == 'e',
                                    *opt == 'r',
                                );
                                let sources = if kind == 0 {
                                    format!("{token} {y}")
                                } else {
                                    token.clone()
                                };
                                b.emit(
                                    &format!("{opcode}/${side}/x-{name}-{opt}"),
                                    &format!("{opcode} $l{side} {sources} {d}"),
                                );
                                b.bump(&format!("x-{name}-{opt}"));
                            }
                        }

                        // Forwarding sources in y (ordinary values, no block
                        // checks). The x operand stays a list source.
                        if kind == 0 {
                            for (name, producer, token) in forward_producers(prec, slot) {
                                b.emit(
                                    &format!("{opcode}/${side}/y-{name}-producer"),
                                    &producer,
                                );
                                b.emit(
                                    &format!("{opcode}/${side}/y-{name}"),
                                    &format!("{opcode} $l{side} {x} {token} {d}"),
                                );
                                b.bump(&format!("y-{name}"));
                                for opt in forward_options(prec, false) {
                                    b.emit(
                                        &format!("{opcode}/${side}/y-{name}-producer2"),
                                        &producer,
                                    );
                                    let token = opts(
                                        &token,
                                        false,
                                        *opt == 'e',
                                        *opt == 'r',
                                    );
                                    b.emit(
                                        &format!("{opcode}/${side}/y-{name}-{opt}"),
                                        &format!("{opcode} $l{side} {x} {token} {d}"),
                                    );
                                    b.bump(&format!("y-{name}-{opt}"));
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}

/// One option line if the combination fits the source bus. `prec` decides
/// which options the CPU accepts for the x and y formats.
fn option_line(
    opcode: &str,
    side: &str,
    x: &str,
    y: Option<&str>,
    d: &str,
    prec: &str,
    what: &str,
) -> Option<String> {
    // x format: d/f/g single-or-double, h half. y format: h uses single.
    let (nx, ny) = match prec {
        "d" => (1usize, 1usize),
        "f" => (1, 2),
        "g" => (2, 2),
        _ => (4, 4),
    };
    let x_ok = if what == "ext" {
        match prec {
            "h" => false,
            _ => true,
        }
    } else {
        match prec {
            "d" => false,
            "h" => nx * 32 <= 128,
            _ => nx * 64 <= 128,
        }
    };
    let y_ok = match (prec, what) {
        (_, "ext") => true,
        ("d", _) => false,
        ("h", _) => ny * 64 <= 128,
        _ => ny * 64 <= 128,
    };
    if !x_ok || (y.is_some() && !y_ok) {
        return None;
    }
    let sources = match y {
        Some(y) => format!("{x} {y}"),
        None => x.to_string(),
    };
    Some(format!("{opcode} $l{side} {sources} {d}"))
}

fn forward_producers(prec: &str, slot: usize) -> Vec<(String, String, String)> {
    let p = pchar(prec);
    // The ALU has no pseudo-single pass-through; f32 pass-through is exact for
    // the words the G matrix source reads.
    let alu_p = if prec == "g" { 'f' } else { p };
    // A half matrix x operand reads four half words from a forwarding register,
    // so the producer must round its single-precision accumulation to half.
    let vp = if prec == "h" { "hvpassar" } else { "" };
    let vp = if vp.is_empty() {
        format!("{p}vpassa")
    } else {
        vp.to_string()
    };
    let mem = 0usize;
    let addr = src_addr(mem, slot);
    let src = mem_tok(mem, 4, addr);
    let dst_mem = 1usize;
    let dst = mem_tok(dst_mem, 2, dst_addr(dst_mem, slot));
    vec![
        (
            "aluf".into(),
            format!("{alu_p}passa {src} {dst}"),
            "$aluf".into(),
        ),
        (
            "mauf".into(),
            format!("{vp} {src} $nowrite"),
            "$mauf".into(),
        ),
        (
            "t".into(),
            format!("{vp} {src} $t"),
            "$t".into(),
        ),
        (
            "mreadf".into(),
            format!("{p}mread $ly0 $nowrite"),
            "$mreadf".into(),
        ),
    ]
}

fn emit_matrix_write(b: &mut Builder) {
    for prec in ["d", "f", "g", "h"] {
        let wls: &[usize] = match prec {
            "d" => &[2],
            "h" => &[2, 4],
            _ => &[1, 2, 4],
        };
        for &wl in wls {
            for side in ["x", "y"] {
                for (addr, where_) in [(0u32, "start"), (7, "wrap")] {
                    let addr = if prec == "h" {
                        if where_ == "wrap" { 14 } else { 0 }
                    } else {
                        addr
                    };
                    let opcode = format!("{}mwrite", pchar(prec));
                    b.configs.insert(format!("{opcode}/wl{wl}"));
                    let slot = b.lines;
                    let sm = slot % 4;
                    let src = mem_tok(sm, wl, src_addr(sm, slot));
                    // hmwrite uses $(l|ll); the other precisions use $l.
                    let mat = if prec == "h" && wl == 4 {
                        format!("$ll{side}{addr}")
                    } else {
                        format!("$l{side}{addr}")
                    };
                    b.emit(
                        &format!("{opcode}/wl{wl}/{side}/{where_}"),
                        &format!("{opcode} {src} {mat}"),
                    );
                    b.bump(&format!("wl{wl}"));

                    if prec == "h" && wl == 2 {
                        b.emit(
                            &format!("{opcode}/wl{wl}/{side}/extended-bf"),
                            &format!("{opcode} $lm4000v {mat}"),
                        );
                        b.bump("extended-bf");
                    }

                    // Sign inversion and the input options where they fit.
                    b.emit(
                        &format!("{opcode}/wl{wl}/{side}/neg"),
                        &format!("{opcode} -{src} {mat}"),
                    );
                    b.bump("neg");
                    let ext_ok = prec != "h";
                    if ext_ok {
                        let tok = opts(&src, false, true, false);
                        b.emit(
                            &format!("{opcode}/wl{wl}/{side}/ext"),
                            &format!("{opcode} {tok} {mat}"),
                        );
                        b.bump("ext");
                    }
                    let rnd_ok = prec != "d" && !(prec == "h" && wl == 4);
                    if rnd_ok {
                        let tok = opts(&src, false, false, true);
                        b.emit(
                            &format!("{opcode}/wl{wl}/{side}/rnd"),
                            &format!("{opcode} {tok} {mat}"),
                        );
                        b.bump("rnd");
                    }

                    // Forwarding and T sources.
                    for (name, producer, token) in forward_producers(prec, slot) {
                        b.emit(
                            &format!("{opcode}/wl{wl}/{side}/{name}-producer"),
                            &producer,
                        );
                        b.emit(
                            &format!("{opcode}/wl{wl}/{side}/{name}"),
                            &format!("{opcode} {token} {mat}"),
                        );
                        b.bump(&format!("src-{name}"));
                        let opts_here: &[char] = match prec {
                            "d" => &['e'],
                            "h" if wl != 4 => &['r'],
                            "h" => &[],
                            _ => &['e', 'r'],
                        };
                        for opt in opts_here {
                            b.emit(
                                &format!("{opcode}/wl{wl}/{side}/{name}-producer2"),
                                &producer,
                            );
                            let token = opts(
                                &token,
                                false,
                                *opt == 'e',
                                *opt == 'r',
                            );
                            b.emit(
                                &format!("{opcode}/wl{wl}/{side}/{name}-{opt}"),
                                &format!("{opcode} {token} {mat}"),
                            );
                            b.bump(&format!("src-{name}-{opt}"));
                        }
                    }
                }
            }
        }
    }
}

fn emit_matrix_read(b: &mut Builder) {
    for prec in ["d", "f", "g", "h"] {
        for side in ["x", "y"] {
            let opcode = format!("{}mread", pchar(prec));
            b.configs.insert(opcode.clone());
            for (addr, where_) in [(0u32, "start"), (7, "wrap")] {
                let addr = if prec == "h" {
                    if where_ == "wrap" { 14 } else { 0 }
                } else {
                    addr
                };
                let slot = b.lines;
                let dm = slot % 4;
                let d = mem_tok(dm, 2, dst_addr(dm, slot));
                let m = if prec == "h" {
                    format!("$ll{side}{addr}")
                } else {
                    format!("$l{side}{addr}")
                };
                b.emit(
                    &format!("{opcode}/{side}/{where_}"),
                    &format!("{opcode} {m} {d}"),
                );
                b.bump("basic");

                // Multiple destinations (two PE memories, T and OMR).
                let dm2 = (dm + 1) % 4;
                b.emit(
                    &format!("{opcode}/{side}/multi"),
                    &format!(
                        "{opcode} {m} {} {} $t $omr{}",
                        mem_tok(dm, 4, dst_addr(dm, slot) & !3),
                        mem_tok(dm2, 2, dst_addr(dm2, slot)),
                        1 + slot % 3
                    ),
                );
                b.bump("multi");
                b.emit(
                    &format!("{opcode}/{side}/dst-masks"),
                    &format!(
                        "{opcode} {m} {}/1010 $t/0110 $omr1/1001",
                        mem_tok(dm, 2, dst_addr(dm, slot))
                    ),
                );
                b.bump("dst-masks");

                // An explicit OMR-entry write mask.
                b.emit(
                    &format!("{opcode}/{side}/imr-mask"),
                    &format!(
                        "{opcode} {m} {}/$imr1",
                        mem_tok(dm, 2, dst_addr(dm, slot))
                    ),
                );
                b.bump("imr-mask");

                // Explicit mask, long mask, flush, directive and $nowrite.
                b.emit(
                    &format!("{opcode}/{side}/mask"),
                    &format!(
                        "{opcode} {m} {}/1010",
                        mem_tok(dm, 2, dst_addr(dm, slot))
                    ),
                );
                b.bump("mask");
                b.emit(
                    &format!("{opcode}/{side}/flush"),
                    &format!(
                        "{opcode}/0110 {m} {}",
                        mem_tok(dm, 2, dst_addr(dm, slot))
                    ),
                );
                b.bump("flush");
                b.emit(
                    &format!("{opcode}/{side}/nowrite"),
                    &format!("{opcode} {m} $nowrite"),
                );
                b.bump("nowrite");
                let target = mchar(dm).to_string();
                b.directive(
                    &format!("{opcode}/{side}/directive"),
                    &format!("mask{target} 1"),
                );
                b.emit(
                    &format!("{opcode}/{side}/directive-line"),
                    &format!("{opcode} {m} {}", mem_tok(dm, 2, dst_addr(dm, slot))),
                );
                b.directive(&format!("{opcode}/{side}/directive-off"), "mask 0");
                b.bump("directive");
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Host-side state
// ---------------------------------------------------------------------------

struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
}

/// A word whose single, double and half exponent fields all encode one common
/// exponent for the block. A half occupies both halves of the word, so the
/// high-half exponent (word bits 30..25), the low-half exponent (bits 14..9),
/// the f32 exponent (bits 30..23) and the double exponent (bits 30..20 of the
/// high word) are all derived from `e16`.
fn block_word(rng: &mut Rng, e16: u32) -> u32 {
    let mantissa = (rng.next() as u32) & 0x800f_81ff;
    mantissa | ((e16 << 2) << 23) | (e16 << 25) | (e16 << 9)
}

fn mat_word(rng: &mut Rng, e16: u32) -> u32 {
    block_word(rng, e16)
}

fn mem_words(rng: &mut Rng, len: usize) -> Vec<u32> {
    let per_pe = len / PES;
    (0..len)
        .map(|i| {
            // The exponent depends only on the address, so every PE reading the
            // same block sees the same exponent (block-float vector check).
            let block = (i % per_pe) / 8;
            let e16 = 28 + (block % 6) as u32;
            let mut w = block_word(rng, e16);
            // Address block 500 (word 4000) carries one half with exponent 0:
            // the half extended representation ("common - 6") that block-float
            // dot products accept next to the common exponent.
            if block == 500 && (i % per_pe) % 8 == 0 {
                w &= !(0x3f << 25);
            }
            w
        })
        .collect()
}

fn mat_flat(rng: &mut Rng) -> Vec<u32> {
    let mut mats = vec![0u32; MAT_WORDS];
    for i in 0..MAT_WORDS {
        let face = (i / (16 * 8)) % 2;
        let row = (i / 8) % 16;
        // The y face is uniform across rows so a matrix read can feed a matrix
        // MAU x operand (block-float check). The x face varies per row.
        let e16 = if face == 1 { 30 } else { 28 + (row % 6) as u32 };
        mats[i] = mat_word(rng, e16);
    }
    mats
}

fn flat_mats(mats: &[[[[u32; 8]; 16]; 2]]) -> Vec<u32> {
    mats.iter()
        .flat_map(|faces| faces.iter())
        .flat_map(|face| face.iter())
        .flat_map(|row| row.iter().copied())
        .collect()
}

fn read_mask_flat(sim: &Sim) -> Vec<u32> {
    let mut out = Vec::with_capacity(PES * 16);
    for p in &sim.m.pes {
        for e in p.mask {
            out.push(e as u32);
        }
    }
    out
}

fn read_forward(sim: &Sim, kind: usize) -> Vec<u32> {
    let mut out = Vec::with_capacity(PES * 16);
    for p in &sim.m.pes {
        let bus = match kind {
            0 => p.aluf,
            1 => p.mauf,
            _ => p.mreadf,
        };
        for cycle in bus {
            out.extend_from_slice(&cycle);
        }
    }
    out
}

fn read_t(sim: &Sim) -> Vec<u32> {
    sim.m.pes.iter().flat_map(|p| p.t.iter().copied()).collect()
}

fn compare(name: &str, cpu: &[u32], gpu: &[u32], width: usize) -> usize {
    if let Some(index) = cpu.iter().zip(gpu).position(|(a, b)| a != b) {
        let total = cpu.iter().zip(gpu).filter(|(a, b)| a != b).count();
        println!(
            "{name}: first mismatch at pe {} word {}: cpu {:08x} gpu {:08x} ({total} mismatches)",
            index / width,
            index % width,
            cpu[index],
            gpu[index]
        );
        return total;
    }
    if cpu.len() != gpu.len() {
        println!("{name}: length {} != {}", cpu.len(), gpu.len());
        return 1;
    }
    0
}

fn main() {
    let list = std::env::args().any(|a| a == "--list");
    let mut b = Builder::new();
    emit_vector(&mut b);
    emit_matrix_mau(&mut b);
    emit_matrix_write(&mut b);
    emit_matrix_read(&mut b);

    let gpu = match Gpu::new() {
        Ok(gpu) => gpu,
        Err(error) => {
            eprintln!("gpu unavailable: {error}");
            std::process::exit(2);
        }
    };
    let state = gpu.allocate_state().expect("allocate state");

    let mut rng = Rng(0x0d15_ea5e_1234_abcd);
    let lm0 = mem_words(&mut rng, PES * LM_WORDS);
    let lm1 = mem_words(&mut rng, PES * LM_WORDS);
    let grf0 = mem_words(&mut rng, PES * GRF_WORDS);
    let grf1 = mem_words(&mut rng, PES * GRF_WORDS);
    let mats = mat_flat(&mut rng);

    let mut mask = vec![0u32; PES * 16];
    for (i, w) in mask.iter_mut().enumerate() {
        *w = (rng.next() as u16) as u32;
        // Entries 1..3 are used by fixed `$imr` masks; keep them nonzero.
        if i % 16 != 0 && *w == 0 {
            *w = 0x1234;
        }
    }
    let mut t = vec![0u32; PES * 16];
    for pe in 0..PES {
        for c in 0..4 {
            let e16 = 28 + (c as u32 % 6);
            for k in 0..4 {
                t[pe * 16 + c * 4 + k] = block_word(&mut rng, e16);
            }
        }
    }
    let mut aluf = vec![0u32; PES * 16];
    let mut mauf = vec![0u32; PES * 16];
    let mut mreadf = vec![0u32; PES * 16];
    for i in 0..PES * 16 {
        aluf[i] = block_word(&mut rng, 30);
        mauf[i] = block_word(&mut rng, 30);
        mreadf[i] = block_word(&mut rng, 30);
    }

    let mut sim = Sim::new();
    sim.m.mem.lm0.copy_from_slice(&lm0);
    sim.m.mem.lm1.copy_from_slice(&lm1);
    sim.m.mem.grf0.copy_from_slice(&grf0);
    sim.m.mem.grf1.copy_from_slice(&grf1);
    for (mab, faces) in sim.m.mats.iter_mut().enumerate() {
        for side in 0..2 {
            for row in 0..16 {
                for word in 0..8 {
                    let index = ((mab * 2 + side) * 16 + row) * 8 + word;
                    faces[side][row][word] = mats[index];
                }
            }
        }
    }
    for (pe, p) in sim.m.pes.iter_mut().enumerate() {
        for e in 0..16 {
            p.mask[e] = mask[pe * 16 + e] as u16;
        }
        for i in 0..16 {
            p.t[i] = t[pe * 16 + i];
            p.aluf[i / 4][i % 4] = aluf[pe * 16 + i];
            p.mauf[i / 4][i % 4] = mauf[pe * 16 + i];
            p.mreadf[i / 4][i % 4] = mreadf[pe * 16 + i];
        }
    }
    sim.m.fwd_error = [None, None, None, None];

    gpu.upload_state(&state, &lm0, &lm1, &grf0, &grf1)
        .expect("upload state");
    gpu.upload_mats(&state, &mats).expect("upload mats");
    gpu.upload_mask(&state, &mask).expect("upload mask");
    gpu.upload_t(&state, &t).expect("upload t");
    gpu.upload_aluf(&state, &aluf).expect("upload aluf");
    gpu.upload_mauf(&state, &mauf).expect("upload mauf");
    gpu.upload_mreadf(&state, &mreadf).expect("upload mreadf");

    let mut bad = 0usize;
    let mut last_action = None;
    for entry in &b.entries {
        sim.exec(&entry.line)
            .unwrap_or_else(|e| {
                panic!(
                    "CPU rejected `{}` (`{}`): {e:?}",
                    entry.label,
                    entry.text,
                    e = e.message()
                )
            });
        let Some(action) = entry.action else {
            continue;
        };
        match action {
            Action::Alu(line) => gpu.run_alu_line(&state, &line).expect("alu"),
            Action::Mau(line) => gpu.run_mau_line(&state, &line).expect("mau"),
            Action::MatWrite(line) => gpu.run_mat_write_line(&state, &line).expect("mat write"),
            Action::MatRead(line) => gpu.run_mat_read_line(&state, &line).expect("mat read"),
            Action::MatMau(line) => gpu.run_mat_mau_line(&state, &line).expect("mat mau"),
        }
        // Compare the state this class of line can change.
        match action {
            Action::Alu(_) => {
                let cpu = read_forward(&sim, 0);
                let got = gpu.download_aluf(&state).expect("download aluf");
                bad += compare(&format!("{}/aluf", entry.label), &cpu, &got, 16);
            }
            Action::Mau(line) => {
                let cpu = read_forward(&sim, 1);
                let got = gpu.download_mauf(&state).expect("download mauf");
                bad += compare(&format!("{}/mauf", entry.label), &cpu, &got, 16);
                if writes_t(line.dst, line.ndst) {
                    let cpu = read_t(&sim);
                    let got = gpu.download_t(&state).expect("download t");
                    bad += compare(&format!("{}/t", entry.label), &cpu, &got, 16);
                }
                if writes_omr(line.dst, line.ndst) {
                    let cpu = read_mask_flat(&sim);
                    let got = gpu.download_mask(&state).expect("download mask");
                    bad += compare(&format!("{}/omr", entry.label), &cpu, &got, 16);
                }
            }
            Action::MatMau(line) => {
                let cpu = read_forward(&sim, 1);
                let got = gpu.download_mauf(&state).expect("download mauf");
                bad += compare(&format!("{}/mauf", entry.label), &cpu, &got, 16);
                let cpu = flat_mats(&sim.m.mats);
                let got = gpu.download_mats(&state).expect("download mats");
                bad += compare(&format!("{}/mats", entry.label), &cpu, &got, 8);
                if writes_t(line.dst, line.ndst) {
                    let cpu = read_t(&sim);
                    let got = gpu.download_t(&state).expect("download t");
                    bad += compare(&format!("{}/t", entry.label), &cpu, &got, 16);
                }
                if writes_omr(line.dst, line.ndst) {
                    let cpu = read_mask_flat(&sim);
                    let got = gpu.download_mask(&state).expect("download mask");
                    bad += compare(&format!("{}/omr", entry.label), &cpu, &got, 16);
                }
            }
            Action::MatWrite(_) => {
                let cpu = flat_mats(&sim.m.mats);
                let got = gpu.download_mats(&state).expect("download mats");
                bad += compare(&format!("{}/mats", entry.label), &cpu, &got, 8);
            }
            Action::MatRead(line) => {
                let cpu = read_forward(&sim, 2);
                let got = gpu.download_mreadf(&state).expect("download mreadf");
                bad += compare(&format!("{}/mreadf", entry.label), &cpu, &got, 16);
                if writes_t(line.dst, line.ndst) {
                    let cpu = read_t(&sim);
                    let got = gpu.download_t(&state).expect("download t");
                    bad += compare(&format!("{}/t", entry.label), &cpu, &got, 16);
                }
                if writes_omr(line.dst, line.ndst) {
                    let cpu = read_mask_flat(&sim);
                    let got = gpu.download_mask(&state).expect("download mask");
                    bad += compare(&format!("{}/omr", entry.label), &cpu, &got, 16);
                }
            }
        }
        last_action = Some(action);
        if bad != 0 {
            println!("conformance failed at {} (`{}`)", entry.label, entry.text);
            std::process::exit(1);
        }
    }

    // Final full comparison.
    let mut out_lm0 = vec![0u32; PES * LM_WORDS];
    let mut out_lm1 = vec![0u32; PES * LM_WORDS];
    let mut out_grf0 = vec![0u32; PES * GRF_WORDS];
    let mut out_grf1 = vec![0u32; PES * GRF_WORDS];
    gpu.download_state(&state, &mut out_lm0, &mut out_lm1, &mut out_grf0, &mut out_grf1)
        .expect("download state");
    for (name, cpu, got, width) in [
        ("lm0", sim.m.mem.lm0.as_slice(), out_lm0.as_slice(), LM_WORDS),
        ("lm1", sim.m.mem.lm1.as_slice(), out_lm1.as_slice(), LM_WORDS),
        ("grf0", sim.m.mem.grf0.as_slice(), out_grf0.as_slice(), GRF_WORDS),
        ("grf1", sim.m.mem.grf1.as_slice(), out_grf1.as_slice(), GRF_WORDS),
    ] {
        bad += compare(name, cpu, got, width);
    }
    let cpu = flat_mats(&sim.m.mats);
    let got = gpu.download_mats(&state).expect("download mats");
    bad += compare("mats", &cpu, &got, 8);
    let cpu = read_t(&sim);
    let got = gpu.download_t(&state).expect("download t");
    bad += compare("t", &cpu, &got, 16);
    let cpu = read_mask_flat(&sim);
    let got = gpu.download_mask(&state).expect("download mask");
    bad += compare("omr", &cpu, &got, 16);
    let cpu = read_forward(&sim, 0);
    let got = gpu.download_aluf(&state).expect("download aluf");
    bad += compare("aluf", &cpu, &got, 16);
    let cpu = read_forward(&sim, 1);
    let got = gpu.download_mauf(&state).expect("download mauf");
    bad += compare("mauf", &cpu, &got, 16);
    if matches!(last_action, Some(Action::MatRead(_))) {
        let cpu = read_forward(&sim, 2);
        let got = gpu.download_mreadf(&state).expect("download mreadf");
        bad += compare("mreadf", &cpu, &got, 16);
    }

    println!(
        "{} lines, {} configurations, {} mismatches",
        b.entries.len(),
        b.configs.len(),
        bad
    );
    println!("ops: {:?}", b.ops);
    if list {
        for c in &b.configs {
            println!("  {c}");
        }
        for (k, v) in &b.counts {
            println!("  {k}: {v}");
        }
    }
    if bad != 0 {
        std::process::exit(1);
    }
}

fn writes_t(dst: [AluDstDesc; 8], ndst: u32) -> bool {
    (0..ndst as usize).any(|i| dst[i].kind == 1)
}

fn writes_omr(dst: [AluDstDesc; 8], ndst: u32) -> bool {
    (0..ndst as usize).any(|i| dst[i].kind == 2)
}

#[allow(dead_code)]
fn writes_mem(dst: [AluDstDesc; 8], ndst: u32) -> bool {
    (0..ndst as usize).any(|i| dst[i].kind == 0)
}
