//! Parser for MN-Core 2 assembly (VSM).
//!
//! The grammar follows SDM chapter 3. Only the parts needed by the simulator are parsed in detail;
//! everything else is kept as text so that it can be reported as unsupported.

use std::fmt;

#[derive(Clone, Debug, PartialEq)]
pub struct ParseError {
    pub line: usize,
    pub msg: String,
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "line {}: {}", self.line, self.msg)
    }
}

/// One source line after comment removal.
#[derive(Clone, Debug, PartialEq)]
pub enum Line {
    /// A PE instruction statement: expressions issued in one step.
    Pe(Vec<Expr>),
    /// `nop` or `nop/<n>`, possibly with `wait`.
    Nop { count: u32, wait: Option<u8> },
    /// An MV instruction statement (kept as text for now).
    Mv(String),
    /// `mask[l|ll][r][s][t][m][n][k] <addr>`: write mask applied to all following steps.
    MaskDirective { wl: u8, targets: MaskTargets, entry: u8 },
    /// `d set ...`
    DebugSet { loc: DebugLoc, count: u32, payload: Vec<u64> },
    /// `d get[d|f|h] ...`
    DebugGet { loc: DebugLoc, count: u32, dtype: Option<char>, comment: String },
    /// `r <group> <addr> <count> <payload>` (address and count in hex): DRAM initialization written directly in the emulator's
    /// input format. Testcases use it, because their prefix and suffix are not assembled.
    DramSet { group: u8, addr: u64, payload: Vec<u64> },
}

impl Line {
    /// Number of instruction words the official assembler emits for this line (`j` + `m` lines).
    pub fn words(&self) -> u32 {
        match self {
            Line::Pe(_) | Line::Mv(_) => 1,
            Line::Nop { count, .. } => *count,
            Line::MaskDirective { .. } | Line::DebugSet { .. } | Line::DebugGet { .. } | Line::DramSet { .. } => 0,
        }
    }
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct MaskTargets {
    pub grf0: bool,
    pub grf1: bool,
    pub t: bool,
    pub lm0: bool,
    pub lm1: bool,
    pub mask_reg: bool,
}

/// A memory location in a debug statement, such as `$lm0n0c0b0m0p1`.
#[derive(Clone, Debug, PartialEq)]
pub struct DebugLoc {
    pub mem: MemKind,
    /// Access length in words (1, 2 or 4).
    pub wl: u8,
    pub addr: u32,
    pub group: Option<u8>,
    pub l2b: Option<u8>,
    pub l1b: Option<u8>,
    pub mab: Option<u8>,
    pub pe: Option<u8>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MemKind {
    Lm0,
    Lm1,
    Grf0,
    Grf1,
    T,
    L1bm,
    L2bm,
    Pdm,
    Dram,
}

/// One PE instruction expression.
#[derive(Clone, Debug, PartialEq)]
pub struct Expr {
    pub op: Op,
    pub srcs: Vec<Operand>,
    pub dsts: Vec<Operand>,
    /// Zero-flush mask applied to the output of this expression (`<opcode>/<mask>`).
    pub flush: Option<MaskSel>,
    pub text: String,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Prec {
    D,
    F,
    G,
    H,
    L,
    I,
    S,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Op {
    Alu { name: AluOp, prec: Option<Prec>, unsigned: bool, /// Mantissa length of `hbfn/<n>` and `hbfe/<n>`.
        arg: Option<u8> },
    Imm { value: u32, u: bool },
    Zero,
    Mau { prec: Prec, matrix: bool, kind: MauKind, half: Option<char>, round: bool },
    MatWrite { prec: Prec },
    MatRead { prec: Prec },
    Wait(u8),
    Noforward,
    /// L1BM / L2BM expressions and others not simulated yet.
    Other(String),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MauKind {
    Fma,
    Mul,
    Add,
    Passa,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AluOp {
    Msl,
    Msr,
    Passa,
    Inc,
    Dec,
    Not,
    Lnot,
    Rsqrt,
    Floor,
    Ftoi,
    Bfe,
    Bfn,
    Max,
    Min,
    Packbit,
    And,
    Or,
    Xor,
    Add,
    Sub,
    Lsl,
    Lsr,
    Bsl,
    Bsr,
    Relu,
    Relu0,
    Relu1,
    Relu2,
    Relu3,
    Lrelud,
    Lreluo,
    Ilrelud,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum AluType {
    Untyped,
    Int,
    Float,
    Both,
    Bfn,
    Bfe,
}

const ALU_OPS: &[(&str, AluOp, AluType, usize)] = &[
    ("msl", AluOp::Msl, AluType::Untyped, 1),
    ("msr", AluOp::Msr, AluType::Untyped, 1),
    ("passa", AluOp::Passa, AluType::Both, 1),
    ("inc", AluOp::Inc, AluType::Int, 1),
    ("dec", AluOp::Dec, AluType::Int, 1),
    ("not", AluOp::Not, AluType::Int, 1),
    ("lnot", AluOp::Lnot, AluType::Int, 1),
    ("rsqrt", AluOp::Rsqrt, AluType::Float, 1),
    ("floor", AluOp::Floor, AluType::Float, 1),
    ("ftoi", AluOp::Ftoi, AluType::Float, 1),
    ("bfe", AluOp::Bfe, AluType::Bfe, 1),
    ("bfn", AluOp::Bfn, AluType::Bfn, 1),
    ("max", AluOp::Max, AluType::Both, 2),
    ("min", AluOp::Min, AluType::Both, 2),
    ("packbit", AluOp::Packbit, AluType::Both, 2),
    ("and", AluOp::And, AluType::Int, 2),
    ("or", AluOp::Or, AluType::Int, 2),
    ("xor", AluOp::Xor, AluType::Int, 2),
    ("add", AluOp::Add, AluType::Int, 2),
    ("sub", AluOp::Sub, AluType::Int, 2),
    ("lsl", AluOp::Lsl, AluType::Int, 2),
    ("lsr", AluOp::Lsr, AluType::Int, 2),
    ("bsl", AluOp::Bsl, AluType::Int, 2),
    ("bsr", AluOp::Bsr, AluType::Int, 2),
    ("relu", AluOp::Relu, AluType::Float, 2),
    ("relu0", AluOp::Relu0, AluType::Float, 2),
    ("relu1", AluOp::Relu1, AluType::Float, 2),
    ("relu2", AluOp::Relu2, AluType::Float, 2),
    ("relu3", AluOp::Relu3, AluType::Float, 2),
    ("lrelud", AluOp::Lrelud, AluType::Float, 2),
    ("lreluo", AluOp::Lreluo, AluType::Float, 2),
    ("ilrelud", AluOp::Ilrelud, AluType::Float, 2),
];

impl AluOp {
    pub fn inputs(self) -> usize {
        ALU_OPS.iter().find(|e| e.1 == self).unwrap().3
    }
}

/// Selects mask flags: a fixed pattern or a variable entry of the mask register.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MaskSel {
    /// Mask application length is two long words (`ll`) rather than one.
    pub ll: bool,
    pub source: MaskSource,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MaskSource {
    /// Fixed pattern, one flag per cycle, cycle 0 first.
    Pattern([bool; 4]),
    /// Variable mask register entry 1 to 15 (`$imr<n>`).
    Entry(u8),
}

#[derive(Clone, Debug, PartialEq)]
pub enum Operand {
    Mem {
        mem: MemKind,
        /// Access length in words (1, 2 or 4).
        wl: u8,
        addr: Addr,
        neg: bool,
        /// `e`: precision extension of the input.
        ext: bool,
        /// `r`: rounding of the input to a lower precision.
        rnd: bool,
        /// Single-line write mask (`<dst>/<mask>`).
        mask: Option<MaskSel>,
    },
    /// Base address register of LM0 or LM1 (`$mb`, `$lmb`, `$nb`, `$lnb`).
    Bar { lm1: bool, wl: u8, mask: Option<MaskSel> },
    Forward { kind: FwdKind, neg: bool, ext: bool, rnd: bool },
    Fixed(FixedKind),
    /// Mask register write (`$omr<n>`).
    Omr { entry: u8, mask: Option<MaskSel> },
    /// Matrix register (`$lx0`, `$ly`, `$llx0`).
    Mat { y: bool, wl: u8, row: Option<u32> },
    Nowrite,
    /// Operands of instructions not simulated yet.
    Raw(String),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FwdKind {
    Aluf,
    Mauf,
    Lbf,
    Mreadf,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FixedKind {
    L2bid,
    L1bid,
    Mabid,
    Peid,
    Subpeid,
    Msb1,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Addr {
    /// Word address for each of the 4 cycles before adding the base address register and T.
    pub cycles: [u32; 4],
    /// `t`: add the word read from the T register in each cycle (LM0 only).
    pub t_indirect: bool,
    /// `j<madpe>`: PEs up to this number add one access length to the address.
    pub madpe: Option<u8>,
}

pub fn parse(src: &str) -> Result<Vec<(usize, Line)>, ParseError> {
    let mut out = Vec::new();
    for (i, raw) in src.lines().enumerate() {
        let lineno = i + 1;
        let text = strip_comment(raw).trim();
        if text.is_empty() {
            continue;
        }
        let line = parse_line(text).map_err(|msg| ParseError { line: lineno, msg })?;
        out.push((lineno, line));
    }
    Ok(out)
}

fn strip_comment(s: &str) -> &str {
    // judge.py removes everything after `#` or `!`.
    match s.find(['#', '!']) {
        Some(i) => &s[..i],
        None => s,
    }
}

fn parse_line(text: &str) -> Result<Line, String> {
    if let Some(rest) = text.strip_prefix("d ") {
        return parse_debug(rest.trim(), text);
    }
    if let Some(rest) = text.strip_prefix("r ") {
        return parse_dram_set(rest);
    }
    let first = text.split_whitespace().next().unwrap();
    if first.starts_with("mv") {
        return Ok(Line::Mv(text.to_string()));
    }
    if let Some(m) = parse_mask_directive(text) {
        return Ok(m);
    }
    let mut exprs = Vec::new();
    let mut nop: Option<u32> = None;
    let mut wait = None;
    for part in text.split(';') {
        let part = part.trim();
        if part.is_empty() {
            continue;
        }
        let opcode = part.split_whitespace().next().unwrap();
        if opcode == "nop" || opcode.starts_with("nop/") {
            let n = match opcode.strip_prefix("nop/") {
                Some(n) => n.parse().map_err(|_| format!("bad nop count `{opcode}`"))?,
                None => 1,
            };
            nop = Some(n);
            continue;
        }
        let expr = parse_expr(part)?;
        if let Op::Wait(tag) = expr.op {
            wait = Some(tag);
        }
        exprs.push(expr);
    }
    if let Some(count) = nop {
        if exprs.iter().any(|e| !matches!(e.op, Op::Wait(_))) {
            return Err("nop can only be issued with wait".into());
        }
        return Ok(Line::Nop { count, wait });
    }
    Ok(Line::Pe(exprs))
}

fn parse_mask_directive(text: &str) -> Option<Line> {
    let mut it = text.split_whitespace();
    let op = it.next()?;
    let arg = it.next()?;
    if it.next().is_some() {
        return None;
    }
    let mut rest = op.strip_prefix("mask")?;
    let wl = if let Some(r) = rest.strip_prefix("ll") {
        rest = r;
        4
    } else if let Some(r) = rest.strip_prefix('l') {
        rest = r;
        2
    } else {
        2
    };
    let mut t = MaskTargets::default();
    for c in rest.chars() {
        match c {
            'r' => t.grf0 = true,
            's' => t.grf1 = true,
            't' => t.t = true,
            'm' => t.lm0 = true,
            'n' => t.lm1 = true,
            'k' => t.mask_reg = true,
            _ => return None,
        }
    }
    let entry = parse_int(arg)? as u8;
    Some(Line::MaskDirective { wl, targets: t, entry })
}

fn parse_int(s: &str) -> Option<u64> {
    if let Some(h) = s.strip_prefix("0x") {
        u64::from_str_radix(h, 16).ok()
    } else if let Some(b) = s.strip_prefix("0b") {
        u64::from_str_radix(b, 2).ok()
    } else {
        s.parse().ok()
    }
}

fn parse_debug(rest: &str, text: &str) -> Result<Line, String> {
    let mut it = rest.split_whitespace();
    let cmd = it.next().ok_or("empty debug statement")?;
    let loc = parse_debug_loc(it.next().ok_or("missing location")?)?;
    let count: u32 = it.next().ok_or("missing count")?.parse().map_err(|_| "bad count")?;
    match cmd {
        "set" => {
            let hex: String = it.collect::<Vec<_>>().concat();
            if hex.len() % 16 != 0 || !hex.chars().all(|c| c.is_ascii_hexdigit()) {
                return Err("d set payload must be 16-digit hex long words".into());
            }
            let payload = (0..hex.len() / 16)
                .map(|i| u64::from_str_radix(&hex[i * 16..i * 16 + 16], 16).unwrap())
                .collect();
            Ok(Line::DebugSet { loc, count, payload })
        }
        _ if cmd.starts_with("get") => {
            let dtype = cmd[3..].chars().next();
            let comment = text.split_once('#').map(|x| x.1.trim().to_string()).unwrap_or_default();
            Ok(Line::DebugGet { loc, count, dtype, comment })
        }
        _ => Err(format!("unknown debug statement `{cmd}`")),
    }
}

fn parse_dram_set(rest: &str) -> Result<Line, String> {
    let f: Vec<&str> = rest.split_whitespace().collect();
    if f.len() != 4 {
        return Err("DRAM initialization needs `r <group> <addr> <count> <payload>`".into());
    }
    let group = f[0].parse().map_err(|_| "bad DRAM group")?;
    let addr = u64::from_str_radix(f[1], 16).map_err(|_| "bad DRAM address")?;
    let count = usize::from_str_radix(f[2], 16).map_err(|_| "bad DRAM count")?;
    let hex = f[3];
    if hex.len() != count * 16 || !hex.chars().all(|c| c.is_ascii_hexdigit()) {
        return Err("DRAM payload must be <count> 16-digit hex long words".into());
    }
    let payload = (0..count).map(|i| u64::from_str_radix(&hex[i * 16..i * 16 + 16], 16).unwrap()).collect();
    Ok(Line::DramSet { group, addr, payload })
}

fn parse_debug_loc(s: &str) -> Result<DebugLoc, String> {
    let s = s.strip_prefix('$').ok_or("debug location must start with $")?;
    let (wl, s) = access_len(s);
    let mut chars = s.char_indices();
    let (_, k) = chars.next().ok_or("empty location")?;
    let mut s = &s[k.len_utf8()..];
    let mem = match k {
        'm' => MemKind::Lm0,
        'n' => MemKind::Lm1,
        'r' => MemKind::Grf0,
        's' => MemKind::Grf1,
        't' => MemKind::T,
        'b' => MemKind::L1bm,
        'c' => MemKind::L2bm,
        'p' => MemKind::Pdm,
        'd' => MemKind::Dram,
        _ => return Err(format!("unknown memory `{k}`")),
    };
    let (addr, r) = take_num(s);
    s = r;
    let mut loc = DebugLoc { mem, wl, addr: addr.unwrap_or(0) as u32, group: None, l2b: None, l1b: None, mab: None, pe: None };
    while let Some(c) = s.chars().next() {
        let (n, r) = take_num(&s[1..]);
        let n = n.ok_or_else(|| format!("missing number after `{c}`"))? as u8;
        match c {
            'n' => loc.group = Some(n),
            'c' => loc.l2b = Some(n),
            'b' => loc.l1b = Some(n),
            'm' => loc.mab = Some(n),
            'p' => loc.pe = Some(n),
            _ => return Err(format!("unexpected `{c}` in location")),
        }
        s = r;
    }
    Ok(loc)
}

fn access_len(s: &str) -> (u8, &str) {
    if let Some(r) = s.strip_prefix("ll") {
        (4, r)
    } else if let Some(r) = s.strip_prefix('l') {
        (2, r)
    } else {
        (1, s)
    }
}

fn take_num(s: &str) -> (Option<u64>, &str) {
    let end = s.find(|c: char| !c.is_ascii_digit()).unwrap_or(s.len());
    if end == 0 {
        (None, s)
    } else {
        (s[..end].parse().ok(), &s[end..])
    }
}

/// Splits an expression into its opcode and operand tokens.
///
/// Operands may be written without spaces between them (`imm f"1.0"$r0`, `$lc0@2.1$p0@0`), so a
/// new operand starts at every `$` that is not part of a mask (`/$imr1`), and at `-$`.
fn tokenize(part: &str) -> (String, Vec<String>) {
    let part = part.trim();
    let (opcode, rest) = match part.find(char::is_whitespace) {
        Some(i) => (&part[..i], &part[i..]),
        None => (part, ""),
    };
    let mut toks: Vec<String> = Vec::new();
    let mut cur = String::new();
    let mut in_quote = false;
    let chars: Vec<char> = rest.chars().collect();
    for (i, &c) in chars.iter().enumerate() {
        if in_quote {
            cur.push(c);
            if c == '"' {
                in_quote = false;
            }
            continue;
        }
        let starts_operand = (c == '$' && !cur.ends_with('/') && !cur.ends_with('-'))
            || (c == '-' && chars.get(i + 1) == Some(&'$'));
        if c.is_whitespace() || (starts_operand && !cur.is_empty()) {
            if !cur.is_empty() {
                toks.push(std::mem::take(&mut cur));
            }
            if c.is_whitespace() {
                continue;
            }
        }
        if c == '"' {
            in_quote = true;
        }
        cur.push(c);
    }
    if !cur.is_empty() {
        toks.push(cur);
    }
    (opcode.to_string(), toks)
}

fn parse_expr(part: &str) -> Result<Expr, String> {
    let (opcode, toks) = tokenize(part);
    let text = part.trim().to_string();
    // `hbfn/<n>` and `hbfe/<n>` carry the mantissa length after the slash.
    let (opcode, bf_arg) = match opcode.strip_prefix("hbfn/").or_else(|| opcode.strip_prefix("hbfe/")) {
        Some(rest) => {
            let (n, tail) = rest.split_once('/').map(|(a, b)| (a, Some(b))).unwrap_or((rest, None));
            let n: u8 = n.parse().map_err(|_| format!("bad mantissa length in `{opcode}`"))?;
            let name = &opcode[..4];
            (match tail { Some(t) => format!("{name}/{t}"), None => name.to_string() }, Some(n))
        }
        None => (opcode, None),
    };
    let (opcode, flush) = match opcode.split_once('/') {
        Some((o, m)) if !o.starts_with("mv") => (o.to_string(), Some(parse_mask_sel(m)?)),
        _ => (opcode, None),
    };

    if opcode == "noforward" {
        return Ok(Expr { op: Op::Noforward, srcs: vec![], dsts: vec![], flush, text });
    }
    if opcode == "wait" {
        let tag = toks.first().and_then(|t| t.strip_prefix('i')).and_then(|t| u8::from_str_radix(t, 16).ok());
        return Ok(Expr { op: Op::Wait(tag.ok_or("bad wait tag")?), srcs: vec![], dsts: vec![], flush, text });
    }
    if opcode.starts_with("l1bm") || opcode.starts_with("l2bm") {
        let srcs = toks.iter().map(|t| Operand::Raw(t.clone())).collect();
        return Ok(Expr { op: Op::Other(opcode), srcs, dsts: vec![], flush, text });
    }
    if opcode == "zero" {
        let dsts = toks.iter().map(|t| parse_operand(t)).collect::<Result<_, _>>()?;
        return Ok(Expr { op: Op::Zero, srcs: vec![], dsts, flush, text });
    }
    if opcode == "imm" || opcode == "immu" {
        let lit = toks.first().ok_or("imm needs a literal")?;
        let value = parse_imm(lit)?;
        let dsts = toks[1..].iter().map(|t| parse_operand(t)).collect::<Result<_, _>>()?;
        return Ok(Expr { op: Op::Imm { value, u: opcode == "immu" }, srcs: vec![], dsts, flush, text });
    }
    let mut op = classify(&opcode).ok_or_else(|| format!("unknown opcode `{opcode}`"))?;
    if let Op::Alu { arg, name, .. } = &mut op {
        if matches!(name, AluOp::Bfn | AluOp::Bfe) {
            *arg = bf_arg;
        }
    }
    let n_in = match &op {
        Op::Alu { name, .. } => name.inputs(),
        Op::Mau { matrix, kind, .. } => match (matrix, kind) {
            (_, MauKind::Fma) => 3,
            (_, MauKind::Mul) | (false, MauKind::Add) => 2,
            _ => 1,
        },
        Op::MatWrite { .. } | Op::MatRead { .. } => 1,
        _ => 0,
    };
    if toks.len() <= n_in {
        return Err(format!("`{opcode}` needs {n_in} inputs and at least one output"));
    }
    let ops: Vec<Operand> = toks.iter().map(|t| parse_operand(t)).collect::<Result<_, _>>()?;
    let (srcs, dsts) = ops.split_at(n_in);
    Ok(Expr { op, srcs: srcs.to_vec(), dsts: dsts.to_vec(), flush, text })
}

fn classify(opcode: &str) -> Option<Op> {
    // MAU and matrix register instructions: [dfgh](m|v)... and [dfgh]m(write|read)
    let mut cs = opcode.chars();
    let p = cs.next()?;
    let prec = match p {
        'd' => Some(Prec::D),
        'f' => Some(Prec::F),
        'g' => Some(Prec::G),
        'h' => Some(Prec::H),
        _ => None,
    };
    if let Some(prec) = prec {
        let rest = &opcode[1..];
        if rest == "mwrite" {
            return Some(Op::MatWrite { prec });
        }
        if rest == "mread" {
            return Some(Op::MatRead { prec });
        }
        for (pre, matrix) in [("m", true), ("v", false)] {
            if let Some(r) = rest.strip_prefix(pre) {
                for (kname, kind) in [("fma", MauKind::Fma), ("mul", MauKind::Mul), ("add", MauKind::Add), ("passa", MauKind::Passa)] {
                    if let Some(mut tail) = r.strip_prefix(kname) {
                        let mut half = None;
                        if let Some(t) = tail.strip_prefix('u') {
                            half = Some('u');
                            tail = t;
                        } else if let Some(t) = tail.strip_prefix('d') {
                            half = Some('d');
                            tail = t;
                        }
                        let round = match tail {
                            "" => false,
                            "r" => true,
                            _ => continue,
                        };
                        return Some(Op::Mau { prec, matrix, kind, half, round });
                    }
                }
            }
        }
    }
    // ALU: [u][(d|f|g|h|l|i|s)]<name>
    let (unsigned, s) = match opcode.strip_prefix('u') {
        Some(r) if !r.is_empty() => (true, r),
        _ => (false, opcode),
    };
    let candidates: [(Option<Prec>, &str); 2] = [
        (None, s),
        (
            match s.chars().next()? {
                'd' => Some(Prec::D),
                'f' => Some(Prec::F),
                'g' => Some(Prec::G),
                'h' => Some(Prec::H),
                'l' => Some(Prec::L),
                'i' => Some(Prec::I),
                's' => Some(Prec::S),
                _ => None,
            },
            &s[1..],
        ),
    ];
    for (prec, name) in candidates {
        if prec.is_none() && name.len() != s.len() {
            continue;
        }
        let Some(&(_, op, ty, _)) = ALU_OPS.iter().find(|e| e.0 == name) else { continue };
        let ok = match (ty, prec) {
            (AluType::Untyped, None) => true,
            (AluType::Untyped, Some(_)) => false,
            (_, None) => false,
            (AluType::Int, Some(p)) => matches!(p, Prec::L | Prec::I | Prec::S),
            (AluType::Float, Some(p)) => matches!(p, Prec::D | Prec::F | Prec::H),
            (AluType::Both, Some(p)) => p != Prec::G,
            (AluType::Bfn, Some(p)) => matches!(p, Prec::D | Prec::F | Prec::G | Prec::H),
            (AluType::Bfe, Some(p)) => p == Prec::H,
        };
        if ok && !(unsigned && prec.is_none()) {
            return Some(Op::Alu { name: op, prec, unsigned, arg: None });
        }
    }
    None
}

/// Parses an immediate literal into the single word that `imm` repeats (SDM 3.2.2).
fn parse_imm(lit: &str) -> Result<u32, String> {
    let (ty, body) = lit.split_once('"').ok_or_else(|| format!("bad immediate `{lit}`"))?;
    let body = body.strip_suffix('"').ok_or_else(|| format!("bad immediate `{lit}`"))?;
    match ty {
        "f" => {
            let v: f32 = parse_c_float(body).ok_or_else(|| format!("bad float `{body}`"))?;
            Ok(v.to_bits())
        }
        "h" => {
            let v: f32 = parse_c_float(body).ok_or_else(|| format!("bad float `{body}`"))?;
            let h = crate::float::encode(crate::float::HALF, crate::float::decode(crate::float::SINGLE, v.to_bits() as u64)) as u32;
            Ok((h << 16) | h)
        }
        "i" | "ui" | "s" | "us" => {
            let (neg, digits) = match body.strip_prefix('-') {
                Some(d) => (true, d),
                None => (false, body.strip_prefix('+').unwrap_or(body)),
            };
            if neg && ty.starts_with('u') {
                return Err(format!("unsigned immediate `{lit}` cannot be negative"));
            }
            let mag = parse_int(digits).ok_or_else(|| format!("bad integer `{body}`"))? as i64;
            let v = if neg { -mag } else { mag };
            let (lo, hi) = match ty {
                "i" => (i32::MIN as i64, i32::MAX as i64),
                "ui" => (0, u32::MAX as i64),
                "s" => (i16::MIN as i64, i16::MAX as i64),
                _ => (0, u16::MAX as i64),
            };
            if v < lo || v > hi {
                return Err(format!("immediate `{lit}` out of range"));
            }
            if ty.ends_with('s') {
                let h = v as u16 as u32;
                Ok((h << 16) | h)
            } else {
                Ok(v as u32)
            }
        }
        _ => Err(format!("unknown immediate type `{ty}`")),
    }
}

/// Approximates C `strtof` for decimal and hexadecimal float literals.
fn parse_c_float(s: &str) -> Option<f32> {
    let s = s.trim();
    let lower = s.to_ascii_lowercase();
    match lower.trim_start_matches(['+', '-']) {
        "inf" | "infinity" => return Some(if s.starts_with('-') { f32::NEG_INFINITY } else { f32::INFINITY }),
        _ => {}
    }
    if lower.trim_start_matches(['+', '-']).starts_with("0x") {
        return None; // TODO: hexadecimal float literals
    }
    s.parse::<f32>().ok()
}

fn parse_mask_sel(s: &str) -> Result<MaskSel, String> {
    let s = s.trim_end_matches(['t', 'p']);
    let (ll, s) = match s.strip_prefix("$llimr") {
        Some(r) => (true, format!("$imr{r}")),
        None => match s.strip_prefix("ll") {
            Some(r) => (true, r.to_string()),
            None => (false, s.to_string()),
        },
    };
    if let Some(n) = s.strip_prefix("$imr") {
        let n: u8 = n.parse().map_err(|_| format!("bad mask entry `{s}`"))?;
        return Ok(MaskSel { ll, source: MaskSource::Entry(n) });
    }
    let b: Vec<char> = s.chars().collect();
    if b.len() == 4 && b.iter().all(|c| *c == '0' || *c == '1') {
        let mut p = [false; 4];
        for i in 0..4 {
            p[i] = b[i] == '1';
        }
        return Ok(MaskSel { ll, source: MaskSource::Pattern(p) });
    }
    Err(format!("bad mask `{s}`"))
}

pub fn parse_operand(tok: &str) -> Result<Operand, String> {
    let (body, mask) = match tok.split_once('/') {
        Some((b, m)) => (b, Some(parse_mask_sel(m)?)),
        None => (tok, None),
    };
    let (neg, body) = match body.strip_prefix('-') {
        Some(b) => (true, b),
        None => (false, body),
    };
    let s = body.strip_prefix('$').ok_or_else(|| format!("operand `{tok}` must start with $"))?;

    let fwd = |kind| Operand::Forward { kind, neg, ext: false, rnd: false };
    match s {
        "aluf" => return Ok(fwd(FwdKind::Aluf)),
        "mauf" => return Ok(fwd(FwdKind::Mauf)),
        "lbf" => return Ok(fwd(FwdKind::Lbf)),
        "mreadf" => return Ok(fwd(FwdKind::Mreadf)),
        "nowrite" => return Ok(Operand::Nowrite),
        "l2bid" => return Ok(Operand::Fixed(FixedKind::L2bid)),
        "l1bid" => return Ok(Operand::Fixed(FixedKind::L1bid)),
        "mabid" => return Ok(Operand::Fixed(FixedKind::Mabid)),
        "peid" => return Ok(Operand::Fixed(FixedKind::Peid)),
        "subpeid" => return Ok(Operand::Fixed(FixedKind::Subpeid)),
        "msb1" => return Ok(Operand::Fixed(FixedKind::Msb1)),
        _ => {}
    }
    for (name, kind) in [("aluf", FwdKind::Aluf), ("mauf", FwdKind::Mauf), ("lbf", FwdKind::Lbf), ("mreadf", FwdKind::Mreadf)] {
        if let Some(sfx) = s.strip_prefix(name) {
            return match sfx {
                "e" => Ok(Operand::Forward { kind, neg, ext: true, rnd: false }),
                "r" => Ok(Operand::Forward { kind, neg, ext: false, rnd: true }),
                _ => Err(format!("bad operand `{tok}`")),
            };
        }
    }
    if let Some(n) = s.strip_prefix("omr") {
        let entry = n.parse().map_err(|_| format!("bad mask register `{tok}`"))?;
        return Ok(Operand::Omr { entry, mask });
    }
    let (wl, s) = access_len(s);
    match s {
        "mb" => return Ok(Operand::Bar { lm1: false, wl, mask }),
        "nb" => return Ok(Operand::Bar { lm1: true, wl, mask }),
        _ => {}
    }
    let mut chars = s.chars();
    let k = chars.next().ok_or_else(|| format!("bad operand `{tok}`"))?;
    let rest = &s[1..];
    if k == 'x' || k == 'y' {
        let (row, r) = take_num(rest);
        if !r.is_empty() {
            return Err(format!("bad matrix operand `{tok}`"));
        }
        return Ok(Operand::Mat { y: k == 'y', wl, row: row.map(|r| r as u32) });
    }
    let mem = match k {
        'm' => MemKind::Lm0,
        'n' => MemKind::Lm1,
        'r' => MemKind::Grf0,
        's' => MemKind::Grf1,
        't' => MemKind::T,
        _ => return Ok(Operand::Raw(tok.to_string())),
    };
    let mut rest = rest;
    let mut ext = false;
    let mut rnd = false;
    if mem == MemKind::T {
        // T is always accessed as two long words and has no address.
        match rest {
            "" => {}
            "e" => ext = true,
            "r" => rnd = true,
            _ => return Err(format!("bad T operand `{tok}`")),
        }
        let addr = Addr { cycles: [0; 4], t_indirect: false, madpe: None };
        return Ok(Operand::Mem { mem, wl: 4, addr, neg, ext, rnd, mask });
    }
    let mut t_indirect = false;
    if mem == MemKind::Lm0 {
        if let Some(r) = rest.strip_prefix('t') {
            t_indirect = true;
            rest = r;
        }
    }
    let cycles: [u32; 4];
    if let Some(r) = rest.strip_prefix('[') {
        let (list, r) = r.split_once(']').ok_or_else(|| format!("bad flat address `{tok}`"))?;
        let v: Vec<u32> = list.split(',').map(|x| x.trim().parse()).collect::<Result<_, _>>().map_err(|_| format!("bad flat address `{tok}`"))?;
        if v.len() != 4 {
            return Err(format!("flat address needs 4 entries `{tok}`"));
        }
        cycles = [v[0], v[1], v[2], v[3]];
        rest = r;
    } else {
        let (base, r) = take_num(rest);
        let base = base.unwrap_or(0) as u32;
        rest = r;
        let mut inc = 0;
        if let Some(r) = rest.strip_prefix('v') {
            let (n, r) = take_num(r);
            inc = n.map(|n| n as u32).unwrap_or(wl as u32);
            rest = r;
        }
        cycles = [base, base + inc, base + 2 * inc, base + 3 * inc];
    }
    let mut madpe = None;
    if let Some(r) = rest.strip_prefix('j') {
        let (n, r) = take_num(r);
        madpe = Some(n.ok_or_else(|| format!("bad j in `{tok}`"))? as u8);
        rest = r;
    }
    match rest {
        "" => {}
        "e" => ext = true,
        "r" => rnd = true,
        _ => return Err(format!("bad operand `{tok}`")),
    }
    Ok(Operand::Mem { mem, wl, addr: Addr { cycles, t_indirect, madpe }, neg, ext, rnd, mask })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn tokenize_glued_operands() {
        let (op, t) = tokenize(r#"imm f"1.0"$r0/1000"#);
        assert_eq!(op, "imm");
        assert_eq!(t, vec![r#"f"1.0""#, "$r0/1000"]);
        let (_, t) = tokenize("dvadd -$lr0v -$lm0v $ln0v");
        assert_eq!(t, vec!["-$lr0v", "-$lm0v", "$ln0v"]);
        let (_, t) = tokenize("lpassa $ln0v $lr0v/$imr1");
        assert_eq!(t, vec!["$ln0v", "$lr0v/$imr1"]);
    }

    #[test]
    fn classify_opcodes() {
        assert!(matches!(classify("fvfma"), Some(Op::Mau { prec: Prec::F, matrix: false, kind: MauKind::Fma, .. })));
        assert!(matches!(classify("dmfmaur"), Some(Op::Mau { prec: Prec::D, matrix: true, half: Some('u'), round: true, .. })));
        assert!(matches!(classify("gmwrite"), Some(Op::MatWrite { prec: Prec::G })));
        assert!(matches!(classify("ixor"), Some(Op::Alu { name: AluOp::Xor, prec: Some(Prec::I), .. })));
        assert!(matches!(classify("lnot"), Some(Op::Alu { name: AluOp::Not, prec: Some(Prec::L), .. })));
        assert!(matches!(classify("ullsr"), Some(Op::Alu { name: AluOp::Lsr, prec: Some(Prec::L), unsigned: true })));
        assert!(matches!(classify("msr"), Some(Op::Alu { name: AluOp::Msr, prec: None, .. })));
        assert!(matches!(classify("gbfn"), Some(Op::Alu { name: AluOp::Bfn, prec: Some(Prec::G), .. })));
        assert!(classify("lsl").is_none());
    }

    #[test]
    fn operands() {
        let o = parse_operand("$lm8v").unwrap();
        assert!(matches!(o, Operand::Mem { mem: MemKind::Lm0, wl: 2, addr: Addr { cycles: [8, 10, 12, 14], .. }, .. }));
        let o = parse_operand("$llr0v8").unwrap();
        assert!(matches!(o, Operand::Mem { wl: 4, addr: Addr { cycles: [0, 8, 16, 24], .. }, .. }));
        let o = parse_operand("$lm[0,2,0,2]").unwrap();
        assert!(matches!(o, Operand::Mem { addr: Addr { cycles: [0, 2, 0, 2], .. }, .. }));
        let o = parse_operand("$r0ve").unwrap();
        assert!(matches!(o, Operand::Mem { wl: 1, ext: true, addr: Addr { cycles: [0, 1, 2, 3], .. }, .. }));
        let o = parse_operand("$lr0/1000").unwrap();
        assert!(matches!(o, Operand::Mem { mask: Some(MaskSel { ll: false, source: MaskSource::Pattern([true, false, false, false]) }), .. }));
        assert!(matches!(parse_operand("$ly4").unwrap(), Operand::Mat { y: true, wl: 2, row: Some(4) }));
        assert!(matches!(parse_operand("$ly").unwrap(), Operand::Mat { y: true, row: None, .. }));
    }

    #[test]
    fn immediates() {
        assert_eq!(parse_imm(r#"f"1.0""#).unwrap(), 0x3f80_0000);
        assert_eq!(parse_imm(r#"i"-1""#).unwrap(), 0xffff_ffff);
        assert_eq!(parse_imm(r#"us"0x8000""#).unwrap(), 0x8000_8000);
        assert!(parse_imm(r#"s"0x8000""#).is_err());
    }

    #[test]
    fn all_problem_solutions_parse() {
        let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../problems");
        let Ok(dirs) = std::fs::read_dir(&root) else { return };
        for d in dirs.flatten() {
            for name in ["main.vsm", "testcase.vsm"] {
                let p = d.path().join(name);
                let Ok(src) = std::fs::read_to_string(&p) else { continue };
                if let Err(e) = parse(&src) {
                    panic!("{}: {e}", p.display());
                }
            }
        }
    }
}
