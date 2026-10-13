//! Entry point for the visualization: simulates a solution with its testcase and returns
//! everything the site shows, as one serializable value.

use serde::Serialize;

use crate::hazard;
use crate::machine::PES;
use crate::run::Sim;
use crate::trace::{self, Access, Flow, Tracer};
use crate::vsm::{self, Line};

pub const VSM_HERE: &str = "# ======= YOUR VSM WILL BE INSERTED HERE =======";

/// One expression of a PE statement.
#[derive(Serialize)]
pub struct ExprInfo {
    pub text: String,
    /// alu, mau, matrix, mwrite, mread, l1-to-pe, pe-to-l1, l2, wait, noforward
    pub unit: &'static str,
    /// The forwarding register this expression updates (aluf, mauf, mreadf, lbf).
    pub fwd: Option<&'static str>,
    /// Issue group of SDM 3.6.4 (table 3.6): at most one expression per group in a step.
    /// alu, mau-calc, mau-mwrite, mau-mread, l1bm, l1bm-turnaround, l2bm, l2bmdarw, wait,
    /// noforward.
    pub group: &'static str,
    /// Opcode and operand texts as written.
    pub opcode: String,
    pub srcs: Vec<String>,
    pub dsts: Vec<String>,
}

#[derive(Serialize)]
pub struct LineInfo {
    /// Line number in the solution (1-based).
    pub lineno: usize,
    pub text: String,
    /// pe, nop, mv, mask, debug
    pub kind: &'static str,
    /// First step this line occupies, and how many it occupies (its share of the score).
    pub step: u32,
    pub words: u32,
    pub flows: Vec<Flow>,
    /// Expressions of a PE statement (empty for other lines).
    pub exprs: Vec<ExprInfo>,
    /// Accesses of the focus PEs in this line.
    pub accesses: Vec<Access>,
}

fn expr_infos(l: &Line) -> Vec<ExprInfo> {
    use crate::vsm::{Op, Operand};
    let Line::Pe(exprs) = l else { return Vec::new() };
    exprs
        .iter()
        .map(|e| {
            let (unit, fwd) = match &e.op {
                Op::Alu { .. } | Op::Imm { .. } | Op::Zero => ("alu", Some("aluf")),
                Op::Mau { matrix: true, .. } => ("matrix", Some("mauf")),
                Op::Mau { .. } => ("mau", Some("mauf")),
                Op::MatWrite { .. } => ("mwrite", None),
                Op::MatRead { .. } => ("mread", Some("mreadf")),
                Op::L1(_) if matches!(e.srcs.first(), Some(Operand::L1bm { .. })) => ("l1-to-pe", Some("lbf")),
                Op::L1(_) => ("pe-to-l1", None),
                Op::L2(_) => ("l2", None),
                Op::Wait(_) => ("wait", None),
                Op::Noforward => ("noforward", None),
                Op::Other(_) => ("other", None),
            };
            let turnaround = e.srcs.iter().chain(&e.dsts).any(|o| matches!(o, Operand::L1bm { addr: None, .. }));
            let group = match &e.op {
                Op::Alu { .. } | Op::Imm { .. } | Op::Zero => "alu",
                Op::Mau { .. } => "mau-calc",
                Op::MatWrite { .. } => "mau-mwrite",
                Op::MatRead { .. } => "mau-mread",
                Op::L1(_) if turnaround => "l1bm-turnaround",
                Op::L1(_) => "l1bm",
                Op::L2(crate::blockop::L2Op::Darw) => "l2bmdarw",
                Op::L2(_) => "l2bm",
                Op::Wait(_) => "wait",
                Op::Noforward => "noforward",
                Op::Other(_) => "other",
            };
            let (opcode, toks) = crate::vsm::tokenize(&e.text);
            let ndst = e.dsts.len().min(toks.len());
            let (srcs, dsts) = toks.split_at(toks.len() - ndst);
            ExprInfo { text: e.text.clone(), unit, fwd, group, opcode, srcs: srcs.to_vec(), dsts: dsts.to_vec() }
        })
        .collect()
}

#[derive(Serialize)]
pub struct Hazard {
    pub rule: &'static str,
    pub kind: &'static str,
    pub res: String,
    pub addr: Option<u32>,
    /// Indices into `lines` of the writing and of the later accessing line.
    pub from: usize,
    pub to: usize,
    pub distance: u32,
    pub required: u32,
}

#[derive(Serialize)]
pub struct Nop {
    /// Index into `lines`.
    pub line: usize,
    /// Indices into `hazards` that need this nop. Empty: one step of it can be removed.
    pub needed_by: Vec<usize>,
}

#[derive(Serialize, Default)]
pub struct OutputCheck {
    /// Number of output values compared with the testcase's expectation.
    pub values: usize,
    /// Values outside the allowed absolute error.
    pub failures: usize,
    pub max_abs_error: f64,
    pub atol: f64,
    /// Description of the first failing value.
    pub first_failure: Option<String>,
}

#[derive(Serialize)]
pub struct Trace {
    pub lines: Vec<LineInfo>,
    pub score: u32,
    pub hazards: Vec<Hazard>,
    pub nops: Vec<Nop>,
    pub focus: Vec<u32>,
    /// Initial contents of the focus PEs' memories written by the testcase (`d set`).
    pub init: Vec<Access>,
    pub output: OutputCheck,
    /// Why the simulation stopped early (unsupported instruction or run-time error).
    pub error: Option<String>,
    pub error_line: Option<usize>,
}

fn kind_of(l: &Line) -> &'static str {
    match l {
        Line::Pe(_) => "pe",
        Line::Nop { .. } => "nop",
        Line::Mv(_) => "mv",
        Line::MaskDirective { .. } => "mask",
        _ => "debug",
    }
}

/// Simulates `solution` inside `testcase` (which contains the VSM_HERE marker) and records
/// the focus PEs (global PE indices).
pub fn trace(testcase: &str, solution: &str, focus: &[usize]) -> Result<Trace, String> {
    let (prefix, suffix) = match testcase.split_once(VSM_HERE) {
        Some((p, s)) => (p, s),
        None => ("", testcase),
    };
    let pre = vsm::parse(prefix).map_err(|e| format!("testcase: {e}"))?;
    let post = vsm::parse(suffix).map_err(|e| format!("testcase: {e}"))?;
    let main = vsm::parse(solution).map_err(|e| format!("solution: {e}"))?;
    let src_lines: Vec<&str> = solution.lines().collect();

    let mut sim = Sim::new();
    *sim.m.tracer.borrow_mut() = Some(Tracer::new(focus, PES));
    let mut error = None;
    let mut error_line = None;
    for (_, l) in &pre {
        if let Err(e) = sim.exec(l) {
            error = Some(format!("testcase: {}", e.message()));
            break;
        }
    }
    let init = sim.m.tracer.borrow_mut().as_mut().map(|t| t.take()).unwrap_or_default();

    let constraints = hazard::analyze(&main);
    let mut lines = Vec::with_capacity(main.len());
    let mut step = 0u32;
    for (i, (lineno, l)) in main.iter().enumerate() {
        if error.is_none() {
            if let Err(e) = sim.exec(l) {
                error = Some(e.message());
                error_line = Some(i);
            }
        }
        let accesses = sim.m.tracer.borrow_mut().as_mut().map(|t| t.take()).unwrap_or_default();
        lines.push(LineInfo {
            lineno: *lineno,
            text: src_lines.get(lineno - 1).map(|s| s.trim().to_string()).unwrap_or_default(),
            kind: kind_of(l),
            step,
            words: l.words(),
            flows: trace::flows(l),
            exprs: expr_infos(l),
            accesses,
        });
        step += l.words();
    }

    // Outputs: run the testcase's suffix and compare with the expected values.
    let mut output = OutputCheck::default();
    if error.is_none() {
        *sim.m.tracer.borrow_mut() = None;
        for (lineno, l) in &post {
            if let Err(e) = sim.exec(l) {
                error = Some(format!("testcase line {lineno}: {}", e.message()));
                break;
            }
            if let Line::DebugGet { loc, count, comment, .. } = l {
                check_output(&sim, loc, *count, comment, &mut output);
            }
        }
    }

    let hazards: Vec<Hazard> = constraints
        .iter()
        .map(|c| Hazard {
            rule: c.rule,
            kind: match c.kind {
                hazard::Kind::DataRace => "data race",
                hazard::Kind::PortConflict => "port conflict",
            },
            res: format!("{:?}", c.res),
            addr: c.addr,
            from: c.from_line,
            to: c.to_line,
            distance: c.distance,
            required: c.required,
        })
        .collect();
    let nops = hazard::nop_reasons(&main, &constraints)
        .into_iter()
        .map(|(line, cs)| Nop {
            line,
            needed_by: cs.iter().filter_map(|c| constraints.iter().position(|x| x == c)).collect(),
        })
        .collect();

    Ok(Trace { lines, score: step, hazards, nops, focus: focus.iter().map(|&p| p as u32).collect(), init, output, error, error_line })
}

/// Compares one `d get` line of the testcase suffix with its `expect=[...]` comment.
fn check_output(sim: &Sim, loc: &vsm::DebugLoc, count: u32, comment: &str, out: &mut OutputCheck) {
    // Comment: "expect=[a, b] / Float @[0,0],[0,1] atol=1e-05"
    let Some(rest) = comment.strip_prefix("expect=[") else { return };
    let Some((vals, rest)) = rest.split_once(']') else { return };
    let expected: Vec<f64> = vals.split(',').filter_map(|v| v.trim().parse().ok()).collect();
    let dtype = rest.trim().trim_start_matches('/').split_whitespace().next().unwrap_or("");
    let atol: f64 = rest.split("atol=").nth(1).and_then(|a| a.trim().parse().ok()).unwrap_or(0.0);
    out.atol = out.atol.max(atol);
    let name = match loc.mem {
        vsm::MemKind::Dram => "DRAM",
        vsm::MemKind::Lm0 => "LM0",
        vsm::MemKind::Lm1 => "LM1",
        vsm::MemKind::Grf0 => "GREG0",
        vsm::MemKind::Grf1 => "GREG1",
        _ => return,
    };
    let path = match loc.mem {
        vsm::MemKind::Dram => format!("n{}", loc.group.unwrap_or(0)),
        _ => format!(
            "n{}c{}b{}m{}p{}",
            loc.group.unwrap_or(0),
            loc.l2b.unwrap_or(0),
            loc.l1b.unwrap_or(0),
            loc.mab.unwrap_or(0),
            loc.pe.unwrap_or(0)
        ),
    };
    let mut actual: Vec<f64> = Vec::new();
    for i in 0..count {
        let a = loc.addr + if loc.mem == vsm::MemKind::Dram { i } else { 2 * i };
        let Some(&v) = sim.dump.get(&(name.to_string(), path.clone(), a)) else { return };
        match dtype {
            "Double" => actual.push(f64::from_bits(v)),
            "Float" => {
                actual.push(f32::from_bits((v >> 32) as u32) as f64);
                actual.push(f32::from_bits(v as u32) as f64);
            }
            _ => {
                // Integers: two words per long word.
                actual.push((v >> 32) as u32 as i32 as f64);
                actual.push(v as u32 as i32 as f64);
            }
        }
    }
    for (k, (e, a)) in expected.iter().zip(&actual).enumerate() {
        out.values += 1;
        let err = (e - a).abs();
        if err.is_finite() {
            out.max_abs_error = out.max_abs_error.max(err);
        }
        let bad = !(err <= atol) && !(e == a);
        if bad {
            out.failures += 1;
            if out.first_failure.is_none() {
                out.first_failure = Some(format!("{name} {path} element {k}: expected {e}, got {a}"));
            }
        }
    }
}
