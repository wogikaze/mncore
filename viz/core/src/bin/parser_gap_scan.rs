//! Inventory parser fallbacks in the 73 checked-in problem answers.
//!
//! Run from the repository with `cargo run --manifest-path viz/core/Cargo.toml
//! --bin parser_gap_scan`; the JSON output is an audit input, not a proof that
//! the answer corpus covers every accepted ISA spelling.

use mncore_sim::vsm::{self, Line, Op, Operand};
use serde_json::{json, Value};
use std::collections::BTreeSet;
use std::fs;
use std::path::{Path, PathBuf};

fn collect_answers(directory: &Path, out: &mut Vec<PathBuf>) -> std::io::Result<()> {
    for entry in fs::read_dir(directory)? {
        let path = entry?.path();
        if path.is_dir() {
            collect_answers(&path, out)?;
        } else if path.file_name().is_some_and(|name| name == "answer.vsm") {
            out.push(path);
        }
    }
    Ok(())
}

fn raw_operand(operand: &Operand) -> Option<&str> {
    match operand {
        Operand::Raw(text) => Some(text),
        _ => None,
    }
}

fn op_name(op: &Op) -> &'static str {
    match op {
        Op::Alu { .. } => "alu",
        Op::Imm { .. } => "imm",
        Op::Zero => "zero",
        Op::Mau { .. } => "mau",
        Op::MatWrite { .. } => "mat_write",
        Op::MatRead { .. } => "mat_read",
        Op::Wait(_) => "wait",
        Op::Noforward => "noforward",
        Op::L1(_) => "l1",
        Op::L2(_) => "l2",
        Op::Other(_) => "other",
    }
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let arguments: Vec<String> = std::env::args().collect();
    let spellings_path = arguments
        .windows(2)
        .find(|pair| pair[0] == "--spellings")
        .map(|pair| PathBuf::from(&pair[1]));
    let mut files = Vec::new();
    collect_answers(Path::new("problems"), &mut files)?;
    files.sort();
    let mut raw_operands = Vec::new();
    let mut other_ops = Vec::new();
    let mut parse_errors = Vec::new();
    let mut op_spellings = BTreeSet::new();
    let mut candidate_results = Vec::new();

    for path in &files {
        let source = fs::read_to_string(path)?;
        match vsm::parse(&source) {
            Err(error) => parse_errors.push(json!({
                "path": path,
                "line": error.line,
                "message": error.msg,
            })),
            Ok(lines) => {
                for (line_number, line) in lines {
                    let Line::Pe(expressions) = line else {
                        continue;
                    };
                    for expression in expressions {
                        op_spellings.insert(
                            expression
                                .text
                                .split_whitespace()
                                .next()
                                .unwrap_or("")
                                .to_string(),
                        );
                        if let Op::Other(text) = &expression.op {
                            other_ops.push(json!({
                                "path": path,
                                "line": line_number,
                                "opcode": text,
                            }));
                        }
                        for (role, operands) in
                            [("src", &expression.srcs), ("dst", &expression.dsts)]
                        {
                            for operand in operands {
                                if let Some(text) = raw_operand(operand) {
                                    raw_operands.push(json!({
                                        "path": path,
                                        "line": line_number,
                                        "expression": expression.text,
                                        "opcode_class": op_name(&expression.op),
                                        "role": role,
                                        "operand": text,
                                    }));
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    if let Some(path) = spellings_path {
        for spelling in fs::read_to_string(path)?
            .lines()
            .map(str::trim)
            .filter(|s| !s.is_empty())
        {
            let source = match spelling {
                "imm" => "imm i\"0\" $n0 $r0 $s0 $lm0 $ln0 $lr0 $ls0".to_string(),
                "immu" => "immu ui\"0\" $n0 $r0 $s0 $lm0 $ln0 $lr0 $ls0".to_string(),
                _ => format!("{spelling} $m0 $n0 $r0 $s0 $lm0 $ln0 $lr0 $ls0"),
            };
            let result = match vsm::parse(&source) {
                Ok(lines) => {
                    let mut parsed = Vec::new();
                    for (_, line) in lines {
                        if let Line::Pe(expressions) = line {
                            for expression in expressions {
                                let raw: Vec<_> = expression
                                    .srcs
                                    .iter()
                                    .chain(&expression.dsts)
                                    .filter_map(raw_operand)
                                    .collect();
                                parsed.push(json!({
                                    "class": op_name(&expression.op),
                                    "source_count": expression.srcs.len(),
                                    "destination_count": expression.dsts.len(),
                                    "raw_operands": raw,
                                }));
                            }
                        }
                    }
                    json!({ "parsed": true, "expressions": parsed })
                }
                Err(error) => json!({
                    "parsed": false,
                    "error": error.msg,
                }),
            };
            candidate_results.push(json!({ "spelling": spelling, "result": result }));
        }
    }

    let result: Value = json!({
        "schema_version": 1,
        "scope": "Checked-in problems/**/answer.vsm files only; not a complete ISA spelling inventory.",
        "answer_files": files.len(),
        "parsed_operator_spellings": op_spellings,
        "raw_operand_occurrences": raw_operands,
        "other_opcode_occurrences": other_ops,
        "parse_errors": parse_errors,
        "opcode_candidate_results": candidate_results,
    });
    println!("{}", serde_json::to_string_pretty(&result)?);
    Ok(())
}
