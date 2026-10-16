//! Inventory parser fallbacks in the 73 checked-in problem answers.
//!
//! Run from the repository with `cargo run --manifest-path viz/core/Cargo.toml
//! --bin parser_gap_scan`; the JSON output is an audit input, not a proof that
//! the answer corpus covers every accepted ISA spelling.

use mncore_sim::vsm::{self, Line, Op, Operand};
use serde_json::{json, Value};
use std::collections::{BTreeMap, BTreeSet};
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
    let mut raw_operand_fallback_probes = Vec::new();
    let mut answer_expression_shape_counts = BTreeMap::new();

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
                        let spelling = expression
                            .text
                            .split_whitespace()
                            .next()
                            .unwrap_or("")
                            .to_string();
                        op_spellings.insert(spelling.clone());
                        *answer_expression_shape_counts.entry((
                            spelling,
                            op_name(&expression.op),
                            expression.srcs.len(),
                            expression.dsts.len(),
                            expression.dsts.iter().enumerate().all(|(index, operand)| {
                                !expression.dsts[index + 1..].contains(operand)
                            }),
                        )).or_insert(0usize) += 1;
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

    for (case, source, expected_role) in [
        ("alu_source", "iadd $qraw $lm0 $ln0", "src"),
        ("alu_destination", "iadd $lm0 $ln0 $qraw", "dst"),
        ("zero_destination", "zero $qraw", "dst"),
        ("matrix_read_source", "gmread $qraw $nowrite", "src"),
        ("l1bm_source", "l1bmm $qraw $lb0", "src"),
    ] {
        let parsed = match vsm::parse(source) {
            Ok(lines) => {
                let mut expressions = Vec::new();
                for (_, line) in lines {
                    if let Line::Pe(parsed_line) = line {
                        for expression in parsed_line {
                            let raw: Vec<_> = [
                                ("src", &expression.srcs),
                                ("dst", &expression.dsts),
                            ]
                            .into_iter()
                            .flat_map(|(role, operands)| {
                                operands.iter().filter_map(move |operand| {
                                    raw_operand(operand).map(|text| json!({
                                        "role": role,
                                        "operand": text,
                                    }))
                                })
                            })
                            .collect();
                            expressions.push(json!({
                                "class": op_name(&expression.op),
                                "raw_operands": raw,
                            }));
                        }
                    }
                }
                json!({ "parsed": true, "expressions": expressions })
            }
            Err(error) => json!({ "parsed": false, "error": error.msg }),
        };
        raw_operand_fallback_probes.push(json!({
            "case": case,
            "source": source,
            "expected_role": expected_role,
            "result": parsed,
        }));
    }

    let answer_expression_shapes: Vec<_> = answer_expression_shape_counts
        .into_iter()
        .map(|((spelling, class, source_count, destination_count, destinations_nodup), occurrences)| json!({
            "spelling": spelling,
            "class": class,
            "source_count": source_count,
            "destination_count": destination_count,
            "destinations_nodup": destinations_nodup,
            "occurrences": occurrences,
        }))
        .collect();
    let result: Value = json!({
        "schema_version": 2,
        "scope": "Checked-in problems/**/answer.vsm files only; not a complete ISA spelling inventory.",
        "answer_files": files.len(),
        "parsed_operator_spellings": op_spellings,
        "answer_expression_shapes": answer_expression_shapes,
        "raw_operand_occurrences": raw_operands,
        "other_opcode_occurrences": other_ops,
        "parse_errors": parse_errors,
        "opcode_candidate_results": candidate_results,
        "raw_operand_fallback_probes": raw_operand_fallback_probes,
    });
    println!("{}", serde_json::to_string_pretty(&result)?);
    Ok(())
}
