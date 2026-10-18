//! Small deterministic oracle for the matrix block-float dot/FMA arithmetic.
//! Input rows are tab separated: input format, output format, kept bits,
//! accumulator format, accumulator bits, left lanes, right lanes.

use mncore_sim::float::{
    self, BF_DOUBLE, BF_HALF, BF_PSEUDO, BF_SINGLE, BfFmt, DOUBLE, Fmt, HALF, SINGLE,
};
use std::io::{self, BufRead};

fn parse_values(field: &str) -> Vec<u64> {
    field
        .split(',')
        .map(|value| value.parse().expect("invalid lane value"))
        .collect()
}

fn format(code: &str) -> Fmt {
    match code {
        "d" => DOUBLE,
        "f" | "g" | "s" => SINGLE,
        "h" => HALF,
        _ => panic!("unknown float format {code}"),
    }
}

fn block_format(code: &str, kept: u32) -> BfFmt {
    let mut result = match code {
        "d" => BF_DOUBLE,
        "f" => BF_SINGLE,
        "g" => BF_PSEUDO,
        "h" => BF_HALF,
        _ => panic!("unknown block format {code}"),
    };
    result.m = kept;
    result
}

fn main() {
    for row in io::stdin().lock().lines() {
        let row = row.expect("failed reading vector");
        if row.is_empty() {
            continue;
        }
        let fields: Vec<_> = row.split('\t').collect();
        assert_eq!(fields.len(), 7, "expected seven fields");
        let kept: u32 = fields[2].parse().expect("invalid kept bits");
        let accumulator = fields[4].parse().expect("invalid accumulator bits");
        let left = parse_values(fields[5]);
        let right = parse_values(fields[6]);
        assert_eq!(left.len(), right.len(), "dot lane counts differ");
        let dot = float::bf_dot(block_format(fields[0], kept), &left, &right);
        let result = float::mat_fma(
            format(fields[1]),
            dot,
            float::decode(format(fields[3]), accumulator),
        );
        println!("{result}");
    }
}
