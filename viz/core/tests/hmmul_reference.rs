//! Half matrix products with extended block-float elements against outputs of the official
//! emulator.
//!
//! `hmmul_reference.tsv` holds 600 `hmfma` outputs (single, with a single-precision y) and 600
//! `hmmulr` outputs (half), each from a row and a vector of 16 half block-float elements that
//! contain extended elements (exponent field 0). They were produced by
//! `research/experiments/hmmul-rounding/hmmul_diff.py` with the challenge emulator; the SDK 0.9
//! emulator gives the same outputs. They cover the rounding of extended products before the sum
//! (`float::ext_product_round_up`) and the alignment of y to the half adder grid.

use mncore_sim::float::{self, Val, BF_HALF, HALF, SINGLE};

fn parse_list(field: &str) -> Vec<u64> {
    field.split(',').map(|v| u64::from_str_radix(v, 16).unwrap()).collect()
}

#[test]
fn half_matrix_products_match_the_official_emulator() {
    let fixture = include_str!("hmmul_reference.tsv");
    let mut checked = 0;
    let mut bad = Vec::new();
    for line in fixture.lines().filter(|l| !l.starts_with('#')) {
        let f: Vec<&str> = line.split('\t').collect();
        let (op, row, vec) = (f[0], parse_list(f[1]), parse_list(f[2]));
        let y = u64::from_str_radix(f[3], 16).unwrap();
        let expect = u64::from_str_radix(f[4], 16).unwrap();
        let dot = float::bf_dot(BF_HALF, &row, &vec);
        let got = match op {
            "hmfma" => float::mat_fma(SINGLE, dot, float::decode(SINGLE, y)),
            "hmmulr" => float::mat_fma(HALF, dot, Val::Zero { neg: false }),
            _ => panic!("unknown op {op}"),
        };
        checked += 1;
        if got != expect {
            bad.push(format!("{op} row {} vec {} y {y:08x}: emulator {expect:x}, sim {got:x}", f[1], f[2]));
        }
    }
    assert_eq!(checked, 1200);
    assert!(bad.is_empty(), "{} of {checked} differ, first: {}", bad.len(), bad[0]);
}
