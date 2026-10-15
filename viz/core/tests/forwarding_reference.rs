//! Only resolved official observations are executable expectations.
//! Five L1-to-PE assembler-rejection cases remain explicitly unresolved.
use mncore_sim::{run::Sim, vsm};
use std::path::PathBuf;

#[test]
fn forwarding_values_errors_and_flags_match_resolved_official_cases() {
    let directory =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../proofs_lean/evidence/forwarding");
    let report: serde_json::Value =
        serde_json::from_str(&std::fs::read_to_string(directory.join("reference.json")).unwrap())
            .unwrap();
    let vectors = std::fs::read_to_string(directory.join("vectors.tsv")).unwrap();
    let lines: Vec<Vec<&str>> = vectors
        .lines()
        .map(|line| line.split('\t').collect())
        .collect();
    let mut resolved = 0;
    let mut unresolved = 0;
    for (index, record) in report["records"].as_array().unwrap().iter().enumerate() {
        if record["unresolved"].as_bool().unwrap() {
            assert_eq!(record["expected"], "unknown");
            assert_eq!(record["matched"], false);
            unresolved += 1;
            continue;
        }
        let text =
            std::fs::read_to_string(directory.join(record["program"].as_str().unwrap())).unwrap();
        let mut sim = Sim::new();
        let result = sim.run(&vsm::parse(&text).unwrap());
        if record["expected"] == "failure" {
            assert!(
                result.unwrap_err().msg.contains("forwarding register"),
                "case {index}"
            );
        } else {
            result.unwrap_or_else(|error| panic!("case {index}: {error:?}"));
            if record["values_checked"].as_bool().unwrap() {
                if record["scenario"]
                    .as_str()
                    .unwrap()
                    .starts_with("disabled-register")
                {
                    for cycle in 0..4 {
                        assert_eq!(
                            sim.dump[&("OMR".into(), "n0c0b0m0p0".into(), 4 + cycle)],
                            0,
                            "case {index}"
                        );
                    }
                } else {
                    let high: u64 = lines[index][3].parse().unwrap();
                    let low: u64 = lines[index][4].parse().unwrap();
                    for offset in 0..8 {
                        assert_eq!(
                            sim.dump[&("GREG1".into(), "n0c0b0m0p0".into(), 64 + 2 * offset)],
                            if offset % 2 == 0 { high } else { low },
                            "case {index}"
                        );
                    }
                }
            }
        }
        resolved += 1;
    }
    assert_eq!((resolved, unresolved), (37, 5));
}
