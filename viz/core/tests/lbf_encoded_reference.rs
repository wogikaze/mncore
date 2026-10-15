//! These fixtures compare unchanged encoded fragments with the emulator.
//! They do not assert that all corresponding whole VSM sources assemble.
use mncore_sim::{run::Sim, vsm};
use std::path::PathBuf;

#[test]
fn lbf_retention_and_replacement_match_encoded_stream_observations() {
    let directory =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../proofs_lean/evidence/lbf-encoded");
    let report: serde_json::Value =
        serde_json::from_str(&std::fs::read_to_string(directory.join("reference.json")).unwrap())
            .unwrap();
    let vectors = std::fs::read_to_string(directory.join("vectors.tsv")).unwrap();
    let expected: Vec<Vec<&str>> = vectors
        .lines()
        .map(|line| line.split('\t').collect())
        .collect();
    let records = report["records"].as_array().unwrap();
    assert_eq!(records.len(), 11);
    let mut rejected_vsm_sources = 0;
    let mut sim = Sim::new();
    for (index, record) in records.iter().enumerate() {
        assert_eq!(record["matched"], true);
        assert_eq!(record["full_prefix_words_identical"], true);
        if record["full_vsm_accepted"] == false {
            rejected_vsm_sources += 1;
        }
        let source = std::fs::read_to_string(
            directory
                .join(record["directory"].as_str().unwrap())
                .join("intended.vsm"),
        )
        .unwrap();
        sim.run(&vsm::parse(&source).unwrap())
            .unwrap_or_else(|error| panic!("case {index}: {error:?}"));
        if record["values_checked"].as_bool().unwrap() {
            let high: u64 = expected[index][3].parse().unwrap();
            let low: u64 = expected[index][4].parse().unwrap();
            for offset in 0..8 {
                assert_eq!(
                    sim.dump[&("GREG1".into(), "n0c0b0m0p0".into(), 64 + 2 * offset)],
                    if offset % 2 == 0 { high } else { low },
                    "case {index}"
                );
            }
        }
    }
    assert_eq!(rejected_vsm_sources, 8);
    assert_eq!(report["whole_vsm_legality_proven"], false);
    assert_eq!(report["decoder_correspondence_proven"], false);
}
