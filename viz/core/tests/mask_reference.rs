//! Replays every mask fixture whose expected values were compared with the official emulator.
use mncore_sim::{run::Sim, vsm};
use std::fmt::Write;

#[test]
fn all_mask_fixtures_match_local_simulator() {
    let fixture = include_str!("../../../proofs_lean/evidence/masks/vectors.tsv");
    let rows: Vec<Vec<&str>> = fixture
        .lines()
        .map(|line| line.split('\t').collect())
        .collect();
    assert_eq!(rows.len(), 768);
    let mut sim = Sim::new();
    for group in rows.chunks_exact(4) {
        let width = group[0][1];
        let mode = group[0][2];
        let mut mask_payload = String::new();
        let mut data_payload = String::new();
        let mut old_payload = String::new();
        for row in group {
            assert_eq!(row.len(), 15);
            let flags: u64 = row[5].parse().unwrap();
            let input: u64 = (0..4)
                .map(|bit| {
                    if flags & (1 << bit) == 0 {
                        1 << (16 * bit)
                    } else {
                        0
                    }
                })
                .sum();
            write!(mask_payload, "{input:016X}DEADBEEFCAFEBABE").unwrap();
            write!(
                data_payload,
                "{:016X}{:016X}",
                row[6].parse::<u64>().unwrap(),
                row[7].parse::<u64>().unwrap()
            )
            .unwrap();
            write!(
                old_payload,
                "{:016X}{:016X}",
                row[8].parse::<u64>().unwrap(),
                row[9].parse::<u64>().unwrap()
            )
            .unwrap();
        }
        let selector = if width == "l" { "$imr1" } else { "$llimr1" };
        let opcode = if matches!(mode, "flush" | "both") {
            format!("spassa/{selector}")
        } else {
            "spassa".into()
        };
        let destination = if matches!(mode, "write" | "both") {
            format!("$lls64v/{selector}{}", if width == "l" { "p" } else { "" })
        } else {
            "$lls64v".into()
        };
        let flags_destination = if matches!(mode, "register" | "override") {
            format!("$omr2/{selector}")
        } else {
            "$omr2".into()
        };
        let directive = match mode {
            "directive" => format!("mask{width}s 1\n"),
            "override" => "masklls 16\n".into(),
            _ => String::new(),
        };
        let program = format!(
            "mask 0\nd set $lr0n0c0b0m0p0 8 {mask_payload}\n\
             d set $lr32n0c0b0m0p0 8 {data_payload}\n\
             d set $ls64n0c0b0m0p0 8 {old_payload}\n\
             d set $ls0n0c0b0m0p0 2 00000000000000000000000000000000\n\
             spassa $llr0v $omr1\nspassa $lls0 $omr2\n\
             {directive}{opcode} $llr32v {destination} {flags_destination}\n\
             nop/2\nmask 0\nd get $ls64n0c0b0m0p0 8\nd get $omr2n0c0b0m0p0 1\n"
        );
        sim.run(&vsm::parse(&program).unwrap()).unwrap();
        for (cycle, row) in group.iter().enumerate() {
            for (addr, field) in [(64 + 4 * cycle, 10), (66 + 4 * cycle, 11)] {
                let key = ("GREG1".into(), "n0c0b0m0p0".into(), addr as u32);
                assert_eq!(
                    sim.dump.get(&key),
                    Some(&row[field].parse::<u64>().unwrap()),
                    "case {} cycle {cycle} addr {addr}",
                    row[0]
                );
            }
            let key = ("OMR".into(), "n0c0b0m0p0".into(), (8 + cycle) as u32);
            assert_eq!(
                sim.dump.get(&key),
                Some(&row[12].parse::<u64>().unwrap()),
                "case {} cycle {cycle} flags",
                row[0]
            );
        }
    }
}
