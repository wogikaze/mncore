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

/// MABs of L1B n0c0b0 whose LM1 long words 0..3 (PE 0) were written by `program`.
fn written_mabs(program: &str) -> Vec<usize> {
    let mut sim = Sim::new();
    sim.run(&vsm::parse(program).unwrap()).unwrap();
    (0..4)
        .filter(|m| {
            (0..8).any(|a| {
                let key = ("LM1".into(), format!("n0c0b0m{m}p0"), a);
                sim.dump.get(&key).is_some_and(|v| *v != 0)
            })
        })
        .collect()
}

/// An expression that writes a mask register and an L1BM-to-PE transfer masked by it in the
/// same step: the transfer uses the mask register as it was before the step. `ilsr $peid`
/// leaves omr1 = 0 only in MAB 0 and T = MAB index; after two `idec`, `ipassa $aluf $omr1`
/// leaves omr1 = 0 only in MAB 2. Measured with the official emulator (SDK 0.9
/// gpfn3_package_main): the l1bmm in the same step writes MAB 0, one step later MAB 2, as does
/// a PE expression one step later. MLSDK's matmul relies on this to write one MAB per
/// iteration.
#[test]
fn l1bm_transfer_uses_mask_before_same_step_write() {
    let mut setup = String::from("mask 0\n");
    for m in 0..4 {
        setup.push_str(&format!("d set $lm0n0c0b0m{m}p0 4 {}\n", "3C00".repeat(16)));
    }
    for a in (0..256).step_by(64) {
        setup.push_str(&format!("d set $lb{a}n0c0b0 64 {}\n", "3C00".repeat(256)));
    }
    setup.push_str("imm i\"2\" $nowrite\nilsr $peid $aluf $t $omr1\nnop/8\nidec $t $t\nnop/8\nidec $t $t\n");
    let get = (0..4).map(|m| format!("d get $ln0n0c0b0m{m}p0 4\n")).collect::<String>();
    let same = |u: &str| format!("{setup}ipassa $aluf $omr1; {u}\nnop/32\n{get}");
    let next = |u: &str| format!("{setup}ipassa $aluf $omr1\n{u}\nnop/32\n{get}");
    assert_eq!(written_mabs(&same("l1bmm $lb0 $ln0v/$imr1")), vec![0]);
    assert_eq!(written_mabs(&next("l1bmm $lb0 $ln0v/$imr1")), vec![2]);
    assert_eq!(written_mabs(&next("lpassa $lm0v $ln0v/$imr1")), vec![2]);
}
