//! Guards the CPU simulator against the official emulator on every problem.
//!
//! `difftest_prog` runs a problem's `testcase.vsm` + solution through the official
//! emulator and through `mncore_sim::Sim` and compares a large state dump. A
//! mismatch here means the simulator and the reference disagree, which is the
//! failure this test exists to catch: it must never be accepted.
//!
//! The full sweep is slow (roughly two seconds per case because the emulator
//! starts per case), so it is `#[ignore]`d and run by
//! `viz/core/scripts/check-conformance.sh` and by CI. A representative subset
//! runs by default, so a regression is caught by an ordinary `cargo test`.

use std::path::{Path, PathBuf};
use std::process::Command;

fn problems_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../problems")
}

/// Problems that exercise the instruction families most likely to drift. Kept
/// small so `cargo test` stays fast; the full list is `all_cases`.
const REPRESENTATIVE: &[&str] = &[
    "2.fmul7",
    "12.divrow-vec",
    "23.dram-dl-256-1024",
    "challenge/1.plus-one",
    "challenge/10.gather-easy",
    "challenge/16.count-up",
];

/// Every `(label, problem dir, solution)` worth comparing: the problems under
/// `problems/` and every solution shipped with a challenge problem.
fn all_cases(root: &Path) -> Vec<(String, PathBuf, PathBuf)> {
    let mut out = Vec::new();
    let mut dirs: Vec<PathBuf> = Vec::new();
    for top in [root.to_path_buf(), root.join("challenge")] {
        let Ok(entries) = std::fs::read_dir(&top) else {
            continue;
        };
        for entry in entries.flatten() {
            let path = entry.path();
            if path.is_dir() && path.join("testcase.vsm").is_file() {
                dirs.push(path);
            }
        }
    }
    dirs.sort();
    for dir in dirs {
        for solution in ["main.vsm", "answer.vsm"] {
            let path = dir.join(solution);
            if path.is_file() {
                let label = format!(
                    "{}/{}",
                    dir.file_name().unwrap().to_string_lossy(),
                    solution
                );
                out.push((label, dir.clone(), path));
            }
        }
    }
    out
}

/// Runs one case and returns `None` on success, or a description of the failure.
fn run_case(bin: &str, dir: &Path, solution: &Path) -> Option<String> {
    let output = Command::new(bin)
        .arg(dir)
        .arg(solution)
        .output()
        .unwrap_or_else(|e| panic!("could not run {bin}: {e}"));
    if output.status.success() {
        return None;
    }
    let text = format!(
        "{}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    // Keep the diff visible but bounded.
    let tail: Vec<&str> = text.lines().rev().take(6).collect();
    Some(tail.into_iter().rev().collect::<Vec<_>>().join("\n"))
}

fn check(cases: &[(String, PathBuf, PathBuf)]) {
    if !mncore_sim::emu::available() {
        eprintln!(
            "skipping problem conformance: the official emulator is not installed \
             (run setup_judge.sh, or set MNCORE_EMU_DIR)"
        );
        return;
    }
    assert!(!cases.is_empty(), "no problem cases found; check the problems/ layout");
    let bin = env!("CARGO_BIN_EXE_difftest_prog");
    let mut failures = Vec::new();
    for (label, dir, solution) in cases {
        if let Some(detail) = run_case(bin, dir, solution) {
            failures.push(format!("{label}\n{detail}"));
        }
    }
    assert!(
        failures.is_empty(),
        "{} of {} cases disagree with the official emulator:\n\n{}",
        failures.len(),
        cases.len(),
        failures.join("\n\n")
    );
}

#[test]
fn representative_problems_match_the_official_emulator() {
    let root = problems_root();
    let cases: Vec<(String, PathBuf, PathBuf)> = REPRESENTATIVE
        .iter()
        .map(|name| {
            let dir = root.join(name);
            assert!(
                dir.join("testcase.vsm").is_file(),
                "representative problem {name} is missing; update REPRESENTATIVE"
            );
            (
                (*name).to_string(),
                dir.clone(),
                dir.join("main.vsm"),
            )
        })
        .collect();
    check(&cases);
}

#[test]
#[ignore = "slow: starts the official emulator for every problem"]
fn every_problem_matches_the_official_emulator() {
    check(&all_cases(&problems_root()));
}
