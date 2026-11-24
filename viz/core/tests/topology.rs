//! Reduced topologies (`mncore_sim::topology`, `docs/topology.md`).
//!
//! The main property: a program whose transfers stay inside units that a topology has in full
//! prints, on that topology, exactly the full chip's values that lie inside the topology.
//! It is checked on the handwritten programs in `tests/topology/` (on topologies with reduced
//! memories), and on every problem and challenge solution in `problems/` at the scope the
//! solution needs (`every_problem_cut_to_a_topology_matches_the_full_chip`, ignored by
//! default because it makes some 700 runs; `scripts/check-conformance.sh` runs it). The other
//! tests pin down what missing units and reduced capacities mean.

use std::collections::{BTreeSet, HashMap};
use std::path::{Path, PathBuf};

use mncore_sim::mv::MvKind;
use mncore_sim::run::{DumpKey, RunError, Sim};
use mncore_sim::topology::Topology;
use mncore_sim::vsm::{self, Line, Op};

const VSM_HERE: &str = "# ======= YOUR VSM WILL BE INSERTED HERE =======";

fn topo(spec: &str) -> Topology {
    Topology::parse(spec).unwrap()
}

fn parse(src: &str) -> Vec<(usize, Line)> {
    vsm::parse(src).unwrap_or_else(|e| panic!("{e}"))
}

fn run(t: Topology, lines: &[(usize, Line)]) -> Result<HashMap<DumpKey, u64>, RunError> {
    let mut sim = Sim::with_topology(t);
    sim.run(lines)?;
    Ok(sim.dump)
}

/// Differences between the full chip's values inside `t` and a reduced run's values.
fn cut_differences(t: &Topology, full: &HashMap<DumpKey, u64>, reduced: &HashMap<DumpKey, u64>) -> Vec<String> {
    let expected = t.restrict(full);
    let keys: BTreeSet<&DumpKey> = expected.keys().chain(reduced.keys()).collect();
    let show = |v: Option<&u64>| v.map(|v| format!("{v:016x}")).unwrap_or("missing".into());
    keys.into_iter()
        .filter(|k| expected.get(*k) != reduced.get(*k))
        .map(|k| format!("{} {} {}: full={} reduced={}", k.0, k.1, k.2, show(expected.get(k)), show(reduced.get(k))))
        .collect()
}

fn assert_cut(label: &str, t: &Topology, full: &HashMap<DumpKey, u64>, reduced: &HashMap<DumpKey, u64>) {
    let diffs = cut_differences(t, full, reduced);
    assert!(
        diffs.is_empty(),
        "{label} on {t}: {} differences, first:\n{}",
        diffs.len(),
        diffs.iter().take(10).cloned().collect::<Vec<_>>().join("\n")
    );
}

/// Topologies with reduced memories (the contract's initial and P3 builds of nano20k, and two
/// irregular shapes). The handwritten programs fit in all of them.
const SMALL: &[&str] = &[
    "l2b=1,l1b=1,mab=1,lm=256,grf=256,l1bm=1024,l2bm=4096",
    "l2b=1,l1b=1,mab=16,lm=256,grf=256,l1bm=1024,l2bm=4096",
    "l2b=2,l1b=2,mab=5,lm=256,grf=32,l1bm=512,l2bm=1024,pdm=4096,dram=65536",
    "l2b=3,l1b=2,mab=5,lm=1024,grf=128",
];

#[test]
fn handwritten_pe_local_programs_are_cut_from_the_full_chip() {
    for (name, src) in [
        ("coords.vsm", include_str!("topology/coords.vsm")),
        ("edge.vsm", include_str!("topology/edge.vsm")),
    ] {
        let lines = parse(src);
        let full = run(Topology::FULL, &lines).unwrap_or_else(|e| panic!("{name}: {e:?}"));
        for spec in SMALL {
            let t = topo(spec);
            let reduced = run(t, &lines).unwrap_or_else(|e| panic!("{name} on {t}: {e:?}"));
            assert!(!reduced.is_empty(), "{name} on {t} printed nothing");
            assert_cut(name, &t, &full, &reduced);
        }
    }
}

#[test]
fn reduced_pes_report_their_chip_coordinates() {
    let t = topo("l2b=3,l1b=2,mab=5");
    let lines = parse(
        "lpassa $l2bid $lr0\nlpassa $l1bid $lr2\nlpassa $mabid $lr4\nlpassa $peid $lr6\nlpassa $subpeid $lr8\nnop/2\n\
         d get $lr0n1c0b1m4p3 5\nd get $lr0n0c1b0m2p1 5\nd get $lr0n1c1b0m0p0 5\n",
    );
    let dump = run(t, &lines).unwrap();
    let get = |pe: &str, a: u32| dump.get(&("GREG0".to_string(), pe.to_string(), a)).copied();
    // The last PE of the third L2B (n1c0): L2B 2, L1B 1, MAB 4, PE 4 * 4 + 3.
    assert_eq!([0, 2, 4, 6, 8].map(|a| get("n1c0b1m4p3", a)), [2, 1, 4, 19, 3].map(Some));
    assert_eq!([0, 2, 4, 6, 8].map(|a| get("n0c1b0m2p1", a)), [1, 0, 2, 9, 1].map(Some));
    // n1c1 is the fourth L2B, which this topology does not have.
    assert_eq!(get("n1c1b0m0p0", 0), None);
    assert_eq!(dump.len(), 10);
}

/// Long word `i` of a `d get` of L1BM/L2BM/DRAM/PDM.
fn block(dump: &HashMap<DumpKey, u64>, mem: &str, unit: &str, a: u32) -> Option<u64> {
    dump.get(&(mem.to_string(), unit.to_string(), a)).copied()
}

#[test]
fn missing_mabs_send_zero_to_an_l1bm_reduction() {
    // Every PE holds its $peid (MAB * 4 + PE); the 16x1 reduction adds it over the MABs.
    let lines = parse("lpassa $peid $lr0\nnop/2\nl1bmrliadd $lr0 $lb0\nnop/3\nd get $lb0n0c0b0 4\nd get $lb0n0c0b1 4\n");
    let full = run(Topology::FULL, &lines).unwrap();
    let t = topo("l2b=1,l1b=2,mab=2");
    let reduced = run(t, &lines).unwrap();
    for pe in 0..4u64 {
        // Full chip: sum over 16 MABs of 4m + pe. Two MABs: 4 * (0 + 1) + 2 pe.
        assert_eq!(block(&full, "L1BM", "n0c0b0", pe as u32), Some(480 + 16 * pe));
        assert_eq!(block(&reduced, "L1BM", "n0c0b0", pe as u32), Some(4 + 2 * pe));
        assert_eq!(block(&reduced, "L1BM", "n0c0b1", pe as u32), Some(4 + 2 * pe));
    }
}

#[test]
fn missing_l1bs_send_zero_and_receive_nothing() {
    let lines = parse(
        "d set $lb0n0c0b0 1 BFF0000000000000\n\
         d set $lb0n0c0b1 1 C000000000000000\n\
         d set $lc64n0c0 1 0123456789ABCDEF\n\
         l2bmrdmax $lb0 $lc0\n\
         l2bmd $lb0 $lc256\n\
         l2bm@5 $lb0 $lc512\n\
         nop/4\n\
         l2bmb $lc64 $lb64\n\
         nop/4\n\
         d get $lc0n0c0 1\nd get $lc256n0c0 24\nd get $lc512n0c0 1\nd get $lb64n0c0b0 1\nd get $lb64n0c0b1 1\n",
    );
    let t = topo("l2b=1,l1b=2,mab=1");
    let dump = run(t, &lines).unwrap();
    // A maximum over L1Bs 0 (-1.0), 1 (-2.0) and six missing ones (zero) is +0.0, not -1.0.
    assert_eq!(block(&dump, "L2BM", "n0c0", 0), Some(0));
    // l2bmd gathers 8 long words per L1B and cycle; L1B 2 is missing.
    assert_eq!(block(&dump, "L2BM", "n0c0", 256), Some(0xBFF0_0000_0000_0000));
    assert_eq!(block(&dump, "L2BM", "n0c0", 264), Some(0xC000_0000_0000_0000));
    assert_eq!(block(&dump, "L2BM", "n0c0", 272), Some(0));
    // l2bm@5 copies from L1B 5, which is missing.
    assert_eq!(block(&dump, "L2BM", "n0c0", 512), Some(0));
    // l2bmb broadcasts to every L1B of the set; only the two that exist receive it.
    assert_eq!(block(&dump, "L1BM", "n0c0b0", 64), Some(0x0123_4567_89AB_CDEF));
    assert_eq!(block(&dump, "L1BM", "n0c0b1", 64), Some(0x0123_4567_89AB_CDEF));
    assert_eq!(dump.keys().filter(|k| k.0 == "L1BM").count(), 2);
}

#[test]
fn missing_l2bs_and_groups_in_mv_transfers() {
    let lines = parse(
        "d set $lc0n0c0 2 00000000000000110000000000000022\n\
         mvp/n64 $lc0@0.0 $d0@0\n\
         mvp/n64 $lc0@0.0 $d0@1\n\
         mvp/n64 $lc0@0.1 $d64@0\n\
         mvp/n64 $lc0@0.0 $lc128@0.1\n\
         mvrliadd/n64 $lc0 $p0@0\n\
         d get $d0n0 2\nd get $d64n0 1\nd get $d0n1 1\nd get $p0n0 2\nd get $lc128 1\n",
    );
    let t = topo("l2b=1");
    let dump = run(t, &lines).unwrap();
    assert_eq!(block(&dump, "DRAM", "n0", 0), Some(0x11));
    assert_eq!(block(&dump, "DRAM", "n0", 1), Some(0x22));
    // L2B n0c1 does not exist: it reads as zero and drops what it is sent.
    assert_eq!(block(&dump, "DRAM", "n0", 64), Some(0));
    // Group 1 has no L2B, so it has no DRAM: nothing is printed for it.
    assert_eq!(block(&dump, "DRAM", "n1", 0), None);
    // The reduction over the 8 L2BMs gets zero from the 7 missing ones.
    assert_eq!(block(&dump, "PIU", "n0", 0), Some(0x11));
    assert_eq!(block(&dump, "PIU", "n0", 1), Some(0x22));
    assert_eq!(dump.keys().filter(|k| k.0 == "L2BM").count(), 1);
    assert_eq!(block(&dump, "L2BM", "n0c0", 128), Some(0));
}

/// Runs `body` after `prefix` on the contract's initial topology with a GRF of 128 long words
/// and small PDM/DRAM, expecting E_RANGE at instruction word `word` with `what` in the message.
fn expect_range(prefix: &str, body: &str, word: u64, what: &str) {
    let t = topo("l2b=1,l1b=1,mab=1,lm=256,grf=128,l1bm=1024,l2bm=4096,pdm=4096,dram=65536");
    let src = format!("{prefix}{body}");
    let lines = parse(&src);
    let err = run(t, &lines).expect_err(&format!("`{body}` must stop"));
    assert!(err.is_range(), "`{body}`: {err:?}");
    assert!(err.msg.contains(what), "`{body}`: {}", err.msg);
    assert_eq!(err.word, word, "`{body}`: {err:?}");
    // The same program never stops on the full chip.
    run(Topology::FULL, &lines).unwrap_or_else(|e| panic!("`{body}` on the full chip: {e:?}"));
}

#[test]
fn accesses_beyond_a_reduced_capacity_stop_with_e_range() {
    let two = "nop\nimm i\"1\" $lr0\n";
    // PE memories: reads, writes, base address register and T-indirect addresses.
    expect_range(two, "lpassa $lm512 $ln0\n", 2, "LM0 n0c0b0m0p0 word address 512");
    expect_range(two, "lpassa $lr0 $ln510v\n", 2, "LM1 n0c0b0m0p0 word address 512");
    expect_range(two, "lpassa $lr256 $ln0\n", 2, "GRF0 n0c0b0m0p0 word address 256");
    expect_range(two, "imm i\"600\" $mb\nnop/2\nlpassa $m0 $ln0\n", 5, "LM0 n0c0b0m0p0 word address 600");
    expect_range(two, "imm i\"508\" $t\nnop/2\nlpassa $lmt0v $ln0\n", 5, "LM0 n0c0b0m0p0 word address 512");
    // Masked-off writes are checked too.
    expect_range(two, "lpassa $lr0 $ln600/0000\n", 2, "LM1 n0c0b0m0p0 word address 600");
    // L1BM, L2BM, PDM and DRAM.
    expect_range(two, "l1bmd $lb1024 $ln0\n", 2, "L1BM n0c0b0 long word address 1024");
    expect_range(two, "l1bmrliadd $lr0 $lb1020\n", 2, "L1BM n0c0b0 long word address 1024");
    expect_range(two, "l2bmb $lc4096 $lb0\n", 2, "L2BM n0c0 long word address 4096");
    expect_range(two, "mvp/n64 $lc0@0.0 $d65472@0\nmvp/n64 $lc0@0.0 $d65536@0\n", 3, "DRAM n0 long word address 65536");
    expect_range(two, "mvp/n64 $p4032@0 $lc0@0.0\nmvp/n64 $p4096@0 $lc0@0.0\n", 3, "PDM n0 long word address 4096");
    // Debug and DRAM initialization statements.
    expect_range(two, "d set $lm512n0c0b0m0p0 1 0000000000000001\n", 2, "LM0 n0c0b0m0p0 word address 512");
    expect_range(two, "d get $lm510n0c0b0m0p0 2\n", 2, "LM0 n0c0b0m0p0 word address 512");
    expect_range(two, "d get $lb1023n0c0b0 2\n", 2, "L1BM n0c0b0 long word address 1024");
    expect_range(two, "r 0 10000 1 0000000000000001\n", 2, "DRAM n0 long word address 65536");
}

#[test]
fn e_range_names_the_first_pe_in_chip_order() {
    // Every PE fails; the fast path runs them in parallel, but the report is deterministic.
    let t = topo("l2b=2,l1b=2,mab=4,lm=16");
    let lines = parse("lpassa $lr0 $ln40\n");
    for _ in 0..20 {
        let err = run(t, &lines).unwrap_err();
        assert!(err.msg.contains("LM1 n0c0b0m0p0 word address 40"), "{}", err.msg);
    }
    // Here only the PEs of L2B n0c1 fail: their base address register is 2 * $l2bid = 2, and
    // LM0 has one long word (words 0 and 1).
    let lines = parse("ipackbit $l2bid $ls0 $mb\nnop/2\nlpassa $m0 $ln0\n");
    let err = run(topo("l2b=2,l1b=1,mab=1,lm=1"), &lines).unwrap_err();
    assert_eq!(err.word, 3);
    assert!(err.msg.contains("LM0 n0c1b0m0p0 word address 2"), "{}", err.msg);
}

#[test]
fn tracing_works_on_a_reduced_topology() {
    let t = topo("l2b=1,l1b=2,mab=2");
    let solution = "lpassa $peid $lr0\nnop/2\nl1bmrliadd $lr0 $lb0\nnop/3\nl1bmd $lb0 $ln0\n";
    let trace = mncore_sim::api::trace_in("", solution, &[12, 13, 14, 15], t).unwrap();
    assert_eq!(trace.error, None);
    // The last MAB of the second L1B: its accesses are recorded, and the L1BM flows count
    // the 16 PEs of the topology.
    assert!(trace.lines[0].accesses.iter().any(|a| a.unit == 15 && a.write));
    let reduce = &trace.lines[2].flows[0];
    assert_eq!((reduce.from, reduce.to, reduce.longs), ("pe", "l1bm", 16 * 4));
}

// ---- every problem ----------------------------------------------------------------------

/// How far a program moves data: inside a MAB, an L1B, an L2B, or across the chip.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Scope {
    Mab,
    L1b,
    L2b,
    Chip,
}

fn scope(lines: &[(usize, Line)]) -> Scope {
    let mut s = Scope::Mab;
    for (_, l) in lines {
        match l {
            Line::Mv(mv) if mv.kind != MvKind::Nop => return Scope::Chip,
            Line::Pe(exprs) => {
                for e in exprs {
                    match e.op {
                        Op::L1(_) => s = s.max(Scope::L1b),
                        Op::L2(_) => s = s.max(Scope::L2b),
                        _ => {}
                    }
                }
            }
            _ => {}
        }
    }
    s
}

/// Whether `t` has in full every unit inside which a program of scope `s` moves data.
fn exact_for(t: &Topology, s: Scope) -> bool {
    match s {
        Scope::Mab => true,
        Scope::L1b => t.mab == 16,
        Scope::L2b => t.mab == 16 && t.l1b == 8,
        Scope::Chip => false,
    }
}

/// Topologies of the problem sweep. Only units are reduced, because the testcases use most of
/// LM; the last one is the contract's initial build, on which many problems stop with E_RANGE.
const SWEEP: &[&str] = &[
    "l2b=1,l1b=1,mab=1",
    "l2b=3,l1b=2,mab=5",
    "l2b=1,l1b=1,mab=16",
    "l2b=2,l1b=3,mab=16",
    "l2b=1,l1b=8,mab=16",
    "l2b=3,l1b=8,mab=16",
    "l2b=1,l1b=1,mab=1,lm=256,grf=256,l1bm=1024,l2bm=4096",
];

fn problems_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../problems")
}

/// Every problem directory with a testcase, and its solutions (main.vsm, answer.vsm).
fn problem_cases(root: &Path) -> Vec<(String, PathBuf, PathBuf)> {
    let mut dirs: Vec<PathBuf> = Vec::new();
    for top in [root.to_path_buf(), root.join("challenge")] {
        let Ok(entries) = std::fs::read_dir(&top) else { continue };
        for entry in entries.flatten() {
            let path = entry.path();
            if path.is_dir() && path.join("testcase.vsm").is_file() {
                dirs.push(path);
            }
        }
    }
    dirs.sort();
    let mut out = Vec::new();
    for dir in dirs {
        for solution in ["main.vsm", "answer.vsm"] {
            let path = dir.join(solution);
            if path.is_file() {
                out.push((format!("{}/{solution}", dir.file_name().unwrap().to_string_lossy()), dir.clone(), path));
            }
        }
    }
    out
}

/// What a reduced run of a solution gave.
enum Outcome {
    /// Exactly the full chip's values inside the topology.
    Equal,
    /// E_RANGE on a topology with reduced memories: the solution and the message.
    Range(String),
    Failed(String),
}

/// Runs one case on the full chip and on each sweep topology it is exact for. Cases the
/// simulator cannot parse or run on the full chip are left to problem_conformance.
fn sweep_case(label: &str, dir: &Path, solution: &Path) -> Vec<(&'static str, Outcome)> {
    let mut out = Vec::new();
    let testcase = std::fs::read_to_string(dir.join("testcase.vsm")).unwrap();
    let (prefix, suffix) = testcase.split_once(VSM_HERE).unwrap_or(("", &testcase));
    let main = std::fs::read_to_string(solution).unwrap();
    let Ok(main_lines) = vsm::parse(&main) else { return out };
    let s = scope(&main_lines);
    let Ok(lines) = vsm::parse(&format!("{prefix}{main}\n{suffix}")) else { return out };
    let Ok(full) = run(Topology::FULL, &lines) else { return out };
    assert_eq!(Topology::FULL.restrict(&full), full, "{label}");
    for spec in SWEEP {
        let t = topo(spec);
        if !exact_for(&t, s) {
            continue;
        }
        let outcome = match run(t, &lines) {
            Ok(reduced) => {
                let diffs = cut_differences(&t, &full, &reduced);
                if diffs.is_empty() {
                    Outcome::Equal
                } else {
                    Outcome::Failed(format!("{label} ({s:?}) on {spec}: {} differences, first {}", diffs.len(), diffs[0]))
                }
            }
            Err(e) if e.is_range() && spec.contains("lm=") => Outcome::Range(format!("{label}: {}", e.msg)),
            Err(e) => Outcome::Failed(format!("{label} ({s:?}) on {spec}: {e:?}")),
        };
        out.push((*spec, outcome));
    }
    out
}

/// Per sweep topology: (topology, equal runs, E_RANGE stops as "solution: message").
type Counts = Vec<(&'static str, usize, Vec<String>)>;

/// Runs the cases on a few threads. Returns the counts per sweep topology and the failures.
fn sweep(cases: &[(String, PathBuf, PathBuf)]) -> (Counts, Vec<String>) {
    use std::sync::atomic::{AtomicUsize, Ordering};
    use std::sync::Mutex;
    let next = AtomicUsize::new(0);
    let results: Mutex<Vec<(&'static str, Outcome)>> = Mutex::new(Vec::new());
    let workers = std::thread::available_parallelism().map(|n| n.get()).unwrap_or(1).clamp(1, 4);
    std::thread::scope(|s| {
        for _ in 0..workers {
            s.spawn(|| loop {
                let i = next.fetch_add(1, Ordering::Relaxed);
                let Some((label, dir, solution)) = cases.get(i) else { break };
                let r = sweep_case(label, dir, solution);
                results.lock().unwrap().extend(r);
            });
        }
    });
    let results = results.into_inner().unwrap();
    let counts = SWEEP
        .iter()
        .map(|spec| {
            let mine = || results.iter().filter(|(s, _)| s == spec).map(|(_, o)| o);
            let equal = mine().filter(|o| matches!(o, Outcome::Equal)).count();
            let mut range: Vec<String> = mine()
                .filter_map(|o| match o {
                    Outcome::Range(m) => Some(m.clone()),
                    _ => None,
                })
                .collect();
            range.sort();
            (*spec, equal, range)
        })
        .collect();
    let mut failures: Vec<String> = results
        .into_iter()
        .filter_map(|(_, o)| match o {
            Outcome::Failed(m) => Some(m),
            _ => None,
        })
        .collect();
    failures.sort();
    (counts, failures)
}

#[test]
fn representative_problems_cut_to_a_topology_match_the_full_chip() {
    let root = problems_root();
    let wanted = ["2.fmul7", "11.maxrow", "32.matmul-trb-mab-lm-4-8-8", "challenge/12.convert-endian", "challenge/14.mat-sq", "challenge/17.transpose-mab"];
    let cases: Vec<_> = problem_cases(&root)
        .into_iter()
        .filter(|(_, dir, _)| wanted.iter().any(|w| dir.ends_with(w)))
        .collect();
    if cases.is_empty() {
        eprintln!("skipping: no problems in {}", root.display());
        return;
    }
    let (counts, failures) = sweep(&cases);
    assert!(failures.is_empty(), "{}", failures.join("\n"));
    let compared: usize = counts.iter().map(|c| c.1).sum();
    assert!(compared >= 2 * wanted.len(), "only {compared} reduced runs were compared");
}

#[test]
#[ignore = "slow: runs every problem on the full chip and on several topologies"]
fn every_problem_cut_to_a_topology_matches_the_full_chip() {
    let cases = problem_cases(&problems_root());
    assert!(!cases.is_empty(), "no problems found");
    let (counts, failures) = sweep(&cases);
    println!("{} solutions; reduced runs equal to the full chip cut to the topology (E_RANGE stops):", cases.len());
    for (spec, equal, range) in &counts {
        println!("  {spec}: {equal} ({})", range.len());
        for r in range {
            println!("    E_RANGE {r}");
        }
    }
    assert!(failures.is_empty(), "{} failures:\n{}", failures.len(), failures.join("\n"));
    let compared: usize = counts.iter().map(|c| c.1).sum();
    assert!(compared > 100, "only {compared} reduced runs were compared");
}

// ---- against the official emulator ------------------------------------------------------

#[test]
fn handwritten_programs_match_the_official_emulator_cut_to_each_topology() {
    if !mncore_sim::emu::available() {
        eprintln!("skipping: the official emulator is not installed (run setup_judge.sh, or set MNCORE_EMU_DIR)");
        return;
    }
    for (name, src) in [
        ("coords.vsm", include_str!("topology/coords.vsm")),
        ("edge.vsm", include_str!("topology/edge.vsm")),
    ] {
        let asm = mncore_sim::emu::assemble(src).unwrap_or_else(|e| panic!("{name}: {e}"));
        let kept: String = asm
            .lines()
            .filter(|l| l.starts_with('j') || l.starts_with('m') || l.starts_with('d') || l.starts_with("r "))
            .map(|l| format!("{l}\n"))
            .collect();
        let official = mncore_sim::emu::parse_dump(&mncore_sim::emu::run_asm(&kept).unwrap_or_else(|e| panic!("{name}: {e}")));
        let lines = parse(src);
        assert_cut(name, &Topology::FULL, &official, &run(Topology::FULL, &lines).unwrap());
        for spec in SMALL {
            let t = topo(spec);
            assert_cut(name, &t, &official, &run(t, &lines).unwrap());
        }
    }
}
