//! Runs a problem's solution with the official emulator and with the simulator, and compares
//! the outputs and the final PE state.
//!
//! Usage: difftest_prog <problem dir> [solution.vsm]
//!
//! The emulator gets what the judge builds (testcase prefix + assembled solution + suffix), plus
//! `d get` lines that dump LM0/LM1/GRF0/GRF1/T of a few PEs at the end.

use mncore_sim::{emu, run::Sim, vsm};

const VSM_HERE: &str = "# ======= YOUR VSM WILL BE INSERTED HERE =======";

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let dir = std::path::PathBuf::from(args.get(1).expect("usage: difftest_prog <problem dir> [solution]"));
    let sol = args.get(2).map(std::path::PathBuf::from).unwrap_or_else(|| dir.join("main.vsm"));
    let testcase = std::fs::read_to_string(dir.join("testcase.vsm")).expect("testcase.vsm");
    let main_vsm = std::fs::read_to_string(&sol).expect("solution");
    let (prefix, suffix) = testcase.split_once(&format!("{VSM_HERE}\n")).expect("VSM_HERE marker");

    let mut probe = String::new();
    for pe in ["n0c0b0m0p0", "n0c0b0m0p3", "n1c1b5m9p2", "n3c1b7m15p3"] {
        for mem in ["lm0", "ln0", "lr0", "ls0"] {
            let n = if mem == "lr0" || mem == "ls0" { 256 } else { 2048 };
            probe += &format!("d get ${mem}{pe} {n}\n");
        }
        probe += &format!("d get $llt{pe} 4\n");
    }
    for l1 in ["n0c0b0", "n2c1b5"] {
        probe += &format!("d get $lb0{l1} 8192\n");
    }
    probe += "d get $lc0n0c0 32768\n";

    let main_asm = match emu::assemble(&main_vsm) {
        Ok(a) => a,
        Err(e) => {
            println!("SKIP: solution does not assemble\n{e}");
            std::process::exit(3);
        }
    };
    let main_asm: String = main_asm.lines().filter(|l| l.starts_with('j') || l.starts_with('m')).map(|l| format!("{l}\n")).collect();
    let words_official = main_asm.lines().count() as u64;
    let asm = format!("{prefix}{main_asm}{probe}{suffix}");
    let dump = emu::run_asm(&asm).unwrap_or_else(|e| panic!("{e}"));
    let expect = emu::parse_dump(&dump);

    let src = format!("{prefix}{main_vsm}\n{probe}{suffix}");
    let lines = vsm::parse(&src).unwrap_or_else(|e| panic!("parse: {e}"));
    let main_lines = vsm::parse(&main_vsm).unwrap();
    let words_sim: u64 = main_lines.iter().map(|(_, l)| l.words() as u64).sum();
    let mut sim = Sim::new();
    if let Err(e) = sim.run(&lines) {
        let text = src.lines().nth(e.line - 1).unwrap_or("");
        println!("UNSUPPORTED at line {}: {}\n  {}", e.line, e.msg, text);
        std::process::exit(2);
    }

    let mut bad = 0;
    let mut keys: Vec<_> = expect.keys().collect();
    keys.sort();
    for k in keys {
        let e = expect[k];
        match sim.dump.get(k) {
            Some(&a) if a == e => {}
            got => {
                bad += 1;
                if bad <= 20 {
                    println!("MISMATCH {} {} {}: emu={e:016x} sim={}", k.0, k.1, k.2, got.map(|v| format!("{v:016x}")).unwrap_or("missing".into()));
                }
            }
        }
    }
    println!(
        "{}: {} values, {} mismatches, score emu={} sim={}",
        dir.display(),
        expect.len(),
        bad,
        words_official,
        words_sim
    );
    if bad > 0 || words_official != words_sim {
        std::process::exit(1);
    }
}
