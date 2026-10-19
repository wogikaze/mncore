//! Runs one VSM file (which may contain `d set` / `d get`) with the official tools and with the
//! simulator, and prints the values that differ.
//!
//! Usage: difftest_file <file.vsm>
//!
//! The emulator is fed the assembled `j`/`m` instructions plus the `d set`/`d get`/`r` lines,
//! which it needs to initialize memory and to print the values being compared. Keeping only the
//! instruction lines would silently compare against zero-initialized memory.

use mncore_sim::{emu, run::Sim, vsm};

fn main() {
    let path = std::env::args().nth(1).expect("usage: difftest_file <file.vsm>");
    let src = std::fs::read_to_string(&path).expect("read");
    let asm = emu::assemble(&src).unwrap_or_else(|e| panic!("{e}"));
    let instr: String = asm
        .lines()
        .filter(|l| l.starts_with('j') || l.starts_with('m') || l.starts_with('d') || l.starts_with("r "))
        .map(|l| format!("{l}\n"))
        .collect();
    let expect = emu::parse_dump(&emu::run_asm(&instr).unwrap_or_else(|e| panic!("{e}")));
    let mut sim = Sim::new();
    if let Err(e) = sim.run(&vsm::parse(&src).unwrap_or_else(|e| panic!("{e}"))) {
        println!("simulator stopped at line {}: {}", e.line, e.msg);
    }
    let mut keys: Vec<_> = expect.keys().collect();
    keys.sort();
    let mut bad = 0;
    for k in keys {
        let e = expect[k];
        if sim.dump.get(k) != Some(&e) {
            bad += 1;
            println!("{} {} {}: emu={e:016x} sim={}", k.0, k.1, k.2, sim.dump.get(k).map(|v| format!("{v:016x}")).unwrap_or("missing".into()));
        }
    }
    println!("{} values, {bad} mismatches", expect.len());
    if std::env::var("SHOW").is_ok() {
        for k in expect.keys() {
            println!("{:?} = {:016x}", k, expect[k]);
        }
    }
}
