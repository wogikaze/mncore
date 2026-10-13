//! Runs one VSM file (which may contain `d set` / `d get`) with the official tools and with the
//! simulator, and prints the values that differ.
//!
//! Usage: difftest_file <file.vsm>

use mncore_sim::{emu, run::Sim, vsm};

fn main() {
    let path = std::env::args().nth(1).expect("usage: difftest_file <file.vsm>");
    let src = std::fs::read_to_string(&path).expect("read");
    let asm = emu::assemble(&src).unwrap_or_else(|e| panic!("{e}"));
    let expect = emu::parse_dump(&emu::run_asm(&asm).unwrap_or_else(|e| panic!("{e}")));
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
}
