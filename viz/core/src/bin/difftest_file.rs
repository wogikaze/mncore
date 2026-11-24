//! Runs one VSM file (which may contain `d set` / `d get`) with the official tools and with the
//! simulator, and prints the values that differ.
//!
//! Usage: difftest_file [--topology <spec>] <file.vsm>
//!
//! The emulator is fed the assembled `j`/`m` instructions plus the `d set`/`d get`/`r` lines,
//! which it needs to initialize memory and to print the values being compared. Keeping only the
//! instruction lines would silently compare against zero-initialized memory.
//!
//! With `--topology` (see `docs/topology.md`) the simulator runs that reduced chip while the
//! emulator runs the full one, and only the emulator's values inside the topology are compared;
//! values the simulator prints outside them are reported too. For a program that moves no data
//! between units the two must agree.

use mncore_sim::{emu, run::Sim, topology::Topology, vsm};

fn main() {
    let mut args = std::env::args().skip(1);
    let mut topo: Option<Topology> = None;
    let mut path: Option<String> = None;
    while let Some(arg) = args.next() {
        if arg == "--topology" {
            let spec = args.next().expect("--topology needs a specification");
            topo = Some(Topology::parse(&spec).unwrap_or_else(|e| panic!("{e}")));
        } else if let Some(spec) = arg.strip_prefix("--topology=") {
            topo = Some(Topology::parse(spec).unwrap_or_else(|e| panic!("{e}")));
        } else {
            path = Some(arg);
        }
    }
    let path = path.expect("usage: difftest_file [--topology <spec>] <file.vsm>");
    let src = std::fs::read_to_string(&path).expect("read");
    let asm = emu::assemble(&src).unwrap_or_else(|e| panic!("{e}"));
    let instr: String = asm
        .lines()
        .filter(|l| l.starts_with('j') || l.starts_with('m') || l.starts_with('d') || l.starts_with("r "))
        .map(|l| format!("{l}\n"))
        .collect();
    let mut expect = emu::parse_dump(&emu::run_asm(&instr).unwrap_or_else(|e| panic!("{e}")));
    if let Some(t) = &topo {
        expect = t.restrict(&expect);
    }
    let mut sim = Sim::with_topology(topo.unwrap_or(Topology::FULL));
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
    if topo.is_some() {
        let mut extra: Vec<_> = sim.dump.keys().filter(|k| !expect.contains_key(*k)).collect();
        extra.sort();
        for k in &extra {
            println!("{} {} {}: emu=missing sim={:016x}", k.0, k.1, k.2, sim.dump[*k]);
        }
        bad += extra.len();
    }
    println!("{} values, {bad} mismatches", expect.len());
    if std::env::var("SHOW").is_ok() {
        for k in expect.keys() {
            println!("{:?} = {:016x}", k, expect[k]);
        }
    }
}
