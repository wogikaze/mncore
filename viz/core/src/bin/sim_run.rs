//! Runs a VSM file on the simulator and prints the values of its `d get` statements.
//!
//! Usage: sim_run [--topology <spec>] [--compare-full] <file.vsm>
//!
//! `--topology` runs a reduced chip (see `docs/topology.md`), for example
//! `--topology l2b=1,l1b=1,mab=16,lm=256,grf=256,l1bm=1024,l2bm=4096`. Omitted keys keep the
//! chip's value; without the option the full chip runs.
//!
//! Output: one line per long word printed by `d get`, sorted,
//! `<memory> <location> <address> <value>`. Memory names and addresses are the keys of
//! `Sim::dump` (`LM0 LM1 GREG0 GREG1 TREG OMR L1BM L2BM DRAM PIU`; word address for LM/GRF,
//! long word address for L1BM/L2BM/DRAM/PDM, T and OMR as documented at `DumpKey`); the value
//! has 16 lower-case hex digits. Locations are chip coordinates, also on a reduced topology.
//!
//! `--compare-full` also runs the full chip and checks that the reduced run printed exactly
//! the full chip's values that lie inside the topology. This holds for programs that do not
//! move data between units.
//!
//! Exit status: 0 success, 1 run-time error, 2 usage or input error, 3 E_RANGE (an access
//! beyond a reduced capacity; stderr names the line and the instruction word), 4 difference
//! found by `--compare-full`.

use std::collections::{BTreeSet, HashMap};
use std::process::exit;

use mncore_sim::run::{DumpKey, Sim};
use mncore_sim::topology::Topology;
use mncore_sim::vsm;

const USAGE: &str = "usage: sim_run [--topology <spec>] [--compare-full] <file.vsm>";

fn usage(msg: &str) -> ! {
    eprintln!("sim_run: {msg}\n{USAGE}");
    exit(2);
}

fn main() {
    let mut topo = Topology::FULL;
    let mut compare = false;
    let mut path: Option<String> = None;
    let mut args = std::env::args().skip(1);
    while let Some(arg) = args.next() {
        let spec = if arg == "--topology" {
            Some(args.next().unwrap_or_else(|| usage("--topology needs a specification")))
        } else {
            arg.strip_prefix("--topology=").map(str::to_string)
        };
        if let Some(spec) = spec {
            topo = Topology::parse(&spec).unwrap_or_else(|e| usage(&e));
            continue;
        }
        match arg.as_str() {
            "--compare-full" => compare = true,
            "-h" | "--help" => {
                println!("{USAGE}");
                return;
            }
            s if s.starts_with('-') => usage(&format!("unknown option `{s}`")),
            s if path.is_none() => path = Some(s.to_string()),
            _ => usage("give one VSM file"),
        }
    }
    let path = path.unwrap_or_else(|| usage("missing VSM file"));
    let src = std::fs::read_to_string(&path).unwrap_or_else(|e| {
        eprintln!("sim_run: {path}: {e}");
        exit(2)
    });
    let lines = vsm::parse(&src).unwrap_or_else(|e| {
        eprintln!("sim_run: {path}: {e}");
        exit(2)
    });

    let mut sim = Sim::with_topology(topo);
    let result = sim.run(&lines);
    print_dump(&sim.dump);
    let mut status = 0;
    if let Err(e) = &result {
        eprintln!("sim_run: {path}: line {} (instruction word {}): {}", e.line, e.word, e.msg);
        status = if e.is_range() { 3 } else { 1 };
    }
    if compare && status == 0 {
        let mut full = Sim::new();
        if let Err(e) = full.run(&lines) {
            eprintln!("sim_run: full chip: line {} (instruction word {}): {}", e.line, e.word, e.msg);
            exit(1);
        }
        let expected = topo.restrict(&full.dump);
        let keys: BTreeSet<&DumpKey> = expected.keys().chain(sim.dump.keys()).collect();
        let mut bad = 0;
        for k in keys {
            let (e, r) = (expected.get(k), sim.dump.get(k));
            if e != r {
                bad += 1;
                if bad <= 20 {
                    let show = |v: Option<&u64>| v.map(|v| format!("{v:016x}")).unwrap_or("missing".into());
                    eprintln!("MISMATCH {} {} {}: full={} reduced={}", k.0, k.1, k.2, show(e), show(r));
                }
            }
        }
        eprintln!("compare-full ({topo}): {} values inside the topology, {bad} differences", expected.len());
        if bad > 0 {
            status = 4;
        }
    }
    exit(status);
}

fn print_dump(dump: &HashMap<DumpKey, u64>) {
    let mut keys: Vec<&DumpKey> = dump.keys().collect();
    keys.sort();
    let mut out = String::new();
    for k in keys {
        out += &format!("{} {} {} {:016x}\n", k.0, k.1, k.2, dump[k]);
    }
    print!("{out}");
}
