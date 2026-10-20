//! Runs a program from the prepared MNIST step state and prints its `d get` dump.
//!
//! Usage: lm_dump <dir> <program.vsm>
//!
//! Insert `d get $lm0n0c0b0m0p0 N` / `d get $ln0n0c0b0m0p0 N` lines to inspect LM.

use std::fs;

use mncore_sim::run::Sim;
use mncore_sim::vsm;

fn read_u64(path: &str) -> Vec<u64> {
    fs::read(path)
        .unwrap()
        .chunks_exact(8)
        .map(|c| u64::from_le_bytes(c.try_into().unwrap()))
        .collect()
}

fn main() {
    let dir = std::env::args().nth(1).unwrap();
    let program_path = std::env::args().nth(2).unwrap();
    let init = read_u64(&format!("{dir}/init_dram.bin"));
    let source = fs::read_to_string(&program_path).unwrap();
    let program = vsm::parse(&source).unwrap();
    let mut sim = Sim::new();
    const DRAM_LONGS: u64 = 264064;
    for g in 0..4usize {
        for a in 0..DRAM_LONGS {
            sim.off.dram[g].set(a, init[g * DRAM_LONGS as usize + a as usize]);
        }
    }
    sim.run(&program).unwrap();

    let mut keys: Vec<_> = sim.dump.keys().cloned().collect();
    keys.sort();
    for (mem, pe, addr) in keys {
        println!("{mem} {pe} {addr} {:016x}", sim.dump[&(mem.clone(), pe.clone(), addr)]);
    }
}
