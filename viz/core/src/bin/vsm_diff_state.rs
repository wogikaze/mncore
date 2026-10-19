//! Runs two VSM programs from the same random initial state and diffs the final state.

use mncore_sim::machine::{GRF_WORDS, LM_WORDS, PES};
use mncore_sim::run::Sim;
use mncore_sim::vsm;

fn rng(state: &mut u64) -> u64 {
    *state ^= *state >> 12;
    *state ^= *state << 25;
    *state ^= *state >> 27;
    state.wrapping_mul(0x2545_F491_4F6C_DD1D)
}

const DRAM_LONGS: u64 = 65536;
const PDM_LONGS: u64 = 512 * 1024;

struct Init {
    lm0: Vec<u32>,
    lm1: Vec<u32>,
    grf0: Vec<u32>,
    grf1: Vec<u32>,
    dram: Vec<u64>,
    pdm: Vec<u64>,
}

fn make(program: &[(usize, vsm::Line)], init: &Init) -> Sim {
    let mut sim = Sim::new();
    seed_sim(&mut sim, init);
    sim.run(program).expect("run");
    sim
}

fn check(pa: &str, pb: &str) -> usize {
    let a = vsm::parse(&std::fs::read_to_string(pa).expect("read a")).expect("parse a");
    let b = vsm::parse(&std::fs::read_to_string(pb).expect("read b")).expect("parse b");
    let seed: u64 = std::env::var("SEED").ok().and_then(|v| v.parse().ok()).unwrap_or(0x1234_5678_9abc_def1);
    let mut s = seed;
    let fill = |n: usize, s: &mut u64| -> Vec<u32> {
        (0..n).map(|_| 0x3f80_0000u32 | (rng(s) as u32 & 0xffff)).collect()
    };
    let init = Init {
        lm0: fill(PES * LM_WORDS, &mut s),
        lm1: fill(PES * LM_WORDS, &mut s),
        grf0: fill(PES * GRF_WORDS, &mut s),
        grf1: fill(PES * GRF_WORDS, &mut s),
        dram: (0..(4 * DRAM_LONGS)).map(|_| rng(&mut s)).collect(),
        pdm: (0..(4 * PDM_LONGS)).map(|_| rng(&mut s)).collect(),
    };
    let trace = std::env::var("TRACE").is_ok();
    let (sa, sb) = if trace {
        let mut x = Sim::new();
        let mut y = Sim::new();
        seed_sim(&mut x, &init);
        seed_sim(&mut y, &init);
        let n = a.len().min(b.len());
        let mut first = None;
        for i in 0..n {
            x.exec(&a[i].1).expect("a");
            y.exec(&b[i].1).expect("b");
            if first.is_none() && probe(&x, &y) {
                first = Some(i);
                eprintln!("first divergence after statement {i} (line {}):", a[i].0);
                eprintln!("  a: {}", line_text(&a[i].1));
                eprintln!("  b: {}", line_text(&b[i].1));
                for j in i.saturating_sub(4)..=i {
                    eprintln!("   [{j}] a: {} | b: {}", line_text(&a[j].1), line_text(&b[j].1));
                }
                break;
            }
        }
        if first.is_none() {
            eprintln!("no divergence in the first {n} statements");
        }
        for line in &a[n..] {
            x.exec(&line.1).expect("a");
        }
        for line in &b[n..] {
            y.exec(&line.1).expect("b");
        }
        (x, y)
    } else {
        (make(&a, &init), make(&b, &init))
    };
    let diffs = count(&sa, &sb);
    println!("{pa} vs {pb}: {diffs} differences");
    if diffs != 0 { 1 } else { 0 }
}

fn probe(a: &Sim, b: &Sim) -> bool {
    for i in 0..4 * LM_WORDS {
        if a.m.mem.lm0[i] != b.m.mem.lm0[i] || a.m.mem.lm1[i] != b.m.mem.lm1[i] {
            return true;
        }
    }
    for i in 0..4 * GRF_WORDS {
        if a.m.mem.grf0[i] != b.m.mem.grf0[i] || a.m.mem.grf1[i] != b.m.mem.grf1[i] {
            return true;
        }
    }
    for g in 0..4usize {
        for i in 0..256u64 {
            if a.off.dram[g].get(i) != b.off.dram[g].get(i) || a.off.pdm[g].get(i) != b.off.pdm[g].get(i) {
                return true;
            }
        }
    }
    false
}

fn line_text(line: &vsm::Line) -> String {
    match line {
        vsm::Line::Pe(exprs) => exprs.iter().map(|e| e.text.to_string()).collect::<Vec<_>>().join("; "),
        vsm::Line::Mv(mv) => mv.text.to_string(),
        vsm::Line::Nop { count, .. } => format!("nop/{count}"),
        other => format!("{other:?}"),
    }
}

fn seed_sim(sim: &mut Sim, init: &Init) {
    sim.m.mem.lm0.clone_from_slice(&init.lm0);
    sim.m.mem.lm1.clone_from_slice(&init.lm1);
    sim.m.mem.grf0.clone_from_slice(&init.grf0);
    sim.m.mem.grf1.clone_from_slice(&init.grf1);
    for g in 0..4usize {
        for (i, v) in init.dram[g * DRAM_LONGS as usize..(g + 1) * DRAM_LONGS as usize]
            .iter()
            .enumerate()
        {
            sim.off.dram[g].set(i as u64, *v);
        }
        for (i, v) in init.pdm[g * PDM_LONGS as usize..(g + 1) * PDM_LONGS as usize]
            .iter()
            .enumerate()
        {
            sim.off.pdm[g].set(i as u64, *v);
        }
    }
}

fn count(a: &Sim, b: &Sim) -> usize {
    let mut d = 0;
    for i in 0..PES * LM_WORDS {
        if a.m.mem.lm0[i] != b.m.mem.lm0[i] {
            d += 1;
        }
        if a.m.mem.lm1[i] != b.m.mem.lm1[i] {
            d += 1;
        }
    }
    for i in 0..PES * GRF_WORDS {
        if a.m.mem.grf0[i] != b.m.mem.grf0[i] {
            d += 1;
        }
        if a.m.mem.grf1[i] != b.m.mem.grf1[i] {
            d += 1;
        }
    }
    for g in 0..4usize {
        for i in 0..DRAM_LONGS {
            if a.off.dram[g].get(i) != b.off.dram[g].get(i) {
                d += 1;
            }
        }
        for i in 0..PDM_LONGS {
            if a.off.pdm[g].get(i) != b.off.pdm[g].get(i) {
                d += 1;
            }
        }
    }
    d
}

fn main() {
    let mut args = std::env::args().skip(1);
    if let Ok(list) = std::env::var("PAIRLIST") {
        // Each line of the list is "<a>|<b>"; run them all in this process.
        let mut bad = 0;
        for line in std::fs::read_to_string(list).unwrap().lines() {
            let (x, y) = line.split_once('|').unwrap();
            if check(x, y) != 0 {
                bad += 1;
            }
        }
        if bad != 0 {
            std::process::exit(1);
        }
        return;
    }
    let pa = args.next().expect("a.vsm");
    let pb = args.next().expect("b.vsm");
    let seed: u64 = args.next().and_then(|s| s.parse().ok()).unwrap_or(0x1234_5678_9abc_def1);
    if std::env::var("REPORT").is_ok() {
        // Trace both runs statement by statement and report where the state first splits.
        eprintln!("REPORT mode: {} {}", pa, pb);
    }
    check(&pa, &pb);
    let _ = seed;
}
