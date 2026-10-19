//! Full memory-path conformance test of the GPU backend against the CPU `Sim`.
//!
//! The sections cover every documented L2BM transfer/reduction/multicast form
//! (SDM 3.6.7), the DAR path (`l2bmdars` / `l2bmdarw`, SDM 3.6.7.10), every
//! documented MV basic mode including DRAM indirect access (SDM 3.5.8 and
//! 3.5.6), operand addressing (`$mb`/`$nb`, BAR-inclusive addresses, T-indirect
//! and `j`/madpe), fixed-value inputs, and `noforward`/`wait` (SDM 3.6.6 and
//! 3.6.13).
//!
//! Every section runs the same program on the CPU `Sim` and on the GPU after
//! loading the same seeded state, then compares LM0/LM1/GRF0/GRF1, T, OMR,
//! aluf/mauf/mreadf, the matrix registers, L1BM, L2BM, the turnaround register,
//! BAR, PDM, DRAM, DAR and the DAR buffer. Any mismatch exits nonzero.
//!
//! Usage: gpu_mem_conformance
//!
//! Exit codes: 0 all sections match, 1 mismatch, 2 no GPU, 3 bad program.

use mncore_sim::blocks::{
    L1BM_LONGS, L1BS, L2BM_LONGS, L2BS, DARBUF_ENTRIES, DAR_ENTRIES,
};
use mncore_sim::gpu::{
    alu_line_from_expr, bfn_line_from_expr_state, l1_read_line_from_expr,
    l1_write_line_from_expr, l2_line_from_expr, l2_reduce_line_from_expr,
    mat_mau_line_from_expr, mat_read_line_from_expr, mat_write_line_from_expr,
    mau_line_from_expr, mv_line_from_mv, Gpu, MAT_WORDS,
};
use mncore_sim::machine::{MaskState, GRF_WORDS, LM_WORDS, PES};
use mncore_sim::mv::{GROUPS, PDM_LONGS};
use mncore_sim::run::Sim;
use mncore_sim::vsm::{self, Line, Op};

/// Device DRAM capacity used by every section (long words per group). Chosen so
/// that all direct and indirect addresses in the generated programs fit.
const DRAM_LONGS: u64 = 1 << 18;

const RRN_FLOAT: [&str; 9] = [
    "dfadd", "ffadd", "hfadd", "dmax", "fmax", "hmax", "dmin", "fmin", "hmin",
];
const RRN_INT: [&str; 15] = [
    "liadd", "iiadd", "siadd", "lband", "iband", "sband", "land", "iand", "sand", "lbor",
    "ibor", "sbor", "lor", "ior", "sor",
];

/// All L1B sets of table 3.7, with their `<l1badr>/<immode>` spelling.
const L1B_SETS: [(&str, u8); 27] = [
    ("0", 0),
    ("1", 0),
    ("2", 0),
    ("3", 0),
    ("4", 0),
    ("5", 0),
    ("6", 0),
    ("7", 0),
    ("0/1", 1),
    ("0/2", 2),
    ("0/4", 4),
    ("1/2", 2),
    ("1/4", 4),
    ("2/1", 1),
    ("2/4", 4),
    ("3/4", 4),
    ("4/1", 1),
    ("4/2", 2),
    ("5/2", 2),
    ("6/1", 1),
    ("0/3", 3),
    ("0/5", 5),
    ("0/6", 6),
    ("1/6", 6),
    ("2/5", 5),
    ("4/3", 3),
    ("0/7", 7),
];

fn rrn_names() -> Vec<&'static str> {
    RRN_FLOAT.iter().chain(RRN_INT.iter()).copied().collect()
}

struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    fn u32(&mut self) -> u32 {
        self.next() as u32
    }
    fn below(&mut self, n: u32) -> u32 {
        (self.next() % n as u64) as u32
    }
}

/// Host copy of every memory the GPU keeps, used for the initial upload.
struct Host {
    lm0: Vec<u32>,
    lm1: Vec<u32>,
    grf0: Vec<u32>,
    grf1: Vec<u32>,
    t: Vec<u32>,
    mask: Vec<u32>,
    bar0: Vec<u32>,
    bar1: Vec<u32>,
    l1: Vec<u64>,
    l2: Vec<u64>,
    lbi: Vec<u64>,
    pdm: Vec<u64>,
    dram: Vec<u64>,
    dar: Vec<u32>,
    darbuf: Vec<u32>,
    dar_addr: [u32; 2],
    mats: Vec<u32>,
}

impl Host {
    fn random(rng: &mut Rng) -> Host {
        let mut lm0 = vec![0u32; PES * LM_WORDS];
        let mut lm1 = vec![0u32; PES * LM_WORDS];
        let mut grf0 = vec![0u32; PES * GRF_WORDS];
        let mut grf1 = vec![0u32; PES * GRF_WORDS];
        for v in lm0.iter_mut().chain(lm1.iter_mut()).chain(grf0.iter_mut()).chain(grf1.iter_mut()) {
            *v = rng.u32();
        }
        let mut t = vec![0u32; PES * 16];
        for v in t.iter_mut() {
            *v = rng.u32();
        }
        let mut mask = vec![0u32; PES * 16];
        for pe in 0..PES {
            for e in 0..16 {
                mask[pe * 16 + e] = if e == 0 { 0 } else { (rng.u32() & 0xffff) as u32 };
            }
        }
        let bar0 = (0..PES).map(|_| rng.u32() & 0xfff).collect();
        let bar1 = (0..PES).map(|_| rng.u32() & 0xfff).collect();
        let l1 = (0..L1BS * L1BM_LONGS).map(|_| rng.next()).collect();
        let l2 = (0..L2BS * L2BM_LONGS).map(|_| rng.next()).collect();
        let lbi = (0..L1BS * 4 * 64).map(|_| rng.next()).collect();
        let pdm = (0..GROUPS * PDM_LONGS as usize).map(|_| rng.next()).collect();
        let dram = (0..GROUPS * DRAM_LONGS as usize).map(|_| rng.next()).collect();
        let dar: Vec<u32> = (0..GROUPS * DAR_ENTRIES)
            .map(|_| rng.below(1536))
            .collect();
        let darbuf = (0..GROUPS * DARBUF_ENTRIES).map(|_| rng.u32()).collect();
        let dar_addr = [rng.below(DAR_ENTRIES as u32), rng.below(DARBUF_ENTRIES as u32)];
        let mats = (0..MAT_WORDS).map(|_| rng.u32()).collect();
        Host {
            lm0,
            lm1,
            grf0,
            grf1,
            t,
            mask,
            bar0,
            bar1,
            l1,
            l2,
            lbi,
            pdm,
            dram,
            dar,
            darbuf,
            dar_addr,
            mats,
        }
    }

    fn apply(&self, sim: &mut Sim) {
        sim.m.mem.lm0.copy_from_slice(&self.lm0);
        sim.m.mem.lm1.copy_from_slice(&self.lm1);
        sim.m.mem.grf0.copy_from_slice(&self.grf0);
        sim.m.mem.grf1.copy_from_slice(&self.grf1);
        for pe in 0..PES {
            let p = &mut sim.m.pes[pe];
            p.t.copy_from_slice(&self.t[pe * 16..(pe + 1) * 16]);
            for e in 0..16 {
                p.mask[e] = self.mask[pe * 16 + e] as u16;
            }
            p.bar0 = self.bar0[pe];
            p.bar1 = self.bar1[pe];
        }
        for b in 0..L1BS {
            sim.m.blocks.l1bm[b]
                .copy_from_slice(&self.l1[b * L1BM_LONGS..(b + 1) * L1BM_LONGS]);
            for c in 0..4 {
                sim.m.blocks.lbi[b][c].copy_from_slice(&self.lbi[(b * 4 + c) * 64..(b * 4 + c + 1) * 64]);
            }
        }
        for b in 0..L2BS {
            sim.m.blocks.l2bm[b]
                .copy_from_slice(&self.l2[b * L2BM_LONGS..(b + 1) * L2BM_LONGS]);
        }
        for g in 0..GROUPS {
            sim.m.blocks.dar[g].copy_from_slice(&self.dar[g * DAR_ENTRIES..(g + 1) * DAR_ENTRIES]);
            sim.m.blocks.darbuf[g]
                .copy_from_slice(&self.darbuf[g * DARBUF_ENTRIES..(g + 1) * DARBUF_ENTRIES]);
            for a in 0..PDM_LONGS as usize {
                sim.off.pdm[g].set(a as u64, self.pdm[g * PDM_LONGS as usize + a]);
            }
            for a in 0..DRAM_LONGS as usize {
                sim.off.dram[g].set(a as u64, self.dram[g * DRAM_LONGS as usize + a]);
            }
        }
        sim.m.blocks.darw_addr = self.dar_addr[0] as usize % DAR_ENTRIES;
        sim.m.blocks.darbuf_read_addr = self.dar_addr[1] as usize % DARBUF_ENTRIES;
        sim.m.mats = vec![[[[0u32; 8]; 16]; 2]; PES / 4];
        for mab in 0..PES / 4 {
            for face in 0..2 {
                for row in 0..16 {
                    for w in 0..8 {
                        let idx = ((mab * 2 + face) * 16 + row) * 8 + w;
                        sim.m.mats[mab][face][row][w] = self.mats[idx];
                    }
                }
            }
        }
    }
}

/// Bump allocator shared by all arrays of one memory kind. Addresses wrap so a
/// long section never runs out; overlapping cases still compare the full final
/// state on both machines.
struct Alloc {
    l1: u32,
    l2: u32,
    pdm: u32,
    dram: u32,
}

impl Alloc {
    fn new() -> Alloc {
        Alloc {
            l1: 0,
            l2: 0,
            pdm: 0,
            dram: 0,
        }
    }
    fn take(slot: &mut u32, n: u32, align: u32, cap: u32) -> u32 {
        let a = (*slot + align - 1) & !(align - 1);
        let a = if a + n > cap { 0 } else { a };
        *slot = a + n;
        a
    }
    fn l1(&mut self, n: u32, align: u32) -> u32 {
        Self::take(&mut self.l1, n, align, (L1BM_LONGS - 256) as u32)
    }
    fn l2(&mut self, n: u32, align: u32) -> u32 {
        Self::take(&mut self.l2, n, align, (L2BM_LONGS - 512) as u32)
    }
    fn pdm(&mut self, n: u32, align: u32) -> u32 {
        Self::take(&mut self.pdm, n, align, (PDM_LONGS - 1024) as u32)
    }
    fn dram(&mut self, n: u32, align: u32) -> u32 {
        Self::take(&mut self.dram, n, align, (DRAM_LONGS - 1024) as u32)
    }
}

struct Section {
    name: &'static str,
    lines: Vec<String>,
    /// Replaces the seeded DAR contents (used by the indirect MV section).
    dar: Option<Vec<u32>>,
    /// Replaces the seeded DRAM capacity? No: every section uses `DRAM_LONGS`.
    cases: usize,
}

impl Section {
    fn new(name: &'static str, dar: Option<Vec<u32>>) -> Section {
        Section {
            name,
            lines: Vec::new(),
            dar,
            cases: 0,
        }
    }
    fn push(&mut self, line: String) {
        self.cases += 1;
        self.lines.push(line);
    }
    fn raw(&mut self, line: String) {
        self.cases += 1;
        self.lines.push(line);
    }
}

// ---------------------------------------------------------------------------
// L2BM (SDM 3.6.7).
// ---------------------------------------------------------------------------

fn section_l2_transfer() -> Section {
    let mut s = Section::new("L2BM transfers", None);
    let mut a = Alloc::new();
    for (set, _) in L1B_SETS {
        let src = a.l2(64, 64);
        let dst = a.l1(64, 16);
        s.push(format!("l2bmb@{set} $lc{src} $lb{dst}"));
    }
    for (set, _) in L1B_SETS {
        let src = a.l2(256, 64);
        let dst = a.l1(64, 16);
        s.push(format!("l2bmb2@{set} $lc{src} $lb{dst}"));
    }
    for (set, _) in L1B_SETS {
        let src = a.l2(256, 64);
        let dst = a.l1(64, 8);
        s.push(format!("l2bmd@{set} $lc{src} $lb{dst}"));
    }
    for l1b in 0..8 {
        let src = a.l1(64, 16);
        let dst = a.l2(64, 16);
        s.push(format!("l2bm@{l1b} $lb{src} $lc{dst}"));
    }
    let src = a.l1(32, 8);
    let dst = a.l2(256, 64);
    s.push(format!("l2bmd $lb{src} $lc{dst}"));
    s
}

fn section_l2_reduce() -> Section {
    let mut s = Section::new("L2BM reductions", None);
    let mut a = Alloc::new();
    // Every RRN with the full set and two partial sets.
    for rrn in rrn_names() {
        for set in ["0/7", "0/4", "1/6"] {
            let src = a.l1(64, 16);
            let dst = a.l2(64, 16);
            s.push(format!("l2bmr{rrn}@{set} $lb{src} $lc{dst}"));
        }
    }
    // Every documented set with one floating RRN.
    for (set, _) in L1B_SETS {
        let src = a.l1(64, 16);
        let dst = a.l2(64, 16);
        s.push(format!("l2bmrffadd@{set} $lb{src} $lc{dst}"));
    }
    // Every RRN for the pairwise form.
    for rrn in rrn_names() {
        let src = a.l1(64, 16);
        let dst = a.l2(256, 64);
        s.push(format!("l2bmr2{rrn} $lb{src} $lc{dst}"));
    }
    // Internal multicast: every admissible immode and a representative base.
    for immode in 0..7u8 {
        for adr in 0..8u8 {
            let src = a.l1(64, 16);
            let dst = a.l1(64, 16);
            s.push(format!("l2bmi@{adr}/{immode} $lb{src} $lb{dst}"));
        }
    }
    // The no-set spelling of the transfer forms.
    let src = a.l1(64, 16);
    let dst = a.l2(256, 64);
    s.push(format!("l2bmb $lc{dst} $lb{src}"));
    let dst = a.l1(64, 16);
    s.push(format!("l2bmb2 $lc{dst} $lb{src}"));
    s.push(format!("l2bmd $lc{dst} $lb{src}"));
    s
}

fn section_l2_dar() -> Section {
    let mut s = Section::new("L2BM DAR (l2bmdars/l2bmdarw)", None);
    let mut a = Alloc::new();
    for l2b in 0..2 {
        for addr in [0u32, 64, 512, 32768 - 256] {
            for dar in [0u32, 1, 511, 1022, 1023] {
                s.push(format!("l2bmdars $lc{addr}@.{l2b} $dar{dar}"));
                for _ in 0..((dar % 4) + 1) {
                    s.raw("l2bmdarw".into());
                }
            }
        }
    }
    // Several consecutive DAR buffer wraps.
    for _ in 0..5 {
        s.raw("l2bmdarw".into());
    }
    // An explicit address for each documented field combination.
    for l2b in 0..2 {
        let src = a.l2(256, 64);
        let dar = 900 + l2b as u32;
        s.raw(format!("l2bmdars $lc{src}@.{l2b} $dar{dar};l2bmdarw"));
        s.raw("l2bmdarw".into());
    }
    // l2bmdarw may be issued together with any other L2BM expression.
    let src = a.l2(64, 64);
    let dst = a.l1(64, 16);
    s.raw(format!("l2bmb@0/7 $lc{src} $lb{dst};l2bmdarw"));
    let src = a.l1(64, 16);
    let dst = a.l2(64, 16);
    s.raw(format!("l2bmrffadd@0/7 $lb{src} $lc{dst};l2bmdarw"));
    s
}

// ---------------------------------------------------------------------------
// MV (SDM 3.5).
// ---------------------------------------------------------------------------

fn section_mv_basic() -> Section {
    let mut s = Section::new("MV basic modes", None);
    let mut a = Alloc::new();
    let pa = a.pdm(1024, 64);
    let pa2 = a.pdm(1024, 64);
    let da = a.dram(1024, 64);
    let ca0 = a.l2(1024, 64);
    let ca1 = a.l2(1024, 64);
    s.push(format!("mvp/n128 $p{pa}@0 $d{da}@1"));
    s.push(format!("mvp/n128i01 $d{da}@2 $p{pa2}@3"));
    s.push(format!("mvp/n128p3 $p{pa2}@1 $d{da}@2"));
    s.push(format!("mvp/n0 $p{pa}@0 $d{da}@1"));
    s.push(format!("mvp/n128 $p{pa2}@0 $lc{ca0}@2.1"));
    s.push(format!("mvp/n128 $lc{ca1}@2.0 $p{pa}@1"));
    s.push(format!("mvp/n128 $d{da}@0 $lc{ca0}@3.1"));
    s.push(format!("mvp/n128 $lc{ca1}@3.1 $d{da}@1"));
    s.push(format!("mvp/n128 $p{pa}@0 $p{pa2}@1"));
    // Overlapping PDM-to-PDM in the same group exercises the snapshot path.
    s.push(format!("mvp/n256 $p{pa}@2 $p{pa}@2"));
    s.push(format!("mvp/n128 $p{pa2} $lc{ca0}@.1"));
    s.push(format!("mvp/n128 $lc{ca1}@.0 $p{pa}"));
    s.push(format!("mvp/n128 $d{da} $lc{ca0}@.1"));
    s.push(format!("mvp/n128 $lc{ca1}@.1 $d{da}"));
    s.push(format!("mvb/n128 $p{pa}@1 $lc{ca1}"));
    s.push(format!("mvb/n128 $p{pa}@2 $lc{ca0}@3.0"));
    s.push(format!("mvb/n128 $d{da} $lc{ca0}"));
    s.push(format!("mvb2/n64 $d{da}@2 $lc{ca1}@3.1"));
    s.push(format!("mvb2/n128 $d{da} $lc{ca1}"));
    s.push(format!("mvb4/n128 $d{da} $lc{ca0}"));
    s.push(format!("mvd/n128 $p{pa}@2 $lc{ca1}"));
    s.push(format!("mvd/n128 $lc{ca0} $p{pa2}@2"));
    s.push(format!("mvd/n128 $p{pa}@1 $d{da}"));
    s.push(format!("mvd/n128 $d{da} $p{pa}@3"));
    s.raw("mvnop".into());
    s
}

fn section_mv_reduce() -> Section {
    let mut s = Section::new("MV reductions", None);
    let mut a = Alloc::new();
    for rrn in rrn_names() {
        let ca = a.l2(64, 64);
        let pa = a.pdm(64, 64);
        s.push(format!("mvr{rrn}/n64 $lc{ca} $p{pa}@0"));
        let ca = a.l2(64, 64);
        let da = a.dram(64, 64);
        s.push(format!("mvr{rrn}/n64 $lc{ca} $d{da}"));
        let ca = a.l2(64, 64);
        let pa = a.pdm(64, 64);
        s.push(format!("mvr2{rrn}/n64 $lc{ca} $p{pa}@1"));
        let ca = a.l2(64, 64);
        let da = a.dram(64, 64);
        s.push(format!("mvr2{rrn}/n64 $lc{ca} $d{da}"));
        let ca = a.l2(64, 64);
        let da = a.dram(64, 64);
        s.push(format!("mvr4{rrn}/n64 $lc{ca} $d{da}"));
    }
    // Group fields of the destination.
    let ca = a.l2(64, 64);
    let pa = a.pdm(64, 64);
    s.push(format!("mvrffadd/n64 $lc{ca} $p{pa}@1"));
    let ca = a.l2(64, 64);
    let pa = a.pdm(64, 64);
    s.push(format!("mvr2ffadd/n64 $lc{ca} $p{pa}"));
    s
}

fn section_mv_indirect(dar: Vec<u32>) -> Section {
    let mut s = Section::new("MV DRAM indirect (DAR)", Some(dar));
    let mut a = Alloc::new();
    let pa = a.pdm(1024, 64);
    let pa2 = a.pdm(1024, 64);
    let ca = a.l2(1024, 64);
    // M values are DAR entries whose contents are small (see `small_dar`).
    for (m, nd) in [(0u32, Some(1u32)), (5, Some(2)), (17, Some(3)), (33, Some(4)), (7, None), (100, None)] {
        let suffix = nd.map(|n| format!("nd{n}")).unwrap_or_default();
        let prefix = if suffix.is_empty() { "/n64".to_string() } else { format!("/n64{suffix}") };
        s.push(format!("mvp{prefix} $p{pa}@0 $di{m}@1"));
        s.push(format!("mvp{prefix} $di{m}@2 $p{pa2}@3"));
        let c = a.l2(64, 64);
        s.push(format!("mvp{prefix} $lc{c}@0.0 $di{m}@2"));
        s.push(format!("mvp{prefix} $di{m}@3 $lc{c}@1.1"));
    }
    // Source and destination both indirect.
    s.push(format!("mvp/n128nd2 $di0@0 $di12@1"));
    s.push(format!("mvb/n64nd2 $di20@0 $lc{ca}"));
    s.push(format!("mvb2/n64nd2 $di24@0 $lc{ca}"));
    s.push(format!("mvb4/n64nd2 $di28@0 $lc{ca}"));
    s.push(format!("mvd/n64nd2 $p{pa}@0 $di40@1"));
    s.push(format!("mvd/n64nd2 $di44@0 $p{pa2}@2"));
    for rrn in ["dfadd", "ffadd", "iiadd", "fmax", "sand"] {
        let c = a.l2(64, 64);
        s.push(format!("mvr{rrn}/n64nd2 $lc{c} $di48@1"));
        let c = a.l2(64, 64);
        s.push(format!("mvr2{rrn}/n64nd2 $lc{c} $di52@1"));
        let c = a.l2(64, 64);
        s.push(format!("mvr4{rrn}/n64nd2 $lc{c} $di56@1"));
    }
    s
}

/// DAR contents whose entries keep every indirect address below 16 * 1536.
fn small_dar(rng: &mut Rng) -> Vec<u32> {
    let mut v = vec![0u32; GROUPS * DAR_ENTRIES];
    for (i, w) in v.iter_mut().enumerate() {
        *w = (i as u32 * 13 + rng.below(7)) % 1536;
    }
    v
}

// ---------------------------------------------------------------------------
// Operand addressing and control.
// ---------------------------------------------------------------------------

fn section_operand() -> Section {
    let mut s = Section::new("operand addressing", None);
    // BAR/T are seeded random; keep the addresses small enough to stay inside
    // the memories. Both machines get exactly the same values.
    s.raw("fpassa $lm0v $ln0v".into());
    s.raw("fpassa $lmt8v $ln8v".into());
    s.raw("fpassa $lm0v4j1 $ln16v".into());
    s.raw("fpassa $lm0v4j3 $ln24v".into());
    s.raw("fpassa $lm[0,8,16,24] $ln32v".into());
    s.raw("fpassa $lmt[0,8,16,24] $ln40v".into());
    // BAR-inclusive destinations.
    s.raw("fpassa $ln64v $lmb".into());
    s.raw("fpassa $lm0v $ln72v".into());
    s.raw("fpassa $lm0v $nb".into());
    s.raw("fpassa $ln0v $lm80v".into());
    // Fixed-value inputs at every documented fixed operand.
    s.raw("ipassa $l2bid $lm96".into());
    s.raw("ipassa $l1bid $lm100".into());
    s.raw("ipassa $mabid $lm104".into());
    s.raw("ipassa $peid $lm108".into());
    s.raw("ipassa $subpeid $lm112".into());
    s.raw("fpassa $msb1 $lm116v".into());
    s.raw("fpassa $msb1 $lm120v".into());
    s.raw("dpassa $subpeid $llm128".into());
    s.raw("lpassa $mabid $llm132".into());
    s.raw("spassa $l2bid $lm136".into());
    s.raw("hpassa $msb1 $lm140".into());
    // MAU sources and destination with BAR/T/j.
    s.raw("fvadd $lm0v $ln0v $lr0v".into());
    s.raw("fvadd $lmt8v $ln8v $lr8v".into());
    s.raw("fvadd $lm0v4j1 $ln16v $lr16v".into());
    s.raw("fvadd $ln0v $lm0v4j2 $lr24v".into());
    s.raw("fpassa $mauf $lr32v".into());
    // BAR destinations of the MAU, L1BM-to-PE and matrix-read paths.
    s.raw("fvadd $ln0v $ln0v $mb".into());
    s.raw("l1bmm $lb0 $nb".into());
    s.raw("fmread $lx0 $mb".into());
    s.raw("fpassa $lm0v $nb".into());
    s.raw("fpassa $lm0v $ln208v".into());
    // L1BM directions with every addressing mode.
    s.raw("l1bmm $lb0 $lm0v".into());
    s.raw("l1bmm $lb64 $lmt8v".into());
    s.raw("l1bmm $lb128 $lm0v4j1".into());
    s.raw("l1bmp $lb192 $ln8v".into());
    s.raw("l1bmm@3 $lm0v $lb256".into());
    s.raw("l1bmm@5 $lmt8v $lb320".into());
    s.raw("l1bmm@7 $lm0v4j2 $lb384".into());
    // Matrix write/read sources and destinations with BAR/T/j.
    s.raw("fmwrite $lm0v $lx0".into());
    s.raw("fmwrite $lmt8v $ly0".into());
    s.raw("fmwrite $lm0v4j1 $lx1".into());
    s.raw("fmread $lx0 $lm0v".into());
    s.raw("fmread $ly0 $lmt8v".into());
    s.raw("fmread $lx1 $lm0v4j2".into());
    // T registers and masks.
    s.raw("fpassa $llt $llm160".into());
    s.raw("fpassa $llm160 $llt".into());
    s.raw("imm i\"0x12345678\" $t".into());
    s.raw("fpassa $t $ln160v".into());
    s.raw("ixor $l2bid $lm168v $omr1".into());
    s.raw("maskn 1".into());
    s.raw("fpassa $lm176v $ln176v".into());
    s.raw("fpassa $lm184v $ln184v/$imr2".into());
    s.raw("mask 0".into());
    s.raw("fpassa $lm192v $ln192v".into());
    s
}

fn section_control() -> Section {
    let mut s = Section::new("noforward and wait", None);
    // ALU forwarding: the noforward step must leave the value of step 1.
    s.raw("fpassa $lm0v $ln0v".into());
    s.raw("noforward; fpassa $lm8v $ln8v".into());
    s.raw("fpassa $aluf $lr0v".into());
    // MAU forwarding.
    s.raw("fvadd $lm16v $ln16v $lr8v".into());
    s.raw("noforward; fvadd $lm24v $ln24v $lr16v".into());
    s.raw("fpassa $mauf $lr24v".into());
    // Matrix-read forwarding.
    s.raw("fmread $lx0 $lm32v".into());
    s.raw("noforward; fmread $lx0 $lm40v".into());
    s.raw("fpassa $mreadf $lr32v".into());
    // The L1BM turnaround register.
    s.raw("l1bmm@0 $lm48v $lb64".into());
    s.raw("noforward; l1bmm@1 $lm56v $lb64".into());
    s.raw("l1bmm $lbi $lr40v".into());
    // wait must accompany another expression and is already satisfied because
    // every MV/PE kernel runs to completion in stream order.
    s.raw("fpassa $lm64v $ln64v; wait i01".into());
    s.raw("l1bmm $lb128 $lm72v; wait i02".into());
    s.raw("nop; wait i03".into());
    // A single noforward step that would update two forwarding paths at once.
    s.raw("noforward; fpassa $lm88v $lr88v; l1bmm@2 $ln96v $lb128".into());
    s
}

// ---------------------------------------------------------------------------
// Execution and comparison.
// ---------------------------------------------------------------------------

fn run_gpu(gpu: &Gpu, state: &mncore_sim::gpu::GpuState, lines: &[(usize, Line)]) -> Result<(), String> {
    let mut mask = MaskState::default();
    for (lineno, line) in lines {
        match line {
            Line::Nop { .. } => {}
            Line::MaskDirective { wl, targets, entry } => {
                mask = MaskState {
                    wl: *wl,
                    targets: *targets,
                    entry: *entry,
                };
            }
            Line::Mv(mv) => {
                let desc = mv_line_from_mv(mv)
                    .ok_or_else(|| format!("line {lineno}: no MV descriptor for {}", mv.text))?;
                gpu.run_mv_line(state, &desc)?;
            }
            Line::Pe(exprs) => {
                mncore_sim::issue::check(exprs).map_err(|e| format!("line {lineno}: {e}"))?;
                let wait = exprs.iter().any(|e| matches!(e.op, Op::Wait(_)));
                if wait {
                    if exprs.len() < 2 {
                        return Err(format!("line {lineno}: wait without another expression"));
                    }
                    if exprs.iter().any(|e| matches!(e.op, Op::Wait(0))) {
                        return Err(format!("line {lineno}: wait tag 0"));
                    }
                }
                let update_forward = !exprs.iter().any(|e| matches!(e.op, Op::Noforward));
                let has_mread = exprs.iter().any(|e| matches!(e.op, Op::MatRead { .. }));
                for expr in exprs {
                    if matches!(expr.op, Op::Noforward | Op::Wait(_)) {
                        continue;
                    }
                    if let Some(line) = alu_line_from_expr(expr, mask) {
                        gpu.run_alu_line_with(state, &line, update_forward)?;
                    } else if let Some(line) = bfn_line_from_expr_state(expr, mask) {
                        gpu.run_bfn_line_with(state, &line, update_forward)?;
                    } else if let Some(line) = l1_read_line_from_expr(expr, mask) {
                        gpu.run_l1_read_line(state, &line)?;
                    } else if let Some(line) = l1_write_line_from_expr(expr) {
                        gpu.run_l1_write_line_with(state, &line, update_forward)?;
                    } else if let Some(line) = l2_line_from_expr(expr) {
                        gpu.run_l2_line(state, &line)?;
                    } else if let Some(line) = l2_reduce_line_from_expr(expr) {
                        gpu.run_l2_reduce_line(state, &line)?;
                    } else if let Some(line) = mat_write_line_from_expr(expr) {
                        gpu.run_mat_write_line(state, &line)?;
                    } else if let Some(line) = mat_read_line_from_expr(expr, mask) {
                        gpu.run_mat_read_line_with(state, &line, update_forward)?;
                    } else if let Some(line) = mat_mau_line_from_expr(expr, mask) {
                        gpu.run_mat_mau_line_with(state, &line, update_forward)?;
                    } else if let Some(line) = mau_line_from_expr(expr, mask) {
                        gpu.run_mau_line_with(state, &line, update_forward)?;
                    } else {
                        return Err(format!("line {lineno}: no GPU descriptor for {}", expr.text));
                    }
                }
                if update_forward && !has_mread {
                    gpu.clear_mreadf(state)?;
                }
            }
            other => return Err(format!("line {lineno}: unsupported line {other:?}")),
        }
    }
    gpu.sync()
}

fn mismatch<T: PartialEq + std::fmt::Debug>(name: &str, cpu: &[T], gpu: &[T], report: bool) -> usize {
    assert_eq!(cpu.len(), gpu.len(), "{name} length");
    let mut bad = 0;
    for (i, (a, b)) in cpu.iter().zip(gpu).enumerate() {
        if a != b {
            bad += 1;
            if report && bad <= 4 {
                println!("  {name}[{i}]: cpu {a:?} gpu {b:?}");
            }
        }
    }
    bad
}

fn compare(
    sim: &Sim,
    gpu: &Gpu,
    state: &mncore_sim::gpu::GpuState,
    host: &Host,
    label: &str,
) -> Result<usize, String> {
    let mut bad = 0;
    let report = true;
    let (lm0, lm1, grf0, grf1) = {
        let mut out = (
            vec![0u32; PES * LM_WORDS],
            vec![0u32; PES * LM_WORDS],
            vec![0u32; PES * GRF_WORDS],
            vec![0u32; PES * GRF_WORDS],
        );
        gpu.download_state(state, &mut out.0, &mut out.1, &mut out.2, &mut out.3)?;
        out
    };
    bad += mismatch("lm0", &sim.m.mem.lm0, &lm0, report);
    bad += mismatch("lm1", &sim.m.mem.lm1, &lm1, report);
    bad += mismatch("grf0", &sim.m.mem.grf0, &grf0, report);
    bad += mismatch("grf1", &sim.m.mem.grf1, &grf1, report);
    let cpu_t: Vec<u32> = sim.m.pes.iter().flat_map(|p| p.t.iter().copied()).collect();
    bad += mismatch("t", &cpu_t, &gpu.download_t(state)?, report);
    let cpu_mask: Vec<u32> = sim
        .m
        .pes
        .iter()
        .flat_map(|p| p.mask.iter().map(|&v| v as u32))
        .collect();
    bad += mismatch("mask", &cpu_mask, &gpu.download_mask(state)?, report);
    let (bar0, bar1) = gpu.download_bar(state)?;
    let cpu_bar0: Vec<u32> = sim.m.pes.iter().map(|p| p.bar0).collect();
    let cpu_bar1: Vec<u32> = sim.m.pes.iter().map(|p| p.bar1).collect();
    bad += mismatch("bar0", &cpu_bar0, &bar0, report);
    bad += mismatch("bar1", &cpu_bar1, &bar1, report);
    let cpu_aluf: Vec<u32> = sim
        .m
        .pes
        .iter()
        .flat_map(|p| p.aluf.iter().flat_map(|c| c.iter().copied()))
        .collect();
    let cpu_mauf: Vec<u32> = sim
        .m
        .pes
        .iter()
        .flat_map(|p| p.mauf.iter().flat_map(|c| c.iter().copied()))
        .collect();
    let cpu_mreadf: Vec<u32> = sim
        .m
        .pes
        .iter()
        .flat_map(|p| p.mreadf.iter().flat_map(|c| c.iter().copied()))
        .collect();
    bad += mismatch("aluf", &cpu_aluf, &gpu.download_aluf(state)?, report);
    bad += mismatch("mauf", &cpu_mauf, &gpu.download_mauf(state)?, report);
    bad += mismatch("mreadf", &cpu_mreadf, &gpu.download_mreadf(state)?, report);
    let cpu_l1: Vec<u64> = sim.m.blocks.l1bm.iter().flatten().copied().collect();
    bad += mismatch("l1bm", &cpu_l1, &gpu.download_l1bm(state)?, report);
    let cpu_l2: Vec<u64> = sim.m.blocks.l2bm.iter().flatten().copied().collect();
    bad += mismatch("l2bm", &cpu_l2, &gpu.download_l2bm(state)?, report);
    let mut cpu_lbi = Vec::new();
    for l1b in 0..L1BS {
        for c in 0..4 {
            cpu_lbi.extend(sim.m.blocks.lbi[l1b][c].iter().copied());
        }
    }
    bad += mismatch("lbi", &cpu_lbi, &gpu.download_l1bi(state)?, report);
    let cpu_pdm: Vec<u64> = (0..GROUPS)
        .flat_map(|g| (0..PDM_LONGS).map(move |a| (g, a)))
        .map(|(g, a)| sim.off.pdm[g].get(a))
        .collect();
    bad += mismatch("pdm", &cpu_pdm, &gpu.download_pdm(state)?, report);
    let cpu_dram: Vec<u64> = (0..GROUPS)
        .flat_map(|g| (0..DRAM_LONGS).map(move |a| (g, a)))
        .map(|(g, a)| sim.off.dram[g].get(a))
        .collect();
    bad += mismatch("dram", &cpu_dram, &gpu.download_dram(state)?, report);
    let cpu_dar: Vec<u32> = sim.m.blocks.dar.iter().flatten().copied().collect();
    bad += mismatch("dar", &cpu_dar, &gpu.download_dar(state)?, report);
    let cpu_darbuf: Vec<u32> = sim.m.blocks.darbuf.iter().flatten().copied().collect();
    bad += mismatch("darbuf", &cpu_darbuf, &gpu.download_darbuf(state)?, report);
    let cpu_addr = [
        sim.m.blocks.darw_addr as u32,
        sim.m.blocks.darbuf_read_addr as u32,
    ];
    bad += mismatch("dar_addr", &cpu_addr, &gpu.download_dar_addr(state)?, report);
    let cpu_mats: Vec<u32> = sim
        .m
        .mats
        .iter()
        .flat_map(|m| m.iter())
        .flat_map(|f| f.iter())
        .flat_map(|r| r.iter())
        .copied()
        .collect();
    if cpu_mats.len() == MAT_WORDS {
        bad += mismatch("mats", &cpu_mats, &gpu.download_mats(state)?, report);
    }
    let mv_errors = gpu.download_mv_errors(state)?;
    if mv_errors != 0 {
        println!("  {label}: {mv_errors} indirect MV access(es) outside device DRAM");
        bad += mv_errors as usize;
    }
    let _ = host;
    Ok(bad)
}

fn main() {
    let gpu = match Gpu::new() {
        Ok(gpu) => gpu,
        Err(error) => {
            eprintln!("gpu unavailable: {error}");
            std::process::exit(2);
        }
    };
    let mut rng = Rng(0x9e37_79b9_7f4a_7c15);
    let sections = vec![
        section_l2_transfer(),
        section_l2_reduce(),
        section_l2_dar(),
        section_mv_basic(),
        section_mv_reduce(),
        section_mv_indirect(small_dar(&mut rng)),
        section_operand(),
        section_control(),
    ];

    println!("GPU memory conformance: {} sections, DRAM {} long words/group", sections.len(), DRAM_LONGS);
    println!();
    let mut total_cases = 0usize;
    let mut total_mismatches = 0usize;
    for (si, section) in sections.iter().enumerate() {
        total_cases += section.cases;
        let text = section.lines.join("\n");
        let parsed = vsm::parse(&text).unwrap_or_else(|e| {
            eprintln!("{}: parse {}:{}: {}", section.name, e.line, e.msg, text.lines().nth(e.line - 1).unwrap_or(""));
            std::process::exit(3);
        });
        let mut host = Host::random(&mut rng);
        if let Some(dar) = &section.dar {
            host.dar.clone_from(dar);
        }
        let mut sim = Sim::new();
        host.apply(&mut sim);
        let state = gpu
            .allocate_state_with_mv(DRAM_LONGS, 1024)
            .unwrap_or_else(|e| {
                eprintln!("allocate: {e}");
                std::process::exit(2);
            });
        gpu.upload_state(&state, &host.lm0, &host.lm1, &host.grf0, &host.grf1)
            .expect("upload state");
        gpu.upload_t(&state, &host.t).expect("upload t");
        gpu.upload_mask(&state, &host.mask).expect("upload mask");
        gpu.upload_bar(&state, &host.bar0, &host.bar1).expect("upload bar");
        gpu.upload_l1bm(&state, &host.l1).expect("upload l1");
        gpu.upload_l2bm(&state, &host.l2).expect("upload l2");
        gpu.upload_l1bi(&state, &host.lbi).expect("upload lbi");
        gpu.upload_pdm(&state, &host.pdm).expect("upload pdm");
        gpu.upload_dram(&state, &host.dram).expect("upload dram");
        gpu.upload_dar(&state, &host.dar).expect("upload dar");
        gpu.upload_darbuf(&state, &host.darbuf).expect("upload darbuf");
        gpu.upload_dar_addr(&state, host.dar_addr).expect("upload dar addr");
        gpu.upload_mats(&state, &host.mats).expect("upload mats");

        if let Err(error) = run_gpu(&gpu, &state, &parsed) {
            eprintln!("{}: GPU run failed: {error}", section.name);
            std::process::exit(3);
        }
        let cpu = sim.run(&parsed);
        if let Err(error) = cpu {
            eprintln!("{}: CPU run failed at line {}: {}", section.name, error.line, error.msg);
            std::process::exit(3);
        }
        let bad = compare(&sim, &gpu, &state, &host, section.name).unwrap_or_else(|e| {
            eprintln!("{}: compare failed: {e}", section.name);
            std::process::exit(3);
        });
        total_mismatches += bad;
        if bad == 0 {
            println!("PASS {:<34} {:>4} cases", section.name, section.cases);
        } else {
            println!("FAIL {:<34} {:>4} cases, {bad} mismatching values", section.name, section.cases);
        }
        let _ = si;
    }
    println!();
    println!("{total_cases} cases, {total_mismatches} mismatching values");
    if total_mismatches != 0 {
        std::process::exit(1);
    }
    println!("PASS: every memory, BAR, DAR, mask and forwarding register matches");
}
