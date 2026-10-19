//! Full conformance test of the GPU L1BM instruction path against the CPU `Sim`.
//!
//! The program covers every L1BM instruction expression of SDM 3.6.8: the
//! 1-long and 2-long forms of `l1bmp`, `l1bmm`, `l1bmm4`, the `@<mab>` forms,
//! the 16x1 and 4x4 reductions over all 24 RRNs with their `r` (output
//! rounding) and `e` (input extension) options, the `l1bmd` distribution and
//! gathering forms with every documented `mabdiff` sign, the `$lbi`
//! turnaround register as source and destination, and PE write masks and
//! zero-flush masks on L1BM-to-PE destinations.
//!
//! Each section is one generated program. Both machines start from the same
//! seeded LM0/LM1/GRF0/GRF1/T/mask/L1BM/L2BM/$lbi state, the CPU `Sim` and the
//! GPU run the same program, and the whole PE memories, T registers, L1BM,
//! L2BM and $lbi are compared afterwards. A mismatch exits nonzero.
//!
//! Usage: gpu_l1_conformance
//!
//! Exit codes: 0 all sections match, 1 mismatch or CPU error, 2 no GPU.

use std::collections::BTreeMap;

use mncore_sim::blocks::{L1BS, L1BM_LONGS, L2BM_LONGS, L2BS};
use mncore_sim::gpu::{
    l1_read_line_from_expr, l1_write_line_from_expr, l2_line_from_expr, Gpu, L2Line, L1ReadLine,
    L1WriteLine,
};
use mncore_sim::machine::{MaskState, GRF_WORDS, LM_WORDS, PES};
use mncore_sim::run::Sim;
use mncore_sim::vsm::{self, Line};

/// All documented RRNs (SDM 3.5.5): 9 floating-point and 15 integer ones.
const RRN_FLOAT: [&str; 9] = [
    "dfadd", "ffadd", "hfadd", "dmax", "fmax", "hmax", "dmin", "fmin", "hmin",
];
const RRN_INT: [&str; 15] = [
    "liadd", "iiadd", "siadd", "lband", "iband", "sband", "land", "iand", "sand", "lbor", "ibor",
    "sbor", "lor", "ior", "sor",
];
/// Every documented `l1bmd` mabdiff suffix: no suffix (0), then +1..+15 and -1..-15.
fn all_diffs() -> Vec<String> {
    let mut v = vec![String::new()];
    for n in 1..=15 {
        v.push(format!("+{n}"));
    }
    for n in 1..=15 {
        v.push(format!("-{n}"));
    }
    v
}

fn diff_name(diff: &str) -> String {
    if diff.is_empty() {
        "0".to_string()
    } else {
        diff.to_string()
    }
}

// Region kinds used to attribute a mismatch to a generated case.
const K_LM0: u8 = 0;
const K_LM1: u8 = 1;
const K_GRF0: u8 = 2;
const K_GRF1: u8 = 3;
const K_T: u8 = 4;
const K_L1BM: u8 = 5;
const K_L2BM: u8 = 6;
const K_LBI: u8 = 7;

#[derive(Clone)]
struct Region {
    label: String,
    kind: u8,
    start: u32,
    len: u32,
}

struct Section {
    name: &'static str,
    lines: Vec<String>,
    matrix: BTreeMap<(String, String), usize>,
    regions: Vec<Region>,
    /// For each generated case, its `(form, option)` and the half-open range of
    /// `lines` it spans. Used to name a case and to reset the seed before it.
    case_ranges: Vec<(String, String, usize, usize)>,
    cases: usize,
}

impl Section {
    fn new(name: &'static str) -> Section {
        Section {
            name,
            lines: Vec::new(),
            matrix: BTreeMap::new(),
            regions: Vec::new(),
            case_ranges: Vec::new(),
            cases: 0,
        }
    }
}

fn round_up(v: u32, align: u32) -> u32 {
    (v + align - 1) & !(align - 1)
}

struct Alloc {
    l1: u32,
    pe: [u32; 4],
}

impl Alloc {
    fn new() -> Alloc {
        Alloc {
            l1: 0,
            pe: [0; 4],
        }
    }

    fn l1(&mut self, align: u32, len: u32) -> u32 {
        self.l1 = round_up(self.l1, align.max(1));
        let a = self.l1;
        self.l1 += len;
        assert!(
            self.l1 <= L1BM_LONGS as u32,
            "L1BM address space exhausted ({} > {L1BM_LONGS})",
            self.l1
        );
        a
    }

    fn pe_mem(&mut self, mem: u8, align: u32, len: u32) -> u32 {
        let slot = &mut self.pe[mem as usize];
        *slot = round_up(*slot, align.max(1));
        let a = *slot;
        *slot += len;
        let cap = if mem < 2 { LM_WORDS } else { GRF_WORDS } as u32;
        assert!(*slot <= cap, "PE memory {mem} exhausted ({} > {cap})", *slot);
        a
    }
}

struct Gen {
    s: Section,
    alloc: Alloc,
    flip: bool,
}

impl Gen {
    fn new(name: &'static str) -> Gen {
        Gen {
            s: Section::new(name),
            alloc: Alloc::new(),
            flip: false,
        }
    }

    fn region(&mut self, label: &str, kind: u8, start: u32, len: u32) {
        self.s.regions.push(Region {
            label: label.to_string(),
            kind,
            start,
            len,
        });
    }

    fn case(&mut self, form: &str, option: &str, line: String) {
        self.case_lines(form, option, &[line]);
    }

    fn case_lines(&mut self, form: &str, option: &str, lines: &[String]) {
        let start = self.s.lines.len();
        self.s.lines.extend(lines.iter().cloned());
        let name = (form.to_string(), option.to_string());
        self.s.case_ranges.push((name.0, name.1, start, self.s.lines.len()));
        self.s.cases += 1;
        *self
            .s
            .matrix
            .entry((form.to_string(), option.to_string()))
            .or_insert(0) += 1;
    }

    fn directive(&mut self, text: &str) {
        self.s.lines.push(text.to_string());
    }

    /// Allocates a PE destination for an L1BM-to-PE read, alternating LM0/LM1.
    fn read_dst(&mut self, label: &str, wl: u8) -> (u8, u32) {
        let mem = if self.flip { 1 } else { 0 };
        self.flip = !self.flip;
        let len = if wl == 4 { 16 } else { 8 };
        let a = self.alloc.pe_mem(mem, 4, len);
        self.region(label, mem, a, len);
        (mem, a)
    }

    fn read_dst_in(&mut self, label: &str, mem: u8, wl: u8) -> u32 {
        let len = if wl == 4 { 16 } else { 8 };
        let a = self.alloc.pe_mem(mem, 4, len);
        self.region(label, mem, a, len);
        a
    }

    fn l1_dst(&mut self, label: &str, align: u32, len: u32) -> u32 {
        let a = self.alloc.l1(align, len);
        self.region(label, K_L1BM, a, len);
        a
    }

    fn l1_src(&mut self, align: u32, len: u32) -> u32 {
        self.alloc.l1(align, len)
    }

    fn finish(self) -> Section {
        self.s
    }
}

fn pe_op(mem: u8, base: u32, two: bool, ext: bool) -> String {
    let name = match mem {
        0 => "m",
        1 => "n",
        2 => "r",
        3 => "s",
        _ => "m",
    };
    format!(
        "${}{name}{base}v{}",
        if two { "ll" } else { "l" },
        if ext { "e" } else { "" }
    )
}

fn l1_op(two: bool, addr: u32) -> String {
    format!("${}{addr}", if two { "llb" } else { "lb" })
}

fn l1_dst_op(two: bool, addr: Option<u32>) -> String {
    match addr {
        Some(a) => l1_op(two, a),
        None => format!("${}lbi", if two { "ll" } else { "" }),
    }
}

// ---------------------------------------------------------------------------
// Section 1: L1BM to PE reads (SDM 3.6.8.6-3.6.8.9, 3.6.8.14, 3.6.8.15, 3.6.8.20)
// ---------------------------------------------------------------------------

fn section_read() -> Section {
    let mut g = Gen::new("read");
    // Read-only L1BM source windows, shared by the cases of the same form.
    let p1 = g.l1_src(1, 8);
    let p2 = g.l1_src(1, 8);
    let m1 = g.l1_src(4, 16);
    let m2 = g.l1_src(8, 32);
    let m41 = g.l1_src(16, 64);
    let m42 = g.l1_src(32, 128);
    let d = g.l1_src(64, 256);

    // --- l1bmp ---
    for two in [false, true] {
        let (mem, a) = g.read_dst("l1bmp", if two { 4 } else { 2 });
        let form = if two { "2L" } else { "1L" };
        g.case(
            "l1bmp",
            &format!("{form},PE {form}"),
            format!(
                "l1bmp {} {}",
                l1_op(two, if two { p2 } else { p1 }),
                pe_op(mem, a, two, false)
            ),
        );
    }
    // PE-side word length (SDM 3.6.8.3): smaller and larger than the L1 side.
    let (mem, a) = g.read_dst("l1bmp", 4);
    g.case(
        "l1bmp",
        "1L,PE 2L (LSB zero)",
        format!("l1bmp {} {}", l1_op(false, p1), pe_op(mem, a, true, false)),
    );
    let (mem, a) = g.read_dst("l1bmp", 2);
    g.case(
        "l1bmp",
        "2L,PE 1L (LSB dropped)",
        format!("l1bmp {} {}", l1_op(true, p2), pe_op(mem, a, false, false)),
    );

    // --- l1bmm ---
    for two in [false, true] {
        let (mem, a) = g.read_dst("l1bmm", if two { 4 } else { 2 });
        g.case(
            "l1bmm",
            if two { "2L" } else { "1L" },
            format!(
                "l1bmm {} {}",
                l1_op(two, if two { m2 } else { m1 }),
                pe_op(mem, a, two, false)
            ),
        );
    }
    let (mem, a) = g.read_dst("l1bmm", 4);
    g.case(
        "l1bmm",
        "1L,PE 2L",
        format!("l1bmm {} {}", l1_op(false, m1), pe_op(mem, a, true, false)),
    );
    let (mem, a) = g.read_dst("l1bmm", 2);
    g.case(
        "l1bmm",
        "2L,PE 1L",
        format!("l1bmm {} {}", l1_op(true, m2), pe_op(mem, a, false, false)),
    );

    // --- l1bmm4 ---
    for two in [false, true] {
        let (mem, a) = g.read_dst("l1bmm4", if two { 4 } else { 2 });
        g.case(
            "l1bmm4",
            if two { "2L" } else { "1L" },
            format!(
                "l1bmm4 {} {}",
                l1_op(two, if two { m42 } else { m41 }),
                pe_op(mem, a, two, false)
            ),
        );
    }
    let (mem, a) = g.read_dst("l1bmm4", 4);
    g.case(
        "l1bmm4",
        "1L,PE 2L",
        format!("l1bmm4 {} {}", l1_op(false, m41), pe_op(mem, a, true, false)),
    );
    let (mem, a) = g.read_dst("l1bmm4", 2);
    g.case(
        "l1bmm4",
        "2L,PE 1L",
        format!("l1bmm4 {} {}", l1_op(true, m42), pe_op(mem, a, false, false)),
    );

    // --- l1bmd distribution, every documented mabdiff sign ---
    for diff in all_diffs() {
        let (mem, a) = g.read_dst("l1bmd distrib", 2);
        g.case(
            "l1bmd distrib",
            &format!("mabdiff {}", diff_name(&diff)),
            format!("l1bmd{diff} {} {}", l1_op(false, d), pe_op(mem, a, false, false)),
        );
    }
    let (mem, a) = g.read_dst("l1bmd distrib", 4);
    g.case(
        "l1bmd distrib",
        "mabdiff 0,PE 2L",
        format!("l1bmd {} {}", l1_op(false, d), pe_op(mem, a, true, false)),
    );

    // Two long word L1BM operands for l1bmd: not in the SDM (distribution and
    // gathering are one long word), but the CPU accepts them and only the MSB
    // long word takes part.
    let (mem, a) = g.read_dst("l1bmd distrib 2L", 2);
    g.case(
        "l1bmd distrib",
        "L1 2L operand",
        format!("l1bmd {} {}", l1_op(true, d), pe_op(mem, a, false, false)),
    );

    // --- several PE destinations in one expression ---
    let a0 = g.read_dst_in("l1bmd multi-dst", 0, 2);
    let a1 = g.read_dst_in("l1bmd multi-dst", 1, 2);
    let a2 = g.read_dst_in("l1bmd multi-dst", 2, 2);
    g.case(
        "l1bmd distrib",
        "three destinations",
        format!(
            "l1bmd {} {} {} {}",
            l1_op(false, d),
            pe_op(0, a0, false, false),
            pe_op(1, a1, false, false),
            pe_op(2, a2, false, false)
        ),
    );

    // --- single-line write masks on PE destinations ---
    let (mem, a) = g.read_dst("l1bmm mask", 2);
    g.case(
        "l1bmm mask",
        "entry /$imr3",
        format!("l1bmm {} {}/$imr3", l1_op(false, m1), pe_op(mem, a, false, false)),
    );
    let (mem, a) = g.read_dst("l1bmm mask", 2);
    g.case(
        "l1bmm mask",
        "long-word entry /ll$imr3",
        format!("l1bmm {} {}/$llimr3", l1_op(false, m1), pe_op(mem, a, false, false)),
    );
    let (mem, a) = g.read_dst("l1bmm mask", 2);
    g.case(
        "l1bmm mask",
        "fixed pattern /0011",
        format!("l1bmm {} {}/0011", l1_op(false, m1), pe_op(mem, a, false, false)),
    );
    let (mem, a) = g.read_dst("l1bmm mask", 4);
    g.case(
        "l1bmm mask",
        "long-word pattern /ll1010",
        format!("l1bmm {} {}/ll1010", l1_op(false, m1), pe_op(mem, a, true, false)),
    );
    let a = g.read_dst_in("l1bmm mask", 0, 2);
    g.case(
        "l1bmm mask",
        "entry 0 is no mask",
        format!("l1bmm {} {}/$imr0", l1_op(false, m1), pe_op(0, a, false, false)),
    );
    // The single-line mask of one destination suppresses directive masks for
    // the whole expression; the other destinations are then unmasked.
    let a0 = g.read_dst_in("l1bmm mixed mask", 0, 2);
    let a1 = g.read_dst_in("l1bmm mixed mask", 1, 2);
    g.directive("maskm 5");
    g.case(
        "l1bmm mixed mask",
        "one masked, one directive-suppressed destination",
        format!(
            "l1bmm {} {}/$imr3 {}",
            l1_op(false, m1),
            pe_op(0, a0, false, false),
            pe_op(1, a1, false, false)
        ),
    );
    g.directive("maskm 0");

    // --- zero-flush masks on the output bus ---
    let (mem, a) = g.read_dst("l1bmm flush", 2);
    g.case(
        "l1bmm flush",
        "entry /$imr2",
        format!("l1bmm/$imr2 {} {}", l1_op(false, m1), pe_op(mem, a, false, false)),
    );
    let (mem, a) = g.read_dst("l1bmm flush", 2);
    g.case(
        "l1bmm flush",
        "long-word entry /ll$imr4",
        format!("l1bmm/ll$imr4 {} {}", l1_op(false, m1), pe_op(mem, a, false, false)),
    );
    let (mem, a) = g.read_dst("l1bmm flush", 2);
    g.case(
        "l1bmm flush",
        "pattern /0101",
        format!("l1bmm/0101 {} {}", l1_op(false, m1), pe_op(mem, a, false, false)),
    );
    let (mem, a) = g.read_dst("l1bmd flush", 2);
    g.case(
        "l1bmd flush",
        "entry /$imr5",
        format!("l1bmd/$imr5 {} {}", l1_op(false, d), pe_op(mem, a, false, false)),
    );

    // --- multi-line mask directives ---
    let a = g.read_dst_in("l1bmm directive", 0, 2);
    g.directive("maskm 6");
    g.case(
        "l1bmm directive",
        "word mask entry 6",
        format!("l1bmm {} {}", l1_op(false, m1), pe_op(0, a, false, false)),
    );
    let a = g.read_dst_in("l1bmm directive", 0, 2);
    g.directive("maskllm 7");
    g.case(
        "l1bmm directive",
        "long-word mask entry 7",
        format!("l1bmm {} {}", l1_op(false, m1), pe_op(0, a, false, false)),
    );
    g.directive("maskm 0");

    // --- $lbi turnaround reads; each read needs a preceding PE-to-L1BM step ---
    let writers = [
        ("l1bmm@", "mab 0, 2L", "l1bmm@0 $llr0v $lbi"),
        ("l1bmm@", "mab 15, 1L", "l1bmm@15 $lr0v $lbi"),
        ("l1bmm4@", "mab 2, 2L", "l1bmm4@2 $llr0v $lbi"),
        ("l1bmr", "ffadd 2L", "l1bmrffadd $llr0v $lbi"),
        ("l1bmd", "gather 2L", "l1bmd $llr0v $lbi"),
    ];
    let (mem, a) = g.read_dst("$lbi l1bmp", 2);
    g.case_lines(
        "l1bmp $lbi",
        "1L",
        &[writers[0].2.to_string(), format!("l1bmp $lbi {}", pe_op(mem, a, false, false))],
    );
    let (mem, a) = g.read_dst("$lbi l1bmp", 4);
    g.case_lines(
        "l1bmp $lbi",
        "2L",
        &[writers[1].2.to_string(), format!("l1bmp $llbi {}", pe_op(mem, a, true, false))],
    );
    let (mem, a) = g.read_dst("$lbi l1bmm", 2);
    g.case_lines(
        "l1bmm $lbi",
        "1L",
        &[writers[0].2.to_string(), format!("l1bmm $lbi {}", pe_op(mem, a, false, false))],
    );
    let (mem, a) = g.read_dst("$lbi l1bmm", 4);
    g.case_lines(
        "l1bmm $lbi",
        "2L",
        &[writers[0].2.to_string(), format!("l1bmm $llbi {}", pe_op(mem, a, true, false))],
    );
    let (mem, a) = g.read_dst("$lbi l1bmm4", 4);
    g.case_lines(
        "l1bmm4 $lbi",
        "2L",
        &[writers[2].2.to_string(), format!("l1bmm4 $llbi {}", pe_op(mem, a, true, false))],
    );
    let (mem, a) = g.read_dst("$lbi l1bmd", 2);
    g.case_lines(
        "l1bmd distrib $lbi",
        "mabdiff +1",
        &[writers[4].2.to_string(), format!("l1bmd+1 $lbi {}", pe_op(mem, a, false, false))],
    );
    let (mem, a) = g.read_dst("$lbi l1bmm4", 4);
    g.case_lines(
        "l1bmr $lbi -> l1bmm4",
        "ffadd writer",
        &[writers[3].2.to_string(), format!("l1bmm4 $llbi {}", pe_op(mem, a, true, false))],
    );
    let (mem, a) = g.read_dst("$lbi l1bmp", 2);
    g.case_lines(
        "l1bmm@ $lbi -> l1bmp",
        "mab 15 writer",
        &[writers[1].2.to_string(), format!("l1bmp $lbi {}", pe_op(mem, a, false, false))],
    );

    // --- T register destinations ---
    g.region("l1bmm $lt", K_T, 0, 16);
    g.case("l1bmm $lt", "1L", format!("l1bmm {} $lt", l1_op(false, m1)));
    g.region("l1bmp $lt", K_T, 0, 16);
    g.case("l1bmp $lt", "2L", format!("l1bmp {} $lt", l1_op(true, p2)));
    g.region("l1bmm masked $lt", K_T, 0, 16);
    g.case(
        "l1bmm $lt mask",
        "entry mask on T",
        format!("l1bmm {} $lt/$imr2", l1_op(false, m1)),
    );

    // --- several destinations, each with the same single-line mask ---
    let a0 = g.read_dst_in("l1bmd masked multi-dst", 0, 2);
    let a1 = g.read_dst_in("l1bmd masked multi-dst", 1, 2);
    let a2 = g.read_dst_in("l1bmd masked multi-dst", 2, 2);
    g.case(
        "l1bmd distrib",
        "three masked destinations",
        format!(
            "l1bmd {} {}/$imr3 {}/$imr3 {}/$imr3",
            l1_op(false, d),
            pe_op(0, a0, false, false),
            pe_op(1, a1, false, false),
            pe_op(2, a2, false, false)
        ),
    );
    let a0 = g.read_dst_in("l1bmm4 masked multi-dst", 0, 2);
    let a1 = g.read_dst_in("l1bmm4 masked multi-dst", 1, 2);
    let a2 = g.read_dst_in("l1bmm4 masked multi-dst", 2, 4);
    g.case(
        "l1bmm4",
        "three destinations",
        format!(
            "l1bmm4 {} {} {} {}",
            l1_op(false, m41),
            pe_op(0, a0, false, false),
            pe_op(1, a1, false, false),
            pe_op(2, a2, true, false)
        ),
    );

    // --- a zero-flush mask and a destination mask in the same expression ---
    let (mem, a) = g.read_dst("l1bmm flush+mask", 2);
    g.case(
        "l1bmm flush+mask",
        "entry 4 twice",
        format!(
            "l1bmm/$imr4 {} {}/$imr4",
            l1_op(false, m1),
            pe_op(mem, a, false, false)
        ),
    );
    let (mem, a) = g.read_dst("l1bmm flush+mask", 2);
    g.case(
        "l1bmm flush+mask",
        "long-word entry 5 twice",
        format!(
            "l1bmm/$llimr5 {} {}/$llimr5",
            l1_op(false, m1),
            pe_op(mem, a, false, false)
        ),
    );

    // --- 1-word PE destinations, GRF directives and flush on T ---
    let a = g.alloc.pe_mem(0, 4, 4);
    g.region("1-word PE destination", K_LM0, a, 4);
    g.case(
        "l1bmm",
        "1-word PE destination",
        format!("l1bmm {} $r{a}v", l1_op(false, m1)),
    );
    let a = g.alloc.pe_mem(2, 4, 8);
    g.region("GRF0 directive", K_GRF0, a, 8);
    g.directive("maskr 3");
    g.case(
        "l1bmm directive",
        "GRF0 word mask entry 3",
        format!("l1bmm {} {}", l1_op(false, m1), pe_op(2, a, false, false)),
    );
    g.directive("maskm 0");
    g.region("l1bmm flush T", K_T, 0, 16);
    g.case(
        "l1bmm $lt flush",
        "pattern flush into T",
        format!("l1bmm/0101 {} $lt", l1_op(false, m1)),
    );

    // --- one long word turnaround writers with two long word readers ---
    let (mem, a) = g.read_dst("$lbi l1bmm", 4);
    g.case_lines(
        "l1bmm $lbi",
        "2L reader, 1L writer (LSB retained)",
        &[
            "l1bmm@7 $lm0v $lbi".to_string(),
            format!("l1bmm $llbi {}", pe_op(mem, a, true, false)),
        ],
    );
    let (mem, a) = g.read_dst("$lbi l1bmm4", 2);
    g.case_lines(
        "l1bmm4 $lbi",
        "1L",
        &[
            "l1bmm4@2 $llr0v $lbi".to_string(),
            format!("l1bmm4 $lbi {}", pe_op(mem, a, false, false)),
        ],
    );
    let (mem, a) = g.read_dst("$lbi l1bmd", 4);
    g.case_lines(
        "l1bmd distrib $lbi",
        "PE 2L",
        &[
            "l1bmd $llr0v $lbi".to_string(),
            format!("l1bmd $lbi {}", pe_op(mem, a, true, false)),
        ],
    );

    // --- l1bmd distribution from the turnaround register, several diffs ---
    for diff in ["", "+15", "-15", "+7", "-7"] {
        let (mem, a) = g.read_dst("l1bmd distrib $lbi", 2);
        g.case_lines(
            "l1bmd distrib $lbi",
            &format!("mabdiff {}", diff_name(diff)),
            &[
                "l1bmd $llm0v $lbi".to_string(),
                format!("l1bmd{diff} $lbi {}", pe_op(mem, a, false, false)),
            ],
        );
    }

    g.finish()
}

// ---------------------------------------------------------------------------
// Section 2: PE to L1BM, 16x1 forms (SDM 3.6.8.10-3.6.8.13, 3.6.8.21)
// ---------------------------------------------------------------------------

fn section_write16() -> Section {
    let mut g = Gen::new("write16");

    // l1bmm@ over every MAB, both word lengths.
    for mab in 0..16 {
        for two in [false, true] {
            let len = if two { 32 } else { 16 };
            let a = g.l1_dst("l1bmm@", if two { 8 } else { 4 }, len);
            g.case(
                "l1bmm@",
                &format!("mab {mab},{}", if two { "2L" } else { "1L" }),
                format!(
                    "l1bmm@{mab} {} {}",
                    pe_op(0, 0, two, false),
                    l1_dst_op(two, Some(a))
                ),
            );
        }
    }

    // Cross L1BM/PE operand lengths for one MAB.
    for (dst_two, src_two) in [(false, true), (true, false)] {
        let len = if dst_two { 32 } else { 16 };
        let a = g.l1_dst("l1bmm@", if dst_two { 8 } else { 4 }, len);
        g.case(
            "l1bmm@",
            &format!(
                "mab 5,L1 {},PE {}",
                if dst_two { "2L" } else { "1L" },
                if src_two { "2L" } else { "1L" }
            ),
            format!(
                "l1bmm@5 {} {}",
                pe_op(0, 0, src_two, false),
                l1_dst_op(dst_two, Some(a))
            ),
        );
    }

    // l1bmr<rrn> over all 24 RRNs and every combination of the L1BM and PE
    // operand lengths (SDM 3.6.8.3).
    for rrn in RRN_FLOAT.iter().chain(RRN_INT.iter()) {
        for dst_two in [false, true] {
            for src_two in [false, true] {
                let len = if dst_two { 32 } else { 16 };
                let a = g.l1_dst("l1bmr", if dst_two { 8 } else { 4 }, len);
                g.case(
                    "l1bmr<rrn>",
                    &format!(
                        "{rrn},L1 {},PE {}",
                        if dst_two { "2L" } else { "1L" },
                        if src_two { "2L" } else { "1L" }
                    ),
                    format!(
                        "l1bmr{rrn} {} {}",
                        pe_op(0, 0, src_two, false),
                        l1_dst_op(dst_two, Some(a))
                    ),
                );
            }
        }
    }

    // r option (round to half), e option (half input extension) and their
    // combination, plus the half-fadd alias.
    let a = g.l1_dst("l1bmr round", 4, 16);
    g.case(
        "l1bmr round",
        "ffaddr,1L,PE 1L",
        format!("l1bmrffaddr $lm0v {}", l1_dst_op(false, Some(a))),
    );
    let a = g.l1_dst("l1bmr round", 8, 24);
    g.case(
        "l1bmr round",
        "ffaddr,2L,PE 2L",
        format!("l1bmrffaddr $llm0v {}", l1_dst_op(true, Some(a))),
    );
    let a = g.l1_dst("l1bmr round", 8, 24);
    g.case(
        "l1bmr round",
        "ffaddr,2L,PE 1L",
        format!("l1bmrffaddr $lm0v {}", l1_dst_op(true, Some(a))),
    );
    let a = g.l1_dst("l1bmr ext", 8, 32);
    g.case(
        "l1bmr ext",
        "ffadd e,2L,PE 2L",
        format!("l1bmrffadd $llm0ve {}", l1_dst_op(true, Some(a))),
    );
    let a = g.l1_dst("l1bmr ext", 4, 32);
    g.case(
        "l1bmr ext",
        "ffadd e,1L dest,PE 2L",
        format!("l1bmrffadd $llm0ve {}", l1_dst_op(false, Some(a))),
    );
    let a = g.l1_dst("l1bmr ext+round", 8, 24);
    g.case(
        "l1bmr ext+round",
        "ffaddr,2L,PE 2L e",
        format!("l1bmrffaddr $llm0ve {}", l1_dst_op(true, Some(a))),
    );
    let a = g.l1_dst("l1bmr alias", 4, 16);
    g.case(
        "l1bmr alias",
        "hfadd,1L",
        format!("l1bmrhfadd $lm0v {}", l1_dst_op(false, Some(a))),
    );
    let a = g.l1_dst("l1bmr alias", 8, 24);
    g.case(
        "l1bmr alias",
        "hfadd,2L",
        format!("l1bmrhfadd $llm0v {}", l1_dst_op(true, Some(a))),
    );
    // Cross word lengths for the round and half-fadd alias options.
    let a = g.l1_dst("l1bmr round", 4, 16);
    g.case(
        "l1bmr round",
        "ffaddr,1L,PE 2L",
        format!("l1bmrffaddr $llm0v {}", l1_dst_op(false, Some(a))),
    );
    let a = g.l1_dst("l1bmr alias", 4, 16);
    g.case(
        "l1bmr alias",
        "hfadd,1L,PE 2L",
        format!("l1bmrhfadd $llm0v {}", l1_dst_op(false, Some(a))),
    );
    let a = g.l1_dst("l1bmr alias", 8, 24);
    g.case(
        "l1bmr alias",
        "hfadd,2L,PE 1L",
        format!("l1bmrhfadd $lm0v {}", l1_dst_op(true, Some(a))),
    );
    let a = g.l1_dst("l1bmr alias", 4, 16);
    g.case(
        "l1bmr alias",
        "hfaddr,1L,PE 1L",
        format!("l1bmrhfaddr $lm0v {}", l1_dst_op(false, Some(a))),
    );
    let a = g.l1_dst("l1bmr ext+round", 8, 24);
    g.case(
        "l1bmr ext+round",
        "ffaddr e,1L dest,PE 2L",
        format!("l1bmrffaddr $llm0ve {}", l1_dst_op(false, Some(a))),
    );

    // Two long word L1BM operand to l1bmd: not in the SDM but accepted by the CPU.
    let a = g.l1_dst("l1bmd gather 2L", 64, 256);
    g.case(
        "l1bmd gather",
        "L1 2L operand (CPU-defined)",
        format!("l1bmd $lm0v {}", l1_dst_op(true, Some(a))),
    );

    // $lbi as destination: only the turnaround register is updated.
    for (form, option, line) in [
        ("l1bmm@ $lbi", "mab 0, 2L", "l1bmm@0 $llm0v $lbi"),
        ("l1bmm@ $lbi", "mab 15, 1L", "l1bmm@15 $lm0v $lbi"),
        ("l1bmr<rrn> $lbi", "ffadd, 2L", "l1bmrffadd $llm0v $lbi"),
        ("l1bmr<rrn> $lbi", "dmax, 1L", "l1bmrdmax $lm0v $lbi"),
        ("l1bmr<rrn> $lbi", "hfadd, 1L", "l1bmrhfadd $lm0v $lbi"),
        ("l1bmd gather $lbi", "2L", "l1bmd $llm0v $lbi"),
    ] {
        g.case(form, option, line.to_string());
        g.region("$lbi write", K_LBI, 0, 64);
    }

    // Other PE source memories and T as source.
    let a = g.l1_dst("l1bmm@ source", 4, 16);
    g.case(
        "l1bmm@ source",
        "GRF0",
        format!("l1bmm@3 $lr0v {}", l1_dst_op(false, Some(a))),
    );
    let a = g.l1_dst("l1bmm@ source", 4, 16);
    g.case(
        "l1bmm@ source",
        "LM1",
        format!("l1bmm@3 $ln0v {}", l1_dst_op(false, Some(a))),
    );
    let a = g.l1_dst("l1bmm@ source", 4, 16);
    g.case(
        "l1bmm@ source",
        "T (4 words)",
        format!("l1bmm@3 $lt {}", l1_dst_op(false, Some(a))),
    );
    let a = g.l1_dst("l1bmm@ source", 8, 32);
    g.case(
        "l1bmm@ source",
        "T (4 words),2L",
        format!("l1bmm@3 $lt {}", l1_dst_op(true, Some(a))),
    );
    let a = g.l1_dst("l1bmm@ source", 4, 16);
    g.case(
        "l1bmm@ source",
        "1-word PE operand",
        format!("l1bmm@3 $r0v {}", l1_dst_op(false, Some(a))),
    );
    let a = g.l1_dst("l1bmm@ source", 4, 16);
    g.case(
        "l1bmm@ source",
        "GRF1",
        format!("l1bmm@3 $ls0v {}", l1_dst_op(false, Some(a))),
    );
    let a = g.l1_dst("l1bmr source", 4, 16);
    g.case(
        "l1bmr<rrn>",
        "ffadd,1L,PE 1-word",
        format!("l1bmrffadd $r0v {}", l1_dst_op(false, Some(a))),
    );
    let a = g.l1_dst("l1bmr source", 4, 16);
    g.case(
        "l1bmr<rrn>",
        "ffadd,1L,GRF1",
        format!("l1bmrffadd $ls0v {}", l1_dst_op(false, Some(a))),
    );

    g.finish()
}

// ---------------------------------------------------------------------------
// Section 3: PE to L1BM, 4x4 forms (SDM 3.6.8.16-3.6.8.19)
// ---------------------------------------------------------------------------

fn section_write4() -> Section {
    let mut g = Gen::new("write4");

    for mab in 0..4 {
        for two in [false, true] {
            let len = if two { 128 } else { 64 };
            let a = g.l1_dst("l1bmm4@", if two { 32 } else { 16 }, len);
            g.case(
                "l1bmm4@",
                &format!("mab {mab},{}", if two { "2L" } else { "1L" }),
                format!(
                    "l1bmm4@{mab} {} {}",
                    pe_op(0, 0, two, false),
                    l1_dst_op(two, Some(a))
                ),
            );
        }
    }

    // Cross L1BM/PE operand lengths for one 4x4 MAB.
    for (dst_two, src_two) in [(false, true), (true, false)] {
        let len = if dst_two { 128 } else { 64 };
        let a = g.l1_dst("l1bmm4@", if dst_two { 32 } else { 16 }, len);
        g.case(
            "l1bmm4@",
            &format!(
                "mab 1,L1 {},PE {}",
                if dst_two { "2L" } else { "1L" },
                if src_two { "2L" } else { "1L" }
            ),
            format!(
                "l1bmm4@1 {} {}",
                pe_op(0, 0, src_two, false),
                l1_dst_op(dst_two, Some(a))
            ),
        );
    }

    for rrn in RRN_FLOAT.iter().chain(RRN_INT.iter()) {
        for two in [false, true] {
            let len = if two { 128 } else { 64 };
            let a = g.l1_dst("l1bmr4", if two { 32 } else { 16 }, len);
            g.case(
                "l1bmr4<rrn>",
                &format!(
                    "{rrn},L1 {},PE {}",
                    if two { "2L" } else { "1L" },
                    if two { "2L" } else { "1L" }
                ),
                format!(
                    "l1bmr4{rrn} {} {}",
                    pe_op(0, 0, two, false),
                    l1_dst_op(two, Some(a))
                ),
            );
        }
    }

    let a = g.l1_dst("l1bmr4 round", 16, 64);
    g.case(
        "l1bmr4 round",
        "ffaddr,1L,PE 1L",
        format!("l1bmr4ffaddr $lm0v {}", l1_dst_op(false, Some(a))),
    );
    let a = g.l1_dst("l1bmr4 round", 16, 64);
    g.case(
        "l1bmr4 round",
        "ffaddr,2L,PE 2L",
        format!("l1bmr4ffaddr $llm0v {}", l1_dst_op(true, Some(a))),
    );
    let a = g.l1_dst("l1bmr4 round", 16, 64);
    g.case(
        "l1bmr4 round",
        "ffaddr,2L,PE 1L",
        format!("l1bmr4ffaddr $lm0v {}", l1_dst_op(true, Some(a))),
    );
    let a = g.l1_dst("l1bmr4 ext", 32, 128);
    g.case(
        "l1bmr4 ext",
        "ffadd e,2L,PE 2L",
        format!("l1bmr4ffadd $llm0ve {}", l1_dst_op(true, Some(a))),
    );
    let a = g.l1_dst("l1bmr4 ext", 16, 128);
    g.case(
        "l1bmr4 ext",
        "ffadd e,1L dest,PE 2L",
        format!("l1bmr4ffadd $llm0ve {}", l1_dst_op(false, Some(a))),
    );
    let a = g.l1_dst("l1bmr4 ext+round", 16, 64);
    g.case(
        "l1bmr4 ext+round",
        "ffaddr,2L,PE 2L e",
        format!("l1bmr4ffaddr $llm0ve {}", l1_dst_op(true, Some(a))),
    );
    let a = g.l1_dst("l1bmr4 alias", 16, 64);
    g.case(
        "l1bmr4 alias",
        "hfadd,1L",
        format!("l1bmr4hfadd $lm0v {}", l1_dst_op(false, Some(a))),
    );
    let a = g.l1_dst("l1bmr4 alias", 16, 64);
    g.case(
        "l1bmr4 alias",
        "hfadd,2L",
        format!("l1bmr4hfadd $llm0v {}", l1_dst_op(true, Some(a))),
    );

    let a = g.l1_dst("l1bmm4@ source", 32, 128);
    g.case(
        "l1bmm4@ source",
        "T (4 words),2L",
        format!("l1bmm4@1 $lt {}", l1_dst_op(true, Some(a))),
    );

    for (form, option, line) in [
        ("l1bmm4@ $lbi", "mab 0, 2L", "l1bmm4@0 $llm0v $lbi"),
        ("l1bmm4@ $lbi", "mab 3, 1L", "l1bmm4@3 $lm0v $lbi"),
        ("l1bmr4<rrn> $lbi", "dmin, 2L", "l1bmr4dmin $llm0v $lbi"),
        ("l1bmr4<rrn> $lbi", "ffadd, 2L", "l1bmr4ffadd $llm0v $lbi"),
        ("l1bmr4<rrn> $lbi", "hfadd, 1L", "l1bmr4hfadd $lm0v $lbi"),
        ("l1bmr4 ext $lbi", "ffadd e, 2L", "l1bmr4ffadd $llm0ve $lbi"),
    ] {
        g.case(form, option, line.to_string());
        g.region("$lbi write", K_LBI, 0, 64);
    }

    g.finish()
}

// ---------------------------------------------------------------------------
// Section 3b: 4x4 reductions with unlike L1BM and PE operand lengths
// ---------------------------------------------------------------------------

fn section_write4cross() -> Section {
    let mut g = Gen::new("write4cross");
    for rrn in RRN_FLOAT.iter().chain(RRN_INT.iter()) {
        for (dst_two, src_two) in [(false, true), (true, false)] {
            let len = if dst_two { 128 } else { 64 };
            let a = g.l1_dst("l1bmr4", if dst_two { 32 } else { 16 }, len);
            g.case(
                "l1bmr4<rrn>",
                &format!(
                    "{rrn},L1 {},PE {}",
                    if dst_two { "2L" } else { "1L" },
                    if src_two { "2L" } else { "1L" }
                ),
                format!(
                    "l1bmr4{rrn} {} {}",
                    pe_op(0, 0, src_two, false),
                    l1_dst_op(dst_two, Some(a))
                ),
            );
        }
    }

    let a = g.l1_dst("l1bmr4 round", 16, 64);
    g.case(
        "l1bmr4 round",
        "ffaddr,1L,PE 2L",
        format!("l1bmr4ffaddr $llm0v {}", l1_dst_op(false, Some(a))),
    );
    let a = g.l1_dst("l1bmr4 round", 32, 64);
    g.case(
        "l1bmr4 round",
        "ffaddr,2L,PE 1L",
        format!("l1bmr4ffaddr $lm0v {}", l1_dst_op(true, Some(a))),
    );
    let a = g.l1_dst("l1bmr4 alias", 16, 64);
    g.case(
        "l1bmr4 alias",
        "hfadd,1L,PE 2L",
        format!("l1bmr4hfadd $llm0v {}", l1_dst_op(false, Some(a))),
    );
    let a = g.l1_dst("l1bmr4 alias", 32, 64);
    g.case(
        "l1bmr4 alias",
        "hfadd,2L,PE 1L",
        format!("l1bmr4hfadd $lm0v {}", l1_dst_op(true, Some(a))),
    );
    let a = g.l1_dst("l1bmr4 ext+round", 16, 64);
    g.case(
        "l1bmr4 ext+round",
        "ffaddr e,1L dest,PE 2L",
        format!("l1bmr4ffaddr $llm0ve {}", l1_dst_op(false, Some(a))),
    );
    let a = g.l1_dst("l1bmr4 ext", 32, 128);
    g.case(
        "l1bmr4 ext",
        "ffadd e,2L,PE 2L",
        format!("l1bmr4ffadd $llm0ve {}", l1_dst_op(true, Some(a))),
    );
    for (form, option, line) in [
        ("l1bmr4<rrn> $lbi", "ffadd, PE 1L", "l1bmr4ffadd $lm0v $lbi"),
        ("l1bmr4<rrn> $lbi", "dmax, PE 2L", "l1bmr4dmax $llm0v $lbi"),
    ] {
        g.case(form, option, line.to_string());
        g.region("$lbi write", K_LBI, 0, 64);
    }
    g.finish()
}

// ---------------------------------------------------------------------------
// Section 4: round trips (L1BM write then read, $lbi, masks, L2BM, PE lengths)
// ---------------------------------------------------------------------------

fn section_roundtrip() -> Section {
    let mut g = Gen::new("roundtrip");

    // l1bmm@ then l1bmm.
    let a = g.l1_dst("l1bmm@ -> l1bmm", 4, 16);
    let (mem, d) = g.read_dst("l1bmm@ -> l1bmm", 2);
    g.case_lines(
        "roundtrip Mwrite -> Mbcast",
        "1L",
        &[
            format!("l1bmm@5 $lm0v {}", l1_dst_op(false, Some(a))),
            format!("l1bmm {} {}", l1_op(false, a), pe_op(mem, d, false, false)),
        ],
    );
    let a = g.l1_dst("l1bmm@ -> l1bmm", 8, 32);
    let (mem, d) = g.read_dst("l1bmm@ -> l1bmm", 4);
    g.case_lines(
        "roundtrip Mwrite -> Mbcast",
        "2L",
        &[
            format!("l1bmm@5 $llm0v {}", l1_dst_op(true, Some(a))),
            format!("l1bmm {} {}", l1_op(true, a), pe_op(mem, d, true, false)),
        ],
    );

    // l1bmm4@ then l1bmm4.
    let a = g.l1_dst("l1bmm4@ -> l1bmm4", 16, 64);
    let (mem, d) = g.read_dst("l1bmm4@ -> l1bmm4", 2);
    g.case_lines(
        "roundtrip M4write -> M4bcast",
        "1L",
        &[
            format!("l1bmm4@2 $lm0v {}", l1_dst_op(false, Some(a))),
            format!("l1bmm4 {} {}", l1_op(false, a), pe_op(mem, d, false, false)),
        ],
    );
    let a = g.l1_dst("l1bmm4@ -> l1bmm4", 32, 128);
    let (mem, d) = g.read_dst("l1bmm4@ -> l1bmm4", 4);
    g.case_lines(
        "roundtrip M4write -> M4bcast",
        "2L",
        &[
            format!("l1bmm4@2 $llm0v {}", l1_dst_op(true, Some(a))),
            format!("l1bmm4 {} {}", l1_op(true, a), pe_op(mem, d, true, false)),
        ],
    );

    // l1bmr then l1bmm; l1bmr4 then l1bmm4.
    let a = g.l1_dst("l1bmr -> l1bmm", 16, 16);
    let (mem, d) = g.read_dst("l1bmr -> l1bmm", 2);
    g.case_lines(
        "roundtrip Reduce -> Mbcast",
        "1L",
        &[
            format!("l1bmrffadd $lm0v {}", l1_dst_op(false, Some(a))),
            format!("l1bmm {} {}", l1_op(false, a), pe_op(mem, d, false, false)),
        ],
    );
    let a = g.l1_dst("l1bmr -> l1bmm", 16, 32);
    let (mem, d) = g.read_dst("l1bmr -> l1bmm", 4);
    g.case_lines(
        "roundtrip Reduce -> Mbcast",
        "2L",
        &[
            format!("l1bmrffadd $llm0v {}", l1_dst_op(true, Some(a))),
            format!("l1bmm {} {}", l1_op(true, a), pe_op(mem, d, true, false)),
        ],
    );
    let a = g.l1_dst("l1bmr4 -> l1bmm4", 16, 64);
    let (mem, d) = g.read_dst("l1bmr4 -> l1bmm4", 2);
    g.case_lines(
        "roundtrip Reduce4 -> M4bcast",
        "1L",
        &[
            format!("l1bmr4ffadd $lm0v {}", l1_dst_op(false, Some(a))),
            format!("l1bmm4 {} {}", l1_op(false, a), pe_op(mem, d, false, false)),
        ],
    );
    let a = g.l1_dst("l1bmr4 -> l1bmm4", 16, 128);
    let (mem, d) = g.read_dst("l1bmr4 -> l1bmm4", 4);
    g.case_lines(
        "roundtrip Reduce4 -> M4bcast",
        "2L",
        &[
            format!("l1bmr4ffadd $llm0v {}", l1_dst_op(true, Some(a))),
            format!("l1bmm4 {} {}", l1_op(true, a), pe_op(mem, d, true, false)),
        ],
    );

    // Gather then distribute with the same mabdiff restores the PE layout.
    for diff in ["+1", "-3", "+7"] {
        let a = g.l1_dst("gather -> distrib", 64, 256);
        let (mem, d) = g.read_dst("gather -> distrib", 2);
        g.case_lines(
            "roundtrip Gather -> Distrib",
            &format!("mabdiff {diff}"),
            &[
                format!("l1bmd{diff} $lm0v {}", l1_dst_op(false, Some(a))),
                format!("l1bmd{diff} {} {}", l1_op(false, a), pe_op(mem, d, false, false)),
            ],
        );
    }

    // $lbi write then read for every form family.
    let pairs: [(&str, &str, &str, &str); 7] = [
        ("$lbi Mwrite -> Mbcast", "2L", "l1bmm@7 $llm0v $lbi", "l1bmm $llbi {}"),
        ("$lbi Mwrite -> Pbcast", "1L", "l1bmm@7 $lm0v $lbi", "l1bmp $lbi {}"),
        ("$lbi M4write -> M4bcast", "2L", "l1bmm4@1 $llm0v $lbi", "l1bmm4 $llbi {}"),
        ("$lbi Reduce -> M4bcast", "2L", "l1bmrffadd $llm0v $lbi", "l1bmm4 $llbi {}"),
        ("$lbi Reduce4 -> M4bcast", "2L", "l1bmr4ffadd $llm0v $lbi", "l1bmm4 $llbi {}"),
        ("$lbi Gather -> Distrib", "2L", "l1bmd+2 $llm0v $lbi", "l1bmd+2 $lbi {}"),
        ("$lbi hfadd -> Mbcast", "1L", "l1bmrhfadd $lm0v $lbi", "l1bmm $lbi {}"),
    ];
    for (form, option, writer, reader) in pairs {
        let (mem, d) = g.read_dst(form, if option == "1L" { 2 } else { 4 });
        let reader = reader.replace(
            "{}",
            &pe_op(mem, d, option == "2L", false),
        );
        g.case_lines(form, option, &[writer.to_string(), reader]);
        g.region("$lbi roundtrip", K_LBI, 0, 64);
    }

    // Masks, flush and several destinations on a round-tripped window.
    let a = g.l1_dst("roundtrip masked", 4, 16);
    let (mem, d) = g.read_dst("roundtrip masked", 2);
    g.case_lines(
        "roundtrip masked read",
        "entry mask",
        &[
            format!("l1bmm@1 $lm0v {}", l1_dst_op(false, Some(a))),
            format!("l1bmm {} {}/$imr3", l1_op(false, a), pe_op(mem, d, false, false)),
        ],
    );
    let a = g.l1_dst("roundtrip masked", 4, 16);
    let (mem, d) = g.read_dst("roundtrip masked", 2);
    g.case_lines(
        "roundtrip masked read",
        "flush pattern",
        &[
            format!("l1bmm@1 $lm0v {}", l1_dst_op(false, Some(a))),
            format!("l1bmm/0101 {} {}", l1_op(false, a), pe_op(mem, d, false, false)),
        ],
    );
    let a = g.l1_dst("roundtrip multi-dst", 4, 16);
    let a0 = g.read_dst_in("roundtrip multi-dst", 0, 2);
    let a1 = g.read_dst_in("roundtrip multi-dst", 1, 2);
    let a2 = g.read_dst_in("roundtrip multi-dst", 2, 2);
    g.case_lines(
        "roundtrip multi-dst read",
        "three destinations",
        &[
            format!("l1bmm@1 $lm0v {}", l1_dst_op(false, Some(a))),
            format!(
                "l1bmm {} {} {} {}",
                l1_op(false, a),
                pe_op(0, a0, false, false),
                pe_op(1, a1, false, false),
                pe_op(2, a2, false, false)
            ),
        ],
    );

    // PE-side word lengths on the write side.
    let a = g.l1_dst("PE 1L -> 2L", 8, 32);
    let (mem, d) = g.read_dst("PE 1L -> 2L", 4);
    g.case_lines(
        "roundtrip PE word length",
        "PE 1L, L1 2L (LSB zero)",
        &[
            format!("l1bmm@4 $lm0v {}", l1_dst_op(true, Some(a))),
            format!("l1bmm {} {}", l1_op(true, a), pe_op(mem, d, true, false)),
        ],
    );
    let a = g.l1_dst("PE 2L -> 1L", 4, 16);
    let (mem, d) = g.read_dst("PE 2L -> 1L", 2);
    g.case_lines(
        "roundtrip PE word length",
        "PE 2L, L1 1L (LSB dropped)",
        &[
            format!("l1bmm@4 $llm0v {}", l1_dst_op(false, Some(a))),
            format!("l1bmm {} {}", l1_op(false, a), pe_op(mem, d, false, false)),
        ],
    );

    // T as a write source and as a read destination.
    let a = g.l1_dst("T roundtrip", 8, 32);
    let (mem, d) = g.read_dst("T roundtrip", 4);
    g.case_lines(
        "roundtrip T source",
        "T -> L1BM -> PE",
        &[
            format!("l1bmm@2 $lt {}", l1_dst_op(true, Some(a))),
            format!("l1bmm {} {}", l1_op(true, a), pe_op(mem, d, true, false)),
        ],
    );
    let a = g.l1_dst("T destination", 4, 16);
    g.region("T destination", K_T, 0, 16);
    g.case_lines(
        "roundtrip T destination",
        "L1BM -> $lt",
        &[
            format!("l1bmm@2 $lm0v {}", l1_dst_op(false, Some(a))),
            format!("l1bmm {} $lt", l1_op(false, a)),
        ],
    );

    // L2BM: L1BM -> L2BM and L2BM -> L1BM.
    let a = g.l1_dst("L2BM transfer", 64, 256);
    g.region("L2BM transfer", K_L2BM, 0, 16);
    g.case_lines(
        "l2bm@ L1BM -> L2BM",
        "16 longs per cycle",
        &[
            format!("l1bmm@0 $lm0v {}", l1_dst_op(false, Some(a))),
            format!("l2bm@0 {} $lc0", l1_op(false, a)),
        ],
    );
    let a = g.l1_dst("L2BM transfer", 64, 64);
    let (mem, d) = g.read_dst("L2BM transfer", 2);
    g.case_lines(
        "l2bmb L2BM -> L1BM",
        "16 longs per cycle",
        &[
            format!("l2bmb $lc0 {}", l1_dst_op(false, Some(a))),
            format!("l1bmm {} {}", l1_op(false, a), pe_op(mem, d, false, false)),
        ],
    );

    g.finish()
}

// ---------------------------------------------------------------------------
// Section 5: every documented l1bmd gathering mabdiff
// ---------------------------------------------------------------------------

fn section_gather() -> Section {
    let mut g = Gen::new("gather");
    for diff in all_diffs() {
        let a = g.l1_dst("l1bmd gather", 64, 256);
        g.case(
            "l1bmd gather",
            &format!("mabdiff {}", diff_name(&diff)),
            format!("l1bmd{diff} $lm0v {}", l1_dst_op(false, Some(a))),
        );
    }
    // A two long word PE operand to a one long word L1BM destination drops
    // its LSB (SDM 3.6.8.3).
    let a = g.l1_dst("l1bmd gather", 64, 256);
    g.case(
        "l1bmd gather",
        "PE 2L (LSB dropped)",
        format!("l1bmd $llm0v {}", l1_dst_op(false, Some(a))),
    );

    g.finish()
}

// ---------------------------------------------------------------------------
// Section 6: address wrapping at the end of the 8,192 long word L1BM
// ---------------------------------------------------------------------------

fn l1_wrap_region(g: &mut Gen, label: &str, addr: u32, len: u32) {
    let end = addr + len;
    if end <= L1BM_LONGS as u32 {
        g.region(label, K_L1BM, addr, len);
    } else {
        let first = L1BM_LONGS as u32 - addr;
        g.region(label, K_L1BM, addr, first);
        g.region(label, K_L1BM, 0, end - L1BM_LONGS as u32);
    }
}

fn section_wrap() -> Section {
    let mut g = Gen::new("wrap");

    let (mem, a) = g.read_dst("wrap l1bmp", 2);
    g.case(
        "wrap",
        "l1bmp $lb8190",
        format!("l1bmp $lb8190 {}", pe_op(mem, a, false, false)),
    );
    let (mem, a) = g.read_dst("wrap l1bmm", 2);
    g.case(
        "wrap",
        "l1bmm $lb8188",
        format!("l1bmm $lb8188 {}", pe_op(mem, a, false, false)),
    );
    let (mem, a) = g.read_dst("wrap l1bmm4", 2);
    g.case(
        "wrap",
        "l1bmm4 $lb8176",
        format!("l1bmm4 $lb8176 {}", pe_op(mem, a, false, false)),
    );
    let (mem, a) = g.read_dst("wrap l1bmd", 2);
    g.case(
        "wrap",
        "l1bmd $lb8128",
        format!("l1bmd $lb8128 {}", pe_op(mem, a, false, false)),
    );

    // Writes crossing the end of L1BM.
    g.case(
        "wrap",
        "l1bmm@ $lb8188",
        "l1bmm@0 $lm0v $lb8188".to_string(),
    );
    l1_wrap_region(&mut g, "wrap l1bmm@", 8188, 16);
    g.case(
        "wrap",
        "l1bmm@ $llb8184",
        "l1bmm@0 $llm0v $llb8184".to_string(),
    );
    l1_wrap_region(&mut g, "wrap l1bmm@ 2L", 8184, 32);
    g.case(
        "wrap",
        "l1bmr $lb8188",
        "l1bmrffadd $lm0v $lb8188".to_string(),
    );
    l1_wrap_region(&mut g, "wrap l1bmr", 8188, 16);
    g.case(
        "wrap",
        "l1bmr $llb8184",
        "l1bmrffadd $llm0v $llb8184".to_string(),
    );
    l1_wrap_region(&mut g, "wrap l1bmr 2L", 8184, 32);
    g.case(
        "wrap",
        "l1bmr4 $lb8176",
        "l1bmr4ffadd $lm0v $lb8176".to_string(),
    );
    l1_wrap_region(&mut g, "wrap l1bmr4", 8176, 64);
    g.case(
        "wrap",
        "l1bmr4 $llb8160",
        "l1bmr4ffadd $llm0v $llb8160".to_string(),
    );
    l1_wrap_region(&mut g, "wrap l1bmr4 2L", 8160, 128);
    g.case(
        "wrap",
        "l1bmm4@ $lb8176",
        "l1bmm4@0 $lm0v $lb8176".to_string(),
    );
    l1_wrap_region(&mut g, "wrap l1bmm4@", 8176, 64);
    g.case(
        "wrap",
        "l1bmd gather $lb8128",
        "l1bmd+1 $lm0v $lb8128".to_string(),
    );
    l1_wrap_region(&mut g, "wrap l1bmd gather", 8128, 256);

    // A write/read round trip across the wrap point.
    let d = g.alloc.pe_mem(0, 4, 8);
    g.region("wrap l1bmm@ roundtrip", K_LM0, d, 8);
    g.case_lines(
        "wrap",
        "l1bmm@ $lb8188 -> l1bmm $lb8188",
        &[
            "l1bmm@0 $lm0v $lb8188".to_string(),
            format!("l1bmm $lb8188 {}", pe_op(0, d, false, false)),
        ],
    );
    l1_wrap_region(&mut g, "wrap l1bmm@ roundtrip", 8188, 16);

    g.finish()
}

// ---------------------------------------------------------------------------
// Seeded state and comparison
// ---------------------------------------------------------------------------

struct Seed {
    lm0: Vec<u32>,
    lm1: Vec<u32>,
    grf0: Vec<u32>,
    grf1: Vec<u32>,
    t: Vec<u32>,
    mask: Vec<u32>,
    l1bm: Vec<u64>,
    l2bm: Vec<u64>,
    lbi: Vec<u64>,
}

fn make_seed(start: u64) -> Seed {
    let mut state = start | 1;
    let mut next = || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state
    };
    let lm_len = PES * LM_WORDS;
    let grf_len = PES * GRF_WORDS;
    Seed {
        lm0: (0..lm_len).map(|_| next() as u32).collect(),
        lm1: (0..lm_len).map(|_| next() as u32).collect(),
        grf0: (0..grf_len).map(|_| next() as u32).collect(),
        grf1: (0..grf_len).map(|_| next() as u32).collect(),
        t: (0..PES * 16).map(|_| next() as u32).collect(),
        mask: (0..PES * 16).map(|_| (next() as u32 & 0xffff) | 1).collect(),
        l1bm: (0..L1BS * L1BM_LONGS).map(|_| next()).collect(),
        l2bm: (0..L2BS * L2BM_LONGS).map(|_| next()).collect(),
        lbi: (0..L1BS * 4 * 128).map(|_| next()).collect(),
    }
}

fn install_cpu(sim: &mut Sim, seed: &Seed) {
    sim.m.mem.lm0.copy_from_slice(&seed.lm0);
    sim.m.mem.lm1.copy_from_slice(&seed.lm1);
    sim.m.mem.grf0.copy_from_slice(&seed.grf0);
    sim.m.mem.grf1.copy_from_slice(&seed.grf1);
    for (l1b, words) in sim.m.blocks.l1bm.iter_mut().enumerate() {
        for (addr, value) in words.iter_mut().enumerate() {
            *value = seed.l1bm[l1b * L1BM_LONGS + addr];
        }
    }
    for (l2b, words) in sim.m.blocks.l2bm.iter_mut().enumerate() {
        for (addr, value) in words.iter_mut().enumerate() {
            *value = seed.l2bm[l2b * L2BM_LONGS + addr];
        }
    }
    for l1b in 0..L1BS {
        for c in 0..4 {
            for a in 0..128 {
                sim.m.blocks.lbi[l1b][c][a] = seed.lbi[(l1b * 4 + c) * 128 + a];
            }
        }
    }
    sim.m.blocks.lbi_error = None;
    for (pe, p) in sim.m.pes.iter_mut().enumerate() {
        for e in 0..16 {
            p.mask[e] = seed.mask[pe * 16 + e] as u16;
        }
        p.t.copy_from_slice(&seed.t[pe * 16..pe * 16 + 16]);
    }
}

fn install_gpu(gpu: &Gpu, state: &mncore_sim::gpu::GpuState, seed: &Seed) -> Result<(), String> {
    gpu.upload_state(state, &seed.lm0, &seed.lm1, &seed.grf0, &seed.grf1)?;
    gpu.upload_l1bm(state, &seed.l1bm)?;
    gpu.upload_l2bm(state, &seed.l2bm)?;
    gpu.upload_l1bi(state, &seed.lbi)?;
    gpu.upload_mask(state, &seed.mask)?;
    gpu.upload_t(state, &seed.t)
}

enum Action {
    Read(L1ReadLine),
    Write(L1WriteLine),
    L2(L2Line),
}

fn action_of(expr: &mncore_sim::vsm::Expr, mask: MaskState) -> Option<Action> {
    if let Some(line) = l1_read_line_from_expr(expr, mask) {
        return Some(Action::Read(line));
    }
    if let Some(line) = l1_write_line_from_expr(expr) {
        return Some(Action::Write(line));
    }
    if let Some(line) = l2_line_from_expr(expr) {
        return Some(Action::L2(line));
    }
    None
}

fn mem_width(kind: u8) -> usize {
    match kind {
        K_LM0 | K_LM1 => LM_WORDS,
        K_GRF0 | K_GRF1 => GRF_WORDS,
        K_T => 16,
        K_L1BM => L1BM_LONGS,
        K_L2BM => L2BM_LONGS,
        K_LBI => 128, // two long-word planes per cycle
        8 => 16, // mask register entries per PE
        _ => 256,
    }
}

fn label_for(regions: &[Region], kind: u8, index: usize) -> String {
    let width = mem_width(kind);
    let addr = (index % width) as u32;
    regions
        .iter()
        .rev()
        .find(|r| r.kind == kind && addr >= r.start && addr < r.start + r.len)
        .map(|r| r.label.clone())
        .unwrap_or_else(|| "<seed>".to_string())
}

fn mismatch_report(
    name: &str,
    kind: u8,
    cpu: &[u32],
    gpu: &[u32],
    regions: &[Region],
    detail: bool,
) -> (usize, BTreeMap<String, usize>) {
    let mut total = 0usize;
    let mut by_label: BTreeMap<String, usize> = BTreeMap::new();
    let width = mem_width(kind);
    for (i, (a, b)) in cpu.iter().zip(gpu).enumerate() {
        if a == b {
            continue;
        }
        total += 1;
        let label = label_for(regions, kind, i);
        *by_label.entry(label.clone()).or_insert(0) += 1;
        if detail && total <= 5 {
            println!(
                "  {name} mismatch: pe {} addr {} cpu {:08x} gpu {:08x} ({label})",
                i / width,
                i % width,
                a,
                b
            );
        }
    }
    (total, by_label)
}

fn mismatch_report_u64(
    name: &str,
    kind: u8,
    cpu: &[u64],
    gpu: &[u64],
    regions: &[Region],
    detail: bool,
) -> (usize, BTreeMap<String, usize>) {
    let mut total = 0usize;
    let mut by_label: BTreeMap<String, usize> = BTreeMap::new();
    let width = mem_width(kind);
    for (i, (a, b)) in cpu.iter().zip(gpu).enumerate() {
        if a == b {
            continue;
        }
        total += 1;
        let label = label_for(regions, kind, i);
        *by_label.entry(label.clone()).or_insert(0) += 1;
        if detail && total <= 5 {
            println!(
                "  {name} mismatch: index {} (addr {}) cpu {:016x} gpu {:016x} ({label})",
                i,
                i % width,
                a,
                b
            );
        }
    }
    (total, by_label)
}

struct SectionRun {
    actions: usize,
    lines: usize,
    mismatches: usize,
    labels: BTreeMap<String, usize>,
}

/// Runs `lines` on the CPU `Sim` and on the GPU, both starting from `seed`, and
/// compares every PE memory, T, L1BM, L2BM, `$lbi` and mask register.
///
/// `label` names the unit under test (one case or a whole section) in errors.
fn run_case(
    gpu: &Gpu,
    section: &Section,
    lines: &[String],
    seed: &Seed,
    label: &str,
) -> Result<SectionRun, String> {
    let source = lines.join("\n");
    let program = vsm::parse(&source).map_err(|e| {
        let text = lines.get(e.line.saturating_sub(1)).cloned().unwrap_or_default();
        format!(
            "section {}: parse error at line {}: {} (source: {text})",
            section.name, e.line, e.msg
        )
    })?;

    // CPU reference.
    let mut sim = Sim::new();
    install_cpu(&mut sim, seed);
    sim.run(&program).map_err(|e| {
        let text = lines.get(e.line.saturating_sub(1)).cloned().unwrap_or_default();
        format!(
            "section {}: {label}: CPU error at line {}: {} (source: {text})",
            section.name, e.line, e.msg
        )
    })?;

    // GPU. The state is rewritten from the seed so that every case starts from
    // exactly the state the CPU reference saw.
    let state = gpu
        .allocate_state()
        .map_err(|e| format!("allocate_state: {e}"))?;
    install_gpu(gpu, &state, seed)
        .map_err(|e| format!("section {}: {label}: upload: {e}", section.name))?;
    let mut mask = MaskState::default();
    let mut actions = 0usize;
    for (lineno, line) in &program {
        match line {
            Line::Nop { .. } => {}
            Line::MaskDirective { wl, targets, entry } => {
                mask = MaskState {
                    wl: *wl,
                    targets: *targets,
                    entry: *entry,
                };
            }
            Line::Pe(exprs) => {
                for expr in exprs {
                    let action = action_of(expr, mask).ok_or_else(|| {
                        format!(
                            "section {}: line {lineno}: no GPU descriptor for `{}`",
                            section.name, expr.text
                        )
                    })?;
                    let result = match &action {
                        Action::Read(l) => gpu.run_l1_read_line(&state, l),
                        Action::Write(l) => gpu.run_l1_write_line(&state, l),
                        Action::L2(l) => gpu.run_l2_line(&state, l),
                    };
                    result.map_err(|e| {
                        format!(
                            "section {}: line {lineno}: `{}`: {e}",
                            section.name, expr.text
                        )
                    })?;
                    actions += 1;
                }
            }
            other => {
                return Err(format!(
                    "section {}: unsupported line {other:?}",
                    section.name
                ));
            }
        }
    }
    gpu.sync()
        .map_err(|e| format!("section {}: sync: {e}", section.name))?;
    // Compare every PE memory, T, L1BM, L2BM and $lbi.
    let mut out = (
        vec![0u32; PES * LM_WORDS],
        vec![0u32; PES * LM_WORDS],
        vec![0u32; PES * GRF_WORDS],
        vec![0u32; PES * GRF_WORDS],
    );
    gpu.download_state(&state, &mut out.0, &mut out.1, &mut out.2, &mut out.3)
        .map_err(|e| format!("section {}: download: {e}", section.name))?;
    let gpu_t = gpu.download_t(&state).map_err(|e| e.to_string())?;
    let gpu_l1 = gpu.download_l1bm(&state).map_err(|e| e.to_string())?;
    let gpu_l2 = gpu.download_l2bm(&state).map_err(|e| e.to_string())?;
    let gpu_lbi = gpu.download_l1bi(&state).map_err(|e| e.to_string())?;
    let gpu_mask = gpu.download_mask(&state).map_err(|e| e.to_string())?;

    let mut mismatches = 0usize;
    let mut labels: BTreeMap<String, usize> = BTreeMap::new();
    let detail = true;
    for (name, kind, cpu, gpu) in [
        ("lm0", K_LM0, sim.m.mem.lm0.as_slice(), out.0.as_slice()),
        ("lm1", K_LM1, sim.m.mem.lm1.as_slice(), out.1.as_slice()),
        ("grf0", K_GRF0, sim.m.mem.grf0.as_slice(), out.2.as_slice()),
        ("grf1", K_GRF1, sim.m.mem.grf1.as_slice(), out.3.as_slice()),
    ] {
        let (n, l) = mismatch_report(name, kind, cpu, gpu, &section.regions, detail);
        mismatches += n;
        for (k, v) in l {
            *labels.entry(k).or_insert(0) += v;
        }
    }
    let cpu_t: Vec<u32> = sim.m.pes.iter().flat_map(|p| p.t.iter().copied()).collect();
    let (n, l) = mismatch_report("t", K_T, &cpu_t, &gpu_t, &section.regions, detail);
    mismatches += n;
    for (k, v) in l {
        *labels.entry(k).or_insert(0) += v;
    }
    let cpu_l1: Vec<u64> = sim
        .m
        .blocks
        .l1bm
        .iter()
        .flat_map(|w| w.iter().copied())
        .collect();
    let (n, l) = mismatch_report_u64("l1bm", K_L1BM, &cpu_l1, &gpu_l1, &section.regions, detail);
    mismatches += n;
    for (k, v) in l {
        *labels.entry(k).or_insert(0) += v;
    }
    let cpu_l2: Vec<u64> = sim
        .m
        .blocks
        .l2bm
        .iter()
        .flat_map(|w| w.iter().copied())
        .collect();
    let (n, l) = mismatch_report_u64("l2bm", K_L2BM, &cpu_l2, &gpu_l2, &section.regions, detail);
    mismatches += n;
    for (k, v) in l {
        *labels.entry(k).or_insert(0) += v;
    }
    let mut cpu_lbi: Vec<u64> = Vec::with_capacity(L1BS * 4 * 128);
    for l1b in 0..L1BS {
        for c in 0..4 {
            cpu_lbi.extend(sim.m.blocks.lbi[l1b][c].iter().copied());
        }
    }
    let (n, l) = mismatch_report_u64("lbi", K_LBI, &cpu_lbi, &gpu_lbi, &section.regions, detail);
    mismatches += n;
    for (k, v) in l {
        *labels.entry(k).or_insert(0) += v;
    }
    let cpu_mask: Vec<u32> = sim
        .m
        .pes
        .iter()
        .flat_map(|p| p.mask.iter().map(|&v| v as u32))
        .collect();
    let (n, l) = mismatch_report("mask", 8, &cpu_mask, &gpu_mask, &section.regions, detail);
    mismatches += n;
    for (k, v) in l {
        *labels.entry(k).or_insert(0) += v;
    }

    Ok(SectionRun {
        actions,
        lines: program.len(),
        mismatches,
        labels,
    })
}

/// A selected run of cases `START_CASE..END_CASE` (end exclusive) of one
/// section, where cases are numbered from 1 in generation order within a
/// section. `START_CASE`/`END_CASE` unset or `0` select the whole section.
struct CaseRange {
    start: usize,
    end: usize,
}

impl CaseRange {
    fn from_env(section: &Section) -> CaseRange {
        let read = |name: &str| std::env::var(name).ok().and_then(|v| v.parse::<usize>().ok());
        let start = read("START_CASE").unwrap_or(1).max(1);
        let end = read("END_CASE").unwrap_or(usize::MAX);
        CaseRange {
            start,
            end: end.min(section.case_ranges.len() + 1),
        }
    }

    fn contains(&self, case_index: usize) -> bool {
        case_index >= self.start && case_index < self.end
    }
}

/// Runs every case of a section from the seed. Each case starts from the seed
/// state on both machines, so a mismatch belongs to that case alone.
fn run_section(
    gpu: &Gpu,
    section: &Section,
    seed: &Seed,
    range: &CaseRange,
    detail: bool,
) -> SectionReport {
    let mut report = SectionReport::default();
    report.selected = (range.start..range.end)
        .filter(|&i| i <= section.case_ranges.len())
        .count();
    for (index, (form, option, start, end)) in section.case_ranges.iter().enumerate() {
        let case_index = index + 1;
        if !range.contains(case_index) {
            continue;
        }
        report.cases += 1;
        let label = format!("case {case_index} {form} / {option}");
        match run_case(gpu, section, &section.lines[*start..*end], seed, &label) {
            Ok(run) => {
                report.actions += run.actions;
                report.lines += run.lines;
                report.mismatches += run.mismatches;
                if run.mismatches == 0 {
                    report.passed += 1;
                } else {
                    report.failed += 1;
                    for (k, v) in run.labels {
                        *report.labels.entry(k).or_insert(0) += v;
                    }
                    report.failures.push((case_index, label, run.mismatches));
                    if detail {
                        println!(
                            "    case {case_index}: {form} / {option}  MISMATCH ({} values)",
                            run.mismatches
                        );
                    }
                }
            }
            Err(error) => {
                report.failed += 1;
                report.errors.push(error);
            }
        }
    }
    report
}

#[derive(Default)]
struct SectionReport {
    cases: usize,
    selected: usize,
    passed: usize,
    failed: usize,
    actions: usize,
    lines: usize,
    mismatches: usize,
    labels: BTreeMap<String, usize>,
    failures: Vec<(usize, String, usize)>,
    errors: Vec<String>,
}

fn main() {
    let sections = [
        section_read(),
        section_write16(),
        section_write4(),
        section_write4cross(),
        section_roundtrip(),
        section_gather(),
        section_wrap(),
    ];
    let seed_count: u64 = std::env::args()
        .nth(1)
        .and_then(|s| s.parse().ok())
        .unwrap_or(3);

    println!(
        "GPU L1BM conformance: {} sections, {seed_count} seed(s)",
        sections.len()
    );
    if let Ok(range) = std::env::var("START_CASE").or_else(|_| std::env::var("END_CASE")) {
        println!("case range: {range} (START_CASE={:?}, END_CASE={:?})",
            std::env::var("START_CASE"), std::env::var("END_CASE"));
    }
    println!();
    println!("{:<30} {:<42} {:>5}", "form", "option", "cases");
    println!("{}", "-".repeat(80));
    let mut matrix_cases = 0usize;
    for s in &sections {
        for ((form, option), count) in &s.matrix {
            println!("{form:<30} {option:<42} {count:>5}");
            matrix_cases += count;
        }
    }
    println!("{}", "-".repeat(80));
    println!("generated case entries: {matrix_cases}");
    println!();

    let gpu = match Gpu::new() {
        Ok(gpu) => gpu,
        Err(error) => {
            eprintln!("gpu unavailable: {error}");
            std::process::exit(2);
        }
    };

    let mut failed = 0usize;
    let mut total_cases = 0usize;
    let mut total_mismatches = 0usize;
    let mut total_actions = 0usize;
    let mut total_lines = 0usize;
    let mut all_failures: Vec<(u64, usize, String, usize)> = Vec::new();
    for seed_index in 0..seed_count {
        let seed = make_seed(
            0x0123_4567_89ab_cdefu64
                ^ seed_index.wrapping_mul(0x9e37_79b9_7f4a_7c15),
        );
        println!("seed {seed_index}:");
        for section in &sections {
            if let Ok(only) = std::env::var("ONLY") {
                if !section.name.contains(&only) { continue; }
            }
            let range = CaseRange::from_env(section);
            let report = run_section(&gpu, section, &seed, &range, true);
            total_cases += report.cases;
            total_actions += report.actions;
            total_lines += report.lines;
            total_mismatches += report.mismatches;
            for error in &report.errors {
                failed += 1;
                eprintln!("  {error}");
            }
            if report.failed == 0 && report.errors.is_empty() {
                println!(
                    "  section {:<12} cases {:>4}  expressions {:>4}  lines {:>4}  ok",
                    section.name, report.cases, report.actions, report.lines
                );
            } else {
                failed += report.failed.max(1);
                println!(
                    "  section {:<12} cases {:>4}  passed {:>4}  failed {:>4}  expressions {:>4}  MISMATCH ({})",
                    section.name, report.cases, report.passed, report.failed, report.actions, report.mismatches
                );
                for (label, count) in &report.labels {
                    println!("    {count:>8} mismatches in {label}");
                }
                for (case_index, label, count) in report.failures {
                    all_failures.push((seed_index, case_index, format!("{}: {label}", section.name), count));
                }
            }
        }
    }

    println!();
    if !all_failures.is_empty() {
        println!("failing cases (re-run one with START_CASE=<n> END_CASE=<n+1> ONLY=<section>):");
        for (seed_index, case_index, label, count) in &all_failures {
            println!("  seed {seed_index} case {case_index:>4}  {label}  ({count} values)");
        }
        println!();
    }
    if total_mismatches == 0 && failed == 0 {
        println!(
            "OK: {} sections x {seed_count} seeds, {total_cases} cases, {total_actions} expressions, {total_lines} lines, 0 mismatches (PE memories, T, L1BM, L2BM, $lbi)",
            sections.len()
        );
    } else {
        println!(
            "FAIL: {failed} case runs failed, {total_mismatches} mismatched values"
        );
        std::process::exit(1);
    }
}
