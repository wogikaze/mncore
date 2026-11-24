//! Chip topology: which L2Bs, L1Bs and MABs exist, and how large their memories are.
//!
//! [`Topology::FULL`] is the real MN-Core 2 (8 L2Bs of 8 L1Bs of 16 MABs of 4 PEs) and is what
//! `Machine::new` and `Sim::new` build. A reduced topology keeps the units counted from
//! `n0c0b0m0p0` and may shrink the memories, as an FPGA build does. `docs/topology.md` defines
//! what instructions mean on a reduced topology. In short:
//!
//! * units keep their chip numbers, so `$peid`, `$l1bid`, ... and dump locations are the real
//!   ones;
//! * a transfer to a unit that does not exist is dropped, and a unit that does not exist reads
//!   as zero when it is the source of a gather or reduction;
//! * an access beyond a reduced capacity stops the run with `ExecError::Range` (E_RANGE).
//!
//! On the full topology none of these cases can occur, so it behaves exactly as without
//! topology support.

use std::collections::HashMap;
use std::fmt;

use crate::blocks::{L1BM_LONGS, L2BM_LONGS};
use crate::machine::{
    PeId, GROUPS, GRF_WORDS, L1B_PER_L2B, L2B_PER_GROUP, LM_WORDS, MAB_PER_L1B, PE_PER_MAB,
};
use crate::mv::{DRAM_LONGS, PDM_LONGS};
use crate::run::DumpKey;

/// L2Bs on the chip (4 groups of 2).
pub const L2BS_ON_CHIP: usize = GROUPS * L2B_PER_GROUP;

/// Units and memory capacities of a (possibly reduced) chip.
///
/// Capacities are in long words (64 bits), per unit. Units are counted from the first one on
/// the chip: L2B `i` is `n{i / 2}c{i % 2}`, and each L2B has L1Bs `b0..`, each L1B MABs `m0..`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Topology {
    /// L2Bs, in the order n0c0, n0c1, n1c0, ... (1 to 8).
    pub l2b: usize,
    /// L1Bs in each L2B (1 to 8).
    pub l1b: usize,
    /// MABs in each L1B (1 to 16). Every MAB has 4 PEs.
    pub mab: usize,
    /// LM0 and LM1 of each PE (1 to 2048).
    pub lm: usize,
    /// GRF0 and GRF1 of each PE (1 to 256).
    pub grf: usize,
    /// L1BM of each L1B (1 to 8192).
    pub l1bm: usize,
    /// L2BM of each L2B (1 to 32768).
    pub l2bm: usize,
    /// PDM of each group (1 to 512 Ki).
    pub pdm: u64,
    /// DRAM of each group (1 to 512 Mi).
    pub dram: u64,
}

impl Default for Topology {
    fn default() -> Self {
        Topology::FULL
    }
}

/// Keys of a topology specification, with their largest (chip) values.
const KEYS: [(&str, u64); 10] = [
    ("l2b", L2BS_ON_CHIP as u64),
    ("l1b", L1B_PER_L2B as u64),
    ("mab", MAB_PER_L1B as u64),
    ("pe", PE_PER_MAB as u64),
    ("lm", (LM_WORDS / 2) as u64),
    ("grf", (GRF_WORDS / 2) as u64),
    ("l1bm", L1BM_LONGS as u64),
    ("l2bm", L2BM_LONGS as u64),
    ("pdm", PDM_LONGS),
    ("dram", DRAM_LONGS),
];

impl Topology {
    /// The real chip.
    pub const FULL: Topology = Topology {
        l2b: L2BS_ON_CHIP,
        l1b: L1B_PER_L2B,
        mab: MAB_PER_L1B,
        lm: LM_WORDS / 2,
        grf: GRF_WORDS / 2,
        l1bm: L1BM_LONGS,
        l2bm: L2BM_LONGS,
        pdm: PDM_LONGS,
        dram: DRAM_LONGS,
    };

    /// Parses a specification such as `l2b=1,l1b=1,mab=16,lm=256`.
    ///
    /// Keys are `l2b`, `l1b`, `mab`, `pe`, `lm`, `grf`, `l1bm`, `l2bm`, `pdm` and `dram`
    /// (memories in long words); omitted keys keep the chip's value. `pe` exists only to state
    /// the PEs per MAB, which are always 4. Values are decimal or `0x` hexadecimal, optionally
    /// followed by `Ki` or `Mi`. An empty specification or `full` is the full chip.
    pub fn parse(spec: &str) -> Result<Topology, String> {
        let spec = spec.trim();
        let mut t = Topology::FULL;
        if spec.is_empty() || spec == "full" {
            return Ok(t);
        }
        let mut seen: Vec<&str> = Vec::new();
        for item in spec.split(',') {
            let item = item.trim();
            let (key, value) = item
                .split_once('=')
                .ok_or_else(|| format!("bad topology item `{item}`: expected key=value"))?;
            let key = key.trim();
            if !KEYS.iter().any(|(k, _)| *k == key) {
                let known: Vec<&str> = KEYS.iter().map(|(k, _)| *k).collect();
                return Err(format!("unknown topology key `{key}` (known: {})", known.join(", ")));
            }
            if seen.contains(&key) {
                return Err(format!("topology key `{key}` is given twice"));
            }
            seen.push(key);
            let v = parse_value(value.trim())
                .ok_or_else(|| format!("bad value `{}` for topology key `{key}`", value.trim()))?;
            match key {
                "l2b" => t.l2b = v as usize,
                "l1b" => t.l1b = v as usize,
                "mab" => t.mab = v as usize,
                "pe" => {
                    if v != PE_PER_MAB as u64 {
                        return Err(format!("pe={v}: a MAB always has {PE_PER_MAB} PEs"));
                    }
                }
                "lm" => t.lm = v as usize,
                "grf" => t.grf = v as usize,
                "l1bm" => t.l1bm = v as usize,
                "l2bm" => t.l2bm = v as usize,
                "pdm" => t.pdm = v,
                _ => t.dram = v,
            }
        }
        t.validate()?;
        Ok(t)
    }

    /// Checks that every count and capacity is between 1 and the chip's value.
    pub fn validate(&self) -> Result<(), String> {
        let values = [
            self.l2b as u64,
            self.l1b as u64,
            self.mab as u64,
            PE_PER_MAB as u64,
            self.lm as u64,
            self.grf as u64,
            self.l1bm as u64,
            self.l2bm as u64,
            self.pdm,
            self.dram,
        ];
        for ((key, max), v) in KEYS.iter().zip(values) {
            if v == 0 || v > *max {
                return Err(format!("topology {key}={v} is outside 1..={max}"));
            }
        }
        Ok(())
    }

    pub fn is_full(&self) -> bool {
        *self == Topology::FULL
    }

    /// Number of PEs (dense indices `0..pes()`, in chip order).
    pub fn pes(&self) -> usize {
        self.mabs() * PE_PER_MAB
    }

    pub fn mabs(&self) -> usize {
        self.l1bs() * self.mab
    }

    pub fn l1bs(&self) -> usize {
        self.l2b * self.l1b
    }

    /// Groups that have at least one L2B. PDM, DRAM and DAR exist only for these.
    pub fn groups(&self) -> usize {
        self.l2b.div_ceil(L2B_PER_GROUP)
    }

    /// Capacity of LM0/LM1 in words.
    pub fn lm_words(&self) -> usize {
        self.lm * 2
    }

    /// Capacity of GRF0/GRF1 in words.
    pub fn grf_words(&self) -> usize {
        self.grf * 2
    }

    /// Chip coordinates of the PE with dense index `i`.
    pub fn pe_id(&self, i: usize) -> PeId {
        if self.mab == MAB_PER_L1B && self.l1b == L1B_PER_L2B {
            return PeId::from_index(i);
        }
        let per_l1b = self.mab * PE_PER_MAB;
        let l2b = i / (per_l1b * self.l1b);
        PeId {
            pe: (i % PE_PER_MAB) as u8,
            mab: (i / PE_PER_MAB % self.mab) as u8,
            l1b: (i / per_l1b % self.l1b) as u8,
            l2b: (l2b % L2B_PER_GROUP) as u8,
            group: (l2b / L2B_PER_GROUP) as u8,
        }
    }

    /// Dense index of the PE at chip coordinates `id`, if it exists.
    pub fn pe_index(&self, id: PeId) -> Option<usize> {
        let l2b = id.group as usize * L2B_PER_GROUP + id.l2b as usize;
        let inside = (id.l2b as usize) < L2B_PER_GROUP
            && l2b < self.l2b
            && (id.l1b as usize) < self.l1b
            && (id.mab as usize) < self.mab
            && (id.pe as usize) < PE_PER_MAB;
        inside.then(|| {
            ((l2b * self.l1b + id.l1b as usize) * self.mab + id.mab as usize) * PE_PER_MAB
                + id.pe as usize
        })
    }

    /// Chip coordinates (group, L2B in group, L1B in L2B) of the L1B with dense index `i`.
    pub fn l1b_coords(&self, i: usize) -> (usize, usize, usize) {
        let l2b = i / self.l1b;
        (l2b / L2B_PER_GROUP, l2b % L2B_PER_GROUP, i % self.l1b)
    }

    /// Location name of the L1B with dense index `i`, such as `n0c1b2`.
    pub fn l1b_name(&self, i: usize) -> String {
        let (g, c, b) = self.l1b_coords(i);
        format!("n{g}c{c}b{b}")
    }

    /// Location name of L2B `i`, such as `n1c0`.
    pub fn l2b_name(i: usize) -> String {
        format!("n{}c{}", i / L2B_PER_GROUP, i % L2B_PER_GROUP)
    }

    /// Whether MAB `m` of an L1B is on the chip but not in this topology.
    pub fn mab_absent(&self, m: usize) -> bool {
        m >= self.mab && m < MAB_PER_L1B
    }

    /// Whether L1B `b` of an L2B is on the chip but not in this topology.
    pub fn l1b_absent(&self, b: usize) -> bool {
        b >= self.l1b && b < L1B_PER_L2B
    }

    /// Whether L2B `i` (`group * 2 + l2b`) is on the chip but not in this topology.
    pub fn l2b_absent(&self, i: usize) -> bool {
        i >= self.l2b && i < L2BS_ON_CHIP
    }

    /// Whether group `g` is on the chip but has no L2B in this topology.
    pub fn group_absent(&self, g: usize) -> bool {
        g >= self.groups() && g < GROUPS
    }

    /// Whether a value of a full-chip dump (`Sim::dump`) lies inside this topology: its unit
    /// exists and its address is inside the capacity.
    ///
    /// A program that only accesses units and addresses inside the topology, and moves no data
    /// between units, prints on this topology exactly the values of its full-chip dump that
    /// this accepts.
    pub fn contains(&self, key: &DumpKey) -> bool {
        let (mem, path, addr) = key;
        let Some(c) = parse_path(path) else { return false };
        let addr = *addr as u64;
        let pe = || -> Option<PeId> {
            Some(PeId {
                group: c[0]? as u8,
                l2b: c[1]? as u8,
                l1b: c[2]? as u8,
                mab: c[3]? as u8,
                pe: c[4]? as u8,
            })
        };
        let l2b = || -> Option<usize> {
            let (g, l) = (c[0]?, c[1]?);
            (l < L2B_PER_GROUP && g * L2B_PER_GROUP + l < self.l2b).then_some(g * L2B_PER_GROUP + l)
        };
        // A dumped long word of LM/GRF is the word at `addr` and the next one.
        let words = |full: usize, cap: usize| {
            let a = addr as usize;
            [a, a + 1].iter().all(|w| fits((w & (full - 1)) as u64, cap as u64, full as u64))
        };
        match mem.as_str() {
            "LM0" | "LM1" => pe().and_then(|p| self.pe_index(p)).is_some()
                && words(LM_WORDS, self.lm_words()),
            "GREG0" | "GREG1" => pe().and_then(|p| self.pe_index(p)).is_some()
                && words(GRF_WORDS, self.grf_words()),
            "TREG" | "OMR" => pe().and_then(|p| self.pe_index(p)).is_some(),
            "L1BM" => {
                l2b().is_some()
                    && c[2].is_some_and(|b| b < self.l1b)
                    && fits(addr, self.l1bm as u64, L1BM_LONGS as u64)
            }
            "L2BM" => l2b().is_some() && fits(addr, self.l2bm as u64, L2BM_LONGS as u64),
            "DRAM" => c[0].is_some_and(|g| g < self.groups()) && fits(addr, self.dram, DRAM_LONGS),
            "PIU" => c[0].is_some_and(|g| g < self.groups()) && fits(addr, self.pdm, PDM_LONGS),
            _ => false,
        }
    }

    /// The values of a full-chip dump that lie inside this topology (see [`Self::contains`]).
    pub fn restrict(&self, dump: &HashMap<DumpKey, u64>) -> HashMap<DumpKey, u64> {
        dump.iter()
            .filter(|(k, _)| self.contains(k))
            .map(|(k, v)| (k.clone(), *v))
            .collect()
    }
}

/// Whether physical address `a` of a memory exists: a memory at its chip size `full` is never
/// reduced, so every address the chip would use is fine.
pub fn fits(a: u64, cap: u64, full: u64) -> bool {
    cap >= full || a < cap
}

fn parse_value(s: &str) -> Option<u64> {
    let (digits, scale) = if let Some(d) = s.strip_suffix("Ki") {
        (d, 1u64 << 10)
    } else if let Some(d) = s.strip_suffix("Mi") {
        (d, 1u64 << 20)
    } else {
        (s, 1)
    };
    let v = match digits.strip_prefix("0x") {
        Some(h) => u64::from_str_radix(h, 16).ok()?,
        None => digits.parse().ok()?,
    };
    v.checked_mul(scale)
}

/// Splits a location such as `n0c1b2m3p0` into its group, L2B, L1B, MAB and PE numbers.
fn parse_path(path: &str) -> Option<[Option<usize>; 5]> {
    let mut out = [None; 5];
    let mut rest = path;
    for (slot, tag) in ['n', 'c', 'b', 'm', 'p'].iter().enumerate() {
        let Some(r) = rest.strip_prefix(*tag) else { break };
        let end = r.find(|c: char| !c.is_ascii_digit()).unwrap_or(r.len());
        out[slot] = Some(r[..end].parse().ok()?);
        rest = &r[end..];
    }
    rest.is_empty().then_some(out)
}

impl fmt::Display for Topology {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "l2b={},l1b={},mab={},pe={PE_PER_MAB},lm={},grf={},l1bm={},l2bm={},pdm={},dram={}",
            self.l2b, self.l1b, self.mab, self.lm, self.grf, self.l1bm, self.l2bm, self.pdm, self.dram
        )
    }
}

impl std::str::FromStr for Topology {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Topology::parse(s)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_and_print() {
        assert_eq!(Topology::parse("").unwrap(), Topology::FULL);
        assert_eq!(Topology::parse("full").unwrap(), Topology::FULL);
        let t = Topology::parse("l2b=1,l1b=1,mab=16,lm=256,grf=0x100,l1bm=1Ki,l2bm=4Ki").unwrap();
        assert_eq!((t.l2b, t.l1b, t.mab, t.lm, t.grf, t.l1bm, t.l2bm), (1, 1, 16, 256, 256, 1024, 4096));
        assert_eq!((t.pdm, t.dram), (PDM_LONGS, DRAM_LONGS));
        assert_eq!(Topology::parse(&t.to_string()).unwrap(), t);
        assert_eq!(
            Topology::FULL.to_string(),
            "l2b=8,l1b=8,mab=16,pe=4,lm=2048,grf=256,l1bm=8192,l2bm=32768,pdm=524288,dram=536870912"
        );
        assert_eq!(t.pes(), 64);
        assert_eq!(Topology::FULL.pes(), crate::machine::PES);
    }

    #[test]
    fn bad_specifications() {
        for spec in ["l2b=0", "l2b=9", "mab=17", "lm=4096", "pe=2", "foo=1", "lm", "lm=x", "lm=1,lm=2"] {
            assert!(Topology::parse(spec).is_err(), "{spec}");
        }
    }

    #[test]
    fn coordinates_follow_the_chip() {
        let t = Topology::parse("l2b=3,l1b=2,mab=5").unwrap();
        assert_eq!(t.pes(), 3 * 2 * 5 * 4);
        assert_eq!(t.groups(), 2);
        for i in 0..t.pes() {
            let id = t.pe_id(i);
            assert_eq!(t.pe_index(id), Some(i));
        }
        // The last PE is in the third L2B, n1c0.
        assert_eq!(t.pe_id(t.pes() - 1).name(), "n1c0b1m4p3");
        assert_eq!(t.l1b_name(5), "n1c0b1");
        assert_eq!(t.pe_index(PeId { group: 1, l2b: 1, l1b: 0, mab: 0, pe: 0 }), None);
        assert_eq!(t.pe_index(PeId { group: 0, l2b: 0, l1b: 0, mab: 5, pe: 0 }), None);
        // The full chip numbers PEs as `PeId::from_index`.
        for i in [0, 1, 63, 64, 511, 512, 1023, 1024, 4095] {
            assert_eq!(Topology::FULL.pe_id(i), PeId::from_index(i));
            assert_eq!(Topology::FULL.pe_index(PeId::from_index(i)), Some(i));
        }
    }

    #[test]
    fn dump_keys_inside() {
        let t = Topology::parse("l2b=1,l1b=1,mab=1,lm=256,grf=256,l1bm=1024,l2bm=4096").unwrap();
        let key = |m: &str, p: &str, a: u32| (m.to_string(), p.to_string(), a);
        assert!(t.contains(&key("LM0", "n0c0b0m0p3", 510)));
        assert!(!t.contains(&key("LM0", "n0c0b0m0p3", 511)));
        assert!(!t.contains(&key("LM1", "n0c0b0m1p0", 0)));
        assert!(t.contains(&key("GREG1", "n0c0b0m0p0", 510)));
        assert!(t.contains(&key("TREG", "n0c0b0m0p0", 7)));
        assert!(t.contains(&key("L1BM", "n0c0b0", 1023)));
        assert!(!t.contains(&key("L1BM", "n0c0b0", 1024)));
        assert!(!t.contains(&key("L1BM", "n0c1b0", 0)));
        assert!(t.contains(&key("L2BM", "n0c0", 4095)));
        assert!(!t.contains(&key("L2BM", "n1c0", 0)));
        assert!(t.contains(&key("DRAM", "n0", 1 << 20)));
        assert!(!t.contains(&key("DRAM", "n1", 0)));
        assert!(Topology::FULL.contains(&key("LM0", "n3c1b7m15p3", 4094)));
    }
}
