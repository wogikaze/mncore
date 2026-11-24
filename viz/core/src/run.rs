//! Runs a whole program: PE statements, debug statements, and the official step count.

use std::collections::HashMap;

use crate::machine::{check_pe_access, ExecError, Machine, MaskState, MemRead, MemWrite};
use crate::mv::{DRAM_LONGS, GROUPS, PDM_LONGS};
use crate::topology::{fits, Topology};
use crate::vsm::{DebugLoc, Line, MemKind};

/// Key of one dumped value: memory name as printed by the emulator (`LM0`, `GREG1`, `TREG`,
/// `OMR`, ...), PE path (`n0c0b0m0p0`), and address. The address is the word address for
/// LM/GRF, the long word index for T (2 * cycle + k, as read by `d get $llt`), and
/// `entry * 4 + cycle` for the mask register.
pub type DumpKey = (String, String, u32);

pub struct Sim {
    pub m: Machine,
    /// Official score so far: the number of `j` + `m` instruction words.
    pub words: u64,
    /// Values printed by `d get`, keyed like `emu::parse_dump`.
    pub dump: HashMap<DumpKey, u64>,
    /// PDM and DRAM.
    pub off: crate::mv::OffChip,
}

#[derive(Debug)]
pub struct RunError {
    pub line: usize,
    /// Index of the failing statement's first instruction word in the program (the `j`/`m`
    /// words before it). With `ExecError::Range` this is the word number an E_RANGE trap
    /// reports.
    pub word: u64,
    pub msg: String,
}

impl RunError {
    /// Whether the run stopped at an access beyond a reduced capacity (`ExecError::Range`).
    pub fn is_range(&self) -> bool {
        self.msg.starts_with("E_RANGE: ")
    }
}

impl Default for Sim {
    fn default() -> Self {
        Self::new()
    }
}

impl Sim {
    /// The full chip.
    pub fn new() -> Sim {
        Sim::with_topology(Topology::FULL)
    }

    /// A chip with the units and capacities of `topo` (see `topology`).
    pub fn with_topology(topo: Topology) -> Sim {
        Sim { m: Machine::with_topology(topo), words: 0, dump: HashMap::new(), off: Default::default() }
    }

    pub fn topology(&self) -> &Topology {
        self.m.topology()
    }

    pub fn run(&mut self, lines: &[(usize, Line)]) -> Result<(), RunError> {
        for (lineno, line) in lines {
            let word = self.words;
            self.exec(line).map_err(|e| RunError { line: *lineno, word, msg: e.message() })?;
        }
        Ok(())
    }

    pub fn exec(&mut self, line: &Line) -> Result<(), ExecError> {
        self.words += line.words() as u64;
        match line {
            Line::Pe(exprs) => {
                crate::issue::check(exprs).map_err(ExecError::Assembly)?;
                self.m.step(exprs)?
            }
            Line::Nop { .. } => {}
            Line::MaskDirective { wl, targets, entry } => {
                self.m.mask_state = MaskState { wl: *wl, targets: *targets, entry: *entry };
            }
            Line::DebugSet { loc, count, payload } => self.debug_set(loc, *count, payload)?,
            Line::DebugGet { loc, count, .. } => self.debug_get(loc, *count)?,
            Line::DramSet { group, addr, payload } => {
                // The DRAM of a group without L2Bs does not exist.
                if self.topology().group_absent(*group as usize) {
                    return Ok(());
                }
                let dram = self.topology().dram;
                for (i, v) in payload.iter().enumerate() {
                    let a = addr + i as u64;
                    if !fits(a, dram, DRAM_LONGS) {
                        return Err(off_range("DRAM", *group as usize, a, dram));
                    }
                    self.off.dram[*group as usize].set(a, *v);
                }
            }
            Line::Mv(mv) => self.off.exec(&mut self.m.blocks, mv)?,
        }
        Ok(())
    }

    /// Dense indices of the PEs of the topology that a debug location selects.
    fn pes_of(topo: &Topology, loc: &DebugLoc) -> Vec<usize> {
        (0..topo.pes())
            .filter(|&i| {
                let id = topo.pe_id(i);
                loc.group.is_none_or(|g| g == id.group)
                    && loc.l2b.is_none_or(|g| g == id.l2b)
                    && loc.l1b.is_none_or(|g| g == id.l1b)
                    && loc.mab.is_none_or(|g| g == id.mab)
                    && loc.pe.is_none_or(|g| g == id.pe)
            })
            .collect()
    }

    /// Indices of the L1Bs (dense) or L2Bs of the topology that a debug location selects.
    fn blocks_of(topo: &Topology, loc: &DebugLoc, l1: bool) -> Vec<usize> {
        let n = if l1 { topo.l1bs() } else { topo.l2b };
        (0..n)
            .filter(|&i| {
                let (g, c, b) = if l1 { topo.l1b_coords(i) } else { (i / 2, i % 2, 0) };
                loc.group.is_none_or(|x| x as usize == g)
                    && loc.l2b.is_none_or(|x| x as usize == c)
                    && (!l1 || loc.l1b.is_none_or(|x| x as usize == b))
            })
            .collect()
    }

    /// Physical address of long word `a` of an L1BM (dense L1B index) or L2BM.
    fn block_addr(&self, l1: bool, unit: usize, a: usize) -> Result<usize, ExecError> {
        if l1 {
            self.m.blocks.l1_addr(unit, a)
        } else {
            self.m.blocks.l2_addr(unit, a)
        }
    }

    fn debug_set(&mut self, loc: &DebugLoc, count: u32, payload: &[u64]) -> Result<(), ExecError> {
        let topo = *self.topology();
        if matches!(loc.mem, MemKind::L1bm | MemKind::L2bm) {
            if loc.wl != 2 {
                return Err(ExecError::Unsupported("d set of L1BM/L2BM with two long word access".into()));
            }
            let l1 = loc.mem == MemKind::L1bm;
            for b in Self::blocks_of(&topo, loc, l1) {
                for i in 0..count as usize {
                    let a = self.block_addr(l1, b, loc.addr as usize + i)?;
                    let mem = if l1 { &mut self.m.blocks.l1bm[b] } else { &mut self.m.blocks.l2bm[b] };
                    mem[a] = payload[i];
                }
            }
            return Ok(());
        }
        // Payload long words per access unit: word access writes the MSB word of each long word.
        for pe in Self::pes_of(&topo, loc) {
            let p = &mut self.m.pes[pe];
            match loc.mem {
                MemKind::T => {
                    // `$lt`/`$t` sets the MSB long word of cycle i; `$llt` sets both long words.
                    let per = if loc.wl == 4 { 2 } else { 1 };
                    for i in 0..count as usize {
                        for k in 0..per {
                            let v = payload[i * per + k];
                            let w = (i % 4) * 4 + 2 * k;
                            p.t[w] = (v >> 32) as u32;
                            p.t[w + 1] = v as u32;
                        }
                    }
                }
                MemKind::Lm0 | MemKind::Lm1 | MemKind::Grf0 | MemKind::Grf1 => {
                    if let Some(t) = self.m.tracer.borrow_mut().as_mut() {
                        let name = match loc.mem {
                            MemKind::Lm0 => "lm0",
                            MemKind::Lm1 => "lm1",
                            MemKind::Grf0 => "grf0",
                            _ => "grf1",
                        };
                        let words: Vec<u32> = match loc.wl {
                            1 => payload.iter().take(count as usize).map(|v| (v >> 32) as u32).collect(),
                            _ => payload.iter().take(count as usize).flat_map(|v| [(v >> 32) as u32, *v as u32]).collect(),
                        };
                        t.pe(pe, 0, name, true, Some(loc.addr), &words);
                    }
                    match loc.wl {
                        1 => {
                            for i in 0..count as usize {
                                let a = loc.addr as usize + i;
                                check_pe_access(&topo, loc.mem, pe, a, 1)?;
                                self.m.mem.poke(loc.mem, pe, a, (payload[i] >> 32) as u32);
                            }
                        }
                        2 => {
                            for i in 0..count as usize {
                                let a = loc.addr as usize + 2 * i;
                                check_pe_access(&topo, loc.mem, pe, a, 1)?;
                                self.m.mem.poke(loc.mem, pe, a, (payload[i] >> 32) as u32);
                                check_pe_access(&topo, loc.mem, pe, a + 1, 1)?;
                                self.m.mem.poke(loc.mem, pe, a + 1, payload[i] as u32);
                            }
                        }
                        _ => return Err(ExecError::Unsupported("d set with two long word access".into())),
                    }
                }
                other => return Err(ExecError::Unsupported(format!("d set to {other:?}"))),
            }
        }
        Ok(())
    }

    fn debug_get(&mut self, loc: &DebugLoc, count: u32) -> Result<(), ExecError> {
        let topo = *self.topology();
        if matches!(loc.mem, MemKind::Dram | MemKind::Pdm) {
            // Named like the emulator. Note that the emulator's `d get $p` actually prints DRAM;
            // this prints the real PDM, so PIU values should not be compared.
            let dram = loc.mem == MemKind::Dram;
            let name = if dram { "DRAM" } else { "PIU" };
            let (cap, full) = if dram { (topo.dram, DRAM_LONGS) } else { (topo.pdm, PDM_LONGS) };
            for g in (0..GROUPS).filter(|&g| !topo.group_absent(g) && loc.group.is_none_or(|x| x as usize == g)) {
                for i in 0..count as u64 {
                    let a = loc.addr as u64 + i;
                    if !fits(a, cap, full) {
                        return Err(off_range(if dram { "DRAM" } else { "PDM" }, g, a, cap));
                    }
                    let v = if dram { self.off.dram[g].get(a) } else { self.off.pdm[g].get(a) };
                    self.dump.insert((name.into(), format!("n{g}"), a as u32), v);
                }
            }
            return Ok(());
        }
        if matches!(loc.mem, MemKind::L1bm | MemKind::L2bm) {
            if loc.wl != 2 {
                return Err(ExecError::Unsupported("d get of L1BM/L2BM with two long word access".into()));
            }
            let l1 = loc.mem == MemKind::L1bm;
            for b in Self::blocks_of(&topo, loc, l1) {
                let name = if l1 { "L1BM" } else { "L2BM" };
                let path = if l1 { topo.l1b_name(b) } else { Topology::l2b_name(b) };
                for i in 0..count as usize {
                    let a = self.block_addr(l1, b, loc.addr as usize + i)?;
                    let v = if l1 { self.m.blocks.l1bm[b][a] } else { self.m.blocks.l2bm[b][a] };
                    self.dump.insert((name.into(), path.clone(), a as u32), v);
                }
            }
            return Ok(());
        }
        let name = match loc.mem {
            MemKind::Lm0 => "LM0",
            MemKind::Lm1 => "LM1",
            MemKind::Grf0 => "GREG0",
            MemKind::Grf1 => "GREG1",
            MemKind::T => "TREG",
            MemKind::Omr => "OMR",
            other => return Err(ExecError::Unsupported(format!("d get of {other:?}"))),
        };
        for pe in Self::pes_of(&topo, loc) {
            let p = &self.m.pes[pe];
            let pname = topo.pe_id(pe).name();
            if loc.mem == MemKind::Omr {
                for i in 0..count {
                    let entry = loc.addr + i;
                    for c in 0..4u32 {
                        let v = match entry {
                            0 => 0xf,
                            1..=15 => (p.mask[entry as usize] >> (4 * c)) & 0xf,
                            _ => if (entry >> (3 - c)) & 1 == 1 { 0xf } else { 0 },
                        };
                        self.dump.insert((name.into(), pname.clone(), entry * 4 + c), v as u64);
                    }
                }
                continue;
            }
            if loc.mem == MemKind::T {
                // `$lt` reads the MSB long word of cycle i % 4; `$llt` reads both long words.
                let per = if loc.wl == 4 { 2 } else { 1 };
                for i in 0..count as usize {
                    for k in 0..per {
                        let w = (i % 4) * 4 + 2 * k;
                        let v = ((p.t[w] as u64) << 32) | p.t[w + 1] as u64;
                        let key = if per == 2 { (i * 2 + k) as u32 } else { i as u32 };
                        self.dump.insert((name.into(), pname.clone(), key), v);
                    }
                }
                continue;
            }
            if loc.wl != 2 {
                return Err(ExecError::Unsupported("d get with word or two long word access".into()));
            }
            for i in 0..count as usize {
                let a = loc.addr as usize + 2 * i;
                check_pe_access(&topo, loc.mem, pe, a, 1)?;
                check_pe_access(&topo, loc.mem, pe, a + 1, 1)?;
                let v = ((self.m.mem.peek(loc.mem, pe, a) as u64) << 32)
                    | self.m.mem.peek(loc.mem, pe, a + 1) as u64;
                self.dump.insert((name.into(), pname.clone(), a as u32), v);
            }
        }
        Ok(())
    }
}

/// E_RANGE of a PDM or DRAM address in a debug or DRAM initialization statement.
fn off_range(name: &str, group: usize, a: u64, cap: u64) -> ExecError {
    ExecError::Range(format!("{name} n{group} long word address {a} is outside the capacity of {cap} long words"))
}
