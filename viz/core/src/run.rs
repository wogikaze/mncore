//! Runs a whole program: PE statements, debug statements, and the official step count.

use std::collections::HashMap;

use crate::emu::DumpKey;
use crate::machine::{ExecError, Machine, MaskState, PeId, PES};
use crate::vsm::{DebugLoc, Line, MemKind};

pub struct Sim {
    pub m: Machine,
    /// Official score so far: the number of `j` + `m` instruction words.
    pub words: u64,
    /// Values printed by `d get`, keyed like `emu::parse_dump`.
    pub dump: HashMap<DumpKey, u64>,
    /// DRAM contents written by `r` lines: (group, long word address) -> value.
    pub dram: HashMap<(u8, u64), u64>,
}

#[derive(Debug)]
pub struct RunError {
    pub line: usize,
    pub msg: String,
}

impl Default for Sim {
    fn default() -> Self {
        Self::new()
    }
}

impl Sim {
    pub fn new() -> Sim {
        Sim { m: Machine::new(), words: 0, dump: HashMap::new(), dram: HashMap::new() }
    }

    pub fn run(&mut self, lines: &[(usize, Line)]) -> Result<(), RunError> {
        for (lineno, line) in lines {
            self.exec(line).map_err(|e| RunError { line: *lineno, msg: e.message() })?;
        }
        Ok(())
    }

    pub fn exec(&mut self, line: &Line) -> Result<(), ExecError> {
        self.words += line.words() as u64;
        match line {
            Line::Pe(exprs) => self.m.step(exprs)?,
            Line::Nop { .. } => {}
            Line::MaskDirective { wl, targets, entry } => {
                self.m.mask_state = MaskState { wl: *wl, targets: *targets, entry: *entry };
            }
            Line::DebugSet { loc, count, payload } => self.debug_set(loc, *count, payload)?,
            Line::DebugGet { loc, count, .. } => self.debug_get(loc, *count)?,
            Line::DramSet { group, addr, payload } => {
                for (i, v) in payload.iter().enumerate() {
                    self.dram.insert((*group, addr + i as u64), *v);
                }
            }
            Line::Mv(text) => return Err(ExecError::Unsupported(format!("MV instruction `{text}`"))),
        }
        Ok(())
    }

    fn pes_of(loc: &DebugLoc) -> Vec<usize> {
        (0..PES)
            .filter(|&i| {
                let id = PeId::from_index(i);
                loc.group.is_none_or(|g| g == id.group)
                    && loc.l2b.is_none_or(|g| g == id.l2b)
                    && loc.l1b.is_none_or(|g| g == id.l1b)
                    && loc.mab.is_none_or(|g| g == id.mab)
                    && loc.pe.is_none_or(|g| g == id.pe)
            })
            .collect()
    }

    /// Indices of the L1Bs (or L2Bs) a debug location selects.
    fn blocks_of(loc: &DebugLoc, l1: bool) -> Vec<usize> {
        let n = if l1 { crate::blocks::L1BS } else { crate::blocks::L2BS };
        (0..n)
            .filter(|&i| {
                let (g, c, b) = if l1 { (i / 16, i / 8 % 2, i % 8) } else { (i / 2, i % 2, 0) };
                loc.group.is_none_or(|x| x as usize == g)
                    && loc.l2b.is_none_or(|x| x as usize == c)
                    && (!l1 || loc.l1b.is_none_or(|x| x as usize == b))
            })
            .collect()
    }

    fn debug_set(&mut self, loc: &DebugLoc, count: u32, payload: &[u64]) -> Result<(), ExecError> {
        if matches!(loc.mem, MemKind::L1bm | MemKind::L2bm) {
            if loc.wl != 2 {
                return Err(ExecError::Unsupported("d set of L1BM/L2BM with two long word access".into()));
            }
            let l1 = loc.mem == MemKind::L1bm;
            for b in Self::blocks_of(loc, l1) {
                let mem = if l1 { &mut self.m.blocks.l1bm[b] } else { &mut self.m.blocks.l2bm[b] };
                let len = mem.len();
                for i in 0..count as usize {
                    mem[(loc.addr as usize + i) % len] = payload[i];
                }
            }
            return Ok(());
        }
        // Payload long words per access unit: word access writes the MSB word of each long word.
        for pe in Self::pes_of(loc) {
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
                    let m = p.mem_mut(loc.mem);
                    match loc.wl {
                        1 => {
                            for i in 0..count as usize {
                                m.set(loc.addr as usize + i, (payload[i] >> 32) as u32);
                            }
                        }
                        2 => {
                            for i in 0..count as usize {
                                m.set(loc.addr as usize + 2 * i, (payload[i] >> 32) as u32);
                                m.set(loc.addr as usize + 2 * i + 1, payload[i] as u32);
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
        if matches!(loc.mem, MemKind::L1bm | MemKind::L2bm) {
            if loc.wl != 2 {
                return Err(ExecError::Unsupported("d get of L1BM/L2BM with two long word access".into()));
            }
            let l1 = loc.mem == MemKind::L1bm;
            for b in Self::blocks_of(loc, l1) {
                let (name, path, mem) = if l1 {
                    ("L1BM", format!("n{}c{}b{}", b / 16, b / 8 % 2, b % 8), &self.m.blocks.l1bm[b])
                } else {
                    ("L2BM", format!("n{}c{}", b / 2, b % 2), &self.m.blocks.l2bm[b])
                };
                for i in 0..count as usize {
                    let a = (loc.addr as usize + i) % mem.len();
                    self.dump.insert((name.into(), path.clone(), a as u32), mem[a]);
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
        for pe in Self::pes_of(loc) {
            let p = &self.m.pes[pe];
            let pname = PeId::from_index(pe).name();
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
            let m = p.mem(loc.mem);
            for i in 0..count as usize {
                let a = loc.addr as usize + 2 * i;
                let v = ((m.get(a) as u64) << 32) | m.get(a + 1) as u64;
                self.dump.insert((name.into(), pname.clone(), a as u32), v);
            }
        }
        Ok(())
    }
}
