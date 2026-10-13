//! Runs a whole program: PE statements, debug statements, and the official step count.

use std::collections::HashMap;

use crate::emu::DumpKey;
use crate::machine::{Machine, MaskState, PeId, Unsupported, PES};
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
            self.exec(line).map_err(|Unsupported(msg)| RunError { line: *lineno, msg })?;
        }
        Ok(())
    }

    pub fn exec(&mut self, line: &Line) -> Result<(), Unsupported> {
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
            Line::Mv(text) => return Err(Unsupported(format!("MV instruction `{text}`"))),
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

    fn debug_set(&mut self, loc: &DebugLoc, count: u32, payload: &[u64]) -> Result<(), Unsupported> {
        // Payload long words per access unit: word access writes the MSB word of each long word.
        for pe in Self::pes_of(loc) {
            let p = &mut self.m.pes[pe];
            match loc.mem {
                MemKind::T => {
                    for (i, v) in payload.iter().enumerate().take(count as usize * (loc.wl as usize / 2).max(1)) {
                        let w = (i * 2) % p.t.len();
                        p.t[w] = (*v >> 32) as u32;
                        p.t[w + 1] = *v as u32;
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
                        _ => return Err(Unsupported("d set with two long word access".into())),
                    }
                }
                other => return Err(Unsupported(format!("d set to {other:?}"))),
            }
        }
        Ok(())
    }

    fn debug_get(&mut self, loc: &DebugLoc, count: u32) -> Result<(), Unsupported> {
        let name = match loc.mem {
            MemKind::Lm0 => "LM0",
            MemKind::Lm1 => "LM1",
            MemKind::Grf0 => "GREG0",
            MemKind::Grf1 => "GREG1",
            MemKind::T => "TREG",
            other => return Err(Unsupported(format!("d get of {other:?}"))),
        };
        for pe in Self::pes_of(loc) {
            let p = &self.m.pes[pe];
            let pname = PeId::from_index(pe).name();
            if loc.mem == MemKind::T {
                for i in 0..count as usize {
                    let w = (i * 2) % p.t.len();
                    let v = ((p.t[w] as u64) << 32) | p.t[w + 1] as u64;
                    self.dump.insert((name.into(), pname.clone(), i as u32), v);
                }
                continue;
            }
            if loc.wl != 2 {
                return Err(Unsupported("d get with word or two long word access".into()));
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
