//! State of all PEs and execution of PE instruction statements.
//!
//! Each step runs in three phases, because every read in a step sees the state before the step
//! (confirmed with the emulator: `lpassa $lr0v $lr2v` reads the old $lr2 in cycle 1):
//! 1. read all source operands of all PEs for the 4 cycles
//! 2. compute the outputs, which may combine values of several PEs (msl/msr, dvfma u/d)
//! 3. apply all writes and update the forwarding registers

use crate::float::{self, Fmt, Val, DOUBLE, HALF, SINGLE};
use crate::vsm::*;
use rayon::prelude::*;

pub const GROUPS: usize = 4;
pub const L2B_PER_GROUP: usize = 2;
pub const L1B_PER_L2B: usize = 8;
pub const MAB_PER_L1B: usize = 16;
pub const PE_PER_MAB: usize = 4;
pub const PES: usize = GROUPS * L2B_PER_GROUP * L1B_PER_L2B * MAB_PER_L1B * PE_PER_MAB;

pub const LM_WORDS: usize = 4096; // 2Ki long words
pub const GRF_WORDS: usize = 512; // 256 long words
pub const T_WORDS: usize = 16; // two long words for each of the 4 cycles

/// Two long words on the PE data path in one cycle. Index 0 is the MSB word.
pub type Bus = [u32; 4];

/// Expressions per line handled by the PE-local fast path.
const MAX_STEP_EXPRS: usize = 8;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PeId {
    pub group: u8,
    pub l2b: u8,
    pub l1b: u8,
    pub mab: u8,
    pub pe: u8,
}

impl PeId {
    pub fn from_index(i: usize) -> PeId {
        PeId {
            pe: (i % 4) as u8,
            mab: (i / 4 % 16) as u8,
            l1b: (i / 64 % 8) as u8,
            l2b: (i / 512 % 2) as u8,
            group: (i / 1024) as u8,
        }
    }
    pub fn index(self) -> usize {
        (((self.group as usize * 2 + self.l2b as usize) * 8 + self.l1b as usize) * 16
            + self.mab as usize)
            * 4
            + self.pe as usize
    }
    pub fn name(self) -> String {
        format!(
            "n{}c{}b{}m{}p{}",
            self.group, self.l2b, self.l1b, self.mab, self.pe
        )
    }
}

/// PE word memories in address-major (SoA) layout: `pe * len + (addr & (len - 1))`.
///
/// One contiguous allocation per memory kind removes the per-PE boxes and lets the fast path
/// hand each PE a mutable slice of its own memory.
pub struct Mem {
    pub lm0: Vec<u32>,
    pub lm1: Vec<u32>,
    pub grf0: Vec<u32>,
    pub grf1: Vec<u32>,
}

impl Mem {
    pub fn new() -> Mem {
        Mem {
            lm0: vec![0; PES * LM_WORDS],
            lm1: vec![0; PES * LM_WORDS],
            grf0: vec![0; PES * GRF_WORDS],
            grf1: vec![0; PES * GRF_WORDS],
        }
    }
}

pub trait MemRead {
    fn peek(&self, m: MemKind, pe: usize, addr: usize) -> u32;
}

pub trait MemWrite: MemRead {
    fn poke(&mut self, m: MemKind, pe: usize, addr: usize, v: u32);
}

impl MemRead for Mem {
    #[inline]
    fn peek(&self, m: MemKind, pe: usize, addr: usize) -> u32 {
        match m {
            MemKind::Lm0 => unsafe {
                *self.lm0.get_unchecked(pe * LM_WORDS + (addr & (LM_WORDS - 1)))
            },
            MemKind::Lm1 => unsafe {
                *self.lm1.get_unchecked(pe * LM_WORDS + (addr & (LM_WORDS - 1)))
            },
            MemKind::Grf0 => unsafe {
                *self.grf0.get_unchecked(pe * GRF_WORDS + (addr & (GRF_WORDS - 1)))
            },
            MemKind::Grf1 => unsafe {
                *self.grf1.get_unchecked(pe * GRF_WORDS + (addr & (GRF_WORDS - 1)))
            },
            other => panic!("not a PE word memory: {other:?}"),
        }
    }
}

impl MemWrite for Mem {
    #[inline]
    fn poke(&mut self, m: MemKind, pe: usize, addr: usize, v: u32) {
        match m {
            MemKind::Lm0 => unsafe {
                *self.lm0.get_unchecked_mut(pe * LM_WORDS + (addr & (LM_WORDS - 1))) = v
            },
            MemKind::Lm1 => unsafe {
                *self.lm1.get_unchecked_mut(pe * LM_WORDS + (addr & (LM_WORDS - 1))) = v
            },
            MemKind::Grf0 => unsafe {
                *self.grf0.get_unchecked_mut(pe * GRF_WORDS + (addr & (GRF_WORDS - 1))) = v
            },
            MemKind::Grf1 => unsafe {
                *self.grf1.get_unchecked_mut(pe * GRF_WORDS + (addr & (GRF_WORDS - 1))) = v
            },
            other => panic!("not a PE word memory: {other:?}"),
        }
    }
}

/// One PE's four memory slices, handed to a parallel worker.
pub struct MemPe<'a> {
    lm0: &'a mut [u32],
    lm1: &'a mut [u32],
    grf0: &'a mut [u32],
    grf1: &'a mut [u32],
}

impl MemRead for MemPe<'_> {
    #[inline]
    fn peek(&self, m: MemKind, _pe: usize, addr: usize) -> u32 {
        match m {
            MemKind::Lm0 => unsafe { *self.lm0.get_unchecked(addr & (LM_WORDS - 1)) },
            MemKind::Lm1 => unsafe { *self.lm1.get_unchecked(addr & (LM_WORDS - 1)) },
            MemKind::Grf0 => unsafe { *self.grf0.get_unchecked(addr & (GRF_WORDS - 1)) },
            MemKind::Grf1 => unsafe { *self.grf1.get_unchecked(addr & (GRF_WORDS - 1)) },
            other => panic!("not a PE word memory: {other:?}"),
        }
    }
}

impl MemWrite for MemPe<'_> {
    #[inline]
    fn poke(&mut self, m: MemKind, _pe: usize, addr: usize, v: u32) {
        match m {
            MemKind::Lm0 => unsafe {
                *self.lm0.get_unchecked_mut(addr & (LM_WORDS - 1)) = v
            },
            MemKind::Lm1 => unsafe {
                *self.lm1.get_unchecked_mut(addr & (LM_WORDS - 1)) = v
            },
            MemKind::Grf0 => unsafe {
                *self.grf0.get_unchecked_mut(addr & (GRF_WORDS - 1)) = v
            },
            MemKind::Grf1 => unsafe {
                *self.grf1.get_unchecked_mut(addr & (GRF_WORDS - 1)) = v
            },
            other => panic!("not a PE word memory: {other:?}"),
        }
    }
}

#[derive(Clone)]
pub struct Pe {
    pub t: [u32; T_WORDS],
    pub bar0: u32,
    pub bar1: u32,
    /// Mask register entries 1 to 15 (index 0 unused). Bits 4c..4c+3 hold cycle c's flags,
    /// with bit 3 of each nibble for the MSB element.
    pub mask: [u16; 16],
    pub aluf: [Bus; 4],
    pub mauf: [Bus; 4],
    pub mreadf: [Bus; 4],
    pub lbf: [Bus; 4],
}

impl Default for Pe {
    fn default() -> Pe {
        Pe {
            t: [0; T_WORDS],
            bar0: 0,
            bar1: 0,
            mask: [0; 16],
            aluf: [[0; 4]; 4],
            mauf: [[0; 4]; 4],
            mreadf: [[0; 4]; 4],
            lbf: [[0; 4]; 4],
        }
    }
}


#[derive(Clone, Debug, PartialEq)]
pub enum ExecError {
    /// An instruction or operand the simulator does not support yet.
    Unsupported(String),
    /// An error the emulator also raises at run time, such as reading `$aluf` after a step
    /// without an ALU instruction, or a matrix product with invalid block-float input.
    Runtime(String),
    /// A line the assembler rejects, such as one breaking the issue conditions of SDM 3.6.4.
    Assembly(String),
}

impl ExecError {
    pub fn message(&self) -> String {
        match self {
            ExecError::Unsupported(m) => format!("unsupported: {m}"),
            ExecError::Runtime(m) => format!("runtime error: {m}"),
            ExecError::Assembly(m) => format!("assembler error: {m}"),
        }
    }
}

/// The multi-line write mask set by `mask...` directives.
#[derive(Clone, Copy, Debug, Default)]
pub struct MaskState {
    pub wl: u8,
    pub targets: MaskTargets,
    pub entry: u8,
}

/// One face of a MAB's matrix register: 16 physical rows of 256 bits (8 words, MSB first).
pub type MatFace = [[u32; 8]; 16];

pub struct Machine {
    pub pes: Vec<Pe>,
    /// PE word memories (LM0, LM1, GRF0, GRF1) in address-major order.
    pub mem: Mem,
    /// Why each forwarding register (aluf, mauf, mreadf, lbf) cannot be read, if it cannot.
    /// Like the emulator, an error is only raised when the register is actually read, e.g.
    /// when the previous step had no instruction for that unit ("IALU is disabled").
    pub fwd_error: [Option<String>; 4],
    /// Matrix registers x (index 0) and y (index 1) of each MAB.
    pub mats: Vec<[MatFace; 2]>,
    /// L1BM, L2BM and the L1BM turnaround register.
    pub blocks: crate::blocks::Blocks,
    /// Records accesses of focus PEs for the visualization, when set.
    pub tracer: std::cell::RefCell<Option<crate::trace::Tracer>>,
    pub mask_state: MaskState,
    /// Lines executed by the generic path and by the PE-local fast path.
    pub slow_steps: u64,
    pub fast_steps: u64,
}

/// A pending write to a matrix register: MAB, face, physical row, and the 8 words of the row.
struct MatWrite {
    expr: u16,
    cycle: usize,
    mab: usize,
    side: usize,
    phys_row: usize,
    /// Words to write; `None` keeps the old word.
    words: [Option<u32>; 8],
}

/// One computed output of an expression: the value for each PE and cycle, and the mask flags.
struct Output {
    bus: Vec<[Bus; 4]>,
    flags: Vec<[u8; 4]>,
    /// Which forwarding register this output updates.
    fwd: Option<FwdKind>,
    /// A run-time error in computing some values. As in the emulator, it is raised only when
    /// such a value is written to memory, or read later from the forwarding register.
    poison: Option<Poison>,
}

struct Poison {
    msg: String,
    /// Poisoned (pe, cycle) values; empty means all.
    at: Vec<[bool; 4]>,
}

impl Poison {
    fn hits(&self, pe: usize, c: usize) -> bool {
        self.at.is_empty() || self.at[pe][c]
    }
}

/// The forwarding register an expression updates.
fn op_fwd_kind(e: &Expr) -> Option<FwdKind> {
    match &e.op {
        Op::Alu { .. } | Op::Imm { .. } | Op::Zero => Some(FwdKind::Aluf),
        Op::Mau { .. } => Some(FwdKind::Mauf),
        Op::MatRead { .. } => Some(FwdKind::Mreadf),
        Op::L1(_) if is_l1_to_pe(e) => Some(FwdKind::Lbf),
        _ => None,
    }
}

fn is_l1_to_pe(e: &Expr) -> bool {
    matches!(e.srcs.first(), Some(Operand::L1bm { .. }))
}

fn unit_name(k: FwdKind) -> &'static str {
    match k {
        FwdKind::Aluf => "IALU",
        FwdKind::Mauf => "MAU",
        FwdKind::Mreadf => "matrix read",
        FwdKind::Lbf => "L1BM-to-PE transfer",
    }
}

impl Default for Machine {
    fn default() -> Self {
        Self::new()
    }
}

impl Machine {
    pub fn new() -> Machine {
        let uninit = |k| {
            Some(format!(
                "uninitialized {} forwarding register",
                unit_name(k)
            ))
        };
        let fwd_error = [
            uninit(FwdKind::Aluf),
            uninit(FwdKind::Mauf),
            uninit(FwdKind::Mreadf),
            uninit(FwdKind::Lbf),
        ];
        Machine {
            pes: vec![Pe::default(); PES],
            mem: Mem::new(),
            fwd_error,
            blocks: Default::default(),
            tracer: Default::default(),
            mats: vec![[[[0; 8]; 16]; 2]; PES / 4],
            mask_state: MaskState::default(),
            slow_steps: 0,
            fast_steps: 0,
        }
    }

    // ---- reads ----------------------------------------------------------------------------

    #[inline]
    fn word_addrs(&self, pe: usize, mem: MemKind, wl: u8, addr: &Addr, cycle: usize) -> usize {
        let p = &self.pes[pe];
        let bar = match mem {
            MemKind::Lm0 => p.bar0,
            MemKind::Lm1 => p.bar1,
            _ => 0,
        } as usize;
        let wl = wl as usize;
        if !addr.t_indirect && addr.madpe.is_none() {
            return (bar + addr.cycles[cycle] as usize) & !(wl - 1);
        }
        // T indirect adds the MSB long word of T as an integer; only its low bits matter, because
        // addresses wrap at the memory size.
        let t = if addr.t_indirect {
            p.t[cycle * 4 + 1] as usize
        } else {
            0
        };
        let maadj = match addr.madpe {
            Some(m) if (pe % 4) as u8 <= m => wl,
            _ => 0,
        };
        (bar + t + addr.cycles[cycle] as usize + maadj) & !(wl - 1)
    }

    fn read_raw(&self, pe: usize, op: &Operand, cycle: usize) -> Result<Bus, ExecError> {
        let bus = self.read_raw_untraced(pe, op, cycle)?;
        if let Some(t) = self.tracer.borrow_mut().as_mut() {
            match op {
                Operand::Mem { mem, wl, addr, .. } => {
                    let (a, n) = if *mem == MemKind::T {
                        (cycle as u32, 4)
                    } else {
                        (
                            self.word_addrs(pe, *mem, *wl, addr, cycle) as u32,
                            *wl as usize,
                        )
                    };
                    t.pe_read(
                        pe,
                        cycle,
                        mem_name(*mem),
                        op as *const Operand as usize,
                        Some(a),
                        &bus[..n],
                    );
                }
                Operand::Forward { kind, .. } => t.pe_read(
                    pe,
                    cycle,
                    fwd_name(*kind),
                    op as *const Operand as usize,
                    None,
                    &bus,
                ),
                _ => {}
            }
        }
        Ok(bus)
    }

    fn read_raw_untraced(&self, pe: usize, op: &Operand, cycle: usize) -> Result<Bus, ExecError> {
        let p = &self.pes[pe];
        Ok(match op {
            Operand::Mem { mem: MemKind::T, .. } => {
                let b = cycle * 4;
                [p.t[b], p.t[b + 1], p.t[b + 2], p.t[b + 3]]
            }
            Operand::Mem { mem, wl, addr, .. } => {
                let a = self.word_addrs(pe, *mem, *wl, addr, cycle);
                let mut bus = [0; 4];
                for i in 0..*wl as usize {
                    bus[i] = self.mem.peek(*mem, pe, a + i);
                }
                bus
            }
            Operand::Forward { kind, .. } if self.fwd_error[fwd_index(*kind)].is_some() => {
                return Err(ExecError::Runtime(format!(
                    "accessing {} forwarding register failed; the error on the previous step is: {}",
                    unit_name(*kind),
                    self.fwd_error[fwd_index(*kind)].as_ref().unwrap()
                )))
            }
            Operand::Forward { kind, .. } => match kind {
                FwdKind::Aluf => p.aluf[cycle],
                FwdKind::Mauf => p.mauf[cycle],
                FwdKind::Mreadf => p.mreadf[cycle],
                FwdKind::Lbf => p.lbf[cycle],
            },
            Operand::Fixed(_) => return Err(ExecError::Unsupported("fixed operands depend on precision".into())),
            other => return Err(ExecError::Unsupported(format!("read of {other:?}"))),
        })
    }

    // ---- step execution -------------------------------------------------------------------

    /// Executes one PE statement.
    pub fn step(&mut self, exprs: &[Expr]) -> Result<(), ExecError> {
        if let Some(fast) = self.step_fast(exprs) {
            self.fast_steps += 1;
            return fast;
        }
        self.slow_steps += 1;
        let noforward = exprs.iter().any(|e| e.op == Op::Noforward);
        let single_line_mask = exprs.iter().any(|e| e.dsts.iter().any(has_mask));
        let mut outputs: Vec<(&Expr, Output)> = Vec::new();
        let mut mat_writes: Vec<MatWrite> = Vec::new();
        let mut block_writes = crate::blocks::BlockWrites::default();
        for (ei, e) in exprs.iter().enumerate() {
            if let Some(t) = self.tracer.borrow_mut().as_mut() {
                t.expr = ei as u16;
                t.srcs = e
                    .srcs
                    .iter()
                    .map(|o| o as *const Operand as usize)
                    .collect();
            }
            match &e.op {
                Op::Noforward | Op::Wait(_) => continue,
                Op::MatWrite { prec } => {
                    mat_writes.extend(self.compute_mwrite(e, *prec)?);
                    continue;
                }
                Op::L1(op) if !is_l1_to_pe(e) => {
                    block_writes.expr = ei as u16;
                    let src = &e.srcs[0];
                    let ext = matches!(
                        src,
                        Operand::Mem { ext: true, .. } | Operand::Forward { ext: true, .. }
                    );
                    let mut vals = vec![[[0u32; 4]; 4]; PES];
                    for pe in 0..PES {
                        for c in 0..4 {
                            vals[pe][c] = self.read_raw(pe, src, c)?;
                        }
                    }
                    let dst = e
                        .dsts
                        .first()
                        .ok_or_else(|| ExecError::Unsupported("missing L1BM operand".into()))?;
                    let src_two =
                        matches!(src, Operand::Mem { wl: 4, .. } | Operand::Forward { .. });
                    self.blocks
                        .pe_to_l1(*op, dst, &vals, ext, src_two, &mut block_writes)?;
                    continue;
                }
                Op::L2(op) => {
                    block_writes.expr = ei as u16;
                    self.blocks.l2(e, *op, &mut block_writes)?;
                    continue;
                }
                _ => {}
            }
            let out = match self.compute(e) {
                Ok(o) => o,
                Err(ExecError::Runtime(msg)) => Output {
                    bus: vec![[[0; 4]; 4]; PES],
                    flags: vec![[0; 4]; PES],
                    fwd: op_fwd_kind(e),
                    poison: Some(Poison {
                        msg,
                        at: Vec::new(),
                    }),
                },
                Err(other) => return Err(other),
            };
            outputs.push((e, out));
        }
        let new_lbi = block_writes.lbi.take();
        if let Some(t) = self.tracer.borrow_mut().as_mut() {
            for &(b, a, v, c, ei) in &block_writes.l1bm {
                t.expr = ei;
                t.l1bm(b, c as usize, true, a as u32, v);
            }
        }
        self.blocks.apply(block_writes);
        if !noforward {
            match new_lbi {
                Some(l) => {
                    self.blocks.lbi = l;
                    self.blocks.lbi_error = None;
                }
                None => {
                    self.blocks.lbi_error =
                        Some("the previous step had no PE-to-L1BM transfer".into())
                }
            }
        }
        for w in mat_writes {
            if let Some(t) = self.tracer.borrow_mut().as_mut() {
                t.expr = w.expr;
                let words: Vec<u32> = w.words.iter().map(|v| v.unwrap_or(0)).collect();
                t.mat(w.mab, w.cycle, w.side, w.phys_row, &words);
            }
            let row = &mut self.mats[w.mab][w.side][w.phys_row];
            for (i, v) in w.words.iter().enumerate() {
                if let Some(v) = v {
                    row[i] = *v;
                }
            }
        }
        let tracing = self.tracer.borrow().is_some();
        let mask_state = self.mask_state;
        for (ei, (e, out)) in outputs.iter().enumerate() {
            let flush = e.flush;
            if !tracing {
                self.write_output_parallel(e, out, flush, single_line_mask, mask_state)?;
                continue;
            }
            let expr_index = exprs.iter().position(|x| std::ptr::eq(x, *e)).unwrap_or(ei) as u16;
            if let Some(t) = self.tracer.borrow_mut().as_mut() {
                t.expr = expr_index;
            }
            for pe in 0..PES {
                for c in 0..4 {
                    let mut bus = out.bus[pe][c];
                    if let Some(t) = self.tracer.borrow_mut().as_mut() {
                        t.wslot = None;
                        t.pe(pe, c, "out", true, None, &bus);
                    }
                    if let Some(sel) = flush {
                        let f = self.mask_flags(pe, &sel, c);
                        bus = apply_flush(bus, f, sel.ll);
                    }
                    let poison = out
                        .poison
                        .as_ref()
                        .filter(|p| p.hits(pe, c))
                        .map(|p| p.msg.as_str());
                    for (di, d) in e.dsts.iter().enumerate() {
                        if let Some(t) = self.tracer.borrow_mut().as_mut() {
                            t.wslot = Some(di as u8);
                        }
                        self.write(pe, d, c, bus, out.flags[pe][c], single_line_mask, poison)?;
                    }
                }
            }
        }
        if !noforward {
            for k in [FwdKind::Aluf, FwdKind::Mauf, FwdKind::Mreadf, FwdKind::Lbf] {
                let mine: Vec<&Output> = outputs
                    .iter()
                    .map(|(_, o)| o)
                    .filter(|o| o.fwd == Some(k))
                    .collect();
                self.fwd_error[fwd_index(k)] = if mine.is_empty() && k == FwdKind::Mreadf {
                    // With no matrix read, the official emulator exposes zero on mreadf
                    // rather than a disabled-producer error. nop/noforward still preserve it.
                    for pe in &mut self.pes {
                        pe.mreadf = [[0; 4]; 4];
                    }
                    None
                } else if mine.is_empty() && k == FwdKind::Lbf {
                    // Encoded-word experiments retain the last L1BM-to-PE value
                    // across ordinary ALU/MAU steps; absence does not disable it.
                    self.fwd_error[fwd_index(k)].clone()
                } else if mine.is_empty() {
                    Some(format!("{} is disabled", unit_name(k)))
                } else {
                    mine.iter()
                        .find_map(|o| o.poison.as_ref().map(|p| p.msg.clone()))
                };
            }
            for (e, out) in &outputs {
                let Some(kind) = out.fwd else { continue };
                self.pes.par_iter_mut().enumerate().for_each(|(pe, p)| {
                    for c in 0..4 {
                        let mut bus = out.bus[pe][c];
                        if let Some(sel) = e.flush {
                            let f = mask_flags_pe(p, &mask_state, &sel, c);
                            bus = apply_flush(bus, f, sel.ll);
                        }
                        match kind {
                            FwdKind::Aluf => p.aluf[c] = bus,
                            FwdKind::Mauf => p.mauf[c] = bus,
                            FwdKind::Mreadf => p.mreadf[c] = bus,
                            FwdKind::Lbf => p.lbf[c] = bus,
                        }
                    }
                });
            }
        }
        Ok(())
    }

    /// Mask flags (4 bits, bit 3 = MSB element) of an entry for one PE and cycle.
    fn mask_flags(&self, pe: usize, sel: &MaskSel, cycle: usize) -> u8 {
        match sel.source {
            MaskSource::Pattern(p) => {
                if p[cycle] {
                    0xf
                } else {
                    0
                }
            }
            MaskSource::Entry(n) => self.entry_flags(pe, n, cycle),
        }
    }

    fn entry_flags(&self, pe: usize, entry: u8, cycle: usize) -> u8 {
        match entry {
            0 => 0xf,
            1..=15 => ((self.pes[pe].mask[entry as usize] >> (4 * cycle)) & 0xf) as u8,
            _ => {
                if (entry >> (3 - cycle)) & 1 == 1 {
                    0xf
                } else {
                    0
                }
            }
        }
    }

    fn write(
        &mut self,
        pe: usize,
        d: &Operand,
        cycle: usize,
        bus: Bus,
        flags: u8,
        single_line: bool,
        poison: Option<&str>,
    ) -> Result<(), ExecError> {
        let fail = |enabled: bool| -> Result<(), ExecError> {
            match poison {
                Some(msg) if enabled => Err(ExecError::Runtime(msg.to_string())),
                _ => Ok(()),
            }
        };
        // Which mask applies: the single-line mask of this operand, or the multi-line directive
        // unless any single-line mask is used in this step (SDM 3.6.2.1).
        let directive = |mem: Option<MemKind>, omr: bool, st: &MaskState| -> Option<MaskSel> {
            if single_line {
                return None;
            }
            let t = st.targets;
            let on = match mem {
                Some(MemKind::Grf0) => t.grf0,
                Some(MemKind::Grf1) => t.grf1,
                Some(MemKind::T) => t.t,
                Some(MemKind::Lm0) => t.lm0,
                Some(MemKind::Lm1) => t.lm1,
                _ => omr && t.mask_reg,
            };
            if on && st.entry != 0 {
                Some(MaskSel {
                    ll: st.wl == 4,
                    source: MaskSource::Entry(st.entry),
                })
            } else {
                None
            }
        };
        let st = self.mask_state;
        match d {
            Operand::Nowrite => {}
            Operand::Mem {
                mem,
                wl,
                addr,
                mask,
                ..
            } => {
                let sel = mask.or_else(|| directive(Some(*mem), false, &st));
                let mflags = sel.map(|s| (self.mask_flags(pe, &s, cycle), s.ll));
                let words = if *mem == MemKind::T { 4 } else { *wl as usize };
                fail((0..words).any(|i| word_enabled(mflags, i)))?;
                if (0..words).any(|i| word_enabled(mflags, i)) {
                    if let Some(t) = self.tracer.borrow_mut().as_mut() {
                        let a = if *mem == MemKind::T {
                            cycle as u32
                        } else {
                            self.word_addrs(pe, *mem, *wl, addr, cycle) as u32
                        };
                        t.pe(pe, cycle, mem_name(*mem), true, Some(a), &bus[..words]);
                    }
                }
                if *mem == MemKind::T {
                    let p = &mut self.pes[pe];
                    for i in 0..4 {
                        if word_enabled(mflags, i) {
                            p.t[cycle * 4 + i] = merge_word(p.t[cycle * 4 + i], bus[i], mflags, i);
                        }
                    }
                    return Ok(());
                }
                let a = self.word_addrs(pe, *mem, *wl, addr, cycle);
                for i in 0..*wl as usize {
                    if word_enabled(mflags, i) {
                        let old = self.mem.peek(*mem, pe, a + i);
                        self.mem.poke(*mem, pe, a + i, merge_word(old, bus[i], mflags, i));
                    }
                }
            }
            Operand::Bar { lm1, mask, .. } => {
                let mem = if *lm1 { MemKind::Lm1 } else { MemKind::Lm0 };
                let sel = mask.or_else(|| directive(Some(mem), false, &st));
                if let Some(s) = sel {
                    if self.mask_flags(pe, &s, cycle) == 0 {
                        return Ok(());
                    }
                }
                fail(true)?;
                if let Some(t) = self.tracer.borrow_mut().as_mut() {
                    t.pe(
                        pe,
                        cycle,
                        if *lm1 { "bar1" } else { "bar0" },
                        true,
                        None,
                        &[bus[0] & 0xfff],
                    );
                }
                let p = &mut self.pes[pe];
                if *lm1 {
                    p.bar1 = bus[0] & 0xfff;
                } else {
                    p.bar0 = bus[0] & 0xfff;
                }
            }
            Operand::Omr { entry, mask } => {
                if *entry == 0 || *entry > 15 {
                    return Err(ExecError::Unsupported(format!(
                        "mask register entry {entry} is read-only"
                    )));
                }
                let sel = mask.or_else(|| directive(None, true, &st));
                let f = match sel {
                    Some(s) => flags & self.mask_flags(pe, &s, cycle),
                    None => flags,
                };
                // Data poison is not forced by a flags-only write. Flags are computed
                // separately; a zero selection still writes zero to the mask register.
                if let Some(t) = self.tracer.borrow_mut().as_mut() {
                    t.pe(pe, cycle, "omr", true, Some(*entry as u32), &[f as u32]);
                }
                let p = &mut self.pes[pe];
                let e = &mut p.mask[*entry as usize];
                *e = (*e & !(0xf << (4 * cycle))) | ((f as u16) << (4 * cycle));
            }
            other => return Err(ExecError::Unsupported(format!("write to {other:?}"))),
        }
        Ok(())
    }

    // ---- compute --------------------------------------------------------------------------

    fn compute(&self, e: &Expr) -> Result<Output, ExecError> {
        match &e.op {
            Op::Zero => Ok(self.alu_like(|_, _| ([[0; 4]; 4], [0; 4]))),
            Op::Imm { value, u } => {
                let v = *value;
                let bus = if *u { [v, 0, v, 0] } else { [v; 4] };
                Ok(self.alu_like(|_, _| ([bus; 4], [0; 4])))
            }
            Op::Alu {
                name: name @ (AluOp::Bfn | AluOp::Bfe),
                prec,
                arg,
                ..
            } => self.compute_bfn(e, *name, prec.unwrap(), *arg),
            Op::Alu {
                name,
                prec,
                unsigned,
                ..
            } => self.compute_alu(e, *name, *prec, *unsigned),
            Op::Mau {
                prec,
                matrix: false,
                kind,
                half,
                round,
            } => self.compute_vec(e, *prec, *kind, *half, *round),
            Op::Mau {
                prec,
                matrix: true,
                kind,
                half,
                round,
            } => self.compute_mat(e, *prec, *kind, *half, *round),
            Op::MatRead { prec } => self.compute_mread(e, *prec),
            Op::L1(op) => {
                let (bus, from) = self.blocks.l1_to_pe(*op, &e.srcs[0])?;
                if let Some(t) = self.tracer.borrow_mut().as_mut() {
                    for pe in 0..PES {
                        for c in 0..4 {
                            let b = &bus[pe][c];
                            t.pe_read(
                                pe,
                                c,
                                "l1bm_src",
                                &e.srcs[0] as *const Operand as usize,
                                from[pe][c],
                                &[b[0], b[1]],
                            );
                        }
                    }
                }
                Ok(Output {
                    bus,
                    flags: vec![[0; 4]; PES],
                    fwd: Some(FwdKind::Lbf),
                    poison: None,
                })
            }
            other => Err(ExecError::Unsupported(format!("{other:?}"))),
        }
    }

    fn alu_like(&self, f: impl Fn(&Machine, usize) -> ([Bus; 4], [u8; 4])) -> Output {
        let mut bus = Vec::with_capacity(PES);
        let mut flags = Vec::with_capacity(PES);
        for pe in 0..PES {
            let (b, fl) = f(self, pe);
            bus.push(b);
            flags.push(fl);
        }
        Output {
            bus,
            flags,
            fwd: Some(FwdKind::Aluf),
            poison: None,
        }
    }

    /// Reads an ALU input operand, applying the `r` option (single to half) if present.
    fn read_alu_input(
        &self,
        pe: usize,
        op: &Operand,
        prec: Option<Prec>,
        cycle: usize,
    ) -> Result<Bus, ExecError> {
        if let Operand::Fixed(k) = op {
            let id = PeId::from_index(pe);
            let v: u64 = match k {
                FixedKind::L2bid => (id.group * 2 + id.l2b) as u64,
                FixedKind::L1bid => id.l1b as u64,
                FixedKind::Mabid => id.mab as u64,
                FixedKind::Peid => (id.mab * 4 + id.pe) as u64,
                FixedKind::Subpeid => id.pe as u64,
                FixedKind::Msb1 => u64::MAX,
            };
            let bits = prec_bits(prec);
            let lane = if *k == FixedKind::Msb1 {
                1u64 << (bits - 1)
            } else {
                v
            };
            return Ok(splat(lane, bits));
        }
        let bus = self.read_raw(pe, op, cycle)?;
        let rnd = matches!(
            op,
            Operand::Mem { rnd: true, .. } | Operand::Forward { rnd: true, .. }
        );
        if rnd {
            let mut out = [0u32; 4];
            let halves: Vec<u64> = (0..4)
                .map(|i| float::encode(HALF, float::decode(SINGLE, bus[i] as u64)))
                .collect();
            out[0] = ((halves[0] << 16) | halves[1]) as u32;
            out[1] = ((halves[2] << 16) | halves[3]) as u32;
            return Ok(out);
        }
        Ok(bus)
    }

    fn compute_alu(
        &self,
        e: &Expr,
        name: AluOp,
        prec: Option<Prec>,
        unsigned: bool,
    ) -> Result<Output, ExecError> {
        if self.tracer.borrow().is_none() && !matches!(name, AluOp::Msl | AluOp::Msr) {
            let mut bus = vec![[[0u32; 4]; 4]; PES];
            let mut flags = vec![[0u8; 4]; PES];
            let pes = &self.pes;
            let mem = &self.mem;
            let fwd_error = &self.fwd_error;
            bus.par_chunks_mut(64)
                .zip(flags.par_chunks_mut(64))
                .enumerate()
                .try_for_each(|(ci, (bc, fc))| -> Result<(), ExecError> {
                    for (j, (b, f)) in bc.iter_mut().zip(fc.iter_mut()).enumerate() {
                        let pe = ci * 64 + j;
                        let (out, fl) =
                            compute_alu_pe(&pes[pe], mem, fwd_error, e, name, prec, unsigned, pe)?;
                        *b = out;
                        *f = fl;
                    }
                    Ok(())
                })?;
            return Ok(Output {
                bus,
                flags,
                fwd: Some(FwdKind::Aluf),
                poison: None,
            });
        }
        if self.tracer.borrow().is_none() && matches!(name, AluOp::Msl | AluOp::Msr) {
            // msl/msr pair PEs inside one MAB; MABs are independent.
            let mut bus = vec![[[0u32; 4]; 4]; PES];
            let mut flags = vec![[0u8; 4]; PES];
            let pes = &self.pes;
            let mem = &self.mem;
            let fwd_error = &self.fwd_error;
            let src = &e.srcs[0];
            let msl = name == AluOp::Msl;
            bus.par_chunks_mut(4)
                .zip(flags.par_chunks_mut(4))
                .enumerate()
                .try_for_each(|(mab, (bc, fc))| -> Result<(), ExecError> {
                    let mut ins = [[[0u32; 4]; 4]; 4];
                    for p in 0..4 {
                        for c in 0..4 {
                            ins[p][c] = read_alu_input_pe(
                                &pes[mab * 4 + p],
                                mem,
                                fwd_error,
                                mab * 4 + p,
                                src,
                                prec,
                                c,
                            )?;
                        }
                    }
                    for p in 0..4 {
                        let from = if msl { (p + 3) % 4 } else { (p + 1) % 4 };
                        for c in 0..4 {
                            let v = ins[from][c];
                            bc[p][c] = [v[0], v[1], 0, 0];
                            fc[p][c] = 0;
                        }
                    }
                    Ok(())
                })?;
            return Ok(Output {
                bus,
                flags,
                fwd: Some(FwdKind::Aluf),
                poison: None,
            });
        }
        let n = name.inputs();
        let mut ins: Vec<Vec<[Bus; 4]>> = vec![vec![[[0; 4]; 4]; PES]; n];
        for (i, op) in e.srcs.iter().enumerate().take(n) {
            for pe in 0..PES {
                for c in 0..4 {
                    ins[i][pe][c] = self.read_alu_input(pe, op, prec, c)?;
                }
            }
        }
        let bits = prec_bits(prec);
        let mut bus = vec![[[0u32; 4]; 4]; PES];
        let mut flags = vec![[0u8; 4]; PES];
        for pe in 0..PES {
            for c in 0..4 {
                let x = ins[0][pe][c];
                let y = if n > 1 { ins[1][pe][c] } else { [0; 4] };
                let (out, fl) = match name {
                    AluOp::Msl | AluOp::Msr => {
                        // msl: PE k outputs the input of PE k-1 within the MAB.
                        let base = pe / 4 * 4;
                        let src = if name == AluOp::Msl {
                            base + (pe + 3) % 4
                        } else {
                            base + (pe + 1) % 4
                        };
                        // Only one long word moves between PEs: the LSB long word is 0 (emulator),
                        // not the first input's LSB long word as for other ALU instructions.
                        let v = ins[0][src][c];
                        ([v[0], v[1], 0, 0], 0)
                    }
                    AluOp::Passa => {
                        let (xl, count) = lanes_fixed(&x, bits);
                        let fl = lane_flags(&xl[..count], bits, |v| v == 0);
                        (x, fl)
                    }
                    _ => {
                        let (xl, count) = lanes_fixed(&x, bits);
                        let (yl, _) = lanes_fixed(&y, bits);
                        let (msb, fl) =
                            alu_lanes(name, prec.unwrap(), unsigned, &xl[..count], &yl[..count])?;
                        let lo = pack_lanes(&msb[..count], bits);
                        ([lo[0], lo[1], x[2], x[3]], fl)
                    }
                };
                bus[pe][c] = out;
                flags[pe][c] = fl;
            }
        }
        Ok(Output {
            bus,
            flags,
            fwd: Some(FwdKind::Aluf),
            poison: None,
        })
    }

    fn compute_vec(
        &self,
        e: &Expr,
        prec: Prec,
        kind: MauKind,
        half: Option<char>,
        round: bool,
    ) -> Result<Output, ExecError> {
        if self.tracer.borrow().is_none() {
            let mut bus = vec![[[0u32; 4]; 4]; PES];
            let mut flags = vec![[0u8; 4]; PES];
            let pes = &self.pes;
            let mem = &self.mem;
            let fwd_error = &self.fwd_error;
            bus.par_chunks_mut(64)
                .zip(flags.par_chunks_mut(64))
                .enumerate()
                .try_for_each(|(ci, (bc, fc))| -> Result<(), ExecError> {
                    for (j, (b, f)) in bc.iter_mut().zip(fc.iter_mut()).enumerate() {
                        let pe = ci * 64 + j;
                        let (out, fl) = compute_vec_pe(
                            &pes[pe], mem, fwd_error, e, prec, kind, half, round, pe,
                        )?;
                        *b = out;
                        *f = fl;
                    }
                    Ok(())
                })?;
            return Ok(Output {
                bus,
                flags,
                fwd: Some(FwdKind::Mauf),
                poison: None,
            });
        }
        // Formats of the inputs a, b, c and of the output in the basic operation (SDM 3.6.9).
        let (fa, fc, fout): (Fmt, Fmt, Fmt) = match prec {
            Prec::D => (DOUBLE, DOUBLE, if round { SINGLE } else { DOUBLE }),
            Prec::F | Prec::G => (SINGLE, SINGLE, SINGLE),
            Prec::H => (HALF, SINGLE, if round { HALF } else { SINGLE }),
            _ => {
                return Err(ExecError::Unsupported(format!(
                    "vector op precision {prec:?}"
                )))
            }
        };
        if matches!(prec, Prec::F | Prec::G) && round {
            return Err(ExecError::Unsupported("fv*r".into()));
        }
        let lanes_n = match prec {
            Prec::D => 1,
            Prec::F | Prec::G => 2,
            _ => 4,
        };
        // Which source operands feed a, b and c.
        let (ia, ib, ic): (Option<usize>, Option<usize>, Option<usize>) = match kind {
            MauKind::Fma => (Some(0), Some(1), Some(2)),
            MauKind::Mul => (Some(0), Some(1), None),
            MauKind::Add => (Some(0), None, Some(1)),
            MauKind::Passa => (Some(0), None, None),
        };
        let read_vals = |m: &Machine,
                         pe: usize,
                         idx: Option<usize>,
                         f: Fmt,
                         c: usize|
         -> Result<Option<Vec<Val>>, ExecError> {
            let Some(i) = idx else { return Ok(None) };
            let op = &e.srcs[i];
            let bus = m.read_raw(pe, op, c)?;
            let (neg, ext, rnd) = match op {
                Operand::Mem { neg, ext, rnd, .. } | Operand::Forward { neg, ext, rnd, .. } => {
                    (*neg, *ext, *rnd)
                }
                _ => (false, false, false),
            };
            let raw_fmt = if ext {
                lower(f).ok_or_else(|| ExecError::Unsupported("extension below half".into()))?
            } else if rnd {
                higher(f)
                    .ok_or_else(|| ExecError::Unsupported("rounding from above double".into()))?
            } else {
                f
            };
            let raw = unpack(&bus, raw_fmt.width(), lanes_n);
            Ok(Some(
                raw.into_iter()
                    .map(|r| {
                        let v = float::decode(raw_fmt, r);
                        let v = if rnd {
                            float::decode(f, float::encode(f, v))
                        } else {
                            v
                        };
                        if neg {
                            v.negate()
                        } else {
                            v
                        }
                    })
                    .collect(),
            ))
        };
        let one_a = float::decode(fa, (fa.bias() as u64) << fa.man_bits);
        let zero = Val::Zero { neg: false };
        let mut bus = vec![[[0u32; 4]; 4]; PES];
        let mut flags = vec![[0u8; 4]; PES];
        for pe in 0..PES {
            for c in 0..4 {
                let a = read_vals(self, pe, ia, fa, c)?.unwrap();
                let b = read_vals(self, pe, ib, fa, c)?;
                let cv = read_vals(self, pe, ic, fc, c)?;
                // dvfma/dvmul with u (PE0, PE1) or d (PE2, PE3) multiply only in those PEs.
                let mul_here = match half {
                    Some('u') => pe % 4 < 2,
                    Some('d') => pe % 4 >= 2,
                    _ => true,
                };
                let mut out = Vec::with_capacity(lanes_n);
                for l in 0..lanes_n {
                    let (x, y) = if mul_here {
                        (a[l], b.as_ref().map(|b| b[l]).unwrap_or(one_a))
                    } else {
                        (zero, zero)
                    };
                    let z = cv.as_ref().map(|c| c[l]).unwrap_or(zero);
                    out.push(float::vfma(fa, fout, x, y, z));
                }
                bus[pe][c] = pack(&out, fout.width());
                flags[pe][c] = mau_flags(&out, fout);
            }
        }
        Ok(Output {
            bus,
            flags,
            fwd: Some(FwdKind::Mauf),
            poison: None,
        })
    }

    /// Executes a PE-local line one PE at a time.
    ///
    /// The generic path computes every expression into a 4,096-entry buffer and applies writes
    /// in a second pass. No ALU/MAU-only line reads another PE's state, so each PE can compute
    /// all of its expressions and then write them, provided every read of the step happens
    /// before that PE's writes. Lines with msl/msr, L1/L2, matrix or tracing stay generic.
    fn step_fast(&mut self, exprs: &[Expr]) -> Option<Result<(), ExecError>> {
        if self.tracer.borrow().is_some() || exprs.len() > MAX_STEP_EXPRS {
            return None;
        }
        let supported = exprs.iter().all(|e| match &e.op {
            Op::Noforward | Op::Wait(_) | Op::Zero | Op::Imm { .. } => true,
            Op::Alu { name, prec, .. } => {
                !matches!(name, AluOp::Msl | AluOp::Msr | AluOp::Bfn | AluOp::Bfe) && prec.is_some()
            }
            Op::Mau {
                prec,
                matrix: false,
                round,
                ..
            } => matches!(prec, Prec::D | Prec::F | Prec::G | Prec::H)
                && !(matches!(prec, Prec::F | Prec::G) && *round),
            _ => false,
        });
        if !supported {
            return None;
        }
        // A disabled forwarding register makes the generic path produce poison, so keep those
        // lines there.
        for e in exprs {
            for op in &e.srcs {
                if let Operand::Forward { kind, .. } = op {
                    if self.fwd_error[fwd_index(*kind)].is_some() {
                        return None;
                    }
                }
            }
        }
        let single_line_mask = exprs.iter().any(|e| e.dsts.iter().any(has_mask));
        let noforward = exprs.iter().any(|e| matches!(e.op, Op::Noforward));
        if let Err(e) = self.run_fast(exprs, single_line_mask, !noforward) {
            return Some(Err(e));
        }
        if !noforward {
            for kind in [FwdKind::Aluf, FwdKind::Mauf, FwdKind::Mreadf, FwdKind::Lbf] {
                let present = exprs.iter().any(|e| op_fwd_kind(e) == Some(kind));
                self.fwd_error[fwd_index(kind)] = if present {
                    None
                } else if kind == FwdKind::Mreadf {
                    for pe in &mut self.pes {
                        pe.mreadf = [[0; 4]; 4];
                    }
                    None
                } else if kind == FwdKind::Lbf {
                    self.fwd_error[fwd_index(kind)].clone()
                } else {
                    Some(format!("{} is disabled", unit_name(kind)))
                };
            }
        }
        Some(Ok(()))
    }

    fn write_output_parallel(
        &mut self,
        e: &Expr,
        out: &Output,
        flush: Option<MaskSel>,
        single_line_mask: bool,
        mask_state: MaskState,
    ) -> Result<(), ExecError> {
        let Machine { pes, mem, .. } = self;
        let Mem {
            lm0,
            lm1,
            grf0,
            grf1,
        } = mem;
        pes.par_iter_mut()
            .zip(lm0.par_chunks_mut(LM_WORDS))
            .zip(lm1.par_chunks_mut(LM_WORDS))
            .zip(grf0.par_chunks_mut(GRF_WORDS))
            .zip(grf1.par_chunks_mut(GRF_WORDS))
            .enumerate()
            .try_for_each(|(pe, ((((p, lm0), lm1), grf0), grf1))| {
                let mut memory = MemPe {
                    lm0,
                    lm1,
                    grf0,
                    grf1,
                };
                for c in 0..4 {
                    let mut bus = out.bus[pe][c];
                    if let Some(sel) = flush {
                        let f = mask_flags_pe(p, &mask_state, &sel, c);
                        bus = apply_flush(bus, f, sel.ll);
                    }
                    let poison = out
                        .poison
                        .as_ref()
                        .filter(|q| q.hits(pe, c))
                        .map(|q| q.msg.as_str());
                    for d in &e.dsts {
                        write_pe(
                            p,
                            &mask_state,
                            &mut memory,
                            pe,
                            d,
                            c,
                            bus,
                            out.flags[pe][c],
                            single_line_mask,
                            poison,
                        )?;
                    }
                }
                Ok(())
            })
    }

    fn run_fast(
        &mut self,
        exprs: &[Expr],
        single_line_mask: bool,
        update_forward: bool,
    ) -> Result<(), ExecError> {
        let Machine {
            pes,
            mem,
            fwd_error,
            mask_state,
            ..
        } = self;
        let mask_state = *mask_state;
        let Mem {
            lm0,
            lm1,
            grf0,
            grf1,
        } = mem;
        thread_pool().install(|| {
            pes.par_iter_mut()
                .zip(lm0.par_chunks_mut(LM_WORDS))
                .zip(lm1.par_chunks_mut(LM_WORDS))
                .zip(grf0.par_chunks_mut(GRF_WORDS))
                .zip(grf1.par_chunks_mut(GRF_WORDS))
                .enumerate()
                .try_for_each(|(pe, ((((p, lm0), lm1), grf0), grf1))| {
                    let mut memory = MemPe {
                        lm0,
                        lm1,
                        grf0,
                        grf1,
                    };
                    run_fast_pe(
                        p,
                        &mut memory,
                        fwd_error,
                        &mask_state,
                        exprs,
                        single_line_mask,
                        update_forward,
                        pe,
                    )
                })
        })
    }
}

/// Worker pool for the PE-local path. SMT threads hurt this workload, so default to the
/// physical-core count (half the logical count on machines with more than six logical CPUs).
fn thread_pool() -> &'static rayon::ThreadPool {
    static POOL: std::sync::OnceLock<rayon::ThreadPool> = std::sync::OnceLock::new();
    POOL.get_or_init(|| {
        let logical = std::thread::available_parallelism()
            .map(|n| n.get())
            .unwrap_or(1);
        let threads = std::env::var("RAYON_NUM_THREADS")
            .ok()
            .and_then(|s| s.parse::<usize>().ok())
            .filter(|&n| n > 0)
            .unwrap_or_else(|| if logical <= 6 { logical } else { (logical + 1) / 2 });
        rayon::ThreadPoolBuilder::new()
            .num_threads(threads)
            .build()
            .expect("build simulator thread pool")
    })
}

fn fwd_index(k: FwdKind) -> usize {
    match k {
        FwdKind::Aluf => 0,
        FwdKind::Mauf => 1,
        FwdKind::Mreadf => 2,
        FwdKind::Lbf => 3,
    }
}

/// Checks that a block-float block has a common exponent, as the emulator does before a
/// matrix product ("Invalid block float format").
fn check_bf(f: Fmt, block: &[u64], what: &str) -> Result<(), ExecError> {
    let exp = |v: u64| (v >> f.man_bits) & f.exp_max();
    let common = block.iter().map(|&v| exp(v)).max().unwrap_or(0);
    for (i, &v) in block.iter().enumerate() {
        let e = exp(v);
        // Exponent 0 is allowed only in half precision, as the extended representation.
        if e != common && !(f == HALF && e == 0) {
            return Err(ExecError::Runtime(format!(
                "invalid block float in {what}: the exponent of element {i} is not the common exponent {common} (bfn/bfe missing?)"
            )));
        }
    }
    Ok(())
}

fn has_mask(op: &Operand) -> bool {
    matches!(
        op,
        Operand::Mem { mask: Some(_), .. }
            | Operand::Bar { mask: Some(_), .. }
            | Operand::Omr { mask: Some(_), .. }
    )
}

/// Whether word `i` of the bus (0 = MSB) is written at all under the given mask flags.
fn word_enabled(mflags: Option<(u8, bool)>, i: usize) -> bool {
    match mflags {
        None => true,
        Some((f, true)) => (f >> (3 - i)) & 1 == 1,
        // Long word masks affect only the MSB long word (four halves).
        // The LSB long word is always written, including when all flags are zero.
        // Confirmed with nonzero old/new sentinels against the official emulator.
        Some((f, false)) => {
            if i < 2 {
                (f >> (2 - 2 * i)) & 3 != 0
            } else {
                true
            }
        }
    }
}

/// Merges a new word into an old one under the mask flags (long word masks are per half word).
fn merge_word(old: u32, new: u32, mflags: Option<(u8, bool)>, i: usize) -> u32 {
    match mflags {
        Some((f, false)) if i < 2 => {
            let hi = (f >> (3 - 2 * i)) & 1 == 1;
            let lo = (f >> (2 - 2 * i)) & 1 == 1;
            let m = (if hi { 0xffff_0000 } else { 0 }) | (if lo { 0x0000_ffff } else { 0 });
            (old & !m) | (new & m)
        }
        _ => new,
    }
}

fn apply_flush(bus: Bus, f: u8, ll: bool) -> Bus {
    let mut out = bus;
    for i in 0..4 {
        if ll {
            if (f >> (3 - i)) & 1 == 0 {
                out[i] = 0;
            }
        } else if i < 2 {
            let hi = (f >> (3 - 2 * i)) & 1 == 1;
            let lo = (f >> (2 - 2 * i)) & 1 == 1;
            let m = (if hi { 0xffff_0000 } else { 0 }) | (if lo { 0x0000_ffff } else { 0 });
            out[i] &= m;
        }
    }
    out
}

fn prec_bits(prec: Option<Prec>) -> u32 {
    match prec {
        Some(Prec::D) | Some(Prec::L) => 64,
        Some(Prec::F) | Some(Prec::G) | Some(Prec::I) | None => 32,
        Some(Prec::H) | Some(Prec::S) => 16,
    }
}

fn lower(f: Fmt) -> Option<Fmt> {
    if f == DOUBLE {
        Some(SINGLE)
    } else if f == SINGLE {
        Some(HALF)
    } else {
        None
    }
}

fn higher(f: Fmt) -> Option<Fmt> {
    if f == HALF {
        Some(SINGLE)
    } else if f == SINGLE {
        Some(DOUBLE)
    } else {
        None
    }
}

/// Extracts `n` elements of `width` bits from the bus, MSB first.
fn unpack(bus: &Bus, width: u32, n: usize) -> Vec<u64> {
    let full = ((bus[0] as u128) << 96)
        | ((bus[1] as u128) << 64)
        | ((bus[2] as u128) << 32)
        | bus[3] as u128;
    (0..n)
        .map(|i| ((full >> (128 - width * (i as u32 + 1))) & ((1u128 << width) - 1)) as u64)
        .collect()
}

/// Packs elements of `width` bits into a bus from the MSB, leaving the rest zero.
fn pack(vals: &[u64], width: u32) -> Bus {
    let mut full: u128 = 0;
    for (i, v) in vals.iter().enumerate() {
        full |= (*v as u128 & ((1u128 << width) - 1)) << (128 - width * (i as u32 + 1));
    }
    [
        (full >> 96) as u32,
        (full >> 64) as u32,
        (full >> 32) as u32,
        full as u32,
    ]
}

/// Extracts `n` elements of `width` bits from the bus without allocating.
fn unpack_fixed(bus: &Bus, width: u32, n: usize) -> [u64; 4] {
    let full = ((bus[0] as u128) << 96)
        | ((bus[1] as u128) << 64)
        | ((bus[2] as u128) << 32)
        | bus[3] as u128;
    let mut out = [0u64; 4];
    for (i, value) in out.iter_mut().enumerate().take(n) {
        *value = ((full >> (128 - width * (i as u32 + 1))) & ((1u128 << width) - 1)) as u64;
    }
    out
}

/// Elements of the MSB long word as a fixed array, with the element count.
fn lanes_fixed(bus: &Bus, bits: u32) -> ([u64; 4], usize) {
    let n = (64 / bits) as usize;
    (unpack_fixed(bus, bits, n), n)
}

fn pack_lanes(vals: &[u64], bits: u32) -> [u32; 2] {
    let b = pack(vals, bits);
    [b[0], b[1]]
}

fn splat(lane: u64, bits: u32) -> Bus {
    let n = (128 / bits) as usize;
    let vals = [lane; 8];
    pack(&vals[..n], bits)
}

/// Rounds the four single-precision words of a bus to half precision (`r` operand option).
fn round_bus(bus: Bus) -> Bus {
    let mut out = [0u32; 4];
    let mut halves = [0u64; 4];
    for (i, half) in halves.iter_mut().enumerate() {
        *half = float::encode(HALF, float::decode(SINGLE, bus[i] as u64));
    }
    out[0] = ((halves[0] << 16) | halves[1]) as u32;
    out[1] = ((halves[2] << 16) | halves[3]) as u32;
    out
}

/// Mask flags (4 bits per cycle) from per-lane conditions of the MSB long word.
fn lane_flags(vals: &[u64], bits: u32, cond: impl Fn(u64) -> bool) -> u8 {
    match bits {
        64 => {
            if cond(vals[0]) {
                0xf
            } else {
                0
            }
        }
        32 => (if cond(vals[0]) { 0xc } else { 0 }) | (if cond(vals[1]) { 0x3 } else { 0 }),
        _ => (0..4)
            .map(|i| (cond(vals[i]) as u8) << (3 - i))
            .fold(0, |a, b| a | b),
    }
}

fn sign_extend(v: u64, bits: u32) -> i64 {
    ((v << (64 - bits)) as i64) >> (64 - bits)
}

fn fmt_of(prec: Prec) -> Fmt {
    match prec {
        Prec::D => DOUBLE,
        Prec::H => HALF,
        _ => SINGLE,
    }
}

/// Applies an ALU operation to each lane of the MSB long word. Returns lanes and mask flags.
fn alu_lanes(
    name: AluOp,
    prec: Prec,
    unsigned: bool,
    x: &[u64],
    y: &[u64],
) -> Result<([u64; 4], u8), ExecError> {
    let bits = prec_bits(Some(prec));
    let mask = if bits == 64 {
        u64::MAX
    } else {
        (1u64 << bits) - 1
    };
    let is_float = matches!(prec, Prec::D | Prec::F | Prec::H);
    let n = x.len();
    let mut out = [0u64; 4];
    let mut cond = [false; 4];
    for i in 0..n {
        let (a, b) = (x[i], y[i]);
        let (sa, sb) = (sign_extend(a, bits), sign_extend(b, bits));
        let msb = |v: u64, k: u32| (v >> (bits - 1 - k)) & 1;
        let (r, c) = match name {
            AluOp::Inc | AluOp::Dec | AluOp::Add | AluOp::Sub => {
                let rhs = match name {
                    AluOp::Inc | AluOp::Dec => 1,
                    _ => b,
                };
                let sub = matches!(name, AluOp::Dec | AluOp::Sub);
                let r = if sub {
                    a.wrapping_sub(rhs)
                } else {
                    a.wrapping_add(rhs)
                } & mask;
                let c = if unsigned {
                    // no overflow (no carry out / no borrow)
                    if sub {
                        a >= rhs
                    } else {
                        (a as u128 + rhs as u128) <= mask as u128
                    }
                } else {
                    msb(r, 0) == 0
                };
                (r, c)
            }
            AluOp::Not => {
                let r = !a & mask;
                (r, r == 0)
            }
            AluOp::Lnot => {
                let r = (a == 0) as u64;
                (r, r == 0)
            }
            AluOp::And => (a & b, a & b == 0),
            AluOp::Or => (a | b, a | b == 0),
            AluOp::Xor => (a ^ b, a ^ b == 0),
            AluOp::Lsl | AluOp::Lsr | AluOp::Bsl | AluOp::Bsr => {
                let s = (b % (2 * bits as u64)) as u32;
                let r = match name {
                    AluOp::Lsl => {
                        if s >= bits {
                            0
                        } else {
                            (a << s) & mask
                        }
                    }
                    AluOp::Lsr => {
                        let s = s.min(bits);
                        if unsigned {
                            if s >= bits {
                                0
                            } else {
                                a >> s
                            }
                        } else {
                            ((sa >> s.min(63)) as u64) & mask
                        }
                    }
                    _ => {
                        let s = if s >= bits { s - bits } else { s };
                        let left = name == AluOp::Bsl;
                        if s == 0 {
                            a
                        } else if left {
                            ((a << s) | (a >> (bits - s))) & mask
                        } else {
                            ((a >> s) | (a << (bits - s))) & mask
                        }
                    }
                };
                (r, r == 0)
            }
            AluOp::Max | AluOp::Min => {
                let pick_x = if is_float {
                    float_max_pick_x(a, b, bits, name == AluOp::Max)
                } else if unsigned {
                    if name == AluOp::Max {
                        a >= b
                    } else {
                        a <= b
                    }
                } else if name == AluOp::Max {
                    sa >= sb
                } else {
                    sa <= sb
                };
                (if pick_x { a } else { b }, pick_x)
            }
            AluOp::Packbit => (((a << 1) | msb(b, 0)) & mask, msb(b, 0) == 0),
            AluOp::Relu | AluOp::Relu0 | AluOp::Relu1 | AluOp::Relu2 | AluOp::Relu3 => {
                let k = match name {
                    AluOp::Relu1 => 1,
                    AluOp::Relu2 => 2,
                    AluOp::Relu3 => 3,
                    _ => 0,
                };
                let neg_zero = 1u64 << (bits - 1);
                (if msb(a, k) == 0 { b } else { neg_zero }, msb(a, k) == 0)
            }
            AluOp::Rsqrt => (float_rsqrt(fmt_of(prec), a), msb(a, 0) == 0),
            AluOp::Floor => (float_floor(fmt_of(prec), a), false),
            AluOp::Ftoi => (float_ftoi(fmt_of(prec), a, unsigned, bits), false),
            AluOp::Lrelud | AluOp::Lreluo | AluOp::Ilrelud => {
                (float_lrelu(name, fmt_of(prec), b), msb(a, 0) == 0)
            }
            other => return Err(ExecError::Unsupported(format!("ALU {other:?}"))),
        };
        out[i] = r & mask;
        cond[i] = c;
    }
    let flags = match bits {
        64 => {
            if cond[0] {
                0xf
            } else {
                0
            }
        }
        32 => (if cond[0] { 0xc } else { 0 }) | (if cond[1] { 0x3 } else { 0 }),
        _ => (0..4)
            .map(|i| (cond[i] as u8) << (3 - i))
            .fold(0, |a, b| a | b),
    };
    Ok((out, flags))
}

/// Float max/min (SDM 3.6.12.13). Returns whether x is output.
fn float_max_pick_x(a: u64, b: u64, bits: u32, max: bool) -> bool {
    if a == b {
        return true;
    }
    let fmt = match bits {
        64 => DOUBLE,
        32 => SINGLE,
        _ => HALF,
    };
    let exp = |v: u64| (v >> fmt.man_bits) & fmt.exp_max();
    if exp(a) == 0 && exp(b) == 0 {
        return true;
    }
    // Otherwise compare as sign-magnitude integers, which also orders infinities by mantissa.
    let key = |v: u64| -> i128 {
        let neg = (v >> (bits - 1)) & 1 == 1;
        let mag = (v & ((1u64 << (bits - 1)) - 1)) as i128;
        let mag = if exp(v) == 0 { 0 } else { mag };
        if neg {
            -mag
        } else {
            mag
        }
    };
    if max {
        key(a) >= key(b)
    } else {
        key(a) <= key(b)
    }
}

/// Approximate reciprocal square root (SDM 3.6.12.9, "about 5 bits").
///
/// Not specified in the SDM; extracted from the emulator for all precisions. The result depends
/// only on the parity of the exponent and the top 4 mantissa bits; its mantissa has 5 bits.
/// Zero and infinity are not special, and the sign is ignored.
fn float_rsqrt(fmt: Fmt, v: u64) -> u64 {
    const MANT5: [[u64; 16]; 2] = [
        [13, 11, 10, 9, 8, 7, 6, 5, 4, 4, 3, 2, 2, 1, 1, 0],
        [
            31, 30, 28, 26, 25, 23, 22, 21, 20, 19, 18, 17, 16, 15, 14, 13,
        ],
    ];
    let m = fmt.man_bits;
    let e = (v >> m) & fmt.exp_max();
    let top4 = (v >> (m - 4)) & 15;
    let bias = fmt.bias() as u64;
    let out_e = bias + (bias + 1) / 2 - 1 - e.div_ceil(2);
    (out_e << m) | (MANT5[(e & 1) as usize][top4 as usize] << (m - 5))
}

fn float_floor(fmt: Fmt, v: u64) -> u64 {
    match float::decode(fmt, v) {
        Val::Zero { .. } | Val::Inf { .. } => v,
        Val::Fin { neg, sig, exp } => {
            if exp >= 0 {
                return v;
            }
            let sh = (-exp) as u32;
            let int = if sh >= 128 { 0 } else { sig >> sh };
            let frac = sh >= 128 || sig & ((1u128 << sh) - 1) != 0;
            let int = if neg && frac { int + 1 } else { int };
            if int == 0 {
                // Zero result: the mantissa is flushed to zero (SDM 3.6.12.10).
                return ((neg as u64) << (fmt.width() - 1)) & !0;
            }
            float::round_pack(fmt, neg, int, 0)
        }
    }
}

/// Leaky-ReLU variants (SDM 3.6.12.18).
///
/// `lrelud`/`lreluo` halve or eighth the second input by decrementing its exponent, and
/// `ilrelud` doubles it by incrementing its exponent. SDM 3.6.12.18 defines an underflow result
/// as a value with a negative sign bit and zero exponent/mantissa (that is, -0), and an overflow
/// result as an all-ones exponent with the sign and mantissa of the input. Infinities have no
/// further encoding to underflow to, so they stay unchanged.
fn float_lrelu(name: AluOp, fmt: Fmt, y: u64) -> u64 {
    let m = fmt.man_bits;
    let zero = 1u64 << (fmt.width() - 1);
    let e = (y >> m) & fmt.exp_max();
    let emax = fmt.exp_max();
    match name {
        AluOp::Lrelud => {
            if e == emax {
                y
            } else if e <= 1 {
                zero
            } else {
                y - (1u64 << m)
            }
        }
        AluOp::Lreluo => {
            if e == emax {
                y
            } else if e <= 3 {
                zero
            } else {
                y - (3u64 << m)
            }
        }
        AluOp::Ilrelud => {
            if e == emax {
                y
            } else {
                y + (1u64 << m)
            }
        }
        _ => y,
    }
}

fn float_ftoi(fmt: Fmt, v: u64, unsigned: bool, bits: u32) -> u64 {
    let (smax, smin, umax) = (
        (1i128 << (bits - 1)) - 1,
        -(1i128 << (bits - 1)),
        (1i128 << bits) - 1,
    );
    let (neg, mag): (bool, i128) = match float::decode(fmt, v) {
        Val::Zero { .. } => (false, 0),
        Val::Inf { neg } => (neg, i128::MAX),
        Val::Fin { neg, sig, exp } => {
            let m = if exp >= 0 {
                if exp > 70 {
                    i128::MAX
                } else {
                    (sig as i128) << exp
                }
            } else if -exp >= 127 {
                0
            } else {
                (sig >> (-exp) as u32) as i128
            };
            (neg, m)
        }
    };
    let mask = if bits == 64 {
        u64::MAX
    } else {
        (1u64 << bits) - 1
    };
    if unsigned {
        (mag.min(umax) as u64) & mask
    } else {
        let s = if neg { (-mag).max(smin) } else { mag.min(smax) };
        (s as i64 as u64) & mask
    }
}

/// MAU mask flags: the inverted sign bit of each output element (SDM 3.6.9.26).
fn mau_flags(out: &[u64], f: Fmt) -> u8 {
    let pos = |v: u64| (v >> (f.width() - 1)) & 1 == 0;
    match out.len() {
        1 if f.width() == 64 => {
            if pos(out[0]) {
                0xf
            } else {
                0
            }
        }
        // Rounded to one word: the LSB two flags are 0.
        1 => {
            if pos(out[0]) {
                0xc
            } else {
                0
            }
        }
        2 => (if pos(out[0]) { 0xc } else { 0 }) | (if pos(out[1]) { 0x3 } else { 0 }),
        _ => (0..4)
            .map(|i| (pos(out[i]) as u8) << (3 - i))
            .fold(0, |a, b| a | b),
    }
}

fn prec_fmt(prec: Prec) -> Fmt {
    match prec {
        Prec::D => DOUBLE,
        Prec::H => HALF,
        _ => SINGLE,
    }
}

/// Logical shape of the matrix register for a precision: (rows, physical row step).
fn mat_shape(prec: Prec) -> (usize, usize) {
    match prec {
        Prec::D => (4, 4),
        Prec::H => (16, 1),
        _ => (8, 2),
    }
}

impl Machine {
    /// Raw bits of logical element (row, col) of a matrix register face.
    fn mat_get(&self, mab: usize, side: usize, prec: Prec, row: usize, col: usize) -> u64 {
        let (_, step) = mat_shape(prec);
        let r = &self.mats[mab][side][row * step];
        match prec {
            Prec::D => ((r[2 * col] as u64) << 32) | r[2 * col + 1] as u64,
            Prec::H => ((r[col / 2] >> if col % 2 == 0 { 16 } else { 0 }) & 0xffff) as u64,
            _ => r[col] as u64,
        }
    }

    /// Reads the raw elements of an operand for mwrite / matrix-vector input, applying the
    /// sign inversion, precision extension and rounding options. Values keep their bit pattern,
    /// because block-float values must not be normalized.
    fn read_raw_elems(
        &self,
        pe: usize,
        op: &Operand,
        f: Fmt,
        n: usize,
        cycle: usize,
    ) -> Result<Vec<u64>, ExecError> {
        let bus = self.read_raw(pe, op, cycle)?;
        let (neg, ext, rnd) = match op {
            Operand::Mem { neg, ext, rnd, .. } | Operand::Forward { neg, ext, rnd, .. } => {
                (*neg, *ext, *rnd)
            }
            _ => (false, false, false),
        };
        let raw_fmt = if ext {
            lower(f).ok_or_else(|| ExecError::Unsupported("extension below half".into()))?
        } else if rnd {
            higher(f).ok_or_else(|| ExecError::Unsupported("rounding from above double".into()))?
        } else {
            f
        };
        let raw = unpack(&bus, raw_fmt.width(), n);
        Ok(raw
            .into_iter()
            .map(|r| {
                let v = if raw_fmt == f {
                    r
                } else {
                    float::encode(f, float::decode(raw_fmt, r))
                };
                if neg {
                    v ^ (1 << (f.width() - 1))
                } else {
                    v
                }
            })
            .collect())
    }

    fn compute_mwrite(&self, e: &Expr, prec: Prec) -> Result<Vec<MatWrite>, ExecError> {
        let Some(Operand::Mat {
            y,
            wl,
            row: Some(addr),
        }) = e.dsts.first()
        else {
            return Err(ExecError::Unsupported(format!(
                "mwrite destination in `{}`",
                e.text
            )));
        };
        let side = *y as usize;
        let f = prec_fmt(prec);
        let (rows, step) = mat_shape(prec);
        let two_rows = prec == Prec::H && *wl == 4;
        // Elements each PE supplies per cycle: d 1, f/g 2, h 4 (8 with two rows).
        let per_pe = match prec {
            Prec::D => 1,
            Prec::H => {
                if two_rows {
                    8
                } else {
                    4
                }
            }
            _ => 2,
        };
        let mut out = Vec::new();
        for mab in 0..PES / 4 {
            for c in 0..4 {
                let mut elems: Vec<u64> = Vec::with_capacity(per_pe * 4);
                for p in 0..4 {
                    elems.extend(self.read_raw_elems(mab * 4 + p, &e.srcs[0], f, per_pe, c)?);
                }
                let nrows = if two_rows { 2 } else { 1 };
                for k in 0..nrows {
                    let row = if two_rows {
                        (*addr as usize + 2 * c) % rows + k
                    } else {
                        (*addr as usize + c) % rows
                    };
                    let row_elems: Vec<u64> = if two_rows {
                        // row a: halves 0..3 of each PE; row a+1: halves 4..7.
                        (0..16)
                            .map(|j| elems[(j / 4) * 8 + k * 4 + j % 4])
                            .collect()
                    } else {
                        elems.clone()
                    };
                    let words = pack_row(&row_elems, f.width());
                    let expr = self.tracer.borrow().as_ref().map(|t| t.expr).unwrap_or(0);
                    out.push(MatWrite {
                        expr,
                        cycle: c,
                        mab,
                        side,
                        phys_row: row * step,
                        words: words.map(Some),
                    });
                }
            }
        }
        Ok(out)
    }

    fn compute_mread(&self, e: &Expr, prec: Prec) -> Result<Output, ExecError> {
        let Some(Operand::Mat {
            y, row: Some(addr), ..
        }) = e.srcs.first()
        else {
            return Err(ExecError::Unsupported(format!(
                "mread source in `{}`",
                e.text
            )));
        };
        let side = *y as usize;
        let f = prec_fmt(prec);
        let (rows, _) = mat_shape(prec);
        let mut bus = vec![[[0u32; 4]; 4]; PES];
        if self.tracer.borrow().is_none() {
            let mats = &self.mats;
            bus.par_chunks_mut(4)
                .enumerate()
                .try_for_each(|(mab, chunk)| -> Result<(), ExecError> {
                    for c in 0..4 {
                        for p in 0..4 {
                            let vals: Vec<u64> = match prec {
                                Prec::D => vec![mat_get_face(
                                    &mats[mab],
                                    side,
                                    prec,
                                    p,
                                    (*addr as usize + c) % rows,
                                )],
                                Prec::H => {
                                    let c0 = (*addr as usize + 2 * c) % rows;
                                    let mut v: Vec<u64> = (0..4)
                                        .map(|k| {
                                            mat_get_face(&mats[mab], side, prec, 4 * p + k, c0)
                                        })
                                        .collect();
                                    v.extend((0..4).map(|k| {
                                        mat_get_face(
                                            &mats[mab],
                                            side,
                                            prec,
                                            4 * p + k,
                                            (c0 + 1) % rows,
                                        )
                                    }));
                                    v
                                }
                                _ => {
                                    let col = (*addr as usize + c) % rows;
                                    vec![
                                        mat_get_face(&mats[mab], side, prec, 2 * p, col),
                                        mat_get_face(&mats[mab], side, prec, 2 * p + 1, col),
                                    ]
                                }
                            };
                            chunk[p][c] = pack(&vals, f.width());
                        }
                    }
                    Ok(())
                })?;
            return Ok(Output {
                bus,
                flags: vec![[0; 4]; PES],
                fwd: Some(FwdKind::Mreadf),
                poison: None,
            });
        }
        for mab in 0..PES / 4 {
            for c in 0..4 {
                for p in 0..4 {
                    let vals: Vec<u64> = match prec {
                        Prec::D => {
                            vec![self.mat_get(mab, side, prec, p, (*addr as usize + c) % rows)]
                        }
                        Prec::H => {
                            let c0 = (*addr as usize + 2 * c) % rows;
                            let mut v: Vec<u64> = (0..4)
                                .map(|k| self.mat_get(mab, side, prec, 4 * p + k, c0))
                                .collect();
                            v.extend((0..4).map(|k| {
                                self.mat_get(mab, side, prec, 4 * p + k, (c0 + 1) % rows)
                            }));
                            v
                        }
                        _ => {
                            let col = (*addr as usize + c) % rows;
                            vec![
                                self.mat_get(mab, side, prec, 2 * p, col),
                                self.mat_get(mab, side, prec, 2 * p + 1, col),
                            ]
                        }
                    };
                    bus[mab * 4 + p][c] = pack(&vals, f.width());
                }
            }
        }
        Ok(Output {
            bus,
            flags: vec![[0; 4]; PES],
            fwd: Some(FwdKind::Mreadf),
            poison: None,
        })
    }

    fn compute_mat(
        &self,
        e: &Expr,
        prec: Prec,
        kind: MauKind,
        half: Option<char>,
        round: bool,
    ) -> Result<Output, ExecError> {
        let Some(Operand::Mat {
            y: side_y,
            row: None,
            ..
        }) = e.srcs.first()
        else {
            return Err(ExecError::Unsupported(format!(
                "matrix operand in `{}`",
                e.text
            )));
        };
        let side = *side_y as usize;
        let (bf, fx, fy, fout) = match prec {
            Prec::D => (
                float::BF_DOUBLE,
                DOUBLE,
                DOUBLE,
                if round { SINGLE } else { DOUBLE },
            ),
            Prec::F => (float::BF_SINGLE, SINGLE, SINGLE, SINGLE),
            Prec::G => (float::BF_PSEUDO, SINGLE, SINGLE, SINGLE),
            Prec::H => (
                float::BF_HALF,
                HALF,
                SINGLE,
                if round { HALF } else { SINGLE },
            ),
            _ => unreachable!(),
        };
        // Elements per PE: x vector, y vector and output.
        let (nx, ny) = match prec {
            Prec::D => (1, 1),
            Prec::F => (1, 2),
            Prec::G => (2, 2),
            _ => (4, 4),
        };
        let (rows, _) = mat_shape(prec);
        let mut bus = vec![[[0u32; 4]; 4]; PES];
        let mut flags = vec![[0u8; 4]; PES];
        let mut poison: Option<Poison> = None;
        for mab in 0..PES / 4 {
            for c in 0..4 {
                let mut x: Vec<u64> = Vec::new();
                let mut yv: Vec<Val> = Vec::new();
                for p in 0..4 {
                    x.extend(self.read_raw_elems(mab * 4 + p, &e.srcs[1], fx, nx, c)?);
                    if kind == MauKind::Fma {
                        let raw = self.read_raw_elems(mab * 4 + p, &e.srcs[2], fy, ny, c)?;
                        yv.extend(raw.into_iter().map(|r| float::decode(fy, r)));
                    } else {
                        yv.extend((0..ny).map(|_| Val::Zero { neg: false }));
                    }
                }
                let active = |i: usize| match half {
                    Some('u') => i < 2,
                    Some('d') => i >= 2,
                    _ => true,
                };
                // Invalid block-float input poisons this MAB's results of this cycle.
                let mut bad = check_bf(fx, &x, "the vector input").err();
                for i in (0..rows).filter(|&i| active(i)) {
                    if bad.is_some() {
                        break;
                    }
                    let cols: Vec<u64> = (0..rows)
                        .map(|j| self.mat_get(mab, side, prec, i, j))
                        .collect();
                    let row: Vec<u64> = if prec == Prec::F {
                        cols.iter().step_by(2).copied().collect()
                    } else {
                        cols
                    };
                    bad = check_bf(fx, &row, "a matrix row").err();
                }
                if let Some(ExecError::Runtime(msg)) = bad {
                    let pz = poison.get_or_insert_with(|| Poison {
                        msg,
                        at: vec![[false; 4]; PES],
                    });
                    for p in 0..4 {
                        pz.at[mab * 4 + p][c] = true;
                    }
                }
                let out: Vec<u64> = (0..rows)
                    .map(|i| {
                        let dot = if active(i) {
                            let arow: Vec<u64> = match prec {
                                // fmfma uses columns 0, 2, 4, 6.
                                Prec::F => (0..4)
                                    .map(|j| self.mat_get(mab, side, prec, i, 2 * j))
                                    .collect(),
                                _ => (0..rows)
                                    .map(|j| self.mat_get(mab, side, prec, i, j))
                                    .collect(),
                            };
                            float::bf_dot(bf, &arow, &x)
                        } else {
                            (Val::Zero { neg: false }, None)
                        };
                        float::mat_fma(fout, dot, yv[i])
                    })
                    .collect();
                let per_pe = rows / 4;
                for p in 0..4 {
                    let o = &out[p * per_pe..(p + 1) * per_pe];
                    bus[mab * 4 + p][c] = pack(o, fout.width());
                    flags[mab * 4 + p][c] = mau_flags(o, fout);
                }
            }
        }
        Ok(Output {
            bus,
            flags,
            fwd: Some(FwdKind::Mauf),
            poison,
        })
    }

    fn compute_bfn(
        &self,
        e: &Expr,
        name: AluOp,
        prec: Prec,
        arg: Option<u8>,
    ) -> Result<Output, ExecError> {
        let f = prec_fmt(prec);
        let keep = match prec {
            Prec::G => 18,
            Prec::H => arg.unwrap_or(9) as u32,
            _ => f.man_bits,
        };
        let extended = name == AluOp::Bfe;
        let blocks: Vec<Vec<(usize, usize)>> = match prec {
            Prec::D => vec![(0..4).map(|p| (p, 0)).collect()],
            Prec::F => vec![
                (0..4).map(|p| (p, 0)).collect(),
                (0..4).map(|p| (p, 1)).collect(),
            ],
            Prec::G => vec![(0..4).flat_map(|p| [(p, 0), (p, 1)]).collect()],
            _ => vec![
                (0..4).flat_map(|p| (0..4).map(move |k| (p, k))).collect(),
                (0..4).flat_map(|p| (4..8).map(move |k| (p, k))).collect(),
            ],
        };
        let w = f.width();
        let mut bus = vec![[[0u32; 4]; 4]; PES];
        if self.tracer.borrow().is_none() {
            let pes = &self.pes;
            let mem = &self.mem;
            let fwd_error = &self.fwd_error;
            let src = &e.srcs[0];
            bus.par_chunks_mut(4)
                .enumerate()
                .try_for_each(|(mab, chunk)| -> Result<(), ExecError> {
                    for c in 0..4 {
                        let ins: Vec<Bus> = (0..4)
                            .map(|p| {
                                read_alu_input_pe(
                                    &pes[mab * 4 + p],
                                    mem,
                                    fwd_error,
                                    mab * 4 + p,
                                    src,
                                    Some(prec),
                                    c,
                                )
                            })
                            .collect::<Result<_, _>>()?;
                        // Blocks: lists of (pe, element index within the PE's bus, width in bits).
                        // Except for half precision, the LSB long word of the output is 0 (emulator).
                        let mut outs: Vec<Bus> = if prec == Prec::H {
                            ins.clone()
                        } else {
                            ins.iter().map(|b| [b[0], b[1], 0, 0]).collect()
                        };
                        for blk in &blocks {
                            let vals: Vec<u64> = blk
                                .iter()
                                .map(|&(p, k)| unpack(&ins[p], w, k + 1)[k])
                                .collect();
                            let conv = float::block_float(f, &vals, keep, extended);
                            for (&(p, k), v) in blk.iter().zip(conv) {
                                let mut all = unpack(&outs[p], w, (128 / w) as usize);
                                all[k] = v;
                                outs[p] = pack(&all, w);
                            }
                        }
                        for p in 0..4 {
                            chunk[p][c] = outs[p];
                        }
                    }
                    Ok(())
                })?;
            return Ok(Output {
                bus,
                flags: vec![[0; 4]; PES],
                fwd: Some(FwdKind::Aluf),
                poison: None,
            });
        }
        for mab in 0..PES / 4 {
            for c in 0..4 {
                let ins: Vec<Bus> = (0..4)
                    .map(|p| self.read_alu_input(mab * 4 + p, &e.srcs[0], Some(prec), c))
                    .collect::<Result<_, _>>()?;
                // Blocks: lists of (pe, element index within the PE's bus, width in bits).
                // Except for half precision, the LSB long word of the output is 0 (emulator).
                let mut outs: Vec<Bus> = if prec == Prec::H {
                    ins.clone()
                } else {
                    ins.iter().map(|b| [b[0], b[1], 0, 0]).collect()
                };
                for blk in &blocks {
                    let vals: Vec<u64> = blk
                        .iter()
                        .map(|&(p, k)| unpack(&ins[p], w, k + 1)[k])
                        .collect();
                    let conv = float::block_float(f, &vals, keep, extended);
                    for (&(p, k), v) in blk.iter().zip(conv) {
                        let mut all = unpack(&outs[p], w, (128 / w) as usize);
                        all[k] = v;
                        outs[p] = pack(&all, w);
                    }
                }
                for p in 0..4 {
                    bus[mab * 4 + p][c] = outs[p];
                }
            }
        }
        Ok(Output {
            bus,
            flags: vec![[0; 4]; PES],
            fwd: Some(FwdKind::Aluf),
            poison: None,
        })
    }
}

/// Packs the elements of one logical matrix row into the 8 words of a physical row.
fn pack_row(elems: &[u64], width: u32) -> [u32; 8] {
    let mut out = [0u32; 8];
    let per_word = (32 / width.min(32)) as usize;
    if width == 64 {
        for (j, v) in elems.iter().enumerate().take(4) {
            out[2 * j] = (v >> 32) as u32;
            out[2 * j + 1] = *v as u32;
        }
    } else {
        for (j, v) in elems.iter().enumerate().take(8 * per_word) {
            let shift = 32 - width * (j % per_word + 1) as u32;
            out[j / per_word] |= ((*v as u32) & ((1u64 << width) - 1) as u32) << shift;
        }
    }
    out
}

fn mem_name(m: MemKind) -> &'static str {
    match m {
        MemKind::Lm0 => "lm0",
        MemKind::Lm1 => "lm1",
        MemKind::Grf0 => "grf0",
        MemKind::Grf1 => "grf1",
        MemKind::T => "t",
        _ => "other",
    }
}

fn fwd_name(k: FwdKind) -> &'static str {
    match k {
        FwdKind::Aluf => "aluf",
        FwdKind::Mauf => "mauf",
        FwdKind::Mreadf => "mreadf",
        FwdKind::Lbf => "lbf",
    }
}

// ---- parallel PE-local execution --------------------------------------------------------

fn word_addrs_pe(p: &Pe, pe: usize, mem: MemKind, wl: u8, addr: &Addr, cycle: usize) -> usize {
    let bar = match mem {
        MemKind::Lm0 => p.bar0,
        MemKind::Lm1 => p.bar1,
        _ => 0,
    } as usize;
    let wl = wl as usize;
    if !addr.t_indirect && addr.madpe.is_none() {
        return (bar + addr.cycles[cycle] as usize) & !(wl - 1);
    }
    let t = if addr.t_indirect {
        p.t[cycle * 4 + 1] as usize
    } else {
        0
    };
    let maadj = match addr.madpe {
        Some(m) if (pe % 4) as u8 <= m => wl,
        _ => 0,
    };
    (bar + t + addr.cycles[cycle] as usize + maadj) & !(wl - 1)
}

fn read_raw_pe<M: MemRead>(
    p: &Pe,
    memory: &M,
    fwd_error: &[Option<String>; 4],
    pe: usize,
    op: &Operand,
    cycle: usize,
) -> Result<Bus, ExecError> {
    Ok(match op {
        Operand::Mem { mem: MemKind::T, .. } => {
            let b = cycle * 4;
            [p.t[b], p.t[b + 1], p.t[b + 2], p.t[b + 3]]
        }
        Operand::Mem { mem, wl, addr, .. } => {
            let a = word_addrs_pe(p, pe, *mem, *wl, addr, cycle);
            let mut bus = [0; 4];
            for i in 0..*wl as usize {
                bus[i] = memory.peek(*mem, pe, a + i);
            }
            bus
        }
        Operand::Forward { kind, .. } if fwd_error[fwd_index(*kind)].is_some() => {
            return Err(ExecError::Runtime(format!(
                "accessing {} forwarding register failed; the error on the previous step is: {}",
                unit_name(*kind),
                fwd_error[fwd_index(*kind)].as_ref().unwrap()
            )))
        }
        Operand::Forward { kind, .. } => match kind {
            FwdKind::Aluf => p.aluf[cycle],
            FwdKind::Mauf => p.mauf[cycle],
            FwdKind::Mreadf => p.mreadf[cycle],
            FwdKind::Lbf => p.lbf[cycle],
        },
        Operand::Fixed(_) => {
            return Err(ExecError::Unsupported(
                "fixed operands depend on precision".into(),
            ))
        }
        other => return Err(ExecError::Unsupported(format!("read of {other:?}"))),
    })
}

fn read_alu_input_pe<M: MemRead>(
    p: &Pe,
    memory: &M,
    fwd_error: &[Option<String>; 4],
    pe: usize,
    op: &Operand,
    prec: Option<Prec>,
    cycle: usize,
) -> Result<Bus, ExecError> {
    if let Operand::Fixed(k) = op {
        let id = PeId::from_index(pe);
        let v: u64 = match k {
            FixedKind::L2bid => (id.group * 2 + id.l2b) as u64,
            FixedKind::L1bid => id.l1b as u64,
            FixedKind::Mabid => id.mab as u64,
            FixedKind::Peid => (id.mab * 4 + id.pe) as u64,
            FixedKind::Subpeid => id.pe as u64,
            FixedKind::Msb1 => u64::MAX,
        };
        let bits = prec_bits(prec);
        let lane = if *k == FixedKind::Msb1 {
            1u64 << (bits - 1)
        } else {
            v
        };
        return Ok(splat(lane, bits));
    }
    let bus = read_raw_pe(p, memory, fwd_error, pe, op, cycle)?;
    let rnd = matches!(
        op,
        Operand::Mem { rnd: true, .. } | Operand::Forward { rnd: true, .. }
    );
    Ok(if rnd { round_bus(bus) } else { bus })
}

fn compute_alu_pe<M: MemRead>(
    p: &Pe,
    memory: &M,
    fwd_error: &[Option<String>; 4],
    e: &Expr,
    name: AluOp,
    prec: Option<Prec>,
    unsigned: bool,
    pe: usize,
) -> Result<([Bus; 4], [u8; 4]), ExecError> {
    if matches!(name, AluOp::Msl | AluOp::Msr) {
        return Err(ExecError::Unsupported(
            "cross-PE ALU is not PE-local".into(),
        ));
    }
    let n = name.inputs();
    let bits = prec_bits(prec);
    let mut x = [[0u32; 4]; 4];
    let mut y = [[0u32; 4]; 4];
    for c in 0..4 {
        x[c] = read_alu_input_pe(p, memory, fwd_error, pe, &e.srcs[0], prec, c)?;
        if n > 1 {
            y[c] = read_alu_input_pe(p, memory, fwd_error, pe, &e.srcs[1], prec, c)?;
        }
    }
    let mut bus = [[0u32; 4]; 4];
    let mut flags = [0u8; 4];
    for c in 0..4 {
        let (out, fl) = match name {
            AluOp::Passa => {
                let (xl, count) = lanes_fixed(&x[c], bits);
                let fl = lane_flags(&xl[..count], bits, |v| v == 0);
                (x[c], fl)
            }
            _ => {
                let (xl, count) = lanes_fixed(&x[c], bits);
                let (yl, _) = lanes_fixed(&y[c], bits);
                let (msb, fl) =
                    alu_lanes(name, prec.unwrap(), unsigned, &xl[..count], &yl[..count])?;
                let lo = pack_lanes(&msb[..count], bits);
                ([lo[0], lo[1], x[c][2], x[c][3]], fl)
            }
        };
        bus[c] = out;
        flags[c] = fl;
    }
    Ok((bus, flags))
}

fn compute_vec_pe<M: MemRead>(
    p: &Pe,
    memory: &M,
    fwd_error: &[Option<String>; 4],
    e: &Expr,
    prec: Prec,
    kind: MauKind,
    half: Option<char>,
    round: bool,
    pe: usize,
) -> Result<([Bus; 4], [u8; 4]), ExecError> {
    let (fa, fc, fout): (Fmt, Fmt, Fmt) = match prec {
        Prec::D => (DOUBLE, DOUBLE, if round { SINGLE } else { DOUBLE }),
        Prec::F | Prec::G => (SINGLE, SINGLE, SINGLE),
        Prec::H => (HALF, SINGLE, if round { HALF } else { SINGLE }),
        _ => {
            return Err(ExecError::Unsupported(format!(
                "vector op precision {prec:?}"
            )))
        }
    };
    if matches!(prec, Prec::F | Prec::G) && round {
        return Err(ExecError::Unsupported("fv*r".into()));
    }
    let lanes_n = match prec {
        Prec::D => 1,
        Prec::F | Prec::G => 2,
        _ => 4,
    };
    let (ia, ib, ic): (Option<usize>, Option<usize>, Option<usize>) = match kind {
        MauKind::Fma => (Some(0), Some(1), Some(2)),
        MauKind::Mul => (Some(0), Some(1), None),
        MauKind::Add => (Some(0), None, Some(1)),
        MauKind::Passa => (Some(0), None, None),
    };
    let read_vals = |idx: Option<usize>, f: Fmt, c: usize| -> Result<Option<[Val; 4]>, ExecError> {
        let Some(i) = idx else { return Ok(None) };
        let op = &e.srcs[i];
        let bus = read_raw_pe(p, memory, fwd_error, pe, op, c)?;
        let (neg, ext, rnd) = match op {
            Operand::Mem { neg, ext, rnd, .. } | Operand::Forward { neg, ext, rnd, .. } => {
                (*neg, *ext, *rnd)
            }
            _ => (false, false, false),
        };
        let raw_fmt = if ext {
            lower(f).ok_or_else(|| ExecError::Unsupported("extension below half".into()))?
        } else if rnd {
            higher(f).ok_or_else(|| ExecError::Unsupported("rounding from above double".into()))?
        } else {
            f
        };
        let raw = unpack_fixed(&bus, raw_fmt.width(), lanes_n);
        let mut vals = [Val::Zero { neg: false }; 4];
        for (l, value) in vals.iter_mut().enumerate() {
            let v = float::decode(raw_fmt, raw[l]);
            let v = if rnd {
                float::decode(f, float::encode(f, v))
            } else {
                v
            };
            *value = if neg { v.negate() } else { v };
        }
        Ok(Some(vals))
    };
    let one_a = float::decode(fa, (fa.bias() as u64) << fa.man_bits);
    let zero = Val::Zero { neg: false };
    let mul_here = match half {
        Some('u') => pe % 4 < 2,
        Some('d') => pe % 4 >= 2,
        _ => true,
    };
    let mut bus = [[0u32; 4]; 4];
    let mut flags = [0u8; 4];
    for c in 0..4 {
        let a = read_vals(ia, fa, c)?.unwrap();
        let b = read_vals(ib, fa, c)?;
        let cv = read_vals(ic, fc, c)?;
        let mut out = [0u64; 4];
        for (l, value) in out.iter_mut().enumerate().take(lanes_n) {
            let (x, y) = if mul_here {
                (a[l], b.map_or(one_a, |b| b[l]))
            } else {
                (zero, zero)
            };
            let z = cv.map_or(zero, |c| c[l]);
            *value = float::vfma(fa, fout, x, y, z);
        }
        bus[c] = pack(&out[..lanes_n], fout.width());
        flags[c] = mau_flags(&out[..lanes_n], fout);
    }
    Ok((bus, flags))
}

fn compute_expr_pe<M: MemRead>(
    p: &Pe,
    memory: &M,
    fwd_error: &[Option<String>; 4],
    e: &Expr,
    pe: usize,
) -> Result<([Bus; 4], [u8; 4]), ExecError> {
    Ok(match &e.op {
        Op::Alu {
            name,
            prec,
            unsigned,
            ..
        } => compute_alu_pe(p, memory, fwd_error, e, *name, *prec, *unsigned, pe)?,
        Op::Mau {
            prec,
            kind,
            half,
            round,
            matrix: false,
        } => compute_vec_pe(p, memory, fwd_error, e, *prec, *kind, *half, *round, pe)?,
        Op::Zero => ([[0; 4]; 4], [0; 4]),
        Op::Imm { value, u } => {
            let bus = if *u {
                [*value, 0, *value, 0]
            } else {
                [*value; 4]
            };
            ([bus; 4], [0; 4])
        }
        _ => ([[0; 4]; 4], [0; 4]),
    })
}

fn mask_flags_pe(p: &Pe, _st: &MaskState, sel: &MaskSel, cycle: usize) -> u8 {
    match sel.source {
        MaskSource::Pattern(pat) => {
            if pat[cycle] {
                0xf
            } else {
                0
            }
        }
        MaskSource::Entry(n) => match n {
            0 => 0xf,
            1..=15 => ((p.mask[n as usize] >> (4 * cycle)) & 0xf) as u8,
            _ => {
                if (n >> (3 - cycle)) & 1 == 1 {
                    0xf
                } else {
                    0
                }
            }
        },
    }
}

fn write_pe<M: MemWrite>(
    p: &mut Pe,
    st: &MaskState,
    memory: &mut M,
    pe: usize,
    d: &Operand,
    cycle: usize,
    bus: Bus,
    flags: u8,
    single_line: bool,
    poison: Option<&str>,
) -> Result<(), ExecError> {
    let fail = |enabled: bool| -> Result<(), ExecError> {
        match poison {
            Some(msg) if enabled => Err(ExecError::Runtime(msg.to_string())),
            _ => Ok(()),
        }
    };
    let directive = |mem: Option<MemKind>, omr: bool| -> Option<MaskSel> {
        if single_line {
            return None;
        }
        let t = st.targets;
        let on = match mem {
            Some(MemKind::Grf0) => t.grf0,
            Some(MemKind::Grf1) => t.grf1,
            Some(MemKind::T) => t.t,
            Some(MemKind::Lm0) => t.lm0,
            Some(MemKind::Lm1) => t.lm1,
            _ => omr && t.mask_reg,
        };
        if on && st.entry != 0 {
            Some(MaskSel {
                ll: st.wl == 4,
                source: MaskSource::Entry(st.entry),
            })
        } else {
            None
        }
    };
    match d {
        Operand::Nowrite => {}
        Operand::Mem {
            mem,
            wl,
            addr,
            mask,
            ..
        } => {
            let sel = mask.or_else(|| directive(Some(*mem), false));
            let mflags = sel.map(|s| (mask_flags_pe(p, st, &s, cycle), s.ll));
            let words = if *mem == MemKind::T {
                4
            } else {
                *wl as usize
            };
            let any = (0..words).any(|i| word_enabled(mflags, i));
            fail(any)?;
            if !any {
                return Ok(());
            }
            if *mem == MemKind::T {
                for i in 0..4 {
                    if word_enabled(mflags, i) {
                        p.t[cycle * 4 + i] = merge_word(p.t[cycle * 4 + i], bus[i], mflags, i);
                    }
                }
                return Ok(());
            }
            let a = word_addrs_pe(p, pe, *mem, *wl, addr, cycle);
            for i in 0..*wl as usize {
                if word_enabled(mflags, i) {
                    let old = memory.peek(*mem, pe, a + i);
                    memory.poke(*mem, pe, a + i, merge_word(old, bus[i], mflags, i));
                }
            }
        }
        Operand::Bar { lm1, mask, .. } => {
            let mem = if *lm1 { MemKind::Lm1 } else { MemKind::Lm0 };
            let sel = mask.or_else(|| directive(Some(mem), false));
            if let Some(s) = sel {
                if mask_flags_pe(p, st, &s, cycle) == 0 {
                    return Ok(());
                }
            }
            fail(true)?;
            if *lm1 {
                p.bar1 = bus[0] & 0xfff;
            } else {
                p.bar0 = bus[0] & 0xfff;
            }
        }
        Operand::Omr { entry, mask } => {
            if *entry == 0 || *entry > 15 {
                return Err(ExecError::Unsupported(format!(
                    "mask register entry {entry} is read-only"
                )));
            }
            let sel = mask.or_else(|| directive(None, true));
            let f = match sel {
                Some(s) => flags & mask_flags_pe(p, st, &s, cycle),
                None => flags,
            };
            let e = &mut p.mask[*entry as usize];
            *e = (*e & !(0xf << (4 * cycle))) | ((f as u16) << (4 * cycle));
        }
        other => return Err(ExecError::Unsupported(format!("write to {other:?}"))),
    }
    Ok(())
}

fn run_fast_pe<M: MemWrite>(
    p: &mut Pe,
    memory: &mut M,
    fwd_error: &[Option<String>; 4],
    mask_state: &MaskState,
    exprs: &[Expr],
    single_line_mask: bool,
    update_forward: bool,
    pe: usize,
) -> Result<(), ExecError> {
    if exprs.len() == 1 {
        let e = &exprs[0];
        if matches!(e.op, Op::Noforward | Op::Wait(_)) {
            return Ok(());
        }
        let kind = op_fwd_kind(e);
        let (buses, flags) = compute_expr_pe(p, &*memory, fwd_error, e, pe)?;
        for c in 0..4 {
            let mut bus = buses[c];
            if let Some(sel) = e.flush {
                let f = mask_flags_pe(p, mask_state, &sel, c);
                bus = apply_flush(bus, f, sel.ll);
            }
            for d in &e.dsts {
                write_pe(p, mask_state, memory, pe, d, c, bus, flags[c], single_line_mask, None)?;
            }
            if update_forward {
                if let Some(kind) = kind {
                    match kind {
                        FwdKind::Aluf => p.aluf[c] = bus,
                        FwdKind::Mauf => p.mauf[c] = bus,
                        FwdKind::Mreadf => p.mreadf[c] = bus,
                        FwdKind::Lbf => p.lbf[c] = bus,
                    }
                }
            }
        }
        return Ok(());
    }
    let mut buses = [[[0u32; 4]; 4]; MAX_STEP_EXPRS];
    let mut flags = [[0u8; 4]; MAX_STEP_EXPRS];
    for (ei, e) in exprs.iter().enumerate() {
        let (b, f) = compute_expr_pe(p, &*memory, fwd_error, e, pe)?;
        buses[ei] = b;
        flags[ei] = f;
    }
    for (ei, e) in exprs.iter().enumerate() {
        for c in 0..4 {
            let mut bus = buses[ei][c];
            if let Some(sel) = e.flush {
                let f = mask_flags_pe(p, mask_state, &sel, c);
                bus = apply_flush(bus, f, sel.ll);
            }
            for d in &e.dsts {
                write_pe(p, mask_state, memory, pe, d, c, bus, flags[ei][c], single_line_mask, None)?;
            }
        }
    }
    if update_forward {
        for (ei, e) in exprs.iter().enumerate() {
            let Some(kind) = op_fwd_kind(e) else { continue };
            for c in 0..4 {
                let mut bus = buses[ei][c];
                if let Some(sel) = e.flush {
                    let f = mask_flags_pe(p, mask_state, &sel, c);
                    bus = apply_flush(bus, f, sel.ll);
                }
                match kind {
                    FwdKind::Aluf => p.aluf[c] = bus,
                    FwdKind::Mauf => p.mauf[c] = bus,
                    FwdKind::Mreadf => p.mreadf[c] = bus,
                    FwdKind::Lbf => p.lbf[c] = bus,
                }
            }
        }
    }
    Ok(())
}

/// Reads one matrix element from a MAB's faces.
fn mat_get_face(face: &[MatFace; 2], side: usize, prec: Prec, row: usize, col: usize) -> u64 {
    let (_, step) = mat_shape(prec);
    let r = &face[side][row * step];
    match prec {
        Prec::D => ((r[2 * col] as u64) << 32) | r[2 * col + 1] as u64,
        Prec::H => ((r[col / 2] >> if col % 2 == 0 { 16 } else { 0 }) & 0xffff) as u64,
        _ => r[col] as u64,
    }
}

#[cfg(test)]
mod lrelu_tests {
    use super::*;

    fn relu(name: AluOp, prec: Prec, x: u64, y: u64) -> (u64, u8) {
        let bits = prec_bits(Some(prec));
        let n = (64 / bits) as usize;
        let xs = vec![x; n];
        let ys = vec![y; n];
        let (out, flags) = alu_lanes(name, prec, false, &xs, &ys).unwrap();
        (out[0], flags)
    }

    #[test]
    fn single_leaky_relu() {
        let one = 0x3f80_0000; // 1.0f
        assert_eq!(relu(AluOp::Lrelud, Prec::F, 0, one), (0x3f00_0000, 0xf)); // 0.5
        assert_eq!(relu(AluOp::Lreluo, Prec::F, 0, one), (0x3e00_0000, 0xf)); // 0.125
        assert_eq!(relu(AluOp::Ilrelud, Prec::F, 0, one), (0x4000_0000, 0xf)); // 2.0
        let neg_one = 0xbf80_0000;
        assert_eq!(relu(AluOp::Lrelud, Prec::F, 0, neg_one), (0xbf00_0000, 0xf));
        assert_eq!(relu(AluOp::Lreluo, Prec::F, 0, neg_one), (0xbe00_0000, 0xf));
        // The negative first input disables the pass-through and clears the flags.
        assert_eq!(relu(AluOp::Lrelud, Prec::F, 0x8000_0000, one), (0x3f00_0000, 0));
        assert_eq!(relu(AluOp::Relu, Prec::F, 0x8000_0000, one), (0x8000_0000, 0));
    }

    #[test]
    fn single_leaky_relu_underflow_and_overflow() {
        // Zero and the minimum normals underflow to -0 (negative sign bit) for /2 and /8.
        assert_eq!(relu(AluOp::Lrelud, Prec::F, 0, 0x8000_0000), (0x8000_0000, 0xf));
        assert_eq!(relu(AluOp::Lrelud, Prec::F, 0, 0x0080_0000), (0x8000_0000, 0xf));
        assert_eq!(relu(AluOp::Lreluo, Prec::F, 0, 0x0100_0000), (0x8000_0000, 0xf));
        assert_eq!(relu(AluOp::Lreluo, Prec::F, 0, 0x0180_0000), (0x8000_0000, 0xf));
        // An increment turns zero into the minimum normal and overflows to infinity.
        assert_eq!(relu(AluOp::Ilrelud, Prec::F, 0, 0), (0x0080_0000, 0xf));
        assert_eq!(relu(AluOp::Ilrelud, Prec::F, 0, 0x8000_0000), (0x8080_0000, 0xf));
        assert_eq!(relu(AluOp::Ilrelud, Prec::F, 0, 0x7f00_0000), (0x7f80_0000, 0xf));
        assert_eq!(relu(AluOp::Ilrelud, Prec::F, 0, 0x7f80_0000), (0x7f80_0000, 0xf));
        assert_eq!(relu(AluOp::Lrelud, Prec::F, 0, 0x7f80_0000), (0x7f80_0000, 0xf));
    }

    #[test]
    fn half_and_double_leaky_relu() {
        // Half 1.0 is 0x3e00; halving decrements the 6-bit exponent by one.
        assert_eq!(relu(AluOp::Lrelud, Prec::H, 0, 0x3e00), (0x3c00, 0xf));
        assert_eq!(relu(AluOp::Ilrelud, Prec::H, 0, 0), (0x0200, 0xf));
        // Double 1.0 is 0x3ff0000000000000.
        assert_eq!(
            relu(AluOp::Lrelud, Prec::D, 0, 0x3ff0_0000_0000_0000),
            (0x3fe0_0000_0000_0000, 0xf)
        );
        assert_eq!(relu(AluOp::Lrelud, Prec::D, 0, 0x8000_0000_0000_0000), (0x8000_0000_0000_0000, 0xf));
    }
}
