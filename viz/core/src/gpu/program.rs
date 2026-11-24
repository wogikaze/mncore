//! Whole-program execution on the GPU.
//!
//! `lower_program` turns a parsed VSM program into the sequence of GPU
//! operations that the per-line kernels execute (the same order and
//! forwarding rules as `gpu_run_program` always used). The sequence can then
//! run either one kernel launch per operation (`Gpu::run_op`) or as a single
//! cooperative launch of the `run_program` interpreter kernel
//! (`Gpu::load_program` + `Gpu::launch_program`).
//!
//! In the interpreter, block B owns L1B B: its 64 PEs, 16 MABs, its L1BM and
//! its `$lbi`. Work on those is always done by the owning block, so the only
//! cross-block data are L1BMs read by L2BM reductions/multicasts, the L2BMs,
//! PDM, DRAM and the DAR state. `load_program` tracks which blocks touched each
//! of those since the last grid barrier and inserts a barrier only in front of
//! an operation that would otherwise race with another block.

use std::ffi::c_void;

use super::*;
use crate::machine::MaskState;
use crate::vsm::{Line, Operand};

/// One kernel-level operation of a lowered program.
#[derive(Clone, Copy, Debug)]
pub enum GpuOp {
    Alu(AluLine, bool),
    Bfn(BfnLine, bool),
    Mau(MauLine, bool),
    L1Read(L1ReadLine),
    L1Write(L1WriteLine, bool),
    L2(L2Line),
    L2Red(L2RedLine),
    MatWrite(MatWriteLine),
    MatRead(MatReadLine, bool),
    MatMau(MatMauLine, bool),
    Mv(MvLine),
    ClearMreadf,
}

/// A lowered program: the operations and the number of instruction words of
/// the source (nops included), which is what words/s rates count.
pub struct LoweredProgram {
    pub ops: Vec<GpuOp>,
    pub words: u64,
    pub pe_lines: usize,
    pub mv_lines: usize,
    /// Device DRAM long words per group the MV statements need.
    pub dram_longs: u64,
    pub scratch_longs: u64,
    pub indirect: bool,
}

fn fwd_index(kind: FwdKind) -> usize {
    match kind {
        FwdKind::Mauf => 0,
        FwdKind::Aluf => 1,
        FwdKind::Mreadf => 2,
        FwdKind::Lbf => 3,
    }
}

fn reads_fwd(e: &Expr, kind: FwdKind) -> bool {
    e.srcs
        .iter()
        .any(|o| matches!(o, Operand::Forward { kind: k, .. } if *k == kind))
}

fn is_lbi_write(e: &Expr) -> bool {
    matches!(e.op, Op::L1(_)) && e.dsts.iter().any(|d| matches!(d, Operand::L1bm { addr: None, .. }))
}

fn is_lbi_read(e: &Expr) -> bool {
    matches!(e.op, Op::L1(_)) && e.srcs.iter().any(|d| matches!(d, Operand::L1bm { addr: None, .. }))
}

fn fwd_written_by(expr: &Expr) -> Option<usize> {
    match &expr.op {
        Op::Mau { .. } => Some(0),
        Op::Alu { .. } | Op::Imm { .. } | Op::Zero => Some(1),
        Op::MatRead { .. } => Some(2),
        Op::L1(_) if matches!(expr.srcs.first(), Some(Operand::L1bm { .. })) => Some(3),
        _ => None,
    }
}

/// Orders one step's expressions so that forwarding reads see the previous
/// step's value (reader before writer) while `$lbi` reads see the current
/// step's PE-to-L1BM writes (writer before reader).
fn order_step(exprs: &[Expr]) -> Vec<&Expr> {
    let n = exprs.len();
    let mut edge = vec![vec![false; n]; n];
    let writes: Vec<Option<usize>> = exprs.iter().map(fwd_written_by).collect();
    for i in 0..n {
        for k in [FwdKind::Mauf, FwdKind::Aluf, FwdKind::Mreadf, FwdKind::Lbf] {
            if reads_fwd(&exprs[i], k) {
                for j in 0..n {
                    if i != j && writes[j].is_some() && writes[j] == Some(fwd_index(k)) {
                        edge[i][j] = true;
                    }
                }
            }
        }
        if is_lbi_read(&exprs[i]) {
            for j in 0..n {
                if i != j && is_lbi_write(&exprs[j]) {
                    edge[i][j] = true;
                }
            }
        }
    }
    let mut used = vec![false; n];
    let mut out = Vec::with_capacity(n);
    for _ in 0..n {
        let pick = (0..n).find(|&i| !used[i] && (0..n).all(|j| j == i || used[j] || !edge[j][i]));
        let Some(pick) = pick else { break };
        used[pick] = true;
        out.push(&exprs[pick]);
    }
    for (i, e) in exprs.iter().enumerate() {
        if !used[i] {
            out.push(e);
        }
    }
    out
}

/// Lowers a parsed program to GPU operations, rejecting what the backend
/// cannot run (with the line number in the message).
pub fn lower_program(program: &[(usize, Line)]) -> Result<LoweredProgram, String> {
    let mut mask = MaskState::default();
    let mut ops = Vec::new();
    let mut pe_lines = 0usize;
    let mut mv_lines = 0usize;
    let mut words = 0u64;
    let mut dram_longs = 0u64;
    let mut scratch_longs = 1u64;
    let mut indirect = false;
    let mut fwd_enabled = [false; 4];
    let mut clear_mreadf_at_end = false;
    for (lineno, line) in program {
        words += u64::from(line.words());
        match line {
            Line::Nop { .. } => {}
            Line::MaskDirective { wl, targets, entry } => {
                mask = MaskState { wl: *wl, targets: *targets, entry: *entry };
            }
            Line::Mv(mv) => {
                let desc = mv_line_from_mv(mv).ok_or(format!("line {lineno}: no GPU MV descriptor"))?;
                dram_longs = dram_longs.max(desc.dram_longs_needed());
                scratch_longs = scratch_longs.max(desc.scratch_longs_needed());
                indirect |= desc.uses_indirect();
                mv_lines += 1;
                ops.push(GpuOp::Mv(desc));
            }
            Line::Pe(exprs) => {
                pe_lines += 1;
                crate::issue::check(exprs).map_err(|e| format!("line {lineno}: {e}"))?;
                // SDM 3.6.4/3.6.13: a wait must accompany another PE expression and
                // its tag must be nonzero. Every MV completes in program order, so an
                // issued wait is already satisfied.
                if exprs.iter().any(|e| matches!(e.op, Op::Wait(_))) {
                    if exprs.len() < 2 {
                        return Err(format!("line {lineno}: wait without another PE expression"));
                    }
                    if exprs.iter().any(|e| matches!(e.op, Op::Wait(0))) {
                        return Err(format!("line {lineno}: wait tag 0 is invalid"));
                    }
                }
                let update_forward = !exprs.iter().any(|e| matches!(e.op, Op::Noforward));
                let has_mread = exprs.iter().any(|e| matches!(e.op, Op::MatRead { .. }));
                for expr in exprs {
                    for src in &expr.srcs {
                        if let Operand::Forward { kind, .. } = src {
                            if !fwd_enabled[fwd_index(*kind)] {
                                return Err(format!(
                                    "line {lineno}: forwarding register {kind:?} is not enabled"
                                ));
                            }
                        }
                    }
                }
                let mut fwd_written = [false; 4];
                for expr in order_step(exprs) {
                    if matches!(expr.op, Op::Noforward | Op::Wait(_)) {
                        continue;
                    }
                    if update_forward {
                        if let Some(index) = fwd_written_by(expr) {
                            fwd_written[index] = true;
                        }
                    }
                    let op = if let Some(l) = alu_line_from_expr(expr, mask) {
                        GpuOp::Alu(l, update_forward)
                    } else if let Some(l) = bfn_line_from_expr_state(expr, mask) {
                        GpuOp::Bfn(l, update_forward)
                    } else if let Some(l) = l1_read_line_from_expr(expr, mask) {
                        GpuOp::L1Read(l)
                    } else if let Some(l) = l1_write_line_from_expr(expr) {
                        GpuOp::L1Write(l, update_forward)
                    } else if let Some(l) = l2_line_from_expr(expr) {
                        GpuOp::L2(l)
                    } else if let Some(l) = l2_reduce_line_from_expr(expr) {
                        GpuOp::L2Red(l)
                    } else if let Some(l) = mat_write_line_from_expr(expr) {
                        GpuOp::MatWrite(l)
                    } else if let Some(l) = mat_read_line_from_expr(expr, mask) {
                        GpuOp::MatRead(l, update_forward)
                    } else if let Some(l) = mat_mau_line_from_expr(expr, mask) {
                        GpuOp::MatMau(l, update_forward)
                    } else if let Some(l) = mau_line_from_expr(expr, mask) {
                        GpuOp::Mau(l, update_forward)
                    } else {
                        return Err(format!("line {lineno}: no GPU descriptor for {:?}", expr.text));
                    };
                    validate(&op).map_err(|e| format!("line {lineno}: {e}"))?;
                    ops.push(op);
                }
                fwd_enabled = if update_forward { fwd_written } else { [false; 4] };
                // CPU steps without a matrix read expose zero on mreadf. A
                // step can only read mreadf right after a matrix read wrote it
                // (fwd_enabled), so intermediate clears are never observed;
                // only the final state needs the last one (pushed below).
                if update_forward {
                    clear_mreadf_at_end = !has_mread;
                }
            }
            other => return Err(format!("line {lineno}: unsupported line {other:?}")),
        }
    }
    if clear_mreadf_at_end {
        ops.push(GpuOp::ClearMreadf);
    }
    if indirect {
        // A DAR entry decides the address at run time. One million long words
        // per group (8 MiB) covers the checked-in programs; out-of-range
        // indirect accesses are counted by the kernel.
        dram_longs = dram_longs.max(1 << 20);
    }
    Ok(LoweredProgram { ops, words, pe_lines, mv_lines, dram_longs, scratch_longs, indirect })
}

/// The descriptor checks of the per-line launchers, done once at lowering.
fn validate(op: &GpuOp) -> Result<(), String> {
    match op {
        GpuOp::Mau(l, _) if l.prec > 3 || l.kind > 3 || l.half > 2 || l.ndst > 16 => {
            Err("mau_line descriptor is out of range".into())
        }
        GpuOp::L1Read(l) if l.wl != 2 && l.wl != 4 => Err(format!("unsupported L1BM access length {}", l.wl)),
        GpuOp::L1Read(l) if l.ndst == 0 || l.ndst > 4 => {
            Err(format!("unsupported L1BM destination count {}", l.ndst))
        }
        GpuOp::L1Write(l, _) if l.wl != 2 && l.wl != 4 => {
            Err(format!("unsupported L1BM access length {}", l.wl))
        }
        GpuOp::L2Red(l) if l.op < 2 && l.bits != 16 && l.bits != 32 && l.bits != 64 => {
            Err(format!("unsupported RRN width {}", l.bits))
        }
        GpuOp::MatWrite(l) if l.prec > 3 || l.side > 1 => Err("mat_write_line descriptor is out of range".into()),
        GpuOp::MatMau(l, _) if l.prec > 3 || l.side > 1 || l.kind > 3 || l.half > 2 || l.ndst > 16 => {
            Err("mat_mau_line descriptor is out of range".into())
        }
        _ => Ok(()),
    }
}

// ---- interpreter descriptors (mirror the structs in program_kernel.cu) ----

const PK_ALU: u32 = 0;
const PK_BFN: u32 = 1;
const PK_MAU: u32 = 2;
const PK_L1R: u32 = 3;
const PK_L1W: u32 = 4;
const PK_L2: u32 = 5;
const PK_L2RED: u32 = 6;
const PK_MATW: u32 = 7;
const PK_MATR: u32 = 8;
const PK_MATMAU: u32 = 9;
const PK_MV: u32 = 10;
const PK_CLEAR_MREADF: u32 = 11;

pub(super) const PF_UPDATE: u32 = 1;
pub(super) const PF_BARRIER: u32 = 2;

/// Names of the interpreter instruction kinds, indexed by kind.
pub const PROGRAM_KIND_NAMES: [&str; 12] = [
    "alu", "bfn", "mau", "l1_read", "l1_write", "l2", "l2_reduce", "mat_write", "mat_read",
    "mat_mau", "mv", "clear_mreadf",
];
/// Flag of an instruction that starts with a grid barrier.
pub const PROGRAM_FLAG_BARRIER: u32 = PF_BARRIER;

/// Shared-memory descriptor capacity of the interpreter (program_kernel.cu).
const PROG_DESC_LONGS: u32 = 160;

/// Blocks of the interpreter launch: one per L1B.
pub const PROGRAM_BLOCKS: u32 = 64;
/// Threads per interpreter block.
pub const PROGRAM_THREADS: u32 = 128;

#[repr(C)]
#[derive(Clone, Copy, Default)]
struct ProgIns {
    kind: u32,
    flags: u32,
    off: u32,
    aux: u32,
}

#[repr(C)]
#[derive(Clone, Copy)]
pub(super) struct DevStateArgs {
    lm0: u64,
    lm1: u64,
    grf0: u64,
    grf1: u64,
    mauf: u64,
    aluf: u64,
    mask: u64,
    t: u64,
    mreadf: u64,
    lbf: u64,
    bar0: u64,
    bar1: u64,
    mats: u64,
    l1bm: u64,
    l2bm: u64,
    lbi: u64,
    pdm: u64,
    dram: u64,
    scratch: u64,
    dram_longs: u64,
    dar: u64,
    darbuf: u64,
    dar_addr: u64,
    mv_errors: u64,
}

impl DevStateArgs {
    pub(super) fn from_state(state: &GpuState) -> Self {
        DevStateArgs {
            lm0: state.lm0,
            lm1: state.lm1,
            grf0: state.grf0,
            grf1: state.grf1,
            mauf: state.mauf,
            aluf: state.aluf,
            mask: state.mask,
            t: state.t,
            mreadf: state.mreadf,
            lbf: state.lbf,
            bar0: state.bar0,
            bar1: state.bar1,
            mats: state.mats,
            l1bm: state.l1bm,
            l2bm: state.l2bm,
            lbi: state.lbi,
            pdm: state.pdm,
            dram: state.dram,
            scratch: state.scratch,
            dram_longs: state.dram_longs,
            dar: state.dar,
            darbuf: state.darbuf,
            dar_addr: state.dar_addr,
            mv_errors: state.mv_errors,
        }
    }
}

#[repr(C)]
#[derive(Clone, Copy, Default)]
struct L1ReadArgs {
    op: i32,
    has_addr: i32,
    addr: u32,
    mabdiff: i32,
    wl: i32,
    ndst: i32,
    dm: [i32; 4],
    db: [[u32; 4]; 4],
    dw: [i32; 4],
    mk: [i32; 4],
    mke: [i32; 4],
    mkp: [i32; 4],
    mkl: [i32; 4],
    dt: [i32; 4],
    dma: [i32; 4],
    fk: i32,
    fe: i32,
    fp: i32,
    fll: i32,
}

#[repr(C)]
#[derive(Clone, Copy, Default)]
struct L1WriteArgs {
    op: i32,
    mab_sel: i32,
    mabdiff: i32,
    has_addr: i32,
    addr: u32,
    dwl: i32,
    smem: i32,
    s: [u32; 4],
    swl: i32,
    st: i32,
    sma: i32,
    two_src: i32,
    bits: i32,
    rrn: i32,
    round_it: i32,
    ext: i32,
    fk: i32,
    fe: i32,
    fp: i32,
    fll: i32,
}

#[repr(C)]
#[derive(Clone, Copy, Default)]
struct L2Args {
    op: i32,
    a0: u32,
    a1: u32,
    l1b: i32,
    mask: i32,
    l2b: i32,
}

#[repr(C)]
#[derive(Clone, Copy, Default)]
struct L2RedArgs {
    op: i32,
    a0: u32,
    a1: u32,
    mask: i32,
    immode: i32,
    bits: i32,
    kind: i32,
}

#[repr(C)]
#[derive(Clone, Copy, Default)]
struct MvArgs {
    src_addr: u64,
    dst_addr: u64,
    size: u64,
    nd: u64,
    total: u64,
    mode: i32,
    phase: i32,
    parallel: i32,
    src_mem: i32,
    src_group: i32,
    src_l2b: i32,
    dst_mem: i32,
    dst_group: i32,
    dst_l2b: i32,
    rrn_op: i32,
    rrn_bits: i32,
    src_indirect: i32,
    dst_indirect: i32,
}

fn l1_read_args(line: &L1ReadLine) -> L1ReadArgs {
    let mut a = L1ReadArgs {
        op: line.op as i32,
        has_addr: line.addr.is_some() as i32,
        addr: line.addr.unwrap_or(0),
        mabdiff: line.mabdiff as i32,
        wl: line.wl as i32,
        ndst: line.ndst as i32,
        fk: line.flush.kind as i32,
        fe: line.flush.entry as i32,
        fp: line.flush.pattern as i32,
        fll: line.flush.ll as i32,
        ..Default::default()
    };
    for i in 0..4 {
        let d = line.dsts[i];
        a.dm[i] = d.dst.mem as i32;
        a.db[i] = d.dst.base;
        a.dw[i] = d.dst.wl as i32;
        a.mk[i] = d.mask.kind as i32;
        a.mke[i] = d.mask.entry as i32;
        a.mkp[i] = d.mask.pattern as i32;
        a.mkl[i] = d.mask.ll as i32;
        a.dt[i] = d.dst.t_indirect as i32;
        a.dma[i] = madpe_arg(d.dst.madpe);
    }
    a
}

fn l1_write_args(line: &L1WriteLine) -> L1WriteArgs {
    L1WriteArgs {
        op: line.op as i32,
        mab_sel: line.mab as i32,
        mabdiff: line.mabdiff as i32,
        has_addr: line.addr.is_some() as i32,
        addr: line.addr.unwrap_or(0),
        dwl: line.wl as i32,
        smem: line.src.mem as i32,
        s: line.src.base,
        swl: line.src.wl as i32,
        st: line.src.t_indirect as i32,
        sma: madpe_arg(line.src.madpe),
        two_src: line.two_src as i32,
        bits: line.bits as i32,
        rrn: line.rrn as i32,
        round_it: line.round as i32,
        ext: line.ext as i32,
        fk: line.flush.kind as i32,
        fe: line.flush.entry as i32,
        fp: line.flush.pattern as i32,
        fll: line.flush.ll as i32,
    }
}

fn mv_args(line: &MvLine, phase: i32) -> MvArgs {
    MvArgs {
        src_addr: line.src.addr,
        dst_addr: line.dst.addr,
        size: line.size,
        nd: line.nd,
        total: line.threads(),
        mode: line.mode as i32,
        phase,
        parallel: line.parallel as i32,
        src_mem: line.src.mem as i32,
        src_group: line.src.group as i32,
        src_l2b: line.src.l2b as i32,
        dst_mem: line.dst.mem as i32,
        dst_group: line.dst.group as i32,
        dst_l2b: line.dst.l2b as i32,
        rrn_op: line.rrn_op as i32,
        rrn_bits: line.rrn_bits as i32,
        src_indirect: line.src.indirect as i32,
        dst_indirect: line.dst.indirect as i32,
    }
}

fn bytes_of<T: Copy>(value: &T) -> &[u8] {
    // SAFETY: the descriptors are plain `repr(C)` structs of integers.
    unsafe { std::slice::from_raw_parts(value as *const T as *const u8, std::mem::size_of::<T>()) }
}

// ---- cross-block hazard tracking ----

/// Which blocks touch a resource: one block, or all of them (grid-stride MV).
#[derive(Clone, Copy, PartialEq, Eq)]
enum Exec {
    Block(u32),
    All,
}

#[derive(Clone, Copy, Default)]
struct Touch {
    bits: u64,
    all: bool,
}

impl Touch {
    fn add(&mut self, e: Exec) {
        match e {
            Exec::Block(b) => self.bits |= 1 << b,
            Exec::All => self.all = true,
        }
    }
    /// Whether a block other than `e` (or every block) touched the resource.
    fn foreign(&self, e: Exec) -> bool {
        match e {
            Exec::Block(b) => self.all || self.bits & !(1u64 << b) != 0,
            Exec::All => self.all || self.bits != 0,
        }
    }
}

const R_L1BM: usize = 0; // + l1b (64)
const R_LBI: usize = 64; // + l1b (64)
const R_L2BM: usize = 128; // + l2b (8)
const R_PDM: usize = 136;
const R_DRAM: usize = 137;
const R_SCRATCH: usize = 138;
const R_DAR: usize = 139;
const R_DARBUF: usize = 140;
const R_DARADDR: usize = 141;
const RESOURCES: usize = 142;

struct Hazards {
    reads: Vec<Touch>,
    writes: Vec<Touch>,
}

impl Hazards {
    fn new() -> Self {
        Hazards { reads: vec![Touch::default(); RESOURCES], writes: vec![Touch::default(); RESOURCES] }
    }
    /// Records the accesses of one operation and says whether a grid barrier
    /// must come first (the tracking restarts after one).
    fn access(&mut self, list: &[(usize, Exec, bool)]) -> bool {
        let conflict = list.iter().any(|&(r, e, write)| {
            self.writes[r].foreign(e) || (write && self.reads[r].foreign(e))
        });
        if conflict {
            self.reads.iter_mut().for_each(|t| *t = Touch::default());
            self.writes.iter_mut().for_each(|t| *t = Touch::default());
        }
        for &(r, e, write) in list {
            if write {
                self.writes[r].add(e);
            } else {
                self.reads[r].add(e);
            }
        }
        conflict
    }
}

fn mv_mem_resources(mem: u8) -> Vec<usize> {
    match mem {
        0 => vec![R_PDM],
        1 => vec![R_DRAM],
        _ => (0..8).map(|j| R_L2BM + j).collect(),
    }
}

/// Resources an operation touches outside the owning block's PE state.
fn accesses(op: &GpuOp, mv_phase: i32) -> Vec<(usize, Exec, bool)> {
    let mut v = Vec::new();
    match op {
        GpuOp::L1Read(_) => {
            for b in 0..64 {
                v.push((R_L1BM + b, Exec::Block(b as u32), false));
                v.push((R_LBI + b, Exec::Block(b as u32), false));
            }
        }
        GpuOp::L1Write(..) => {
            for b in 0..64 {
                v.push((R_L1BM + b, Exec::Block(b as u32), true));
                v.push((R_LBI + b, Exec::Block(b as u32), true));
            }
        }
        GpuOp::L2(l) => match l.op {
            0 | 1 | 3 => {
                for b in 0..64usize {
                    if (l.mask >> (b % 8)) & 1 != 0 {
                        v.push((R_L2BM + b / 8, Exec::Block(b as u32), false));
                        v.push((R_L1BM + b, Exec::Block(b as u32), true));
                    }
                }
            }
            4 => {
                for b in 0..64usize {
                    v.push((R_L1BM + b, Exec::Block(b as u32), false));
                    v.push((R_L2BM + b / 8, Exec::Block(b as u32), true));
                }
            }
            2 => {
                for l2 in 0..8usize {
                    let b = l2 * 8 + l.l1b as usize;
                    v.push((R_L1BM + b, Exec::Block(b as u32), false));
                    v.push((R_L2BM + l2, Exec::Block(b as u32), true));
                }
            }
            5 => {
                for j in 0..8 {
                    v.push((R_L2BM + j, Exec::Block(0), false));
                }
                v.push((R_DARBUF, Exec::Block(0), true));
                v.push((R_DARADDR, Exec::Block(0), true));
            }
            _ => {
                v.push((R_DARBUF, Exec::Block(0), false));
                v.push((R_DAR, Exec::Block(0), true));
                v.push((R_DARADDR, Exec::Block(0), true));
            }
        },
        GpuOp::L2Red(l) => {
            for b in 0..64usize {
                let l2 = b / 8;
                for s in 0..8 {
                    v.push((R_L1BM + l2 * 8 + s, Exec::Block(b as u32), false));
                }
                if l.op < 2 {
                    v.push((R_L2BM + l2, Exec::Block(b as u32), true));
                } else {
                    v.push((R_L1BM + b, Exec::Block(b as u32), true));
                }
            }
        }
        GpuOp::Mv(l) => {
            let (src, dst): (Vec<usize>, Vec<usize>) = match l.mode {
                MV_MODE_P => (mv_mem_resources(l.src.mem), mv_mem_resources(l.dst.mem)),
                MV_MODE_B_PDM | MV_MODE_D_PDM_L2 => (vec![R_PDM], mv_mem_resources(2)),
                MV_MODE_B_DRAM | MV_MODE_B4 => (vec![R_DRAM], mv_mem_resources(2)),
                MV_MODE_B2 => (mv_mem_resources(l.src.mem), mv_mem_resources(2)),
                MV_MODE_D_L2_PDM | MV_MODE_R_PDM => (mv_mem_resources(2), vec![R_PDM]),
                MV_MODE_D_PDM_DRAM => (vec![R_PDM], vec![R_DRAM]),
                MV_MODE_D_DRAM_PDM => (vec![R_DRAM], vec![R_PDM]),
                MV_MODE_R_DRAM | MV_MODE_R4 => (mv_mem_resources(2), vec![R_DRAM]),
                _ => (mv_mem_resources(2), mv_mem_resources(l.dst.mem)),
            };
            let (src, dst) = match mv_phase {
                0 => (src, vec![R_SCRATCH]),
                1 => (vec![R_SCRATCH], dst),
                _ => (src, dst),
            };
            for r in src {
                v.push((r, Exec::All, false));
            }
            for r in dst {
                v.push((r, Exec::All, true));
            }
            v.push((R_DAR, Exec::All, false));
        }
        // ALU, MAU, matrix and mreadf work touches only the owning block's PEs.
        _ => {}
    }
    v
}

/// One encoded operation (see `Gpu::encode_ops`).
pub(super) struct EncOp {
    pub kind: u32,
    pub flags: u32,
    pub desc: Vec<u8>,
    /// ALU/MAU only: every (PE, cycle) thread may write its own result.
    pub direct: bool,
    /// What the operation reads, for the JIT's L2 prefetch: `mem << 16 | row`
    /// with mem 0-3 a PE memory word row (before BAR) and mem 8 an L1BM
    /// long-word address of the block's own L1BM.
    pub prefetch: Vec<u32>,
}

fn src_rows(s: &AluSrc, out: &mut Vec<u32>) {
    if s.fixed != 0 || s.mem >= 4 {
        return;
    }
    let len = mem_words(s.mem) as u32;
    for c in 0..4 {
        for i in 0..s.wl.max(1) {
            out.push(s.mem << 16 | ((s.base[c].wrapping_add(i)) & (len - 1)));
        }
    }
}

/// The PE-memory rows and L1BM addresses an operation reads (see
/// `EncOp::prefetch`). Only a hint: BAR and T offsets are not known here.
fn prefetch_rows(op: &GpuOp) -> Vec<u32> {
    let mut v = Vec::new();
    match op {
        GpuOp::Alu(l, _) | GpuOp::Bfn(l, _) => {
            if l.op > 1 {
                src_rows(&l.a, &mut v);
            }
            if (12..=31).contains(&l.op) {
                src_rows(&l.b, &mut v);
            }
        }
        GpuOp::Mau(l, _) => {
            src_rows(&l.a, &mut v);
            if l.kind <= 1 {
                src_rows(&l.b, &mut v);
            }
            if l.kind == 0 || l.kind == 2 {
                src_rows(&l.c, &mut v);
            }
        }
        GpuOp::MatWrite(l) => src_rows(&l.src, &mut v),
        GpuOp::MatMau(l, _) => {
            src_rows(&l.x, &mut v);
            if l.kind == 0 {
                src_rows(&l.y, &mut v);
            }
        }
        GpuOp::L1Write(l, _) => {
            let s = AluSrc { mem: l.src.mem as u32, wl: l.src.wl as u32, base: l.src.base, ..Default::default() };
            src_rows(&s, &mut v);
        }
        GpuOp::L1Read(l) => {
            if let Some(a) = l.addr {
                // Up to 4 cycles x 64 long words from the address.
                for k in 0..16u32 {
                    v.push(8 << 16 | ((a + k * 16) & 8191));
                }
            }
        }
        _ => {}
    }
    v.sort_unstable();
    v.dedup();
    v
}

/// Raw word interval `[lo, hi)` an operand may touch for one cycle before the
/// (cycle-independent) BAR offset and alignment are applied. Alignment can
/// move the access down by up to `wl - 1` words, so the interval covers that.
fn cycle_interval(base: u32, wl: u32) -> (i64, i64) {
    (base as i64 - (wl as i64 - 1), base as i64 + wl as i64)
}

/// Whether two intervals intersect modulo `len` (a power of two).
fn intervals_meet(a: (i64, i64), b: (i64, i64), len: i64) -> bool {
    if a.1 - a.0 >= len || b.1 - b.0 >= len {
        return true;
    }
    for shift in [-len, 0, len] {
        let (lo, hi) = (b.0 + shift, b.1 + shift);
        if a.0 < hi && lo < a.1 {
            return true;
        }
    }
    false
}

fn mem_words(mem: u32) -> i64 {
    if mem < 2 {
        crate::machine::LM_WORDS as i64
    } else {
        crate::machine::GRF_WORDS as i64
    }
}

/// Whether the four cycles of one PE can be computed and written by four
/// independent threads with the same result as "read every cycle, then write
/// every cycle": no cycle may write words that another cycle reads or writes.
/// Anything whose address is not known per cycle (T-indirect, `j`, BAR or mask
/// destinations) is rejected.
fn cycles_independent(srcs: &[&AluSrc], dsts: &[AluDstDesc]) -> bool {
    // (memory, cycle, interval) of every PE-memory read and write.
    let mut reads: Vec<(u32, usize, (i64, i64))> = Vec::new();
    let mut writes: Vec<(u32, usize, (i64, i64))> = Vec::new();
    for s in srcs {
        if s.fixed != 0 {
            continue;
        }
        if s.t_indirect != 0 || s.madpe != 0 {
            return false;
        }
        if s.mem < 4 {
            for c in 0..4 {
                reads.push((s.mem, c, cycle_interval(s.base[c], s.wl.max(1))));
            }
        }
    }
    for d in dsts {
        match d.kind {
            0 => {
                if d.t_indirect != 0 || d.madpe != 0 || d.mem >= 4 {
                    return false;
                }
                for c in 0..4 {
                    writes.push((d.mem, c, cycle_interval(d.base[c], d.wl.max(1))));
                }
            }
            // T rows and $nowrite are per cycle.
            1 | 3 => {}
            _ => return false,
        }
    }
    for &(wm, wc, wi) in &writes {
        for &(m, c, i) in reads.iter().chain(writes.iter()) {
            if m == wm && c != wc && intervals_meet(wi, i, mem_words(m)) {
                return false;
            }
        }
    }
    true
}

fn alu_direct_ok(l: &AluLine) -> bool {
    // msl/msr read the neighbouring PE.
    if l.op == 2 || l.op == 3 {
        return false;
    }
    let mut srcs: Vec<&AluSrc> = Vec::new();
    // zero and imm read nothing; only the two-input ops (max..ilrelud) read b.
    if l.op > 1 {
        srcs.push(&l.a);
    }
    if (12..=31).contains(&l.op) {
        srcs.push(&l.b);
    }
    cycles_independent(&srcs, &l.dst[..(l.ndst as usize).min(16)])
}

fn mau_direct_ok(l: &MauLine) -> bool {
    let srcs: Vec<&AluSrc> = match l.kind {
        0 => vec![&l.a, &l.b, &l.c],
        1 => vec![&l.a, &l.b],
        2 => vec![&l.a, &l.c],
        _ => vec![&l.a],
    };
    cycles_independent(&srcs, &l.dst[..(l.ndst as usize).min(16)])
}

/// Descriptor fields that hold addresses, immediates or sizes, as
/// `(word index, C++ field path, is the low word of a u64)`. The JIT
/// specializes code on every other word (the operation's "shape") and reads
/// these at run time, so operations that differ only in addresses share one
/// compiled function.
pub(super) fn variable_fields(kind: u32) -> Vec<(usize, String, bool)> {
    use std::mem::offset_of;
    let w = |bytes: usize| bytes / 4;
    let src = |at: usize, name: &str| -> Vec<(usize, String, bool)> {
        (0..4).map(|i| (w(at + offset_of!(AluSrc, base)) + i, format!("{name}.base[{i}]"), false)).collect()
    };
    let dsts = |at: usize| -> Vec<(usize, String, bool)> {
        let size = std::mem::size_of::<AluDstDesc>();
        (0..16)
            .flat_map(|k| {
                (0..4).map(move |i| {
                    (w(at + k * size + offset_of!(AluDstDesc, base)) + i, format!("dst[{k}].base[{i}]"), false)
                })
            })
            .collect()
    };
    let one = |at: usize, name: &str| vec![(w(at), name.to_string(), false)];
    let mut v = Vec::new();
    match kind {
        PK_ALU | PK_BFN => {
            v.extend(one(offset_of!(AluDesc, imm), "imm"));
            v.extend(src(offset_of!(AluDesc, a), "a"));
            v.extend(src(offset_of!(AluDesc, b), "b"));
            v.extend(dsts(offset_of!(AluDesc, dst)));
        }
        PK_MAU => {
            v.extend(src(offset_of!(MauLine, a), "a"));
            v.extend(src(offset_of!(MauLine, b), "b"));
            v.extend(src(offset_of!(MauLine, c), "c"));
            v.extend(dsts(offset_of!(MauLine, dst)));
        }
        PK_MATW => {
            v.extend(one(offset_of!(MatWriteLine, addr), "addr"));
            v.extend(src(offset_of!(MatWriteLine, src), "src"));
        }
        PK_MATR => {
            v.extend(one(offset_of!(MatReadLine, addr), "addr"));
            v.extend(dsts(offset_of!(MatReadLine, dst)));
        }
        PK_MATMAU => {
            v.extend(src(offset_of!(MatMauLine, x), "x"));
            v.extend(src(offset_of!(MatMauLine, y), "y"));
            v.extend(dsts(offset_of!(MatMauLine, dst)));
        }
        PK_L1R => {
            v.extend(one(offset_of!(L1ReadArgs, addr), "addr"));
            for i in 0..16 {
                v.push((w(offset_of!(L1ReadArgs, db)) + i, format!("db[{}][{}]", i / 4, i % 4), false));
            }
        }
        PK_L1W => {
            v.extend(one(offset_of!(L1WriteArgs, addr), "addr"));
            for i in 0..4 {
                v.push((w(offset_of!(L1WriteArgs, s)) + i, format!("s[{i}]"), false));
            }
        }
        PK_L2 => {
            v.extend(one(offset_of!(L2Args, a0), "a0"));
            v.extend(one(offset_of!(L2Args, a1), "a1"));
        }
        PK_L2RED => {
            v.extend(one(offset_of!(L2RedArgs, a0), "a0"));
            v.extend(one(offset_of!(L2RedArgs, a1), "a1"));
        }
        PK_MV => {
            for (at, name) in [
                (offset_of!(MvArgs, src_addr), "src_addr"),
                (offset_of!(MvArgs, dst_addr), "dst_addr"),
                (offset_of!(MvArgs, size), "size"),
                (offset_of!(MvArgs, nd), "nd"),
                (offset_of!(MvArgs, total), "total"),
            ] {
                v.push((w(at), name.to_string(), true));
                v.push((w(at) + 1, String::new(), false));
            }
        }
        _ => {}
    }
    v
}

/// A program loaded into device memory for the interpreter kernel.
pub struct GpuProgram {
    ins: u64,
    blob: u64,
    sync: u64,
    n: i32,
    /// Operations, grid barriers and instruction words of the program.
    pub ops: usize,
    pub barriers: usize,
    pub words: u64,
    /// `(kind, flags)` of every interpreter instruction.
    pub kinds: Vec<(u32, u32)>,
    free: CuMemFree,
}

impl Drop for GpuProgram {
    fn drop(&mut self) {
        unsafe {
            for p in [self.ins, self.blob, self.sync] {
                if p != 0 {
                    (self.free)(p);
                }
            }
        }
    }
}

impl Gpu {
    /// Runs one operation with its own kernel launch.
    pub fn run_op(&self, state: &GpuState, op: &GpuOp) -> Result<(), String> {
        match op {
            GpuOp::Alu(l, u) => self.run_alu_line_with(state, l, *u),
            GpuOp::Bfn(l, u) => self.run_bfn_line_with(state, l, *u),
            GpuOp::Mau(l, u) => self.run_mau_line_with(state, l, *u),
            GpuOp::L1Read(l) => self.run_l1_read_line(state, l),
            GpuOp::L1Write(l, u) => self.run_l1_write_line_with(state, l, *u),
            GpuOp::L2(l) => self.run_l2_line(state, l),
            GpuOp::L2Red(l) => self.run_l2_reduce_line(state, l),
            GpuOp::MatWrite(l) => self.run_mat_write_line(state, l),
            GpuOp::MatRead(l, u) => self.run_mat_read_line_with(state, l, *u),
            GpuOp::MatMau(l, u) => self.run_mat_mau_line_with(state, l, *u),
            GpuOp::Mv(l) => self.run_mv_line(state, l),
            GpuOp::ClearMreadf => self.clear_mreadf(state),
        }
    }

    /// Encodes the operations for the interpreter kernel, decides the grid
    /// barriers and copies everything to the device.
    /// Encodes the operations for the interpreter or the JIT: the kind, the
    /// flags (including the grid barriers) and the descriptor bytes.
    pub(super) fn encode_ops(&self, state: &GpuState, ops: &[GpuOp]) -> Result<Vec<EncOp>, String> {
        let mut out: Vec<EncOp> = Vec::new();
        let mut hazards = Hazards::new();
        // Diagnostics: a grid barrier before every operation, and no direct
        // (per-cycle thread) writes.
        let all_barriers = std::env::var("MNCORE_GPU_ALL_BARRIERS").is_ok();
        let no_direct = std::env::var("MNCORE_GPU_NO_DIRECT").is_ok();
        let mut push = |kind: u32, update: bool, desc: Vec<u8>, acc: Vec<(usize, Exec, bool)>,
                        direct: bool, out: &mut Vec<EncOp>| {
            let mut flags = if update { PF_UPDATE } else { 0 };
            if hazards.access(&acc) || all_barriers {
                flags |= PF_BARRIER;
            }
            out.push(EncOp { kind, flags, desc, direct: direct && !no_direct, prefetch: Vec::new() });
        };
        for op in ops {
            let acc = accesses(op, 2);
            let before = out.len();
            self.encode_one(state, op, acc, &mut push, &mut out)?;
            if out.len() == before + 1 {
                out[before].prefetch = prefetch_rows(op);
            }
        }
        Ok(out)
    }

    fn encode_one(
        &self,
        state: &GpuState,
        op: &GpuOp,
        acc: Vec<(usize, Exec, bool)>,
        push: &mut impl FnMut(u32, bool, Vec<u8>, Vec<(usize, Exec, bool)>, bool, &mut Vec<EncOp>),
        out: &mut Vec<EncOp>,
    ) -> Result<(), String> {
        {
            match op {
                GpuOp::Alu(l, u) => push(PK_ALU, *u, bytes_of(l).to_vec(), acc, alu_direct_ok(l), out),
                GpuOp::Bfn(l, u) => push(PK_BFN, *u, bytes_of(l).to_vec(), acc, false, out),
                GpuOp::Mau(l, u) => push(PK_MAU, *u, bytes_of(l).to_vec(), acc, mau_direct_ok(l), out),
                GpuOp::L1Read(l) => push(PK_L1R, false, bytes_of(&l1_read_args(l)).to_vec(), acc, false, out),
                GpuOp::L1Write(l, u) => {
                    push(PK_L1W, *u, bytes_of(&l1_write_args(l)).to_vec(), acc, false, out)
                }
                GpuOp::L2(l) => {
                    let a = L2Args {
                        op: l.op as i32,
                        a0: l.a0,
                        a1: l.a1,
                        l1b: l.l1b as i32,
                        mask: l.mask as i32,
                        l2b: l.l2b as i32,
                    };
                    push(PK_L2, false, bytes_of(&a).to_vec(), acc, false, out)
                }
                GpuOp::L2Red(l) => {
                    let a = L2RedArgs {
                        op: l.op as i32,
                        a0: l.a0,
                        a1: l.a1,
                        mask: l.mask as i32,
                        immode: l.immode as i32,
                        bits: l.bits as i32,
                        kind: l.rrn as i32,
                    };
                    push(PK_L2RED, false, bytes_of(&a).to_vec(), acc, false, out)
                }
                GpuOp::MatWrite(l) => push(PK_MATW, false, bytes_of(l).to_vec(), acc, false, out),
                GpuOp::MatRead(l, u) => push(PK_MATR, *u, bytes_of(l).to_vec(), acc, false, out),
                GpuOp::MatMau(l, u) => push(PK_MATMAU, *u, bytes_of(l).to_vec(), acc, false, out),
                GpuOp::ClearMreadf => push(PK_CLEAR_MREADF, false, Vec::new(), acc, false, out),
                GpuOp::Mv(l) => {
                    if l.mode == MV_MODE_NOP || l.threads() == 0 {
                        return Ok(());
                    }
                    self.check_mv_line(state, l)?;
                    let phases: &[i32] = if l.snapshot { &[0, 1] } else { &[2] };
                    for &phase in phases {
                        push(PK_MV, false, bytes_of(&mv_args(l, phase)).to_vec(), accesses(op, phase), false, out);
                    }
                }
            }
        }
        Ok(())
    }

    /// Encodes the operations for the interpreter kernel and copies them to
    /// the device.
    pub fn load_program(
        &self,
        state: &GpuState,
        ops: &[GpuOp],
        words: u64,
    ) -> Result<GpuProgram, String> {
        let enc = self.encode_ops(state, ops)?;
        let mut ins: Vec<ProgIns> = Vec::new();
        let mut blob: Vec<u8> = Vec::new();
        let mut barriers = 0usize;
        for e in &enc {
            while blob.len() % 16 != 0 {
                blob.push(0);
            }
            let off = blob.len() as u32;
            blob.extend_from_slice(&e.desc);
            let longs = e.desc.len().div_ceil(8) as u32;
            if longs > PROG_DESC_LONGS {
                return Err(format!("descriptor of {} bytes is too large", e.desc.len()));
            }
            if e.flags & PF_BARRIER != 0 {
                barriers += 1;
            }
            ins.push(ProgIns { kind: e.kind, flags: e.flags, off, aux: longs });
        }
        if blob.is_empty() {
            blob.push(0);
        }
        let n = ins.len();
        let ins_ptr = self.alloc_copy(bytes_of_slice(&ins))?;
        let blob_ptr = self.alloc_copy(&blob)?;
        let sync_ptr = self.alloc_copy(&[0u8; 16])?;
        Ok(GpuProgram {
            ins: ins_ptr,
            blob: blob_ptr,
            sync: sync_ptr,
            n: n as i32,
            ops: n,
            barriers,
            words,
            kinds: ins.iter().map(|i| (i.kind, i.flags)).collect(),
            free: self.cu_mem_free,
        })
    }

    fn alloc_copy(&self, bytes: &[u8]) -> Result<u64, String> {
        let mut p: u64 = 0;
        self.check(unsafe { (self.cu_mem_alloc)(&mut p, bytes.len().max(16)) }, "cuMemAlloc(program)")?;
        self.check(
            unsafe { (self.cu_htod)(p, bytes.as_ptr() as *const c_void, bytes.len()) },
            "upload program",
        )?;
        self.check(unsafe { (self.cu_sync)() }, "sync program upload")?;
        Ok(p)
    }

    /// Enqueues one run of a loaded program (one cooperative launch).
    pub fn launch_program(&self, state: &GpuState, program: &GpuProgram) -> Result<(), String> {
        self.launch_program_prof(state, program, 0)
    }

    /// Runs a program once with per-instruction SM clock stamps of every block
    /// and returns `(kind, flags, max-over-blocks cycles)` per instruction.
    pub fn profile_program(
        &self,
        state: &GpuState,
        program: &GpuProgram,
    ) -> Result<Vec<(u32, u32, u64)>, String> {
        let n = program.n as usize;
        let len = PROGRAM_BLOCKS as usize * (n + 1);
        let mut prof: u64 = 0;
        self.check(unsafe { (self.cu_mem_alloc)(&mut prof, len * 8) }, "cuMemAlloc(prof)")?;
        let zeros = vec![0u64; len];
        self.check(
            unsafe { (self.cu_htod)(prof, zeros.as_ptr() as *const c_void, len * 8) },
            "zero prof",
        )?;
        self.check(unsafe { (self.cu_sync)() }, "sync prof")?;
        let result = (|| {
            self.launch_program_prof(state, program, prof)?;
            self.check(unsafe { (self.cu_sync)() }, "sync prof")?;
            let mut t = vec![0u64; len];
            self.check(
                unsafe { (self.cu_dtoh)(t.as_mut_ptr() as *mut c_void, prof, len * 8) },
                "download prof",
            )?;
            let first = (0..PROGRAM_BLOCKS as usize).map(|b| t[b * (n + 1)]).min().unwrap_or(0);
            let last = (0..PROGRAM_BLOCKS as usize).map(|b| t[b * (n + 1) + n]).max().unwrap_or(0);
            eprintln!("in-kernel span (SM cycles, max block): {} = {:.3} ms at 1.9 GHz", (0..PROGRAM_BLOCKS as usize).map(|b| t[b * (n + 1) + n] - t[b * (n + 1)]).max().unwrap_or(0), (0..PROGRAM_BLOCKS as usize).map(|b| t[b * (n + 1) + n] - t[b * (n + 1)]).max().unwrap_or(0) as f64 / 1.9e6); let _ = (first, last);
            let mut out = Vec::with_capacity(n);
            for i in 0..n {
                // Median over blocks: robust against a block that was preempted.
                let mut d: Vec<u64> = (0..PROGRAM_BLOCKS as usize)
                    .map(|b| {
                        let row = &t[b * (n + 1)..(b + 1) * (n + 1)];
                        row[i + 1].saturating_sub(row[i])
                    })
                    .collect();
                d.sort_unstable();
                out.push((program.kinds[i].0, program.kinds[i].1, d[d.len() / 2]));
            }
            Ok(out)
        })();
        unsafe { (self.cu_mem_free)(prof) };
        result
    }

    fn launch_program_prof(
        &self,
        state: &GpuState,
        program: &GpuProgram,
        prof: u64,
    ) -> Result<(), String> {
        let mut prof = prof;
        let mut st = DevStateArgs::from_state(state);
        let mut ins = program.ins;
        let mut n = program.n;
        let mut blob = program.blob;
        let mut sync = program.sync;
        let mut args = [
            &mut st as *mut DevStateArgs as *mut c_void,
            &mut ins as *mut u64 as *mut c_void,
            &mut n as *mut i32 as *mut c_void,
            &mut blob as *mut u64 as *mut c_void,
            &mut sync as *mut u64 as *mut c_void,
            &mut prof as *mut u64 as *mut c_void,
        ];
        self.check(
            unsafe {
                (self.cu_launch_coop)(
                    self.program_function,
                    PROGRAM_BLOCKS,
                    1,
                    1,
                    PROGRAM_THREADS,
                    1,
                    1,
                    0,
                    self.stream,
                    args.as_mut_ptr(),
                )
            },
            "cuLaunchCooperativeKernel(run_program)",
        )
    }
}

fn bytes_of_slice<T: Copy>(values: &[T]) -> &[u8] {
    // SAFETY: plain `repr(C)` integer structs.
    unsafe { std::slice::from_raw_parts(values.as_ptr() as *const u8, std::mem::size_of_val(values)) }
}

