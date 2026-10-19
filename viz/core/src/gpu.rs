//! Minimal CUDA Driver API and NVRTC wrapper for the GPU backend.
//!
//! The libraries are loaded at runtime so the CPU build does not need a CUDA
//! toolchain. On WSL the driver comes from `/usr/lib/wsl/lib/libcuda.so.1`;
//! NVRTC comes from the PyTorch CUDA wheels unless `NVRTC_LIB` is set.

use std::ffi::{c_char, c_int, c_void, CStr, CString};
use std::path::Path;

use libloading::Library;

use crate::blockop::{L1Op, L2Op, Rrn, RrnOp};
use crate::machine::MaskState;
use crate::mv::{Mv, MvKind, MvOperand};
use crate::vsm::{Expr, FwdKind, MauKind, MaskSel, MaskSource, MemKind, Op, Operand, Prec};

type CuResult = c_int;
type CuDevice = c_int;
type CuContext = *mut c_void;
type CuModule = *mut c_void;
type CuFunction = *mut c_void;
type CuDevicePtr = u64;

/// Matrix-register words: 1,024 MABs x 2 faces x 16 physical rows x 8 words.
pub const MAT_WORDS: usize = (crate::machine::PES / 4) * 2 * 16 * 8;

type CuInit = unsafe extern "C" fn(u32) -> CuResult;
type CuDeviceGet = unsafe extern "C" fn(*mut CuDevice, c_int) -> CuResult;
type CuDeviceGetAttribute = unsafe extern "C" fn(*mut c_int, c_int, CuDevice) -> CuResult;
type CuCtxCreate = unsafe extern "C" fn(*mut CuContext, u32, CuDevice) -> CuResult;
type CuCtxDestroy = unsafe extern "C" fn(CuContext) -> CuResult;
type CuCtxSync = unsafe extern "C" fn() -> CuResult;
type CuModuleLoad = unsafe extern "C" fn(*mut CuModule, *const c_void, u32, *const c_void, *const c_void) -> CuResult;
type CuModuleGetFunction = unsafe extern "C" fn(*mut CuFunction, CuModule, *const c_char) -> CuResult;
type CuMemAlloc = unsafe extern "C" fn(*mut CuDevicePtr, usize) -> CuResult;
type CuMemFree = unsafe extern "C" fn(CuDevicePtr) -> CuResult;
type CuMemcpyHtoD = unsafe extern "C" fn(CuDevicePtr, *const c_void, usize) -> CuResult;
type CuMemcpyDtoH = unsafe extern "C" fn(*mut c_void, CuDevicePtr, usize) -> CuResult;
type CuLaunchKernel = unsafe extern "C" fn(
    CuFunction,
    u32,
    u32,
    u32,
    u32,
    u32,
    u32,
    u32,
    *mut c_void,
    *mut *mut c_void,
    *mut *mut c_void,
) -> CuResult;
type CuGetErrorString = unsafe extern "C" fn(CuResult, *mut *const c_char) -> CuResult;

type NvrtcResult = c_int;
type NvrtcProgram = *mut c_void;
type NvrtcCreate = unsafe extern "C" fn(
    *mut NvrtcProgram,
    *const c_char,
    *const c_char,
    c_int,
    *const *const c_char,
    *const *const c_char,
) -> NvrtcResult;
type NvrtcCompile = unsafe extern "C" fn(NvrtcProgram, c_int, *const *const c_char) -> NvrtcResult;
type NvrtcGetSize = unsafe extern "C" fn(NvrtcProgram, *mut usize) -> NvrtcResult;
type NvrtcGet = unsafe extern "C" fn(NvrtcProgram, *mut c_char) -> NvrtcResult;
type NvrtcDestroy = unsafe extern "C" fn(*mut NvrtcProgram) -> NvrtcResult;

macro_rules! load {
    ($lib:expr, $name:literal, $ty:ty) => {{
        let symbol: libloading::Symbol<'_, $ty> = unsafe { $lib.get($name) }
            .map_err(|e| format!("{}: {e}", String::from_utf8_lossy(&$name[..$name.len() - 1])))?;
        *symbol
    }};
}

fn mem_source(op: &Operand, allow_neg: bool, allow_mask: bool) -> Option<MauSrc> {
    let Operand::Mem {
        mem,
        wl,
        addr,
        neg,
        ext,
        rnd,
        mask,
    } = op
    else {
        return None;
    };
    if (*wl != 1 && *wl != 2 && *wl != 4)
        || (!allow_neg && *neg)
        || *ext
        || *rnd
        || (!allow_mask && mask.is_some())
    {
        return None;
    }
    if addr.t_indirect || addr.madpe.is_some() {
        return None;
    }
    let mem = match mem {
        MemKind::Lm0 => 0,
        MemKind::Lm1 => 1,
        MemKind::Grf0 => 2,
        MemKind::Grf1 => 3,
        MemKind::T => {
            return Some(MauSrc {
                mem: 6,
                wl: 4,
                base: [0; 4],
                neg: *neg,
            })
        }
        _ => return None,
    };
    Some(MauSrc {
        mem,
        wl: *wl,
        base: addr.cycles.map(|c| c & !(*wl as u32 - 1)),
        neg: *neg,
    })
}

fn line_source(op: &Operand) -> Option<MauSrc> {
    if let Operand::Forward {
        kind,
        neg,
        ext: false,
        rnd: false,
    } = op
    {
        let mem = match kind {
            FwdKind::Mauf => 4,
            FwdKind::Aluf => 5,
            _ => return None,
        };
        return Some(MauSrc {
            mem,
            wl: 4,
            base: [0; 4],
            neg: *neg,
        });
    }
    mem_source(op, true, false)
}

/// Builds a `MauLine` for a PE-local f32 MAU expression. Returns `None` for
/// anything the current kernel does not handle (masks, T, base registers,
/// neg/ext/rnd, other forwarding registers, other precisions).
fn resolve_mask(op: &Operand, state: MaskState, single_line: bool) -> MaskInfo {
    let none = MaskInfo {
        kind: 0,
        entry: 0,
        pattern: 0,
        ll: false,
    };
    let Operand::Mem { mem, mask, .. } = op else {
        return none;
    };
    let directive = if single_line {
        None
    } else {
        let t = state.targets;
        let on = match mem {
            MemKind::Grf0 => t.grf0,
            MemKind::Grf1 => t.grf1,
            MemKind::T => t.t,
            MemKind::Lm0 => t.lm0,
            MemKind::Lm1 => t.lm1,
            _ => false,
        };
        if on && state.entry != 0 {
            Some(MaskSel {
                ll: state.wl == 4,
                source: MaskSource::Entry(state.entry),
            })
        } else {
            None
        }
    };
    let Some(sel) = mask.or(directive) else {
        return none;
    };
    match sel.source {
        MaskSource::Entry(entry) => MaskInfo {
            kind: 1,
            entry,
            pattern: 0,
            ll: sel.ll,
        },
        MaskSource::Pattern(p) => MaskInfo {
            kind: 2,
            entry: 0,
            pattern: p.iter().enumerate().fold(0u8, |acc, (i, &on)| {
                acc | ((on as u8) << i)
            }),
            ll: sel.ll,
        },
    }
}

pub fn mau_line_from_expr(expr: &Expr, mask_state: MaskState) -> Option<MauLine> {
    let Op::Mau {
        prec: Prec::F,
        matrix: false,
        kind,
        half: None,
        round: false,
    } = &expr.op
    else {
        return None;
    };
    if expr.flush.is_some() || expr.dsts.len() != 1 {
        return None;
    }
    let zero = MauSrc {
        mem: 0,
        wl: 1,
        base: [0; 4],
        neg: false,
    };
    let kind = match kind {
        MauKind::Fma => 0,
        MauKind::Mul => 1,
        MauKind::Add => 2,
        MauKind::Passa => 3,
    };
    let a = line_source(expr.srcs.first()?)?;
    let (b, c) = match kind {
        0 => (
            line_source(expr.srcs.get(1)?)?,
            line_source(expr.srcs.get(2)?)?,
        ),
        1 => (line_source(expr.srcs.get(1)?)?, zero),
        2 => (zero, line_source(expr.srcs.get(1)?)?),
        _ => (zero, zero),
    };
    let dst_op = &expr.dsts[0];
    let single_line = expr
        .dsts
        .iter()
        .any(|d| matches!(d, Operand::Mem { mask: Some(_), .. }));
    let dst = mem_source(dst_op, false, true)?;
    let mask = resolve_mask(dst_op, mask_state, single_line);
    Some(MauLine {
        kind,
        wl: dst.wl,
        a,
        b,
        c,
        dst,
        mask,
    })
}

/// One source or destination of a MAU line: memory kind (0 LM0, 1 LM1,
/// 2 GRF0, 3 GRF1) and the already-aligned base word address per cycle.
#[derive(Clone, Copy, Debug)]
pub struct MauSrc {
    pub mem: u8,
    pub wl: u8,
    pub base: [u32; 4],
    pub neg: bool,
}

/// Resolved write mask: kind 0 none, 1 OMR entry, 2 fixed pattern.
#[derive(Clone, Copy, Debug)]
pub struct MaskInfo {
    pub kind: u8,
    pub entry: u8,
    pub pattern: u8,
    pub ll: bool,
}

/// A PE-local f32 MAU expression, with kind 0 FMA, 1 MUL, 2 ADD, 3 PASSA.
#[derive(Clone, Copy, Debug)]
pub struct MauLine {
    pub kind: u8,
    pub wl: u8,
    pub a: MauSrc,
    pub b: MauSrc,
    pub c: MauSrc,
    pub dst: MauSrc,
    pub mask: MaskInfo,
}

/// Builds an `AluLine` for a PE-local f32 Passa expression.
pub fn alu_line_from_expr(expr: &Expr) -> Option<AluLine> {
    let (kind, need_b, has_source) = match &expr.op {
        Op::Zero => (5u8, false, false),
        Op::Imm { .. } => (6u8, false, false),
        Op::Alu {
            name: crate::vsm::AluOp::Passa,
            prec: Some(Prec::F),
            ..
        } => (0u8, false, true),
        Op::Alu {
            name: crate::vsm::AluOp::Xor,
            prec: Some(Prec::I),
            ..
        } => (1u8, true, true),
        Op::Alu {
            name: crate::vsm::AluOp::Max,
            prec: Some(Prec::F),
            ..
        } => (2u8, true, true),
        Op::Alu {
            name: crate::vsm::AluOp::Rsqrt,
            prec: Some(Prec::F),
            ..
        } => (3u8, false, true),
        Op::Alu {
            name: crate::vsm::AluOp::Msr,
            ..
        } => (4u8, false, true),
        _ => return None,
    };
    let want_sources = if need_b { 2 } else { 1 };
    if expr.flush.is_some()
        || expr.srcs.len() != if has_source { want_sources } else { 0 }
        || expr.dsts.len() != 1
    {
        return None;
    }
    let dummy = MauSrc {
        mem: 0,
        wl: 1,
        base: [0; 4],
        neg: false,
    };
    let a = if has_source {
        let a = line_source(&expr.srcs[0])?;
        if a.neg {
            return None;
        }
        a
    } else {
        dummy
    };
    let b = if need_b {
        let b = line_source(&expr.srcs[1])?;
        if b.neg {
            return None;
        }
        b
    } else {
        dummy
    };
    let (imm, imm_u) = match &expr.op {
        Op::Imm { value, u } => (*value, *u),
        _ => (0, false),
    };
    let dst = match &expr.dsts[0] {
        Operand::Mem {
            mem: MemKind::T, ..
        } => AluDst::T,
        Operand::Mem { .. } => AluDst::Mem(mem_source(&expr.dsts[0], false, false)?),
        Operand::Omr { entry, mask: None } if (1..=15).contains(entry) => AluDst::Omr(*entry),
        Operand::Nowrite => AluDst::None,
        _ => return None,
    };
    Some(AluLine {
        kind,
        a,
        b,
        dst,
        imm,
        imm_u,
    })
}

/// Destination of an ALU line: a PE memory, an OMR entry, or nowhere.
#[derive(Clone, Copy, Debug)]
pub enum AluDst {
    Mem(MauSrc),
    T,
    Omr(u8),
    None,
}

/// An L1BM-to-PE read: Mbcast (op 0) or Distrib (op 1).
#[derive(Clone, Copy, Debug)]
pub struct L1ReadLine {
    pub op: u8,
    pub addr: u32,
    pub mabdiff: i16,
    pub wl: u8,
    pub dst: MauSrc,
}

pub fn l1_read_line_from_expr(expr: &Expr) -> Option<L1ReadLine> {
    let Op::L1(op) = &expr.op else {
        return None;
    };
    let (kind, mabdiff) = match op {
        L1Op::Mbcast => (0u8, 0i16),
        L1Op::Distrib { mabdiff } => (1u8, *mabdiff),
        L1Op::Pbcast => (2u8, 0i16),
        _ => return None,
    };
    let (wl, addr) = match expr.srcs.first()? {
        Operand::L1bm {
            wl,
            addr: Some(addr),
        } => (*wl, *addr),
        _ => return None,
    };
    if wl != 2 && wl != 4 {
        return None;
    }
    let dst = mem_source(expr.dsts.first()?, false, false)?;
    Some(L1ReadLine {
        op: kind,
        addr,
        mabdiff,
        wl,
        dst,
    })
}

/// An L1BM write from one MAB (l1bmm@mab).
#[derive(Clone, Copy, Debug)]
pub struct L1WriteLine {
    pub mab: u8,
    pub addr: u32,
    pub wl: u8,
    pub src: MauSrc,
}

pub fn l1_write_line_from_expr(expr: &Expr) -> Option<L1WriteLine> {
    let Op::L1(L1Op::Mwrite { mab }) = &expr.op else {
        return None;
    };
    let (wl, addr) = match expr.dsts.first()? {
        Operand::L1bm {
            wl,
            addr: Some(addr),
        } => (*wl, *addr),
        _ => return None,
    };
    if wl != 2 && wl != 4 {
        return None;
    }
    let src = mem_source(expr.srcs.first()?, false, false)?;
    Some(L1WriteLine {
        mab: *mab,
        addr,
        wl,
        src,
    })
}

/// Device memory of an MV operand: 0 PDM, 1 DRAM, 2 L2BM. A group or l2b of
/// `MV_GROUP_NONE` means that the operand did not name one (CPU: all groups,
/// or the first group depending on the opcode; see `mv_line_from_mv`).
#[derive(Clone, Copy, Debug)]
pub struct MvRef {
    pub mem: u8,
    pub group: u8,
    pub l2b: u8,
    pub addr: u64,
}

const MV_GROUP_NONE: u8 = 255;
const MV_MODE_P: u8 = 0;
const MV_MODE_B_PDM: u8 = 1;
const MV_MODE_B_DRAM: u8 = 2;
const MV_MODE_B2: u8 = 3;
const MV_MODE_D_PDM_L2: u8 = 4;
const MV_MODE_D_L2_PDM: u8 = 5;
const MV_MODE_D_PDM_DRAM: u8 = 6;
const MV_MODE_D_DRAM_PDM: u8 = 7;
const MV_MODE_B4: u8 = 8;
const MV_MODE_R_PDM: u8 = 9;
const MV_MODE_R_DRAM: u8 = 10;
const MV_MODE_R2: u8 = 11;
const MV_MODE_R4: u8 = 12;
const MV_MODE_NOP: u8 = 13;

/// A resolved MV statement for the device kernel.
#[derive(Clone, Copy, Debug)]
pub struct MvLine {
    pub mode: u8,
    pub size: u64,
    pub src: MvRef,
    pub dst: MvRef,
    pub parallel: bool,
    /// `mvp` with source and destination in the same memory level and group:
    /// all reads must happen before the writes, so the transfer is staged.
    pub snapshot: bool,
    pub rrn_op: u8,
    pub rrn_bits: u8,
}

fn mv_ref(op: MvOperand) -> Option<MvRef> {
    let group = |g: Option<u8>| -> Option<u8> {
        match g {
            Some(g) if (g as usize) < crate::mv::GROUPS => Some(g),
            Some(_) => None,
            None => Some(MV_GROUP_NONE),
        }
    };
    match op {
        MvOperand::Pdm { addr, group: g } => Some(MvRef {
            mem: 0,
            group: group(g)?,
            l2b: 0,
            addr,
        }),
        MvOperand::Dram {
            addr,
            group: g,
            indirect,
        } => {
            if indirect {
                return None;
            }
            Some(MvRef {
                mem: 1,
                group: group(g)?,
                l2b: 0,
                addr,
            })
        }
        MvOperand::L2bm {
            addr,
            group: g,
            l2b,
        } => {
            let l2b = match l2b {
                Some(c) if c < 2 => c,
                Some(_) => return None,
                None => 0,
            };
            Some(MvRef {
                mem: 2,
                group: group(g)?,
                l2b,
                addr,
            })
        }
    }
}

fn rrn_code(op: Rrn) -> (u8, u8) {
    let code = match op.op {
        RrnOp::Fadd => 0,
        RrnOp::Max => 1,
        RrnOp::Min => 2,
        RrnOp::Iadd => 3,
        RrnOp::Band => 4,
        RrnOp::And => 5,
        RrnOp::Bor => 6,
        RrnOp::Or => 7,
    };
    (code, op.bits() as u8)
}

/// Builds the kernel descriptor for an MV statement. Returns `None` for
/// indirect DRAM access and for operand combinations the kernel does not
/// implement (the CPU rejects some of these too).
pub fn mv_line_from_mv(mv: &Mv) -> Option<MvLine> {
    if mv.kind == MvKind::Nop {
        let none = MvRef {
            mem: 0,
            group: MV_GROUP_NONE,
            l2b: 0,
            addr: 0,
        };
        return Some(MvLine {
            mode: MV_MODE_NOP,
            size: 0,
            src: none,
            dst: none,
            parallel: false,
            snapshot: false,
            rrn_op: 0,
            rrn_bits: 0,
        });
    }
    let (src_op, dst_op) = (mv.src?, mv.dst?);
    let src = mv_ref(src_op)?;
    let dst = mv_ref(dst_op)?;
    // The CPU does `size / 64` blocks of 64 long words; a smaller remainder is ignored.
    let size = (mv.size / 64) * 64;
    let line = |mode, size, src, dst, parallel, snapshot, (rrn_op, rrn_bits)| MvLine {
        mode,
        size,
        src,
        dst,
        parallel,
        snapshot,
        rrn_op,
        rrn_bits,
    };
    match mv.kind {
        MvKind::Nop => None,
        MvKind::P => {
            let (parallel, size) = match (src.group, dst.group) {
                (MV_GROUP_NONE, MV_GROUP_NONE) => (true, size),
                (MV_GROUP_NONE, _) | (_, MV_GROUP_NONE) => return None,
                _ => (false, size),
            };
            // The CPU defaults a missing L2B number to 0 for both operands.
            let snapshot = src.mem == dst.mem
                && src.group == dst.group
                && (src.mem != 2 || src.l2b == dst.l2b);
            Some(line(MV_MODE_P, size, src, dst, parallel, snapshot, (0, 0)))
        }
        MvKind::B => match src.mem {
            0 if dst.mem == 2 => Some(line(
                MV_MODE_B_PDM,
                size,
                MvRef {
                    group: if src.group == MV_GROUP_NONE { 0 } else { src.group },
                    ..src
                },
                // The CPU ignores the destination groups and writes every L2BM.
                MvRef { mem: 2, group: 0, l2b: 0, ..dst },
                false,
                false,
                (0, 0),
            )),
            1 if dst.mem == 2 => Some(line(
                MV_MODE_B_DRAM,
                size,
                MvRef { group: 0, ..src },
                MvRef { mem: 2, group: 0, l2b: 0, ..dst },
                false,
                false,
                (0, 0),
            )),
            _ => None,
        },
        MvKind::B2 if src.mem == 1 && dst.mem == 2 => Some(line(
            MV_MODE_B2,
            size,
            MvRef { group: 0, ..src },
            MvRef { mem: 2, group: 0, l2b: 0, ..dst },
            false,
            false,
            (0, 0),
        )),
        MvKind::B4 if src.mem == 1 && dst.mem == 2 => Some(line(
            MV_MODE_B4,
            size,
            MvRef { group: 0, ..src },
            MvRef { mem: 2, group: 0, l2b: 0, ..dst },
            false,
            false,
            (0, 0),
        )),
        MvKind::D => {
            let (mode, src, dst) = match (src.mem, dst.mem) {
                (0, 2) => (
                    MV_MODE_D_PDM_L2,
                    MvRef { group: if src.group == MV_GROUP_NONE { 0 } else { src.group }, ..src },
                    MvRef { mem: 2, group: 0, l2b: 0, ..dst },
                ),
                (2, 0) => (
                    MV_MODE_D_L2_PDM,
                    MvRef { mem: 2, group: 0, l2b: 0, ..src },
                    MvRef { group: if dst.group == MV_GROUP_NONE { 0 } else { dst.group }, ..dst },
                ),
                (0, 1) => (
                    MV_MODE_D_PDM_DRAM,
                    MvRef { group: if src.group == MV_GROUP_NONE { 0 } else { src.group }, ..src },
                    MvRef { group: 0, ..dst },
                ),
                (1, 0) => (
                    MV_MODE_D_DRAM_PDM,
                    MvRef { group: 0, ..src },
                    MvRef { group: if dst.group == MV_GROUP_NONE { 0 } else { dst.group }, ..dst },
                ),
                _ => return None,
            };
            Some(line(mode, size, src, dst, false, false, (0, 0)))
        }
        MvKind::R2(op) if src.mem == 2 && matches!(dst.mem, 0 | 1) => Some(line(
            MV_MODE_R2,
            size,
            MvRef { mem: 2, group: 0, l2b: 0, ..src },
            dst,
            false,
            false,
            rrn_code(op),
        )),
        MvKind::R(op) if src.mem == 2 && matches!(dst.mem, 0 | 1) => {
            let (mode, dst) = if dst.mem == 0 {
                (
                    MV_MODE_R_PDM,
                    MvRef { group: if dst.group == MV_GROUP_NONE { 0 } else { dst.group }, ..dst },
                )
            } else {
                (MV_MODE_R_DRAM, MvRef { group: 0, ..dst })
            };
            Some(line(
                mode,
                size,
                MvRef { mem: 2, group: 0, l2b: 0, ..src },
                dst,
                false,
                false,
                rrn_code(op),
            ))
        }
        MvKind::R4(op) if src.mem == 2 && dst.mem == 1 => Some(line(
            MV_MODE_R4,
            size,
            MvRef { mem: 2, group: 0, l2b: 0, ..src },
            MvRef { group: 0, ..dst },
            false,
            false,
            rrn_code(op),
        )),
        _ => None,
    }
}

impl MvLine {
    /// Upper bound of the device DRAM this statement can touch on either side.
    /// Every data flow stays below `addr + size` (the widest is a plain `mvp`
    /// or `mvb2`); the kernel and host range check use this same bound.
    pub fn dram_longs_needed(&self) -> u64 {
        let mut need = 1;
        for r in [self.src, self.dst] {
            if r.mem == 1 {
                need = need.max(r.addr.saturating_add(self.size));
            }
        }
        need
    }

    /// Scratch long words needed by the two-pass snapshot of an overlapping `mvp`.
    pub fn scratch_longs_needed(&self) -> u64 {
        if self.snapshot {
            self.size * if self.parallel { 4 } else { 1 }
        } else {
            0
        }
    }

    fn threads(&self) -> u64 {
        match self.mode {
            MV_MODE_P => self.size * if self.parallel { 4 } else { 1 },
            MV_MODE_B2 => self.size * 4,
            MV_MODE_D_PDM_L2 | MV_MODE_D_L2_PDM => self.size * 8,
            MV_MODE_B4 | MV_MODE_R4 => self.size * 2,
            MV_MODE_R2 => self.size * if self.dst.group == MV_GROUP_NONE { 4 } else { 1 },
            MV_MODE_NOP => 0,
            _ => self.size,
        }
    }
}

/// An L2BM transfer: op 0 Distrib (L2 to L1), 1 Bcast (L2 to L1), 2 FromL1b (L1 to L2).
#[derive(Clone, Copy, Debug)]
pub struct L2Line {
    pub op: u8,
    pub a0: u32,
    pub a1: u32,
    pub l1b: u8,
    pub mask: u8,
}

pub fn l2_line_from_expr(expr: &Expr) -> Option<L2Line> {
    let Op::L2(op) = &expr.op else {
        return None;
    };
    let addr_of = |op: &Operand| -> Option<u32> {
        match op {
            Operand::L2bm { addr, .. } => Some(*addr),
            Operand::L1bm { addr: Some(a), .. } => Some(*a),
            _ => None,
        }
    };
    let a0 = addr_of(expr.srcs.first()?)?;
    let a1 = addr_of(expr.dsts.first()?)?;
    match op {
        L2Op::Distrib { set } => Some(L2Line {
            op: 0,
            a0,
            a1,
            l1b: 0,
            mask: set.mask,
        }),
        L2Op::Bcast { set } => Some(L2Line {
            op: 1,
            a0,
            a1,
            l1b: 0,
            mask: set.mask,
        }),
        L2Op::Bcast2 { set } => Some(L2Line {
            op: 3,
            a0,
            a1,
            l1b: 0,
            mask: set.mask,
        }),
        L2Op::FromL1b { l1b } => Some(L2Line {
            op: 2,
            a0,
            a1,
            l1b: *l1b,
            mask: 0xff,
        }),
        _ => None,
    }
}

/// An L2BM reduction or internal multicast: op 0 Reduce, 1 Reduce2, 2 Imcast.
#[derive(Clone, Copy, Debug)]
pub struct L2RedLine {
    pub op: u8,
    pub a0: u32,
    pub a1: u32,
    /// L1B set mask and immode (unused by Reduce2).
    pub mask: u8,
    pub immode: u8,
    /// Element width in bits (unused by Imcast).
    pub bits: u32,
    /// Reduction kind: 0 fadd, 1 max, 2 min, 3 iadd, 4 band, 5 and, 6 bor, 7 or.
    pub rrn: u8,
}

fn mv_rrn_code(rrn: Rrn) -> u8 {
    match rrn.op {
        RrnOp::Fadd => 0,
        RrnOp::Max => 1,
        RrnOp::Min => 2,
        RrnOp::Iadd => 3,
        RrnOp::Band => 4,
        RrnOp::And => 5,
        RrnOp::Bor => 6,
        RrnOp::Or => 7,
    }
}

pub fn l2_reduce_line_from_expr(expr: &Expr) -> Option<L2RedLine> {
    let Op::L2(op) = &expr.op else {
        return None;
    };
    let addr_of = |op: &Operand| -> Option<u32> {
        match op {
            Operand::L2bm { addr, l2b: None } => Some(*addr),
            Operand::L1bm { addr: Some(a), .. } => Some(*a),
            _ => None,
        }
    };
    let a0 = addr_of(expr.srcs.first()?)?;
    let a1 = addr_of(expr.dsts.first()?)?;
    match op {
        L2Op::Reduce { rrn, set } => Some(L2RedLine {
            op: 0,
            a0,
            a1,
            mask: set.mask,
            immode: set.immode,
            bits: rrn.bits(),
            rrn: mv_rrn_code(*rrn),
        }),
        L2Op::Reduce2 { rrn } => Some(L2RedLine {
            op: 1,
            a0,
            a1,
            mask: 0xff,
            immode: 0,
            bits: rrn.bits(),
            rrn: mv_rrn_code(*rrn),
        }),
        L2Op::Imcast { set } => Some(L2RedLine {
            op: 2,
            a0,
            a1,
            mask: set.mask,
            immode: set.immode,
            bits: 0,
            rrn: 0,
        }),
        _ => None,
    }
}

/// A gbfn (block-float) line.
#[derive(Clone, Copy, Debug)]
pub struct BfnLine {
    pub src: MauSrc,
    pub dst: AluDst,
}

/// Builds a BfnLine for a gbfn expression.
pub fn bfn_line_from_expr(expr: &Expr) -> Option<BfnLine> {
    let Op::Alu {
        name: crate::vsm::AluOp::Bfn,
        prec: Some(Prec::G),
        arg: None,
        ..
    } = &expr.op
    else {
        return None;
    };
    if expr.flush.is_some() || expr.srcs.len() != 1 || expr.dsts.len() != 1 {
        return None;
    }
    let src = line_source(&expr.srcs[0])?;
    let dst = match &expr.dsts[0] {
        Operand::Nowrite => AluDst::None,
        Operand::Mem { .. } => AluDst::Mem(mem_source(&expr.dsts[0], false, false)?),
        _ => return None,
    };
    Some(BfnLine { src, dst })
}

/// A matrix-register write (`fmwrite`/`gmwrite`): each MAB writes one face row
/// per cycle from its four PEs.
#[derive(Clone, Copy, Debug)]
pub struct MatWriteLine {
    pub prec: Prec,
    pub side: u8,
    pub wl: u8,
    pub addr: u32,
    pub src: MauSrc,
}

/// A matrix-register read (`fmread`/`gmread`) into a PE memory bus.
#[derive(Clone, Copy, Debug)]
pub struct MatReadLine {
    pub prec: Prec,
    pub side: u8,
    pub addr: u32,
    pub dst: MauSrc,
}

/// A matrix MAU line (`fmfma`/`gmmul` and friends).
#[derive(Clone, Copy, Debug)]
pub struct MatMauLine {
    pub prec: Prec,
    pub side: u8,
    /// 0 FMA, 1 MUL, 2 ADD, 3 PASSA. Only FMA reads the y operand.
    pub kind: u8,
    pub x: MauSrc,
    pub y: MauSrc,
    pub dst: AluDst,
}

/// Whether the multi-line mask directive of `state` affects a PE memory write.
fn directive_mask_applies(op: &Operand, state: MaskState) -> bool {
    let Operand::Mem { mem, .. } = op else {
        return false;
    };
    let on = match mem {
        MemKind::Grf0 => state.targets.grf0,
        MemKind::Grf1 => state.targets.grf1,
        MemKind::T => state.targets.t,
        MemKind::Lm0 => state.targets.lm0,
        MemKind::Lm1 => state.targets.lm1,
        _ => false,
    };
    on && state.entry != 0
}

/// Builds a `MatWriteLine` for fmwrite/gmwrite. The current kernel supports the
/// 32-bit element precisions (F and G).
pub fn mat_write_line_from_expr(expr: &Expr) -> Option<MatWriteLine> {
    let Op::MatWrite {
        prec: prec @ (Prec::F | Prec::G),
    } = &expr.op
    else {
        return None;
    };
    if expr.flush.is_some() || expr.srcs.len() != 1 || expr.dsts.len() != 1 {
        return None;
    }
    let Operand::Mat {
        y,
        wl,
        row: Some(addr),
    } = &expr.dsts[0]
    else {
        return None;
    };
    let src = line_source(&expr.srcs[0])?;
    if src.mem >= 6 {
        return None;
    }
    Some(MatWriteLine {
        prec: *prec,
        side: *y as u8,
        wl: *wl,
        addr: *addr,
        src,
    })
}

/// Builds a `MatReadLine` for fmread/gmread. Reads whose destination is masked
/// by the current `mask` directive are rejected, because the kernel does not
/// merge masked writes yet.
pub fn mat_read_line_from_expr(expr: &Expr, mask_state: MaskState) -> Option<MatReadLine> {
    let Op::MatRead {
        prec: prec @ (Prec::F | Prec::G),
    } = &expr.op
    else {
        return None;
    };
    if expr.flush.is_some() || expr.srcs.len() != 1 || expr.dsts.len() != 1 {
        return None;
    }
    let Operand::Mat {
        y,
        row: Some(addr),
        ..
    } = &expr.srcs[0]
    else {
        return None;
    };
    let dst = match &expr.dsts[0] {
        // A read to $nowrite still updates mreadf, like the CPU write path.
        Operand::Nowrite => MauSrc {
            mem: 0,
            wl: 0,
            base: [0; 4],
            neg: false,
        },
        Operand::Mem { .. } if !directive_mask_applies(&expr.dsts[0], mask_state) => {
            let dst = mem_source(&expr.dsts[0], false, false)?;
            if dst.mem >= 6 {
                return None;
            }
            dst
        }
        _ => return None,
    };
    Some(MatReadLine {
        prec: *prec,
        side: *y as u8,
        addr: *addr,
        dst,
    })
}

/// Builds a `MatMauLine` for a matrix MAU expression (`fmfma`, `gmmul`, ...).
pub fn mat_mau_line_from_expr(expr: &Expr, mask_state: MaskState) -> Option<MatMauLine> {
    let Op::Mau {
        prec: prec @ (Prec::F | Prec::G),
        matrix: true,
        kind,
        half: None,
        ..
    } = &expr.op
    else {
        return None;
    };
    let kind = match kind {
        MauKind::Fma => 0,
        MauKind::Mul => 1,
        MauKind::Add => 2,
        MauKind::Passa => 3,
    };
    let want = if kind == 0 { 3 } else { 2 };
    if expr.flush.is_some() || expr.srcs.len() != want || expr.dsts.len() != 1 {
        return None;
    }
    let Operand::Mat {
        y: side_y,
        row: None,
        ..
    } = &expr.srcs[0]
    else {
        return None;
    };
    let x = line_source(&expr.srcs[1])?;
    if x.mem >= 6 {
        return None;
    }
    let y = if kind == 0 {
        let y = line_source(&expr.srcs[2])?;
        if y.mem >= 6 {
            return None;
        }
        y
    } else {
        MauSrc {
            mem: 0,
            wl: 1,
            base: [0; 4],
            neg: false,
        }
    };
    let dst = match &expr.dsts[0] {
        Operand::Nowrite => AluDst::None,
        Operand::Mem { .. } => {
            if directive_mask_applies(&expr.dsts[0], mask_state) {
                return None;
            }
            let dst = mem_source(&expr.dsts[0], false, false)?;
            if dst.mem >= 6 {
                return None;
            }
            AluDst::Mem(dst)
        }
        _ => return None,
    };
    Some(MatMauLine {
        prec: *prec,
        side: *side_y as u8,
        kind,
        x,
        y,
        dst,
    })
}

/// A single ALU line. Kind 0 is Passa and kind 1 is Xor.
#[derive(Clone, Copy, Debug)]
pub struct AluLine {
    pub kind: u8,
    pub a: MauSrc,
    pub b: MauSrc,
    pub dst: AluDst,
    pub imm: u32,
    pub imm_u: bool,
}

/// LM0, LM1, GRF0 and GRF1 in device memory, in the same PE-major layout as
/// `machine::Mem`.
pub struct GpuState {
    lm0: u64,
    lm1: u64,
    grf0: u64,
    grf1: u64,
    mauf: u64,
    aluf: u64,
    mask: u64,
    t: u64,
    l1bm: u64,
    l2bm: u64,
    /// PDM (4 x `mv::PDM_LONGS`) and a truncated DRAM (4 x `dram_longs`).
    /// Both are zero when the state was allocated without MV support.
    pdm: u64,
    dram: u64,
    scratch: u64,
    dram_longs: u64,
    scratch_longs: u64,
    /// 1,024 MABs x 2 faces x 16 physical rows x 8 words.
    mats: u64,
    /// Matrix read forwarding register, 4 cycles x 4 words per PE.
    mreadf: u64,
    free: CuMemFree,
}

impl Drop for GpuState {
    fn drop(&mut self) {
        unsafe {
            for pointer in [
                self.lm0,
                self.lm1,
                self.grf0,
                self.grf1,
                self.mauf,
                self.aluf,
                self.mask,
                self.t,
                self.l1bm,
                self.l2bm,
                self.pdm,
                self.dram,
                self.scratch,
                self.mats,
                self.mreadf,
            ] {
                if pointer != 0 {
                    (self.free)(pointer);
                }
            }
        }
    }
}

pub struct Gpu {
    _cuda: Library,
    _nvrtc: Library,
    context: CuContext,
    function: CuFunction,
    mau_function: CuFunction,
    alu_function: CuFunction,
    bfn_function: CuFunction,
    l1_function: CuFunction,
    l1_write_function: CuFunction,
    l2_function: CuFunction,
    l2_reduce_function: CuFunction,
    mv_function: CuFunction,
    mat_write_function: CuFunction,
    mat_read_function: CuFunction,
    mat_mau_function: CuFunction,
    cu_ctx_destroy: CuCtxDestroy,
    cu_mem_alloc: CuMemAlloc,
    cu_mem_free: CuMemFree,
    cu_htod: CuMemcpyHtoD,
    cu_dtoh: CuMemcpyDtoH,
    cu_launch: CuLaunchKernel,
    cu_sync: CuCtxSync,
    cu_error: CuGetErrorString,
}

unsafe impl Send for Gpu {}

impl Gpu {
    /// Initializes the first GPU and compiles the vfma kernel.
    pub fn new() -> Result<Gpu, String> {
        let cuda = unsafe { Library::new("libcuda.so.1") }
            .map_err(|e| format!("libcuda.so.1: {e}"))?;
        let nvrtc = load_nvrtc()?;

        let cu_init: CuInit = load!(cuda, b"cuInit\0", CuInit);
        let cu_device_get: CuDeviceGet = load!(cuda, b"cuDeviceGet\0", CuDeviceGet);
        let cu_attr: CuDeviceGetAttribute =
            load!(cuda, b"cuDeviceGetAttribute\0", CuDeviceGetAttribute);
        let cu_ctx_create: CuCtxCreate = load!(cuda, b"cuCtxCreate_v2\0", CuCtxCreate);
        let cu_ctx_destroy: CuCtxDestroy = load!(cuda, b"cuCtxDestroy_v2\0", CuCtxDestroy);
        let cu_module_load: CuModuleLoad =
            load!(cuda, b"cuModuleLoadDataEx\0", CuModuleLoad);
        let cu_get_function: CuModuleGetFunction =
            load!(cuda, b"cuModuleGetFunction\0", CuModuleGetFunction);
        let cu_mem_alloc: CuMemAlloc = load!(cuda, b"cuMemAlloc_v2\0", CuMemAlloc);
        let cu_mem_free: CuMemFree = load!(cuda, b"cuMemFree_v2\0", CuMemFree);
        let cu_htod: CuMemcpyHtoD = load!(cuda, b"cuMemcpyHtoD_v2\0", CuMemcpyHtoD);
        let cu_dtoh: CuMemcpyDtoH = load!(cuda, b"cuMemcpyDtoH_v2\0", CuMemcpyDtoH);
        let cu_launch: CuLaunchKernel = load!(cuda, b"cuLaunchKernel\0", CuLaunchKernel);
        let cu_sync: CuCtxSync = load!(cuda, b"cuCtxSynchronize\0", CuCtxSync);
        let cu_error: CuGetErrorString = load!(cuda, b"cuGetErrorString\0", CuGetErrorString);

        let nvrtc_create: NvrtcCreate = load!(nvrtc, b"nvrtcCreateProgram\0", NvrtcCreate);
        let nvrtc_compile: NvrtcCompile = load!(nvrtc, b"nvrtcCompileProgram\0", NvrtcCompile);
        let nvrtc_log_size: NvrtcGetSize = load!(nvrtc, b"nvrtcGetProgramLogSize\0", NvrtcGetSize);
        let nvrtc_log: NvrtcGet = load!(nvrtc, b"nvrtcGetProgramLog\0", NvrtcGet);
        let nvrtc_ptx_size: NvrtcGetSize = load!(nvrtc, b"nvrtcGetPTXSize\0", NvrtcGetSize);
        let nvrtc_ptx: NvrtcGet = load!(nvrtc, b"nvrtcGetPTX\0", NvrtcGet);
        let nvrtc_destroy: NvrtcDestroy = load!(nvrtc, b"nvrtcDestroyProgram\0", NvrtcDestroy);

        let check = |code: CuResult, what: &str| -> Result<(), String> {
            if code == 0 {
                return Ok(());
            }
            let mut text: *const c_char = std::ptr::null();
            unsafe { cu_error(code, &mut text) };
            let message = if text.is_null() {
                format!("error {code}")
            } else {
                unsafe { CStr::from_ptr(text) }
                    .to_string_lossy()
                    .into_owned()
            };
            Err(format!("{what}: {message}"))
        };

        unsafe { cu_init(0) };
        let mut device: CuDevice = 0;
        check(unsafe { cu_device_get(&mut device, 0) }, "cuDeviceGet")?;
        let mut major: c_int = 0;
        let mut minor: c_int = 0;
        let _ = unsafe { cu_attr(&mut major, 75, device) };
        let _ = unsafe { cu_attr(&mut minor, 76, device) };
        if major == 0 {
            major = 8;
            minor = 6;
        }
        let mut context: CuContext = std::ptr::null_mut();
        check(unsafe { cu_ctx_create(&mut context, 0, device) }, "cuCtxCreate")?;

        // The MV kernel reuses the Fmt/round_pack helpers of the vfma kernel,
        // so both files are compiled as one translation unit.
        let source = concat!(
            include_str!("../gpu/vfma_kernel.cu"),
            include_str!("../gpu/mv_kernel.cu")
        );
        let source_c = CString::new(source).map_err(|e| e.to_string())?;
        let name = CString::new("vfma.cu").unwrap();
        let mut program: NvrtcProgram = std::ptr::null_mut();
        let created = unsafe {
            nvrtc_create(
                &mut program,
                source_c.as_ptr(),
                name.as_ptr(),
                0,
                std::ptr::null(),
                std::ptr::null(),
            )
        };
        if created != 0 {
            check(unsafe { cu_ctx_destroy(context) }, "cuCtxDestroy")?;
            return Err(format!("nvrtcCreateProgram: {created}"));
        }
        let arch = CString::new(format!("--gpu-architecture=compute_{major}{minor}")).unwrap();
        let int128 = CString::new("--device-int128").unwrap();
        let options = [arch.as_ptr(), int128.as_ptr()];
        let compiled = unsafe { nvrtc_compile(program, 2, options.as_ptr()) };
        if compiled != 0 {
            let mut size = 0usize;
            unsafe { nvrtc_log_size(program, &mut size) };
            let mut log = vec![0u8; size.max(1)];
            if size > 0 {
                unsafe { nvrtc_log(program, log.as_mut_ptr() as *mut c_char) };
            }
            unsafe { nvrtc_destroy(&mut program) };
            unsafe { cu_ctx_destroy(context) };
            return Err(format!(
                "nvrtcCompileProgram: {}",
                String::from_utf8_lossy(&log)
            ));
        }
        let mut ptx_size = 0usize;
        unsafe { nvrtc_ptx_size(program, &mut ptx_size) };
        let mut ptx = vec![0u8; ptx_size];
        unsafe { nvrtc_ptx(program, ptx.as_mut_ptr() as *mut c_char) };
        unsafe { nvrtc_destroy(&mut program) };

        let mut module: CuModule = std::ptr::null_mut();
        check(
            unsafe {
                cu_module_load(
                    &mut module,
                    ptx.as_ptr() as *const c_void,
                    0,
                    std::ptr::null(),
                    std::ptr::null(),
                )
            },
            "cuModuleLoadDataEx",
        )?;
        let mut function: CuFunction = std::ptr::null_mut();
        check(
            unsafe { cu_get_function(&mut function, module, b"vfma_f32\0".as_ptr() as *const c_char) },
            "cuModuleGetFunction",
        )?;
        let mut mau_function: CuFunction = std::ptr::null_mut();
        check(
            unsafe { cu_get_function(&mut mau_function, module, b"mau_line\0".as_ptr() as *const c_char) },
            "cuModuleGetFunction(mau_line)",
        )?;
        let mut alu_function: CuFunction = std::ptr::null_mut();
        check(
            unsafe { cu_get_function(&mut alu_function, module, b"alu_line\0".as_ptr() as *const c_char) },
            "cuModuleGetFunction(alu_line)",
        )?;
        let mut bfn_function: CuFunction = std::ptr::null_mut();
        check(
            unsafe { cu_get_function(&mut bfn_function, module, b"bfn_line\0".as_ptr() as *const c_char) },
            "cuModuleGetFunction(bfn_line)",
        )?;
        let mut l1_function: CuFunction = std::ptr::null_mut();
        check(
            unsafe { cu_get_function(&mut l1_function, module, b"l1_read_line\0".as_ptr() as *const c_char) },
            "cuModuleGetFunction(l1_read_line)",
        )?;
        let mut l1_write_function: CuFunction = std::ptr::null_mut();
        check(
            unsafe { cu_get_function(&mut l1_write_function, module, b"l1_write_line\0".as_ptr() as *const c_char) },
            "cuModuleGetFunction(l1_write_line)",
        )?;
        let mut l2_function: CuFunction = std::ptr::null_mut();
        check(
            unsafe { cu_get_function(&mut l2_function, module, b"l2_line\0".as_ptr() as *const c_char) },
            "cuModuleGetFunction(l2_line)",
        )?;
        let mut l2_reduce_function: CuFunction = std::ptr::null_mut();
        check(
            unsafe {
                cu_get_function(
                    &mut l2_reduce_function,
                    module,
                    b"l2_reduce_line\0".as_ptr() as *const c_char,
                )
            },
            "cuModuleGetFunction(l2_reduce_line)",
        )?;
        let mut mv_function: CuFunction = std::ptr::null_mut();
        check(
            unsafe { cu_get_function(&mut mv_function, module, b"mv_line\0".as_ptr() as *const c_char) },
            "cuModuleGetFunction(mv_line)",
        )?;
        let mut mat_write_function: CuFunction = std::ptr::null_mut();
        check(
            unsafe {
                cu_get_function(
                    &mut mat_write_function,
                    module,
                    b"mat_write_line\0".as_ptr() as *const c_char,
                )
            },
            "cuModuleGetFunction(mat_write_line)",
        )?;
        let mut mat_read_function: CuFunction = std::ptr::null_mut();
        check(
            unsafe {
                cu_get_function(
                    &mut mat_read_function,
                    module,
                    b"mat_read_line\0".as_ptr() as *const c_char,
                )
            },
            "cuModuleGetFunction(mat_read_line)",
        )?;
        let mut mat_mau_function: CuFunction = std::ptr::null_mut();
        check(
            unsafe {
                cu_get_function(
                    &mut mat_mau_function,
                    module,
                    b"mat_mau_line\0".as_ptr() as *const c_char,
                )
            },
            "cuModuleGetFunction(mat_mau_line)",
        )?;
        Ok(Gpu {
            _cuda: cuda,
            _nvrtc: nvrtc,
            context,
            function,
            mau_function,
            alu_function,
            bfn_function,
            l1_function,
            l1_write_function,
            l2_function,
            l2_reduce_function,
            mv_function,
            mat_write_function,
            mat_read_function,
            mat_mau_function,
            cu_ctx_destroy,
            cu_mem_alloc,
            cu_mem_free,
            cu_htod,
            cu_dtoh,
            cu_launch,
            cu_sync,
            cu_error,
        })
    }

    fn error(&self, code: CuResult) -> String {
        let mut text: *const c_char = std::ptr::null();
        unsafe { (self.cu_error)(code, &mut text) };
        if text.is_null() {
            format!("error {code}")
        } else {
            unsafe { CStr::from_ptr(text) }
                .to_string_lossy()
                .into_owned()
        }
    }

    fn check(&self, code: CuResult, what: &str) -> Result<(), String> {
        if code == 0 {
            Ok(())
        } else {
            Err(format!("{what}: {}", self.error(code)))
        }
    }

    /// Allocates the four PE memories and the L1BM/L2BM buffers on the device.
    pub fn allocate_state(&self) -> Result<GpuState, String> {
        self.allocate_state_with_mv(0, 0)
    }

    /// Allocates the base state plus PDM and MV support.
    ///
    /// The full CPU DRAM is 4 x 512 Mi long words (128 GiB), so the device keeps
    /// only `dram_longs` long words per group. MV statements whose DRAM access
    /// bound (`addr + size`) exceeds this capacity are rejected by
    /// `run_mv_line`; `MvLine::dram_longs_needed` gives a fitting size.
    /// `scratch_longs` is used by the two-pass snapshot of overlapping `mvp`.
    pub fn allocate_state_with_mv(
        &self,
        dram_longs: u64,
        scratch_longs: u64,
    ) -> Result<GpuState, String> {
        let lm_bytes = crate::machine::PES * crate::machine::LM_WORDS * 4;
        let grf_bytes = crate::machine::PES * crate::machine::GRF_WORDS * 4;
        let fwd_bytes = crate::machine::PES * 16 * 4;
        let l1bm_bytes = crate::blocks::L1BS * crate::blocks::L1BM_LONGS * 8;
        let l2bm_bytes = crate::blocks::L2BS * crate::blocks::L2BM_LONGS * 8;
        let mats_bytes = MAT_WORDS * 4;
        let mut sizes = vec![
            lm_bytes,
            lm_bytes,
            grf_bytes,
            grf_bytes,
            fwd_bytes,
            fwd_bytes,
            fwd_bytes,
            fwd_bytes,
            l1bm_bytes,
            l2bm_bytes,
            mats_bytes,
            fwd_bytes,
        ];
        let want_mv = dram_longs > 0;
        if want_mv {
            let pdm_bytes = (crate::mv::GROUPS as u64 * crate::mv::PDM_LONGS * 8) as usize;
            let dram_bytes = usize::try_from(dram_longs)
                .ok()
                .and_then(|n| n.checked_mul(crate::mv::GROUPS).and_then(|n| n.checked_mul(8)))
                .ok_or("MV DRAM size overflows usize")?;
            let scratch_bytes = usize::try_from(scratch_longs.max(1))
                .ok()
                .and_then(|n| n.checked_mul(8))
                .ok_or("MV scratch size overflows usize")?;
            sizes.push(pdm_bytes);
            sizes.push(dram_bytes);
            sizes.push(scratch_bytes);
        }
        let mut buffers = vec![0u64; sizes.len()];
        for i in 0..sizes.len() {
            let code = unsafe { (self.cu_mem_alloc)(&mut buffers[i], sizes[i]) };
            if let Err(error) = self.check(code, "cuMemAlloc(state)") {
                for buffer in &buffers[..i] {
                    let _ = unsafe { (self.cu_mem_free)(*buffer) };
                }
                return Err(error);
            }
        }
        Ok(GpuState {
            lm0: buffers[0],
            lm1: buffers[1],
            grf0: buffers[2],
            grf1: buffers[3],
            mauf: buffers[4],
            aluf: buffers[5],
            mask: buffers[6],
            t: buffers[7],
            l1bm: buffers[8],
            l2bm: buffers[9],
            mats: buffers[10],
            mreadf: buffers[11],
            pdm: if want_mv { buffers[12] } else { 0 },
            dram: if want_mv { buffers[13] } else { 0 },
            scratch: if want_mv { buffers[14] } else { 0 },
            dram_longs: if want_mv { dram_longs } else { 0 },
            scratch_longs: if want_mv { scratch_longs } else { 0 },
            free: self.cu_mem_free,
        })
    }

    /// Uploads the four host memories. The slices must have the simulator's sizes.
    pub fn upload_state(
        &self,
        state: &GpuState,
        lm0: &[u32],
        lm1: &[u32],
        grf0: &[u32],
        grf1: &[u32],
    ) -> Result<(), String> {
        let lm = crate::machine::PES * crate::machine::LM_WORDS;
        let grf = crate::machine::PES * crate::machine::GRF_WORDS;
        if lm0.len() != lm || lm1.len() != lm || grf0.len() != grf || grf1.len() != grf {
            return Err("state slices have the wrong length".into());
        }
        self.check(
            unsafe { (self.cu_htod)(state.lm0, lm0.as_ptr() as *const c_void, lm * 4) },
            "upload lm0",
        )?;
        self.check(
            unsafe { (self.cu_htod)(state.lm1, lm1.as_ptr() as *const c_void, lm * 4) },
            "upload lm1",
        )?;
        self.check(
            unsafe { (self.cu_htod)(state.grf0, grf0.as_ptr() as *const c_void, grf * 4) },
            "upload grf0",
        )?;
        self.check(
            unsafe { (self.cu_htod)(state.grf1, grf1.as_ptr() as *const c_void, grf * 4) },
            "upload grf1",
        )?;
        let forward = vec![0u32; crate::machine::PES * 16];
        for (pointer, what) in [
            (state.mauf, "upload mauf"),
            (state.aluf, "upload aluf"),
            (state.mask, "upload mask"),
            (state.t, "upload t"),
            (state.mreadf, "upload mreadf"),
        ] {
            self.check(
                unsafe {
                    (self.cu_htod)(
                        pointer,
                        forward.as_ptr() as *const c_void,
                        forward.len() * 4,
                    )
                },
                what,
            )?;
        }
        let mats = vec![0u32; MAT_WORDS];
        self.check(
            unsafe {
                (self.cu_htod)(
                    state.mats,
                    mats.as_ptr() as *const c_void,
                    mats.len() * 4,
                )
            },
            "upload mats",
        )?;
        Ok(())
    }

    /// Downloads the four device memories.
    pub fn download_state(
        &self,
        state: &GpuState,
        lm0: &mut [u32],
        lm1: &mut [u32],
        grf0: &mut [u32],
        grf1: &mut [u32],
    ) -> Result<(), String> {
        let lm = crate::machine::PES * crate::machine::LM_WORDS;
        let grf = crate::machine::PES * crate::machine::GRF_WORDS;
        self.check(
            unsafe { (self.cu_dtoh)(lm0.as_mut_ptr() as *mut c_void, state.lm0, lm * 4) },
            "download lm0",
        )?;
        self.check(
            unsafe { (self.cu_dtoh)(lm1.as_mut_ptr() as *mut c_void, state.lm1, lm * 4) },
            "download lm1",
        )?;
        self.check(
            unsafe { (self.cu_dtoh)(grf0.as_mut_ptr() as *mut c_void, state.grf0, grf * 4) },
            "download grf0",
        )?;
        self.check(
            unsafe { (self.cu_dtoh)(grf1.as_mut_ptr() as *mut c_void, state.grf1, grf * 4) },
            "download grf1",
        )
    }

    /// Uploads the L1BM long words (L1BS x L1BM_LONGS).
    pub fn upload_l1bm(&self, state: &GpuState, words: &[u64]) -> Result<(), String> {
        let count = crate::blocks::L1BS * crate::blocks::L1BM_LONGS;
        if words.len() != count {
            return Err("L1BM slice has the wrong length".into());
        }
        self.check(
            unsafe {
                (self.cu_htod)(
                    state.l1bm,
                    words.as_ptr() as *const c_void,
                    count * 8,
                )
            },
            "upload l1bm",
        )
    }

    /// Downloads the L1BM long words.
    pub fn download_l1bm(&self, state: &GpuState) -> Result<Vec<u64>, String> {
        let count = crate::blocks::L1BS * crate::blocks::L1BM_LONGS;
        let mut out = vec![0u64; count];
        self.check(
            unsafe {
                (self.cu_dtoh)(
                    out.as_mut_ptr() as *mut c_void,
                    state.l1bm,
                    count * 8,
                )
            },
            "download l1bm",
        )?;
        Ok(out)
    }

    /// Uploads the L2BM long words.
    pub fn upload_l2bm(&self, state: &GpuState, words: &[u64]) -> Result<(), String> {
        let count = crate::blocks::L2BS * crate::blocks::L2BM_LONGS;
        if words.len() != count {
            return Err("L2BM slice has the wrong length".into());
        }
        self.check(
            unsafe {
                (self.cu_htod)(
                    state.l2bm,
                    words.as_ptr() as *const c_void,
                    count * 8,
                )
            },
            "upload l2bm",
        )
    }

    /// Downloads the L2BM long words.
    pub fn download_l2bm(&self, state: &GpuState) -> Result<Vec<u64>, String> {
        let count = crate::blocks::L2BS * crate::blocks::L2BM_LONGS;
        let mut out = vec![0u64; count];
        self.check(
            unsafe {
                (self.cu_dtoh)(
                    out.as_mut_ptr() as *mut c_void,
                    state.l2bm,
                    count * 8,
                )
            },
            "download l2bm",
        )?;
        Ok(out)
    }

    /// Uploads all four PDM groups (4 x `mv::PDM_LONGS` long words, group-major).
    pub fn upload_pdm(&self, state: &GpuState, words: &[u64]) -> Result<(), String> {
        let count = crate::mv::GROUPS * crate::mv::PDM_LONGS as usize;
        if state.pdm == 0 {
            return Err("GPU state was allocated without MV support".into());
        }
        if words.len() != count {
            return Err("PDM slice has the wrong length".into());
        }
        self.check(
            unsafe {
                (self.cu_htod)(
                    state.pdm,
                    words.as_ptr() as *const c_void,
                    count * 8,
                )
            },
            "upload pdm",
        )
    }

    /// Downloads all four PDM groups.
    pub fn download_pdm(&self, state: &GpuState) -> Result<Vec<u64>, String> {
        if state.pdm == 0 {
            return Err("GPU state was allocated without MV support".into());
        }
        let count = crate::mv::GROUPS * crate::mv::PDM_LONGS as usize;
        let mut out = vec![0u64; count];
        self.check(
            unsafe {
                (self.cu_dtoh)(
                    out.as_mut_ptr() as *mut c_void,
                    state.pdm,
                    count * 8,
                )
            },
            "download pdm",
        )?;
        Ok(out)
    }

    /// Uploads the truncated device DRAM (4 x `dram_longs`, group-major).
    pub fn upload_dram(&self, state: &GpuState, words: &[u64]) -> Result<(), String> {
        if state.dram == 0 {
            return Err("GPU state was allocated without MV support".into());
        }
        let count = (crate::mv::GROUPS as u64 * state.dram_longs) as usize;
        if words.len() != count {
            return Err("DRAM slice has the wrong length".into());
        }
        self.check(
            unsafe {
                (self.cu_htod)(
                    state.dram,
                    words.as_ptr() as *const c_void,
                    count * 8,
                )
            },
            "upload dram",
        )
    }

    /// Downloads the truncated device DRAM.
    pub fn download_dram(&self, state: &GpuState) -> Result<Vec<u64>, String> {
        if state.dram == 0 {
            return Err("GPU state was allocated without MV support".into());
        }
        let count = (crate::mv::GROUPS as u64 * state.dram_longs) as usize;
        let mut out = vec![0u64; count];
        self.check(
            unsafe {
                (self.cu_dtoh)(
                    out.as_mut_ptr() as *mut c_void,
                    state.dram,
                    count * 8,
                )
            },
            "download dram",
        )?;
        Ok(out)
    }

    /// Uploads the matrix registers (`[mab][face][physical row][word]`, u32).
    pub fn upload_mats(&self, state: &GpuState, words: &[u32]) -> Result<(), String> {
        if words.len() != MAT_WORDS {
            return Err("matrix slice has the wrong length".into());
        }
        self.check(
            unsafe {
                (self.cu_htod)(
                    state.mats,
                    words.as_ptr() as *const c_void,
                    MAT_WORDS * 4,
                )
            },
            "upload mats",
        )
    }

    /// Downloads the matrix registers.
    pub fn download_mats(&self, state: &GpuState) -> Result<Vec<u32>, String> {
        let mut out = vec![0u32; MAT_WORDS];
        self.check(
            unsafe {
                (self.cu_dtoh)(
                    out.as_mut_ptr() as *mut c_void,
                    state.mats,
                    MAT_WORDS * 4,
                )
            },
            "download mats",
        )?;
        Ok(out)
    }

    /// Downloads the OMR entries (16 per PE).
    pub fn download_mask(&self, state: &GpuState) -> Result<Vec<u32>, String> {
        let mut out = vec![0u32; crate::machine::PES * 16];
        self.check(
            unsafe {
                (self.cu_dtoh)(
                    out.as_mut_ptr() as *mut c_void,
                    state.mask,
                    out.len() * 4,
                )
            },
            "download mask",
        )?;
        Ok(out)
    }

    /// Downloads aluf (4 cycles x 4 words per PE).
    pub fn download_aluf(&self, state: &GpuState) -> Result<Vec<u32>, String> {
        let mut out = vec![0u32; crate::machine::PES * 16];
        self.check(
            unsafe {
                (self.cu_dtoh)(
                    out.as_mut_ptr() as *mut c_void,
                    state.aluf,
                    out.len() * 4,
                )
            },
            "download aluf",
        )?;
        Ok(out)
    }

    /// Downloads the T registers (16 words per PE).
    pub fn download_t(&self, state: &GpuState) -> Result<Vec<u32>, String> {
        let mut out = vec![0u32; crate::machine::PES * 16];
        self.check(
            unsafe {
                (self.cu_dtoh)(
                    out.as_mut_ptr() as *mut c_void,
                    state.t,
                    out.len() * 4,
                )
            },
            "download t",
        )?;
        Ok(out)
    }

    /// Waits for all previously enqueued kernels.
    pub fn sync(&self) -> Result<(), String> {
        self.check(unsafe { (self.cu_sync)() }, "cuCtxSynchronize")
    }

    /// Launches one f32 MAU line for all 4,096 PEs and four cycles.
    pub fn run_mau_line(&self, state: &GpuState, line: &MauLine) -> Result<(), String> {
        for src in [line.a, line.b, line.c, line.dst] {
            if src.wl != 1 && src.wl != 2 && src.wl != 4 {
                return Err("mau_line supports wl = 1, 2 or 4".into());
            }
        }
        let mut lm0 = state.lm0;
        let mut lm1 = state.lm1;
        let mut grf0 = state.grf0;
        let mut grf1 = state.grf1;
        let mut mauf = state.mauf;
        let mut aluf = state.aluf;
        let mut mask_state = state.mask;
        let mut t = state.t;
        let mut kind = line.kind as i32;
        let mut amem = line.a.mem as i32;
        let mut a = line.a.base;
        let mut awl = line.a.wl as i32;
        let mut aneg = line.a.neg as i32;
        let mut bmem = line.b.mem as i32;
        let mut b = line.b.base;
        let mut bwl = line.b.wl as i32;
        let mut bneg = line.b.neg as i32;
        let mut cmem = line.c.mem as i32;
        let mut c = line.c.base;
        let mut cwl = line.c.wl as i32;
        let mut cneg = line.c.neg as i32;
        let mut dmem = line.dst.mem as i32;
        let mut d = line.dst.base;
        let mut dwl = line.dst.wl as i32;
        let mut mask_kind = line.mask.kind as i32;
        let mut mask_entry = line.mask.entry as i32;
        let mut mask_pattern = line.mask.pattern as i32;
        let mut mask_ll = line.mask.ll as i32;
        let mut args = [
            &mut lm0 as *mut u64 as *mut c_void,
            &mut lm1 as *mut u64 as *mut c_void,
            &mut grf0 as *mut u64 as *mut c_void,
            &mut grf1 as *mut u64 as *mut c_void,
            &mut mauf as *mut u64 as *mut c_void,
            &mut aluf as *mut u64 as *mut c_void,
            &mut mask_state as *mut u64 as *mut c_void,
            &mut t as *mut u64 as *mut c_void,
            &mut kind as *mut i32 as *mut c_void,
            &mut amem as *mut i32 as *mut c_void,
            &mut a[0] as *mut u32 as *mut c_void,
            &mut a[1] as *mut u32 as *mut c_void,
            &mut a[2] as *mut u32 as *mut c_void,
            &mut a[3] as *mut u32 as *mut c_void,
            &mut awl as *mut i32 as *mut c_void,
            &mut aneg as *mut i32 as *mut c_void,
            &mut bmem as *mut i32 as *mut c_void,
            &mut b[0] as *mut u32 as *mut c_void,
            &mut b[1] as *mut u32 as *mut c_void,
            &mut b[2] as *mut u32 as *mut c_void,
            &mut b[3] as *mut u32 as *mut c_void,
            &mut bwl as *mut i32 as *mut c_void,
            &mut bneg as *mut i32 as *mut c_void,
            &mut cmem as *mut i32 as *mut c_void,
            &mut c[0] as *mut u32 as *mut c_void,
            &mut c[1] as *mut u32 as *mut c_void,
            &mut c[2] as *mut u32 as *mut c_void,
            &mut c[3] as *mut u32 as *mut c_void,
            &mut cwl as *mut i32 as *mut c_void,
            &mut cneg as *mut i32 as *mut c_void,
            &mut dmem as *mut i32 as *mut c_void,
            &mut d[0] as *mut u32 as *mut c_void,
            &mut d[1] as *mut u32 as *mut c_void,
            &mut d[2] as *mut u32 as *mut c_void,
            &mut d[3] as *mut u32 as *mut c_void,
            &mut dwl as *mut i32 as *mut c_void,
            &mut mask_kind as *mut i32 as *mut c_void,
            &mut mask_entry as *mut i32 as *mut c_void,
            &mut mask_pattern as *mut i32 as *mut c_void,
            &mut mask_ll as *mut i32 as *mut c_void,
        ];
        let grid = ((crate::machine::PES * 4) as u32 + 255) / 256;
        self.check(
            unsafe {
                (self.cu_launch)(
                    self.mau_function,
                    grid,
                    1,
                    1,
                    256,
                    1,
                    1,
                    0,
                    std::ptr::null_mut(),
                    args.as_mut_ptr(),
                    std::ptr::null_mut(),
                )
            },
            "cuLaunchKernel(mau_line)",
        )
    }

    /// Launches one ALU line for all 4,096 PEs.
    pub fn run_alu_line(&self, state: &GpuState, line: &AluLine) -> Result<(), String> {
        let mut lm0 = state.lm0;
        let mut lm1 = state.lm1;
        let mut grf0 = state.grf0;
        let mut grf1 = state.grf1;
        let mut mauf = state.mauf;
        let mut aluf = state.aluf;
        let mut mask = state.mask;
        let mut t = state.t;
        let mut kind = line.kind as i32;
        let mut amem = line.a.mem as i32;
        let mut a = line.a.base;
        let mut awl = line.a.wl as i32;
        let mut bmem = line.b.mem as i32;
        let mut b = line.b.base;
        let mut bwl = line.b.wl as i32;
        let mut imm = line.imm;
        let mut imm_u = line.imm_u as i32;
        let (mut dmem, mut d, mut dwl, mut omr, mut tdst) = match line.dst {
            AluDst::Mem(dst) => (dst.mem as i32, dst.base, dst.wl as i32, 0i32, 0i32),
            AluDst::T => (0i32, [0u32; 4], 0i32, 0i32, 1i32),
            AluDst::Omr(entry) => (0i32, [0u32; 4], 0i32, entry as i32, 0i32),
            AluDst::None => (0i32, [0u32; 4], 0i32, 0i32, 0i32),
        };
        let mut args = [
            &mut lm0 as *mut u64 as *mut c_void,
            &mut lm1 as *mut u64 as *mut c_void,
            &mut grf0 as *mut u64 as *mut c_void,
            &mut grf1 as *mut u64 as *mut c_void,
            &mut mauf as *mut u64 as *mut c_void,
            &mut aluf as *mut u64 as *mut c_void,
            &mut mask as *mut u64 as *mut c_void,
            &mut t as *mut u64 as *mut c_void,
            &mut kind as *mut i32 as *mut c_void,
            &mut amem as *mut i32 as *mut c_void,
            &mut a[0] as *mut u32 as *mut c_void,
            &mut a[1] as *mut u32 as *mut c_void,
            &mut a[2] as *mut u32 as *mut c_void,
            &mut a[3] as *mut u32 as *mut c_void,
            &mut awl as *mut i32 as *mut c_void,
            &mut bmem as *mut i32 as *mut c_void,
            &mut b[0] as *mut u32 as *mut c_void,
            &mut b[1] as *mut u32 as *mut c_void,
            &mut b[2] as *mut u32 as *mut c_void,
            &mut b[3] as *mut u32 as *mut c_void,
            &mut bwl as *mut i32 as *mut c_void,
            &mut dmem as *mut i32 as *mut c_void,
            &mut d[0] as *mut u32 as *mut c_void,
            &mut d[1] as *mut u32 as *mut c_void,
            &mut d[2] as *mut u32 as *mut c_void,
            &mut d[3] as *mut u32 as *mut c_void,
            &mut dwl as *mut i32 as *mut c_void,
            &mut omr as *mut i32 as *mut c_void,
            &mut tdst as *mut i32 as *mut c_void,
            &mut imm as *mut u32 as *mut c_void,
            &mut imm_u as *mut i32 as *mut c_void,
        ];
        let grid = (crate::machine::PES as u32 + 255) / 256;
        self.check(
            unsafe {
                (self.cu_launch)(
                    self.alu_function,
                    grid,
                    1,
                    1,
                    256,
                    1,
                    1,
                    0,
                    std::ptr::null_mut(),
                    args.as_mut_ptr(),
                    std::ptr::null_mut(),
                )
            },
            "cuLaunchKernel(alu_line)",
        )
    }

    /// Launches one gbfn line for all 1,024 MABs and four cycles.
    pub fn run_bfn_line(&self, state: &GpuState, line: &BfnLine) -> Result<(), String> {
        let mut lm0 = state.lm0;
        let mut lm1 = state.lm1;
        let mut grf0 = state.grf0;
        let mut grf1 = state.grf1;
        let mut mauf = state.mauf;
        let mut aluf = state.aluf;
        let mut smem = line.src.mem as i32;
        let mut s = line.src.base;
        let mut swl = line.src.wl as i32;
        let (mut dmem, mut d, mut dwl) = match line.dst {
            AluDst::Mem(dst) => (dst.mem as i32, dst.base, dst.wl as i32),
            _ => (0i32, [0u32; 4], 0i32),
        };
        let mut args = [
            &mut lm0 as *mut u64 as *mut c_void,
            &mut lm1 as *mut u64 as *mut c_void,
            &mut grf0 as *mut u64 as *mut c_void,
            &mut grf1 as *mut u64 as *mut c_void,
            &mut mauf as *mut u64 as *mut c_void,
            &mut aluf as *mut u64 as *mut c_void,
            &mut smem as *mut i32 as *mut c_void,
            &mut s[0] as *mut u32 as *mut c_void,
            &mut s[1] as *mut u32 as *mut c_void,
            &mut s[2] as *mut u32 as *mut c_void,
            &mut s[3] as *mut u32 as *mut c_void,
            &mut swl as *mut i32 as *mut c_void,
            &mut dmem as *mut i32 as *mut c_void,
            &mut d[0] as *mut u32 as *mut c_void,
            &mut d[1] as *mut u32 as *mut c_void,
            &mut d[2] as *mut u32 as *mut c_void,
            &mut d[3] as *mut u32 as *mut c_void,
            &mut dwl as *mut i32 as *mut c_void,
        ];
        let grid = (crate::machine::PES as u32 + 255) / 256;
        self.check(
            unsafe {
                (self.cu_launch)(
                    self.bfn_function,
                    grid,
                    1,
                    1,
                    256,
                    1,
                    1,
                    0,
                    std::ptr::null_mut(),
                    args.as_mut_ptr(),
                    std::ptr::null_mut(),
                )
            },
            "cuLaunchKernel(bfn_line)",
        )
    }

    /// Launches one L2BM transfer.
    pub fn run_l2_line(&self, state: &GpuState, line: &L2Line) -> Result<(), String> {
        let mut l1bm = state.l1bm;
        let mut l2bm = state.l2bm;
        let mut op = line.op as i32;
        let mut a0 = line.a0;
        let mut a1 = line.a1;
        let mut l1b = line.l1b as i32;
        let mut mask = line.mask as i32;
        let mut args = [
            &mut l1bm as *mut u64 as *mut c_void,
            &mut l2bm as *mut u64 as *mut c_void,
            &mut op as *mut i32 as *mut c_void,
            &mut a0 as *mut u32 as *mut c_void,
            &mut a1 as *mut u32 as *mut c_void,
            &mut l1b as *mut i32 as *mut c_void,
            &mut mask as *mut i32 as *mut c_void,
        ];
        self.check(
            unsafe {
                (self.cu_launch)(
                    self.l2_function,
                    64,
                    1,
                    1,
                    256,
                    1,
                    1,
                    0,
                    std::ptr::null_mut(),
                    args.as_mut_ptr(),
                    std::ptr::null_mut(),
                )
            },
            "cuLaunchKernel(l2_line)",
        )
    }

    /// Launches one L2BM reduction or internal multicast.
    pub fn run_l2_reduce_line(&self, state: &GpuState, line: &L2RedLine) -> Result<(), String> {
        if line.op < 2 && line.bits != 16 && line.bits != 32 && line.bits != 64 {
            return Err(format!("unsupported RRN width {}", line.bits));
        }
        let mut l1bm = state.l1bm;
        let mut l2bm = state.l2bm;
        let mut op = line.op as i32;
        let mut a0 = line.a0;
        let mut a1 = line.a1;
        let mut mask = line.mask as i32;
        let mut immode = line.immode as i32;
        let mut bits = line.bits as i32;
        let mut rrn = line.rrn as i32;
        let mut args = [
            &mut l1bm as *mut u64 as *mut c_void,
            &mut l2bm as *mut u64 as *mut c_void,
            &mut op as *mut i32 as *mut c_void,
            &mut a0 as *mut u32 as *mut c_void,
            &mut a1 as *mut u32 as *mut c_void,
            &mut mask as *mut i32 as *mut c_void,
            &mut immode as *mut i32 as *mut c_void,
            &mut bits as *mut i32 as *mut c_void,
            &mut rrn as *mut i32 as *mut c_void,
        ];
        self.check(
            unsafe {
                (self.cu_launch)(
                    self.l2_reduce_function,
                    16,
                    1,
                    1,
                    256,
                    1,
                    1,
                    0,
                    std::ptr::null_mut(),
                    args.as_mut_ptr(),
                    std::ptr::null_mut(),
                )
            },
            "cuLaunchKernel(l2_reduce_line)",
        )
    }

    /// Launches one MV statement. An overlapping `mvp` is run as two passes
    /// through a scratch buffer so that all reads precede all writes, like the
    /// CPU's write list.
    pub fn run_mv_line(&self, state: &GpuState, line: &MvLine) -> Result<(), String> {
        if line.mode == MV_MODE_NOP {
            return Ok(());
        }
        if state.pdm == 0 || state.dram == 0 {
            return Err("GPU state was allocated without MV support".into());
        }
        let total = line.threads();
        if total == 0 {
            return Ok(());
        }
        for r in [line.src, line.dst] {
            if r.mem == 1 {
                let end = r.addr.saturating_add(line.size);
                if end > crate::mv::DRAM_LONGS {
                    return Err(format!(
                        "MV DRAM range {}..{} wraps the CPU DRAM",
                        r.addr, end
                    ));
                }
                if end > state.dram_longs {
                    return Err(format!(
                        "MV DRAM range {}..{} exceeds the device DRAM of {} long words",
                        r.addr, end, state.dram_longs
                    ));
                }
            }
        }
        if line.snapshot && line.scratch_longs_needed() > state.scratch_longs {
            return Err(format!(
                "overlapping MV needs {} scratch long words, state has {}",
                line.scratch_longs_needed(),
                state.scratch_longs
            ));
        }
        let grid = total.div_ceil(256);
        if grid > u32::MAX as u64 {
            return Err("MV transfer is too large for a kernel grid".into());
        }
        let grid = grid as u32;
        let phases: &[i32] = if line.snapshot { &[0, 1] } else { &[2] };
        for &phase in phases {
            let mut pdm = state.pdm;
            let mut dram = state.dram;
            let mut l2bm = state.l2bm;
            let mut scratch = state.scratch;
            let mut dram_longs = state.dram_longs;
            let mut mode = line.mode as i32;
            let mut phase = phase;
            let mut parallel = line.parallel as i32;
            let mut src_mem = line.src.mem as i32;
            let mut src_group = line.src.group as i32;
            let mut src_l2b = line.src.l2b as i32;
            let mut src_addr = line.src.addr;
            let mut dst_mem = line.dst.mem as i32;
            let mut dst_group = line.dst.group as i32;
            let mut dst_l2b = line.dst.l2b as i32;
            let mut dst_addr = line.dst.addr;
            let mut size = line.size;
            let mut rrn_op = line.rrn_op as i32;
            let mut rrn_bits = line.rrn_bits as i32;
            let mut args = [
                &mut pdm as *mut u64 as *mut c_void,
                &mut dram as *mut u64 as *mut c_void,
                &mut l2bm as *mut u64 as *mut c_void,
                &mut scratch as *mut u64 as *mut c_void,
                &mut dram_longs as *mut u64 as *mut c_void,
                &mut mode as *mut i32 as *mut c_void,
                &mut phase as *mut i32 as *mut c_void,
                &mut parallel as *mut i32 as *mut c_void,
                &mut src_mem as *mut i32 as *mut c_void,
                &mut src_group as *mut i32 as *mut c_void,
                &mut src_l2b as *mut i32 as *mut c_void,
                &mut src_addr as *mut u64 as *mut c_void,
                &mut dst_mem as *mut i32 as *mut c_void,
                &mut dst_group as *mut i32 as *mut c_void,
                &mut dst_l2b as *mut i32 as *mut c_void,
                &mut dst_addr as *mut u64 as *mut c_void,
                &mut size as *mut u64 as *mut c_void,
                &mut rrn_op as *mut i32 as *mut c_void,
                &mut rrn_bits as *mut i32 as *mut c_void,
            ];
            self.check(
                unsafe {
                    (self.cu_launch)(
                        self.mv_function,
                        grid,
                        1,
                        1,
                        256,
                        1,
                        1,
                        0,
                        std::ptr::null_mut(),
                        args.as_mut_ptr(),
                        std::ptr::null_mut(),
                    )
                },
                "cuLaunchKernel(mv_line)",
            )?;
        }
        Ok(())
    }

    /// Launches one l1bmm@mab write.
    pub fn run_l1_write_line(&self, state: &GpuState, line: &L1WriteLine) -> Result<(), String> {
        let mut lm0 = state.lm0;
        let mut lm1 = state.lm1;
        let mut grf0 = state.grf0;
        let mut grf1 = state.grf1;
        let mut l1bm = state.l1bm;
        let mut mab = line.mab as i32;
        let mut addr = line.addr;
        let mut dwl = line.wl as i32;
        let mut smem = line.src.mem as i32;
        let mut s = line.src.base;
        let mut swl = line.src.wl as i32;
        let mut args = [
            &mut lm0 as *mut u64 as *mut c_void,
            &mut lm1 as *mut u64 as *mut c_void,
            &mut grf0 as *mut u64 as *mut c_void,
            &mut grf1 as *mut u64 as *mut c_void,
            &mut l1bm as *mut u64 as *mut c_void,
            &mut mab as *mut i32 as *mut c_void,
            &mut addr as *mut u32 as *mut c_void,
            &mut dwl as *mut i32 as *mut c_void,
            &mut smem as *mut i32 as *mut c_void,
            &mut s[0] as *mut u32 as *mut c_void,
            &mut s[1] as *mut u32 as *mut c_void,
            &mut s[2] as *mut u32 as *mut c_void,
            &mut s[3] as *mut u32 as *mut c_void,
            &mut swl as *mut i32 as *mut c_void,
        ];
        let grid = (crate::machine::PES as u32 + 255) / 256;
        self.check(
            unsafe {
                (self.cu_launch)(
                    self.l1_write_function,
                    grid,
                    1,
                    1,
                    256,
                    1,
                    1,
                    0,
                    std::ptr::null_mut(),
                    args.as_mut_ptr(),
                    std::ptr::null_mut(),
                )
            },
            "cuLaunchKernel(l1_write_line)",
        )
    }

    /// Launches one L1BM-to-PE read line.
    pub fn run_l1_read_line(&self, state: &GpuState, line: &L1ReadLine) -> Result<(), String> {
        let mut lm0 = state.lm0;
        let mut lm1 = state.lm1;
        let mut grf0 = state.grf0;
        let mut grf1 = state.grf1;
        let mut l1bm = state.l1bm;
        let mut op = line.op as i32;
        let mut addr = line.addr;
        let mut mabdiff = line.mabdiff as i32;
        let mut swl = line.wl as i32;
        let mut dmem = line.dst.mem as i32;
        let mut d = line.dst.base;
        let mut dwl = line.dst.wl as i32;
        let mut args = [
            &mut lm0 as *mut u64 as *mut c_void,
            &mut lm1 as *mut u64 as *mut c_void,
            &mut grf0 as *mut u64 as *mut c_void,
            &mut grf1 as *mut u64 as *mut c_void,
            &mut l1bm as *mut u64 as *mut c_void,
            &mut op as *mut i32 as *mut c_void,
            &mut addr as *mut u32 as *mut c_void,
            &mut mabdiff as *mut i32 as *mut c_void,
            &mut swl as *mut i32 as *mut c_void,
            &mut dmem as *mut i32 as *mut c_void,
            &mut d[0] as *mut u32 as *mut c_void,
            &mut d[1] as *mut u32 as *mut c_void,
            &mut d[2] as *mut u32 as *mut c_void,
            &mut d[3] as *mut u32 as *mut c_void,
            &mut dwl as *mut i32 as *mut c_void,
        ];
        let grid = (crate::machine::PES as u32 + 255) / 256;
        self.check(
            unsafe {
                (self.cu_launch)(
                    self.l1_function,
                    grid,
                    1,
                    1,
                    256,
                    1,
                    1,
                    0,
                    std::ptr::null_mut(),
                    args.as_mut_ptr(),
                    std::ptr::null_mut(),
                )
            },
            "cuLaunchKernel(l1_read_line)",
        )
    }

    /// Launches one matrix-register write (`fmwrite`/`gmwrite`).
    pub fn run_mat_write_line(&self, state: &GpuState, line: &MatWriteLine) -> Result<(), String> {
        if !matches!(line.prec, Prec::F | Prec::G) {
            return Err("mat_write_line supports f32 and pseudo-single".into());
        }
        let mut lm0 = state.lm0;
        let mut lm1 = state.lm1;
        let mut grf0 = state.grf0;
        let mut grf1 = state.grf1;
        let mut mauf = state.mauf;
        let mut aluf = state.aluf;
        let mut mats = state.mats;
        let mut side = line.side as i32;
        let mut addr = line.addr;
        let mut smem = line.src.mem as i32;
        let mut s = line.src.base;
        let mut swl = line.src.wl as i32;
        let mut sneg = line.src.neg as i32;
        let mut args = [
            &mut lm0 as *mut u64 as *mut c_void,
            &mut lm1 as *mut u64 as *mut c_void,
            &mut grf0 as *mut u64 as *mut c_void,
            &mut grf1 as *mut u64 as *mut c_void,
            &mut mauf as *mut u64 as *mut c_void,
            &mut aluf as *mut u64 as *mut c_void,
            &mut mats as *mut u64 as *mut c_void,
            &mut side as *mut i32 as *mut c_void,
            &mut addr as *mut u32 as *mut c_void,
            &mut smem as *mut i32 as *mut c_void,
            &mut s[0] as *mut u32 as *mut c_void,
            &mut s[1] as *mut u32 as *mut c_void,
            &mut s[2] as *mut u32 as *mut c_void,
            &mut s[3] as *mut u32 as *mut c_void,
            &mut swl as *mut i32 as *mut c_void,
            &mut sneg as *mut i32 as *mut c_void,
        ];
        let grid = (crate::machine::PES as u32 + 255) / 256;
        self.check(
            unsafe {
                (self.cu_launch)(
                    self.mat_write_function,
                    grid,
                    1,
                    1,
                    256,
                    1,
                    1,
                    0,
                    std::ptr::null_mut(),
                    args.as_mut_ptr(),
                    std::ptr::null_mut(),
                )
            },
            "cuLaunchKernel(mat_write_line)",
        )
    }

    /// Launches one matrix-register read (`fmread`/`gmread`).
    pub fn run_mat_read_line(&self, state: &GpuState, line: &MatReadLine) -> Result<(), String> {
        if !matches!(line.prec, Prec::F | Prec::G) {
            return Err("mat_read_line supports f32 and pseudo-single".into());
        }
        let mut lm0 = state.lm0;
        let mut lm1 = state.lm1;
        let mut grf0 = state.grf0;
        let mut grf1 = state.grf1;
        let mut mreadf = state.mreadf;
        let mut mats = state.mats;
        let mut side = line.side as i32;
        let mut addr = line.addr;
        let mut dmem = line.dst.mem as i32;
        let mut d = line.dst.base;
        let mut dwl = line.dst.wl as i32;
        let mut args = [
            &mut lm0 as *mut u64 as *mut c_void,
            &mut lm1 as *mut u64 as *mut c_void,
            &mut grf0 as *mut u64 as *mut c_void,
            &mut grf1 as *mut u64 as *mut c_void,
            &mut mreadf as *mut u64 as *mut c_void,
            &mut mats as *mut u64 as *mut c_void,
            &mut side as *mut i32 as *mut c_void,
            &mut addr as *mut u32 as *mut c_void,
            &mut dmem as *mut i32 as *mut c_void,
            &mut d[0] as *mut u32 as *mut c_void,
            &mut d[1] as *mut u32 as *mut c_void,
            &mut d[2] as *mut u32 as *mut c_void,
            &mut d[3] as *mut u32 as *mut c_void,
            &mut dwl as *mut i32 as *mut c_void,
        ];
        let grid = (crate::machine::PES as u32 + 255) / 256;
        self.check(
            unsafe {
                (self.cu_launch)(
                    self.mat_read_function,
                    grid,
                    1,
                    1,
                    256,
                    1,
                    1,
                    0,
                    std::ptr::null_mut(),
                    args.as_mut_ptr(),
                    std::ptr::null_mut(),
                )
            },
            "cuLaunchKernel(mat_read_line)",
        )
    }

    /// Launches one matrix MAU line (`fmfma`/`gmmul` and friends).
    pub fn run_mat_mau_line(&self, state: &GpuState, line: &MatMauLine) -> Result<(), String> {
        let prec = match line.prec {
            Prec::F => 0i32,
            Prec::G => 1i32,
            _ => return Err("mat_mau_line supports f32 and pseudo-single".into()),
        };
        let mut lm0 = state.lm0;
        let mut lm1 = state.lm1;
        let mut grf0 = state.grf0;
        let mut grf1 = state.grf1;
        let mut mauf = state.mauf;
        let mut aluf = state.aluf;
        let mut mats = state.mats;
        let mut prec = prec;
        let mut side = line.side as i32;
        let mut kind = line.kind as i32;
        let mut xmem = line.x.mem as i32;
        let mut x = line.x.base;
        let mut xwl = line.x.wl as i32;
        let mut xneg = line.x.neg as i32;
        let mut ymem = line.y.mem as i32;
        let mut y = line.y.base;
        let mut ywl = line.y.wl as i32;
        let mut yneg = line.y.neg as i32;
        let (mut dmem, mut d, mut dwl) = match line.dst {
            AluDst::Mem(dst) => (dst.mem as i32, dst.base, dst.wl as i32),
            _ => (0i32, [0u32; 4], 0i32),
        };
        let mut args = [
            &mut lm0 as *mut u64 as *mut c_void,
            &mut lm1 as *mut u64 as *mut c_void,
            &mut grf0 as *mut u64 as *mut c_void,
            &mut grf1 as *mut u64 as *mut c_void,
            &mut mauf as *mut u64 as *mut c_void,
            &mut aluf as *mut u64 as *mut c_void,
            &mut mats as *mut u64 as *mut c_void,
            &mut prec as *mut i32 as *mut c_void,
            &mut side as *mut i32 as *mut c_void,
            &mut kind as *mut i32 as *mut c_void,
            &mut xmem as *mut i32 as *mut c_void,
            &mut x[0] as *mut u32 as *mut c_void,
            &mut x[1] as *mut u32 as *mut c_void,
            &mut x[2] as *mut u32 as *mut c_void,
            &mut x[3] as *mut u32 as *mut c_void,
            &mut xwl as *mut i32 as *mut c_void,
            &mut xneg as *mut i32 as *mut c_void,
            &mut ymem as *mut i32 as *mut c_void,
            &mut y[0] as *mut u32 as *mut c_void,
            &mut y[1] as *mut u32 as *mut c_void,
            &mut y[2] as *mut u32 as *mut c_void,
            &mut y[3] as *mut u32 as *mut c_void,
            &mut ywl as *mut i32 as *mut c_void,
            &mut yneg as *mut i32 as *mut c_void,
            &mut dmem as *mut i32 as *mut c_void,
            &mut d[0] as *mut u32 as *mut c_void,
            &mut d[1] as *mut u32 as *mut c_void,
            &mut d[2] as *mut u32 as *mut c_void,
            &mut d[3] as *mut u32 as *mut c_void,
            &mut dwl as *mut i32 as *mut c_void,
        ];
        let grid = ((crate::machine::PES / 4) as u32 + 255) / 256;
        self.check(
            unsafe {
                (self.cu_launch)(
                    self.mat_mau_function,
                    grid,
                    1,
                    1,
                    256,
                    1,
                    1,
                    0,
                    std::ptr::null_mut(),
                    args.as_mut_ptr(),
                    std::ptr::null_mut(),
                )
            },
            "cuLaunchKernel(mat_mau_line)",
        )
    }

    /// Runs the f32 vfma kernel over three equal-length input slices.
    pub fn vfma_f32(&self, a: &[u32], b: &[u32], c: &[u32]) -> Result<Vec<u32>, String> {
        let n = a.len();
        if b.len() != n || c.len() != n {
            return Err("vfma slices differ in length".into());
        }
        if n == 0 {
            return Ok(Vec::new());
        }
        let size = n * 4;
        let mut buffers = [0u64; 4];
        for buffer in &mut buffers {
            self.check(unsafe { (self.cu_mem_alloc)(buffer, size) }, "cuMemAlloc")?;
        }
        let result = (|| -> Result<(), String> {
            self.check(unsafe { (self.cu_htod)(buffers[0], a.as_ptr() as *const c_void, size) }, "upload a")?;
            self.check(unsafe { (self.cu_htod)(buffers[1], b.as_ptr() as *const c_void, size) }, "upload b")?;
            self.check(unsafe { (self.cu_htod)(buffers[2], c.as_ptr() as *const c_void, size) }, "upload c")?;
            let args = [
                &mut buffers[0] as *mut u64 as *mut c_void,
                &mut buffers[1] as *mut u64 as *mut c_void,
                &mut buffers[2] as *mut u64 as *mut c_void,
                &mut buffers[3] as *mut u64 as *mut c_void,
            ];
            let mut count = n as i32;
            let mut all = [
                args[0], args[1], args[2], args[3],
                &mut count as *mut i32 as *mut c_void,
            ];
            let grid = ((n as u32) + 255) / 256;
            self.check(
                unsafe {
                    (self.cu_launch)(
                        self.function,
                        grid,
                        1,
                        1,
                        256,
                        1,
                        1,
                        0,
                        std::ptr::null_mut(),
                        all.as_mut_ptr(),
                        std::ptr::null_mut(),
                    )
                },
                "cuLaunchKernel",
            )?;
            self.check(unsafe { (self.cu_sync)() }, "cuCtxSynchronize")?;
            Ok(())
        })();
        let mut out = vec![0u32; n];
        if result.is_ok() {
            self.check(
                unsafe { (self.cu_dtoh)(out.as_mut_ptr() as *mut c_void, buffers[3], size) },
                "download",
            )?;
        }
        for buffer in buffers {
            let _ = unsafe { (self.cu_mem_free)(buffer) };
        }
        result.map(|()| out)
    }
}

impl Drop for Gpu {
    fn drop(&mut self) {
        unsafe { (self.cu_ctx_destroy)(self.context) };
    }
}

#[cfg(test)]
mod mv_tests {
    use super::*;
    use crate::mv::parse;

    fn descriptor(text: &str) -> Option<MvLine> {
        mv_line_from_mv(&parse(text).unwrap())
    }

    #[test]
    fn mv_descriptors() {
        let line = descriptor("mvp/n64i9f $p0@0 $lc0@2.1").unwrap();
        assert_eq!(line.mode, MV_MODE_P);
        assert!(!line.parallel);
        assert!(!line.snapshot);
        assert_eq!(line.size, 64);
        assert_eq!((line.src.mem, line.src.group), (0, 0));
        assert_eq!((line.dst.mem, line.dst.group, line.dst.l2b), (2, 2, 1));

        let line = descriptor("mvp/n256i9f $d0 $lc0@.0").unwrap();
        assert!(line.parallel);
        assert_eq!(line.size, 256);
        assert_eq!(line.src.mem, 1);

        // A remainder below 64 long words is ignored, as in the CPU.
        assert_eq!(descriptor("mvp/n100i9f $d0 $lc0@.0").unwrap().size, 64);

        let line = descriptor("mvp/n64i9f $p0@0 $p16@0").unwrap();
        assert!(line.snapshot);
        assert_eq!(line.scratch_longs_needed(), 64);
        assert!(!descriptor("mvp/n64i9f $p0@0 $p16@1").unwrap().snapshot);
        assert!(!descriptor("mvp/n64i9f $d0@0 $lc0@0.0").unwrap().snapshot);

        let line = descriptor("mvb2/n512i9f $d112000 $lc0").unwrap();
        assert_eq!(line.mode, MV_MODE_B2);
        assert_eq!(line.threads(), 4 * 512);
        assert_eq!(line.dram_longs_needed(), 112512);

        let line = descriptor("mvrffadd/n64i9f $lc0 $p0@0").unwrap();
        assert_eq!(line.mode, MV_MODE_R_PDM);
        assert_eq!((line.rrn_op, line.rrn_bits), (0, 32));
        let line = descriptor("mvr4dmax/n64i9f $lc0 $d0").unwrap();
        assert_eq!(line.mode, MV_MODE_R4);
        assert_eq!((line.rrn_op, line.rrn_bits), (1, 64));

        assert!(descriptor("mvp/n256nd4 $p1600@1 $di512@2").is_none());
        assert!(descriptor("mvp/n64i9f $p0@0 $lc0@.0").is_none());
        assert!(descriptor("mvb/n64i9f $p0@0 $d0@0").is_none());
        assert_eq!(descriptor("mvnop").unwrap().mode, MV_MODE_NOP);
    }
}

fn load_nvrtc() -> Result<Library, String> {
    if let Ok(path) = std::env::var("NVRTC_LIB") {
        return unsafe { Library::new(path) }.map_err(|e| format!("NVRTC_LIB: {e}"));
    }
    let home = std::env::var("HOME").unwrap_or_default();
    let candidates = [
        format!("{home}/.local/lib/python3.10/site-packages/nvidia/cuda_nvrtc/lib/libnvrtc.so.12"),
        format!("{home}/.local/lib/python3.11/site-packages/nvidia/cuda_nvrtc/lib/libnvrtc.so.12"),
        format!("{home}/.local/lib/python3.12/site-packages/nvidia/cuda_nvrtc/lib/libnvrtc.so.12"),
    ];
    for path in candidates {
        if Path::new(&path).exists() {
            return unsafe { Library::new(&path) }.map_err(|e| format!("{path}: {e}"));
        }
    }
    unsafe { Library::new("libnvrtc.so.12") }.map_err(|e| format!("libnvrtc.so.12: {e}"))
}
