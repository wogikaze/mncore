//! Minimal CUDA Driver API and NVRTC wrapper for the GPU backend.
//!
//! The libraries are loaded at runtime so the CPU build does not need a CUDA
//! toolchain. On WSL the driver comes from `/usr/lib/wsl/lib/libcuda.so.1`;
//! NVRTC comes from the PyTorch CUDA wheels unless `NVRTC_LIB` is set.

use std::ffi::{c_char, c_int, c_void, CStr, CString};
use std::path::Path;

use libloading::Library;

use crate::machine::MaskState;
use crate::vsm::{Expr, FwdKind, MauKind, MaskSel, MaskSource, MemKind, Op, Operand, Prec};

type CuResult = c_int;
type CuDevice = c_int;
type CuContext = *mut c_void;
type CuModule = *mut c_void;
type CuFunction = *mut c_void;
type CuDevicePtr = u64;

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
    let (kind, need_b) = match &expr.op {
        Op::Alu {
            name: crate::vsm::AluOp::Passa,
            prec: Some(Prec::F),
            ..
        } => (0u8, false),
        Op::Alu {
            name: crate::vsm::AluOp::Xor,
            prec: Some(Prec::I),
            ..
        } => (1u8, true),
        Op::Alu {
            name: crate::vsm::AluOp::Max,
            prec: Some(Prec::F),
            ..
        } => (2u8, true),
        Op::Alu {
            name: crate::vsm::AluOp::Rsqrt,
            prec: Some(Prec::F),
            ..
        } => (3u8, false),
        _ => return None,
    };
    if expr.flush.is_some() || expr.srcs.len() != if need_b { 2 } else { 1 } || expr.dsts.len() != 1 {
        return None;
    }
    let a = line_source(&expr.srcs[0])?;
    if a.neg {
        return None;
    }
    let b = if need_b {
        let b = line_source(&expr.srcs[1])?;
        if b.neg {
            return None;
        }
        b
    } else {
        MauSrc {
            mem: 0,
            wl: 1,
            base: [0; 4],
            neg: false,
        }
    };
    let dst = match &expr.dsts[0] {
        Operand::Mem { .. } => AluDst::Mem(mem_source(&expr.dsts[0], false, false)?),
        Operand::Omr { entry, mask: None } if (1..=15).contains(entry) => AluDst::Omr(*entry),
        Operand::Nowrite => AluDst::None,
        _ => return None,
    };
    Some(AluLine { kind, a, b, dst })
}

/// Destination of an ALU line: a PE memory, an OMR entry, or nowhere.
#[derive(Clone, Copy, Debug)]
pub enum AluDst {
    Mem(MauSrc),
    Omr(u8),
    None,
}

/// A single ALU line. Kind 0 is Passa and kind 1 is Xor.
#[derive(Clone, Copy, Debug)]
pub struct AluLine {
    pub kind: u8,
    pub a: MauSrc,
    pub b: MauSrc,
    pub dst: AluDst,
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
    free: CuMemFree,
}

impl Drop for GpuState {
    fn drop(&mut self) {
        unsafe {
            (self.free)(self.lm0);
            (self.free)(self.lm1);
            (self.free)(self.grf0);
            (self.free)(self.grf1);
            (self.free)(self.mauf);
            (self.free)(self.aluf);
            (self.free)(self.mask);
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

        let source = include_str!("../gpu/vfma_kernel.cu");
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
        Ok(Gpu {
            _cuda: cuda,
            _nvrtc: nvrtc,
            context,
            function,
            mau_function,
            alu_function,
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

    /// Allocates the four PE memories on the device.
    pub fn allocate_state(&self) -> Result<GpuState, String> {
        let lm_bytes = crate::machine::PES * crate::machine::LM_WORDS * 4;
        let grf_bytes = crate::machine::PES * crate::machine::GRF_WORDS * 4;
        let fwd_bytes = crate::machine::PES * 16 * 4;
        let mut buffers = [0u64; 7];
        let sizes = [
            lm_bytes,
            lm_bytes,
            grf_bytes,
            grf_bytes,
            fwd_bytes,
            fwd_bytes,
            fwd_bytes,
        ];
        for i in 0..7 {
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
        let mut kind = line.kind as i32;
        let mut amem = line.a.mem as i32;
        let mut a = line.a.base;
        let mut awl = line.a.wl as i32;
        let mut bmem = line.b.mem as i32;
        let mut b = line.b.base;
        let mut bwl = line.b.wl as i32;
        let (mut dmem, mut d, mut dwl, mut omr) = match line.dst {
            AluDst::Mem(dst) => (dst.mem as i32, dst.base, dst.wl as i32, 0i32),
            AluDst::Omr(entry) => (0i32, [0u32; 4], 0i32, entry as i32),
            AluDst::None => (0i32, [0u32; 4], 0i32, 0i32),
        };
        let mut args = [
            &mut lm0 as *mut u64 as *mut c_void,
            &mut lm1 as *mut u64 as *mut c_void,
            &mut grf0 as *mut u64 as *mut c_void,
            &mut grf1 as *mut u64 as *mut c_void,
            &mut mauf as *mut u64 as *mut c_void,
            &mut aluf as *mut u64 as *mut c_void,
            &mut mask as *mut u64 as *mut c_void,
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
