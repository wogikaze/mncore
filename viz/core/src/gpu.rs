//! Minimal CUDA Driver API and NVRTC wrapper for the GPU backend.
//!
//! The libraries are loaded at runtime so the CPU build does not need a CUDA
//! toolchain. On WSL the driver comes from `/usr/lib/wsl/lib/libcuda.so.1`;
//! NVRTC comes from the PyTorch CUDA wheels unless `NVRTC_LIB` is set.

use std::ffi::{c_char, c_int, c_void, CStr, CString};
use std::path::Path;

use libloading::Library;

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

/// One source or destination of a MAU line: memory kind (0 LM0, 1 LM1,
/// 2 GRF0, 3 GRF1) and the already-aligned base word address per cycle.
#[derive(Clone, Copy, Debug)]
pub struct MauSrc {
    pub mem: u8,
    pub base: [u32; 4],
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
}

/// LM0, LM1, GRF0 and GRF1 in device memory, in the same PE-major layout as
/// `machine::Mem`.
pub struct GpuState {
    lm0: u64,
    lm1: u64,
    grf0: u64,
    grf1: u64,
    free: CuMemFree,
}

impl Drop for GpuState {
    fn drop(&mut self) {
        unsafe {
            (self.free)(self.lm0);
            (self.free)(self.lm1);
            (self.free)(self.grf0);
            (self.free)(self.grf1);
        }
    }
}

pub struct Gpu {
    _cuda: Library,
    _nvrtc: Library,
    context: CuContext,
    function: CuFunction,
    mau_function: CuFunction,
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
        Ok(Gpu {
            _cuda: cuda,
            _nvrtc: nvrtc,
            context,
            function,
            mau_function,
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
        let mut buffers = [0u64; 4];
        let sizes = [lm_bytes, lm_bytes, grf_bytes, grf_bytes];
        for i in 0..4 {
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
        )
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

    /// Waits for all previously enqueued kernels.
    pub fn sync(&self) -> Result<(), String> {
        self.check(unsafe { (self.cu_sync)() }, "cuCtxSynchronize")
    }

    /// Launches one f32 MAU line for all 4,096 PEs and four cycles.
    pub fn run_mau_line(&self, state: &GpuState, line: &MauLine) -> Result<(), String> {
        if line.wl != 1 && line.wl != 2 {
            return Err("mau_line supports wl = 1 or 2".into());
        }
        let mut lm0 = state.lm0;
        let mut lm1 = state.lm1;
        let mut grf0 = state.grf0;
        let mut grf1 = state.grf1;
        let mut kind = line.kind as i32;
        let mut wl = line.wl as i32;
        let mut amem = line.a.mem as i32;
        let mut a = line.a.base;
        let mut bmem = line.b.mem as i32;
        let mut b = line.b.base;
        let mut cmem = line.c.mem as i32;
        let mut c = line.c.base;
        let mut dmem = line.dst.mem as i32;
        let mut d = line.dst.base;
        let mut args = [
            &mut lm0 as *mut u64 as *mut c_void,
            &mut lm1 as *mut u64 as *mut c_void,
            &mut grf0 as *mut u64 as *mut c_void,
            &mut grf1 as *mut u64 as *mut c_void,
            &mut kind as *mut i32 as *mut c_void,
            &mut wl as *mut i32 as *mut c_void,
            &mut amem as *mut i32 as *mut c_void,
            &mut a[0] as *mut u32 as *mut c_void,
            &mut a[1] as *mut u32 as *mut c_void,
            &mut a[2] as *mut u32 as *mut c_void,
            &mut a[3] as *mut u32 as *mut c_void,
            &mut bmem as *mut i32 as *mut c_void,
            &mut b[0] as *mut u32 as *mut c_void,
            &mut b[1] as *mut u32 as *mut c_void,
            &mut b[2] as *mut u32 as *mut c_void,
            &mut b[3] as *mut u32 as *mut c_void,
            &mut cmem as *mut i32 as *mut c_void,
            &mut c[0] as *mut u32 as *mut c_void,
            &mut c[1] as *mut u32 as *mut c_void,
            &mut c[2] as *mut u32 as *mut c_void,
            &mut c[3] as *mut u32 as *mut c_void,
            &mut dmem as *mut i32 as *mut c_void,
            &mut d[0] as *mut u32 as *mut c_void,
            &mut d[1] as *mut u32 as *mut c_void,
            &mut d[2] as *mut u32 as *mut c_void,
            &mut d[3] as *mut u32 as *mut c_void,
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
