//! Whole programs compiled to one specialized CUDA kernel.
//!
//! `Gpu::compile_program` emits a kernel whose body is the program's operation
//! list, unrolled: each operation calls the same executor as the interpreter
//! (`px_*` in program_kernel.cu) with its descriptor as a constant array, so
//! NVRTC folds the descriptor fields into the code. The executors, block
//! ownership and grid barriers are those of the interpreter (see program.rs);
//! the JIT only removes the per-operation dispatch and descriptor loads and
//! lets ALU/MAU lines whose cycles are independent run one thread per
//! (PE, cycle) with no staging.
//!
//! The CUBIN is cached under `target/gpu-jit-cache` (or `$MNCORE_JIT_CACHE`),
//! keyed by a hash of the generated source and the compile options.

use std::ffi::{c_char, c_int, c_void, CString};
use std::fmt::Write as _;

use super::program::{variable_fields, DevStateArgs, EncOp, PF_BARRIER, PF_UPDATE};
use super::*;

/// Threads per block of a JIT program: one per (PE, cycle) of the L1B.
pub const JIT_THREADS: u32 = 256;

/// Shared copies of the per-PE registers and the helpers that move them.
const JIT_SHARED_REGS: &str = r#"
__shared__ unsigned jsh_mauf[1024], jsh_aluf[1024], jsh_mask[1024], jsh_t[1024];
__shared__ unsigned jsh_mreadf[1024], jsh_lbf[1024], jsh_bar0[64], jsh_bar1[64];
__device__ __forceinline__ DevState jit_local_state() {
    DevState st = jit_st;
    st.mauf = jsh_mauf; st.aluf = jsh_aluf; st.mask = jsh_mask; st.t = jsh_t;
    st.mreadf = jsh_mreadf; st.lbf = jsh_lbf; st.bar0 = jsh_bar0; st.bar1 = jsh_bar1;
    return st;
}
// L2 prefetch of one row (two 128-byte lines: the block's PEs 0-31 and
// 32-63) of a PE memory, or one line of the block's own L1BM (mem 8).
__device__ __forceinline__ void jpf(int B, int tid, unsigned mem, unsigned row) {
    const void* p;
    if (mem < 4) {
        const unsigned* base = mem == 0 ? jit_st.lm0 : mem == 1 ? jit_st.lm1 : mem == 2 ? jit_st.grf0 : jit_st.grf1;
        unsigned len = mem < 2 ? 4096u : 512u;
        unsigned r = row;
        if (mem == 0) r += jsh_bar0[0];
        else if (mem == 1) r += jsh_bar1[0];
        p = base + PEM(B * 64 + (tid & 1) * 32, r & (len - 1));
    } else {
        if (tid & 1) return;
        p = jit_st.l1bm + (size_t)B * 8192 + row;
    }
    // A load whose result is never used: the warp does not wait for it, and
    // the line lands in L2 for the later operation.
    unsigned dummy;
    asm volatile("ld.global.cg.u32 %0, [%1];" : "=r"(dummy) : "l"(p));
}
__device__ __forceinline__ void jit_load_regs(int B, int tid) {
    for (int i = tid; i < 1024; i += 256) {
        unsigned g = (unsigned)(i >> 6) * 4096u + (unsigned)(B * 64 + (i & 63));
        jsh_mauf[i] = jit_st.mauf[g]; jsh_aluf[i] = jit_st.aluf[g];
        jsh_mask[i] = jit_st.mask[g]; jsh_t[i] = jit_st.t[g];
        jsh_mreadf[i] = jit_st.mreadf[g]; jsh_lbf[i] = jit_st.lbf[g];
    }
    if (tid < 64) {
        jsh_bar0[tid] = jit_st.bar0[B * 64 + tid];
        jsh_bar1[tid] = jit_st.bar1[B * 64 + tid];
    }
    __syncthreads();
}
__device__ __forceinline__ void jit_store_regs(int B, int tid) {
    __syncthreads();
    for (int i = tid; i < 1024; i += 256) {
        unsigned g = (unsigned)(i >> 6) * 4096u + (unsigned)(B * 64 + (i & 63));
        jit_st.mauf[g] = jsh_mauf[i]; jit_st.aluf[g] = jsh_aluf[i];
        jit_st.mask[g] = jsh_mask[i]; jit_st.t[g] = jsh_t[i];
        jit_st.mreadf[g] = jsh_mreadf[i]; jit_st.lbf[g] = jsh_lbf[i];
    }
    if (tid < 64) {
        jit_st.bar0[B * 64 + tid] = jsh_bar0[tid];
        jit_st.bar1[B * 64 + tid] = jsh_bar1[tid];
    }
}
"#;

/// Operations per generated chunk function.
const JIT_CHUNK: usize = 64;

/// A compiled program, ready to launch.
pub struct JitProgram {
    function: CuFunction,
    module: CuModule,
    /// `(kind, flags, direct)` of every operation.
    kinds: Vec<(u32, u32, bool)>,
    /// The state the program was bound to (its pointers are compiled in).
    lm0: u64,
    sync: u64,
    pub ops: usize,
    pub barriers: usize,
    pub words: u64,
    /// Operations whose cycles run as independent threads.
    pub direct: usize,
    /// Distinct operation shapes (compiled functions).
    pub shapes: usize,
    /// Seconds spent in NVRTC (0 when the cache was used).
    pub compile_seconds: f64,
    free: CuMemFree,
}

impl Drop for JitProgram {
    fn drop(&mut self) {
        // The module stays loaded with the context; only the counter is freed.
        unsafe { (self.free)(self.sync) };
    }
}

fn fnv1a(bytes: &[u8]) -> u64 {
    let mut h: u64 = 0xcbf29ce484222325;
    for &b in bytes {
        h ^= b as u64;
        h = h.wrapping_mul(0x100000001b3);
    }
    h
}


/// C++ field layout of the descriptors (program_kernel.cu / vfma_kernel.cu),
/// for assigning a descriptor field by field: every field a plain 32-bit word
/// except `W`, a 64-bit one.
#[derive(Clone, Copy)]
enum F {
    U(&'static str),
    A(&'static str, usize),
    A2(&'static str, usize, usize),
    W(&'static str),
    S(&'static str, &'static [F]),
    SA(&'static str, usize, &'static [F]),
}

const SRC: &[F] = &[
    F::U("mem"), F::U("wl"), F::A("base", 4), F::U("rnd"), F::U("fixed"), F::U("neg"),
    F::U("ext"), F::U("t_indirect"), F::U("madpe"),
];
const DST: &[F] = &[
    F::U("kind"), F::U("mem"), F::U("wl"), F::A("base", 4), F::U("entry"), F::U("mask_kind"),
    F::U("mask_entry"), F::U("mask_pattern"), F::U("mask_ll"), F::U("t_indirect"), F::U("madpe"),
];
const FLUSH: [F; 4] = [F::U("flush_kind"), F::U("flush_entry"), F::U("flush_pattern"), F::U("flush_ll")];

fn schema(kind: u32) -> Vec<F> {
    let mut v: Vec<F> = match kind {
        0 | 1 => vec![
            F::U("op"), F::U("prec"), F::U("uns"), F::U("arg"), F::U("imm"), F::U("imm_u"),
            F::S("a", SRC), F::S("b", SRC), F::U("ndst"), F::SA("dst", 16, DST),
        ],
        2 => vec![
            F::U("prec"), F::U("kind"), F::U("half"), F::U("round"), F::S("a", SRC), F::S("b", SRC),
            F::S("c", SRC), F::U("ndst"), F::SA("dst", 16, DST),
        ],
        3 => vec![
            F::U("op"), F::U("has_addr"), F::U("addr"), F::U("mabdiff"), F::U("wl"), F::U("ndst"),
            F::A("dm", 4), F::A2("db", 4, 4), F::A("dw", 4), F::A("mk", 4), F::A("mke", 4),
            F::A("mkp", 4), F::A("mkl", 4), F::A("dt", 4), F::A("dma", 4), F::U("fk"), F::U("fe"),
            F::U("fp"), F::U("fll"),
        ],
        4 => vec![
            F::U("op"), F::U("mab_sel"), F::U("mabdiff"), F::U("has_addr"), F::U("addr"), F::U("dwl"),
            F::U("smem"), F::A("s", 4), F::U("swl"), F::U("st"), F::U("sma"), F::U("two_src"),
            F::U("bits"), F::U("rrn"), F::U("round_it"), F::U("ext"), F::U("fk"), F::U("fe"),
            F::U("fp"), F::U("fll"),
        ],
        5 => vec![F::U("op"), F::U("a0"), F::U("a1"), F::U("l1b"), F::U("mask"), F::U("l2b")],
        6 => vec![F::U("op"), F::U("a0"), F::U("a1"), F::U("mask"), F::U("immode"), F::U("bits"), F::U("kind")],
        7 => vec![F::U("prec"), F::U("side"), F::U("wl"), F::U("addr"), F::S("src", SRC)],
        8 => vec![F::U("prec"), F::U("side"), F::U("addr"), F::U("ndst"), F::SA("dst", 16, DST)],
        9 => vec![
            F::U("prec"), F::U("side"), F::U("kind"), F::U("half"), F::U("round"), F::S("x", SRC),
            F::S("y", SRC), F::U("ndst"), F::SA("dst", 16, DST),
        ],
        10 => vec![
            F::W("src_addr"), F::W("dst_addr"), F::W("size"), F::W("nd"), F::W("total"), F::U("mode"),
            F::U("phase"), F::U("parallel"), F::U("src_mem"), F::U("src_group"), F::U("src_l2b"),
            F::U("dst_mem"), F::U("dst_group"), F::U("dst_l2b"), F::U("rrn_op"), F::U("rrn_bits"),
            F::U("src_indirect"), F::U("dst_indirect"),
        ],
        _ => vec![],
    };
    if matches!(kind, 0 | 1 | 2 | 8 | 9) {
        v.extend(FLUSH);
    }
    v
}

/// Flattens a schema to `(path, word index, 64-bit)` in layout order.
fn flatten(fields: &[F], prefix: &str, word: &mut usize, out: &mut Vec<(String, usize, bool)>) {
    for f in fields {
        match *f {
            F::U(n) => {
                out.push((format!("{prefix}{n}"), *word, false));
                *word += 1;
            }
            F::A(n, k) => {
                for i in 0..k {
                    out.push((format!("{prefix}{n}[{i}]"), *word, false));
                    *word += 1;
                }
            }
            F::A2(n, k, m) => {
                for i in 0..k {
                    for j in 0..m {
                        out.push((format!("{prefix}{n}[{i}][{j}]"), *word, false));
                        *word += 1;
                    }
                }
            }
            F::W(n) => {
                *word = word.next_multiple_of(2);
                out.push((format!("{prefix}{n}"), *word, true));
                *word += 2;
            }
            F::S(n, sub) => flatten(sub, &format!("{prefix}{n}."), word, out),
            F::SA(n, k, sub) => {
                for i in 0..k {
                    flatten(sub, &format!("{prefix}{n}[{i}]."), word, out);
                }
            }
        }
    }
}

fn type_name(kind: u32) -> &'static str {
    match kind {
        0 | 1 => "AluDesc",
        2 => "MauLineDesc",
        3 => "L1ReadArgs",
        4 => "L1WriteArgs",
        5 => "L2Args",
        6 => "L2RedArgs",
        7 => "MatWriteLineDesc",
        8 => "MatReadLineDesc",
        9 => "MatMauLineDesc",
        10 => "MvArgs",
        _ => "",
    }
}

/// The executor call of one shape, with the descriptor in a local `d`.
fn shape_call(kind: u32, direct: bool, upd: i32) -> String {
    match kind {
        0 if direct => format!("px_alu_direct(st, B, tid, d, {upd});"),
        0 => format!("px_alu(st, B, tid, 256, d, {upd}, sm);"),
        1 => format!("px_bfn(st, B, tid, 256, d, {upd}, sm);"),
        2 if direct => format!("px_mau_direct(st, B, tid, d, {upd});"),
        2 => format!("px_mau(st, B, tid, 256, d, {upd}, sm);"),
        3 => "px_l1r(st, B, tid, 256, d);".to_string(),
        4 => format!("px_l1w(st, B, tid, 256, d, {upd});"),
        5 => "px_l2(st, B, tid, 256, d);".to_string(),
        6 => "px_l2red(st, B, tid, 256, d);".to_string(),
        7 => "px_matw(st, B, tid, 256, d);".to_string(),
        8 => format!("px_matr(st, B, tid, 256, d, {upd});"),
        9 => format!("px_matmau(st, B, tid, 256, d, {upd}, sm);"),
        10 => "px_mv(st, B, tid, 256, d);".to_string(),
        _ => "px_clear_mreadf(st, B, tid, 256);".to_string(),
    }
}

fn desc_words(desc: &[u8]) -> Vec<u32> {
    desc.chunks(4)
        .map(|c| {
            let mut b = [0u8; 4];
            b[..c.len()].copy_from_slice(c);
            u32::from_le_bytes(b)
        })
        .collect()
}

/// The generated part of a JIT program: one specialized function per
/// operation shape, the per-operation address words, and the kernel.
fn generate(enc: &[EncOp]) -> (String, usize) {
    let mut src = String::new();
    // Device state pointers live in constant memory (written at load time).
    src.push_str("__constant__ DevState jit_st;\n");
    // Per-PE registers of the block's 64 PEs (PR16/PRB layout under MNCORE_JIT).
    src.push_str(JIT_SHARED_REGS);
    // Optional per-operation clock stamps: [block][op + 1], null when off.
    src.push_str("__constant__ unsigned long long* jit_prof;\n");
    let _ = writeln!(src, "#define JPROF(i) do {{ if (jit_prof && tid == 0) jit_prof[(size_t)B * {} + (i)] = clock64(); }} while (0)", enc.len() + 1);

    let mut shapes: std::collections::HashMap<(u32, bool, i32, Vec<u32>), usize> = Default::default();
    let mut op_shape = Vec::with_capacity(enc.len());
    for (i, e) in enc.iter().enumerate() {
        let upd = if e.flags & PF_UPDATE != 0 { 1 } else { 0 };
        let mut words = desc_words(&e.desc);
        // Zero the padding words (not in the schema): their bytes are not
        // initialized and must not split shapes.
        {
            let mut flat = Vec::new();
            let mut word = 0usize;
            flatten(&schema(e.kind), "", &mut word, &mut flat);
            let mut used = vec![false; words.len()];
            for (_, at, wide) in &flat {
                if *at < used.len() {
                    used[*at] = true;
                }
                if *wide && at + 1 < used.len() {
                    used[at + 1] = true;
                }
            }
            for (w, u) in words.iter_mut().zip(&used) {
                if !u {
                    *w = 0;
                }
            }
        }
        let fields = variable_fields(e.kind);
        let var: Vec<usize> = fields.iter().map(|f| f.0).collect();
        let mut shape = words.clone();
        for &v in &var {
            if v < shape.len() {
                shape[v] = 0;
            }
        }
        let key = (e.kind, e.direct, upd, shape.clone());
        let next = shapes.len();
        let id = *shapes.entry(key).or_insert_with(|| {
            // The shape function: constant words, plus the variable words
            // read from the operation's address array `p`.
            let ty = type_name(e.kind);
            let _ = writeln!(
                src,
                "__device__ __noinline__ void js{next}(int B, int tid, const unsigned* p, ProgSmem& sm) {{\nconst DevState st = jit_local_state();"
            );
            if !ty.is_empty() {
                // Every field is assigned by name: constants from the shape,
                // addresses from `p`. The descriptor then lives in registers.
                let mut flat = Vec::new();
                let mut word = 0usize;
                flatten(&schema(e.kind), "", &mut word, &mut flat);
                assert!(
                    word.next_multiple_of(2) * 4 == e.desc.len().next_multiple_of(8),
                    "descriptor layout of kind {} does not match its schema",
                    e.kind
                );
                let _ = writeln!(src, "{ty} d;");
                for (path, at, wide) in &flat {
                    let var_at = var.iter().position(|&v| v == *at);
                    match (wide, var_at) {
                        (true, Some(j)) => {
                            let _ = writeln!(src, "d.{path} = (unsigned long long)p[{j}] | ((unsigned long long)p[{}] << 32);", j + 1);
                        }
                        (true, None) => {
                            let v = shape[*at] as u64 | ((shape[at + 1] as u64) << 32);
                            let _ = writeln!(src, "d.{path} = {v:#x}ull;");
                        }
                        (false, Some(j)) => {
                            let _ = writeln!(src, "d.{path} = p[{j}];");
                        }
                        (false, None) => {
                            let _ = writeln!(src, "d.{path} = {:#x}u;", shape[*at]);
                        }
                    }
                }
            }
            src.push_str(&shape_call(e.kind, e.direct, upd));
            src.push_str("\n}\n");
            next
        });
        // The address words of this operation.
        if !var.is_empty() {
            let _ = write!(src, "static __device__ const unsigned jv{i}[] = {{");
            for (j, &v) in var.iter().enumerate() {
                if j > 0 {
                    src.push(',');
                }
                let _ = write!(src, "{:#x}u", words.get(v).copied().unwrap_or(0));
            }
            src.push_str("};\n");
        }
        op_shape.push((id, !var.is_empty()));
    }

    let distance: usize = std::env::var("MNCORE_JIT_PREFETCH").ok().and_then(|v| v.parse().ok()).unwrap_or(4);
    // The operations go into chunk functions so that NVRTC optimizes bounded
    // pieces instead of one huge function.
    let chunks: Vec<(usize, &[EncOp])> =
        enc.chunks(JIT_CHUNK).enumerate().map(|(k, c)| (k * JIT_CHUNK, c)).collect();
    for (k, (start, chunk)) in chunks.iter().enumerate() {
        let _ = writeln!(
            src,
            "__device__ __noinline__ void jit_chunk{k}(int B, int tid, ProgSmem& sm, unsigned* sync, unsigned base, unsigned& barriers) {{\nconst unsigned nb = gridDim.x;"
        );
        for (j, e) in chunk.iter().enumerate() {
            let i = start + j;
            let _ = writeln!(src, "JPROF({i});");
            // Prefetch what operation i + D reads (the first chunk also covers
            // operations 0..D at its start).
            let targets: Vec<usize> = if i == 0 { (0..=distance.min(enc.len().saturating_sub(1))).collect() } else { vec![i + distance] };
            if distance > 0 {
                for t in targets {
                    if let Some(op) = enc.get(t) {
                        if !op.prefetch.is_empty() && op.prefetch.len() <= 128 {
                            src.push_str("switch (tid >> 1) {");
                            for (k, e) in op.prefetch.iter().enumerate() {
                                let _ = write!(src, "case {k}: jpf(B, tid, {}u, {}u); break;", e >> 16, e & 0xffff);
                            }
                            src.push_str("default: break; }\n");
                        }
                    }
                }
            }
            if e.flags & PF_BARRIER != 0 && std::env::var("MNCORE_JIT_NOGRID").is_err() {
                src.push_str("++barriers; prog_grid_barrier(&sync[0], base + barriers * nb);\n");
            }
            let (id, has_var) = op_shape[i];
            let arr = if has_var { format!("jv{i}") } else { "0".to_string() };
            // MNCORE_JIT_NOSYNC (experiment only, wrong results): no block
            // barrier between operations, to measure the overlap potential.
            if std::env::var("MNCORE_JIT_NOSYNC").is_ok() {
                let _ = writeln!(src, "js{id}(B, tid, {arr}, sm);");
            } else {
                let _ = writeln!(src, "js{id}(B, tid, {arr}, sm);\n__syncthreads();");
            }
        }
        src.push_str("}\n");
    }
    src.push_str(
        "extern \"C\" __global__ void __launch_bounds__(256, 3) jit_program(unsigned* sync) {\n\
         const int B = blockIdx.x;\n\
         const int tid = threadIdx.x;\n\
         const unsigned nb = gridDim.x;\n\
         __shared__ ProgSmem sm;\n\
         const unsigned base = sync[1];\n\
         unsigned barriers = 0;\n\
         jit_load_regs(B, tid);\n",
    );
    for k in 0..chunks.len() {
        let _ = writeln!(src, "jit_chunk{k}(B, tid, sm, sync, base, barriers);");
    }
    let _ = writeln!(src, "JPROF({});", enc.len());
    src.push_str("jit_store_regs(B, tid);\n");
    src.push_str(
        "++barriers; prog_grid_barrier(&sync[0], base + barriers * nb);\n\
         if (B == 0 && tid == 0) sync[1] = base + barriers * nb;\n}\n",
    );
    (src, shapes.len())
}

impl Gpu {
    /// Compiles NVRTC source to a CUBIN for this device.
    fn nvrtc_cubin(&self, source: &str, options: &[String]) -> Result<Vec<u8>, String> {
        let source_c = CString::new(source).map_err(|e| e.to_string())?;
        let name = CString::new("jit_program.cu").unwrap();
        let mut program: NvrtcProgram = std::ptr::null_mut();
        let created = unsafe {
            (self.nvrtc_create)(
                &mut program,
                source_c.as_ptr(),
                name.as_ptr(),
                0,
                std::ptr::null(),
                std::ptr::null(),
            )
        };
        if created != 0 {
            return Err(format!("nvrtcCreateProgram: {created}"));
        }
        let opts: Vec<CString> = options.iter().map(|o| CString::new(o.as_str()).unwrap()).collect();
        let ptrs: Vec<*const c_char> = opts.iter().map(|o| o.as_ptr()).collect();
        let compiled = unsafe { (self.nvrtc_compile)(program, ptrs.len() as c_int, ptrs.as_ptr()) };
        if compiled != 0 {
            let mut size = 0usize;
            unsafe { (self.nvrtc_log_size)(program, &mut size) };
            let mut log = vec![0u8; size.max(1)];
            if size > 0 {
                unsafe { (self.nvrtc_log)(program, log.as_mut_ptr() as *mut c_char) };
            }
            unsafe { (self.nvrtc_destroy)(&mut program) };
            return Err(format!("nvrtcCompileProgram: {}", String::from_utf8_lossy(&log)));
        }
        let mut size = 0usize;
        unsafe { (self.nvrtc_cubin_size)(program, &mut size) };
        let mut cubin = vec![0u8; size];
        unsafe { (self.nvrtc_cubin)(program, cubin.as_mut_ptr() as *mut c_char) };
        unsafe { (self.nvrtc_destroy)(&mut program) };
        Ok(cubin)
    }

    /// Compiles a lowered program into one specialized kernel.
    pub fn compile_program(
        &self,
        state: &GpuState,
        ops: &[GpuOp],
        words: u64,
    ) -> Result<JitProgram, String> {
        let enc = self.encode_ops(state, ops)?;
        let barriers = enc.iter().filter(|e| e.flags & PF_BARRIER != 0).count();
        let direct = enc.iter().filter(|e| e.direct).count();
        let mut source = String::new();
        source.push_str(include_str!("../../gpu/vfma_kernel.cu"));
        source.push_str(include_str!("../../gpu/mv_kernel.cu"));
        source.push_str(include_str!("../../gpu/program_kernel.cu"));
        let (generated, shapes) = generate(&enc);
        source.push_str(&generated);
        let mut options = vec![
            format!("--gpu-architecture=sm_{}{}", self.arch.0, self.arch.1),
            "--device-int128".to_string(),
            "-DMNCORE_JIT".to_string(),
        ];
        if let Ok(extra) = std::env::var("MNCORE_NVRTC_OPTS") {
            options.extend(extra.split_whitespace().map(str::to_string));
        }
        if let Ok(path) = std::env::var("MNCORE_JIT_DUMP") {
            let _ = std::fs::write(path, &source);
        }
        let key = fnv1a(format!("{}\n{}", options.join(" "), source).as_bytes());
        let dir = std::env::var("MNCORE_JIT_CACHE").unwrap_or_else(|_| {
            concat!(env!("CARGO_MANIFEST_DIR"), "/target/gpu-jit-cache").to_string()
        });
        let path = std::path::Path::new(&dir).join(format!("{key:016x}.cubin"));
        let mut compile_seconds = 0.0;
        let cubin = match std::fs::read(&path) {
            Ok(bytes) if !bytes.is_empty() => bytes,
            _ => {
                let start = std::time::Instant::now();
                let cubin = self.nvrtc_cubin(&source, &options)?;
                compile_seconds = start.elapsed().as_secs_f64();
                let _ = std::fs::create_dir_all(&dir);
                let _ = std::fs::write(&path, &cubin);
                cubin
            }
        };
        let mut module: CuModule = std::ptr::null_mut();
        self.check(
            unsafe {
                (self.cu_module_load)(
                    &mut module,
                    cubin.as_ptr() as *const c_void,
                    0,
                    std::ptr::null(),
                    std::ptr::null(),
                )
            },
            "cuModuleLoadDataEx(jit)",
        )?;
        let mut function: CuFunction = std::ptr::null_mut();
        self.check(
            unsafe {
                (self.cu_get_function)(&mut function, module, b"jit_program\0".as_ptr() as *const c_char)
            },
            "cuModuleGetFunction(jit_program)",
        )?;
        let mut st_ptr: u64 = 0;
        let mut st_size: usize = 0;
        self.check(
            unsafe {
                (self.cu_module_get_global)(
                    &mut st_ptr,
                    &mut st_size,
                    module,
                    b"jit_st\0".as_ptr() as *const c_char,
                )
            },
            "cuModuleGetGlobal(jit_st)",
        )?;
        let st = DevStateArgs::from_state(state);
        if st_size != std::mem::size_of::<DevStateArgs>() {
            return Err(format!("jit_st has {st_size} bytes"));
        }
        self.check(
            unsafe {
                (self.cu_htod)(st_ptr, &st as *const DevStateArgs as *const c_void, st_size)
            },
            "upload jit_st",
        )?;
        let mut sync: u64 = 0;
        self.check(unsafe { (self.cu_mem_alloc)(&mut sync, 16) }, "cuMemAlloc(jit sync)")?;
        let zero = [0u8; 16];
        self.check(
            unsafe { (self.cu_htod)(sync, zero.as_ptr() as *const c_void, 16) },
            "zero jit sync",
        )?;
        self.check(unsafe { (self.cu_sync)() }, "sync jit upload")?;
        Ok(JitProgram {
            function,
            module,
            kinds: enc.iter().map(|e| (e.kind, e.flags, e.direct)).collect(),
            lm0: state.lm0,
            sync,
            ops: enc.len(),
            barriers,
            words,
            direct,
            shapes,
            compile_seconds,
            free: self.cu_mem_free,
        })
    }

    /// Runs a JIT program once with per-operation SM clock stamps and returns
    /// `(kind, flags, direct, median-over-blocks cycles)` per operation.
    pub fn profile_jit(
        &self,
        state: &GpuState,
        program: &JitProgram,
    ) -> Result<Vec<(u32, u32, bool, u64)>, String> {
        let n = program.kinds.len();
        let len = PROGRAM_BLOCKS as usize * (n + 1);
        let mut prof: u64 = 0;
        self.check(unsafe { (self.cu_mem_alloc)(&mut prof, len * 8) }, "cuMemAlloc(prof)")?;
        let mut sym: u64 = 0;
        let mut size: usize = 0;
        self.check(
            unsafe {
                (self.cu_module_get_global)(&mut sym, &mut size, program.module, b"jit_prof\0".as_ptr() as *const c_char)
            },
            "cuModuleGetGlobal(jit_prof)",
        )?;
        let set = |v: u64| {
            self.check(unsafe { (self.cu_htod)(sym, &v as *const u64 as *const c_void, 8) }, "set jit_prof")?;
            self.check(unsafe { (self.cu_sync)() }, "sync jit_prof")
        };
        set(prof)?;
        // Several runs, keeping each operation's minimum: the GPU is shared with
        // the desktop, and a time slice taken mid-run would show up as one slow
        // operation.
        let runs: usize = std::env::var("GPU_PROFILE_RUNS").ok().and_then(|v| v.parse().ok()).unwrap_or(5);
        let result = (|| {
            let mut best = vec![u64::MAX; n];
            for _ in 0..runs.max(1) {
                self.launch_jit(state, program)?;
                self.check(unsafe { (self.cu_sync)() }, "sync prof")?;
                let mut t = vec![0u64; len];
                self.check(
                    unsafe { (self.cu_dtoh)(t.as_mut_ptr() as *mut c_void, prof, len * 8) },
                    "download prof",
                )?;
                if std::env::var("GPU_PROFILE_BLOCKS").is_ok() {
                    // Busy cycles per block (excluding grid-barrier waits is not
                    // possible here; this is the span from first to last op).
                    let mut spans: Vec<(u64, usize)> = (0..PROGRAM_BLOCKS as usize)
                        .map(|b| (t[b * (n + 1) + n] - t[b * (n + 1)], b))
                        .collect();
                    spans.sort_unstable();
                    let mut smids = vec![0u32; 0];
                    let _ = &mut smids;
                    eprintln!("block spans (cycles): min {:?} median {:?} max {:?}", spans[0], spans[spans.len() / 2], spans[spans.len() - 1]);
                    // Work between barriers: sum over ops of per-block durations, per block.
                    let mut work = vec![0u64; PROGRAM_BLOCKS as usize];
                    for b in 0..PROGRAM_BLOCKS as usize {
                        for i in 0..n {
                            if program.kinds[i].1 & PF_BARRIER == 0 {
                                work[b] += t[b * (n + 1) + i + 1] - t[b * (n + 1) + i];
                            }
                        }
                    }
                    let mut w: Vec<(u64, usize)> = work.iter().copied().zip(0..).collect();
                    w.sort_unstable();
                    eprintln!("non-barrier work per block: min {:?} median {:?} max {:?}", w[0], w[w.len() / 2], w[w.len() - 1]);
                    eprintln!("slowest blocks: {:?}", &w[w.len() - 10..]);
                }
                for i in 0..n {
                    let mut d: Vec<u64> = (0..PROGRAM_BLOCKS as usize)
                        .map(|b| t[b * (n + 1) + i + 1].saturating_sub(t[b * (n + 1) + i]))
                        .collect();
                    d.sort_unstable();
                    best[i] = best[i].min(d[d.len() / 2]);
                }
            }
            Ok(best
                .iter()
                .enumerate()
                .map(|(i, &c)| {
                    let (k, f, dir) = program.kinds[i];
                    (k, f, dir, c)
                })
                .collect())
        })();
        set(0)?;
        unsafe { (self.cu_mem_free)(prof) };
        result
    }

    /// Registers per thread and local bytes per thread of a JIT program.
    pub fn jit_resources(&self, program: &JitProgram) -> (i32, i32) {
        let mut regs = 0;
        let mut local = 0;
        unsafe {
            (self.cu_func_attr)(&mut regs, 4, program.function);
            (self.cu_func_attr)(&mut local, 3, program.function);
        }
        (regs, local)
    }

    /// Enqueues one run of a compiled program (one cooperative launch).
    pub fn launch_jit(&self, state: &GpuState, program: &JitProgram) -> Result<(), String> {
        if state.lm0 != program.lm0 {
            return Err("a JIT program runs only on the state it was compiled for".into());
        }
        let mut sync = program.sync;
        let mut args = [&mut sync as *mut u64 as *mut c_void];
        self.check(
            unsafe {
                (self.cu_launch_coop)(
                    program.function,
                    PROGRAM_BLOCKS,
                    1,
                    1,
                    JIT_THREADS,
                    1,
                    1,
                    0,
                    self.stream,
                    args.as_mut_ptr(),
                )
            },
            "cuLaunchCooperativeKernel(jit_program)",
        )
    }
}
