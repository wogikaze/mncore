// Whole-program interpreter for the GPU backend.
//
// This file is concatenated after vfma_kernel.cu and mv_kernel.cu. One
// cooperative launch runs a whole lowered program: the host stores the
// instruction list and the per-instruction descriptors in device memory, and
// every block walks the list in order.
//
// Block B owns L1B B (PEs 64B..64B+63, MABs 16B..16B+15, L1BM B). PE-local and
// L1B-local work is done only by the owning block, so consecutive instructions
// need just a __syncthreads. The host inserts a grid-wide barrier (flag
// PF_BARRIER) only before an instruction whose data another block touched since
// the previous barrier (L2BM, PDM, DRAM, DAR, other L1Bs).

#define PK_ALU 0
#define PK_BFN 1
#define PK_MAU 2
#define PK_L1R 3
#define PK_L1W 4
#define PK_L2 5
#define PK_L2RED 6
#define PK_MATW 7
#define PK_MATR 8
#define PK_MATMAU 9
#define PK_MV 10
#define PK_CLEAR_MREADF 11

#define PF_UPDATE 1u
#define PF_BARRIER 2u

#define PROGRAM_BLOCKS 64
// Largest descriptor in long words (MatMauLineDesc / AluDesc with 16 destinations).
#define PROG_DESC_LONGS 160

struct DevState {
    unsigned* lm0;
    unsigned* lm1;
    unsigned* grf0;
    unsigned* grf1;
    unsigned* mauf;
    unsigned* aluf;
    unsigned* mask;
    unsigned* t;
    unsigned* mreadf;
    unsigned* lbf;
    unsigned* bar0;
    unsigned* bar1;
    unsigned* mats;
    unsigned long long* l1bm;
    unsigned long long* l2bm;
    unsigned long long* lbi;
    unsigned long long* pdm;
    unsigned long long* dram;
    unsigned long long* scratch;
    unsigned long long dram_longs;
    unsigned* dar;
    unsigned* darbuf;
    unsigned* dar_addr;
    unsigned* mv_errors;
};

struct ProgIns {
    unsigned kind;
    unsigned flags;
    unsigned off;
    unsigned aux;
};

struct L1ReadArgs {
    int op, has_addr;
    unsigned addr;
    int mabdiff, wl, ndst;
    int dm[4];
    unsigned db[4][4];
    int dw[4], mk[4], mke[4], mkp[4], mkl[4], dt[4], dma[4];
    int fk, fe, fp, fll;
};

struct L1WriteArgs {
    int op, mab_sel, mabdiff, has_addr;
    unsigned addr;
    int dwl, smem;
    unsigned s[4];
    int swl, st, sma, two_src, bits, rrn, round_it, ext;
    int fk, fe, fp, fll;
};

struct L2Args {
    int op;
    unsigned a0, a1;
    int l1b, mask, l2b;
};

struct L2RedArgs {
    int op;
    unsigned a0, a1;
    int mask, immode, bits, kind;
};

struct MvArgs {
    unsigned long long src_addr, dst_addr, size, nd, total;
    int mode, phase, parallel;
    int src_mem, src_group, src_l2b;
    int dst_mem, dst_group, dst_l2b;
    int rrn_op, rrn_bits, src_indirect, dst_indirect;
};

__device__ __forceinline__ unsigned prog_ld_acquire(const unsigned* p) {
    unsigned v;
    asm volatile("ld.acquire.gpu.u32 %0, [%1];" : "=r"(v) : "l"(p) : "memory");
    return v;
}

// Grid-wide barrier on a monotonically increasing arrival counter. `target`
// is the counter value once every block has arrived at this barrier.
__device__ __forceinline__ void prog_grid_barrier(unsigned* counter, unsigned target) {
    __syncthreads();
    if (threadIdx.x == 0) {
        __threadfence();
        atomicAdd(counter, 1u);
        while ((int)(prog_ld_acquire(counter) - target) < 0) {
        }
        __threadfence();
    }
    __syncthreads();
}


// Staging shared by the executors: the read/compute phase of an operation
// fills it, a __syncthreads follows, then the per-PE writers drain it.
union ProgSmem {
    struct {
        unsigned bus[256][4];
        unsigned fl[256];
    } bus;
    struct {
        unsigned long long x[4][16][16];
        unsigned long long y[4][16][16];
        unsigned long long out[4][16][16];
    } mat;
};

// ---------------------------------------------------------------------------
// Executors. Each runs one operation for the L1B owned by block B with `nt`
// threads (`tid` < nt). They are shared by the interpreter (run_program) and
// by the JIT-compiled programs, and end with the block's work issued but not
// synchronized: the caller puts a __syncthreads between operations.
// ---------------------------------------------------------------------------

__device__ __forceinline__ void px_alu(const DevState& st, int B, int tid, int nt,
                                       const AluDesc& a, int upd, ProgSmem& sm) {
    for (int j = tid; j < 256; j += nt) {
        int pe = B * 64 + (j & 63), c = j >> 6;
        alu_compute(a, pe, c, st.lm0, st.lm1, st.grf0, st.grf1, st.mauf, st.aluf, st.t,
                    st.mreadf, st.lbf, st.bar0, st.bar1, sm.bus.bus[j], sm.bus.fl[j]);
    }
    __syncthreads();
    for (int j = tid; j < 64; j += nt) {
        for (int c = 0; c < 4; ++c) {
            unit_store(a, B * 64 + j, c, sm.bus.bus[c * 64 + j], sm.bus.fl[c * 64 + j],
                       st.lm0, st.lm1, st.grf0, st.grf1, st.aluf, st.mask, st.t,
                       st.bar0, st.bar1, upd);
        }
    }
}

// The ALU line when the host proved that the four cycles of a PE neither read
// what another cycle writes nor write the same words: every (PE, cycle)
// thread computes and writes its own result (needs nt == 256).
__device__ __forceinline__ void px_alu_direct(const DevState& st, int B, int tid,
                                              const AluDesc& a, int upd) {
    int pe = B * 64 + (tid & 63), c = tid >> 6;
    unsigned out[4], fl;
    alu_compute(a, pe, c, st.lm0, st.lm1, st.grf0, st.grf1, st.mauf, st.aluf, st.t,
                st.mreadf, st.lbf, st.bar0, st.bar1, out, fl);
    unit_store(a, pe, c, out, fl, st.lm0, st.lm1, st.grf0, st.grf1, st.aluf, st.mask, st.t,
               st.bar0, st.bar1, upd);
}

__device__ __forceinline__ void px_mau(const DevState& st, int B, int tid, int nt,
                                       const MauLineDesc& a, int upd, ProgSmem& sm) {
    for (int j = tid; j < 256; j += nt) {
        int pe = B * 64 + (j & 63), c = j >> 6;
        mau_compute(a, pe, c, st.lm0, st.lm1, st.grf0, st.grf1, st.mauf, st.aluf, st.t,
                    st.mreadf, st.lbf, st.bar0, st.bar1, sm.bus.bus[j], sm.bus.fl[j]);
    }
    __syncthreads();
    for (int j = tid; j < 64; j += nt) {
        for (int c = 0; c < 4; ++c) {
            unit_store(a, B * 64 + j, c, sm.bus.bus[c * 64 + j], sm.bus.fl[c * 64 + j],
                       st.lm0, st.lm1, st.grf0, st.grf1, st.mauf, st.mask, st.t,
                       st.bar0, st.bar1, upd);
        }
    }
}

__device__ __forceinline__ void px_mau_direct(const DevState& st, int B, int tid,
                                              const MauLineDesc& a, int upd) {
    int pe = B * 64 + (tid & 63), c = tid >> 6;
    unsigned out[4], fl;
    mau_compute(a, pe, c, st.lm0, st.lm1, st.grf0, st.grf1, st.mauf, st.aluf, st.t,
                st.mreadf, st.lbf, st.bar0, st.bar1, out, fl);
    unit_store(a, pe, c, out, fl, st.lm0, st.lm1, st.grf0, st.grf1, st.mauf, st.mask, st.t,
               st.bar0, st.bar1, upd);
}

__device__ __forceinline__ void px_bfn(const DevState& st, int B, int tid, int nt,
                                       const AluDesc& a, int upd, ProgSmem& sm) {
    for (int j = tid; j < 64; j += nt) {
        int mabl = j & 15, c = j >> 4;
        unsigned out[4][4];
        bfn_compute(a, B * 16 + mabl, c, st.lm0, st.lm1, st.grf0, st.grf1, st.mauf, st.aluf,
                    st.t, st.mreadf, st.lbf, st.bar0, st.bar1, out);
        for (int p = 0; p < 4; ++p) {
            for (int w = 0; w < 4; ++w) sm.bus.bus[c * 64 + mabl * 4 + p][w] = out[p][w];
        }
    }
    __syncthreads();
    for (int j = tid; j < 64; j += nt) {
        for (int c = 0; c < 4; ++c) {
            unit_store(a, B * 64 + j, c, sm.bus.bus[c * 64 + j], 0u, st.lm0, st.lm1, st.grf0,
                       st.grf1, st.aluf, st.mask, st.t, st.bar0, st.bar1, upd);
        }
    }
}

__device__ __forceinline__ void px_matmau(const DevState& st, int B, int tid, int nt,
                                          const MatMauLineDesc& a, int upd, ProgSmem& sm) {
    const int rows = (a.prec == 0) ? 4 : (a.prec == 3) ? 16 : 8;
    const int nx = (a.prec == 0) ? 1 : (a.prec == 3) ? 4 : (a.prec == 2) ? 2 : 1;
    const int ny = (a.prec == 0) ? 1 : (a.prec == 3) ? 4 : 2;
    // x/y elements of every PE and cycle, grouped [c][mab][p * n + k].
    for (int j = tid; j < 256; j += nt) {
        int pl = j & 63, c = j >> 6;
        unsigned long long xo[4], yo[4];
        mat_mau_read(a, B * 64 + pl, c, st.lm0, st.lm1, st.grf0, st.grf1, st.mauf, st.aluf,
                     st.t, st.mreadf, st.lbf, st.bar0, st.bar1, xo, yo);
        int mabl = pl >> 2, p = pl & 3;
        for (int k = 0; k < nx; ++k) sm.mat.x[c][mabl][p * nx + k] = xo[k];
        if (a.kind == 0) {
            for (int k = 0; k < ny; ++k) sm.mat.y[c][mabl][p * ny + k] = yo[k];
        }
    }
    __syncthreads();
    for (int j = tid; j < 64 * rows; j += nt) {
        int i = j % rows, mc = j / rows, mabl = mc & 15, c = mc >> 4;
        sm.mat.out[c][mabl][i] =
            mat_mau_row(a, B * 16 + mabl, i, sm.mat.x[c][mabl], sm.mat.y[c][mabl], st.mats);
    }
    __syncthreads();
    for (int j = tid; j < 64; j += nt) {
        for (int c = 0; c < 4; ++c) {
            mat_mau_store(a, B * 64 + j, c, sm.mat.out[c][j >> 2], st.lm0, st.lm1, st.grf0,
                          st.grf1, st.mauf, st.mask, st.t, st.bar0, st.bar1, upd);
        }
    }
}

__device__ __forceinline__ void px_l1r(const DevState& st, int B, int tid, int nt,
                                       const L1ReadArgs& a) {
    for (int j = tid; j < 64; j += nt) {
        l1_read_line_body(
            B * 64 + j, st.lm0, st.lm1, st.grf0, st.grf1, st.t, st.l1bm, st.lbi, st.mask,
            st.lbf, st.bar0, st.bar1, a.op, a.has_addr, a.addr, a.mabdiff, a.wl, a.ndst,
            a.dm[0], a.db[0][0], a.db[0][1], a.db[0][2], a.db[0][3], a.dw[0],
            a.mk[0], a.mke[0], a.mkp[0], a.mkl[0], a.dt[0], a.dma[0],
            a.dm[1], a.db[1][0], a.db[1][1], a.db[1][2], a.db[1][3], a.dw[1],
            a.mk[1], a.mke[1], a.mkp[1], a.mkl[1], a.dt[1], a.dma[1],
            a.dm[2], a.db[2][0], a.db[2][1], a.db[2][2], a.db[2][3], a.dw[2],
            a.mk[2], a.mke[2], a.mkp[2], a.mkl[2], a.dt[2], a.dma[2],
            a.dm[3], a.db[3][0], a.db[3][1], a.db[3][2], a.db[3][3], a.dw[3],
            a.mk[3], a.mke[3], a.mkp[3], a.mkl[3], a.dt[3], a.dma[3],
            a.fk, a.fe, a.fp, a.fll);
    }
}

__device__ __forceinline__ void px_l1w(const DevState& st, int B, int tid, int nt,
                                       const L1WriteArgs& a, int upd) {
    // Items (sub PE, cycle, part): part is the MAB of a Gather, the MAB group
    // of an M4write and the reduction group of a Reduce4.
    const int parts = (a.op == 1) ? 16 : (a.op == 2 || a.op == 4) ? 4 : 1;
    for (int j = tid; j < 16 * parts; j += nt) {
        int sub = j & 3, c = (j >> 2) & 3, part = j >> 4;
        l1_write_line_body(
            B * 4 + sub, c, parts > 1 ? part : -1, st.lm0, st.lm1, st.grf0, st.grf1, st.t,
            st.mauf, st.aluf, st.mreadf, st.lbf, st.mask, st.l1bm, st.lbi, st.bar0, st.bar1, upd,
            a.op, a.mab_sel, a.mabdiff, a.has_addr, a.addr, a.dwl, a.smem, a.s[0], a.s[1],
            a.s[2], a.s[3], a.swl, a.st, a.sma, a.two_src, a.bits, a.rrn, a.round_it, a.ext,
            a.fk, a.fe, a.fp, a.fll);
    }
}

__device__ __forceinline__ void px_l2(const DevState& st, int B, int tid, int nt,
                                      const L2Args& a) {
    const int l2 = B >> 3;
    const int b = B & 7;
    if (a.op == 0 || a.op == 4) {
        // Distrib (to L1BM B) and Gather (from L1BM B).
        for (int j = tid; j < 32; j += nt) {
            int c = j >> 3, k = j & 7;
            l2_line_body(((l2 * 4 + c) * 8 + b) * 8 + k, st.l1bm, st.l2bm, st.darbuf, st.dar,
                         st.dar_addr, a.op, a.a0, a.a1, a.l1b, a.mask, a.l2b);
        }
    } else if (a.op == 1 || a.op == 3) {
        for (int j = tid; j < 64; j += nt) {
            int c = j >> 4, k = j & 15;
            l2_line_body(((l2 * 4 + c) * 8 + b) * 16 + k, st.l1bm, st.l2bm, st.darbuf, st.dar,
                         st.dar_addr, a.op, a.a0, a.a1, a.l1b, a.mask, a.l2b);
        }
    } else if (a.op == 2) {
        // FromL1b: done by the block of the source L1B.
        if (b == a.l1b) {
            for (int j = tid; j < 64; j += nt) {
                l2_line_body(l2 * 64 + j, st.l1bm, st.l2bm, st.darbuf, st.dar, st.dar_addr,
                             a.op, a.a0, a.a1, a.l1b, a.mask, a.l2b);
            }
        }
    } else if (B == 0) {
        int count = (a.op == 5) ? 1024 : 1;
        for (int j = tid; j < count; j += nt) {
            l2_line_body(j, st.l1bm, st.l2bm, st.darbuf, st.dar, st.dar_addr, a.op, a.a0, a.a1,
                         a.l1b, a.mask, a.l2b);
        }
    }
}

__device__ __forceinline__ void px_l2red(const DevState& st, int B, int tid, int nt,
                                         const L2RedArgs& a) {
    const int l2 = B >> 3;
    const int b = B & 7;
    if (a.op == 0) {
        for (int j = tid; j < 8; j += nt) {
            l2_reduce_line_body(l2 * 64 + b * 8 + j, st.l1bm, st.l2bm, a.op, a.a0, a.a1, a.mask,
                                a.immode, a.bits, a.kind);
        }
    } else if (a.op == 1) {
        for (int j = tid; j < 32; j += nt) {
            l2_reduce_line_body(l2 * 256 + b * 32 + j, st.l1bm, st.l2bm, a.op, a.a0, a.a1,
                                a.mask, a.immode, a.bits, a.kind);
        }
    } else {
        for (int j = tid; j < 64; j += nt) {
            int c = j >> 4, k = j & 15;
            l2_reduce_line_body(((l2 * 4 + c) * 8 + b) * 16 + k, st.l1bm, st.l2bm, a.op, a.a0,
                                a.a1, a.mask, a.immode, a.bits, a.kind);
        }
    }
}

__device__ __forceinline__ void px_matw(const DevState& st, int B, int tid, int nt,
                                        const MatWriteLineDesc& a) {
    for (int j = tid; j < 64; j += nt) {
        mat_write_line_body(B * 64 + j, st.lm0, st.lm1, st.grf0, st.grf1, st.mauf, st.aluf,
                            st.mats, st.t, st.mreadf, st.lbf, st.bar0, st.bar1, a);
    }
}

__device__ __forceinline__ void px_matr(const DevState& st, int B, int tid, int nt,
                                        const MatReadLineDesc& a, int upd) {
    for (int j = tid; j < 64; j += nt) {
        mat_read_line_body(B * 64 + j, st.lm0, st.lm1, st.grf0, st.grf1, st.mreadf, st.lbf,
                           st.mask, st.t, st.mats, st.bar0, st.bar1, upd, a);
    }
}

__device__ __forceinline__ void px_mv(const DevState& st, int B, int tid, int nt,
                                      const MvArgs& a) {
    const unsigned long long stride = (unsigned long long)gridDim.x * nt;
    for (unsigned long long j = (unsigned long long)B * nt + tid; j < a.total; j += stride) {
        mv_line_body(j, st.pdm, st.dram, st.l2bm, st.scratch, st.dram_longs, a.mode, a.phase,
                     a.parallel, a.src_mem, a.src_group, a.src_l2b, a.src_addr, a.dst_mem,
                     a.dst_group, a.dst_l2b, a.dst_addr, a.size, a.rrn_op, a.rrn_bits, st.dar,
                     st.mv_errors, a.src_indirect, a.dst_indirect, a.nd);
    }
}

__device__ __forceinline__ void px_clear_mreadf(const DevState& st, int B, int tid, int nt) {
    for (int j = tid; j < 64 * 16; j += nt) {
        st.mreadf[PR16(B * 64 + (j & 63), j >> 6)] = 0;
    }
}

#ifndef MNCORE_JIT
extern "C" __global__ void __launch_bounds__(128) run_program(
    DevState st, const ProgIns* ins, int n, const unsigned char* blob, unsigned* sync,
    unsigned long long* prof) {
    const int B = blockIdx.x;
    const int tid = threadIdx.x;
    const int nt = blockDim.x;
    const unsigned nb = gridDim.x;
    __shared__ ProgSmem sm;
    __shared__ unsigned long long sdesc[PROG_DESC_LONGS];
    // sync[0] is the arrival counter and sync[1] its value when this launch
    // started; block 0 advances sync[1] after the final barrier.
    const unsigned base = sync[1];
    unsigned barriers = 0;
    for (int i = 0; i < n; ++i) {
        const ProgIns in = ins[i];
        if (prof != 0 && tid == 0) prof[(size_t)B * (n + 1) + i] = clock64();
        if (in.flags & PF_BARRIER) {
            ++barriers;
            prog_grid_barrier(&sync[0], base + barriers * nb);
        }
        // Stage the descriptor in shared memory: every thread reads it many times.
        {
            const unsigned long long* src = (const unsigned long long*)(blob + in.off);
            for (unsigned j = tid; j < in.aux; j += nt) sdesc[j] = src[j];
        }
        __syncthreads();
        const unsigned char* d = (const unsigned char*)sdesc;
        const int upd = (in.flags & PF_UPDATE) ? 1 : 0;
        switch (in.kind) {
        case PK_ALU: px_alu(st, B, tid, nt, *(const AluDesc*)d, upd, sm); break;
        case PK_BFN: px_bfn(st, B, tid, nt, *(const AluDesc*)d, upd, sm); break;
        case PK_MAU: px_mau(st, B, tid, nt, *(const MauLineDesc*)d, upd, sm); break;
        case PK_L1R: px_l1r(st, B, tid, nt, *(const L1ReadArgs*)d); break;
        case PK_L1W: px_l1w(st, B, tid, nt, *(const L1WriteArgs*)d, upd); break;
        case PK_L2: px_l2(st, B, tid, nt, *(const L2Args*)d); break;
        case PK_L2RED: px_l2red(st, B, tid, nt, *(const L2RedArgs*)d); break;
        case PK_MATW: px_matw(st, B, tid, nt, *(const MatWriteLineDesc*)d); break;
        case PK_MATR: px_matr(st, B, tid, nt, *(const MatReadLineDesc*)d, upd); break;
        case PK_MATMAU: px_matmau(st, B, tid, nt, *(const MatMauLineDesc*)d, upd, sm); break;
        case PK_MV: px_mv(st, B, tid, nt, *(const MvArgs*)d); break;
        case PK_CLEAR_MREADF: px_clear_mreadf(st, B, tid, nt); break;
        }
        __syncthreads();
    }
    if (prof != 0 && tid == 0) prof[(size_t)B * (n + 1) + n] = clock64();
    // A last barrier so that every block has left the program before block 0
    // publishes the counter base of the next launch.
    ++barriers;
    prog_grid_barrier(&sync[0], base + barriers * nb);
    if (B == 0 && tid == 0) {
        sync[1] = base + barriers * nb;
    }
}
#endif
