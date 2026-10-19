// MV transfers (SDM 3.5) for the GPU backend.
//
// This file is concatenated after vfma_kernel.cu by Gpu::new, so it reuses
// `Fmt`, `round_pack`, `inf_bits` and the other f32 helpers defined there.
//
// Device state:
//   pdm   [4][PDM_LONGS]                     long words, group-major
//   dram  [4][dram_longs]                    long words, group-major (truncated DRAM)
//   l2bm  [8][L2BM_LONGS]                    group g has L2B 2*g and 2*g+1
//
// One launch executes one MV statement. `mode` selects the data flow, and
// `phase` distinguishes a normal transfer (2) from the two passes of an
// overlapping PDM/DRAM/L2BM-to-same-level copy (0 = source to scratch,
// 1 = scratch to destination). All reads of a statement happen before its
// writes on the CPU, hence the snapshot for overlapping `mvp` lines.

#define MV_PDM_LONGS 524288ULL
#define MV_L2BM_LONGS 32768ULL

__device__ __forceinline__ unsigned long long mv_read(
    int mem, int group, int l2b, unsigned long long addr,
    const unsigned long long* pdm, const unsigned long long* dram,
    const unsigned long long* l2bm, unsigned long long dram_longs) {
    if (mem == 0) {
        return pdm[(unsigned long long)group * MV_PDM_LONGS + addr % MV_PDM_LONGS];
    }
    if (mem == 1) {
        return dram[(unsigned long long)group * dram_longs + addr];
    }
    return l2bm[((unsigned long long)group * 2 + l2b) * MV_L2BM_LONGS +
                addr % MV_L2BM_LONGS];
}

__device__ __forceinline__ void mv_write(
    int mem, int group, int l2b, unsigned long long addr, unsigned long long value,
    unsigned long long* pdm, unsigned long long* dram,
    unsigned long long* l2bm, unsigned long long dram_longs) {
    if (mem == 0) {
        pdm[(unsigned long long)group * MV_PDM_LONGS + addr % MV_PDM_LONGS] = value;
    } else if (mem == 1) {
        dram[(unsigned long long)group * dram_longs + addr] = value;
    } else {
        l2bm[((unsigned long long)group * 2 + l2b) * MV_L2BM_LONGS +
             addr % MV_L2BM_LONGS] = value;
    }
}

__device__ __forceinline__ Fmt mv_fmt(int bits) {
    if (bits == 16) return {6, 9, -1};
    if (bits == 32) return {8, 23, -1};
    return {11, 52, -1};
}

__device__ __forceinline__ unsigned __int128 mv_round_shift(
    unsigned __int128 v, unsigned shift) {
    if (shift == 0) return v;
    if (shift >= 128) return 0;
    unsigned __int128 k = v >> shift;
    unsigned __int128 rem = v & ((((unsigned __int128)1) << shift) - 1);
    unsigned __int128 half = ((unsigned __int128)1) << (shift - 1);
    return k + ((rem > half || (rem == half && (k & 1))) ? 1 : 0);
}

// rrn.rs `fadd`: align every non-zero value to the largest exponent with
// round-to-nearest-even, add exactly, and round once to the output format.
__device__ __forceinline__ unsigned long long mv_rrn_fadd(
    Fmt f, const unsigned long long* vals, int n, Fmt out) {
    int mbits = f.man_bits;
    unsigned long long emask = exp_max(f);
    unsigned long long max_e = 0;
    for (int i = 0; i < n; ++i) {
        unsigned long long e = (vals[i] >> mbits) & emask;
        if (e > max_e) max_e = e;
    }
    if (max_e == 0) return 0;
    if (max_e == emask) {
        bool neg = true;
        for (int i = 0; i < n; ++i) {
            unsigned long long e = (vals[i] >> mbits) & emask;
            if (e == emask && (((vals[i] >> (width(f) - 1)) & 1) == 0)) neg = false;
        }
        return inf_bits(out, neg);
    }
    __int128 sum = 0;
    for (int i = 0; i < n; ++i) {
        unsigned long long v = vals[i];
        unsigned long long e = (v >> mbits) & emask;
        if (e == 0) continue;
        unsigned __int128 sig =
            ((((unsigned __int128)1 << mbits) | (v & (((unsigned long long)1 << mbits) - 1))) << 3);
        unsigned d = (unsigned)(max_e - e);
        unsigned __int128 aligned = mv_round_shift(sig, d);
        __int128 s = (__int128)aligned;
        bool neg = ((v >> (width(f) - 1)) & 1) == 1;
        sum += neg ? -s : s;
    }
    if (sum == 0) return 0;
    int e = (int)max_e - bias(f) - mbits - 3;
    bool neg = sum < 0;
    unsigned __int128 mag = neg ? (unsigned __int128)(-sum) : (unsigned __int128)sum;
    return round_pack(out, neg, mag, e);
}

// One RRN stage over n lane values. `bits` is the element width.
__device__ __forceinline__ unsigned long long mv_rrn_stage(
    int op, int bits, const unsigned long long* vals, int n) {
    unsigned long long m = (bits == 64) ? ~0ULL : (((unsigned long long)1 << bits) - 1);
    Fmt f = mv_fmt(bits);
    switch (op) {
        case 0:
            return mv_rrn_fadd(f, vals, n, f) & m;
        case 1:
        case 2: {
            unsigned long long best = vals[0];
            __int128 best_key = 0;
            for (int i = 0; i < n; ++i) {
                unsigned long long v = vals[i];
                bool neg = ((v >> (bits - 1)) & 1) == 1;
                __int128 mag = (__int128)(v & (m >> 1));
                __int128 key = neg ? -mag - 1 : mag;
                if (i == 0 || (op == 1 ? key > best_key : key < best_key)) {
                    best_key = key;
                    best = v;
                }
            }
            return best & m;
        }
        case 3: {
            unsigned long long sum = 0;
            for (int i = 0; i < n; ++i) sum += vals[i];
            return sum & m;
        }
        case 4: {
            unsigned long long acc = m;
            for (int i = 0; i < n; ++i) acc &= vals[i];
            return acc;
        }
        case 5: {
            bool all = true;
            for (int i = 0; i < n; ++i) all = all && vals[i] != 0;
            return all ? 1 : 0;
        }
        case 6: {
            unsigned long long acc = 0;
            for (int i = 0; i < n; ++i) acc |= vals[i];
            return acc & m;
        }
        default: {
            bool any = false;
            for (int i = 0; i < n; ++i) any = any || vals[i] != 0;
            return any ? 1 : 0;
        }
    }
}

// A single reduction stage, split into lanes and packed back into long words.
__device__ __forceinline__ unsigned long long mv_reduce_n(
    int op, int bits, const unsigned long long* vals, int n) {
    int lanes = 64 / bits;
    unsigned long long m = (bits == 64) ? ~0ULL : (((unsigned long long)1 << bits) - 1);
    unsigned long long out = 0;
    for (int lane = 0; lane < lanes; ++lane) {
        int sh = 64 - bits * (lane + 1);
        unsigned long long lv[8];
        for (int i = 0; i < n; ++i) lv[i] = (vals[i] >> sh) & m;
        unsigned long long r = mv_rrn_stage(op, bits, lv, n);
        out |= (r & m) << sh;
    }
    return out;
}

// mvr<op>: reduce the two L2BMs within each group, then the four groups.
// The CPU rounds each stage, so the two stages must stay separate.
__device__ __forceinline__ unsigned long long mv_reduce8(
    int op, int bits, const unsigned long long* vals) {
    int lanes = 64 / bits;
    unsigned long long m = (bits == 64) ? ~0ULL : (((unsigned long long)1 << bits) - 1);
    unsigned long long out = 0;
    for (int lane = 0; lane < lanes; ++lane) {
        int sh = 64 - bits * (lane + 1);
        unsigned long long lv[8];
        for (int i = 0; i < 8; ++i) lv[i] = (vals[i] >> sh) & m;
        unsigned long long stage[4];
        for (int g = 0; g < 4; ++g) {
            unsigned long long pair[2] = {lv[2 * g], lv[2 * g + 1]};
            stage[g] = mv_rrn_stage(op, bits, pair, 2);
        }
        unsigned long long r = mv_rrn_stage(op, bits, stage, 4);
        out |= (r & m) << sh;
    }
    return out;
}

// DRAM address of one 16-long-word indirect chunk (SDM 3.5.6, measured
// against the official emulator). The address word covers 16 long words, and
// chunk i of a transfer uses DAR[(M + i/N) % 1024] + i % N; without `nd` each
// chunk advances the DAR entry. `nd` is the same for both DRAM operands.
#define MV_DRAM_LONGS 536870912ULL

__device__ __forceinline__ unsigned long long mv_dram_addr(
    const unsigned* dar, int group, unsigned long long m, int indirect,
    unsigned long long nd, unsigned long long chunk, unsigned long long k) {
    if (!indirect) return m + 16 * chunk + k;
    unsigned long long entry = nd ? ((m + chunk / nd) % 1024ULL)
                                  : ((m + chunk) % 1024ULL);
    unsigned long long off = nd ? (chunk % nd) : 0ULL;
    unsigned long long word =
        ((unsigned long long)dar[group * 1024 + entry] + off) & 0xffffffffULL;
    return (word * 16ULL + k) % MV_DRAM_LONGS;
}

__device__ __forceinline__ unsigned long long mv_dram_read(
    const unsigned* dar, unsigned* mv_errors, int group, unsigned long long m,
    int indirect, unsigned long long nd, unsigned long long chunk,
    unsigned long long k, const unsigned long long* dram,
    unsigned long long dram_longs) {
    unsigned long long a =
        mv_dram_addr(dar, group, m, indirect, nd, chunk, k);
    if (a >= dram_longs) {
        atomicAdd(mv_errors, 1u);
        return 0;
    }
    return dram[(unsigned long long)group * dram_longs + a];
}

__device__ __forceinline__ void mv_dram_write(
    const unsigned* dar, unsigned* mv_errors, int group, unsigned long long m,
    int indirect, unsigned long long nd, unsigned long long chunk,
    unsigned long long k, unsigned long long value,
    unsigned long long* dram, unsigned long long dram_longs) {
    unsigned long long a =
        mv_dram_addr(dar, group, m, indirect, nd, chunk, k);
    if (a >= dram_longs) {
        atomicAdd(mv_errors, 1u);
        return;
    }
    dram[(unsigned long long)group * dram_longs + a] = value;
}

// mode 0  mvp (parallel or single group, phase 2, or snapshot phases 0/1)
// mode 1  mvb from PDM (broadcast to both L2BMs of every group)
// mode 2  mvb from DRAM (gather 16 words per group, broadcast to L2BMs)
// mode 3  mvb2 (DRAM to both L2BMs of every group)
// mode 4  mvd PDM -> L2BM
// mode 5  mvd L2BM -> PDM
// mode 6  mvd PDM -> DRAM
// mode 7  mvd DRAM -> PDM
// mode 8  mvb4 DRAM -> L2BM
// mode 9  mvr<op> L2BM -> PDM
// mode 10 mvr<op> L2BM -> DRAM
// mode 11 mvr2<op> L2BM -> PDM/DRAM
// mode 12 mvr4<op> L2BM -> DRAM
// mode 13 mvnop
extern "C" __global__ void mv_line(
    unsigned long long* pdm, unsigned long long* dram, unsigned long long* l2bm,
    unsigned long long* scratch, unsigned long long dram_longs,
    int mode, int phase, int parallel,
    int src_mem, int src_group, int src_l2b, unsigned long long src_addr,
    int dst_mem, int dst_group, int dst_l2b, unsigned long long dst_addr,
    unsigned long long size, int rrn_op, int rrn_bits,
    const unsigned* dar, unsigned* mv_errors, int src_indirect,
    int dst_indirect, unsigned long long nd) {
    unsigned long long idx =
        (unsigned long long)blockIdx.x * blockDim.x + threadIdx.x;

    if (mode == 0) {
        unsigned long long total = size * (parallel ? 4ULL : 1ULL);
        if (idx >= total) return;
        int gs, gd;
        unsigned long long k;
        if (parallel) {
            gs = gd = (int)(idx / size);
            k = idx % size;
        } else {
            gs = src_group;
            gd = dst_group;
            k = idx;
        }
        unsigned long long chunk = k / 16;
        unsigned long long kk = k % 16;
        if (phase == 0) {
            scratch[idx] = (src_mem == 1)
                ? mv_dram_read(dar, mv_errors, gs, src_addr, src_indirect, nd,
                               chunk, kk, dram, dram_longs)
                : mv_read(src_mem, gs, src_l2b, src_addr + k,
                          pdm, dram, l2bm, dram_longs);
            return;
        }
        unsigned long long value = (phase == 1)
            ? scratch[idx]
            : (src_mem == 1
                ? mv_dram_read(dar, mv_errors, gs, src_addr, src_indirect, nd,
                               chunk, kk, dram, dram_longs)
                : mv_read(src_mem, gs, src_l2b, src_addr + k,
                          pdm, dram, l2bm, dram_longs));
        if (dst_mem == 1) {
            mv_dram_write(dar, mv_errors, gd, dst_addr, dst_indirect, nd,
                          chunk, kk, value, dram, dram_longs);
        } else {
            mv_write(dst_mem, gd, dst_l2b, dst_addr + k, value,
                     pdm, dram, l2bm, dram_longs);
        }
        return;
    }

    if (mode == 1) {
        if (idx >= size) return;
        unsigned long long value =
            mv_read(0, src_group, 0, src_addr + idx, pdm, dram, l2bm, dram_longs);
        for (int g = 0; g < 4; ++g) {
            for (int c = 0; c < 2; ++c) {
                mv_write(2, g, c, dst_addr + idx, value, pdm, dram, l2bm, dram_longs);
            }
        }
        return;
    }

    if (mode == 2) {
        if (idx >= size) return;
        int gd = (int)((idx % 64) / 16);
        unsigned long long chunk = idx / 16;
        unsigned long long kk = idx % 16;
        unsigned long long value =
            mv_dram_read(dar, mv_errors, gd, src_addr, src_indirect, nd,
                         chunk, kk, dram, dram_longs);
        for (int g = 0; g < 4; ++g) {
            for (int c = 0; c < 2; ++c) {
                mv_write(2, g, c, dst_addr + idx, value, pdm, dram, l2bm, dram_longs);
            }
        }
        return;
    }

    if (mode == 3) {
        if (idx >= 4 * size) return;
        int g = (int)(idx / size);
        unsigned long long k = idx % size;
        unsigned long long value =
            (src_mem == 1)
                ? mv_dram_read(dar, mv_errors, g, src_addr, src_indirect, nd,
                               k / 16, k % 16, dram, dram_longs)
                : mv_read(src_mem, g, 0, src_addr + k, pdm, dram, l2bm, dram_longs);
        for (int c = 0; c < 2; ++c) {
            mv_write(2, g, c, dst_addr + k, value, pdm, dram, l2bm, dram_longs);
        }
        return;
    }

    if (mode == 4 || mode == 5) {
        if (idx >= 8 * size) return;
        unsigned long long i = idx / 512;
        unsigned long long rem = idx % 512;
        int j = (int)(rem / 128);
        int g = (int)((rem % 128) / 32);
        int c = (int)((rem % 32) / 16);
        int k = (int)(rem % 16);
        unsigned long long l2_off = 64 * i + 16 * j + k;
        if (mode == 4) {
            unsigned long long value = mv_read(0, src_group, 0, src_addr + idx,
                                               pdm, dram, l2bm, dram_longs);
            mv_write(2, g, c, dst_addr + l2_off, value, pdm, dram, l2bm, dram_longs);
        } else {
            unsigned long long value = mv_read(2, g, c, src_addr + l2_off,
                                               pdm, dram, l2bm, dram_longs);
            mv_write(0, dst_group, 0, dst_addr + idx, value,
                     pdm, dram, l2bm, dram_longs);
        }
        return;
    }

    if (mode == 6 || mode == 7) {
        if (idx >= size) return;
        unsigned long long chunk = idx / 16;
        unsigned long long k = idx % 16;
        if (mode == 6) {
            unsigned long long value = mv_read(0, src_group, 0, src_addr + idx,
                                               pdm, dram, l2bm, dram_longs);
            mv_dram_write(dar, mv_errors, (int)((idx % 64) / 16), dst_addr,
                          dst_indirect, nd, chunk, k, value, dram, dram_longs);
        } else {
            unsigned long long value =
                mv_dram_read(dar, mv_errors, (int)((idx % 64) / 16), src_addr,
                             src_indirect, nd, chunk, k, dram, dram_longs);
            mv_write(0, dst_group, 0, dst_addr + idx, value,
                     pdm, dram, l2bm, dram_longs);
        }
        return;
    }

    if (mode == 8) {
        if (idx >= 2 * size) return;
        unsigned long long i = idx / 128;
        int c = (int)((idx % 128) / 64);
        int gs = (int)((idx % 64) / 16);
        int k = (int)(idx % 16);
        unsigned long long dst_off = 64 * i + 16 * gs + k;
        unsigned long long value =
            mv_dram_read(dar, mv_errors, gs, src_addr, src_indirect, nd,
                         2 * i + (unsigned long long)c, (unsigned long long)k,
                         dram, dram_longs);
        for (int g = 0; g < 4; ++g) {
            mv_write(2, g, c, dst_addr + dst_off, value, pdm, dram, l2bm, dram_longs);
        }
        return;
    }

    if (mode == 9 || mode == 10) {
        if (idx >= size) return;
        unsigned long long vals[8];
        for (int g = 0; g < 4; ++g) {
            for (int c = 0; c < 2; ++c) {
                vals[2 * g + c] = mv_read(2, g, c, src_addr + idx,
                                          pdm, dram, l2bm, dram_longs);
            }
        }
        unsigned long long value = mv_reduce8(rrn_op, rrn_bits, vals);
        if (mode == 9) {
            mv_write(0, dst_group, 0, dst_addr + idx, value, pdm, dram, l2bm, dram_longs);
        } else {
            mv_dram_write(dar, mv_errors, (int)((idx % 64) / 16), dst_addr,
                          dst_indirect, nd, idx / 16, idx % 16, value,
                          dram, dram_longs);
        }
        return;
    }

    if (mode == 11) {
        unsigned long long total = size * (dst_group == 255 ? 4ULL : 1ULL);
        if (idx >= total) return;
        int g = dst_group == 255 ? (int)(idx / size) : dst_group;
        unsigned long long k = idx % size;
        unsigned long long vals[2] = {
            mv_read(2, g, 0, src_addr + k, pdm, dram, l2bm, dram_longs),
            mv_read(2, g, 1, src_addr + k, pdm, dram, l2bm, dram_longs),
        };
        unsigned long long value = mv_reduce_n(rrn_op, rrn_bits, vals, 2);
        if (dst_mem == 1) {
            mv_dram_write(dar, mv_errors, g, dst_addr, dst_indirect, nd,
                          k / 16, k % 16, value, dram, dram_longs);
        } else {
            mv_write(dst_mem, g, 0, dst_addr + k, value, pdm, dram, l2bm, dram_longs);
        }
        return;
    }

    if (mode == 12) {
        if (idx >= 2 * size) return;
        unsigned long long i = idx / 128;
        int c = (int)((idx % 128) / 64);
        int g = (int)((idx % 64) / 16);
        int k = (int)(idx % 16);
        unsigned long long off = 64 * i + 16 * g + k;
        unsigned long long vals[4];
        for (int gs = 0; gs < 4; ++gs) {
            vals[gs] = mv_read(2, gs, c, src_addr + off, pdm, dram, l2bm, dram_longs);
        }
        unsigned long long value = mv_reduce_n(rrn_op, rrn_bits, vals, 4);
        mv_dram_write(dar, mv_errors, g, dst_addr, dst_indirect, nd,
                      2 * i + (unsigned long long)c, (unsigned long long)k,
                      value, dram, dram_longs);
        return;
    }
}
