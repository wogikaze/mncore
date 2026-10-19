
struct Fmt {
    int exp_bits;
    int man_bits;
    int mul_full_bits; // -1: exact product
};

struct Val {
    int kind; // 0 zero, 1 inf, 2 finite
    bool neg;
    unsigned __int128 sig;
    int exp;
};

__device__ __forceinline__ int width(Fmt f) {
    return 1 + f.exp_bits + f.man_bits;
}

__device__ __forceinline__ long long bias(Fmt f) {
    return (1LL << (f.exp_bits - 1)) - 1;
}

__device__ __forceinline__ unsigned long long exp_max(Fmt f) {
    return (1ULL << f.exp_bits) - 1;
}

__device__ __forceinline__ unsigned long long man_mask(Fmt f) {
    return (1ULL << f.man_bits) - 1;
}

__device__ __forceinline__ unsigned long long inf_bits(Fmt f, bool neg) {
    return ((unsigned long long)neg << (width(f) - 1)) |
           (exp_max(f) << f.man_bits);
}

__device__ __forceinline__ int lz128(unsigned __int128 x) {
    unsigned long long hi = (unsigned long long)(x >> 64);
    if (hi) return __clzll(hi);
    unsigned long long lo = (unsigned long long)x;
    return lo ? 64 + __clzll(lo) : 128;
}

__device__ __forceinline__ Val decode(Fmt f, unsigned long long bits) {
    bool neg = (bits >> (width(f) - 1)) & 1;
    unsigned long long e = (bits >> f.man_bits) & exp_max(f);
    unsigned long long m = bits & man_mask(f);
    if (e == 0) return {0, neg, 0, 0};
    if (e == exp_max(f)) return {1, neg, 0, 0};
    unsigned __int128 sig = ((unsigned __int128)1 << f.man_bits) | (unsigned __int128)m;
    return {2, neg, sig, (int)e - (int)bias(f) - f.man_bits};
}

__device__ __forceinline__ unsigned long long round_pack(
    Fmt f, bool neg, unsigned __int128 sig, int exp) {
    if (sig == 0) return 0;
    int m = f.man_bits;
    int p = 127 - lz128(sig);
    unsigned __int128 keep;
    if (p > m) {
        unsigned shift = (unsigned)(p - m);
        unsigned __int128 k = sig >> shift;
        unsigned __int128 rem = sig & ((((unsigned __int128)1) << shift) - 1);
        unsigned __int128 half = ((unsigned __int128)1) << (shift - 1);
        bool up = rem > half || (rem == half && (k & 1));
        keep = k + (up ? 1 : 0);
    } else {
        keep = sig << (unsigned)(m - p);
    }
    if ((keep >> (m + 1)) != 0) {
        keep >>= 1;
        p += 1;
    }
    long long biased = (long long)exp + p + bias(f);
    if (biased >= (long long)exp_max(f)) return inf_bits(f, neg);
    if (biased <= 0) return 0;
    return ((unsigned long long)neg << (width(f) - 1)) |
           ((unsigned long long)biased << f.man_bits) |
           ((unsigned long long)keep & man_mask(f));
}

__device__ __forceinline__ Val mul_exact(Fmt f, Val a, Val b) {
    bool neg = a.neg ^ b.neg;
    if (a.kind == 0 || b.kind == 0) return {0, neg, 0, 0};
    if (a.kind == 1 || b.kind == 1) return {1, neg, 0, 0};
    unsigned __int128 prod = a.sig * b.sig;
    if (f.mul_full_bits >= 0) {
        int low = f.man_bits - f.mul_full_bits;
        unsigned __int128 low_mask = (((unsigned __int128)1) << low) - 1;
        unsigned __int128 dropped = (a.sig & low_mask) * (b.sig & low_mask);
        if (dropped != 0) {
            prod = prod - dropped + (((unsigned __int128)1) << (2 * low - 2));
        }
    }
    return {2, neg, prod, a.exp + b.exp};
}

__device__ __forceinline__ void norm128(
    unsigned __int128 sig, int exp, unsigned __int128 &out_sig, int &out_exp) {
    int p = 127 - lz128(sig);
    if (p <= 125) {
        int shift = 125 - p;
        out_sig = sig << shift;
        out_exp = exp - shift;
    } else {
        int shift = p - 125;
        bool sticky = (sig & ((((unsigned __int128)1) << shift) - 1)) != 0;
        out_sig = (sig >> shift) | (sticky ? 1 : 0);
        out_exp = exp + shift;
    }
}

__device__ __forceinline__ Val add_exact(Val a, Val b) {
    if (a.kind == 1 && b.kind == 1) return {1, a.neg && b.neg, 0, 0};
    if (a.kind == 1) return a;
    if (b.kind == 1) return b;
    if (a.kind == 0 && b.kind == 0) return {0, a.neg && b.neg, 0, 0};
    if (a.kind == 0) return b;
    if (b.kind == 0) return a;
    unsigned __int128 sa, sb;
    int ea, eb;
    norm128(a.sig, a.exp, sa, ea);
    norm128(b.sig, b.exp, sb, eb);
    bool nh, nl;
    unsigned __int128 sh, sl;
    int eh, el;
    if (ea >= eb) {
        nh = a.neg; sh = sa; eh = ea;
        nl = b.neg; sl = sb; el = eb;
    } else {
        nh = b.neg; sh = sb; eh = eb;
        nl = a.neg; sl = sa; el = ea;
    }
    unsigned d = (unsigned)(eh - el);
    if (d == 0) {
        // keep sl
    } else if (d >= 127) {
        sl = (sl != 0) ? 1 : 0;
    } else {
        unsigned __int128 mask = (((unsigned __int128)1) << d) - 1;
        sl = (sl >> d) | ((sl & mask) ? 1 : 0);
    }
    if (nh == nl) return {2, nh, sh + sl, eh};
    if (sh > sl) return {2, nh, sh - sl, eh};
    if (sl > sh) return {2, nl, sl - sh, eh};
    return {0, false, 0, 0};
}

__device__ __forceinline__ Val align_c(Val c, int grid) {
    if (c.kind != 2) return c;
    if (c.exp >= grid) return c;
    int lead = c.exp + 127 - lz128(c.sig);
    if (lead - grid <= -2) return {0, false, 0, 0};
    unsigned s = (unsigned)(grid - c.exp);
    unsigned __int128 kept = (s >= 128) ? 0 : (c.sig >> s);
    bool sticky = s >= 128 || (c.sig & ((((unsigned __int128)1) << s) - 1)) != 0;
    return {2, c.neg, kept | (sticky ? 1 : 0), grid};
}

__device__ __forceinline__ unsigned long long vfma_bits(
    Fmt in_fmt, Fmt out_fmt, unsigned a_bits, unsigned b_bits, unsigned c_bits) {
    Val a = decode(in_fmt, a_bits);
    Val b = decode(in_fmt, b_bits);
    Val c = decode(in_fmt, c_bits);
    if (a.kind == 2 && b.kind == 2) {
        int m = in_fmt.man_bits;
        int full = in_fmt.mul_full_bits >= 0 ? in_fmt.mul_full_bits : in_fmt.man_bits;
        c = align_c(c, (a.exp + m) + (b.exp + m) - full - m);
    }
    Val r = add_exact(mul_exact(in_fmt, a, b), c);
    if (r.kind == 0) return 0;
    if (r.kind == 1) return inf_bits(out_fmt, r.neg);
    return round_pack(out_fmt, r.neg, r.sig, r.exp);
}

extern "C" __global__ void vfma_f32(
    const unsigned* a, const unsigned* b, const unsigned* c,
    unsigned* out, int n) {
    int i = blockIdx.x * blockDim.x + threadIdx.x;
    if (i < n) {
        Fmt f = {8, 23, 18};
        out[i] = (unsigned)vfma_bits(f, f, a[i], b[i], c[i]);
    }
}

__device__ __forceinline__ unsigned* pick_mem(
    int which, unsigned* lm0, unsigned* lm1, unsigned* grf0, unsigned* grf1) {
    if (which == 0) return lm0;
    if (which == 1) return lm1;
    if (which == 2) return grf0;
    return grf1;
}

__device__ __forceinline__ int mem_len(int which) {
    return which < 2 ? 4096 : 512;
}

// One f32 MAU line. Each thread handles one PE, reads all four cycles
// before writing, and computes the two f32 lanes. Every operand has its own
// access length; lanes beyond a source's length read as zero. Masks, T,
// base registers, ext/rnd and the other forwarding registers are not part
// of this kernel yet.
extern "C" __global__ void mau_line(
    unsigned* lm0, unsigned* lm1, unsigned* grf0, unsigned* grf1,
    unsigned* mauf, unsigned* aluf, unsigned* mask, unsigned* t,
    int kind,
    int amem, unsigned a0, unsigned a1, unsigned a2, unsigned a3, int awl, int aneg,
    int bmem, unsigned b0, unsigned b1, unsigned b2, unsigned b3, int bwl, int bneg,
    int cmem, unsigned c0, unsigned c1, unsigned c2, unsigned c3, int cwl, int cneg,
    int dmem, unsigned d0, unsigned d1, unsigned d2, unsigned d3, int dwl,
    int mask_kind, int mask_entry, int mask_pattern, int mask_ll) {
    int pe = blockIdx.x * blockDim.x + threadIdx.x;
    if (pe >= 4096) return;
    unsigned ab[4] = {a0, a1, a2, a3};
    unsigned bb[4] = {b0, b1, b2, b3};
    unsigned cb[4] = {c0, c1, c2, c3};
    unsigned db[4] = {d0, d1, d2, d3};
    unsigned* pa = pick_mem(amem, lm0, lm1, grf0, grf1);
    unsigned* pb = pick_mem(bmem, lm0, lm1, grf0, grf1);
    unsigned* pc = pick_mem(cmem, lm0, lm1, grf0, grf1);
    unsigned* pd = pick_mem(dmem, lm0, lm1, grf0, grf1);
    int la = mem_len(amem);
    int lb = mem_len(bmem);
    int lc = mem_len(cmem);
    int ld = mem_len(dmem);
    Fmt f = {8, 23, 18};
    unsigned one = 0x3f800000u;
    unsigned values[4][2];
    for (int c = 0; c < 4; ++c) {
        for (int l = 0; l < 2; ++l) {
            unsigned av = (amem == 4)
                ? mauf[pe * 16 + c * 4 + l]
                : (amem == 5)
                    ? aluf[pe * 16 + c * 4 + l]
                    : (l < awl ? pa[pe * la + ab[c] + l] : 0);
            if (aneg) av ^= 0x80000000u;
            unsigned bv;
            unsigned cv;
            if (kind == 0) {
                bv = (bmem == 4)
                    ? mauf[pe * 16 + c * 4 + l]
                    : (bmem == 5)
                        ? aluf[pe * 16 + c * 4 + l]
                        : (l < bwl ? pb[pe * lb + bb[c] + l] : 0);
                cv = (cmem == 4)
                    ? mauf[pe * 16 + c * 4 + l]
                    : (cmem == 5)
                        ? aluf[pe * 16 + c * 4 + l]
                        : (l < cwl ? pc[pe * lc + cb[c] + l] : 0);
                if (bneg) bv ^= 0x80000000u;
                if (cneg) cv ^= 0x80000000u;
            } else if (kind == 1) {
                bv = (bmem == 4)
                    ? mauf[pe * 16 + c * 4 + l]
                    : (bmem == 5)
                        ? aluf[pe * 16 + c * 4 + l]
                        : (l < bwl ? pb[pe * lb + bb[c] + l] : 0);
                if (bneg) bv ^= 0x80000000u;
                cv = 0;
            } else if (kind == 2) {
                bv = one;
                cv = (cmem == 4)
                    ? mauf[pe * 16 + c * 4 + l]
                    : (cmem == 5)
                        ? aluf[pe * 16 + c * 4 + l]
                        : (l < cwl ? pc[pe * lc + cb[c] + l] : 0);
                if (cneg) cv ^= 0x80000000u;
            } else {
                bv = one;
                cv = 0;
            }
            values[c][l] = (unsigned)vfma_bits(f, f, av, bv, cv);
        }
    }
    for (int c = 0; c < 4; ++c) {
        unsigned flags = 0xf;
        if (mask_kind == 1) {
            flags = (mask_entry >= 1 && mask_entry <= 15)
                ? ((mask[pe * 16 + mask_entry] >> (4 * c)) & 0xf)
                : (((mask_entry >> (3 - c)) & 1) ? 0xf : 0);
        } else if (mask_kind == 2) {
            flags = ((mask_pattern >> c) & 1) ? 0xf : 0;
        }
        for (int l = 0; l < dwl; ++l) {
            int enabled;
            if (mask_kind == 0) {
                enabled = 1;
            } else if (mask_ll) {
                enabled = (flags >> (3 - l)) & 1;
            } else if (l < 2) {
                enabled = ((flags >> (2 - 2 * l)) & 3) != 0;
            } else {
                enabled = 1;
            }
            if (!enabled) continue;
            unsigned value = (l < 2) ? values[c][l] : 0;
            if (mask_kind != 0 && !mask_ll && l < 2) {
                unsigned hi = (flags >> (3 - 2 * l)) & 1;
                unsigned lo = (flags >> (2 - 2 * l)) & 1;
                unsigned m = (hi ? 0xffff0000u : 0) | (lo ? 0x0000ffffu : 0);
                unsigned old = pd[pe * ld + db[c] + l];
                value = (old & ~m) | (value & m);
            }
            pd[pe * ld + db[c] + l] = value;
        }
        mauf[pe * 16 + c * 4] = values[c][0];
        mauf[pe * 16 + c * 4 + 1] = values[c][1];
        mauf[pe * 16 + c * 4 + 2] = 0;
        mauf[pe * 16 + c * 4 + 3] = 0;
    }
}

// One f32 ALU line: Passa (kind 0) or Xor (kind 1). A destination can be a
// PE memory, OMR entry (omr > 0) or nowhere (dwl = 0). Masks on the write and
// the other ALU opcodes are not part of this kernel yet.
extern "C" __global__ void alu_line(
    unsigned* lm0, unsigned* lm1, unsigned* grf0, unsigned* grf1,
    unsigned* mauf, unsigned* aluf, unsigned* mask, unsigned* t,
    int kind,
    int amem, unsigned a0, unsigned a1, unsigned a2, unsigned a3, int awl,
    int bmem, unsigned b0, unsigned b1, unsigned b2, unsigned b3, int bwl,
    int dmem, unsigned d0, unsigned d1, unsigned d2, unsigned d3, int dwl,
    int omr, int tdst, unsigned imm, int imm_u) {
    int pe = blockIdx.x * blockDim.x + threadIdx.x;
    if (pe >= 4096) return;
    unsigned ab[4] = {a0, a1, a2, a3};
    unsigned bb[4] = {b0, b1, b2, b3};
    unsigned db[4] = {d0, d1, d2, d3};
    unsigned* pa = pick_mem(amem, lm0, lm1, grf0, grf1);
    unsigned* pb = pick_mem(bmem, lm0, lm1, grf0, grf1);
    unsigned* pd = pick_mem(dmem, lm0, lm1, grf0, grf1);
    int la = mem_len(amem);
    int lb = mem_len(bmem);
    int ld = mem_len(dmem);
    for (int c = 0; c < 4; ++c) {
        unsigned av[4];
        unsigned bv[4];
        for (int i = 0; i < 4; ++i) {
            if (amem == 4) {
                av[i] = mauf[pe * 16 + c * 4 + i];
            } else if (amem == 5) {
                av[i] = aluf[pe * 16 + c * 4 + i];
            } else if (amem == 6) {
                av[i] = t[pe * 16 + c * 4 + i];
            } else {
                av[i] = (i < awl) ? pa[pe * la + ab[c] + i] : 0;
            }
            if (bmem == 4) {
                bv[i] = mauf[pe * 16 + c * 4 + i];
            } else if (bmem == 5) {
                bv[i] = aluf[pe * 16 + c * 4 + i];
            } else if (bmem == 6) {
                bv[i] = t[pe * 16 + c * 4 + i];
            } else {
                bv[i] = (i < bwl) ? pb[pe * lb + bb[c] + i] : 0;
            }
        }
        unsigned out[4];
        unsigned flags;
        if (kind == 0) {
            for (int i = 0; i < 4; ++i) out[i] = av[i];
            flags = ((av[0] == 0) ? 0xc : 0) | ((av[1] == 0) ? 0x3 : 0);
        } else if (kind == 1) {
            out[0] = av[0] ^ bv[0];
            out[1] = av[1] ^ bv[1];
            out[2] = av[2];
            out[3] = av[3];
            flags = ((out[0] == 0) ? 0xc : 0) | ((out[1] == 0) ? 0x3 : 0);
        } else if (kind == 2) {
            int pick0 = 0;
            int pick1 = 0;
            for (int l = 0; l < 2; ++l) {
                unsigned a = av[l];
                unsigned b = bv[l];
                bool pick;
                if (a == b) {
                    pick = true;
                } else if (((a >> 23) & 0xff) == 0 && ((b >> 23) & 0xff) == 0) {
                    pick = true;
                } else {
                    unsigned am = (a & 0x7fffffffu);
                    unsigned bm = (b & 0x7fffffffu);
                    if (((a >> 23) & 0xff) == 0) am = 0;
                    if (((b >> 23) & 0xff) == 0) bm = 0;
                    long long ka = (a >> 31) ? -(long long)am : (long long)am;
                    long long kb = (b >> 31) ? -(long long)bm : (long long)bm;
                    pick = ka >= kb;
                }
                out[l] = pick ? a : b;
                if (pick) {
                    if (l == 0) pick0 = 1;
                    else pick1 = 1;
                }
            }
            out[2] = av[2];
            out[3] = av[3];
            flags = (pick0 ? 0xc : 0) | (pick1 ? 0x3 : 0);
        } else if (kind == 3) {
            const unsigned MANT5[2][16] = {
                {13, 11, 10, 9, 8, 7, 6, 5, 4, 4, 3, 2, 2, 1, 1, 0},
                {31, 30, 28, 26, 25, 23, 22, 21, 20, 19, 18, 17, 16, 15, 14, 13},
            };
            unsigned sign0 = (av[0] >> 31) & 1;
            unsigned sign1 = (av[1] >> 31) & 1;
            for (int l = 0; l < 2; ++l) {
                unsigned v = av[l];
                unsigned e = (v >> 23) & 0xff;
                unsigned top4 = (v >> 19) & 15;
                unsigned out_e = 127 + 64 - 1 - ((e + 1) / 2);
                out[l] = (out_e << 23) | (MANT5[e & 1][top4] << 18);
            }
            out[2] = av[2];
            out[3] = av[3];
            flags = ((sign0 == 0) ? 0xc : 0) | ((sign1 == 0) ? 0x3 : 0);
        } else if (kind == 4) {
            int src_pe = (pe & ~3) | ((pe + 1) & 3);
            unsigned sv[4];
            for (int i = 0; i < 4; ++i) {
                if (amem == 4) {
                    sv[i] = mauf[src_pe * 16 + c * 4 + i];
                } else if (amem == 5) {
                    sv[i] = aluf[src_pe * 16 + c * 4 + i];
                } else {
                    sv[i] = (i < awl) ? pa[src_pe * la + ab[c] + i] : 0;
                }
            }
            out[0] = sv[0];
            out[1] = sv[1];
            out[2] = 0;
            out[3] = 0;
            flags = 0;
        } else if (kind == 5) {
            for (int i = 0; i < 4; ++i) out[i] = 0;
            flags = 0;
        } else {
            unsigned value = imm;
            if (imm_u) {
                out[0] = value;
                out[1] = 0;
                out[2] = value;
                out[3] = 0;
            } else {
                for (int i = 0; i < 4; ++i) out[i] = value;
            }
            flags = 0;
        }
        if (tdst) {
            for (int i = 0; i < 4; ++i) {
                t[pe * 16 + c * 4 + i] = out[i];
            }
        } else if (omr > 0) {
            unsigned old = mask[pe * 16 + omr];
            unsigned field = 0xfu << (4 * c);
            mask[pe * 16 + omr] = (old & ~field) | ((unsigned)flags << (4 * c));
        } else {
            for (int i = 0; i < dwl; ++i) {
                pd[pe * ld + db[c] + i] = out[i];
            }
        }
        for (int i = 0; i < 4; ++i) {
            aluf[pe * 16 + c * 4 + i] = out[i];
        }
    }
}

__device__ __forceinline__ unsigned __int128 round_shift128(
    unsigned __int128 v, unsigned shift) {
    if (shift == 0) return v;
    if (shift >= 128) return 0;
    unsigned __int128 k = v >> shift;
    unsigned __int128 rem = v & ((((unsigned __int128)1) << shift) - 1);
    unsigned __int128 half = ((unsigned __int128)1) << (shift - 1);
    return k + ((rem > half || (rem == half && (k & 1))) ? 1 : 0);
}

__device__ __forceinline__ void block_float_single(
    const unsigned* vals, unsigned* out) {
    int m = 23;
    unsigned emax = 255;
    unsigned sign_bit = 1u << 31;
    int dropped = 5;
    unsigned max_e = 0;
    for (int i = 0; i < 8; ++i) {
        unsigned e = (vals[i] >> m) & emax;
        if (e > max_e) max_e = e;
    }
    unsigned common = max_e;
    bool top = false;
    for (int i = 0; i < 8; ++i) {
        unsigned v = vals[i];
        unsigned e = (v >> m) & emax;
        unsigned man = v & ((1u << m) - 1);
        if (e == max_e && (man >> dropped) == ((1u << 18) - 1)) top = true;
    }
    if (top) common += 1;
    for (int i = 0; i < 8; ++i) {
        unsigned v = vals[i];
        unsigned s = v & sign_bit;
        unsigned e = (v >> m) & emax;
        unsigned man = v & ((1u << m) - 1);
        if (common >= emax) {
            out[i] = s | (emax << m);
            continue;
        }
        if (max_e == 0) {
            out[i] = s;
            continue;
        }
        if (e == 0) {
            out[i] = s | (common << m);
            continue;
        }
        unsigned d = common - e;
        unsigned __int128 sig = ((unsigned __int128)1 << m) | man;
        unsigned shift = d + 1 + dropped;
        unsigned __int128 r = round_shift128(sig, shift);
        r <<= dropped;
        if (r == 0) {
            out[i] = s | (common << m);
            continue;
        }
        out[i] = s | (common << m) | ((unsigned)r & ((1u << m) - 1));
    }
}

// One gbfn line. Each thread handles one MAB and one cycle: it reads the
// four PEs' source buses, converts the eight values as one block and writes
// aluf (and the destination, if any).
extern "C" __global__ void bfn_line(
    unsigned* lm0, unsigned* lm1, unsigned* grf0, unsigned* grf1,
    unsigned* mauf, unsigned* aluf,
    int smem, unsigned s0, unsigned s1, unsigned s2, unsigned s3, int swl,
    int dmem, unsigned d0, unsigned d1, unsigned d2, unsigned d3, int dwl) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx >= 4096) return;
    int mab = idx >> 2;
    int c = idx & 3;
    unsigned sb[4] = {s0, s1, s2, s3};
    unsigned db[4] = {d0, d1, d2, d3};
    unsigned* ps = pick_mem(smem, lm0, lm1, grf0, grf1);
    unsigned* pd = pick_mem(dmem, lm0, lm1, grf0, grf1);
    int ls = mem_len(smem);
    int ld = mem_len(dmem);
    unsigned bus[4][4];
    for (int p = 0; p < 4; ++p) {
        int pe = mab * 4 + p;
        for (int i = 0; i < 4; ++i) {
            if (smem == 4) {
                bus[p][i] = mauf[pe * 16 + c * 4 + i];
            } else if (smem == 5) {
                bus[p][i] = aluf[pe * 16 + c * 4 + i];
            } else {
                bus[p][i] = (i < swl) ? ps[pe * ls + sb[c] + i] : 0;
            }
        }
    }
    unsigned vals[8];
    unsigned conv[8];
    for (int p = 0; p < 4; ++p) {
        vals[2 * p] = bus[p][0];
        vals[2 * p + 1] = bus[p][1];
    }
    block_float_single(vals, conv);
    for (int p = 0; p < 4; ++p) {
        int pe = mab * 4 + p;
        unsigned out[4] = {conv[2 * p], conv[2 * p + 1], 0, 0};
        if (dmem < 4) {
            for (int i = 0; i < dwl; ++i) {
                pd[pe * ld + db[c] + i] = out[i];
            }
        }
        for (int i = 0; i < 4; ++i) {
            aluf[pe * 16 + c * 4 + i] = out[i];
        }
    }
}
