
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
                    : (amem == 6)
                        ? t[pe * 16 + c * 4 + l]
                        : (l < awl ? pa[pe * la + ab[c] + l] : 0);
            if (aneg) av ^= 0x80000000u;
            unsigned bv;
            unsigned cv;
            if (kind == 0) {
                bv = (bmem == 4)
                    ? mauf[pe * 16 + c * 4 + l]
                    : (bmem == 5)
                        ? aluf[pe * 16 + c * 4 + l]
                        : (bmem == 6)
                            ? t[pe * 16 + c * 4 + l]
                            : (l < bwl ? pb[pe * lb + bb[c] + l] : 0);
                cv = (cmem == 4)
                    ? mauf[pe * 16 + c * 4 + l]
                    : (cmem == 5)
                        ? aluf[pe * 16 + c * 4 + l]
                        : (cmem == 6)
                            ? t[pe * 16 + c * 4 + l]
                            : (l < cwl ? pc[pe * lc + cb[c] + l] : 0);
                if (bneg) bv ^= 0x80000000u;
                if (cneg) cv ^= 0x80000000u;
            } else if (kind == 1) {
                bv = (bmem == 4)
                    ? mauf[pe * 16 + c * 4 + l]
                    : (bmem == 5)
                        ? aluf[pe * 16 + c * 4 + l]
                        : (bmem == 6)
                            ? t[pe * 16 + c * 4 + l]
                            : (l < bwl ? pb[pe * lb + bb[c] + l] : 0);
                if (bneg) bv ^= 0x80000000u;
                cv = 0;
            } else if (kind == 2) {
                bv = one;
                cv = (cmem == 4)
                    ? mauf[pe * 16 + c * 4 + l]
                    : (cmem == 5)
                        ? aluf[pe * 16 + c * 4 + l]
                        : (cmem == 6)
                            ? t[pe * 16 + c * 4 + l]
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

// ---------------------------------------------------------------------------
// Full ALU instruction set (SDM 3.6.12) and block-float conversion (3.6.12.12).
//
// A descriptor built by `gpu::alu_line_from_expr` is passed by value. One
// thread handles one MAB (four PEs) and all four cycles: all inputs are read
// before anything is written, so msl/msr and overlapping memory destinations
// behave like the CPU model.
// ---------------------------------------------------------------------------

struct AluSrc {
    unsigned mem;
    unsigned wl;
    unsigned base[4];
    unsigned rnd;
    unsigned fixed;
    unsigned neg;
    unsigned ext;
};

struct AluDstDesc {
    unsigned kind;
    unsigned mem;
    unsigned wl;
    unsigned base[4];
    unsigned entry;
    unsigned mask_kind;
    unsigned mask_entry;
    unsigned mask_pattern;
    unsigned mask_ll;
};

struct AluDesc {
    unsigned op;
    unsigned prec;
    unsigned uns;
    unsigned arg;
    unsigned imm;
    unsigned imm_u;
    AluSrc a;
    AluSrc b;
    unsigned ndst;
    AluDstDesc dst[8];
    unsigned flush_kind;
    unsigned flush_entry;
    unsigned flush_pattern;
    unsigned flush_ll;
};

enum {
    AOP_ZERO = 0, AOP_IMM = 1, AOP_MSL = 2, AOP_MSR = 3, AOP_PASSA = 4,
    AOP_INC = 5, AOP_DEC = 6, AOP_NOT = 7, AOP_LNOT = 8, AOP_RSQRT = 9,
    AOP_FLOOR = 10, AOP_FTOI = 11, AOP_MAX = 12, AOP_MIN = 13,
    AOP_PACKBIT = 14, AOP_AND = 15, AOP_OR = 16, AOP_XOR = 17,
    AOP_ADD = 18, AOP_SUB = 19, AOP_LSL = 20, AOP_LSR = 21, AOP_BSL = 22,
    AOP_BSR = 23, AOP_RELU = 24, AOP_RELU0 = 25, AOP_RELU1 = 26,
    AOP_RELU2 = 27, AOP_RELU3 = 28, AOP_LRELUD = 29, AOP_LRELUO = 30,
    AOP_ILRELUD = 31, AOP_BFN = 32, AOP_BFE = 33
};

__device__ __forceinline__ int alu_prec_bits(unsigned p) {
    if (p == 0 || p == 4) return 64; // D, L
    if (p == 3 || p == 6) return 16; // H, S
    return 32;                       // F, G, I, none
}

__device__ __forceinline__ bool alu_is_float(unsigned p) {
    return p == 0 || p == 1 || p == 3;
}

__device__ __forceinline__ Fmt alu_fmt(unsigned p) {
    if (p == 0) return {11, 52, 36}; // double
    if (p == 3) return {6, 9, -1};   // half
    return {8, 23, 18};              // single
}

__device__ __forceinline__ unsigned long long alu_mask(int bits) {
    return bits == 64 ? ~0ULL : ((1ULL << bits) - 1);
}

__device__ __forceinline__ long long alu_sext(unsigned long long v, int bits) {
    if (bits == 64) return (long long)v;
    return (long long)(v << (64 - bits)) >> (64 - bits);
}

__device__ __forceinline__ void alu_unpack(const unsigned b[4], int bits, unsigned long long out[4]) {
    unsigned __int128 full = ((unsigned __int128)b[0] << 96) |
                             ((unsigned __int128)b[1] << 64) |
                             ((unsigned __int128)b[2] << 32) | b[3];
    int n = 64 / bits;
    unsigned __int128 m = (((unsigned __int128)1) << bits) - 1;
    for (int i = 0; i < n; ++i) {
        out[i] = (unsigned long long)((full >> (128 - bits * (i + 1))) & m);
    }
}

__device__ __forceinline__ void alu_pack_lanes(const unsigned long long in[4], int bits, unsigned out[4]) {
    unsigned __int128 full = 0;
    int n = 64 / bits;
    unsigned __int128 m = (((unsigned __int128)1) << bits) - 1;
    for (int i = 0; i < n; ++i) {
        full |= ((unsigned __int128)(in[i] & (unsigned long long)m)) << (128 - bits * (i + 1));
    }
    out[0] = (unsigned)(full >> 96);
    out[1] = (unsigned)(full >> 64);
}

__device__ __forceinline__ void alu_splat(unsigned long long lane, int bits, unsigned out[4]) {
    unsigned __int128 full = 0;
    int n = 128 / bits;
    unsigned __int128 m = (((unsigned __int128)1) << bits) - 1;
    for (int i = 0; i < n; ++i) {
        full |= ((unsigned __int128)(lane & (unsigned long long)m)) << (128 - bits * (i + 1));
    }
    out[0] = (unsigned)(full >> 96);
    out[1] = (unsigned)(full >> 64);
    out[2] = (unsigned)(full >> 32);
    out[3] = (unsigned)full;
}

__device__ __forceinline__ unsigned long long alu_fixed_value(unsigned kind, int pe, int bits) {
    int group = pe / 1024;
    int l2b = (pe / 512) & 1;
    int l1b = (pe / 64) & 7;
    int mab = (pe / 4) & 15;
    int sub = pe & 3;
    switch (kind) {
        case 1: return (unsigned long long)(group * 2 + l2b);
        case 2: return (unsigned long long)l1b;
        case 3: return (unsigned long long)mab;
        case 4: return (unsigned long long)(mab * 4 + sub);
        case 5: return (unsigned long long)sub;
        case 6: return 1ULL << (bits - 1);
        default: return 0;
    }
}

__device__ __forceinline__ unsigned long long encode_val(Fmt f, Val v) {
    if (v.kind == 0) return 0;
    if (v.kind == 1) return inf_bits(f, v.neg);
    return round_pack(f, v.neg, v.sig, v.exp);
}

__device__ __forceinline__ void round_bus_dev(const unsigned in[4], unsigned out[4]) {
    Fmt s = {8, 23, 18};
    Fmt h = {6, 9, -1};
    unsigned long long hh[4];
    for (int i = 0; i < 4; ++i) hh[i] = encode_val(h, decode(s, in[i]));
    out[0] = (unsigned)((hh[0] << 16) | hh[1]);
    out[1] = (unsigned)((hh[2] << 16) | hh[3]);
    out[2] = 0;
    out[3] = 0;
}

// Reads one input bus for one PE and cycle and applies the `r` operand option.
__device__ __forceinline__ void alu_read_src(
    const AluSrc& s, int pe, int c,
    unsigned* lm0, unsigned* lm1, unsigned* grf0, unsigned* grf1,
    unsigned* mauf, unsigned* aluf, unsigned* t, unsigned* mreadf,
    int bits, unsigned out[4]) {
    for (int i = 0; i < 4; ++i) out[i] = 0;
    if (s.fixed != 0) {
        unsigned long long lane = alu_fixed_value(s.fixed, pe, bits);
        alu_splat(lane, bits, out);
    } else if (s.mem < 4) {
        unsigned* p = pick_mem((int)s.mem, lm0, lm1, grf0, grf1);
        int len = mem_len((int)s.mem);
        unsigned base = s.base[c];
        for (unsigned i = 0; i < s.wl && i < 4; ++i) {
            out[i] = p[pe * len + (int)((base + i) & (unsigned)(len - 1))];
        }
    } else if (s.mem == 4) {
        for (int i = 0; i < 4; ++i) out[i] = mauf[pe * 16 + c * 4 + i];
    } else if (s.mem == 5) {
        for (int i = 0; i < 4; ++i) out[i] = aluf[pe * 16 + c * 4 + i];
    } else if (s.mem == 6) {
        for (int i = 0; i < 4; ++i) out[i] = t[pe * 16 + c * 4 + i];
    } else if (s.mem == 8) {
        for (int i = 0; i < 4; ++i) out[i] = mreadf[pe * 16 + c * 4 + i];
    }
    if (s.rnd) {
        unsigned r[4];
        round_bus_dev(out, r);
        for (int i = 0; i < 4; ++i) out[i] = r[i];
    }
    // `neg` and `ext` are no-ops for ALU instructions in the CPU model.
}

__device__ __forceinline__ unsigned alu_flags(const bool cond[4], int bits) {
    if (bits == 64) return cond[0] ? 0xf : 0;
    if (bits == 32) return (cond[0] ? 0xc : 0) | (cond[1] ? 0x3 : 0);
    unsigned f = 0;
    for (int i = 0; i < 4; ++i) f |= (cond[i] ? 1u : 0u) << (3 - i);
    return f;
}

__device__ __forceinline__ unsigned long long float_rsqrt_dev(Fmt f, unsigned long long v) {
    const unsigned MANT5[2][16] = {
        {13, 11, 10, 9, 8, 7, 6, 5, 4, 4, 3, 2, 2, 1, 1, 0},
        {31, 30, 28, 26, 25, 23, 22, 21, 20, 19, 18, 17, 16, 15, 14, 13},
    };
    unsigned m = (unsigned)f.man_bits;
    unsigned long long e = (v >> m) & exp_max(f);
    unsigned long long top4 = (v >> (m - 4)) & 15;
    unsigned long long bias = (unsigned long long)((1LL << (f.exp_bits - 1)) - 1);
    unsigned long long out_e = bias + (bias + 1) / 2 - 1 - (e + 1) / 2;
    return (out_e << m) | ((unsigned long long)MANT5[e & 1][top4] << (m - 5));
}

__device__ __forceinline__ unsigned long long float_floor_dev(Fmt f, unsigned long long v) {
    Val x = decode(f, v);
    if (x.kind != 2) return v;
    if (x.exp >= 0) return v;
    unsigned sh = (unsigned)(-x.exp);
    unsigned __int128 sig = x.sig;
    unsigned __int128 iv = (sh >= 128) ? 0 : (sig >> sh);
    bool frac = sh >= 128 || (sig & ((((unsigned __int128)1) << sh) - 1)) != 0;
    if (x.neg && frac) iv += 1;
    if (iv == 0) return x.neg ? (1ULL << (width(f) - 1)) : 0;
    return round_pack(f, x.neg, iv, 0);
}

__device__ __forceinline__ unsigned long long float_ftoi_dev(
    Fmt f, unsigned long long v, bool uns, int bits) {
    Val x = decode(f, v);
    bool neg = false;
    bool overflow = false;
    unsigned __int128 mag = 0;
    if (x.kind == 1) {
        neg = x.neg;
        overflow = true;
    } else if (x.kind == 2) {
        neg = x.neg;
        if (x.exp >= 0) {
            if (x.exp > 70) {
                overflow = true;
            } else {
                mag = x.sig << x.exp;
            }
        } else if (-x.exp >= 127) {
            mag = 0;
        } else {
            mag = x.sig >> (unsigned)(-x.exp);
        }
    }
    unsigned long long mask = alu_mask(bits);
    unsigned __int128 smax = (((unsigned __int128)1) << (bits - 1)) - 1;
    unsigned __int128 smin = -(((unsigned __int128)1) << (bits - 1));
    unsigned __int128 umax = (((unsigned __int128)1) << bits) - 1;
    if (uns) {
        if (overflow) return (unsigned long long)umax & mask;
        unsigned __int128 r = mag > umax ? umax : mag;
        return (unsigned long long)r & mask;
    }
    __int128 s;
    if (overflow) {
        s = neg ? (__int128)smin : (__int128)smax;
    } else if (neg) {
        s = -(__int128)mag;
        if (s < (__int128)smin) s = (__int128)smin;
    } else {
        s = (__int128)mag;
        if (s > (__int128)smax) s = (__int128)smax;
    }
    return (unsigned long long)(long long)s & mask;
}

__device__ __forceinline__ bool float_max_pick_dev(Fmt f, unsigned long long a, unsigned long long b, bool max) {
    if (a == b) return true;
    int bits = width(f);
    unsigned long long ea = (a >> f.man_bits) & exp_max(f);
    unsigned long long eb = (b >> f.man_bits) & exp_max(f);
    if (ea == 0 && eb == 0) return true;
    unsigned long long ma = a & ((1ULL << (bits - 1)) - 1);
    unsigned long long mb = b & ((1ULL << (bits - 1)) - 1);
    if (ea == 0) ma = 0;
    if (eb == 0) mb = 0;
    long long ka = (a >> (bits - 1)) ? -(long long)ma : (long long)ma;
    long long kb = (b >> (bits - 1)) ? -(long long)mb : (long long)mb;
    return max ? ka >= kb : ka <= kb;
}

__device__ __forceinline__ unsigned long long float_lrelu_dev(unsigned op, Fmt f, unsigned long long y) {
    unsigned m = (unsigned)f.man_bits;
    unsigned long long zero = 1ULL << (width(f) - 1);
    unsigned long long e = (y >> m) & exp_max(f);
    unsigned long long emax = exp_max(f);
    if (op == AOP_LRELUD) {
        if (e == emax) return y;
        if (e <= 1) return zero;
        return y - (1ULL << m);
    }
    if (op == AOP_LRELUO) {
        if (e == emax) return y;
        if (e <= 3) return zero;
        return y - (3ULL << m);
    }
    if (e == emax) return y;
    return y + (1ULL << m);
}

__device__ __forceinline__ bool is_alu_two_input(unsigned op) {
    return op >= AOP_MAX && op <= AOP_ILRELUD;
}

// Computes one lane of an ALU operation. Returns the mask-flag condition.
__device__ __forceinline__ bool alu_lane(
    unsigned op, int bits, Fmt f, bool is_float, bool uns, unsigned long long a,
    unsigned long long b, unsigned long long& r) {
    unsigned long long mask = alu_mask(bits);
    long long sa = alu_sext(a, bits);
    long long sb = alu_sext(b, bits);
    bool c = false;
    switch (op) {
        case AOP_INC: case AOP_DEC: case AOP_ADD: case AOP_SUB: {
            unsigned long long rhs = (op == AOP_INC || op == AOP_DEC) ? 1ULL : b;
            bool sub = (op == AOP_DEC || op == AOP_SUB);
            r = (sub ? a - rhs : a + rhs) & mask;
            c = (bits < 64) ? (((r >> (bits - 1)) & 1) == 0) : (((r >> 63) & 1) == 0);
            if (is_float) c = false;
            break;
        }
        case AOP_NOT:
            r = (~a) & mask;
            c = r == 0;
            break;
        case AOP_LNOT:
            r = (a == 0) ? 1ULL : 0ULL;
            c = a != 0;
            break;
        case AOP_AND: r = a & b; c = (a & b) == 0; break;
        case AOP_OR: r = a | b; c = (a | b) == 0; break;
        case AOP_XOR: r = a ^ b; c = (a ^ b) == 0; break;
        case AOP_LSL: case AOP_LSR: case AOP_BSL: case AOP_BSR: {
            unsigned s = (unsigned)(b % (unsigned long long)(2 * bits));
            if (op == AOP_LSL) {
                r = (s >= (unsigned)bits) ? 0 : ((a << s) & mask);
            } else if (op == AOP_LSR) {
                r = uns ? ((s >= (unsigned)bits) ? 0 : (a >> s))
                        : ((unsigned long long)(sa >> (s < 63 ? s : 63)) & mask);
            } else {
                unsigned sh = (s >= (unsigned)bits) ? (s - bits) : s;
                if (sh == 0) {
                    r = a;
                } else if (op == AOP_BSL) {
                    r = ((a << sh) | (a >> (bits - sh))) & mask;
                } else {
                    r = ((a >> sh) | (a << (bits - sh))) & mask;
                }
            }
            c = r == 0;
            break;
        }
        case AOP_MAX: case AOP_MIN: {
            bool pick;
            if (is_float) {
                pick = float_max_pick_dev(f, a, b, op == AOP_MAX);
            } else if (uns) {
                pick = (op == AOP_MAX) ? (a >= b) : (a <= b);
            } else {
                pick = (op == AOP_MAX) ? (sa >= sb) : (sa <= sb);
            }
            r = pick ? a : b;
            c = pick;
            break;
        }
        case AOP_PACKBIT: {
            unsigned long long msb = (b >> (bits - 1)) & 1;
            r = ((a << 1) | msb) & mask;
            c = msb == 0;
            break;
        }
        case AOP_RELU: case AOP_RELU0: case AOP_RELU1: case AOP_RELU2: case AOP_RELU3: {
            int k = (op == AOP_RELU1) ? 1 : (op == AOP_RELU2) ? 2 : (op == AOP_RELU3) ? 3 : 0;
            unsigned long long bit = (a >> (bits - 1 - k)) & 1;
            r = (bit == 0) ? b : (1ULL << (bits - 1));
            c = bit == 0;
            break;
        }
        case AOP_RSQRT:
            r = float_rsqrt_dev(f, a);
            c = ((a >> (bits - 1)) & 1) == 0;
            break;
        case AOP_FLOOR:
            r = float_floor_dev(f, a);
            c = false;
            break;
        case AOP_FTOI:
            r = float_ftoi_dev(f, a, false, bits); // unsigned handled by caller flag
            c = false;
            break;
        case AOP_LRELUD: case AOP_LRELUO: case AOP_ILRELUD:
            r = float_lrelu_dev(op, f, b);
            c = ((a >> (bits - 1)) & 1) == 0;
            break;
        default:
            r = 0;
            break;
    }
    return c;
}

// ---------------------------------------------------------------------------
// Mask application, shared by every destination writer.
// ---------------------------------------------------------------------------

__device__ __forceinline__ unsigned mask_flags_dev(
    const unsigned* entries, unsigned kind, unsigned entry, unsigned pattern, int c) {
    if (kind == 1) {
        if (entry == 0) return 0xf;
        if (entry <= 15) return (entries[entry] >> (4 * c)) & 0xf;
        return ((entry >> (3 - c)) & 1) ? 0xf : 0;
    }
    if (kind == 2) return ((pattern >> c) & 1) ? 0xf : 0;
    return 0xf;
}

__device__ __forceinline__ bool word_enabled(bool masked, unsigned f, bool ll, int i) {
    if (!masked) return true;
    if (ll) return ((f >> (3 - i)) & 1) == 1;
    if (i < 2) return ((f >> (2 - 2 * i)) & 3) != 0;
    return true;
}

__device__ __forceinline__ unsigned merge_word(
    bool masked, unsigned f, bool ll, int i, unsigned old, unsigned v) {
    if (!masked || ll || i >= 2) return v;
    unsigned hi = (f >> (3 - 2 * i)) & 1;
    unsigned lo = (f >> (2 - 2 * i)) & 1;
    unsigned m = (hi ? 0xffff0000u : 0) | (lo ? 0x0000ffffu : 0);
    return (old & ~m) | (v & m);
}

__device__ __forceinline__ void alu_apply_flush(unsigned bus[4], unsigned f, bool ll) {
    for (int i = 0; i < 4; ++i) {
        if (ll) {
            if (((f >> (3 - i)) & 1) == 0) bus[i] = 0;
        } else if (i < 2) {
            unsigned hi = (f >> (3 - 2 * i)) & 1;
            unsigned lo = (f >> (2 - 2 * i)) & 1;
            unsigned m = (hi ? 0xffff0000u : 0) | (lo ? 0x0000ffffu : 0);
            bus[i] &= m;
        }
    }
}

__device__ __forceinline__ void alu_write_dst(
    const AluDstDesc& d, int pe, int c, const unsigned bus[4], unsigned flags,
    unsigned* lm0, unsigned* lm1, unsigned* grf0, unsigned* grf1,
    unsigned* mask, unsigned* t) {
    if (d.kind == 3) return;
    bool masked = d.mask_kind != 0;
    unsigned mf = masked ? mask_flags_dev(mask + pe * 16, d.mask_kind, d.mask_entry, d.mask_pattern, c) : 0xf;
    bool ll = d.mask_ll != 0;
    if (d.kind == 0) {
        unsigned* p = pick_mem((int)d.mem, lm0, lm1, grf0, grf1);
        int len = mem_len((int)d.mem);
        int words = (int)d.wl;
        bool any = false;
        for (int i = 0; i < words; ++i) any |= word_enabled(masked, mf, ll, i);
        if (!any) return;
        unsigned base = d.base[c];
        for (int i = 0; i < words; ++i) {
            if (!word_enabled(masked, mf, ll, i)) continue;
            int a = pe * len + (int)((base + i) & (unsigned)(len - 1));
            p[a] = merge_word(masked, mf, ll, i, p[a], bus[i]);
        }
    } else if (d.kind == 1) {
        bool any = false;
        for (int i = 0; i < 4; ++i) any |= word_enabled(masked, mf, ll, i);
        if (!any) return;
        for (int i = 0; i < 4; ++i) {
            if (!word_enabled(masked, mf, ll, i)) continue;
            int a = pe * 16 + c * 4 + i;
            t[a] = merge_word(masked, mf, ll, i, t[a], bus[i]);
        }
    } else if (d.kind == 2) {
        if (d.entry == 0 || d.entry > 15) return;
        unsigned f = masked ? (flags & mf) : flags;
        int a = pe * 16 + (int)d.entry;
        mask[a] = (mask[a] & ~(0xfu << (4 * c))) | (f << (4 * c));
    }
}

// ---------------------------------------------------------------------------
// ALU line.
// ---------------------------------------------------------------------------

extern "C" __global__ void alu_line(
    unsigned* lm0, unsigned* lm1, unsigned* grf0, unsigned* grf1,
    unsigned* mauf, unsigned* aluf, unsigned* mask, unsigned* t,
    unsigned* mreadf, AluDesc d) {
    int mab = blockIdx.x * blockDim.x + threadIdx.x;
    if (mab >= 1024) return;
    int bits = alu_prec_bits(d.prec);
    int nlanes = 64 / bits;
    Fmt f = alu_fmt(d.prec);
    bool is_float = alu_is_float(d.prec);
    bool two = is_alu_two_input(d.op);
    bool cross = (d.op == AOP_MSL || d.op == AOP_MSR);

    unsigned abus[4][4][4];
    unsigned bbus[4][4][4];
    for (int p = 0; p < 4; ++p) {
        int pe = mab * 4 + p;
        int ape = pe;
        if (d.op == AOP_MSL) ape = mab * 4 + ((p + 3) & 3);
        if (d.op == AOP_MSR) ape = mab * 4 + ((p + 1) & 3);
        for (int c = 0; c < 4; ++c) {
            alu_read_src(d.a, ape, c, lm0, lm1, grf0, grf1, mauf, aluf, t, mreadf, bits, abus[p][c]);
            if (two) {
                alu_read_src(d.b, pe, c, lm0, lm1, grf0, grf1, mauf, aluf, t, mreadf, bits, bbus[p][c]);
            }
        }
    }

    unsigned out[4][4][4];
    unsigned fl[4][4];
    for (int p = 0; p < 4; ++p) {
        for (int c = 0; c < 4; ++c) {
            bool cond[4] = {false, false, false, false};
            if (d.op == AOP_ZERO) {
                for (int i = 0; i < 4; ++i) out[p][c][i] = 0;
                fl[p][c] = 0;
            } else if (d.op == AOP_IMM) {
                unsigned v = d.imm;
                if (d.imm_u) {
                    out[p][c][0] = v; out[p][c][1] = 0; out[p][c][2] = v; out[p][c][3] = 0;
                } else {
                    for (int i = 0; i < 4; ++i) out[p][c][i] = v;
                }
                fl[p][c] = 0;
            } else if (d.op == AOP_PASSA) {
                for (int i = 0; i < 4; ++i) out[p][c][i] = abus[p][c][i];
                unsigned long long lanes[4];
                alu_unpack(abus[p][c], bits, lanes);
                for (int i = 0; i < nlanes; ++i) cond[i] = lanes[i] == 0;
                fl[p][c] = alu_flags(cond, bits);
            } else if (cross) {
                out[p][c][0] = abus[p][c][0];
                out[p][c][1] = abus[p][c][1];
                out[p][c][2] = 0;
                out[p][c][3] = 0;
                fl[p][c] = 0;
            } else {
                unsigned long long x[4] = {0, 0, 0, 0};
                unsigned long long y[4] = {0, 0, 0, 0};
                unsigned long long r[4] = {0, 0, 0, 0};
                alu_unpack(abus[p][c], bits, x);
                if (two) alu_unpack(bbus[p][c], bits, y);
                for (int i = 0; i < nlanes; ++i) {
                    bool cc;
                    if (d.op == AOP_FTOI) {
                        r[i] = float_ftoi_dev(f, x[i], d.uns != 0, bits);
                        cc = false;
                    } else {
                        cc = alu_lane(d.op, bits, f, is_float, d.uns != 0, x[i], y[i], r[i]);
                    }
                    cond[i] = cc;
                }
                alu_pack_lanes(r, bits, out[p][c]);
                unsigned o2 = abus[p][c][2];
                unsigned o3 = abus[p][c][3];
                out[p][c][2] = o2;
                out[p][c][3] = o3;
                fl[p][c] = alu_flags(cond, bits);
            }
            // The unsigned inc/dec/add/sub/lsr/max/min flags differ from the signed ones.
            if (d.uns && (d.op == AOP_INC || d.op == AOP_DEC || d.op == AOP_ADD || d.op == AOP_SUB)) {
                bool uc[4] = {false, false, false, false};
                unsigned long long x[4] = {0, 0, 0, 0};
                unsigned long long y[4] = {0, 0, 0, 0};
                alu_unpack(abus[p][c], bits, x);
                if (two) alu_unpack(bbus[p][c], bits, y);
                unsigned long long m = alu_mask(bits);
                bool sub = (d.op == AOP_DEC || d.op == AOP_SUB);
                for (int i = 0; i < nlanes; ++i) {
                    unsigned long long rhs = (d.op == AOP_INC || d.op == AOP_DEC) ? 1ULL : y[i];
                    unsigned __int128 sum = (unsigned __int128)x[i] + (unsigned __int128)rhs;
                    uc[i] = sub ? (x[i] >= rhs) : (sum <= (unsigned __int128)m);
                }
                fl[p][c] = alu_flags(uc, bits);
            } else if (d.uns && d.op == AOP_LSR) {
                bool uc[4] = {false, false, false, false};
                unsigned long long x[4] = {0, 0, 0, 0};
                unsigned long long y[4] = {0, 0, 0, 0};
                alu_unpack(abus[p][c], bits, x);
                alu_unpack(bbus[p][c], bits, y);
                for (int i = 0; i < nlanes; ++i) {
                    unsigned s = (unsigned)(y[i] % (unsigned long long)(2 * bits));
                    unsigned long long r = (s >= (unsigned)bits) ? 0 : (x[i] >> s);
                    uc[i] = r == 0;
                }
                fl[p][c] = alu_flags(uc, bits);
            } else if (d.uns && (d.op == AOP_MAX || d.op == AOP_MIN) && !is_float) {
                bool uc[4] = {false, false, false, false};
                unsigned long long x[4] = {0, 0, 0, 0};
                unsigned long long y[4] = {0, 0, 0, 0};
                alu_unpack(abus[p][c], bits, x);
                alu_unpack(bbus[p][c], bits, y);
                for (int i = 0; i < nlanes; ++i) {
                    uc[i] = (d.op == AOP_MAX) ? (x[i] >= y[i]) : (x[i] <= y[i]);
                }
                fl[p][c] = alu_flags(uc, bits);
            }
        }
    }

    for (int p = 0; p < 4; ++p) {
        int pe = mab * 4 + p;
        for (int c = 0; c < 4; ++c) {
            unsigned bus[4];
            for (int i = 0; i < 4; ++i) bus[i] = out[p][c][i];
            if (d.flush_kind != 0) {
                unsigned mf = mask_flags_dev(mask + pe * 16, d.flush_kind, d.flush_entry, d.flush_pattern, c);
                alu_apply_flush(bus, mf, d.flush_ll != 0);
            }
            for (unsigned k = 0; k < d.ndst && k < 8; ++k) {
                alu_write_dst(d.dst[k], pe, c, bus, fl[p][c], lm0, lm1, grf0, grf1, mask, t);
            }
            // The CPU model stores the zero-flushed output in the forwarding register too.
            for (int i = 0; i < 4; ++i) aluf[pe * 16 + c * 4 + i] = bus[i];
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

// Generic block-float conversion (SDM 3.6.12.12 and float.rs). `keep` is the
// number of mantissa bits kept, `extended` selects the hbfe representation.
__device__ __forceinline__ void block_float_any(
    Fmt f, const unsigned long long* block, int n, int keep, bool extended,
    unsigned long long* conv) {
    int m = (int)f.man_bits;
    unsigned long long emax = exp_max(f);
    unsigned long long sign_bit = 1ULL << (width(f) - 1);
    unsigned long long man_mask_ = man_mask(f);
    int dropped = m - keep;
    unsigned long long max_e = 0;
    for (int i = 0; i < n; ++i) {
        unsigned long long e = (block[i] >> m) & emax;
        if (e > max_e) max_e = e;
    }
    unsigned long long common = max_e;
    bool top = false;
    for (int i = 0; i < n; ++i) {
        unsigned long long v = block[i];
        unsigned long long e = (v >> m) & emax;
        unsigned long long man = v & man_mask_;
        if (e == max_e && (man >> dropped) == ((1ULL << keep) - 1)) top = true;
    }
    if (top) common += 1;
    bool half = (m == 9);
    if (half) common += (unsigned long long)dropped;
    for (int i = 0; i < n; ++i) {
        unsigned long long v = block[i];
        unsigned long long s = v & sign_bit;
        unsigned long long e = (v >> m) & emax;
        unsigned long long man = v & man_mask_;
        if (common >= emax) {
            conv[i] = s | (emax << m);
            continue;
        }
        if (max_e == 0) {
            conv[i] = s;
            continue;
        }
        if (e == 0) {
            conv[i] = extended ? s : (s | (common << m));
            continue;
        }
        unsigned long long d = common - e;
        unsigned __int128 sig = (((unsigned __int128)1) << m) | man;
        bool top_ones = (man >> dropped) == ((1ULL << keep) - 1);
        bool flag = extended && ((long long)d > 6 + dropped ||
                                 ((long long)d == 6 + dropped && !top_ones));
        unsigned shift = (unsigned)(flag ? d - 6 : d) + 1 + (half ? 0u : (unsigned)dropped);
        unsigned __int128 r = round_shift128(sig, shift);
        if (!half) r <<= (unsigned)dropped;
        if (r == 0) {
            conv[i] = extended ? s : (s | (common << m));
            continue;
        }
        unsigned long long ee = flag ? 0 : common;
        conv[i] = s | (ee << m) | ((unsigned long long)r & man_mask_);
    }
}

__device__ __forceinline__ unsigned bfn_get_half(const unsigned bus[4], int k) {
    unsigned w = bus[k / 2];
    return (k & 1) ? (w & 0xffffu) : (w >> 16);
}

__device__ __forceinline__ void bfn_put_half(unsigned bus[4], int k, unsigned h) {
    unsigned& w = bus[k / 2];
    if (k & 1) {
        w = (w & 0xffff0000u) | (h & 0xffffu);
    } else {
        w = (w & 0x0000ffffu) | (h << 16);
    }
}

// One bfn/bfe line. One thread handles one MAB and reads all four cycles
// before writing, matching the CPU's read-all-then-write order.
extern "C" __global__ void bfn_line(
    unsigned* lm0, unsigned* lm1, unsigned* grf0, unsigned* grf1,
    unsigned* mauf, unsigned* aluf, unsigned* mask, unsigned* t,
    unsigned* mreadf, AluDesc d) {
    int mab = blockIdx.x * blockDim.x + threadIdx.x;
    if (mab >= 1024) return;
    unsigned prec = d.prec;
    int bits = (prec == 0) ? 64 : (prec == 3) ? 16 : 32;
    Fmt f = (prec == 0) ? Fmt{11, 52, 36} : (prec == 3) ? Fmt{6, 9, -1} : Fmt{8, 23, 18};
    bool extended = (d.op == AOP_BFE);
    int keep;
    if (prec == 0) keep = 52;
    else if (prec == 1) keep = 23;
    else if (prec == 2) keep = 18;
    else keep = d.arg ? (int)d.arg : 9;

    unsigned bus[4][4][4];
    for (int p = 0; p < 4; ++p) {
        int pe = mab * 4 + p;
        for (int c = 0; c < 4; ++c) {
            alu_read_src(d.a, pe, c, lm0, lm1, grf0, grf1, mauf, aluf, t, mreadf, bits, bus[p][c]);
        }
    }

    unsigned out[4][4][4];
    for (int c = 0; c < 4; ++c) {
        unsigned long long block[32];
        unsigned long long conv[32];
        for (int p = 0; p < 4; ++p) {
            if (prec == 0) {
                block[p] = ((unsigned long long)bus[p][c][0] << 32) | bus[p][c][1];
            } else if (prec == 1 || prec == 2) {
                block[p] = bus[p][c][0];
                block[4 + p] = bus[p][c][1];
            } else {
                for (int k = 0; k < 4; ++k) block[p * 4 + k] = bfn_get_half(bus[p][c], k);
                for (int k = 4; k < 8; ++k) block[16 + p * 4 + (k - 4)] = bfn_get_half(bus[p][c], k);
            }
        }
        if (prec == 0) {
            block_float_any(f, block, 4, keep, extended, conv);
            for (int p = 0; p < 4; ++p) {
                out[p][c][0] = (unsigned)(conv[p] >> 32);
                out[p][c][1] = (unsigned)conv[p];
                out[p][c][2] = 0;
                out[p][c][3] = 0;
            }
        } else if (prec == 1) {
            // Two blocks, one per 32-bit word of each PE.
            block_float_any(f, block, 4, 23, extended, conv);
            block_float_any(f, block + 4, 4, 23, extended, conv + 4);
            for (int p = 0; p < 4; ++p) {
                out[p][c][0] = (unsigned)conv[p];
                out[p][c][1] = (unsigned)conv[4 + p];
                out[p][c][2] = 0;
                out[p][c][3] = 0;
            }
        } else if (prec == 2) {
            // One block of eight pseudo-single values.
            block_float_any(f, block, 8, 18, extended, conv);
            for (int p = 0; p < 4; ++p) {
                out[p][c][0] = (unsigned)conv[p];
                out[p][c][1] = (unsigned)conv[4 + p];
                out[p][c][2] = 0;
                out[p][c][3] = 0;
            }
        } else {
            // Two blocks of sixteen half values: words 0-1 and words 2-3.
            block_float_any(f, block, 16, keep, extended, conv);
            block_float_any(f, block + 16, 16, keep, extended, conv + 16);
            for (int p = 0; p < 4; ++p) {
                for (int k = 0; k < 4; ++k) bfn_put_half(out[p][c], k, (unsigned)conv[p * 4 + k]);
                for (int k = 4; k < 8; ++k) {
                    bfn_put_half(out[p][c], k, (unsigned)conv[16 + p * 4 + (k - 4)]);
                }
            }
        }
    }

    for (int p = 0; p < 4; ++p) {
        int pe = mab * 4 + p;
        for (int c = 0; c < 4; ++c) {
            unsigned busw[4];
            for (int i = 0; i < 4; ++i) busw[i] = out[p][c][i];
            if (d.flush_kind != 0) {
                unsigned mf = mask_flags_dev(mask + pe * 16, d.flush_kind, d.flush_entry, d.flush_pattern, c);
                alu_apply_flush(busw, mf, d.flush_ll != 0);
            }
            for (unsigned k = 0; k < d.ndst && k < 8; ++k) {
                alu_write_dst(d.dst[k], pe, c, busw, 0, lm0, lm1, grf0, grf1, mask, t);
            }
            // The CPU model stores the zero-flushed output in the forwarding register too.
            for (int i = 0; i < 4; ++i) aluf[pe * 16 + c * 4 + i] = busw[i];
        }
    }
}

// L2BM transfers. op 0: Distrib L2->L1BM; op 1: Bcast L2->L1BM;
// op 2: FromL1b L1BM->L2BM.
extern "C" __global__ void l2_line(
    unsigned long long* l1bm, unsigned long long* l2bm,
    int op, unsigned a0, unsigned a1, int l1b, int mask) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (op == 0) {
        if (idx >= 8 * 4 * 8 * 8) return;
        int k = idx % 8;
        int b = (idx / 8) % 8;
        int c = (idx / 64) % 4;
        int l2 = idx / (64 * 4);
        if (((mask >> b) & 1) == 0) return;
        int dst = (l2 * 8 + b) * 8192 + (a1 + c * 8 + k) % 8192;
        int src = l2 * 32768 + (a0 + c * 64 + 8 * b + k) % 32768;
        l1bm[dst] = l2bm[src];
    } else if (op == 1) {
        if (idx >= 8 * 4 * 8 * 16) return;
        int k = idx % 16;
        int b = (idx / 16) % 8;
        int c = (idx / 128) % 4;
        int l2 = idx / (128 * 4);
        if (((mask >> b) & 1) == 0) return;
        int dst = (l2 * 8 + b) * 8192 + (a1 + c * 16 + k) % 8192;
        int src = l2 * 32768 + (a0 + c * 16 + k) % 32768;
        l1bm[dst] = l2bm[src];
    } else if (op == 3) {
        if (idx >= 8 * 4 * 8 * 16) return;
        int k = idx % 16;
        int b = (idx / 16) % 8;
        int c = (idx / 128) % 4;
        int l2 = idx / (128 * 4);
        if (((mask >> b) & 1) == 0) return;
        int dst = (l2 * 8 + b) * 8192 + (a1 + c * 16 + k) % 8192;
        int src = l2 * 32768 + (a0 + c * 64 + 16 * (b / 2) + k) % 32768;
        l1bm[dst] = l2bm[src];
    } else if (op == 4) {
        if (idx >= 8 * 4 * 8 * 8) return;
        int k = idx % 8;
        int b = (idx / 8) % 8;
        int c = (idx / 64) % 4;
        int l2 = idx / (64 * 4);
        int src = (l2 * 8 + b) * 8192 + (a0 + c * 8 + k) % 8192;
        int dst = l2 * 32768 + (a1 + c * 64 + 8 * b + k) % 32768;
        l2bm[dst] = l1bm[src];
    } else {
        if (idx >= 8 * 4 * 16) return;
        int k = idx % 16;
        int c = (idx / 16) % 4;
        int l2 = idx / (16 * 4);
        int src = (l2 * 8 + l1b) * 8192 + (a0 + c * 16 + k) % 8192;
        int dst = l2 * 32768 + (a1 + c * 16 + k) % 32768;
        l2bm[dst] = l1bm[src];
    }
}

// RRN reductions (SDM 3.5.5 and 4.2). `kind` is 0 fadd, 1 max, 2 min, 3 iadd,
// 4 band, 5 and, 6 bor, 7 or; `bits` is the element width.
__device__ __forceinline__ unsigned long long rrn_mask(int bits) {
    return bits == 64 ? ~0ULL : ((1ULL << bits) - 1);
}

__device__ __forceinline__ Fmt rrn_fmt(int bits) {
    if (bits == 64) return {11, 52, -1};
    if (bits == 32) return {8, 23, -1};
    return {6, 9, -1};
}

// The identity element sent by L1Bs outside the selected set.
__device__ __forceinline__ unsigned long long rrn_unit(int kind, int bits) {
    unsigned long long m = rrn_mask(bits);
    if (kind == 4) return m;
    if (kind == 5) return 1;
    if (kind == 1) return m;
    if (kind == 2) return m >> 1;
    return 0;
}

// The identity element replicated over a long word.
__device__ __forceinline__ unsigned long long rrn_unit_long(int kind, int bits) {
    unsigned long long u = rrn_unit(kind, bits);
    int lanes = 64 / bits;
    unsigned long long out = 0;
    for (int i = 0; i < lanes; ++i) out |= u << (i * bits);
    return out;
}

// One floating-point addition stage: align every mantissa to the largest
// exponent with round-to-nearest-even, add the signed mantissas exactly, then
// round once to `out` (same steps as rrn::fadd on the CPU).
__device__ __forceinline__ unsigned long long rrn_fadd(
    Fmt f, const unsigned long long* vals, int n, Fmt out) {
    unsigned long long emask = exp_max(f);
    unsigned max_e = 0;
    for (int i = 0; i < n; ++i) {
        unsigned e = (unsigned)((vals[i] >> f.man_bits) & emask);
        if (e > max_e) max_e = e;
    }
    if (max_e == 0) return 0;
    if ((unsigned long long)max_e == emask) {
        bool neg = true;
        for (int i = 0; i < n; ++i) {
            if (((vals[i] >> f.man_bits) & emask) == emask &&
                ((vals[i] >> (width(f) - 1)) & 1) == 0) {
                neg = false;
            }
        }
        return inf_bits(out, neg);
    }
    long long sum = 0;
    for (int i = 0; i < n; ++i) {
        unsigned e = (unsigned)((vals[i] >> f.man_bits) & emask);
        if (e == 0) continue;
        unsigned __int128 sig =
            (((unsigned __int128)1 << f.man_bits) |
             (unsigned __int128)(vals[i] & man_mask(f))) << 3;
        unsigned __int128 aligned = round_shift128(sig, max_e - e);
        bool neg = ((vals[i] >> (width(f) - 1)) & 1) != 0;
        sum += neg ? -(long long)aligned : (long long)aligned;
    }
    if (sum == 0) return 0;
    int e = (int)max_e - (int)bias(f) - (int)f.man_bits - 3;
    unsigned __int128 mag = sum < 0
        ? (unsigned __int128)(-(sum + 1)) + 1
        : (unsigned __int128)sum;
    return round_pack(out, sum < 0, mag, e);
}

// Sign-magnitude comparison key of max/min (SDM 4.2.2).
__device__ __forceinline__ long long rrn_key(unsigned long long v, int bits) {
    unsigned long long m = rrn_mask(bits);
    bool neg = ((v >> (bits - 1)) & 1) != 0;
    unsigned long long mag = v & (m >> 1);
    return neg ? -(long long)mag - 1 : (long long)mag;
}

// One reduction stage over `n` raw elements of the RRN precision. `out_bits`
// is the precision the floating-point addition rounds to (16 for the `r`
// option, otherwise the input precision).
__device__ __forceinline__ unsigned long long rrn_reduce_out(
    int kind, int bits, int out_bits, const unsigned long long* vals, int n) {
    unsigned long long m = rrn_mask(bits);
    if (kind == 0) return rrn_fadd(rrn_fmt(bits), vals, n, rrn_fmt(out_bits));
    if (kind == 1 || kind == 2) {
        long long best = rrn_key(vals[0], bits);
        unsigned long long pick = vals[0];
        for (int i = 1; i < n; ++i) {
            long long k = rrn_key(vals[i], bits);
            if (kind == 1 ? k > best : k < best) {
                best = k;
                pick = vals[i];
            }
        }
        return pick;
    }
    if (kind == 3) {
        unsigned long long acc = 0;
        for (int i = 0; i < n; ++i) acc = (acc + vals[i]) & m;
        return acc;
    }
    if (kind == 4) {
        unsigned long long acc = m;
        for (int i = 0; i < n; ++i) acc &= vals[i];
        return acc;
    }
    if (kind == 5) {
        for (int i = 0; i < n; ++i) {
            if (vals[i] == 0) return 0;
        }
        return 1;
    }
    if (kind == 6) {
        unsigned long long acc = 0;
        for (int i = 0; i < n; ++i) acc |= vals[i];
        return acc;
    }
    for (int i = 0; i < n; ++i) {
        if (vals[i] != 0) return 1;
    }
    return 0;
}

__device__ __forceinline__ unsigned long long rrn_reduce(
    int kind, int bits, const unsigned long long* vals, int n) {
    return rrn_reduce_out(kind, bits, bits, vals, n);
}

// Reduces long words lane by lane in one stage (L2BM reductions).
__device__ __forceinline__ unsigned long long rrn_reduce_longs(
    int kind, int bits, const unsigned long long* vals, int n) {
    int lanes = 64 / bits;
    unsigned long long m = rrn_mask(bits);
    unsigned long long out = 0;
    unsigned long long lane_vals[8];
    for (int lane = 0; lane < lanes; ++lane) {
        int sh = 64 - bits * (lane + 1);
        for (int i = 0; i < n; ++i) lane_vals[i] = (vals[i] >> sh) & m;
        out |= (rrn_reduce(kind, bits, lane_vals, n) & m) << sh;
    }
    return out;
}

// Mask flags of one cycle and PE (SDM 3.6.2). `kind` is 0 none, 1 OMR entry,
// 2 fixed pattern; the layout matches machine.rs.
__device__ __forceinline__ unsigned mask_flags_cycle(
    const unsigned* omr, int pe, int kind, int entry, int pattern, int c) {
    if (kind == 2) return ((pattern >> c) & 1) ? 0xfu : 0u;
    if (kind == 1) {
        if (entry == 0) return 0xfu;
        if (entry <= 15) return (omr[pe * 16 + entry] >> (4 * c)) & 0xfu;
        return ((entry >> (3 - c)) & 1) ? 0xfu : 0u;
    }
    return 0xfu;
}

__device__ __forceinline__ bool word_enabled_cycle(unsigned f, int ll, int i) {
    if (ll) return ((f >> (3 - i)) & 1) != 0;
    if (i < 2) return ((f >> (2 - 2 * i)) & 3) != 0;
    return true;
}

__device__ __forceinline__ unsigned merge_word_cycle(
    unsigned old, unsigned value, unsigned f, int ll, int i) {
    if (!ll && i < 2) {
        unsigned hi = (f >> (3 - 2 * i)) & 1;
        unsigned lo = (f >> (2 - 2 * i)) & 1;
        unsigned m = (hi ? 0xffff0000u : 0u) | (lo ? 0x0000ffffu : 0u);
        return (old & ~m) | (value & m);
    }
    return value;
}

__device__ __forceinline__ void flush_bus(unsigned* bus, unsigned f, int ll) {
    for (int i = 0; i < 4; ++i) {
        if (ll) {
            if (((f >> (3 - i)) & 1) == 0) bus[i] = 0;
        } else if (i < 2) {
            unsigned hi = (f >> (3 - 2 * i)) & 1;
            unsigned lo = (f >> (2 - 2 * i)) & 1;
            unsigned m = (hi ? 0xffff0000u : 0u) | (lo ? 0x0000ffffu : 0u);
            bus[i] &= m;
        }
    }
}

// Reads the four words of a PE operand for one cycle. `base` is the
// per-cycle, already aligned word address.
__device__ __forceinline__ void read_pe_bus(
    unsigned* bus, int mem, unsigned* lm0, unsigned* lm1, unsigned* grf0,
    unsigned* grf1, unsigned* t, int pe, int c, const unsigned* base, int wl) {
    if (mem == 6) {
        for (int i = 0; i < 4; ++i) bus[i] = t[pe * 16 + c * 4 + i];
        return;
    }
    unsigned* p = pick_mem(mem, lm0, lm1, grf0, grf1);
    int l = mem_len(mem);
    for (int i = 0; i < 4; ++i) {
        bus[i] = (i < wl) ? p[pe * l + base[c] + i] : 0;
    }
}

// Writes one PE operand for one cycle under a resolved mask.
__device__ __forceinline__ void write_pe_bus(
    unsigned* lm0, unsigned* lm1, unsigned* grf0, unsigned* grf1, unsigned* t,
    int mem, int pe, int c, unsigned base, int wl, const unsigned* bus,
    unsigned flags, int ll, int kind) {
    if (kind == 0) {
        if (mem == 6) {
            for (int i = 0; i < 4; ++i) t[pe * 16 + c * 4 + i] = bus[i];
        } else {
            unsigned* p = pick_mem(mem, lm0, lm1, grf0, grf1);
            int l = mem_len(mem);
            for (int i = 0; i < wl; ++i) p[pe * l + base + i] = bus[i];
        }
        return;
    }
    unsigned* p = (mem == 6) ? t : pick_mem(mem, lm0, lm1, grf0, grf1);
    int l = (mem == 6) ? 16 : mem_len(mem);
    int off = (mem == 6) ? c * 4 : (int)base;
    int words = (mem == 6) ? 4 : wl;
    for (int i = 0; i < words; ++i) {
        if (!word_enabled_cycle(flags, ll, i)) continue;
        unsigned old = p[pe * l + off + i];
        p[pe * l + off + i] = merge_word_cycle(old, bus[i], flags, ll, i);
    }
}

__device__ __forceinline__ unsigned long long bus_long(const unsigned* bus, int k) {
    return ((unsigned long long)bus[2 * k] << 32) | bus[2 * k + 1];
}

// A half long word as four singles (SDM 3.6.8.4). Decoding zero always yields
// a positive zero, like float::encode(SINGLE, decode(HALF, ..)) on the CPU.
__device__ __forceinline__ void extend_half_long(
    unsigned long long msb, unsigned long long* out) {
    unsigned s[4];
    for (int j = 0; j < 4; ++j) {
        unsigned h = (unsigned)((msb >> (48 - 16 * j)) & 0xffffu);
        unsigned sign = (h >> 15) & 1;
        unsigned e = (h >> 9) & 0x3f;
        unsigned man = h & 0x1ff;
        if (e == 0) {
            s[j] = 0;
        } else if (e == 63) {
            s[j] = (sign << 31) | (0xffu << 23);
        } else {
            s[j] = (sign << 31) | ((e + 96) << 23) | (man << 14);
        }
    }
    out[0] = ((unsigned long long)s[0] << 32) | s[1];
    out[1] = ((unsigned long long)s[2] << 32) | s[3];
}

// Packs four 16-bit results of a rounding reduction into one long word, in
// the order measured with the emulator (CPU: pe_to_l1's rounded branch).
__device__ __forceinline__ unsigned long long pack_rounded(
    unsigned long long r0, unsigned long long r1) {
    unsigned long long v = 0;
    for (int j = 0; j < 4; ++j) {
        unsigned long long l = (j < 2) ? r0 : r1;
        unsigned long long h = (l >> (32 - 32 * (j & 1))) & 0xffffu;
        v = (v << 16) | h;
    }
    return v;
}

// One L1BM-to-PE read: op 0 Mbcast, 1 Distrib, 2 Pbcast, 3 M4bcast.
// `has_addr` says whether the L1BM operand is an address (else $lbi).
extern "C" __global__ void l1_read_line(
    unsigned* lm0, unsigned* lm1, unsigned* grf0, unsigned* grf1, unsigned* t,
    unsigned long long* l1bm, unsigned long long* lbi, unsigned* omr,
    int op, int has_addr, unsigned addr, int mabdiff, int wl, int ndst,
    int dm0, unsigned d00, unsigned d01, unsigned d02, unsigned d03, int dw0,
    int mk0, int mke0, int mkp0, int mkl0,
    int dm1, unsigned d10, unsigned d11, unsigned d12, unsigned d13, int dw1,
    int mk1, int mke1, int mkp1, int mkl1,
    int dm2, unsigned d20, unsigned d21, unsigned d22, unsigned d23, int dw2,
    int mk2, int mke2, int mkp2, int mkl2,
    int dm3, unsigned d30, unsigned d31, unsigned d32, unsigned d33, int dw3,
    int mk3, int mke3, int mkp3, int mkl3,
    int fk, int fe, int fp, int fll) {
    int pe = blockIdx.x * blockDim.x + threadIdx.x;
    if (pe >= 4096) return;
    int l1b = pe >> 6;
    int mab = (pe >> 2) & 15;
    int sub = pe & 3;
    int dm[4] = {dm0, dm1, dm2, dm3};
    unsigned db[4][4] = {
        {d00, d01, d02, d03},
        {d10, d11, d12, d13},
        {d20, d21, d22, d23},
        {d30, d31, d32, d33},
    };
    int dw[4] = {dw0, dw1, dw2, dw3};
    int mk[4] = {mk0, mk1, mk2, mk3};
    int mke[4] = {mke0, mke1, mke2, mke3};
    int mkp[4] = {mkp0, mkp1, mkp2, mkp3};
    int mkl[4] = {mkl0, mkl1, mkl2, mkl3};
    int base_l1 = l1b * 8192;
    for (int c = 0; c < 4; ++c) {
        unsigned om;
        unsigned ol = 0;
        bool has_ol = false;
        if (op == 2) {
            // Pbcast: addr + cycle, and the next long word for two long words.
            om = has_addr ? (unsigned)c : 0u;
            if (wl == 4) {
                ol = om + 4;
                has_ol = true;
            }
        } else if (op == 0) {
            // Mbcast: four MAB lanes; from $lbi even a one long word read has
            // the second long word at 4 + sub (CPU blocks.rs).
            if (wl == 4) {
                unsigned b = has_addr ? (unsigned)(c * 8) : 0u;
                om = b + (unsigned)sub;
                ol = om + 4;
                has_ol = true;
            } else if (!has_addr) {
                om = (unsigned)sub;
                ol = (unsigned)(4 + sub);
                has_ol = true;
            } else {
                om = (unsigned)(c * 4) + (unsigned)sub;
            }
        } else if (op == 3) {
            // M4bcast: [[4 (MAB high bits)][2 (long word)][4 (PE)]].
            int i = mab >> 2;
            if (wl == 4) {
                unsigned b = has_addr ? (unsigned)(c * 32) : 0u;
                om = b + (unsigned)(i * 8) + (unsigned)sub;
                ol = om + 4;
                has_ol = true;
            } else {
                unsigned b = has_addr ? (unsigned)(c * 16) : 0u;
                om = b + (unsigned)(i * 4) + (unsigned)sub;
            }
        } else {
            // Distrib: the source MAB is shifted by -mabdiff.
            int sm = (mab - mabdiff) % 16;
            if (sm < 0) sm += 16;
            unsigned b = has_addr ? (unsigned)(c * 64) : 0u;
            om = b + (unsigned)(sm * 4) + (unsigned)sub;
        }
        unsigned long long m;
        unsigned long long l = 0;
        if (has_addr) {
            m = l1bm[base_l1 + (int)(((unsigned long long)addr + om) % 8192)];
            if (has_ol) {
                l = l1bm[base_l1 + (int)(((unsigned long long)addr + ol) % 8192)];
            }
        } else {
            int b = (l1b * 4 + c) * 64;
            m = lbi[b + (int)(om % 64)];
            if (has_ol) l = lbi[b + (int)(ol % 64)];
        }
        unsigned bus[4] = {
            (unsigned)(m >> 32),
            (unsigned)m,
            (unsigned)(l >> 32),
            (unsigned)l,
        };
        if (fk != 0) {
            unsigned f = mask_flags_cycle(omr, pe, fk, fe, fp, c);
            flush_bus(bus, f, fll);
        }
        for (int d = 0; d < ndst; ++d) {
            unsigned f = 0;
            if (mk[d] != 0) {
                f = mask_flags_cycle(omr, pe, mk[d], mke[d], mkp[d], c);
            }
            write_pe_bus(
                lm0, lm1, grf0, grf1, t, dm[d], pe, c, db[d][c], dw[d], bus,
                f, mkl[d], mk[d]);
        }
    }
}

// One PE-to-L1BM transfer. op 0 Mwrite, 1 Gather, 2 M4write, 3 Reduce
// (16x1), 4 Reduce4 (4x4). `has_addr` selects L1BM or the turnaround
// register $lbi as the destination; the turnaround is updated either way.
extern "C" __global__ void l1_write_line(
    unsigned* lm0, unsigned* lm1, unsigned* grf0, unsigned* grf1, unsigned* t,
    unsigned long long* l1bm, unsigned long long* lbi,
    int op, int mab_sel, int mabdiff, int has_addr, unsigned addr, int dwl,
    int smem, unsigned s0, unsigned s1, unsigned s2, unsigned s3, int swl,
    int two_src, int bits, int rrn, int round_it, int ext) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx >= 256) return;
    int l1b = idx >> 2;
    int sub = idx & 3;
    int base_l1 = l1b * 8192;
    int lbi_base = l1b * 4 * 64;
    unsigned sb[4] = {s0, s1, s2, s3};
    int red_longs;
    if (round_it) {
        red_longs = (dwl == 4 || two_src || ext) ? 2 : 1;
    } else {
        red_longs = (dwl == 4 || ext) ? 2 : 1;
    }
    for (int c = 0; c < 4; ++c) {
        if (op == 0) {
            int pe = l1b * 64 + mab_sel * 4 + sub;
            unsigned bus[4];
            read_pe_bus(bus, smem, lm0, lm1, grf0, grf1, t, pe, c, sb, swl);
            unsigned long long v0 = bus_long(bus, 0);
            int step = (dwl == 4) ? 8 : 4;
            unsigned off = (unsigned)sub;
            if (has_addr) {
                l1bm[base_l1 + (int)(((unsigned long long)addr + (unsigned long long)(c * step) + off) % 8192)] = v0;
            }
            lbi[lbi_base + c * 64 + (int)off] = v0;
            if (dwl == 4) {
                unsigned long long v1 = bus_long(bus, 1);
                if (has_addr) {
                    l1bm[base_l1 + (int)(((unsigned long long)addr + (unsigned long long)(c * step) + off + 4) % 8192)] = v1;
                }
                lbi[lbi_base + c * 64 + (int)off + 4] = v1;
            }
        } else if (op == 1) {
            for (int m = 0; m < 16; ++m) {
                int pe = l1b * 64 + m * 4 + sub;
                unsigned bus[4];
                read_pe_bus(bus, smem, lm0, lm1, grf0, grf1, t, pe, c, sb, swl);
                unsigned long long v = bus_long(bus, 0);
                int dst_mab = (m + mabdiff) % 16;
                if (dst_mab < 0) dst_mab += 16;
                unsigned off = (unsigned)(dst_mab * 4 + sub);
                if (has_addr) {
                    l1bm[base_l1 + (int)(((unsigned long long)addr + (unsigned long long)(c * 64) + off) % 8192)] = v;
                }
                lbi[lbi_base + c * 64 + m * 4 + sub] = v;
            }
        } else if (op == 2) {
            int step = (dwl == 4) ? 32 : 16;
            for (int mo = 0; mo < 4; ++mo) {
                int mab = mo * 4 + mab_sel;
                int pe = l1b * 64 + mab * 4 + sub;
                unsigned bus[4];
                read_pe_bus(bus, smem, lm0, lm1, grf0, grf1, t, pe, c, sb, swl);
                unsigned long long v0 = bus_long(bus, 0);
                unsigned off0 = (dwl == 4) ? (unsigned)(mo * 8 + sub)
                                           : (unsigned)(mo * 4 + sub);
                if (has_addr) {
                    l1bm[base_l1 + (int)(((unsigned long long)addr + (unsigned long long)(c * step) + off0) % 8192)] = v0;
                }
                lbi[lbi_base + c * 64 + (int)off0] = v0;
                if (dwl == 4) {
                    unsigned long long v1 = bus_long(bus, 1);
                    unsigned off1 = off0 + 4;
                    if (has_addr) {
                        l1bm[base_l1 + (int)(((unsigned long long)addr + (unsigned long long)(c * step) + off1) % 8192)] = v1;
                    }
                    lbi[lbi_base + c * 64 + (int)off1] = v1;
                }
            }
        } else {
            int four = (op == 4);
            int groups = four ? 4 : 1;
            int n = four ? 4 : 16;
            int step;
            if (round_it) step = four ? 16 : 4;
            else if (ext) step = four ? 32 : 8;
            else if (dwl == 4) step = four ? 32 : 8;
            else step = four ? 16 : 4;
            for (int g = 0; g < groups; ++g) {
                unsigned long long v0[16];
                unsigned long long v1[16];
                for (int m = 0; m < n; ++m) {
                    int mab = four ? g * 4 + m : m;
                    int pe = l1b * 64 + mab * 4 + sub;
                    unsigned bus[4];
                    read_pe_bus(bus, smem, lm0, lm1, grf0, grf1, t, pe, c, sb, swl);
                    v0[m] = bus_long(bus, 0);
                    v1[m] = bus_long(bus, 1);
                    if (ext) {
                        unsigned long long e[2];
                        extend_half_long(v0[m], e);
                        v0[m] = e[0];
                        v1[m] = e[1];
                    }
                }
                unsigned long long res[2] = {0, 0};
                int lanes = 64 / bits;
                unsigned long long mask = rrn_mask(bits);
                for (int k = 0; k < red_longs; ++k) {
                    unsigned long long r = 0;
                    for (int lane = 0; lane < lanes; ++lane) {
                        int sh = 64 - bits * (lane + 1);
                        unsigned long long lv[16];
                        for (int m = 0; m < n; ++m) {
                            unsigned long long lw = (k == 0) ? v0[m] : v1[m];
                            lv[m] = (lw >> sh) & mask;
                        }
                        unsigned long long rr;
                        if (four) {
                            rr = rrn_reduce_out(rrn, bits, round_it ? 16 : bits, lv, 4);
                        } else {
                            unsigned long long st[4];
                            for (int q = 0; q < 4; ++q) {
                                st[q] = rrn_reduce_out(rrn, bits, bits, lv + 4 * q, 4);
                            }
                            rr = rrn_reduce_out(rrn, bits, round_it ? 16 : bits, st, 4);
                        }
                        r |= (rr & mask) << sh;
                    }
                    res[k] = r;
                }
                unsigned off;
                if (round_it) {
                    off = (unsigned)((four ? g * 4 : 0) + sub);
                    unsigned long long v = pack_rounded(res[0], red_longs > 1 ? res[1] : 0);
                    if (has_addr) {
                        l1bm[base_l1 + (int)(((unsigned long long)addr + (unsigned long long)(c * step) + off) % 8192)] = v;
                    }
                    lbi[lbi_base + c * 64 + (int)off] = v;
                } else {
                    // With `e` the CPU writes both reduced long words even to a
                    // one long word destination (blocks.rs ext branch).
                    if (dwl == 4 || ext) {
                        off = (unsigned)((four ? g * 8 : 0) + sub);
                        if (has_addr) {
                            l1bm[base_l1 + (int)(((unsigned long long)addr + (unsigned long long)(c * step) + off) % 8192)] = res[0];
                            l1bm[base_l1 + (int)(((unsigned long long)addr + (unsigned long long)(c * step) + off + 4) % 8192)] = res[1];
                        }
                        lbi[lbi_base + c * 64 + (int)off] = res[0];
                        lbi[lbi_base + c * 64 + (int)off + 4] = res[1];
                    } else {
                        off = (unsigned)((four ? g * 4 : 0) + sub);
                        if (has_addr) {
                            l1bm[base_l1 + (int)(((unsigned long long)addr + (unsigned long long)(c * step) + off) % 8192)] = res[0];
                        }
                        lbi[lbi_base + c * 64 + (int)off] = res[0];
                    }
                }
            }
        }
    }
}

// L2BM reductions and internal multicast. op 0: l2bmr (Reduce), op 1: l2bmr2
// (Reduce2), op 2: l2bmi (Imcast). `mask`/`immode` are the L1B set.
extern "C" __global__ void l2_reduce_line(
    unsigned long long* l1bm, unsigned long long* l2bm,
    int op, unsigned a0, unsigned a1, int mask, int immode, int bits, int kind) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (op == 0) {
        if (idx >= 8 * 4 * 16) return;
        int k = idx % 16;
        int c = (idx / 16) % 4;
        int l2 = idx / 64;
        unsigned long long vals[8];
        for (int b = 0; b < 8; ++b) {
            vals[b] = ((mask >> b) & 1)
                ? l1bm[(l2 * 8 + b) * 8192 + (a0 + c * 16 + k) % 8192]
                : rrn_unit_long(kind, bits);
        }
        l2bm[l2 * 32768 + (a1 + c * 16 + k) % 32768] =
            rrn_reduce_longs(kind, bits, vals, 8);
    } else if (op == 1) {
        if (idx >= 8 * 4 * 4 * 16) return;
        int k = idx % 16;
        int g = (idx / 16) % 4;
        int c = (idx / 64) % 4;
        int l2 = idx / 256;
        unsigned long long vals[2];
        for (int j = 0; j < 2; ++j) {
            vals[j] = l1bm[(l2 * 8 + 2 * g + j) * 8192 +
                           (a0 + c * 16 + k) % 8192];
        }
        l2bm[l2 * 32768 + (a1 + c * 64 + 16 * g + k) % 32768] =
            rrn_reduce_longs(kind, bits, vals, 2);
    } else {
        // One thread per destination L1B and word. The last source in the set
        // with the same immode group wins, matching the CPU's write order.
        if (idx >= 8 * 4 * 8 * 16) return;
        int k = idx % 16;
        int d = (idx / 16) % 8;
        int c = (idx / 128) % 4;
        int l2 = idx / 512;
        int src = -1;
        for (int s = 7; s >= 0; --s) {
            if (s == d || !((mask >> s) & 1)) continue;
            if ((s & immode) == (d & immode)) {
                src = s;
                break;
            }
        }
        if (src < 0) return;
        l1bm[(l2 * 8 + d) * 8192 + (a1 + c * 16 + k) % 8192] =
            l1bm[(l2 * 8 + src) * 8192 + (a0 + c * 16 + k) % 8192];
    }
}

// ---- matrix unit ------------------------------------------------------------------------

__device__ __forceinline__ unsigned long long encode_bits(Fmt f, Val v) {
    if (v.kind == 0) return 0;
    if (v.kind == 1) return inf_bits(f, v.neg);
    return round_pack(f, v.neg, v.sig, v.exp);
}

// Exact dot product of one block-float row and one block-float vector, ported
// from float::bf_dot for single precision with 18 (pseudo-single) or 23 (full)
// mantissa bits. `has_grid` is clear only for the zero and infinity results.
__device__ Val bf_dot_single(
    const unsigned long long* a, const unsigned long long* b, int n, int bf_m,
    int* has_grid, int* grid) {
    const int man_bits = 23;
    const int emax = 255;
    const int bias = 127;
    *has_grid = 0;
    *grid = 0;
    unsigned ca = 0;
    unsigned cb = 0;
    for (int i = 0; i < n; ++i) {
        unsigned ea = ((unsigned)(a[i] >> man_bits)) & emax;
        unsigned eb = ((unsigned)(b[i] >> man_bits)) & emax;
        if (ea > ca) ca = ea;
        if (eb > cb) cb = eb;
    }
    if (ca == 0 || cb == 0) return {0, false, 0, 0};
    if (ca == emax || cb == emax) return {1, false, 0, 0};
    int low = (bf_m == man_bits) ? 41 : 36;
    *has_grid = 1;
    *grid = (int)ca + (int)cb - 2 * bias + 2 - low;
    bool negs[16];
    unsigned __int128 terms[16];
    int exps[16];
    int count = 0;
    for (int i = 0; i < n; ++i) {
        unsigned ma = (unsigned)(a[i] & 0x7fffffu) >> (man_bits - bf_m);
        unsigned mb = (unsigned)(b[i] & 0x7fffffu) >> (man_bits - bf_m);
        if (ma == 0 || mb == 0) continue;
        unsigned ea = ((unsigned)(a[i] >> man_bits)) & emax;
        unsigned eb = ((unsigned)(b[i] >> man_bits)) & emax;
        if (ea == 0) ea = ca > 6 ? ca - 6 : 0;
        if (eb == 0) eb = cb > 6 ? cb - 6 : 0;
        unsigned __int128 p = (unsigned __int128)ma * (unsigned __int128)mb;
        if (bf_m == man_bits) {
            unsigned low_mask = 31;
            unsigned dropped = (ma & low_mask) * (mb & low_mask);
            if (dropped != 0) {
                p = p - (unsigned __int128)dropped + (((unsigned __int128)1) << 8);
            }
        }
        negs[count] = (((a[i] ^ b[i]) >> 31) & 1) != 0;
        terms[count] = p;
        exps[count] = (int)ea + (int)eb - 2 * bias - 2 * (bf_m - 1);
        ++count;
    }
    if (count == 0) return {0, false, 0, 0};
    int min_e = exps[0];
    for (int i = 1; i < count; ++i) {
        if (exps[i] < min_e) min_e = exps[i];
    }
    bool exact = true;
    __int128 total = 0;
    for (int i = 0; i < count; ++i) {
        int sh = exps[i] - min_e;
        if (sh > 16 || lz128(terms[i]) < (unsigned)(sh + 4)) {
            exact = false;
            break;
        }
        __int128 v = (__int128)(terms[i] << sh);
        total += negs[i] ? -v : v;
    }
    if (exact) {
        if (total == 0) return {0, false, 0, 0};
        bool neg = total < 0;
        unsigned __int128 sig = (unsigned __int128)(neg ? -total : total);
        return {2, neg, sig, min_e};
    }
    Val acc = {0, false, 0, 0};
    for (int i = 0; i < count; ++i) {
        acc = add_exact(acc, {2, negs[i], terms[i], exps[i]});
    }
    return acc;
}

// float::mat_fma for a single-precision output: align c to the adder grid, add
// the exact dot product, and round once.
__device__ __forceinline__ unsigned long long mat_fma_bits(
    Val dot, int has_grid, int grid, Val c) {
    Fmt f = {8, 23, 18};
    Val cc = has_grid ? align_c(c, grid) : c;
    return encode_bits(f, add_exact(dot, cc));
}

// ---- matrix unit ------------------------------------------------------------------------

// One matrix-register write (fmwrite/gmwrite). Each thread handles one MAB and
// one cycle: the four PEs supply two f32 elements each, which become the eight
// words of one physical row of the selected face.
extern "C" __global__ void mat_write_line(
    unsigned* lm0, unsigned* lm1, unsigned* grf0, unsigned* grf1,
    unsigned* mauf, unsigned* aluf, unsigned* mats,
    int prec, int side, unsigned addr, int smem,
    unsigned s0, unsigned s1, unsigned s2, unsigned s3, int swl, int sneg) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx >= 4096) return;
    int mab = idx >> 2;
    int c = idx & 3;
    unsigned sb[4] = {s0, s1, s2, s3};
    if (prec == 1) {
        unsigned* p = pick_mem(smem, lm0, lm1, grf0, grf1);
        int l = mem_len(smem);
        for (int q = 0; q < 4; ++q) {
            int pe = mab * 4 + q;
            unsigned w0 = 0, w1 = 0;
            if (smem == 4) {
                w0 = mauf[pe * 16 + c * 4];
                w1 = mauf[pe * 16 + c * 4 + 1];
            } else if (smem == 5) {
                w0 = aluf[pe * 16 + c * 4];
                w1 = aluf[pe * 16 + c * 4 + 1];
            } else {
                if (swl > 0) w0 = p[pe * l + sb[c]];
                if (swl > 1) w1 = p[pe * l + sb[c] + 1];
            }
            unsigned long long v = ((unsigned long long)w0 << 32) | w1;
            if (sneg) v ^= (1ULL << 63);
            int row = (int)((addr + (unsigned)c) % 4u);
            int base = ((mab * 2 + side) * 16 + row * 4) * 8;
            mats[base + 2 * q] = (unsigned)(v >> 32);
            mats[base + 2 * q + 1] = (unsigned)v;
        }
        return;
    }
    unsigned* ps = pick_mem(smem, lm0, lm1, grf0, grf1);
    int ls = mem_len(smem);
    unsigned vals[8];
    for (int p = 0; p < 4; ++p) {
        int pe = mab * 4 + p;
        for (int i = 0; i < 2; ++i) {
            unsigned v;
            if (smem == 4) {
                v = mauf[pe * 16 + c * 4 + i];
            } else if (smem == 5) {
                v = aluf[pe * 16 + c * 4 + i];
            } else {
                v = (i < swl) ? ps[pe * ls + sb[c] + i] : 0;
            }
            if (sneg) v ^= 0x80000000u;
            vals[p * 2 + i] = v;
        }
    }
    int row = (int)((addr + (unsigned)c) % 8u);
    int base = ((mab * 2 + side) * 16 + row * 2) * 8;
    for (int j = 0; j < 8; ++j) {
        mats[base + j] = vals[j];
    }
}

// One matrix-register read (fmread/gmread). Each thread handles one PE: the
// elements of logical rows 2p and 2p+1 (physical rows 4p and 4p+2) form the two
// f32 lanes of the bus, which goes to the destination and to mreadf.
extern "C" __global__ void mat_read_line(
    unsigned* lm0, unsigned* lm1, unsigned* grf0, unsigned* grf1,
    unsigned* mreadf, unsigned* mats,
    int prec, int side, unsigned addr, int dmem,
    unsigned d0, unsigned d1, unsigned d2, unsigned d3, int dwl) {
    int pe = blockIdx.x * blockDim.x + threadIdx.x;
    if (pe >= 4096) return;
    int mab = pe >> 2;
    int p = pe & 3;
    unsigned db[4] = {d0, d1, d2, d3};
    unsigned* pd = pick_mem(dmem, lm0, lm1, grf0, grf1);
    int ld = mem_len(dmem);
    int base = (mab * 2 + side) * 16 * 8;
    for (int c = 0; c < 4; ++c) {
        int col = (int)((addr + (unsigned)c) % (prec == 1 ? 4u : 8u));
        unsigned bus[4];
        if (prec == 1) {
            int word = base + p * 4 * 8 + col * 2;
            bus[0] = mats[word];
            bus[1] = mats[word + 1];
            bus[2] = 0;
            bus[3] = 0;
        } else {
            bus[0] = mats[base + (4 * p) * 8 + col];
            bus[1] = mats[base + (4 * p + 2) * 8 + col];
            bus[2] = 0;
            bus[3] = 0;
        }
        for (int i = 0; i < dwl; ++i) {
            pd[pe * ld + db[c] + i] = bus[i];
        }
        for (int i = 0; i < 4; ++i) {
            mreadf[pe * 16 + c * 4 + i] = bus[i];
        }
    }
}

// One matrix MAU line. Each thread handles one MAB: it reads all four cycles'
// x and y vectors first, matching the CPU (which computes the whole line before
// writing), then computes the eight rows of each cycle as a block-float dot
// product plus the y element, rounded once. Results go to the destination and
// to mauf.
extern "C" __global__ void mat_mau_line(
    unsigned* lm0, unsigned* lm1, unsigned* grf0, unsigned* grf1,
    unsigned* mauf, unsigned* aluf, unsigned* mats,
    int prec, int side, int kind,
    int xmem, unsigned x0, unsigned x1, unsigned x2, unsigned x3, int xwl, int xneg,
    int ymem, unsigned y0, unsigned y1, unsigned y2, unsigned y3, int ywl, int yneg,
    int dmem, unsigned d0, unsigned d1, unsigned d2, unsigned d3, int dwl) {
    int mab = blockIdx.x * blockDim.x + threadIdx.x;
    if (mab >= 1024) return;
    int nx = (prec == 0) ? 1 : 2;
    int ny = 2;
    int bf_m = (prec == 0) ? 23 : 18;
    unsigned xb[4] = {x0, x1, x2, x3};
    unsigned yb[4] = {y0, y1, y2, y3};
    unsigned* px = pick_mem(xmem, lm0, lm1, grf0, grf1);
    unsigned* py = pick_mem(ymem, lm0, lm1, grf0, grf1);
    int lx = mem_len(xmem);
    int ly = mem_len(ymem);
    unsigned long long xv[4][8];
    unsigned long long yv[4][8];
    for (int c = 0; c < 4; ++c) {
        for (int p = 0; p < 4; ++p) {
            int pe = mab * 4 + p;
            for (int i = 0; i < nx; ++i) {
                unsigned v;
                if (xmem == 4) {
                    v = mauf[pe * 16 + c * 4 + i];
                } else if (xmem == 5) {
                    v = aluf[pe * 16 + c * 4 + i];
                } else {
                    v = (i < xwl) ? px[pe * lx + xb[c] + i] : 0;
                }
                if (xneg) v ^= 0x80000000u;
                xv[c][p * nx + i] = v;
            }
            for (int i = 0; i < ny; ++i) {
                unsigned v = 0;
                if (kind == 0) {
                    if (ymem == 4) {
                        v = mauf[pe * 16 + c * 4 + i];
                    } else if (ymem == 5) {
                        v = aluf[pe * 16 + c * 4 + i];
                    } else {
                        v = (i < ywl) ? py[pe * ly + yb[c] + i] : 0;
                    }
                    if (yneg) v ^= 0x80000000u;
                }
                yv[c][p * ny + i] = v;
            }
        }
    }
    Fmt f = {8, 23, 18};
    int cols = (prec == 0) ? 4 : 8;
    int base = (mab * 2 + side) * 16 * 8;
    unsigned db[4] = {d0, d1, d2, d3};
    unsigned* pd = pick_mem(dmem, lm0, lm1, grf0, grf1);
    int ld = mem_len(dmem);
    for (int c = 0; c < 4; ++c) {
        unsigned out[8];
        for (int i = 0; i < 8; ++i) {
            unsigned long long arow[8];
            for (int j = 0; j < cols; ++j) {
                int col = (prec == 0) ? 2 * j : j;
                arow[j] = mats[base + (i * 2) * 8 + col];
            }
            int has_grid;
            int grid;
            Val dot = bf_dot_single(arow, xv[c], cols, bf_m, &has_grid, &grid);
            Val yval = (kind == 0) ? decode(f, yv[c][i]) : Val{0, false, 0, 0};
            out[i] = (unsigned)mat_fma_bits(dot, has_grid, grid, yval);
        }
        for (int p = 0; p < 4; ++p) {
            int pe = mab * 4 + p;
            unsigned bus[4] = {out[2 * p], out[2 * p + 1], 0, 0};
            if (dmem < 4) {
                for (int i = 0; i < dwl; ++i) {
                    pd[pe * ld + db[c] + i] = bus[i];
                }
            }
            for (int i = 0; i < 4; ++i) {
                mauf[pe * 16 + c * 4 + i] = bus[i];
            }
        }
    }
}
