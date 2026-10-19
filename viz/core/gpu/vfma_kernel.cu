
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
// before writing, and processes two lanes (wl = 2). Masks, forwarding and
// the neg/ext/rnd options are not part of this kernel yet.
extern "C" __global__ void mau_line(
    unsigned* lm0, unsigned* lm1, unsigned* grf0, unsigned* grf1,
    unsigned* mauf,
    int kind, int wl,
    int amem, unsigned a0, unsigned a1, unsigned a2, unsigned a3,
    int bmem, unsigned b0, unsigned b1, unsigned b2, unsigned b3,
    int cmem, unsigned c0, unsigned c1, unsigned c2, unsigned c3,
    int dmem, unsigned d0, unsigned d1, unsigned d2, unsigned d3) {
    int pe = blockIdx.x * blockDim.x + threadIdx.x;
    if (pe >= 4096 || (wl != 1 && wl != 2)) return;
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
        for (int l = 0; l < wl; ++l) {
            unsigned av = (amem == 4)
                ? mauf[pe * 16 + c * 4 + l]
                : pa[pe * la + ab[c] + l];
            unsigned bv;
            unsigned cv;
            if (kind == 0) {
                bv = (bmem == 4)
                    ? mauf[pe * 16 + c * 4 + l]
                    : pb[pe * lb + bb[c] + l];
                cv = (cmem == 4)
                    ? mauf[pe * 16 + c * 4 + l]
                    : pc[pe * lc + cb[c] + l];
            } else if (kind == 1) {
                bv = (bmem == 4)
                    ? mauf[pe * 16 + c * 4 + l]
                    : pb[pe * lb + bb[c] + l];
                cv = 0;
            } else if (kind == 2) {
                bv = one;
                cv = (cmem == 4)
                    ? mauf[pe * 16 + c * 4 + l]
                    : pc[pe * lc + cb[c] + l];
            } else {
                bv = one;
                cv = 0;
            }
            values[c][l] = (unsigned)vfma_bits(f, f, av, bv, cv);
        }
    }
    for (int c = 0; c < 4; ++c) {
        for (int l = 0; l < wl; ++l) {
            pd[pe * ld + db[c] + l] = values[c][l];
        }
        mauf[pe * 16 + c * 4] = values[c][0];
        mauf[pe * 16 + c * 4 + 1] = (wl == 2) ? values[c][1] : 0;
        mauf[pe * 16 + c * 4 + 2] = 0;
        mauf[pe * 16 + c * 4 + 3] = 0;
    }
}
