
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
    int omr, int tdst, unsigned imm, int imm_u,
    int mask_kind, int mask_entry, int mask_pattern, int mask_ll) {
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
            } else if (amem == 9) {
                av[i] = (unsigned)(pe & 3);
            } else if (amem == 10) {
                av[i] = (i & 1) ? (unsigned)(pe & 3) : 0;
            } else {
                av[i] = (i < awl) ? pa[pe * la + ab[c] + i] : 0;
            }
            if (bmem == 4) {
                bv[i] = mauf[pe * 16 + c * 4 + i];
            } else if (bmem == 5) {
                bv[i] = aluf[pe * 16 + c * 4 + i];
            } else if (bmem == 6) {
                bv[i] = t[pe * 16 + c * 4 + i];
            } else if (bmem == 9) {
                bv[i] = (unsigned)(pe & 3);
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
        } else if (kind == 7) {
            unsigned r0 = av[0] + bv[0];
            unsigned r1 = av[1] + bv[1];
            out[0] = r0; out[1] = r1; out[2] = av[2]; out[3] = av[3];
            flags = (((int)r0 >= 0) ? 0xc : 0) | (((int)r1 >= 0) ? 0x3 : 0);
        } else if (kind == 8) {
            for (int l = 0; l < 2; ++l) {
                unsigned shift = bv[l] % 64;
                out[l] = (shift >= 32) ? 0 : (av[l] << shift);
            }
            out[2] = av[2]; out[3] = av[3];
            flags = ((out[0] == 0) ? 0xc : 0) | ((out[1] == 0) ? 0x3 : 0);
        } else if (kind == 9) {
            for (int l = 0; l < 2; ++l) {
                out[l] = ((av[l] >> 31) == 0) ? bv[l] : 0x80000000u;
            }
            out[2] = av[2]; out[3] = av[3];
            flags = (((av[0] >> 31) == 0) ? 0xc : 0) | (((av[1] >> 31) == 0) ? 0x3 : 0);
        } else if (kind == 10) {
            Fmt f = {8, 23, 18};
            for (int l = 0; l < 2; ++l) {
                unsigned v = av[l];
                Val x = decode(f, v);
                if (x.kind != 2 || x.exp >= 0) {
                    out[l] = v;
                    continue;
                }
                unsigned sh = (unsigned)(-x.exp);
                unsigned __int128 sig = x.sig;
                unsigned __int128 iv = (sh >= 128) ? 0 : (sig >> sh);
                bool frac = sh >= 128 || (sig & ((((unsigned __int128)1) << sh) - 1)) != 0;
                if (x.neg && frac) iv += 1;
                if (iv == 0) {
                    out[l] = x.neg ? (1u << 31) : 0;
                } else {
                    out[l] = (unsigned)round_pack(f, x.neg, iv, 0);
                }
            }
            out[2] = av[2]; out[3] = av[3];
            flags = 0;
        } else if (kind == 11) {
            Fmt f = {8, 23, 18};
            for (int l = 0; l < 2; ++l) {
                Val x = decode(f, av[l]);
                long long r;
                if (x.kind == 0) {
                    r = 0;
                } else if (x.kind == 1) {
                    r = x.neg ? (-2147483647LL - 1) : 2147483647LL;
                } else {
                    unsigned __int128 mag;
                    if (x.exp >= 0) {
                        mag = (x.exp > 70) ? (((unsigned __int128)1) << 127) : (x.sig << x.exp);
                    } else if (-x.exp >= 127) {
                        mag = 0;
                    } else {
                        mag = x.sig >> (unsigned)(-x.exp);
                    }
                    if (x.neg) {
                        long long s = (mag > (unsigned __int128)2147483648ULL)
                            ? (-2147483647LL - 1)
                            : -(long long)(unsigned long long)mag;
                        r = s;
                    } else {
                        r = (mag > (unsigned __int128)2147483647ULL)
                            ? 2147483647LL
                            : (long long)(unsigned long long)mag;
                    }
                }
                out[l] = (unsigned)r;
            }
            out[2] = av[2]; out[3] = av[3];
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
            unsigned flags = 0xf;
            if (mask_kind == 1) {
                flags = (mask_entry >= 1 && mask_entry <= 15)
                    ? ((mask[pe * 16 + mask_entry] >> (4 * c)) & 0xf)
                    : (((mask_entry >> (3 - c)) & 1) ? 0xf : 0);
            } else if (mask_kind == 2) {
                flags = ((mask_pattern >> c) & 1) ? 0xf : 0;
            }
            for (int i = 0; i < dwl; ++i) {
                int enabled;
                if (mask_kind == 0) {
                    enabled = 1;
                } else if (mask_ll) {
                    enabled = (flags >> (3 - i)) & 1;
                } else if (i < 2) {
                    enabled = ((flags >> (2 - 2 * i)) & 3) != 0;
                } else {
                    enabled = 1;
                }
                if (!enabled) continue;
                unsigned value = out[i];
                if (mask_kind != 0 && !mask_ll && i < 2) {
                    unsigned hi = (flags >> (3 - 2 * i)) & 1;
                    unsigned lo = (flags >> (2 - 2 * i)) & 1;
                    unsigned m = (hi ? 0xffff0000u : 0) | (lo ? 0x0000ffffu : 0);
                    unsigned old = pd[pe * ld + db[c] + i];
                    value = (old & ~m) | (value & m);
                }
                pd[pe * ld + db[c] + i] = value;
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
    unsigned* mauf, unsigned* aluf, unsigned* mreadf,
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
            } else if (smem == 8) {
                bus[p][i] = mreadf[pe * 16 + c * 4 + i];
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

// One L1BM-to-PE read: op 0 is Mbcast, op 1 is Distrib.
extern "C" __global__ void l1_read_line(
    unsigned* lm0, unsigned* lm1, unsigned* grf0, unsigned* grf1,
    unsigned long long* l1bm,
    int op, unsigned addr, int mabdiff, int swl,
    int dmem, unsigned d0, unsigned d1, unsigned d2, unsigned d3, int dwl) {
    int pe = blockIdx.x * blockDim.x + threadIdx.x;
    if (pe >= 4096) return;
    int l1b = pe / 64;
    int mab = (pe / 4) % 16;
    int sub = pe % 4;
    unsigned db[4] = {d0, d1, d2, d3};
    unsigned* pd = pick_mem(dmem, lm0, lm1, grf0, grf1);
    int ld = mem_len(dmem);
    int base = l1b * 8192;
    for (int c = 0; c < 4; ++c) {
        int om;
        int ol = -1;
        if (op == 0) {
            if (swl == 4) {
                om = c * 8 + sub;
                ol = om + 4;
            } else {
                om = c * 4 + sub;
            }
        } else if (op == 2) {
            om = c;
            if (swl == 4) ol = c + 4;
        } else {
            int src_mab = (mab - mabdiff + 16) % 16;
            om = c * 64 + src_mab * 4 + sub;
        }
        unsigned long long m = l1bm[base + (addr + om) % 8192];
        unsigned long long l = (ol >= 0) ? l1bm[base + (addr + ol) % 8192] : 0;
        unsigned bus[4] = {
            (unsigned)(m >> 32),
            (unsigned)m,
            (unsigned)(l >> 32),
            (unsigned)l,
        };
        for (int i = 0; i < dwl; ++i) {
            pd[pe * ld + db[c] + i] = bus[i];
        }
    }
}

// One l1bmm@mab write: the selected MAB's PEs store two long words per cycle.
extern "C" __global__ void l1_write_line(
    unsigned* lm0, unsigned* lm1, unsigned* grf0, unsigned* grf1,
    unsigned long long* l1bm,
    int op, int mab_sel, int mabdiff, unsigned addr, int dwl,
    int smem, unsigned s0, unsigned s1, unsigned s2, unsigned s3, int swl) {
    int pe = blockIdx.x * blockDim.x + threadIdx.x;
    if (pe >= 4096) return;
    int mab = (pe / 4) % 16;
    int dst_mab = (mab + mabdiff + 16) % 16;
    if (op == 0 && mab != mab_sel) return;
    int l1b = pe / 64;
    int sub = pe % 4;
    unsigned sb[4] = {s0, s1, s2, s3};
    unsigned* ps = pick_mem(smem, lm0, lm1, grf0, grf1);
    int ls = mem_len(smem);
    int base = l1b * 8192;
    int step = (dwl == 4) ? 8 : 4;
    for (int c = 0; c < 4; ++c) {
        unsigned bus[4];
        for (int i = 0; i < 4; ++i) {
            bus[i] = (smem < 4 && i >= swl) ? 0 : ps[pe * ls + sb[c] + i];
        }
        unsigned long long msb = ((unsigned long long)bus[0] << 32) | bus[1];
        unsigned long long lsb = ((unsigned long long)bus[2] << 32) | bus[3];
        if (op == 1) {
            l1bm[base + (addr + c * 64 + dst_mab * 4 + sub) % 8192] = msb;
        } else {
            l1bm[base + (addr + c * step + sub) % 8192] = msb;
            if (dwl == 4) {
                l1bm[base + (addr + c * step + 4 + sub) % 8192] = lsb;
            }
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

// One reduction stage over `n` raw elements of the RRN precision.
__device__ __forceinline__ unsigned long long rrn_reduce(
    int kind, int bits, const unsigned long long* vals, int n) {
    unsigned long long m = rrn_mask(bits);
    if (kind == 0) return rrn_fadd(rrn_fmt(bits), vals, n, rrn_fmt(bits));
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

// One l1bmrffadd reduction: 16 MABs per L1B, 4 PEs and 4 cycles.
extern "C" __global__ void l1_reduce_line(
    unsigned* lm0, unsigned* lm1, unsigned* grf0, unsigned* grf1,
    unsigned long long* l1bm,
    int smem, unsigned s0, unsigned s1, unsigned s2, unsigned s3, int swl,
    unsigned addr) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx >= 1024) return;
    int pe_sub = idx & 3;
    int c = (idx >> 2) & 3;
    int l1b = idx >> 4;
    unsigned sb[4] = {s0, s1, s2, s3};
    unsigned* ps = pick_mem(smem, lm0, lm1, grf0, grf1);
    int ls = mem_len(smem);
    unsigned long long v0[16];
    unsigned long long v1[16];
    for (int m = 0; m < 16; ++m) {
        int pe = l1b * 64 + m * 4 + pe_sub;
        v0[m] = (smem < 4 && swl > 0) ? ps[pe * ls + sb[c]] : 0;
        v1[m] = (smem < 4 && swl > 1) ? ps[pe * ls + sb[c] + 1] : 0;
    }
    unsigned long long st0[4];
    unsigned long long st1[4];
    for (int g = 0; g < 4; ++g) {
        st0[g] = rrn_reduce(0, 32, v0 + g * 4, 4);
        st1[g] = rrn_reduce(0, 32, v1 + g * 4, 4);
    }
    unsigned long long r0 = rrn_reduce(0, 32, st0, 4);
    unsigned long long r1 = rrn_reduce(0, 32, st1, 4);
    l1bm[l1b * 8192 + (addr + (unsigned)c * 4 + (unsigned)pe_sub) % 8192] =
        (r0 << 32) | r1;
}
