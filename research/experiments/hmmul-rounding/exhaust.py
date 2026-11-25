#!/usr/bin/env python3
"""Exhaustive single-term probe: row element extended (exp 0), vector element normal.
Row r of MAB m holds only element j = r (mantissa e), vector cycle c element j holds o.
Pairs (e, o) are enumerated; the emulator's hmmul (single output) gives the rounded product."""
import os, sys, json, subprocess, tempfile, struct
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import hmmul_diff as H
CA, CB = 30, 30          # common exponents of row blocks and vector blocks
def f32(bits): return struct.unpack('>f', struct.pack('>I', bits))[0]
def run_batch(pairs, emu_bin):
    # pairs: list of 1024 (e, o); index = ((mab * 4 + c) * 16 + r)
    lm = [[0] * 40 for _ in range(64)]
    for mab in range(16):
        # rows: element r has mantissa from cycle 0's pair (rows are shared by cycles)
        for r in range(16):
            blk = [0] * 16
            blk[0] = (CA << 9)                    # common exponent carrier (mantissa 0)
            e = pairs[(mab * 4 + 0) * 16 + r][0]
            row_exp = 0 if MODE in ('row', 'both') else CA
            blk[r] = (row_exp << 9) | e if r != 0 else (CA << 9)  # element 0 carries the common exponent
            for p in range(4):
                w0, w1 = H.pack_words(blk[4 * p:4 * p + 4])
                lm[mab * 4 + p][2 * r] = w0; lm[mab * 4 + p][2 * r + 1] = w1
        for c in range(4):
            vec_exp = 0 if MODE in ('vec', 'both') else CB
            blk = [((vec_exp if j else CB) << 9) | pairs[(mab * 4 + c) * 16 + j][1] for j in range(16)]
            for p in range(4):
                w0, w1 = H.pack_words(blk[4 * p:4 * p + 4])
                lm[mab * 4 + p][32 + 2 * c] = w0; lm[mab * 4 + p][32 + 2 * c + 1] = w1
    lines = [f"d set $lm0{H.pe_name(pe)} 20 " + "".join(f"{w:08X}" for w in lm[pe]) for pe in range(64)]
    lines += [f"hmwrite $lm{8 * k}v $lx{4 * k}" for k in range(4)]
    lines += ["hmmul $lx $lm32v $lln0v", "nop"]
    lines += [f"d get $ln0{H.pe_name(pe)} 8" for pe in range(64)]
    with tempfile.TemporaryDirectory(dir=H.TMP_ROOT) as tmp:
        out = H.run_emulator("\n".join(lines) + "\n", emu_bin, tmp)
    res = []
    for mab in range(16):
        for c in range(4):
            for r in range(16):
                p, i = divmod(r, 4)
                word = 4 * c + i
                lw = out[(H.pe_name(mab * 4 + p), word & ~1)]
                bits = (lw >> (32 if word % 2 == 0 else 0)) & 0xffffffff
                res.append(bits)
    return res
MODE = 'row'
if __name__ == '__main__':
    MODE = sys.argv[2] if len(sys.argv) > 2 else 'row'
    emu = os.path.join(H.CHALLENGE_EMU, 'gpfn3_package_main')
    out = open(sys.argv[1], 'w')
    # e: row element mantissa (extended), o: vector mantissa; r = 0 is skipped (element 0
    # carries the common exponent), so each batch covers 15 rows x 4 cycles x 16 MABs.
    all_pairs = [(e, o) for e in range(512) for o in range(512)]
    batch = []
    done = 0
    # assign e per (mab, r) and o per (mab, c, r): iterate e over rows, o over 4 cycles
    i = 0
    while i < len(all_pairs):
        pairs = [(0, 0)] * 1024
        slots = []
        for mab in range(16):
            for r in range(1, 16):
                if i >= len(all_pairs): break
                e = all_pairs[i][0]
                for c in range(4):
                    if i < len(all_pairs) and all_pairs[i][0] == e:
                        pairs[(mab * 4 + c) * 16 + r] = all_pairs[i]
                        slots.append(((mab * 4 + c) * 16 + r, all_pairs[i])); i += 1
        res = run_batch(pairs, emu)
        for idx, (e, o) in slots:
            out.write(f"{e} {o} {res[idx]}\n")
        done += len(slots)
        if done % 20000 < len(slots): print(done, file=sys.stderr, flush=True)
