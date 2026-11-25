#!/usr/bin/env python3
"""Differential test of half-precision matrix products (hmmul / hmmulr).

Random half block-float matrices and vectors (with extended elements, whose
exponent field is 0 and whose exponent is "common - 6") are written into the
matrix registers of 16 MABs with hmwrite, multiplied, and the results are
compared bit for bit between the official emulator and the Rust simulator.

Usage: hmmul_diff.py [--op hmmul|hmmulr] [--runs N] [--seed S] [--sparse]
                     [--emu DIR] [--sdk] [--dump FILE]

--sparse keeps one nonzero product per output row, so a single-precision
hmmul output shows one rounded product exactly.
--sdk runs the SDK 0.9 emulator inside the mncore-sdk-minimal:0.9 image
(MNCORE_SDK_RUN, default research/experiments/mlsdk-diff/sdk_run.sh) instead of the challenge
emulator (the challenge assembler is used in both cases).
--dump writes every compared output as a JSON line (inputs, emulator, sim).
"""

import argparse
import json
import os
import random
import re
import subprocess
import sys
import tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
CHALLENGE_EMU = os.path.join(ROOT, "judge/judge-py/mncore2_emuenv")
SIM_RUN = os.path.join(ROOT, "viz/core/target/release/sim_run")
# Wrapper that runs an SDK 0.9 tool inside the SDK image; temporary files must
# live under /home so that the container sees them.
SDK_RUN = os.environ.get("MNCORE_SDK_RUN", os.path.join(ROOT, "research/experiments/mlsdk-diff/sdk_run.sh"))
TMP_ROOT = os.environ.get("MNCORE_TMP", os.path.expanduser("~/dl/tmp"))
MABS = 16


def pe_name(pe):
    return f"n0c0b0m{pe // 4}p{pe % 4}"


def gen_block(rng, sparse_index=None, ext_prob=0.5, zero_prob=0.15):
    """16 half block-float elements: sign(1) exp(6) mantissa(9)."""
    common = rng.randint(8, 50)
    elems = []
    for i in range(16):
        sign = rng.getrandbits(1)
        man = rng.getrandbits(9)
        if sparse_index is not None and i != sparse_index:
            man = 0
        elif rng.random() < zero_prob:
            man = 0
        exp = 0 if (i != 0 and rng.random() < ext_prob) else common
        elems.append((sign << 15) | (exp << 9) | man)
    # Element 0 carries the common exponent; when the sparse term sits on an
    # extended element elsewhere, element 0 still defines the common exponent.
    return elems


def pack_words(elems4):
    """Four halves -> two 32-bit words (first half in the high bits)."""
    w0 = (elems4[0] << 16) | elems4[1]
    w1 = (elems4[2] << 16) | elems4[3]
    return w0, w1


def build(rng, op, sparse):
    # LM0 words per PE: rows r = 0..15 at words 2r, 2r+1 (cycle r % 4 of the
    # hmwrite that covers rows 4k..4k+3); vectors of cycles c at 32 + 2c.
    lm = [[0] * 40 for _ in range(MABS * 4)]
    rows = {}
    vecs = {}
    for mab in range(MABS):
        for r in range(16):
            j = rng.randrange(16) if sparse else None
            blk = gen_block(rng, j)
            rows[(mab, r)] = blk
            for p in range(4):
                w0, w1 = pack_words(blk[4 * p:4 * p + 4])
                lm[mab * 4 + p][2 * r] = w0
                lm[mab * 4 + p][2 * r + 1] = w1
        for c in range(4):
            blk = gen_block(rng, None, zero_prob=0.0 if sparse else 0.15)
            vecs[(mab, c)] = blk
            for p in range(4):
                w0, w1 = pack_words(blk[4 * p:4 * p + 4])
                lm[mab * 4 + p][32 + 2 * c] = w0
                lm[mab * 4 + p][32 + 2 * c + 1] = w1
    lines = []
    ys = {}
    for pe in range(MABS * 4):
        hexs = "".join(f"{w:08X}" for w in lm[pe])
        lines.append(f"d set $lm0{pe_name(pe)} {len(lm[pe]) // 2} {hexs}")
    if op in ("hmfma", "hmfmar"):
        for pe in range(MABS * 4):
            mab = pe // 4
            words = []
            for c in range(4):
                for i in range(4):
                    row = 4 * (pe % 4) + i
                    # y near the dot product's magnitude so that its alignment matters.
                    ca = max((v >> 9) & 63 for v in rows[(mab, row)])
                    cb = max((v >> 9) & 63 for v in vecs[(mab, c)])
                    e = ca + cb - 62 + 127 + rng.randint(-12, 4)
                    e = min(max(e, 1), 254)
                    y = (rng.getrandbits(1) << 31) | (e << 23) | rng.getrandbits(23)
                    if rng.random() < 0.05:
                        y = 0
                    ys[(pe, c, i)] = y
                    words.append(y)
            lines.append(f"d set $lr0{pe_name(pe)} 8 " + "".join(f"{w:08X}" for w in words))
    for k in range(4):
        lines.append(f"hmwrite $lm{8 * k}v $lx{4 * k}")
    if op == "hmmul":
        lines.append("hmmul $lx $lm32v $lln0v")
        out_words = 16
    elif op == "hmfma":
        lines.append("hmfma $lx $lm32v $llr0v $lln0v")
        out_words = 16
    elif op == "hmfmar":
        lines.append("hmfmar $lx $lm32v $llr0v $ln0v")
        out_words = 8
    else:
        lines.append("hmmulr $lx $lm32v $ln0v")
        out_words = 8
    lines.append("nop")
    for pe in range(MABS * 4):
        lines.append(f"d get $ln0{pe_name(pe)} {out_words // 2}")
    return "\n".join(lines) + "\n", rows, vecs, ys, out_words


DUMP_RE = re.compile(r"DEBUG-(\w+)\(([^,]+),(\d+)\)[^v]*v:0x([0-9a-fA-F]+)")


def run_emulator(vsm, emu_bin, tmp):
    vsm_path = os.path.join(tmp, "in.vsm")
    asm_path = os.path.join(tmp, "in.asm")
    dmp_path = os.path.join(tmp, "out.dmp")
    with open(vsm_path, "w") as f:
        f.write(vsm)
    with open(asm_path, "w") as f:
        subprocess.run([os.path.join(CHALLENGE_EMU, "assemble3"), vsm_path], stdout=f, check=True)
    if emu_bin == "sdk":
        # SDK 0.9 tools run in the mncore-sdk-minimal:0.9 image (see SDK_RUN).
        args = [SDK_RUN, "gpfn3_package_main", "--no-mmap", "--offchip-memory-init", "zero",
                "-i", asm_path, "-d", dmp_path]
    else:
        args = [emu_bin, "--offchip-memory-init", "zero", "-i", asm_path, "-d", dmp_path]
    subprocess.run(args, stdout=subprocess.DEVNULL, stderr=subprocess.PIPE, check=True)
    out = {}
    for line in open(dmp_path):
        for m in re.finditer(r"DEBUG-(\w+)\(([^,]+),(\d+)\)", line):
            pass
        m = re.match(r"DEBUG-(\w+)\(([^,]+),(\d+)\)", line)
        if not m:
            continue
        vals = re.findall(r"v:0x([0-9a-fA-F]+)", line)
        addr = int(m.group(3))
        for k, v in enumerate(vals):
            out[(m.group(2), addr + 2 * k)] = int(v, 16)
    return out


def run_sim(vsm, tmp):
    vsm_path = os.path.join(tmp, "in.vsm")
    with open(vsm_path, "w") as f:
        f.write(vsm)
    res = subprocess.run([SIM_RUN, vsm_path], capture_output=True, text=True)
    if res.returncode != 0:
        raise RuntimeError(res.stderr)
    out = {}
    for line in res.stdout.splitlines():
        mem, loc, addr, val = line.split()
        out[(loc, int(addr))] = int(val, 16)
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--op", default="hmmulr", choices=["hmmul", "hmmulr", "hmfma", "hmfmar"])
    ap.add_argument("--runs", type=int, default=1)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--sparse", action="store_true")
    ap.add_argument("--sdk", action="store_true")
    ap.add_argument("--dump")
    args = ap.parse_args()
    emu_bin = "sdk" if args.sdk else os.path.join(CHALLENGE_EMU, "gpfn3_package_main")
    rng = random.Random(args.seed)
    dump = open(args.dump, "w") if args.dump else None
    total = bad = 0
    for run in range(args.runs):
        vsm, rows, vecs, ys, out_words = build(rng, args.op, args.sparse)
        with tempfile.TemporaryDirectory(dir=TMP_ROOT) as tmp:
            emu = run_emulator(vsm, emu_bin, tmp)
            sim = run_sim(vsm, tmp)
        single_out = args.op in ("hmmul", "hmfma")
        width = 32 if single_out else 16
        for pe in range(MABS * 4):
            mab, p = divmod(pe, 4)
            for la in range(0, out_words, 2):
                key = (pe_name(pe), la)
                e, s = emu.get(key), sim.get(key)
                if e is None or s is None:
                    raise RuntimeError(f"missing output {key}: emu {e} sim {s}")
                # Split the long word into its outputs: cycle and row.
                for k in range(64 // width):
                    sh = 64 - width * (k + 1)
                    ev = (e >> sh) & ((1 << width) - 1)
                    sv = (s >> sh) & ((1 << width) - 1)
                    word = la + k * width // 32
                    if single_out:
                        cyc, i = divmod(word, 4)
                    else:
                        cyc, half = divmod(la * 2 + k, 4)
                        i = half
                    row = 4 * p + i
                    total += 1
                    if ev != sv:
                        bad += 1
                    if dump:
                        dump.write(json.dumps({
                            "row": rows[(mab, row)], "vec": vecs[(mab, cyc)],
                            "y": ys.get((pe, cyc, i)), "emu": ev, "sim": sv,
                        }) + "\n")
        print(f"run {run}: {bad} / {total} mismatches so far", file=sys.stderr)
    print(f"{args.op}{' sparse' if args.sparse else ''}: {bad} of {total} outputs differ")


if __name__ == "__main__":
    main()
