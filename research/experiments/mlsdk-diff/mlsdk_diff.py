#!/usr/bin/env python3
"""Runs an MLSDK-generated VSM on the SDK 0.9 emulator and on the Rust simulator
with the same random DRAM contents and compares every DRAM region it declares.

Usage: mlsdk_diff.py WORKLOAD.vsm [--seeds N] [--first-seed S]

The VSM header lists the tensors as `# name: DRAM@<begin>-<end>/<Dtype>(...)`
(long-word addresses, the same range in each of the four groups). Every range
is filled with random values of its dtype (half and float in a moderate range,
ints small), the program runs, and every range is read back with `d get` on both
sides. The SDK assembler and emulator run in the mncore-sdk-minimal:0.9 image
(MNCORE_SDK_RUN, default research/experiments/mlsdk-diff/sdk_run.sh); the simulator is
viz/core/target/release/sim_run, which reads the same `r` DRAM records.
"""
import argparse
import os
import random
import re
import struct
import subprocess
import sys
import tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
SIM_RUN = os.path.join(ROOT, "viz/core/target/release/sim_run")
SDK_RUN = os.environ.get("MNCORE_SDK_RUN", os.path.join(ROOT, "research/experiments/mlsdk-diff/sdk_run.sh"))
TMP_ROOT = os.environ.get("MNCORE_TMP", os.path.expanduser("~/dl/tmp"))
GROUPS = 4
REGION_RE = re.compile(r"^# (\S+): DRAM@(\d+)-(\d+)/(\w+)\(")


def regions(vsm):
    out = {}
    for line in vsm.splitlines():
        if line.startswith("# === Dump vsm start"):
            break
        m = REGION_RE.match(line)
        if m:
            out[(int(m.group(2)), int(m.group(3)))] = (m.group(1), m.group(4))
    return out


def rand_half(rng):
    # MN-Core half: sign, 6-bit exponent (bias 31), 9-bit mantissa.
    return (rng.getrandbits(1) << 15) | (rng.randint(27, 33) << 9) | rng.getrandbits(9)


def rand_float(rng):
    return struct.unpack(">I", struct.pack(">f", rng.uniform(-2.0, 2.0)))[0]


def rand_long(rng, dtype):
    if dtype == "Half":
        v = 0
        for _ in range(4):
            v = (v << 16) | rand_half(rng)
        return v
    if dtype == "Float":
        return (rand_float(rng) << 32) | rand_float(rng)
    return rng.randint(0, 3)


def dram_records(regs, rng):
    lines = []
    for (begin, end), (_, dtype) in sorted(regs.items()):
        for g in range(GROUPS):
            for start in range(begin, end, 256):
                n = min(256, end - start)
                payload = "".join(f"{rand_long(rng, dtype):016X}" for _ in range(n))
                lines.append(f"r {g} {start:x} {n:x} {payload}")
    return lines


def gets(regs):
    return [f"d get $d{b}n{g} {e - b}" for (b, e) in sorted(regs) for g in range(GROUPS)]


def parse_emu(dump):
    out = {}
    for line in dump.splitlines():
        m = re.match(r"DEBUG-DRAM\(n(\d+),(\d+)\)", line)
        v = re.search(r"v:0x([0-9a-fA-F]+)", line)
        if m and v:
            out[(int(m.group(1)), int(m.group(2)))] = int(v.group(1), 16)
    return out


def parse_sim(text):
    out = {}
    for line in text.splitlines():
        mem, loc, addr, val = line.split()
        if mem == "DRAM":
            out[(int(loc.lstrip("n")), int(addr))] = int(val, 16)
    return out


def run_one(vsm, regs, seed):
    rng = random.Random(seed)
    records = dram_records(regs, rng)
    body = vsm.rstrip("\n") + "\n" + "\n".join(gets(regs)) + "\n"
    with tempfile.TemporaryDirectory(dir=TMP_ROOT) as tmp:
        vsm_path = os.path.join(tmp, "in.vsm")
        open(vsm_path, "w").write(body)
        asm = subprocess.run([SDK_RUN, "assemble3", vsm_path], capture_output=True, text=True, cwd=tmp)
        if asm.returncode != 0:
            raise RuntimeError(asm.stderr[-2000:])
        asm_path = os.path.join(tmp, "in.asm")
        open(asm_path, "w").write("\n".join(records) + "\n" + asm.stdout)
        dmp = os.path.join(tmp, "out.dmp")
        emu = subprocess.run([SDK_RUN, "gpfn3_package_main", "--no-mmap", "--offchip-memory-init", "zero",
                              "-i", asm_path, "-d", dmp], capture_output=True, text=True, cwd=tmp)
        if emu.returncode != 0:
            raise RuntimeError(emu.stderr[-2000:])
        emu_out = parse_emu(open(dmp).read())
        sim_path = os.path.join(tmp, "sim.vsm")
        open(sim_path, "w").write("\n".join(records) + "\n" + body)
        sim = subprocess.run([SIM_RUN, sim_path], capture_output=True, text=True)
        if sim.returncode != 0:
            raise RuntimeError(sim.stderr[-2000:])
        sim_out = parse_sim(sim.stdout)
    diff = {}
    for (begin, end), (name, _) in sorted(regs.items()):
        n = 0
        for g in range(GROUPS):
            for a in range(begin, end):
                e, s = emu_out.get((g, a)), sim_out.get((g, a))
                if e is None or s is None:
                    raise RuntimeError(f"missing DRAM {g}:{a} (emu {e}, sim {s})")
                n += e != s
        diff[name] = (n, (end - begin) * GROUPS)
    return diff


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("vsm")
    ap.add_argument("--seeds", type=int, default=3)
    ap.add_argument("--first-seed", type=int, default=1)
    args = ap.parse_args()
    vsm = open(args.vsm).read()
    regs = regions(vsm)
    total = 0
    for seed in range(args.first_seed, args.first_seed + args.seeds):
        diff = run_one(vsm, regs, seed)
        bad = {k: v for k, v in diff.items() if v[0]}
        total += sum(v[0] for v in diff.values())
        words = sum(v[1] for v in diff.values())
        print(f"{os.path.basename(args.vsm)} seed {seed}: {sum(v[0] for v in diff.values())} of {words} long words differ"
              + (f" {bad}" if bad else ""))
    sys.exit(1 if total else 0)


if __name__ == "__main__":
    main()
