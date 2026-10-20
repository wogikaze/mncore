#!/usr/bin/env python3
"""Probe: MAU immediates, MAU writes to GRF, co-issue matrix."""
import subprocess
import sys
from pathlib import Path

ROOT = Path("/home/wogikaze/wgkz/mncore")
ASM = ROOT / "judge/judge-py/mncore2_emuenv/assemble3"
sys.path.insert(0, str(ROOT))
from mncompile.sim import simulator  # noqa: E402

def run(src):
    p = subprocess.run([str(ASM), "--instruction-mode", "flat"], input=src.encode(),
                       capture_output=True)
    if p.returncode != 0:
        msg = next((l.strip() for l in p.stderr.decode().splitlines() if l.strip()), "")
        return None, msg
    out = p.stdout.decode()
    j = sum(1 for l in out.splitlines() if l[:1] == "j")
    m = sum(1 for l in out.splitlines() if l[:1] == "m")
    return (j, m), ""

sim = simulator()

CASES = [
    ("fvadd imm src", 'fvadd $r0 63.0 $r16'),
    ("fvadd imm src f-lit", 'fvadd $r0 f"63.0" $r16'),
    ("fvadd imm src int-lit", 'fvadd $r0 63 $r16'),
    ("fvpassa GRF->GRF", 'fvpassa $s0v $r16'),
    ("fvpassa to T", 'fvpassa $r0 $t'),
    ("fvadd imm -> T", 'fvadd $r0 8388608.0 $t'),
    ("MAU dst + ALU nowrite host", 'ior $aluf $s0 $nowrite; fvadd $r0 63.0 $r16'),
    ("MAU dst + ALU nowrite host (rev)", 'fvadd $r0 63.0 $r16; ior $aluf $s0 $nowrite'),
    ("MAU dst GRF0 + ALU writes GRF1", 'ior $aluf $s0 $s16; fvadd $r0 63.0 $r16'),
    ("MAU 2 dst + ALU nowrite", 'fvadd $r0 63.0 $r16 $s16; ior $aluf $s0 $nowrite'),
    ("MAU imm + ALU imm (both imm field)", 'imm i"7" $r17; fvadd $r0 63.0 $r16'),
    ("MAU + ALU reading same bank other addr", 'ior $lr0v $s0 $nowrite; fvadd $r0 63.0 $r16'),
]

for label, src in CASES:
    wc, err = run(src + "\n")
    if wc is None:
        print(f"FAIL {label:44s} {err}")
        continue
    r = sim.run(src + '\nd get $lr0 12\n')
    vals = []
    if r.error:
        print(f"ASM-OK {label:42s} words={wc}  SIM-ERROR {r.error}")
        continue
    for (mem, peid, addr), val in sorted(r.dump.items()):
        if str(peid) == "n0c0b0m0p0" and addr in (0, 16, 32):
            vals.append(f"{mem}@{addr}=0x{val:016x}")
    print(f"ASM-OK {label:42s} words={wc}  " + " ".join(vals))
