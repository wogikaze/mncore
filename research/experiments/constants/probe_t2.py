#!/usr/bin/env python3
"""Probe T-register addressing: dump T and the LM0 words read via T-indirect."""
import sys

ROOT = "/home/wogikaze/wgkz/mncore"
sys.path.insert(0, ROOT)
from mncompile.sim import simulator  # noqa: E402

sim = simulator()
payload = " ".join(f"{1000+i:08x}{2000+i:08x}" for i in range(16))

CASES = [
    ("T = imm i\"5\" $t", f'd set $lm0n0c0b0m0p0 16 {payload}\n'
     'imm i"5" $t\nd get $llt 4\nipassa $mt[0,1,2,3] $ln0v\nd get $ln0 8'),
    ("T = imm ui\"0x4b000005\" $t", f'd set $lm0n0c0b0m0p0 16 {payload}\n'
     'imm ui"0x4b000005" $t\nd get $llt 4\nipassa $mt[0,1,2,3] $ln0v\nd get $ln0 8'),
    ("T = ipassa $r16 (r16=imm 5)", f'd set $lm0n0c0b0m0p0 16 {payload}\n'
     'imm i"5" $r16\nipassa $r16 $t\nd get $llt 4\nipassa $mt[0,1,2,3] $ln0v\nd get $ln0 8'),
    ("T = fvpassa $r16v (r16 float 5)", f'd set $lm0n0c0b0m0p0 16 {payload}\n'
     'imm f"5.0" $r16\nfvpassa $r16v $t\nd get $llt 4\nipassa $mt[0,1,2,3] $ln0v\nd get $ln0 8'),
]
for label, prog in CASES:
    r = sim.run(prog + "\n")
    print("=" * 60)
    print(label, "->", ("ERROR " + str(r.error)) if r.error else "ok")
    if r.error:
        continue
    for (mem, peid, addr), val in sorted(r.dump.items()):
        if str(peid) != "n0c0b0m0p0":
            continue
        if mem.startswith("TREG") or mem.startswith("LM1"):
            print(f"  {mem}@{addr} = 0x{val:016x}")
