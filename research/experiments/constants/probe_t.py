#!/usr/bin/env python3
"""Probe T-register semantics for LM0 T-indirect addressing."""
import sys

ROOT = "/home/wogikaze/wgkz/mncore"
sys.path.insert(0, ROOT)
from mncompile.sim import simulator  # noqa: E402

sim = simulator()

# LM0 words 0..15 hold 1000+i in the MSB word, 2000+i in the LSB word
payload = " ".join(f"{1000+i:08x}{2000+i:08x}" for i in range(16))

CASES = [
    ("T=0x4b000005 (fvpassa float)", f'd set $lm0n0c0b0m0p0 16 {payload}\n'
     'imm ui"0x4b000005" $r16\nfvpassa $r16v $t\n'
     'ipassa $mt[0,1,2,3] $ln0v\nd get $ln0 8'),
    ("T=0x4b000000", f'd set $lm0n0c0b0m0p0 16 {payload}\n'
     'imm ui"0x4b000000" $r16\nfvpassa $r16v $t\n'
     'ipassa $mt[0,1,2,3] $ln0v\nd get $ln0 8'),
    ("T=integer 5 (ipassa $r16 $t)", f'd set $lm0n0c0b0m0p0 16 {payload}\n'
     'imm i"5" $r16\nipassa $r16 $t\n'
     'ipassa $mt[0,1,2,3] $ln0v\nd get $ln0 8'),
    ("T=0 via imm i\"0\"", f'd set $lm0n0c0b0m0p0 16 {payload}\n'
     'imm i"0" $t\n'
     'ipassa $mt[0,1,2,3] $ln0v\nd get $ln0 8'),
    ("T=0x4b000075", f'd set $lm0n0c0b0m0p0 16 {payload}\n'
     'imm ui"0x4b000075" $r16\nfvpassa $r16v $t\n'
     'ipassa $mt[0,1,2,3] $ln0v\nd get $ln0 8'),
    ("T=0x4b000075, read mt[43,41] only", f'd set $lm0n0c0b0m0p0 16 {payload}\n'
     'imm ui"0x4b000075" $r16\nfvpassa $r16v $t\n'
     'ipassa $mt[43,41,0,0] $ln0v\nd get $ln0 8'),
]
for label, prog in CASES:
    r = sim.run(prog + "\n")
    print("=" * 60)
    print(label, "->", ("ERROR " + str(r.error)) if r.error else "ok")
    if r.error:
        continue
    for (mem, peid, addr), val in sorted(r.dump.items()):
        if str(peid) == "n0c0b0m0p0" and mem.startswith("LM1"):
            print(f"  LM1@{addr} = 0x{val:016x}  (msb={val>>32}, lsb={val & 0xffffffff})")
