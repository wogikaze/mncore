#!/usr/bin/env python3
"""Does imm update the aluf forwarding register? (chain-break semantics)"""
import sys

ROOT = "/home/wogikaze/wgkz/mncore"
sys.path.insert(0, ROOT)
from mncompile.sim import simulator  # noqa: E402

sim = simulator()

CASES = [
    ("passa aluf after imm in between",
     'imm i"1" $r0\n'
     'ipassa $r0 $nowrite\n'
     'imm i"5" $r1\n'
     'ipassa $aluf $s2\nd get $ls0 8'),
    ("ipassa aluf -> s2 directly after ipassa r0 (no imm)",
     'imm i"1" $r0\n'
     'ipassa $r0 $nowrite\n'
     'ipassa $aluf $s2\nd get $ls0 8'),
    ("imm then ALU reads aluf (imm value?)",
     'imm i"1" $r0\n'
     'ipassa $r0 $nowrite\n'
     'imm i"5" $r1\n'
     'iadd $aluf $aluf $s4\nd get $ls0 8'),
    ("MAU reads aluf after imm",
     'imm i"1" $r0\n'
     'ipassa $r0 $nowrite\n'
     'imm i"5" $r1\n'
     'fvadd $aluf $ls0 $s4\nd get $ls0 8'),
    ("does dmwrite/dmread update aluf? (ipassa r0 / dmread / ipassa aluf)",
     'imm i"1" $r0\n'
     'ipassa $r0 $nowrite\n'
     'dmread $lx0 $lr10\nd get $lr10 4'),
]
for label, prog in CASES:
    r = sim.run(prog + "\n")
    print("=" * 70)
    print(label, "->", ("ERROR " + str(r.error)) if r.error else "ok")
    if r.error:
        continue
    for (mem, peid, addr), val in sorted(r.dump.items()):
        if str(peid) == "n0c0b0m0p0":
            print(f"  {mem}@{addr} = 0x{val:016x}")
