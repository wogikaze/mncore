#!/usr/bin/env python3
"""Probe write footprints of ALU/imm/iinc forms."""
import sys

ROOT = "/home/wogikaze/wgkz/mncore"
sys.path.insert(0, ROOT)
from mncompile.sim import simulator  # noqa: E402

sim = simulator()

CASES = [
    ("imm i\"7\" $lr2v4", 'imm i"7" $lr2v4\nd get $lr0 24'),
    ("imm i\"7\" $lr2v", 'imm i"7" $lr2v\nd get $lr0 24'),
    ("imm i\"7\" $lr2", 'imm i"7" $lr2\nd get $lr0 24'),
    ("imm ui\"7\" $lr2v", 'imm ui"7" $lr2v\nd get $lr0 24'),
    ("imm f\"0.001\" $lr72", 'imm f"0.001" $lr72\nd get $lr0 80'),
    ("iinc mreadf lr2v4 after dance",
     'ipackbit $subpeid $t $nowrite\n'
     'dmwrite $aluf $lx0\n'
     'dmread $lx0 $lr0v4\n'
     'iinc $mreadf $lr2v4\nd get $lr0 24'),
    ("iinc mreadf lr0v4 after dance",
     'ipackbit $subpeid $t $nowrite\n'
     'dmwrite $aluf $lx0\n'
     'dmread $lx0 $lr0v4\n'
     'iinc $mreadf $lr0v4\nd get $lr0 24'),
    ("iinc mreadf lr0 (no v)",
     'ipackbit $subpeid $t $nowrite\n'
     'dmwrite $aluf $lx0\n'
     'dmread $lx0 $lr0v4\n'
     'iinc $mreadf $lr0\nd get $lr0 24'),
    ("iinc mreadf ln0v4 (GRF1)",
     'ipackbit $subpeid $t $nowrite\n'
     'dmwrite $aluf $lx0\n'
     'dmread $lx0 $lr0v4\n'
     'iinc $mreadf $ls0v4\nd get $ls0 24'),
    ("iinc mreadf lr2v4 (no dmread)",
     'ipackbit $subpeid $t $nowrite\n'
     'dmwrite $aluf $lx0\n'
     'iinc $mreadf $lr2v4\nd get $lr0 24'),
    ("iinc aluf lr2v4 (src=aluf)",
     'iinc $aluf $lr2v4\nd get $lr0 24'),
]
for label, prog in CASES:
    r = sim.run(prog + "\n")
    print("=" * 70)
    print(label, "->", ("ERROR " + str(r.error)) if r.error else "ok")
    if r.error:
        continue
    vals = []
    for (mem, peid, addr), val in sorted(r.dump.items()):
        if str(peid) == "n0c0b0m0p0" and addr <= 200:
            vals.append((addr, val))
    for addr, val in vals:
        print(f"  w{addr:3d} = 0x{val:016x}")
