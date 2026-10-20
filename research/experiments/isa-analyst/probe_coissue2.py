#!/usr/bin/env python3
"""Max co-issue, second attempt with conflict-free operands."""
import subprocess
from pathlib import Path

ASM = Path(__file__).resolve().parents[3] / "judge/judge-py/mncore2_emuenv/assemble3"

CASES = [
 ("2: ALU + MAUcalc", "lpassa $lm0v $ln0v;fvpassa $ls16v $ls24v"),
 ("2: MAUcalc + mwrite (same precision+src)", "fvpassa $ls16v $ls24v;fmwrite $ls16v $ly0"),
 ("3: ALU + MAUcalc + mwrite", "lpassa $lm0v $ln0v;fvpassa $ls16v $ls24v;fmwrite $ls16v $ly0"),
 ("4: + L1BM", "lpassa $lm0v $ln0v;fvpassa $ls16v $ls24v;fmwrite $ls16v $ly0;l1bmd $lr0v $lb0"),
 ("5: + L2BM", "lpassa $lm0v $ln0v;fvpassa $ls16v $ls24v;fmwrite $ls16v $ly0;l1bmd $lr0v $lb0;l2bmd $lb64 $lc0"),
 ("6: + noforward", "lpassa $lm0v $ln0v;fvpassa $ls16v $ls24v;fmwrite $ls16v $ly0;l1bmd $lr0v $lb0;l2bmd $lb64 $lc0;noforward"),
 ("7: + wait i01 (tagged MV first)",
  "mvp/n64 $p0@0 $d0@0\nlpassa $lm0v $ln0v;fvpassa $ls16v $ls24v;fmwrite $ls16v $ly0;l1bmd $lr0v $lb0;l2bmd $lb64 $lc0;noforward;wait i01"),
 ("8: + l2bmdarw",
  "mvp/n64 $p0@0 $d0@0\nlpassa $lm0v $ln0v;fvpassa $ls16v $ls24v;fmwrite $ls16v $ly0;l1bmd $lr0v $lb0;l2bmd $lb64 $lc0;l2bmdarw;noforward;wait i01"),
 ("MAU: calc+mwrite same prec", "fvpassa $ls16v $ls24v;fmwrite $ls16v $ly0"),
 ("MAU: calc+mread same prec", "fvpassa $ls16v $ls24v;fmread $lx $lr16v"),
 ("MAU: mwrite+mread same prec", "fmwrite $ls16v $ly0;fmread $lx $lr16v"),
 ("3 MAU groups rejected", "fvpassa $ls16v $ls24v;fmwrite $ls16v $ly0;fmread $lx $lr16v"),
 ("ALU + mwrite + mread", "lpassa $lm0v $ln0v;fmwrite $ls16v $ly0;fmread $lx $lr16v"),
]


def run(src: str):
    p = subprocess.run([str(ASM), "--instruction-mode", "flat"], input=(src + "\n").encode(), capture_output=True)
    return p.returncode, p.stdout.decode(errors="replace"), p.stderr.decode(errors="replace")


for label, src in CASES:
    rc, out, err = run(src)
    if rc == 0:
        j = sum(1 for l in out.splitlines() if l[:1] == "j")
        m = sum(1 for l in out.splitlines() if l[:1] == "m")
        print(f"OK   {label:44s} j={j} m={m} words={j+m}")
    else:
        msg = next((l.strip() for l in err.splitlines() if l.strip()), "")
        print(f"FAIL {label:44s} {msg}")
