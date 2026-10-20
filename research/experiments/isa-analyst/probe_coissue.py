#!/usr/bin/env python3
"""Find the maximum number of co-issued expressions on one PE line (one word)."""
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
ASM = HERE.parents[2] / "judge/judge-py/mncore2_emuenv/assemble3"

CASES = [
 ("2: ALU + L1BM", "lpassa $lm0v $ln0v;l1bmd $ls0v $lb0"),
 ("2: ALU + L2BM", "lpassa $lm0v $ln0v;l2bmd $lb64 $lc0"),
 ("3: ALU + MAUcalc + L1BM", "lpassa $lm0v $ln0v;dvpassa $ls0v $ls8v;l1bmd $ls16v $lb0"),
 ("3: ALU + MAUcalc + mwrite", "lpassa $lm0v $ln0v;dvpassa $ls0v $ls8v;gmwrite $ls16v $ly0"),
 ("4: ALU + MAUcalc + L1BM + L2BM",
  "lpassa $lm0v $ln0v;dvpassa $ls0v $ls8v;l1bmd $ls16v $lb0;l2bmd $lb64 $lc0"),
 ("5: + mwrite", "lpassa $lm0v $ln0v;dvpassa $ls0v $ls8v;gmwrite $ls16v $ly0;l1bmd $ls24v $lb0;l2bmd $lb64 $lc0"),
 ("5: ALU + MAUcalc + mread + L1BM + L2BM",
  "lpassa $lm0v $ln0v;dvpassa $ls0v $ls8v;dmread $lx $ls16v;l1bmd $ls24v $lb0;l2bmd $lb64 $lc0"),
 ("6: + noforward", "lpassa $lm0v $ln0v;dvpassa $ls0v $ls8v;gmwrite $ls16v $ly0;l1bmd $ls24v $lb0;l2bmd $lb64 $lc0;noforward"),
 ("7: + wait i01 (tagged MV before)",
  "mvp/n64 $p0@0 $d0@0\nlpassa $lm0v $ln0v;dvpassa $ls0v $ls8v;gmwrite $ls16v $ly0;dmread $ly $ls24v;l1bmd $ls32v $lb0;l2bmd $lb64 $lc0;wait i01"),
 ("MAU: calc + mwrite + mread (3 MAU groups)",
  "dvpassa $ls0v $ls8v;gmwrite $ls16v $ly0;dmread $lx $ls24v"),
 ("MAU: calc + mwrite", "dvpassa $ls0v $ls8v;gmwrite $ls16v $ly0"),
 ("MAU: calc + mread", "dvpassa $ls0v $ls8v;dmread $lx $ls16v"),
 ("MAU: mwrite + mread", "gmwrite $ls0v $ly0;dmread $lx $ls16v"),
 ("ALU + mwrite + mread (2 MAU)", "lpassa $lm0v $ln0v;gmwrite $ls0v $ly0;dmread $lx $ls16v"),
 ("doc example 11 expressions line 2",
  "l2bmdars $lc0@.0 $dar0;l2bmdarw;l1bmrdfadd $lr0v $lbi\nnoforward;l2bmb $lc256 $lb0;l2bmdarw;l1bmm $lbi $lr0v/$imr1;l1bmrdfadd $lr8v $lb256;gmmul $lx $lm0v $ln0v/$imr1;gmwrite $ls0v $ly0;hrelu/$imr1 $t $t $t;wait i01"),
 ("mvn128 mnemonic does not exist", "mvn128/n64 $p0@0 $d0@0"),
 ("mvn128 with n128 form", "mvp/n128 $p0@0 $d0@0"),
]


def run(src: str):
    p = subprocess.run([str(ASM), "--instruction-mode", "flat"], input=(src + "\n").encode(), capture_output=True)
    return p.returncode, p.stdout.decode(errors="replace"), p.stderr.decode(errors="replace")


for label, src in CASES:
    rc, out, err = run(src)
    if rc == 0:
        j = sum(1 for l in out.splitlines() if l[:1] == "j")
        m = sum(1 for l in out.splitlines() if l[:1] == "m")
        print(f"OK   {label:46s} j={j} m={m} words={j+m}")
    else:
        msg = next((l.strip() for l in err.splitlines() if l.strip()), "")
        print(f"FAIL {label:46s} {msg}")
