#!/usr/bin/env python3
"""Sweep assembler acceptance of MV size for every MV basic-mode family."""
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
ASM = ROOT / "judge/judge-py/mncore2_emuenv/assemble3"

FORMS = {
    "mvp PDM->DRAM single      ": "mvp/n{n} $p0@0 $d0@0",
    "mvp DRAM->PDM single      ": "mvp/n{n} $d0@0 $p0@0",
    "mvp PDM->L2BM parallel    ": "mvp/n{n} $p0 $lc0@.0",
    "mvp L2BM->PDM parallel    ": "mvp/n{n} $lc0@.0 $p0",
    "mvp L2BM->DRAM single     ": "mvp/n{n} $lc0@0.0 $d0@0",
    "mvp L2BM->DRAM parallel   ": "mvp/n{n} $lc0@.0 $d0",
    "mvp DRAM->L2BM parallel   ": "mvp/n{n} $d0 $lc0@.0",
    "mvd L2BM->PDM gather      ": "mvd/n{n} $lc0 $p0@0",
    "mvd PDM->DRAM distribute  ": "mvd/n{n} $p0@0 $d0",
    "mvd DRAM->PDM gather      ": "mvd/n{n} $d0 $p0@0",
    "mvd PDM->L2BM distribute  ": "mvd/n{n} $p0@0 $lc0",
    "mvb PDM->L2BM broadcast   ": "mvb/n{n} $p0@0 $lc0",
    "mvb2 DRAM->L2BM in-group  ": "mvb2/n{n} $d0 $lc0",
    "mvb4 DRAM->L2BM inter-grp ": "mvb4/n{n} $d0 $lc0",
    "mvb DRAM->L2BM inter-grp  ": "mvb/n{n} $d0 $lc0",
    "mvr2dfadd L2BM->DRAM      ": "mvr2dfadd/n{n} $lc0 $d0",
    "mvr4dfadd L2BM->DRAM      ": "mvr4dfadd/n{n} $lc0 $d0",
    "mvrdfadd  L2BM->DRAM      ": "mvrdfadd/n{n} $lc0 $d0",
    "mvrdfadd  L2BM->PDM       ": "mvrdfadd/n{n} $lc0 $p0@0",
    "mvr2dfadd L2BM->PDM       ": "mvr2dfadd/n{n} $lc0@0 $p0@0",
}

SIZES = [16, 32, 48, 64, 128, 1024, 16384, 32640, 32704, 32752, 32768]


def rc(line: str) -> tuple[int, str, str]:
    p = subprocess.run([str(ASM), "--instruction-mode", "flat"], input=(line + "\n").encode(), capture_output=True)
    err = next((l.strip() for l in p.stderr.decode(errors="replace").splitlines() if l.strip()), "")
    return p.returncode, p.stdout.decode(errors="replace"), err


def main() -> None:
    print(f"{'form':28s} " + " ".join(f"{s:>7d}" for s in SIZES))
    for label, tpl in FORMS.items():
        row = []
        for n in SIZES:
            code, out, err = rc(tpl.format(n=n))
            if code == 0:
                # word cost = number of m lines
                m = sum(1 for l in out.splitlines() if l[:1] == "m")
                row.append(f"{'OK('+str(m)+')':>7s}")
            else:
                key = "align" if "aligned" in err else ("field" if "2^11" in err else "ERR")
                row.append(f"{key:>7s}")
        print(f"{label:28s} " + " ".join(row))


if __name__ == "__main__":
    main()
