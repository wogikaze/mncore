#!/usr/bin/env python3
"""Assemble with assemble3 and run gpfn3_package_main; dump selected DRAM words.

Usage: python3 run_official.py prog.vsm [--init zero|unique] [--dump A:B ...]
       (dump every addr in [A,B))
The program is a VSM fragment; `d getd $d<i>n0 1` lines are appended for the
requested addresses (the suffix is not part of the scored word count).
"""
import argparse, re, subprocess, tempfile
from pathlib import Path
ROOT = Path(__file__).resolve().parents[2]
EMUENV = ROOT / "judge/judge-py/mncore2_emuenv"
ASM, EMU = EMUENV/"assemble3", EMUENV/"gpfn3_package_main"

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("prog"); ap.add_argument("--init", default="unique")
    ap.add_argument("--dump", action="append", default=[])
    a=ap.parse_args()
    text=Path(a.prog).read_text()
    ranges=[]
    for spec in a.dump:
        lo,hi=map(int,spec.split(":")); ranges += list(range(lo,hi))
    suffix="".join(f"d getd $d{i}n0 1\n" for i in ranges)
    with tempfile.TemporaryDirectory() as td:
        src=Path(td)/"in.vsm"; src.write_text(text+"\n"+suffix)
        p=subprocess.run([str(ASM),"--instruction-mode","flat"],input=src.read_text().encode(),capture_output=True)
        if p.returncode:
            print("ASM FAIL", p.stderr.decode(errors="replace")[:800]); return 1
        asm=p.stdout.decode()
        asmfile=Path(td)/"in.asm"; asmfile.write_text(asm)
        dump=Path(td)/"out.dmp"
        q=subprocess.run([str(EMU),"-i",str(asmfile),"-d",str(dump),"--offchip-memory-init",a.init],capture_output=True)
        txt=(dump.read_text() if dump.exists() else "")+q.stdout.decode(errors="replace")
        vals={}
        for line in txt.splitlines():
            m=re.search(r"DEBUG-DRAM\(n0,(\d+)\):\(([-0-9.e+]+)\) \(0x([0-9a-fA-F]+)\)", line)
            if m: vals[int(m.group(1))]=m.group(3)
        print(f"asm_words j={sum(1 for l in asm.splitlines() if l.startswith('j '))} "
              f"m={sum(1 for l in asm.splitlines() if l.startswith('m '))} rc_emu={q.returncode}")
        for addr in ranges:
            print(f"D{addr} = 0x{vals.get(addr,'??')}")
    return 0
if __name__=="__main__": raise SystemExit(main())
