#!/usr/bin/env python3
"""Dump GRF/T after each line N (emulator completes instantly). usage: trace.py prog.vsm N m p [regs]"""
import sys, subprocess, re
from pathlib import Path
ROOT = Path(__file__).resolve().parents[4]
E = ROOT/"judge/judge-py/mncore2_emuenv"
tc = (ROOT/"problems/16.onehot/testcase.vsm").read_text()
pre, suf = tc.split("# ======= YOUR VSM WILL BE INSERTED HERE =======")
prog = Path(sys.argv[1]).read_text().splitlines()
N=int(sys.argv[2]); m=sys.argv[3]; p=sys.argv[4]
regs = sys.argv[5].split(",") if len(sys.argv)>5 else ["r0:24","s0:24","n0:16"]
dbg=[]
for rg in regs:
    name,cnt=rg.split(":")
    if name=="t": dbg.append(f"d get $ltn0c0b0m{m}p{p} 4")
    elif name.startswith("b"): dbg.append(f"d get $lb{name[1:]}n0c0b0 {cnt}")
    else: dbg.append(f"d getf ${name}n0c0b0m{m}p{p} {cnt}")
text = pre + "\n" + "\n".join(prog[:N]) + "\n" + "\n".join(dbg)+"\n"
a = subprocess.run([str(E/"assemble3"), "--instruction-mode", "flat"], input=text, text=True, capture_output=True)
if a.returncode: print("ASM ERR", a.stderr[-2000:]); sys.exit(1)
r = subprocess.run([str(E/"gpfn3_package_main"), "--offchip-memory-init", "zero"], input=a.stdout, text=True, capture_output=True)
out={}
if "-v" in sys.argv: print(r.stdout[:3000], r.stderr[:3000])
for line in (r.stdout+r.stderr).splitlines():
    mm=re.match(r"DEBUG-(\w+)\((\S+?),(\d+)\):(.*?)#(.*)",line)
    if not mm: continue
    kind,loc,idx,val,cmd=mm.groups()
    key=cmd.split()[1].split("n0")[0]
    out.setdefault(key,[]).append((int(idx),val.strip()))
for k,v in out.items():
    vals=[]
    for idx,val in v:
        h=re.search(r"\(0x([0-9a-f]+)\)",val)
        if "i:" in val:
            vals.append(re.search(r"v:(0x[0-9A-Fa-f]+)",val).group(1))
        else:
            vals.append(h.group(1) if h else val)
    print(k, " ".join(x.lstrip("0") or "0" for x in vals))
