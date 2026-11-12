#!/usr/bin/env python3
"""quick probe: t.py 'prog lines (\\n sep)' 'dumps' ; dumps like 'r0:8@m0p1 t@m1p2 b0:8'"""
import sys, subprocess, re
from pathlib import Path
ROOT = Path(__file__).resolve().parents[4]
E = ROOT/"judge/judge-py/mncore2_emuenv"
tc = (ROOT/"problems/16.onehot/testcase.vsm").read_text()
pre, suf = tc.split("# ======= YOUR VSM WILL BE INSERTED HERE =======")
def run(prog, dumps, asm_only=False):
    dbg=[]
    for d in dumps.split():
        loc = "n0c0b0"
        if "@" in d: d,where=d.split("@"); loc+=where
        if d=="t": dbg.append(f"d get $lt{loc} 4"); continue
        name,cnt=d.split(":")
        if name.startswith("b"): dbg.append(f"d get $lb{name[1:]}n0c0b0 {cnt}")
        else: dbg.append(f"d getf ${name}{loc} {cnt}")
    text = pre + "\n" + prog + "\n" + "\n".join(dbg)+"\n"
    a = subprocess.run([str(E/"assemble3"), "--instruction-mode", "flat"], input=text, text=True, capture_output=True)
    if a.returncode: return "ASM ERR " + "\n".join(l for l in a.stderr.splitlines() if "0x" not in l)[-1500:]
    r = subprocess.run([str(E/"gpfn3_package_main"), "--offchip-memory-init", "zero"], input=a.stdout, text=True, capture_output=True)
    out={}; order=[]
    for line in (r.stdout+r.stderr).splitlines():
        mm=re.match(r"DEBUG-(\w+)\((\S+?),(\d+)\):(.*?)#(.*)",line)
        if not mm: continue
        kind,loc,idx,val,cmd=mm.groups()
        key=cmd.strip()
        if key not in out: out[key]=[]; order.append(key)
        if "v:" in val: out[key].append(re.search(r"v:(0x[0-9A-Fa-f]+)",val).group(1))
        else:
            h=re.search(r"\(0x([0-9a-f]+)\)",val); out[key].append(h.group(1).lstrip("0") or "0" if h else val)
    err=[l for l in r.stderr.splitlines() if "exception]" in l][:2]
    return "\n".join(err+[k+" => "+" ".join(out[k]) for k in order])
if __name__=="__main__":
    print(run(sys.argv[1].replace("\\n","\n"), sys.argv[2] if len(sys.argv)>2 else ""))
