#!/usr/bin/env python3
"""dbg.py prog.vsm [after_line:getspec ...]  -- run official asm+emu, insert d get after program line N (1-based)."""
import sys, subprocess, re
R='/home/wogikaze/wgkz/mncore/'
E=R+'judge/judge-py/mncore2_emuenv/'
tc=open(R+'problems/challenge/19.inversion/testcase.vsm').read()
M="# ======= YOUR VSM WILL BE INSERTED HERE ======="
pre,suf=tc.split(M)
prog=[l for l in open(sys.argv[1]).read().split('\n')]
ins={}
for a in sys.argv[2:]:
    n,s=a.split(':',1); ins.setdefault(int(n),[]).append(s)
out=[]
for i,l in enumerate(prog,1):
    out.append(l)
    for s in ins.get(i,[]): out.append('d '+s)
for s in ins.get(0,[]): out.append('d '+s)
vsm=pre+'\n'.join(out)+'\n'+(suf if '--suf' in sys.argv else '')
vsm=re.sub(r"[#!].*$","",vsm,flags=re.M)
p=subprocess.run([E+'assemble3','--instruction-mode','flat'],input=vsm.encode(),capture_output=True)
if p.returncode: print(p.stderr.decode()); sys.exit(1)
asm='\n'.join(l for l in p.stdout.decode().split('\n') if l.split()[:1] in (['j'],['m'],[]) or (l.startswith('d ')))
q=subprocess.run([E+'gpfn3_package_main'],input=asm.encode(),capture_output=True)
print(q.stderr.decode()[-20000:])
