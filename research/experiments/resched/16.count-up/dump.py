# usage: python3 dump.py file.vsm N mem... ; prints compact arrays as (hi,lo) 32-bit pairs
import sys,subprocess,re
lines=open(sys.argv[1]).read().splitlines()
n=int(sys.argv[2]); gets=sys.argv[3:]
prog=lines[:n]+["d getd "+g for g in gets]
open('/tmp/cu_d.vsm','w').write("\n".join(prog)+"\n")
out=subprocess.run(['./emu.sh','/tmp/cu_d.vsm'],capture_output=True,text=True).stdout
cur=None;arr=[]
def flush():
    if cur: 
        print(cur, " ".join(arr))
for l in out.splitlines():
    if not l.startswith('DEBUG'):
        print(l); continue
    tag=l.split('#')[1].strip()
    m=re.search(r'\(0x([0-9A-Fa-f]+)\)',l)
    v=int(m.group(1),16) if m else None
    loc=l.split(':')[0].split(',')[0]
    tag=tag+' '+loc
    if tag!=cur:
        flush(); cur=tag; arr=[]
    arr.append(f"{v>>32:x}|{v&0xffffffff:x}" if v is not None else l)
flush()
