import sys,re
sys.path.insert(0,'/home/wogikaze/wgkz/mncore')
from mncompile.sim import official_run
MARK="# ======= YOUR VSM WILL BE INSERTED HERE ======="
pre=open('full.vsm').read().split(MARK)[0]
# map PE path,addr -> A pair
A={}
for l in pre.splitlines():
    m=re.match(r'd set \$lm(\d+)(n\S+) 1 ([0-9A-F]{8})([0-9A-F]{8})',l)
    if m: A[(m[2],int(m[1]))]=int(m[3],16); A[(m[2],int(m[1])+1)]=int(m[4],16)
def run(prog, mem='ln'):
    suf="d getd $%s0 4\n"%mem
    r=official_run(prog, pre, suf)
    if r.error: raise SystemExit(r.error)
    out={}
    for (m,pe,addr),v in r.dump.items():
        out[A[(pe,addr)]] = v>>32; out[A[(pe,addr+1)]] = v&0xffffffff
    return out
