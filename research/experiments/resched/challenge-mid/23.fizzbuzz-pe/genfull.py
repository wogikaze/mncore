# full-range testcase: every A in 1..32768 appears exactly once
import re,sys
src=open('/home/wogikaze/wgkz/mncore/problems/challenge/23.fizzbuzz-pe/testcase.vsm').read().splitlines()
def f(a):
    if a%15==0: return 0xFFFFBBBB
    if a%3==0: return 0x0000FFFF
    if a%5==0: return 0x0000BBBB
    return a
vals=iter(range(1,32769))
out=[]
for l in src:
    m=re.match(r'd set (\S+) 1 ([0-9A-F]{16}) # values=\[(\d+), (\d+)\] / UInt (.*)',l)
    if m:
        a=next(vals); b=next(vals)
        out.append(f'd set {m[1]} 1 {a:08X}{b:08X} # values=[{a}, {b}] / UInt {m[5]}'); continue
    m=re.match(r'd getd (\S+) 1 # expect=\[(\d+), (\d+)\] / UInt (.*)',l)
    if m: out.append(None); out.append(l); continue
    out.append(l)
# rebuild expects in same order as sets
sets=[l for l in out if l and l.startswith('d set')]
gi=0; res=[]
for l in out:
    if l is None: continue
    if l.startswith('d getd'):
        s=sets[gi]; gi+=1
        m=re.match(r'd set (\S+) 1 ([0-9A-F]{16})',s); a=int(m[2][:8],16); b=int(m[2][8:],16)
        addr=re.match(r'd getd (\S+)',l)[1]
        assert addr.replace('$ln','$lm')==m[1], (addr,m[1])
        l=f'd getd {addr} 1 # expect=[{f(a)}, {f(b)}] / UInt '+l.split('/ UInt ',1)[1]
    res.append(l)
open('full.vsm','w').write('\n'.join(res)+'\n')
