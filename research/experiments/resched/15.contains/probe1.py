import sys; sys.path.insert(0,'.')
from custom import *
sol = Path(sys.argv[1]).read_text()
lines = sol.splitlines()
k = int(sys.argv[2]); gets = sys.argv[3:]
def runx(A,B):
    L=[]
    for g in range(64):
        n,c,b=g//16,(g//8)%2,g%8
        for i in range(16): L.append(f"d set $lm{2*i}n{n}c{c}b{b} 1 {A[g*16+i]:016X}")
    for q in range(64):
        m,p=q//4,q%4
        for i in range(16): L.append(f"d set $ln{2*i}m{m}p{p} 1 {B[q*16+i]:016X}")
    full="\n".join(L)+"\n"+"\n".join(lines[:k]+gets+lines[k:])+"\n"
    asm=subprocess.run([str(E/'assemble3'),'--instruction-mode','flat'],input=full.encode(),capture_output=True)
    ls=[l for l in asm.stdout.decode().split('\n') if l.split() and (l.split()[0] in 'jm' or l.split()[0]=='d')]
    r=subprocess.run([str(E/'gpfn3_package_main'),'--offchip-memory-init','zero'],input="\n".join(ls).encode(),capture_output=True)
    return [l[:90] for l in r.stderr.decode().splitlines() if l.startswith('DEBUG') and 'LM' not in l[:9] or 'LM0(' in l[:12] ]
for bv in [(48,),(49,),(48,49)]:
    B=[1000]*1024
    for i,v in enumerate(bv): B[i]=v   # PE m0p0 B[0..]
    A=[47,48,49,50]+[999]*12
    A=A*64
    print(bv); print("\n".join(runx(A,B)))
