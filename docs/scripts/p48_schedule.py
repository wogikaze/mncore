# Generates the 61-step solution of problem 48 (matmul_tra_pkg_lmdram_16_256_1024).
# Usage: python3 p48_schedule.py [l2bmd start line] > main.vsm
# Notes on the design: docs/shortening_techniques.md
import sys
L={}
def put(n,*ins):
    L.setdefault(n,[]).extend(i for i in ins if i)
def xv(c,i): return 16*(i%8)+4*c+2*(i//8)
G=[[0,8,1,9],[2,10,3,11],[4,12,5,13],[6,14,7,15]]
def calc(face,c,g,y=None,dst='$nowrite'):
    xs=','.join(str(xv(c,i)) for i in G[g])
    if y is None: return f"gmmul $l{face} $ls[{xs}] {dst}"
    return f"gmfma $l{face} $ls[{xs}] {y} {dst}"
def P(mem,g): return f"$l{mem}[" + ','.join(str(1024+2*i) for i in G[g]) + "]"
def bw(c,half,face): return f"gmwrite $lm{128+2*c+32*half}v8 $l{face}{4*half}"
def gb(dst): return f"gbfn $mreadf {dst}"
def bt(c,half): return f"$lr{16*c+8*half}v"
def mat(c,half,face): return f"gmwrite $lr{16*c+8*half}v $l{face}{4*half}"
def bc(col): s,q=divmod(col,4); return f"l1bmm $llb{256*s+64*q} $lls{16*col}v"
def coll(g): return f"l1bmd $mauf $lb{1024+256*g}"
# early phase: transposes (T needs one step between write and read)
put(0,"ipassa $mabid $nowrite", bw(0,0,'x'))
put(1,"iadd $aluf $aluf $t", bw(0,1,'x'))
put(2,"gmread $lx0 $nowrite")
put(3,gb(bt(0,0)), "gmwrite $lmt0v16 $ly0", "gmread $lx4 $nowrite")
put(4,gb(bt(0,1)), "gmwrite $lmt64v16 $ly4")
put(5,bw(1,0,'x'), "gmread $ly0 $nowrite")
put(6,gb("$nowrite"), bw(1,1,'x'), "gmread $ly4 $nowrite")
put(7,gb("$nowrite"), bw(2,0,'y'), "gmread $lx0 $nowrite", "l1bmd $aluf $lb0")
put(8,gb(bt(1,0)), bw(2,1,'y'), "gmread $lx4 $nowrite", "l1bmd $aluf $lb256")
put(9,gb(bt(1,1)), bw(3,0,'x'), "gmread $ly0 $nowrite")
put(10,gb(bt(2,0)), bw(3,1,'x'), "gmread $ly4 $nowrite")
put(11,gb(bt(2,1)), mat(0,0,'y'), "gmread $lx0 $nowrite")
put(12,gb(bt(3,0)), mat(0,1,'y'), "gmread $lx4 $nowrite")
put(13,gb(bt(3,1)), mat(1,0,'x'))
put(14,mat(1,1,'x'))
BC0=11
for col in range(8): put(BC0+col, bc(col))
# calcs
put(14,calc('y',0,0))
put(15,calc('x',1,0,'$mauf',P('m',0)), mat(2,0,'y'))
put(16,calc('x',1,1), mat(2,1,'y'))
put(17,calc('y',2,1,'$mauf',P('n',1)), mat(3,0,'x'))
put(18,calc('y',2,0,P('m',0)), mat(3,1,'x'))
put(19,calc('x',3,0,'$mauf'), mat(0,0,'y'))
put(20,calc('x',3,1,P('n',1)), mat(0,1,'y'), coll(0))
put(21,calc('y',0,1,'$mauf'), mat(1,0,'x'))
put(22,calc('y',0,2), mat(1,1,'x'), coll(1))
put(23,calc('x',1,2,'$mauf',P('m',2)))
put(24,calc('y',0,3))
put(25,calc('x',1,3,'$mauf',P('n',3)), mat(2,0,'y'))
put(26,mat(2,1,'y'))
put(27,calc('y',2,2,P('m',2),P('m',2)), mat(3,0,'x'))
put(28,calc('y',2,3,P('n',3)), mat(3,1,'x'))
put(29,calc('x',3,3,'$mauf'))
put(30,calc('x',3,2,P('m',2)), coll(3))
put(31,coll(2))
S=int(sys.argv[1]) if len(sys.argv)>1 else 23
order=[0,1,3,2]
rowbase={}
for g in range(4):
    for q,i in enumerate(G[g]): rowbase[i]=1024+256*g+64*q
k=0
for g in order:
    for i in G[g]:
        for h in range(2):
            put(S+k, f"l2bmd $lb{rowbase[i]+32*h} $lc{512*i+256*h}"); k+=1
n=max(L)+1
out=[';'.join(L.get(j,[])) or 'nop' for j in range(n)]
out.append('nop')
out.append('mvrffadd/n8192 $lc0 $p0@0')
for g in range(4): out.append(f"mvp/n2048 $p{2048*g}@0 $d0@{g}")
print('\n'.join(out))
