import sys
def c(j):
    p,s=divmod(j,4); return 2*p+s if s<2 else 8+2*p+s-2
def build(d, Tins="ipackbit $mabid $ls0 $t $mb"):
    S={}
    def add(s,x): S.setdefault(s,[]).append(x)
    add(1,Tins)
    a=d  # B raw
    add(a,"hmwrite $lm[128,160,256,256]r $lx0")
    add(a+1,"hmread $llx0 $nowrite"); add(a+1,"hmwrite $llmt[0,64,256,256]r $ly0")
    add(a+2,"hmread $llx8 $nowrite"); add(a+2,"hbfn/9 $mreadf $nowrite")
    add(a+3,"hmwrite $aluf $llx0"); add(a+3,"hmread $lly0 $nowrite"); add(a+3,"hbfn/9 $mreadf $nowrite")
    add(a+4,"hmwrite $aluf $llx8"); add(a+4,"hmread $lly8 $nowrite"); add(a+4,"hbfn/9 $mreadf $lls0v")
    add(a+5,"hbfn/9 $mreadf $lls16v")
    groups=[(None,[0,2,4,6]),(0,[1,3,5,7]),(16,[8,10,12,14]),(16,[9,11,13,15])]
    s=a+5
    for gi,(base,cols) in enumerate(groups):
        src="$aluf" if base is None else "$ls["+",".join(str(base+4*((j%8)//2)+2*(j%2)) for j in cols)+"]"
        add(s+gi,f"hmmul $lx {src} $nowrite")
        add(s+gi+1,"l1bmrffadd $mauf $lbi")
        add(s+gi+2,"l1bmm $lbi $ln["+",".join(str(2*c(j)) for j in cols)+"]")
    n=max(S)
    return "\n".join("; ".join(S.get(i,["nop"])) for i in range(1,n+1))+"\n"
if __name__=="__main__":
    d=int(sys.argv[1]); open(sys.argv[2],"w").write(build(d))
