import sys; from emu import *
prog=open(sys.argv[1]).read().split('\n')
loc=sys.argv[2] if len(sys.argv)>2 else 'n0c0b0m0p0'
specs=[('ls',0,8),('ls',64,1),('ls',160,16),('lr',0,32),('ln',64,1),('lm',4080,8)]
for i in range(1,len(prog)+1):
    if not prog[i-1].strip(): continue
    d={i:[f'get $l{m}{a}{loc} {n}' for m,a,n in specs]+[f'get $lt{loc} 4']}
    t=run(prog,d); v=vals(t)
    print(f'--- after {i}: {prog[i-1]}')
    def fmt(x):
        a,b=pair(x)
        def g(w): return str(w) if w<0x10000 or w>0xffff0000 else f'{f32(w):.6g}'
        return f'{g(a)}|{g(b)}'
    for spec,(_,_,n) in zip(['ls0','ls64','ls160','lr0','ln64','lm4080'],specs): pass
    print(' '.join(f'{a}:{fmt(x)}' for _,a,x in v if x))
