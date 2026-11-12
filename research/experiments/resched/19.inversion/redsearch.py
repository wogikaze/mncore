# Search reduction schedules: items with write times; MAU ops lines first..F; final at (F, f)
import sys, itertools
def T(l,c): return 4*l+c
def search(items, first, F, finals, lat=7, share_mauf=True):
    # items: list of (name, line, cycle)
    N=len(items); FULL=(1<<N)-1
    lines=list(range(first,F+1))
    best=[0,None]
    sys.setrecursionlimit(10000)
    # node values: dict (l,c)->mask ; sources readable at (l,c): items with T(l,c)>=T(wl,wc)+lat; nodes same
    def readable(l,c,nodes):
        r=[]
        for i,(n,wl,wc) in enumerate(items):
            if T(l,c)>=T(wl,wc)+lat: r.append((1<<i,('it',n)))
        for (nl,nc),m in nodes.items():
            if m and T(l,c)>=T(nl,nc)+lat: r.append((m,('nd',nl,nc)))
        return r
    results=[]
    def rec(li, ltype, c, nodes, used):
        # used: set of source ids consumed
        if li==len(lines):
            for f in finals:
                m=nodes.get((F,f),0)
                if m==FULL:
                    results.append(dict(nodes)); return True
            return False
        l=lines[li]
        if c==0 and ltype is None:
            for t in ('mauf','mem'):
                if t=='mauf' and li==0: continue
                if rec(li,t,0,nodes,used): return True
            return False
        if c==4:
            return rec(li+1,None,0,nodes,used)
        # options for node (l,c)
        srcs=[s for s in readable(l,c,nodes) if s[1] not in used]
        opts=[(0,None,None)]
        A=[]
        if ltype=='mauf':
            pm=nodes.get((l-1,c),0)
            if pm and ('nd',l-1,c) not in used: A=[(pm,('nd',l-1,c),'f')]
            elif not pm: A=[(0,None,'f')]
            for b in srcs+[(0,None)]:
                for a in A:
                    if a[0]&b[0]: continue
                    if b[1]==a[1]: continue
                    opts.append((a[0]|b[0],a[1],b[1]))
        else:
            for x,y in itertools.combinations(srcs+[(0,None)],2):
                if x[0]&y[0]: continue
                opts.append((x[0]|y[0],x[1],y[1]))
        # prune: remaining lines cannot... (no prune)
        for m,a,b in sorted(opts,key=lambda o:-bin(o[0]).count('1')):
            nn=dict(nodes); nn[(l,c)]=m
            nu=set(used)
            if a: nu.add(a)
            if b: nu.add(b)
            if rec(li,ltype,c+1,nn,nu): return True
        return False
    ok=rec(0,None,0,{},set())
    return results
if __name__=='__main__':
    pass
