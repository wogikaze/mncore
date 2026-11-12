import numpy as np
from scipy.optimize import linprog
from opt import *
xs=np.concatenate([np.linspace(-3,2,200001)]).astype(np.float32)
rd,Sd=front(xs); yd=np.exp(xs.astype(np.float64))
r,S=front(x); sel=np.where(x>-16)[0]
R=np.concatenate([r[sel],rd]).astype(np.float64); SS=np.concatenate([S[sel],Sd]).astype(np.float64); YY=np.concatenate([Y[sel],yd])
groups=[[0,1],[2],[3],[4],[5]]
A=np.stack([SS*sum(R**i for i in g) for g in groups],1)
n=len(R);m=len(groups)
res=linprog(np.r_[np.zeros(m),1],A_ub=np.vstack([np.hstack([A,-np.ones((n,1))]),np.hstack([-A,-np.ones((n,1))])]),b_ub=np.r_[YY,-YY],bounds=[(None,None)]*(m+1),method='highs')
c=[0]*6
for j,g in enumerate(groups):
    for i in g: c[i]=res.x[j]
print("LP",res.x[-1])
cb=[fb(v) for v in c]; cb[1]=cb[0]; cb[4]=(cb[4]&~63)|23
xs2=np.concatenate([np.random.default_rng(2).uniform(-14,2,1000000),np.linspace(0,2,1000001)]).astype(np.float32)
r2,S2=front(xs2); y2=np.exp(xs2.astype(np.float64))
def score(cb):
    et=np.abs(horner(r,S,cb).astype(np.float64)-Y).max()
    ed=np.abs(horner(r2,S2,cb).astype(np.float64)-y2).max()
    return et,ed
best=score(cb); print([hex(b) for b in cb],best)
rng=np.random.default_rng(1)
def key(s): return (s[0]>1e-6, s[1], s[0])
for it in range(1500):
    nb=list(cb)
    for i in [0,2,3,4,5]:
        if rng.random()<0.4: nb[i]+=int(rng.integers(-3,4))*(64 if i==4 else 1)
    nb[1]=nb[0]
    s=score(nb)
    if key(s)<key(best):
        best=s; cb=nb; print(it,[hex(b) for b in cb],s)
