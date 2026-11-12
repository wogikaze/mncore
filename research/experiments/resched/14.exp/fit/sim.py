import numpy as np
from scipy.optimize import linprog
f32=np.float32
def fma(a,b,c): # approx single-rounded fma
    return (np.float64(a)*np.float64(b)+np.float64(c)).astype(np.float32)
LN2F=np.float32(0.6931471805599453)
L=0.3466
def fit(deg, ties=[], lo=-L-1e-4, hi=L+1e-4, n=6001):
    r=np.linspace(lo,hi,n)
    w=np.where(r<2-3*np.log(2),8.0,4.0)
    # variable groups
    groups=[]; seen=set()
    for t in ties:
        groups.append(list(t)); seen|=set(t)
    for i in range(deg+1):
        if i not in seen: groups.append([i])
    A=np.stack([sum(r**i for i in g) for g in groups],1)*w[:,None]
    b=w*np.exp(r)
    m=len(groups)
    Aub=np.vstack([np.hstack([A,-np.ones((n,1))]),np.hstack([-A,-np.ones((n,1))])])
    res=linprog(np.r_[np.zeros(m),1],A_ub=Aub,b_ub=np.r_[b,-b],bounds=[(None,None)]*(m+1))
    c=[0]*(deg+1)
    for j,g in enumerate(groups):
        for i in g: c[i]=res.x[j]
    return res.x[-1],c
def run(x,c,log2e=np.float32(1.4426950408889634)):
    x=x.astype(np.float32)
    M=np.float32(12583040.0) # 1.5*2^23+128
    t=fma(x,log2e,M)
    kf=(t.astype(np.float64)-M).astype(np.float32)
    r=fma(kf,-LN2F,x)
    cc=[np.float32(v/2) for v in c]
    p=fma(r,cc[5],cc[4])
    for i in (3,2,1,0):
        p=fma(p,r,cc[i])
    tb=t.view(np.uint32)
    Sb=(tb<<np.uint32(23)).astype(np.uint32)
    S=Sb.view(np.float32)
    y=(p.astype(np.float64)*S).astype(np.float32)
    return y
x=np.random.default_rng(1).uniform(-14,2,2000000).astype(np.float32)
x=np.concatenate([x,np.linspace(1.5,2,500001).astype(np.float32)])
ex=np.exp(x.astype(np.float64))
for ties in [[],[(0,1)]]:
    E,c=fit(5,ties)
    y=run(x,c)
    err=np.abs(y-ex)
    print(ties,E,c, "maxerr",err.max(), x[err.argmax()])
