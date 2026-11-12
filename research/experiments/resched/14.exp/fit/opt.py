import numpy as np, struct, sys
from scipy.optimize import linprog
x=np.load('/tmp/e14/tx.npy'); Y=np.load('/tmp/e14/ty.npy')
def bf(b): return np.array([b],dtype=np.uint32).view(np.float32)[0]
def fb(v): return int(np.array([v],dtype=np.float32).view(np.uint32)[0])
def fma(a,b,c): return (a.astype(np.float64)*np.float64(b) if np.isscalar(b) or b.dtype!=object else None)
def F(a,b,c):
    return (np.float64(a)*np.float64(b)+np.float64(c)).astype(np.float32)
LOG2E=bf(0x3FB8AA3B); M=np.float32(12583040.0)
def front(x, ln2b=0x3F317218):
    t=F(x,LOG2E,M); kf=(t.astype(np.float64)-M).astype(np.float32)
    r=F(kf,-bf(ln2b),x)
    S=(t.view(np.uint32)<<np.uint32(23)).view(np.float32)
    return r,S
def horner(r,S,cb):  # cb = bits of halved coeffs c0..c5
    c=[bf(b) for b in cb]
    p=F(r,c[5],c[4])
    for i in (3,2,1,0): p=F(p,r,c[i])
    return (p.astype(np.float64)*S).astype(np.float32)
def err(cb,ln2b=0x3F317218):
    r,S=front(x,ln2b); y=horner(r,S,cb); return np.abs(y.astype(np.float64)-Y)
if __name__=="__main__":
    cb=[0x3F000001,0x3F000001,0x3E7FFE8B,0x3DAAAB48,0x3CABAB97,0x3B885E66]
    e=err(cb); print(e.max(), np.sort(e)[-5:])
