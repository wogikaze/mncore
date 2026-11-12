"""rounding-aware iterated LP for the c8b structure (testcase + dense grid)."""
import numpy as np, dense, model, sys
from scipy.optimize import linprog
keys=sorted(dense.tcx)
tx=np.array([dense.tcx[k] for k in keys],dtype=np.float32); ty=np.array([dense.tcy[k] for k in keys])
gx=np.linspace(-2,2,40001).astype(np.float32); gy=np.exp(gx.astype(float))
X=np.r_[tx,gx]; Yt=np.r_[ty,gy]
Gx=np.linspace(-2,2,400001).astype(np.float32); Gy=np.exp(Gx.astype(float))
def exact(x,p):
    C0,A0,A1,A3,A4=p; x=x.astype(float)
    return C0+A0*x+A1*x**2+16*A4*x**3+A3*x**4+float(model.h(np.float32(A4)))*x**5
def sim(x,p):
    C0,A0,A1,A3,A4=p; return model.c8b(x,A4,A3,A1,A0,C0).astype(float)
def full(p):
    return max(np.abs(sim(tx,p)-ty).max(), np.abs(sim(Gx,p)-Gy).max())
p=np.array([float(v) for v in sys.argv[1:6]]) if len(sys.argv)>5 else np.array([1.0028804540634155,1.003490924835205,0.48619675636291504,0.05077836290001869,0.010116133838891983])
D=float(sys.argv[6]) if len(sys.argv)>6 else 0.5
best=(full(p),p.copy()); print('start',best[0])
xd=X.astype(float)
B=np.stack([np.ones_like(xd),xd,xd**2,xd**4,16*xd**3+xd**5],1)
for it in range(30):
    r=sim(X,p)-exact(X,p)   # rounding residual
    g=Yt-r
    m=B.shape[1]; c=np.r_[np.zeros(m),1]
    Aub=np.r_[np.c_[B,-np.ones(len(xd))],np.c_[-B,-np.ones(len(xd))]]
    sol=linprog(c,A_ub=Aub,b_ub=np.r_[g,-g],bounds=[(None,None)]*(m+1))
    q=sol.x[:m]; q=np.array([q[0],q[1],q[2],q[3],q[4]])
    # damped update
    p=(1-D)*p+D*q
    p=np.array([float(np.float32(v)) for v in p])
    f=full(p); print(it,'lp',sol.x[-1],'full',f)
    if f<best[0]: best=(f,p.copy())
print('best',best[0],[repr(v) for v in best[1]])
