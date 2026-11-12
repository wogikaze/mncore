import numpy as np, dense, model, sys
keys=sorted(dense.tcx)
tx=np.array([dense.tcx[k] for k in keys],dtype=np.float32); ty=np.array([dense.tcy[k] for k in keys])
gx=np.linspace(-2,2,400001).astype(np.float32); gy=np.exp(gx.astype(float))
def obj(p):
    e1=np.abs(model.c8b(tx,*p).astype(float)-ty).max()
    e2=np.abs(model.c8b(gx,*p).astype(float)-gy).max()
    return max(e1,e2),e1,e2
p=[np.float32(v) for v in sys.argv[1:6]]
best=obj(p); print('start',best)
rng=np.random.default_rng(int(sys.argv[6]) if len(sys.argv)>6 else 0)
step=np.array([1e-4,4e-4,1e-3,1e-3,1e-3])
for it in range(4000):
    q=list(p)
    for i in range(5):
        if rng.random()<0.5: q[i]=np.float32(q[i]+rng.normal()*step[i])
    o=obj(q)
    if o[0]<best[0]: p,best=q,o
    if it%500==499: step*=0.6; print(it,best,[repr(float(v)) for v in p]); sys.stdout.flush()
print('final',best,[repr(float(v)) for v in p])
