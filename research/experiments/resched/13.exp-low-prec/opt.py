import numpy as np, dense, model, sys
keys=sorted(dense.tcx)
tx=np.array([dense.tcx[k] for k in keys],dtype=np.float32); ty=np.array([dense.tcy[k] for k in keys])
print('expect vs exp(x32):',np.abs(ty-np.exp(tx.astype(float))).max())
gx=np.linspace(-2,2,400001).astype(np.float32); gy=np.exp(gx.astype(float))
def obj(p):
    e1=np.abs(model.c8(tx,*p).astype(float)-ty).max()
    e2=np.abs(model.c8(gx,*p).astype(float)-gy).max()
    return max(e1,e2),e1,e2
p=[np.float32(v) for v in (0.010129311408213236,0.05072228538980888,0.4860721629091754,1.003211173413711)]
best=obj(p); print('start',best)
rng=np.random.default_rng(0)
step=[2e-4,5e-4,2e-3,2e-3]
for it in range(3000):
    q=list(p)
    for i in range(4):
        if rng.random()<0.6: q[i]=np.float32(q[i]+rng.normal()*step[i])
    o=obj(q)
    if o[0]<best[0]: p,best=q,o; print(it,best,[float(v) for v in p]); sys.stdout.flush()
    if it%500==499: step=[s*0.6 for s in step]
print('final',best,[repr(float(v)) for v in p])
