import re, numpy as np
from pathlib import Path
T=Path('/home/wogikaze/wgkz/mncore/problems/14.exp/testcase.vsm').read_text()
X={};Y={}
for l in T.splitlines():
    m=re.search(r"values=\[([^\]]*)\].*@\[(\d+),(\d+)\],\[(\d+),(\d+)\]",l)
    if m:
        v=[float(s) for s in m[1].split(",")]
        X[(int(m[2]),int(m[3]))]=v[0]; X[(int(m[4]),int(m[5]))]=v[1]
    m=re.search(r"expect=\[([^\]]*)\].*@\[(\d+),(\d+)\],\[(\d+),(\d+)\]",l)
    if m:
        v=[float(s) for s in m[1].split(",")]
        Y[(int(m[2]),int(m[3]))]=v[0]; Y[(int(m[4]),int(m[5]))]=v[1]
keys=sorted(Y)
x=np.array([X[k] for k in keys],dtype=np.float32); y=np.array([Y[k] for k in keys])
np.save('/tmp/e14/tx.npy',x); np.save('/tmp/e14/ty.npy',y)
print(len(x), x.min(), x.max(), (x>-14).sum(), (x>0.3).sum())
d=y-np.exp(x.astype(np.float64)); print("expected-exp(x32): max", np.abs(d).max(), "rel", np.abs(d/y)[x>-14].max())
