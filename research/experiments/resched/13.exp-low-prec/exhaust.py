"""model check: every f32 in given octaves of [-2,2]; plus bit-exact model-vs-emulator spot check."""
import numpy as np, model, dense, sys
from pathlib import Path
P=dict(A4=0.010084506124258041,A3=0.05305923521518707,A1=0.4768313765525818,A0=1.0052642822265625,C0=1.007557988166809)
f=lambda x: model.c8b(x,P['A4'],P['A3'],P['A1'],P['A0'],P['C0'])
# emulator vs model
body=dense.asm(Path('exp8.vsm').read_text()); keys=sorted(dense.tcx)
g=np.linspace(1.9,2,len(keys)).astype(np.float32)
r=dense.run(body,{k:float(v) for k,v in zip(keys,g)})
y=np.array([r[k] for k in keys],dtype=np.float32); print('emu-vs-model mismatches:',(y!=f(g)).sum())
worst=0
for lo in [2.0**-k for k in range(-1,24)]:
    for sgn in (1,-1):
        b0=np.float32(lo).view(np.uint32); n=1<<23
        if lo==2.0: n=1
        xs=(b0+np.arange(n,dtype=np.uint32)).view(np.float32)*np.float32(sgn)
        e=np.abs(f(xs).astype(float)-np.exp(xs.astype(float))); m=e.max()
        if m>worst: worst=m
        if m>0.006: print(f'octave {sgn*lo:+g}: max {m:.6f} at {xs[e.argmax()]}')
print('max over all f32 with |x| in [2^-23,2]:',worst)
