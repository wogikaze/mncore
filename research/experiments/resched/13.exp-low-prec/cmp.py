import sys, numpy as np
sys.argv=[sys.argv[0]]+sys.argv[1:]
import dense, model
from pathlib import Path
body=dense.asm(Path('c8.vsm').read_text())
keys=sorted(dense.tcx)
r=dense.run(body,dense.tcx)
x=np.array([dense.tcx[k] for k in keys],dtype=np.float32); y=np.array([r[k] for k in keys],dtype=np.float32)
m=model.c8(x,0.010129311408213236,0.05072228538980888,0.4860721629091754,1.003211173413711)
d=(m!=y); print('mismatch',d.sum(),'maxdiff',np.abs(m.astype(float)-y).max())
