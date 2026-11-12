"""Parse testcase: A[l2b][row][col], B[l2b][row]."""
import re, struct
from pathlib import Path
ROOT = Path(__file__).resolve().parents[4]
tc = (ROOT/"problems/12.divrow-vec/testcase.vsm").read_text()
pre = tc.split("# ======= YOUR VSM")[0]
def f32(h): return struct.unpack('>f', bytes.fromhex(h))[0]
lm = {}  # (l2b, pe, addr) -> float
for m in re.finditer(r'd set \$lm(\d+)n(\d)c0(?:p(\d))? 1 ([0-9A-F]{16})', pre):
    a, n, p, h = int(m[1]), int(m[2]), m[3], m[4]
    pes = [int(p)] if p is not None else range(4)
    for pe in pes:
        lm[(n, pe, a)] = f32(h[:8]); lm[(n, pe, a+1)] = f32(h[8:])
B = [[lm[(n, 0, 256+r)] for r in range(64)] for n in range(4)]
A = [[[lm[(n, pe, 4*r+w)] for pe in range(4) for w in range(4)] for r in range(64)] for n in range(4)]
