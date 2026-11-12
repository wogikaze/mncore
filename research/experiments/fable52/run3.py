import sys
NS = sys.argv[1:]; sys.argv = ["x"] + NS
import gen2
from sched import schedule3, render
ops = gen2.OPS
idx = {d: i for i, o in enumerate(ops) for d in o["dst"]}
extra = {idx[t]: [("X", "r")] for t in ("tS1", "tS2", "tT1", "tT2", "tT3", "tE1", "tE2")}
best = None
for seed in range(int(sys.argv[1]) if len(sys.argv) > 1 else 40):
    try:
        lines, pre = schedule3(ops, extra_deps=extra, noise=(4.0 + (seed % 5)) if seed else 0.0, seed=seed)
    except RuntimeError as e:
        continue
    if best is None or len(lines) < len(best[0]): best = (lines, pre, seed)
if best is None: print("all failed"); raise SystemExit
lines, pre, seed = best
open("/tmp/v2f.vsm", "w").write(render(lines) + "\n".join(gen2.TAIL) + "\n")
print("lines", len(lines), "pre", pre, "seed", seed, "total", len(lines) + len(gen2.TAIL))
