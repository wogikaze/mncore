import sys, importlib
mod = sys.argv[1] if len(sys.argv) > 1 else "gen2"
tries = int(sys.argv[2]) if len(sys.argv) > 2 else 300
out = sys.argv[3] if len(sys.argv) > 3 else "/tmp/best.vsm"
sys.argv = ["x"]
g = importlib.import_module(mod)
from sched import schedule_best, render
lines, line_of, t = schedule_best(g.OPS, tries=tries)
open(out, "w").write(render(lines) + "\n".join(g.TAIL) + "\n")
print("best lines", len(lines), "total", len(lines) + len(g.TAIL), "try", t)
