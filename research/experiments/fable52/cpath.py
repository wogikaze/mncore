import sys, functools, importlib
mod = sys.argv[1] if len(sys.argv) > 1 else "gen2"
sys.argv = ["x"]
g = importlib.import_module(mod)
ops = g.OPS
prod = {d: i for i, o in enumerate(ops) for d in o["dst"]}
@functools.lru_cache(None)
def cp(i):
    o = ops[i]; best = 0
    for v, _ in o["src"]:
        p = prod[v]; L = 3 if ops[p]["unit"] == "imm" else 2
        best = max(best, cp(p) + L)
    if o["fwd"]: best = max(best, cp(prod[o["fwd"]]) + 1)
    return best
last = max(range(len(ops)), key=cp)
print("critical path:", cp(last))
i = last; path = []
while True:
    path.append((cp(i), ops[i]["text"][:56]))
    o = ops[i]; nxt = None
    for v, _ in o["src"]:
        p = prod[v]; L = 3 if ops[p]["unit"] == "imm" else 2
        if cp(p) + L == cp(i): nxt = p
    if o["fwd"] and cp(prod[o["fwd"]]) + 1 == cp(i): nxt = prod[o["fwd"]]
    if nxt is None: break
    i = nxt
for x in reversed(path): print(x)
from collections import Counter
print(Counter(o["unit"] for o in ops))
