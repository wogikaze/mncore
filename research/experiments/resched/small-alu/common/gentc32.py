"""Rewrite a 2-values-per-long-word int testcase (13.mod3 / 24.log2) with new inputs.
usage: gentc32.py <problem dir> <mode: mod3|log2> <seed> <out>"""
import re, sys, random
pdir, mode, seed, outp = sys.argv[1], sys.argv[2], int(sys.argv[3]), sys.argv[4]
random.seed(seed)
src = open(pdir + '/testcase.vsm').read()
vals = {}
if mode == 'mod3':
    pool = list(range(256)); f = lambda v: v % 3; gen = lambda: random.randrange(256)
else:
    pool = [1 << k for k in range(12)]; f = lambda v: v.bit_length() - 1; gen = lambda: random.choice(pool)
out, idx = [], 0
for line in src.splitlines():
    m = re.match(r"(d set \$lm(\d+)m(\d+)p(\d) 1 )[0-9A-F]+( # values=)\[\d+, \d+\](.*)", line)
    g = re.match(r"(d getd \$ln(\d+)n0c0b0m(\d+)p(\d) 1 # expect=)\[\d+, \d+\](.*)", line)
    if m:
        key = (m.group(2), m.group(3), m.group(4))
        a = pool[idx % len(pool)] if seed == 0 else gen(); idx += 1
        b = pool[idx % len(pool)] if seed == 0 else gen(); idx += 1
        vals[key] = (a, b)
        line = f"{m.group(1)}{a:08X}{b:08X}{m.group(5)}[{a}, {b}]{m.group(6)}"
    elif g:
        a, b = vals[(g.group(2), g.group(3), g.group(4))]
        line = f"{g.group(1)}[{f(a)}, {f(b)}]{g.group(5)}"
    out.append(line)
open(outp, 'w').write("\n".join(out) + "\n")
