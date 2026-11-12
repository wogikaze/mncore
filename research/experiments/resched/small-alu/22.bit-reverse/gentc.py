import random, re, sys
src = open('../../../../../problems/challenge/22.bit-reverse/testcase.vsm').read()
seed = int(sys.argv[1]); random.seed(seed)
X = [random.getrandbits(64) for _ in range(16)]
if seed == 0: X = [(1 << 64) - 1] * 16
if seed == 1: X = [1 << (i * 4 % 64) for i in range(16)]
def rev(x): return int(f"{x:064b}"[::-1], 2)
out = []
for line in src.splitlines():
    m = re.match(r"d set \$lm(\d+)p(\d) 1 ([0-9A-F]+) # values=\[\d+\] / ULong @\[(\d+)\]", line)
    g = re.match(r"(d getd \$ln\d+n0c0b0m0p\d 1) # expect=\[\d+\] / ULong @\[(\d+)\]", line)
    if m:
        i = int(m.group(4)); line = f"d set $lm{m.group(1)}p{m.group(2)} 1 {X[i]:016X} # values=[{X[i]}] / ULong @[{i}]"
    elif g:
        i = int(g.group(2)); y = rev(X[15 - i]); line = f"{g.group(1)} # expect=[{y}] / ULong @[{i}]"
    out.append(line)
open(f'tc{seed}.vsm', 'w').write("\n".join(out) + "\n")
