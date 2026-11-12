import sys; from emu import *
prog=open(sys.argv[1]).read().split('\n')
loc=sys.argv[2]
lines=[int(x) for x in sys.argv[3].split(',')]
specs=sys.argv[4:]
d={i:[f'get $l{s.split(":")[0]}{loc} {s.split(":")[1]}' for s in specs] for i in lines}
t=run(prog,d)
if t.startswith('ASM'): print(t[:500]); sys.exit()
cur=None
for l in t.split('\n'):
    m=re.match(r'DEBUG-([A-Z0-9]+)\((\w+),(\d+)\):.*?v:0x([0-9A-Fa-f]+).*#d get (\S+)',l)
    if not m: continue
    v=int(m.group(4),16); a,b=v>>32,v&0xffffffff
    print(f'{m.group(5)[:6]}{m.group(3):>5}: {a:08x} {b:08x}  ({a}, {b})  f=({f32(a):.10g}, {f32(b):.10g})')
