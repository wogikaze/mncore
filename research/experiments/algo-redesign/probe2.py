import sys
sys.path.insert(0,'/home/wogikaze/wgkz/mncore')
from mncompile.sim import simulator
s=simulator()
prog=sys.argv[1]
r=s.run(prog)
print('err',r.error,r.part,r.line)
for k,v in sorted(r.dump.items())[:40]: print(k,hex(v))
