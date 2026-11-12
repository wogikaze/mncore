import sys,subprocess
lines=open(sys.argv[1]).read().splitlines()
n=int(sys.argv[2]); gets=sys.argv[3:]
prog=lines[:n]+[ "d get "+g for g in gets]
open('/tmp/cu_step.vsm','w').write("\n".join(prog)+"\n")
out=subprocess.run(['./emu.sh','/tmp/cu_step.vsm'],capture_output=True,text=True).stdout
for l in out.splitlines():
    if l.startswith('DEBUG'):
        h,rest=l.split(':',1)
        v=rest.split('v:')[-1].split(')')[0] if 'v:' in rest else rest
        print(h, v, l.split('#')[-1])
    else: print(l)
