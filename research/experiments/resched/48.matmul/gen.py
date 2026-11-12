"""gen.py out.vsm spec.py : build a candidate from base.vsm.
spec defines ADD (line->expr, 1-based), MODE ('dbl' or 'swap'), TAIL list, optional BODY transform."""
import re,sys
base=open('base.vsm').read().splitlines()
spec={}
exec(open(sys.argv[2]).read(),spec)
body=base[:56]
mode=spec.get('MODE','dbl')
def perm(l):
    def r(m):
        c=int(m.group(2))//256
        d=512*c+256 if mode=='dbl' else 256*(c^1)
        return f"l2bmd $lb{m.group(1)} $lc{d}"
    return re.sub(r"l2bmd \$lb(\d+) \$lc(\d+)", r, l)
body=[perm(l) for l in body]
if 'BODY' in spec: body=spec['BODY'](body)
for k,v in sorted(spec['ADD'].items()):
    for e in (v if isinstance(v,list) else [v]):
        body[k-1]= e if body[k-1]=='nop' else body[k-1]+';'+e
n=16384 if mode=='dbl' else 8192
tail=spec.get('TAIL',[f'mvrffadd/n{n} $lc0 $p0@0',f'mvb/n{n} $p0@0 $lc0',f'mvp/n{n}nd16 $lc0@.0 $di0'])
open(sys.argv[1],'w').write("\n".join(body+tail)+"\n")
