"""Doubled-range DAR version: real chunk k at lc 512k+256, DAR entries pairs (2k,2k+1) both = 16k ^ 128g."""
import re,sys
base=open('base.vsm').read().splitlines()
body=base[:56]   # includes trailing nop (line 56)
def perm(l):
    return re.sub(r"l2bmd \$lb(\d+) \$lc(\d+)", lambda m: f"l2bmd $lb{m.group(1)} $lc{512*(int(m.group(2))//256)+256}", l)
body=[perm(l) for l in body]
add={3:'imm i"4" $ln200', 6:'ilsl $peid $ln200 $t', 15:'imm i"6" $nowrite', 16:'ilsl $l2bid $aluf $nowrite',
     17:'ixor $aluf $t $nowrite', 18:'l1bmd $aluf $lb4096', 21:'l2bm@0 $lb4096 $lc0', 23:'l2bmdars $lc0@.0 $dar0;l2bmdarw'}
for i in range(24,39): add[i]='l2bmdarw'
for k,v in add.items(): body[k-1]=body[k-1]+';'+v if body[k-1]!='nop' else v
tail=['mvrffadd/n16384 $lc0 $p0@0','mvb/n16384 $p0@0 $lc0','mvp/n16384nd16 $lc0@.0 $di0']
open(sys.argv[1],'w').write("\n".join(body+tail)+"\n")
