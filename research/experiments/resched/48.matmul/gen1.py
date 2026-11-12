import re,sys
base=open('base.vsm').read().splitlines()
body=base[:55]
# permute l2bmd destinations: chunk c -> c^1
def perm(l):
    def rep(m):
        a=int(m.group(1)); c=a//256; return f"l2bmd $lb{m.group(2)} $lc{256*(c^1)}"
    return re.sub(r"l2bmd \$lb(\d+) \$lc(\d+)", lambda m: f"l2bmd $lb{m.group(1)} $lc{256*((int(m.group(2))//256)^1)}", l)
body=[perm(l) for l in body]
pro=[
 'imm i"5" $lr200',
 'imm i"6" $lr202',
 'nop','nop',
 'ilsl $peid $lr200 $lr204',
 'ilsl $l2bid $lr202 $ls206',
 'nop','nop',
 'ixor $lr204 $ls206 $lr208',
 'immu i"16" $ls210',
 'nop','nop',
 'ior $lr208 $ls210 $lr212',
 'nop','nop',
 'l1bmd $lr212 $lb4096',
 'nop','nop','nop','nop',
 'l2bm@0 $lb4096 $lc8192',
 'nop','nop','nop',
 'l2bmdars $lc8192@.0 $dar0;l2bmdarw',
]+['l2bmdarw']*7+['nop']*2
tail=['nop','mvrffadd/n8192 $lc0 $p0@0','mvb/n8192 $p0@0 $lc0','mvp/n8192nd16 $lc0@.0 $di0']
open(sys.argv[1],'w').write("\n".join(pro+body+tail)+"\n")
