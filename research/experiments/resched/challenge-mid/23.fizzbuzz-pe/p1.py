from fb import *
prog='''imm ui"0x3EAAAAAB" $lr32/1000
iadd $lm0v $aluf $nowrite
fvadd $aluf -$lr32 $ls0v
nop
fvmul $ls0v $lr32 $ln0v
'''
o=run(prog)
print(len(o))
bad=[a for a,v in o.items() if a%3==0 and (v&0x3ff)]
print('div3 with low10 nonzero',len(bad),bad[:5])
nz=[a for a,v in o.items() if a%3!=0 and (v&0x78)==0]
print('nondiv with 0x78 zero',len(nz))
for s in range(1,11):
    m=(1<<s)-1
    print(s, sum(1 for a,v in o.items() if a%3==0 and v&m), sum(1 for a,v in o.items() if a%3 and not v&m))
