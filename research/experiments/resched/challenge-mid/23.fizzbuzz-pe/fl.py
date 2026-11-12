import sys
sys.path.insert(0,'/home/wogikaze/wgkz/mncore')
from mncompile.sim import official_run
from fb import pre
def run(prog, n=4):
    r=official_run(prog, pre, "d getd $ln0n0c0b0m0p0 %d\n"%n)
    if r.error: return r.error
    return ' '.join('%016x'%r.dump[('LM1','n0c0b0m0p0',2*i)] for i in range(n))
for x in ['0x3c00bc00','0xbc003c00','0x3c003c00','0xbc00bc00']:
    for op in ['hvpassa','fvpassa']:
        prog=f'''imm ui"{x}" $nowrite
{op} $aluf $omr1
imm ui"0x11111111" $ln0v
nop
nop
imm ui"0xFFFFFFFF" $ln0v/$imr1
'''
        print(x,op,run(prog))
