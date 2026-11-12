from emu import *
import sys
def T(patx, s, acc):
    prog=[f'imm ui"{patx}" $ls2', f'imm ui"{s}" $lr8', f'imm ui"{acc}" $ln0','nop','nop',
          'fvfma $ls2 $lr8 $ln0 $lr20','nop','nop']
    t=run(prog,{8:['getf $lr20n0c0b0m0p0 1']})
    return t.split('\n')[0]
for p in ['0xFFFFFF9C','0xFFFFFFFF','0x00000005','0x80000005','0x7F800000','0x7FFFFF9C']:
    print(p, T(p,'0x0A800000','0x3F800000'))
