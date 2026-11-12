# Enumerate single-ALU-op T setups (12-word candidates): op $l2bid [src2] $t ; nop ; l1bmd <operand> $lb0 ; ...
import sys, itertools
sys.path.insert(0, "/home/wogikaze/wgkz/mncore/tools"); sys.path.insert(0, "/home/wogikaze/wgkz/mncore")
from golfcheck import Checker
ck = Checker("27.dram-ul-16-1024")
REST = """nop
nop
l2bmd $lb0 $lc0
l2bmd $lb32 $lc256
l2bmd $lb64 $lc512
l2bmd $lb96 $lc768
nop
mvp/n1024 $lc0@.0 $d0
mvp/n1024 $lc0@.1 $d1024
"""
bin_ops = ["add","sub","packbit","lsl","lsr","bsl","bsr","and","or","xor","max","min"]
un_ops = ["passa","inc","dec","not","lnot","ftoi","floor"]
precs = ["i","l","s","h","f","d","u","ui","ul","us"]
seconds = ["$r0","$lm0","$lm32","$ln0","$t","$lr0v","$lm0v","$lm2","$lm1"]
firsts = []
for p in precs:
    for o in bin_ops:
        for s in seconds:
            firsts.append(f"{p}{o} $l2bid {s} $t")
    for o in un_ops:
        firsts.append(f"{p}{o} $l2bid $t")
operands = ["$lmt0v","$llmt0v","$lmt0","$lmt0v2","$lmt0v4","$llmt0v2","$lmt[0,2,4,6]"]
seen=0; hits=[]
for f in firsts:
    for opnd in operands:
        text = f + "\nnop\n" + f"l1bmd {opnd} $lb0\n" + REST
        run = ck._run(text)
        seen+=1
        if run.error or not run.dump: continue
        bad = sum(1 for k,v in ck.expected.items() if run.dump.get(k)!=v)
        if bad < 4096:
            print(bad, repr(f), opnd, flush=True)
        if bad==0:
            r = ck.check(text); print("FULL", r); hits.append(text)
print("tried", seen, "hits", len(hits))
