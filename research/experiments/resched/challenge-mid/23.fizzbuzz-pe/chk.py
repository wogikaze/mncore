import sys
from fb import run
def f(a):
    if a%15==0: return 0xFFFFBBBB
    if a%3==0: return 0x0000FFFF
    if a%5==0: return 0x0000BBBB
    return a
o=run(open(sys.argv[1]).read())
from collections import Counter
c=Counter(); ex={}
for a,v in o.items():
    cls=('15' if a%15==0 else '3' if a%3==0 else '5' if a%5==0 else '-')
    ok=v==f(a)
    c[(cls,ok)]+=1
    if not ok and cls not in ex: ex[cls]=(a,hex(v))
print(sorted(c.items())); print(ex)
