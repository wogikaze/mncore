# Can one ALU op on an imm value V (with half(V) in [8,16) so it can feed hvadd) and a fixed
# operand ($msb1 / 0) give the iadd constant T'(K) = 0x01800000-(K-8)*2^20 (or the xor / isub forms)?
import numpy as np
lo=np.float32(8-2**-8).view(np.uint32); hi=np.float32(16).view(np.uint32)
V=np.arange(int(lo),int(hi),dtype=np.uint64)
K=V.astype(np.uint32).view(np.float32).astype(np.float16).astype(np.float64)
ok=(K>=8)&(K<16); V=V[ok]; K=K[ok]
Tadd=(0x01800000-((K-8)*2**20)).astype(np.int64)
Txor=(0x03800000^((K-8)*2**20).astype(np.int64))
M=0xffffffff
def ops(x,y,bits):
    m=(1<<bits)-1
    s=y%(2*bits)
    yield 'add',(x+y)&m; yield 'sub',(x-y)&m; yield 'sub_r',(y-x)&m
    yield 'and',x&y; yield 'or',x|y; yield 'xor',x^y
    yield 'lsl',np.where(s>=bits,0,(x<<np.minimum(s,bits-1))&m)
    yield 'lsr',np.where(s>=bits,0,x>>np.minimum(s,bits-1))
    ss=np.where(s>=bits,s-bits,s)
    yield 'bsl',((x<<ss)|(x>>(bits-ss)))&m
    yield 'bsr',((x>>ss)|(x<<(bits-ss)))&m
    yield 'packbit',((x<<1)|(y>>(bits-1)))&m
    yield 'not',(~x)&m
def lanes(v,bits):
    if bits==32: return [v]
    return [(v>>16)&0xffff, v&0xffff]
found=0
for xs in ['V','msb1','zero']:
  for bits in (32,16):
    if xs=='V': X=lanes(V,bits)
    elif xs=='msb1': X=[np.full_like(V,1<<(bits-1))]*(1 if bits==32 else 2)
    else: X=[np.zeros_like(V)]*(1 if bits==32 else 2)
    Y=lanes(V,bits)
    res={}
    for i,(xx,yy) in enumerate(zip(X,Y)):
        for n,r in ops(xx,yy,bits): res.setdefault(n,[]).append(r)
    for n,rs in res.items():
        r=rs[0] if bits==32 else ((rs[0]<<16)|rs[1])
        r=r.astype(np.int64)
        for tn,T in (('add',Tadd),('isub',(-Tadd)&M),('xor',Txor)):
            d=np.abs(((r-T+2**31)&M)-2**31)
            hit=d<=13
            if hit.any():
                found+=1; i=np.argmax(hit); print(xs,bits,n,tn,hex(int(V[i])),hex(int(r[i])),hit.sum())
print('found',found)
# list all lsl hits
s=V%64; r=np.where(s>=32,0,(V<<np.minimum(s,31))&M).astype(np.int64)
for tn,T in (('add',Tadd),('isub',(-Tadd)&M),('xor',Txor)):
    d=np.abs(((r-T+2**31)&M)-2**31)
    for i in np.nonzero(d<=13)[0]: print(tn,hex(int(V[i])),'K=',K[i],'T=',hex(int(r[i])), 'V=',np.uint32(V[i]).view(np.float32))
