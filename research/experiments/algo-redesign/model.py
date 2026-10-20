"""Python model of a per-word FizzBuzz generation algorithm.

Word o covers bytes [8o, 8o+8) of the concatenated FizzBuzz stream.
We model the stream as 15-token blocks per digit-width segment:
  d=1: n=1..9 (prefix, handled separately)
  d=2: n=10..99,  block size P=63
  d=3: n=100..999, block size P=71
  d=4: n=1000..6334, block size P=79 (last block partial)
Within a block (n0 = 10,100,1000; n0 % 15 == 10):
  cell j (0..14) is token n0+15k+j.
  lengths: d+1 for number cells, 5 for Fizz/Buzz, 9 for FizzBuzz (j=5).
"""
import codecs, re

# ---------- official expected stream ----------
ROOT='/home/wogikaze/wgkz/mncore'
TEST=ROOT+'/problems/challenge/20.fizzbuzz/testcase.vsm'
def build_stream():
    exp={}
    for m in re.finditer(r'd getd \$d(\d+)n0 1\s*#\s*expect="([^"]*)"', open(TEST).read()):
        exp[int(m.group(1))]=codecs.decode(m.group(2),'unicode_escape').encode('latin-1')
    out=bytearray()
    for i in range(4096): out+=exp[i]
    # last 2 bytes: pad with zeros to 32768
    out+=b'\x00'*(32768-len(out))
    return bytes(out), exp

STREAM, EXP = build_stream()

# segment data
SEG = [ (1,1,9,0), (2,10,99,30), (3,100,999,408), (4,1000,6334,4668) ]

def token(n):
    if n%15==0: return b'FizzBuzz'
    if n%3==0: return b'Fizz'
    if n%5==0: return b'Buzz'
    return str(n).encode()

TOK=[None]+[token(n) for n in range(1,6335)]
def cell_bytes(n):
    if n>6334: return b''
    return TOK[n] + (b'\n' if n<6334 else b'')

def segof(n):
    if n<10: return 0
    if n<100: return 1
    if n<1000: return 2
    return 3

# cell layout tables per segment d=2,3,4
def layout(d):
    n0={2:10,3:100,4:1000}[d]
    C=[0]; L=[]
    for j in range(15):
        n=n0+j
        t=TOK[n]
        l=len(t)+1  # token + newline always (blocks entirely before 6334)
        L.append(l); C.append(C[-1]+l)
    P=C[-1]
    return n0,C,L,P
LAY={d:layout(d) for d in (2,3,4)}

def word_recipe(o):
    """Return dict describing how to build word o."""
    B=8*o
    d = 0 if B<30 else (2 if B<408 else (3 if B<4668 else 4))
    if d==0:
        return dict(d=0,B=B)
    n0,C,L,P = LAY[d]
    S0={2:30,3:408,4:4668}[d]
    X=B-S0
    k=X//P; r=X-k*P
    # find j
    j=0
    while j<15 and C[j+1]<=r: j+=1
    off=r-C[j]
    n=n0+15*k+j
    return dict(d=d,B=B,S0=S0,P=P,k=k,r=r,j=j,off=off,n=n,n0=n0,C=C,L=L)

def cell_int(n):
    b=cell_bytes(n)
    # left-align in 128 bits so big-endian byte order starts at bit 120
    return int.from_bytes(b,'big') << (8*(16-len(b)))

def assemble_token_model(rec):
    off=rec['off']; n=rec['n']
    c=[cell_int(n+i) for i in range(4)]
    L=[len(cell_bytes(n+i)) for i in range(4)]
    M=(1<<64)-1
    acc=0
    for i in range(4):
        sh=8*(off-sum(L[:i]))
        if sh>=0:
            acc |= (c[i]<<sh)&((1<<128)-1)
        else:
            acc |= (c[i]>>(-sh))
    return (acc>>64)&M

def check():
    bad=[]
    for o in range(4096):
        rec=word_recipe(o)
        got=assemble_token_model(rec) if rec['d']!=0 else int.from_bytes(STREAM[8*o:8*o+8],'big')
        want=int.from_bytes(STREAM[8*o:8*o+8],'big')
        if got!=want: bad.append((o,rec,hex(got),hex(want)))
    return bad

if __name__=='__main__':
    bad=check()
    print('mismatched words:',len(bad))
    for b in bad[:5]: print(b)
    # stats
    from collections import Counter
    c=Counter()
    for o in range(4096):
        r=word_recipe(o); c[r['d']]+=1
    print('words per segment',c)
    # how many words need 3 tokens (i.e. off + 8 > L0+L1)
    three=0
    for o in range(4096):
        r=word_recipe(o)
        if r['d']==0: continue
        L=r['L']; off=r['off']
        if off+8 > L[r['j']]+L[(r['j']+1)%15]: three+=1
        if r['j']>=13 and off+8>L[r['j']]+L[(r['j']+1)%15]: pass
    print('words spanning 3+ tokens',three)
    # print some examples
    for o in [0,1,2,3,4,50,51,100,583,584,585,4095]:
        r=word_recipe(o)
        print(o,{k:r[k] for k in ('d','k','r','j','off','n') if k in r}, STREAM[8*o:8*o+8])
