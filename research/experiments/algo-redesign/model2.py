"""Python model of the per-byte (per-lane) algorithm for the d=4 segment.

For each output byte offset X in [4668,32766):
  k = floor((X-4668)/79); u = X-4668-79k
  u' = u - 4*[u>=34]; j = u'//5; off = u'-5j
  n = 1000+15k+j
  FB region: 25 <= u < 34  -> char = "FizzBuzz\n"[u-25]
  else if token(n) is Fizz/Buzz -> char = token(n)[off]  (off<4 digits? specials are 5 chars)
  else if off==4 -> '\n'
  else -> digit n at position off
"""
import model
STREAM=model.STREAM
FB=b'FizzBuzz\n'
def char_at(X):
    if X>=32766: return 0
    k=(X-4668)//79; u=X-4668-79*k
    if 25<=u<34: return FB[u-25]
    up=u-4*(u>=34)
    j=up//5; off=up-5*j
    n=1000+15*k+j
    t=model.token(n)
    if len(t)==4:  # number
        return t[off] if off<4 else 10
    # Fizz/Buzz (len 4) -> +'\n'
    return t[off] if off<4 else 10
bad=0; first=[]
for o in range(4096):
    B=8*o
    if B<4668: continue
    want=STREAM[B:B+8]
    got=bytes(char_at(B+i) for i in range(8))
    if got[:len(want)]!=want:
        bad+=1
        if len(first)<8: first.append((o,B,got,want))
print('d=4 words',sum(1 for o in range(4096) if 8*o>=4668),'bad',bad)
for f in first: print(f)
