import itertools
# Upper bound on |M| per op ignoring overlap. 'G' growth op (fmax), 'S' shift op. GRF read gap 2.
for n in (7,8):
  for pat in itertools.product('GS', repeat=n):
    if pat.count('S')<3 or pat[-1]!='G': continue
    a=[]
    for t,o in enumerate(pat):
        stored=[a[s] for s in range(t-1)]
        al=a[t-1] if t>0 else 0
        if o=='S':
            v=max([al]+stored+[1])
        else:
            v=max([al+1]+[al+s for s in stored]+[x+y for x,y in itertools.combinations(stored,2)]+[s+1 for s in stored]+[1])
        a.append(v)
    if a[-1]>=16: print(n,''.join(pat),a)
