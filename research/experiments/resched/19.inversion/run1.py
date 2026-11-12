from redsearch import search
import sys,time
items=[('B%d'%c,13,c) for c in range(4)]+[('A%d'%c,14,c) for c in range(4)]
F=int(sys.argv[1]); fin=[int(x) for x in sys.argv[2].split(',')]
t=time.time()
r=search(items,15,F,fin)
print(time.time()-t, r[:1])
