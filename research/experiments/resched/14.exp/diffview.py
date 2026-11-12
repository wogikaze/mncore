import sys,re
prev={}
cur=None
for line in open(sys.argv[1]):
    if line.startswith("==="):
        if cur is not None:
            ch=[f"{k}={v}" for k,v in cur.items() if prev.get(k)!=v]
            print("    "+"  ".join(ch)); prev.update(cur)
        print(line.rstrip()); cur={}
        continue
    m=re.search(r"DEBUG-(\w+)\(([^,]+),(\d+)\):(.*?)#",line)
    if m:
        cur[f"{m[1]}{m[3]}"]=m[4].strip().split(") (")[0].strip("(")
ch=[f"{k}={v}" for k,v in cur.items() if prev.get(k)!=v]
print("    "+"  ".join(ch))
