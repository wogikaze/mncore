# run vsm (with d set allowed) and compare DRAM group0 [0:16384] against expected
import sys,subprocess,re
src=open(sys.argv[1]).read()
src+="\nd getd $d0n0 16384\n"
open('/tmp/cu_chk.vsm','w').write(src)
out=subprocess.run(['./emu.sh','/tmp/cu_chk.vsm'],capture_output=True,text=True).stdout
vals=[int(m.group(1),16) for m in re.finditer(r'DEBUG-DRAM\(n0,\d+\):\([^)]*\) \(0x([0-9A-Fa-f]+)\)',out)]
bad=[k for k in range(16384) if k>=len(vals) or vals[k]!=(((2*k+1)<<32)|(2*k+2))]
print("n",len(vals),"bad",len(bad), [(k,hex(vals[k]) if k<len(vals) else None) for k in bad[:8]])
if len(vals)==0: print(out[:2000])
