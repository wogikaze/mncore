import subprocess
from pathlib import Path
ASM=Path('/home/wogikaze/wgkz/mncore/judge/judge-py/mncore2_emuenv/assemble3')
for body in ['mvd/n64 $p0@0 $d0\n','mvd/n64 $p0@0 $d0@0\n','mvd/n64 $p0 $d0@0\n','mvd/n64 $p0@0 $d0@1\n','mvd/n16384 $p0@0 $d0\n']:
    p=subprocess.run([str(ASM),'--instruction-mode','flat'],input=('nop\n'+body).encode(),capture_output=True)
    err=next((l.strip() for l in p.stderr.decode(errors='replace').splitlines() if l.strip()),'')
    print(('OK   ' if p.returncode==0 else 'FAIL ')+body.strip()+('  '+err[:80] if err else ''))
