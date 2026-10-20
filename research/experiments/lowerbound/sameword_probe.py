import subprocess, tempfile
from pathlib import Path
ROOT=Path('/home/wogikaze/wgkz/mncore'); EM=ROOT/'judge/judge-py/mncore2_emuenv'
def run(name, body, init='zero'):
    src=body+"d get $ls2n0c0b0m0p0 4\n"
    with tempfile.TemporaryDirectory() as td:
        p=subprocess.run([str(EM/'assemble3'),'--instruction-mode','flat'],input=src.encode(),capture_output=True)
        if p.returncode:
            print(name,'ASM FAIL',p.stderr.decode(errors='replace')[:200].replace('\n',' | ')); return
        f=Path(td)/'a.asm'; f.write_text(p.stdout.decode()); d=Path(td)/'o.dmp'
        q=subprocess.run([str(EM/'gpfn3_package_main'),'-i',str(f),'-d',str(d),'--offchip-memory-init',init],capture_output=True)
        txt=(d.read_text() if d.exists() else '')+q.stdout.decode(errors='replace')+q.stderr.decode(errors='replace')
        vals=[l for l in txt.splitlines() if 'GREG1' in l]
        print(name, '=>', vals[0][:130] if vals else 'NO DUMP')
# Does an L1BM read + ALU write of same reg in same word assemble? What value is read?
# First set s0=1111..., then in one word l1bmd reads s0 while ipassa writes s0=2222...
run('same-word l1bmd s0 + ALU writes s0',
    'imm i"0x11111111" $ls0\nnop\nnop\nl1bmd $ls0 $lb0; ipassa $t $ls0/1100\nnop\nnop\nl1bmd $lb0 $ls2\n')
run('control: l1bmd s0 alone',
    'imm i"0x11111111" $ls0\nnop\nnop\nl1bmd $ls0 $lb0\nnop\nnop\nl1bmd $lb0 $ls2\n')
run('ALU writes s0=2222, then l1bmd reads it',
    'imm i"0x22222222" $ls0\nnop\nl1bmd $ls0 $lb0\nnop\nnop\nl1bmd $lb0 $ls2\n')
