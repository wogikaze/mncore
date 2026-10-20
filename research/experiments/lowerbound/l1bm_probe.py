import subprocess, tempfile
from pathlib import Path
ROOT=Path('/home/wogikaze/wgkz/mncore'); EM=ROOT/'judge/judge-py/mncore2_emuenv'
def run(name, body):
    src=body+"d get $ls2n0c0b0m0p0 8\n"
    with tempfile.TemporaryDirectory() as td:
        p=subprocess.run([str(EM/'assemble3'),'--instruction-mode','flat'],input=src.encode(),capture_output=True)
        if p.returncode:
            print(name,'ASM FAIL',p.stderr.decode(errors='replace')[:300]); return
        f=Path(td)/'a.asm'; f.write_text(p.stdout.decode()); d=Path(td)/'o.dmp'
        q=subprocess.run([str(EM/'gpfn3_package_main'),'-i',str(f),'-d',str(d),'--offchip-memory-init','zero'],capture_output=True)
        txt=(d.read_text() if d.exists() else '')+q.stdout.decode(errors='replace')+q.stderr.decode(errors='replace')
        print('==',name)
        for line in txt.splitlines():
            if 'DEBUG-' in line and ('GREG1' in line or 'TREG' in line): print('  ',line[:150])
run('imm -> 2nop -> l1bmd ls0 -> 2nop -> l1bmd lb0 -> ls2',
    'imm i"0x12345678" $ls0\nnop\nnop\nl1bmd $ls0 $lb0\nnop\nnop\nl1bmd $lb0 $ls2\n')
run('imm -> l1bmd aluf -> 2nop -> l1bmd lb0 -> ls2',
    'imm i"0x12345678" $ls0\nl1bmd $aluf $lb0\nnop\nnop\nl1bmd $lb0 $ls2\n')
run('ipassa t -> 1nop -> l1bmd ls0 -> 2nop -> l1bmd lb0 -> ls2',
    'ipassa $t $ls0/1100\nnop\nl1bmd $ls0 $lb0\nnop\nnop\nl1bmd $lb0 $ls2\n')
