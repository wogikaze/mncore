import subprocess, tempfile
from pathlib import Path
ROOT=Path('/home/wogikaze/wgkz/mncore'); EM=ROOT/'judge/judge-py/mncore2_emuenv'
def run(name, body):
    src=body+"d get $ls2n0c0b0m0p0 4\n"
    with tempfile.TemporaryDirectory() as td:
        p=subprocess.run([str(EM/'assemble3'),'--instruction-mode','flat'],input=src.encode(),capture_output=True)
        if p.returncode:
            print(name,'ASM FAIL',p.stderr.decode(errors='replace')[:160].replace('\n',' | ')); return
        f=Path(td)/'a.asm'; f.write_text(p.stdout.decode()); d=Path(td)/'o.dmp'
        q=subprocess.run([str(EM/'gpfn3_package_main'),'-i',str(f),'-d',str(d),'--offchip-memory-init','zero'],capture_output=True)
        txt=(d.read_text() if d.exists() else '')+q.stdout.decode(errors='replace')+q.stderr.decode(errors='replace')
        vals=[l for l in txt.splitlines() if 'GREG1' in l]
        print(name, '=>', vals[0][:130] if vals else 'NO DUMP')
run('imm 1111 -> imm 2222 -> ior lw -> aluf -> l1bmd',
    'imm i"0x11111111" $r0\nimm i"0x22222222" $r4\nnop\nior $lr0 $lr4 $ls0\nl1bmd $aluf $lb0\nnop\nnop\nl1bmd $lb0 $ls2\n')
run('imm 1111 -> imm 2222 -> ior lw -> 1nop -> l1bmd ls0',
    'imm i"0x11111111" $r0\nimm i"0x22222222" $r4\nnop\nior $lr0 $lr4 $ls0\nnop\nl1bmd $ls0 $lb0\nnop\nnop\nl1bmd $lb0 $ls2\n')
run('l1bmd $laluf variant',
    'imm i"0x11111111" $r0\nimm i"0x22222222" $r4\nnop\nior $lr0 $lr4 $ls0\nl1bmd $laluf $lb0\nnop\nnop\nl1bmd $lb0 $ls2\n')
