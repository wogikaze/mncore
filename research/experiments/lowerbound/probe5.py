import subprocess
from pathlib import Path
ROOT = Path(__file__).resolve().parents[3]
ASM = ROOT / "judge/judge-py/mncore2_emuenv/assemble3"
def asm(label, body):
    p = subprocess.run([str(ASM), "--instruction-mode", "flat"], input=body.encode(), capture_output=True)
    err=p.stderr.decode(errors="replace"); ok=p.returncode==0
    first=next((l.strip() for l in err.splitlines() if l.strip()), "")
    print(("OK   " if ok else "FAIL ")+f"{label:60s} {first[:100]}")
tail='nop\nnop\nl2bmd $lb0 $lc0\nnop\nmvd/n64 $lc0 $p0@0\nmvp/n4096 $p0@0 $d0@0\n'
prods = {
 'ipassa t -> ls0/1100': 'ipassa $t $ls0/1100\n',
 'ipassa lr0 -> ls0/1100': 'ipassa $lr0 $ls0/1100\n',
 'imm 1 -> ls0': 'imm i"1" $ls0\n',
 'ipassa aluf -> ls0/1100': 'ipassa $aluf $ls0/1100\n',
 'ior mt -> ls0/1100': 'ior $mt[0,1,2,3] $aluf $ls0/1100\n',
}
for name,prod in prods.items():
    for gap in range(0,3):
        asm(f"{name} + {gap} nop + l1bmd ls0", prod + 'nop\n'*gap + 'l1bmd $ls0 $lb0\n' + tail)
