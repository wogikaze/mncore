import subprocess
from pathlib import Path
ROOT = Path(__file__).resolve().parents[3]
ASM = ROOT / "judge/judge-py/mncore2_emuenv/assemble3"
def asm(label, body):
    p = subprocess.run([str(ASM), "--instruction-mode", "flat"], input=body.encode(), capture_output=True)
    err=p.stderr.decode(errors="replace"); ok=p.returncode==0
    first=next((l.strip() for l in err.splitlines() if l.strip()), "")
    print(("OK   " if ok else "FAIL ")+f"{label:58s} {first[:100]}")
tail='nop\nnop\nl2bmd $lb0 $lc0\nnop\nmvd/n64 $lc0 $p0@0\nmvp/n4096 $p0@0 $d0@0\n'
for gap in range(0,3):
    body = 'ior $lr0 $lr4 $ls0/1100\n' + 'nop\n'*gap + 'l1bmd $ls0 $lb0\n' + tail
    asm(f"producer ior lw -> {gap} nop -> l1bmd ls0", body)
# no producer at all, values assumed present
asm("l1bmd ls0 -> 2nop -> l2bmd -> 1nop -> mvd -> mvp", 'l1bmd $ls0 $lb0\nnop\nnop\nl2bmd $lb0 $lc0\nnop\nmvd/n64 $lc0 $p0@0\nmvp/n4096 $p0@0 $d0@0\n')
# mvd reading both l2bmd ranges
for gap in range(0,3):
    body='l2bmd $lb0 $lc0\nl2bmd $lb32 $lc256\n'+'nop\n'*gap+'mvd/n512 $lc0 $p0@0\nmvp/n4096 $p0@0 $d0@0\n'
    asm(f"l2bmd,l2bmd -> {gap} nop -> mvd/n512", body)
