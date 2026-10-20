import subprocess
from pathlib import Path
ROOT = Path(__file__).resolve().parents[3]
ASM = ROOT / "judge/judge-py/mncore2_emuenv/assemble3"
def asm(label, body):
    p = subprocess.run([str(ASM), "--instruction-mode", "flat"], input=body.encode(), capture_output=True)
    err=p.stderr.decode(errors="replace"); ok=p.returncode==0
    first=next((l.strip() for l in err.splitlines() if l.strip()), "")
    print(("OK   " if ok else "FAIL ")+f"{label:55s} {first[:100]}")
# realistic producer (long-word ior with mask) then l1bmd reading s0
for gap in range(0,4):
    body = 'ior $r0 $r4 $s0/1100\n' + 'nop\n'*gap + 'l1bmd $s0 $lb0\n' + 'nop\nnop\n' + 'l2bmd $lb0 $lc0\n' + 'nop\n' + 'mvd/n64 $lc0 $p0@0\n' + 'mvp/n4096 $p0@0 $d0@0\n'
    asm(f"producer ior -> {gap} nop -> l1bmd", body)
# l1bmd source from aluf, then chain
asm("imm -> l1bmd aluf -> 2nop -> l2bmd ...", 'imm i"1" $s0\nl1bmd $aluf $lb0\nnop\nnop\nl2bmd $lb0 $lc0\nnop\nmvd/n64 $lc0 $p0@0\nmvp/n4096 $p0@0 $d0@0\n')
# gap between the two l2bmd and mvd
asm("l2bmd, l2bmd, 1nop, mvd", 'l2bmd $lb0 $lc0\nl2bmd $lb32 $lc256\nnop\nmvd/n64 $lc0 $p0@0\n')
asm("l2bmd, 1nop, l2bmd, mvd", 'l2bmd $lb0 $lc0\nnop\nl2bmd $lb32 $lc256\nmvd/n64 $lc0 $p0@0\n')
asm("l2bmd, l2bmd, mvd (no nop)", 'l2bmd $lb0 $lc0\nl2bmd $lb32 $lc256\nmvd/n64 $lc0 $p0@0\n')
# mvd then mvp with no gap
asm("mvd, mvp no gap", 'mvd/n512 $lc0 $p0@0\nmvp/n4096 $p0@0 $d0@0\n')
# mvp to PDM then mvp PDM->DRAM
asm("mvp L2->PDM n512 then mvp PDM->DRAM", 'mvp/n512 $lc0@.1 $p0\nnop\nmvp/n4096 $p0@0 $d0@0\n')
