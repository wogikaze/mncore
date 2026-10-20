import subprocess
from pathlib import Path
ROOT = Path(__file__).resolve().parents[3]
ASM = ROOT / "judge/judge-py/mncore2_emuenv/assemble3"
def asm(label, body):
    p = subprocess.run([str(ASM), "--instruction-mode", "flat"], input=body.encode(), capture_output=True)
    out=p.stdout.decode(errors="replace"); err=p.stderr.decode(errors="replace")
    ok=p.returncode==0
    first=next((l.strip() for l in err.splitlines() if l.strip()), "")
    print(("OK   " if ok else "FAIL ")+f"{label:52s} words={out.count(chr(10)):3d} {first[:120]}")
for n in [64,512,1024,2048,4096,8192,16384,32768]:
    asm(f"mvp L2g->DRAM n{n}", f"nop\nmvp/n{n} $lc0@0.1 $d0@0\n")
for n in [64,512,1024,2048,4096,8192,16384]:
    asm(f"mvd L2->PDM n{n}", f"nop\nmvd/n{n} $lc0 $p0@0\n")
for n in [64,512,1024,2048,4096,8192,16384]:
    asm(f"mvp PDM->DRAM n{n}", f"nop\nmvp/n{n} $p0@0 $d0@0\n")
for n in [64,512,1024,2048,4096,8192,16384]:
    asm(f"mvd PDM->DRAM n{n}", f"nop\nmvd/n{n} $p0@0 $d0@0\n")
# dependencies
asm("producer s0 -> nop -> l1bmd s0", 'imm i"1" $s0\nnop\nl1bmd $s0 $lb0\n')
asm("producer s0 -> l1bmd s0 (no nop)", 'imm i"1" $s0\nl1bmd $s0 $lb0\n')
asm("producer aluf -> l1bmd aluf", 'imm i"1" $s0\nl1bmd $aluf $lb0\n')
asm("l1bmd -> l2bmd no gap", 'l1bmd $s0 $lb0\nl2bmd $lb0 $lc0\n')
asm("l1bmd -> nop -> l2bmd", 'l1bmd $s0 $lb0\nnop\nl2bmd $lb0 $lc0\n')
asm("l1bmd -> 2nop -> l2bmd", 'l1bmd $s0 $lb0\nnop\nnop\nl2bmd $lb0 $lc0\n')
asm("l2bmd -> mvd no gap", 'l2bmd $lb0 $lc0\nmvd/n64 $lc0 $p0@0\n')
asm("l2bmd -> nop -> mvd", 'l2bmd $lb0 $lc0\nnop\nmvd/n64 $lc0 $p0@0\n')
asm("mvd -> mvp no gap", 'mvd/n64 $lc0 $p0@0\nmvp/n64 $p0@0 $d0@0\n')
