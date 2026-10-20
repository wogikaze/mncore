#!/usr/bin/env python3
"""Test the L78 (imm 8) removal: rewrite pack shifts to $s28 and delete the line."""
import subprocess
from pathlib import Path

ROOT = Path("/home/wogikaze/wgkz/mncore")
ASM = ROOT / "judge/judge-py/mncore2_emuenv/assemble3"
BASE = Path(__file__).resolve().parent / "base.vsm"


def run(src):
    p = subprocess.run([str(ASM), "--instruction-mode", "flat"], input=src.encode(),
                       capture_output=True)
    out = p.stdout.decode()
    j = sum(1 for l in out.splitlines() if l[:1] == "j")
    m = sum(1 for l in out.splitlines() if l[:1] == "m")
    if p.returncode != 0:
        msg = next((l.strip() for l in p.stderr.decode().splitlines() if l.strip()), "")
        return None, msg
    return (j, m), ""


lines = [l for l in BASE.read_text().splitlines() if l.split("#")[0].strip()]

def variant(name, repl=None, delete=()):
    cand = list(lines)
    for ln, new in (repl or {}).items():
        cand[ln - 1] = new
    keep = [l for i, l in enumerate(cand, 1) if i not in delete]
    src = "\n".join(keep) + "\n"
    wc, err = run(src)
    print(f"{name:60s} {'words=%s' % (wc,) if wc else 'FAIL: ' + err}")
    return src, wc


src, wc = variant("base (93)", )
variant("L84 pack-end shifted: delete L78, r8 -> s28",
        {81: "ilsl $aluf $s28 $nowrite", 83: "ilsl $aluf $s28 $nowrite"},
        delete={78})
variant("delete L78 only (r8 undefined -> asm?)", delete={78})
variant("delete L78 + L85 nop (pack start unchanged)",
        {81: "ilsl $aluf $s28 $nowrite", 83: "ilsl $aluf $s28 $nowrite"},
        delete={78, 85})
variant("delete L78, L85, and one tail nop",
        {81: "ilsl $aluf $s28 $nowrite", 83: "ilsl $aluf $s28 $nowrite"},
        delete={78, 85, 88})
variant("delete L78,L85,L88,L91 (tail crush)",
        {81: "ilsl $aluf $s28 $nowrite", 83: "ilsl $aluf $s28 $nowrite"},
        delete={78, 85, 88, 91})
