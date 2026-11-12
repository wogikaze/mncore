#!/usr/bin/env python3
"""Stage C: block coordinates. Produces per (PE, cycle): X = 8*B (float, hi lane) and role k."""
import struct
from simh import run, pes, f32

def hf(x):
    """half-precision (1,6,9) bit pattern of a small exactly representable value."""
    if x == 0: return 0
    s = 0x8000 if x < 0 else 0
    x = abs(x); e = 0
    while x >= 2: x /= 2; e += 1
    while x < 1: x *= 2; e -= 1
    man = (x - 1) * 512
    assert man == int(man), "not representable in half"
    return s | ((e + 31) << 9) | int(man)
def hp(a, b):
    return f'ui"0x{(hf(a) << 16) | hf(b):08x}"'
def fbits(x):
    return struct.unpack(">I", struct.pack(">f", x))[0]

STAGE_C = f"""imm ui"0x4b000000" $t $lr0/1000 $ls0/1000
ior $subpeid $aluf $lr8/1000 $ls8/1000
dmwrite $aluf $lx0; ior $l2bid $t $lr6/1000
dmread $lx0 $lr16v $ls16v; imm {hp(126, 14)} $n0/1000
imm {hp(-4, 0)} $n1/1000
uilsr $mabid $r[16,20,22,16] $r[28,26,24,30]; imm ui"0x{fbits(-(2.0**36) - 2.0**26):08x}" $ln4/1000
uilsr $l1bid $r[16,18,16,16] $r[27,25,31,31]; fvfma $lr16v $ln6 $ln4 $ln8v
imm {hp(16, 16)} $n2/1000
ior $lr[24,26,28,6] $t $lr[32,34,36,38]
imm f"8192" $ln6/1000
fvadd $lr[32,34,36,38] -$ls0 $lr40v $ls40v
imm f"8" $n16/1000
fvfma $lr[40,42,46,40] $n[0,1,2,3]e $ls[42,44,8,40] $lr48v $ls48v
imm f"64" $n17/1000
imm f"32" $n18/1000
fvfma $ls52 $n16 $ln8v $nowrite
fvfma $r49 $n17 $mauf $nowrite
fvfma $r48 $n18 $mauf $lr56v $ls56v $ln56v
"""
if __name__ == "__main__":
    prog = STAGE_C + "d get $lr56 4\nd get $r50 1\n"
    try:
        r = run(prog)
    except RuntimeError as e:
        print("ERR", e); raise SystemExit(1)
    bad = 0; n = 0
    for path, g, c, b, m, p in pes():
        l2b = 2 * g + c
        B0 = 512 * (m >> 3) + 128 * (b >> 1) + 16 * l2b + 8 * (b & 1) + 4 * ((m >> 2) & 1) + p
        for cyc in range(4):
            v = r.dump[("GREG0", path, 56 + 2 * cyc)]
            X = f32(v >> 32)
            if X != 8 * (B0 + 1024 * cyc): bad += 1
            n += 1
        k = f32(r.dump[("GREG0", path, 50)] >> 32)
        if k != (m & 3): bad += 1
    print("words", r.words, "checked", n, "bad", bad)
    print(run(prog.replace("d get $lr56 4", "d get $lr56n1c1b7m15p3 4").replace("d get $r50 1", "d get $lr40n1c1b7m15p3 8")).dump)
