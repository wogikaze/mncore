#!/usr/bin/env python3
"""23-word SubRow vec: T = mabid, T := 4*mabid after the B load, MAB k handles rows k+16c."""
L = []
L.append('ipassa $mabid $t; fvpassa $m[257,273,289,305] $r8v2')
L.append('imm ui"0x00000002" $nowrite; fvpassa $mauf $r9v2')
L.append('llsl $mabid $aluf $t; fvpassa $mt256v16 $r0v2')
L.append('fpassa $mauf $r1v2')
L.append('fvadd $lm[4,6,68,70] -$lr[8,8,10,10] $ln[4,6,68,70]')
L.append('fvadd $lmt[0,2,64,66] -$lr[0,0,2,2] $ls0v $ln[0,2,64,66]')
L.append('fvadd $lmt[128,130,192,194] -$lr[4,4,6,6] $ls8v $ln[128,130,192,194]')
L.append('fvadd $lm[132,134,196,198] -$lr[12,12,14,14] $ln[132,134,196,198]')
for k in range(2, 17):
    parts = []
    if k <= 15:
        parts.append(f'l1bmm@{k} $lls0v $llbi')
    if k >= 3:
        j = k - 1
        dst = "[" + ",".join(str(4*j + 64*c) for c in range(4)) + "]"
        parts.append(f'l1bmm $llbi $lln{dst}')
    L.append('; '.join(parts))
print("\n".join(L))
