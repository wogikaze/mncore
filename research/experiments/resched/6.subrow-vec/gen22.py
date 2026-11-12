#!/usr/bin/env python3
"""22-word SubRow vec.

T = mabid for the B load, then T = 4*mabid for A.  MAB k handles rows k+16c (c=0..3).
MAB0 itself writes rows of k=0 (its own computation), k=2 and k=3 (flat addresses, B taken from one
long-word load of the pairs (B[2+16c], B[3+16c]) and duplicated with two single-word copies).
MABs 1,4..15 are streamed to MAB0's LM1 through the L1BM turnaround (13 x 16 words).
"""
def fl(base, cs=(0, 1)):
    return "[" + ",".join(str(base + 64*c + o) for c in cs for o in (0, 2)) + "]"
L = []
L.append('ipassa $mabid $t; fvpassa $lm[258,274,290,306] $lr8v $ls16v')
L.append('imm ui"0x00000002" $nowrite; fvpassa $mauf $r9v2')
L.append('llsl $mabid $aluf $t; fvpassa $mt256v16 $r0v2')
L.append(f'fpassa $mauf $r1v2; fvadd $lm{fl(8)} -$lr[8,8,10,10] $ln{fl(8)}')
L.append(f'fpassa $s[17,19,21,23] $s16v2; fvadd $lm{fl(8,(2,3))} -$lr[12,12,14,14] $ln{fl(8,(2,3))}')
L.append(f'fvadd $lmt{fl(0)} -$lr[0,0,2,2] $lr16v $ln{fl(0)}')
L.append(f'fvadd $lmt{fl(0,(2,3))} -$lr[4,4,6,6] $lr24v $ln{fl(0,(2,3))}')
L.append(f'fvadd $lm{fl(12)} -$ls[16,16,18,18] $ln{fl(12)}')
senders = [1] + list(range(4, 16))
L.append(f'fvadd $lm{fl(12,(2,3))} -$ls[20,20,22,22] $ln{fl(12,(2,3))}; l1bmm@{senders[0]} $llr16v $llbi')
for i, k in enumerate(senders):
    dst = "[" + ",".join(str(4*k + 64*c) for c in range(4)) + "]"
    s = f'l1bmm@{senders[i+1]} $llr16v $llbi; ' if i + 1 < len(senders) else ''
    L.append(f'{s}l1bmm $llbi $lln{dst}')
print("\n".join(L))
