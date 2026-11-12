#!/usr/bin/env python3
"""P1: T = mabid (no imm), MAB k handles rows k+16C."""
import sys
L = []
L.append('ipassa $mabid $t')
L.append('nop')
L.append('frsqrt $mt256v16 $nowrite; fvpassa $mt256v16 $r0v')
L.append('imm ui"0x40000000" $nowrite; fvmul $aluf $aluf $ls0v')
L.append('fvfma -$mauf $r0v $aluf $nowrite; l1bmd+0 $aluf $lbi')
L.append('fvmul $mauf $ls0v $ls0v; l1bmd+0 $lbi $nowrite')
L.append('imm ui"0x00000002" $nowrite; fvfma -$mauf $r0v $lbf $nowrite')
L.append('llsl $mabid $aluf $lmb; fvmul $mauf $ls0v $ls0v')
L.append('fvpassa $mauf $s1v2')
L.append('nop')
f = lambda base: "[" + ",".join(str(base + 64*c + o) for c in (0,1) for o in (0,2)) + "]"
g = lambda base: "[" + ",".join(str(base + 64*c + o) for c in (2,3) for o in (0,2)) + "]"
L.append(f'fvmul $lm{f(0)} $ls[0,0,2,2] $lr0v $ln{f(0)}; l1bmm@1 $ls[0,0,2,2] $lbi')
L.append(f'fvmul $lm{g(0)} $ls[4,4,6,6] $lr8v $ln{g(0)}; l1bmm@1 $ls[4,4,6,6] $lbi; l1bmm $lbi $nowrite')
L.append(f'fvmul $lm{f(4)} $lbf $ln{f(4)}; l1bmm $lbi $nowrite')
L.append(f'fvmul $lm{g(4)} $lbf $ln{g(4)}; l1bmm@2 $llr0v $llbi')
for k in range(2, 16):
    dst = "[" + ",".join(str(4*k + 64*c) for c in range(4)) + "]"
    s = f'l1bmm@{k+1} $llr0v $llbi; ' if k < 15 else ''
    L.append(f'{s}l1bmm $llbi $lln{dst}')
print("\n".join(L))
