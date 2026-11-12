ADD={3:'imm i"4" $ln200', 6:'ilsl $peid $ln200 $t', 15:'imm i"6" $nowrite', 16:'ilsl $l2bid $aluf $nowrite',
     17:'ixor $aluf $t $ln204', 20:'l1bmd $ln204 $lb4096', 23:'l2bm@0 $lb4096 $lc0', 24:['l2bmdars $lc0@.0 $dar0','l2bmdarw']}
for i in range(25,40): ADD[i]='l2bmdarw'
