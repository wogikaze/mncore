MODE='swap'
ADD={2:'ipassa $l1bid $nowrite', 3:'ilsl $peid $aluf $ln200', 14:'imm i"6" $nowrite', 15:'ilsl $l2bid $aluf $nowrite',
     16:'ixor $aluf $ln200 $t', 17:'immu i"16" $nowrite', 18:'ior $aluf $t $nowrite', 19:'l1bmd $aluf $lb4096',
     21:'l2bm@5 $lb4048 $lc8144', 22:['l2bmdars $lc8192@.0 $dar0','l2bmdarw']}
for i in range(23,30): ADD[i]='l2bmdarw'
