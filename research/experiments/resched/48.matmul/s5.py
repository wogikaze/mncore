MODE='swap'
ADD={3:'imm i"5" $ln200', 6:'ilsl $peid $ln200 $t', 15:'imm i"6" $nowrite', 16:'ilsl $l2bid $aluf $nowrite',
     17:'ixor $aluf $t $t', 18:'immu i"16" $nowrite', 19:'ior $aluf $t $nowrite', 20:'l1bmd $aluf $lb4096',
     22:'l2bm@0 $lb4048 $lc8144', 23:['l2bmdars $lc8192@.0 $dar0','l2bmdarw']}
for i in range(24,31): ADD[i]='l2bmdarw'
