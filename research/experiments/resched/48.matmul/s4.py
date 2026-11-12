ADD={3:'imm i"4" $ln200', 6:'ilsl $peid $ln200 $t', 15:"imm i\"6\" $nowrite", 16:"ipassa $aluf $nowrite", 17:'ilsl $l2bid $aluf $nowrite',
     18:'ixor $aluf $t $nowrite', 19:'ipassa $aluf $nowrite', 20:'l1bmd $aluf $lb4096', 22:'l2bm@0 $lb4064 $lc32', 23:['l2bmdars $lc64@.0 $dar0','l2bmdarw']}
for i in range(24,39): ADD[i]='l2bmdarw'
