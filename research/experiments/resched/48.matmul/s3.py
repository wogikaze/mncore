def BODY(b):
    b[18]=b[18].replace('l1bmm $llb448 $lls112v;','')
    b[19]='l1bmm $llb448 $lls112v;'+b[19]
    return b
ADD={3:'imm i"4" $ln200', 6:'ilsl $peid $ln200 $t', 15:'imm i"6" $nowrite', 16:'ilsl $l2bid $aluf $nowrite',
     17:'ixor $aluf $t $nowrite', 18:'ipassa $aluf $nowrite', 19:'l1bmd $aluf $lb4096', 22:'l2bm@0 $lb4096 $lc0', 23:['l2bmdars $lc0@.0 $dar0','l2bmdarw']}
for i in range(24,39): ADD[i]='l2bmdarw'
