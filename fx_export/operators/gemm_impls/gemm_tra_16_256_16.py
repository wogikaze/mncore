from typing import List
from .. import BaseOperator


def generate_vsm(operator: BaseOperator) -> List[str]:
    operator.check_layout_in("((8_L2B:1, 4:2, 8_L1B:1), (2:1, 4_PE:1, 2_W:1))", 0)
    operator.check_layout_in("((8_L2B:1, 4:2, 8_L1B:1), (2:1, 4_PE:1, 2_W:1))", 1)
    operator.check_layout_out("((4_L2B:2, 4:8), (8:1, 2_W:1))")
    assert operator.loc_prefix_out() == "d" # DRAM 出力


    assert operator.loc_prefix_in(0) == "m" # LM0 に入力を仮定し、実装を軽減
    assert operator.loc_prefix_in(1) == "m" # LM0 に入力を仮定し、実装を軽減
    
    assert operator.addr_in(0) == 0   # 入力1 を addr0 に仮定し、実装を軽減
                                            # ↑、つまり、入力0が "$lm0v" だと仮定している
    assert operator.addr_in(1) == operator.memory_len_in(0)
                                            # 入力2 を、入力 0 の直後と仮定し、実装を軽減


    c = operator.addr_out()      # "$d0" の "0" の部分

    # test unit_tests/train_step/Gemm_256x16_256x16_16x16_transA_a/
    # 問題名：「Mmul TA D 16_256_16」 (problems/46, 1位解 25 行)
    # The reference kernel writes X/Y before reading them, so the matrix-face
    # clear that the old kernel needed is not required here.
    lines = """gmwrite $lm16v4 $lx0; zero $ls128v
gmwrite $aluf $lx4; ipackbit $mabid $aluf $t
gmwrite $ls128v $ly4; gmread $lx0 $nowrite;
gmwrite $lmt0v4 $ly0; gmread $lx4 $nowrite; gbfn $mreadf $lr0v4
gmwrite $lm18v4 $lx0; gmread $ly0 $nowrite; gbfn $mreadf $lr16v4
gmwrite $ls128v $lx4; gmread $ly4 $nowrite; gbfn $mreadf $ls0v4;
gmwrite $lr0v4 $ly0; gmread $lx0 $nowrite; gbfn $mreadf $ls16v4
gmwrite $lr16v4 $ly4; gmread $lx4 $nowrite; gbfn $mreadf $nowrite;
gmwrite $aluf $lx0; gmmul $ly $ls0v4 $ln0v4 $lr0v4; gbfn $mreadf $nowrite;
gmwrite $aluf $lx4; gmmul $ly $ls16v4 $ln16v4 $lr16v4
gmmul $lx $ls0v4 $ln2v4 $lr2v4
gmmul $lx $ls16v4 $ln18v4 $lr18v4
l1bmm@0 $llr0v $llb64
l1bmm@0 $llr16v $llb128
l1bmm@1 $llr0v $llb192
l1bmm@1 $llr16v $llb256; l2bmrffadd $lb32 $lc32
l2bmrffadd $lb96 $lc96
l2bmrffadd $lb160 $lc160
l2bmrffadd $lb224 $lc224
nop/1
mvrffadd/n256 $lc64 $p0@0
mvp/n64 $p0@0 $dOUT@0
mvp/n64 $p64@0 $dOUT@1
mvp/n64 $p128@0 $dOUT@2
mvp/n64 $p192@0 $dOUT@3"""
    return [l.replace("$dOUT", f"$d{c}") for l in lines.splitlines()]

    return lines