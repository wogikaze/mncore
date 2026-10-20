from typing import List
from .. import BaseOperator



def generate_vsm(operator: BaseOperator) -> List[str]:
    operator.check_layout_in("((8_L2B:1, 4:2, 8_L1B:1), (2:1, 4_PE:1, 2_W:1))", 0)
    operator.check_layout_in("((16:2), (2:1, 4_PE:1, 2_W:1))", 1)
    operator.check_layout_out("((8_L2B:1, 4:2, 8_L1B:1), (2:1, 4_PE:1, 2_W:1))")


    assert operator.loc_prefix_in(0) == "m" # LM0 に入力を仮定し、実装を軽減
    assert operator.loc_prefix_in(1) == "m" # LM0 に入力を仮定し、実装を軽減
    
    assert operator.addr_in(0) == 0   # 入力0 を addr0 に仮定し、実装を軽減
                                            # ↑、つまり、入力0が "$lm0v" だと仮定している
    assert operator.addr_in(1) == operator.memory_len_in(0)
                                            # 入力1 を、入力 0 の直後と仮定し、実装を軽減

    assert operator.loc_prefix_out() == "n" # LM1 に出力を仮定し、実装を軽減
    assert operator.addr_out() == 0         # 出力 を addr0 に仮定し、実装を軽減
                                            # ↑、つまり、出力が "$ln0v" だと仮定している
    
    # test unit_tests/train_step/Gemm_256x16_16x16_256x16_a/
    # 問題名：「Mmul 256_16_16」 (problems/42, 1位解 13 行)
    lines = []
    lines.append("lpassa $mabid $t")
    lines.append("gbfn $lm0v4 $lr0v")
    lines.append("gmwrite $lmt16v4 $lx0")
    lines.append("gmwrite $lmt32v4 $lx4")
    lines.append("gmwrite $lmt48v4 $ly0; gmread $lx0 $nowrite")
    lines.append("gbfn $mreadf $nowrite; gmwrite $lmt64v4 $ly4; gmread $lx4 $nowrite")
    lines.append("gbfn $mreadf $nowrite; gmwrite $aluf $lx0; gmread $ly0 $nowrite")
    lines.append("gbfn $mreadf $nowrite; gmwrite $aluf $lx4; gmread $ly4 $nowrite")
    lines.append("gbfn $mreadf $nowrite; gmwrite $aluf $ly0")
    lines.append("gbfn $lm2v4 $nowrite; gmmul $lx $lr0v $nowrite; gmwrite $aluf $ly4")
    lines.append("gmfma $ly $aluf $mauf $ln0v4")
    lines.append("l1bmm@2 $mauf $lbi")
    lines.append("l1bmm $lbi $ln2v4")
    return lines
