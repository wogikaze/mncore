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
    # 問題名：「Mmul 256_16_16」
    
    lines = []

    lines.append("gmwrite $lm16v4 $ly0")
    lines.append("gmwrite $lm32v4 $ly4")
    lines.append("gmread $ly0 $lr16v4")
    lines.append("gmread $ly4 $lr32v4")
    lines.append("gmwrite $lm18v4 $ly0")
    lines.append("gmwrite $lm34v4 $ly4")
    lines.append("gmread $ly0 $lr48v4")
    lines.append("gmread $ly4 $lr64v4")
    lines.append("gmwrite $lm48v4 $ly0")
    lines.append("gmwrite $lm64v4 $ly4")
    lines.append("gmread $ly0 $lr18v4")
    lines.append("gmread $ly4 $lr34v4")
    lines.append("gmwrite $lm50v4 $ly0")
    lines.append("gmwrite $lm66v4 $ly4")
    lines.append("gmread $ly0 $lr50v4")
    lines.append("gmread $ly4 $lr66v4")
    lines.append("gbfn $lr16v4 $nowrite")
    lines.append("gmwrite $aluf $ly0")
    lines.append("gbfn $lr32v4 $nowrite")
    lines.append("gmwrite $aluf $ly4")
    lines.append("gbfn $lm0v4 $nowrite")
    lines.append("gmmul $ly $aluf $ls0v4")
    lines.append("gbfn $lr18v4 $nowrite")
    lines.append("gmwrite $aluf $ly0")
    lines.append("gbfn $lr34v4 $nowrite")
    lines.append("gmwrite $aluf $ly4")
    lines.append("gbfn $lm2v4 $nowrite")
    lines.append("gmfma $ly $aluf $ls0v4 $ln0v4")
    lines.append("gbfn $lr48v4 $nowrite")
    lines.append("gmwrite $aluf $ly0")
    lines.append("gbfn $lr64v4 $nowrite")
    lines.append("gmwrite $aluf $ly4")
    lines.append("gbfn $lm0v4 $nowrite")
    lines.append("gmmul $ly $aluf $ls0v4")
    lines.append("gbfn $lr50v4 $nowrite")
    lines.append("gmwrite $aluf $ly0")
    lines.append("gbfn $lr66v4 $nowrite")
    lines.append("gmwrite $aluf $ly4")
    lines.append("gbfn $lm2v4 $nowrite")
    lines.append("gmfma $ly $aluf $ls0v4 $ln2v4")

    return lines