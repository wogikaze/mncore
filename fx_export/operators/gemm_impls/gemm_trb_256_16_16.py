from typing import List
from .. import BaseOperator



def generate_vsm(operator: BaseOperator) -> List[str]:
    operator.check_layout_in("((8_L2B:1, 4:2, 8_L1B:1), (2:1, 4_PE:1, 2_W:1))", 0)
    operator.check_layout_in("((16:2), (2:1, 4_PE:1, 2_W:1))", 1)
    operator.check_layout_out("((8_L2B:1, 4:2, 8_L1B:1), (2:1, 4_PE:1, 2_W:1))")


    assert operator.loc_prefix_in(0) == "m" # LM0 に入力を仮定し、実装を軽減
    assert operator.loc_prefix_in(1) == "m" # LM0 に入力を仮定し、実装を軽減
    
    assert operator.addr_in(0) == 0   # 入力1 を addr0 に仮定し、実装を軽減
                                            # ↑、つまり、入力 0 が "$lm0v" だと仮定している
    assert operator.addr_in(1) == operator.memory_len_in(0)
                                            # 入力2 を、入力 0 の直後と仮定し、実装を軽減

    assert operator.loc_prefix_out() == "n" # LM1 に出力を仮定し、実装を軽減
    assert operator.addr_out() == 0         # 出力 を addr0 に仮定し、実装を軽減
                                            # ↑、つまり、出力が "$ln0v" だと仮定している
    
    # test unit_tests/train_step/Gemm_256x16_16x16_256x16_transB_a/
    # 問題名：「Mmul TB 256_16_16」 (problems/36, 1位解 6 行、半精度)
    # この問題の 1 位解は hbfn/hmmul（half）を使う。学習全体の精度より行数を優先。
    lines = []
    lines.append("hbfn/9 $llm[16,20,48,52]r $nowrite")
    lines.append("hmwrite $aluf $ly0; hbfn/9 $llm[24,28,56,60]r $nowrite")
    lines.append("hmwrite $aluf $ly4; hbfn/9 $llm[32,36,64,68]r $nowrite")
    lines.append("hmwrite $aluf $ly8; hbfn/9 $llm[40,44,72,76]r $nowrite")
    lines.append("hmwrite $aluf $ly12; hbfn/9 $llm0vr $nowrite")
    lines.append("hmmul $ly $aluf $lln0v")
    return lines
