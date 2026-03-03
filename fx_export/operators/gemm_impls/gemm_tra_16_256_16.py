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
    # 問題名：「Mmul TA D 16_256_16」
    
    lines = []

    lines.append("zero $nowrite;gmwrite $lm0v4 $lx0")
    lines.append("gmread $lx0 $lr0v4")
    lines.append("gmread $lx4 $lr16v4")
    lines.append("gmwrite $lm2v4 $lx0")
    lines.append("gmread $lx0 $lr2v4")
    lines.append("gmread $lx4 $lr18v4")
    lines.append("gmwrite $lm16v4 $lx0")
    lines.append("gmread $lx0 $nowrite")
    lines.append("gbfn $mreadf $nowrite")
    lines.append("gmwrite $aluf $ly0;gmread $lx4 $nowrite")
    lines.append("gbfn $mreadf $nowrite")
    lines.append("gmwrite $aluf $ly4;gbfn $lr0v4 $nowrite")
    lines.append("gmmul $ly $aluf $ln0v4;gbfn $lr16v4 $nowrite")
    lines.append("gmmul $ly $aluf $ln16v4;gbfn $lr2v4 $nowrite")
    lines.append("gmmul $ly $aluf $ln32v4;gbfn $lr18v4 $nowrite")
    lines.append("gmmul $ly $aluf $ln48v4;gmwrite $lm18v4 $lx0")
    lines.append("gmread $lx0 $nowrite")
    lines.append("gbfn $mreadf $nowrite")
    lines.append("gmwrite $aluf $ly0;gmread $lx4 $nowrite")
    lines.append("gbfn $mreadf $nowrite")
    lines.append("gmwrite $aluf $ly4;gbfn $lr0v4 $nowrite")
    lines.append("gmmul $ly $aluf $ln2v4;gbfn $lr16v4 $nowrite")
    lines.append("gmmul $ly $aluf $ln18v4;gbfn $lr2v4 $nowrite")
    lines.append("gmmul $ly $aluf $ln34v4;gbfn $lr18v4 $nowrite")
    lines.append("gmmul $ly $aluf $ln50v4")
    lines.append("nop")
    lines.append("nop")
    lines.append("l1bmm@0 $lln0v $llb0")
    lines.append("l1bmm@0 $lln16v $llb32")
    lines.append("l1bmm@0 $lln32v $llb64")
    lines.append("l1bmm@0 $lln48v $llb96")
    lines.append("l2bmrffadd $lb0 $lc0")
    lines.append("l2bmrffadd $lb32 $lc64")
    lines.append("l2bmrffadd $lb64 $lc128")
    lines.append("l2bmrffadd $lb96 $lc192")
    lines.append("nop")
    lines.append("mvrffadd/n64 $lc0 $p0@0")
    lines.append("mvrffadd/n64 $lc64 $p64@0")
    lines.append("mvrffadd/n64 $lc128 $p128@0")
    lines.append("mvrffadd/n64 $lc192 $p192@0")
    lines.append(f"mvp/n64 $p0@0 $d{c}@0")
    lines.append(f"mvp/n64 $p64@0 $d{c}@1")
    lines.append(f"mvp/n64 $p128@0 $d{c}@2")
    lines.append(f"mvp/n64 $p192@0 $d{c}@3")

    return lines