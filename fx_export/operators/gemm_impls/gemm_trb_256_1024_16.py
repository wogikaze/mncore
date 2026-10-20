from typing import List
from .. import BaseOperator


def generate_vsm(operator: BaseOperator) -> List[str]:
    operator.check_layout_in("((8_L2B:1, 32:1), (8_MAB:2, 8_L1B:1, 2_MAB:1, 4_PE:1, 2_W:1))", 0)
    operator.check_layout_in("((16:1), (8_MAB:2, 8_L1B:1, 2_MAB:1, 4_PE:1, 2_W:1))", 1)
    operator.check_layout_out("((4_L2B:2, 64:8), (8:1, 2_W:1))")
    assert operator.loc_prefix_out() == "d" # DRAM 出力


    assert operator.loc_prefix_in(0) == "m" # LM0 に入力0を仮定し、実装を軽減
    assert operator.loc_prefix_in(1) == "m" # LM0 に入力1を仮定し、実装を軽減
    
    assert operator.addr_in(0) == 0   # 入力1 を addr0 に仮定し、実装を軽減
                                            # ↑、つまり、入力 0 が "$lm0v" だと仮定している
    assert operator.addr_in(1) == operator.memory_len_in(0)
                                            # 入力2 を、入力 0 の直後と仮定し、実装を軽減


    c = operator.addr_out()      # "$d0" の "0" の部分
    
    # test unit_tests/train_step/Gemm_256x1024_16x1024_256x16_transB_a/
    # 問題名：「Mmul TB D 256_1024_16」 (problems/39, 1位解 29 行)
    lines = """gbfn $lm64v $nowrite
gbfn $lm72v $nowrite; gmwrite $aluf $lx0
gbfn $lm80v $nowrite; gmwrite $aluf $lx4
gbfn $lm88v $nowrite; gmwrite $aluf $ly0
gbfn $lm0v $t; gmwrite $aluf $ly4
gmmul $lx $aluf $lr0v4
gbfn $lm8v $t; gmmul $ly $t $lr2v4
gmmul $lx $aluf $ls0v4
gbfn $lm16v $t; gmmul $ly $t $ls2v4; l1bmrffadd $llr0v $llb0
gmmul $lx $aluf $lr0v4
gbfn $lm24v $t; gmmul $ly $t $lr2v4; l1bmrffadd $lls0v $llb32
gmmul $lx $aluf $ls0v4
gbfn $lm32v $t; gmmul $ly $t $ls2v4; l1bmrffadd $llr0v $llb64
gmmul $lx $aluf $lr0v4
gbfn $lm40v $t; gmmul $ly $t $lr2v4; l1bmrffadd $lls0v $llb96
gmmul $lx $aluf $ls0v4
gbfn $lm48v $t; gmmul $ly $t $ls2v4; l1bmrffadd $llr0v $llb128
gmmul $lx $aluf $lr0v4
gbfn $lm56v $t; gmmul $ly $t $lr2v4; l1bmrffadd $lls0v $llb160
gmmul $lx $aluf $ls0v4
gmmul $ly $t $ls2v4; l1bmrffadd $llr0v $llb192
nop
l1bmrffadd $lls0v $llb224; l2bmrffadd $lb0 $lc0
l2bmrffadd $lb64 $lc64
l2bmrffadd $lb128 $lc128
l2bmrffadd $lb192 $lc192
nop
mvp/n256 $lc0@.0 $dOUT
mvp/n256 $lc0@.1 $dOUT2"""
    return [l.replace("$dOUT2", f"$d{c + 256}").replace("$dOUT", f"$d{c}") for l in lines.splitlines()]
