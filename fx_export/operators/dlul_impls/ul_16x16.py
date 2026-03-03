from typing import List
from .. import BaseOperator

def generate_vsm(operator: BaseOperator) -> List[str]:
    assert operator.layout_in() == "((16:2), (2:1, 4_PE:1, 2_W:1))", operator.layout_in()
    assert operator.layout_out() == "((4_L2B:2, 4:8), (8:1, 2_W:1))", operator.layout_out()
    
    assert operator.loc_prefix_in() == "n" # LM1 に入力を仮定し、実装を軽減

    z = operator.addr_in()       # "$ln0v" の "0" の部分
    y = operator.addr_out()      # "$d0" の "0" の部分
    
    # test unit_tests/train_step/UL_16x16_*
    # 問題名：「UL 16_16」
    
    lines = []
    lines.append(f"l1bmm@0 $lln{z}v $llb0")
    lines.append(f"l1bmm@0 $lln{z+16}v $llb32")
    lines.append(f"l1bmm@0 $lln{z+32}v $llb64")
    lines.append(f"l1bmm@0 $lln{z+48}v $llb96")
    lines.append("nop")
    lines.append("l2bm@0 $lb0 $lc0")
    lines.append("l2bm@0 $lb32 $lc64")
    lines.append("l2bm@0 $lb64 $lc128")
    lines.append("l2bm@0 $lb96 $lc192")
    lines.append("nop")
    lines.append(f"mvp/n64 $lc0@0.0 $d{y}@0")
    lines.append(f"mvp/n64 $lc64@0.0 $d{y}@1")
    lines.append(f"mvp/n64 $lc128@0.0 $d{y}@2")
    lines.append(f"mvp/n64 $lc192@0.0 $d{y}@3")

    return lines