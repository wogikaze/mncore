from typing import List
from .. import BaseOperator

def generate_vsm(operator: BaseOperator) -> List[str]:
    assert operator.layout_in() == "((4_L2B:2, 4:8), (8:1, 2_W:1))", operator.layout_in()
    assert operator.layout_out() == "((16:2), (2:1, 4_PE:1, 2_W:1))", operator.layout_out()
    
    assert operator.loc_prefix_out() == "m" # LM0 に出力を仮定し、実装を軽減
    
    x = operator.addr_in()      # "$d0" の "0" の部分
    y = operator.addr_out()     # "$lm0v" の "0" の部分

    # test unit_tests/train_step/DL_16x16*
    # 問題名：「DL 16_16」
    
    lines = []

    lines.append(f"mvp/n64 $d{x}@0 $p0@0")
    lines.append(f"mvp/n64 $d{x}@1 $p64@0")
    lines.append(f"mvp/n64 $d{x}@2 $p128@0")
    lines.append(f"mvp/n64 $d{x}@3 $p192@0")
    lines.append("mvb/n256 $p0@0 $lc0")
    lines.append("l2bmb $lc0 $lb0")
    lines.append("l2bmb $lc64 $lb32")
    lines.append("l2bmb $lc128 $lb64")
    lines.append("l2bmb $lc192 $lb96")
    lines.append("nop")
    lines.append(f"l1bmm $llb0 $llm{y}v")
    lines.append(f"l1bmm $llb32 $llm{y+16}v")
    lines.append(f"l1bmm $llb64 $llm{y+32}v")
    lines.append(f"l1bmm $llb96 $llm{y+48}v")

    return lines