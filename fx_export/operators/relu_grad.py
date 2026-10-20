#!/usr/bin/env python3

"""Fused ReLU backward: ``grad * (x > 0)`` in one operator."""

from typing import Dict, List, Optional

from . import BaseOperator, register_operator


@register_operator("ReluGrad")
class ReluGradOperator(BaseOperator):
    """The mask is built with a single ``frelu`` and never goes to DRAM."""

    LAYOUT = "((8_L2B:1, 4:2, 8_L1B:1), (2:1, 4_PE:1, 2_W:1))"

    def generate_vsm(self) -> List[str]:
        assert self.in_shape(0) == [256, 16]
        assert self.in_shape(0) == self.in_shape(1) == self.out_shape()
        self.check_layout_in(self.LAYOUT, 0)
        self.check_layout_in(self.LAYOUT, 1)
        self.check_layout_out(self.LAYOUT)

        assert self.loc_prefix_in(0) == "m" and self.addr_in(0) == 0
        assert self.loc_prefix_in(1) == "m"
        assert self.addr_in(1) == self.memory_len_in(0)
        assert self.loc_prefix_out() == "n" and self.addr_out() == 0

        lines = ['imm f"1.0" $t']
        vectors = (self.memory_len_in(0) + 7) // 8
        for i in range(vectors):
            off = i * 8
            one = "$aluf" if i == 0 else "$t"
            # mask = (x > 0) ? 1 : 0, forwarded from the ALU.
            lines.append(f"frelu $lm{self.addr_in(1) + off}v {one} $nowrite")
            lines.append(f"fvmul $lm{off}v $aluf $ln{off}v")
        return lines

    def get_memory_layout_tag(self) -> Dict[str, List[str]]:
        return {"inputs": ["default", "default"], "outputs": ["default"]}

    def testcase_hint(self) -> Optional[str]:
        return None
