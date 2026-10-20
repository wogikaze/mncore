#!/usr/bin/env python3

"""Fused softmax gradient: ``grad = (probs - target) * scale``."""

from typing import Dict, List, Optional

from . import BaseOperator, register_operator


@register_operator("LossGrad")
class LossGradOperator(BaseOperator):
    """One pass over the [256, 16] tensors instead of Sub -> DRAM -> Mul."""

    LAYOUT = "((8_L2B:1, 4:2, 8_L1B:1), (2:1, 4_PE:1, 2_W:1))"

    def _scale(self) -> float:
        for attr in self.node.attribute:
            if attr.name == "scale":
                return float(attr.f)
        raise ValueError(f"LossGrad '{self.name}' has no scale attribute")

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

        lines = [f'imm f"{self._scale()}" $t']
        vectors = (self.memory_len_in(0) + 7) // 8
        for i in range(vectors):
            off = i * 8
            lines.append(f"ipassa $lm{self.addr_in(1) + off}v $nowrite")
            # probs - target, forwarded from the ALU, then scaled by the MAU.
            lines.append(f"fvadd $lm{off}v -$aluf $nowrite")
            lines.append(f"fvmul $mauf $t $ln{off}v")
        return lines

    def get_memory_layout_tag(self) -> Dict[str, List[str]]:
        return {"inputs": ["default", "default"], "outputs": ["default"]}

    def testcase_hint(self) -> Optional[str]:
        return None
