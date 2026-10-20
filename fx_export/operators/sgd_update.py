#!/usr/bin/env python3

"""Fused SGD step: ``updated = param - learning_rate * grad``.

The graph export used to emit ``Mul(grad, lr)`` followed by ``Sub(param, scaled)``,
which forces the scaled gradient through DRAM and back (a UL and a DL per
parameter).  This operator keeps the product in the MAU forwarding register, so
the parameter is read once, the gradient is read once, and the update is written
once.
"""

from typing import Dict, List, Optional

from . import BaseOperator, register_operator


@register_operator("SGDUpdate")
class SGDUpdateOperator(BaseOperator):
    """param -= lr * grad in one pass."""

    LAYOUTS = {
        (16, 1024): "((16:1), (8_MAB:2, 8_L1B:1, 2_MAB:1, 4_PE:1, 2_W:1))",
        (16, 16): "((16:2), (2:1, 4_PE:1, 2_W:1))",
        (16,): "((2:1, 4_PE:1, 2_W:1))",
    }

    def _learning_rate(self) -> float:
        for attr in self.node.attribute:
            if attr.name == "learning_rate":
                return float(attr.f)
        raise ValueError(f"SGDUpdate '{self.name}' has no learning_rate attribute")

    def _layout(self) -> str:
        shape = tuple(self.in_shape(0))
        if shape not in self.LAYOUTS:
            raise NotImplementedError(f"SGDUpdate: unsupported shape {shape}")
        return self.LAYOUTS[shape]

    def generate_vsm(self) -> List[str]:
        shape = self.in_shape(0)
        assert shape == self.in_shape(1) == self.out_shape(), (shape, self.in_shape(1), self.out_shape())

        layout = self._layout()
        self.check_layout_in(layout, 0)
        self.check_layout_in(layout, 1)
        self.check_layout_out(layout)

        assert self.loc_prefix_in(0) == "m"  # param is loaded to LM0 at addr 0
        assert self.addr_in(0) == 0
        assert self.loc_prefix_in(1) == "m"  # grad follows the param in LM0
        assert self.addr_in(1) == self.memory_len_in(0)
        assert self.loc_prefix_out() == "n"  # result goes to LM1 at addr 0
        assert self.addr_out() == 0

        lr = self._learning_rate()
        lines = [f'imm f"{lr}" $t']
        in0 = self.loc_prefix_in(0)
        in1 = self.loc_prefix_in(1)
        out = self.loc_prefix_out()
        in0_addr = self.addr_in(0)
        in1_addr = self.addr_in(1)
        out_addr = self.addr_out()

        vectors = (self.memory_len_in(0) + 7) // 8
        for i in range(vectors):
            off = i * 8
            fwd = "$aluf" if i == 0 else "$t"
            # The MAU keeps the product in $mauf, so the fused subtract never
            # round-trips the scaled gradient through memory.
            lines.append(
                f"fvmul {fwd} $l{in1}{in1_addr + off}v $nowrite"
            )
            lines.append(
                f"fvadd $l{in0}{in0_addr + off}v -$mauf $l{out}{out_addr + off}v"
            )
        return lines

    def get_memory_layout_tag(self) -> Dict[str, List[str]]:
        return {"inputs": ["default", "default"], "outputs": ["default"]}

    def testcase_hint(self) -> Optional[str]:
        return None
