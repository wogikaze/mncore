#!/usr/bin/env python3

"""Fused row-max and subtract: ``out = x - max(x, axis=-1)``.

The ReduceMax kernel writes the max straight to LM0:256, where the SubRow
kernel reads it, so the max never goes through DRAM (its UL and DL disappear).
"""

from typing import Dict, List, Optional

from . import BaseOperator, register_operator


@register_operator("MaxSub")
class MaxSubOperator(BaseOperator):
    LAYOUT = "((4_L2B:2, 64:2), (2:1, 4_PE:1, 2_W:1))"

    REDUCE_MAX = '''imm ui"0x00000004" $nowrite
llsl $mabid $aluf $t
nop
fpassa $mt0v4 $nowrite
fmax $mt1v4 $aluf $nowrite
fmax $mt2v4 $aluf $nowrite
fmax $mt3v4 $aluf $r0v
msl $aluf $nowrite
fmax $aluf $r0v $r0v
msl $aluf $nowrite
msl $aluf $nowrite
fmax $aluf $r0v $r0v $s0v $m256v
l1bmm4@1 $aluf $lbi
l1bmm4@2 $s0v $lbi; l1bmm4 $lbi $r4v $m260v
l1bmm4@3 $lls0 $llbi; l1bmm4 $lbi $r8v $m264v
l1bmm4 $llbi $llr12/ll1000 $llm268/ll1000
l1bmm@4 $llr0v $llbi
l1bmm@8 $llr0v $llbi; l1bmm $llbi $llm272v
l1bmm@12 $llr0v $llbi; l1bmm $llbi $llm288v
l1bmm $llbi $llm304v'''

    SUB = '''imm ui"0x00000002" $nowrite
llsl $mabid $aluf $t; fvpassa $m260v $r8v2
imm ui"0x00000004" $nowrite; fvpassa $mauf $r9v2
llsl $mabid $aluf $t; fvpassa $mt256v $r0v2
fpassa $mauf $r1v2; fvadd $lm16v -$lr[8,8,10,10] $ln16v
fvadd $mt0v -$r0 $s0v $n0v
fvadd $mt4v -$r2 $s4v $n4v
fvadd $lmt8v -$lr[4,4,6,6] $ls8v $ln8v
fvadd $lm24v -$lr[12,12,14,14] $ln24v
l1bmm@2 $lls0v $llbi
l1bmm@3 $lls0v $llbi; l1bmm $llbi $lln32v
l1bmm@4 $lls0v $llbi; l1bmm $llbi $lln48v
l1bmm@5 $lls0v $llbi; l1bmm $llbi $lln64v
l1bmm@6 $lls0v $llbi; l1bmm $llbi $lln80v
l1bmm@7 $lls0v $llbi; l1bmm $llbi $lln96v
l1bmm@8 $lls0v $llbi; l1bmm $llbi $lln112v
l1bmm@9 $lls0v $llbi; l1bmm $llbi $lln128v
l1bmm@10 $lls0v $llbi; l1bmm $llbi $lln144v
l1bmm@11 $lls0v $llbi; l1bmm $llbi $lln160v
l1bmm@12 $lls0v $llbi; l1bmm $llbi $lln176v
l1bmm@13 $lls0v $llbi; l1bmm $llbi $lln192v
l1bmm@14 $lls0v $llbi; l1bmm $llbi $lln208v
l1bmm@15 $lls0v $llbi; l1bmm $llbi $lln224v
l1bmm $llbi $lln240v'''

    def generate_vsm(self) -> List[str]:
        assert self.in_shape(0) == [256, 16]
        assert self.out_shape() == [256, 16]
        self.check_layout_in(self.LAYOUT, 0)
        self.check_layout_out(self.LAYOUT)
        assert self.loc_prefix_in(0) == "m" and self.addr_in(0) == 0
        assert self.loc_prefix_out() == "n" and self.addr_out() == 0
        assert self.memory_len_in(0) == 256
        lines = self.REDUCE_MAX.splitlines() + ["nop/3"] + self.SUB.splitlines()
        return lines

    def get_memory_layout_tag(self) -> Dict[str, List[str]]:
        return {"inputs": ["PE"], "outputs": ["PE"]}

    def testcase_hint(self) -> Optional[str]:
        return None
