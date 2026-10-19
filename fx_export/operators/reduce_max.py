#!/usr/bin/env python3

from typing import List, Dict, Any, Optional
from . import BaseOperator
from . import register_operator


@register_operator("ReduceMax")
class ReduceMaxOperator(BaseOperator):
    """ReduceMax演算オペレーター"""

    def generate_vsm(self) -> List[str]:
        # グラフから形状を取得
        shape = self.in_shape()
        lines = []

        axes = list(self.get_attr("axes").ints)

        # 形状によって処理を分岐
        if len(shape) == 2 and (axes == [-1]):  # max_row（行方向の最大）
            if shape == [256, 16]:
                self.check_layout_in("((4_L2B:2, 64:2), (2:1, 4_PE:1, 2_W:1))")
                self.check_layout_out("((4_L2B:2, 32:1, 2_W:1))")
                assert self.loc_prefix_in() == "m"  # LM0 に入力を仮定し、実装を軽減
                assert self.addr_in() == 0  # Addr 0 に入力を仮定し、実装を軽減
                # ↑、つまり、入力が "$lm0v" だと仮定している

                assert self.loc_prefix_out() == "n"  # LM1 に出力を仮定し、実装を軽減
                assert self.addr_out() == 0  # Addr 0 に出力を仮定し、実装を軽減
                # ↑、つまり、出力が "$ln0v" だと仮定している

                # test unit_tests/train_step/ReduceMax_*
                # 問題名：「MaxRow」
                
                lines.append(f'''
imm ui"0x00000004" $nowrite
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
fmax $aluf $r0v $r0v $s0v $n0v
l1bmm4@1 $aluf $lbi
l1bmm4@2 $s0v $lbi; l1bmm4 $lbi $r4v $n4v
l1bmm4@3 $lls0 $llbi; l1bmm4 $lbi $r8v $n8v
l1bmm4 $llbi $llr12/ll1000 $lln12/ll1000
l1bmm@4 $llr0v $llbi
l1bmm@8 $llr0v $llbi; l1bmm $llbi $lln16v
l1bmm@12 $llr0v $llbi; l1bmm $llbi $lln32v
l1bmm $llbi $lln48v
                ''')
                return lines
        raise NotImplementedError

    def testcase_hint(self) -> Optional[str]:
        return "max_row.vsm"

    def get_memory_layout_tag(self) -> Dict[str, List[str]]:
        shape0 = self.in_shape(0)
        oshape = self.out_shape(0)
        axes = list(self.get_attr("axes").ints)
        if shape0 == [256, 16] and oshape == [256] and axes == [-1]:
            return {"inputs": ["PE"], "outputs": ["default"]}
        raise NotImplementedError(f"ReduceMax: shape={shape0}, axes={axes}")

    def generate_cpp(self) -> List[str]:
        """C++コード生成"""
        lines = []

        assert (
            len(self.inputs) >= 1
        ), f"ReduceMax node requires at least 1 input, got {len(self.inputs)}"

        in_var = self.get_mapped_var(self.inputs[0])
        out_var = self.get_output_var_name()

        # 属性を取得
        axes = list(self.get_attr("axes").ints)

        # 形状を取得
        shape = self.in_shape(0)

        if len(shape) == 2 and (axes == [-1]):
            # 行方向の最大値（最後の次元）
            lines.append(
                f"    const Vector<{shape[0]}> {out_var} = row_max<{shape[0]}, {shape[1]}>({in_var});"
            )
        else:
            raise NotImplementedError(f"ReduceMax: axes={axes}, shape={shape}")

        self.variable_map[self.outputs[0]] = out_var
        return lines

    def generate_python(self) -> List[str]:
        """Pythonコード生成"""
        lines = []

        inp = self.inputs[0]
        out = self.outputs[0]
        out_var = self.get_output_var_name()

        # 属性を取得
        axes = list(self.get_attr("axes").ints)
        if len(axes) != 1:
            raise NotImplementedError(f"ReduceMax: axes={axes}")

        axis = axes[0]
        lines.append(
            f"    {out_var}, _ = torch.max({self.get_mapped_var(inp)}, dim={axis}, keepdim=False)"
        )

        self.variable_map[out] = out_var

        return lines
