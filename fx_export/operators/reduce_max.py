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
fvpassa $m0v4 $nowrite
fmax $m1v4 $mauf $nowrite
fmax $m2v4 $aluf $nowrite
fmax $m3v4 $aluf $r0v
msr $aluf $s0v
fmax $aluf $r0v $r0v
msr $s0v $s0v
fmax $aluf $r0v $r0v
msr $s0v $s0v
fmax $aluf $r0v $n0v;fvpassa $m16v4 $nowrite
fmax $m17v4 $mauf $nowrite
fmax $m18v4 $aluf $nowrite
fmax $m19v4 $aluf $r0v
msr $aluf $s0v
fmax $aluf $r0v $r0v
msr $s0v $s0v
fmax $aluf $r0v $r0v
msr $s0v $s0v
fmax $aluf $r0v $n4v;fvpassa $m32v4 $nowrite
fmax $m33v4 $mauf $nowrite
fmax $m34v4 $aluf $nowrite
fmax $m35v4 $aluf $r0v
msr $aluf $s0v
fmax $aluf $r0v $r0v
msr $s0v $s0v
fmax $aluf $r0v $r0v
msr $s0v $s0v
fmax $aluf $r0v $n8v;fvpassa $m48v4 $nowrite
fmax $m49v4 $mauf $nowrite
fmax $m50v4 $aluf $nowrite
fmax $m51v4 $aluf $r0v
msr $aluf $s0v
fmax $aluf $r0v $r0v
msr $s0v $s0v
fmax $aluf $r0v $r0v
msr $s0v $s0v
fmax $aluf $r0v $n12v;fvpassa $m64v4 $nowrite
fmax $m65v4 $mauf $nowrite
fmax $m66v4 $aluf $nowrite
fmax $m67v4 $aluf $r0v
msr $aluf $s0v
fmax $aluf $r0v $r0v
msr $s0v $s0v
fmax $aluf $r0v $r0v
msr $s0v $s0v
fmax $aluf $r0v $n16v;fvpassa $m80v4 $nowrite
fmax $m81v4 $mauf $nowrite
fmax $m82v4 $aluf $nowrite
fmax $m83v4 $aluf $r0v
msr $aluf $s0v
fmax $aluf $r0v $r0v
msr $s0v $s0v
fmax $aluf $r0v $r0v
msr $s0v $s0v
fmax $aluf $r0v $n20v;fvpassa $m96v4 $nowrite
fmax $m97v4 $mauf $nowrite
fmax $m98v4 $aluf $nowrite
fmax $m99v4 $aluf $r0v
msr $aluf $s0v
fmax $aluf $r0v $r0v
msr $s0v $s0v
fmax $aluf $r0v $r0v
msr $s0v $s0v
fmax $aluf $r0v $n24v;fvpassa $m112v4 $nowrite
fmax $m113v4 $mauf $nowrite
fmax $m114v4 $aluf $nowrite
fmax $m115v4 $aluf $r0v
msr $aluf $s0v
fmax $aluf $r0v $r0v
msr $s0v $s0v
fmax $aluf $r0v $r0v
msr $s0v $s0v
fmax $aluf $r0v $n28v;fvpassa $m128v4 $nowrite
fmax $m129v4 $mauf $nowrite
fmax $m130v4 $aluf $nowrite
fmax $m131v4 $aluf $r0v
msr $aluf $s0v
fmax $aluf $r0v $r0v
msr $s0v $s0v
fmax $aluf $r0v $r0v
msr $s0v $s0v
fmax $aluf $r0v $n32v;fvpassa $m144v4 $nowrite
fmax $m145v4 $mauf $nowrite
fmax $m146v4 $aluf $nowrite
fmax $m147v4 $aluf $r0v
msr $aluf $s0v
fmax $aluf $r0v $r0v
msr $s0v $s0v
fmax $aluf $r0v $r0v
msr $s0v $s0v
fmax $aluf $r0v $n36v;fvpassa $m160v4 $nowrite
fmax $m161v4 $mauf $nowrite
fmax $m162v4 $aluf $nowrite
fmax $m163v4 $aluf $r0v
msr $aluf $s0v
fmax $aluf $r0v $r0v
msr $s0v $s0v
fmax $aluf $r0v $r0v
msr $s0v $s0v
fmax $aluf $r0v $n40v;fvpassa $m176v4 $nowrite
fmax $m177v4 $mauf $nowrite
fmax $m178v4 $aluf $nowrite
fmax $m179v4 $aluf $r0v
msr $aluf $s0v
fmax $aluf $r0v $r0v
msr $s0v $s0v
fmax $aluf $r0v $r0v
msr $s0v $s0v
fmax $aluf $r0v $n44v;fvpassa $m192v4 $nowrite
fmax $m193v4 $mauf $nowrite
fmax $m194v4 $aluf $nowrite
fmax $m195v4 $aluf $r0v
msr $aluf $s0v
fmax $aluf $r0v $r0v
msr $s0v $s0v
fmax $aluf $r0v $r0v
msr $s0v $s0v
fmax $aluf $r0v $n48v;fvpassa $m208v4 $nowrite
fmax $m209v4 $mauf $nowrite
fmax $m210v4 $aluf $nowrite
fmax $m211v4 $aluf $r0v
msr $aluf $s0v
fmax $aluf $r0v $r0v
msr $s0v $s0v
fmax $aluf $r0v $r0v
msr $s0v $s0v
fmax $aluf $r0v $n52v;fvpassa $m224v4 $nowrite
fmax $m225v4 $mauf $nowrite
fmax $m226v4 $aluf $nowrite
fmax $m227v4 $aluf $r0v
msr $aluf $s0v
fmax $aluf $r0v $r0v
msr $s0v $s0v
fmax $aluf $r0v $r0v
msr $s0v $s0v
fmax $aluf $r0v $n56v;fvpassa $m240v4 $nowrite
fmax $m241v4 $mauf $nowrite
fmax $m242v4 $aluf $nowrite
fmax $m243v4 $aluf $r0v
msr $aluf $s0v
fmax $aluf $r0v $r0v
msr $s0v $s0v
fmax $aluf $r0v $r0v
msr $s0v $s0v
fmax $aluf $r0v $n60v
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
