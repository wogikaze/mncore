#!/usr/bin/env python3

from typing import List, Dict, Any, Optional
from . import BaseOperator
from . import register_operator
from .gemm_impls import gemm_trb_256_1024_16_bias_relu


@register_operator("GemmBiasRelu")
class GemmBiasReluOperator(BaseOperator):
    """Gemm + バイアス加算 + ReLU の融合演算オペレーター (FC-ReLU fusion)

    入力:
      0: [256, 1024]  FC 入力行列
      1: [16, 1024]   重み行列 (transB 適用)
      2: [16]         バイアスベクトル
    出力:
      0: [256, 16]    ReLU 適用後の結果 (LM1 に直接書き込み)
    """

    def generate_vsm(self) -> List[str]:
        shape0 = self.in_shape(0)
        shape1 = self.in_shape(1)
        shape2 = self.in_shape(2)

        if shape0 == [256, 1024] and shape1 == [16, 1024] and shape2 == [16]:
            return gemm_trb_256_1024_16_bias_relu.generate_vsm(self)

        raise NotImplementedError(
            f"GemmBiasRelu: shapes {shape0} x {shape1} + {shape2} not supported"
        )

    def testcase_hint(self) -> Optional[str]:
        return "gemm_bias_relu_*.vsm"

    def get_memory_layout_tag(self) -> Dict[str, List[str]]:
        shape0 = self.in_shape(0)
        shape1 = self.in_shape(1)
        shape2 = self.in_shape(2)

        if shape0 == [256, 1024] and shape1 == [16, 1024] and shape2 == [16]:
            return {
                "inputs": ["default", "default", "default"],
                "outputs": ["default"],
            }

        raise NotImplementedError(
            f"GemmBiasRelu: shapes {shape0} x {shape1} + {shape2} not supported"
        )

    def generate_python(self) -> List[str]:
        lines = []
        a_var = self.get_mapped_var(self.inputs[0])
        b_var = self.get_mapped_var(self.inputs[1])
        c_var = self.get_mapped_var(self.inputs[2])
        out_var = self.get_output_var_name()

        lines.append(f"    {out_var} = torch.relu(torch.matmul({a_var}, {b_var}.T) + {c_var})")
        self.variable_map[self.outputs[0]] = out_var
        return lines

    def generate_cpp(self) -> List[str]:
        lines = []
        a_var = self.get_mapped_var(self.inputs[0])
        b_var = self.get_mapped_var(self.inputs[1])
        c_var = self.get_mapped_var(self.inputs[2])
        out_var = self.get_output_var_name()

        shape0 = self.in_shape(0)  # [256, 1024]
        shape1 = self.in_shape(1)  # [16, 1024]  (transB)

        m, k = shape0
        n = shape1[0]

        lines.append(
            f"    const Matrix<{m}, {n}> {out_var} = "
            f"relu<{m}, {n}>(add_colvec<{m}, {n}>("
            f"matmul<{m}, {k}, {n}>({a_var}, trans<{n}, {k}>({b_var})), {c_var}));"
        )
        self.variable_map[self.outputs[0]] = out_var
        return lines
