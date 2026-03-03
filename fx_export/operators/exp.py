#!/usr/bin/env python3

from typing import List, Dict, Any, Optional
from . import BaseOperator, register_operator

@register_operator("Exp")
class ExpOperator(BaseOperator):
    """Exp（指数関数）演算オペレーター"""
    def generate_vsm(self) -> List[str]:
        
        assert self.loc_prefix_in()  == "m" # LM0 に入力を仮定し、実装を軽減
        assert self.addr_in()        ==  0  # Addr 0 に入力を仮定し、実装を軽減
                                            # ↑、つまり、入力が "$lm0v" だと仮定している
        
        assert self.loc_prefix_out() == "n" # LM1 に出力を仮定し、実装を軽減
        assert self.addr_out()       ==  0  # Addr 0 に出力を仮定し、実装を軽減
                                            # ↑、つまり、出力が "$ln0v" だと仮定している
        
        assert self.memory_len_in(0) == 16  # 実装の簡略化のため、PE あたり 16 単語を仮定
        
        # test unit_tests/train_step/Exp_*
        lines = []

        lines.append(f'''
imm f"1.4426950408889634" $t
imm f"0.5" $r0v
imm f"0.5" $r4v
imm f"0.5" $r8v
imm f"0.5" $r12v
fvfma $m0v $t $r0v $r0v
fvfma $m4v $t $r4v $r4v
fvfma $m8v $t $r8v $r8v
fvfma $m12v $t $r12v $r12v
ffloor $r0v $r0v
ffloor $r4v $r4v
ffloor $r8v $r8v
ffloor $r12v $r12v

fvpassa $r0v $s0v
fvpassa $r4v $s4v
fvpassa $r8v $s8v
fvpassa $r12v $s12v

imm f"-0.6931471805599453" $t
fvfma $s0v $aluf $m0v $r0v
fvfma $s4v $t $m4v $r4v
fvfma $s8v $t $m8v $r8v
fvfma $s12v $t $m12v $r12v

fftoi $s0v $s0v
fftoi $s4v $s4v
fftoi $s8v $s8v
fftoi $s12v $s12v
imm i"23" $t
ilsl $s0v $aluf $s0v
ilsl $s4v $t $s4v
ilsl $s8v $t $s8v
ilsl $s12v $t $s12v

fvpassa $r0v $n0v
fvpassa $r4v $n4v
fvpassa $r8v $n8v
fvpassa $r12v $n12v

imm f"0.0001984126984126984" $r0v
imm f"0.0001984126984126984" $r4v
imm f"0.0001984126984126984" $r8v
imm f"0.0001984126984126984" $r12v
imm f"0.001388888888888889" $t
fvfma $r0v $n0v $aluf $r0v
fvfma $r4v $n4v $t $r4v
fvfma $r8v $n8v $t $r8v
fvfma $r12v $n12v $t $r12v

imm f"0.008333333333333333" $t
fvfma $r0v $n0v $aluf $r0v
fvfma $r4v $n4v $t $r4v
fvfma $r8v $n8v $t $r8v
fvfma $r12v $n12v $t $r12v

imm f"0.041666666666666664" $t
fvfma $r0v $n0v $aluf $r0v
fvfma $r4v $n4v $t $r4v
fvfma $r8v $n8v $t $r8v
fvfma $r12v $n12v $t $r12v

imm f"0.16666666666666666" $t
fvfma $r0v $n0v $aluf $r0v
fvfma $r4v $n4v $t $r4v
fvfma $r8v $n8v $t $r8v
fvfma $r12v $n12v $t $r12v

imm f"0.5" $t
fvfma $r0v $n0v $aluf $r0v
fvfma $r4v $n4v $t $r4v
fvfma $r8v $n8v $t $r8v
fvfma $r12v $n12v $t $r12v

imm f"1.0" $t
fvfma $r0v $n0v $aluf $r0v
fvfma $r4v $n4v $t $r4v
fvfma $r8v $n8v $t $r8v
fvfma $r12v $n12v $t $r12v
fvfma $r0v $n0v $t $r0v
fvfma $r4v $n4v $t $r4v
fvfma $r8v $n8v $t $r8v
fvfma $r12v $n12v $t $r12v

iadd $r0v $s0v $r0v
iadd $r4v $s4v $r4v
iadd $r8v $s8v $r8v
iadd $r12v $s12v $r12v

imm f"14.0" $t
fvadd $m0v $aluf $s0v
fvadd $m4v $t $s4v
fvadd $m8v $t $s8v
fvadd $m12v $t $s12v
frelu $s0v $r0v $n0v
frelu $s4v $r4v $n4v
frelu $s8v $r8v $n8v
frelu $s12v $r12v $n12v
        ''')
        return lines

    def testcase_hint(self) -> Optional[str]:
        return "exp.vsm"

    def get_memory_layout_tag(self) -> Dict[str, List[str]]:
        return {
            "inputs": ["default"],
            "outputs": ["default"]
        }
    
    def generate_cpp(self) -> List[str]:
        """C++コード生成"""
        lines = []
        
        assert len(self.inputs) >= 1, f"Exp node requires at least 1 input, got {len(self.inputs)}"
        
        in_var = self.get_mapped_var(self.inputs[0])
        out_var = self.get_output_var_name()
        
        # 出力形状を取得（Expの出力形状は入力形状と同じ）
        shape = self.in_shape(0)
        
        if not shape:
            # 形状情報が全くない場合はエラー
            raise ValueError(f"Exp: No shape information available for output '{self.outputs[0]}'. "
                           f"This is likely a bug in the ONNX graph generation.")
        
        if len(shape) == 2:
            lines.append(f"    const Matrix<{shape[0]}, {shape[1]}> {out_var} = exp<{shape[0]}, {shape[1]}>({in_var});")
        else:
            raise NotImplementedError(f"Exp: Unsupported shape {shape}. Only 2D matrices are supported.")
        
        self.variable_map[self.outputs[0]] = out_var
        return lines
    
    def generate_python(self) -> List[str]:
        """Pythonコード生成"""
        lines = []
        
        inp = self.inputs[0]
        out = self.outputs[0]
        out_var = self.get_output_var_name()
        
        shape = self.in_shape(0)
        if len(shape) != 2:
            raise NotImplementedError(f"Exp: shape {shape}")

        lines.append(f"    {out_var} = torch.exp({self.get_mapped_var(inp)})")
        
        self.variable_map[out] = out_var
        
        return lines
