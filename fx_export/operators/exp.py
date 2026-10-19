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
ipassa $mabid $omr1; hvadd $t $llm0v $lls0v
imm ui"0x3E000000" $lr12; fvpassa $mauf $ls2v4/$imr1
imm ui"0xBB2AAAAB" $lr16; l1bmr4ffadd $aluf $lbi
imm ui"0x3FB8AA3B" $lr20; fvadd $aluf $aluf $nowrite; l1bmm4 $lbi $ln0
imm ui"0x3F317217" $lr24/1000; fvfma $aluf $ls2v4 $lbf $nowrite; l1bmr4ffadd $mauf $lbi
ffloor $mauf $lr0v; l1bmm4 $lbi $ls16
imm ui"0x39888889" $nowrite; fvfma $aluf -$lr24 $ls2v4 $t; l1bmrffadd $lbf $lbi
imm ui"0x3F7FFFFF" $ls20; fvfma $aluf $mauf -$lr16 $nowrite; l1bmm $lbi $nowrite
fvfma $mauf $t -$ls16 $nowrite; l1bmr4hfadd $lbf $lbi
fvfma $mauf $t $lr12 $nowrite; l1bmm4 $lbi $lm16
fmax $ls2v4 $lbf $omr2; fvfma $mauf $t $ln0 $nowrite
fftoi $lr0v $nowrite; fvfma $mauf $t $ls20 $nowrite
ilsl $aluf $lr24 $nowrite; fvmul $mauf $mauf $nowrite
iadd/$imr2 $aluf $mauf $ln0v4
l1bmm@4 $aluf $lbi
l1bmm $lbi $ln2v4
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
