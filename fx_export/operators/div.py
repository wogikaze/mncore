#!/usr/bin/env python3

from typing import List, Dict, Any, Optional
from . import BaseOperator, register_operator

@register_operator("Div")
class DivOperator(BaseOperator):
    """除算演算オペレーター"""
    
    def generate_vsm(self) -> List[str]:
        lines = []
        shape0 = self.in_shape(0)
        shape1 = self.in_shape(1)
        
        if len(shape0) == 2 and len(shape1) == 1 and shape0[0] == shape1[0]:
            # ブロードキャスト除算（ベクトルで各行を除算） DivRow
            self.check_layout_in("((4_L2B:2, 64:2), (2:1, 4_PE:1, 2_W:1))", 0)
            self.check_layout_in("((4_L2B:2, 32:1, 2_W:1))", 1)
            self.check_layout_out("((4_L2B:2, 64:2), (2:1, 4_PE:1, 2_W:1))")
            
            assert self.loc_prefix_in(0)  == "m" # LM0 に入力0を仮定し、実装を軽減
            assert self.loc_prefix_in(1)  == "m" # LM0 に入力1を仮定し、実装を軽減
            assert self.addr_in(0)        ==  0  # Addr 0 に入力を仮定し、実装を軽減
                                                       # ↑、つまり、入力0が "$lm0v" だと仮定している
            
            assert self.loc_prefix_out(0) == "n" # LM1 に出力を仮定し、実装を軽減
            assert self.addr_in(1)        ==  self.memory_len_in(0)  # IN0 の次に入力を仮定し、実装を軽減
            assert self.addr_out(0)       ==  0  # Addr 0 に出力を仮定し、実装を軽減
                                                       # ↑、つまり、出力が "$ln0v" だと仮定している

            # test unit_tests/train_step/Div_*
            # 問題名：「DivRow vec」
            
            # The 29-line winner of the DivRow problem (problems/12.divrow-vec/answer.vsm).
            lines.append(f'''
imm ui"0x00000002" $nowrite
llsl $mabid $aluf $t
nop
frsqrt $mt256v $nowrite; fvpassa $mt256v $r0v
imm ui"0x40000000" $nowrite; fvmul $aluf $aluf $ls0v
fvfma -$mauf $r0v $aluf $nowrite; l1bmd+0 $aluf $lbi
fvmul $mauf $ls0v $ls0v; l1bmd+0 $lbi $nowrite
imm ui"0x00000004" $nowrite; fvfma -$mauf $r0v $lbf $nowrite
llsl $mabid $aluf $lmb; fvmul $mauf $ls0v $ls0v
fvpassa $mauf $s1v2
nop
fvmul $lm0v $ls[0,0,2,2] $lr0v $ln0v; l1bmm@1 $ls[0,0,2,2] $lbi
fvmul $lm8v $ls[4,4,6,6] $lr8v $ln8v; l1bmm@1 $ls[4,4,6,6] $lbi; l1bmm $lbi $nowrite
fvmul $lm16v $lbf $ln16v; l1bmm $lbi $nowrite
fvmul $lm24v $lbf $ln24v; l1bmm@2 $llr0v $llbi
zero $lmb; l1bmm@3 $llr0v $llbi; l1bmm $llbi $lln32v
l1bmm@4 $llr0v $llbi; l1bmm $llbi $lln48v
l1bmm@5 $llr0v $llbi; l1bmm $llbi $lln64v
l1bmm@6 $llr0v $llbi; l1bmm $llbi $lln80v
l1bmm@7 $llr0v $llbi; l1bmm $llbi $lln96v
l1bmm@8 $llr0v $llbi; l1bmm $llbi $lln112v
l1bmm@9 $llr0v $llbi; l1bmm $llbi $lln128v
l1bmm@10 $llr0v $llbi; l1bmm $llbi $lln144v
l1bmm@11 $llr0v $llbi; l1bmm $llbi $lln160v
l1bmm@12 $llr0v $llbi; l1bmm $llbi $lln176v
l1bmm@13 $llr0v $llbi; l1bmm $llbi $lln192v
l1bmm@14 $llr0v $llbi; l1bmm $llbi $lln208v
l1bmm@15 $llr0v $llbi; l1bmm $llbi $lln224v
l1bmm $llbi $lln240v
            ''')

            return lines
        raise NotImplementedError(f"Div: shapes {shape0} / {shape1}")
        
    def testcase_hint(self) -> Optional[str]:
        return "div_row.vsm"

    def get_memory_layout_tag(self) -> Dict[str, List[str]]:
        shape0 = self.in_shape(0)
        shape1 = self.in_shape(1)
        if shape0 == [256, 16] and shape1 == [256]:
            return {
                "inputs": ["PE", "default"],
                "outputs": ["PE"]
            }
        raise NotImplementedError(f"Div: shapes {shape0} / {shape1}")
    
        
    def generate_cpp(self) -> List[str]:
        """C++コード生成"""
        lines = []
        
        assert len(self.inputs) >= 2, f"Div node requires 2 inputs, got {len(self.inputs)}"
        
        a = self.inputs[0]
        b = self.inputs[1]
        out = self.outputs[0]
        out_var = self.get_output_var_name()
        
        a_var = self.get_mapped_var(a)
        b_var = self.get_mapped_var(b)
        
        # 形状を取得
        shape0 = self.in_shape(0)
        shape1 = self.in_shape(1)
        
        if len(shape0) == 2 and len(shape1) == 1 and shape0[0] == shape1[0]:
            # ブロードキャスト除算（ベクトルで各行を除算）
            lines.append(f"    const Matrix<{shape0[0]}, {shape0[1]}> {out_var} = div_rowvec<{shape0[0]}, {shape0[1]}>({a_var}, {b_var});")
        else:
            raise NotImplementedError(f"Div: shapes {shape0} / {shape1}")
        
        self.variable_map[out] = out_var
        
        return lines
    
    def generate_python(self) -> List[str]:
        """Pythonコード生成"""
        lines = []
        
        a = self.inputs[0]
        b = self.inputs[1]
        out = self.outputs[0]
        out_var = self.get_output_var_name()
        
        shape0 = self.in_shape(0)
        shape1 = self.in_shape(1)
        if len(shape0) == 2 and len(shape1) == 1 and shape0[0] == shape1[0]:
            lines.append(f"    {out_var} = {self.get_mapped_var(a)} / {self.get_mapped_var(b)}.unsqueeze(-1)")
        else:
            raise NotImplementedError(f"Div: shapes {shape0} / {shape1}")
        
        self.variable_map[out] = out_var
        
        return lines
