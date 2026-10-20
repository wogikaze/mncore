#!/usr/bin/env python3

from typing import List, Dict, Any, Optional
from . import BaseOperator
from . import register_operator

@register_operator("Sub")
class SubOperator(BaseOperator):
    """減算演算オペレーター"""
    
    def generate_vsm(self) -> List[str]:
        lines = []
        shape0 = self.in_shape(0)
        shape1 = self.in_shape(1)
        
        in0_prefix = self.loc_prefix_in(0)  # $lm0v  の "m" の部分
        in1_prefix = self.loc_prefix_in(1)  # $lm16v の "m" の部分
        out_prefix = self.loc_prefix_out()        # $ln0v  の "n" の部分
        
        in0_offset = self.addr_in(0)        # $lm0v  の "0" の部分
        in1_offset = self.addr_in(1)        # $lm16v の "16" の部分
        out_offset = self.addr_out()              # $ln0v の "0" の部分
        
        if shape0 == shape1:
            # 同じ形状の場合
            # test unit_tests/train_step/Sub_256x16_256x16_256x16_*
            # 問題名：「A - B」
            
            for i in range(self.memory_len_in_div_ceil(8, 0)):  # PE あたりの長さを、8単語で割って切り上げ
                lines.append(f"ipassa $l{in1_prefix}{in1_offset + i * 8}v $nowrite")
                lines.append(f"fvadd $lm{8 * i}v -$aluf $ln{8 * i}v")

        elif len(shape0) == 2 and len(shape1) == 1 and shape0[0] == shape1[0]:
            # ブロードキャスト（ベクトルを各行から減算） SubRow
            # test unit_tests/train_step/Sub_256x16_256_256x16_*
            # 問題名：「SubRow vec」
            
            
            self.check_layout_in("((4_L2B:2, 64:2), (2:1, 4_PE:1, 2_W:1))", 0)
            self.check_layout_in("((4_L2B:2, 32:1, 2_W:1))", 1)
            self.check_layout_out("((4_L2B:2, 64:2), (2:1, 4_PE:1, 2_W:1))")
            
            assert self.loc_prefix_in(0)  == "m" # LM0 に入力 0 を仮定し、実装を軽減
            assert self.addr_in(0)        ==  0  # Addr 0 に入力 0 を仮定し、実装を軽減
                                                       # ↑、つまり、入力 0 が "$lm0v" だと仮定している
            
            assert self.loc_prefix_in(1)  == "m" # LM0 に入力 1 を仮定し、実装を軽減
            assert self.addr_in(1)        ==  self.memory_len_in(0)  # IN0 の次に入力を仮定し、実装を軽減
            
            assert self.loc_prefix_out(0) == "n" # LM1 に出力を仮定し、実装を軽減
            assert self.addr_out(0)       ==  0  # Addr 0 に出力を仮定し、実装を軽減
                                                       # ↑、つまり、出力 0 が "$ln0v" だと仮定している
        
            # The 24-line winner of the SubRow problem (problems/6.subrow-vec/answer.vsm).
            lines.append(f'''
imm ui"0x00000002" $nowrite
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
l1bmm $llbi $lln240v
            ''')
            return lines
        
        return lines
    
    def testcase_hint(self) -> Optional[str]:
        shape0 = self.in_shape(0)
        shape1 = self.in_shape(1)
        if shape0 == shape1:
            return "mat_sub.vsm"
        else:
            return "sub_rowvec.vsm"
    
    def get_memory_layout_tag(self) -> Dict[str, List[str]]:
        shape0 = self.in_shape(0)
        shape1 = self.in_shape(1)
        if shape0 == shape1:
            # 同じシェイプで、要素ごとの減算
            return {
                "inputs": ["default", "default"],
                "outputs": ["default"]
            }
        elif shape0 == [256, 16] and shape1 == [256]:
            return {
                "inputs": ["PE", "default"],
                "outputs": ["PE"]
            }
        raise NotImplementedError(f"Sub: shapes {shape0} - {shape1}")
    

    def generate_cpp(self) -> List[str]:
        """C++コード生成"""
        lines = []
        
        assert len(self.inputs) >= 2, f"Sub node requires at least 2 inputs, got {len(self.inputs)}"
        
        in1_var = self.get_mapped_var(self.inputs[0])
        in2_var = self.get_mapped_var(self.inputs[1])
        out_var = self.get_output_var_name()
        
        # 形状を取得
        shape0 = self.in_shape(0)
        shape1 = self.in_shape(1)
        
        if shape0 == shape1:
            # 同じ形状の場合
            if len(shape0) == 2:
                lines.append(f"    const Matrix<{shape0[0]}, {shape0[1]}> {out_var} = sub<{shape0[0]}, {shape0[1]}>({in1_var}, {in2_var});")
            elif len(shape0) == 1:
                lines.append(f"    const Vector<{shape0[0]}> {out_var} = sub<{shape0[0]}>({in1_var}, {in2_var});")
            else:
                raise NotImplementedError(f"Sub: shape {shape0}")
        elif len(shape0) == 2 and len(shape1) == 1 and shape0[0] == shape1[0]:
            # ブロードキャスト（ベクトルを各行から減算）
            lines.append(f"    const Matrix<{shape0[0]}, {shape0[1]}> {out_var} = sub_rowvec<{shape0[0]}, {shape0[1]}>({in1_var}, {in2_var});")
        else:
            raise NotImplementedError(f"Sub: shapes {shape0} - {shape1}")
        
        self.variable_map[self.outputs[0]] = out_var
        return lines
    
    def generate_python(self) -> List[str]:
        """Pythonコード生成"""
        lines = []
        
        a = self.inputs[0]
        b = self.inputs[1]
        out = self.outputs[0]
        out_var = self.get_output_var_name()
        
        shape_a = self.in_shape(0)
        shape_b = self.in_shape(1)
        if shape_a == shape_b:
            lines.append(f"    {out_var} = {self.get_mapped_var(a)} - {self.get_mapped_var(b)}")
        elif len(shape_a) == 2 and len(shape_b) == 1 and shape_a[0] == shape_b[0]:
            lines.append(f"    {out_var} = {self.get_mapped_var(a)} - {self.get_mapped_var(b)}.unsqueeze(-1)")
        else:
            raise NotImplementedError(f"Sub: shapes {shape_a} - {shape_b}")
        self.variable_map[out] = out_var
        
        return lines
