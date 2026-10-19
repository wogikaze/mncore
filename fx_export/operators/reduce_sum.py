#!/usr/bin/env python3

from typing import List, Dict, Any, Optional
from . import BaseOperator
from . import register_operator

@register_operator("ReduceSum")
class ReduceSumOperator(BaseOperator):
    """ReduceSum演算オペレーター"""

    def generate_vsm(self) -> List[str]:
        # グラフから形状を取得
        shape = self.in_shape()
        lines = []
        
        axes = list(self.get_attr('axes').ints)
        
        # 形状によって処理を分岐
        if len(shape) == 2 and (axes == [0]): # sum_col（列方向の和）
            if shape == [256, 16]:
                self.check_layout_in("((8_L2B:1, 4:2, 8_L1B:1), (2:1, 4_PE:1, 2_W:1))")
                self.check_layout_out("((8:1, 2_W:1))")
                assert self.loc_prefix_out() == "d"
                
                assert self.loc_prefix_in()  == "m" # LM0 に入力を仮定し、実装を軽減
                assert self.addr_in()        ==  0  # Addr 0 に入力を仮定し、実装を軽減
                                                    # ↑、つまり、入力が "$lm0v" だと仮定している

                #  test unit_tests/train_step/ReduceSum_256x16_16_*
                # 問題名：「SumCol」
                
                x = self.addr_out()        # "$d0" の "0" の部分

                lines.append("fvpassa $lm[0,2,0,2] $nowrite")
                lines.append("fvadd $lm[4,6,4,6] $mauf $nowrite")
                lines.append("fvadd $lm[8,10,8,10] $mauf $nowrite")
                lines.append("fvadd $lm[12,14,12,14] $mauf $lr0v")
                lines.append("")
                lines.append("nop")
                lines.append("l1bmm@0 $lr0v $lb0")
                lines.append("nop/3")
                lines.append("l2bmrffadd $lb0 $lc0")
                lines.append(f"mvrffadd/n64 $lc0 $d{x}")

                return lines
            
        if len(shape) == 2 and (axes == [-1]): # sum_row（行方向の和）
            if shape == [256, 16]:
                self.check_layout_in("((4_L2B:2, 64:2), (2:1, 4_PE:1, 2_W:1))")
                self.check_layout_out("((4_L2B:2, 32:1, 2_W:1))")
                
                assert self.loc_prefix_in()  == "m" # LM0 に入力を仮定し、実装を軽減
                assert self.addr_in()        ==  0  # Addr 0 に入力を仮定し、実装を軽減
                                                    # ↑、つまり、入力が "$lm0v" だと仮定している
                
                assert self.loc_prefix_out() == "n" # LM1 に出力を仮定し、実装を軽減
                assert self.addr_out()       ==  0  # Addr 0 に出力を仮定し、実装を軽減
                                                    # ↑、つまり、出力が "$ln0v" だと仮定している


                #  test unit_tests/train_step/ReduceSum_256x16_256_*
                # 問題名：「SumRow」
                

                lines.append(f'''
imm ui"0x00000004" $nowrite
ilsl $mabid $aluf $lt
imm ui"0x3FC00000" $nowrite
fbfn $mt0v4 $nowrite; fmwrite $aluf $lx0
fbfn $mt1v4 $nowrite; fmmul $lx $aluf $nowrite
fbfn $mt2v4 $nowrite; fmfma $lx $aluf $mauf $nowrite
fbfn $mt3v4 $nowrite; fmfma $lx $aluf $mauf $nowrite
fmfma $lx $aluf $mauf $r0v $s0v $n0v
l1bmm4@1 $mauf $lbi
l1bmm4@2 $s0v $lbi; l1bmm4 $lbi $r4v $n4v
l1bmm4@3 $lls0 $llbi; l1bmm4 $lbi $r8v $n8v
l1bmm4 $llbi $llr12/ll1000 $lln12/ll1000
l1bmm@4 $llr0v $llbi
l1bmm@8 $llr0v $llbi; l1bmm $llbi $lln16v
l1bmm@12 $llr0v $llbi; l1bmm $llbi $lln32v
l1bmm $llbi $lln48v
                ''')

                return lines
        
        raise NotImplementedError(f"ReduceSum: shape={shape}, axes={axes}")

    def testcase_hint(self) -> Optional[str]:
        return "sum_*.vsm"

    
    def get_memory_layout_tag(self) -> Dict[str, List[str]]:
        shape = self.in_shape(0)
        axes = list(self.get_attr('axes').ints)
        if axes == [0]:  # col_sum（列方向の和）
            if shape == [256, 16]:
                return {
                    "inputs": ["default"],
                    "outputs": ["DRAM"]
                }
        elif axes == [1] or axes == [-1]:  # row_sum（行方向の和）
            if shape == [256, 16]:
                return {
                    "inputs": ["PE"],
                    "outputs": ["default"]
                }
        raise NotImplementedError(f"ReduceSum: shape={shape}, axes={axes}")


    def generate_cpp(self) -> List[str]:
        """C++コード生成"""
        lines = []
        
        assert len(self.inputs) >= 1, f"ReduceSum node requires at least 1 input, got {len(self.inputs)}"
        
        in_var = self.get_mapped_var(self.inputs[0])
        out_var = self.get_output_var_name()
        
        # 軸を取得
        axes = list(self.get_attr('axes').ints)
        
        # 形状を取得
        shape = self.in_shape(0)
        
        if len(shape) != 2:
            raise NotImplementedError
        if axes == [0]:
            # 行方向の合計（列ベクトルを返す）
            assert len(shape) == 2, f"ReduceSum with axis=0 expects 2D tensor, got {shape}"
            lines.append(f"    const Vector<{shape[1]}> {out_var} = col_sum<{shape[0]}, {shape[1]}>({in_var});")
        elif axes == [1] or axes == [-1]:
            # 列方向の合計（行ベクトルを返す）
            assert len(shape) == 2, f"ReduceSum with axis=1 expects 2D tensor, got {shape}"
            lines.append(f"    const Vector<{shape[0]}> {out_var} = row_sum<{shape[0]}, {shape[1]}>({in_var});")
        else:
            NotImplementedError
        self.variable_map[self.outputs[0]] = out_var
        return lines

    
    def generate_python(self) -> List[str]:
        """Pythonコード生成"""
        lines = []
        
        inp = self.inputs[0]
        out = self.outputs[0]
        out_var = self.get_output_var_name()
        
        # 軸を取得
        axes = None
        for attr in self.node.attribute:
            if attr.name == 'axes':
                axes = list(attr.ints)
                break
        
        if axes:
            lines.append(f"    {out_var} = torch.sum({self.get_mapped_var(inp)}, dim={axes[0]})")
        else:
            lines.append(f"    {out_var} = torch.sum({self.get_mapped_var(inp)})")
        
        self.variable_map[out] = out_var
        
        return lines
