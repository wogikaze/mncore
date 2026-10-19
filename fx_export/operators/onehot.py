#!/usr/bin/env python3

from typing import List, Dict, Any, Optional
from onnx import numpy_helper
from . import BaseOperator
from . import register_operator

@register_operator("OneHot")
class OneHotOperator(BaseOperator):
    """OneHot演算オペレーター"""

    def _get_depth(self) -> int:
        for attr in self.node.attribute:
            if attr.name == 'depth':
                return int(attr.i)

        if len(self.inputs) < 2:
            raise ValueError("OneHot requires a depth input")

        depth_name = self.inputs[1]
        for init in self.graph.initializer:
            if init.name == depth_name:
                depth_arr = numpy_helper.to_array(init)
                if depth_arr.size != 1:
                    raise ValueError(f"OneHot depth must be scalar: {depth_arr.shape}")
                return int(depth_arr.reshape(()))

        raise ValueError(f"OneHot depth initializer '{depth_name}' not found")
    
    def generate_vsm(self) -> List[str]:
        lines = []
        shape0 = self.in_shape()
        if shape0 == [256] and self.out_shape() == [256, 16]:
            self.check_layout_in("((4_L2B:2, 32:1, 2_W:1))")
            self.check_layout_out("((4_L2B:2, 64:2), (2:1, 4_PE:1, 2_W:1))")
            assert self.loc_prefix_in()  == "m" # LM0 に入力を仮定し、実装を軽減
            assert self.addr_in()        ==  0  # Addr 0 に入力を仮定し、実装を軽減
                                                # ↑、つまり、入力が "$lm0v" だと仮定している
            
            assert self.loc_prefix_out() == "n" # LM1 に出力を仮定し、実装を軽減
            assert self.addr_out()       ==  0  # Addr 0 に出力を仮定し、実装を軽減
                                                # ↑、つまり、出力が "$ln0v" だと仮定している
            
            # test unit_tests/train_step/OneHot_*

            lines.append(f'''
lpassa $mabid $t #入力がLM0のときのみ
imm/0101 ui"0x3F800008" $lr0v $ls0v
ipackbit $subpeid $aluf $nowrite; hvpassar -$aluf $omr1; l1bmd+0 $mt[0,0,16,16] $lbi
linc $aluf $nowrite; hvpassar $ls2 $nowrite; l1bmd+0 $mt[32,32,48,48] $lbi; l1bmd+0 $lbi $r8v
iadd/$imr1 $aluf $lr0v $t; fvpassa $mauf $nowrite; l1bmd+0 $lbi $s0v
ixor $aluf $lr[8,8,10,10] $omr1; fvpassa $mauf $nowrite; l1bmd+0 $mauf $lbi
ixor $t $ls[0,0,2,2] $omr2; fvpassa/$imr1 $mauf $ln[0,2,64,66] $lr0v; l1bmd+0 $lbi $nowrite
fvpassa/$imr2 $lbf $ln[128,130,192,194] $lr8v; l1bmm@1 $mauf $lbi
l1bmm@1 $mauf $lbi; l1bmm $lbi $ln[4,6,68,70]
l1bmm@2 $llr0v $llbi; l1bmm $lbi $ln[132,134,196,198]
l1bmm@3 $llr0v $llbi; l1bmm $llbi $lln[8,72,136,200]
l1bmm@4 $llr0v $llbi; l1bmm $llbi $lln[12,76,140,204]
l1bmm@5 $llr0v $llbi; l1bmm $llbi $lln[16,80,144,208]
l1bmm@6 $llr0v $llbi; l1bmm $llbi $lln[20,84,148,212]
l1bmm@7 $llr0v $llbi; l1bmm $llbi $lln[24,88,152,216]
l1bmm@8 $llr0v $llbi; l1bmm $llbi $lln[28,92,156,220]
l1bmm@9 $llr0v $llbi; l1bmm $llbi $lln[32,96,160,224]
l1bmm@10 $llr0v $llbi; l1bmm $llbi $lln[36,100,164,228]
l1bmm@11 $llr0v $llbi; l1bmm $llbi $lln[40,104,168,232]
l1bmm@12 $llr0v $llbi; l1bmm $llbi $lln[44,108,172,236]
l1bmm@13 $llr0v $llbi; l1bmm $llbi $lln[48,112,176,240]
l1bmm@14 $llr0v $llbi; l1bmm $llbi $lln[52,116,180,244]
l1bmm@15 $llr0v $llbi; l1bmm $llbi $lln[56,120,184,248]
l1bmm $llbi $lln[60,124,188,252]
            ''')

            return lines
        
        return lines

    
    def testcase_hint(self) -> Optional[str]:
        return "onehot.vsm"
    
    def get_memory_layout_tag(self) -> Dict[str, List[str]]:
        """メモリレイアウトタグを定義"""
        shape0 = self.in_shape(0)
        oshape = self.out_shape(0)
        if shape0 == [256] and oshape == [256, 16]:
            # OneHotは3入力: indices, depth, values
            # depthとvaluesは定数（initializer）なのでlayout不要
            return {
                "inputs": ["default"],  # 最初の入力（indices）のみlayoutが必要
                "outputs": ["PE"]
            }
        raise NotImplementedError(f"OneHot: shape={shape0} -> {oshape}")
        
    def generate_cpp(self) -> List[str]:
        """C++コード生成"""
        lines = []
        
        assert len(self.inputs) >= 1, f"OneHot node requires at least 1 input, got {len(self.inputs)}"
        
        indices_var = self.get_mapped_var(self.inputs[0])
        out_var = self.get_output_var_name()
        
        # 形状を取得
        indices_shape = self.in_shape(0)
        assert len(indices_shape) == 1, f"OneHot expects 1D indices, got {indices_shape}"
        
        batch_size = indices_shape[0]
        
        # depth（クラス数）を取得
        depth = self._get_depth()
        
        # OneHot変換（ループで実装）
        lines.append(f"    Matrix<{batch_size}, {depth}> {out_var} = zeros<{batch_size}, {depth}>();")
        lines.append(f"    for (int i = 0; i < {batch_size}; i++) {{")
        lines.append(f"        {out_var}[i][{indices_var}[i]] = 1.0f;")
        lines.append(f"    }}")
        
        self.variable_map[self.outputs[0]] = out_var
        return lines
    
    def generate_python(self) -> List[str]:
        """Pythonコード生成"""
        lines = []
        
        indices = self.inputs[0]
        out = self.outputs[0]
        out_var = self.get_output_var_name()
        
        # depthの値を取得
        depth_val = self._get_depth()
        
        lines.append(f"    {out_var} = F.one_hot({self.get_mapped_var(indices)}, num_classes={depth_val}).float()")
        self.variable_map[out] = out_var
        
        return lines
