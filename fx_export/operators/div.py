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
            
            lines.append(f'''
imm f"2.0" $t
frsqrt $m256 $nowrite
fvmul $aluf $aluf $r0
fvfma -$m256 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvfma -$m256 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvmul $m0v $mauf $n0v
frsqrt $m257 $nowrite
fvmul $aluf $aluf $r0
fvfma -$m257 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvfma -$m257 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvmul $m4v $mauf $n4v
frsqrt $m258 $nowrite
fvmul $aluf $aluf $r0
fvfma -$m258 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvfma -$m258 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvmul $m8v $mauf $n8v
frsqrt $m259 $nowrite
fvmul $aluf $aluf $r0
fvfma -$m259 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvfma -$m259 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvmul $m12v $mauf $n12v
frsqrt $m260 $nowrite
fvmul $aluf $aluf $r0
fvfma -$m260 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvfma -$m260 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvmul $m16v $mauf $n16v
frsqrt $m261 $nowrite
fvmul $aluf $aluf $r0
fvfma -$m261 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvfma -$m261 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvmul $m20v $mauf $n20v
frsqrt $m262 $nowrite
fvmul $aluf $aluf $r0
fvfma -$m262 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvfma -$m262 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvmul $m24v $mauf $n24v
frsqrt $m263 $nowrite
fvmul $aluf $aluf $r0
fvfma -$m263 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvfma -$m263 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvmul $m28v $mauf $n28v
frsqrt $m264 $nowrite
fvmul $aluf $aluf $r0
fvfma -$m264 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvfma -$m264 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvmul $m32v $mauf $n32v
frsqrt $m265 $nowrite
fvmul $aluf $aluf $r0
fvfma -$m265 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvfma -$m265 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvmul $m36v $mauf $n36v
frsqrt $m266 $nowrite
fvmul $aluf $aluf $r0
fvfma -$m266 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvfma -$m266 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvmul $m40v $mauf $n40v
frsqrt $m267 $nowrite
fvmul $aluf $aluf $r0
fvfma -$m267 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvfma -$m267 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvmul $m44v $mauf $n44v
frsqrt $m268 $nowrite
fvmul $aluf $aluf $r0
fvfma -$m268 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvfma -$m268 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvmul $m48v $mauf $n48v
frsqrt $m269 $nowrite
fvmul $aluf $aluf $r0
fvfma -$m269 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvfma -$m269 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvmul $m52v $mauf $n52v
frsqrt $m270 $nowrite
fvmul $aluf $aluf $r0
fvfma -$m270 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvfma -$m270 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvmul $m56v $mauf $n56v
frsqrt $m271 $nowrite
fvmul $aluf $aluf $r0
fvfma -$m271 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvfma -$m271 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvmul $m60v $mauf $n60v
frsqrt $m272 $nowrite
fvmul $aluf $aluf $r0
fvfma -$m272 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvfma -$m272 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvmul $m64v $mauf $n64v
frsqrt $m273 $nowrite
fvmul $aluf $aluf $r0
fvfma -$m273 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvfma -$m273 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvmul $m68v $mauf $n68v
frsqrt $m274 $nowrite
fvmul $aluf $aluf $r0
fvfma -$m274 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvfma -$m274 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvmul $m72v $mauf $n72v
frsqrt $m275 $nowrite
fvmul $aluf $aluf $r0
fvfma -$m275 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvfma -$m275 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvmul $m76v $mauf $n76v
frsqrt $m276 $nowrite
fvmul $aluf $aluf $r0
fvfma -$m276 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvfma -$m276 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvmul $m80v $mauf $n80v
frsqrt $m277 $nowrite
fvmul $aluf $aluf $r0
fvfma -$m277 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvfma -$m277 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvmul $m84v $mauf $n84v
frsqrt $m278 $nowrite
fvmul $aluf $aluf $r0
fvfma -$m278 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvfma -$m278 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvmul $m88v $mauf $n88v
frsqrt $m279 $nowrite
fvmul $aluf $aluf $r0
fvfma -$m279 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvfma -$m279 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvmul $m92v $mauf $n92v
frsqrt $m280 $nowrite
fvmul $aluf $aluf $r0
fvfma -$m280 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvfma -$m280 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvmul $m96v $mauf $n96v
frsqrt $m281 $nowrite
fvmul $aluf $aluf $r0
fvfma -$m281 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvfma -$m281 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvmul $m100v $mauf $n100v
frsqrt $m282 $nowrite
fvmul $aluf $aluf $r0
fvfma -$m282 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvfma -$m282 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvmul $m104v $mauf $n104v
frsqrt $m283 $nowrite
fvmul $aluf $aluf $r0
fvfma -$m283 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvfma -$m283 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvmul $m108v $mauf $n108v
frsqrt $m284 $nowrite
fvmul $aluf $aluf $r0
fvfma -$m284 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvfma -$m284 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvmul $m112v $mauf $n112v
frsqrt $m285 $nowrite
fvmul $aluf $aluf $r0
fvfma -$m285 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvfma -$m285 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvmul $m116v $mauf $n116v
frsqrt $m286 $nowrite
fvmul $aluf $aluf $r0
fvfma -$m286 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvfma -$m286 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvmul $m120v $mauf $n120v
frsqrt $m287 $nowrite
fvmul $aluf $aluf $r0
fvfma -$m287 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvfma -$m287 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvmul $m124v $mauf $n124v
frsqrt $m288 $nowrite
fvmul $aluf $aluf $r0
fvfma -$m288 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvfma -$m288 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvmul $m128v $mauf $n128v
frsqrt $m289 $nowrite
fvmul $aluf $aluf $r0
fvfma -$m289 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvfma -$m289 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvmul $m132v $mauf $n132v
frsqrt $m290 $nowrite
fvmul $aluf $aluf $r0
fvfma -$m290 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvfma -$m290 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvmul $m136v $mauf $n136v
frsqrt $m291 $nowrite
fvmul $aluf $aluf $r0
fvfma -$m291 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvfma -$m291 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvmul $m140v $mauf $n140v
frsqrt $m292 $nowrite
fvmul $aluf $aluf $r0
fvfma -$m292 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvfma -$m292 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvmul $m144v $mauf $n144v
frsqrt $m293 $nowrite
fvmul $aluf $aluf $r0
fvfma -$m293 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvfma -$m293 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvmul $m148v $mauf $n148v
frsqrt $m294 $nowrite
fvmul $aluf $aluf $r0
fvfma -$m294 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvfma -$m294 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvmul $m152v $mauf $n152v
frsqrt $m295 $nowrite
fvmul $aluf $aluf $r0
fvfma -$m295 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvfma -$m295 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvmul $m156v $mauf $n156v
frsqrt $m296 $nowrite
fvmul $aluf $aluf $r0
fvfma -$m296 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvfma -$m296 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvmul $m160v $mauf $n160v
frsqrt $m297 $nowrite
fvmul $aluf $aluf $r0
fvfma -$m297 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvfma -$m297 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvmul $m164v $mauf $n164v
frsqrt $m298 $nowrite
fvmul $aluf $aluf $r0
fvfma -$m298 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvfma -$m298 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvmul $m168v $mauf $n168v
frsqrt $m299 $nowrite
fvmul $aluf $aluf $r0
fvfma -$m299 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvfma -$m299 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvmul $m172v $mauf $n172v
frsqrt $m300 $nowrite
fvmul $aluf $aluf $r0
fvfma -$m300 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvfma -$m300 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvmul $m176v $mauf $n176v
frsqrt $m301 $nowrite
fvmul $aluf $aluf $r0
fvfma -$m301 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvfma -$m301 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvmul $m180v $mauf $n180v
frsqrt $m302 $nowrite
fvmul $aluf $aluf $r0
fvfma -$m302 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvfma -$m302 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvmul $m184v $mauf $n184v
frsqrt $m303 $nowrite
fvmul $aluf $aluf $r0
fvfma -$m303 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvfma -$m303 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvmul $m188v $mauf $n188v
frsqrt $m304 $nowrite
fvmul $aluf $aluf $r0
fvfma -$m304 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvfma -$m304 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvmul $m192v $mauf $n192v
frsqrt $m305 $nowrite
fvmul $aluf $aluf $r0
fvfma -$m305 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvfma -$m305 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvmul $m196v $mauf $n196v
frsqrt $m306 $nowrite
fvmul $aluf $aluf $r0
fvfma -$m306 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvfma -$m306 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvmul $m200v $mauf $n200v
frsqrt $m307 $nowrite
fvmul $aluf $aluf $r0
fvfma -$m307 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvfma -$m307 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvmul $m204v $mauf $n204v
frsqrt $m308 $nowrite
fvmul $aluf $aluf $r0
fvfma -$m308 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvfma -$m308 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvmul $m208v $mauf $n208v
frsqrt $m309 $nowrite
fvmul $aluf $aluf $r0
fvfma -$m309 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvfma -$m309 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvmul $m212v $mauf $n212v
frsqrt $m310 $nowrite
fvmul $aluf $aluf $r0
fvfma -$m310 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvfma -$m310 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvmul $m216v $mauf $n216v
frsqrt $m311 $nowrite
fvmul $aluf $aluf $r0
fvfma -$m311 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvfma -$m311 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvmul $m220v $mauf $n220v
frsqrt $m312 $nowrite
fvmul $aluf $aluf $r0
fvfma -$m312 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvfma -$m312 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvmul $m224v $mauf $n224v
frsqrt $m313 $nowrite
fvmul $aluf $aluf $r0
fvfma -$m313 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvfma -$m313 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvmul $m228v $mauf $n228v
frsqrt $m314 $nowrite
fvmul $aluf $aluf $r0
fvfma -$m314 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvfma -$m314 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvmul $m232v $mauf $n232v
frsqrt $m315 $nowrite
fvmul $aluf $aluf $r0
fvfma -$m315 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvfma -$m315 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvmul $m236v $mauf $n236v
frsqrt $m316 $nowrite
fvmul $aluf $aluf $r0
fvfma -$m316 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvfma -$m316 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvmul $m240v $mauf $n240v
frsqrt $m317 $nowrite
fvmul $aluf $aluf $r0
fvfma -$m317 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvfma -$m317 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvmul $m244v $mauf $n244v
frsqrt $m318 $nowrite
fvmul $aluf $aluf $r0
fvfma -$m318 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvfma -$m318 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvmul $m248v $mauf $n248v
frsqrt $m319 $nowrite
fvmul $aluf $aluf $r0
fvfma -$m319 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvfma -$m319 $mauf $t $nowrite
nop
fvmul $r0 $mauf $r0
fvmul $m252v $mauf $n252v
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
