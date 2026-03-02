---
title: 3.6.12.1 ALU命令式の生成するマスクフラグ
id: 6994ed97553a7721f749ac18
created_unix: 1771367921
updated_unix: 1771368296
views: 0
---

# 3.6.12.1 ALU命令式の生成するマスクフラグ

[[ALU命令式]]が生成する[[マスクフラグ]]([[3.6.2 マスクレジスタ]])を表3.11 に示す。
 「符号なし」カラムは[[符号なしオプション]]による場合分けを示す。
  “-”であれば符号なしオプションが存在しないオペコードであることを示す。
  “false”であれば[[符号ありモード]]の場合であること、
  “true”であれば[[符号なしモード]]の場合であることを示す。
  “both”であれば、符号なしオプションは存在するが、マスクフラグの生成方法には影響しないことを示す。
 「フラグが1になる条件」カラムは、出力長語中の各語について、それが満たされるときマスクフラグは1になり、そうでなければ0になることを示す。
 マスクフラグは必ずサイクルあたり4ビット出力され、精度指定が長語なら1語の結果が4ビットに、単語なら2語の結果がそれぞれ2ビットずつに複製されることに注意する。
 [[passa命令]]、[[浮動小数点数モード]]の[[max/min命令]]は若干条件が複雑なため、それぞれ[[3.6.12.5 passa-コピー命令]]と[[3.6.12.13 max,min-最大値・最小値命令]]で詳細を述べる。
 マスクレジスタは各エントリごとに16ビットのサイズを持ち、これは[[即値命令]]が生成可能なビット数に収まるが、即値命令を用いて任意の値を直接書き込むことはできないことに注意する。

table:表3.11 オペコードと符号なし指定有無ごとの、ALU命令式が生成するマスクフラグ
 オペコード	符号なし	フラグが1になる条件
 zero/imm/msl/msr/floor/ftoi/bfe/bfn	-	never
 passa	-	output is all 0 (ignore LSB long-word)
 inc/dec/add/sub	false	output is non-negative
 inc/dec/add/sub	true	overflow does not occur
 not/lnot/and/or/xor	-	output is all 0
 rsqrt/relu/relu0/lrelud/lreluo/ilrelud	-	MSB of x is 0
 max/min (int)	both	x is selected or x = y
 max/min (float)	-	x is selected or x = y
 packbit	-	MSB of y is 0
 lsl/bs1/bsr	-	output is all 0
 1sr	both	output is all 0
 relu1/relu2/relu3	-	2nd/3rd/4th MSB of x is 0 resp
