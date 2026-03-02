---
title: 3.6.12 ALU命令式
id: 66b35fff37748a001ca4db8e
created_unix: 1723031551
updated_unix: 1771370135
views: 118
---

# 3.6.12 ALU命令式

[[ALU]]は[[PE]]につきひとつ存在し、ほとんどの[[オペコード]]で[[サイクル]]あたり 1 長語を処理する。
 このとき、[[精度指定]]が[[単精度]]であれば長語内の 2 要素、[[半精度]]であれば長語内の 4 要素に対して並列に演算が行われる。
 よって、[[MAB]]あたりでは、半精度であればサイクルあたり 16 要素に並列に演算が行われることになる。
特に[[スループット]]が必要とされる一部のオペコードではサイクルあたり 2 長語を処理できる。

ALU命令式の一般化した文法は次の通りである。
```syntax
[u][(d|f|g|h|l|i|s)]<opecode> <src_x> [<src_y>] <dst_0> [<dst_1>..]
| zero<dst_0> [<dst_1>..]
| imm[u]  <dst_0> [<dst_1>..]
```
`<opecode>`は[[ゼロ出力命令]] [[zero]]および[[即値命令]] [[imm]]を除くオペコードである。
`<dst_0>` `[[<dst_1>..]]`は書き込み先[[PEオペランド]]である。
 これには[[マスクレジスタ書き込み]]([[3.6.1.13 omr-マスクレジスタへの書き込み]])を含めることができる。
ゼロ出力命令と即値命令は読み出し元PEオペランドを取らない。
 即値命令は代わりに[[即値ペイロード]]([[3.2.2 即値]])を[[入力オペランド]]とする。即値命令の`[[u]]`オプションについては[[3.6.12.3 imm-即値命令]]で述べる。

ゼロ出力命令や即値命令以外について述べる。
 これらは 1 入力または 2 入力である。`<src_x>`は第 1 入力、`<src_y>`は第 2 入力の読み出し元[[PEオペランド]]である。`<src_x>`と`<src_y>`は同一でも構わない。
 `<src_x>`に限り、[[3.6.1.20 固定値入力オペランド]]で述べた[[固定値入力オペランド]]が指定可能である。
 先頭の`[[u]]`は[[符号なし演算オプション]]指定、`[[(d|f|g|h|l|i|s)]]`は[[精度指定]]である。
  `d, f, g, h`が浮動小数点数の倍精度・単精度・疑似単精度・半精度、
  `l, i, s`が整数の倍・単・半精度である。
  `<opecode>`によって符号なし演算オプションを受け付けるかどうか、およびどの精度指定を受け付けるかが異なる。
  [[符号なし演算オプション]]を受け付けるオペコードについて、オプションを指定する場合を[[符号なしモード]]、指定しない場合を[[符号ありモード]]と呼ぶことにする。

オペコードの一覧を`表3.9`に示す。
「[[演算種別]]」カラムは可能な[[精度指定]]を示している。
 演算種別ごとに実際に指定可能な精度を`表3.10`に示す。
  例えば[[msl]]の演算種別は[[untyped]]なので精度指定は付けられず、
  [[inc]]の演算種別は[[int]]なので`l, i, s`のいずれかのみを付けられるということが分かる。
  入力のコピーを行う[[passa]]などの出力は精度指定に影響されないが、後述の生成される[[マスクフラグ]]は影響されることに注意する。
「[[2長語動作]]」カラムは 2 長語幅での動作をする場合があるかを示している。
 これがnoであれば、[[ALU]]が出力する 2 長語の[[LSB]]側 1 長語は、第 1 入力のLSB側 1 長語がそのまま入る。
  第 1 入力の丸め([[3.6.12.19 ALUへの入力の単精度から半精度への精度縮減]])が有効であれば、このLSB側 1 長語は 0 になる。
  `yes`の場合の動作はそれぞれの命令の項目で解説する。
「[[符号なしオプション]]」は[[uオプション]]を受け付けるかを示している。
 [[imm命令]]についてはuオプションの意味は[[符号なし]]とは異なるので`no`としてある。
 `yes`の場合の符号ありなしでの動作の違いはそれぞれの命令の項目で解説する。


表3.9 [[ALU命令オペコードの一覧]]。
 出力の列において第 1 入力オペランドの値をx、第 2 入力オペランドの値をyと表記する。
table:表3.9
 オペコード	演算種別	入力数2	長語動作	符号なしオプション	出力
 [[zero]]	untyped	0	yes	no	all 0
 [[imm]]	untyped	1	yes	no	immediate value ([[3.2.2 即値]])
 [[msl]]	untyped	1	no	no	x of previous PE
 [[msr]]	untyped	1	no	no	x of next PE
 [[passa]]	both	1	yes	no	x
 [[inc]]	int	1	no	yes	x+1
 [[dec]]	int	1	no	yes	x−1
 [[not]]	int	1	no	no	bitwise not x
 [[lnot]]	int	1	no	no	1 if x == 0,0 otherwise
 [[rsqrt]]	float	1	no	no	approx. of x^{−1/2}
 [[floor]]	float	1	no	no	floor(x)
 [[ftoi]]	float	1	no	yes	cast x to integer
 [[bfe]]	bfe	1	yes	no	extended half block float of x
 [[bfn]]	bfn	1	yes (half only)	no	block float of x
 [[max]]	both	2	no	yes (int only)	max(x, y)
 [[min]]	both	2	no	yes (int only)	min(x, y)
 [[packbit]]	both	2	no	no	(x << 1) | (MSB of y)
 [[and]]	int	2	no	no	bitwise x & y
 [[or]]	int	2	no	no	bitwise x | y
 [[xor]]	int	2	no	no	bitwise x xor y
 [[add]]	int	2	no	yes	x + y
 [[sub]]	int	2	no	yes	x − y
 [[lsl]]	int	2	no	no	x << y
 [[lsr]]	int	2	no	yes	x >> y
 [[bsl]]	int	2	no	no	circularly x <<  y
 [[bsr]]	int	2	no	no	circularly x >> y
 [[relu]]	float	2	no	no	y if (MSB of x) == 0, −0 otherwise
 [[relu0]]	float	2	no	no	same as relu
 [[relu1]]	float	2	no	no	y if (2nd MSB of x) == 0, −0 otherwise
 [[relu2]]	float	2	no	no	y if (3rd MSB of x) == 0, −0 otherwise
 [[relu3]]	float	2	no	no	y if (4th MSB of x) == 0, −0 otherwise
 [[lrelud]]	float	2	no	no	y if x ≥ 0 , y / 2 otherwise
 [[lreluo]]	float	2	no	no	y if x ≥ 0 ,y / 8 otherwise
 [[ilrelud]]	float	2	no	no	y if x ≥ 0, 2y otherwise



表3.10 表3.9に現れる、ALU命令オペコードの演算種別に対し、指定可能な精度の一覧。
 noneの場合は精度指定を付けてはいけない。
table:表3.10
 演算種別	指定可能な精度
 int 	l,i, s
 float 	d, f, h
 both 	d, f, h, l, i, s
 bfn 	d, f, g, h
 bfe 	h
 untyped 	none

また、[[ALU命令式]]が生成する[[マスクフラグ]]([[3.6.2 マスクレジスタ]])を表3.11に示す。
 「[[符号なし]]」カラムは[[符号なしオプション]]による場合分けを示す。
  `“-”`であれば符号なしオプションが存在しないオペコードであることを示す。
  `“false”`であれば符号ありモードの場合であること、
  `“true”`であれば符号なしモードの場合であることを示す。
  `“both”`であれば、符号なしオプションは存在するが、マスクフラグの生成方法には影響しないことを示す。
 「[[フラグが1になる条件]]」カラムは、出力長語中の各語について、それが満たされるときマスクフラグは 1になり、そうでなければ 0 になることを示す。
  マスクフラグは必ずサイクルあたり 4 ビット出力され、精度指定が長語なら 1 語の結果が 4 ビットに、単語なら 2 語の結果がそれぞれ 2 ビットずつに複製されることに注意する。
 [[passa命令]]、浮動小数点数モードの[[max/min命令]]は若干条件が複雑なため、それぞれ[[3.6.12.5 passa-コピー命令]]と[[3.6.12.13 max,min-最大値・最小値命令]]で詳細を述べる。

表3.11 [[オペコードと符号なし指定有無ごとの、ALU命令式が生成するマスクフラグ]]
table:表3.11
 オペコード	符号なし	フラグが 1 になる条件
 [[zero]]/[[imm]]/[[msl]]/[[msr]]/[[floor]]/[[ftoi]]/[[bfe]]/[[bfn]]	-	never
 [[passa]]	-	output is all 0 (ignore LSB long-word)
 [[inc]]/[[dec]]/[[add]]/[[sub]]	false	output is non-negative
 [[inc]]/[[dec]]/[[add]]/[[sub]]	true	overflow does not occur
 [[not]]/[[lnot]]/[[and]]/[[or]]/[[xor]]	-	output is all 0
 [[rsqrt]]/[[relu]]/[[relu0]]/[[lrelud]]/[[lreluo]]/[[ilrelud]]	-	MSB ofxis 0
 [[max]]/[[min]] (int)	both	xis selected orx==y
 [[max]]/[[min]] (float)	-	xis selected orx==y
 [[packbit]]	-	MSB ofyis 0
 [[lsl]]/[[bsl]]/[[bsr]]	-	output is all 0
 [[lsr]]	both	output is all 0
 [[relu1]]/[[relu2]]/relu3	-	2nd/3rd/4th MSB ofxis 0 resp.




以降では各オペランドの詳細を述べる。
[[3.6.12.1 ALU命令式の生成するマスクフラグ]]
[[3.6.12.2 zero-ゼロ出力命令]]

[[3.6.12.3 imm-即値命令]]

[[3.6.12.4 msl,msr-PE間循環シフト命令]]

[[3.6.12.5 passa-コピー命令]]

[[3.6.12.6 inc,dec-インクリメント・デクリメント命令]]

[[3.6.12.7 not-ビット反転命令]]

[[3.6.12.8 lnot-論理否定命令]]

[[3.6.12.9 rsqrt-近似逆数平方根命令]]

[[3.6.12.10 floor-floor命令]]

[[3.6.12.11 ftoi-整数への変換]]

[[3.6.12.12 bfe,bfn-ブロックフロート化命令]]

[[3.6.12.13 max,min-最大値・最小値命令]]

[[3.6.12.14 packbit-符号部パック命令]]

[[3.6.12.15 and,or,xor-ビット論理積・論理和・排他的論理和命令]]

[[3.6.12.16 add,sub-加算・減算命令]]

[[3.6.12.17 lsl,lsr,bsl,bsr-シフト命令]]

[[3.6.12.18 ReLU系命令]]

[[3.6.12.19 ALUへの入力の単精度から半精度への精度縮減]]
