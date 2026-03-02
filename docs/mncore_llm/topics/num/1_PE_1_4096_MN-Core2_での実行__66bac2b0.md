---
title: 1 PE (1/4096 MN-Core2) での実行
id: 66bac2b0505485001c39a20c
created_unix: 1723515569
updated_unix: 1724422405
views: 67
---

# 1 PE (1/4096 MN-Core2) での実行

from [[チュートリアル]]

[*** 1[[PE]] (1/4096 MN-Core2) での実行]
 この節での追加事項
  [[Debug set文]]/[[Debug get文]]
  [[Arithmetic and Logic Unit]] ([[ALU]])
  [[LM0]]/[[LM1]]
  [[GRF0]]/[[GRF1]]
  [[T register]]
  [[Mask register]]
  [[Forwarding-path]]

[** [[d set]]/[[d get]]]
 `d set/get`で扱う`<raw-payload>`は[[長語]]単位(64bit)で指定する。
  [[単語]](32bit)や[[半語]](16bit)の値を`d set`する場合、残りの32bitもしくは48bit分の要素を付け加える必要がある。
 `n0c0b0m0p0`に位置する[[LM0]]のアドレス0にdouble型の1.0(`0x3FF0000000000000`)を1つだけ書き込む:
 code:vsm
  d set $lm0n0c0b0m0p0 1 3FF0000000000000
  # $lm0: LM0 ($ln => LM1, $lr => GRF0, $ls => GRF1)
  #    ^: address
  # n0c0b0m0p0
  #  ^        : group-id [0,4)
  #    ^      : l2b-id [0,2)
  #      ^    : l1b-id [0,8)
  #        ^  : mab-id [0,16)
  #          ^: pe-id [0,4)
  d getd $lm0n0c0b0m0p0 1
  #    ^ d: double
 code:dmp
  DEBUG-LM0(n0c0b0m0p0,0):(1) (0x3ff0000000000000) #d getd $lm0n0c0b0m0p0 1

 `n0c0b0m0p0`に位置する[[LM0]]の[[アドレス]]0に[[float]]型の1.0(0x3F800000)を2つ書き込む:
 code:vsm
  d set $lm0n0c0b0m0p0 1 3F8000003F800000
  d getf $lm0n0c0b0m0p0 1
  #    ^ f: float
 code:dmp
  DEBUG-LM0(n0c0b0m0p0,0):(1, 1) (0x3f800000, 0x3f800000) #d getf $lm0n0c0b0m0p0 1

 `n0c0b0m0p0`に位置する[[LM0]]のアドレス0に[[half]]型の1.0(0x3e00)を4つ書き込む:
 code:vsm
  d set $lm0n0c0b0m0p0 1 3e003e003e003e00
  d geth $lm0n0c0b0m0p0 1
  #    ^ h: half
 code:dmp
  DEBUG-LM0(n0c0b0m0p0,0):(1, 1, 1, 1) (0x3e00, 0x3e00, 0x3e00, 0x3e00) #d geth $lm0n0c0b0m0p0 1

 `d set/get`で複数の[[ペイロード]]を指定する際、アドレス増分の最小単位が[[単語]]であるのに注意する。
  `$`の直後に来る`l`は長語単位でアクセスすることを指定しており、これを外すと単語指定となる。
  note: 長語指定の場合、アドレスは2の倍数に[[アラインメント]]されていなければならない。例えば`$lm1`は不適格であるため、エミュレータは[[未定義動作]]をする。
 code:_
  LM0上でのデータの並び:  3FF00000_00000000_3FF00000_00000000
               長語指定: |      $lm0       |      $lm2       |
               単語指定: |  $m0   |  $m1   |  $m2   |  $m3   |

 double型の1.0を2つ書き込む:
 code:vsm
  d set $lm0n0c0b0m0p0 2 3FF00000000000003FF0000000000000
  d getd $lm0n0c0b0m0p0 2
 code:dmp
  DEBUG-LM0(n0c0b0m0p0,0):(1) (0x3ff0000000000000) #d getd $lm0n0c0b0m0p0 2
  DEBUG-LM0(n0c0b0m0p0,2):(1) (0x3ff0000000000000) #d getd $lm0n0c0b0m0p0 2
                       ^: 次のアドレスが2になっている
 なったわ[[wogikaze.icon]]
  `$lm1`にsetすると0ずれ込む(未定義動作だから使わないだろうけど)

 整数を扱う場合は`d get`に[[精度指定]]は不要:
 code:vsm
  d set $lm0n0c0b0m0p0 1 0042004200000042
  d get $lm0n0c0b0m0p0 1
 code:dmp
  DEBUG-LM0(n0c0b0m0p0,0):(f:2.00268e-307, i:{{0x42,0x42},{0x0,0x42}}, v:0x42004200000042) #d get $lm0n0c0b0m0p0 1

 [[LM0]]以外のロケーションも`d set/get`の対象に出来る(`d set`については省略する)。
 code:vsm
  d get $ln0n0c0b0m0p0 1
  d get $lr0n0c0b0m0p0 1
  d get $ls0n0c0b0m0p0 1
  d get $ltn0c0b0m0p0 1
  d get $omr1n0c0b0m0p0 1
 code:dmp
        vvv: この部分でロケーションを表示
  DEBUG-LM1(n0c0b0m0p0,0):(f:0, i:{{0x0,0x0},{0x0,0x0}}, v:0x0) #d get $ln0n0c0b0m0p0 1
  DEBUG-GREG0(n0c0b0m0p0,0):(f:0, i:{{0x0,0x0},{0x0,0x0}}, v:0x0) #d get $lr0n0c0b0m0p0 1
  DEBUG-GREG1(n0c0b0m0p0,0):(f:0, i:{{0x0,0x0},{0x0,0x0}}, v:0x0) #d get $ls0n0c0b0m0p0 1
  DEBUG-TREG(n0c0b0m0p0,0):(f:0, i:{{0x0,0x0},{0x0,0x0}}, v:0x0) #d get $ltn0c0b0m0p0 1
        vvv: マスクレジスタは4cycle(=1step)分がまとめて出力される。
  DEBUG-OMR(n0c0b0m0p0,1):Mask{0} #d get $omr1n0c0b0m0p0 1
  DEBUG-OMR(n0c0b0m0p0,1):Mask{0} #d get $omr1n0c0b0m0p0 1
  DEBUG-OMR(n0c0b0m0p0,1):Mask{0} #d get $omr1n0c0b0m0p0 1
  DEBUG-OMR(n0c0b0m0p0,1):Mask{0} #d get $omr1n0c0b0m0p0 1
 [[メモリ]]の表を参考にして指定する[[wogikaze.icon]]

[[** 各オペランドの特徴]]

[[LM0]]/[[LM1]] (2048長語): それぞれvsmでは[[$lm]]/[[$ln]]で表す。
 生存期間の長い変数の格納場所として設計されており
 容量の大きさの引き換えに、一部の例外を除いてRead及びWriteは同一ステップに片方のみしか行えない。
 code:vsm
  d set $lm0n0c0b0m0p0 1 0000000000000042
  
  linc $lm0 $ln0
  
  d get $ln0n0c0b0m0p0 1
  
  # 書き込んだものが読み込めるまで2stepかかる。(optional: nopの数を減らすと...?)
  # これは実機での制約であり、エミュレータ内部の状態は即座に更新されるため、`d get`によって例外的に更新後の値を読める。
  # また、LMに限り書き込み後はアドレスによらず2stepは読み込めない。
  nop
  nop
  linc $ln0 $lm2
  
  d get $lm2n0c0b0m0p0 1
  
  nop/2
  # ladd $ln0 $lm2 $ln2 # <= error
  ladd $ln0 $lm2 $ln0   # <= valid (命令ビット衝突が起きない例外)
  
  d get $ln0n0c0b0m0p0 1
 [[linc]], [[nop]], [[ladd]]を参照[[wogikaze.icon]]
  nopを減らすと
  > A racy memory read is detected line 12. Consider inserting a nop here.
 code:dmp
  DEBUG-LM1(n0c0b0m0p0,0):(f:0, i:{{0x0,0x0},{0x0,0x43}}, v:0x43) #d get $ln0n0c0b0m0p0 1
  DEBUG-LM0(n0c0b0m0p0,2):(f:0, i:{{0x0,0x0},{0x0,0x44}}, v:0x44) #d get $lm2n0c0b0m0p0 1
  DEBUG-LM1(n0c0b0m0p0,0):(f:0, i:{{0x0,0x0},{0x0,0x87}}, v:0x87) #d get $ln0n0c0b0m0p0 1

[[GRF0]]/[[GRF1]] (256長語): それぞれvsmでは[[$lr]]/[[$ls]]で表す。
 こちらは生存期間の短い変数の格納場所として設計されており
 Read及びWriteは同一ステップに同時に行える。
 code:vsm
  d set $lr0n0c0b0m0p0 1 0000000000000002
  d set $ls0n0c0b0m0p0 1 0000000000000005
  
  linc $lr0 $lr0
  linc $ls0 $ls2
  
  d get $lr0n0c0b0m0p0 1
  d get $ls2n0c0b0m0p0 1
  
  nop
  # $ls2への書き込みから1stepしか経っていないが、別アドレスからの読み込みは可能。(LMでは不可)
  ladd $lr0 $ls0 $lr2
  
  d get $lr2n0c0b0m0p0 1
  
  nop/2
  ladd $lr2 $ls2 $lr4 $ls4
  
  d get $lr4n0c0b0m0p0 1
  d get $lr4n0c0b0m0p0 1
 code:dmp
  DEBUG-GREG0(n0c0b0m0p0,0):(f:0, i:{{0x0,0x0},{0x0,0x3}}, v:0x3) #d get $lr0n0c0b0m0p0 1
  DEBUG-GREG1(n0c0b0m0p0,2):(f:0, i:{{0x0,0x0},{0x0,0x6}}, v:0x6) #d get $ls2n0c0b0m0p0 1
  DEBUG-GREG0(n0c0b0m0p0,2):(f:0, i:{{0x0,0x0},{0x0,0x8}}, v:0x8) #d get $lr2n0c0b0m0p0 1
  DEBUG-GREG0(n0c0b0m0p0,4):(f:0, i:{{0x0,0x0},{0x0,0xE}}, v:0xE) #d get $lr4n0c0b0m0p0 1
  DEBUG-GREG0(n0c0b0m0p0,4):(f:0, i:{{0x0,0x0},{0x0,0xE}}, v:0xE) #d get $lr4n0c0b0m0p0 1

[[T]] (通常4長語、最大4*二長語): vsmでは[[$t]]([[$lt]],[[$llt]])で表す。
 アドレスの指定が出来ないことと容量以外は[[GRF]]と同様に扱える他
 [[Tレジスタ間接参照]]といった特殊な用途がある。
  語長の指定は出来ないが、これは[[オペコード]]の[[精度変換オプション]]の値から自動的に決定される。
 code:vsm
  d set $lm0n0c0b0m0p0 4 l0000000000000001l0000000000000002l0000000000000003l0000000000000004
  d set $lm8n0c0b0m0p0 4 l0000000000000005l0000000000000006l0000000000000007l0000000000000008
  
  lpassa $lm0v $lt
  
  d get $tn0c0b0m0p0 4
  
  lpassa $lm8v $t
  
  d get $ltn0c0b0m0p0 4
 [[lpassa]]を参照[[wogikaze.icon]]
 code:dmp
  DEBUG-TREG(n0c0b0m0p0,0):(f:0, i:{{0x0,0x0},{0x0,0x1}}, v:0x1) #d get $ltn0c0b0m0p0 4
  DEBUG-TREG(n0c0b0m0p0,1):(f:0, i:{{0x0,0x0},{0x0,0x2}}, v:0x2) #d get $ltn0c0b0m0p0 4
  DEBUG-TREG(n0c0b0m0p0,2):(f:0, i:{{0x0,0x0},{0x0,0x3}}, v:0x3) #d get $ltn0c0b0m0p0 4
  DEBUG-TREG(n0c0b0m0p0,3):(f:0, i:{{0x0,0x0},{0x0,0x4}}, v:0x4) #d get $ltn0c0b0m0p0 4
  DEBUG-TREG(n0c0b0m0p0,0):(f:0, i:{{0x0,0x0},{0x0,0x5}}, v:0x5) #d get $ltn0c0b0m0p0 4
  DEBUG-TREG(n0c0b0m0p0,1):(f:0, i:{{0x0,0x0},{0x0,0x6}}, v:0x6) #d get $ltn0c0b0m0p0 4
  DEBUG-TREG(n0c0b0m0p0,2):(f:0, i:{{0x0,0x0},{0x0,0x7}}, v:0x7) #d get $ltn0c0b0m0p0 4
  DEBUG-TREG(n0c0b0m0p0,3):(f:0, i:{{0x0,0x0},{0x0,0x8}}, v:0x8) #d get $ltn0c0b0m0p0 4

[[M]] (4bit): vsmでは[[$omr]]で表す。
 各[[サイクル]]において書き込む(1)か書き込まない(0)かの情報を保持する。
 code:vsm
  d set $lm0n0c0b0m0p0 4 l0000000000000000l0000000000000001l0000000000000042l0000000000000000
  d set $lm8n0c0b0m0p0 4 l3FF0000000000000l3FF0000000000000l3FF0000000000000l3FF0000000000000
  
  lpassa $lm0v $omr1
  maskn 1
  lpassa $lm8v $ln0v
  mask 0
  
  d get $lm0n0c0b0m0p0 4
  d get $omr1n0c0b0m0p0 1
  d getd $ln0n0c0b0m0p0 4
 [[maskn]]を参照[[wogikaze.icon]]
 code:_
  DEBUG-LM0(n0c0b0m0p0,0):(f:0, i:{{0x0,0x0},{0x0,0x0}}, v:0x0) #d get $lm0n0c0b0m0p0 4
  DEBUG-LM0(n0c0b0m0p0,2):(f:0, i:{{0x0,0x0},{0x0,0x1}}, v:0x1) #d get $lm0n0c0b0m0p0 4
  DEBUG-LM0(n0c0b0m0p0,4):(f:0, i:{{0x0,0x0},{0x0,0x42}}, v:0x42) #d get $lm0n0c0b0m0p0 4
  DEBUG-LM0(n0c0b0m0p0,6):(f:0, i:{{0x0,0x0},{0x0,0x0}}, v:0x0) #d get $lm0n0c0b0m0p0 4
                               vv: 実装の都合で15(=0b1111)が表示されている
  DEBUG-OMR(n0c0b0m0p0,1):Mask{15} #d get $omr1n0c0b0m0p0 1  1cycle目: 書き込む(1)
  DEBUG-OMR(n0c0b0m0p0,1):Mask{0} #d get $omr1n0c0b0m0p0 1   2cycle目: 書き込まない(0)
  DEBUG-OMR(n0c0b0m0p0,1):Mask{0} #d get $omr1n0c0b0m0p0 1   3cycle目: 書き込まない(0)
  DEBUG-OMR(n0c0b0m0p0,1):Mask{15} #d get $omr1n0c0b0m0p0 1  4cycle目: 書き込む(1)
  DEBUG-LM1(n0c0b0m0p0,0):(1) (0x3ff0000000000000) #d getd $ln0n0c0b0m0p0 4
  DEBUG-LM1(n0c0b0m0p0,2):(0) (0x0000000000000000) #d getd $ln0n0c0b0m0p0 4
  DEBUG-LM1(n0c0b0m0p0,4):(0) (0x0000000000000000) #d getd $ln0n0c0b0m0p0 4
  DEBUG-LM1(n0c0b0m0p0,6):(1) (0x3ff0000000000000) #d getd $ln0n0c0b0m0p0 4

[[MR]] (4x4(double),8x4(float),8x8(pseudo-float),16x16(half)の2面): [[$x]],[[$y]]に対応する。
 詳細は[[MAB]]の項で。

[[forwarding-path]]: vsmでは出力元[[ユニット]]に応じて[[$mauf]],[[$aluf]],[[$lbf]],[[$mreadf]]で表す。
 直前の[[演算ユニット]]等の出力をここから読み出すことが出来る。
 例外を除いて毎[[ステップ]]更新されるため、内容を使い回すことは出来ない。
  演算結果を使いまわしたい場合、単にそれをメモリに書き込めば良く
  その場合でも [[forwarding-path]] の内容は更新される。
 code:vsm
  d set $lr0n0c0b0m0p0 1 0000000000000042
  
  linc $lr0 $lm0
  linc $aluf $ln0
  
  d get $lm0n0c0b0m0p0 1
  d get $ln0n0c0b0m0p0 1
 code:dmp
  DEBUG-LM0(n0c0b0m0p0,0):(f:0, i:{{0x0,0x0},{0x0,0x43}}, v:0x43) #d get $lm0n0c0b0m0p0 1
  DEBUG-LM1(n0c0b0m0p0,0):(f:0, i:{{0x0,0x0},{0x0,0x44}}, v:0x44) #d get $ln0n0c0b0m0p0 1

[[固定値入力]]: vsmでは[[$l2bid]],[[$l1bid]],[[$mabid]],[[$peid]],[[$subpeid]],[[$msb1]]で表す。
 MN-Core2上の全[[PE]]は同一のアセンブリを受け取る([[SIMD]])ため、PE毎に異なる処理をしたい場合は、これらの[[オペランド]]を利用して[[マスク処理]]などをする。

[[Tレジスタ間接参照]]
 [[numpy.ndarray]]に対する[[indexing]]のように、実行時に定まる[[アドレス]]を元に[[間接参照]]したい場合がある。
  その際はTレジスタ間接参照の機能を使うと良い。
 code:vsm
  d set $lm0n0c0b0m0p0 4 l0000000000000000l3FF0000000000000l4000000000000000l4008000000000000
  # LM0上の4要素に対して[[2,1,3,0]]の順番でアクセスしたい場合、Tレジスタに以下のように書き込む。
  #                                     v: 2*2           v: 2*1           v: 2*3           v: 2*0
  d set $ltn0c0b0m0p0 4 l0000000000000004l0000000000000002l0000000000000006l0000000000000000
  
  lpassa $lmt $ln0v
  
  d getd $lm0n0c0b0m0p0 4
  d getd $ln0n0c0b0m0p0 4
 code:dmp
  DEBUG-LM0(n0c0b0m0p0,0):(0) (0x0000000000000000) #d getd $lm0n0c0b0m0p0 4
  DEBUG-LM0(n0c0b0m0p0,2):(1) (0x3ff0000000000000) #d getd $lm0n0c0b0m0p0 4
  DEBUG-LM0(n0c0b0m0p0,4):(2) (0x4000000000000000) #d getd $lm0n0c0b0m0p0 4
  DEBUG-LM0(n0c0b0m0p0,6):(3) (0x4008000000000000) #d getd $lm0n0c0b0m0p0 4
  DEBUG-LM1(n0c0b0m0p0,0):(2) (0x4000000000000000) #d getd $ln0n0c0b0m0p0 4
  DEBUG-LM1(n0c0b0m0p0,2):(1) (0x3ff0000000000000) #d getd $ln0n0c0b0m0p0 4
  DEBUG-LM1(n0c0b0m0p0,4):(3) (0x4008000000000000) #d getd $ln0n0c0b0m0p0 4
  DEBUG-LM1(n0c0b0m0p0,6):(0) (0x0000000000000000) #d getd $ln0n0c0b0m0p0 4
 [[3.6.1.12 t-Tレジスタ]]
 [[3.6.1.6 m-LM0(ベースアドレスレジスタ書き込みを除く)]]
