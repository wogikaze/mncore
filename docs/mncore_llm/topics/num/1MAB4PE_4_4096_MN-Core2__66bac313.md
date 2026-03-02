---
title: 1MAB=4PE (4/4096 MN-Core2)
id: 66bac313e6b4a6001c0e2f78
created_unix: 1723515669
updated_unix: 1725026126
views: 81
---

# 1MAB=4PE (4/4096 MN-Core2)

from [[チュートリアル]]

[*** 1[[MAB]]=4[[PE]] (4/4096 MN-Core2)]
 この節での追加事項
  [[Matrix Arithmetic Unit]] ([[MAU]])
  [[Matrix register]]

[[** ベクトル演算]]
 [[Matrix Arithmetic Unit]] ([[MAU]]) という名前だが、MN-Core2における[[ベクトル演算]]はMAUが行う。
  多くのケースで[[PE]]毎に閉じた計算を行うが、[[倍精度]]の積は4つのPEを意識した操作が入る。

[* [[dv]]([[mul]]|[[fma]])]
 code:vsm
  d set $lm0n0c0b0m0p0 1 3FF0000000000000
  d set $lm0n0c0b0m0p1 1 4000000000000000
  d set $lm0n0c0b0m0p2 1 4008000000000000
  d set $lm0n0c0b0m0p3 1 4010000000000000
  d set $ln0n0c0b0m0p0 1 3FF0000000000000
  d set $ln0n0c0b0m0p1 1 4008000000000000
  d set $ln0n0c0b0m0p2 1 4014000000000000
  d set $ln0n0c0b0m0p3 1 401C000000000000
  
  # p[[0:3]]は省略可能。その場合自動的に展開される。
  d getd $lm0n0c0b0m0 1
  d getd $ln0n0c0b0m0 1
  
  dvmulu $lm0 $ln0 $nowrite
  dvfmad $lm0 $ln0 $mauf $ls2
  
  # 上の2行を冗長に書くと以下のようになる。(optional: 下を実行してdump結果を見てみる)
  
  # dvmulu $lm0 $ln0 $lr0
  # dvmuld $lm0 $ln0 $ls0
  # d getd $lr0n0c0b0m0 1
  # d getd $ls0n0c0b0m0 1
  # nop/2
  # dvadd $lr0 $ls0 $ls2
  
  d getd $ls2n0c0b0m0 1
 [[$nowrite]], [[$mauf]]
 [[dvmulu]], [[dvfmad]], [[dvmuld]], [[dvadd]]
  倍精度で全て計算
  `/u$/`なコマンドはPE0,1のみ
  `/d$/`なコマンドはPE2,3のみ
 code:dmp
  DEBUG-LM0(n0c0b0m0p0,0):(1) (0x3ff0000000000000) #d getd $lm0n0c0b0m0 1
  DEBUG-LM0(n0c0b0m0p1,0):(2) (0x4000000000000000) #d getd $lm0n0c0b0m0 1
  DEBUG-LM0(n0c0b0m0p2,0):(3) (0x4008000000000000) #d getd $lm0n0c0b0m0 1
  DEBUG-LM0(n0c0b0m0p3,0):(4) (0x4010000000000000) #d getd $lm0n0c0b0m0 1
  DEBUG-LM1(n0c0b0m0p0,0):(1) (0x3ff0000000000000) #d getd $ln0n0c0b0m0 1
  DEBUG-LM1(n0c0b0m0p1,0):(3) (0x4008000000000000) #d getd $ln0n0c0b0m0 1
  DEBUG-LM1(n0c0b0m0p2,0):(5) (0x4014000000000000) #d getd $ln0n0c0b0m0 1
  DEBUG-LM1(n0c0b0m0p3,0):(7) (0x401c000000000000) #d getd $ln0n0c0b0m0 1
  DEBUG-GREG1(n0c0b0m0p0,2):(1) (0x3ff0000000000000) #d getd $ls2n0c0b0m0 1
  DEBUG-GREG1(n0c0b0m0p1,2):(6) (0x4018000000000000) #d getd $ls2n0c0b0m0 1
  DEBUG-GREG1(n0c0b0m0p2,2):(15) (0x402e000000000000) #d getd $ls2n0c0b0m0 1
  DEBUG-GREG1(n0c0b0m0p3,2):(28) (0x403c000000000000) #d getd $ls2n0c0b0m0 1

[* [[fv]]([[mul]]|[[fma]])]
 code:vsm
  d set $lm0n0c0b0m0p0 1 3F80000040A00000 # 1,5
  d set $lm0n0c0b0m0p1 1 4000000040C00000 # 2,6
  d set $lm0n0c0b0m0p2 1 4040000040E00000 # 3,7
  d set $lm0n0c0b0m0p3 1 4080000041000000 # 4,8
  
  d set $ln0n0c0b0m0p0 1 3F80000041100000 # 1,9
  d set $ln0n0c0b0m0p1 1 4040000041300000 # 3,11
  d set $ln0n0c0b0m0p2 1 40A0000041500000 # 5,13
  d set $ln0n0c0b0m0p3 1 40E0000041700000 # 7,15
  
  d set $lr0n0c0b0m0p0 1 3F8000003F800000 # 1,1
  d set $lr0n0c0b0m0p1 1 3F8000003F800000 # 1,1
  d set $lr0n0c0b0m0p2 1 3F8000003F800000 # 1,1
  d set $lr0n0c0b0m0p3 1 3F8000003F800000 # 1,1
  
  d getf $lm0n0c0b0m0 1
  d getf $ln0n0c0b0m0 1
  
  fvmul $lm0 $ln0 $ls0
  
  d getf $ls0n0c0b0m0 1
  
  fvfma $lm0 $ln0 $lr0 $ls0
  
  d getf $ls0n0c0b0m0 1
 [[fvmul]], [[fvfma]]
 code:dmp
  DEBUG-LM0(n0c0b0m0p0,0):(1, 5) (0x3f800000, 0x40a00000) #d getf $lm0n0c0b0m0 1
  DEBUG-LM0(n0c0b0m0p1,0):(2, 6) (0x40000000, 0x40c00000) #d getf $lm0n0c0b0m0 1
  DEBUG-LM0(n0c0b0m0p2,0):(3, 7) (0x40400000, 0x40e00000) #d getf $lm0n0c0b0m0 1
  DEBUG-LM0(n0c0b0m0p3,0):(4, 8) (0x40800000, 0x41000000) #d getf $lm0n0c0b0m0 1
  DEBUG-LM1(n0c0b0m0p0,0):(1, 9) (0x3f800000, 0x41100000) #d getf $ln0n0c0b0m0 1
  DEBUG-LM1(n0c0b0m0p1,0):(3, 11) (0x40400000, 0x41300000) #d getf $ln0n0c0b0m0 1
  DEBUG-LM1(n0c0b0m0p2,0):(5, 13) (0x40a00000, 0x41500000) #d getf $ln0n0c0b0m0 1
  DEBUG-LM1(n0c0b0m0p3,0):(7, 15) (0x40e00000, 0x41700000) #d getf $ln0n0c0b0m0 1
  DEBUG-GREG1(n0c0b0m0p0,0):(1, 45) (0x3f800000, 0x42340000) #d getf $ls0n0c0b0m0 1
  DEBUG-GREG1(n0c0b0m0p1,0):(6, 66) (0x40c00000, 0x42840000) #d getf $ls0n0c0b0m0 1
  DEBUG-GREG1(n0c0b0m0p2,0):(15, 91) (0x41700000, 0x42b60000) #d getf $ls0n0c0b0m0 1
  DEBUG-GREG1(n0c0b0m0p3,0):(28, 120) (0x41e00000, 0x42f00000) #d getf $ls0n0c0b0m0 1
  DEBUG-GREG1(n0c0b0m0p0,0):(2, 46) (0x40000000, 0x42380000) #d getf $ls0n0c0b0m0 1
  DEBUG-GREG1(n0c0b0m0p1,0):(7, 67) (0x40e00000, 0x42860000) #d getf $ls0n0c0b0m0 1
  DEBUG-GREG1(n0c0b0m0p2,0):(16, 92) (0x41800000, 0x42b80000) #d getf $ls0n0c0b0m0 1
  DEBUG-GREG1(n0c0b0m0p3,0):(29, 121) (0x41e80000, 0x42f20000) #d getf $ls0n0c0b0m0 1

[* [[hv]]([[mul]]|[[fma]])]
 code:vsm
  d set $lm0n0c0b0m0p0 1 3E00428044404540
  d set $lm0n0c0b0m0p1 1 4000430044804580
  d set $lm0n0c0b0m0p2 1 4100438044C045C0
  d set $lm0n0c0b0m0p3 1 4200440045004600
  d set $ln0n0c0b0m0p0 1 3E00444046204720
  d set $ln0n0c0b0m0p1 1 410044C046604760
  d set $ln0n0c0b0m0p2 1 4280454046A047A0
  d set $ln0n0c0b0m0p3 1 438045C046E047E0
  d set $lr0n0c0b0m0p0 1 3E003E003E003E00
  d set $lr0n0c0b0m0p1 1 3E003E003E003E00
  d set $lr0n0c0b0m0p2 1 3E003E003E003E00
  d set $lr0n0c0b0m0p3 1 3E003E003E003E00
  
  # (optional: 上を参考にexpectedと一致するようなvsmをここに足してみる)
 [[hvmul]]
 [[hvfma]]
 想定出力:
 code:dmp
  DEBUG-GREG1(n0c0b0m0p0,0):(1, 45, 153, 325) (0x3e00, 0x48d0, 0x4c64, 0x4e8a) #d geth $ls0n0c0b0m0 1
  DEBUG-GREG1(n0c0b0m0p1,0):(6, 66, 190, 378) (0x4300, 0x4a10, 0x4cf8, 0x4ef4) #d geth $ls0n0c0b0m0 1
  DEBUG-GREG1(n0c0b0m0p2,0):(15, 91, 231, 435) (0x45c0, 0x4ad8, 0x4d9c, 0x4f66) #d geth $ls0n0c0b0m0 1
  DEBUG-GREG1(n0c0b0m0p3,0):(28, 120, 276, 496) (0x4780, 0x4bc0, 0x4e28, 0x4fe0) #d geth $ls0n0c0b0m0 1
  DEBUG-GREG1(n0c0b0m0p0,0):(2, 46, 154, 326) (0x4000, 0x48e0, 0x4c68, 0x4e8c) #d geth $ls0n0c0b0m0 1
  DEBUG-GREG1(n0c0b0m0p1,0):(7, 67, 191, 379) (0x4380, 0x4a18, 0x4cfc, 0x4ef6) #d geth $ls0n0c0b0m0 1
  DEBUG-GREG1(n0c0b0m0p2,0):(16, 92, 232, 436) (0x4600, 0x4ae0, 0x4da0, 0x4f68) #d geth $ls0n0c0b0m0 1
  DEBUG-GREG1(n0c0b0m0p3,0):(29, 121, 277, 497) (0x47a0, 0x4bc8, 0x4e2a, 0x4fe2) #d geth $ls0n0c0b0m0 1
 想定ではない出力(hint: 基本的に半精度の加算は[[精度拡張]]してから行う):
  [[3.6.9.23 入力の精度拡張]]
  [[3.6.8.4 入力の精度拡張]]
 code:dmp
  DEBUG-GREG1(n0c0b0m0p0,0):(1.75, 0, 4.40625, 0) (0x3f80, 0x0000, 0x4234, 0x0000) #d geth $ls0n0c0b0m0 1
  DEBUG-GREG1(n0c0b0m0p1,0):(2.75, 0, 5.03125, 0) (0x40c0, 0x0000, 0x4284, 0x0000) #d geth $ls0n0c0b0m0 1
  DEBUG-GREG1(n0c0b0m0p2,0):(3.4375, 0, 5.42188, 0) (0x4170, 0x0000, 0x42b6, 0x0000) #d geth $ls0n0c0b0m0 1
  DEBUG-GREG1(n0c0b0m0p3,0):(3.875, 0, 5.875, 0) (0x41e0, 0x0000, 0x42f0, 0x0000) #d geth $ls0n0c0b0m0 1
  DEBUG-GREG1(n0c0b0m0p0,0):(1.78125, 6.98492e-09, 4.40625, -0) (0x3f90, 0x07c0, 0x4234, 0x803e) #d geth $ls0n0c0b0m0 1
  DEBUG-GREG1(n0c0b0m0p1,0):(2.76562, 0, 5.03125, 2.12109) (0x40c4, 0x01f0, 0x4284, 0x401f) #d geth $ls0n0c0b0m0 1
  DEBUG-GREG1(n0c0b0m0p2,0):(3.44531, 0, 5.42188, 2.12109) (0x4172, 0x00f8, 0x42b6, 0x401f) #d geth $ls0n0c0b0m0 1
  DEBUG-GREG1(n0c0b0m0p3,0):(3.87891, 0, 5.875, 2.12109) (0x41e1, 0x007c, 0x42f0, 0x401f) #d geth $ls0n0c0b0m0 1
 `(d|f|h)`[[vpassa]]は一見[[IALU]]の[[passa]]と同じ動作をするように見えるが
  その過程で[[正規化]]を挟むため、整数や特殊な負数に対してvpassaをしてはいけない:
 code:vsm
  d set $lm0n0c0b0m0p0 1 0000004280000000
  
  fvpassa $lm0 $ln0
  
  d getf $lm0n0c0b0m0p0 1
  d get $lm0n0c0b0m0p0 1
  d getf $ln0n0c0b0m0p0 1
  d get $ln0n0c0b0m0p0 1
 code:dmp
  DEBUG-LM0(n0c0b0m0p0,0):(0, -0) (0x00000042, 0x80000000) #d getf $lm0n0c0b0m0p0 1
  DEBUG-LM0(n0c0b0m0p0,0):(f:0, i:{{0x0,0x42},{0x8000,0x0}}, v:0x4280000000) #d get $lm0n0c0b0m0p0 1
  # 以下の出力では42や-0が潰れてしまっていることがわかる
  DEBUG-LM1(n0c0b0m0p0,0):(0, 0) (0x00000000, 0x00000000) #d getf $ln0n0c0b0m0p0 1
  DEBUG-LM1(n0c0b0m0p0,0):(f:0, i:{{0x0,0x0},{0x0,0x0}}, v:0x0) #d get $ln0n0c0b0m0p0 1
[[vpassa]]の有効な使い方に[[精度変換]]がある:
 code:vsm
  d set $lm0n0c0b0m0p0 4 l3FF0000000000000l4000000000000000l4008000000000000l4010000000000000
  
  dvpassar $lm0v $n0v
  
  d getd $lm0n0c0b0m0p0 4
  d getf $ln0n0c0b0m0p0 2
  
  d set $lm0n0c0b0m0p0 1 3E00428044404540
  
  hvpassa $lm0 $lln0
  
  d geth $lm0n0c0b0m0p0 1
  d getf $ln0n0c0b0m0p0 2
 code:dmp
  DEBUG-LM0(n0c0b0m0p0,0):(1) (0x3ff0000000000000) #d getd $lm0n0c0b0m0p0 4
  DEBUG-LM0(n0c0b0m0p0,2):(2) (0x4000000000000000) #d getd $lm0n0c0b0m0p0 4
  DEBUG-LM0(n0c0b0m0p0,4):(3) (0x4008000000000000) #d getd $lm0n0c0b0m0p0 4
  DEBUG-LM0(n0c0b0m0p0,6):(4) (0x4010000000000000) #d getd $lm0n0c0b0m0p0 4
  DEBUG-LM1(n0c0b0m0p0,0):(1, 2) (0x3f800000, 0x40000000) #d getf $ln0n0c0b0m0p0 2
  DEBUG-LM1(n0c0b0m0p0,2):(3, 4) (0x40400000, 0x40800000) #d getf $ln0n0c0b0m0p0 2
  DEBUG-LM0(n0c0b0m0p0,0):(1, 5, 9, 13) (0x3e00, 0x4280, 0x4440, 0x4540) #d geth $lm0n0c0b0m0p0 1
  DEBUG-LM1(n0c0b0m0p0,0):(1, 5) (0x3f800000, 0x40a00000) #d getf $ln0n0c0b0m0p0 2
  DEBUG-LM1(n0c0b0m0p0,2):(9, 13) (0x41100000, 0x41500000) #d getf $ln0n0c0b0m0p0 2
 マジで解けない...[[wogikaze.icon]]
  [[チュートリアル：hvmulの解]]

[** [[行列演算]]]
 行列演算は大まかに各行列の[[ブロックフロート化]]と[[行列レジスタ]]への書き込み、m([[mul]]|[[fma]])命令の呼び出しの手順が必要になる。
  ここでは[[倍精度]]における[[行列積]]を取り上げて説明する。


[[* 4x4 matmul in double (AxB) を考える]]
 code:vsm
  # A
  d set $lm0n0c0b0m0p0 4 80000000000000000000000000000000BFF0000000000000BFF0000000000000
  d set $lm0n0c0b0m0p1 4 000000000000000040100000000000003FF0000000000000BFF0000000000000
  d set $lm0n0c0b0m0p2 4 4000000000000000BFF0000000000000BFF00000000000003FF0000000000000
  d set $lm0n0c0b0m0p3 4 BFF0000000000000C010000000000000BFF0000000000000BFF0000000000000
  
  # B
  d set $ln0n0c0b0m0p0 4 80000000000000003FF00000000000003FF0000000000000BFF0000000000000
  d set $ln0n0c0b0m0p1 4 3FF0000000000000BFF00000000000003FF00000000000003FF0000000000000
  d set $ln0n0c0b0m0p2 4 BFF000000000000040080000000000003FF00000000000003FF0000000000000
  d set $ln0n0c0b0m0p3 4 C0100000000000003FF0000000000000C008000000000000BFF0000000000000
  
  d getd $lm0n0c0b0m0 4
  d getd $ln0n0c0b0m0 4
  
  # ブロックフロート化とは内積回路への2入力それぞれに対して指数部の値を揃えることである。倍精度の場合はdbfn命令を使ってこれを行う。
  dbfn $lm0v $lr0v # BF-ed A
  dbfn $ln0v $ls0v # BF-ed B
  
  # 次にBF-ed Aを行列レジスタへ書き込む
  dmwrite $lr0v $lx0
  
  # dmmulu+dmfmadを発行する
  dmmulu $lx $ls0v $nowrite
  dmfmad $lx $ls0v $mauf $lm8v
  
  d getd $lm8n0c0b0m0 4
 [[dbfn]]: [[3.6.12.12 bfe,bfn-ブロックフロート化命令]]
 [[dmwrite]]: [[3.6.10.1 dmwrite-倍精度行列レジスタ書き込み]]
 [[dmmulu]], [[dmfmad]]
 code:dmp
  DEBUG-LM0(n0c0b0m0p0,0):(-0) (0x8000000000000000) #d getd $lm0n0c0b0m0 4
  DEBUG-LM0(n0c0b0m0p0,2):(0) (0x0000000000000000) #d getd $lm0n0c0b0m0 4
  DEBUG-LM0(n0c0b0m0p0,4):(-1) (0xbff0000000000000) #d getd $lm0n0c0b0m0 4
  DEBUG-LM0(n0c0b0m0p0,6):(-1) (0xbff0000000000000) #d getd $lm0n0c0b0m0 4
  DEBUG-LM0(n0c0b0m0p1,0):(0) (0x0000000000000000) #d getd $lm0n0c0b0m0 4
  DEBUG-LM0(n0c0b0m0p1,2):(4) (0x4010000000000000) #d getd $lm0n0c0b0m0 4
  DEBUG-LM0(n0c0b0m0p1,4):(1) (0x3ff0000000000000) #d getd $lm0n0c0b0m0 4
  DEBUG-LM0(n0c0b0m0p1,6):(-1) (0xbff0000000000000) #d getd $lm0n0c0b0m0 4
  DEBUG-LM0(n0c0b0m0p2,0):(2) (0x4000000000000000) #d getd $lm0n0c0b0m0 4
  DEBUG-LM0(n0c0b0m0p2,2):(-1) (0xbff0000000000000) #d getd $lm0n0c0b0m0 4
  DEBUG-LM0(n0c0b0m0p2,4):(-1) (0xbff0000000000000) #d getd $lm0n0c0b0m0 4
  DEBUG-LM0(n0c0b0m0p2,6):(1) (0x3ff0000000000000) #d getd $lm0n0c0b0m0 4
  DEBUG-LM0(n0c0b0m0p3,0):(-1) (0xbff0000000000000) #d getd $lm0n0c0b0m0 4
  DEBUG-LM0(n0c0b0m0p3,2):(-4) (0xc010000000000000) #d getd $lm0n0c0b0m0 4
  DEBUG-LM0(n0c0b0m0p3,4):(-1) (0xbff0000000000000) #d getd $lm0n0c0b0m0 4
  DEBUG-LM0(n0c0b0m0p3,6):(-1) (0xbff0000000000000) #d getd $lm0n0c0b0m0 4
  DEBUG-LM1(n0c0b0m0p0,0):(-0) (0x8000000000000000) #d getd $ln0n0c0b0m0 4
  DEBUG-LM1(n0c0b0m0p0,2):(1) (0x3ff0000000000000) #d getd $ln0n0c0b0m0 4
  DEBUG-LM1(n0c0b0m0p0,4):(1) (0x3ff0000000000000) #d getd $ln0n0c0b0m0 4
  DEBUG-LM1(n0c0b0m0p0,6):(-1) (0xbff0000000000000) #d getd $ln0n0c0b0m0 4
  DEBUG-LM1(n0c0b0m0p1,0):(1) (0x3ff0000000000000) #d getd $ln0n0c0b0m0 4
  DEBUG-LM1(n0c0b0m0p1,2):(-1) (0xbff0000000000000) #d getd $ln0n0c0b0m0 4
  DEBUG-LM1(n0c0b0m0p1,4):(1) (0x3ff0000000000000) #d getd $ln0n0c0b0m0 4
  DEBUG-LM1(n0c0b0m0p1,6):(1) (0x3ff0000000000000) #d getd $ln0n0c0b0m0 4
  DEBUG-LM1(n0c0b0m0p2,0):(-1) (0xbff0000000000000) #d getd $ln0n0c0b0m0 4
  DEBUG-LM1(n0c0b0m0p2,2):(3) (0x4008000000000000) #d getd $ln0n0c0b0m0 4
  DEBUG-LM1(n0c0b0m0p2,4):(1) (0x3ff0000000000000) #d getd $ln0n0c0b0m0 4
  DEBUG-LM1(n0c0b0m0p2,6):(1) (0x3ff0000000000000) #d getd $ln0n0c0b0m0 4
  DEBUG-LM1(n0c0b0m0p3,0):(-4) (0xc010000000000000) #d getd $ln0n0c0b0m0 4
  DEBUG-LM1(n0c0b0m0p3,2):(1) (0x3ff0000000000000) #d getd $ln0n0c0b0m0 4
  DEBUG-LM1(n0c0b0m0p3,4):(-3) (0xc008000000000000) #d getd $ln0n0c0b0m0 4
  DEBUG-LM1(n0c0b0m0p3,6):(-1) (0xbff0000000000000) #d getd $ln0n0c0b0m0 4
  DEBUG-LM0(n0c0b0m0p0,8):(2) (0x4000000000000000) #d getd $lm8n0c0b0m0 4
  DEBUG-LM0(n0c0b0m0p0,10):(5) (0x4014000000000000) #d getd $lm8n0c0b0m0 4
  DEBUG-LM0(n0c0b0m0p0,12):(5) (0x4014000000000000) #d getd $lm8n0c0b0m0 4
  DEBUG-LM0(n0c0b0m0p0,14):(3) (0x4008000000000000) #d getd $lm8n0c0b0m0 4
  DEBUG-LM0(n0c0b0m0p1,8):(21) (0x4035000000000000) #d getd $lm8n0c0b0m0 4
  DEBUG-LM0(n0c0b0m0p1,10):(-11) (0xc026000000000000) #d getd $lm8n0c0b0m0 4
  DEBUG-LM0(n0c0b0m0p1,12):(15) (0x402e000000000000) #d getd $lm8n0c0b0m0 4
  DEBUG-LM0(n0c0b0m0p1,14):(7) (0x401c000000000000) #d getd $lm8n0c0b0m0 4
  DEBUG-LM0(n0c0b0m0p2,8):(6) (0x4018000000000000) #d getd $lm8n0c0b0m0 4
  DEBUG-LM0(n0c0b0m0p2,10):(-6) (0xc018000000000000) #d getd $lm8n0c0b0m0 4
  DEBUG-LM0(n0c0b0m0p2,12):(2) (0x4000000000000000) #d getd $lm8n0c0b0m0 4
  DEBUG-LM0(n0c0b0m0p2,14):(2) (0x4000000000000000) #d getd $lm8n0c0b0m0 4
  DEBUG-LM0(n0c0b0m0p3,8):(2) (0x4000000000000000) #d getd $lm8n0c0b0m0 4
  DEBUG-LM0(n0c0b0m0p3,10):(2) (0x4000000000000000) #d getd $lm8n0c0b0m0 4
  DEBUG-LM0(n0c0b0m0p3,12):(2) (0x4000000000000000) #d getd $lm8n0c0b0m0 4
  DEBUG-LM0(n0c0b0m0p3,14):(2) (0x4000000000000000) #d getd $lm8n0c0b0m0 4

上のDump結果を簡単に図示するとこのようになる。
 code:_
                     A (on $lx)                     B                                  Result
           PE0   PE1   PE2   PE3          PE0   PE1   PE2   PE3                PE0   PE1   PE2   PE3
         +-----+-----+-----+-----+      +-----+-----+-----+-----+            +-----+-----+-----+-----+
  addr 0 | -0  |  0  |  2  | -1  | mmul | -0  |  1  | -1  | -4  |    addr  8 |  2  |  21 |  6  |  2  |
  addr 2 |  0  |  4  | -1  | -4  |  +   |  1  | -1  |  3  |  1  | =  addr 10 |  5  | -11 | -6  |  2  |
  addr 4 | -1  |  1  | -1  | -1  | mfma |  1  |  1  |  1  | -3  |    addr 12 |  5  |  15 |  2  |  2  |
  addr 6 | -1  | -1  |  1  | -1  |      | -1  |  1  |  1  | -1  |    addr 14 |  3  |  7  |  2  |  2  |
         +-----+-----+-----+-----+      +-----+-----+-----+-----+            +-----+-----+-----+-----+

 図を確認しながらここまでの計算を追うと、普段考える行列積と異なるものを計算したような気分になるはず。
  その理由は[[アドレス伸長]]方向を行、[[PE]]方向を列と見たとき
  ここで計算したものは [[$ (A@B^T)^T]] であるため。
  [[MN-Core 2 ソフトウェア開発者マニュアル]]により詳細な説明があるが
   直感的には[[アドレス]]方向に一行ずつ取り出したベクトルと行列の積を取り
   それを[[サイクル]]毎に繰り返したものになっている
 code:_
  Result[[addr8,PE0]]=A[[addr0,PE0]]*B[[addr0,PE0]]+A[[addr0,PE1]]*B[[addr0,PE1]]+A[[addr0,PE2]]*B[[addr0,PE2]]+A[[addr0,PE3]]*B[[addr0,PE3]]
  Result[[addr8,PE1]]=A[[addr2,PE0]]*B[[addr0,PE0]]+A[[addr2,PE1]]*B[[addr0,PE1]]+A[[addr2,PE2]]*B[[addr0,PE2]]+A[[addr2,PE3]]*B[[addr0,PE3]]
  Result[[addr8,PE2]]=A[[addr4,PE0]]*B[[addr0,PE0]]+A[[addr4,PE1]]*B[[addr0,PE1]]+A[[addr4,PE2]]*B[[addr0,PE2]]+A[[addr4,PE3]]*B[[addr0,PE3]]
  Result[[addr8,PE3]]=A[[addr6,PE0]]*B[[addr0,PE0]]+A[[addr6,PE1]]*B[[addr0,PE1]]+A[[addr6,PE2]]*B[[addr0,PE2]]+A[[addr6,PE3]]*B[[addr0,PE3]]
                 ^        ^                         ^                         ^                         ^
  ...
 という具合に計算が進んでいく。この計算内容をNumPyを使って再現すると以下のようになる。
 code:py
  import numpy as np
  a = np.array(
      [[[0, 0, 2, -1]], [[0, 4, -1, -4]], [[-1, 1, -1, -1]], [[-1, -1, 1, -1]]], dtype=np.float32
  )
  b = np.array(
      [[[0, 1, -1, -4]], [[1, -1, 3, 1]], [[1, 1, 1, -3]], [[-1, 1, 1, -1]]], dtype=np.float32
  )
  print((a @ b.T).T)
 code:py
  [[[2.  21.   6.   2.]]
   [[5. -11.  -6.   2.]]
   [[5.  15.   2.   2.]]
   [[3.   7.   2.   2.]]]
 [[行列積]]の片方が転置されている場合、全く異なる計算内容になっていると考えるかもしれない。
 しかし、MN-Coreはその特殊な[[メモリ]]構造から、ホスト上のデータを並べ替えてからデバイスへ送る必要があり、その際に転置も含めてやってしまうことで結果的に求めたいものを得ることができる。
 また、もちろんMN-Core上で[[行列の転置]]を行うこともできる。

challenge: 16x16 matmul (A@B) in half を書いてみる。
 直感的な[[$ A@B]]を実現するために、MN-Core2上で[[$ B^T×A]]を計算してみよう。
 [[行列の転置]]についての説明はソフトウェア開発者マニュアルの[[mread]]付近でなされている。

 code:vsm
  # A
  d set $lm0n0c0b0m0p0 16 8000BE00BE00BE003E003E003E003E003E003E00BE003E003E00BE003E00BE00BE003E00BE003E00BE00BE003E003E003E00BE003E003E003E00BE003E00BE003E00BE00BE003E003E00BE00BE00BE00BE003E00BE00BE00BE00BE00BE00BE00BE003E00BE003E003E00BE003E00BE00BE00BE003E003E003E00BE00BE003E00
  d set $lm0n0c0b0m0p1 16 3E003E003E00BE003E00BE003E003E003E00BE00BE003E003E003E00BE0041003E003E003E003E003E00BE003E003E003E003E003E00BE003E004280BE003E003E00BE00BE00BE00BE003E00BE003E00BE00BE003E003E00BE00BE00BE003E00BE003E003E00BE00BE00BE00BE00BE003E00BE00C1003E00BE003E00BE00BE00
  d set $lm0n0c0b0m0p2 16 BE00BE00BE003E003E003E003E00BE003E00BE003E003E00BE00BE00BE00BE003E003E00BE00BE00BE003E003E003E003E003E003E003E00BE003E003E003E003E00BE00BE003E00BE00BE004000BE003E003E003E003E00BE003E003E00BE00BE00BE00BE004000BE00BE003E003E00BE003E003E00BE003E00BE003E00BE00
  d set $lm0n0c0b0m0p3 16 BE00BE00BE00BE00BE003E003E00BE00BE00BE003E00BE003E003E00BE00BE00BE003E003E003E003E00BE003E003E00BE003E003E00BE003E00BE00BE00BE00BE00BE00BE003E00BE00BE003E003E003E00BE00BE003E00BE00BE00BE00BE003E00BE00BE003E00BE00BE00BE003E003E003E003E003E00BE00BE00BE00BE00
  # B
  d set $ln0n0c0b0m0p0 16 80003E003E00BE003E003E003E003E00BE00BE003E003E00BE00BE003E003E004200BE003E003E00BE00BE00BE003E00BE003E00BE003E003E003E003E003E003E003E00BE003E003E003E003E00BE0040003E00BE003E00BE003E003E00BE003E003E00BE00BE00BE00BE00BE003E003E003E00BE00BE003E00BE003E00BE00
  d set $ln0n0c0b0m0p1 16 3E00BE003E003E00BE00BE00BE003E0042003E003E003E003E00BE00BE00BE00BE00BE003E00BE00BE003E003E00BE00BE003E003E00BE003E00BE00BE00BE003E003E003E00BE00BE003E003E003E00BE003E00BE003E00BE00BE00BE003E003E003E003E003E00BE00BE003E003E00BE003E003E003E00BE003E003E003E00
  d set $ln0n0c0b0m0p2 16 3E003E003E00BE00BE003E00BE00BE003E003E003E00BE00BE003E003E003E003E003E00BE00BE003E003E00BE00BE003E003E00BE003E003E003E00BE003E00BE003E004100BE00BE003E00BE003E003E003E003E00BE003E00BE00BE003E00BE003E003E00BE003E00BE003E003E003E003E003E00BE003E004200BE00BE00
  d set $ln0n0c0b0m0p3 16 BE00BE003E00BE003E00BE00BE003E00BE003E00BE00BE003E00BE00BE00BE00BE003E00BE00BE003E00BE00BE003E003E003E00BE00BE00BE00BE003E00BE003E003E00BE00BE003E00BE003E003E003E00BE00BE000000BE00BE003E00BE003E00BE00BE003E00BE00BE00BE003E003E00BE00BE003E003E003E003E00BE00
  
  # (write vsm here!)
  d geth $ln32n0c0b0m0 16
想定出力:
 code:dnp
  DEBUG-LM1(n0c0b0m0p0,32):(-5, -3, -1, -1) (0xc280, 0xc100, 0xbe00, 0xbe00) #d geth $ln32n0c0b0m0 16
  DEBUG-LM1(n0c0b0m0p0,34):(7, 4, 2, 8) (0x4380, 0x4200, 0x4000, 0x4400) #d geth $ln32n0c0b0m0 16
  DEBUG-LM1(n0c0b0m0p0,36):(9, 6, 4, 2) (0x4440, 0x4300, 0x4200, 0x4000) #d geth $ln32n0c0b0m0 16
  DEBUG-LM1(n0c0b0m0p0,38):(1, -4, 2, 4) (0x3e00, 0xc200, 0x4000, 0x4200) #d geth $ln32n0c0b0m0 16
  DEBUG-LM1(n0c0b0m0p0,40):(5, -2, 0, 6) (0x4280, 0xc000, 0x0000, 0x4300) #d geth $ln32n0c0b0m0 16
  DEBUG-LM1(n0c0b0m0p0,42):(7, 2, 4, -2) (0x4380, 0x4000, 0x4200, 0xc000) #d geth $ln32n0c0b0m0 16
  DEBUG-LM1(n0c0b0m0p0,44):(-1, 0, -2, 4) (0xbe00, 0x0000, 0xc000, 0x4200) #d geth $ln32n0c0b0m0 16
  DEBUG-LM1(n0c0b0m0p0,46):(1, -2, 0, 2) (0x3e00, 0xc000, 0x0000, 0x4000) #d geth $ln32n0c0b0m0 16
  DEBUG-LM1(n0c0b0m0p0,48):(1, -4, 6, -4) (0x3e00, 0xc200, 0x4300, 0xc200) #d geth $ln32n0c0b0m0 16
  DEBUG-LM1(n0c0b0m0p0,50):(3, 1, -3, -3) (0x4100, 0x3e00, 0xc100, 0xc100) #d geth $ln32n0c0b0m0 16
  DEBUG-LM1(n0c0b0m0p0,52):(5, 10, 0, -2) (0x4280, 0x4480, 0x0000, 0xc000) #d geth $ln32n0c0b0m0 16
  DEBUG-LM1(n0c0b0m0p0,54):(1, 2, 0, -2) (0x3e00, 0x4000, 0x0000, 0xc000) #d geth $ln32n0c0b0m0 16
  DEBUG-LM1(n0c0b0m0p0,56):(-10, -1, 1, -3) (0xc480, 0xbe00, 0x3e00, 0xc100) #d geth $ln32n0c0b0m0 16
  DEBUG-LM1(n0c0b0m0p0,58):(-5, -2, 4, -6) (0xc280, 0xc000, 0x4200, 0xc300) #d geth $ln32n0c0b0m0 16
  DEBUG-LM1(n0c0b0m0p0,60):(11, -6, 4, -2) (0x44c0, 0xc300, 0x4200, 0xc000) #d geth $ln32n0c0b0m0 16
  DEBUG-LM1(n0c0b0m0p0,62):(-5, -2, -4, 2) (0xc280, 0xc000, 0xc200, 0x4000) #d geth $ln32n0c0b0m0 16
  DEBUG-LM1(n0c0b0m0p1,32):(-6, -3, -1, -7) (0xc300, 0xc100, 0xbe00, 0xc380) #d geth $ln32n0c0b0m0 16
  DEBUG-LM1(n0c0b0m0p1,34):(3, -2, 2, 0) (0x4100, 0xc000, 0x4000, 0x0000) #d geth $ln32n0c0b0m0 16
  DEBUG-LM1(n0c0b0m0p1,36):(-1, -8, -8, -2) (0xbe00, 0xc400, 0xc400, 0xc000) #d geth $ln32n0c0b0m0 16
  DEBUG-LM1(n0c0b0m0p1,38):(11, -6, 2, -4) (0x44c0, 0xc300, 0x4000, 0xc200) #d geth $ln32n0c0b0m0 16
  DEBUG-LM1(n0c0b0m0p1,40):(-9, 0, 4, -6) (0xc440, 0x0000, 0x4200, 0xc300) #d geth $ln32n0c0b0m0 16
  DEBUG-LM1(n0c0b0m0p1,42):(1, 4, 0, 2) (0x3e00, 0x4200, 0x0000, 0x4000) #d geth $ln32n0c0b0m0 16
  DEBUG-LM1(n0c0b0m0p1,44):(-1, 2, 6, 0) (0xbe00, 0x4000, 0x4300, 0x0000) #d geth $ln32n0c0b0m0 16
  DEBUG-LM1(n0c0b0m0p1,46):(1, 4, 4, -2) (0x3e00, 0x4200, 0x4200, 0xc000) #d geth $ln32n0c0b0m0 16
  DEBUG-LM1(n0c0b0m0p1,48):(1, -6, -2, -4) (0x3e00, 0xc300, 0xc000, 0xc200) #d geth $ln32n0c0b0m0 16
  DEBUG-LM1(n0c0b0m0p1,50):(-4, 3, -3, 1) (0xc200, 0x4100, 0xc100, 0x3e00) #d geth $ln32n0c0b0m0 16
  DEBUG-LM1(n0c0b0m0p1,52):(-5, 4, -4, 2) (0xc280, 0x4200, 0xc200, 0x4000) #d geth $ln32n0c0b0m0 16
  DEBUG-LM1(n0c0b0m0p1,54):(-1, 0, -8, -2) (0xbe00, 0x0000, 0xc400, 0xc000) #d geth $ln32n0c0b0m0 16
  DEBUG-LM1(n0c0b0m0p1,56):(-6, -1, -5, -1) (0xc300, 0xbe00, 0xc280, 0xbe00) #d geth $ln32n0c0b0m0 16
  DEBUG-LM1(n0c0b0m0p1,58):(5, 0, -4, 6) (0x4280, 0x0000, 0xc200, 0x4300) #d geth $ln32n0c0b0m0 16
  DEBUG-LM1(n0c0b0m0p1,60):(5, 0, 0, 6) (0x4280, 0x0000, 0x0000, 0x4300) #d geth $ln32n0c0b0m0 16
  DEBUG-LM1(n0c0b0m0p1,62):(3, 0, -4, -6) (0x4100, 0x0000, 0xc200, 0xc300) #d geth $ln32n0c0b0m0 16
  DEBUG-LM1(n0c0b0m0p2,32):(3, -10, -9, 3) (0x4100, 0xc480, 0xc440, 0x4100) #d geth $ln32n0c0b0m0 16
  DEBUG-LM1(n0c0b0m0p2,34):(2, 5, 6, 0) (0x4000, 0x4280, 0x4300, 0x0000) #d geth $ln32n0c0b0m0 16
  DEBUG-LM1(n0c0b0m0p2,36):(0, -1, 4, -2) (0x0000, 0xbe00, 0x4200, 0xc000) #d geth $ln32n0c0b0m0 16
  DEBUG-LM1(n0c0b0m0p2,38):(6, -3, -2, 0) (0x4300, 0xc100, 0xc000, 0x0000) #d geth $ln32n0c0b0m0 16
  DEBUG-LM1(n0c0b0m0p2,40):(0, 9, -4, 2) (0x0000, 0x4440, 0xc200, 0x4000) #d geth $ln32n0c0b0m0 16
  DEBUG-LM1(n0c0b0m0p2,42):(4, 9, -4, 2) (0x4200, 0x4440, 0xc200, 0x4000) #d geth $ln32n0c0b0m0 16
  DEBUG-LM1(n0c0b0m0p2,44):(6, 1, 6, 0) (0x4300, 0x3e00, 0x4300, 0x0000) #d geth $ln32n0c0b0m0 16
  DEBUG-LM1(n0c0b0m0p2,46):(8, 3, -8, -6) (0x4400, 0x4100, 0xc400, 0xc300) #d geth $ln32n0c0b0m0 16
  DEBUG-LM1(n0c0b0m0p2,48):(-2, -1, 2, 0) (0xc000, 0xbe00, 0x4000, 0x0000) #d geth $ln32n0c0b0m0 16
  DEBUG-LM1(n0c0b0m0p2,50):(7, 4, -1, -5) (0x4380, 0x4200, 0xbe00, 0xc280) #d geth $ln32n0c0b0m0 16
  DEBUG-LM1(n0c0b0m0p2,52):(-4, 5, -4, 2) (0xc200, 0x4280, 0xc200, 0x4000) #d geth $ln32n0c0b0m0 16
  DEBUG-LM1(n0c0b0m0p2,54):(-4, -9, -4, 6) (0xc200, 0xc440, 0xc200, 0x4300) #d geth $ln32n0c0b0m0 16
  DEBUG-LM1(n0c0b0m0p2,56):(-3, 0, -9, 3) (0xc100, 0x0000, 0xc440, 0x4100) #d geth $ln32n0c0b0m0 16
  DEBUG-LM1(n0c0b0m0p2,58):(4, -3, 0, -2) (0x4200, 0xc100, 0x0000, 0xc000) #d geth $ln32n0c0b0m0 16
  DEBUG-LM1(n0c0b0m0p2,60):(0, 5, 4, -2) (0x0000, 0x4280, 0x4200, 0xc000) #d geth $ln32n0c0b0m0 16
  DEBUG-LM1(n0c0b0m0p2,62):(-4, -5, 8, -2) (0xc200, 0xc280, 0x4400, 0xc000) #d geth $ln32n0c0b0m0 16
  DEBUG-LM1(n0c0b0m0p3,32):(-5, 5, 3, -2) (0xc280, 0x4280, 0x4100, 0xc000) #d geth $ln32n0c0b0m0 16
  DEBUG-LM1(n0c0b0m0p3,34):(0, -2, -6, -3) (0x0000, 0xc000, 0xc300, 0xc100) #d geth $ln32n0c0b0m0 16
  DEBUG-LM1(n0c0b0m0p3,36):(-2, -4, 0, -5) (0xc000, 0xc200, 0x0000, 0xc280) #d geth $ln32n0c0b0m0 16
  DEBUG-LM1(n0c0b0m0p3,38):(-12, -2, 2, -1) (0xc500, 0xc000, 0x4000, 0xbe00) #d geth $ln32n0c0b0m0 16
  DEBUG-LM1(n0c0b0m0p3,40):(6, 0, -4, 1) (0x4300, 0x0000, 0xc200, 0x3e00) #d geth $ln32n0c0b0m0 16
  DEBUG-LM1(n0c0b0m0p3,42):(2, 0, 0, -5) (0x4000, 0x0000, 0x0000, 0xc280) #d geth $ln32n0c0b0m0 16
  DEBUG-LM1(n0c0b0m0p3,44):(0, -2, -6, -3) (0x0000, 0xc000, 0xc300, 0xc100) #d geth $ln32n0c0b0m0 16
  DEBUG-LM1(n0c0b0m0p3,46):(-2, -8, 0, 3) (0xc000, 0xc400, 0x0000, 0x4100) #d geth $ln32n0c0b0m0 16
  DEBUG-LM1(n0c0b0m0p3,48):(-4, 6, 6, -9) (0xc200, 0x4300, 0x4300, 0xc440) #d geth $ln32n0c0b0m0 16
  DEBUG-LM1(n0c0b0m0p3,50):(1, -3, 5, 1) (0x3e00, 0xc100, 0x4280, 0x3e00) #d geth $ln32n0c0b0m0 16
  DEBUG-LM1(n0c0b0m0p3,52):(6, 0, 4, -1) (0x4300, 0x0000, 0x4200, 0xbe00) #d geth $ln32n0c0b0m0 16
  DEBUG-LM1(n0c0b0m0p3,54):(-2, 0, 8, 3) (0xc000, 0x0000, 0x4400, 0x4100) #d geth $ln32n0c0b0m0 16
  DEBUG-LM1(n0c0b0m0p3,56):(5, -1, 1, 0) (0x4280, 0xbe00, 0x3e00, 0x0000) #d geth $ln32n0c0b0m0 16
  DEBUG-LM1(n0c0b0m0p3,58):(-6, 4, 8, -5) (0xc300, 0x4200, 0x4400, 0xc280) #d geth $ln32n0c0b0m0 16
  DEBUG-LM1(n0c0b0m0p3,60):(-2, -4, 0, 3) (0xc000, 0xc200, 0x0000, 0x4100) #d geth $ln32n0c0b0m0 16
  DEBUG-LM1(n0c0b0m0p3,62):(2, 0, 0, -1) (0x4000, 0x0000, 0x0000, 0xbe00) #d geth $ln32n0c0b0m0 16
