---
title: 2.3 エミュレータ
id: 66b35ffed0fb0f001d0cde78
created_unix: 1723031550
updated_unix: 1723376510
views: 81
---

# 2.3 エミュレータ

MN-Core 2[[ボード]]の[[エミュレータ]]が存在する。[[命令ストリーム]]が[[パック形式]]([[1.2 機械語命令概観]])になっている必要がなく、また[[アセンブリ言語]]内で主要なメモリ要素の内容を出力する[[制御文]]([[3.4.3 Debug get文]])が記述できるため挙動の確認に向く。
標準の[[バイナリ名]]は[[gpfn3_package_main]]である。

以下はファイル`sample.vsm`に手書きした[[命令列]]を[[アセンブル]]し、エミュレータで実行する例である。
 `assemble3`および`gpfn3_package_main`にPATHが通っている前提とする。

1 行目の[[lpassa]]は[[LM0]]にそれが属する[[PE]]の番号(0から3)を書き込み、 2 行目の[[d get]]はあるひとつの[[MAB]]について、書き込んだ場所の内容を読み出している。
d get命令で読み出した値は[[-dオプション]]で指定したファイルに出力される。
 よってファイル`sample.dmp`には、[[PE番号]]に対応して 0 から 3 の値が書き込まれることとなる。
 1 行目のlpassa命令についての詳細は[[3.6.12.5 passa-コピー命令]]、[[3.6.1.20 固定値入力オペランド]]、[[3.6.1.6 m-LM0(ベースアドレスレジスタ書き込みを除く)]]を、 2 行目のd get命令についての詳細は[[3.4.3 Debug get文]]を参照のこと。

[[vsm]]と[[asm]]と[[dmp]]がそもそもわからない[[wogikaze.icon]]
 [[Virtual State Machine]]
  コンピュータプログラムの実行を抽象化した概念モデル[[Claude.icon]]
 [[Assembly]]
  アセンブリ言語は低水準のプログラミング言語で、機械語に非常に近い形式で書かれています[[Claude.icon]]
 [[dump]]
  通常はシステムやプログラムの状態をキャプチャしたデバッグ情報を含むファイルを指します。[[Claude.icon]]
  この場合、特定のハードウェアやソフトウェアコンポーネントの状態をデバッグ目的で記録したものだと考えられます。

[[エミュレータを動かしてみる]]

$ cat sample.vsm
```sample.vsm
lpassa $subpeid $lm
d get $lm0n0c0b0m0 1

```
$ assemble3 sample.vsm > sample.asm
$ gpfn3_package_main -i sample.asm -d sample.dmp
$ cat sample.dmp
```sample.dmp
DEBUG-LM0(n0c0b0m0p0,0):(f:0,i:{{0x0,0x0},{0x0,0x0}},v:0x0) #d get $lm0n0c0b0m0 1
DEBUG-LM0(n0c0b0m0p1,0):(f:0,i:{{0x0,0x0},{0x0,0x1}},v:0x1) #d get $lm0n0c0b0m0 1
DEBUG-LM0(n0c0b0m0p2,0):(f:0,i:{{0x0,0x0},{0x0,0x2}},v:0x2) #d get $lm0n0c0b0m0 1
DEBUG-LM0(n0c0b0m0p3,0):(f:0,i:{{0x0,0x0},{0x0,0x3}},v:0x3) #d get $lm0n0c0b0m0 1

```
