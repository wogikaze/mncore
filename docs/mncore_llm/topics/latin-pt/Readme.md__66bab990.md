---
title: Readme.md
id: 66bab9908eef83001c084c3f
created_unix: 1723513235
updated_unix: 1723513575
views: 15
---

# Readme.md

[[エミュレータ]]に同梱されていたReadme.md

[[*** 配布物]]
 `README.md` 本文書
 `DISCLAIMER.txt` 配布物についての[[免責事項]]
 `NOTICE.md` OSSライセンス表示
 `mncore2_dev_manual_ja.pdf` [[MN-Core 2 ソフトウェア開発者マニュアル]]
 `tutorial.md` [[アセンブラ]]・[[エミュレータ]]を利用した[[チュートリアル]]
 `assemble3` MN-Core 2 アセンブラ
 `gpfn3_package_main` MN-Core 2 エミュレータ
 `Changelog.md` [[変更履歴]]


[[*** 想定環境]]
 本パッケージで配布するアセンブラ・エミュレータは実行環境として[[Ubuntu]]22.04を想定している。

[[*** 依存ライブラリのインストール]]
 [[** Debian/Ubuntu]]
 code:sh
  apt-get install libgomp1
 [[** Rocky Linux/Fedora]]
 code:sh
  yum install libgomp


[[*** アセンブラ]]
 MN-Core 2 アセンブラは、MN-Core 2 ソフトウェア開発者マニュアル(以下[[SDM]])第3章で述べるアセンブリ言語で実装されたプログラムを機械語に変換する。
 標準のバイナリ名は`assemble3`である。
 `assemble3`に[[PATH]]が通っている状況で以下を実行するとpass.asmにアセンブル結果が出力される。
  code:sh
   echo 'lpassa $lm0v $ln0v' > pass.vsm
   assemble3 pass.vsm > pass.asm

[[*** エミュレータ]]
 MN-Core 2ボードのエミュレータが存在する。
 [[命令ストリーム]]が[[パック形式]] ([[1.2 機械語命令概観]]) になっている必要がなく、また[[アセンブリ言語]]内で主要なメモリ要素の内容を出力する制御文 ([[Debug get文]]、[[3.4.3 Debug get文]]) が記述できるため挙動の確認に向く。
 標準のバイナリ名は`gpfn3_package_main`である。
 以下はファイル`sample.vsm`に手書きした[[命令列]]を[[アセンブル]]し、エミュレータで実行する例である。
 `assemble3`および`gpfn3_package_main`にPATHが通っている前提とする。
  1行目の`lpassa`命令は[[LM0]]にそれが属する[[PE]]の番号 (0から3) を書き込み
  2行目の`d get`命令はあるひとつの[[MAB]]について、書き込んだ場所の内容を読み出している。
 `d get`命令で読み出した値は`-d`オプションで指定したファイルに出力される。
 よってファイル`sample.dmp`には、[[PE番号]]に対応して0から3の値が書き込まれることとなる。
  1行目の`lpassa`命令についての詳細は[[3.6.12.5 passa-コピー命令]]、[[3.6.1.20 固定値入力オペランド]]、[[3.6.1.6 m-LM0(ベースアドレスレジスタ書き込みを除く)]]
  2行目の`d get`命令についての詳細は[[3.4.3 Debug get文]]を参照のこと。

```sh
$ cat sample.vsm
lpassa $subpeid $lm0
d get $lm0n0c0b0m0 1
$ assemble3 sample.vsm > sample.asm
$ gpfn3_package_main -i sample.asm -d sample.dmp
$ cat sample.dmp
DEBUG-LM0(n0c0b0m0p0,0):(f:0, i:{{0x0,0x0},{0x0,0x0}}, v:0x0) #d get $lm0n0c0b0m0 1
DEBUG-LM0(n0c0b0m0p1,0):(f:0, i:{{0x0,0x0},{0x0,0x1}}, v:0x1) #d get $lm0n0c0b0m0 1
DEBUG-LM0(n0c0b0m0p2,0):(f:0, i:{{0x0,0x0},{0x0,0x2}}, v:0x2) #d get $lm0n0c0b0m0 1
DEBUG-LM0(n0c0b0m0p3,0):(f:0, i:{{0x0,0x0},{0x0,0x3}}, v:0x3) #d get $lm0n0c0b0m0 1


```
