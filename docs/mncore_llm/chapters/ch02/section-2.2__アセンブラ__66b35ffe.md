---
title: 2.2 アセンブラ
id: 66b35ffed0fb0f001d0cde75
created_unix: 1723031550
updated_unix: 1723074483
views: 55
---

# 2.2 アセンブラ

MN-Core 2[[アセンブラ]]は、[[第3章 MN-Core2アセンブリ言語による開発]]で述べる[[アセンブリ言語]]で実装されたプログラムを機械語に変換する。
標準のバイナリ名は[[assemble3]]である。
assemble3にPATHが通っている状況で以下を実行すると`pass.asm`にアセンブル結果が出力される。
$ echo'lpassa $lm0v $ln0v' >pass.vsm
$ assemble3 pass.vsm >pass.asm
