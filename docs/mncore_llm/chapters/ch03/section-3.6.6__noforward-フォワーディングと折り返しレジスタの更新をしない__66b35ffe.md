---
title: 3.6.6 noforward-フォワーディングと折り返しレジスタの更新をしない
id: 66b35ffe02bee8001d369bc6
created_unix: 1723031550
updated_unix: 1771370075
views: 21
---

# 3.6.6 noforward-フォワーディングと折り返しレジスタの更新をしない

[[noforward命令]]が書かれた[[ステップ]]では、
 [[フォワーディングレジスタ]]([[$mauf]]、[[$aluf]]、[[$mreadf]]、[[$lbf]])と[[L1BM折り返しレジスタ]]([[$lbi]])の更新をしない。
noforward命令式は[[nop]]を除く他の任意の[[PE命令]]式と同時発行できる。

```文法
noforward

```
