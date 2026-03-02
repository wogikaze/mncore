---
title: 3.6.3.8 PE→L1BM転送⇒L1BM→PE転送
id: 66b35ffec7de62001da434ee
created_unix: 1723031550
updated_unix: 1724423460
views: 13
---

# 3.6.3.8 PE→L1BM転送⇒L1BM→PE転送

PE→[[L1BM]]転送命令から、[[L1BM]]→PE転送命令まではポート衝突のため 2 [[ステップ]]空ける必要がある。


```例 1
l1bmrdfadd $lr0v $lb0
nop/2
l1bmm $lb16 $ls0v

```
この例で[[nop]]/2を[[nop]]とするとエラーになる。
