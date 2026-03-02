---
title: 3.6.3.2 L1BM→L2BM転送⇒L2BM→L1BM転送
id: 66b35ffec7de62001da434dc
created_unix: 1723031550
updated_unix: 1724423214
views: 21
---

# 3.6.3.2 L1BM→L2BM転送⇒L2BM→L1BM転送

[[L1BM]]→[[L2BM]]転送命令から[[L2BM]]→[[L1BM]]転送命令まではポート衝突のため 3 [[ステップ]]空ける必要がある。

```例
l2bm@0 $lb0 $lc0
nop/3
l2bmb $lc64 $lb64
```
この例でnop/3をnop/2とするとエラーになる。
[[l2bm]], [[l2bmb]]
