---
title: 3.6.12.8 lnot-論理否定命令
id: 66b35fffd1af80001d29ccf0
created_unix: 1723031551
updated_unix: 1771368762
views: 26
---

# 3.6.12.8 lnot-論理否定命令

[[lnot命令]]は[[論理否定]]を返す。すなわち、入力がall 0なら 1 を返し、そうでなければ 0 を返す。


```例
ilnot $subpeid $lr0
```
関連：[[$subpeid]]
 `$lr0`には 0 番PEでのみ単精度整数の 1 が 2 つ並んだ値が入り、それ以外のPEではall 0となる。
