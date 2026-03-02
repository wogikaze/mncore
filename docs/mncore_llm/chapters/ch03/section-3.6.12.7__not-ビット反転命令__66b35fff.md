---
title: 3.6.12.7 not-ビット反転命令
id: 66b35fffd1af80001d29cced
created_unix: 1723031551
updated_unix: 1771368729
views: 10
---

# 3.6.12.7 not-ビット反転命令

[[not命令]]は[[ビット反転]]を行う。

```例
zero $nowrite
lnot $aluf $lr0v
```
関連：[[zero命令]]

GRF0には 4 長語の`all 1`が書き込まれる。
この[[lnot]]は[[論理否定命令]]([[3.6.12.8 lnot-論理否定命令]])ではなく、精度指定が長語の[[ビット反転命令]]である。
