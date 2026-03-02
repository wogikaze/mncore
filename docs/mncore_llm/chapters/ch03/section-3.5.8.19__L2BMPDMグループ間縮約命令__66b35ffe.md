---
title: 3.5.8.19 L2BM→PDMグループ間縮約命令
id: 66b35ffe9453fb001c212d39
created_unix: 1723031550
updated_unix: 1771433503
views: 9
---

# 3.5.8.19 L2BM→PDMグループ間縮約命令

8 個すべての[[L2BM]]から等サイズで読んで[[L2B方向]]に[[縮約]]し、指定したグループの[[PDM]]に書き込む。
単位動作は 64 長語である。
スループットは 8 長語/サイクルである。

```txt文法
mvr<op>/n<size>[<tag>] $lc<addr_c> $p<addr_p>@<group_p>
```
[[縮約演算指定]]`<op>`については[[3.5.5 縮約演算指定]]を参照のこと。

```効果
uint_t n=size / 64
for i= 0:n
  uint_t src_addr=addr_c + 64 *i
  uint_t dst_addr=addr_p + 64 *i
  LongWord buf[64]
  forall group,l2b
    buf[0:64] =op(buf[0:64],MEM[group][l2b].l2bm[src_addr:src_addr+64])
    MEM[group_p].pdm[dst_addr:dst_addr+64] = buf
```
注意：縮約を内部的に実際にこの手順で行っているわけではない。

エラー
 sizeが単位動作 64 の倍数でないとエラーになる。

```例
mvrdfadd/n64 $lc0 $p0@0
```
8 個すべてのL2BMから 64 長語ずつ読んで、L2B番号方向に[[倍精度浮動小数点数加算]]で縮約し、 0 番グループのPDMに書き込む。

$ mvrdfadd/n64 $lc0 $p0@1
 <https://gyazo.com/ed21cb19a880f5927d178b038db64188>
