---
title: 3.5.8.15 L2BM→PDMグループ内縮約命令
id: 66b35ffe9453fb001c212d2d
created_unix: 1723031550
updated_unix: 1771433472
views: 7
---

# 3.5.8.15 L2BM→PDMグループ内縮約命令

指定したグループについて、 2 個両方の[[L2BM]]から等サイズで読んで[[L2B方向]]に縮約し、同じグループの[[PDM]]に書き込む。
 単位動作は 64 長語である。
スループットは 16 長語/サイクルである。
この命令には対となる[[PDM→L2BMグループ内放送命令]]が存在しないことに注意する。

```文法
mvr2<op>/n<size>[<tag>] $lc<addr_c>@<group> $p<addr_p>@<group>

```
[[縮約演算指定]]`<op>`については[[3.5.5 縮約演算指定]]を参照のこと。

```効果
uint_t n=size / 64
for i= 0:n
  uint_t src_addr=addr_c + 64 *i
  uint_t dst_addr=addr_p + 64 *i
  LongWord buf[64] = [0, ..., 0]
  forall l2b
    buf[0:64] =op(buf[0:64],MEM[group][l2b].l2bm[src_addr:src_addr+64])
    MEM[group].pdm[dst_addr:dst_addr+64] =buf

```
注意：縮約を内部的に実際にこの手順で行っているわけではない。

エラー
 sizeが単位動作 64 の倍数でないとエラーになる。

```例
mvr2dfadd/n64 $lc0@1 $p0@1
```
1 番グループについて、 2 つのL2BMから 64 長語ずつ読んで[[倍精度浮動小数点数加算]]を行い、完成した 64長語を 1 番PDMに書き込む。

$ mvr2dfadd/n64 $lc0@1 $p0@1
 <https://gyazo.com/fd245d94ef6c07a2e42961a679b6f701>
