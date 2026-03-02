---
title: 3.5.8.21 L2BM→DRAMグループ間縮約命令
id: 66b35ffe9453fb001c212d3f
created_unix: 1723031550
updated_unix: 1771427894
views: 6
---

# 3.5.8.21 L2BM→DRAMグループ間縮約命令

すべての[[L2BM]]から等サイズに読んで[[L2B方向]]に[[縮約]]し、 4 つの[[DRAM]]に等分配する。
単位動作はL2BM側 64 長語、DRAM側 16 長語である。
スループットはL2BM側で数えて 32 長語/サイクルである。

```文法
mvr<op>/n<size>[<tag>] $lc<addr_c> $d<addr_d>
```
[[縮約演算指定]]`<op>`については[[3.5.5 縮約演算指定]]を参照のこと。

```効果
uint_t n=size / 64
for i= 0:n
  uint_t src_addr=addr_c + 64 *i
  uint_t dst_oddr=addr_d + 16 *i
  LongWord buf[64]
  forall group
    forall l2b
      buf[0:64] =op(buf[0:64],MEM[group][l2b].l2bm[src_addr:src_addr+64]
   forall group
     uint_t buf_addr= 16 *group
     MEM[group].dram[dst_addr:dst_addr+16] = buf[buf_addr:buf_addr+16]
```
注意：縮約を内部的に実際にこの手順で行っているわけではない。

エラー
 sizeが単位動作 64 の倍数でないとエラーになる。

```例
mvrdfadd/n64 $lc0 $d0
```
8 個すべてのL2BMから 64 長語ずつ読んでL2B方向に縮約した 64 長語を、各グループ 16 長語ずつにしてDRAMに書き込む。

$ mvrdfadd/n64 $lc0 $d0
 <https://gyazo.com/5a60c5a0921b907ade055656e00e6af2>
