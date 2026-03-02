---
title: 3.5.8.20 DRAM→L2BMグループ間放送命令
id: 66b35ffe9453fb001c212d3c
created_unix: 1723031550
updated_unix: 1771426121
views: 18
---

# 3.5.8.20 DRAM→L2BMグループ間放送命令

すべてのグループの[[DRAM]]から等サイズに読んで結合し、すべての[[L2BM]]に[[放送]]する。
単位動作はDRAM側 16 長語、L2BM側 64 長語である。
スループットはL2BM側で数えて 32 長語/サイクルである。

```文法
mvb/n<size>[<tag>] $d<addr_d> $lc<addr_c> 

```
```効果
uint_t n=size / 64
for i= 0:n
  uint_t src_addr=addr_d + 16 *i
  uint_t dst_addr=addr_c + 64 *i
  LongWord buf[64]
  for group_dram= 0:4
    uint_t buf_addr=group_dram * 16
    buf[buf_addr:buf_addr+16] = MEM[group_dram].dram[src_addr:src_addr+16]
  forall group,l2b
    MEM[group][l2b].l2bm[dst_addr:dst_addr+64] = buf[0:64]


```
エラー
 sizeが単位動作 64 の倍数でないとエラーになる。

```例
mvb/n64 $d0 $lc0
```
すべてのグループのDRAMから 16 長語ずつ読んで結合した 64 長語をすべてのL2BMに放送する。

$ mvb/n64 $d0 $lc0
 <https://gyazo.com/49fa4561b21cee7acca9f2d8ebc41348>
