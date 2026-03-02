---
title: 3.5.8.16 DRAM→L2BMグループ間分配放送命令
id: 66b35ffe9453fb001c212d30
created_unix: 1723031550
updated_unix: 1771407725
views: 6
---

# 3.5.8.16 DRAM→L2BMグループ間分配放送命令

この命令は複雑なのでまず具体的に、単位動作である[[L2BM側 64 長語書き込み]]の動作を説明する。
　各グループの[[DRAM]]から 32 長語ずつ読み、前半 16 長語をグループ順に並べた 64 長語を全グループの 0 番目の[[L2BM]]に[[放送]]する。
　後半 16 長語を同様に並べた 64 長語を全グループの 1 番目のL2BMに放送する。

単位動作でない場合はこれを繰り返す。

スループットはDRAM側 8 長語/サイクル、L2BM側 16 長語/サイクルである。

```文法
mvb4/n<size>[<tag>] $d<addr_d> $lc<addr_c> 

```
```効果
uint_t n=size / 64
for i= 0:n
  uint_t src_offset= addr_d+ 32 * i
  uint_t dst_addr=addr_c + 64 *i
  LongWord buf[2][64]
  forall group,l2b
    uint_t src_addr=src_offset +l2b* 16
    uint_t buf_addr=group* 16
    buf[l2b][buf_addr:buf_addr+16] = MEM[group].dram[src_addr:src_addr+16]
  forall group,l2b
    MEM[group][l2b].l2bm[dst_addr:dst_addr+64] = buf[l2b][0:64]
    

```
エラー
 sizeが単位動作 64 の倍数でないとエラーになる。

```例
mvb4/n64 $d0 $lc0
```
本節冒頭で延べた単位動作である。

<https://tech.preferred.jp/wp-content/uploads/2024/07/anim11.gif>
