---
title: 3.5.8.13 DRAM→L2BMグループ内放送命令
id: 66b35ffe9453fb001c212d27
created_unix: 1723031550
updated_unix: 1771425430
views: 8
---

# 3.5.8.13 DRAM→L2BMグループ内放送命令

すべてのグループについて、[[DRAM]]から同じグループの 2 つの[[L2BM]]にデータをコピーする。
 単位動作は 64 長語である。
スループットは 16 長語/サイクルである。

```文法
mvb2/n<size>[<tag>] $d<addr_d> $lc<addr_c>

```
```効果
uint_t n=size / 64
for i= 0:n
  uint_t src_addr=addr_d + 64 *i
  uint_t dst_addr=addr_c + 64 *i
  forall group
    LongWord data[64] = MEM[group].dram[src_addr:src_addr+64]
    forall l2b
      MEM[group][l2b].l2bm[dst_addr:dst_addr+64] = data


```
エラー
 sizeが単位動作 64 の倍数でないとエラーになる。

```例
mvb2/n64 $d0 $lc0
```
すべてのグループについて、DRAMから 2 つのL2BMに 64 長語を放送する。

$ mvb2/n64 $d0 $lc0
 <https://gyazo.com/273eb6a4e8d92c8b6302ad30e2bd8b46>
