---
title: 3.5.8.11 DRAM→L2BM並列個別転送命令
id: 66b35ffe9453fb001c212d1b
created_unix: 1723031550
updated_unix: 1771433580
views: 11
---

# 3.5.8.11 DRAM→L2BM並列個別転送命令

すべてのグループについて、[[DRAM]]から同じグループの指定した[[L2B番号]]の[[L2BM]]にデータをコピーする。
 単位動作は 64 長語である。
スループットはグループあたり 16 長語/サイクルである。
```文法
mvp/n<size>[<tag>] $d<addr_d> $lc<addr_c>@.<l2b_c>

```
```効果
uint_t n=size / 64
for i= 0:n
  uint_t src_addr=addr_d + 64 *i
  uint_t dst_addr=addr_c + 64 *i
  forall group
    LongWord data[64] = MEM[group].dram[src_addr:src_addr+64]
    MEM[group][l2b_c].l2bm[dst_addr:dst_addr+64] = data

```
エラー
 sizeが単位動作 64 の倍数でないとエラーになる。

```例
mvp/n64 $d0 $lc0@.1
```
すべてのグループについて、DRAMから 1 番L2BのL2BMに 64 長語をコピーする。

$ mvp/n64 $d0 $lc0@.1
 <https://gyazo.com/9e3744dde2dc5b7b442c98dbdacf785e>
