---
title: 3.5.8.12 L2BM→DRAM並列個別転送命令
id: 66b35ffe9453fb001c212d24
created_unix: 1723031550
updated_unix: 1771427918
views: 14
---

# 3.5.8.12 L2BM→DRAM並列個別転送命令

すべてのグループについて、指定した[[L2B番号]]の[[L2BM]]から、同じグループの[[DRAM]]にデータをコピーする。
 単位動作は 64 長語である。
スループットはグループあたり 16 長語/サイクルである。

```文法
mvp/n<size>[<tag>] $lc<addr_c>@.<l2b_c> $d<addr_d>

```
```効果
uint_t n=size / 64
for i= 0:n
  uint_t src_addr=addr_c + 64 *i
  uint_t dst_addr=addr_d + 64 *i
  forall group
    LongWord data[64] = MEM[group][l2b_c].l2bm[src_addr:src_addr+64]
    MEM[group].dram[dst_addr:dst_addr+64] = data

```
エラー
 sizeが単位動作 64 の倍数でないとエラーになる。

```例
mvp/n64 $lc0@.1 $d0
```
すべてのグループについて、 1 番L2BのL2BMからDRAMに 64 長語をコピーする。

$ mvp/n64 $lc0@.1 $d0
 <https://gyazo.com/891a658d12616c9667f65e46a70cabda>
