---
title: 3.5.8.7 L2BM→DRAM単独個別転送命令
id: 66b35ffe9453fb001c212d0f
created_unix: 1723031550
updated_unix: 1771428074
views: 15
---

# 3.5.8.7 L2BM→DRAM単独個別転送命令

指定した[[グループ番号]]・[[L2B番号]]の[[L2BM]]から、指定したグループの[[DRAM]]にデータをコピーする。
 単位動作は 64 長語である。
スループットはグループ内の場合 16 長語/サイクル、グループ間の場合 8 長語/サイクルである。
すべてのグループについて同じアドレスで[[グループ内転送]]を行う場合、[[3.5.8.12 L2BM→DRAM並列個別転送命令]]で述べる並列版を利用した方がレイテンシの面で有利である。

```文法
mvp/n<size>[<tag>] $lc<addr_c>@<group_c>.<l2b_c> $d<addr_d>@<group_d>

```
```効果
uint_t n=size / 64
for i= 0:n
  uint_t src_addr=addr_c + 64 *i
  uint_t dst_addr=addr_d + 64 *i
  LongWord data[64] = MEM[group_c][l2b_c].l2bm[src_addr:src_addr+64]
  MEM[group_d].dram[dst_addr:dst_addr+64] = data

```
エラー
 sizeが単位動作 64 の倍数でないとエラーになる。

```例
mvp/n64 $lc0@2.1$d0
```
2 番グループ・ 1 番L2BのL2BMから 0 番グループのDRAMに 64 長語をコピーする。

$ mvp/n64 $lc0@0.1 $d0@0
 <https://gyazo.com/eefa1c9a21dec4df39aea35e45b5163b>
$ mvp/n64 $lc0@2.1 $d0@0
 <https://gyazo.com/92224fd487ce6697930a7f3dd1774167>
