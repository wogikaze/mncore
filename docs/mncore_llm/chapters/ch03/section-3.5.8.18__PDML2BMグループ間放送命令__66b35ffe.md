---
title: 3.5.8.18 PDM→L2BMグループ間放送命令
id: 66b35ffe9453fb001c212d36
created_unix: 1723031550
updated_unix: 1771433108
views: 8
---

# 3.5.8.18 PDM→L2BMグループ間放送命令

指定したグループのPDMから 8 個すべての[[L2BM]]にデータを放送する。
単位動作は 64 長語である。
スループットは 8 長語/サイクルである。

```文法
mvb/n<size>[<tag>] $p<addr_p>@<group_p> $lc<addr_c>

```
```効果
uint_t n=size / 64
for i= 0:n
  uint_t src_addr=addr_p + 64 *i
  uint_t dst_addr=addr_c + 64 *i
  LongWord data[64] = MEM[group_p].pdm[src_addr:src_addr+64]
  forall group,l2b
    MEM[group][l2b].l2bm[dst_addr:dst_addr+64] = data

```
エラー
 sizeが単位動作 64 の倍数でないとエラーになる。

```例
mvb/n64 $p0@0 $lc0
```
0 番グループのPDMから 8 個すべてのL2BMに 64 長語を放送する。

$ mvb/n64 $p0@1 $lc0
 <https://gyazo.com/104c1349195f2b1759c4e34b997a2f96>
