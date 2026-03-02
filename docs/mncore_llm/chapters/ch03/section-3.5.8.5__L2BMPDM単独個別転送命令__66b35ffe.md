---
title: 3.5.8.5 L2BM→PDM単独個別転送命令
id: 66b35ffe9453fb001c212d09
created_unix: 1723031550
updated_unix: 1771433268
views: 12
---

# 3.5.8.5 L2BM→PDM単独個別転送命令

指定したグループと[[L2B番号]]の[[L2BM]]から指定したグループのPDMにデータをコピーする。
 単位動作は 64 長語である。
読み出し元と書き込み先のグループは同じでも別でもよい。
スループットはグループ内の場合 16 長語/サイクル、グループ間の場合 8 長語/サイクルである。
すべてのグループについて同じアドレスで[[グループ内転送]]を行う場合、[[3.5.8.10 L2BM→PDM並列個別転送命令]]で述べる並列版を利用した方がレイテンシの面で有利である。

```文法
mvp/n<size>[<tag>] $lc<addr_c>@<group_c>.<l2b_c> $p<addr_p>@<group_p>

```
```効果
uint_t n=size / 64
for i= 0:n
  uint_t src_addr=addr_c + 64 *i
  uint_t dst_addr=addr_p + 64 *i
  LongWord data[64] = MEM[group_c][l2b_c].l2bm[src_addr:src_addr+64]
  MEM[group_p].pdm[dst_addr:dst_addr+64] = data

```
エラー
 sizeが単位動作 64 の倍数でないとエラーになる。

```例
mvp/n64 $lc0@2.1$p0@0
```
2 番グループ・ 1 番L2BのL2BMから 0 番グループのPDMに 64 長語をコピーする。

$ mvp/n64 $lc0@0.1$p0@0
 <https://gyazo.com/d5d5579d9543987f34ee06e79b6816c3>
$ mvp/n64 $lc0@2.1$p0@0
 <https://gyazo.com/444d1e87162132f62204ba9900f5d8ed>
