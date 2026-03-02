---
title: 3.5.8.4 PDM→L2BM単独個別転送命令
id: 66b35ffe9453fb001c212d06
created_unix: 1723031550
updated_unix: 1771433042
views: 10
---

# 3.5.8.4 PDM→L2BM単独個別転送命令

指定したグループの[[PDM]]から指定したグループと[[L2B番号]]の[[L2BM]]にデータをコピーする。
 単位動作は 64 長語である。
読み出し元と書き込み先のグループは同じでも別でもよい。
スループットはグループ内の場合 16 長語/サイクル、グループ間の場合 8 長語/サイクルである。
すべてのグループについて同じアドレスで[[グループ内転送]]を行う場合、[[3.5.8.9 PDM→L2BM並列個別転送命令]]で述べる並列版を利用した方がレイテンシの面で有利である。

```文法
mvp/n<size>[<tag>] $p<addr_p>@<group_p> $lc<addr_c>@<group_c>.<l2b_c>

```
```効果
uint_t n=size / 64
for i= 0:n
  uint_t src_addr=addr_p + 64 *i
  uint_t dst_addr=addr_c + 64 *i
  LongWord data[64] = MEM[group_p].pdm[src_addr:src_addr+64]
  MEM[group_c][l2b_c].l2bm[dst_addr:dst_addr+64] = data

```
エラー
 sizeが単位動作 64 の倍数でないとエラーになる。

```例
mvp/n64 $p0@0 $lc0@2.1
```
0 番グループのPDMから 2 番グループ・ 1 番L2BのL2BMに 64 長語をコピーする。

$ mvp/n64 $p0@0 $lc0@0.1
 <https://gyazo.com/8c00ece3653230153b20fa56ec9c654d>
$ mvp/n64 $p0@0 $lc0@2.1
 <https://gyazo.com/fd784bf38157cc2e4ef0fc1b4c9c1f24>
