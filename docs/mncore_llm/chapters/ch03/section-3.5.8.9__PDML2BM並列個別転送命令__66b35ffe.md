---
title: 3.5.8.9 PDM→L2BM並列個別転送命令
id: 66b35ffe9453fb001c212d15
created_unix: 1723031550
updated_unix: 1771433071
views: 23
---

# 3.5.8.9 PDM→L2BM並列個別転送命令

すべてのグループについて、[[PDM]]から同じグループの指定した[[L2B番号]]の[[L2BM]]にデータをコピーする。
 単位動作は 64 長語である。
スループットはグループあたり 16 長語/サイクルである。

```文法
mvp/n<size>[<tag>] $p<addr_p> $lc<addr_c>@.<l2b_c>

```
```効果
uint_t n=size / 64
for i= 0:n
  uint_t src_addr=addr_p + 64 *i
  uint_t dst_addr=addr_c + 64 *i
  forall group
    LongWord data[64] = MEM[group].pdm[src_addr:src_addr+64]
    MEM[group][l2b_c].l2bm[dst_addr:dst_addr+64] = data

```
エラー
 sizeが単位動作 64 の倍数でないとエラーになる。

```例
mvp/n64 $p0 $lc0@.1
```
すべてのグループについて、PDMから 1 番L2BのL2BMに 64 長語をコピーする。

$ mvp/n64 $p0 $lc0@.1
 <https://gyazo.com/39a1d729c9cb1a76ecd31d74dc2776a9>
