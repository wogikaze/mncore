---
title: 3.5.8.8 PDM→PDM単独個別転送命令
id: 66b35ffe9453fb001c212d12
created_unix: 1723031550
updated_unix: 1771442199
views: 23
---

# 3.5.8.8 PDM→PDM単独個別転送命令

指定したグループの[[PDM]]から指定した異なるグループのPDMにデータをコピーする。
 単位動作は 64 長語である。
スループットは 8 長語/サイクルである。

```文法
mvp/n<size>[<tag>] $p<addr0>@<group0> $p<addr1>@<group1>

```
```効果
uint_t n=size / 64
for i= 0:n
  uint_t src_addr=addr0+ 64 * i
  uint_t dst_addr=addr1+ 64 * i
  LongWord data[64] = MEM[group0].pdm[src_addr:src_addr+64]
  MEM[group1].pdm[dst_addr:dst_addr+64] = data[0:64]

```
エラー
 sizeが単位動作 64 の倍数でないとエラーになる。

```例
mvp/n64 $p0@0 $p0@1
```
0 番グループのPDMから 1 番グループのPDMに 64 長語コピーする。

$ mvp/n64 $p0@0 $p0@1
 <https://gyazo.com/1a1496c8451598e7fe70b29efdd54bff>
