---
title: 3.5.8.2 PDM→DRAM単独個別転送命令
id: 66b35ffe9453fb001c212d00
created_unix: 1723031550
updated_unix: 1771425352
views: 10
---

# 3.5.8.2 PDM→DRAM単独個別転送命令

指定したグループの[[PDM]]から指定したグループの[[DRAM]]にデータをコピーする。
単位動作は 64 長語である。
読み出し元と書き込み先のグループは同じでも別でもよい。
スループットはグループ内の場合 16 長語/サイクル、グループ間の場合 8 長語/サイクルである。
```文法
mvp/n<size>[<tag>] $p<addr_p>@<group_p> $d<addr_d>@<group_d>

```
```効果
uint_t n=size / 64
for i= 0:n
  uint_t src_addr=addr_p + 64 *i
  uint_t dst_addr=addr_d + 64 *i
  LongWord data[64] = MEM[group_p].pdm[src_addr:src_addr+64]
  MEM[group_d].dram[dst_addr:dst_addr+64] = data[0:64]

```
エラー
 sizeが単位動作 64 の倍数でないとエラーになる。

```例
mvp/n64 $p0@0 $d0@1
```
0 番グループのPDMから 1 番グループのDRAMに 64 長語コピーする。
$ mvp/n64 $p0@0 $d0@0
 <https://gyazo.com/533ec48a9c3504fdc93bb0abc2ded0f7>
$ mvp/n64 $p0@0 $d0@1
 <https://gyazo.com/e07518dab52645f50fa0cab138362574>
