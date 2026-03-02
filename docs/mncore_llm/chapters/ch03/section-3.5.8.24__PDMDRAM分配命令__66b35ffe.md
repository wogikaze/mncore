---
title: 3.5.8.24 PDM→DRAM分配命令
id: 66b35ffe3c1ad7001de55f5d
created_unix: 1723031550
updated_unix: 1771432595
views: 11
---

# 3.5.8.24 PDM→DRAM分配命令

指定したグループの[[PDM]]から読み出したデータを 4 分割して各グループの[[DRAM]]に書き込む。
単位動作はPDM側 64 長語、DRAM側 16 長語である。
スループットはPDM側 8 長語/サイクル、DRAM側 2 長語/サイクルである。

```文法
mvd/n<size>[<tag>] $p<addr_p>@<group_p> $d<addr_d>

```
```効果
uint_t n=size / 64
for i= 0:n
  uint_t src_addr=addr_p + 64 *i
  uint_t dst_addr=addr_d + 16 *i
  LongWord buf[64] =MEM[group_p].pdm[src_addr:src_addr+64]
  forall group
    uint_t buf_addr=group* 16
    MEM[group].dram[dst_addr:dst_addr+16] = buf[buf_addr:buf_addr+16]

```
エラー
 sizeが単位動作 64 の倍数でないとエラーになる。

```例
mvd/n64 $p0@0 $d0
```
0 番グループのPDMから 64 長語を読み出して各DRAMに 16 長語ずつ書き込む。

$ mvd/n64 $p0@0 $d0
 <https://gyazo.com/53a8811914e9b194f66905c02b6a281f>
