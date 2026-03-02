---
title: 3.5.8.25 DRAM→PDM結合命令
id: 66b35ffe3c1ad7001de55f60
created_unix: 1723031550
updated_unix: 1771432731
views: 5
---

# 3.5.8.25 DRAM→PDM結合命令

各グループの[[DRAM]]から読み出したデータを結合して指定したグループの[[PDM]]に書き込む。
 単位動作はDRAM側 16 長語、PDM側 64 長語である。
スループットはDRAM側 2 長語/サイクル、PDM側 8 長語/サイクルである。

```文法
mvd/n<size>[<tag>] $d<addr_d> $p<addr_p>@<group_p>

```
```効果
uint_t n=size / 64
for i= 0:n
  uint_t src_addr=addr_d + 16 *i
  uint_t dst_addr=addr_p + 64 *i
  LongWord buf[64]
  forall group
    uint_t buf_addr=group* 16
    buf[buf_addr:buf_addr+16] = MEM[group].dram[src_addr:src_addr+16]
    MEM[group_p].pdm[dst_addr:dst_addr+64] = buf[0:64]

```
エラー
 sizeが単位動作 64 の倍数でないとエラーになる。

```例
mvd/n64 $d0 $p0@0
```
各DRAMから 16 長語ずつ読み出し、結合して 0 番グループのPDMに 64 長語を書き込む。

$ mvd/n64 $d0 $p0@0
 <https://gyazo.com/33c9450235e09a0c4bceacdd7cb674b8>
