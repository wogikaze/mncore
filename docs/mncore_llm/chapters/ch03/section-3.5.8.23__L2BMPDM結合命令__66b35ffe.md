---
title: 3.5.8.23 L2BM→PDM結合命令
id: 66b35ffe3c1ad7001de55f5a
created_unix: 1723031550
updated_unix: 1771433441
views: 8
---

# 3.5.8.23 L2BM→PDM結合命令

全[[L2B]]から読み出したデータを結合して指定したグループの[[PDM]]に書き込む。
単位動作はL2BM側 64 長語、PDM側 512 長語である。結合方法は 16 長語単位で 0 から 7 の[[L2B通し番号方向]]に[[ラウンドロビン]]である。
 詳細は効果のパートを参照のこと。

スループットはL2BM側 1 長語/サイクル、PDM側 8 長語/サイクルである。
```文法
mvd/n<size>[<tag>] $lc<addr_c> $p<addr_p>@<group_p>

```
```効果
uint_t n=size / 64
for i= 0:n
  uint_t src_offset= addr_c+ 64 * i
  uint_t dst_addr=addr_p + 512 *i
  LongWord buf[512]
  for j= 0:4
    forall group,l2b
      uint_t src_addr =src_offset +j* 16
      uint_t buf_addr = (j* 8 + group* 2 +l2b) * 16
      buf[buf_addr:buf_addr+16] = MEM[group][l2b].l2bm[src_addr:src_addr+16]
    MEM[group_p].pdm[dst_addr:dst_addr+512] =buf[0:512]


```
エラー
 sizeが単位動作 64 の倍数でないとエラーになる。

```例
mvd/n64 $lc0 $p0@0
```
各L2BMから 64 長語ずつ読んで結合した 512 長語を 0 番グループのPDMに書き込む。

$ mvd/n64 $lc0 $p0@0
 <https://gyazo.com/c1cb6c7e09117d6f974f2d23c04d0617>
