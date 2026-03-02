---
title: 3.5.8.22 PDM→L2BM分配命令
id: 66b35ffe3c1ad7001de55f57
created_unix: 1723031550
updated_unix: 1771433138
views: 5
---

# 3.5.8.22 PDM→L2BM分配命令

指定したグループの[[PDM]]から読み出したデータを 8 分割して各グループの[[L2BM]]に書き込む。
単位動作はPDM側 512 長語、L2BM側 64 長語である。
分割方法は 16 長語単位で 0 から 7 の[[L2B通し番号方向]]に[[ラウンドロビン]]である。
 詳細は効果のパートを参照のこと。
スループットはPDM側 8 長語/サイクル、L2BM側 1 長語/サイクルである。

```文法
mvd/n<size>[<tag>] $p<addr_p>@<group_p> $lc<addr_c>

```
```効果
uint_t n=size / 64
for i= 0:n
  uint_t src_addr=addr_p + 512 *i
  uint_t dst_offset= addr_c+ 64 * i
  LongWord buf[512] =MEM[group_p].pdm[src_addr:src_addr+512]
  for j= 0:4
    forall group,l2b
      uint_t buf_addr = (j* 8 + group* 2 +l2b) * 16
      uint_t dst_addr =dst_offset +j* 16
      MEM[group][l2b].l2bm[dst_addr:dst_addr+16] = buf[buf_addr:buf_addr+16]

```
エラー
 sizeが単位動作 64 の倍数でないとエラーになる。

```例
mvd/n64 $p0@0 $lc0
```
0 番グループのPDMから 512 長語を読んで各L2BMに 64 長語ずつ書き込む。

$ mvd/n64 $p0@0 $lc0
 <https://gyazo.com/80467397b2f2c90bf8e19bcfc0ed9c74>
