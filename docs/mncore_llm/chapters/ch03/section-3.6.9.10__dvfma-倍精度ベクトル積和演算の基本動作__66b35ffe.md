---
title: 3.6.9.10 dvfma-倍精度ベクトル積和演算の基本動作
id: 66b35ffe48094e001dcddda7
created_unix: 1723031550
updated_unix: 1771399383
views: 27
---

# 3.6.9.10 dvfma-倍精度ベクトル積和演算の基本動作

[[MAB]]内で[[倍精度ベクトル]][[FMA]] ([[$ x*y+z]])を行う。
```文法
dvfma(u|d) <src_x> <src_y> <src_z> <dst_0> [<dst_1>..]
```
`(u|d)`は 4 個の[[PE]]のうち[[PE0]],[[PE1]]または[[PE2]],[[PE3]]どちらの2PEの要素について乗算を行うかを指
定する。
 `u`を指定した場合は[[PE0]],[[PE1]]でxとyと掛け合わせたものを[[$ x* y]]の中間結果とし、[[PE2]],[[PE3]]では[[$ x*y]]の中間結果を便宜的に 0 として、zとの加算を行う(以下効果においてoffset=0)。
 `d`を指定した場合は[[PE2]],[[PE3]]でxとyと掛け合わせたものを[[$ x*y]]の中間結果とし、[[PE0]],[[PE1]]では[[$ x*y]]の中間結果を便宜的に 0 として、zとの加算を行う(以下効果においてoffset=2)。

第 1 入力の`<src_x>`、第 2 入力の`<src_y>`、および第 3 入力の`<src_z>`は読み出し元[[PEオペランド]]である。
 基本動作においていずれも通常の[[倍精度]]の値で、[[アクセス語長]]は[[長語]]である。
`<dst_0>` `[[<dst_1>..]]`は書き込み先[[PEオペランド]]である。
 演算結果は複数の[[PEメモリ]]に同時に書き込むことができるが、以下効果では簡単のため単一の書き込み先として[[dst]]を指定した例を示している。
 基本動作において演算結果は通常の[[倍精度]]であり、書き込みの[[アクセス語長]]は[[長語]]である。

```効果.py
for cycle= 0:4
  forall chip,l2b,l1b,mab
    LongWord dst_data[4] = {0, 0, 0, 0}
    for i= 0:2
      LongWord src_data_x = MEM[chip][l2b][l1b][mab][i+ offset].refer_pemem(src_x,cycle)
      LongWord src_data_y = MEM[chip][l2b][l1b][mab][i+ offset].refer_pemem(src_y,cycle)
      dst_data[i+ offset] = src_data_x * src_data_y
    forall pe
      LongWord src_data_z = MEM[chip][l2b][l1b][mab][pe].refer_pemem(src_z,cycle)
      dst_data[pe] += src_data_z
      MEM[chip][l2b][l1b][mab][pe].refer_pemem(dst,cycle) = dst_data[pe]

```
[[dvfma]]
