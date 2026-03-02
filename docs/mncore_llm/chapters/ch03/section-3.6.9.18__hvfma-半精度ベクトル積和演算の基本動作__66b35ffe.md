---
title: 3.6.9.18 hvfma-半精度ベクトル積和演算の基本動作
id: 66b35ffe48094e001dcdddb0
created_unix: 1723031550
updated_unix: 1771399388
views: 25
---

# 3.6.9.18 hvfma-半精度ベクトル積和演算の基本動作

[[MAB]]内で[[半精度ベクトル積和演算]][[FMA]] (x*y+z)を行う。
```文法
hvfma <src_x> <src_y> <src_z> <dst_0> [<dst_1>..]

```
第 1 入力の`<src_x>`、第 2 入力の`<src_y>`、および第 3 入力の`<src_z>`は読み出し元[[PEオペランド]]である。

基本動作において`<src_x>`および`<src_y>`は通常の[[半精度]]の値で、[[アクセス語長]]は[[長語]]である。
基本動作において`<src_z>`は通常の[[単精度]]の値で、[[アクセス語長]]は 2 [[長語]]である。
 `<dst_0>` `[[<dst_1>..]]`は書き込み先[[PEオペランド]]である。

演算結果は複数の[[PEメモリ]]に同時に書き込むことができるが、以下効果では簡単のため単一の書き込み先として[[dst]]を指定した例を示している。
基本動作において演算結果は通常の[[単精度]]であり、書き込みの[[アクセス語長]]は 2 [[長語]]である。

```効果.py
for cycle = 0:4
  forall chip,l2b,l1b,mab,pe
    HalfWord src_data_x[4] = MEM[chip][l2b][l1b][mab][pe].refer_pemem(src_x,cycle)
    HalfWord src_data_y[4] = MEM[chip][l2b][l1b][mab][pe].refer_pemem(src_y,cycle)
    ShortWord src_data_z[4] = MEM[chip][l2b][l1b][mab][pe].refer_pemem(src_z, cycle)
    ShortWord dst_data[4] = src_data_x[:] * src_data_y[:] + src_data_z[:]
    MEM[chip][l2b][l1b][mab][pe].refer_pemem(dst,cycle) = dst_data[:]

```
[[hvfma]]
