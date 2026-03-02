---
title: 3.6.9.14 fvfma-単精度ベクトル積和演算の基本動作
id: 66b35ffe48094e001dcdddad
created_unix: 1723031550
updated_unix: 1771399351
views: 20
---

# 3.6.9.14 fvfma-単精度ベクトル積和演算の基本動作

[[MAB]]内で[[単精度ベクトルFMA]] (x*y+z)を行う。

```文法
fvfma <src_x> <src_y> <src_z> <dst_0> [<dst_1>..]

```
第 1 入力の`<src_x>`、第 2 入力の`<src_y>`、および第 3 入力の`<src_z>`は読み出し元[[PEオペランド]]である。基本動作においていずれも通常の[[単精度]]の値で、[[アクセス語長]]は[[長語]]である。
 `<dst_0>` `[[<dst_1>..]]`は書き込み先[[PEオペランド]]である。

演算結果は複数の[[PEメモリ]]に同時に書き込むことができるが、以下効果では簡単のため単一の書き込み先として[[dst]]を指定した例を示している。
基本動作において演算結果は通常の[[単精度]]であり、書き込みの[[アクセス語長]]は[[長語]]である。

```効果.py
for cycle= 0:4
  forall chip,l2b,l1b,mab,pe
    ShortWord src_data_x[2] = MEM[chip][l2b][l1b][mab][pe].refer_pemem(src_x, cycle)
    ShortWord src_data_y[2] = MEM[chip][l2b][l1b][mab][pe].refer_pemem(src_y,cycle)
    ShortWord src_data_z[2] = MEM[chip][l2b][l1b][mab][pe].refer_pemem(src_z,cycle)
    ShortWord dst_data[2] =src_data_x[:] * src_data_y[:] +src_data_z[:]
    MEM[chip][l2b][l1b][mab][pe].refer_pemem(dst, cycle) =dst_data[:]


```
[[fvfma]]
