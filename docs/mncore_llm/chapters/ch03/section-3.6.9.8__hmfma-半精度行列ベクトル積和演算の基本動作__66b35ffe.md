---
title: 3.6.9.8 hmfma-半精度行列ベクトル積和演算の基本動作
id: 66b35ffe48094e001dcddda4
created_unix: 1723031550
updated_unix: 1724425713
views: 31
---

# 3.6.9.8 hmfma-半精度行列ベクトル積和演算の基本動作

あらかじめ[[行列レジスタ]]に書かれた行列データをAとして 16 次元の[[半精度行列ベクトル積]][[FMA]] (Ax+y)を行う。

```文法
hmfma $l(x|y) <src_x> <src_y> <dst_0> [<dst_1>..]

```
第 1 入力の`$l(x|y)`は読み出し元の[[行列レジスタ]]であり、以下効果において[[side]]として参照する。
第 2 入力の`<src_x>`および第 3 入力の`<src_y>`は読み出し元[[PEオペランド]]である。
 `<src_x>`は[[ブロックフロート半精度]]の値で[[アクセス語長]]は[[長語]]である。
 基本動作において`<src_y>`は通常の[[単精度]]の値で、[[アクセス語長]]は 2 [[長語]]である。
 `<dst_0>` `[[<dst_1>..]]`は書き込み先[[PEオペランド]]である。

演算結果は複数の[[PEメモリ]]に同時に書き込むことができるが、以下効果では簡単のため単一の書き込み先として[[dst]]を指定した例を示している。
基本動作において演算結果は通常の[[単精度]]であり、書き込みの[[アクセス語長]]は 2 [[長語]]である。

```効果.py
for cycle = 0:4
  forall chip,l2b,l1b,mab
    HalfWord src_data_A[16][16] = MEM[chip][l2b][l1b][mab].refer_matreg(side,HalfWord)
    HalfWord src_data_x[4][4] = MEM[chip][l2b][l1b][mab][0:4].refer_pemem(src_x,cycle)
    ShortWord src_data_y[4][4] = MEM[chip][l2b][l1b][mab][0:4].refer_pemem(src_y, cycle)
    ShortWord dst_data[16] = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    for i= 0:16
      for j = 0:16
        dst_data[i] += src_data_A[i][j] *src_data_x[j/4][j%4]
        dst_data[i] += src_data_y[i/4][i%4]
    forall pe
      MEM[chip][l2b][l1b][mab][pe].refer_pemem(dst,cycle) = dst_data[pe*4:(pe+1)*4]


```
