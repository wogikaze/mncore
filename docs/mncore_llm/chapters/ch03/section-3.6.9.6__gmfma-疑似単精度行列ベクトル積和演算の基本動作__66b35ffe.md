---
title: 3.6.9.6 gmfma-疑似単精度行列ベクトル積和演算の基本動作
id: 66b35ffe3c1ad7001de55f99
created_unix: 1723031550
updated_unix: 1724425705
views: 40
---

# 3.6.9.6 gmfma-疑似単精度行列ベクトル積和演算の基本動作

あらかじめ[[行列レジスタ]]に書かれた行列データをAとして 8 次元の[[疑似単精度行列ベクトル積]][[FMA]] (Ax+y)を行う。

```文法
gmfma $l(x|y) <src_x> <src_y> <dst_0> [<dst_1>..] 

```
第 1 入力の`$l(x|y)`は読み出し元の[[行列レジスタ]]であり、以下効果において[[side]]として参照する。
第 2 入力の`<src_x>`および第 3 入力の`<src_y>`は読み出し元[[PEオペランド]]である。`<src_x>`は[[ブロックフロート疑似単精度]]の値で[[アクセス語長]]は[[長語]]である。基本動作において`<src_y>`は通常の[[単精度]]の値で、アク
セス[[語]]長は[[長語]]である。
`<dst_0>` `[[<dst_1>..]]`は書き込み先[[PEオペランド]]である。演算結果は複数の[[PEメモリ]]に同時に書き込
むことができるが、以下効果では簡単のため単一の書き込み先として[[dst]]を指定した例を示している。基本動
作において演算結果は通常の[[単精度]]であり、書き込みの[[アクセス語長]]は[[長語]]である。

```効果.py
for cycle= 0:4
  forall chip,l2b,l1b,mab
    ShortWord src_data_A[8][8] =MEM[chip][l2b][l1b][mab].refer_matreg(side, ShortWord)
    ShortWord src_data_x[4][2] =MEM[chip][l2b][l1b][mab][0:4].refer_pemem(src_x, cycle)
    ShortWord src_data_y[4][2] =MEM[chip][l2b][l1b][mab][0:4].refer_pemem(src_y, cycle)
    ShortWord dst_data[8] = {0, 0, 0, 0, 0, 0, 0, 0}
    for i= 0:8
      for j = 0:8
        dst_data[i] +=src_data_A[i][j] *src_data_x[j/2][j%2]
        dst_data[i] +=src_data_y[i/2][i%2]
    forall pe
      MEM[chip][l2b][l1b][mab][pe].refer_pemem(dst,cycle) =dst_data[pe*2:(pe+1)*2]


```
