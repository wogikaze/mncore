---
title: 3.6.9.2 dmfma-倍精度行列ベクトル積和演算の基本動作
id: 66b35ffe3c1ad7001de55f93
created_unix: 1723031550
updated_unix: 1723546828
views: 21
---

# 3.6.9.2 dmfma-倍精度行列ベクトル積和演算の基本動作

あらかじめ[[行列レジスタ]]に書かれた行列データをAとして4次元の[[倍精度行列ベクトル積]][[FMA]] (Ax+y)を行う。
[[行列レジスタ]]から読み出した 4 行 4 列の[[ブロックフロート倍精度]]行列データのうち、後述する指定に応じて0,1行目あるいは2,3行目を抽出した 2 行 4 列の行列が使用される。

```文法
dmfma(u|d) $l(x|y) <src_x> <src_y> <dst_0> [<dst_1>..]


```
`(u|d)`は 4 行 4 列のうち上半分・下半分どちらの 2 行 4 列を演算に使用するかを指定するために用いられる。
 `u`を指定した場合はAの0,1行目をxと掛け合わせたものをAxの0,1要素目とし、Axの2,3要素目を 0 としてyとの加算を行う(以下効果においてoffset=0)。
 `d`を指定した場合はAの2,3行目をxと掛け合わせたものをAxの2,3要素目とし、Axの0,1要素目を 0 としてyとの加算を行う(以下効果においてoffset=2)。
第 1 入力の`$l(x|y)`は読み出し元の[[行列レジスタ]]であり、以下効果において[[side]]として参照する。
第 2 入力の`<src_x>`および第 3 入力の`<src_y>`は読み出し元[[PEオペランド]]である。
 <src_x>は[[ブロックフロート倍精度]]の値で[[アクセス語長]]は[[長語]]である。
 基本動作において`<src_y>`は通常の[[倍精度]]の値で、[[アクセス語長]]は[[長語]]である。
`<dst_0>` `[[<dst_1>..]]`は書き込み先[[PEオペランド]]である。
演算結果は複数の[[PEメモリ]]に同時に書き込むことができるが、以下効果では簡単のため単一の書き込み先として[[dst]]を指定した例を示している。
基本動作において演算結果は通常の[[倍精度]]であり、書き込みの[[アクセス語長]]は[[長語]]である。

```効果.py
for cycle = 0:4
  forall chip,l2b,l1b,mab
    LongWord src_data_A[4][4] = MEM[chip][l2b][l1b][mab].refer_matreg(side, LongWord)
    LongWord src_data_x[4] = MEM[chip][l2b][l1b][mab][0:4].refer_pemem(src_x,cycle)
    LongWord src_data_y[4] = MEM[chip][l2b][l1b][mab][0:4].refer_pemem(src_y,cycle)
    LongWord dst_data[4] = {0, 0, 0, 0}
    for i = 0:2
      for j = 0:4
      	dst_data[i + offset] += src_data_A[i + offset][j] * src_data_x[j]
    for i = 0:4
      dst_data[i] += src_data_y[i]
    MEM[chip][l2b][l1b][mab][0:4].refer_pemem(dst, cycle) = dst_data[0:4]


```
