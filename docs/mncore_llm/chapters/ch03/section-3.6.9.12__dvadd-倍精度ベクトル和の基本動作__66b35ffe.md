---
title: 3.6.9.12 dvadd-倍精度ベクトル和の基本動作
id: 66b35ffe48094e001dcdddaa
created_unix: 1723031550
updated_unix: 1724425726
views: 21
---

# 3.6.9.12 dvadd-倍精度ベクトル和の基本動作

MAB内で[[倍精度ベクトル和]](x+y)を行う。
```文法
dvadd <src_x> <src_y> <dst_0> [<dst_1>..]

```
第 1 入力の`<src_x>`および第 2 入力の`<src_y>`は読み出し元[[PEオペランド]]である。

基本動作においていずれも通常の[[倍精度]]の値で、[[アクセス語長]]は[[長語]]である。
`<dst_0>` `[[<dst_1>..]]`は書き込み先[[PEオペランド]]である。
 演算結果は複数の[[PEメモリ]]に同時に書き込むことができるが、
 以下効果では簡単のため単一の書き込み先として[[dst]]を指定した例を示している。

基本動作において演算結果は通常の[[倍精度]]であり、書き込みのアクセス語長は[[長語]]である。

```効果
for cycle= 0:4
  forall chip,l2b,l1b,mab,pe
    LongWord src_data_x=MEM[chip][l2b][l1b][mab][pe].refer_pemem(src_x,cycle)
    LongWord src_data_y=MEM[chip][l2b][l1b][mab][pe].refer_pemem(src_y,cycle)
    LongWord dst_data= src_data_x+ src_data_y
    MEM[chip][l2b][l1b][mab][pe].refer_pemem(dst,cycle) =dst_data

```
