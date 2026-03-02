---
title: 3.6.8.6 l1bmp-1長語PE放送
id: 66b35ffe306631001da24570
created_unix: 1723031550
updated_unix: 1771438524
views: 34
---

# 3.6.8.6 l1bmp-1長語PE放送

[[L1BM]]から[[サイクル]]あたり 1 長語を読み出し、配下の 64 個の[[PE]]全てに放送する。
 対称な[[PE→L1BM]]方向の転送命令は存在しない。

```文法
l1bmp $lb<addr_b> <dst_0> [<dst_1>..]

```
`<dst_0> [[<dst_1>..]]`は書き込み先[[PEオペランド]]である。
 演算結果は複数の[[PEメモリ]]に同時に書き込むことができるが、以下効果では簡単のため単一の書き込み先として[[dst]]を指定した例を示している。
 これは以降のすべての[[L1BM命令式]]の記述について同様である。
 [[L1BM]]側の[[アラインメント]]制約は存在しない。


```効果
for cycle= 0:4
  forall group,l2b,l1b
    uint_t src_addr=addr_b +cycle
    LongWord data= MEM[group][l2b][l1b].l1bm[src_addr]
    forall mab,pe
      MEM[group][l2b][l1b][mab][pe].refer_pemem(dst,cycle) =data


```
$ l1bmp $lb0 $lp0
 <https://gyazo.com/61fdf59a772e28814beb48b41c8b0b06>
