---
title: 3.6.7.2 l2bmb-L2BM→L1BM放送
id: 66b35ffe02bee8001d369bcf
created_unix: 1723031550
updated_unix: 1771433878
views: 8
---

# 3.6.7.2 l2bmb-L2BM→L1BM放送

[[L2BM]]から、配下のすべてまたは一部の[[L1BM]]に 16 長語/サイクルで連続領域のコピーをする。

```文法
l2bmb[@<l1bset>] $lc<addr_c> $lb<addr_b>
```
`@`以降は[[3.6.7.1 L1B部分集合指定]]で定めた[[L1B集合]]の指定であり、これに含まれるL1Bのみで書き込みが行われる。
 省略時は全L1Bに書き込みが行われる。
読み出しアドレス`<addr_c>`と書き込みアドレス`<addr_b>`はいずれも 16 長語アラインである必要がある。

```効果
for cycle= 0:4
  forall group,l2b
    uint_t src_addr=addr_c +cycle* 16
    uint_t dst_addr=addr_b +cycle* 16
    LongWord data[16] = MEM[group][l2b].l2bm[src_addr:src_addr+16]
    for l1b in l1bset
      MEM[group][l2b][l1b].l1bm[dst_addr:dst_addr+16] =data[0:16]

```
```例
l2bmb@[0,1,2,3] $lc0 $lb0
```
L2BMから計 64 長語を0,1,2,3番L1BMのみに[[放送]]する。


$ l2bmb@[[1,3,5,7]] $lc0 $lb0
 <https://gyazo.com/ffa4db542786178575e10a56e2610f9b>
