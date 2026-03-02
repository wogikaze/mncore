---
title: 3.6.7.4 l2bmd-L2BM→L1BM分配
id: 66b35ffe02bee8001d369bd5
created_unix: 1723031550
updated_unix: 1771433811
views: 5
---

# 3.6.7.4 l2bmd-L2BM→L1BM分配

[[L2BM]]から 64 長語/サイクルで連続領域を読み、配下のすべての[[L1BM]]に 8 長語/サイクルずつ[[分配]]をして連続領域に書き込む。

```文法
l2bmd[@<l1bset>] $lc<addr_c> $lb<addr_b>
```
`@`以降は[[3.6.7.1 L1B部分集合指定]]で定めた[[L1B集合]]の指定であり、これに含まれるL1Bのみで書き込みが行われる。
 省略時は全L1Bに書き込みが行われる。
読み出しアドレス`<addr_c>`は 64 長語アライン、書き込みアドレス`<addr_b>`は 8 長語アラインである必要がある。

```効果
for cycle= 0:4
  forall group,l2b
    uint_t src_addr=addr_c +cycle* 64
    uint_t dst_addr=addr_b +cycle* 8
    LongWord data[64] = MEM[group][l2b].l2bm[src_addr:src_addr+64]
    for l1b in l1bset
      uint_t data_addr = 8 *l1b
      MEM[group][l2b][l1b].l1bm[dst_addr:dst_addr+8] =data[data_addr:data_addr+8]

```
```txt
l2bmd@[0,1,2,3] $lc0 $lb0
```
L2BMから計 256 長語を読み出し、0,1,2,3番L1BMに異なる 32 長語ずつのデータを書き込む(4,5,6,7番L1BMに対応するデータは捨てられることになる)。

$ l2bmd@[[0,1,2,3]] $lc0 $lb0
 <https://gyazo.com/49b28c757bedabeb77e1f5d9667ca85f>
