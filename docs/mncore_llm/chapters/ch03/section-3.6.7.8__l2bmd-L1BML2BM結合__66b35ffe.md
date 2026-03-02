---
title: 3.6.7.8 l2bmd-L1BM→L2BM結合
id: 66b35ffe306631001da24555
created_unix: 1723031550
updated_unix: 1771442649
views: 26
---

# 3.6.7.8 l2bmd-L1BM→L2BM結合

各[[L2BM]]について、配下のすべての[[L1BM]]から 8 長語/サイクルずつ連続領域を読み出して[[結合]]し、L2BMの連続領域に 64 長語/サイクルで書き込む。

[[3.6.7.4 l2bmd-L2BM→L1BM分配]]で述べた[[L2BM→L1BM分配命令]]と対になっている。

```文法
l2bmd $lb<addr_b> $lc<addr_c>
```
読み出しアドレス`<addr_b>`は 8 長語アライン、書き込みアドレス`<addr_c>`は 64 長語アラインである必要がある。


```効果
for cycle= 0:4
  forall group,l2b
    uint_t src_addr=addr_b +cycle* 8
    uint_t dst_addr=addr_c +cycle* 64
    LongWord data[64]
    forall l1b
      uint_t data_addr = 8 *l1b
      data[data_addr:data_addr+8] = MEM[group][l2b][l1b].l1bm[src_addr:src_addr+8]
      MEM[group][l2b].l2bm[dst_addr:dst_addr+64] = data[0:64]

```
```例
l2bmd $lb0 $lc0
```
L1BMから各 32 長語を読み出し、 8 長語単位で結合してL2BMに計 256 長語を書き込む。

$ l2bmd $lb0 $lc0
 <https://gyazo.com/f6d0e8bd68a01bcecd4d16ac2f3c187d>
