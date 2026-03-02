---
title: 3.6.7.5 l2bm@-L1BM→L2BM個別転送
id: 66b35ffe02bee8001d369bd8
created_unix: 1723031550
updated_unix: 1771442833
views: 26
---

# 3.6.7.5 l2bm@-L1BM→L2BM個別転送

指定した[[L1B番号]]の[[L1BM]]から、[[L2BM]]に 16 長語/サイクルで連続領域のコピーをする。

```文法
l2bm@<l1badr> $lb<addr_b> $lc<addr_c>
```
`<l1badr>`は 0 から 7 のL1B番号である。
読み出しアドレス`<addr_b>`と書き込みアドレス`<addr_c>`はいずれも 16 長語アラインである必要がある。


```効果
for cycle= 0:4
  forall group,l2b
    uint_t src_addr=addr_b +cycle* 16
    uint_t dst_addr=addr_c +cycle* 16
    LongWord data[16] = MEM[group][l2b][l1badr].l1bm[src_addr:src_addr+16]
    MEM[group][l2b].l2bm[dst_addr:dst_addr+16] = data[0:16]

```
```例
l2bm@1 $lb0 $lc0
```
1 番L1BMから計 64 長語をL2BMにコピーする。

$ l2bm@1 $lb0 $lc0
 <https://gyazo.com/29cdb0f2c63de108557f4e8e51e7553d>
