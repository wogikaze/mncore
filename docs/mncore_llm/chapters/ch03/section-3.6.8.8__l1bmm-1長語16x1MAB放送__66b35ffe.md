---
title: 3.6.8.8 l1bmm-1長語16x1MAB放送
id: 66b35ffe9453fb001c212d4b
created_unix: 1723031550
updated_unix: 1771438834
views: 14
---

# 3.6.8.8 l1bmm-1長語16x1MAB放送

[[L1BM]]から[[サイクル]]あたり 4 長語を読み出し、配下の 16 個の[[MAB]]全てに放送し、 4 長語を4PEに分配して 1 長語を書き込む。


```文法
l1bmm $lb<addr_b> <dst_0> [<dst_1>..]
```
`<dst_0> [[<dst_1>..]]`は書き込み先PEオペランドである。
 [[L1BMアドレス]]`<addr_b>`は 4 長語アラインである必要がある。

```効果
for cycle= 0:4
  forall group,l2b,l1b
    uint_t src_addr=addr_b +cycle* 4
    LongWord data[4] = MEM[group][l2b][l1b].l1bm[src_addr:src_addr+4]
    forall mab,pe
      MEM[group][l2b][l1b][mab][pe].refer_pemem(dst,cycle) =data[pe]

```
$ l1bmm $lb0 $lp0
 <https://gyazo.com/c27221409186eb17a0c600f9c47a6513>
