---
title: 3.6.8.14 l1bmm4-1長語4x4MAB放送
id: 66b35ffe9453fb001c212d5d
created_unix: 1723031550
updated_unix: 1771439180
views: 30
---

# 3.6.8.14 l1bmm4-1長語4x4MAB放送

[[L1BM]]から[[サイクル]]あたり 16 長語を読み出し、[[3.6.8.1 4x4モードについて]]で述べた対応で[[MAB]]に対して分配と放送を行い、分配後の 4 長語をさらに4PEに分配して 1 長語を書き込む。

```文法
l1bmm4 $lb<addr_b> <dst_0> [<dst_1>..]
```
`<dst_0> [[<dst_1>..]]`は書き込み先[[PEオペランド]]である。
 [[L1BMアドレス]]`<addr_b>`は 16 長語アラインである必要がある。

```効果
for cycle= 0:4
  forall group,l2b,l1b
    uint_t src_addr=addr_b +cycle* 16
    LongWord data[16] = MEM[group][l2b][l1b].l1bm[src_addr:src_addr+16]
    forall mab,pe
      uint_t idx= (mab>> 2) * 4 +pe
      MEM[group][l2b][l1b][mab][pe].refer_pemem(dst,cycle) =data[idx]

```
$ l1bmm4 $lb0 $lp0
 <https://gyazo.com/d4e7f2bad545cece5030f06d0e84d561>
