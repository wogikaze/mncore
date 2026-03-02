---
title: 3.6.8.9 l1bmm-2長語16x1MAB放送
id: 66b35ffe9453fb001c212d4e
created_unix: 1723031550
updated_unix: 1771438880
views: 16
---

# 3.6.8.9 l1bmm-2長語16x1MAB放送

[[L1BM]]から[[サイクル]]あたり 8 長語を読み出し、配下の 16 個の[[MAB]]全てに放送し、 8 長語を4PEに分配して 2 長語を書き込む。


```文法
l1bmm $llb<addr_b> <dst_0> [<dst_1>..]

```
`<dst_0> [[<dst_1>..]]`は書き込み先PEオペランドである。
 L1BMアドレス`<addr_b>`は 8 長語アラインである必要がある。


```効果
for cycle= 0:4
  forall group,l2b,l1b
    uint_t src_addr=addr_b +cycle* 8
    LongWord data[4][2]
    data[0:4][0] = MEM[group][l2b][l1b].l1bm[src_addr:src_addr+4]
    data[0:4][1] = MEM[group][l2b][l1b].l1bm[src_addr+4:src_addr+8]
    forall mab,pe
      MEM[group][l2b][l1b][mab][pe].refer_pemem(dst,cycle) =data[pe][0:2]

```
$ l1bmm $llb0 $llp0
 <https://gyazo.com/a5bd2ceb957bf6da3990d32a70e78e62>
