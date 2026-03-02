---
title: 3.6.8.15 l1bmm4-2長語4x4MAB放送
id: 66b35ffe9453fb001c212d60
created_unix: 1723031550
updated_unix: 1771439223
views: 36
---

# 3.6.8.15 l1bmm4-2長語4x4MAB放送

[[L1BM]]から[[サイクル]]あたり 32 長語を読み出し、[[3.6.8.1 4x4モードについて]]で述べた対応で[[MAB]]に対して分配と放送を行い、分配後の 8 長語をさらに4PEに分配して 2 長語を書き込む。

```文法
l1bmm4 $llb<addr_b> <dst_0> [<dst_1>..]
```
`<dst_0> [[<dst_1>..]]`は書き込み先[[PEオペランド]]である。
 [[L1BMアドレス]]`<addr_b>`は 32 長語アラインである必要がある。


```効果
for cycle= 0:4
  forall group,l2b,l1b
    uint_t src_addr=addr_b +cycle* 32
    LongWord data[16][2]
    for i= 0:4
      data[i*4:(i+1)*4][0] =MEM[group][l2b][l1b].l1bm[src_addr+i*8:src_addr+i*8+4]
      data[i*4:(i+1)*4][1] =MEM[group][l2b][l1b].l1bm[src_addr+i*8+4:src_addr+i*8+8]
      forall mab,pe
        uint_t idx= (mab>> 2) * 4 +pe
        MEM[group][l2b][l1b][mab][pe].refer_pemem(dst,cycle) =data[idx][0:2]      

```
$ l1bmm4 $llb0 $llp0
 <https://gyazo.com/77a6bc59f462f442642da7d6627c8054>
