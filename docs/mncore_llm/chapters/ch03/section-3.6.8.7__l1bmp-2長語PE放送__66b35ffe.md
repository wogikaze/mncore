---
title: 3.6.8.7 l1bmp-2長語PE放送
id: 66b35ffe9453fb001c212d48
created_unix: 1723031550
updated_unix: 1771438516
views: 18
---

# 3.6.8.7 l1bmp-2長語PE放送

[[L1BM]]から[[サイクル]]あたり 2 長語を読み出し、配下の 64 個のPE全てに放送する。

対称な[[PE→L1BM]]方向の転送命令は存在しない。

```文法
l1bmp $llb<addr_b> <dst_0> [<dst_1>..]


```
`<dst_0> [[<dst_1>..]]`は書き込み先[[PEオペランド]]である。
 [[L1BM]]側の[[アラインメント]]制約は存在しないが、[[アドレス]]の下位 6 ビットの値は 0 から 56 のいずれかでなければならない。

```効果
for cycle= 0:4
  forall group,l2b,l1b
    uint_t src_addr=addr_b +cycle
    LongWord data[2]
    data[0] = MEM[group][l2b][l1b].l1bm[src_addr]
    data[1] = MEM[group][l2b][l1b].l1bm[src_addr+4]
    forall mab,pe
      MEM[group][l2b][l1b][mab][pe].refer_pemem(dst,cycle) =data[0:2]


```
サイクル内のL1BMの読み出し領域が不連続なので注意する。

$ l1bmp $llb0 $llp0
 <https://gyazo.com/ed25d30485c2a417799a42ec965ab7d6>
