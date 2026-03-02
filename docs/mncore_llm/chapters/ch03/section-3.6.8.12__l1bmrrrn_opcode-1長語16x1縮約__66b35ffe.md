---
title: 3.6.8.12 l1bmr<rrn_opcode>-1長語16x1縮約
id: 66b35ffe9453fb001c212d57
created_unix: 1723031550
updated_unix: 1771439857
views: 22
---

# 3.6.8.12 l1bmr<rrn_opcode>-1長語16x1縮約

各[[L1BM]]について、各[[MAB]]配下の4PEから[[サイクル]]あたり 1 長語ずつを読み出し、[[MAB]]方向には縮約、PE方向には結合して[[L1BM]]に[[サイクル]]あたり 4 長語で書き込む。

```文法
l1bmr<rrn_opcode> <src> $lb<addr_b>
```
`<rrn_opcode>`は[[3.5.5 縮約演算指定]]で定めた[[縮約演算指定]]である。
`<src>`は読み出し元PEオペランドである。
L1BMアドレス`<addr_b>`は 4 長語アラインである必要がある。

```効果
for cycle= 0:4
  forall group,l2b,l1b
    LongWord data[4]
    data[:] = get_unit_value(rrn_opcode)
    forall mab,pe
      data[pe] =rrn_opcode(data[pe],MEM[group][l2b][l1b][mab][pe].refer_pemem(src,cycle))
      uint_t dst_addr=addr_b +cycle* 4
      MEM[group][l2b][l1b].l1bm[dst_addr:dst_addr+4] =data[0:4]

```
注意：縮約を内部的に実際にこの手順で行っているわけではない。

$ l1bmr $lp0 $lb0
 <https://gyazo.com/0dd32c795b6d14fdb675d3fc2e092eab>
