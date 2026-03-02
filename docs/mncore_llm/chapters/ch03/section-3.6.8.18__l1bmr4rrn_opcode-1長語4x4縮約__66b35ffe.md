---
title: 3.6.8.18 l1bmr4<rrn_opcode>-1長語4x4縮約
id: 66b35ffe3c1ad7001de55f81
created_unix: 1723031550
updated_unix: 1771439893
views: 11
---

# 3.6.8.18 l1bmr4<rrn_opcode>-1長語4x4縮約

各[[L1BM]]について、各[[MAB]]配下の4PEからサイクルあたり 1 長語ずつを読み出し、
 PE方向には結合し、[[3.6.8.1 4x4モードについて]]で述べた対応でMABに対して[[縮約]]と[[結合]]を行ってL1BMにサイクルあたり 16 長語で書き込む。

```文法
l1bmr4<rrn_opcode> <src>$lb<addr_b> 
```
`<rrn_opcode>`は[[3.5.5 縮約演算指定]]で定めた[[縮約演算指定]]である。
 `<src>`は読み出し元[[PEオペランド]]である。
 [[L1BMアドレス]]`<addr_b>`は 16 長語アラインである必要がある。

```効果
for cycle= 0:4
  forall group,l2b,l1b
    LongWord data[16]
    data[:] = get_unit_value(rrn_opcode)
    forall mab,pe
      uint_t idx= (mab>> 2) * 4 +pe
      data[idx] =rrn_opcode(data[idx], MEM[group][l2b][l1b][mab][pe].refer_pemem(src,cycle))
    uint_t dst_addr=addr_b +cycle* 16
    MEM[group][l2b][l1b].l1bm[dst_addr:dst_addr+16] =data[0:16]


```
注意：縮約を内部的に実際にこの手順で行っているわけではない。

$ l1bmr4 $lp0 $lb0
 <https://gyazo.com/8f3f08360d7b09217211fe237954f289>
