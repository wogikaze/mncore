---
title: 3.6.8.13 l1bmr<rrn_opcode>-2長語16x1縮約
id: 66b35ffe9453fb001c212d5a
created_unix: 1723031550
updated_unix: 1771439870
views: 25
---

# 3.6.8.13 l1bmr<rrn_opcode>-2長語16x1縮約

各[[L1BM]]について、各[[MAB]]配下の4PEから[[サイクル]]あたり 2 長語ずつを読み出し、[[MAB]]方向には縮約、PE方向には結合して[[L1BM]]に[[サイクル]]あたり 8 長語で書き込む。
 2 長語動作は[[単精度]]の[[浮動小数点数演算]]または任意精度の[[bor]]についてのみ可能である。
 この命令は[[3.6.8.4 入力の精度拡張]]で述べた、[[半精度]]から[[単精度]]への入力値変換つきの動作を指定可能である。

```文法
l1bmr<rrn_opcode> <src> $llb<addr_b>
```
`<rrn_opcode>`は[[3.5.5 縮約演算指定]]で定めた縮約演算指定である。
`<src>`は読み出し元[[PEオペランド]]である。
[[L1BMアドレス]]`<addr_b>`は 8 長語アラインである必要がある。

```効果
for cycle= 0:4
  forall group,l2b,l1b
    LongWord data[4][2]
    data[:][:] =get_unit_value(rrn_opcode)
    forall mab,pe
      data[pe][0:2] =rrn_opcode(data[pe][0:2],MEM[group][l2b][l1b][mab][pe].refer_pemem(src,cycle))
      uint_t dst_addr=addr_b +cycle* 8
      MEM[group][l2b][l1b].l1bm[dst_addr:dst_addr+4] =data[0:4][0]
      MEM[group][l2b][l1b].l1bm[dst_addr+4:dst_addr+8] =data[0:4][1]
    

```
注意：縮約を内部的に実際にこの手順で行っているわけではない。

$ l1bmr $llp0 $llb0
 <https://gyazo.com/44ecb6f6bc7446c9a0878a55da280c58>
