---
title: 3.6.8.19 l1bmr4<rrn_opcode>-2長語4x4縮約
id: 66b35ffe3c1ad7001de55f84
created_unix: 1723031550
updated_unix: 1771439907
views: 14
---

# 3.6.8.19 l1bmr4<rrn_opcode>-2長語4x4縮約

各[[L1BM]]について、各[[MAB]]配下の4PEから[[サイクル]]あたり 2 長語ずつを読み出し、PE方向には結合し、[[3.6.8.1 4x4モードについて]]で述べた対応で[[MAB]]に対して縮約と結合を行って[[L1BM]]に[[サイクル]]あたり 32 長語で書き込む。

2 長語動作は[[単精度]]の[[浮動小数点数演算]]または任意精度の[[bor]]についてのみ可能である。
この命令は[[3.6.8.4 入力の精度拡張]]で述べた、[[半精度]]から[[単精度]]への入力値変換つきの動作を指定可能である。

```文法
l1bmr<rrn_opcode>  $llb<addr_b>

```
`<rrn_opcode>`は[[3.5.5 縮約演算指定]]で定めた[[縮約演算指定]]である。
`<src>`は読み出し元[[PEオペランド]]である。
[[L1BMアドレス]]`<addr_b>`は 32 長語アラインである必要がある。


```効果
for cycle= 0:4
  forall group,l2b,l1b
    LongWord data[16][2]
    data[:][:] =get_unit_value(rrn_opcode)
    forall mab,pe
      uint_t idx= (mab>> 2) * 4 +pe
      data[idx][0:2] =rrn_opcode(data[idx][0:2],MEM[group][l2b][l1b][mab][pe].refer_pemem(src,cycle))
      uint_t dst_addr=addr_b +cycle* 32
    for i= 0:4
      MEM[group][l2b][l1b].l1bm[dst_addr+i*8:dst_addr+i*8+4] =data[i*4:(i+1)*4][0]
      MEM[group][l2b][l1b].l1bm[dst_addr+i*8+4:dst_addr+i*8+8] =data[i*4:(i+1)*4][1]


```
注意：縮約を内部的に実際にこの手順で行っているわけではない。

$ l1bmr4 $llp0 $llb0
 <https://gyazo.com/59f57e2a1f66f06c0ea3abf5f95cbcc3>
