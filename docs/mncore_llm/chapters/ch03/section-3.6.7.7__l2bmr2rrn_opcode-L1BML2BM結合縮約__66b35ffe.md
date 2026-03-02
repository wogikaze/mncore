---
title: 3.6.7.7 l2bmr2<rrn_opcode>-L1BM→L2BM結合縮約
id: 66b35ffe02bee8001d369bde
created_unix: 1723031550
updated_unix: 1771442701
views: 12
---

# 3.6.7.7 l2bmr2<rrn_opcode>-L1BM→L2BM結合縮約

各[[L2BM]]について、配下の[[L1BM]]から 16 長語/サイクルで連続領域を読み、L1Bを先頭から 2 つずつ 4グループに分けてグループ内では指定した演算で[[縮約]]、グループ間では[[結合]]を行い、L2BMに 64 長語/サイクルで書き込む。
[[3.6.7.3 l2bmb2-L2BM→L1BM分配放送]]で述べた[[L2BM→L1BM分配放送]]と対になっている。
```文法
l2bmr2<rrn_opcode> $lb<addr_b> $lc<addr_c>
```
`<rrn_opcode>`は[[3.5.5 縮約演算指定]]で定めた[[縮約演算指定]]である。
 [[結合縮約]]ではない[[通常の縮約]]([[3.6.7.6 l2bmr<rrn_opcode>-L1BM→L2BM縮約]])とは異なり、読み出し元L1B集合を指定することはできない。
読み出しアドレス`<addr_b>`は 16 長語アライン、書き込みアドレス<addr_c>は 64 長語アラインである必要がある。

```効果
for cycle= 0:4
  forall group,l2b
    uint_t src_addr=addr_b +cycle* 16
    uint_t dst_addr=addr_c +cycle* 64
    LongWord buf[64]
    buf[:] =get_unit_value(rrn_opcode)
    forall l1b
      uint_t data_addr = 16 * (l1b / 2)
      buf[data_addr:data_addr+16] =rrn_opcode(buf[data_addr:data_addr+16],MEM[group][l2b][l1b].l1bm[src_addr:src_addr+16])
      MEM[group][l2b].l2bm[dst_addr:dst_addr+64] = buf[0:64]
```
注意：縮約を内部的に実際にこの手順で行っているわけではない。

```例
l2bmr2dfadd $lb0 $lc0
```
L1BMからそれぞれ 64 長語を読み出し、[[倍精度浮動小数点数]]と解釈してグループ内で加算し、グループ間では結合して計 256 長語をL2BMに書き込む。

$ l2bmr2 $lb0 $lc0
 <https://gyazo.com/ed56d736facf2bf39b466f03e51819be>
