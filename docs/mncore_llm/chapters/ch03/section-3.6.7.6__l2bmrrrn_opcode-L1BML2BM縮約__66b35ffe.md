---
title: 3.6.7.6 l2bmr<rrn_opcode>-L1BM→L2BM縮約
id: 66b35ffe02bee8001d369bdb
created_unix: 1723031550
updated_unix: 1771407036
views: 14
---

# 3.6.7.6 l2bmr<rrn_opcode>-L1BM→L2BM縮約

[[L2BM]]について、配下のすべてまたは一部の[[L1BM]]から 16 長語/サイクルで連続領域を読み、[[L1B方向]]に指定した演算で縮約し、L2BMに書き込む。
 [[3.6.7.2 l2bmb-L2BM→L1BM放送]]で述べた[[L2BM→L1BM放送]]と対になっている。

```文法
l2bmr<rrn_opcode>[@<l1bset>] $lb<addr_b> $lc<addr_c>
```
`<rrn_opcode>`は[[3.5.5 縮約演算指定]]で定めた[[縮約演算指定]]である。
 `@`以降は[[3.6.7.1 L1B部分集合指定]]で定めた[[L1B集合]]の指定であり、これに含まれるL1Bのみから読み出しが行われる。
  省略時は全L1Bから読み出しが行われる。
  L1B集合に含まれないL1Bからは[[縮約演算の単位元]]が送信される。
読み出しアドレス`<addr_b>`と書き込みアドレス`<addr_c>`はいずれも 16 長語アラインである必要がある。

```効果
for cycle= 0:4
  forall group,l2b
    uint_t src_addr=addr_b +cycle* 16
    uint_t dst_addr=addr_c +cycle* 16
    LongWord buf[16]
    buf[:] =get_unit_value(rrn_opcode)
    for l1b in l1bset
      buf[0:16] =rrn_opcode(buf[0:16],MEM[group][l2b][l1b].l1bm[src_addr:src_addr+16])
      MEM[group][l2b].l2bm[dst_addr:dst_addr+16] = buf[0:16]
```
注意：縮約を内部的に実際にこの手順で行っているわけではない。

```例
l2bmrdfadd@[0,4] $lb0 $lc0 
```
0,4番L1BMからそれぞれ 64 長語を読み出し、[[倍精度浮動小数点数]]と解釈して[[L1B方向]]に加算し、結果の計 64 長語をL2BMに書き込む。

<https://tech.preferred.jp/wp-content/uploads/2024/07/anim4.gif>
