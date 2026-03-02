---
title: 3.6.7.3 l2bmb2-L2BM→L1BM分配放送
id: 66b35ffe02bee8001d369bd2
created_unix: 1723031550
updated_unix: 1771433843
views: 6
---

# 3.6.7.3 l2bmb2-L2BM→L1BM分配放送

[[L2BM]]から 64 長語/サイクルで読み出し、配下の[[L1B]]を先頭から 2 つずつ 4 グループに分けてグループ内では[[放送]]、グループ間では[[分配]]を行い、各[[L1BM]]に 16 長語/サイクルで書き込む。

```文法
l2bmb2[@<l1bset>] $lc<addr_c> $lb<addr_b>
```
`@`以降は[[3.6.7.1 L1B部分集合指定]]で定めた[[L1B集合]]の指定であり、これに含まれるL1Bのみで書き込みが行われる。
 省略時は全L1Bに書き込みが行われる。
読み出しアドレス`<addr_c>`は 64 長語アライン、書き込みアドレス`<addr_b>`は 16 長語アラインである必要がある。

```効果
for cycle= 0:4
  forall group,l2b
    uint_t src_addr=addr_c +cycle* 64
    uint_t dst_addr=addr_b +cycle* 16
    LongWord data[64] = MEM[group][l2b].l2bm[src_addr:src_addr+64]
    for l1b in l1bset
      uint_t data_addr = 16 * (l1b / 2)
      MEM[group][l2b][l1b].l1bm[dst_addr:dst_addr+16] =data[data_addr:data_addr+16]

```
```例
l2bmb2 $lc0 $lb0
```
L2BMから計 256 長語を読み出し、L1Bについてグループ内では放送、グループ間では分配を行い、各L1BMに 64 長語を書き込む。

$ l2bmb2 $lc0 $lb0
 <https://gyazo.com/bf91dbc4fc6d3255443ed3782d803498>
