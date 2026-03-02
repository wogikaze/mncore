---
title: 3.6.8.11 l1bmm@-2長語16x1個別転送
id: 66b35ffe9453fb001c212d54
created_unix: 1723031550
updated_unix: 1771438984
views: 14
---

# 3.6.8.11 l1bmm@-2長語16x1個別転送

各[[L1BM]]について、指定した番号の[[MAB]]配下の4PEから[[サイクル]]あたり 2 長語ずつを読み出し、結合して[[L1BM]]に[[サイクル]]あたり 8 長語で書き込む。

```文法
l1bmm@<mabadr> <src> $llb<addr_b>
```
`<mabadr>`は 0 から 15 の[[MAB番号]]、`<src>`は読み出し元[[PEオペランド]]である。
[[L1BMアドレス]]`<addr_b>`は 8 長語アラインである必要がある。


```効果
for cycle= 0:4
  forall group,l2b,l1b
    LongWord data[4][2]
    forall pe
      data[pe][0:2] =MEM[group][l2b][l1b][mabadr][pe].refer_pemem(src, cycle)
      uint_t dst_addr=addr_b +cycle* 8
      MEM[group][l2b][l1b].l1bm[dst_addr:dst_addr+4] =data[0:4][0]
      MEM[group][l2b][l1b].l1bm[dst_addr+4:dst_addr+8] =data[0:4][1]

```
$ l1bmmm $llb0 $llp0
 <https://gyazo.com/a5bd2ceb957bf6da3990d32a70e78e62>
