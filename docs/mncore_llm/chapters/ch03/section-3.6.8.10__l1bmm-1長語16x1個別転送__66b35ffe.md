---
title: 3.6.8.10 l1bmm@-1長語16x1個別転送
id: 66b35ffe9453fb001c212d51
created_unix: 1723031550
updated_unix: 1771438955
views: 13
---

# 3.6.8.10 l1bmm@-1長語16x1個別転送

各[[L1BM]]について、指定した番号の[[MAB]]配下の4PEから[[サイクル]]あたり 1 長語ずつを読み出し、結合して[[L1BM]]に[[サイクル]]あたり 4 長語で書き込む。


```文法
l1bmm@<mabadr> <src> $lb<addr_b>
```
`<mabadr>`は 0 から 15 の[[MAB番号]]、`<src>`は読み出し元[[PEオペランド]]である。
 [[L1BMアドレス]]`<addr_b>`は 4 長語アラインである必要がある。


```効果
for cycle= 0:4
  forall group,l2b,l1b
    LongWord data[4]
    forall pe
      data[pe] =MEM[group][l2b][l1b][mabadr][pe].refer_pemem(src, cycle)
      uint_t dst_addr=addr_b +cycle* 4
      MEM[group][l2b][l1b].l1bm[dst_addr:dst_addr+4] =data[0:4]
    

```
$ l1bmmm $lb0 $lp0
 <https://gyazo.com/c27221409186eb17a0c600f9c47a6513>
