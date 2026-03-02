---
title: 3.6.8.16 l1bmm4@-1長語4x4個別転送
id: 66b35ffe9453fb001c212d63
created_unix: 1723031550
updated_unix: 1771439703
views: 25
---

# 3.6.8.16 l1bmm4@-1長語4x4個別転送

各[[L1BM]]について、`0 +i,4 +i,8 +i,12 +i`番[[MAB]] (iは` 0 , 1 , 2 , 3 `のいずれか指定した値)の配下の4PEから[[サイクル]]あたり 1 長語ずつを読み出し、結合して[[L1BM]]に[[サイクル]]あたり 16 長語で書き込む。

```文法
l1bmm4@<mabadr> <src> $lb<addr_b>
```
`<mabadr>`は 0 から 3 の[[MAB番号]]、`<src>`は読み出し元[[PEオペランド]]である。
[[L1BMアドレス]]`<addr_b>`は 16 長語アラインである必要がある。


```効果
for cycle= 0:4
  forall group,l2b,l1b
    LongWord data[16]
    for mab_outer= 0:4
      forall pe
        data[mab_outer * 4 +pe] =MEM[group][l2b][l1b][mab_outer * 4 +mabadr][pe].
        refer_pemem(src, cycle)
        uint_t dst_addr=addr_b +cycle* 16
        MEM[group][l2b][l1b].l1bm[dst_addr:dst_addr+16] =data[0:16]
      

```
$ l1bmm4@0 $lp0 $lb0
 <https://gyazo.com/dd5e697223a98b4f30ff06fbaf961eba>
$ l1bmm4@1 $lp0 $lb0
 <https://gyazo.com/cd30e53758a89dff774c843e7a57867f>
$ l1bmm4@2 $lp0 $lb0
 <https://gyazo.com/342159babaa3fa3feafd44b2d968ccb8>
$ l1bmm4@3 $lp0 $lb0
 <https://gyazo.com/a2fd6cc9b5c7e7c2f4a506cc6c3abab3>
