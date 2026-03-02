---
title: 3.6.8.17 l1bmm4@-2長語4x4個別転送
id: 66b35ffe3c1ad7001de55f7e
created_unix: 1723031550
updated_unix: 1771439801
views: 14
---

# 3.6.8.17 l1bmm4@-2長語4x4個別転送

各[[L1BM]]について、`0 +i,4 +i,8 +i,12 +i`番[[MAB]] (iは `0 , 1 , 2 , 3` のいずれか指定した値)の配下の4PEから[[サイクル]]あたり 2 長語ずつを読み出し、結合して[[L1BM]]に[[サイクル]]あたり 32 長語で書き込む。

```文法
l1bmm4@<mabadr> <src>$llb<addr_b>

```
`<mabadr>`は 0 から 3 の[[MAB番号]]、`<src>`は読み出し元[[PEオペランド]]である。
[[L1BMアドレス]]`<addr_b>`は 32 長語アラインである必要がある。

```効果
for cycle= 0:4
  forall group,l2b,l1b
    LongWord data[16][2]
    for mab_outer= 0:4
      forall pe
        data[mab_outer * 4 +pe][0:2] =MEM[group][l2b][l1b][mab_outer * 4 +mabadr][pe].refer_pemem(src, cycle)
        uint_t dst_addr=addr_b +cycle* 32
        for i= 0:4
          MEM[group][l2b][l1b].l1bm[dst_addr+i*8:dst_addr+i*8+4] =data[i*4:(i+1)*4][0]
          MEM[group][l2b][l1b].l1bm[dst_addr+i*8+4:dst_addr+i*8+8] =data[i*4:(i+1)*4][1]

```
$ l1bmm4@0 $llb0 $llp0
 <https://gyazo.com/4d07be85c3706c10766bb020b0f3a125>
$ l1bmm4@1 $llb0 $llp0
 <https://gyazo.com/7a10e12798ebfab92c8a5f93d2431ab2>
$ l1bmm4@2 $llb0 $llp0
 <https://gyazo.com/f11dfb1c9667c25269a473563023d1f6>
$ l1bmm4@3 $llb0 $llp0
 <https://gyazo.com/108296889bc2a38e460d160f03099da8>
