---
title: 3.6.8.21 l1bmd-結合
id: 66b35ffe3c1ad7001de55f8a
created_unix: 1723031550
updated_unix: 1771438687
views: 40
---

# 3.6.8.21 l1bmd-結合

PEから[[サイクル]]あたり 1 長語を読み出し、[[L1BM]]配下の 64 個のPEについて結合し[[L1BM]]に[[サイクル]]あたり 64 長語で書き込む。
 [[L1BMアドレス]]と[[MAB番号]]・[[PE番号]]との対応関係は分配命令と同じである。
 この際、 4 長語ごとに異なる[[MAB]]から送られた値が書き込まれることになるが、送り元の[[MAB番号]]をラウンドロビンにずらすことができる。
 この機能は[[折り返しレジスタ]]への書き込み時は動作しない。
 なお 2 長語動作の結合命令は存在しない。

```文法
l1bmd[<mabdiff>] <src> $lb<addr_b>
```
`<src>`は読み出し元PEオペランドである。
`<mabdiff>`は+か-の後に 0 から 15 の整数を付け、[[MAB番号]]をずらす量を指定する。正の場合でも符号は必須である。
 `<mabdiff>`番分ずれた[[アドレス]]に、`<mabdiff>`未指定であれば送信されるはずだったデータが送られるという対応関係になる。
[[折り返し転送]]の際の注意は[[分配命令]]の項目([[3.6.8.20 l1bmd-分配]])を参照のこと。
[[L1BMアドレス]]`<addr_b>`は 64 長語アラインである必要がある。

```効果
for cycle= 0:4
  forall group,l2b,l1b
    LongWord data[64]
    LongWord data_turnaround[64]
    forall mab,pe
      uint_t dst_mab = (mab+ mabdiff) % 16
      data[dst_mab* 4 +pe] =MEM[group][l2b][l1b][mab][pe].refer_pemem(src,cycle)
      data_turnaround[mab * 4 +pe] =MEM[group][l2b][l1b][mab][pe].refer_pemem(src,cycle)
    uint_t dst_addr=addr_b +cycle* 64
    MEM[group][l2b][l1b].l1bm[dst_addr:dst_addr+64] =data[0:64]
    MEM[group][l2b][l1b].l1bm_turnaround[cycle][0:64] = data_turnaround[0:64]

```
l1bm_turnaroundは[[折り返しレジスタ]]を表している。
[[折り返しレジスタ]]への書き込みが起きるのは他の[[PE→L1BM転送命令]]も同様だが、[[結合命令]]のみ[[MAB番号]]をずらす機能に関して特殊な動作をするため、特別に記載した。


```例
l1bmd+1 $lr0v $lb0
l1bmd $lr0v $lb256
nop/2
l1bmd $lb0 $ls0v
l1bmd+1 $lb256 $ls8v

```
この例では`$ls0`から 4 長語の範囲に書き込まれる値と、`$ls8`から 4 長語の範囲に書き込まれる値は等しくなる。
 つまり、あるの値を結合時に指定するのと分配時に指定するのは等価になるような定義になっている。

$ l1bmd $lr0 $lb0
 <https://gyazo.com/92d68f658b97bacaf5203cdf39d97dbc>
$ l1bmd+1 $lr0 $lb0
 <https://gyazo.com/6ce37f88846a65d140e2a99956e650f5>
