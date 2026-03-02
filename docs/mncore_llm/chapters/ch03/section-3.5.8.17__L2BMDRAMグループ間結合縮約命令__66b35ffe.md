---
title: 3.5.8.17 L2BM→DRAMグループ間結合縮約命令
id: 66b35ffe9453fb001c212d33
created_unix: 1723031550
updated_unix: 1771427845
views: 9
---

# 3.5.8.17 L2BM→DRAMグループ間結合縮約命令

この命令は複雑なのでまず具体的に、単位動作である[[L2BM側 64 長語読み出し]]の動作を説明する。
 全[[L2BM]]から 64 長語ずつ読み、グループ方向に[[縮約]]する。
 全グループの 0 番L2Bのデータを縮約した 64 長語を 16 長語ずつに分割し、各DRAMに書き込む。
 同様に全グループの 1 番L2Bのデータを縮約した 64 長語を 16 長語ずつに分割し、各DRAMに書き込む。
 以上で各DRAMに 32 長語が書き込まれる。

単位動作でない場合はこれを繰り返す。

スループットはL2BM側 16 長語/サイクル、DRAM側 8 長語/サイクルである。
```文法
mvr4<op>/n<size>[<tag>] $lc<addr_c> $d<addr_d>
```
[[縮約演算指定]]`<op>`については[[3.5.5 縮約演算指定]]を参照のこと。

```効果
uint_t n=size / 64
for i= 0:n
  uint_t src_addr=addr_c + 64 *i
  uint_t dst_offset= addr_d+ 32 * i
  LongWord buf[2][64]
  forall group,l2b
    buf[l2b][0:64] =op(buf[l2b][0:64],MEM[group][l2b].l2bm[src_addr:src_addr+64])
  forall group,l2b
    uint_t buf_addr= 16 *group
    uint_t dst_addr=dst_offset + 16 *l2b
    MEM[group].dram[dst_addr:dst_addr+16] = buf[l2b][buf_addr:buf_addr+16]
```
注意：縮約を内部的に実際にこの手順で行っているわけではない。

エラー
 sizeが単位動作 64 の倍数でないとエラーになる。

```例
mvr4dfadd/n64 $lc0 $d0
```
本節冒頭で延べた単位動作である。縮約には[[倍精度浮動小数点数加算]]を用いている。

$ mvr4dfadd/n64 $lc0 $d0
 <https://gyazo.com/43053a67eace6869a51b925150c6902d>
