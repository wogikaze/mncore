---
title: 3.5.8.3 DRAM→PDM単独個別転送命令
id: 66b35ffe9453fb001c212d03
created_unix: 1723031550
updated_unix: 1771432667
views: 11
---

# 3.5.8.3 DRAM→PDM単独個別転送命令

指定したグループの[[DRAM]]から指定したグループの[[PDM]]にデータをコピーする。
単位動作は 64 長語である。
読み出し元と書き込み先のグループは同じでも別でもよい。
スループットはグループ内の場合 8 長語/サイクル、グループ間の場合 4 長語/サイクルである。
```文法
mvp/n<size>[<tag>] $d<addr_d>@<group_d> $p<addr_p>@<group_p>

```
```効果
uint_t n=size / 64
for i= 0:n
  uint_t src_addr=addr_d + 64 *i
  uint_t dst_addr=addr_p + 64 *i
  Word64 data[64] =MEM[group_d].dram[src_addr:src_addr+64]
  MEM[group_p].pdm[dst_addr:dst_addr+64] = data[0:64]

```
エラー
 sizeが単位動作 64 の倍数でないとエラーになる。

```例
mvp/n64 $d0@1 $p0@0
```
1 番グループのDRAMから 0 番グループのPDMに 64 長語コピーする。

$ mvp/n64 $d0@0 $p0@0
 <https://gyazo.com/a9666a2223e8218ee295d502d6da2aa5>
$ mvp/n64 $d0@1 $p0@0
 <https://gyazo.com/24d7bb211553eb7a7ad5788259240e98>
