---
title: 3.6.11.3 hmread-半精度行列レジスタ読み出し
id: 66b35fff37748a001ca4db8b
created_unix: 1723031551
updated_unix: 1723940584
views: 12
---

# 3.6.11.3 hmread-半精度行列レジスタ読み出し

半精度データの行列レジスタからの読み出しを行う。
```文法
hmread $ll(x|y)<addr> <dst_0> [<dst_1>..]

```
`$ll(x|y)`は読み出し元の[[行列レジスタ]][[オペランド]]である。
 [[hmwrite]]と違い常に[[サイクル]]あたり 2 行が読み出される。
 `(x|y)`はどちらの[[行列レジスタ]]から読み出すかの指定であり、以下効果において[[side]]として参照する。

`<addr>`は読み出しを開始する列番号である。
 [[サイクル]]ごとに連続する列を重複なくアクセスするように[[インクリメント]]される。
 `<addr>`は 2 の倍数でなければならない。
 [[半精度]]行列データは 16 行 16 列であるので、 2 命令で行列データ全体を[[行列レジスタ]]から読み出すことができる。

`<dst_0>` `[[<dst_1>..]]`は書き込み先[[PEオペランド]]である。
 複数の[[PEメモリ]]に同時に書き込むことができるが、以下効果では簡単のため単一の書き込み先として[[dst]]を指定した例を示している。
 読み出した内容は通常の[[半精度]]であり、書き込みの[[アクセス語長]]は 2 長語である。


```効果
for cycle= 0:4
  forall chip,l2b,l1b,mab
    HalfWord src_data[4][8]
    for i= 0:16
      src_data[i/4][i%4] =MEM[chip][l2b][l1b][mab].refer_matreg(side,HalfWord)[i][(
      addr+cycle*2)%16]
      src_data[i/4][i%4+4] =MEM[chip][l2b][l1b][mab].refer_matreg(side, HalfWord)[i][(addr+cycle*2)%16+1]
    forall pe
      MEM[chip][l2b][l1b][mab][pe].refer_pemem(dst,cycle) =src_data[pe][:]


```
