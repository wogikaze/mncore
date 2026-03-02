---
title: 3.6.10.3 hmwrite-半精度行列レジスタ書き込み
id: 66b35fff37748a001ca4db7f
created_unix: 1723031551
updated_unix: 1724755551
views: 18
---

# 3.6.10.3 hmwrite-半精度行列レジスタ書き込み

[[半精度]]データの[[行列レジスタ]]への書き込みを行う。
```文法
hmwrite<src> $(l|ll)(x|y)<addr>

```
`<src>`は読み出し元[[PEオペランド]]であり、[[アクセス語長]]は長語または 2 長語である。[[アクセス語長]]は後述
の[[行列レジスタ]]の[[アクセス語長]]と一致している必要がある。[[行列ベクトル積和演算]]を目的として書き込む場合
は[[ブロックフロート半精度]]の値であり、行列[[転置読み出し]]を目的として書き込む場合は通常の[[半精度]]の値で
ある。
`$(l|ll)(x|y)`は書き込み先の[[行列レジスタオペランド]]である。
 (l|ll)は[[行列レジスタ]]への[[アクセス語長]]を表す。
  lでは[[サイクル]]あたり 1 行、llでは[[サイクル]]あたり 2 行に書き込む。
 以下効果でwlとして参照する。

`(x|y)`はどちらの[[行列レジスタ]]に書き込むかの指定であり、以下効果において[[side]]として参照する。

`<addr>`は書き込みを開始する行番号である。
 [[サイクル]]ごとに連続する行を重複なくアクセスするように[[インクリメント]]される。
 wlがllの場合はは 2 の倍数である必要がある。
 [[半精度]]行列データは 16 行 16 列であるので、[[サイクル]]ごとに 2 行ずつ書き込めば 2 命令で行列データ全体を[[行列レジスタ]]に書き込むことができる。


```効果
for cycle= 0:4
forall chip,l2b,l1b,mab
if wl==l
HalfWord src_data[4][4] =MEM[chip][l2b][l1b][mab][0:4].refer_pemem(src,cycle)
for j = 0:16
MEM[chip][l2b][l1b][mab].refer_matreg(side, HalfWord)[(addr+cycle)%16][j] =
src_data[j/4][j%4]
elif wl== ll
HalfWord src_data[4][8] =MEM[chip][l2b][l1b][mab][0:4].refer_pemem(src,cycle)
for j = 0:16
MEM[chip][l2b][l1b][mab].refer_matreg(side, HalfWord)[(addr+cycle*2)%16][j] =
src_data[j/4][j%4]
MEM[chip][l2b][l1b][mab].refer_matreg(side, HalfWord)[(addr+cycle*2)%16+1][j] =
src_data[j/4][j%4+4]


```
