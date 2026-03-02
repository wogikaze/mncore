---
title: 3.6.8.20 l1bmd-分配
id: 66b35ffe3c1ad7001de55f87
created_unix: 1723031550
updated_unix: 1771438420
views: 20
---

# 3.6.8.20 l1bmd-分配

[[L1BM]]から[[サイクル]]あたり 64 長語を読み出し、配下の 64 個のPEに分配し、[[サイクル]]あたり 1 長語で書き込む。
 [[L1BMアドレス]]上では[[MAB番号]]が外側、[[PE番号]]が内側に対応する。
 つまり、C言語の多次元配列風に書くと`[[16 (MAB番号)]][[4 (PE番号)]]`という並びになる。
 この際、[[L1BM]]上のデータは 4 長語ごとに異なる[[MAB]]に送られることになるが、行き先の[[MAB番号]]をラウンドロビンにずらすことができる。
なお 2 長語動作の[[分配命令]]は存在しない。


```文法
l1bmd[<mabdiff>] $lb<addr_b> <dst_0> [<dst_1>..]

```
`<dst_0> [[<dst_1>..]]`は書き込み先PEオペランドである。
`[[<mabdiff>]]`は+か-の後に 0 から 15 の整数を付け、[[MAB番号]]をずらす量を指定する。正の場合でも符号は必須である。
番ずれた[[MAB]]に、未指定であれば送信されるはずだったデータが送られるという対応関係になる。
[[MAB番号]]をずらす機能は[[折り返し転送]]でも有効である。
 この際、対になる[[結合命令]]([[3.6.8.21 l1bmd-結合]])と[[分配命令]]で[[MAB番号]]をずらす量は一致していなければならない。
この機能は結合命令で[[折り返しレジスタ]]に書き込む際には適用されないので、折り返しの結果 2 倍ずれてしまうということにはならない。
[[L1BMアドレス]]`<addr_b>`は 64 長語アラインである必要がある。


```効果
for cycle= 0:4
  forall group,l2b,l1b
    uint_t src_addr=addr_b +cycle* 64
    LongWord data[64] = MEM[group][l2b][l1b].l1bm[src_addr:src_addr+64]
    forall mab,pe
      uint_t src_mab = (mab+ mabdiff) % 16
      MEM[group][l2b][l1b][mab][pe].refer_pemem(dst,cycle) =data[src_mab* 4 +pe]

```
```例
lpassa $mabid $lr0v
nop
l1bmd+1 $lr0v $lb0
l1bmd-1 $lr0v $lb256;l1bmd+1$lbi $ls0v
l1bmd-1 $lbi $ls8v
nop
l1bmd $lb0 $ls16v
l1bmd $lb256 $ls24v


```
[[折り返し転送]]の解説のため、[[3.6.8.21 l1bmd-結合]]で述べる[[結合命令]]も含めた例とした。
 0 番[[MAB]]の[[$ls]]0, [[$ls]]8, [[$ls]]16, [[$ls]]24にはそれぞれ 15 , 1 , 15 , 1 が入る。
前者 2 つでは折り返し分配時に[[MAB番号]]をずらす機能が適用されており、後者 2 つでは[[$lb]]0, [[$lb]]256への結合書き込み時に同機能が適用されている。

$ l1bmd $lb0 $lp0
 <https://gyazo.com/bfb6f775b60c9dc50867ba609456cc6a>
$ l1bmd+1 $lb0 $lp0
 <https://gyazo.com/8c124249d6e119bde535a1e501c6c188>
