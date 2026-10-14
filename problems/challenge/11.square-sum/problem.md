---
source_url: https://mncore-challenge.preferred.jp/problem/square_sum
slug: square_sum
fetched_at: 2026-10-14T00:38:56+00:00
---

# Square Sum

- Top: 11 lines / syttrea
- Par: 191 lines

## Problem Statement

LM0上の \(2\) 次元 `Double` 配列 \(X\) に対して \(Y[i] = \sum\limits_{j=0}^{127} (X[i, j])^2\) を計算してLM1に出力してください。

## Explanation

例えば以下のようにすることで、\(2\) 命令で `$lm[0,2,4,6]` の \(4\) 要素それぞれの二乗を `$lr[0,2,4,6]` へ出力できます。
```vsm
dvmulu $lm0v $lm0v $nowrite
dvfmad $lm0v $lm0v $mauf $lr0v
```

ここでの注意として MN-Core 2 では、倍精度の乗算は PE0,1 だけ乗算を動作させる `dvmul u` と、PE2,3 だけ乗算を動作させる `dvmul d` に分かれています。
積和演算 (`fma`) も同様に `dvfma u` と `dvfma d` に分かれています。乗算が動作しない側の PE も乗算回路は \(0\) を出力します。
つまり、`dvmulu` で乗算を行うと、PE0,1 は期待通りの乗算結果を出力し、PE2,3 は \(0\) を出力します。
積和演算も、入力を \(x \times y + z\) として `dvfmau` を行うと、PE0,1 は \(x \times y + z\) を出力し、PE2,3 は \(0 + z\) を出力します。
これを元に、先程の VSM を解説しましょう。PE 0 の入力を \(a\)、PE 1 の入力を \(b\)、… として、\(4\) PE の入力 \([a, b, c, d]\) から最終的に \([a^2, b^2, c^2, d^2]\) を得るのを目的にしています。
\(1\) 命令目 `dvmulu` の出力は、\([a^2, b^2, 0, 0]\) となります。\(2\) 命令目の乗算回路の出力は \([0, 0, c^2, d^2]\) であり、`fma` の加算項として \(1\) 命令目の結果を forwarding で参照して足しているので、結果として \(2\) 命令で \([a^2, b^2, c^2, d^2]\) を計算しています。
さて、この調子で PE ごとに素直に \(128\) 要素の積和計算をしてもこの問題を解くことができますが、MN-Core の特徴である並列計算を活かして解く方法も紹介します。
入力のレイアウトを確認すると、`B@[MAB,L1B]` と書かれています。なので MAB, L1B それぞれで同じ値が与えられることが分かります。
また出力に関しても MAB, L1B が省略されていますが、本ジャッジでは省略された階層に関しては最初の要素だけが判定の対象になります。つまり今回の場合、\(0\) 番 L1B の \(0\) 番 MAB の値が正しければ正解になります。
MN-Core 2 は、以下のような階層構造を持っています。
今回、MAB それぞれに同じ値が与えられていることに注目し、\(128\) 要素を \(16\) MAB に分割し、MAB によって異なるアドレスの \(8\) 要素の二乗和を計算して、\(16\) MAB 間で縮約（今回は総和演算）することでも正解できます。
縮約は以下の VSM で行うことができます。
```vsm
l1bmrdfadd $lr0v $lb0
nop
nop
l1bmm $lb0 $lr0v
```

このVSMはまず、 [l1bmr](https://mncore-challenge.preferred.jp/memory-animation/?file=MAB16x1→L1BM reduce&movie=l1bmr %24lp0 %24lb0&frame=1) 命令によって \(16\) MAB 内の PE メモリから倍精度の加算縮約 `dfadd` を行って L1BM（L1B メモリ）の `$lb[0:16]` へ書き込みます。図にすると以下のとおりです。
MAB には専用の階層メモリが存在しないため、階層構造的には MAB をスキップし、PE のメモリから読み出した値を同じ PE 番号間で加算して L1BM へ書き込んでいます。
このとき、PE メモリは単語単位のアドレッシングなのに対し、L1B メモリは長語単位のアドレッシングであることに注意してください。
その後 [l1bmm](https://mncore-challenge.preferred.jp/memory-animation/?file=L1BM→MAB16x1 bcast&movie=l1bmm %24lb0 %24lp0&frame=1) 命令によって L1B メモリ `$lb[0:16]` から \(16\) 個の MAB の PE メモリへ放送し、同じく `$lr[0:8]` に書き込みます。
PE → L1BM 転送命令から、L1BM → PE 転送命令までは \(2\) ステップ空ける必要があるため、上の例のように `nop` 命令が \(2\) つ必要です（[SDM 3.6.3.8「PE → L1BM 転送 ⇒ L1BM → PE 転送」](https://projects.preferred.jp/mn-core/assets/mncore2_dev_manual_ja.pdf#subsubsection.3.6.3.8)）。
しかし、[l1bmm](https://mncore-challenge.preferred.jp/memory-animation/?file=L1BM→MAB16x1 bcast&movie=l1bmm %24lb0 %24lp0&frame=1) を折り返しレジスタ `$lbi` からの読み出しとすることで、直前のステップで L1BM に書き込まれたデータをすぐに読み出して使用することができ、以下のように短縮できます（[SDM 3.6.8.2「L1BM 命令式種別と折り返し動作」](https://projects.preferred.jp/mn-core/assets/mncore2_dev_manual_ja.pdf#subsubsection.3.6.8.2)）。
```vsm
l1bmrdfadd $lr0v $lb0
l1bmm $lbi $lr0v
```

なお、L2BM-L1BM 間に相当する折り返しレジスタは MN-Core 2 には存在しません。
また、\(1\) つの MAB 内の \(4\) PE 間で値を縮約する命令もありません。
PE 間でのデータのやり取りをしたい場合には、ALU の PE 間循環シフト命令 `msl` `msr` などが役立ちます。

## Inputs

* \(X\) (\(-1 \le X[{i, j}] \le 1\)): Double `$lm[0:256]`, `/((8_L2B:1, 4_PE:1), (128:1); B@[MAB,L1B])`

## Outputs

* \(Y\): Double `$ln[0:2]`, `/((8_L2B:1, 4_PE:1))` / \(10^{-9}\) 以下の絶対誤差が許容されます

## Testcases

* [testcase.vsm](https://mncore-challenge.preferred.jp/testcase/square_sum/testcase.vsm)
