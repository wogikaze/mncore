---
source_url: https://mncore-challenge.preferred.jp/mnist/problem/max_row/
slug: max_row
fetched_at: 2026-03-02T23:59:44+00:00
---

# MaxRow

- Top: 21 lines / syttrea
- Par: 160 lines

## Problem Statement

LM上に Float \(256\times16\) 行列 \(A\) が与えられます。2 次元目を最大値を求めて縮約して、ベクトル \(S\) (size:256)を LM に出力してください。

## Explanation

[SumRow](https://mncore-challenge.preferred.jp/mnist/problem/sum_row/)
### 最大値を求めるには？
`fvadd` の代わりに ALU 命令の `fmax` を使うのがおすすめです。
### ヒント2
実装にもよりますが、`fvadd` を単純に `fmax` に置き換えた場合、`$mauf` を使っていたのであれば MAU ではなく ALU のフォワーディングを使いたいので、代わりに `$aluf` を使う必要があります。
### ヒント3
実装にもよりますが、`$mauf` を単純に `$aluf` に置き換えた場合、MAU 命令である `fvpassa` を使っていたのであれば代わりに ALU 命令の `fpassa` （もしくは`ipassa`）命令を使う必要があります。

## Inputs

* \(A\) (\(-10000 \le A[{i, j}] \le 10000\)): Float `$lm[0:256]`, `(256,16)/((4_L2B:2, 64:2), (2:1, 4_PE:1, 2_W:1); B@[MAB,L1B])`

## Outputs

* \(S\): Float `$ln[0:64]`, `(256)/((4_L2B:2, 32:1, 2_W:1))`

## Testcases

* [testcase.vsm](https://mncore-challenge.preferred.jp/mnist/testcase/max_row/testcase.vsm)
