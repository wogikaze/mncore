---
source_url: https://mncore-challenge.preferred.jp/mnist/problem/sum_row/
slug: sum_row
fetched_at: 2026-03-02T23:59:44+00:00
---

# SumRow

- Top: 20 lines / syttrea
- Par: 160 lines

## Problem Statement

LM上に Float \(256\times16\) 行列 \(A\) が与えられます。2 次元目を総和で縮約して、ベクトル \(S\) (size:256)を LM に出力してください。

## Explanation

[SumRow mini](https://mncore-challenge.preferred.jp/mnist/problem/sum_row_mini/)
今回の問題は、[SumCol](https://mncore-challenge.preferred.jp/mnist/problem/sum_col_mini/) と違い、出力は DRAM ではなく通常通り LM1 に格納する事になっています。
### 実は…
[SumRow mini](https://mncore-challenge.preferred.jp/mnist/problem/sum_row_mini/)
SumRow mini では `$m[0:16]` の値を入力に `$n[0:4]` へ出力しましたが、この調子で続きも書いてみましょう。
コードをスクリプトを使用して生成しても構いません。
### 考え方・方針
行列の 2 次元目のそれぞれで総和を求めるので、1 次元目ごと独立していると考えられます。つまり、16 要素の合計を求める問題が、256 個独立に存在するとも言えます。
1 次元目の 256 が `4_L2B:2` と、4 個の L2B に分割されていて、出力も同じ `4_L2B:2` で分割されているので、256 個の問題が 4 個の L2B に 64 個ずつ分割されていると考えることができます。
そして、各 PE で考えると、入力が `(64:2)` のレイアウト、つまり、2 長語間隔で 64 個並んでいます。SumRow mini では `(4:2)`、つまり 2 長語間隔で 4 個を計算してもらったので、これを 16 回繰り返せば Accept です。

## Inputs

* \(A\) (\(0 \le A[{i, j}] \le 10\)): Float `$lm[0:256]`, `(256,16)/((4_L2B:2, 64:2), (2:1, 4_PE:1, 2_W:1); B@[MAB,L1B])`

## Outputs

* \(S\): Float `$ln[0:64]`, `(256)/((4_L2B:2, 32:1, 2_W:1))` / \(0.0001\) 以下の絶対誤差が許容されます

## Testcases

* [testcase.vsm](https://mncore-challenge.preferred.jp/mnist/testcase/sum_row/testcase.vsm)
