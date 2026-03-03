---
source_url: https://mncore-challenge.preferred.jp/mnist/problem/sum_row_mini/
slug: sum_row_mini
fetched_at: 2026-03-02T23:59:44+00:00
---

# SumRow mini

- Top: 6 lines / syttrea
- Par: 10 lines

## Problem Statement

LM上に Float \(4\times16\) 行列 \(A\) が与えられます。2 次元目を総和で縮約して、ベクトル \(S\) (size:4)を LM に出力してください。

## Explanation

[SumCol mini](https://mncore-challenge.preferred.jp/mnist/problem/sum_col_mini/)
また、PE 内の 4 要素の縮約に加えて、4 PE の縮約も必要になり、合計 16 要素の縮約を行う必要があります。
### 考え方・方針
\(A[0]\) の 16 要素は 4 PEに分散して `$m[0,1,2,3]` にありました。今度はこの PE 内の `$m0` から `$m3` の 4 要素と × 4 PE の 16 要素の総和を求めて、`$n0` に格納する問題です。
`$m0v4` と書くと `$n[0,4,8,12]` を意味するので、これを使用して SumCol mini 同様にいっきに計算することができます。
### 4PE 間の縮約
4PE 間で `$r0` の縮約を行う方法について、命令一覧を見てもぱっと思いつかないかもしれません。
例えば PE 間循環シフト命令 `msl` を使うことで、PE0 の値を PE1 へ、PE1 の値を PE2 へ、… のように循環させることができるので、これを使って3回、値を回しながら `fvadd` を行えば実現できるでしょう。

## Inputs

* \(A\) (\(0 \le A[{i, j}] \le 10\)): Float `$lm[0:16]`, `(4,16)/((4:2), (2:1, 4_PE:1, 2_W:1); B@[MAB,L1B,L2B])`

## Outputs

* \(S\): Float `$ln[0:4]`, `(4)/((2:1, 2_W:1))` / \(0.0001\) 以下の絶対誤差が許容されます

## Testcases

* [testcase.vsm](https://mncore-challenge.preferred.jp/mnist/testcase/sum_row_mini/testcase.vsm)
