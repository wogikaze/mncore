---
source_url: https://mncore-challenge.preferred.jp/mnist/problem/sum_col_mini/
slug: sum_col_mini
fetched_at: 2026-03-02T23:59:44+00:00
---

# SumCol mini

- Top: 4 lines / syttrea
- Par: 4 lines

## Problem Statement

LM上に Float \(4\times16\) 行列 \(A\) が与えられます。1 次元目を総和で縮約して、ベクトル \(S\) (size:16)を LM に出力してください。

## Explanation

### 考え方・方針
\(A[0]\) の 16 要素は 4 PEに分散して `$m[0,1,2,3]` に、\(A[1]\) は同様に `$m[4,5,6,7]` に格納されています。
\(A[0]\) から \(A[3]\) の和を、`$n[0,1,2,3]` に格納する問題です。
つまり、`$n0 = $m0 + $m4 + $m8 + $m12` のように計算します。
入力も出力も 2 次元目は 4 PEに分散しているので、独立したものとして考えることができます。

## Inputs

* \(A\) (\(0 \le A[{i, j}] \le 10\)): Float `$lm[0:16]`, `(4,16)/((4:2), (2:1, 4_PE:1, 2_W:1); B@[MAB,L1B,L2B])`

## Outputs

* \(S\): Float `$ln[0:4]`, `(16)/((2:1, 4_PE:1, 2_W:1))` / \(0.0001\) 以下の絶対誤差が許容されます

## Testcases

* [testcase.vsm](https://mncore-challenge.preferred.jp/mnist/testcase/sum_col_mini/testcase.vsm)
