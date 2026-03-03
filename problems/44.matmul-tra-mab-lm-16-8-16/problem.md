---
source_url: https://mncore-challenge.preferred.jp/mnist/problem/matmul_tra_mab_lm_16_8_16/
slug: matmul_tra_mab_lm_16_8_16
fetched_at: 2026-03-02T23:59:59+00:00
---

# Mmul TA 16_8_16

- Top: 17 lines / syttrea
- Par: 64 lines

## Problem Statement

\(8 \times 16\) 行列 \(A\) と、\(8 \times 16\) 行列 \(B\) に対して、行列積 \(C = A^T \times B\) (shape:\(16 \times 16\)) を計算してください。\(A,B,C\) のレイアウトは以下のとおりです。
A: (( 8:2), (2:1, 4_PE:1, 2_W:1)) B: (( 8:2), (2:1, 4_PE:1, 2_W:1)) C: ((16:2), (2:1, 4_PE:1, 2_W:1))
### \(A, B, C\) の値はこちらです。
_詳細データは省略。必要なら source_url を参照してください。_

## Explanation

前回の [Mmul TA 8_8_8](https://mncore-challenge.preferred.jp/mnist/problem/matmul_tra_mab_lm_8_8_8/) では、\(8 \times 8\) 行列同士の行列積を計算しました。
今回は、\(8 \times 16\) 行列を、右半分、左半分に分けて、それぞれ \(8 \times 8\) 行列を計算し、結合することで計算することができます。
つまり、イメージとしては行列 \(A,B\) のそれぞれ左半分と右半分を \(A_0, A_1, B_0, B_1\) としたとき、
[A0 × B0, A0 × B1], [A1 × B0, A1 × B1],
を計算します。
4 回の \(8 \times 8\) 行列積を行うたびに入力の転置を行うことで 64 行程度で Accept できますし、
最初に \(A,B\) の転置を行ってから行列積を行うことで、36 行程度で Accept できます。
### 小行列のレイアウトのおさらい
詳しくは [Mmul 4_16_16](https://mncore-challenge.preferred.jp/mnist/problem/matmul_notr_mab_lm_4_16_16/) のときに `((*:2), (2:1, 4_PE:1, 2_W:1))` のレイアウトの意味を説明しました。
今回の場合、
* \(A\) の左半分 \(A_0\) `A[0:8][0:8 ]` は、`$lm0v4`, `$lm16v4` に、
* \(A\) の右半分 \(A_1\) `A[0:8][8:16]` は、`$lm2v4`, `$lm18v4` に、
* \(B\) の左半分 \(B_0\) `B[0:8][0:8 ]` は、`$lm32v4`, `$lm48v4` に、
* \(B\) の右半分 \(B_1\) `B[0:8][8:16]` は、`$lm34v4`, `$lm50v4` にあります
また、出力の \(C\) に関して、
* 左上の `C[0:8 ][0:8 ]` は、`$ln0v4`, `$ln16v4` に、
* 右上の `C[0:8 ][8:16]` は、`$ln2v4`, `$ln18v4` に、
* 左下の `C[8:16][0:8 ]` は、`$ln32v4`, `$ln48v4` に、
* 右下の `C[8:16][8:16]` は、`$ln34v4`, `$ln50v4` にあります

## Inputs

* \(A\) (\(0 \le A[{i, j}] \le 128\)): Float `$lm[0:32]`, `(8,16)/((8:2), (2:1, 4_PE:1, 2_W:1); B@[MAB,L1B,L2B])`
* \(B\) (\(200 \le B[{i, j}] \le 328\)): Float `$lm[32:64]`, `(8,16)/((8:2), (2:1, 4_PE:1, 2_W:1); B@[MAB,L1B,L2B])`

## Outputs

* \(C\): Float `$ln[0:64]`, `(16,16)/((16:2), (2:1, 4_PE:1, 2_W:1))` / \(0.00001\) 以下の絶対誤差が許容されます

## Testcases

* [testcase.vsm](https://mncore-challenge.preferred.jp/mnist/testcase/matmul_tra_mab_lm_16_8_16/testcase.vsm)
