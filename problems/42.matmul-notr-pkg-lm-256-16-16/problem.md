---
source_url: https://mncore-challenge.preferred.jp/mnist/problem/matmul_notr_pkg_lm_256_16_16/
slug: matmul_notr_pkg_lm_256_16_16
fetched_at: 2026-03-02T23:59:59+00:00
---

# Mmul 256_16_16★

- Top: 13 lines / syttrea
- Par: 48 lines

## Problem Statement

\(256 \times 16\) 行列 \(A\) と、\(16 \times 16\) 行列 \(B\) に対して、行列積 \(C = A \times B\) (shape:\(256 \times 16\)) を計算してください。\(A,B,C\) のレイアウトは以下のとおりです。
A: ((8_L2B:1, 4:2, 8_L1B:1), (2:1, 4_PE:1, 2_W:1)) B: ((16:2), (2:1, 4_PE:1, 2_W:1)) C: ((8_L2B:1, 4:2, 8_L1B:1), (2:1, 4_PE:1, 2_W:1))
### \(A, B\) の値はこちらです。この問題は乱数値が使用されています。
_詳細データは省略。必要なら source_url を参照してください。_

## Explanation

前回の問題 [Mmul 4_16_16](https://mncore-challenge.preferred.jp/mnist/problem/matmul_notr_mab_lm_4_16_16/) のレイアウトは以下の通りでした。
A: (( 4:2), (2:1, 4_PE:1, 2_W:1)) B: ((16:2), (2:1, 4_PE:1, 2_W:1)) C: (( 4:2), (2:1, 4_PE:1, 2_W:1))
比較してみると、\(A,C\) の 1 次元目に `8_L2B:1, 8_L1B:1` とある通り、8 個の L2B, 8 個の L1B に分散して配置され、1 次元目の長さが 4 から 256 に 64 倍に増えています。

## Inputs

* \(A\) (\(0 \le A[{i, j}] \le 512\)): Float `$lm[0:16]`, `(256,16)/((8_L2B:1, 4:2, 8_L1B:1), (2:1, 4_PE:1, 2_W:1); B@[MAB])`
* \(B\) (\(0 \le B[{i, j}] \le 512\)): Float `$lm[16:80]`, `(16,16)/((16:2), (2:1, 4_PE:1, 2_W:1); B@[MAB,L1B,L2B])`

## Outputs

* \(C\): Float `$ln[0:16]`, `(256,16)/((8_L2B:1, 4:2, 8_L1B:1), (2:1, 4_PE:1, 2_W:1))` / \(0.00001\) 以下の絶対誤差が許容されます

## Testcases

* [testcase.vsm](https://mncore-challenge.preferred.jp/mnist/testcase/matmul_notr_pkg_lm_256_16_16/testcase.vsm)
