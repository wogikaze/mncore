---
source_url: https://mncore-challenge.preferred.jp/mnist/problem/matmul_trb_mab_lm_4_16_16/
slug: matmul_trb_mab_lm_4_16_16
fetched_at: 2026-03-02T23:59:53+00:00
---

# Mmul TB 4_16_16

- Top: 12 lines / syttrea
- Par: 24 lines

## Problem Statement

\(4 \times 16\) 行列 \(A\) と、\(16 \times 16\) 行列 \(B\) に対して、行列積 \(C = A \times B^T\) (shape:\(4 \times 16\)) を計算してください。\(A,B,C\) のレイアウトは以下のとおりです。
A: ((4:2), (2:1, 4_PE:1, 2_W:1)) B: ((16:2), (2:1, 4_PE:1, 2_W:1)) C: ((4:2), (2:1, 4_PE:1, 2_W:1))
### \(A, B, C\) の値はこちらです。
_詳細データは省略。必要なら source_url を参照してください。_

## Explanation

[Mmul TB 4_8_8](https://mncore-challenge.preferred.jp/mnist/problem/matmul_trb_mab_lm_4_8_8/)
[Mmul TB 4_8_16](https://mncore-challenge.preferred.jp/mnist/problem/matmul_trb_mab_lm_4_8_16/)
[Mmul TB 4_16_8](https://mncore-challenge.preferred.jp/mnist/problem/matmul_trb_mab_lm_4_16_8/)
`gmmul` を 2 回、`gmfma` を 2 回使います。
### 回答例（1/4）
gbfn $lm16v4 $nowrite gmwrite $aluf $ly0 gbfn $lm32v4 $nowrite gmwrite $aluf $ly4 gbfn $lm0v4 $nowrite gmmul $ly $aluf $ls0v4

## Inputs

* \(A\) (\(0 \le A[{i, j}] \le 64\)): Float `$lm[0:16]`, `(4,16)/((4:2), (2:1, 4_PE:1, 2_W:1); B@[MAB,L1B,L2B])`
* \(B\) (\(100 \le B[{i, j}] \le 356\)): Float `$lm[16:80]`, `(16,16)/((16:2), (2:1, 4_PE:1, 2_W:1); B@[MAB,L1B,L2B])`

## Outputs

* \(C\): Float `$ln[0:16]`, `(4,16)/((4:2), (2:1, 4_PE:1, 2_W:1))` / \(0.00001\) 以下の絶対誤差が許容されます

## Testcases

* [testcase.vsm](https://mncore-challenge.preferred.jp/mnist/testcase/matmul_trb_mab_lm_4_16_16/testcase.vsm)
