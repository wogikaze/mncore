---
source_url: https://mncore-challenge.preferred.jp/mnist/problem/matmul_trb_mab_lm_32_8_16/
slug: matmul_trb_mab_lm_32_8_16
fetched_at: 2026-03-02T23:59:53+00:00
---

# Mmul TB 32_8_16

- Top: 17 lines / syttrea
- Par: 96 lines

## Problem Statement

\(32 \times 8\) 行列 \(A\) と、\(16 \times 8\) 行列 \(B\) に対して、行列積 \(C = A \times B^T\) (shape:\(32 \times 16\)) を計算してください。\(A,B,C\) のレイアウトは以下のとおりです。
A: ((32:1), (4_PE:1, 2_W:1)) B: ((16:1), (4_PE:1, 2_W:1)) C: ((32:2), (2:1, 4_PE:1, 2_W:1))
### \(A, B, C\) の値はこちらです。
_詳細データは省略。必要なら source_url を参照してください。_

## Explanation

[Mmul TB 4_8_16](https://mncore-challenge.preferred.jp/mnist/problem/matmul_trb_mab_lm_4_8_16/)
gmmul
gmfma
入力 \(A\) が `$lm[0:8]` から `$lm[0:64]` に変わり、\(B\) も `$lm[8:40]` から `$lm[64:96]` に変わったことに対応しましょう。
答えをスクリプトで生成すると良いかもしれません。
### 回答例（1/8）
[Mmul TB 4_8_16](https://mncore-challenge.preferred.jp/mnist/problem/matmul_trb_mab_lm_4_8_16/)
gbfn $lm64v $nowrite # $lm8v から変更 gmwrite $aluf $ly0 gbfn $lm72v $nowrite # $lm16v から変更 gmwrite $aluf $ly4 gbfn $lm0v $nowrite gmmul $ly $aluf $ln0v4 gbfn $lm80v $nowrite # $lm24v から変更 gmwrite $aluf $ly0 gbfn $lm88v $nowrite # $lm32v から変更 gmwrite $aluf $ly4 gbfn $lm0v $nowrite gmmul $ly $aluf $ln2v4
に変更することで、`64 value(s) correct, but 448 value(s) mismatch` と、64/512 (=1/8) が合うようになります。
入力 \(A\) の `$lm[64:96]` を処理して、`$ln[0:16]` に出力が終えたところなので、残りの 7/8 も同様に処理しましょう。

## Inputs

* \(A\) (\(0 \le A[{i, j}] \le 256\)): Float `$lm[0:64]`, `(32,8)/((32:1), (4_PE:1, 2_W:1); B@[MAB,L1B,L2B])`
* \(B\) (\(300 \le B[{i, j}] \le 428\)): Float `$lm[64:96]`, `(16,8)/((16:1), (4_PE:1, 2_W:1); B@[MAB,L1B,L2B])`

## Outputs

* \(C\): Float `$ln[0:128]`, `(32,16)/((32:2), (2:1, 4_PE:1, 2_W:1))` / \(0.00001\) 以下の絶対誤差が許容されます

## Testcases

* [testcase.vsm](https://mncore-challenge.preferred.jp/mnist/testcase/matmul_trb_mab_lm_32_8_16/testcase.vsm)
