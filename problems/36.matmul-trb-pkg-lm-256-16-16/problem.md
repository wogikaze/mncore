---
source_url: https://mncore-challenge.preferred.jp/mnist/problem/matmul_trb_pkg_lm_256_16_16/
slug: matmul_trb_pkg_lm_256_16_16
fetched_at: 2026-03-02T23:59:53+00:00
---

# Mmul TB 256_16_16★

- Top: 12 lines / syttrea
- Par: 24 lines

## Problem Statement

\(256 \times 16\) 行列 \(A\) と、\(16 \times 16\) 行列 \(B\) に対して、行列積 \(C = A \times B^T\) (shape:\(256 \times 16\)) を計算してください。\(A,B,C\) のレイアウトは以下のとおりです。
A: ((8_L2B:1, 4:2, 8_L1B:1), (2:1, 4_PE:1, 2_W:1)) B: ((16:2), (2:1, 4_PE:1, 2_W:1)) C: ((8_L2B:1, 4:2, 8_L1B:1), (2:1, 4_PE:1, 2_W:1))
### \(A, B\) の値はこちらです。この問題は乱数値が使用されています。
_詳細データは省略。必要なら source_url を参照してください。_

## Explanation

\(A\) の 1 次元目が \(256\) と、[Mmul TB 4_16_16](https://mncore-challenge.preferred.jp/mnist/problem/matmul_trb_mab_lm_4_16_16/) の \(4\) に比べ、64 倍になっています。
レイアウトを確認すると、`(8_L2B:1, 4:2, 8_L1B:1)` と、長さ 256 の軸が 8 個の L2B, 8 個の L1B に分割して配置されています。
これに伴い、出力の 1 次元目のサイズも同様に \(256\) に増えています。
出力 \(C\) の 1 次元目のレイアウトも同じく `(8_L2B:1, 4:2, 8_L1B:1)` なので、出力も長さ 256 の軸が 8 個の L2B, 8 個の L1B に分割して配置されています。
### 実は…
[Mmul TB 4_16_16](https://mncore-challenge.preferred.jp/mnist/problem/matmul_trb_mab_lm_4_16_16/)
### というのも
\(A\) の 1 次元目が 8 個の L2B, 8 個の L1B に分割して配置され増えていますが、出力も同様のレイアウトです。
\(A\) の 1 次元目が増えても、内積すべき要素やサイズは変わらず、出力が増えるだけで、増えた出力も 8 個の L2B, 8 個の L1B に分割されているので、L1B ごとに独立に考えられます。

## Inputs

* \(A\) (\(0 \le A[{i, j}] \le 512\)): Float `$lm[0:16]`, `(256,16)/((8_L2B:1, 4:2, 8_L1B:1), (2:1, 4_PE:1, 2_W:1); B@[MAB])`
* \(B\) (\(0 \le B[{i, j}] \le 512\)): Float `$lm[16:80]`, `(16,16)/((16:2), (2:1, 4_PE:1, 2_W:1); B@[MAB,L1B,L2B])`

## Outputs

* \(C\): Float `$ln[0:16]`, `(256,16)/((8_L2B:1, 4:2, 8_L1B:1), (2:1, 4_PE:1, 2_W:1))` / \(0.00001\) 以下の絶対誤差が許容されます

## Testcases

* [testcase.vsm](https://mncore-challenge.preferred.jp/mnist/testcase/matmul_trb_pkg_lm_256_16_16/testcase.vsm)
