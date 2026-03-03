---
source_url: https://mncore-challenge.preferred.jp/mnist/problem/matmul_tra_mab_lm_16_32_8/
slug: matmul_tra_mab_lm_16_32_8
fetched_at: 2026-03-02T23:59:59+00:00
---

# Mmul TA 16_32_8

- Top: 17 lines / syttrea
- Par: 96 lines

## Problem Statement

\(32 \times 16\) 行列 \(A\) と、\(32 \times 8\) 行列 \(B\) に対して、行列積 \(C = A^T \times B\) (shape:\(16 \times 8\)) を計算してください。\(A,B,C\) のレイアウトは以下のとおりです。
A: ((32:2), (2:1, 4_PE:1, 2_W:1)) B: ((32:1), (4_PE:1, 2_W:1)) C: ((16:1), (4_PE:1, 2_W:1))
### \(A, B, C\) の値はこちらです。
_詳細データは省略。必要なら source_url を参照してください。_

## Explanation

### 方針
行列 \(A, B, C\) を、\(8\times8\) の単位の小行列に分けて考えると、以下のようになります。
A = [ A00, A01 ] [ A10, A11 ] [ A20, A21 ] [ A30, A31 ] B = [ B0 ] [ B1 ] [ B2 ] [ B3 ]
### このとき、求める行列 \(C\) は、このような分割と計算になります。
C0: [ A00 x B0 + A10 x B1 + A20 x B2 + A30 x B3 ] C1: [ A01 x B0 + A11 x B1 + A21 x B2 + A31 x B3 ]
### 行列 \(A, B, C\) の小行列のアドレス
A00 $lm0v4, $lm16v4 A01 $lm2v4, $lm18v4 A10 $lm32v4, $lm48v4 A11 $lm34v4, $lm50v4 A20 $lm64v4, $lm80v4 A21 $lm66v4, $lm82v4 A30 $lm96v4, $lm112v4 A31 $lm98v4, $lm114v4 B0 $lm128v, $lm136v B1 $lm144v, $lm152v B2 $lm160v, $lm168v B3 $lm176v, $lm184v C0 $ln0v, $ln8v C1 $ln16v, $ln24v

## Inputs

* \(A\) (\(0 \le A[{i, j}] \le 512\)): Float `$lm[0:128]`, `(32,16)/((32:2), (2:1, 4_PE:1, 2_W:1); B@[MAB,L1B,L2B])`
* \(B\) (\(-256 \le B[{i, j}] \le 0\)): Float `$lm[128:192]`, `(32,8)/((32:1), (4_PE:1, 2_W:1); B@[MAB,L1B,L2B])`

## Outputs

* \(C\): Float `$ln[0:32]`, `(16,8)/((16:1), (4_PE:1, 2_W:1))` / \(0.00001\) 以下の絶対誤差が許容されます

## Testcases

* [testcase.vsm](https://mncore-challenge.preferred.jp/mnist/testcase/matmul_tra_mab_lm_16_32_8/testcase.vsm)
