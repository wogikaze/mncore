---
source_url: https://mncore-challenge.preferred.jp/mnist/problem/mul_const/
slug: mul_const
fetched_at: 2026-03-02T23:59:43+00:00
---

# FMul 7

- Top: 5 lines / Wogikaze
- Par: 6 lines

## Problem Statement

LM上の Float \(16\times1024\) 行列 \(A\) に対して \(C = A \times 7.0\) を計算し、LM上に出力してください。

## Explanation

イメージとしては、`$ln[0:32] = $lm[0:32] * 7.0` を行えばよいです。
ただし、今回は浮動小数点数の計算なので、`fvmul` 命令を使います。
`imm f"7.0" $t` などで即値を定義し、それを使って掛けると良いでしょう。

## Inputs

* \(A\) (\(-512 \le A[{i, j}] \le 512\)): Float `$lm[0:32]`, `(16,1024)/((16:1), (8_MAB:2, 8_L1B:1, 2_MAB:1, 4_PE:1, 2_W:1); B@[L2B])`

## Outputs

* \(C\): Float `$ln[0:32]`, `(16,1024)/((16:1), (8_MAB:2, 8_L1B:1, 2_MAB:1, 4_PE:1, 2_W:1))` / \(0.0001\) 以下の絶対誤差が許容されます

## Testcases

* [testcase.vsm](https://mncore-challenge.preferred.jp/mnist/testcase/mul_const/testcase.vsm)
