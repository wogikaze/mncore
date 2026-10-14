---
source_url: https://mncore-challenge.preferred.jp/problem/inversion
slug: inversion
fetched_at: 2026-10-14T00:39:05+00:00
---

# Inversion

- Top: 31 lines / sosuupoyo
- Par: 1080 lines

## Problem Statement

LM0上の \(2\) 次元 `UInt` 配列 \(A\) について、転倒数、すなわち \(j < k\) かつ \(A[i, j] > A[i, k]\) であるような \((j, k)\) の組の数 \(I[i]\) を各 \(i\) について計算してLM1に出力してください。

## Inputs

* \(A\) (\(0 \le A[{i, j}] \le 100\)): UInt `$lm[0:128]`, `/((16_MAB:1, 4_PE:1, 2_W:1), (64:1); B@[L1B,L2B])`

## Outputs

* \(I\): UInt `$ln[0:2]`, `/((16_MAB:1, 4_PE:1, 2_W:1))`

## Testcases

* [testcase.vsm](https://mncore-challenge.preferred.jp/testcase/inversion/testcase.vsm)
