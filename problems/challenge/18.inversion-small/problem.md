---
source_url: https://mncore-challenge.preferred.jp/problem/inversion_small
slug: inversion_small
fetched_at: 2026-10-14T00:39:02+00:00
---

# Inversion Small

- Top: 9 lines / logicmachine
- Par: 359 lines

## Problem Statement

LM0上の \(2\) 次元 `ULong` 配列 \(A\) について、転倒数、すなわち \(j < k\) かつ \(A[i, j] > A[i, k]\) であるような \((j, k)\) の組の数 \(I[i]\) を各 \(i\) について計算してLM1に出力してください。
入力の \(A[0]\) は \([4, 2, 6, 4, 8, 6, 1, 3, 8, 1, 9, 8, 9, 4, 1, 3]\) の \(16\) 要素の配列ですが、この転倒数は \(52\) なので \(I[0] = 52\) になります。

## Inputs

* \(A\) (\(0 \le A[{i, j}] \le 10\)): ULong `$lm[0:32]`, `/((8_L2B:1, 8_L1B:1), (16:1); B@[PE,MAB])`

## Outputs

* \(I\): ULong `$ln[0:2]`, `/((8_L2B:1, 8_L1B:1))`

## Testcases

* [testcase.vsm](https://mncore-challenge.preferred.jp/testcase/inversion_small/testcase.vsm)
