---
source_url: https://mncore-challenge.preferred.jp/problem/mod3
slug: mod3
fetched_at: 2026-10-14T00:38:57+00:00
---

# Mod 3

- Top: 8 lines / syttrea
- Par: 124 lines

## Problem Statement

LM0上の `UInt` 配列 \(X\) の各要素 \(X[i]\) に対して \(Y[i] = X[i] \bmod 3\) を計算し、LM1上に出力してください。

## Inputs

* \(X\) (\(0 \le X[{i}] \le 255\)): UInt `$lm[0:32]`, `/((16_MAB:1, 4_PE:1, 16:1, 2_W:1); B@[L1B,L2B])`

## Outputs

* \(Y\): UInt `$ln[0:32]`, `/((16_MAB:1, 4_PE:1, 16:1, 2_W:1))`

## Testcases

* [testcase.vsm](https://mncore-challenge.preferred.jp/testcase/mod3/testcase.vsm)
