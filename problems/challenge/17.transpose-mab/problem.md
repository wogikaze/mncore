---
source_url: https://mncore-challenge.preferred.jp/problem/transpose_mab
slug: transpose_mab
fetched_at: 2026-10-14T00:39:02+00:00
---

# Transpose MAB

- Top: 15 lines / sosuupoyo
- Par: 112 lines

## Problem Statement

表記に従ってレイアウトを変換しつつ、LM0 から LM1 にコピーしてください。

## Inputs

* \(X\) (\(-1 \le X[{i}] \le 1\)): Double `$lm[0:32]`, `/((16_MAB:1, 16:1); B@[PE,L1B,L2B])`

## Outputs

* \(Y\): Double `$ln[0:32]`, `/((16:1, 16_MAB:1))`

## Testcases

* [testcase.vsm](https://mncore-challenge.preferred.jp/testcase/transpose_mab/testcase.vsm)
