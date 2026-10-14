---
source_url: https://mncore-challenge.preferred.jp/problem/contains
slug: contains
fetched_at: 2026-10-14T00:38:59+00:00
---

# Contains

- Top: 20 lines / sosuupoyo
- Par: 220 lines

## Problem Statement

LM0上の `ULong` 配列 \(A\) の各要素 \(A[i]\) について、LM1上の `ULong` 配列 \(B\) に含まれているかどうか判定し、含まれているなら \(C[i]=1\)、そうでなければ \(C[i]=0\) としてLM1に出力してください。

## Inputs

* \(A\) (\(0 \le A[{i}] \le 1000\)): ULong `$lm[0:32]`, `/((8_L2B:1, 8_L1B:1, 16:1); B@[PE,MAB])`
* \(B\) (\(0 \le B[{i}] \le 1000\)): ULong `$ln[0:32]`, `/((16_MAB:1, 4_PE:1, 16:1); B@[L1B,L2B])`

## Outputs

* \(C\): ULong `$ln[32:64]`, `/((8_L2B:1, 8_L1B:1, 16:1))`

## Testcases

* [testcase.vsm](https://mncore-challenge.preferred.jp/testcase/contains/testcase.vsm)
