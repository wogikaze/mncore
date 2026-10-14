---
source_url: https://mncore-challenge.preferred.jp/problem/bit_reverse
slug: bit_reverse
fetched_at: 2026-10-14T00:39:07+00:00
---

# Bit Reverse

- Top: 10 lines / syttrea
- Par: 330 lines

## Problem Statement

LM0上の入力を \(1\) 次元（\(1024\) ビット）のビット列とみなし、これを逆順に並べたものをLM1上に出力してください。

## Inputs

* \(X\) (\(0 \le X[{i}] \le 2^{64}-1\)): ULong `$lm[0:8]`, `/((4:1, 4_PE:1); B@[MAB,L1B,L2B])`

## Outputs

* \(Y\): ULong `$ln[0:8]`, `/((4:1, 4_PE:1))`

## Testcases

* [testcase.vsm](https://mncore-challenge.preferred.jp/testcase/bit_reverse/testcase.vsm)
