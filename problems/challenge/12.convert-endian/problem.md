---
source_url: https://mncore-challenge.preferred.jp/problem/convert_endian
slug: convert_endian
fetched_at: 2026-10-14T00:38:57+00:00
---

# Convert Endian

- Top: 3 lines / kik
- Par: 48 lines

## Problem Statement

入力をリトルエンディアンで並べられた \(8\) バイトで \(1\) ワードの列とみなし、これをビッグエンディアンに変換してください。
すなわち、入力の各要素 \(X[i]\) について \(Y[i]\) を以下のように計算してください。
```vsm
Y[i] = (
    ((X[i] >> 56) & 0x00000000000000FF)
  | ((X[i] >> 40) & 0x000000000000FF00)
  | ((X[i] >> 24) & 0x0000000000FF0000)
  | ((X[i] >> 8)  & 0x00000000FF000000)
  | ((X[i] << 8)  & 0x000000FF00000000)
  | ((X[i] << 24) & 0x0000FF0000000000)
  | ((X[i] << 40) & 0x00FF000000000000)
  | ((X[i] << 56) & 0xFF00000000000000)
)
```

## Inputs

* \(X\) (\(0 \le X[{i}] \le 2^{64}-1\)): ULong `$lm[0:2]`, `/((4_PE:1); B@[MAB,L1B,L2B])`

## Outputs

* \(Y\): ULong `$ln[0:2]`, `/((4_PE:1))`

## Testcases

* [testcase.vsm](https://mncore-challenge.preferred.jp/testcase/convert_endian/testcase.vsm)
