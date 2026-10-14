---
source_url: https://mncore-challenge.preferred.jp/problem/fizzbuzz_pe
slug: fizzbuzz_pe
fetched_at: 2026-10-14T00:39:07+00:00
---

# FizzBuzz PE

- Top: 9 lines / syttrea
- Par: 24 lines

## Problem Statement

各 PE の LM0 に置かれた \(8\) 要素の符号なし 32bit 整数について、
* \(15\) の倍数なら `0xFFFFBBBB`
* \(5\) の倍数でなく \(3\) の倍数なら `0x0000FFFF`
* \(3\) の倍数でなく \(5\) の倍数なら `0x0000BBBB`
* それ以外ならそのままの数字
に置き換えたものを LM1 に書き込んでください。

## Inputs

* \(A\) (\(1 \le A[{i}] \le 2^{15}\)): UInt `$lm[0:8]`, `/((8_L2B:1, 8_L1B:1, 16_MAB:1, 4_PE:1, 4:1, 2_W:1))`

## Outputs

* \(B\): UInt `$ln[0:8]`, `/((8_L2B:1, 8_L1B:1, 16_MAB:1, 4_PE:1, 4:1, 2_W:1))`

## Testcases

* [testcase.vsm](https://mncore-challenge.preferred.jp/testcase/fizzbuzz_pe/testcase.vsm)
