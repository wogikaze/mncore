---
source_url: https://mncore-challenge.preferred.jp/mnist/problem/dram_ul_16_1024/
slug: dram_ul_16_1024
fetched_at: 2026-03-02T23:59:51+00:00
---

# UL 16_1024

- Top: 13 lines / syttrea
- Par: 43 lines

## Problem Statement

LM に `((16:1), (8_MAB:2, 8_L1B:1, 2_MAB:1, 4_PE:1, 2_W:1))` のレイアウトで分割されて配置された shape = `(16, 1024)` の Float Tensor \(L\) を、DRAM にある Tensor \(D\) に指定のレイアウトで格納してください。

## Explanation

[DL 16_1024](https://mncore-challenge.preferred.jp/mnist/problem/dram_dl_16_1024/)
DL 16_1024 では、8 つの L2BM への放送を効率化するために、一旦 PDM を経由しましたが、今回の問題では PDM を経由せず、単に 0 番 L2BM の値を各 DRAM に転送すれば良いでしょう。
### 具体的な命令
* `l1bmd` 結合命令 [[Link]](https://mncore-challenge.preferred.jp/memory-animation/?file=PE→L1BM%20concat&movie=l1bmd%20%24lp0%20%24lb0&frame=1)
* `l2bmd` L1BM → L2BM 結合 [[Link]](https://mncore-challenge.preferred.jp/memory-animation/?file=L1BM→L2BM%20concat&movie=l2bmd%20%24lb0%20%24lc0&frame=1)
* `mvp/n2048 $lc0@0.0 $d0@0` L2BM → DRAM 単独個別転送命令 [[Link]](https://mncore-challenge.preferred.jp/memory-animation/?file=L2BM→DRAM%20parallel-unicast&movie=mvp%2Fn64%20%24lc0%40.1%20%24d0&frame=1)
を使用します。

## Inputs

* \(L\) (\(0 \le L[{i, j}] \le 2^{14}\)): Float `$lm[0:32]`, `(16,1024)/((16:1), (8_MAB:2, 8_L1B:1, 2_MAB:1, 4_PE:1, 2_W:1); B@[L2B])`

## Outputs

* \(D\): Float `$d[0:2048]@0`, `(16,1024)/((4_L2B:2, 4:512), (512:1, 2_W:1))`

## Testcases

* [testcase.vsm](https://mncore-challenge.preferred.jp/mnist/testcase/dram_ul_16_1024/testcase.vsm)
