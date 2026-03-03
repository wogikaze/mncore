---
source_url: https://mncore-challenge.preferred.jp/mnist/problem/dram_ul_256_16p/
slug: dram_ul_256_16p
fetched_at: 2026-03-02T23:59:51+00:00
---

# UL PE 256_16

- Top: 10 lines / syttrea
- Par: 42 lines

## Problem Statement

LM に `((4_L2B:2, 64:2), (2:1, 4_PE:1, 2_W:1))` のレイアウトで分割されて配置された shape = `(256, 16)` の Float Tensor \(L\) を、DRAM にある Tensor \(D\) に指定のレイアウトで格納してください。

## Explanation

[DL PE 256_16](https://mncore-challenge.preferred.jp/mnist/problem/dram_dl_256_16p/)
### 考え方・方針
* `l1bmm@0` (MAB) 16x1 個別転送 命令 [l1bmm@0](https://mncore-challenge.preferred.jp/memory-animation/?file=MAB16x1%E2%86%92L1BM%20single-unicast&movie=l1bmm%401%20%24llp0%20%24llb0&frame=1)
* `l2bm@0` L1BM → L2BM 個別転送 [l1bmm@0](https://mncore-challenge.preferred.jp/memory-animation/?file=L1BM→L2BM%20single-unicast&movie=l2bm%401%20%24lb0%20%24lc0&frame=1)
* `mvp/n512 $lc0@.0 $d0` L2BM → DRAM 並列個別転送命令 [mvp](https://mncore-challenge.preferred.jp/memory-animation/?file=L2BM→DRAM%20parallel-unicast&movie=mvp%2Fn64%20%24lc0%40.1%20%24d0&frame=1)
を使います。
PE→L1BM→L2BM の転送量が多いため、`l1bmm@0`, `l2bm@0` 命令は DL PE 256_16 と同様に複数発行する必要があります。

## Inputs

* \(L\) (\(0 \le L[{i, j}] \le 4096\)): Float `$lm[0:256]`, `(256,16)/((4_L2B:2, 64:2), (2:1, 4_PE:1, 2_W:1); B@[MAB,L1B])`

## Outputs

* \(D\): Float `$d[0:512]@0`, `(256,16)/((4_L2B:2, 64:8), (8:1, 2_W:1))`

## Testcases

* [testcase.vsm](https://mncore-challenge.preferred.jp/mnist/testcase/dram_ul_256_16p/testcase.vsm)
