---
source_url: https://mncore-challenge.preferred.jp/mnist/problem/dram_ul_16_16/
slug: dram_ul_16_16
fetched_at: 2026-03-02T23:59:52+00:00
---

# UL 16_16

- Top: 9 lines / syttrea
- Par: 18 lines

## Problem Statement

LM に `((16:2), (2:1, 4_PE:1, 2_W:1))` のレイアウトで分割されて配置された shape = `(16, 16)` の Float Tensor \(L\) を、DRAM にある Tensor \(D\) に指定のレイアウトで格納してください。

## Explanation

[DL 16_16](https://mncore-challenge.preferred.jp/mnist/problem/dram_dl_16_16/)
Download 操作の逆に対応した命令があるので、それを使います。
`DL 16_16` では、DRAM → L2BM への放送を、PDM 経由で効率的に行う方法を紹介しましたが、今回の L2BM → DRAM に関しては PDM を経由せず、0 番 L2BM の内容だけを使って 4 グループの DRAM にそれぞれ個別転送する方法で良いでしょう。
### 使用する命令
* `l1bmm@0` (MAB) 16x1 個別転送 命令 [l1bmm@0](https://mncore-challenge.preferred.jp/memory-animation/?file=MAB16x1%E2%86%92L1BM%20single-unicast&movie=l1bmm%401%20%24llp0%20%24llb0&frame=1)
* `l2bm@0` L1BM → L2BM 個別転送 [l2bm@0](https://mncore-challenge.preferred.jp/memory-animation/?file=L1BM→L2BM%20single-unicast&movie=l2bm%401%20%24lb0%20%24lc0&frame=1)
* `mvp/n64 $lc0@0.0 $d0@0` L2BM → DRAM 単独個別転送命令 [mvp](https://mncore-challenge.preferred.jp/memory-animation/?file=L2BM→DRAM%20parallel-unicast&movie=mvp%2Fn64%20%24lc0%40.1%20%24d0&frame=1)

## Inputs

* \(L\) (\(0 \le L[{i, j}] \le 256\)): Float `$lm[0:64]`, `(16,16)/((16:2), (2:1, 4_PE:1, 2_W:1); B@[MAB,L1B,L2B])`

## Outputs

* \(D\): Float `$d[0:32]@0`, `(16,16)/((4_L2B:2, 4:8), (8:1, 2_W:1))`

## Testcases

* [testcase.vsm](https://mncore-challenge.preferred.jp/mnist/testcase/dram_ul_16_16/testcase.vsm)
