---
source_url: https://mncore-challenge.preferred.jp/mnist/problem/dram_dl_256_1024/
slug: dram_dl_256_1024
fetched_at: 2026-03-02T23:59:51+00:00
---

# DL 256_1024

- Top: 69 lines / syttrea
- Par: 74 lines

## Problem Statement

DRAM に分割されて配置された shape = `(256, 1024)` の Float Tensor \(D\) を、
LM にある Tensor \(L\) に`((8_L2B:1, 32:1), (8_MAB:2, 8_L1B:1, 2_MAB:1, 4_PE:1, 2_W:1))`のレイアウトで格納してください。

## Explanation

レイアウトを見ると、`L2B`, `L1B`, `MAB`, `PE` のすべてが含まれているので、各 L2B, L1B, MAB, PE に分配することが分かります。
### 考え方・方針
使用する命令は以下のとおりです。
* `mvp/n16384 $d0 $lc0@.0` DRAM → L2BM 並列個別転送命令 [mvp](https://mncore-challenge.preferred.jp/memory-animation/?file=DRAM→L2BM%20parallel-unicast&movie=mvp%2Fn64%20%24d0%20%24lc0%40.1&frame=1)
* `l2bmd $lc0 $lb0` L2BM → L1BM 分配命令 [l2bmd](https://mncore-challenge.preferred.jp/memory-animation/?file=L2BM%E2%86%92L1BM%20distrib&movie=l2bmd%40%5B0%2C1%2C2%2C3%5D%20%24lc0%20%24lb0&frame=1)
* `l1bmd $lb0 $lm0v` (PE) 分配命令 [l1bmd](https://mncore-challenge.preferred.jp/memory-animation/?file=L1BM%E2%86%92PE%20distrib&movie=l1bmd%20%24lb0%20%24lp0&frame=1)
を使います。
各 DRAM にそれぞれ \(32768\) 長語と大量の値が配置され、分配しながら下ろしていくとは言え、`l2bmd` 命令を \(64\) 回、`l1bmd` 命令を \(8\) 回発行する必要があり、最終的に各 PE に \(64\) 単語を分配します。

## Inputs

* \(D\) (\(0 \le D[{i, j}] \le 2^{18}\)): Float `$d[0:32768]@0`, `(256,1024)/((4_L2B:2, 64:512), (512:1, 2_W:1); B@[4_L2B:2])`

## Outputs

* \(L\): Float `$lm[0:64]`, `(256,1024)/((8_L2B:1, 32:1), (8_MAB:2, 8_L1B:1, 2_MAB:1, 4_PE:1, 2_W:1))`

## Testcases

* [testcase.vsm](https://mncore-challenge.preferred.jp/mnist/testcase/dram_dl_256_1024/testcase.vsm)
