---
source_url: https://mncore-challenge.preferred.jp/mnist/problem/dram_dl_256_16_l2b/
slug: dram_dl_256_16_l2b
fetched_at: 2026-03-02T23:59:51+00:00
---

# DL L2B 256_16

- Top: 12 lines / syttrea
- Par: 14 lines

## Problem Statement

DRAM に分割されて配置された shape = `(256, 16)` の Float Tensor \(D\) を、
LM にある Tensor \(L\) に`((8_L2B:1, 32:2), (2:1, 4_PE:1, 2_W:1))`のレイアウトで格納してください。

## Explanation

[DL 256_16](https://mncore-challenge.preferred.jp/mnist/problem/dram_dl_256_16/)
今回の 1 次元目の入出力は `(4_L2B:2, 64:8)` → `(8_L2B:1, 32:2)` です。 4 つの L2B にそれぞれ \(64\times8=512\) 長語ずつ分割して配置された DRAM の内容を、8 つの L2B に分割して転送する必要があります。
`mvp/n256 $d0 $lc0@.0` DRAM → L2BM 並列個別転送命令 [mvp](https://mncore-challenge.preferred.jp/memory-animation/?file=DRAM→L2BM%20parallel-unicast&movie=mvp%2Fn64%20%24d0%20%24lc0%40.1&frame=1) 命令を 2 回用い、256 長語ずつ、グループ内の 2 つの L2B に分配すればよいでしょう。
その後の分割の方法は、[DL PE 256_16](https://mncore-challenge.preferred.jp/mnist/problem/dram_dl_256_16p/) と同様なので、発行する命令数に気をつけながら同様に転送すればよいでしょう。
### 使用する命令
* `mvp/n256 $d0 $lc0@.0` DRAM → L2BM 並列個別転送命令 [mvp](https://mncore-challenge.preferred.jp/memory-animation/?file=DRAM→L2BM%20parallel-unicast&movie=mvp%2Fn64%20%24d0%20%24lc0%40.1&frame=1)
* L2BM → L1BM 放送命令 [l2bmb](https://mncore-challenge.preferred.jp/memory-animation/?file=L2BM%E2%86%92L1BM%20bcast&movie=l2bmb%40%5B1%2C3%2C5%2C7%5D%20%24lc0%20%24lb0&frame=1)
* 16x1MAB 放送命令 [l1bmm](https://mncore-challenge.preferred.jp/memory-animation/?file=L1BM%E2%86%92MAB16x1%20bcast&movie=l1bmm%20%24llb0%20%24llp0&frame=1)
を使います。

## Inputs

* \(D\) (\(0 \le D[{i, j}] \le 4096\)): Float `$d[0:512]@0`, `(256,16)/((4_L2B:2, 64:8), (8:1, 2_W:1); B@[4_L2B:2])`

## Outputs

* \(L\): Float `$lm[0:128]`, `(256,16)/((8_L2B:1, 32:2), (2:1, 4_PE:1, 2_W:1))`

## Testcases

* [testcase.vsm](https://mncore-challenge.preferred.jp/mnist/testcase/dram_dl_256_16_l2b/testcase.vsm)
