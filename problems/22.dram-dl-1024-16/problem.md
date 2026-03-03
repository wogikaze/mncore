---
source_url: https://mncore-challenge.preferred.jp/mnist/problem/dram_dl_1024_16/
slug: dram_dl_1024_16
fetched_at: 2026-03-02T23:59:51+00:00
---

# DL 1024_16

- Top: 8 lines / syttrea
- Par: 10 lines

## Problem Statement

DRAM に分割されて配置された shape = `(1024, 16)` の Float Tensor \(D\) を、
LM にある Tensor \(L\) に`((8_L2B:1, 16:2, 8_L1B:1), (2:1,4_PE:1, 2_W:1))`のレイアウトで格納してください。

## Explanation

サイズが 4 倍になりましたが、[DL 256_16](https://mncore-challenge.preferred.jp/mnist/problem/dram_dl_256_16/) と同様の命令で、解くことができます。
### おさらい
`L2B` について、入力が `4_L2B:2` で出力が `8_L2B:1` なので、各グループの DRAM にある 2048 長語を、2 個ずつの L2B に 1024 長語ずつ分配する必要があります。
出力に `8_L1B:1` が含まれるので、L2BM に下ろした値を 8 個の L1BM に分配する必要があります。
最後に、`MAB` が含まれずに `4_PE:1` が含まれるので、L1BM にある値を 4 個の PE に分配する必要があります。
使用する命令は以下のとおりです。
* `mvp/n1024 $d0 $lc0@.0` DRAM → L2BM 並列個別転送命令 [mvp](https://mncore-challenge.preferred.jp/memory-animation/?file=DRAM→L2BM%20parallel-unicast&movie=mvp%2Fn64%20%24d0%20%24lc0%40.1&frame=1)
* `l2bmd $lc0 $lb0` L2BM → L1BM 分配命令 [l2bmd](https://mncore-challenge.preferred.jp/memory-animation/?file=L2BM%E2%86%92L1BM%20distrib&movie=l2bmd%40%5B0%2C1%2C2%2C3%5D%20%24lc0%20%24lb0&frame=1)
* `l1bmm $llb0 $llm0v` 16x1MAB 放送 命令（2長語） [l1bmm](https://mncore-challenge.preferred.jp/memory-animation/?file=L1BM%E2%86%92MAB16x1%20bcast&movie=l1bmm%20%24llb0%20%24llp0&frame=1)
を使います。
L2BM → L1BM 分配にて、L2BM にある 1024 長語を分配しないといけませんが、[l2bmd](https://mncore-challenge.preferred.jp/memory-animation/?file=L2BM%E2%86%92L1BM%20distrib&movie=l2bmd%40%5B0%2C1%2C2%2C3%5D%20%24lc0%20%24lb0&frame=1) 命令は一命令で 256長語を L2BM から読み、8 個の L1B に 32長語の分配を行うので、4 命令必要です。
同様に、L1BM → PE でも、L1BM にある 128 長語を分配しないといけませんが、[l1bmm](https://mncore-challenge.preferred.jp/memory-animation/?file=L1BM%E2%86%92MAB16x1%20bcast&movie=l1bmm%20%24llb0%20%24llp0&frame=1) 命令は一命令で 32 長語を L1BM から読み、4 PE に 8 長語（16単語）ずつ分配するので、4 命令必要です。

## Inputs

* \(D\) (\(0 \le D[{i, j}] \le 2^{14}\)): Float `$d[0:2048]@0`, `(1024,16)/((4_L2B:2, 256:8), (8:1, 2_W:1); B@[4_L2B:2])`

## Outputs

* \(L\): Float `$lm[0:64]`, `(1024,16)/((8_L2B:1, 16:2, 8_L1B:1), (2:1,4_PE:1, 2_W:1))`

## Testcases

* [testcase.vsm](https://mncore-challenge.preferred.jp/mnist/testcase/dram_dl_1024_16/testcase.vsm)
