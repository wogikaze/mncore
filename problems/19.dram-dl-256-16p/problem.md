---
source_url: https://mncore-challenge.preferred.jp/mnist/problem/dram_dl_256_16p/
slug: dram_dl_256_16p
fetched_at: 2026-03-02T23:59:50+00:00
---

# DL PE 256_16

- Top: 19 lines / syttrea
- Par: 41 lines

## Problem Statement

DRAM に分割されて配置された shape = `(256, 16)` の Float Tensor \(D\) を、
LM にある Tensor \(L\) に`((4_L2B:2, 64:2), (2:1, 4_PE:1, 2_W:1))`のレイアウトで格納してください。

## Explanation

[DL 256_16](https://mncore-challenge.preferred.jp/mnist/problem/dram_dl_256_16/)
前回の出力 1 次元目は `(8_L2B:1, 4:2, 8_L1B:1)` でしたが、今回は `(4_L2B:2, 64:2)` です。
前回の `L2B` は入出力で `4_L2B:2` → `8_L2B:1` だったので、各グループの DRAM から 2 個ずつの L2B に分配しました。
今回は、入出力で `4_L2B:2` → `4_L2B:2` と同じなので、各グループの DRAM からグループ内の L2B に分配せず、512 長語ぶんの内容をグループ内放送命令 [mvb2](https://mncore-challenge.preferred.jp/memory-animation/?file=DRAM%E2%86%92L2BM%20ingroup-bcast&movie=mvb2%2Fn64%20%24d0%20%24lc0&frame=1) で送ります。
前回は分配をしたので転送量は 256 長語でしたが、今回は 512 長語なので `mvb2/n512` とすると良いでしょう。
次に `L1B` に注目すると、今回の出力レイアウトには登場しないので、L2BM にある 512 長語の内容を各 L1B に同じ内容を放送することが読み取れます。L2BM → L1BM 放送命令 [l2bmb](https://mncore-challenge.preferred.jp/memory-animation/?file=L2BM%E2%86%92L1BM%20bcast&movie=l2bmb%40%5B1%2C3%2C5%2C7%5D%20%24lc0%20%24lb0&frame=1) を使います。
`l2bmb` 命令は、1 命令で 64 長語を読み出し、8 個の L1BM に 64 長語をそのまま放送する命令です。今回は 512 長語を転送するので、`l2bmb` 命令を 8 回発行すれば良いでしょう。
最後に、`MAB` と `PE` ですが、前回と同じく `4_PE:1` はあるけど `MAB` は含まれないので、16x1MAB 放送命令 [l1bmm](https://mncore-challenge.preferred.jp/memory-animation/?file=L1BM%E2%86%92MAB16x1%20bcast&movie=l1bmm%20%24llb0%20%24llp0&frame=1)を使います。
ただし、今回は L1BM にある 512 長語の内容を、各 PE に 128 長語ずつ放送する必要があります。`l1bmm` 命令は 2 長語動作のときは L1BM から 32 長語を読み出し、各 PE に 8長語（16単語）ずつ書き込みます。
L1BM は長語アドレッシング、PE は単語アドレッシングなので、
l1bmm $llb0 $llm0v l1bmm $llb32 $llm16v ...
のように、16 回発行すれば良いでしょう。

## Inputs

* \(D\) (\(0 \le D[{i, j}] \le 4096\)): Float `$d[0:512]@0`, `(256,16)/((4_L2B:2, 64:8), (8:1, 2_W:1); B@[4_L2B:2])`

## Outputs

* \(L\): Float `$lm[0:256]`, `(256,16)/((4_L2B:2, 64:2), (2:1, 4_PE:1, 2_W:1))`

## Testcases

* [testcase.vsm](https://mncore-challenge.preferred.jp/mnist/testcase/dram_dl_256_16p/testcase.vsm)
