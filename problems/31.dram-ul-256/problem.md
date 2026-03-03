---
source_url: https://mncore-challenge.preferred.jp/mnist/problem/dram_ul_256/
slug: dram_ul_256
fetched_at: 2026-03-02T23:59:52+00:00
---

# UL 256

- Top: 12 lines / syttrea
- Par: 29 lines

## Problem Statement

LM に `((4_L2B:2, 32:1, 2_W:1))` のレイアウトで分割されて配置された長さ \(256\) の Float Vector \(L\) を、DRAM にある Vector \(D\) に指定のレイアウトで格納してください。

## Explanation

[DL 256](https://mncore-challenge.preferred.jp/mnist/problem/dram_dl_256/)
l1bmp
[PE 放送命令](https://mncore-challenge.preferred.jp/memory-animation/?file=L1BM%E2%86%92PE%20bcast&movie=l1bmp%20%24lb0%20%24lp0&frame=1)
なんとか頑張りましょう。
### 考え方・方針
`l1bmp` の逆操作にあたるような、1 PE から連続したメモリを L1BM に転送する命令は存在せず、必ず 4 PE が同時に転送されます。
そこで、4 PE で共有で、レイアウトの転置が行える行列レジスタを使った[転置命令](https://mncore-challenge.preferred.jp/memory-animation/?file=PE→MAU→PE%20matrix-transpose&movie=dmwrite%20%24l...%2C%20dmread%20%24l...&frame=1)を使うことで、1 PE のメモリを 4 PE の先頭に移動することができます。
その状態で、長語 16x1 個別転送命令 [l1bmm@0](https://mncore-challenge.preferred.jp/memory-animation/?file=MAB16x1→L1BM%20single-unicast&movie=l1bmm%401%20%24lp0%20%24lb0&frame=1) を使うことで、L1BM の先頭 4 長語に、PE0 の 4 長語を転送することができます。
なお、倍精度の `dmwrite`, `dmread` を使用しないと、例えば `f(mwrite|mread)` を使用すると、長語内の `(2_W)` も転置されてひっくり返ってしまいます。
まとめると、
* `dmwrite`, `dmread`, `l1bmm@0` をそれぞれ 8 回
* `l2bm@0` L1BM → L2BM 個別転送 [l2bm@0](https://mncore-challenge.preferred.jp/memory-animation/?file=L1BM→L2BM%20single-unicast&movie=l2bm%401%20%24lb0%20%24lc0&frame=1)
* `mvp/n64 $lc0@.0 $d0`DRAM → L2BM 並列個別転送命令 [mvp](https://mncore-challenge.preferred.jp/memory-animation/?file=L2BM→DRAM%20parallel-unicast&movie=mvp%2Fn64%20%24lc0%40.1%20%24d0&frame=1)
で実現できます。

## Inputs

* \(L\) (\(0 \le L[{i}] \le 256\)): Float `$lm[0:64]`, `(256)/((4_L2B:2, 32:1, 2_W:1); B@[PE,MAB,L1B])`

## Outputs

* \(D\): Float `$d[0:32]@0`, `(256)/((4_L2B:2, 32:1, 2_W:1))`

## Testcases

* [testcase.vsm](https://mncore-challenge.preferred.jp/mnist/testcase/dram_ul_256/testcase.vsm)
