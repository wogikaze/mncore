---
source_url: https://mncore-challenge.preferred.jp/mnist/problem/dram_dl_16_16/
slug: dram_dl_16_16
fetched_at: 2026-03-02T23:59:52+00:00
---

# DL 16_16

- Top: 11 lines / syttrea
- Par: 18 lines

## Problem Statement

DRAM に分割されて配置された shape = `(16, 16)` の Float Tensor \(D\) を、
LM にある Tensor \(L\) に`((16:2), (2:1, 4_PE:1, 2_W:1))`のレイアウトで格納してください。

## Explanation

出力レイアウトに `L2B`, `L1B`, `MAB` は含まれていないので、すべての `MAB` で同じ内容を放送することが分かります。`4_PE:1` は含まれているので、4 個の PE には分配します。
### 考え方・方針
4 つの DRAM に 32 長語ずつ分割して配置された値を、8 個の L2BM に同じ内容を放送したいです。
様々な方法がありますが、[DL 16](https://mncore-challenge.preferred.jp/mnist/problem/dram_dl_16/) と似た方針で、グループ 0 の PDM に、`DRAM → PDM 単独個別転送命令` [mvp](https://mncore-challenge.preferred.jp/memory-animation/?file=DRAM→PDM%20single-unicast&movie=mvp%2Fn64%20%24d0%400%20%24p0%400&frame=1) を 4 回行い、特定の PDM に集めたあと、`PDM → L2BM グループ間放送命令` [mvb](https://mncore-challenge.preferred.jp/memory-animation/?file=PDM→L2BM%20intergroup-bcast&movie=mvb%2Fn64%20%24p0%401%20%24lc0&frame=1) を 1 回行い、8 個の L2B に放送する方法が良いでしょう。
ただし、mvp の動作単位は 64 長語なので、
mvp/n32 $d0@0 $p0@0 mvp/n32 $d0@1 $p32@0 mvp/n32 $d0@2 $p64@0 mvp/n32 $d0@3 $p96@0
とは書けません。
そこで、
mvp/n64 $d0@0 $p0@0 mvp/n64 $d0@1 $p64@0 mvp/n64 $d0@2 $p128@0 mvp/n64 $d0@3 $p192@0 mvb/n256 $p0@0 $lc0
と 64 長語転送し、その後 256 長語を L2BM に放送します。
このとき、この256 長語のうち有効値の範囲は [0:32], [64:96], [128:160], [192:224] の場所の 128 長語であり、いわゆるパディングが入った状態です。
この 32 × 4 長語を L1BM に放送する際に、
l2bmb $lc0 $lb0 l2bmb $lc64 $lb32 l2bmb $lc128 $lb64 l2bmb $lc192 $lb96
のように、パディングを飛ばして L1BM に放送すると、L1BM に 128 長語が詰まった状態になります。
その後、[l1bmm](https://mncore-challenge.preferred.jp/memory-animation/?file=L1BM→MAB16x1%20bcast&movie=l1bmm%20%24lb0%20%24lp0&frame=1) 命令で PE に分配すれば良いでしょう。

## Inputs

* \(D\) (\(0 \le D[{i, j}] \le 256\)): Float `$d[0:32]@0`, `(16,16)/((4_L2B:2, 4:8), (8:1, 2_W:1); B@[4_L2B:2])`

## Outputs

* \(L\): Float `$lm[0:64]`, `(16,16)/((16:2), (2:1, 4_PE:1, 2_W:1))`

## Testcases

* [testcase.vsm](https://mncore-challenge.preferred.jp/mnist/testcase/dram_dl_16_16/testcase.vsm)
