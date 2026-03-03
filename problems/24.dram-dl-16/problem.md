---
source_url: https://mncore-challenge.preferred.jp/mnist/problem/dram_dl_16/
slug: dram_dl_16
fetched_at: 2026-03-02T23:59:51+00:00
---

# DL 16

- Top: 5 lines / syttrea
- Par: 7 lines

## Problem Statement

0 番グループの DRAM にある 長さ 16 の Float Vector \(D\) を、
LM にある Vector \(L\) に `((2:1, 4_PE:1, 2_W:1); B@[MAB,L1B,L2B])` のレイアウトで格納してください。
※ジャッジの都合で、\(8\) 個あるすべての L2B に同じ内容を放送していることをチェックするために、入力が長さ \(16\) の \(1\) 次元配列なのに対し、出力が \(8\times16\) の \(2\) 次元配列になっています。気にせず、Vector を放送する問題だと思ってトライしてください。

## Explanation

この問題では、入力が小さいので 4 グループの DRAM には分割せずに、0 番グループのみに与えられます。それを、すべての L2B, L1B, MAB に放送し、出力に `4_PE:1` が含まれる通り 4 PE には分配をします。
L2BM → L1BM には放送命令 [l2bmb](https://mncore-challenge.preferred.jp/memory-animation/?file=L2BM%E2%86%92L1BM%20bcast&movie=l2bmb%40%5B1%2C3%2C5%2C7%5D%20%24lc0%20%24lb0&frame=1)を、L1BM から 16 MAB には同じ内容で 4 PE に分配するには 16x1MAB 放送 命令 [l1bmm](https://mncore-challenge.preferred.jp/memory-animation/?file=L1BM→MAB16x1%20bcast&movie=l1bmm%20%24lb0%20%24lp0&frame=1) を使用します。
1 つの DRAM から、グループをまたいで 8 つの L2BM に放送するには、直接的な命令はありません。
DRAM → L2BM 単独個別転送命令 [mvp](https://mncore-challenge.preferred.jp/memory-animation/?file=DRAM→L2BM%20single-unicast&movie=mvp%2Fn64%20%24d0%400%20%24lc0%400.1&frame=1) を 8 回発行してもいいですが、各グループに存在する PDM を経由する方法を紹介します。
グループ 0 の DRAM から、グループ 0 の PDM に、`DRAM → PDM 単独個別転送命令` [mvp](https://mncore-challenge.preferred.jp/memory-animation/?file=DRAM→PDM%20single-unicast&movie=mvp%2Fn64%20%24d0%400%20%24p0%400&frame=1) で個別転送したあと、`PDM → L2BM グループ間放送命令` [mvb](https://mncore-challenge.preferred.jp/memory-animation/?file=PDM→L2BM%20intergroup-bcast&movie=mvb%2Fn64%20%24p0%401%20%24lc0&frame=1) を使用することで 2 命令で実現できます。
mvp/n64 $d0@0 $p0@0 mvb/n64 $p0@0 $lc0
グループ 0 の DRAM `$d[0:64]` を、グループ 0 の PDM `$p[0:64]` に転送し、
その後、グループ 0 の PDM `$p[0:64]` を、すべての L2BM `$lc[0:64]` に放送しています。

## Inputs

* \(D\) (\(0 \le D[{i}] \le 16\)): Float `$d[0:8]@0`, `(16)/((8:1, 2_W:1); B@[4_L2B:2])`

## Outputs

* \(L\): Float `$lm[0:4]`, `(8,16)/((8_L2B:1), (2:1, 4_PE:1, 2_W:1))`

## Testcases

* [testcase.vsm](https://mncore-challenge.preferred.jp/mnist/testcase/dram_dl_16/testcase.vsm)
