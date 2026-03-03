---
source_url: https://mncore-challenge.preferred.jp/mnist/problem/dram_dl_16_1024/
slug: dram_dl_16_1024
fetched_at: 2026-03-02T23:59:51+00:00
---

# DL 16_1024

- Top: 40 lines / syttrea
- Par: 41 lines

## Problem Statement

DRAM に分割されて配置された shape = `(16, 1024)` の Float Tensor \(D\) を、
LM にある Tensor \(L\) に `((16:1), (8_MAB:2, 8_L1B:1, 2_MAB:1, 4_PE:1, 2_W:1); B@[8_L2B:1])` のレイアウトで格納してください。
※ジャッジの都合で、複数の L2B に同じ内容を放送していることをチェックするために、入力が 2 次の Tensor なのに対し、出力が 3 次の Tensor になっています。気にせず、Tensor を放送・分配する問題だと思ってトライしてください。

## Explanation

レイアウトを見ると、`8_L1B:1`, `4_PE:1` が含まれているので、8 個の L1B, 4 個の PE に分配することが分かります。`MAB` に関しては `8_MAB:2, 2_MAB:1` となっていますが、合わせると 16 個ある MAB に分割してくださいという指示になるので、こちらも MAB に関して分配します。
L2B に関しては、`B@[8_L2B:1]` と明示されているので、8 個の L2B に放送（Broadcast）、つまりそれぞれの L2B で同じ内容を複製することが分かります。
DRAM→L2BM の転送は、入力は 4 枚の DRAM に分割して 2048 長語ずつ配置されていますが、L2BM では連結して、8 個の L2B で同じ内容にする必要があります。
`DRAM → L2BM グループ間放送命令` [mvb](https://mncore-challenge.preferred.jp/memory-animation/?file=DRAM→L2BM%20intergroup-bcast&movie=mvb%2Fn64%20%24d0%20%24lc0&frame=1) の使用も考えられますが、こちらは 16 長語ずつ 4 グループの内容が交互に配置されてしまうので、今回の目的には合いません。
[DL 16](https://mncore-challenge.preferred.jp/mnist/problem/dram_dl_16/)
DRAM → PDM 単独個別転送命令
[mvp](https://mncore-challenge.preferred.jp/memory-animation/?file=DRAM→PDM%20single-unicast&movie=mvp%2Fn64%20%24d0%400%20%24p0%400&frame=1)
PDM → L2BM グループ間放送命令
[mvb](https://mncore-challenge.preferred.jp/memory-animation/?file=PDM→L2BM%20intergroup-bcast&movie=mvb%2Fn64%20%24p0%401%20%24lc0&frame=1)
### 具体的な命令
mvp/n2048 $d0@0 $p0@0 mvp/n2048 $d0@1 $p2048@0 mvp/n2048 $d0@2 $p4096@0 mvp/n2048 $d0@3 $p6144@0 mvb/n8192 $p0@0 $lc0
これで、`$lc[0:8192]` に、集めることができたので、8 個の L1B, 16 個の MAB, 4 個の PE に分配していきます。
`8_L1B:1` に分配するには L2BM → L1BM 分配命令 [l2bmd](https://mncore-challenge.preferred.jp/memory-animation/?file=L2BM%E2%86%92L1BM%20distrib&movie=l2bmd%40%5B0%2C1%2C2%2C3%5D%20%24lc0%20%24lb0&frame=1) を使用します。1 命令で 256 長語を L2BM から読み出し、8 個の L1B に 32 長語ずつ分配するので、32 命令必要です。これで各 L1BM に 1024 長語ずつ分配されます。
L1BM の内容を 16 個の MAB, 4 個の PE に分配するには、(PE) 分配命令 [l1bmd](https://mncore-challenge.preferred.jp/memory-animation/?file=L1BM%E2%86%92PE%20distrib&movie=l1bmd%20%24lb0%20%24lp0&frame=1) を使用します。1 命令で 256 長語を読み出し、16 個のMAB, 4 個の PE に 4 長語（8 単語）ずつ分配するので、4 命令必要です。
これで各 PE に 32 単語ずつ分配されます。

## Inputs

* \(D\) (\(0 \le D[{i, j}] \le 2^{14}\)): Float `$d[0:2048]@0`, `(16,1024)/((4_L2B:2, 4:512), (512:1, 2_W:1); B@[4_L2B:2])`

## Outputs

* \(L\): Float `$lm[0:32]`, `(2,16,1024)/((2_L2B:3), (16:1), (8_MAB:2, 8_L1B:1, 2_MAB:1, 4_PE:1, 2_W:1))`

## Testcases

* [testcase.vsm](https://mncore-challenge.preferred.jp/mnist/testcase/dram_dl_16_1024/testcase.vsm)
