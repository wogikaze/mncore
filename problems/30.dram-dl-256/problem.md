---
source_url: https://mncore-challenge.preferred.jp/mnist/problem/dram_dl_256/
slug: dram_dl_256
fetched_at: 2026-03-02T23:59:52+00:00
---

# DL 256

- Top: 11 lines / syttrea
- Par: 11 lines

## Problem Statement

DRAM に分割されて配置された長さ 256 の Float Vector \(D\) を、
LM にある Vector \(L\) に`((4_L2B:2, 32:1, 2_W:1))`のレイアウトで格納してください。

## Explanation

ポイントとしては、今回は入出力で `4_L2B:2` → `4_L2B:2` と同じなのと、出力レイアウトに `L2B` 以外の分割の指示がありません。
`4_PE:1` の分割すらないのはこの問題で初ですね。L1B までは [DL PE 256_16](https://mncore-challenge.preferred.jp/mnist/problem/dram_dl_256_16p/) と同様の設定です。
L1BM まで値を下ろした後は、1 長語 PE 放送命令 [l1bmp](https://mncore-challenge.preferred.jp/memory-animation/?file=L1BM%E2%86%92PE%20bcast&movie=l1bmp%20%24lb0%20%24lp0&frame=1) を使って、L1BM にある値を 16 個の MAB、4 個の PE に放送すれば良いです。
1 長語 PE 放送命令はサイクルごとに 1 長語を読み出し、各 PE に 1 長語ずつ放送するので、1 命令で 4 長語（8単語）を転送します。大量の値を放送するときは
l1bmp $lb0 $lm0v l1bmp $lb4 $lm8v
のようになります。
なお、PE 放送命令は、`l1bmp $llb0 $llm0v` のように書くと [2長語動作](https://mncore-challenge.preferred.jp/memory-animation/?file=L1BM%E2%86%92PE%20bcast&movie=l1bmp%20%24llb0%20%24llp0&frame=1) になりますが、こちらはスループットが倍になる他に出力のレイアウトも変わるので、こちらで行いたい場合はお気をつけください。
### 使用する命令まとめ
* `mvb2` DRAM → L2BM グループ内放送命令 [mvb2](https://mncore-challenge.preferred.jp/memory-animation/?file=DRAM%E2%86%92L2BM%20ingroup-bcast&movie=mvb2%2Fn64%20%24d0%20%24lc0&frame=1)
* `l2bmb` L2BM → L1BM 放送命令 [l2bmb](https://mncore-challenge.preferred.jp/memory-animation/?file=L2BM%E2%86%92L1BM%20bcast&movie=l2bmb%40%5B1%2C3%2C5%2C7%5D%20%24lc0%20%24lb0&frame=1)
* `l1bmp` PE 放送命令(1 長語) [l1bmp](https://mncore-challenge.preferred.jp/memory-animation/?file=L1BM%E2%86%92PE%20bcast&movie=l1bmp%20%24lb0%20%24lp0&frame=1)
最初、各 DRAM には `$d[0:32]` の通り、32 長語ずつ分配されて配置されています。
これを DRAM → L2BM → L1BM と放送していきます。`mvb2` 命令は 64 長語単位で放送するので、`mvb2/n32 $d0 $lc0` ではなく `mvb2/n64 $d0 $lc0` とします。
これを行い、各 L1BM に 32 長語を持っていったのち、`l1bmp` PE 放送命令(1 長語) を8回発行して、各 PE に 32 長語（64単語）を放送します。

## Inputs

* \(D\) (\(0 \le D[{i}] \le 256\)): Float `$d[0:32]@0`, `(256)/((4_L2B:2, 32:1, 2_W:1); B@[4_L2B:2])`

## Outputs

* \(L\): Float `$lm[0:64]`, `(256)/ ((4_L2B:2, 32:1, 2_W:1))`

## Testcases

* [testcase.vsm](https://mncore-challenge.preferred.jp/mnist/testcase/dram_dl_256/testcase.vsm)
