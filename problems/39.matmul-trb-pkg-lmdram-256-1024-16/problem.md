---
source_url: https://mncore-challenge.preferred.jp/mnist/problem/matmul_trb_pkg_lmdram_256_1024_16/
slug: matmul_trb_pkg_lmdram_256_1024_16
fetched_at: 2026-03-02T23:59:58+00:00
---

# Mmul TB D 256_1024_16★

- Top: 29 lines / syttrea
- Par: 113 lines

## Problem Statement

\(256 \times 1024\) 行列 \(A\) と、\(16 \times 1024\) 行列 \(B\) に対して、行列積 \(C = A \times B^T\) (shape:\(256 \times 16\)) を計算し、DRAMへ 出力してください。\(A,B,C\) のレイアウトは以下のとおりです。
A: ((8_L2B:1, 32:1), (8_MAB:2, 8_L1B:1, 2_MAB:1, 4_PE:1, 2_W:1)) B: ((16:1), (8_MAB:2, 8_L1B:1, 2_MAB:1, 4_PE:1, 2_W:1)) C: ((4_L2B:2, 64:8), (8:1, 2_W:1))

## Explanation

前回の [Mmul TB 256_128_16](https://mncore-challenge.preferred.jp/mnist/problem/matmul_trb_pkg_lm_256_128_16/) では、レイアウトは以下の通りでした。
A: ((8_L2B:1, 32:1), (16_MAB:1, 4_PE:1, 2_W:1)) B: ((16:1), (16_MAB:1, 4_PE:1, 2_W:1)) C: ((8_L2B:1, 32:2), (2:1, 4_PE:1, 2_W:1))
比較してみると、\(A,B\) の 2 次元目に `8_L1B:1` が増えたことで長さが 8 倍になっています。問題の都合で、`16_MAB:1` が `8_MAB:2, 2_MAB:1` の2つに別れていますが結局総和で縮約するので、要素セットが同じであれば順番はあまり気にしなくて良いです。
さて、今回の問題は、最終的に DRAM へ出力することが求められています。`((4_L2B:2, 64:8), (8:1, 2_W:1))` というレイアウトは、\(256 \times 16 = 4096\) 要素の Float を、4 グループの DRAM に順番に 4 分割して配置することを意味します。
### 考え方・方針
出力が LM ではなく DRAM なので、[Mmul TB 256_128_16](https://mncore-challenge.preferred.jp/mnist/problem/matmul_trb_pkg_lm_256_128_16/) では [l1bmm](https://mncore-challenge.preferred.jp/memory-animation/?file=L1BM→MAB16x1%20bcast&movie=l1bmm%20%24lb0%20%24lp0&frame=1) 命令で L1BM → LM へ戻していましたが、今回は不要です。
代わりに、8 個の L1BM を縮約して L2BM へ上げる必要があるため、`l2bmrffadd $lb0 $lc0` L1BM → L2BM 縮約 [l2bmr](https://mncore-challenge.preferred.jp/memory-animation/?file=L1BM%E2%86%92L2BM%20reduce&movie=l2bmr%40%5B0%2C2%2C4%2C6%5D%20%24lb0%20%24lc0&frame=1) 命令を使います。
L2BM から DRAM への移動は、`8_L2B:1` と、8 個の L2BM に分割された行列を結合し、各グループ、合計4枚ある DRAM へ分配する必要があります。
このとき、`mvp/n256 $lc0@.0 $d0`DRAM → L2BM 並列個別転送命令 [mvp](https://mncore-challenge.preferred.jp/memory-animation/?file=L2BM→DRAM%20parallel-unicast&movie=mvp%2Fn64%20%24lc0%40.1%20%24d0&frame=1) を使うと良いでしょう。
### L1BM → L2BM の縮約を行うコード例
L1BM には 256 長語あり、`l2bmr` は 1 命令で 64 長語を処理するので、4 回発行する必要があります。
l2bmrffadd $lb0 $lc0 l2bmrffadd $lb64 $lc64 l2bmrffadd $lb128 $lc128 l2bmrffadd $lb192 $lc192
### L2BM → DRAM の転送を行うコード例
8 個の L2BM それぞれにある 256 長語を、4 グループの DRAM へ分配し、各グループの DRAM に 512 長語を集めます。
DRAM から見たら、グループ内の L2BM それぞれから 256 長語を貰えばいいので、以下のように書けます。
mvp/n256 $lc0@.0 $d0 mvp/n256 $lc0@.1 $d256

## Additional Constraints

* 入力の値は、小数点以下切り捨てされています。

## Inputs

* \(A\) (\(-512 \le A[{i, j}] \le 512\)): Float `$lm[0:64]`, `(256,1024)/((8_L2B:1, 32:1), (8_MAB:2, 8_L1B:1, 2_MAB:1, 4_PE:1, 2_W:1))`
* \(B\) (\(-512 \le B[{i, j}] \le 512\)): Float `$lm[64:96]`, `(16,1024)/((16:1), (8_MAB:2, 8_L1B:1, 2_MAB:1, 4_PE:1, 2_W:1); B@[L2B])`

## Outputs

* \(C\): Float `$d[0:512]@0`, `(256,16)/((4_L2B:2, 64:8), (8:1, 2_W:1))` / \(0.00001\) 以下の絶対誤差が許容されます

## Testcases

* [testcase.vsm](https://mncore-challenge.preferred.jp/mnist/testcase/matmul_trb_pkg_lmdram_256_1024_16/testcase.vsm)
