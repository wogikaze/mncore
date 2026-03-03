---
source_url: https://mncore-challenge.preferred.jp/mnist/problem/matmul_tra_pkg_lmdram_16_256_1024/
slug: matmul_tra_pkg_lmdram_16_256_1024
fetched_at: 2026-03-02T23:59:59+00:00
---

# Mmul TA D 16_256_1024 ★

- Top: 70 lines / syttrea
- Par: 140 lines

## Problem Statement

\(256 \times 16\) 行列 \(A\) と、\(256 \times 1024\) 行列 \(B\) に対して、行列積 \(C = A^T \times B\) (shape:\(16 \times 1024\)) を計算し、DRAMへ 出力してください。\(A,B\) のレイアウトは以下のとおりです。
A: ((8_L2B:1, 32:2), (2:1, 4_PE:1, 2_W:1)) B: ((8_L2B:1, 32:1), (8_MAB:2, 8_L1B:1, 2_MAB:1, 4_PE:1, 2_W:1))

## Explanation

前回の問題 [Mmul TA 16_32_8](https://mncore-challenge.preferred.jp/mnist/problem/matmul_tra_mab_lm_16_32_8/) のレイアウトは以下の通りでした。
A: ((32:2), (2:1, 4_PE:1, 2_W:1)) B: ((32:1), (4_PE:1, 2_W:1)) C: ((16:1), (4_PE:1, 2_W:1))
今回の問題では、\(A, B\) の 1 次元目に `8_L2B:1` とある通り、8 個の L2B に分散して配置されています。
また、\(B\) の 2 次元目に `8_MAB:2, 8_L1B:1, 2_MAB:1` が追加されています。これは \(B\) の 2 次元目が、8 個の L1B と 16 個の MAB に分散して配置されていることを示しています。
### 方針
今回の行列積は、\(1\) 次元目は縮約される次元なので、8 個の L2B 間で縮約を行う必要があります。
また、\(2\) 次元目は結合を行う次元なので、`Mmul TA 16_32_8` を行って得られた \(16\times8\) 行列 `((16:1), (4_PE:1, 2_W:1))` を、16 個の MAB と 8 個の L1B 間で結合を行うことで、最終的に \(16\times1024\) 行列を得ることができます。
L2BM 間の縮約は、L2BM から PDM への縮約と、PDM から DRAM への転送に分けると良いでしょう。
### 縮約・結合で使用する具体的な命令
* `l1bmd` 結合命令 [l1bmd](https://mncore-challenge.preferred.jp/memory-animation/?file=PE→L1BM%20concat&movie=l1bmd%20%24lp0%20%24lb0&frame=1)
* `l2bmd` L1BM → L2BM 結合 [l2bmd](https://mncore-challenge.preferred.jp/memory-animation/?file=L1BM→L2BM%20concat&movie=l2bmd%20%24lb0%20%24lc0&frame=1)
* `mvrffadd/n8192 $lc0 $p0@0` L2BM → PDM グループ間縮約命令[mvr](https://mncore-challenge.preferred.jp/memory-animation/?file=L2BM→PDM%20intergroup-reduce&movie=mvr%2Fn64%20%24lc0%20%24p0%401&frame=1)
* `mvp/n2048 $p0@0 $d0@0` PDM → DRAM 単独個別転送命令 [mvp](https://mncore-challenge.preferred.jp/memory-animation/?file=PDM→DRAM%20single-unicast&movie=mvp%2Fn64%20%24p0%400%20%24d0%400&frame=1)
を使用します。

## Inputs

* \(A\) (\(-512 \le A[{i, j}] \le 512\)): Float `$lm[0:128]`, `(256,16)/((8_L2B:1, 32:2), (2:1, 4_PE:1, 2_W:1); B@[MAB,L1B])`
* \(B\) (\(-512 \le B[{i, j}] \le 512\)): Float `$lm[128:192]`, `(256,1024)/((8_L2B:1, 32:1), (8_MAB:2, 8_L1B:1, 2_MAB:1, 4_PE:1, 2_W:1))`

## Outputs

* \(C\): Float `$d[0:2048]@0`, `(16,1024)/((4_L2B:2, 4:512), (512:1, 2_W:1))` / \(0.00001\) 以下の絶対誤差が許容されます

## Testcases

* [testcase.vsm](https://mncore-challenge.preferred.jp/mnist/testcase/matmul_tra_pkg_lmdram_16_256_1024/testcase.vsm)
