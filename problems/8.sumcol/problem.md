---
source_url: https://mncore-challenge.preferred.jp/mnist/problem/sum_col/
slug: sum_col
fetched_at: 2026-03-02T23:59:44+00:00
---

# SumCol

- Top: 9 lines / syttrea
- Par: 13 lines

## Problem Statement

LM上に Float \(256\times16\) 行列 \(A\) が与えられます。1 次元目を総和で縮約して、ベクトル \(S\) (size:16)を DRAM に出力してください。

## Explanation

[SumCol mini](https://mncore-challenge.preferred.jp/mnist/problem/sum_col_mini/)
また、出力の 16 要素を最終的に DRAM に格納する事になっています。
### 考え方・方針
入力レイアウトから `8_L2B`, `8_L1B` を無視すると `((4:2), (2:1, 4_PE:1, 2_W:1))` になり、[SumCol mini](https://mncore-challenge.preferred.jp/mnist/problem/sum_col_mini/) と同じになります。
なので一旦、PE 内で 4 要素の縮約をした後、DRAM に移動する過程で、8 個の L1B を縮約、更に8個の L2B を縮約することで、256 要素の縮約ができます。
MAB 同士の縮約は必要ないので個別転送命令で MAB0 の内容を L1BM に転送します。
その後、L1BM から L2BM へ移動させる際、8 個の L1BM の値を縮約して L2BM に格納する命令を使用します。
そして最後に、8 個の L2BM の値を縮約し、4 グループそれぞれにある DRAM に同じ内容を書き込む、[L2BM → DRAM グループ間縮約命令](https://mncore-challenge.preferred.jp/memory-animation/?file=L2BM→DRAM%20intergroup-reduce&movie=mvr%2Fn64%20%24lc0%20%24d0&frame=1)を使用します。
### DRAM への移動・縮約で使用する命令
`l1bmm@0 $ln0v $lb0` (16x1 個別転送命令)で、MAB0 の内容を L1BM にそのまま転送します。[[link]](https://mncore-challenge.preferred.jp/memory-animation/?file=MAB16x1%E2%86%92L1BM%20single-unicast&movie=l1bmm%401%20%24lp0%20%24lb0&frame=1)
`l2bmrffadd $lb0 $lc0` (L1BM → L2BM 縮約命令 `l2bmr`) で 8 個の L1BM の値を縮約します。`ffadd` で、浮動小数点数の和として縮約できます。[[link]](https://mncore-challenge.preferred.jp/memory-animation/?file=L1BM%E2%86%92L2BM%20reduce&movie=l2bmr%40%5B0%2C2%2C4%2C6%5D%20%24lb0%20%24lc0&frame=1)
`mvrffadd/n64 $lc0 $d0` (L2BM → DRAM グループ間結合縮約命令) で、8 個の L2BM の値を縮約します。[[link]](https://mncore-challenge.preferred.jp/memory-animation/?file=L2BM→DRAM%20intergroup-reduce&movie=mvr%2Fn64%20%24lc0%20%24d0&frame=1)
各命令間に最大 3 nop 程度挟む必要があるので、適宜挿入しましょう。

## Inputs

* \(A\) (\(0 \le A[{i, j}] \le 10\)): Float `$lm[0:16]`, `(256,16)/((8_L2B:1, 4:2, 8_L1B:1), (2:1, 4_PE:1, 2_W:1); B@[MAB])`

## Outputs

* \(S\): Float `$d[0:8]@0`, `(16)/((8:1, 2_W:1))` / \(0.001\) 以下の絶対誤差が許容されます

## Testcases

* [testcase.vsm](https://mncore-challenge.preferred.jp/mnist/testcase/sum_col/testcase.vsm)
