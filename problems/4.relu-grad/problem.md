---
source_url: https://mncore-challenge.preferred.jp/mnist/problem/relu_grad/
slug: relu_grad
fetched_at: 2026-03-02T23:59:43+00:00
---

# ReLU grad

- Top: 3 lines / Wogikaze
- Par: 6 lines

## Problem Statement

LM に \(2\) 次元行列 \(A\) (size: \(256\times16\)) が与えられます。LM 上の出力 \(2\) 次元行列 \(C\) に対して \(A[i][j]\) が \(0\) 以上のときは \(C[i][j] = 1\)、負のときは \(C[i][j] = -0\) としてください。

## Explanation

[ReLU 関数の微分](https://manabitimes.jp/math/1373#2)
`imm f"1.0" $t` などで即値を定義し、それを使うと良いでしょう。
### 考え方・方針
マスクなどを使用したり、様々な方針で実装できますが、MN-Core 2 の `relu` 命令が 2 引数命令であることを利用し、\(A[i][j]\) を第1引数、定数 1.0f を第2引数に指定し \(A[i][j]\) の正負に応じて 1.0f か -0 かを返すのがおしゃれです。

## Inputs

* \(A\) (\(-512 \le A[{i, j}] \le 512\)): Float `$lm[0:16]`, `(256,16)/((8_L2B:1, 4:2, 8_L1B:1), (2:1, 4_PE:1, 2_W:1); B@[MAB])`

## Outputs

* \(C\): Float `$ln[0:16]`, `(256,16)/((8_L2B:1, 4:2, 8_L1B:1), (2:1, 4_PE:1, 2_W:1))` / \(0.0001\) 以下の絶対誤差が許容されます

## Testcases

* [testcase.vsm](https://mncore-challenge.preferred.jp/mnist/testcase/relu_grad/testcase.vsm)
