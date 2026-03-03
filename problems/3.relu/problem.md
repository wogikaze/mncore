---
source_url: https://mncore-challenge.preferred.jp/mnist/problem/relu/
slug: relu
fetched_at: 2026-03-02T23:59:43+00:00
---

# ReLU

- Top: 2 lines / syttrea
- Par: 2 lines

## Problem Statement

LM に \(2\) 次元行列 \(A\) (size: \(256\times16\)) が与えられます。LM 上の出力 \(2\) 次元行列 \(C\) に対して \(A[i][j]\) が \(0\) 以上のときは \(C[i][j] = A[i][j]\)、負のときは \(C[i][j] = -0\) としてください。

## Explanation

ニューラルネットワークの活性化関数としておなじみ、 [ReLU (Rectified Linear Unit)](https://manabitimes.jp/math/1373)です。
MN-Core には `relu` 命令があるので、float32 なので `frelu $X $Y $OUT` のように書きます。
本来、ReLU 関数は \(a = \operatorname{ReLU}(x)\) のような 1 引数関数ですが、MN-Core 2 の `relu` 命令は 2 引数関数 \(a = \operatorname{ReLU}(x, y)\) で、\(x\) が \(0\) 以上のときに \(y\) を、\(x\) が負のときに \(-0\) を返します。

## Inputs

* \(A\) (\(-512 \le A[{i, j}] \le 512\)): Float `$lm[0:16]`, `(256,16)/((8_L2B:1, 4:2, 8_L1B:1), (2:1, 4_PE:1, 2_W:1); B@[MAB])`

## Outputs

* \(C\): Float `$ln[0:16]`, `(256,16)/((8_L2B:1, 4:2, 8_L1B:1), (2:1, 4_PE:1, 2_W:1))`

## Testcases

* [testcase.vsm](https://mncore-challenge.preferred.jp/mnist/testcase/relu/testcase.vsm)
