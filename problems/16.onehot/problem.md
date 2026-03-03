---
source_url: https://mncore-challenge.preferred.jp/mnist/problem/onehot/
slug: onehot
fetched_at: 2026-03-02T23:59:50+00:00
---

# Onehot

- Top: 24 lines / syttrea
- Par: 153 lines

## Problem Statement

LM に、値域が 0 以上 16 未満で長さが \(256\) の Int ベクトル \(T\) が与えられます。
出力として、\(32 \times 256\) 行列 \(X_{i,j}\) に対して、`j = T[j]` であれば \(1.0\), そうでないなら \(0.0\) で埋められた行列を LM に作成してください。

## Explanation

[Onehot mini](https://mncore-challenge.preferred.jp/mnist/problem/onehot_mini/)
(4_L2B:2)
PE あたりのサイズが \(16\) 倍 になったので、Onehot mini をそのまま \(16\) 倍に増やすことで Accept が得られます。

## Inputs

* \(T\) (\(0 \le T[{i}] \le 15\)): Int `$lm[0:64]`, `(256)/((4_L2B:2, 32:1, 2_W:1); B@[PE,MAB,L1B])`

## Outputs

* \(X\): Float `$ln[0:256]`, `(256,16)/((4_L2B:2, 64:2), (2:1, 4_PE:1, 2_W:1))`

## Testcases

* [testcase.vsm](https://mncore-challenge.preferred.jp/mnist/testcase/onehot/testcase.vsm)
