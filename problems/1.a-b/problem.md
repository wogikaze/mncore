---
url: https://mncore-challenge.preferred.jp/mnist/problem/mat_sub
title: "A - B - Event (Additional Problems (MNIST))"
date: 2026-02-18T21:40:24.287Z
lang: ja
---

# A - B

![top](/images/icon-crown.png) Top: 3 lines / syttrea

![par](/images/icon-par.png) Par: 4 lines

My Best: [4 lines](/mnist/shortest/mat_sub/Wogikaze/)

## Problem Statement

LM上の Float 256×16 行列 A, B に対して C\=A−B を計算し、LM上に出力してください。

## Explanation

MNCore Challenge のチュートリアル 3 問目 [A + B](https://mncore-challenge.preferred.jp/problem/a_plus_b) に似た問題になっています。

A, B 両方とも、256×16 サイズの行列の 1 次元目が `(8_L2B:1, 4:2, 8_L1B:1)` のレイアウトで格納されています。表記を読み解くと、簡単には 8 個の L2B ブロック、8 個の L1B に分割され、PE あたりとしては長さ 4 で分割されています。

16 の長さの軸も、4 個の PE に分割され、各 PE は 長さ 4 で割り当てられています。

A, B, 出力がすべて同じレイアウトで分割され、また要素単位に独立した演算しかしないので、イメージとしては `$ln[0:16] = $lm[0:16] - $lm[16:32]` を行うだけで大丈夫です。

ただし、今回は浮動小数点数の計算なのと、`fvsub` 命令は直接は無く、代わりに `fvadd` 命令と、MAU の符号反転オプションを使って `fvadd $hoge -$fuga $out` のように書きます。

## Inputs

* A (−512≤A\[i,j\]≤512): Float `$lm[0:16]`, `(256,16)/((8_L2B:1, 4:2, 8_L1B:1), (2:1, 4_PE:1, 2_W:1); B@[MAB])`

    ?

* B (−512≤B\[i,j\]≤512): Float `$lm[16:32]`, `(256,16)/((8_L2B:1, 4:2, 8_L1B:1), (2:1, 4_PE:1, 2_W:1); B@[MAB])`

    ?

## Outputs

* C: Float `$ln[0:16]`, `(256,16)/((8_L2B:1, 4:2, 8_L1B:1), (2:1, 4_PE:1, 2_W:1))`

    ?

    / 0.0001 以下の絶対誤差が許容されます

## Testcases

[testcase.vsm](/mnist/testcase/mat_sub/testcase.vsm)

## Submission

0 / 50000 bytes

Submit
