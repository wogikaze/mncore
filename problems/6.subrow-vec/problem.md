---
source_url: https://mncore-challenge.preferred.jp/mnist/problem/sub_rowvec/
slug: sub_rowvec
fetched_at: 2026-03-02T23:59:44+00:00
---

# SubRow vec

- Top: 24 lines / syttrea
- Par: 80 lines

## Problem Statement

LM上に Float \(256 \times 16\) 行列 \(A\) と、長さ \(256\) のベクトル \(B\) があります。行列 \(C[i][j] = A[i][j] - B[i]\) を求め、LM 上に出力してください。

## Explanation

ただの [AddCol vec](https://mncore-challenge.preferred.jp/mnist/problem/add_colvec/) の減算版かと思いきや、ベクトルを行列に拡張する次元が異なります。また、与えられる入力のレイアウトも異なります。
浮動小数点数の減算は、`fvadd $lm0v -$lr0v $ln0v` のように、加算命令と符号オプションを使って計算できます。
### レイアウトのおさらい
A,B の 1 次元目が両方 `4_L2B:2` のように分散されているので、PE 単位で見ると、行列 `A` はサイズ \(64\times4\) で `$lm[0:256]` へ `((64:2), (2:1, 2_W:1))` の形で格納されていることが分かります。
ベクトル \(B\) も同じく、長さ \(64\) で `$lm[256:320]` へ `(32:1, 2_W:1)` の形で格納されていることが分かります。
\(A[0]\) は `$m[0,1,2,3]` に、\(A[1]\) は `$m[4,5,6,7]` に格納されています。
\(B[0]\) は `$m256` に、\(B[1]\) は `$m257` に格納されています。
出力の \(C[0]\) は `$n[0,1,2,3]` なので、`$m[0,1,2,3]` から `$m256` を引いて `$n[0,1,2,3]` に出力することになります。
PE あたりの行列サイズが大きいので、`fvadd` 命令は 64 個程度発行する必要があります。

## Inputs

* \(A\) (\(-512 \le A[{i, j}] \le 512\)): Float `$lm[0:256]`, `(256,16)/((4_L2B:2, 64:2), (2:1, 4_PE:1, 2_W:1); B@[MAB,L1B])`
* \(B\) (\(-512 \le B[{i}] \le 512\)): Float `$lm[256:320]`, `(256)/((4_L2B:2, 32:1, 2_W:1); B@[PE,MAB,L1B])`

## Outputs

* \(C\): Float `$ln[0:256]`, `(256,16)/((4_L2B:2, 64:2), (2:1, 4_PE:1, 2_W:1))` / \(0.00001\) 以下の絶対誤差が許容されます

## Testcases

* [testcase.vsm](https://mncore-challenge.preferred.jp/mnist/testcase/sub_rowvec/testcase.vsm)
