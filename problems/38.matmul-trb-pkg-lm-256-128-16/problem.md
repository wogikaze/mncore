---
source_url: https://mncore-challenge.preferred.jp/mnist/problem/matmul_trb_pkg_lm_256_128_16/
slug: matmul_trb_pkg_lm_256_128_16
fetched_at: 2026-03-02T23:59:53+00:00
---

# Mmul TB 256_128_16

- Top: 23 lines / syttrea
- Par: 132 lines

## Problem Statement

\(256 \times 128\) 行列 \(A\) と、\(16 \times 128\) 行列 \(B\) に対して、行列積 \(C = A \times B^T\) (shape:\(256 \times 16\)) を計算してください。\(A,B,C\) のレイアウトは以下のとおりです。
A: ((8_L2B:1, 32:1), (16_MAB:1, 4_PE:1, 2_W:1)) B: ((16:1), (16_MAB:1, 4_PE:1, 2_W:1)) C: ((8_L2B:1, 32:2), (2:1, 4_PE:1, 2_W:1))

## Explanation

前回の [Mmul TB 32_8_16](https://mncore-challenge.preferred.jp/mnist/problem/matmul_trb_mab_lm_32_8_16/) では、レイアウトは以下の通りでした。
A: ((32:1), (4_PE:1, 2_W:1)) B: ((16:1), (4_PE:1, 2_W:1)) C: ((32:2), (2:1, 4_PE:1, 2_W:1))
比較してみると、\(A,C\) の 1 次元目に `8_L2B:1` が増えたことで長さが 8 倍になり、\(A,B\) の 2 次元目に `16_MAB:1` が増えたことで長さが 16 倍になっています。
### 考え方・方針
\(A,C\) の 1 次元目が増えたバリエーションは [Mmul TB 256_16_16](https://mncore-challenge.preferred.jp/mnist/problem/matmul_trb_pkg_lm_256_16_16/) でも経験しました。
この場所が増えても結局分割して配置されているだけで、L2B で並列して計算できるので、VSM に影響はありませんでした。
しかし、\(A,B\) の 2 次元目が増えたことは影響します。行列の内積をする長さが 8 から 128 の 16 倍になります。
今回は、内積をする軸が `16_MAB:1` と、16 MAB に分割されているので、各 MAB で [Mmul TB 32_8_16](https://mncore-challenge.preferred.jp/mnist/problem/matmul_trb_mab_lm_32_8_16/) と同じく \(32\times8\) 行列と \(8\times16\) 行列の積を計算し、それを MAB 間で総和で縮約を行うことで、 \(32\times128\) 行列と \(128\times16\) 行列の積を計算します。
### 16 MAB 間の縮約で使用する命令
16 MAB 間の縮約は、以下の 2 つの命令を使用します。
* `l1bmrffadd $ln0v $lb0` 16x1(MAB) 縮約命令 [l1bmr](https://mncore-challenge.preferred.jp/memory-animation/?file=MAB16x1%E2%86%92L1BM%20reduce&movie=l1bmr%20%24lp0%20%24lb0&frame=1)
* `l1bmm $lb0 $lm0v` 16x1MAB 放送命令 [l1bmm](https://mncore-challenge.preferred.jp/memory-animation/?file=L1BM→MAB16x1%20bcast&movie=l1bmm%20%24lb0%20%24lp0&frame=1)
それぞれ、1命令で PE 側は 4 長語（8単語）を入力に、4 PE 間の値を結合しつつ L1BM に 16 長語の値を書き込みます。
`$ln[0:128]` の 128 単語を処理しないといけないため、それぞれ 16 命令程度発行するとよいでしょう。
### 縮約を行うコード例(2/16)
前回の [Mmul TB 32_8_16](https://mncore-challenge.preferred.jp/mnist/problem/matmul_trb_mab_lm_32_8_16/) の回答に、以下を付け加えると、`512 value(s) correct, but 3584 value(s) mismatch` と、512/4096 = 2/16 が通ります。
nop/2 l1bmrffadd $ln0v $lb0 l1bmrffadd $ln8v $lb16 nop/2 l1bmm $lb0 $ln0v l1bmm $lb16 $ln8v
なお、今回はそれぞれ 16 命令ずつ発行しますが、実は合計 16 命令で行うことも可能です。

## Additional Constraints

* 入力の値は、小数点以下切り捨てされています。

## Inputs

* \(A\) (\(0 \le A[{i, j}] \le 512\)): Float `$lm[0:64]`, `(256,128)/((8_L2B:1, 32:1), (16_MAB:1, 4_PE:1, 2_W:1); B@[L1B])`
* \(B\) (\(0 \le B[{i, j}] \le 512\)): Float `$lm[64:96]`, `(16,128)/((16:1), (16_MAB:1, 4_PE:1, 2_W:1); B@[L1B,L2B])`

## Outputs

* \(C\): Float `$ln[0:128]`, `(256,16)/((8_L2B:1, 32:2), (2:1, 4_PE:1, 2_W:1))` / \(0.00001\) 以下の絶対誤差が許容されます

## Testcases

* [testcase.vsm](https://mncore-challenge.preferred.jp/mnist/testcase/matmul_trb_pkg_lm_256_128_16/testcase.vsm)
