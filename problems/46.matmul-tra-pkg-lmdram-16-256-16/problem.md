---
source_url: https://mncore-challenge.preferred.jp/mnist/problem/matmul_tra_pkg_lmdram_16_256_16/
slug: matmul_tra_pkg_lmdram_16_256_16
fetched_at: 2026-03-02T23:59:59+00:00
---

# Mmul TA D 16_256_16★

- Top: 26 lines / syttrea
- Par: 85 lines

## Problem Statement

\(256 \times 16\) 行列 \(A\) と、\(256 \times 16\) 行列 \(B\) に対して、行列積 \(C = A^T \times B\) (shape:\(16 \times 16\)) を計算し、DRAMへ 出力してください。\(A,B,C\) のレイアウトは以下のとおりです。
A: ((8_L2B:1, 4:2, 8_L1B:1), (2:1, 4_PE:1, 2_W:1)) B: ((8_L2B:1, 4:2, 8_L1B:1), (2:1, 4_PE:1, 2_W:1)) C: ((4_L2B:2, 4:8), (8:1, 2_W:1))
### \(A, B, C\) の値はこちらです。この問題は乱数値が使用されています。
_詳細データは省略。必要なら source_url を参照してください。_

## Explanation

前回の問題 [Mmul TA 16_4_16](https://mncore-challenge.preferred.jp/mnist/problem/matmul_tra_mab_lm_16_4_16/) のレイアウトは以下の通りでした。
A: (( 4:2), (2:1, 4_PE:1, 2_W:1)) B: (( 4:2), (2:1, 4_PE:1, 2_W:1))
今回の問題では、\(A, B\) の 1 次元目に `8_L2B:1, 8_L1B:1` とある通り、8 個の L2B, 8 個の L1B に分散して配置され、1 次元目の長さが 4 から 256 に 64 倍に増えています。
今回の問題の行列サイズに注目すると、\((256\times16)\times(256\times16)^T = (16\times16)\) という計算です。
\((256\times16)\) の行列を縦に 64 個に分け \((4\times16)\) の形の行列にして、前問のように、\((4\times16)^T\times(4\times16) = (16\times16)\) の行列演算を行った後、64 個に分割した出力の \((16\times16)\) 行列を足し合わせること最終的な答えの \((16\times16)\) 行列を求めることができます。
各 L1B に分かれて \((4\times16)\) の行列積を求めたあと、DRAM まで値を転送する過程で L1B 間、L2B 間の縮約を行うことで、Accept を得られます。
なお、DRAM へは、\(16\times16\) 行列を 4 グループに分けて、各グループの DRAM に分割して格納する必要があります。
### DRAM までの縮約に使う命令
L2BM 間の縮約と、4 DRAM への分割を効率的に行うために、L2BM から PDM への縮約と、PDM から DRAM への転送に分けると良いでしょう。
* `l1bmm@0` (MAB) 16x1 個別転送 命令 [l1bmm](https://mncore-challenge.preferred.jp/memory-animation/?file=MAB16x1%E2%86%92L1BM%20single-unicast&movie=l1bmm%401%20%24llp0%20%24llb0&frame=1)
* `l2bmrffadd $lb0 $lc0` L1BM → L2BM 縮約 [l2bmr](https://mncore-challenge.preferred.jp/memory-animation/?file=L1BM%E2%86%92L2BM%20reduce&movie=l2bmr%40%5B0%2C2%2C4%2C6%5D%20%24lb0%20%24lc0&frame=1)
* `mvrffadd/n64 $lc0 $p0@0` L2BM → PDM グループ間縮約命令[mvr](https://mncore-challenge.preferred.jp/memory-animation/?file=L2BM→PDM%20intergroup-reduce&movie=mvr%2Fn64%20%24lc0%20%24p0%401&frame=1)
* `mvp/n64 $p0@0 $d0@0` PDM → DRAM 単独個別転送命令 [mvp](https://mncore-challenge.preferred.jp/memory-animation/?file=PDM→DRAM%20single-unicast&movie=mvp%2Fn64%20%24p0%400%20%24d0%400&frame=1)
最初、各 PE には 64 単語（32長語）の値があり、4 PE 間での結合と、0 番 MAB の値を L1BM に転送します。
次に各 L1BM にある 128 長語を、L2BM へ 8 L1BM 間で縮約を行います。
各 L2BM には 128 長語があり、8 L2BM 間で縮約を行い、PDM へ転送します。
PDM には 128 長語があり、4 グループの各 DRAM へそれぞれ 32 長語を個別転送します。
…と最後に、PDM から DRAM への転送粒度・アドレスの指定が 64（長語）単位でないと行けない問題に遭遇します。
どうにかして 4 DRAM に分割する方法は無いでしょうか？
ひとまず、これらの命令自体は使用するので、一度書いて考えてみましょう。
### 4 DRAM への分割とアライメント
[l1bmm@0](https://mncore-challenge.preferred.jp/memory-animation/?file=MAB16x1%E2%86%92L1BM%20single-unicast&movie=l1bmm%401%20%24llp0%20%24llb0&frame=1)
[l2bmrffadd](https://mncore-challenge.preferred.jp/memory-animation/?file=L1BM%E2%86%92L2BM%20reduce&movie=l2bmr%40%5B0%2C2%2C4%2C6%5D%20%24lb0%20%24lc0&frame=1)
[mvrffadd/n64](https://mncore-challenge.preferred.jp/memory-animation/?file=L2BM→PDM%20intergroup-reduce&movie=mvr%2Fn64%20%24lc0%20%24p0%401&frame=1)
単独個別転送命令 [mvp](https://mncore-challenge.preferred.jp/memory-animation/?file=PDM→DRAM%20single-unicast&movie=mvp%2Fn64%20%24p0%400%20%24d0%400&frame=1) をしようにも、32 長語単位で送りたいのに 64 長語単位でしかアドレスを指定できず、PDM → DRAM 分配命令 [mvd](https://mncore-challenge.preferred.jp/memory-animation/?file=PDM→DRAM%20distrib&movie=mvd%2Fn64%20%24p0%400%20%24d0&frame=1) を使おうにも、要素の順番がうまく揃いません。
L1BM まで 128 長語を上げた後、
l2bmrffadd $lb0 $lc0 l2bmrffadd $lb32 $lc32 l2bmrffadd $lb64 $lc64 l2bmrffadd $lb96 $lc96
で L2BM 間で縮約を行うと思いますが、ここで書き込みアドレスを
l2bmrffadd $lb0 $lc0 l2bmrffadd $lb32 $lc64 l2bmrffadd $lb64 $lc128 l2bmrffadd $lb96 $lc192
のようにあえてパディングを入れることで、回避することができます。

## Inputs

* \(A\) (\(-512 \le A[{i, j}] \le 512\)): Float `$lm[0:16]`, `(256,16)/((8_L2B:1, 4:2, 8_L1B:1), (2:1, 4_PE:1, 2_W:1); B@[MAB])`
* \(B\) (\(-512 \le B[{i, j}] \le 512\)): Float `$lm[16:32]`, `(256,16)/((8_L2B:1, 4:2, 8_L1B:1), (2:1, 4_PE:1, 2_W:1); B@[MAB])`

## Outputs

* \(C\): Float `$d[0:32]@0`, `(16,16)/((4_L2B:2, 4:8), (8:1, 2_W:1))` / \(0.00001\) 以下の絶対誤差が許容されます

## Testcases

* [testcase.vsm](https://mncore-challenge.preferred.jp/mnist/testcase/matmul_tra_pkg_lmdram_16_256_16/testcase.vsm)
