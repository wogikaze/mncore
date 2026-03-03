---
source_url: https://mncore-challenge.preferred.jp/mnist/problem/dram_ul_256_16/
slug: dram_ul_256_16
fetched_at: 2026-03-02T23:59:50+00:00
---

# UL 256_16

- Top: 6 lines / syttrea
- Par: 7 lines

## Problem Statement

LM に `((8_L2B:1, 4:2, 8_L1B:1), (2:1, 4_PE:1, 2_W:1))` のレイアウトで分割されて配置された shape = `(256, 16)` の Float Tensor \(L\) を、DRAM にある Tensor \(D\) に指定のレイアウトで格納してください。

## Explanation

PE の LM にある値を DRAM に転送する操作を、MN-Core 用語でアップロードと呼びます。問題名の UL は Upload の略です。
[DL PE 256_16](https://mncore-challenge.preferred.jp/mnist/problem/dram_dl_256_16/)
### 考え方・方針
* `l1bmm@0` (MAB) 16x1 個別転送 命令 [[Link]](https://mncore-challenge.preferred.jp/memory-animation/?file=MAB16x1%E2%86%92L1BM%20single-unicast&movie=l1bmm%401%20%24llp0%20%24llb0&frame=1)
* `l2bmd` L1BM → L2BM 結合 [[Link]](https://mncore-challenge.preferred.jp/memory-animation/?file=L1BM→L2BM%20concat&movie=l2bmd%20%24lb0%20%24lc0&frame=1)
* `mvp/n256 $lc0@.0 $d0` L2BM → DRAM 並列個別転送命令 [[Link]](https://mncore-challenge.preferred.jp/memory-animation/?file=L2BM→DRAM%20parallel-unicast&movie=mvp%2Fn64%20%24lc0%40.1%20%24d0&frame=1)
を使います。
MN-Core の命令は、同じオペコードで、オペランドの指定を変えることで、アップロードとダウンロードが切り替わるものが多いです。
例えば、DRAM → L2BM → L1BM の順に分配する
mvp/n256 $d0 $lc0@.0 mvp/n256 $d256 $lc0@.1 l2bmd $lc0 $lb0
の逆方向、L1BM → L2BM → DRAM の結合は
l2bmd $lb0 $lc0 nop mvp/n256 $lc0@.0 $d0 mvp/n256 $lc0@.1 $d256
のようになります。
L1BM → PE で MAB 放送（PE分配）を行うときは
l1bmm $llb0 $llm0v
のように行いました。放送の逆命令は縮約か個別転送になるので、個別転送命令で MAB 0 番の値を使うことにして、
l1bmm@0 $llm0v $llb0
を使うと良いでしょう。
（今回は縮約要素間すべて同じ値なので `l1bmr` 命令を使って `l1bmrffmax` のように最大値で縮約を行うことも一応可能ですが、個別転送の方が目的に合うでしょう）

## Inputs

* \(L\) (\(0 \le L[{i, j}] \le 4096\)): Float `$lm[0:16]`, `(256,16)/((8_L2B:1, 4:2, 8_L1B:1), (2:1, 4_PE:1, 2_W:1); B@[MAB])`

## Outputs

* \(D\): Float `$d[0:512]@0`, `(256,16)/((4_L2B:2, 64:8), (8:1, 2_W:1))`

## Testcases

* [testcase.vsm](https://mncore-challenge.preferred.jp/mnist/testcase/dram_ul_256_16/testcase.vsm)
