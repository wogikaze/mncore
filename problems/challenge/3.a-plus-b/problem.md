---
source_url: https://mncore-challenge.preferred.jp/problem/a_plus_b
slug: a_plus_b
fetched_at: 2026-10-14T00:38:49+00:00
---

# A + B

- Top: 6 lines / tantal
- Par: 14 lines

## Problem Statement

LM上の整数ベクトル \(A\), \(B\) に対して \(C = A + B\) を計算し、LM上に出力してください。

## Explanation

以下の入出力に記載のとおり、`$lm[0:32]` と `$ln[0:32]` を加算した結果を `$lm[32:64]` に出力したいです。
今回は `Int` の加算になるので、`iadd` を使いましょう。
LM の制約のため、違うアドレスの LM0 (`$lm`) に同時に入出力できないので、データ移動命令 `ipassa` などを用いると良いでしょう。
例えば、`ipassa $lr0v $ls0v` とすると `$lr0v` のデータを `$ls0v` にそのままコピーできます。
ちなみに、`passa` 命令は ALU の \(A\) ポート入力をそのまま転送 (pass) する、"pass A" という意味です。
ところで、入出力に書いてある `((4_PE:1, 16:1, 2_W:1))` について軽く説明しましょう。
実は MN-Core 2 は階層構造になっており、具体的には、最上位には \(8\) 個の L2B があり、各L2Bには \(8\) 個の L1B があり、各L1Bには \(16\) 個の MAB、各MABの中には \(4\) 個の PE があります。
すなわち、合計して \(4096\) 個の PE が存在していることになりますが、その全てが同じ命令を並列に処理しています。
「MAB」や「L1BM」など説明していない要素もありますが、今は MN-Core 2 がこのような階層構造をしていることを覚えておいてください。
MN-Core ではベクトル（配列）やテンソル（多次元配列）をこれらで分割して並列に計算することを考えます。
今回の `((4_PE:1, 16:1, 2_W:1))` という表記は、\(4\times16\times2\) の長さの配列が、「\(4\) つのPEの」、「\(16\) 長語分のアドレス領域に」、「長語内に \(2\) 要素」で配置されていることを意味します。
その後ろの `B@[MAB,L1B,L2B]` に関しては、\(16\) 個の MAB、\(8\) 個の L1B、\(8\) 個の L2B に関してはそれぞれ同じ内容が配置されている（Broadcast されている）ことを意味します。
詳細が気になる方は [MN-Core におけるテンソルのメモリ配置レイアウト表現](https://tech.preferred.jp/ja/blog/mn-core-tensor-layout/) をご覧ください。
「LM の制約のため、違うアドレスの LM0 に同時に入出力できない」といった制約について、[こちら](https://mncore-challenge.preferred.jp/tips/VLIW) に MN-Core の機械語の仕組みに基づく説明があります。理解の補足として参考にしてください。
### ヒント・想定解

### ヒント・想定解（ネタバレ）
### \(8\) 行解法
```vsm
iadd $lm0v $ln0v $lr0v
iadd $lm8v $ln8v $lr8v
iadd $lm16v $ln16v $lr16v
iadd $lm24v $ln24v $lr24v
ipassa $lr0v $lm32v
ipassa $lr8v $lm40v
ipassa $lr16v $lm48v
ipassa $lr24v $lm56v
```

### \(6\) 行解法のヒント \(1\)
`ipassa` の \(4\) 行を、\(2\) 行にすることができます。
### \(6\) 行解法のヒント \(2\)
[Plus 2](https://mncore-challenge.preferred.jp/problem/plus_two)
### \(6\) 行解法の方針（ネタバレ）
ALU の `passa` は \(2\) 長語のデータをコピーできます。
### \(6\) 行解法（ネタバレ）
```vsm
iadd $lm0v $ln0v $lr0v
iadd $lm8v $ln8v $lr8v
iadd $lm16v $ln16v $lr16v
iadd $lm24v $ln24v $lr24v
ipassa $llr0v $llm32v
ipassa $llr16v $llm48v
```

## Inputs

* \(A\) (\(0 \le A[{i}] \le 100\)): Int `$lm[0:32]`, `/((4_PE:1, 16:1, 2_W:1); B@[MAB,L1B,L2B])`
* \(B\) (\(0 \le B[{i}] \le 100\)): Int `$ln[0:32]`, `/((4_PE:1, 16:1, 2_W:1); B@[MAB,L1B,L2B])`

## Outputs

* \(C\): Int `$lm[32:64]`, `/((4_PE:1, 16:1, 2_W:1))`

## Testcases

* [testcase.vsm](https://mncore-challenge.preferred.jp/testcase/a_plus_b/testcase.vsm)
