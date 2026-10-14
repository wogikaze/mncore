---
source_url: https://mncore-challenge.preferred.jp/problem/transpose_addr
slug: transpose_addr
fetched_at: 2026-10-14T00:38:54+00:00
---

# Transpose

- Top: 10 lines / sosuupoyo
- Par: 64 lines

## Problem Statement

レイアウト表記の理解のための練習問題です。LM0 上の \(2\) 次元配列を、表記に従ってレイアウトを変換しつつ、LM1 にコピーしてください。

## Explanation

`((8:8, 8:1))` という表記は、`:` の左側が各軸の要素数、右側がストライドを表します。
すなわち、長さ \(64\) のベクトル \(X\) を `X.reshape(8, 8)` したものについて、\(1\) 軸目が \(1\) 進むとアドレスが長語単位で \(8\) 進み、\(2\) 軸目が \(1\) 進むとアドレスが長語単位で \(1\) 進むことを意味します。
reshape 後の `[2, 3]` の要素は、`$lm38`（\(=(2\times 8+3\times 1)\times 2\)）に配置されます。
同様に `((8:1, 8:8))` のレイアウトの場合、`[2, 3]` の要素は `$lm52`（\(=(2\times 1+3\times 8)\times 2\)）に配置されます。
別の例として `((4_PE:1, 16:1, 2_W:1))` といった表記ですと、`A.reshape(4, 16, 2)` としたものの \(1, 2, 3\) 軸目をそれぞれ「\(4\) つのPE」「\(16\) 長語」「長語内の \(2\) 単語」で分割します。
例えばこの `[3, 2, 1]` の要素は「PE=\(3\)」「\(2\) 長語目」「長語内の単語=\(1\)」となるので、PE \(3\) のアドレス `$m5`（\(5=2\times 2+1\)）となります。
VSM を短く書くためには、\(1\) 問目 [Welcome](https://mncore-challenge.preferred.jp/problem/plus_one/) の Auto stride 表記 `$lm0v2` なども参考にしてください。

## Inputs

* \(X\) (\(0 \le X[{i, j}] \le 64\)): Double `$lm[0:128]`, `/((8:8), (8:1); B@[PE,MAB,L1B,L2B])`

## Outputs

* \(Y\): Double `$ln[0:128]`, `/((8:1), (8:8))`

## Testcases

* [testcase.vsm](https://mncore-challenge.preferred.jp/testcase/transpose_addr/testcase.vsm)
