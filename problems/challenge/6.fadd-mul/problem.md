---
source_url: https://mncore-challenge.preferred.jp/problem/fadd_mul
slug: fadd_mul
fetched_at: 2026-10-14T00:38:51+00:00
---

# FAM 8

- Top: 14 lines / sosuupoyo
- Par: 20 lines

## Problem Statement

LM0上の `Float` 配列 \(X\) の各要素 \(X[i]\) について、 \(Y[i] = (X[i] + 8) \times 8\) を計算し、LM1上に出力してください。

## Explanation

PE の中からは ALU の他に MAU（行列演算ユニット） という、浮動小数点数の積和演算ができるユニットが使えます。
MAU という名前ですが行列演算の他に要素ごとの演算も可能であり、\(A \times B + C\) の形で演算可能な、積和 `fma`、乗算 `mul`、加算 `add`、転送 `passa` が行えます。
例えば、`Float` で積を求める `fvmul` 命令を用いて、`$lm[0:8]` の \(8\) 要素それぞれの二乗を求めるコードは以下のとおりです。
```vsm
fvmul $lm0v $lm0v $ln0v
```

また MAU にも ALU と同様に、直前の MAU 命令の出力を利用できるフォワーディングパス `$mauf` があります。
その他の命令および詳細（符号の指定、入出力精度の変換など）は [SDM 3.6.9「MAU 命令式」](https://projects.preferred.jp/mn-core/assets/mncore2_dev_manual_ja.pdf#subsection.3.6.9) をご覧ください。
なお、MAU の出力は正規化されます。指数部が \(0\) なら全ビットが \(0\) に、指数部のビットが全て \(1\) なら仮数部が \(0\) になるので、浮動小数点数でない小さい整数などを `vpassa` 命令によってコピーできないことに注意してください。

## Inputs

* \(X\) (\(0 \le X[{i}] \le 1\)): Float `$lm[0:128]`, `/((16_MAB:1, 4_PE:1, 64:1, 2_W:1); B@[L1B,L2B])`

## Outputs

* \(Y\): Float `$ln[0:128]`, `/((16_MAB:1, 4_PE:1, 64:1, 2_W:1))` / \(0.0001\) 以下の絶対誤差が許容されます

## Testcases

* [testcase.vsm](https://mncore-challenge.preferred.jp/testcase/fadd_mul/testcase.vsm)
