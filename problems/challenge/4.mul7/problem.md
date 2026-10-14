---
source_url: https://mncore-challenge.preferred.jp/problem/mul7
slug: mul7
fetched_at: 2026-10-14T00:38:50+00:00
---

# Mul 7

- Top: 6 lines / sosuupoyo
- Par: 24 lines

## Problem Statement

LM0上の `ULong` 配列 \(X\) の各要素 \(X[i]\) について、 \(Y[i] = X[i] \times 7\) を計算し、LM1上に出力してください。

## Explanation

ここまでの説明に出てきていない ALU 命令が役立つかもしれません。
ALU 命令一覧については [SDM 表3.9「ALU 命令オペコードの一覧」](https://projects.preferred.jp/mn-core/assets/mncore2_dev_manual_ja.pdf#table.3.9)をご覧ください。
なお、MN-Core 2 には整数乗算命令はありません。

## Inputs

* \(X\) (\(0 \le X[{i}] \le 1000\)): ULong `$lm[0:32]`, `/((16_MAB:1, 4_PE:1, 16:1); B@[L1B,L2B])`

## Outputs

* \(Y\): ULong `$ln[0:32]`, `/((16_MAB:1, 4_PE:1, 16:1))`

## Testcases

* [testcase.vsm](https://mncore-challenge.preferred.jp/testcase/mul7/testcase.vsm)
