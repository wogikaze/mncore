---
source_url: https://mncore-challenge.preferred.jp/problem/hsv2rgb
slug: hsv2rgb
fetched_at: 2026-10-14T00:39:10+00:00
---

# HSV2RGB

- Top: 12 lines / syttrea
- Par: 60 lines

## Problem Statement

HSV色空間からRGB色空間への変換を実装してください。
入力ではレイアウトの `(3:1)` 部分にアドレスの小さい方から H, S, V が、出力では同じく R, G, B が並びます。
変換式は Python 標準ライブラリの [colorsys.hsv_to_rgb()](https://github.com/python/cpython/blob/7aafa305d40fe2aad2d2e2fad4079fb868dd2e7e/Lib/colorsys.py#L145) に従ってください。
値域は
* \(0 \leq H, V, R, G, B \lt 1\)
* \(0 \leq S \leq 1\)
とします。

## Additional Constraints

* \(H, V \neq 1\)

## Inputs

* \(HSV\) (\(0 \le HSV[{i, j}] \le 1\)): Float `$lm[0:24]`, `/((4:3, 2_W:1, 4_PE:1), (3:1); B@[MAB,L1B,L2B])`

## Outputs

* \(RGB\): Float `$ln[0:24]`, `/((4:3, 2_W:1, 4_PE:1), (3:1))` / \(0.0001\) 以下の絶対誤差が許容されます

## Testcases

* [testcase.vsm](https://mncore-challenge.preferred.jp/testcase/hsv2rgb/testcase.vsm)
