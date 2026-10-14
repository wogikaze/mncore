---
source_url: https://mncore-challenge.preferred.jp/problem/mat_sq
slug: mat_sq
fetched_at: 2026-10-14T00:38:58+00:00
---

# Matrix Square

- Top: 10 lines / v
- Par: 160 lines

## Problem Statement

LM0上の \(3\) 次元 `Float` 配列 \(X\) に対して、\(2\) 次元目と \(3\) 次元目に対する \(2\) 次元行列積の転置 \(Y[i] = (X[i] \times X[i])^T\) を計算してLM1に出力してください。

## Explanation

各 MAB に \(16 \times 16\) 行列が、`((4_PE:1, 2:1, 2_W:1), (16:2))` のレイアウトで格納されています。
この行列の \(2\) 乗を計算し、転置を行った結果を同様のレイアウトで出力する問題です。
いよいよ最後のチュートリアルです。MN-Core の大きな特色の一つである行列演算の問題です。
行列演算は大まかに、各行列のブロックフロート化と行列レジスタへの書き込み、`m(mul|fma)`命令の呼び出しが必要になります。
また行列演算では、半精度と単精度の中間の精度である疑似単精度も使用することができます。
チュートリアルの内容が長いため、別ページに分けています。以下のリンクから進んでください。
* [行列演算チュートリアル](https://mncore-challenge.preferred.jp/tips/matrix_tutorial)
* [行列演算の図まとめ](https://mncore-challenge.preferred.jp/tips/matrix_figure)
#### 行列積の注意点要点

・行列レジスタ(`$lx`, `$ly`) の読み書きをする命令は、`mwrite` と `mread` であり、読み出しの方は転置で読み込みをします。
・行列演算を行う際、乗算を行う値は、内積を行う組単位で指数を合わせる「ブロックフロート」化を行う必要があります。
・行列積和演算 `mfma` の場合、加算項はブロックフロート化を行う必要はありません。
・疑似単精度は指数部は単精度と同じ\(8\) bit、仮数部長は \(18\) bit で、MSB側に有効値が配置されています。つまり単精度から、 LSB 側 \(5\) bit が無視されるものです。
・LM, GRF は単語 (\(32\) bit) 基準のアドレッシングですが、行列レジスタは長語 (\(64\) bit) 基準のアドレッシングですのでお気をつけください。

## 練習用入出力

いきなり \(16\times16\) 行列の行列積を実装するのは難しいかもしれませんので練習用の小さい入出力を用意しました。必要であれば練習にご使用ください。
### Double \(4\times4\) 行列 testcase.vsm
```vsm
# ======= In(0): ((4_PE:1), (4:1))@LM0 / Double =======
d set $lm0p0 1 4008000000000000 # values=[3.0] / Double @[0,0]
d set $lm2p0 1 4022000000000000 # values=[9.0] / Double @[0,1]
d set $lm4p0 1 401C000000000000 # values=[7.0] / Double @[0,2]
d set $lm6p0 1 4014000000000000 # values=[5.0] / Double @[0,3]
d set $lm0p1 1 3FF0000000000000 # values=[1.0] / Double @[1,0]
d set $lm2p1 1 3FF0000000000000 # values=[1.0] / Double @[1,1]
d set $lm4p1 1 0000000000000000 # values=[0.0] / Double @[1,2]
d set $lm6p1 1 4020000000000000 # values=[8.0] / Double @[1,3]
d set $lm0p2 1 4018000000000000 # values=[6.0] / Double @[2,0]
d set $lm2p2 1 401C000000000000 # values=[7.0] / Double @[2,1]
d set $lm4p2 1 0000000000000000 # values=[0.0] / Double @[2,2]
d set $lm6p2 1 4022000000000000 # values=[9.0] / Double @[2,3]
d set $lm0p3 1 4020000000000000 # values=[8.0] / Double @[3,0]
d set $lm2p3 1 4000000000000000 # values=[2.0] / Double @[3,1]
d set $lm4p3 1 3FF0000000000000 # values=[1.0] / Double @[3,2]
d set $lm6p3 1 3FF0000000000000 # values=[1.0] / Double @[3,3]

# ======= YOUR VSM WILL BE INSERTED HERE =======
# ======= Out(0): ((4_PE:1), (4:1))@LM1 / Double =======
d getd $ln0n0c0b0m0p0 1 # expect=[100.0] / Double @[0,0] atol=1e-05
d getd $ln2n0c0b0m0p0 1 # expect=[68.0] / Double @[0,1] atol=1e-05
d getd $ln4n0c0b0m0p0 1 # expect=[97.0] / Double @[0,2] atol=1e-05
d getd $ln6n0c0b0m0p0 1 # expect=[40.0] / Double @[0,3] atol=1e-05
d getd $ln0n0c0b0m0p1 1 # expect=[95.0] / Double @[1,0] atol=1e-05
d getd $ln2n0c0b0m0p1 1 # expect=[26.0] / Double @[1,1] atol=1e-05
d getd $ln4n0c0b0m0p1 1 # expect=[79.0] / Double @[1,2] atol=1e-05
d getd $ln6n0c0b0m0p1 1 # expect=[83.0] / Double @[1,3] atol=1e-05
d getd $ln0n0c0b0m0p2 1 # expect=[26.0] / Double @[2,0] atol=1e-05
d getd $ln2n0c0b0m0p2 1 # expect=[15.0] / Double @[2,1] atol=1e-05
d getd $ln4n0c0b0m0p2 1 # expect=[51.0] / Double @[2,2] atol=1e-05
d getd $ln6n0c0b0m0p2 1 # expect=[57.0] / Double @[2,3] atol=1e-05
d getd $ln0n0c0b0m0p3 1 # expect=[155.0] / Double @[3,0] atol=1e-05
d getd $ln2n0c0b0m0p3 1 # expect=[21.0] / Double @[3,1] atol=1e-05
d getd $ln4n0c0b0m0p3 1 # expect=[95.0] / Double @[3,2] atol=1e-05
d getd $ln6n0c0b0m0p3 1 # expect=[66.0] / Double @[3,3] atol=1e-05
```

### Float \(8\times8\) 行列 testcase.vsm
_詳細データは省略。必要なら source_url を参照してください。_
### Float \(8\times8\) 行列 テキスト形式
```vsm
[[3,9,7,5,1,1,0,8],
 [6,7,0,9,8,2,1,1],
 [3,5,4,2,6,1,2,3],
 [4,7,1,5,5,0,6,1],
 [0,9,9,8,3,0,6,4],
 [1,4,0,9,2,6,3,5],
 [5,1,9,7,9,8,5,9],
 [0,1,0,3,3,2,8,3]]
```

### 入力の `$l2bid = 0` の \(16\times16\) 行列 テキスト形式
```vsm
[[43, 95, 75, 63, 24, 24, 15, 87, 64, 73, 11, 97, 84, 29, 26, 26],
 [37, 57, 48, 36, 65, 22, 36, 42, 51, 80, 27, 56, 63, 14, 64, 25],
 [15, 95, 96, 82, 37, 18, 71, 49, 20, 54, 13, 91, 33, 69, 38, 56],
 [59, 26, 97, 79, 94, 90, 63, 92, 17, 27, 14, 39, 44, 34, 84, 42],
 [35, 58, 22, 82, 16, 98, 79, 27, 10, 83, 73, 75, 79, 16, 42, 20],
 [87, 66, 39, 15, 37, 39, 75, 67, 89, 52, 20, 74, 78, 60, 79, 54],
 [57, 48, 12, 19, 12, 67, 38, 55, 91, 32, 46, 77, 30, 16, 36, 24],
 [93, 82, 67, 88, 82, 26, 90, 58, 82, 90, 38, 19, 30, 48, 83, 87],
 [10, 55, 47, 29, 20, 40, 94, 39, 56, 73, 42, 97, 96, 32, 54, 37],
 [35, 13, 64, 55, 14, 35, 91, 31, 23, 54, 98, 31, 70, 78, 31, 75],
 [43, 66, 67, 58, 18, 85, 38, 26, 13, 63, 70, 11, 56, 30, 68, 25],
 [72, 44, 94, 22, 40, 20, 93, 88, 33, 69, 83, 59, 57, 31, 18, 90],
 [91, 66, 40, 41, 75, 90, 89, 80, 67, 17, 24, 90, 64, 10, 19, 69],
 [10, 24, 59, 72, 68, 30, 74, 31, 39, 77, 68, 86, 69, 61, 18, 43],
 [33, 31, 97, 45, 90, 66, 81, 55, 61, 54, 27, 75, 35, 12, 68, 25],
 [94, 95, 92, 43, 11, 93, 48, 96, 96, 86, 36, 44, 86, 38, 25, 60]]
```

## Additional Constraints

* 入力の値は、小数点以下切り捨てされています。

## Inputs

* \(X\) (\(0 \le X[{i, j, k}] \le 100\)): Float `$lm[0:64]`, `/((8_L2B:1), (4_PE:1, 2:1, 2_W:1), (16:2); B@[MAB,L1B])`

## Outputs

* \(Y\): Float `$ln[0:64]`, `/((8_L2B:1), (4_PE:1, 2:1, 2_W:1), (16:2))` / \(0.00001\) 以下の絶対誤差が許容されます

## Testcases

* [testcase.vsm](https://mncore-challenge.preferred.jp/testcase/mat_sq/testcase.vsm)
