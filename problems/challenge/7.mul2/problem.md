---
source_url: https://mncore-challenge.preferred.jp/problem/mul2
slug: mul2
fetched_at: 2026-10-14T00:38:52+00:00
---

# FMul 2

- Top: 9 lines / sosuupoyo
- Par: 14 lines

## Problem Statement

LM0上の `Half` 配列 \(X\) の各要素 \(X[i]\) に対して \(Y[i] = X[i] \times 2\) を計算し、LM1上に出力してください。

## Explanation

MAU 命令も覚えたので、この問題も `imm h"2.0"` で即値を用意したあと、半精度の乗算命令 `hvmul` を使用して `2.0` を掛ければ良いと思うところでしょう。しかし、MAU を使用した MN-Core 2 の半精度系演算は注意が必要です。
半精度の積和演算は、half × half + float = float の精度で行われるため、この精度に合わせて入出力を行わないといけないからです。
半精度乗算命令 `hvmul` はサイクルあたり \(1\) 長語ぶんの「\(4\) 要素の half」をふたつ受け取り、\(2\) 長語で「\(4\) 要素の float」の出力をします。つまり、half で結果を得たい場合は、出力を float から half に変換する必要があります。
#### ・出力の丸め

MN-Core 2 では `hvmul r` のように、MAU 命令式オペコードの末尾に `r` を付加することで、double 出力を float に、float 出力を half に変換する事ができます。 （[SDM 3.6.9.25「出力の精度縮減」](https://projects.preferred.jp/mn-core/assets/mncore2_dev_manual_ja.pdf#subsubsection.3.6.9.25)）
つまり、`hvmul r $lr0v $ls0v $lm0v` とすれば、half の長語入力を \(2\) つ受け取り、half の長語出力を得ることができます。
同様に、`fvmul r $lr0v $ls0v $m0v` とすれば float の長語入力を \(2\) つ受け取り half の単語出力が、`dvadd r $lr0v $ls0v $m0v` とすれば double の長語入力を \(2\) つ受け取り、float の単語出力が得られます。
#### ・入力の精度拡張

半精度の積和演算 `hvfma` を使用して、半精度の値 \(r, s, m\) に対して \(n = r \times s + m\) を計算する場合を考えます。
このとき、`hvfma` の \(3\) 番目の引数は float である必要があるので、\(m\) を half から float に変換する必要があります。
MN-Core 2 では `hvfma $lr0v $ls0v $lm0v e $lln0v` のように、入力オペランドの末尾に `e` を付加すると、half の入力を float に、float の入力を double に変換して入力することができます。（[SDM 3.6.9.23「入力の精度拡張」](https://projects.preferred.jp/mn-core/assets/mncore2_dev_manual_ja.pdf#subsubsection.3.6.9.23)）
この例を見ると、hvfma はサイクルあたり \(1\) 長語ぶんの「\(4\) 要素の half」を \(2\) つと、\(2\) 長語ぶんの「\(4\) 要素の float」を受け取り、\(2\) 長語ぶんの「\(4\) 要素の float」を出力します。
そのため、`$lm0` の \(1\) 長語領域にある「\(4\) 要素の half」を精度拡張し、\(2\) 長語ぶんの「\(4\) 要素の float」に変換しています。
結果も half で良ければ、出力の丸めと組み合わせて `hvfmar $lr0v $ls0v $lm0ve $ln0v` にします。
#### ・入力の丸め

半精度を入力に演算をする命令に関しては、`hvmul $lr0 $lls0 r $lln0` のように入力オペランドの末尾に `r` を付加すると、float を half に変換して入力できます。（[SDM 3.6.9.24「入力の精度縮減」](https://projects.preferred.jp/mn-core/assets/mncore2_dev_manual_ja.pdf#subsubsection.3.6.9.24)）
この例では、\(1\) 長語ぶんの「\(4\) 要素の half」と、\(2\) 長語ぶんの「\(4\) 要素の float」を half に変換して受け取り、それらの積を \(2\) 長語ぶんの「\(4\) 要素の float」を出力します。
なお、double を float に入力で丸める事はできません。また、同様の入力丸め機能は ALU の半精度演算命令にも存在します。（[SDM 3.6.12.19「ALU への入力の単精度から半精度への精度縮減」](https://projects.preferred.jp/mn-core/assets/mncore2_dev_manual_ja.pdf#subsubsection.3.6.12.19)）
#### ・その他の注意点

出力を float から double のように精度拡張する事はできません。
半精度の積和演算は、half × half + float = float の精度で行われると説明しましたが、`vadd` や `vpassa` もこの積和演算器を流用しているため、同様に精度の丸めや拡張を行う必要があります。
hvadd は half + float = float で行われるので、入力を half で行いたい場合は、\(2\) 番目の引数を `e` で精度拡張する必要があります。
hvpassa も half → float で行われるので、出力を half で行いたい場合は出力を half に丸める必要があります。
なお、 `hvfma $lr0v $ls0v $ls0v e $lln0v` のように、同じ読み出し元 PE オペランドに対して精度変換の指定を混在させることも可能です。

## Inputs

* \(X\) (\(-1 \le X[{i}] \le 1\)): Half `$lm[0:96]`, `/((16_MAB:1, 4_PE:1, 48:1, 4_W:1); B@[L1B,L2B])`

## Outputs

* \(Y\): Half `$ln[0:96]`, `/((16_MAB:1, 4_PE:1, 48:1, 4_W:1))` / \(10^{-9}\) 以下の絶対誤差が許容されます

## Testcases

* [testcase.vsm](https://mncore-challenge.preferred.jp/testcase/mul2/testcase.vsm)
