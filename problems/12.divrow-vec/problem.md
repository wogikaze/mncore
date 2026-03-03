---
source_url: https://mncore-challenge.preferred.jp/mnist/problem/div_row/
slug: div_row
fetched_at: 2026-03-02T23:59:44+00:00
---

# DivRow vec

- Top: 29 lines / syttrea
- Par: 160 lines

## Problem Statement

LM上に Float \(256 \times 16\) 行列 \(A\) と、長さ \(256\) のベクトル \(B\) があります。行列 \(C[i][j] = A[i][j] \div B[i]\) を求め、LM 上に出力してください。

## Explanation

[SubRow vec](https://mncore-challenge.preferred.jp/mnist/problem/sub_rowvec/)
MN-Core には除算命令はありません。代わりに近似した逆数平方根 \(\frac{1}{\sqrt{x}}\) を求める `rsqrt` 命令を使います。
逆数であれば、それを乗算すれば除算につかえるけどなんで逆数平方根なの？？ と思われる方もいるかも知れません。
実は、逆数平方根の自乗 \((1/\sqrt{x})^2\) を求めることで、 逆数 \(1/x\) を得ることができます。
また、逆数平方根にもとの値を乗算 \(x\times\frac{1}{\sqrt{x}}\) することで平方根 \(\sqrt{x}\) を得ることができます。逆数平方根自体、ベクトルの正規化などに使われるので用途がありますし、逆数や平方根の専用回路を実装しなくても逆数平方根と乗算で実現できるのです。
また、MN-Core では `rsqrt` は ALU 命令なので、乗算の MAU 命令と実行を重ねられるので、スループットを維持したまま計算することができます。
ただし、本来は非常に計算時間のかかる除算系演算を、FMA などの乗算と同じ \(1\) サイクルのスループットで計算できるようにするために近似が使われており `rsqrt` 命令は 5 bit 程度の精度となっています。
半精度でそこまで精度が要らない場合はこれでも問題ありませんが、float32 では仮数部が 23 bit なので、用途によっては精度が足りない場合があります。
精度が必要な場合はニュートン法で逆数の精度を上げることができます。具体的には、入力 `x` と、`rsqrt` の結果を二乗して求めた近似逆数 `a` を用いて、`a = a*(2-x*a)` を繰り返すことで、1 回ごとに `a` の精度が 2 倍ずつ上がります。
`imm f"2.0" $lt` などで即値を作成し、`y = (-x * a + 2)`; `a = a * y` の 2 回の乗加算を繰り返すことで、精度を上げることができます。今回の問題は 2 回程度の反復で十分な精度が得られるように設定されています。

## Inputs

* \(A\) (\(1 \le A[{i, j}] \le 8\)): Float `$lm[0:256]`, `(256,16)/((4_L2B:2, 64:2), (2:1, 4_PE:1, 2_W:1); B@[MAB,L1B])`
* \(B\) (\(1 \le B[{i}] \le 8\)): Float `$lm[256:320]`, `(256)/((4_L2B:2, 32:1, 2_W:1); B@[PE,MAB,L1B])`

## Outputs

* \(C\): Float `$ln[0:256]`, `(256,16)/((4_L2B:2, 64:2), (2:1, 4_PE:1, 2_W:1))` / \(0.0001\) 以下の絶対誤差が許容されます

## Testcases

* [testcase.vsm](https://mncore-challenge.preferred.jp/mnist/testcase/div_row/testcase.vsm)
