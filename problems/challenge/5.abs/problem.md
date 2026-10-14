---
source_url: https://mncore-challenge.preferred.jp/problem/abs
slug: abs
fetched_at: 2026-10-14T00:38:50+00:00
---

# Abs

- Top: 13 lines / sosuupoyo
- Par: 44 lines

## Problem Statement

LM0上の `Int` 配列 \(X\) の各要素 \(X[i]\) について、絶対値 \(Y[i] = |X[i]|\) を計算し、LM1上に出力してください。

## Explanation

様々な解法が考えられますが、良い機会なのでマスクについて説明します。MN-Core は数多くの PE 全てが同じ命令を並列に処理しますが、その際にマスクを使うことで if 文のような条件分岐を実現することができます。（[SDM 3.6.2「マスクレジスタ」](https://projects.preferred.jp/mn-core/assets/mncore2_dev_manual_ja.pdf#subsection.3.6.2)）
次の VSM は、C 言語でいう `if (m[i] >= 0) n[i] = m[i];` を実現しています。
```vsm
imm i"0" $nowrite
isub $lm0v $aluf $omr1
ipassa $lm0v $ln0v/$imr1
```

\(2\) 行目では `$lm[0:8]` から \(0\) を引き、同じ PE 内の \(1\) 番目のマスクレジスタに書き込んでいます。
ここで、マスクレジスタへの書き込みの際は、他のレジスタへの書き込みと違って、命令によって異なる方法で生成される \(16\) ビット（\(4\) サイクル × \(4\) 半語）のフラグを書き込むことになります。
isub 命令の場合、単語ごとに比較し、演算結果が非負のときフラグ上で対応するビットが立つことになります（[SDM 表3.11「オペコードと符号なし指定有無ごとの、ALU 命令式が生成するマスクフラグ」](https://projects.preferred.jp/mn-core/assets/mncore2_dev_manual_ja.pdf#table.3.11)）。
今回の場合、`$m[i]` が \(0\) 以上のとき、\(1\) 単語は \(2\) 半語であるので、\(2i\) 番目と \(2i + 1\) 番目のフラグが立つことになります。
次に \(3\) 行目に注目します。
`$ln0v/$imr1` のように書き込み先を指定したときに、マスクレジスタの \(4 \times i + j\) 番目のビットが立っていると、\(i\) サイクル目の、MSB から数えて \(j\) 番目の半語への書き込みが有効になります。
したがって、上記の VSM は `$m[i]` が \(0\) 以上のとき、 `$n[i]` に `$m[i]` を書き込みます。
`$lln0v/$llimr1` のようにマスク作用語長指定を \(2\) 長語に指定した場合、\(16\) bit の半語単位ではなく \(32\) bit の単語単位でのマスクが行われます。
また、`ipassa/$imr1 $lm0v $ln0v` のように、書き込み先ではなく命令にマスクを指定することもできます。これはゼロフラッシュマスク（[SDM 3.6.2.2「ゼロフラッシュマスク適用」](https://projects.preferred.jp/mn-core/assets/mncore2_dev_manual_ja.pdf#subsubsection.3.6.2.2)）といい、フラグが \(0\) の箇所には \(0\) を書き込みます。これは `$aluf` などのフォワーディングパスの値にも反映されます。
PE 命令の出力先は、並列実行条件（[SDM 3.6.4「並列実行条件」](https://projects.preferred.jp/mn-core/assets/mncore2_dev_manual_ja.pdf#subsection.3.6.4)）などの制約が許すかぎり複数指定でき、その場合は同じ値が複数のレジスタに書き込まれます。
マスクレジスタへ書き込みを行う場合も同様であり、マスク結果と演算結果の両方が必要なときに有用です。
```vsm
isub $lr0v $lm0v $omr1 $ls0v $lr10v
```

上記の例は所要ステップ数を除き、以下と同様の動作をします。
```vsm
isub $lr0v $lm0v $omr1
isub $lr0v $lm0v $ls0v
isub $lr0v $lm0v $lr10v
```

## Inputs

* \(X\) (\(-100 \le X[{i}] \le 100\)): Int `$lm[0:88]`, `/((16_MAB:1, 4_PE:1, 44:1, 2_W:1); B@[L1B,L2B])`

## Outputs

* \(Y\): Int `$ln[0:88]`, `/((16_MAB:1, 4_PE:1, 44:1, 2_W:1))`

## Testcases

* [testcase.vsm](https://mncore-challenge.preferred.jp/testcase/abs/testcase.vsm)
