---
source_url: https://mncore-challenge.preferred.jp/mnist/problem/onehot_mini/
slug: onehot_mini
fetched_at: 2026-03-02T23:59:45+00:00
---

# Onehot mini

- Top: 7 lines / syttrea
- Par: 19 lines

## Problem Statement

LM に、値域が 0 以上 16 未満で長さが \(32\) の Int ベクトル \(T\) が与えられます。
出力として、\(32 \times 16\) 行列 \(X_{i,j}\) に対して、`j = T[j]` であれば \(1.0\), そうでないなら \(0.0\) で埋められた行列を LM に作成してください。

## Explanation

長さ \(32\) のベクトルとのことですが、`(8_L2B:1)` の通り \(8\) 個の L2B に分割されているので、各 PE では長さ \(4\) のベクトルだと考えることができます。
出力の行列も \(8\) 個の L2B に分割されており、2 次元目は `(2:1, 4_PE:1, 2_W:1)`のレイアウトなので 4 つの PE に分散して \(4 \times 16\) の 0, 1 行列を作成することになります。
\(1.0\) の即値は `imm f"1.0" $lr0v` のように作成できます。
### `(2:1, 4_PE:1, 2_W:1)` の読み方のおさらい
下の方から見ていきます。`2_W:1` とは長語内に2つのワードなので、`[0, 1]` 番目の要素が配置されています。
`4_PE:1` は、それまでの塊が、4 つの PE に順に配置されているので、PE0 は `[0, 1]`、PE1 は `[2, 3]`、PE2 は `[4, 5]`、PE3 は `[6, 7]` が配置されます。
`2:1` は、それまでの塊が、1 長語(=2単語)毎に2つ配置されているので、PE0 は `[0, 1, 8, 9]`、PE1 は `[2, 3, 10, 11]`、PE2 は `[4, 5, 12, 13]`、PE3 は `[6, 7, 14, 15]` が配置されます。
表にしてまとめると、以下のとおりになります。
`$n0``$n1``$n2``$n3` PE00189 PE1231011 PE2451213 PE3671415
### 考え方・方針
MN-Core には間接参照機能（配列の添字アクセスのようなもの）もあるので、最初に X を0クリアしたあと、間接参照で X[i][T[i]] = 1.0f を代入する方針も考えられます。
しかし、T レジスタ間接参照では同じ PE 内の LM0 の範囲でしか間接参照できないのに対し、出力の 2 次元目が `4_PE:1` に分散されているので、面倒です。
なので、`(2:1, 4_PE:1, 2_W:1)` の範囲でインデックス番号を生成し、それと \(T[j]\) が一致していれば \(1.0\)、そうでなければ \(0.0\) を代入する方針が良いでしょう。
条件分岐は、マスクレジスタで実現できます。
参考: [Lesseq](https://mncore-challenge.preferred.jp/problem/fle)、[SDM 表3.11「オペコードと符号なし指定有無ごとの、ALU 命令式が生成するマスクフラグ」](https://projects.preferred.jp/mn-core/assets/mncore2_dev_manual_ja.pdf#table.3.11)、[SDM 3.6.2「マスクレジスタ」](https://projects.preferred.jp/mn-core/assets/mncore2_dev_manual_ja.pdf#subsection.3.6.2)、[SDM 3.6.2.2「ゼロフラッシュマスク適用」](https://projects.preferred.jp/mn-core/assets/mncore2_dev_manual_ja.pdf#subsubsection.3.6.2.2)
### インデックスの作成方法
出力の 2 次元目のレイアウトは `(2:1, 4_PE:1, 2_W:1)` です。つまり、インデックスは以下のように作成すべきです。
`$n0``$n1``$n2``$n3` PE00189 PE1231011 PE2451213 PE3671415
即値命令 `imm` を使って `imm i"0" $s0` と即値を作ったり、PE 番号が得られる固定値入力 `$subpeid` を使って `iadd` などで加算することでインデックスが作成できます。PE 番号は 2 倍しないといけないこと、固定値入力は ALU 命令の 2 番目の引数には使えないことに注意してください。
`$m0` に対して、対応するインデックスと比較をして `$n[0,1,2,3]` に 0/1 を代入、 `$m1` に対して `$n[4,5,6,7]` に 0/1 を代入、を `$m3` まで繰り返していくことで、Accept が得られます。
### 一致の判定方法
[SDM 表3.11「オペコードと符号なし指定有無ごとの、ALU 命令式が生成するマスクフラグ」](https://projects.preferred.jp/mn-core/assets/mncore2_dev_manual_ja.pdf#table.3.11)
<=
==
実は、`==` の判定は、`xor` 命令を使うことで実現できます。Int 単位の比較なので今回は `ixor` 命令を使います。

## Inputs

* \(T\) (\(0 \le T[{i}] \le 15\)): Int `$lm[0:4]`, `(32)/((8_L2B:1, 2:1, 2_W:1); B@[PE,MAB,L1B])`

## Outputs

* \(X\): Float `$ln[0:16]`, `(32,16)/((8_L2B:1, 4:2), (2:1, 4_PE:1, 2_W:1))`

## Testcases

* [testcase.vsm](https://mncore-challenge.preferred.jp/mnist/testcase/onehot_mini/testcase.vsm)
